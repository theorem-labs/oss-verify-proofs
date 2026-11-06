(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, module names, addresses and numbers changed; 483 of its 591 lines of code are new or changed and 440 lines of the source are left out. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_shape_of_c.
Import ListNotations.
Open Scope Z_scope.

Lemma swe_pre :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists j0 m',
       ms' = MS (mkR (Z_to_bv 64 0x16dc0) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 a2 a1
                     (Z_to_bv 64 16) a1 a2 a3 a4 a5 a6 a7 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 48)
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d94) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
  apply evt_done.
  do 2 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma swe_mid1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16dcc) sp gp tp t0 t1 t2 s0 s1 a0 s2
                                    a2 a3 a4 a5 a6 a7 s2 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16dc0) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma swe_mid2 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16dd8) sp gp tp t0 t1 t2 s0 s1 s3 s1
                                    a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16dcc) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma swe_mid3 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16de4) sp gp tp t0 t1 t2 s0 s1 s3 s0
                                    a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16dd8) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma swe_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 s30 : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 j0; C8 s30; C8 s20; C8 s10'; C8 s00; C8 ra0] -> 48 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s3 a0 (Z_to_bv 64 1) a3 a4 a5 a6 a7
                                    s20 s30 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16df4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 s30 j0 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 10 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma swe_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10705 (str_bytes "worker_env"%string).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma swe_shape : shape_find shape_rows (str_bytes "worker_env"%string) = 0x10417.
Proof. vm_compute. reflexivity. Qed.

Lemma swe_after : rec_shape_of_contract ->
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sp0 ra0 s00 s10' s20 s30 : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 j0; C8 s30; C8 s20; C8 s10'; C8 s00; C8 ra0] ->
  stk rsegs m lo (bv_unsigned sp0 - 48) -> lo + 112 <= bv_unsigned sp0 -> 0x343f0 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s10' s3 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                     a3' a4' a5' a6' a7' s20 s30 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16310) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp0 - 112, bv_unsigned sp0 - 48)] m m' /\ wmono rsegs m m')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16de4) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp0 ra0 s00 s10' s20 s30 j0 FR ST LO LO2 GS MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 48)) = bv_unsigned sp0 - 48) by (apply unsigned_lit; lia).
  do 4 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "worker_env"%string).
    - exact MI.
    - rewrite SPU. exact ST.
    - rewrite SPU. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. rewrite SPU. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (swe_verb m MI)|].
      left. rewrite SPU. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  rewrite SPU in MU2. unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16df4) by lia. rewrite swe_shape.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 48) [CB 8 j0; C8 s30; C8 s20; C8 s10'; C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m m2 _ _ FR MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply swe_tail; [exact FR2 | lia] |].
  intros ms3 ->. apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|].
  split; [|exact WM2].
  replace (bv_unsigned sp0 - 112) with (bv_unsigned sp0 - 48 - 64) by ring. exact MU2.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecSeq RecStep RecGlue RecTail RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import answer_c record_c xmalloc_c arg_s_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import sup_worker_env_c.
Local Open Scope Z_scope.

Definition swe_kx (xs : list Z) (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> ~ In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma swe_kx_trans : forall xs R1 R2 R3, swe_kx xs R1 R2 -> swe_kx xs R2 R3 -> swe_kx xs R1 R3.
Proof. intros xs R1 R2 R3 H1 H2 r Hr N. rewrite (H2 r Hr N). exact (H1 r Hr N). Qed.

Lemma swe_kx_of_pres : forall xs R R', regs_preserved R R' -> swe_kx xs R R'.
Proof. intros xs R R' H r Hr _. exact (H r Hr). Qed.

Lemma swe_kx_pres : forall xs R R', swe_kx xs R R' ->
  (forall r, In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> regs_preserved R R'.
Proof.
  intros xs R R' K E r Hr. destruct (in_dec Z.eq_dec r xs) as [H|H]; [exact (E r H) | exact (K r Hr H)].
Qed.

Ltac swe_one X :=
  first [ exfalso; match goal with N : ~ In _ _ |- _ => apply N end; cbn [In]; lia
        | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity] ].

Ltac swe_tac X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Nrr := fresh "Nrr" in
  intros rr Hrr Nrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; swe_one X|]);
  subst rr; swe_one X.

Lemma swe_host_shape : forall m, ro_agree rsegs m -> answer_c.ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
Proof.
  intros m RA.
  assert (RO : forall i, 0 <= i <= 6 -> ro_addr rsegs (Z_to_bv 64 (0x10417 + i)) = true).
  { intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity. }
  split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    unfold wa. rewrite (RA _ (RO (Z.of_nat i) ltac:(lia))).
    assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
  - split; [apply no0_nz; vm_compute; reflexivity|]. split; [cbn; unfold LMAX; lia|].
    split; [apply fits_shape_set; left; reflexivity|]. intros i Hi. apply RO. cbn in Hi. lia.
Qed.

Lemma swe_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma swe_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite swe_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Section P.
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
Hypothesis ARGS : arg_s_contract B API.
Hypothesis ANS : answer_contract B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Lemma swe_shapes_kept : forall K L A regs mem md E excl L' A' regs' mem' md',
  call_pre_k B (aa_MR API) K L A regs mem md ->
  call_post_rec B (aa_MR API) K L A regs mem md E excl L' A' regs' mem' md' ->
  (forall a, G_SHAPES <= a < G_SHAPES + 448 -> ~ E a) ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  bytes_at rsegs mem' G_SHAPES g_shapes_bytes.
Proof using SEGS RIMG RFREE.
  intros K L A regs mem md E excl L' A' regs' mem' md' PRE POST HE BS.
  pose proof alloc_ceiling_val as AC.
  destruct PRE as (HM & _ & _ & _ & _ & HCE & _).
  destruct POST as (PM & _ & _ & _ & _ & _ & _ & PF & _).
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  apply (bytes_at_transfer rsegs mem); [exact BS|]. intros i Hi. rewrite GL in Hi.
  assert (RL : in_globals frame_RELRO (G_SHAPES + i)).
  { exists 0x226b0, 1680. split; [left; reflexivity | unfold G_SHAPES; lia]. }
  destruct (RIMG _ RL) as (I1 & _ & _ & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  rewrite <- SEGS.
  assert (NS : ~ scratch_k B K regs (G_SHAPES + i))
    by (unfold scratch_k; intros [H|H]; [lia | exact (I4 H)]).
  exact (proj1 (PF _ (or_intror I1) (RFREE _ _ _ _ _ HM RL) (RFREE _ _ _ _ _ PM RL) NS
                 (HE (G_SHAPES + i) ltac:(lia)))).
Qed.

Lemma swe_rjr_shapes : forall K S O L A mem md Lc Ac mc mdc,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  bytes_at rsegs mc G_SHAPES g_shapes_bytes.
Proof using SEGS RIMG.
  intros K S O L A mem md Lc Ac mc mdc RJ BS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct RJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  apply (bytes_at_transfer rsegs mem); [exact BS|]. intros i Hi. rewrite GL in Hi.
  assert (RL : in_globals frame_RELRO (G_SHAPES + i)).
  { exists 0x226b0, 1680. split; [left; reflexivity | unfold G_SHAPES; lia]. }
  destruct (RIMG _ RL) as (I1 & I2 & I3 & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  assert (NS : ~ (S - K <= G_SHAPES + i < S)) by lia.
  assert (NR : ~ rec_area (G_SHAPES + i))
    by (unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES; lia).
  rewrite <- SEGS. exact (proj1 (HF _ (or_intror (conj I1 (conj I2 I3))) NS I4 NR)).
Qed.

Theorem sup_worker_env_holds : sup_worker_env_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN AX CTX SLACK REC ARGS ANS RSO RIMG RFREE.
  unfold sup_worker_env_contract.
  intros L A regs mem md pf pc pn format cpus nice R O b PRE G10 G11 G12 SA1 SA2 SA3 GS GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_WORKER_ENV_K in PRE, PRK, HCEIL, HWS, SA1, SA2, SA3.
  unfold SUP_WORKER_ENV.
  rewrite SEGS in GR, RA, F18, HWS, GS |- *.
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof (sinv_init B API 12384 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as HN.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & _ & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  change (snd (sup_worker_env_m R format cpus nice)) with
    (snd (rec_answer (rec_record R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice])
       (REC_WORKER_ENV, [sarg format; sarg cpus; sarg nice]) (daemon_shape "worker_env") true)) in ROOM.
  unfold sup_worker_env_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice])
                  (REC_WORKER_ENV, [sarg format; sarg cpus; sarg nice]) (daemon_shape "worker_env") true)) <= 16)%nat).
  { pose proof (swe_len R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice] (daemon_shape "worker_env") true HCODE)
      as H.
    assert (LX6 : length (daemon_shape "worker_env") = 6%nat) by (vm_compute; reflexivity).
    rewrite LX6 in H. exact H. }
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 12384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    eapply swe_pre; [exact ST | lia]. }
  intros ms1 (can1 & (j0 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16dc0) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 pn) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact G12).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 pc) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; exact G11).
  assert (E1_18 : getr R1 18 = Z_to_bv 64 pf) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; exact G10).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 REC_WORKER_ENV)
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (K01 : swe_kx [2; 8; 9; 18; 19] regs R1) by swe_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1
           REC_WORKER_ENV _ SI1).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia. }
  { rewrite SP1. lia. }
  { rewrite E1_4. exact HTP. }
  { exact E1_10. }
  { unfold REC_FN_COUNT, REC_WORKER_ENV. lia. }
  intros L1 A1 regs1 m2 md1 O1 SI2 BLE1 PR1 R10 FK1.
  rewrite E1_1. rewrite sb_shift_refl in BLE1.
  pose proof SI2 as (RJ2 & _). pose proof RJ2 as (HM2 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply swe_mid1. }
  intros ms2 (can2 & -> & EQ2).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x16dcc) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 48)).
  { rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs. exact (eq_trans (PR1 2 ltac:(unfold callee_saved; lia)) E1_2). }
  assert (E2_4 : getr R2 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs. exact (eq_trans (PR1 4 ltac:(unfold callee_saved; lia)) E1_4). }
  assert (E2_8 : getr R2 8 = Z_to_bv 64 pn).
  { rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs. exact (eq_trans (PR1 8 ltac:(unfold callee_saved; lia)) E1_8). }
  assert (E2_9 : getr R2 9 = Z_to_bv 64 pc).
  { rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs. exact (eq_trans (PR1 9 ltac:(unfold callee_saved; lia)) E1_9). }
  assert (E2_10 : getr R2 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; exact R10).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 pf).
  { rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs.
    exact (eq_trans (PR1 18 ltac:(unfold callee_saved; lia)) E1_18). }
  assert (E2_19 : getr R2 19 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 19 X2 eq_refl); simp_regs; exact R10).
  assert (K1r : swe_kx [2; 8; 9; 18; 19] R1 regs1) by exact (swe_kx_of_pres _ _ _ PR1).
  assert (K12 : swe_kx [2; 8; 9; 18; 19] regs1 R2) by swe_tac X2.
  assert (SP2 : spZ R2 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (FK1 (bv_unsigned sp - 48 + i) ltac:(rewrite SP1; lia)) as [K1 K2].
    split; [exact K1 | exact (proj1 K2)]. }
  assert (SRC2 : arg_s_src B L1 A1 (spZ R2) m2 pf format).
  { apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L1 A1 m2 md1
             (rec_record R REC_WORKER_ENV []) O1 b pf format (spZ R2) SI2 RA).
    - rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    - rewrite SP2. lia.
    - exact SA1. }
  destruct (sarg_facts B L1 A1 (spZ R2) m2 pf format SRC2) as (NO2 & LX2).
  apply (sinv_arg_s B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L1 A1 m2 md1 R
           REC_WORKER_ENV O1 b R2 pf format _ SI2).
  { rewrite E2_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP2. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP2. lia. }
  { rewrite E2_4. exact HTP. }
  { exact E2_10. }
  { exact E2_11. }
  { exact SRC2. }
  { eapply room_slots_mono; [| | exact ROOM].
    - eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      apply sb_le_malloc; lia.
    - unfold LMAX in *. lia. }
  intros L2 A2 regs2 m3 md2 p1 SI3 EQB2 INI2 PR2 FK2.
  rewrite E2_1.
  pose proof SI3 as (RJ3 & _). pose proof RJ3 as (HM3 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply swe_mid2. }
  intros ms3 (can3 & -> & EQ3).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x16dd8) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 48)).
  { rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs. exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) E2_2). }
  assert (E3_4 : getr R3 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs. exact (eq_trans (PR2 4 ltac:(unfold callee_saved; lia)) E2_4). }
  assert (E3_8 : getr R3 8 = Z_to_bv 64 pn).
  { rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs. exact (eq_trans (PR2 8 ltac:(unfold callee_saved; lia)) E2_8). }
  assert (E3_10 : getr R3 10 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs.
    exact (eq_trans (PR2 19 ltac:(unfold callee_saved; lia)) E2_19). }
  assert (E3_11 : getr R3 11 = Z_to_bv 64 pc).
  { rewrite (getr_of_eqv _ _ 11 X3 eq_refl); simp_regs. exact (eq_trans (PR2 9 ltac:(unfold callee_saved; lia)) E2_9). }
  assert (E3_19 : getr R3 19 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 19 X3 eq_refl); simp_regs.
    exact (eq_trans (PR2 19 ltac:(unfold callee_saved; lia)) E2_19). }
  assert (K2r : swe_kx [2; 8; 9; 18; 19] R2 regs2) by exact (swe_kx_of_pres _ _ _ PR2).
  assert (K23 : swe_kx [2; 8; 9; 18; 19] regs2 R3) by swe_tac X3.
  assert (SP3 : spZ R3 = bv_unsigned sp - 48) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    destruct (FK2 (bv_unsigned sp - 48 + i) ltac:(rewrite SP2; lia)) as [K1 K2].
    split; [exact K1 | exact (proj1 K2)]. }
  assert (SRC3 : arg_s_src B L2 A2 (spZ R3) m3 pc cpus).
  { apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 _ _ b pc cpus
             (spZ R3) SI3 RA).
    - rewrite SP3. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    - rewrite SP3. lia.
    - exact SA2. }
  destruct (sarg_facts B L2 A2 (spZ R3) m3 pc cpus SRC3) as (NO3 & LX3).
  apply (sinv_arg_sn B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 R
           REC_WORKER_ENV [sarg format] _ b R3 pc cpus _ SI3).
  { cbn [length]. lia. }
  { rewrite E3_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP3. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP3. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP3. lia. }
  { rewrite E3_4. exact HTP. }
  { exact E3_10. }
  { exact E3_11. }
  { exact SRC3. }
  { rewrite EQB2. eapply room_slots_mono; [| | exact ROOM].
    - eapply sb_le_trans; [apply sb_malloc_mono, sb_malloc_mono; exact BLE1|].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      apply sb_le_malloc; lia.
    - unfold LMAX in *. lia. }
  intros L3 A3 regs3 m4 md3 p2 SI4 EQB3 INI3 PR3 FK3.
  cbn [app] in SI4.
  rewrite E3_1.
  pose proof SI4 as (RJ4 & _). pose proof RJ4 as (HM4 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM4) as (Hh4 & Hl4 & _).
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply swe_mid3. }
  intros ms4 (can4 & -> & EQ4).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
  assert (E4_1 : getr R4 1 = Z_to_bv 64 0x16de4) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 48)).
  { rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs. exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E3_2). }
  assert (E4_4 : getr R4 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X4 eq_refl); simp_regs. exact (eq_trans (PR3 4 ltac:(unfold callee_saved; lia)) E3_4). }
  assert (E4_10 : getr R4 10 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs.
    exact (eq_trans (PR3 19 ltac:(unfold callee_saved; lia)) E3_19). }
  assert (E4_11 : getr R4 11 = Z_to_bv 64 pn).
  { rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs. exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E3_8). }
  assert (E4_19 : getr R4 19 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 19 X4 eq_refl); simp_regs.
    exact (eq_trans (PR3 19 ltac:(unfold callee_saved; lia)) E3_19). }
  assert (K3r : swe_kx [2; 8; 9; 18; 19] R3 regs3) by exact (swe_kx_of_pres _ _ _ PR3).
  assert (K34 : swe_kx [2; 8; 9; 18; 19] regs3 R4) by swe_tac X4.
  assert (SP4 : spZ R4 = bv_unsigned sp - 48) by (unfold spZ; rewrite E4_2; apply unsigned_lit; lia).
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (FK3 (bv_unsigned sp - 48 + i) ltac:(rewrite SP3; lia)) as [K1 K2].
    split; [exact K1 | exact (proj1 K2)]. }
  assert (SRC4 : arg_s_src B L3 A3 (spZ R4) m4 pn nice).
  { apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L3 A3 m4 md3 _ _ b pn nice
             (spZ R4) SI4 RA).
    - rewrite SP4. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    - rewrite SP4. lia.
    - exact SA3. }
  destruct (sarg_facts B L3 A3 (spZ R4) m4 pn nice SRC4) as (NO4 & LX4).
  apply (sinv_arg_sn B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L3 A3 m4 md3 R
           REC_WORKER_ENV [sarg format; sarg cpus] _ b R4 pn nice _ SI4).
  { cbn [length]. lia. }
  { rewrite E4_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP4. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP4. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP4. lia. }
  { rewrite E4_4. exact HTP. }
  { exact E4_10. }
  { exact E4_11. }
  { exact SRC4. }
  { rewrite EQB3, EQB2. eapply room_slots_mono; [| | exact ROOM].
    - eapply sb_le_trans; [apply sb_malloc_mono, sb_malloc_mono, sb_malloc_mono; exact BLE1|].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      apply sb_le_malloc; lia.
    - unfold LMAX in *. lia. }
  intros L4 A4 regs4 m5 md4 p3 SI5 EQB4 INI4 PR4 FK4.
  cbn [app] in SI5.
  rewrite E4_1.
  assert (R4_2 : getr regs4 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (PR4 2 ltac:(unfold callee_saved; lia)) E4_2).
  assert (R4_19 : getr regs4 19 = Z_to_bv 64 e) by exact (eq_trans (PR4 19 ltac:(unfold callee_saved; lia)) E4_19).
  assert (K4r : swe_kx [2; 8; 9; 18; 19] R4 regs4) by exact (swe_kx_of_pres _ _ _ PR4).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m4); [exact FR4|]. intros i Hi. cbn in Hi.
    destruct (FK4 (bv_unsigned sp - 48 + i) ltac:(rewrite SP4; lia)) as [K1 K2].
    split; [exact K1 | exact (proj1 K2)]. }
  pose proof SI5 as (RJ5 & _ & _ & _ & _ & RA5 & _).
  pose proof RJ5 as (HM5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC5 & _).
  rewrite SEGS in HSC5.
  destruct (mr_model B _ LAWS L4 A4 m5 md4 HM5) as (Hh5 & Hl5 & _).
  assert (FRn : rw_cells rsegs (normalize rsegs m5) (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]) by (apply rw_cells_norm_hi; [exact RA5 | lia | exact FR5]).
  assert (STn : stk rsegs (normalize rsegs m5) (bv_unsigned sp - 12384) (bv_unsigned sp - 48)).
  { apply stk_norm; [lia | lia |]. intros a Ha. apply HSC5. left. lia. }
  pose proof (bytes_at_normalize rsegs m5 _ _ RA5
                (swe_rjr_shapes 12384 (bv_unsigned sp) O L A mem md L4 A4 m5 md4 RJ5 GS)) as GSn.
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs4 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by exact R4_2.
    rewrite Q2.
    eapply (evt_normalize rsegs); [exact WX | exact RA5 |].
    eapply (swe_after RSO); [exact FRn | exact STn | lia | lia | exact GSn | apply mem_inv_normalize]. }
  intros ms6 (can6 & (s6n & Q6 & REL6 & RO6) & EQ6).
  destruct Q6 as (m6n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU6n & WM6n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL6) as [EC6 MR6r].
  revert EC6 MR6r RO6 EQ6. generalize (ms_mem can6) as m6. intros m6 EC6 MR6r RO6 EQ6. subst can6.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m5 RA5) MR6r RO6 MU6n) as MU6.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m5 RA5) MR6r RO6 WM6n) as WM6.
  clear MU6n WM6n MR6r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ6 eq_refl eq_refl) as (R6 & -> & X6).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L4 A4 m5 md4 _ _ b m6 _ SI5 MU6 WM6
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI6.
  assert (E6_1 : getr R6 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_2 : getr R6 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_10 : getr R6 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X6 eq_refl); simp_regs; exact R4_19).
  assert (E6_11 : getr R6 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_12 : getr R6 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X6 eq_refl); simp_regs; reflexivity).
  assert (K46 : swe_kx [2; 8; 9; 18; 19] regs4 R6) by swe_tac X6.
  assert (RP6 : regs_preserved regs R6).
  { apply (swe_kx_pres [2; 8; 9; 18; 19]).
    - apply (swe_kx_trans _ regs R1 R6 K01).
      apply (swe_kx_trans _ R1 regs1 R6 K1r).
      apply (swe_kx_trans _ regs1 R2 R6 K12).
      apply (swe_kx_trans _ R2 regs2 R6 K2r).
      apply (swe_kx_trans _ regs2 R3 R6 K23).
      apply (swe_kx_trans _ R3 regs3 R6 K3r).
      apply (swe_kx_trans _ regs3 R4 R6 K34).
      exact (swe_kx_trans _ R4 regs4 R6 K4r K46).
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X6 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (SP6 : spZ R6 = spZ regs) by (unfold spZ; rewrite E6_2; reflexivity).
  pose proof SI6 as (RJ6 & GR6 & ON6 & B16 & B26 & RA6 & F186 & RS6).
  assert (SHP : answer_c.ans_shape rsegs m6 0x10417 (daemon_shape "worker_env")).
  { replace (daemon_shape "worker_env") with REC_MOD_HOST_SHAPE by (vm_compute; reflexivity).
    exact (swe_host_shape m6 RA6). }
  assert (BLE4 : sb_le (sb_shift b A A4)
                   (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length (sarg format)) + 1))
                      (Z.of_nat (length (sarg cpus)) + 1)) (Z.of_nat (length (sarg nice)) + 1))).
  { rewrite EQB4, EQB3, EQB2. apply sb_malloc_mono, sb_malloc_mono, sb_malloc_mono. exact BLE1. }
  assert (ROOM5 : room_slots
            (sb_malloc (sb_malloc (sb_shift b A A4)
               (Z.of_nat (length (snd (rec_answer (rec_record R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice])
                  (REC_WORKER_ENV, [sarg format; sarg cpus; sarg nice]) (daemon_shape "worker_env") true))) + 1))
               (Z.of_nat (length (snd (rec_answer (rec_record R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice])
                  (REC_WORKER_ENV, [sarg format; sarg cpus; sarg nice]) (daemon_shape "worker_env") true))) + 1))
            (Z.of_nat (length (snd (rec_answer (rec_record R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice])
               (REC_WORKER_ENV, [sarg format; sarg cpus; sarg nice]) (daemon_shape "worker_env") true))) + 1)).
  { eapply room_slots_mono; [| | exact ROOM].
    - apply sb_malloc_mono, sb_malloc_mono. exact BLE4.
    - unfold LMAX. lia. }
  rewrite <- SEGS in GR6, RA6, F186, SHP.
  pose proof (answer_tail B API SEGS AX CTX ERRNO_LOW ANS SLACK 12384 L A regs mem md O L4 A4 R6 m6 md4
                (rec_record R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice]) _ b _ (sb_shift b A A4) e 0x10417
                (REC_WORKER_ENV, [sarg format; sarg cpus; sarg nice]) (daemon_shape "worker_env") true PRE AK RJ6 E6_1
                SP6 RP6 E6_10 E6_11 ltac:(rewrite E6_12; reflexivity) GR6 (fun _ => SHP)
                (fun _ _ => ans_entry_record R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice] HN)
                FRM F186 RA6 RS6 eq_refl BLE4 ROOM5 ON6 B16 B26) as TR0.
  rewrite SEGS in TR0.
  eapply SR_mono; [exact TR0|].
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_worker_env_m R format cpus nice)), O',
    (snd (sup_worker_env_m R format cpus nice)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK'|].
  split; [exact POST'|].
  do 10 (split; [assumption|]).
  split.
  { rewrite SEGS.
    apply (swe_shapes_kept 12384 L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' PRK POST');
      [|exact GS].
    intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
  repeat (split; [assumption|]). exact RES'.
Qed.

End P.
