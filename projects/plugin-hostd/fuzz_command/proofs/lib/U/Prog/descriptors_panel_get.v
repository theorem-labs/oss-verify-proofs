(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, module names, addresses and numbers changed; 344 of its 447 lines of code are new or changed and 445 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_shape_of_c.
Import ListNotations.
Open Scope Z_scope.

Lemma dpg_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists j m',
       ms' = MS (mkR (Z_to_bv 64 0x172e0) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 a0 s1
                     (Z_to_bv 64 24) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [CB 8 j; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x172c4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  apply evt_done.
  do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma dpg_run2 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 0x172ec) sp gp tp t0 t1 t2 s0 a0 a0 s0 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x172e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step. apply evt_done. reflexivity.
Qed.

Lemma dpg_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [CB 8 j0; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s1 a0 (Z_to_bv 64 0)
                                    a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x172fc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' j0 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 8 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma dpg_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x109a9 (str_bytes "panel_get"%string).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma dpg_shape : shape_find shape_rows (str_bytes "panel_get"%string) = 0x104b4.
Proof. vm_compute. reflexivity. Qed.

Lemma dpg_after : rec_shape_of_contract ->
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sp0 ra0 s00 s10' : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [CB 8 j0; C8 s10'; C8 s00; C8 ra0] ->
  stk rsegs m lo (bv_unsigned sp0 - 32) -> lo + 96 <= bv_unsigned sp0 -> 0x34100 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s10' s1 (Z_to_bv 64 0x104b4) (Z_to_bv 64 0)
                     a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16310) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp0 - 96, bv_unsigned sp0 - 32)] m m' /\ wmono rsegs m m')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x172ec) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp0 ra0 s00 s10' j0 FR ST LO LO2 GS MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 32)) = bv_unsigned sp0 - 32) by (apply unsigned_lit; lia).
  do 4 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "panel_get"%string).
    - exact MI.
    - rewrite SPU. exact ST.
    - rewrite SPU. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. rewrite SPU. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (dpg_verb m MI)|].
      left. rewrite SPU. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  rewrite SPU in MU2. unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x172fc) by lia. rewrite dpg_shape.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 32) [CB 8 j0; C8 s10'; C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m m2 _ _ FR MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply dpg_tail; [exact FR2 | lia] |].
  intros ms3 ->. apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|].
  split; [|exact WM2].
  replace (bv_unsigned sp0 - 96) with (bv_unsigned sp0 - 32 - 64) by ring. exact MU2.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import xmalloc_c record_c arg_s_c answer_c RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import descriptors_panel_get_c.
Local Open Scope Z_scope.

Definition dpg_rom_chk (a : Z) (bs : list byte) : bool :=
  forallb (fun i => ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) &&
     match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error bs i with
     | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
     | _, _ => false
     end) (seq 0 (length bs)).

Lemma dpg_rom_chk_at : forall a bs i, dpg_rom_chk a bs = true -> (i < length bs)%nat ->
  ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true /\
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros a bs i C Hi. unfold dpg_rom_chk in C.
  pose proof (proj1 (forallb_forall _ _) C i ltac:(apply in_seq; lia)) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Cr Cv]. split; [exact Cr|].
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in Cv. f_equal. apply bv_eq. exact Cv.
Qed.

Lemma dpg_rom_chk_bytes : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  dpg_rom_chk a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RA H0 H1 C. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (dpg_rom_chk_at a bs i C Hi) as [Cr Cv]. unfold wa. rewrite (RA _ Cr). exact Cv.
Qed.

Lemma dpg_ans_shape_chk : forall m a x, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length x) + 1 <= 2 ^ 64 ->
  dpg_rom_chk a (x ++ [Z_to_bv 8 0]) = true -> no0 x -> Z.of_nat (length x) <= LMAX -> fits x ->
  ans_shape rsegs m a x.
Proof.
  intros m a x RA H0 H1 C N0 LX FT. pose proof (length_app x [Z_to_bv 8 0]) as LA. cbn [length] in LA.
  split; [apply dpg_rom_chk_bytes; [exact RA | lia | rewrite LA; lia | exact C]|].
  split; [exact N0|]. split; [exact LX|]. split; [exact FT|].
  intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  exact (proj1 (dpg_rom_chk_at a _ (Z.to_nat i) C ltac:(rewrite LA; lia))).
Qed.

Lemma dpg_ans_shape : forall m, ro_agree rsegs m -> ans_shape rsegs m 0x104b4 (daemon_shape "panel_get").
Proof.
  intros m RA. change (daemon_shape "panel_get") with (shape_of (bstr "panel_get")).
  destruct (shape_of_facts (bstr "panel_get")) as (FT & _ & L78 & N0).
  apply dpg_ans_shape_chk; [exact RA | lia | lia | vm_compute; reflexivity | exact N0 | unfold LMAX; lia | exact FT].
Qed.

Lemma dpg_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma dpg_stub_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length (inst x)) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - lia.
  - rewrite dpg_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Ltac dpg_pres X4 X2 X1 regs1 regs2 P1 P2 :=
  match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X4 eq_refl); simp_regs;
    transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
    rewrite (P2 k ltac:(unfold callee_saved; lia));
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X2 eq_refl); simp_regs;
    transitivity (getr regs1 (Z_to_bv 5 k)); [reflexivity|];
    rewrite (P1 k ltac:(unfold callee_saved; lia));
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X1 eq_refl); simp_regs; reflexivity
  end.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ARGS : arg_s_contract B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis ANS : forall fx' : YK11.FPState, @answer_contract fx' rc B API.

Lemma dpg_relro : forall i, 0 <= i < 448 -> in_globals frame_RELRO (G_SHAPES + i).
Proof. intros i Hi. exists 0x226b0, 1680. split; [left; reflexivity | unfold G_SHAPES; lia]. Qed.

Lemma dpg_shapes_kept : forall K L A regs mem md E excl L' A' regs' mem' md',
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
  pose proof (dpg_relro i ltac:(lia)) as RL.
  destruct (RIMG _ RL) as (I1 & _ & _ & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  rewrite <- SEGS.
  assert (NS : ~ scratch_k B K regs (G_SHAPES + i))
    by (unfold scratch_k; intros [H|H]; [lia | exact (I4 H)]).
  exact (proj1 (PF _ (or_intror I1) (RFREE _ _ _ _ _ HM RL) (RFREE _ _ _ _ _ PM RL) NS
                 (HE (G_SHAPES + i) ltac:(lia)))).
Qed.

Lemma dpg_rjr_shapes : forall K S O L A mem md Lc Ac mc mdc,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  bytes_at rsegs mc G_SHAPES g_shapes_bytes.
Proof using SEGS RIMG.
  intros K S O L A mem md Lc Ac mc mdc RJ BS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct RJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  apply (bytes_at_transfer rsegs mem); [exact BS|]. intros i Hi. rewrite GL in Hi.
  pose proof (dpg_relro i ltac:(lia)) as RL.
  destruct (RIMG _ RL) as (I1 & I2 & I3 & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  assert (NS : ~ (S - K <= G_SHAPES + i < S)) by lia.
  assert (NR : ~ rec_area (G_SHAPES + i))
    by (unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES; lia).
  rewrite <- SEGS. exact (proj1 (HF _ (or_intror (conj I1 (conj I2 I3))) NS I4 NR)).
Qed.

Theorem descriptors_panel_get_holds : descriptors_panel_get_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN RIMG RFREE AX CTX SLACK REC ARGS RSO ANS.
  unfold descriptors_panel_get_contract.
  intros L A regs mem md pu uri R O b PRE A0 SA GS GR RA FRM F18 RES ROOM.
  rewrite SEGS in GS, GR, RA, F18 |- *.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & _).
  unfold DESCRIPTORS_PANEL_GET_K in PRE, PRK, HCEIL, HWS, SA.
  rewrite SEGS in HWS.
  pose proof GR as (Q0 & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HCODE & _) & _) & _).
  change (snd (descriptors_panel_get_m R uri)) with
    (snd (rec_answer (rec_record R REC_DESCRIPTORS_PANEL_GET [sarg uri]) (REC_DESCRIPTORS_PANEL_GET, [sarg uri])
      (daemon_shape "panel_get") false)) in ROOM.
  unfold descriptors_panel_get_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_DESCRIPTORS_PANEL_GET [sarg uri])
                  (REC_DESCRIPTORS_PANEL_GET, [sarg uri]) (daemon_shape "panel_get") false)) <= 28)%nat).
  { pose proof (dpg_stub_len R REC_DESCRIPTORS_PANEL_GET [sarg uri] (daemon_shape "panel_get") false HCODE) as H.
    destruct (shape_of_facts (bstr "panel_get")) as (_ & HI & _ & _).
    change (shape_of (bstr "panel_get")) with (daemon_shape "panel_get") in HI. lia. }
  pose proof (sinv_init B API 12384 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 12384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. eapply dpg_run1; [exact ST | lia]. }
  intros ms1 (can1 & (j & m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & XR1).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x172e0) by (rewrite (getr_of_eqv _ _ 1 XR1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 XR1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 XR1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 pu) by (rewrite (getr_of_eqv _ _ 8 XR1 eq_refl); simp_regs; exact A0).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 24) by (rewrite (getr_of_eqv _ _ 10 XR1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1
           REC_DESCRIPTORS_PANEL_GET).
  - exact SI1.
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - rewrite E1_4. exact HTP.
  - exact E1_10.
  - unfold REC_FN_COUNT, REC_DESCRIPTORS_PANEL_GET. lia.
  - intros L1 A1 regs1 m2 md1 O1 SI2 BLE1 PR1 R10 FK1.
    rewrite E1_1. rewrite sb_shift_refl in BLE1.
    pose proof SI2 as (RJ2 & _). pose proof RJ2 as (HM2 & _).
    destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply dpg_run2. }
    intros ms2 (can2 & -> & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & XR2).
    assert (E2_1 : getr R2 1 = Z_to_bv 64 0x172ec) by (rewrite (getr_of_eqv _ _ 1 XR2 eq_refl); simp_regs; reflexivity).
    assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 32)).
    { rewrite (getr_of_eqv _ _ 2 XR2 eq_refl); simp_regs.
      exact (eq_trans (PR1 2 ltac:(unfold callee_saved; lia)) E1_2). }
    assert (E2_4 : getr R2 4 = getr regs 4).
    { rewrite (getr_of_eqv _ _ 4 XR2 eq_refl); simp_regs.
      exact (eq_trans (PR1 4 ltac:(unfold callee_saved; lia)) E1_4). }
    assert (E2_9 : getr R2 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
      by (rewrite (getr_of_eqv _ _ 9 XR2 eq_refl); simp_regs; exact R10).
    assert (E2_10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
      by (rewrite (getr_of_eqv _ _ 10 XR2 eq_refl); simp_regs; exact R10).
    assert (E2_11 : getr R2 11 = Z_to_bv 64 pu).
    { rewrite (getr_of_eqv _ _ 11 XR2 eq_refl); simp_regs.
      exact (eq_trans (PR1 8 ltac:(unfold callee_saved; lia)) E1_8). }
    assert (SP2 : spZ R2 = bv_unsigned sp - 32) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
    assert (SRC2 : arg_s_src B L1 A1 (spZ R2) m2 pu uri).
    { apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L1 A1 m2 md1
               (rec_record R REC_DESCRIPTORS_PANEL_GET []) O1 b pu uri (spZ R2) SI2 RA).
      - rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
      - rewrite SP2. lia.
      - exact SA. }
    destruct (sarg_facts B L1 A1 (spZ R2) m2 pu uri SRC2) as (NO2 & LX2).
    assert (ROOM2 : room_slots (sb_malloc (sb_shift b A A1) (Z.of_nat (length (sarg uri)) + 1))
                      (Z.of_nat (length (sarg uri)) + 1)).
    { eapply room_slots_mono; [| | exact ROOM].
      - eapply sb_le_trans; [exact (sb_malloc_mono _ _ _ BLE1)|].
        eapply sb_le_trans; apply sb_le_malloc; lia.
      - unfold LMAX in *. lia. }
    apply (sinv_arg_s B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 12384 (bv_unsigned sp) L A mem md O L1 A1 m2 md1 R
             REC_DESCRIPTORS_PANEL_GET O1 b R2 pu uri).
    + exact SI2.
    + rewrite E2_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP2. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    + rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    + rewrite SP2. lia.
    + rewrite E2_4. exact HTP.
    + exact E2_10.
    + exact E2_11.
    + exact SRC2.
    + exact ROOM2.
    + intros L2 A2 regs2 m3 md2 p SI3 EQB INI PR2 FK2.
      rewrite E2_1.
      set (x := sarg uri) in *.
      set (e := rec_entry G_REC REC_SC R) in *.
      pose proof SI3 as (RJ3 & _ & _ & _ & _ & RA3 & _).
      pose proof RJ3 as (HM3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC3 & _).
      rewrite SEGS in HSC3.
      destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
      assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 32)
                      [CB 8 j; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        destruct (FK1 (bv_unsigned sp - 32 + i) ltac:(rewrite SP1; lia)) as [Ea Wa].
        destruct (FK2 (bv_unsigned sp - 32 + i) ltac:(rewrite SP2; lia)) as [Eb Wb].
        split; [rewrite Eb; exact Ea | intros W; apply Wb; apply Wa; exact W]. }
      assert (Q2 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
        by exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) E2_2).
      assert (R3_9 : getr regs2 9 = Z_to_bv 64 e)
        by exact (eq_trans (PR2 9 ltac:(unfold callee_saved; lia)) E2_9).
      pose proof (dpg_rjr_shapes 12384 (bv_unsigned sp) O L A mem md L2 A2 m3 md2 RJ3 GS) as GS3.
      eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2.
        eapply (evt_normalize rsegs); [exact wx_apart_rsegs | exact RA3 |].
        eapply (dpg_after RSO) with (lo := bv_unsigned sp - 12384).
        - apply rw_cells_norm_hi; [exact RA3 | lia | exact FR3].
        - apply stk_norm; [lia | lia |]. intros a Ha. apply HSC3. left. lia.
        - lia.
        - lia.
        - exact (bytes_at_normalize rsegs m3 _ _ RA3 GS3).
        - apply mem_inv_normalize. }
      intros ms4 (can4 & (s4 & Q4 & REL4 & RO4) & EQ4).
      destruct Q4 as (m4n & t0' & t1' & t2' & c3 & c4 & c5 & c6 & c7 & t3' & t4' & t5' & t6' & -> & MU4n & WM4n).
      destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL4) as [EC4 MR4r].
      revert EC4 MR4r RO4 EQ4. generalize (ms_mem can4) as m4. intros m4 EC4 MR4r RO4 EQ4. subst can4.
      pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4 MU4n) as MU4.
      pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4 WM4n) as WM4.
      clear MU4n WM4n MR4r.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
      pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 _ _ b m4 _ SI3 MU4 WM4
                    ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI4.
      assert (E4_1 : getr R4 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
      assert (E4_2 : getr R4 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs; reflexivity).
      assert (E4_10 : getr R4 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs; exact R3_9).
      assert (E4_11 : getr R4 11 = Z_to_bv 64 0x104b4)
        by (rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs; reflexivity).
      assert (E4_12 : getr R4 12 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 12 X4 eq_refl); simp_regs; reflexivity).
      assert (SP4 : spZ R4 = spZ regs) by (unfold spZ; rewrite E4_2; reflexivity).
      assert (RP4 : regs_preserved regs R4).
      { intros r Hr. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 8 \/ r = 9 \/ r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        clear Hr.
        destruct C as [->|[->|[->|C]]].
        - rewrite (getr_of_eqv _ _ (Z_to_bv 5 2) X4 eq_refl); simp_regs. reflexivity.
        - rewrite (getr_of_eqv _ _ (Z_to_bv 5 8) X4 eq_refl); simp_regs. reflexivity.
        - rewrite (getr_of_eqv _ _ (Z_to_bv 5 9) X4 eq_refl); simp_regs. reflexivity.
        - repeat (destruct C as [C|C]; [subst r; dpg_pres X4 XR2 XR1 regs1 regs2 PR1 PR2|]).
          subst r. dpg_pres X4 XR2 XR1 regs1 regs2 PR1 PR2. }
      assert (BLE2 : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length x) + 1)))
        by (rewrite EQB; exact (sb_malloc_mono _ _ _ BLE1)).
      assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
      set (t := snd (rec_answer (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (REC_DESCRIPTORS_PANEL_GET, [x])
                  (daemon_shape "panel_get") false)) in *.
      assert (ROOM3 : room_slots (sb_malloc (sb_malloc (sb_shift b A A2) (Z.of_nat (length t) + 1))
                                   (Z.of_nat (length t) + 1)) (Z.of_nat (length t) + 1)).
      { eapply room_slots_mono; [| | exact ROOM].
        - apply sb_malloc_mono, sb_malloc_mono. exact BLE2.
        - unfold LMAX. lia. }
      pose proof SI4 as (RJ4 & GR4 & ON4 & B14 & B24 & RA4 & F184 & RS4).
      pose proof (dpg_ans_shape m4 RA4) as SHP.
      rewrite <- SEGS in GR4, RA4, F184, SHP.
      pose proof (answer_tail (fx := fx) B API SEGS AX CTX ERRNO_LOW (ANS fx) SLACK 12384 L A regs mem md O L2 A2 R4 m4
                    md2 (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (O1 ++ [(p, Z.of_nat (length x) + 1)]) b
                    (sb_malloc b (Z.of_nat (length x) + 1)) (sb_shift b A A2) e 0x104b4
                    (REC_DESCRIPTORS_PANEL_GET, [x]) (daemon_shape "panel_get") false PRE AK RJ4 E4_1 SP4 RP4 E4_10
                    E4_11 ltac:(rewrite E4_12; reflexivity) GR4 (fun _ => SHP)
                    ltac:(intros _ H; discriminate H)
                    FRM F184 RA4 RS4 eq_refl BLE2 ROOM3 ON4 B14 B24) as TR0.
      rewrite SEGS in TR0.
      eapply SR_mono; [exact TR0|].
      intros c' TR.
      destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
        & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
      unfold descriptors_panel_get_ret.
      exists fx'', L', A', regs', mem', md', (fst (descriptors_panel_get_m R uri)), O',
        (snd (descriptors_panel_get_m R uri)), q.
      split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK'|].
      split; [exact POST'|].
      do 10 (split; [assumption|]).
      split.
      { rewrite SEGS. apply (dpg_shapes_kept _ L A regs mem md _ _ L' A' regs' mem' md' PRK POST'); [|exact GS].
        intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
      repeat (split; [assumption|]). exact RES'.
Qed.

End P.
