(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths, module names and numbers changed; 647 of its 708 lines of code are new or changed and 1005 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/arg_i.v, with its module paths, module names, addresses and numbers changed; 720 of its 819 lines of code are new or changed and 609 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c RecAns
  rec_shape_of_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma sii_pf_dec : forall v, (-2^31 <= v < 2^31)%Z -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros c Hc. unfold pf_dec, dec. unfold pf_bytes.
  assert (P : (10 ^ Z.of_nat (S 9) = 10000000000)%Z) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c)%Z by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Definition SII_FMT : list Z := [37%Z; 100%Z].
Definition SII_PS : list pf_piece := [Pd].

Lemma sii_parse : pf_parse SII_FMT = Some SII_PS.
Proof. reflexivity. Qed.

Lemma sii_text : forall v, pf_text SII_PS [AInt v] = Some (pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma sii_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes (SII_FMT ++ [0%Z])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Definition rom_chk (a : Z) (bs : list byte) : bool :=
  forallb (fun i => ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) &&
     match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error bs i with
     | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
     | _, _ => false
     end) (seq 0 (length bs)).

Lemma rom_chk_at : forall a bs i, rom_chk a bs = true -> (i < length bs)%nat ->
  ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true /\
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros a bs i C Hi. unfold rom_chk in C.
  pose proof (proj1 (forallb_forall _ _) C i ltac:(apply in_seq; lia)) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Cr Cv]. split; [exact Cr|].
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in Cv. f_equal. apply bv_eq. exact Cv.
Qed.

Lemma rom_chk_bytes : forall m a bs, ro_agree rsegs m -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  rom_chk a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RA H0 H1 C. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (rom_chk_at a bs i C Hi) as [Cr Cv]. unfold wa. rewrite (RA _ Cr). exact Cv.
Qed.

Lemma sii_ro_of_inv : forall m, mem_inv rsegs m -> ro_agree rsegs m.
Proof.
  intros m MI x Hx. unfold mrd. destruct (m x) as [b|] eqn:E; [|reflexivity].
  rewrite (MI _ _ E) in Hx. discriminate.
Qed.

Lemma sii_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x103c1 (str_bytes "instance_info"%string).
Proof.
  intros m MI. apply rom_chk_bytes; [exact (sii_ro_of_inv m MI) | lia | cbn; lia | vm_compute; reflexivity].
Qed.

Lemma sii_shape : shape_find shape_rows (str_bytes "instance_info"%string) = 0x108b2%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma sii_run0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16ac4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a0 s1
                     (Z_to_bv 64 9) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp + -24, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp + -24)%Z [C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16aa8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -24, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 24%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 24%nat junk [] [8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma sii_run1 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo id : Z) (canary : word),
  (-2^31 <= id < 2^31)%Z ->
  stk rsegs m lo (bv_unsigned sp + 24) -> (lo + SNPRINTF_K <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  (bv_unsigned sp + 24 < 2^63)%Z ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                               (fc' : bv 32) (m' : word -> option byte) (slack : list byte),
       ms' = MS (mkR (Z_to_bv 64 0x16aec) sp gp tp t0' t1' t2' (Z_to_bv 64 id) a0 a0 (Z_to_bv 64 (bv_unsigned sp + 8))
                     a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs)
       /\ munch [(lo, bv_unsigned sp + 24)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k)
       /\ length slack = (15 - length (dec id))%nat
       /\ bytes_at rsegs m' (bv_unsigned sp + 8)%Z (dec id ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16ac4) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo id canary HV ST LO IE S63 FRM MI TM GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (dec_length id HV) as DL.
  pose proof (sii_pf_dec id HV) as PD.
  assert (TL : length (pf_dec id) = length (dec id)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  carve_frame 16%nat ST.
  carve_frame 8%nat ST.
  clear FR0.
  replace (bv_unsigned sp + 0)%Z with (bv_unsigned sp) in * by lia.
  do 7 step.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp + 8)%Z junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary SII_FMT SII_PS
              [AInt id] (pf_dec id) junk).
    - rewrite unsigned_lit by lia. apply sii_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, SII_FMT. cbn [length]. lia.
    - exact sii_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (sii_text id).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
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
  replace (ret_pc (Z_to_bv 64 0x16ae0)) with (Z_to_bv 64 0x16ae0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (JL : length junk = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec id))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + 8 + Z.of_nat (S (length (pf_dec id))))%Z
                   (skipn (S (length (pf_dec id))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes (pf_dec id ++ [0%Z]) = dec id ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (pf_dec id)) with (pf_bytes (pf_dec id)).
    rewrite PD. reflexivity. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp + 8)%Z
                  (dec id ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec id))) junk)).
  { replace (dec id ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec id))) junk) with
      ((dec id ++ [Z_to_bv 8 0]) ++ skipn (S (length (pf_dec id))) junk)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, <- TL. cbn [length].
    replace (Z.of_nat (length (pf_dec id) + 1)) with (Z.of_nat (S (length (pf_dec id)))) by lia. exact BJT2. }
  assert (MUc : munch [(lo, bv_unsigned sp + 24)]%Z m m2).
  { eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  clear BT BJT BJT2 BJ BJL FR.
  do 3 step.
  apply evt_done.
  do 16 eexists. exists (skipn (S (length (pf_dec id))) junk). split; [reflexivity|].
  split; [exact MUc|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, TL; lia | exact BUF].
Qed.

Lemma sii_run2 : rec_shape_of_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 64 <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z -> (bv_unsigned sp < 2 ^ 63)%Z ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (m' : word -> option byte) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR (Z_to_bv 64 0x16b0c) sp gp tp t0' t1' t2' s0 s1 s1 (Z_to_bv 64 0x108b2) (Z_to_bv 64 0)
                     a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16310) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16aec) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 S63 GS MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  do 4 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "instance_info"%string).
    - exact MI.
    - exact ST.
    - unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (sii_verb m MI)|].
      left. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16afc) by lia. rewrite sii_shape.
  do 4 step.
  apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|]. split; [exact MU2 | exact WM2].
Qed.

Lemma sii_run3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (s1v s0v rav : word),
  rw_cells rsegs m (bv_unsigned sp + 24)%Z [C8 s1v; C8 s0v; C8 rav] -> (bv_unsigned sp + 48 < 2 ^ 64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16b0c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m s1v s0v rav FR HB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 5 step. apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecSeq RecStep
  RecGlue RecTail RecAnsB RecStubU record_c arg_s_c xmalloc_c answer_c sup_instance_info_c.
Local Open Scope Z_scope.

Lemma sii_fpk_trans : forall f1 f2 f3 : YK11.FPState, fp_kept f1 f2 -> fp_kept f2 f3 -> fp_kept f1 f3.
Proof. intros f1 f2 f3 (_ & H1) (C & H2). split; [exact C|]. intros r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma sii_getr_nz : forall r, callee_saved r -> bv_eqb (Z_to_bv 5 r) 0 = false.
Proof.
  intros r Hr. assert (Hk : 0 < r < 32) by (unfold callee_saved in Hr; lia).
  unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia.
Qed.

Lemma sii_pres_tail : forall regs R1 R2 R3 M3,
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  regs_preserved R1 R2 -> Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r)) ->
  (forall r, callee_saved r -> r = 2 \/ r = 8 \/ r = 9 -> reg_get M3 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  regs_preserved regs R3.
Proof.
  intros regs R1 R2 R3 M3 P1 P X3 K1 K2 r Hr.
  pose proof (sii_getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ.
  destruct (Z.eq_dec r 2) as [E|N2]; [exact (K2 r Hr (or_introl E))|].
  destruct (Z.eq_dec r 8) as [E|N8]; [exact (K2 r Hr (or_intror (or_introl E)))|].
  destruct (Z.eq_dec r 9) as [E|N9]; [exact (K2 r Hr (or_intror (or_intror E)))|].
  rewrite (K1 r Hr N2 N8 N9).
  pose proof (P r Hr) as E3. unfold getr in E3. rewrite NZ in E3. rewrite E3.
  pose proof (P1 r Hr N2 N8 N9) as E4. unfold getr in E4. rewrite NZ in E4. exact E4.
Qed.

Ltac sii_pres X :=
  intros rr Hrr N2 N8 N9; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
               rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr N2 N8 N9;
  repeat (destruct CC as [CC|CC]; [subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
    simp_regs; first [reflexivity | unfold getr; reflexivity]|]);
  subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Lemma sii_ans_shape_chk : forall m a x, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length x) + 1 <= 2 ^ 64 ->
  rom_chk a (x ++ [Z_to_bv 8 0]) = true -> no0 x -> Z.of_nat (length x) <= LMAX -> fits x ->
  ans_shape rsegs m a x.
Proof.
  intros m a x RA H0 H1 C N0 LX FT. pose proof (length_app x [Z_to_bv 8 0]) as LA. cbn [length] in LA.
  split; [apply rom_chk_bytes; [exact RA | lia | rewrite LA; lia | exact C]|].
  split; [exact N0|]. split; [exact LX|]. split; [exact FT|].
  intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  exact (proj1 (rom_chk_at a _ (Z.to_nat i) C ltac:(rewrite LA; lia))).
Qed.

Lemma sii_ans_shape : forall m, ro_agree rsegs m -> ans_shape rsegs m 0x108b2 (daemon_shape "instance_info"%string).
Proof.
  intros m RA. change (daemon_shape "instance_info"%string) with (shape_of (bstr "instance_info"%string)).
  destruct (shape_of_facts (bstr "instance_info"%string)) as (FT & _ & L78 & N0).
  apply sii_ans_shape_chk; [exact RA | lia | lia | vm_compute; reflexivity | exact N0 | unfold LMAX; lia | exact FT].
Qed.

Lemma sii_inst_len : (length (inst (daemon_shape "instance_info"%string)) <= 16)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Lemma sii_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length (inst x)) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - lia.
  - assert (E : r_code (rec_record R fn As) = r_code R)
      by (unfold rec_record; destruct (Nat.ltb (length (r_calls R)) 16); reflexivity).
    rewrite E. pose proof (resp_length (r_code R) H). lia.
Qed.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RSO : rec_shape_of_contract.
Hypothesis ANS : answer_contract B API.

Lemma sii_rjr_shapes : forall K S O L A mem md Lc Ac mc mdc,
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
  assert (NR : ~ rec_area (G_SHAPES + i)) by (unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES; lia).
  rewrite <- SEGS. exact (proj1 (HF _ (or_intror (conj I1 (conj I2 I3))) NS I4 NR)).
Qed.

Lemma sii_tail : forall L A regs mem md (O : list (Z * Z)) L1 A1 regs1 mem1 md1 (R1 : rstate) (O1 : list (Z * Z))
    b bpre c sh e x chg,
  call_pre_t B API SUP_INSTANCE_INFO_K L A regs mem md ->
  sinv B API SUP_INSTANCE_INFO_K (spZ regs) L A mem md O L1 A1 mem1 md1 R1 O1 b ->
  getr regs1 1 = Z_to_bv 64 0x16b0c -> getr regs1 2 = Z_to_bv 64 (spZ regs - 48) ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs mem1 (spZ regs - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  getr regs1 10 = Z_to_bv 64 c -> getr regs1 11 = Z_to_bv 64 sh -> chg = negb (bv_unsigned (getr regs1 12) =? 0) ->
  (r_refuse R1 = 0 -> ans_shape rsegs mem1 sh x) ->
  (r_refuse R1 = 0 -> chg = true -> ans_entry R1 c e) ->
  frm_zero fp_csr ->
  sb_le (sb_shift b A A1) bpre ->
  room_slots (sb_malloc (sb_malloc (sb_shift b A A1) (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
                (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
             (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 ANSWER) mem1 (seg_rom rsegs)) md1)
    (tail_ret B API SUP_INSTANCE_INFO_K L A regs mem md O R1 e x chg b bpre).
Proof using SEGS ERRNO_LOW AX CTX SLACK ANS.
  intros L A regs mem md O L1 A1 regs1 mem1 md1 R1 O1 b bpre c sh e x chg
    PRE SI RA1 SP1 PRS FR A10 A11 ACH SHAPE ENTRY FRM BLE ROOM1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (R & GREP1 & P1 & P2 & P5 & RO1 & F18 & RES1).
  pose proof R as R0.
  destruct R0 as (HM1 & HWA & HW1 & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  pose proof PRE as ((HM & _ & _ & HRA & HAL & HCE & H63 & _ & HTP & _) & HTS).
  assert (KV : SUP_INSTANCE_INFO_K = 12432) by reflexivity.
  assert (AKV : ANSWER_K = 12384) by reflexivity.
  set (S := spZ regs) in *.
  assert (SPV : spZ regs1 = S - 48) by (unfold spZ; rewrite SP1; apply unsigned_lit; lia).
  assert (PRE1 : call_pre_t B API ANSWER_K L1 A1 regs1 mem1 md1).
  { split; [|rewrite SPV; lia].
    apply (call_pre_k_of_rjr B (aa_MR API) SUP_INSTANCE_INFO_K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1
             ANSWER_K regs1 R).
    - rewrite RA1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SPV. replace (S - 48) with (S + (-3) * 16) by ring. rewrite Z.mod_add by lia. exact HAL.
    - lia.
    - rewrite SPV. lia.
    - rewrite SPV. lia.
    - exact (eq_trans (PRS 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) HTP). }
  pose proof ANS as ANS'. unfold answer_contract in ANS'. rewrite SEGS in ANS'.
  eapply SR_bind.
  { apply (ANS' L1 A1 regs1 mem1 md1 R1 O1 c sh e x chg (sb_shift b A A1) PRE1 A10 A11 ACH GREP1 SHAPE);
      [|exact FRM | exact F18 | exact RES1 | exact ROOM1 | exact RO1].
    intros Hr Hc. split; [exact (ENTRY Hr Hc)|]. intros q k a Hq Ha. exact (SLACK L1 A1 mem1 md1 q k a HM1 Hq Ha). }
  intros c' RET. unfold answer_ret in RET.
  destruct RET as (fx' & L' & A' & regs' & mem' & md' & p1 & p2 & old & O' & EC & FPK & OLDB & POST & A0 & NE12 & AL1 & AL2
    & FR1 & FR2 & (c1 & c2 & HB & HIFF & NI1 & NI2) & BK & UBK & GREP' & HO' & HO2 & HBC & BY1 & BY2 & RA' & F18' & GK
    & INIT & REG & GR' & RES').
  rewrite SEGS in EC. subst c'.
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  set (n := Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) in *.
  assert (HB' : exists kold, (old = 0 /\ blocks L1 A1 = c1 ++ c2) \/
                             (old <> 0 /\ In (old, kold) O1 /\ blocks L1 A1 = c1 ++ (old, kold) :: c2)).
  { destruct HB as [H|(k & H)]; [exists 0; left; exact H | exists k; right; exact H]. }
  destruct HB' as [kold HB'].
  assert (STAB : forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
            In (p, k) (user_blocks A1) /\ ptr_addr L1 p = ptr_addr L p).
  { intros p k Hu Hno.
    split; [exact (rjr_in_cur B (aa_MR API) SUP_INSTANCE_INFO_K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1
                     p k R Hu Hno)|].
    exact (ptr_addr_stable A L L1 p k HWA Hu HL). }
  assert (R2 : rjr B (aa_MR API) SUP_INSTANCE_INFO_K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md').
  { apply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW SUP_INSTANCE_INFO_K S rec_area (fun pn => In pn O) L A mem md
             L1 A1 mem1 md1 ANSWER_K regs1 ans_writes (fun a => a = old) L' A' regs' mem' md' R POST).
    - rewrite SPV. lia.
    - rewrite SPV. lia.
    - intros a Ha _.
      unfold ans_writes, rec_area, G_REC, REC_SC, OFF_ANSWER, OFF_STATE, SC_SIZE, REC_SIZE in *.
      split; [lia|]. lia.
    - intros p k Hu Hno Hk E.
      destruct (STAB p k Hu Hno) as [Hu1 Ep].
      pose proof (mr_blocks_range B (aa_MR API) LAWS L A mem md p k HM Hu) as Hr.
      destruct HB' as [(E0 & _)|(NZ & Ho & EB)]; [lia|].
      assert (Hob : In (old, kold) (blocks L1 A1)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
      pose proof (user_in_blocks L1 A1 p k Hu1) as Hb. rewrite Ep, E in Hb.
      pose proof (rec_rep_pos rsegs G_REC REC_SC L1 A1 mem1 R1 O1 (old, kold) GREP1 Ho) as Hk0. cbn [snd] in Hk0.
      assert (Ek : k = kold) by exact (blocks_same_addr B (aa_MR API) LAWS L1 A1 mem1 md1 old k kold HM1 Hb Hob Hk Hk0).
      subst k. rewrite E in Hno.
      destruct (P1 _ Ho) as [H|H]; [exact (Hno H)|]. apply H. rewrite <- E. exact (user_in_blocks L A p kold Hu).
    - intros p k Hu Hu1 Hu'.
      destruct (in_dec pair_dec (ptr_addr L p, k) O) as [H|H]; [exact H|]. exfalso. apply Hu'. apply UBK; [exact Hu1|].
      rewrite (ptr_addr_stable A L L1 p k HWA Hu HL). intros Ho.
      destruct (P1 _ Ho) as [H'|H']; [exact (H H') | exact (H' (user_in_blocks L A p k Hu))].
    - exact REG.
    - rewrite INIT. discriminate. }
  assert (FR' : rw_cells rsegs mem' (S - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs mem1); [exact FR|]. intros i Hi. cbn in Hi.
    pose proof PF as PF'. rewrite SEGS in PF'.
    destruct (PF' (S - 24 + i)) as [E1 E2].
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L1 A1 mem1 md1 _ HM1 Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L' A' mem' md' _ PM Ho). lia.
    - unfold scratch_k. rewrite SPV. intros [H|H]; lia.
    - unfold ans_writes, G_REC, OFF_ANSWER, OFF_STATE. lia.
    - split; [exact E1 | apply E2]. }
  destruct (mr_model B _ LAWS L' A' mem' md' PM) as (Hh' & Hl' & _).
  rewrite RA1.
  eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs' 2 = Z_to_bv 64 (S - 48)) by exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) SP1).
    rewrite Q2.
    eapply sii_run3 with (s1v := reg_get regs 9) (s0v := reg_get regs 8) (rav := reg_get regs 1).
    - rewrite unsigned_lit by lia. replace (S - 48 + 24) with (S - 24) by ring. exact FR'.
    - rewrite unsigned_lit by lia. lia. }
  intros ms5 (can5 & Q5 & EQ5). subst can5.
  destruct (eqv_mkst (fx := fx') _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5). clear EQ5.
  assert (RP5 : regs_preserved regs R5).
  { apply (sii_pres_tail regs regs1 regs' R5 _ PRS PR X5).
    - intros rr Hrr N2 N8 N9. unfold callee_saved in Hrr.
      assert (CC : rr = 3 \/ rr = 4 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
                   rr = 25 \/ rr = 26 \/ rr = 27) by lia.
      clear Hrr N2 N8 N9.
      repeat (destruct CC as [CC|CC]; [subst rr; simp_regs; reflexivity|]). subst rr; simp_regs; reflexivity.
    - intros rr _ [CC|[CC|CC]]; subst rr; simp_regs.
      + rewrite unsigned_lit by lia. replace (S - 48 + 48) with S by ring. exact (Z_to_bv_lit_self (reg_get regs 2)).
      + reflexivity.
      + reflexivity. }
  pose proof (rjr_final B (aa_MR API) CTX SUP_INSTANCE_INFO_K rec_area (fun pn => In pn O) (fun a => In a (map fst O))
                L A regs mem md L' A' R5 mem' md' (proj1 PRE) R2 RP5 ltac:(intros a k G; exact (in_map fst O (a, k) G)))
    as FIN.
  pose proof (rjr_others_kept B (aa_MR API) SUP_INSTANCE_INFO_K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md' O
                R2 (fun pn H => H)) as OK.
  destruct (tail_owns_blocks (blocks L A) (blocks L1 A1) (blocks L' A') O O1 O' c1 c2 old kold p1 p2 n
              P1 P2 P5 HB' NI1 HO' HBC) as [OWN BLK].
  assert (Hq : In (p2, n) (blocks L' A')) by (apply HIFF; right; right; reflexivity).
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  apply SR_ret. unfold tail_ret.
  exists fx', L', A', R5, mem', md', O', p2.
  split; [rewrite RP, SEGS; reflexivity|].
  split; [exact FPK|]. split; [exact FIN|].
  split; [rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact A0|].
  split; [exact GREP'|]. split; [exact OWN|].
  split; [exact BLK|]. split; [exact Hq|]. split; [exact FR2|].
  split; [intros Hin; apply in_map_iff in Hin as (pn & Epn & Hpn); exact (HO2 pn Hpn Epn)|].
  split; [exact BY2|]. split; [exact OK|].
  split.
  { intros p0 k0 Hu0 Hno0.
    enough (D : ptr_addr L p0 + k0 <= p2 \/ p2 + n <= ptr_addr L p0) by (unfold n in D; lia).
    revert p0 k0 Hu0 Hno0.
    apply (q_apart_tail B (aa_MR API) LAWS (ms_segs B) L A mem L' A' mem' md' O p2 n PM OK Hq).
    intros p k Hu Hno. destruct (STAB p k Hu Hno) as [Hu1 Ep].
    apply (tail_q_distinct (blocks L A) (blocks L1 A1) O O1 c1 c2 old kold p2 n (ptr_addr L p, k) P1 HB' NI2).
    - exact (user_in_blocks L A p k Hu).
    - exact Hno.
    - rewrite <- Ep. exact (user_in_blocks L1 A1 p k Hu1). }
  split; [exact RA'|]. split; [exact F18'|]. split; [exact INIT|]. split; [lia|].
  rewrite <- (sb_shift_trans b A A1 A').
  split; [eapply sb_le_trans; [exact GR' | apply sb_malloc_mono; apply sb_malloc_mono; exact BLE] | exact RES'].
Qed.

Lemma sii_mid2 : forall L A regs mem md (O : list (Z * Z)) L4 A4 regs4 m4 md4 (R4 : rstate) (O4 : list (Z * Z))
    b bpre slot e,
  call_pre_t B API SUP_INSTANCE_INFO_K L A regs mem md ->
  sinv B API SUP_INSTANCE_INFO_K (spZ regs) L A mem md O L4 A4 m4 md4 R4 O4 b ->
  getr regs4 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs4 9 = Z_to_bv 64 slot ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs m4 (spZ regs - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  frm_zero fp_csr ->
  sb_le (sb_shift b A A4) bpre ->
  room_slots (sb_malloc (sb_malloc (sb_shift b A A4)
                 (Z.of_nat (length (snd (rec_answer R4 e (daemon_shape "instance_info"%string) false))) + 1))
                 (Z.of_nat (length (snd (rec_answer R4 e (daemon_shape "instance_info"%string) false))) + 1))
             (Z.of_nat (length (snd (rec_answer R4 e (daemon_shape "instance_info"%string) false))) + 1) ->
  SR rsegs (mkCfg (mkst regs4 (Z_to_bv 64 0x16aec) m4 (seg_rom rsegs)) md4)
    (tail_ret B API SUP_INSTANCE_INFO_K L A regs mem md O R4 e (daemon_shape "instance_info"%string) false b bpre).
Proof using SEGS ERRNO_LOW GOWN AX CTX SLACK RIMG RSO ANS.
  intros L A regs mem md O L4 A4 regs4 m4 md4 R4 O4 b bpre slot e PRE SI SP4 S94 PRS FR GS FRM BLE ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as ((HM & _ & _ & HRA & HAL & HCE & H63 & _ & HTP & _) & HTS).
  assert (KV : SUP_INSTANCE_INFO_K = 12432) by reflexivity.
  set (S := spZ regs) in *.
  pose proof SI as (RJ & GR4 & _ & _ & _ & RA4 & F184 & _).
  pose proof RJ as (HM4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC4 & _).
  rewrite SEGS in HSC4.
  destruct (mr_model B _ LAWS L4 A4 m4 md4 HM4) as (Hh4 & Hl4 & _).
  pose proof (sii_rjr_shapes SUP_INSTANCE_INFO_K S O L A mem md L4 A4 m4 md4 RJ GS) as GS4.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  pose proof (bytes_at_normalize_cj_low rsegs m4 G_SHAPES g_shapes_bytes RA4
    ltac:(rewrite GL; unfold G_SHAPES, TASK_SIZE; lia) GS4) as GSn.
  assert (STn : stk rsegs (normalize_cj rsegs m4) (S - 12432) (S - 48)).
  { apply stk_normalize_cj; [lia | lia | intros a Ha; apply HSC4; left; lia]. }
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs4 2 = Z_to_bv 64 (S - 48)) by exact SP4.
    rewrite Q2.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA4 |].
    eapply (sii_run2 RSO) with (lo := S - 12432).
    - rewrite unsigned_lit by lia. exact STn.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - exact GSn.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m4)). }
  intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
  destruct Q5 as (m5n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU5n & WM5n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL5) as [EC5 MR5r].
  revert EC5 MR5r RO5 EQ5. generalize (ms_mem can5) as m5. intros m5 EC5 MR5r RO5 EQ5. subst can5.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m4 RA4) MR5r RO5 MU5n) as MU5.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m4 RA4) MR5r RO5 WM5n) as WM5.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  clear MU5n WM5n EQ5 MR5r.
  rewrite unsigned_lit in MU5 by lia.
  pose proof (sinv_stack B API SEGS GOWN AX SUP_INSTANCE_INFO_K S L A mem md O L4 A4 m4 md4 R4 O4 b m5 _ SI MU5 WM5
                ltac:(intros a Ra Hm; cbn [outside] in Hm; lia)) as SI5.
  assert (FR5 : rw_cells rsegs m5 (S - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m4 m5 _ _ FR MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  apply (sii_tail L A regs mem md O L4 A4 R5 m5 md4 R4 O4 b bpre slot 0x108b2 e (daemon_shape "instance_info"%string) false
           PRE SI5).
  - rewrite (getr_of_eqv _ _ 1 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 2 X5 eq_refl). simp_regs. reflexivity.
  - intros rr Hrr N2 N8 N9. rewrite <- (PRS rr Hrr N2 N8 N9). revert rr Hrr N2 N8 N9. sii_pres X5.
  - exact FR5.
  - rewrite (getr_of_eqv _ _ 10 X5 eq_refl). simp_regs. exact S94.
  - rewrite (getr_of_eqv _ _ 11 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 12 X5 eq_refl). simp_regs. reflexivity.
  - intros _. apply sii_ans_shape. pose proof SI5 as (_ & _ & _ & _ & _ & RA5 & _). exact RA5.
  - intros _ H. discriminate H.
  - exact FRM.
  - exact BLE.
  - exact ROOM.
Qed.

End T.

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
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.
Hypothesis REC : record_contract B API.
Hypothesis ARGS : forall fx0 : YK11.FPState, arg_s_contract (fx := fx0) B API.
Hypothesis SNP : snprintf_contract.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis ANS : forall fx0 : YK11.FPState, answer_contract (fx := fx0) B API.

Lemma sii_shapes_kept : forall K L A regs mem md E excl L' A' regs' mem' md',
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

Lemma sii_mid1 : forall L A regs mem md id (R : rstate) (O : list (Z * Z)) b L2 A2 regs2 m2 md2 (O2 : list (Z * Z)),
  call_pre_t B API SUP_INSTANCE_INFO_K L A regs mem md -> -2 ^ 31 <= id < 2 ^ 31 ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_instance_info_sizes id (snd (sup_instance_info_m R id)))) 17 ->
  -2^31 <= r_code R < 2^31 ->
  sinv B API SUP_INSTANCE_INFO_K (spZ regs) L A mem md O L2 A2 m2 md2 (rec_record R REC_INSTANCE_INFO []) O2 b ->
  sb_le (sb_shift b A A2) b ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 8 = Z_to_bv 64 id ->
  getr regs2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs m2 (spZ regs - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR rsegs (mkCfg (mkst regs2 (Z_to_bv 64 0x16ac4) m2 (seg_rom rsegs)) md2)
    (sup_instance_info_ret B API L A regs mem md id R O b).
Proof using SEGS ERRNO_LOW GFACT GOWN AX CTX SLACK RIMG RFREE ARGS SNP RSO ANS.
  intros L A regs mem md id R O b L2 A2 regs2 m2 md2 O2 PRE HID GS FRM ROOM HCODE SI BLE2 SP2 S82 A02 PRS FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as ((HM & _ & _ & HRA & HAL & HCE & H63 & _ & HTP & _) & HTS).
  assert (KV : SUP_INSTANCE_INFO_K = 12432) by reflexivity.
  set (S := spZ regs) in *.
  change (snd (sup_instance_info_m R id)) with
    (snd (rec_answer (rec_record R REC_INSTANCE_INFO [dec id]) (REC_INSTANCE_INFO, [dec id])
            (daemon_shape "instance_info"%string) false)) in ROOM.
  unfold sup_instance_info_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  pose proof (sii_len R REC_INSTANCE_INFO [dec id] (daemon_shape "instance_info"%string) false HCODE) as LT.
  pose proof sii_inst_len as IL.
  pose proof (dec_length id HID) as DL.
  pose proof SI as (RJ & GR2 & _ & _ & _ & RA2 & F182 & _).
  pose proof RJ as (HM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC2 & _).
  rewrite SEGS in HSC2.
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM2) as (Hh2 & Hl2 & _).
  pose proof F182 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs m2 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs m2 snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_normalize_cj_low rsegs m2 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA2
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs m2 snprintf_c.GUARD (Mem.le8 canary) RA2
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (STn : stk rsegs (normalize_cj rsegs m2) (S - 12432) (S - 24)).
  { apply stk_normalize_cj; [lia | lia | intros a Ha; apply HSC2; left; lia]. }
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs2 2 = Z_to_bv 64 (S - 48)) by exact SP2.
    assert (Q8 : reg_get regs2 8 = Z_to_bv 64 id) by exact S82.
    rewrite Q2, Q8.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA2 |].
    eapply (sii_run1 SNP) with (lo := S - 12432) (canary := canary).
    - exact HID.
    - rewrite unsigned_lit by lia. replace (S - 48 + 24) with (S - 24) by ring. exact STn.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact GGn.
    - exact GWn. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m3n & slack
    & -> & MU3n & WM3n & MI3n & FRM1 & FK1 & SL & BUF3n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA2) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA2) MR3r RO3 WM3n) as WM3.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR3r BUF3n) as BUF3.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ3) as (R3 & -> & X3).
  clear MU3n WM3n MI3n BUF3n EQ3 MR3r.
  rewrite unsigned_lit in MU3, BUF3 by lia.
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x16aec) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (S - 48)) by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 9 X3 eq_refl); simp_regs; exact A02).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact A02).
  assert (E3_11 : getr R3 11 = Z_to_bv 64 (S - 40)).
  { rewrite (getr_of_eqv _ _ 11 X3 eq_refl). simp_regs. rewrite unsigned_lit by lia. f_equal. lia. }
  assert (SP3 : spZ R3 = S - 48) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (PRS3 : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros rr Hrr N2 N8 N9. rewrite <- (PRS rr Hrr N2 N8 N9). revert rr Hrr N2 N8 N9. sii_pres X3. }
  assert (FKA : fp_kept fx (mkFP F1 fc1)).
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  pose proof (sinv_stack B API SEGS GOWN AX SUP_INSTANCE_INFO_K S L A mem md O L2 A2 m2 md2 _ _ b m3 _ SI MU3 WM3
                ltac:(intros a Ra Hm; cbn [outside] in Hm; lia)) as SI3.
  assert (FR3 : rw_cells rsegs m3 (S - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  apply (sinv_arg_s (fx := mkFP F1 fc1) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS (mkFP F1 fc1))
           SUP_INSTANCE_INFO_K S L A mem md O L2 A2 m3 md2 R REC_INSTANCE_INFO O2 b R3 (S - 40) (Some (dec id)) _ SI3).
  - rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP3. replace (S - 48) with (S + (-3) * 16) by ring. rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP3. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
  - rewrite SP3. lia.
  - exact (eq_trans (PRS3 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) HTP).
  - exact E3_10.
  - exact E3_11.
  - cbn [arg_s_src]. rewrite SEGS.
    split; [lia|]. split; [apply dec_no0|]. split; [unfold LMAX; lia|].
    exists slack. split; [replace (S - 40) with (S - 48 + 8) by ring; exact BUF3|].
    assert (SLZ : Z.of_nat (length slack) = 15 - Z.of_nat (length (dec id))) by (rewrite SL; lia).
    split.
    { rewrite SLZ. pose proof (Z.div_mod S 16 ltac:(lia)) as DS. rewrite HAL, Z.add_0_r in DS.
      Z.div_mod_to_equations. lia. }
    split; [right; rewrite SP3; lia|].
    left. rewrite SP3. split; lia.
  - cbn [sarg]. eapply room_slots_mono; [| | exact ROOM].
    + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE2|].
      eapply sb_le_trans; apply sb_le_malloc; lia.
    + lia.
  - intros L4 A4 regs4 m4 md4 p SI4 SB4 INI4 RP4 FK4.
    cbn [sarg] in SI4, SB4.
    rewrite E3_1.
    assert (FR4 : rw_cells rsegs m4 (S - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
      destruct (FK4 (S - 24 + i) ltac:(rewrite SP3; lia)) as [K1 K2]. split; [exact K1 | exact (proj1 K2)]. }
    assert (BLE4 : sb_le (sb_shift b A A4) (sb_malloc b (Z.of_nat (length (dec id)) + 1))).
    { rewrite SB4. apply sb_malloc_mono. exact BLE2. }
    eapply SR_mono.
    { apply (sii_mid2 (fx := mkFP F1 fc1) B API SEGS ERRNO_LOW GOWN AX CTX SLACK RIMG RSO (ANS (mkFP F1 fc1))
               L A regs mem md O L4 A4 regs4 m4 md4 (rec_record R REC_INSTANCE_INFO [dec id])
               (O2 ++ [(p, Z.of_nat (length (dec id)) + 1)]) b (sb_malloc b (Z.of_nat (length (dec id)) + 1))
               (rec_entry G_REC REC_SC R) (REC_INSTANCE_INFO, [dec id]) PRE SI4).
      - exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E3_2).
      - exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E3_9).
      - intros rr Hrr N2 N8 N9. rewrite (RP4 rr Hrr). exact (PRS3 rr Hrr N2 N8 N9).
      - exact FR4.
      - exact GS.
      - cbn [fp_csr]. exact FRM1.
      - exact BLE4.
      - eapply room_slots_mono; [| | exact ROOM].
        + apply sb_malloc_mono, sb_malloc_mono. exact BLE4.
        + lia. }
    intros c' TR.
    destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
      & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
    exists fx'', L', A', regs', mem', md', (fst (sup_instance_info_m R id)), O', (snd (sup_instance_info_m R id)), q.
    split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact (sii_fpk_trans _ _ _ FKA FK')|].
    split; [exact POST'|].
    do 10 (split; [assumption|]).
    split.
    { rewrite SEGS. apply (sii_shapes_kept _ L A regs mem md _ _ L' A' regs' mem' md' (proj1 PRE) POST'); [|exact GS].
      intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
    repeat (split; [assumption|]). exact RES'.
Qed.

Theorem sup_instance_info_holds : sup_instance_info_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN AX CTX SLACK RIMG RFREE REC ARGS SNP RSO ANS.
  unfold sup_instance_info_contract.
  intros L A regs mem md id R O b PRE A0 HID GS GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (KV : SUP_INSTANCE_INFO_K = 12432) by reflexivity.
  rewrite SEGS in GS, GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API SUP_INSTANCE_INFO_K L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (_ & _ & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 12432) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    eapply sii_run0; [exact ST | lia | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16ac4) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact A0).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 REC_INSTANCE_INFO)
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (PRS1 : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by sii_pres X1.
  pose proof (sinv_stack B API SEGS GOWN AX SUP_INSTANCE_INFO_K (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0
                MU1 WM1 ltac:(intros a Ra Hm; cbn [outside] in Hm; lia)) as SI1.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC SUP_INSTANCE_INFO_K (bv_unsigned sp) L A mem md O L A m1 md R O b R1
           REC_INSTANCE_INFO _ SI1).
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL.
  - rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - rewrite E1_4. exact HTP.
  - exact E1_10.
  - unfold REC_FN_COUNT, REC_INSTANCE_INFO. lia.
  - intros L2 A2 regs2 m2 md2 O2 SI2 BLE2 RP2 R10 FK2.
    rewrite E1_1.
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
      destruct (FK2 (bv_unsigned sp - 24 + i) ltac:(rewrite SP1; lia)) as [K1 K2]. split; [exact K1 | exact (proj1 K2)]. }
    rewrite sb_shift_refl in BLE2.
    apply (sii_mid1 L A regs mem md id R O b L2 A2 regs2 m2 md2 O2 PRE HID GS FRM ROOM HCODE SI2 BLE2).
    + exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E1_2).
    + exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E1_8).
    + exact R10.
    + intros rr Hrr N2 N8 N9. rewrite (RP2 rr Hrr). exact (PRS1 rr Hrr N2 N8 N9).
    + exact FR2.
Qed.

End P.
