(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths, module names, addresses and numbers changed; 617 of its 717 lines of code are new or changed and 2642 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_shape_of_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma scc_pf_dec : forall c, -2^31 <= c < 2^31 -> pf_bytes (pf_dec c) = dec c.
Proof.
  intros c Hc. unfold pf_dec, dec, pf_bytes.
  assert (P : 10 ^ Z.of_nat (S 9) = 10000000000) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c) by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Lemma scc_fmt : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes ([37; 100] ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma scc_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1041e (str_bytes "chain_clear"%string).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma scc_shape : shape_find shape_rows (str_bytes "chain_clear"%string) = 0x10417.
Proof. vm_compute. reflexivity. Qed.

Lemma scc_pro :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x40000 <= lo ->
  evt rsegs (fun ms' => exists m' junk,
       ms' = MS (mkR (Z_to_bv 64 0x16fdc) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 a0 s1 (Z_to_bv 64 18)
                     a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [CB 24 junk; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16fc0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [24; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma scc_mid : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo id : Z) (canary : word) (junk : list byte),
  -2^31 <= id < 2^31 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + SNPRINTF_K <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bv_unsigned sp + 24 < 2 ^ 63 ->
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 16 junk] ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                               (fc' : bv 32) (m' : word -> option byte) (slack : list byte),
       ms' = MS (mkR (Z_to_bv 64 0x17004) sp gp tp t0' t1' t2' (Z_to_bv 64 id) a0 a0 (Z_to_bv 64 (bv_unsigned sp + 8))
                     a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs)
       /\ munch [(lo, bv_unsigned sp); (bv_unsigned sp + 8, bv_unsigned sp + 8 + Z.of_nat (length (dec id)) + 1)] m m'
       /\ wmono rsegs m m' /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
       /\ length slack = (15 - length (dec id))%nat
       /\ bytes_at rsegs m' (bv_unsigned sp + 8) (dec id ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16fdc) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo id canary junk HID ST LO LO2 S63 BUF FRM MI TM GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K in LO.
  pose proof (dec_length id HID) as DL.
  pose proof (scc_pf_dec id HID) as PB.
  assert (PL : length (pf_dec id) = length (dec id)) by (rewrite <- PB; unfold pf_bytes; symmetry; apply length_map).
  assert (BJ : bytes_at rsegs m (bv_unsigned sp + 8) junk).
  { destruct BUF as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (JL : length junk = 16%nat) by (destruct BUF as [[[HJ _] _] _]; exact HJ).
  do 7 step.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary [37; 100] [Pd]
              [AInt id] (pf_dec id) junk).
    - rewrite unsigned_lit by lia. apply scc_fmt. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END. cbn [length]. lia.
    - reflexivity.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HID | apply lit_mod32].
    - cbn. rewrite app_nil_r. reflexivity.
    - rewrite !unsigned_lit by lia. exact BUF.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - right. rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - exact ST.
    - unfold SNPRINTF_K in *. lia.
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
  rewrite !unsigned_lit in MU2 by lia. rewrite !unsigned_lit in BT by lia.
  change (Z.to_nat (16 - 1)) with 15%nat in BT, MU2.
  rewrite (firstn_all2 (n := 15%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 94200)) with (Z_to_bv 64 94200) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec id))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + 8 + Z.of_nat (S (length (pf_dec id))))
                   (skipn (S (length (pf_dec id))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PBT : pf_bytes (pf_dec id ++ [0]) = dec id ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (pf_dec id)) with (pf_bytes (pf_dec id)).
    rewrite PB. reflexivity. }
  rewrite PBT in BT.
  assert (BUF2 : bytes_at rsegs m2 (bv_unsigned sp + 8) (dec id ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec id))) junk)).
  { replace (dec id ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec id))) junk) with
      ((dec id ++ [Z_to_bv 8 0]) ++ skipn (S (length (pf_dec id))) junk) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, <- PL. cbn [length].
    replace (Z.of_nat (length (pf_dec id) + 1)) with (Z.of_nat (S (length (pf_dec id)))) by lia. exact BJT2. }
  rewrite PL in MU2.
  clear BT BJT BJT2 BJ.
  do 3 step.
  apply evt_done. do 16 eexists. exists (skipn (S (length (pf_dec id))) junk). split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, PL; lia | exact BUF2].
Qed.

Lemma scc_after : rec_shape_of_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> 0x40000 <= lo -> bv_unsigned sp < 2 ^ 63 ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x17024) sp gp tp t0' t1' t2' s0 s1 s1 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                     a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16310) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17004) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 S63 GS MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  do 4 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "chain_clear"%string).
    - exact MI.
    - exact ST.
    - unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite !unsigned_lit by lia. split; [exact (scc_verb m MI)|].
      left. unfold REC_SHAPE_OF_FRAME. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x17014) by lia. rewrite scc_shape.
  do 4 step.
  apply evt_done. exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
  split; [reflexivity|]. split; [exact MU2 | exact WM2].
Qed.

Lemma scc_epi :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 sv0 sv1 : word),
  rw_cells rsegs m (bv_unsigned sp + 24) [C8 sv1; C8 sv0; C8 ra0] -> bv_unsigned sp + 48 = bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 sv0 sv1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17024) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 sv0 sv1 FR HS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
  do 5 step.
  replace (Z_to_bv 64 (bv_unsigned sp + 48)) with sp0 by (rewrite HS; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecSeq RecStep RecGlue RecTail RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import record_c arg_s_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import sup_chain_clear_c.
Local Open Scope Z_scope.

Lemma scc_tlen : forall R1 e x chg, -2^31 <= r_code R1 < 2^31 ->
  (length (snd (rec_answer R1 e x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R1 e x chg H. rewrite rec_answer_text. destruct (r_refuse R1 =? 0).
  - pose proof (inst_length x). lia.
  - pose proof (resp_length (r_code R1) H). lia.
Qed.

Lemma scc_host : forall m, ro_agree rsegs m -> ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
Proof.
  intros m RA.
  assert (RO : forall i, 0 <= i <= 6 -> ro_addr rsegs (Z_to_bv 64 (0x10417 + i)) = true)
    by (intros i Hi; apply rs_ro_rsegs; lia).
  split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    unfold wa. rewrite (RA _ (RO (Z.of_nat i) ltac:(lia))).
    assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
  - split; [apply no0_nz; vm_compute; reflexivity|]. split; [cbn; unfold LMAX; lia|].
    split; [apply fits_shape_set; left; reflexivity|]. intros i Hi. apply RO. cbn in Hi. lia.
Qed.

Lemma scc_fpk : forall f1 f2 f3 : YK11.FPState, fp_kept f1 f2 -> fp_kept f2 f3 -> fp_kept f1 f3.
Proof. intros f1 f2 f3 (_ & H1) (C & H2). split; [exact C|]. intros r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma scc_nz : forall r, callee_saved r -> bv_eqb (Z_to_bv 5 r) 0 = false.
Proof.
  intros r Hr. assert (Hk : 0 < r < 32) by (unfold callee_saved in Hr; lia).
  unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia.
Qed.

Lemma scc_keep : forall regs Rp R M,
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr Rp (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  Regs6ss.xregs_eqv M R ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> reg_get M (Z_to_bv 5 r) = reg_get Rp (Z_to_bv 5 r)) ->
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
  intros regs Rp R M KP X KM r Hr N2 N8 N9. pose proof (scc_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X NZ), (KM r Hr N2 N8 N9), <- (KP r Hr N2 N8 N9). unfold getr. rewrite NZ. reflexivity.
Qed.

Lemma scc_pres_tail : forall regs R1 R2 R3 M3,
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  regs_preserved R1 R2 -> Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r)) ->
  (forall r, callee_saved r -> r = 2 \/ r = 8 \/ r = 9 -> reg_get M3 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  regs_preserved regs R3.
Proof.
  intros regs R1 R2 R3 M3 P1 P X3 K1 K2 r Hr.
  pose proof (scc_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ.
  destruct (Z.eq_dec r 2) as [E|N2]; [exact (K2 r Hr (or_introl E))|].
  destruct (Z.eq_dec r 8) as [E|N8]; [exact (K2 r Hr (or_intror (or_introl E)))|].
  destruct (Z.eq_dec r 9) as [E|N9]; [exact (K2 r Hr (or_intror (or_intror E)))|].
  rewrite (K1 r Hr N2 N8 N9).
  pose proof (P r Hr) as E3. unfold getr in E3. rewrite NZ in E3. rewrite E3.
  pose proof (P1 r Hr N2 N8 N9) as E4. unfold getr in E4. rewrite NZ in E4. exact E4.
Qed.

Ltac scc_enum :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in
  let N2 := fresh "N2" in let N8 := fresh "N8" in let N9 := fresh "N9" in
  intros rr Hrr N2 N8 N9; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
               rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr N2 N8 N9;
  repeat (destruct CC as [CC|CC]; [subst rr; simp_regs; reflexivity|]); subst rr; simp_regs; reflexivity.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis SNP : snprintf_contract.
Hypothesis ARGS : forall fx0 : YK11.FPState, arg_s_contract (fx := fx0) B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis ANSF : forall fx0 : YK11.FPState, answer_contract (fx := fx0) B API.

Lemma scc_shapes : forall K S O L A mem md Lc Ac mc mdc,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> bytes_at rsegs mc G_SHAPES g_shapes_bytes.
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

Lemma scc_tail : forall L A regs mem md id R O b (F3 : bvmap 5 word) (fc3 : bv 32) L4 A4 R5 m5 md4 Om,
  call_pre_t B API 12432 L A regs mem md -> -2^31 <= id < 2^31 ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  room_slots (sb_mallocs b (sup_chain_clear_sizes id (snd (sup_chain_clear_m R id)))) 17 ->
  fp_kept fx (mkFP F3 fc3) ->
  sinv B API 12432 (spZ regs) L A mem md O L4 A4 m5 md4 (rec_record R REC_CHAIN_CLEAR [dec id]) Om b ->
  sb_le (sb_shift b A A4) (sb_malloc b (Z.of_nat (length (dec id)) + 1)) ->
  st_init_done A4 = true ->
  getr R5 1 = Z_to_bv 64 0x17024 -> getr R5 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr R5 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R5 11 = Z_to_bv 64 0x10417 ->
  getr R5 12 = Z_to_bv 64 1 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R5 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs m5 (spZ regs - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR rsegs (mkCfg (@mkst (mkFP F3 fc3) R5 (Z_to_bv 64 ANSWER) m5 (seg_rom rsegs)) md4)
    (sup_chain_clear_ret B API L A regs mem md id R O b).
Proof using SEGS RIMG AX CTX ERRNO_LOW ANSF SLACK.
  intros L A regs mem md id R O b F3 fc3 L4 A4 R5 m5 md4 Om PRE HID GS ROOM FK3 SI BLE INI E1 E2 E10 E11 E12 KR FRS.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & HWA & _ & _ & HL & HLEN & _).
  pose proof (rec_record_calls R REC_CHAIN_CLEAR [dec id] (rec_rep_calls_le _ _ _ _ _ _ _ _ GR)) as HN.
  pose proof GR as (Q & (_ & _ & _ & _ & HX & _) & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  pose proof (dec_length id HID) as DL.
  pose proof (scc_tlen (rec_record R REC_CHAIN_CLEAR [dec id]) (REC_CHAIN_CLEAR, [dec id]) (daemon_shape "chain_clear")
                true HCODE) as TL.
  assert (LX : length (daemon_shape "chain_clear") = 6%nat) by (vm_compute; reflexivity).
  rewrite LX in TL. change (Nat.max 6 16) with 16%nat in TL.
  pose proof ROOM as RM.
  change (snd (sup_chain_clear_m R id)) with
    (snd (rec_answer (rec_record R REC_CHAIN_CLEAR [dec id]) (REC_CHAIN_CLEAR, [dec id]) (daemon_shape "chain_clear")
      true)) in RM.
  unfold sup_chain_clear_sizes, sb_mallocs in RM. cbn [fold_left] in RM.
  set (S := spZ regs) in *.
  assert (SP5 : spZ R5 = S - 48) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  assert (AK : ANSWER_K = 12384) by reflexivity.
  assert (PRA : call_pre_t B API ANSWER_K L4 A4 R5 m5 md4).
  { split; [|rewrite SP5; lia].
    apply (call_pre_k_of_rjr B _ 12432 S rec_area _ L A mem md L4 A4 m5 md4 ANSWER_K R5 RJ).
    - rewrite E1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SP5. replace (S - 48) with (S + (-3) * 16) by ring. rewrite Z.mod_add by lia. exact HAL.
    - rewrite AK. lia.
    - rewrite SP5, AK. lia.
    - rewrite SP5. lia.
    - exact (eq_trans (KR 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) HTP). }
  rewrite <- SEGS.
  eapply SR_bind.
  { apply (answer_tail (fx := mkFP F3 fc3) B API SEGS AX CTX ERRNO_LOW (ANSF (mkFP F3 fc3)) SLACK ANSWER_K
             L4 A4 R5 m5 md4 Om L4 A4 R5 m5 md4 (rec_record R REC_CHAIN_CLEAR [dec id]) Om (sb_shift b A A4)
             (sb_malloc b (Z.of_nat (length (dec id)) + 1)) (sb_shift b A A4) (rec_entry G_REC REC_SC R) 0x10417
             (REC_CHAIN_CLEAR, [dec id]) (daemon_shape "chain_clear") true PRA (Z.le_refl _)
             (rjr_init B (aa_MR API) ANSWER_K rec_area (fun pn => In pn Om) L4 A4 R5 m5 md4 (proj1 PRA)
                ltac:(rewrite AK; lia))
             eq_refl eq_refl (fun r _ => eq_refl) E10 E11 ltac:(rewrite E12; reflexivity)).
    - rewrite SEGS. exact GR.
    - intros _. replace (daemon_shape "chain_clear") with REC_MOD_HOST_SHAPE by (vm_compute; reflexivity).
      rewrite SEGS. exact (scc_host m5 RA).
    - intros _ _. exact (ans_entry_record R REC_CHAIN_CLEAR [dec id] HN).
    - exact (proj1 FK3).
    - rewrite SEGS. exact F18.
    - rewrite SEGS. exact RA.
    - exact RS.
    - rewrite sb_shift_refl. reflexivity.
    - exact BLE.
    - eapply room_slots_mono; [| | exact RM].
      + apply sb_malloc_mono, sb_malloc_mono. exact BLE.
      + lia.
    - intros pn H. left. exact H.
    - intros pn H. destruct (in_dec pair_dec pn Om) as [H1|H1]; [right; exact H1 | left; split; assumption].
    - intros pn H1 H2. contradiction. }
  intros c' TR. unfold tail_ret in TR.
  destruct TR as (fx6 & L6 & A6 & regs6 & m6 & md6 & O6 & q & -> & FK6 & POST6 & A06 & GR6 & ON6 & BL6 & IN6 & FB6
    & NQ6 & BY6 & OK6 & AP6 & RA6 & F186 & INI6 & RGN6 & BLE6 & RES6).
  pose proof POST6 as (PM & PW & PB & PLE & PA & PR & PV & PF & PK & PS).
  rewrite SEGS in PF, RA6, F186, BY6, OK6, GR6.
  rewrite E1, SEGS.
  assert (FRS6 : rw_cells rsegs m6 (S - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m5); [exact FRS|]. intros i Hi. cbn in Hi.
    destruct (PF (S - 24 + i)) as [K1 K2].
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L4 A4 m5 md4 _ HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L6 A6 m6 md6 _ PM Ho). lia.
    - unfold scratch_k. rewrite SP5, AK. intros [H|H]; lia.
    - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (RJ6 : rjr B (aa_MR API) 12432 S rec_area (fun pn => In pn O) L A mem md L6 A6 m6 md6).
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW 12432 S rec_area _ L A mem md L4 A4 m5 md4 ANSWER_K R5 rec_area
             (fun a => In a (map fst Om)) L6 A6 regs6 m6 md6 RJ POST6).
    - rewrite SP5, AK. lia.
    - rewrite SP5. lia.
    - intros a Ha _. split; [exact Ha|]. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Ha. lia.
    - intros p n Hp Hg Hn Hx. apply in_map_iff in Hx as ([a k'] & Ea & Hq). cbn [fst] in Ea. subst a.
      pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hq) as Hb.
      pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hq) as Hk'. cbn [snd] in Hk'.
      pose proof (rjr_in_cur B _ 12432 S rec_area _ L A mem md L4 A4 m5 md4 p n RJ Hp Hg) as Hc.
      pose proof (user_blocks_in L4 A4 p n Hc) as Hbn. rewrite (ptr_addr_stable A L L4 p n HWA Hp HL) in Hbn.
      pose proof (blocks_same_addr B _ LAWS L4 A4 m5 md4 (ptr_addr L p) n k' HM Hbn Hb Hn Hk') as <-.
      destruct (ON _ Hq) as [X|X]; [exact (Hg X) | exact (X (user_blocks_in L A p n Hp))].
    - intros p n Hp Hc Hn1.
      pose proof (ptr_addr_stable A L L4 p n HWA Hp HL) as EA.
      destruct (in_dec pair_dec (ptr_addr L p, n) Om) as [H|H].
      + destruct (ON _ H) as [X|X]; [exact X|]. exfalso. exact (X (user_blocks_in L A p n Hp)).
      + exfalso. apply Hn1. rewrite <- EA in H. exact (proj1 (OK6 p n Hc H)).
    - exact RGN6.
    - intros Hf. rewrite INI6 in Hf. discriminate. }
  destruct (mr_model B _ LAWS L6 A6 m6 md6 PM) as (Hh6 & Hl6 & _).
  eapply evt_SR_canon; [ | exact Hh6 | exact Hl6 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs6 2 = Z_to_bv 64 (S - 48))
      by exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) E2).
    rewrite Q2.
    eapply scc_epi with (sp0 := reg_get regs 2).
    - rewrite unsigned_lit by lia. replace (S - 48 + 24) with (S - 24) by ring. exact FRS6.
    - rewrite unsigned_lit by lia. unfold S, spZ. change (getr regs 2) with (reg_get regs 2). lia. }
  intros ms7 (can7 & -> & EQ7).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ7 eq_refl eq_refl) as (R7 & -> & X7).
  rewrite (ret_pc_of_ok (reg_get regs 1) HRA).
  assert (RP7 : regs_preserved regs R7).
  { apply (scc_pres_tail regs R5 regs6 R7 _ KR PR X7).
    - scc_enum.
    - intros rr _ CC. repeat (destruct CC as [CC|CC]; [subst rr; simp_regs; reflexivity|]).
      subst rr; simp_regs; reflexivity. }
  apply SR_ret.
  unfold sup_chain_clear_ret. rewrite SEGS.
  exists fx6, L6, A6, R7, m6, md6, (fst (sup_chain_clear_m R id)), O6, (snd (sup_chain_clear_m R id)), q.
  split; [apply surjective_pairing|].
  split; [reflexivity|].
  split; [exact (scc_fpk _ _ _ FK3 FK6)|].
  split.
  { exact (rjr_final B (aa_MR API) CTX 12432 rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
             L6 A6 R7 m6 md6 PRK RJ6 RP7 (fun a k G => in_map fst O (a, k) G)). }
  split; [rewrite (getr_of_eqv _ _ 10 X7 eq_refl); simp_regs; exact A06|].
  split; [exact GR6|].
  split.
  { intros pn Hpn. destruct (ON6 pn Hpn) as [H|H]; [exact (ON pn H)|].
    destruct (in_dec pair_dec pn (blocks L A)) as [Hb|Hb]; [|right; exact Hb]. left. exact (B2 pn Hb H). }
  split.
  { intros pn Hpn. destruct (BL6 pn Hpn) as [(Hc & Hn)|[H|H]].
    - destruct (B1 pn Hc) as [X|X]; [left; exact X | contradiction].
    - right; left; exact H.
    - right; right; exact H. }
  split; [exact IN6|]. split; [exact FB6|]. split; [exact NQ6|]. split; [exact BY6|].
  split.
  { pose proof (rjr_others_kept B (aa_MR API) 12432 S rec_area (fun pn => In pn O) L A mem md L6 A6 m6 md6 O RJ6
                  (fun pn H => H)) as OK. rewrite SEGS in OK. exact OK. }
  split.
  { intros p k Hp Hno.
    assert (Hc : In (p, k) (user_blocks A4))
      by exact (rjr_in_cur B _ 12432 S rec_area _ L A mem md L4 A4 m5 md4 p k RJ Hp Hno).
    pose proof (ptr_addr_stable A L L4 p k HWA Hp HL) as EA.
    assert (Hno' : ~ In (ptr_addr L4 p, k) Om).
    { rewrite EA. intros H. destruct (ON _ H) as [X|X]; [exact (Hno X) | exact (X (user_blocks_in L A p k Hp))]. }
    pose proof (AP6 p k Hc Hno') as D. rewrite EA in D. exact D. }
  split; [exact (scc_shapes 12432 S O L A mem md L6 A6 m6 md6 RJ6 GS)|].
  split; [exact RA6|]. split; [exact F186|]. split; [exact INI6|].
  split; [pose proof RJ6 as (_ & _ & _ & _ & _ & HLen6 & _); exact HLen6|].
  rewrite sb_shift_trans in BLE6, RES6.
  split; [|exact RES6].
  unfold sup_chain_clear_sizes, sb_mallocs. cbn [fold_left]. exact BLE6.
Qed.

Lemma scc_after_arg : forall L A regs mem md id R O b (F3 : bvmap 5 word) (fc3 : bv 32) L4 A4 regs4 m4 md4 Om,
  call_pre_t B API 12432 L A regs mem md -> -2^31 <= id < 2^31 ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  room_slots (sb_mallocs b (sup_chain_clear_sizes id (snd (sup_chain_clear_m R id)))) 17 ->
  fp_kept fx (mkFP F3 fc3) ->
  sinv B API 12432 (spZ regs) L A mem md O L4 A4 m4 md4 (rec_record R REC_CHAIN_CLEAR [dec id]) Om b ->
  sb_le (sb_shift b A A4) (sb_malloc b (Z.of_nat (length (dec id)) + 1)) ->
  st_init_done A4 = true ->
  getr regs4 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs4 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs m4 (spZ regs - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR rsegs (mkCfg (@mkst (mkFP F3 fc3) regs4 (Z_to_bv 64 0x17004) m4 (seg_rom rsegs)) md4)
    (sup_chain_clear_ret B API L A regs mem md id R O b).
Proof using SEGS RIMG GOWN AX CTX ERRNO_LOW ANSF SLACK RSO.
  intros L A regs mem md id R O b F3 fc3 L4 A4 regs4 m4 md4 Om PRE HID GS ROOM FK3 SI BLE INI E2 E9 KR FRS.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof SI as (RJ & GR & _ & _ & _ & RA & F18 & RS).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS L4 A4 m4 md4 HM) as (Hh & Hl & _).
  set (S := spZ regs) in *.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs4 2 = Z_to_bv 64 (S - 48)) by exact E2.
    rewrite Q2.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply (scc_after RSO) with (lo := S - 12432).
    - rewrite unsigned_lit by lia. apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. lia.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - apply (bytes_at_normalize rsegs m4 _ _ RA). exact (scc_shapes 12432 S O L A mem md L4 A4 m4 md4 RJ GS).
    - apply mem_inv_normalize. }
  intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
  destruct Q5 as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5n & -> & MU5n & WM5n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL5) as [EC5 MR5r].
  revert EC5 MR5r RO5 EQ5. generalize (ms_mem can5) as m5. intros m5 EC5 MR5r RO5 EQ5. subst can5.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m4 RA) MR5r RO5 MU5n) as MU5.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m4 RA) MR5r RO5 WM5n) as WM5.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ5) as (R5 & -> & X5).
  clear MU5n WM5n MR5r.
  rewrite !unsigned_lit in MU5 by lia.
  pose proof (sinv_stack B API SEGS GOWN AX 12432 S L A mem md O L4 A4 m4 md4 _ _ b m5 _ SI MU5 WM5
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI5.
  assert (FRS5 : rw_cells rsegs m5 (S - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m4 m5 _ _ FRS MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (E5_1 : getr R5 1 = Z_to_bv 64 0x17024) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_2 : getr R5 2 = Z_to_bv 64 (S - 48))
    by (rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_10 : getr R5 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact E9).
  assert (E5_11 : getr R5 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_12 : getr R5 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X5 eq_refl); simp_regs; reflexivity).
  assert (KR5 : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R5 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by (apply (scc_keep regs regs4 R5 _ KR X5); scc_enum).
  exact (scc_tail L A regs mem md id R O b F3 fc3 L4 A4 R5 m5 md4 Om PRE HID GS ROOM FK3 SI5 BLE INI E5_1 E5_2 E5_10
           E5_11 E5_12 KR5 FRS5).
Qed.

Lemma scc_after_rec : forall L A regs mem md id R O b L2 A2 regs2 m2 md2 O2,
  call_pre_t B API 12432 L A regs mem md -> -2^31 <= id < 2^31 ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_chain_clear_sizes id (snd (sup_chain_clear_m R id)))) 17 ->
  sinv B API 12432 (spZ regs) L A mem md O L2 A2 m2 md2 (rec_record R REC_CHAIN_CLEAR []) O2 b ->
  sb_le (sb_shift b A A2) b ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 8 = Z_to_bv 64 id ->
  getr regs2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs m2 (spZ regs - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  SR rsegs (mkCfg (mkst regs2 (Z_to_bv 64 0x16fdc) m2 (seg_rom rsegs)) md2)
    (sup_chain_clear_ret B API L A regs mem md id R O b).
Proof using SEGS ERRNO_LOW GFACT RIMG GOWN AX CTX SLACK SNP ARGS RSO ANSF.
  intros L A regs mem md id R O b L2 A2 regs2 m2 md2 O2 PRE HID GS FRM ROOM SI BLE E2 E8 E10 KR FRS.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof SI as (RJ & GR & _ & _ & _ & RA & F18 & RS).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM) as (Hh & Hl & _).
  pose proof (dec_length id HID) as DL.
  set (S := spZ regs) in *.
  rewrite SEGS in HSC.
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs m2 GOT_GUARD (Mem.le8 (Z_to_bv 64 GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs m2 GUARD (Mem.le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_normalize_cj_low rsegs m2 GOT_GUARD (Mem.le8 (Z_to_bv 64 GUARD)) RA
    ltac:(rewrite Mem.length_le8; unfold GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs m2 GUARD (Mem.le8 canary) RA
    ltac:(rewrite Mem.length_le8; unfold GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (STa : stk rsegs (normalize_cj rsegs m2) (S - 12432) (S - 24)).
  { apply stk_normalize_cj; [lia | lia | intros a Ha; apply HSC; left; lia]. }
  destruct (stk_carve rsegs _ _ _ 16 STa ltac:(lia)) as [STb [junk BUFn]].
  change (Z.of_nat 16) with 16 in STb, BUFn.
  destruct (stk_carve rsegs _ _ _ 8 STb ltac:(lia)) as [STc _].
  change (Z.of_nat 8) with 8 in STc.
  replace (S - 24 - 16 - 8) with (S - 48) in STc by ring.
  replace (S - 24 - 16) with (S - 40) in BUFn by ring.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get regs2 2 = Z_to_bv 64 (S - 48)) by exact E2.
    assert (Q8 : reg_get regs2 8 = Z_to_bv 64 id) by exact E8.
    rewrite Q2, Q8.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    eapply (scc_mid SNP) with (lo := S - 12432) (canary := canary) (junk := junk).
    - exact HID.
    - rewrite unsigned_lit by lia. exact STc.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. replace (S - 48 + 8) with (S - 40) by ring. exact BUFn.
    - exact FRM.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact GGn.
    - exact GWn. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F3 & fc3 & m3n & slack
    & -> & MU3n & WM3n & FRM3 & FK3 & SL3 & BUF3n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA) MR3r RO3 WM3n) as WM3.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR3r BUF3n) as BUF3.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ3) as (R3 & -> & X3).
  clear MU3n WM3n BUF3n MR3r.
  rewrite !unsigned_lit in MU3 by lia. rewrite !unsigned_lit in BUF3 by lia.
  replace (S - 48 + 8) with (S - 40) in MU3, BUF3 by ring.
  pose proof (sinv_stack B API SEGS GOWN AX 12432 S L A mem md O L2 A2 m2 md2 _ _ b m3 _ SI MU3 WM3
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI3.
  assert (FRS3 : rw_cells rsegs m3 (S - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FRS MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x17004) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (S - 48))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 9 X3 eq_refl); simp_regs; exact E10).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact E10).
  assert (E3_11 : getr R3 11 = Z_to_bv 64 (S - 40)).
  { rewrite (getr_of_eqv _ _ 11 X3 eq_refl). simp_regs. rewrite unsigned_lit by lia. f_equal. lia. }
  assert (KR3 : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by (apply (scc_keep regs regs2 R3 _ KR X3); scc_enum).
  assert (SP3 : spZ R3 = S - 48) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (FKA : fp_kept fx (mkFP F3 fc3)).
  { split; [exact FRM3|]. intros r Hr. cbn [fp_regs]. apply FK3.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. unfold fs_saved in Hr.
    rewrite Z.mod_small by lia. lia. }
  assert (H40 : (S - 40) mod 8 = 0) by (clear - HAL; Z.div_mod_to_equations; lia).
  assert (MODB : forall s L0, s mod 8 = 0 -> 1 <= L0 <= 11 -> (- (s + L0 + 1)) mod 8 <= 15 - L0)
    by (intros s L0 Hs HL0; Z.div_mod_to_equations; lia).
  assert (ROOM1 : room_slots (sb_malloc (sb_shift b A A2) (Z.of_nat (length (dec id)) + 1))
                    (Z.of_nat (length (dec id)) + 1)).
  { pose proof ROOM as RM. unfold sup_chain_clear_sizes, sb_mallocs in RM. cbn [fold_left] in RM.
    eapply room_slots_mono; [| | exact RM].
    - eapply sb_le_trans; [apply sb_malloc_mono; exact BLE|].
      eapply sb_le_trans; apply sb_le_malloc; lia.
    - lia. }
  apply (sinv_arg_s (fx := mkFP F3 fc3) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS (mkFP F3 fc3)) 12432 S L A mem md O
           L2 A2 m3 md2 R REC_CHAIN_CLEAR O2 b R3 (S - 40) (Some (dec id)) _ SI3).
  - rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP3. replace (S - 48) with (S + (-3) * 16) by ring. rewrite Z.mod_add by lia. exact HAL.
  - assert (ASK : ARG_S_K = 8256) by reflexivity. rewrite SP3, ASK. lia.
  - rewrite SP3. lia.
  - exact (eq_trans (KR3 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) HTP).
  - exact E3_10.
  - exact E3_11.
  - cbn [arg_s_src]. split; [lia|]. split; [exact (dec_no0 id)|]. split; [unfold LMAX; lia|].
    exists slack. rewrite SEGS. split; [exact BUF3|].
    split.
    { rewrite SL3, Nat2Z.inj_sub by lia.
      pose proof (MODB (S - 40) (Z.of_nat (length (dec id))) H40 ltac:(lia)). lia. }
    split; [right; rewrite SP3; lia|].
    left. rewrite SP3. split; lia.
  - exact ROOM1.
  - intros L4 A4 regs4 m4 md4 p SI4 SB4 INI4 RP4 FK4.
    rewrite E3_1.
    apply (scc_after_arg L A regs mem md id R O b F3 fc3 L4 A4 regs4 m4 md4 _ PRE HID GS ROOM FKA SI4).
    + rewrite SB4. apply sb_malloc_mono. exact BLE.
    + exact INI4.
    + exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E3_2).
    + exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E3_9).
    + intros r Hr N2 N8 N9. rewrite (RP4 r Hr). exact (KR3 r Hr N2 N8 N9).
    + apply (rw_cells_transfer rsegs m3); [exact FRS3|]. intros i Hi. cbn in Hi.
      destruct (FK4 (S - 24 + i) ltac:(rewrite SP3; lia)) as [K1 K2]. split; [exact K1 | exact (proj1 K2)].
Qed.

Theorem sup_chain_clear_holds : sup_chain_clear_contract B API.
Proof using SEGS ERRNO_LOW GFACT RIMG GOWN AX CTX SLACK REC SNP ARGS RSO ANSF.
  unfold sup_chain_clear_contract.
  intros L A regs mem md id R O b PRE A0 HID GS GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  unfold SUP_CHAIN_CLEAR_K in PRE.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite SEGS in GS, GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API 12432 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  assert (ST : stk rsegs mem (spZ regs - 12432) (spZ regs)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. change (reg_get regs 2) with (getr regs 2).
    eapply scc_pro; [exact ST | change (bv_unsigned (getr regs 2)) with (spZ regs); lia
                    | change (bv_unsigned (getr regs 2)) with (spZ regs); lia]. }
  intros ms1 (can1 & (m1 & junk & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU1, FR1.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16fdc) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (spZ regs - 48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact A0).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 18) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (KR1 : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by (apply (scc_keep regs regs R1 _ (fun r _ _ _ _ => eq_refl) X1); scc_enum).
  assert (SP1 : spZ R1 = spZ regs - 48) by (unfold spZ at 1; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12432 (spZ regs) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  destruct (rw_cells_app_split rsegs m1 _ [CB 24 junk] [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]
              FR1) as [_ FRS1].
  change (Z.of_nat (cells_size [CB 24 junk])) with 24 in FRS1.
  replace (spZ regs - 48 + 24) with (spZ regs - 24) in FRS1 by ring.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12432 (spZ regs) L A mem md O L A m1 md R O b R1 REC_CHAIN_CLEAR _ SI1).
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by ring. rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - exact (eq_trans (KR1 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) HTP).
  - exact E1_10.
  - unfold REC_FN_COUNT, REC_CHAIN_CLEAR. lia.
  - intros L2 A2 regs2 m2 md2 O2 SI2 BLE2 RP2 R102 FK2.
    rewrite E1_1. rewrite sb_shift_refl in BLE2.
    apply (scc_after_rec L A regs mem md id R O b L2 A2 regs2 m2 md2 O2 PRE HID GS FRM ROOM SI2 BLE2).
    + exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E1_2).
    + exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E1_8).
    + exact R102.
    + intros r Hr N2 N8 N9. rewrite (RP2 r Hr). exact (KR1 r Hr N2 N8 N9).
    + apply (rw_cells_transfer rsegs m1); [exact FRS1|]. intros i Hi. cbn in Hi.
      destruct (FK2 (spZ regs - 24 + i) ltac:(rewrite SP1; lia)) as [K1 K2]. split; [exact K1 | exact (proj1 K2)].
Qed.

End P.
