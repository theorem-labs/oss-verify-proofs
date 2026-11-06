(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, module names, addresses and numbers changed; 284 of its 399 lines of code are new or changed and 433 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_shape_of_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma swl_head :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x40000 <= lo ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16a78) (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 8)
                     a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 16) [C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a64) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 16%nat junk [] [8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 5 step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma swl_pre :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 0x16a8c) sp gp tp t0 t1 t2 a0 s1 (Z_to_bv 64 0x1060b) (Z_to_bv 64 11)
                     a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x158e4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

Lemma swl_post :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 16) [C8 s00; C8 ra0] -> 16 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s1 s0 a0 (Z_to_bv 64 0) a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a8c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 7 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 16 + 16)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma swl_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1060b (str_bytes "worker_list"%string).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma swl_shape : shape_find shape_rows (str_bytes "worker_list"%string) = 0x10384.
Proof. vm_compute. reflexivity. Qed.

Lemma swl_mid : rec_shape_of_contract ->
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sp0 ra0 s00 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 16) [C8 s00; C8 ra0] ->
  stk rsegs m lo (bv_unsigned sp0 - 16) -> lo + 80 <= bv_unsigned sp0 -> 0x40000 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s1 a0 (Z_to_bv 64 0x10384)
                     (Z_to_bv 64 0) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16310) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp0 - 80, bv_unsigned sp0 - 16)] m m'
       /\ wmono rsegs m m')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a78) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp0 ra0 s00 FR ST LO LO2 GS MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 16)) = bv_unsigned sp0 - 16) by (apply unsigned_lit; lia).
  eapply evt_cut; [apply swl_pre|].
  intros ms1 ->.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "worker_list"%string).
    - exact MI.
    - rewrite SPU. exact ST.
    - rewrite SPU. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. rewrite SPU. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (swl_verb m MI)|].
      left. rewrite SPU. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  rewrite SPU in MU2. unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16a8c) by lia. rewrite swl_shape.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 16) [C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m m2 _ _ FR MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply swl_post; [exact FR2 | lia]|].
  intros ms3 ->. apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|].
  split; [|exact WM2].
  apply (munch_weaken [(bv_unsigned sp0 - 16 - 64, bv_unsigned sp0 - 16)]); [|exact MU2].
  intros x Hx. cbn in Hx |- *. repeat split; lia.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecSeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecStep RecGlue RecAnsB RecTail RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import record_c answer_c sup_worker_list_c.
Local Open Scope Z_scope.

Definition swl_rom_chk (a : Z) (bs : list byte) : bool :=
  forallb (fun i => Mem.ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) &&
     match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error bs i with
     | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
     | _, _ => false
     end) (seq 0 (length bs)).

Lemma swl_rom_chk_at : forall a bs i, swl_rom_chk a bs = true -> (i < length bs)%nat ->
  Mem.ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true /\
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros a bs i C Hi. unfold swl_rom_chk in C.
  pose proof (proj1 (forallb_forall _ _) C i ltac:(apply in_seq; lia)) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Cr Cv]. split; [exact Cr|].
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in Cv. f_equal. apply bv_eq. exact Cv.
Qed.

Lemma swl_ans_shape : forall m, ro_agree rsegs m -> ans_shape rsegs m 0x10384 (daemon_shape "worker_list").
Proof.
  intros m RA. change (daemon_shape "worker_list") with (shape_of (bstr "worker_list")).
  destruct (shape_of_facts (bstr "worker_list")) as (FT & _ & L78 & N0).
  assert (C : swl_rom_chk 0x10384 (shape_of (bstr "worker_list") ++ [Z_to_bv 8 0]) = true) by (vm_compute; reflexivity).
  pose proof (length_app (shape_of (bstr "worker_list")) [Z_to_bv 8 0]) as LA. cbn [length] in LA.
  split.
  - split; [lia|]. split; [rewrite LA; lia|]. intros i Hi.
    destruct (swl_rom_chk_at _ _ i C Hi) as [Cr Cv]. unfold wa. rewrite (RA _ Cr). exact Cv.
  - split; [exact N0|]. split; [unfold LMAX; lia|]. split; [exact FT|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    exact (proj1 (swl_rom_chk_at _ _ (Z.to_nat i) C ltac:(rewrite LA; lia))).
Qed.

Lemma swl_inst_len : (length (inst (daemon_shape "worker_list")) <= 24)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Lemma swl_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma swl_stub_len : forall R, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R REC_WORKER_LIST []) (REC_WORKER_LIST, []) (daemon_shape "worker_list") false))
     <= 24)%nat.
Proof.
  intros R H. rewrite rec_answer_text. destruct (r_refuse (rec_record R REC_WORKER_LIST []) =? 0).
  - exact swl_inst_len.
  - rewrite swl_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Ltac swl_saved :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr ?; unfold callee_saved in Hr;
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
              r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  clear Hr;
  repeat (destruct C as [C|C]; [subst r; first [lia | reflexivity]|]);
  subst r; first [lia | reflexivity].

Section SWL.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ANS : answer_contract B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Lemma swl_shapes_kept : forall K L A regs mem md E excl L' A' regs' mem' md',
  call_pre_k B (aa_MR API) K L A regs mem md ->
  call_post_rec B (aa_MR API) K L A regs mem md E excl L' A' regs' mem' md' ->
  (forall a, G_SHAPES <= a < G_SHAPES + 448 -> ~ E a) ->
  Mem.bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  Mem.bytes_at rsegs mem' G_SHAPES g_shapes_bytes.
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

Lemma swl_rjr_shapes : forall K S O L A mem md Lc Ac mc mdc,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  Mem.bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  Mem.bytes_at rsegs mc G_SHAPES g_shapes_bytes.
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

Theorem sup_worker_list_holds : sup_worker_list_contract B API.
Proof using SEGS ERRNO_LOW GOWN AX CTX SLACK REC ANS RSO RIMG RFREE.
  unfold sup_worker_list_contract.
  intros L A regs mem md R O b PRE GS GR RA FRM F18 RES ROOM.
  pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  assert (IL : img_low B)
    by (apply (img_low_of_check B (2 ^ 21)); [unfold img_check; rewrite SEGS; vm_compute; reflexivity | lia]).
  assert (KV : RECORD_K = 8336) by reflexivity.
  assert (AK : ANSWER_K <= SUP_WORKER_LIST_K) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof PRE as (PRK & HTS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (kb_md B API _ _ _ _ HMR) as [Hh Hl].
  pose proof (kb_stk B API IL _ _ _ _ _ _ PRK ltac:(unfold SUP_WORKER_LIST_K; lia)) as ST. rewrite SEGS in ST.
  rewrite SEGS in GS, GR, RA, F18.
  pose proof (rec_rep_calls_le rsegs G_REC REC_SC L A mem R O GR) as C1.
  pose proof GR as (Q0 & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HCODE & _) & _) & _).
  pose proof (sinv_init B API SUP_WORKER_LIST_K L A regs mem md R O b PRK ltac:(unfold SUP_WORKER_LIST_K; lia)
                GR RA F18 RES) as SI0.
  change (sup_worker_list_m R)
    with (rec_answer (rec_record R REC_WORKER_LIST []) (REC_WORKER_LIST, []) (daemon_shape "worker_list") false)
    in ROOM.
  unfold sup_worker_list_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  pose proof (swl_stub_len R HCODE) as LT.
  set (sp := getr regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SUP_WORKER_LIST_K in HCEIL.
  eapply (kb_run B regs (Z_to_bv 64 SUP_WORKER_LIST) mem md
    (fun R1 pc' m' =>
       pc' = Z_to_bv 64 0x1612c /\
       munch [(bv_unsigned sp - 16, bv_unsigned sp)] mem m' /\ wmono rsegs mem m' /\
       rw_cells rsegs m' (bv_unsigned sp - 16) [C8 (getr regs 8); C8 (getr regs 1)] /\
       getr R1 1 = Z_to_bv 64 0x16a78 /\ getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 16) /\
       getr R1 10 = Z_to_bv 64 8 /\
       (forall r, callee_saved r -> r <> 2 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)))
    _ Hh Hl).
  { unfold rmk. fold sp. rewrite SEGS. eapply evt_cut.
    - eapply (swl_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr mem
                (bv_unsigned sp - SUP_WORKER_LIST_K));
        [exact ST | unfold SUP_WORKER_LIST_K; lia | unfold SUP_WORKER_LIST_K; lia].
    - intros ms' (m' & -> & MU & WM & FR). apply evt_done.
      do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact FR|].
      do 3 (split; [reflexivity|]). swl_saved. }
  intros R1 pc1 m1 regs1 (-> & MU1 & WM1 & FR1 & E1_1 & E1_2 & E1_10 & E1_S) HG1.
  rewrite <- HG1 in E1_1, E1_2, E1_10.
  assert (E1S : forall r, callee_saved r -> r <> 2 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r H1 H2. rewrite HG1. exact (E1_S r H1 H2). }
  clear E1_S.
  assert (SP1 : spZ regs1 = bv_unsigned sp - 16) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (HW1 : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(bv_unsigned sp - 16, bv_unsigned sp)] a ->
            bv_unsigned sp - SUP_WORKER_LIST_K <= a < bv_unsigned sp).
  { intros a Ra Hm. cbn in Hm. unfold SUP_WORKER_LIST_K. lia. }
  pose proof (sinv_stack B API SEGS GOWN AX SUP_WORKER_LIST_K (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                SI0 MU1 WM1 HW1) as SI1.
  rewrite SEGS.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC SUP_WORKER_LIST_K (bv_unsigned sp) L A mem md O L A m1 md R O b regs1
           REC_WORKER_LIST _ SI1);
    [ rewrite E1_1; apply bv_eq; vm_compute; reflexivity
    | rewrite SP1; replace (bv_unsigned sp - 16) with (bv_unsigned sp + (-1) * 16) by ring;
      rewrite Z.mod_add by lia; exact HAL
    | rewrite SP1, KV; unfold SUP_WORKER_LIST_K; lia
    | rewrite SP1; lia
    | exact (eq_trans (E1S 4 ltac:(unfold callee_saved; lia) ltac:(lia)) HTP)
    | exact E1_10
    | unfold REC_FN_COUNT, REC_WORKER_LIST; lia
    | ].
  intros L1 A1 regs2 m2 md2 O1 SI2 BLE2 PR R10 FK.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 16) [C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (FK (bv_unsigned sp - 16 + i) ltac:(rewrite SP1; lia)) as [E W].
    split; [exact E | apply W]. }
  pose proof SI2 as (RJ2 & GR3 & ON2 & B12 & B22 & RA3 & F183 & RS3).
  pose proof RJ2 as (PM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC2 & _).
  assert (E2_2 : getr regs2 2 = Z_to_bv 64 (bv_unsigned sp - 16))
    by exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2S : forall r, callee_saved r -> r <> 2 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r H1 H2. rewrite (PR r H1). exact (E1S r H1 H2). }
  destruct (kb_md B API _ _ _ _ PM) as [Hh2 Hl2].
  assert (STn : Frame.stk rsegs (normalize rsegs m2) (bv_unsigned sp - SUP_WORKER_LIST_K) (bv_unsigned sp - 16)).
  { apply stk_norm; [unfold SUP_WORKER_LIST_K; lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC2. left. lia. }
  pose proof (bytes_at_normalize rsegs m2 _ _ RA3 (swl_rjr_shapes _ _ _ _ _ _ _ _ _ _ _ RJ2 GS)) as GSn.
  pose proof (rw_cells_norm_hi m2 (bv_unsigned sp - 16) _ RA3 ltac:(lia) FR2) as FRn.
  rewrite E1_1. rewrite <- SEGS.
  eapply (kb_run B regs2 (Z_to_bv 64 0x16a78) m2 md2
    (fun R3 pc' m' =>
       pc' = Z_to_bv 64 0x16310 /\
       munch [(bv_unsigned sp - 80, bv_unsigned sp - 16)] m2 m' /\ wmono rsegs m2 m' /\
       getr R3 1 = getr regs 1 /\ getr R3 2 = sp /\ getr R3 10 = getr regs2 10 /\
       getr R3 11 = Z_to_bv 64 0x10384 /\ getr R3 12 = Z_to_bv 64 0 /\ regs_preserved regs R3)
    _ Hh2 Hl2).
  { unfold rmk. rewrite SEGS. rewrite E2_2. eapply evt_cut.
    - eapply (evt_normalize rsegs); [exact WX | exact RA3 |].
      eapply (swl_mid RSO) with (lo := bv_unsigned sp - SUP_WORKER_LIST_K);
        [exact FRn | exact STn | unfold SUP_WORKER_LIST_K; lia | unfold SUP_WORKER_LIST_K; lia | exact GSn
        | apply mem_inv_normalize].
    - intros ms' (sm & QM & REL & RO).
      destruct QM as (m3n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU3n & WM3n).
      destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR3].
      rewrite EC. apply evt_done.
      do 3 eexists. split; [reflexivity|].
      split; [reflexivity|].
      split; [exact (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA3) MR3 RO MU3n)|].
      split; [exact (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA3) MR3 RO WM3n)|].
      do 5 (split; [reflexivity|]).
      intros r Hr. pose proof Hr as Hr0. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 8 \/ (r <> 2 /\ r <> 8)) by lia.
      destruct C as [->|[->|[H2 H8]]]; [reflexivity | reflexivity |].
      rewrite <- (E2S r Hr0 H2).
      assert (C : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                  r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      clear Hr Hr0 H2 H8.
      repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity. }
  intros R3 pc3 m3 regs3 (-> & MU3 & WM3 & E3_1 & E3_2 & E3_10 & E3_11 & E3_12 & P3) HG3.
  rewrite <- HG3 in E3_1, E3_2, E3_10, E3_11, E3_12.
  assert (RP3 : regs_preserved regs regs3) by exact (kb_preserved_getr regs R3 regs3 P3 HG3).
  assert (HW3 : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(bv_unsigned sp - 80, bv_unsigned sp - 16)] a ->
            bv_unsigned sp - SUP_WORKER_LIST_K <= a < bv_unsigned sp).
  { intros a Ra Hm. cbn in Hm. unfold SUP_WORKER_LIST_K. lia. }
  pose proof (sinv_stack B API SEGS GOWN AX SUP_WORKER_LIST_K (bv_unsigned sp) L A mem md O L1 A1 m2 md2
                (rec_record R REC_WORKER_LIST []) O1 b m3 _ SI2 MU3 WM3 HW3) as SI3.
  pose proof SI3 as (RJ3 & GR4 & ON3 & B13 & B23 & RA4 & F184 & RS4).
  assert (BLEb : sb_le (sb_shift b A A1) b) by (rewrite sb_shift_refl in BLE2; exact BLE2).
  eapply SR_mono.
  { apply (answer_tail B API SEGS AX CTX ERRNO_LOW ANS SLACK SUP_WORKER_LIST_K L A regs mem md O L1 A1 regs3 m3 md2
             (rec_record R REC_WORKER_LIST []) O1 b b (sb_shift b A A1) (rec_slot R) 0x10384
             (REC_WORKER_LIST, []) (daemon_shape "worker_list") false PRE AK RJ3 E3_1
             ltac:(unfold spZ; rewrite E3_2; reflexivity) RP3).
    - rewrite E3_10. exact R10.
    - exact E3_11.
    - rewrite E3_12. reflexivity.
    - rewrite SEGS. exact GR4.
    - intros _. rewrite SEGS. exact (swl_ans_shape m3 RA4).
    - intros _ H. discriminate H.
    - exact FRM.
    - rewrite SEGS. exact F184.
    - rewrite SEGS. exact RA4.
    - exact RS4.
    - reflexivity.
    - exact BLEb.
    - apply (room_slots_mono _ _ _ 25 (sb_malloc_mono _ _ _ (sb_malloc_mono _ _ _ BLEb))); [lia | exact ROOM].
    - exact ON3.
    - exact B13.
    - exact B23. }
  intros c' TR. unfold sup_worker_list_ret.
  destruct TR as (fx' & L' & A' & regs' & mem' & md' & O' & q & EC & FPK & POST & A0 & GR' & OWN & BLK & Hq & FRB
    & NI & BY & OK & AP & RA' & F18' & INIT & LEN & SBL & RES').
  exists fx', L', A', regs', mem', md', (fst (sup_worker_list_m R)), O', (snd (sup_worker_list_m R)), q.
  split; [apply surjective_pairing|].
  split; [exact EC|]. split; [exact FPK|]. split; [exact POST|]. split; [exact A0|]. split; [exact GR'|].
  split; [exact OWN|]. split; [exact BLK|]. split; [exact Hq|]. split; [exact FRB|]. split; [exact NI|].
  split; [exact BY|]. split; [exact OK|]. split; [exact AP|].
  split.
  { rewrite SEGS. apply (swl_shapes_kept _ L A regs mem md _ _ L' A' regs' mem' md' PRK POST); [|exact GS].
    intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
  split; [exact RA'|]. split; [exact F18'|]. split; [exact INIT|]. split; [exact LEN|]. split; [exact SBL | exact RES'].
Qed.

End SWL.
