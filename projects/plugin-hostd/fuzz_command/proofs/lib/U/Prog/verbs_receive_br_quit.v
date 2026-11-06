(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v; 113 of its 149 lines of code are new or changed and 179 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br verbs_receive_br2 sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma quit_k1 : forall (tk : list (list byte))
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : word),
  s5 = verbs_receive_disp.ntokw tk -> (length tk <= 64)%nat ->
  rw_cells rsegs m 0x343e8 [C4 q] ->
  evt rsegs (fun ms' =>
      (length tk = 1%nat /\ exists m',
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0x346a8) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x176c0) fc None m' (seg_rom rsegs) /\
         munch [(0x343e8, 0x343ec)] m m' /\ wmono rsegs m m' /\ rw_cells rsegs m' 0x343e8 [C4 (Z_to_bv 64 1)]) \/
      (length tk <> 1%nat /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x178a4) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x176a0) fc None m (seg_rom rsegs)).
Proof.
  intros tk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q E5 HL HQ. subst s5.
  pose proof (munch_refl [(0x343e8, 0x343ec)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 zstep. rewrite verbs_receive_disp.eqb_ntokw by lia.
  destruct (Z.of_nat (length tk) =? 1) eqn:E; cbv beta iota delta [negb].
  - apply Z.eqb_eq in E. assert (L1 : length tk = 1%nat) by lia.
    do 4 zstep. apply evt_done. left. split; [exact L1|]. eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption | eassumption].
  - apply Z.eqb_neq in E. apply evt_done. right. split; [lia | reflexivity].
Qed.

Lemma gq_wr_at : forall m n, 0 <= n <= 4 -> wr_at rsegs m 0x343e8 n.
Proof.
  intros m n Hn. split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  unfold writable_at, wview.
  destruct Hc as [E | [E | [E | E]]]; subst i; destruct (m _); try discriminate; vm_compute; discriminate.
Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis SRESP : forall f : YK11.FPState, @sup_resp_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_quit : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RQuit) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RQuit -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  join_k B API S 0x176c4 10 rg R1 k1 qv P ->
  rej_k B API S f 0x178a4 rg R1 k1 qv P ->
  SR rsegs c P.
Proof using HF HS SRESP.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST RT N21 HK JOIN REJ.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & FPK & VR & H & FR & GQ & GW).
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  assert (R21 : reg_get rg 21 = verbs_receive_disp.ntokw (toks D)) by (rewrite <- N21; reflexivity).
  assert (NL : (length (toks D) <= 64)%nat) by apply Verbs.toks_length.
  assert (QC : rw_cells rsegs (normalize rsegs mem1) 0x343e8 [C4 (Z_to_bv 64 qv)]).
  { split; [split|].
    - cbn. split; exact I.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_normalize; [exact RO1 | exact GQ].
    - cbn [cells_size csize]. apply gq_wr_at. lia. }
  assert (FRM : forall mem2, munch [(G_QUIT, G_QUIT + 4)] mem1 mem2 ->
             forall a, s_spf S <= a < s_spf S + 608 ->
             mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
  { intros mem2 MU a Ha.
    assert (Ra : 0 <= a < 2 ^ 64) by (unfold s_spf, VR_K in *; lia).
    assert (Oa : Frame.outside [(G_QUIT, G_QUIT + 4)] a)
      by (cbn [Frame.outside]; split; [unfold s_spf, G_QUIT, VR_K in *; lia | exact I]).
    split; [exact (munch_mbyte rsegs _ mem1 mem2 a MU Ra Oa) | exact (munch_writable rsegs _ mem1 mem2 a MU Ra Oa)]. }
  eapply (ka_bridge B API HF S HS rg (route_pc RQuit) mem1 md1 L1 A1 R1 O1 k1 qv None jk c
            [(G_QUIT, G_QUIT + 4)] _ P HST).
  - intros x Hx Hs Hq. cbn [Frame.outside]. split; [|exact I]. unfold G_QUIT in *. lia.
  - eapply evt_mono.
    + unfold Regs6ss.mkR_of. cbn [route_pc]. eapply (quit_k1 (toks D)); [exact R21 | exact NL | exact QC].
    + intros ms' HQ. split; [exact HQ|].
      destruct HQ as [(_ & m' & -> & MU & WM & _)|(_ & ->)]; do 3 eexists; (split; [reflexivity|]).
      * split; [exact MU | exact WM].
      * split; [apply munch_refl | apply wmono_refl].
  - intros R' pc' m' mem2 rg' HQ X RL MU WM H2.
    destruct HQ as [(L1' & m'' & EQ & _ & _ & QC')|(L1' & EQ)]; injection EQ as ER EP EM; subst R' pc'.
    + subst m''.
      assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
      assert (HST1 : @vr_state f _ B API S rg' 0x176c0 mem2 md1 L1 A1 R1 O1 k1 1 None jk
                       (mkCfg (mkst rg' (Z_to_bv 64 0x176c0) mem2 (seg_rom rsegs)) md1)).
      { split; [reflexivity|]. split; [exact FPK|]. split; [exact (vregs_pres S rg rg' VR PR)|].
        split; [exact H2|].
        split; [exact (vfr_keep B API S HS mem1 mem2 jk (FRM mem2 MU) FR)|].
        split.
        - pose proof (rw_cells_of_rel rsegs mem2 _ 0x343e8 _ RL QC') as [[_ QB] _].
          cbn [cells_bytes cbytes] in QB. rewrite app_nil_r in QB. exact QB.
        - intros i Hi. apply WM. exact (GW i Hi). }
      apply (@resp_join f _ B API HF S HS SRESP rg R1 k1 qv true 0x176c0 0x176c4 rg' mem2 md1 L1 A1 R1 O1 k1 jk _
               0 P).
      * right; right. split; reflexivity.
      * exact HST1.
      * rewrite (getr_of_eqv _ _ 10 X eq_refl). reflexivity.
      * lia.
      * rewrite (getr_of_eqv _ _ 18 X eq_refl). reflexivity.
      * intros Ej. lia.
      * rewrite RT. destruct (toks D) as [|v [|a r]]; cbn [length] in L1'; try lia. reflexivity.
      * lia.
      * lia.
      * exact HK.
      * exact JOIN.
    + subst m'.
      assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
      eapply REJ. split.
      { split; [reflexivity|]. split; [exact FPK|]. split; [exact (vregs_pres S rg rg' VR PR)|].
        split; [exact H2|].
        split; [exact (vfr_keep B API S HS mem1 mem2 jk (FRM mem2 MU) FR)|].
        split.
        - pose proof (rw_cells_of_rel rsegs mem2 _ 0x343e8 _ RL QC) as [[_ QB] _].
          cbn [cells_bytes cbytes] in QB. rewrite app_nil_r in QB. exact QB.
        - intros i Hi. apply WM. exact (GW i Hi). }
      split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
      split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity|].
      split; [|reflexivity].
      rewrite RT. destruct (toks D) as [|v [|a r]]; cbn [plan_at]; try reflexivity.
      exfalso. apply L1'. reflexivity.
Qed.

End R.
