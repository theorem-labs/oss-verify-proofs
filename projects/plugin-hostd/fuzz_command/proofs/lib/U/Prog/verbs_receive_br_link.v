(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v, with its module names changed; 134 of its 168 lines of code are new or changed and 181 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br verbs_receive_br2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require strcmp_c strcspn_c strncmp_c verb_is_c is_instance_verb_c.
Import ListNotations.
Local Open Scope Z_scope.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).
Local Notation REL L1 A1 mem1 md1 :=
  (vr_rel B API (s_O S) (s_L S) (s_A S) (s_regs S) (s_mem S) (s_md S) L1 A1 mem1 md1).

Lemma tab_keep : forall L1 A1 mem1 md1 a bs, REL L1 A1 mem1 md1 -> ro_agree rsegs mem1 ->
  le_at B (s_mem S) a bs -> 0x226b0 <= a -> a + Z.of_nat (length bs) <= 0x226b0 + 1680 ->
  bytes_at rsegs (normalize rsegs mem1) a bs.
Proof using HF HS.
  intros L1 A1 mem1 md1 a bs HR RO H Ha Hb. pose proof (vf_segs B API HF) as SEGS.
  apply bytes_at_normalize; [exact RO|]. rewrite <- SEGS.
  apply (RecKindB.bytes_at_transfer _ (s_mem S)).
  - apply reply.le_at_bytes; [exact H | lia | lia].
  - intros i Hi. apply (st_relro B API HF S HS _ _ _ _ _ HR). exists 0x226b0, 1680. split; [left; reflexivity | lia].
Qed.

Lemma msg_keep : forall L1 A1 mem1 md1, REL L1 A1 mem1 md1 -> ro_agree rsegs mem1 ->
  bytes_at rsegs (normalize rsegs mem1) (s_msg S) (le4 (Z_to_bv 64 (s_fd S))).
Proof using HF HS.
  intros L1 A1 mem1 md1 HR RO. pose proof (vf_segs B API HF) as SEGS.
  pose proof HR as (HM1 & _ & _ & _ & _ & _ & HK & _).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (ok_spm B API S HS) as SPM. pose proof (ok_m63 B API S HS) as M63.
  pose proof (ok_m4k B API S HS) as M4K.
  unfold spZ, VR_K in SPC.
  apply bytes_at_normalize; [exact RO|]. rewrite <- SEGS.
  apply (RecKindB.bytes_at_transfer _ (s_mem S)).
  - apply reply.le_at_bytes; [exact (ok_fd B API S HS) | lia | rewrite length_le4; lia].
  - intros i Hi. rewrite length_le4 in Hi.
    destruct (ok_mout B API S HS i ltac:(lia)) as [NO NS].
    assert (DOM : vr_dom B (s_msg S + i)) by (unfold vr_dom; left; lia).
    assert (NO1 : ~ owned B L1 A1 (s_msg S + i)).
    { intros Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ _ HM1 Ho). lia. }
    exact (proj1 (HK (s_msg S + i) DOM NO NO1 NS (ok_mnw B API S HS i ltac:(lia)))).
Qed.

Hypothesis SCMP : strcmp_c.strcmp_contract.
Hypothesis CSPN : strcspn_c.strcspn_contract.
Hypothesis NCMP : strncmp_c.strncmp_contract.
Hypothesis VIS : verb_is_c.verb_is_contract.
Hypothesis IIV : is_instance_verb_c.is_instance_verb_contract.

Lemma vr_route : forall rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  VS fx rg verbs_receive_disp.DISPATCH mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  toks D <> [] -> getr rg 18 = Z_to_bv 64 (s_msg S) ->
  getr rg 19 = verbs_receive_disp.ntokw (toks D) -> getr rg 21 = verbs_receive_disp.ntokw (toks D) ->
  (forall rg' mem2,
     VS fx rg' (route_pc (route (toks D))) mem2 md1 L1 A1 R1 O1 k1 qv None jk
       (mkCfg (mkst rg' (Z_to_bv 64 (route_pc (route (toks D)))) mem2 (seg_rom rsegs)) md1) ->
     getr rg' 18 = Mem.sx32 (Z_to_bv 64 (s_fd S)) -> getr rg' 19 = verbs_receive_disp.ntokw (toks D) ->
     getr rg' 20 = hd (Z_to_bv 64 0) (s_ps S) -> getr rg' 21 = verbs_receive_disp.ntokw (toks D) ->
     verbs_receive_disp.route_regs (route (toks D)) (length (toks D)) (getr rg' 8) (getr rg' 10) (getr rg' 11)
       (getr rg' 22) ->
     SR rsegs (mkCfg (mkst rg' (Z_to_bv 64 (route_pc (route (toks D)))) mem2 (seg_rom rsegs)) md1) P) ->
  SR rsegs c P.
Proof using HF HS SCMP CSPN NCMP VIS IIV.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST NE E18 E19 E21 K.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & _ & VR & H & FR & _).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as HR. pose proof HR as (HM1 & _ & _ & _ & _ & _ & _ & _ & HS9).
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  destruct (st_f18 B API HF _ _ _ _ HM1) as (_ & cn & SSP).
  pose proof (ok_m4k B API S HS) as M4K. pose proof (ok_m63 B API S HS) as M63.
  set (sp0 := Z_to_bv 64 (s_spf S)).
  assert (USP : bv_unsigned sp0 = s_spf S) by (apply unsigned_lit; unfold s_spf, VR_K in *; lia).
  set (lo := s_spf S - verbs_receive_disp.VR_DK).
  set (msgw := Z_to_bv 64 (s_msg S)).
  set (fdw := Z_to_bv 64 (s_fd S)).
  assert (UM : bv_unsigned msgw = s_msg S) by (apply unsigned_lit; lia).
  assert (HD : verbs_receive_disp.vr_disp (normalize rsegs mem1) lo sp0 msgw D fdw (s_ps S) cn).
  { pose proof (ok_tab B API S HS) as (TIV & TINFO & _).
    split; [exact NE|].
    split; [pose proof (ok_nD B API S HS); pose proof (ok_n8 B API S HS); lia|].
    split; [rewrite UM; exact (msg_keep _ _ _ _ HR RO1)|].
    split; [rewrite USP; apply bytes_at_normalize; [exact RO1 | exact (proj2 (proj2 FR))]|].
    split.
    { pose proof (h_x B API S _ _ _ _ _ _ _ _ H (s_cb S, s_ncb S) (or_intror (or_introl eq_refl))) as [INC _].
      assert (NC : 0 < s_ncb S) by (unfold s_ncb; lia).
      destruct (blk_low B API HF L1 A1 mem1 md1 (s_cb S) (s_ncb S) 0 HM1 INC ltac:(lia)) as (_ & HC & _).
      eapply Forall2_impl; [|exact (h_tok B API S _ _ _ _ _ _ _ _ H)].
      intros p w ((Hb & Hnz) & H1 & H2). split; [split; [apply bytes_at_normalize; [exact RO1 | exact Hb] | exact Hnz]|].
      left. unfold lo, s_spf, verbs_receive_disp.VR_DK, VR_K in *. lia. }
    split; [exact (tab_keep _ _ _ _ _ _ HR RO1 TIV ltac:(apply Z.leb_le; vm_compute; reflexivity)
                     ltac:(apply Z.leb_le; vm_compute; reflexivity))|].
    split; [exact (tab_keep _ _ _ _ _ _ HR RO1 TINFO ltac:(apply Z.leb_le; vm_compute; reflexivity)
                     ltac:(apply Z.leb_le; vm_compute; reflexivity))|].
    split.
    { destruct SSP as [S1 S2].
      split; apply bytes_at_normalize; try exact RO1; rewrite <- SEGS; apply reply.le_at_bytes;
        first [exact S1 | exact S2 | unfold VerbsMem.SSP_GOT, VerbsMem.SSP_GUARD; rewrite ?length_le8; lia]. }
    split; [apply mem_inv_normalize|].
    split.
    { rewrite USP. apply RecAns.stk_normalize; [unfold lo, s_spf, verbs_receive_disp.VR_DK, VR_K in *; lia
                                               | unfold s_spf in *; lia |].
      intros a Ha. rewrite <- SEGS. apply HS9. left. unfold lo, s_spf, verbs_receive_disp.VR_DK, VR_K in *. lia. }
    split; [rewrite USP; unfold lo; lia|].
    unfold lo, verbs_receive_disp.IMG_TOP, s_spf, verbs_receive_disp.VR_DK, VR_K in *. lia. }
  pose proof (verbs_receive_disp.vr_dispatch SCMP CSPN NCMP VIS IIV
    (reg_get rg 1) sp0 (reg_get rg 3) (reg_get rg 4) (reg_get rg 5) (reg_get rg 6) (reg_get rg 7)
    (reg_get rg 8) (reg_get rg 9) (reg_get rg 10) (reg_get rg 11) (reg_get rg 12) (reg_get rg 13)
    (reg_get rg 14) (reg_get rg 15) (reg_get rg 16) (reg_get rg 17) msgw (reg_get rg 20)
    (reg_get rg 22) (reg_get rg 23) (reg_get rg 24) (reg_get rg 25) (reg_get rg 26) (reg_get rg 27)
    (reg_get rg 28) (reg_get rg 29) (reg_get rg 30) (reg_get rg 31)
    fp_regs fp_csr (normalize rsegs mem1) lo D fdw (s_ps S) cn HD) as EVD.
  apply (@ka_w fx rc B API HF S HS rg verbs_receive_disp.DISPATCH mem1 md1 L1 A1 R1 O1 k1 qv None jk c
           [(bv_unsigned sp0 - verbs_receive_disp.VR_DK, bv_unsigned sp0)]
           (verbs_receive_disp.vr_routed sp0 (reg_get rg 3) (reg_get rg 4) (reg_get rg 8) (reg_get rg 9)
              (reg_get rg 25) (reg_get rg 26) (reg_get rg 27) fp_regs fp_csr lo (normalize rsegs mem1) fdw
              (hd (Z_to_bv 64 0) (s_ps S)) (toks D)) P HST).
  - intros x Hx Hn. cbn [Frame.outside]. split; [|exact I].
    rewrite USP. unfold s_spf, verbs_receive_disp.VR_DK, VR_K in *. lia.
  - eapply evt_mono; [eapply evt_eq; [|exact EVD]|].
    + unfold Regs6ss.mkR_of. f_equal. f_equal.
      all: first [exact (proj1 VR) | exact E18 | exact E19 | exact E21].
    + intros ms' HQ. split; [exact HQ|]. unfold verbs_receive_disp.vr_routed in HQ.
      do 19 destruct HQ as [? HQ]. destruct HQ as (m'' & -> & _ & MU & WM & _).
      do 3 eexists. split; [reflexivity | split; [exact MU | exact WM]].
  - intros R' pc' m' rg' mem2 HQ X MK. unfold verbs_receive_disp.vr_routed in HQ.
    do 19 destruct HQ as [? HQ]. destruct HQ as (m'' & E & RR & _).
    injection E as ER EP EM. subst R' pc'.
    assert (VR' : vregs S rg').
    { destruct VR as (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27).
      split; [rewrite (getr_of_eqv _ _ 2 X eq_refl); reflexivity|].
      split; [rewrite (getr_of_eqv _ _ 3 X eq_refl); exact V3|].
      split; [rewrite (getr_of_eqv _ _ 4 X eq_refl); exact V4|].
      split; [rewrite (getr_of_eqv _ _ 8 X eq_refl); exact V8|].
      split; [rewrite (getr_of_eqv _ _ 9 X eq_refl); exact V9|].
      split; [rewrite (getr_of_eqv _ _ 25 X eq_refl); exact V25|].
      split; [rewrite (getr_of_eqv _ _ 26 X eq_refl); exact V26|].
      rewrite (getr_of_eqv _ _ 27 X eq_refl); exact V27. }
    apply (K rg' mem2 (MK (route_pc (route (toks D))) eq_refl VR')).
    + rewrite (getr_of_eqv _ _ 18 X eq_refl). reflexivity.
    + rewrite (getr_of_eqv _ _ 19 X eq_refl). reflexivity.
    + rewrite (getr_of_eqv _ _ 20 X eq_refl). reflexivity.
    + rewrite (getr_of_eqv _ _ 21 X eq_refl). reflexivity.
    + rewrite (getr_of_eqv _ _ 8 X eq_refl), (getr_of_eqv _ _ 10 X eq_refl), (getr_of_eqv _ _ 11 X eq_refl),
        (getr_of_eqv _ _ 22 X eq_refl). exact RR.
Qed.

End L.
