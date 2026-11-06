(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths changed; 199 of its 247 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/WriterCall.v, with its module paths and module names changed; 105 of its 137 lines of code are new or changed and 215 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0 FrameAPI AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Cells Step Exec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger GIInit KindBGlue SlotInv SlotDefs
  SlotStep SlotStepA HState HStateRoom check_no_overread_c SlotRunB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
Import ListNotations.
Local Open Scope Z_scope.

(* From the check_0 call to the malloc call: check_0 (its contract), then segment sB. *)

Lemma ret_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 z).
Proof.
  intros z Hz He. unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ. apply bv_eq.
  rewrite !Z_to_bv_unsigned, Z.add_0_r. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small z) by lia.
  replace (Z.land z (-2)) with z.
  - rewrite ?Z.mod_small by lia; reflexivity.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec. destruct (Z.eq_dec i 0) as [->|Hne].
    + rewrite Z.bit0_odd. replace (Z.odd z) with false; [reflexivity|].
      rewrite Zodd_mod. rewrite He. reflexivity.
    + replace (Z.testbit (-2) i) with true; [rewrite andb_true_r; reflexivity|].
      replace (-2) with (Z.lnot 1) by reflexivity. rewrite Z.lnot_spec by lia.
      rewrite Z.bits_above_log2 by (cbn; lia). reflexivity.
Qed.

Lemma statics_G : forall a, alloc_statics a -> in_globals omx_G a.
Proof.
  intros a H. unfold alloc_statics in H. unfold in_globals, omx_G.
  destruct H as [H|[H|[H|H]]].
  - exists G_LIVE, 8. split; [left; reflexivity | lia].
  - exists G_PEAK, 8. split; [right; left; reflexivity | lia].
  - exists G_COUNT, 8. split; [right; right; left; reflexivity | lia].
  - exists G_FAIL, 8. split; [right; right; right; left; reflexivity | lia].
Qed.

Lemma room_nor : forall b n ok, slot_bnd b -> 0 <= n <= 3 * 2 ^ 20 -> hs_room b (nor_ops n ok).
Proof.
  intros b n ok (Hl & Hb & Hc) Hn.
  apply (hs_room_of_bound 12 (2 ^ 25)).
  - lia.
  - unfold nor_ops, dec_ops, dec_free_ops. cbv zeta. destruct ok; cbn [length app]; lia.
  - unfold hs_small, nor_ops, dec_ops, dec_free_ops. cbv zeta. destruct ok; cbn [app];
      repeat (apply Forall_cons; [cbv beta iota; lia|]); apply Forall_nil.
  - rewrite Hc. unfold CAPMAX. change (Z.of_nat 12) with 12. lia.
  - change (Z.of_nat 12) with 12. lia.
Qed.

Section B.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma ub_keep : forall L A mem md A', MR L A mem md -> ublocks_kept L A A' (0, 0) ->
  forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A').
Proof.
  intros L A mem md A' HM UK q k Hq. apply (UK q k Hq). intros E. injection E as E1 _.
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq). lia.
Qed.

Definition at_mal (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (p0 : Z) (pl : list byte) (cnt0 : Z) (b : sbound)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  exists peak cnt, slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L A regs mem md (Z_to_bv 64 (2 ^ 64 - 1)) [] peak cnt b /\
  cnt <= cnt0 + 3 /\
  getr regs 1 = Z_to_bv 64 0x13374 /\ getr regs 8 = getr regs0 8 /\
  getr regs 9 = Z_to_bv 64 (slot_nn pl) /\ getr regs 10 = Z_to_bv 64 (slot_nn pl + 1) /\
  getr regs 18 = Z_to_bv 64 p0 /\ getr regs 19 = getr regs0 19 /\ slot_nn pl <= 0x300000.

Lemma step_c0 : slot_env B API -> check_no_overread_contract B API ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md (P : config -> Prop),
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> slot_bnd b ->
  at_c0 B API regs0 L0 A0 mem0 md0 p0 pl cnt0 b L A regs mem md ->
  (forall L' A' regs' mem' md', at_mal regs0 L0 A0 mem0 md0 p0 pl cnt0 b L' A' regs' mem' md' ->
     SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 (ms_malloc B)) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x13440) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros ENV CNO regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md P HS HB
    (peak & MID & -> & -> & -> & R1 & R8 & R9 & R10 & R11 & R18 & R19 & Hnn) KC.
  pose proof ENV as (SEG & MAL & FRE & ERR & AX & BS & GF & SNK).
  pose proof HS as (SP & _ & _ & _ & _ & _ & _ & _ & _ & Hp & Hpe & _ & _ & _ & _ & _ & _ & _ & HCN & HJ).
  pose proof MID as (_ & REL & R2 & RS & FR & LG & HC & RES & RA & FZ).
  pose proof (mid_spZ B regs0 regs SP R2) as Hsp.
  pose proof (slot_sp_lo B regs0 SP) as [Hlo Hhi].
  pose proof alloc_ceiling_val as Hac. pose proof alloc_ceiling_lt as Hacl.
  destruct (start_data B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j L0 A0 mem md0 HS REL) as [BY BL].
  pose proof (slot_nn_range pl) as Hnr. pose proof (slot_db_length pl) as Hdl.
  assert (Hj : Z.of_nat j <= 3) by lia.
  assert (Hcnt : cnt0 <= 3 * 2 ^ 60) by nia.
  unfold SLOT_STACK in *.
  eapply SR_bind.
  { apply (CNO L0 A0 regs mem md0 p0 (slot_db pl) b [] peak cnt0).
    - eapply mid_pre; [exact MID | unfold CNO_STK, ALLOC_STACK, SLOT_STACK; lia |].
      rewrite R1. apply ret_lit; lia.
    - exact R10.
    - rewrite Hdl. exact R11.
    - unfold slot_db. apply BY. lia.
    - apply slot_db_nozero.
    - rewrite Hdl. lia.
    - intros Hn. exists p0, (Z.of_nat (length pl)). split; [|lia].
      apply BL. intros E. rewrite Hdl in Hn. rewrite E in Hn. cbn in Hn. lia.
    - intros a Ha. unfold in_window, CNO_STK, ALLOC_STACK. rewrite Hsp. lia.
    - exact LG.
    - lia.
    - exact RA.
    - exact RES.
    - rewrite Hdl. apply room_nor; [exact HB | lia]. }
  intros c' (L' & A' & regs' & mem' & md' & peak' & -> & RA' & GK & CP & HI & BLK & KP & UK & HPK & LG' & RES').
  rewrite R1.
  pose proof CP as (HM' & _ & _ & _ & _ & RP & _).
  assert (MID' : slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' (Z_to_bv 64 (2 ^ 64 - 1)) []
                   peak' (cnt0 + 3) b).
  { eapply mid_call; [exact ENV | exact MID | exact CP | unfold CNO_STK, ALLOC_STACK, SLOT_STACK; lia | | | | exact LG' |
      lia | | exact RA'].
    - intros a Ha. left. exact (statics_G a Ha).
    - intros q k _ Hq. exact (ub_keep L0 A0 mem md0 A' (proj1 REL) UK q k Hq).
    - exact HI.
    - eapply res_same_blocks; [exact RES | exact RES' | reflexivity | exact BLK]. }
  destruct (kb_md B API L' A' mem' md' HM') as [Hh Hl].
  eapply (kb_seg B regs' (Z_to_bv 64 0x1336c) mem' md' _ P Hh Hl SEG).
  - eapply sB_run; [exact (eq_trans (RP 9 ltac:(unfold callee_saved; lia)) R9) | lia].
  - intros ms' ->. do 3 eexists. reflexivity.
  - intros R pc' m2 regs2 HQ HG. injection HQ as ER Epc Em. subst R pc' m2.
    rewrite MAL in KC. apply (KC L' A'). exists peak', (cnt0 + 3).
    split.
    { apply (mid_regs B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' _ [] peak' (cnt0 + 3) b regs2 MID').
      - rewrite HG. reflexivity.
      - slot_kept HG. }
    split; [lia|].
    split; [rewrite HG; reflexivity|].
    split; [rewrite HG; exact (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) R8)|].
    split; [rewrite HG; exact (eq_trans (RP 9 ltac:(unfold callee_saved; lia)) R9)|].
    split; [rewrite HG; reflexivity|].
    split; [rewrite HG; exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18)|].
    split; [rewrite HG; exact (eq_trans (RP 19 ltac:(unfold callee_saved; lia)) R19)|].
    exact Hnn.
Qed.

End B.
