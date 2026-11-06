(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths changed; 199 of its 247 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/WriterCall.v, with its module paths and module names changed; 105 of its 137 lines of code are new or changed and 215 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/SlotStepB.v, with its addresses changed; 196 of its 247 lines of code are new or changed and 86 lines of the source are left out. *)
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
  SlotStep SlotStepA SlotStepB HState HStateRoom memcpy_c fuzz_alloc_live_c fuzz_alloc_peak_reset_c SlotRunA.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
Import ListNotations.
Local Open Scope Z_scope.

(* From the malloc call to the decoder call: malloc (its contract), then segment sC (the copy of the text and its
   NUL, fuzz_alloc_live, fuzz_alloc_peak_reset). *)

Lemma pw_in2 : forall {X} (R : X -> X -> Prop) l x y, pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros X R l. induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|].
  cbn [pairwise] in H. destruct H as [H1 H2]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso. exact (Hne eq_refl).
  - left. exact (H1 y Hy).
  - right. exact (H1 x Hx).
  - exact (IH x y H2 Hx Hy Hne).
Qed.

Lemma pw_mid : forall {X} (R : X -> X -> Prop) b1 x b2 y, pairwise R (b1 ++ x :: b2) -> In y (b1 ++ b2) ->
  R x y \/ R y x.
Proof.
  intros X R b1. induction b1 as [|z b1 IH]; intros x b2 y H Hy; cbn [app pairwise] in H; cbn [app In] in Hy.
  - left. exact (proj1 H y Hy).
  - destruct H as [H1 H2]. destruct Hy as [<-|Hy].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH x b2 y H2 Hy).
Qed.

Lemma cap_of : forall b b', slot_bnd b -> sb_cap b' = sb_cap b -> sb_live b' <= sb_live b + 2 ->
  sb_bytes b' <= sb_bytes b + 2 ^ 25 -> hs_cap b' 200 (2 ^ 25).
Proof.
  intros b b' (Hl & Hb & Hc) E1 E2 E3. unfold hs_cap. rewrite E1, Hc. unfold CAPMAX.
  change (Z.of_nat 200) with 200. lia.
Qed.

Lemma room_of : forall b b' n, slot_bnd b -> sb_cap b' = sb_cap b -> sb_live b' <= sb_live b + 2 ->
  sb_bytes b' <= sb_bytes b + 2 ^ 25 -> 0 <= n <= 2 ^ 25 -> room_slots b' n.
Proof.
  intros b b' n HB E1 E2 E3 Hn. apply (hs_cap_room b' 199 (2 ^ 25) n); [lia | exact Hn |].
  exact (cap_of b b' HB E1 E2 E3).
Qed.

Lemma live_G : forall x, G_LIVE <= x < G_LIVE + 24 -> in_globals omx_G x.
Proof.
  intros x Hx. unfold in_globals, omx_G, G_LIVE in *.
  destruct (Z_lt_ge_dec x 0x33458); [exists G_LIVE, 8; split; [left; reflexivity | unfold G_LIVE; lia]|].
  destruct (Z_lt_ge_dec x 0x33460); [exists G_PEAK, 8; split; [right; left; reflexivity | unfold G_PEAK; lia]|].
  exists G_COUNT, 8. split; [right; right; left; reflexivity | unfold G_COUNT; lia].
Qed.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma blk_apart : forall L A mem md q k q' k', MR L A mem md -> In (q, k) (user_blocks A) ->
  In (q', k') (user_blocks A) -> ptr_addr L q <> ptr_addr L q' ->
  ptr_addr L q + k <= ptr_addr L q' \/ ptr_addr L q' + k' <= ptr_addr L q.
Proof.
  intros L A mem md q k q' k' HM H1 H2 Hne.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as PW.
  assert (I1 : In (ptr_addr L q, k) (blocks L A))
    by (unfold blocks; apply in_map_iff; exists (q, k); split; [reflexivity | exact H1]).
  assert (I2 : In (ptr_addr L q', k') (blocks L A))
    by (unfold blocks; apply in_map_iff; exists (q', k'); split; [reflexivity | exact H2]).
  destruct (pw_in2 _ _ _ _ PW I1 I2 ltac:(intros E; injection E as E _; exact (Hne E))) as [D|D];
    unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
Qed.

Lemma glob_img : slot_env B API -> forall x, in_globals omx_G x -> in_img B x.
Proof. intros (_ & _ & _ & _ & _ & _ & GF & _) x Hx. exact (proj1 (GF x Hx)). Qed.

Lemma glob_free : slot_env B API -> forall L A mem md x, MR L A mem md -> in_globals omx_G x -> ~ owned B L A x.
Proof.
  intros (_ & _ & _ & _ & _ & _ & GF & _) L A mem md x HM Hx.
  destruct (GF x Hx) as (_ & _ & _ & _ & H). exact (proj1 (H L A mem md HM)).
Qed.

Definition at_dec (regs0 : bvmap 5 word) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (p0 : Z) (pl : list byte) (cnt0 : Z) (b : sbound)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  exists cnt pt text,
  slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L A regs mem md (Z_to_bv 64 (2 ^ 64 - 1)) [] 0 cnt
    (sb_malloc b (slot_nn pl + 1)) /\
  cnt <= cnt0 + 3 /\
  In (pt, slot_nn pl + 1) (user_blocks A) /\ ptr_addr L pt = text /\ text mod 16 = 0 /\
  (forall q k, In (q, k) (user_blocks A0) -> 0 < k -> ptr_addr L0 q <> text) /\
  Mem.bytes_at (ms_segs B) mem text (slot_db pl ++ [Z_to_bv 8 0]) /\
  getr regs 1 = Z_to_bv 64 0x133b0 /\ getr regs 8 = Z_to_bv 64 text /\ getr regs 9 = Z_to_bv 64 (slot_nn pl) /\
  getr regs 10 = Z_to_bv 64 text /\ getr regs 11 = Z_to_bv 64 (spZ regs0 - 48) /\
  getr regs 18 = Z_to_bv 64 p0 /\ getr regs 19 = Z_to_bv 64 0 /\ slot_nn pl <= 0x300000.

Lemma step_mal : slot_env B API -> malloc_contract B API -> memcpy_contract -> fuzz_alloc_live_contract ->
  fuzz_alloc_peak_reset_contract ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md (P : config -> Prop),
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> slot_bnd b ->
  at_mal B API regs0 L0 A0 mem0 md0 p0 pl cnt0 b L A regs mem md ->
  (forall L' A' regs' mem' md', at_dec regs0 L0 A0 mem0 md0 p0 pl cnt0 b L' A' regs' mem' md' ->
     SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 0x14e90) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros ENV MALC MEMCPY FAL FAPR regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L A regs mem md P HS HB
    (peak & cnt & MID & Hcn & R1 & R8 & R9 & R10 & R18 & R19 & Hnn) KC.
  pose proof ENV as (SEG & MAL & FRE & ERR & AX & BS & GF & SNK).
  pose proof HS as (SP & _ & _ & _ & _ & _ & _ & _ & _ & Hp & Hpe & _ & _ & _ & _ & _ & _ & _ & HCN & HJ).
  pose proof MID as (_ & REL & R2 & RS & FR & LG & HC & RES & RA & FZ).
  pose proof (mid_spZ B regs0 regs SP R2) as Hsp.
  pose proof (slot_sp_lo B regs0 SP) as [Hlo Hhi].
  pose proof alloc_ceiling_val as Hac. pose proof alloc_ceiling_lt as Hacl.
  pose proof (slot_nn_range pl) as Hnr. pose proof (slot_db_length pl) as Hdl.
  pose proof REL as (HM & _).
  pose proof HB as (HBl & HBb & HBc).
  unfold SLOT_STACK in *.
  eapply SR_bind.
  { apply (MALC L A regs mem md (slot_nn pl + 1) b).
    - apply (proj2 (call_pre_k_alloc B MR L A regs mem md)).
      eapply mid_pre; [exact MID | unfold ALLOC_STACK, SLOT_STACK; lia |]. rewrite R1. apply ret_lit; lia.
    - exact RA.
    - exact R10.
    - exact RES.
    - apply (room_of b b); [exact HB | reflexivity | lia | lia | lia]. }
  intros c' (L' & A' & regs' & mem' & md' & res & -> & CP & R10' & Hr0 & Hr16 & FB & BLs & BK & RA' & GK & UB &
    INIT & REG & RES').
  rewrite R1.
  pose proof CP as (HM' & _ & _ & _ & PA & RP & _).
  assert (LG' : ledger B L' A' mem' [] peak cnt (2 ^ 64 - 1)).
  { eapply ledger_frame; [exact LG | intros a k [] |].
    intros x [Hx|(a & k & [] & _)].
    apply (kb_post_globals B API omx_G ALLOC_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' x GF HM CP).
    - rewrite Hsp. unfold ALLOC_STACK. lia.
    - exact (statics_G x Hx).
    - intros []. }
  assert (MID1 : slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs' mem' md' (Z_to_bv 64 (2 ^ 64 - 1)) [] peak cnt
                   (sb_malloc b (slot_nn pl + 1))).
  { eapply mid_call; [exact ENV | exact MID | exact CP | unfold ALLOC_STACK, SLOT_STACK; lia | intros a [] | | | exact LG' | lia |
      exact RES' | exact RA'].
    - intros q k _ Hq. exact (UB q k Hq).
    - intros _. exact INIT. }
  pose proof MID1 as (_ & REL1 & R21 & RS1 & _).
  destruct BLs as (b1 & b2 & Eb' & Eb).
  assert (Hin' : In (res, slot_nn pl + 1) (blocks L' A')) by (rewrite Eb'; apply in_or_app; right; left; reflexivity).
  destruct (HsKindB.in_blocks L' A' res _ Hin') as (pt & Hpt & Ept).
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') as PW. rewrite Eb' in PW.
  assert (DJ : forall a k, In (a, k) (blocks L A) -> res + (slot_nn pl + 1) <= a \/ a + k <= res).
  { intros a k Hak. rewrite Eb in Hak.
    destruct (pw_mid _ b1 (res, slot_nn pl + 1) b2 (a, k) PW Hak) as [D|D];
      unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  assert (FA0 : forall q k, In (q, k) (user_blocks A0) -> 0 < k -> ptr_addr L0 q <> res).
  { intros q k Hq Hk E. pose proof REL as (_ & _ & _ & _ & _ & U & _). destruct (U q k Hq) as [Hq1 Ep].
    assert (Hb : In (ptr_addr L0 q, k) (blocks L A)).
    { unfold blocks. apply in_map_iff. exists (q, k). split; [cbn [fst snd]; rewrite Ep; reflexivity | exact Hq1]. }
    rewrite E in Hb. destruct (DJ _ _ Hb); lia. }
  destruct (kb_md B API L' A' mem' md' HM') as [Hh Hl].
  pose proof FB as (Hr4096 & Hrc & FBi).
  destruct (start_data B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j L' A' mem' md' HS REL1) as [BY _].
  destruct (start_data B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j L A mem md HS REL) as [_ BL].
  assert (Hsp' : bv_unsigned (getr regs' 2) = spZ regs0 - 48)
    by exact (eq_trans (f_equal bv_unsigned (RP 2 ltac:(unfold callee_saved; lia))) Hsp).
  pose proof LG' as ((W1 & W2 & W3 & W4) & _ & HC1 & HF1 & _ & _).
  eapply (kb_seg B regs' (Z_to_bv 64 0x13374) mem' md' _ P Hh Hl SEG).
  - eapply sC_run with (text := res) (nn := slot_nn pl) (p := p0) (db := slot_db pl) (live := Z_to_bv 64 0).
    + exact MEMCPY.
    + exact FAL.
    + exact FAPR.
    + exact R10'.
    + exact (eq_trans (RP 9 ltac:(unfold callee_saved; lia)) R9).
    + exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18).
    + lia.
    + exact Hdl.
    + lia.
    + rewrite Hsp'. lia.
    + destruct (Z_le_gt_dec (res + slot_nn pl + 1) 0x33450) as [H1|H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (0x33450 + 24) res) as [H2|H2]; [right; exact H2|].
      exfalso. apply (FBi (Z.max res 0x33450 - res)); [lia|].
      replace (res + (Z.max res 0x33450 - res)) with (Z.max res 0x33450) by lia.
      apply (glob_img ENV). apply live_G. unfold G_LIVE. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      pose proof (mr_blocks _ _ (aa_laws API) _ _ _ _ pt _ i HM' Hpt Hi) as (Hpr & _).
      rewrite <- Ept in Hpr. rewrite <- SEG. exact (present_writable B mem' _ Hpr).
    + intros i Hi. unfold Mem.ro_addr. rewrite Mem.wa_unsigned by lia.
      destruct (find_segment rsegs (res + i) 1) as [seg|] eqn:F; [|reflexivity].
      exfalso. apply (FBi i Hi). exact (seg_img B API ENV _ _ F).
    + intros Hn0. split; [lia|]. split.
      * rewrite <- SEG. unfold slot_db. apply BY. lia.
      * assert (Hne : pl <> []) by (intros E; rewrite E in Hn0; cbn in Hn0; lia).
        destruct (DJ _ _ (BL Hne)); lia.
    + rewrite <- SEG. apply word_mem_le8; [exact W1 | lia | unfold G_LIVE; lia | unfold G_LIVE; lia].
    + rewrite <- SEG. apply (globals_wr_at B API omx_G mem' G_PEAK peak GF); [|exact W2].
      intros k Hk. apply live_G. unfold G_LIVE, G_PEAK. lia.
    + rewrite <- SEG. exact RA'.
  - intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m2 regs2 HQ HG.
    destruct HQ as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & EQ & MU & WM &
      RA2 & BYT & PK2).
    injection EQ as ER Epc Em. subst R pc' m2.
    assert (KK : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs2 (Z_to_bv 5 k) = getr regs' (Z_to_bv 5 k))
      by (slot_kept HG).
    assert (LG2 : ledger B L' A' m3 [] 0 cnt (2 ^ 64 - 1)).
    { assert (TXg : forall x, in_globals omx_G x -> ~ (res <= x < res + slot_nn pl + 1)).
      { intros x Hg Hx. apply (FBi (x - res)); [lia|]. replace (res + (x - res)) with x by lia.
        exact (glob_img ENV x Hg). }
      assert (HWo : forall a, (a = G_LIVE \/ a = G_COUNT \/ a = G_FAIL) -> forall x, a <= x < a + 8 ->
                Frame.outside [(res, res + slot_nn pl + 1); (0x33458, 0x33458 + 8)] x).
      { intros a Ha x Hx. cbn [Frame.outside]. split; [|split; [|exact I]].
        - apply TXg. unfold in_globals, omx_G. exists a, 8. split; [|lia].
          destruct Ha as [-> | [-> | ->]]; cbn [In]; auto 10.
        - unfold G_LIVE, G_COUNT, G_FAIL in Ha. lia. }
      split; [|split; [cbn [lsum]; lia | split; [exact HC1 | split; [exact HF1 | split; constructor]]]].
      split; [|split; [|split]].
      - apply (HsKindB.word_mem_munch _ _ mem' m3 G_LIVE _ MU); [unfold G_LIVE; lia | unfold G_LIVE; lia | |exact W1].
        apply HWo. left. reflexivity.
      - rewrite <- SEG in PK2. pose proof (bytes_at_le8_word (ms_segs B) m3 0x33458 (Z_to_bv 64 0) PK2) as W.
        rewrite MState.unsigned_lit in W by lia. exact W.
      - apply (HsKindB.word_mem_munch _ _ mem' m3 G_COUNT _ MU); [unfold G_COUNT; lia | unfold G_COUNT; lia | |exact W3].
        apply HWo. right. left. reflexivity.
      - apply (HsKindB.word_mem_munch _ _ mem' m3 G_FAIL _ MU); [unfold G_FAIL; lia | unfold G_FAIL; lia | |exact W4].
        apply HWo. right. right. reflexivity. }
    assert (MID2 : slot_mid B API regs0 L0 A0 mem0 md0 cnt0 L' A' regs2 m3 md' (Z_to_bv 64 (2 ^ 64 - 1)) [] 0 cnt
                     (sb_malloc b (slot_nn pl + 1))).
    { eapply mid_A; [exact ENV | exact MID1 | exact MU | exact WM | | | | | | | exact LG2 | lia | rewrite SEG; exact RA2].
      - intros x Hx _. cbn [Frame.outside]. split; [|split; [|exact I]]; lia.
      - intros x Hi Hg. cbn [Frame.outside]. split; [|split; [|exact I]].
        + intros Hx. apply (FBi (x - res)); [lia|]. replace (res + (x - res)) with x by lia. exact Hi.
        + intros Hx. apply Hg. apply live_G. unfold G_LIVE. lia.
      - intros x Hx Ho. cbn [Frame.outside]. split; [|split; [|exact I]].
        + intros Hxr. pose proof (mr_blocks _ _ (aa_laws API) _ _ _ _ pt _ (x - res) HM' Hpt ltac:(lia)) as (_ & _ & _ & No).
          rewrite <- Ept in No. replace (res + (x - res)) with x in No by lia. exact (No Ho).
        + intros Hxr. apply (glob_free ENV L' A' mem' md' x HM'); [apply live_G; unfold G_LIVE; lia | exact Ho].
      - intros q k i Hq Hi. pose proof REL1 as (_ & _ & _ & _ & _ & U1 & _). destruct (U1 q k Hq) as [Hq1 Ep].
        cbn [Frame.outside]. split; [|split; [|exact I]].
        + intros Hx. assert (Hne : ptr_addr L' q <> ptr_addr L' pt) by (rewrite Ep, <- Ept; exact (FA0 q k Hq ltac:(lia))).
          destruct (blk_apart L' A' mem' md' q k pt _ HM' Hq1 Hpt Hne); rewrite <- Ept, Ep in *; lia.
        + intros Hx. apply (ax_blocks_img AX L' A' mem' md' q k i HM' Hq1 Hi). rewrite Ep.
          apply (glob_img ENV). apply live_G. unfold G_LIVE. lia.
      - rewrite HG. exact R21.
      - intros k Hk. rewrite (KK k Hk). exact (RS1 k Hk). }
    apply (KC L' A'). exists cnt, pt, res.
    split; [exact MID2|]. split; [exact Hcn|]. split; [exact Hpt|]. split; [symmetry; exact Ept|].
    split; [exact Hr16|]. split; [exact FA0|]. split; [rewrite SEG; exact BYT|].
    split; [rewrite HG; reflexivity|]. split; [rewrite HG; reflexivity|].
    split; [rewrite HG; exact (eq_trans (RP 9 ltac:(unfold callee_saved; lia)) R9)|].
    split; [rewrite HG; reflexivity|].
    split; [rewrite HG; exact R21|].
    split; [rewrite HG; exact (eq_trans (RP 18 ltac:(unfold callee_saved; lia)) R18)|].
    split; [rewrite HG; reflexivity|].
    exact Hnn.
Qed.

End C.
