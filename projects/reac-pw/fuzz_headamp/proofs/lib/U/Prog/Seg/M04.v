(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 211 of its 233 lines of code are new or changed and 552 lines of the source are left out. *)
(* Segment M04 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan): [0x147e0, 0x1482c), K147e0 -> K1482c
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_M04). Two evts, Section hypotheses, each run on the normalized memory:
   - headamp_dup_first_contract (0x147e0 `beqz a0` not taken, s7 := first, memcpy(first, out, 3 rc) at 0x147f8 for
     rc > 0, to 0x147fc) at the cut's FP state (Tac_slot.sl_run); FR follows by Tac_b1.b1_fr_hb (the first block);
   - headamp_plain_contract (memset(out) at 0x14808, reac_headamp_prop_parse at 0x14818, check_plain at 0x14828, to
     0x1482c), lifted by Tac_errno.sl_mid_fp_hb_errno (the stack below sp, the out block and errno: te_fp3) at the run's
     own FP state with rounding mode 0, which is the FP state of the cut K1482c.
   The plain run reads first = the first parse's cells (memcpy's copy of out's prefix for rc > 0; no bytes for
   rc <= 0), errno as a C4 cell and strtol's SSP cells (M03_cells.v). No malloc or free in this segment. No function is
   proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 Tac_errno.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.Seg Require Import M03_cells.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

Section M04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Hypothesis DUPFIRST : headamp_dup_first_contract.
Hypothesis PLAIN : headamp_plain_contract.

Lemma seg_M04 : S_M04 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   six segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF DUPFIRST PLAIN.
  unfold S_M04. intros H1 g c (pp & pod & out & first & nf & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hf0 & Hf16 & Enf & H9 & Hpod0 & Hpod16 & H18 & H19 & Hout0 & Hout16 & H20 & H21 & H22 & H24 &
     HB70 & HBpod & HBout & _).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  assert (Hcap : 0 <= g_cap g <= 9) by exact (mc_cap_rng _).
  assert (Hnl : 0 <= g_null g <= 1) by exact (mc_null_rng _).
  assert (Hlb : 8 <= g_len g <= 5440) by exact (mc_len_bound _).
  assert (Hrc0 : -1 <= ans_rc (g_ans g) <= g_cap g) by exact (mc_rc_rng _ _ _ (proj1 Hcap)).
  assert (Hclen : Z.of_nat (length (ha_cells_bytes (ans_cells (g_ans g)))) = 3 * Z.max (ans_rc (g_ans g)) 0)
    by exact (mc_cells_len _ _ _ (proj1 Hcap)).
  assert (Hrc : -1 <= ans_rc (g_ans g) <= 9) by lia.
  assert (Hrcap : ans_rc (g_ans g) <= g_cap g) by lia.
  destruct (mc_first_req (ans_rc (g_ans g)) Hrc) as (Hfr1 & Hfr2 & Hfr3).
  assert (Hinf : In (first, nf) (hb_first g first nf out pod pp)) by (left; reflexivity).
  assert (Hino : In (out, OUT_LEN (g_cap g)) (hb_first g first nf out pod pp)) by (right; left; reflexivity).
  assert (Hinpod : In (pod, g_len g) (hb_first g first nf out pod pp)) by (right; right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g _ first nf L A regs mem md HFR HP Hinf) as (STf & Hf4096 & Hfc).
  destruct (b1_hb B APIf ra empty FF g _ out (OUT_LEN (g_cap g)) L A regs mem md HFR HP Hino)
    as (STo & Ho4096 & Hoc).
  destruct (b1_hb B APIf ra empty FF g _ pod (g_len g) L A regs mem md HFR HP Hinpod) as (STp & Hp4096 & Hpc).
  assert (Sfo : first + nf <= out \/ out + OUT_LEN (g_cap g) <= first).
  { assert (HD : fst (first, nf) + snd (first, nf) <= fst (out, OUT_LEN (g_cap g)) \/
                 fst (out, OUT_LEN (g_cap g)) + snd (out, OUT_LEN (g_cap g)) <= fst (first, nf)).
    { eapply b1_sep with (hb1 := []) (hb2 := [(out, OUT_LEN (g_cap g)); (pod, g_len g); (pp, POD_PROPS)]);
        first [exact HFR | exact HP | exact FF | (cbn [app]; left; reflexivity)]. }
    cbn [fst snd] in HD. exact HD. }
  assert (Sfp : first + nf <= pod \/ pod + g_len g <= first).
  { assert (HD : fst (first, nf) + snd (first, nf) <= fst (pod, g_len g) \/
                 fst (pod, g_len g) + snd (pod, g_len g) <= fst (first, nf)).
    { eapply b1_sep with (hb1 := []) (hb2 := [(out, OUT_LEN (g_cap g)); (pod, g_len g); (pp, POD_PROPS)]);
        first [exact HFR | exact HP | exact FF | (cbn [app]; right; left; reflexivity)]. }
    cbn [fst snd] in HD. exact HD. }
  assert (Sop : out + OUT_LEN (g_cap g) <= pod \/ pod + g_len g <= out).
  { assert (HD : fst (out, OUT_LEN (g_cap g)) + snd (out, OUT_LEN (g_cap g)) <= fst (pod, g_len g) \/
                 fst (pod, g_len g) + snd (pod, g_len g) <= fst (out, OUT_LEN (g_cap g))).
    { eapply b1_sep with (hb1 := [(first, nf)]) (hb2 := [(pod, g_len g); (pp, POD_PROPS)]);
        first [exact HFR | exact HP | exact FF | (cbn [app]; right; left; reflexivity)]. }
    cbn [fst snd] in HD. exact HD. }
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI0 & HRL & HM & _).
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSKc & HS47c & _).
  pose proof alloc_ceiling_value as HAC.
  pose proof (sl_errno B APIf ra empty FF) as Herrc.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 608).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  destruct (sl_rw_of_stk _ _ _ first (Z.to_nat nf) STf ltac:(lia) ltac:(lia)) as (junkF & HRWF).
  assert (HBw : bytes_at rsegs mem out (ha_cells_bytes (ans_cells (g_ans g)))).
  { unfold out_after in HBout. apply bytes_at_app in HBout. exact (proj1 HBout). }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  (* ---- dup_first: first = a copy of out's first 3 rc bytes ---- *)
  eapply (sl_run regs (Z_to_bv 64 0x147e0) mem md _ _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply DUPFIRST with (w := ha_cells_bytes (ans_cells (g_ans g))) (junk := junkF)
      (rc := ans_rc (g_ans g)) (out := out) (first := first).
    + exact H10.
    + exact Hf0.
    + exact H19.
    + exact H22.
    + lia.
    + exact H24.
    + intros Hpos. split; [rewrite Hclen; lia|]. exact (bytes_at_normalize rsegs mem _ _ HMI HBw).
    + rewrite <- Enf. exact HRWF.
    + rewrite <- Enf. unfold OUT_LEN in Sfo. lia.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m0 & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    (* nf stays a variable of the cut: keep its value as two inequalities, which subst leaves alone *)
    assert (Enf2 : nf <= first_req (ans_rc (g_ans g)) <= nf) by lia. clear Enf.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & HE & HBF & MU & WM & MIv).
    injection HE; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    assert (Hsp2 : YK11.getr regs' 2 = YK11.getr regs 2) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (Hspu' : bv_unsigned (YK11.getr regs' 2) = g_S g - 608) by (rewrite Hsp2; exact Hspu).
    assert (HFR' : FR B APIf ra empty g (hb_first g first nf out pod pp) L A regs' m' md).
    { apply (b1_fr_hb B APIf ra empty FF g _ first nf L A regs mem md regs' m' HFR HP Hinf).
      - intros a Ha Hs Hb. apply MU'. rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
        split; [lia | exact I].
      - exact WM'.
      - exact Hro'.
      - exact Hsp2.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    assert (HBpod1 : bytes_at rsegs m' pod (buf (g_rec g))).
    { apply (b1_keep _ mem _ m' pod _ HMI MU Hrel); [|exact HBpod].
      change (Z.of_nat (length (buf (g_rec g)))) with (g_len g).
      cbn [disjoint_from]. split; [lia | exact I]. }
    assert (HB70' : bytes_at rsegs m' (g_S g - 608 + 0x70) (le8 (Z_to_bv 64 pp))).
    { apply (b1_keep _ mem _ m' _ _ HMI MU Hrel); [|exact HB70].
      rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I]. }
    pose proof HFR' as (_ & _ & _ & _ & _ & _ & _ & _ & HM' & _ & _ & _ & _ & _ & _ & _ & Herr' & _).
    destruct (mc_errno_norm B APIf ra empty FF m' Hro' Herr') as (ev & HERR).
    destruct (mc_ssp_norm B APIf ra empty FF L A m' md HM' Hro') as (HGOT & can & HGRD).
    destruct (te_parse_tp B APIf ra empty FF g _ L A regs' m' md HFR') as (Etp & EPE).
    pose proof (mc_errno_val B APIf ra empty FF) as Eerr.
    destruct (b1_hb B APIf ra empty FF g _ out (OUT_LEN (g_cap g)) L A regs' m' md HFR' HP Hino) as (STo' & _ & _).
    destruct (sl_rw_of_stk _ _ _ out (Z.to_nat (OUT_LEN (g_cap g))) STo' ltac:(lia) ltac:(unfold OUT_LEN in *; lia))
      as (junkO & HRWO).
    rewrite <- SEGS.
    (* ---- the plain parse and check_plain ---- *)
    eapply (sl_mid_fp_hb_errno B APIf ra empty FF g _ out (OUT_LEN (g_cap g)) L A regs' m' md
              (Z_to_bv 64 HEAD_PLAIN) _ _ HFR' HP Hino).
    + rewrite sl_mkR_of.
      apply PLAIN with (inp := g_rest g) (junk := junkO) (nl := g_null g) (cap := g_cap g) (pod := pod)
        (out := out) (first := first) (lo := g_S g - 65536) (ev := ev) (can := can).
      * rewrite (sl_getr_eqv _ _ _ Hx). exact H18.
      * rewrite (sl_getr_eqv _ _ _ Hx). exact H19.
      * rewrite (sl_getr_eqv _ _ _ Hx). exact H20.
      * rewrite (sl_getr_eqv _ _ _ Hx). exact H21.
      * rewrite (sl_getr_eqv _ _ _ Hx). exact H22.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * exact Hnl.
      * exact Hcap.
      * lia.
      * exact Hpod16.
      * exact (bytes_at_normalize rsegs m' _ _ Hro' HBpod1).
      * lia.
      * exact HRWO.
      * intros a Ha. exact (b1_blk_rom B APIf ra empty FF g _ out _ L A regs' m' md HFR' HP Hino a Ha).
      * change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g).
        destruct (Z_lt_dec 0 (ans_rc (g_ans g))) as [Hpos|Hnpos].
        -- exact (bytes_at_normalize rsegs m' _ _ Hro' (b1_out _ m' _ _ Hrel (HBF Hpos))).
        -- assert (Ec : ans_cells (g_ans g) = []).
           { apply (mc_cells_nil (g_null g) (g_cap g) (g_rest g) (proj1 Hcap)).
             change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g). lia. }
           rewrite Ec. apply sl_bytes_nil. lia.
      * exact Sop.
      * change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g). unfold OUT_LEN in *. lia.
      * unfold OUT_LEN in *. lia.
      * change (head_len (g_rest g)) with (g_len g). lia.
      * change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g). lia.
      * rewrite Hspu'. unfold FRAME_LOCALS.
        apply (b8_stk_sub _ _ _ _ _ _ (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR'));
          unfold SLOT_K, SLOT_STACK; lia.
      * rewrite Hspu'. unfold MID_STACK, PARSE_STACK. lia.
      * rewrite Hspu'. Z.div_mod_to_equations. lia.
      * rewrite Hspu'. unfold FRAME_LOCALS. intros a Ha.
        apply (b8_seg_rom_hi B APIf ra empty FF). lia.
      * rewrite EPE. exact HERR.
      * rewrite EPE. change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g).
        change (head_len (g_rest g)) with (g_len g). cbn [disjoint_from].
        pose proof (mc_errno_blk B APIf ra empty FF L A m' md pod (g_len g) HM' (b1_in_hb _ _ _ _ HP Hinpod)
                      ltac:(lia)) as D1.
        pose proof (mc_errno_blk B APIf ra empty FF L A m' md out _ HM' (b1_in_hb _ _ _ _ HP Hino)
                      ltac:(unfold OUT_LEN; lia)) as D2.
        pose proof (mc_errno_blk B APIf ra empty FF L A m' md first nf HM' (b1_in_hb _ _ _ _ HP Hinf)
                      ltac:(lia)) as D3.
        repeat split; lia.
      * unfold PARSE_SSP_GOT, PARSE_SSP_GUARD. exact HGOT.
      * unfold PARSE_SSP_GUARD. exact HGRD.
      * rewrite EPE, Eerr. unfold PARSE_SSP_GOT. cbn [disjoint_from].
        pose proof (mc_got_blk B APIf ra empty FF L A m' md out _ HM' (b1_in_hb _ _ _ _ HP Hino)
                      ltac:(unfold OUT_LEN; lia)) as D1.
        repeat split; lia.
      * rewrite EPE, Eerr. unfold PARSE_SSP_GUARD. cbn [disjoint_from].
        pose proof (mc_guard_blk B APIf ra empty FF L A m' md out _ HM' (b1_in_hb _ _ _ _ HP Hino)
                      ltac:(unfold OUT_LEN; lia)) as D1.
        repeat split; lia.
      * exact Hfrm.
      * exact (mem_inv_normalize rsegs m').
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F2 & fc2 & m2 & ev2 & -> &
                 Hfrm2 & _ & MU2 & WM2 & _).
      do 5 eexists. split; [reflexivity|]. split; [exact Hfrm2|].
      split; [|split; [reflexivity | split; reflexivity]].
      eexists. split; [exact MU2|]. split; [exact WM2|].
      intros y0 Hy0 HO.
      apply te_fp3 with (lo := bv_unsigned (YK11.getr regs' 2) - MID_STACK) (hi := bv_unsigned (YK11.getr regs' 2))
        (o := out) (k := OUT_LEN (g_cap g)) (E := PARSE_ERRNO (YK11.getr regs' 4)).
      * rewrite Hspu'. unfold SLOT_K, SLOT_STACK, MID_STACK, PARSE_STACK. lia.
      * rewrite Hspu'. lia.
      * lia.
      * lia.
      * exact EPE.
      * exact HO.
    + intros R2 F2 pc2 fc2 m02 regs2 m2 HQ2 Hx2 Hrel2 Hfrm2 HFR2.
      destruct HQ2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & ev3 & HE2 &
                       _ & _ & MU2 & _).
      injection HE2; intros; subst.
      unfold HEAD_FREE.
      lazymatch goal with
      | |- SR _ (mkCfg (@YK11.mkst ?f _ _ _ _) _) _ =>
          apply H1; exists pp, pod, out, first, nf, f, L, A, regs2, m2, md
      end.
      split; [reflexivity|]. split; [exact Hfrm2|]. split; [exact HFR2|]. split; [exact HP|].
      unfold rg. split; [|split; [|split]].
      * rewrite (sl_getr_eqv _ _ _ Hx2). transitivity (YK11.getr regs' 23); [reflexivity|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx2). transitivity (YK11.getr regs' 19); [reflexivity|].
        rewrite (sl_getr_eqv _ _ _ Hx). exact H19.
      * rewrite (sl_getr_eqv _ _ _ Hx2). transitivity (YK11.getr regs' 9); [reflexivity|].
        rewrite (sl_getr_eqv _ _ _ Hx). exact H9.
      * apply (b1_keep _ m' _ m2 _ _ Hro' MU2 Hrel2); [|exact HB70'].
        rewrite length_le8, Hspu', EPE, Eerr. unfold fsp, SLOT_FRAME, MID_STACK, PARSE_STACK, OUT_LEN in *.
        change (Z.of_nat 8) with 8. cbn [disjoint_from].
        repeat split; lia.
Qed.

End M04.
