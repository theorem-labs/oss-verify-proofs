(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module names changed; 253 of its 277 lines of code are new or changed and 550 lines of the source are left out. *)
(* Segment M04 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (plain): [0x14168, 0x141b4), K14168 -> K141b4
   (Prog/LLVMFuzzerTestOneInput_c.v's S_M04).
   Two evts taken as Section hypotheses, run one after the other on the normalized memory:
   - headamp_dup_first_contract from 0x14168 (s7 := first; for rc > 0, memcpy(first, out, 3 rc)), at the cut's FP
     state (no FP instruction), by Tac_slot.sl_run. Its premises from FR at K14168: out's first 3 rc bytes are the
     first parse's cells (the cut's out_after bytes, Spec/HeadBytes.v ha_cells_bytes, of length 3 rc for rc > 0 by
     Pod/Headamp.v answer_ok), the first block's first_req rc cells (live: Tac_b1.b1_hb), first apart from out
     (Tac_b1.b1_sep; 3 max(rc, 0) <= 3 (cap + 1)). It writes the first block only, so FR holds after it by
     Tac_b1.b1_fr_hb; the state at 0x14184 is not a cut.
   - headamp_plain_contract from 0x14184 (memset(out), reac_headamp_prop_parse, check_plain), which writes the stack
     below sp, the out block and errno at a changed FP state, run and lifted by Tac_errno.sl_mid_fp_hb_errno with the
     footprint Tac_errno.te_fp3. Its premises: the pod bytes from the cut, kept by dup_first (pod apart from first);
     first's bytes = the cells (dup_first's post for rc > 0; no cell for rc <= 0); out's cells (live); errno's cell
     (each of errno's four bytes, tp - 164 = 0x3017c, lies in a writable image segment with initial bytes, so it
     reads and is writable on any memory: SegFacts.sf_errno_cells) and the SSP GOT slot 0x1eea8 and guard 0x50490
     from the allocator relation's statics (SegFacts.sf_ssp), on the memory after dup_first; the regions apart
     (block bytes are outside the image, errno and the SSP cells inside it: SegFacts.sf_apart); frm0 from the cut.
   The cut K141b4 closes at the plain run's own FP state: s7 = first (dup_first's post, kept by plain), s3 = out and
   s1 = pod (kept by both), and the frame cell sp + 0x58 = pp (dup_first writes only first; plain writes below sp,
   out and errno). No function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 Tac_errno SegFacts.
Import ListNotations.
Open Scope Z_scope.

Section M04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis DUPF : headamp_dup_first_contract.
Hypothesis PLAIN : headamp_plain_contract.

(* A live block of hb holds no image byte. *)
Lemma m04_blk_nimg : forall g hb phi n L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  forall a, phi <= a < phi + n -> ~ in_img B a.
Proof.
  intros g hb phi n L A regs mem md HFR HP Hin a Ha Hi.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (b1_in_hb _ _ _ _ HP Hin) as HinL. apply blocks_In in HinL as (p & Ep & Hp).
  apply (ax_blocks_img (b1_ax B APIf ra empty FF) L A mem md p n (a - phi) HM Hp ltac:(lia)).
  rewrite Ep. replace (phi + (a - phi)) with a by lia. exact Hi.
Qed.

Lemma seg_M04 : S_M04 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF DUPF PLAIN.
  unfold S_M04. intros H1 g c (pp & pod & out & first & nf & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hf0 & Hf16 & Enf & H9 & Hpod0 & Hpod16 & H18 & H19 & Hout0 & Hout16 & H20 & H21 & H22 & H24 &
     HB58 & HBpod & HBout & _).
  subst nf.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  assert (Hinf : In (first, first_req (ans_rc (g_ans g)))
                   (hb_first g first (first_req (ans_rc (g_ans g))) out pod pp)) by (left; reflexivity).
  assert (Hinout : In (out, OUT_LEN (g_cap g)) (hb_first g first (first_req (ans_rc (g_ans g))) out pod pp))
    by (right; left; reflexivity).
  assert (Hinpod : In (pod, g_len g) (hb_first g first (first_req (ans_rc (g_ans g))) out pod pp))
    by (right; right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g _ first (first_req (ans_rc (g_ans g))) L A regs mem md HFR HP Hinf)
    as (STf & Hf4096 & Hfc).
  destruct (b1_hb B APIf ra empty FF g _ out (OUT_LEN (g_cap g)) L A regs mem md HFR HP Hinout)
    as (STout & Hout4096 & Houtc).
  destruct (b1_hb B APIf ra empty FF g _ pod (g_len g) L A regs mem md HFR HP Hinpod)
    as (STpod & Hpod4096 & Hpodc).
  pose proof (m04_blk_nimg g _ first _ L A regs mem md HFR HP Hinf) as HNIf.
  pose proof (m04_blk_nimg g _ out _ L A regs mem md HFR HP Hinout) as HNIout.
  pose proof (m04_blk_nimg g _ pod _ L A regs mem md HFR HP Hinpod) as HNIpod.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI0 & HRL & HM & _).
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSKc & HS47c & _).
  pose proof alloc_ceiling_value as HAC.
  pose proof (sf_len_bound (g_rest g) : 8 <= g_len g <= 5440) as Hlb.
  pose proof (sf_cap_rng (g_in g) : 0 <= g_cap g <= 9) as Hcap.
  pose proof (sf_null_rng (g_in g) : 0 <= g_null g <= 1) as Hnl.
  pose proof (sf_rc_bound (g_null g) (g_cap g) (g_rest g) ltac:(lia)) as Hrc.
  pose proof (sf_ans_ok (g_null g) (g_cap g) (g_rest g) ltac:(lia)) as HOK.
  change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g) in Hrc, HOK.
  pose proof (sf_first_max (ans_rc (g_ans g))) as Hfm.
  pose proof (sf_first_req (ans_rc (g_ans g)) ltac:(lia)) as Hfr.
  pose proof (sl_errno_val B APIf ra empty FF) as Eerr.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 560).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (ERL : head_len (g_rest g) = g_len g) by reflexivity.
  assert (EREC : head_rec (g_rest g) = g_rec g) by reflexivity.
  (* The blocks apart. *)
  assert (HSfo : first + first_req (ans_rc (g_ans g)) <= out \/ out + OUT_LEN (g_cap g) <= first).
  { assert (HD : fst (first, first_req (ans_rc (g_ans g))) + snd (first, first_req (ans_rc (g_ans g))) <=
                   fst (out, OUT_LEN (g_cap g)) \/
                 fst (out, OUT_LEN (g_cap g)) + snd (out, OUT_LEN (g_cap g)) <=
                   fst (first, first_req (ans_rc (g_ans g)))).
    { first [ exact (b1_sep B APIf ra empty g [] (first, first_req (ans_rc (g_ans g)))
                       [(out, OUT_LEN (g_cap g)); (pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (out, OUT_LEN (g_cap g)) HFR HP ltac:(cbn [app]; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [] (first, first_req (ans_rc (g_ans g)))
                       [(out, OUT_LEN (g_cap g)); (pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (out, OUT_LEN (g_cap g)) HFR HP ltac:(cbn [app]; left; reflexivity)) ]. }
    cbn [fst snd] in HD. lia. }
  assert (HSfp : first + first_req (ans_rc (g_ans g)) <= pod \/ pod + g_len g <= first).
  { assert (HD : fst (first, first_req (ans_rc (g_ans g))) + snd (first, first_req (ans_rc (g_ans g))) <=
                   fst (pod, g_len g) \/
                 fst (pod, g_len g) + snd (pod, g_len g) <= fst (first, first_req (ans_rc (g_ans g)))).
    { first [ exact (b1_sep B APIf ra empty g [] (first, first_req (ans_rc (g_ans g)))
                       [(out, OUT_LEN (g_cap g)); (pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (pod, g_len g) HFR HP ltac:(cbn [app]; right; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [] (first, first_req (ans_rc (g_ans g)))
                       [(out, OUT_LEN (g_cap g)); (pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (pod, g_len g) HFR HP ltac:(cbn [app]; right; left; reflexivity)) ]. }
    cbn [fst snd] in HD. lia. }
  assert (HSop : out + OUT_LEN (g_cap g) <= pod \/ pod + g_len g <= out).
  { assert (HD : fst (out, OUT_LEN (g_cap g)) + snd (out, OUT_LEN (g_cap g)) <= fst (pod, g_len g) \/
                 fst (pod, g_len g) + snd (pod, g_len g) <= fst (out, OUT_LEN (g_cap g))).
    { first [ exact (b1_sep B APIf ra empty g [(first, first_req (ans_rc (g_ans g)))] (out, OUT_LEN (g_cap g))
                       [(pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (pod, g_len g) HFR HP ltac:(cbn [app]; right; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [(first, first_req (ans_rc (g_ans g)))] (out, OUT_LEN (g_cap g))
                       [(pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (pod, g_len g) HFR HP ltac:(cbn [app]; right; left; reflexivity)) ]. }
    cbn [fst snd] in HD. lia. }
  (* errno and the SSP cells are apart from the blocks. *)
  assert (HEf : 0x3017c + 4 <= first \/ first + first_req (ans_rc (g_ans g)) <= 0x3017c).
  { apply (sf_apart (in_img B) first (first + first_req (ans_rc (g_ans g))) 0x3017c 4);
      [lia | lia | exact HNIf | exact (sf_errno_in B SEGS)]. }
  assert (HEout : 0x3017c + 4 <= out \/ out + OUT_LEN (g_cap g) <= 0x3017c).
  { apply (sf_apart (in_img B) out (out + OUT_LEN (g_cap g)) 0x3017c 4);
      [unfold OUT_LEN; lia | lia | exact HNIout | exact (sf_errno_in B SEGS)]. }
  assert (HEpod : 0x3017c + 4 <= pod \/ pod + g_len g <= 0x3017c).
  { apply (sf_apart (in_img B) pod (pod + g_len g) 0x3017c 4);
      [lia | lia | exact HNIpod | exact (sf_errno_in B SEGS)]. }
  assert (HGout : 0x1eea8 + 8 <= out \/ out + OUT_LEN (g_cap g) <= 0x1eea8).
  { apply (sf_apart (in_img B) out (out + OUT_LEN (g_cap g)) 0x1eea8 8);
      [unfold OUT_LEN; lia | lia | exact HNIout | exact (sf_got_in B SEGS)]. }
  assert (HUout : 0x50490 + 8 <= out \/ out + OUT_LEN (g_cap g) <= 0x50490).
  { apply (sf_apart (in_img B) out (out + OUT_LEN (g_cap g)) 0x50490 8);
      [unfold OUT_LEN; lia | lia | exact HNIout | exact (sf_guard_in B SEGS)]. }
  (* dup_first's premises: first's cells and out's first 3 rc bytes on the normalized memory. *)
  destruct (sl_rw_of_stk _ _ _ first (Z.to_nat (first_req (ans_rc (g_ans g)))) STf ltac:(lia) ltac:(lia))
    as (junkf & HRWf).
  assert (HBcells : bytes_at rsegs mem out (ha_cells_bytes (ans_cells (g_ans g)))).
  { pose proof HBout as HBo. unfold out_after in HBo. apply bytes_at_app in HBo as [HBo _]. exact HBo. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x14168) mem md _ _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply DUPF with (w := ha_cells_bytes (ans_cells (g_ans g))) (junk := junkf) (rc := ans_rc (g_ans g))
      (out := out) (first := first).
    + exact H10.
    + exact Hf0.
    + exact H19.
    + exact H22.
    + lia.
    + exact H24.
    + intros Hpos. split; [exact (sf_cells_pos (g_cap g) (g_ans g) HOK Hpos)|].
      exact (bytes_at_normalize rsegs mem _ _ HMI HBcells).
    + exact HRWf.
    + unfold OUT_LEN in HSfo. lia.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m0 & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & HE & HBf & MU & WM & MIv).
    injection HE; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    (* FR across dup_first: it writes the first block only. *)
    assert (HFR1 : FR B APIf ra empty g (hb_first g first (first_req (ans_rc (g_ans g))) out pod pp) L A regs' m' md).
    { apply (b1_fr_hb B APIf ra empty FF g _ first (first_req (ans_rc (g_ans g))) L A regs mem md regs' m'
               HFR HP Hinf).
      - intros a Ha Hs Hb. apply MU'. rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
        split; [lia | exact I].
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    (* The bytes dup_first keeps. *)
    assert (HBpod1 : bytes_at rsegs m' pod (buf (g_rec g))).
    { apply (b1_keep _ mem _ m' pod _ HMI MU Hrel); [|exact HBpod].
      change (Z.of_nat (length (buf (g_rec g)))) with (g_len g). cbn [disjoint_from].
      split; [lia | exact I]. }
    assert (HB58_1 : bytes_at rsegs m' (g_S g - 560 + 0x58) (le8 (Z_to_bv 64 pp))).
    { apply (b1_keep _ mem _ m' _ _ HMI MU Hrel); [|exact HB58].
      rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I]. }
    assert (HBfirst : bytes_at rsegs (normalize rsegs m') first (ha_cells_bytes (ans_cells (g_ans g)))).
    { destruct (Z_lt_le_dec 0 (ans_rc (g_ans g))) as [Hpos|Hnp].
      - apply (bytes_at_normalize rsegs m' _ _ Hro'). exact (b1_out _ m' first _ Hrel (HBf Hpos)).
      - rewrite (sf_cells_nonpos (g_cap g) (g_ans g) HOK Hnp). cbn [ha_cells_bytes flat_map].
        apply sl_bytes_nil. lia. }
    (* The plain run's premises on the memory after dup_first. *)
    pose proof HFR1 as (_ & _ & _ & _ & _ & _ & _ & _ & HM1 & _).
    pose proof HFR1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin1).
    assert (Hsp1 : YK11.getr regs' 2 = YK11.getr regs 2) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (Hspu1 : bv_unsigned (YK11.getr regs' 2) = g_S g - 560) by (rewrite Hsp1; exact Hspu).
    destruct (te_parse_tp B APIf ra empty FF g _ L A regs' m' md HFR1) as (_ & Etp).
    rewrite Eerr in Etp. change (0x30220 - 164) with 0x3017c in Etp.
    destruct (sf_errno_cells (normalize rsegs m')) as (ev1 & HERR1).
    destruct (b1_syms B APIf ra empty FF) as (_ & _ & _ & Eguard & Egot & _).
    destruct (sf_ssp B _ (b1_ax B APIf ra empty FF) SEGS Egot Eguard L A m' md HM1) as (HSSP1 & gv & Hgv & HSSP2).
    destruct (b1_hb B APIf ra empty FF g _ out (OUT_LEN (g_cap g)) L A regs' m' md HFR1 HP Hinout)
      as (STout1 & _ & _).
    destruct (sl_rw_of_stk _ _ _ out (Z.to_nat (OUT_LEN (g_cap g))) STout1 ltac:(lia)
                ltac:(unfold OUT_LEN in *; lia)) as (junko & HRWo).
    pose proof (b1_blk_rom B APIf ra empty FF g _ out (OUT_LEN (g_cap g)) L A regs' m' md HFR1 HP Hinout)
      as HROMout.
    rewrite <- SEGS.
    eapply (sl_mid_fp_hb_errno B APIf ra empty FF g (hb_first g first (first_req (ans_rc (g_ans g))) out pod pp)
              out (OUT_LEN (g_cap g)) L A regs' m' md (Z_to_bv 64 HEAD_PLAIN) _ _ HFR1 HP Hinout).
    + rewrite sl_mkR_of.
      apply PLAIN with (inp := g_rest g) (junk := junko) (nl := g_null g) (cap := g_cap g) (pod := pod)
        (out := out) (first := first) (lo := g_S g - 65536) (ev := ev1) (can := Z_to_bv 64 gv).
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
      * rewrite EREC. exact (bytes_at_normalize rsegs m' _ _ Hro' HBpod1).
      * lia.
      * exact HRWo.
      * exact HROMout.
      * exact HBfirst.
      * rewrite ERL. exact HSop.
      * change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g). lia.
      * lia.
      * rewrite ERL. lia.
      * change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g). lia.
      * rewrite Hspu1. unfold FRAME_LOCALS.
        apply (b8_stk_sub _ _ _ _ _ _ (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR1));
          unfold SLOT_K, SLOT_STACK; lia.
      * rewrite Hspu1. unfold MID_STACK, PARSE_STACK. lia.
      * rewrite Hspu1. Z.div_mod_to_equations. lia.
      * rewrite Hspu1. unfold FRAME_LOCALS. intros a Ha.
        apply (b8_seg_rom_hi B APIf ra empty FF). lia.
      * rewrite Etp. exact HERR1.
      * rewrite Etp, Hspu1, ERL. change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g).
        unfold FRAME_LOCALS. cbn [disjoint_from].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
      * exact (bytes_at_normalize rsegs m' _ _ Hro' HSSP1).
      * exact (bytes_at_normalize rsegs m' _ _ Hro' HSSP2).
      * rewrite Etp, Hspu1. unfold FRAME_LOCALS, PARSE_SSP_GOT. cbn [disjoint_from].
        split; [lia|]. split; [lia|]. split; [lia | exact I].
      * rewrite Etp, Hspu1. unfold FRAME_LOCALS, PARSE_SSP_GUARD. cbn [disjoint_from].
        split; [lia|]. split; [lia|]. split; [lia | exact I].
      * exact Hfrm.
      * exact (mem_inv_normalize rsegs m').
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F2 & fc2 & m2 & ev2 & -> & Hfrm2 &
                 HERR2 & MU2 & WM2 & _).
      do 5 eexists. split; [reflexivity|]. split; [exact Hfrm2|].
      split.
      * eexists. split; [exact MU2|]. split; [exact WM2|].
        intros xo Hxo HO. rewrite Hspu1, Etp in HO. unfold MID_STACK, PARSE_STACK in HO.
        assert (HEB : 0x3017c = errno_addr B) by (rewrite Eerr; reflexivity).
        first [ apply (te_fp3 B g (g_S g - 560 - (0xa0 + 0x120 + 0x50)) (g_S g - 560) out
                         (OUT_LEN (g_cap g)) out (OUT_LEN (g_cap g)) 0x3017c xo)
              | apply (te_fp3 B APIf ra empty FF g (g_S g - 560 - (0xa0 + 0x120 + 0x50)) (g_S g - 560) out
                         (OUT_LEN (g_cap g)) out (OUT_LEN (g_cap g)) 0x3017c xo) ];
          [unfold SLOT_K, SLOT_STACK; lia | lia | lia | lia | exact HEB | exact HO].
      * split; [reflexivity|]. split; reflexivity.
    + intros R2 F2 pc2 fc2 m02 regs'' m'' HQ Hx2 Hrel2 Hfrm2 HFR2.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & ev3 & HE2 &
                      Hfrm3 & HERR3 & MU3 & WM3 & _).
      injection HE2; intros; subst.
      unfold HEAD_FREE. apply H1.
      exists pp, pod, out, first, (first_req (ans_rc (g_ans g))).
      exists (mkFP F3 fc3), L, A. do 3 eexists.
      split; [reflexivity|]. split; [exact Hfrm2|]. split; [exact HFR2|]. split; [exact HP|].
      unfold rg.
      split.
      { transitivity (YK11.getr regs' 23); [rewrite (sl_getr_eqv _ _ _ Hx2); reflexivity|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
      split.
      { transitivity (YK11.getr regs' 19); [rewrite (sl_getr_eqv _ _ _ Hx2); reflexivity|].
        rewrite (sl_getr_eqv _ _ _ Hx). exact H19. }
      split.
      { transitivity (YK11.getr regs' 9); [rewrite (sl_getr_eqv _ _ _ Hx2); reflexivity|].
        rewrite (sl_getr_eqv _ _ _ Hx). exact H9. }
      unfold fsp, SLOT_FRAME.
      apply (b1_keep _ m' _ m'' _ _ Hro' MU3 Hrel2); [|exact HB58_1].
      rewrite length_le8, Hspu1, Etp. unfold MID_STACK, PARSE_STACK. cbn [disjoint_from].
      split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

End M04.
