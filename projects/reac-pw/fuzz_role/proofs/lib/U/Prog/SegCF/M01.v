(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 218 of its 246 lines of code are new or changed and 547 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/M01.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_pin's U/Prog/SegCF/M01.v, as libreac/fuzz_ctrl's released U/Prog/SegCF/*.v copy its
   U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg -> SegCF, the segment statements from
   SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the allocator contracts in their cut-free
   forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Segment M01 of reac-pw/fuzz_role LLVMFuzzerTestOneInput (UBSan): [0x12f48, 0x13f34), K12f48 -> K13f34
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_M01).
   The plain segment (lib/Prog/Seg/M01.v) with the UBSan numbers: the frame is 544 bytes, the cursor is s6, the
   flags byte lives in the frame cell sp + 0x10, malloc is 0x160ec, and the cut's cells are sp + 0x68 (pp) and
   sp + 0x70 (pp + 0x4d14). role_build_contract is a Section hypothesis, run on the normalized memory with
   Tac_slot.sl_run; its premises come from FR at K12f48 (the input tail at the cursor, the live pp block, the stack
   region, the .data.rel.ro tables, mem_inv). The evt ends at 0x13f30 `jal malloc`; one step takes it to malloc's
   entry with ra = 0x13f34 and the request a0 = pp->len, and Tac_b1.b1_malloc_call runs the call from
   hb = [(pp, 19744)], whose kept-bytes clauses carry the three frame cells and the pp block's bytes to the cut.
   No function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1 Tac_b8.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Model Layout Spa.
Import ListNotations.
Open Scope Z_scope.

(* The bytes after the first one. *)
Lemma m01_ba_tl : forall m a b l, bytes_at rsegs m a (b :: l) -> bytes_at rsegs m (a + 1) l.
Proof.
  intros m a b l (H1 & H2 & H). cbn [length] in H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply H. cbn [length]. lia.
Qed.

Lemma m01_rest_len : forall g, Z.of_nat (length (g_rest g)) = g_k g.
Proof. intros g. unfold g_rest, g_k, g_n. destruct (g_in g) as [|b l]; cbn [tl length]; lia. Qed.

Lemma m01_rec_wf : forall g, pod_rec_wf (g_rec g).
Proof.
  intros g. unfold g_rec. apply (pod_build_wf (g_rest g) _ (snd (pod_build (g_rest g)))).
  apply surjective_pairing.
Qed.

Lemma m01_len_bound : forall g, 8 <= g_len g <= 5440.
Proof. intros g. destruct (buf_header (g_rec g) (m01_rec_wf g)) as (_ & _ & _ & H). exact H. Qed.

Lemma m01_pp_len : forall g, Z.of_nat (length (pp_bytes (g_rec g))) = POD_PROPS.
Proof. intros g. rewrite (length_pp_bytes (g_rec g) (m01_rec_wf g)). reflexivity. Qed.

(* ---- The run: K12f48 to malloc's entry with ra = 0x13f34 ---- *)
Definition m01_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (rest : list byte) (fl pp lo : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s9' s10' s11' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 ROLE_CHECK) sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (role_len rest))
                  a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (role_len rest)) s3' s4' s5' s6'
                  (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9' s10' s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0x160ec) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pp (pp_bytes (fst (pod_build rest))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    Frame.munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
    Frame.wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

Lemma m01_evt : role_build_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s6 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) -> 0 <= fl < 256 ->
    bytes_at rsegs m (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) ->
    s1 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
    0 < src -> bytes_at rsegs m src rest ->
    rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] ->
    (forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None) ->
    (src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src) ->
    src + Z.of_nat (length rest) <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs (m01_post sp gp tp F fc m rest fl pp lo)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ROLE_BUILD) fc None m (seg_rom rsegs)).
Proof.
  intros BUILD ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rest junk fl src pp lo E10 Hpp0 Hpp16 E22 E18 Hfl HFL E9 E8 Hsrc0 HBY HRW HROM HSEP HSL HPL
    ST HMID HSP16 HROMS HREL HMI.
  eapply evt_cut.
  - eapply BUILD with (rest := rest) (junk := junk) (fl := fl) (src := src) (pp := pp) (lo := lo);
      eassumption.
  - intros ms' POST.
    destruct POST as (ra' & t0' & t1' & t2' & s0' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s4' &
                      s5' & s6' & s9' & s10' & s11' & t3' & t4' & t5' & t6' & m' & -> & HB & HC10 & HC68 & HC70 &
                      MU & WM & MIv & ST2).
    unfold ROLE_MALLOC2. step. apply evt_done.
    unfold m01_post. do 24 eexists.
    split; [reflexivity|]. split; [exact HB|]. split; [exact HC10|]. split; [exact HC68|]. split; [exact HC70|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MIv | exact ST2].
Qed.

(* ---- The segment ---- *)
Section M01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.
Hypothesis BUILD : role_build_contract.

Lemma seg_M01 : S_M01 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   four segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF BUILD.
  unfold S_M01. intros H1 g c (pp & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP (H10 & Hpp0 & Hpp16 & H22 & H18 & HFL & H9 & H8).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  assert (Hinpp : In (pp, POD_PROPS) (hb_pp pp)) by (left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g (hb_pp pp) pp POD_PROPS L A regs mem md HFR HP Hinpp)
    as (STb & Hpp4096 & Hppc).
  pose proof (b1_blk_rom B APIf ra empty FF g (hb_pp pp) pp POD_PROPS L A regs mem md HFR HP Hinpp) as HROM.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI0 & HRL & HM & _).
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSKc & HS47c & _).
  pose proof alloc_ceiling_value as HAC.
  pose proof (m01_rest_len g) as Hlen.
  pose proof (m01_len_bound g) as Hlb.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 544).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  destruct (sl_rw_of_stk _ _ _ pp (Z.to_nat POD_PROPS) STb ltac:(lia) ltac:(unfold POD_PROPS; lia))
    as (junk & HRW).
  assert (HNOSEG : forall a, pp <= a < pp + POD_PROPS -> find_segment rsegs a 1 = None).
  { intros a Ha. exact (b1_blk_noseg B APIf ra empty FF L A mem md pp POD_PROPS a HM
                          (b1_in_hb _ _ _ _ HP Hinpp) Ha). }
  assert (HSRC : bytes_at rsegs mem (g_src g) (g_rest g) /\ 0 < g_src g /\
                 g_src g + Z.of_nat (length (g_rest g)) <= YM05.alloc_ceiling /\
                 (g_src g + Z.of_nat (length (g_rest g)) <= pp \/ pp + POD_PROPS <= g_src g)).
  { pose proof (ff_empty B APIf ra empty FF) as Hemp.
    pose proof (ff_empty_val B APIf ra empty FF) as Hempv.
    destruct Hpl as [(Hn0 & Hpe) | (Hn0 & Hinb)].
    - assert (Ein : g_in g = []) by (apply length_zero_iff_nil; unfold g_n in Hn0; lia).
      assert (Esrc : g_src g = empty) by (unfold g_src; rewrite Hn0, Hpe; lia).
      assert (Erest : g_rest g = []) by (unfold g_rest; rewrite Ein; reflexivity).
      assert (HQ : find_segment rsegs (g_src g) 1 <> None).
      { rewrite Esrc, Hempv. intros HH. vm_compute in HH. discriminate HH. }
      rewrite Erest. cbn [length].
      split; [apply sl_bytes_nil; rewrite Esrc; lia|].
      split; [rewrite Esrc; lia|].
      split; [rewrite Esrc, Hempv; lia|].
      destruct (Z_lt_dec (g_src g) pp) as [Hl|Hl]; [left; lia|].
      destruct (Z_lt_dec (g_src g) (pp + POD_PROPS)) as [Hr|Hr];
        [exfalso; apply HQ; apply HNOSEG; lia | right; lia].
    - destruct (b1_in_all B APIf ra empty FF g (hb_pp pp) L A regs mem md HFR HP Hn0)
        as (Hinb' & Hp4096 & Hpac & HBYT).
      assert (Ein : exists b0 r0, g_in g = b0 :: r0).
      { destruct (g_in g) as [|b0 r0] eqn:E; [exfalso; unfold g_n in Hn0; rewrite E in Hn0; cbn in Hn0; lia|].
        exists b0, r0. reflexivity. }
      destruct Ein as (b0 & r0 & Ein).
      assert (Esrc : g_src g = g_p g + 1) by (unfold g_src, g_n; rewrite Ein; cbn [length]; lia).
      assert (Erest : g_rest g = r0) by (unfold g_rest; rewrite Ein; reflexivity).
      assert (Elen : Z.of_nat (length r0) = g_n g - 1) by (unfold g_n; rewrite Ein; cbn [length]; lia).
      rewrite Ein in HBYT.
      pose proof (m01_ba_tl _ _ _ _ HBYT) as HB1.
      assert (HD : fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (g_p g, g_n g) \/
                   fst (g_p g, g_n g) + snd (g_p g, g_n g) <= fst (pp, POD_PROPS)).
      { first [ exact (b1_sep B APIf ra empty g [] (pp, POD_PROPS) [] L A regs mem md (g_p g, g_n g)
                         HFR HP ltac:(cbn [app]; exact Hinb'))
              | exact (b1_sep B APIf ra empty FF g [] (pp, POD_PROPS) [] L A regs mem md (g_p g, g_n g)
                         HFR HP ltac:(cbn [app]; exact Hinb')) ]. }
      cbn [fst snd] in HD.
      rewrite Esrc, Erest.
      split; [exact HB1|]. split; [lia|]. split; [lia|]. lia. }
  destruct HSRC as (HBY & Hsrc0 & Hsrcc & HSEP).
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x12f48) mem md
            (m01_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (@fp_regs fx') (@fp_csr fx')
               (normalize rsegs mem) (g_rest g) (g_fl g) pp (g_S g - 65536)) _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply (m01_evt BUILD) with (junk := junk) (src := g_src g).
    + exact H10.
    + exact Hpp0.
    + exact Hpp16.
    + exact H22.
    + rewrite Hlen. exact H18.
    + unfold g_fl. destruct (g_in g) as [|b l]; [lia | exact (b1_byte_rng b)].
    + rewrite Hspu. exact (bytes_at_normalize rsegs mem _ _ HMI HFL).
    + exact H9.
    + exact H8.
    + exact Hsrc0.
    + exact (bytes_at_normalize rsegs mem _ _ HMI HBY).
    + exact HRW.
    + intros a Ha. apply HROM. lia.
    + exact HSEP.
    + lia.
    + lia.
    + rewrite Hspu. unfold FRAME_LOCALS. apply (b8_stk_sub _ _ _ _ _ _ ST); lia.
    + rewrite Hspu. unfold MID_STACK. lia.
    + rewrite Hspu. Z.div_mod_to_equations. lia.
    + rewrite Hspu. unfold FRAME_LOCALS. intros a Ha.
      apply (b8_seg_rom_hi B APIf ra empty FF). lia.
    + intros a Ha. apply (b8_relro_norm B APIf ra empty FF mem a HRL HMI0).
      unfold RELRO_TBL, RELRO_TBL_END in Ha. lia.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m0 &
               -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                    m'' & HE & HB & HC10 & HC68 & HC70 & MU & WM & MIv & ST2).
    injection HE; intros; subst.
    rewrite Hspu in MU, HC10, HC68, HC70. unfold MID_STACK, FRAME_LOCALS in MU.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    pose proof (b1_out _ m' _ _ Hrel HB) as HB'.
    pose proof (b1_out _ m' _ _ Hrel HC10) as HC10'.
    pose proof (b1_out _ m' _ _ Hrel HC68) as HC68'.
    pose proof (b1_out _ m' _ _ Hrel HC70) as HC70'.
    assert (HFR' : FR B APIf ra empty g (hb_pp pp) L A regs' m' md).
    { apply (b1_fr_hb B APIf ra empty FF g (hb_pp pp) pp POD_PROPS L A regs mem md regs' m' HFR HP Hinpp).
      - intros a Ha Hs Hb. unfold SLOT_K, SLOT_STACK in Hs. apply MU'.
        rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
        split; [lia | split; [lia | exact I]].
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 ROLE_CHECK) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 (g_len g)) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g (hb_pp pp) L A regs' m' md regs' (g_len g));
      [exact HFR' | exact HP | unfold hb_pp; cbn [length]; lia
       | unfold hb_bytes, hb_pp; cbn [map fold_right snd]; unfold POD_PROPS; lia
       | reflexivity | reflexivity | reflexivity
       | rewrite E1; vm_compute; reflexivity | exact E10' | lia |].
    intros L' A' regs'' mem'' md' res HF2 HP2 RP H10' Hres0 Hres16 HKF HKB.
    rewrite E1. apply H1. exists pp, res, fx', L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF2|]. split; [exact HP2|].
    unfold rg.
    split; [exact H10'|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [etransitivity; [exact (RP 18 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 24 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 23 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split.
    { apply (b1_ba_mbyte m'); [exact HC10'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HC68'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HC70'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    apply (b1_ba_mbyte m'); [exact HB'|].
    intros i Hi. rewrite (m01_pp_len g) in Hi. apply (HKB pp POD_PROPS i Hinpp). exact Hi.
Qed.

End M01.
