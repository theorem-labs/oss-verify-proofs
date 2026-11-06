(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 288 of its 319 lines of code are new or changed and 544 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/M01.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_role's U/Prog/SegCF/M01.v, as libreac/fuzz_ctrl's released
   U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg -> SegCF, the
   segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the allocator
   contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Segment M01 of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (UBSan): [0x13110, 0x1420c), K13110 -> K1420c
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_M01).
   Ported from reac-pw/fuzz_role's U/Prog/Seg/M01.v, re-walked at rate's
   numbers: the frame is 592 bytes; at K13110 (U/Prog/SlotInv.Inv_K13110) a0 = pp, s7 = the input cursor g_src g,
   s1 = the bytes left g_k g, s2 = fl, s5 = mask, s4 = b3, the cells sp + 0x30 = buflen, sp + 0x28 = b4 << 8,
   sp + 0x20 = b5, sp + 0x18 = b6 << 8, s3 = 19744, s0 = 0x5000; malloc is 0x16a7c.
   rate_build_contract is a Section hypothesis, run on the normalized memory with Tac_slot.sl_run at rest := g_rest g
   (the input after its seven header bytes) at src := g_src g, the header values of the ghost and lo := S - 65536
   (the slot's stack window [S - SLOT_K, S)); its premises come from FR at K13110 (the input tail at the cursor, the
   live pp block, the stack window, the .data.rel.ro tables [0x1ecc8, 0x1edc0) inside frame_RELRO's first block
   (0x1ecb8, 448), mem_inv). The evt ends at 0x14208 `jal malloc`; one step takes it to malloc's entry with
   ra = 0x1420c and the request a0 = pp->len, and Tac_b1.b1_malloc_call runs the call from hb = [(pp, 19744)], whose
   kept-bytes clauses carry the header cells sp + 8 .. sp + 0x38, the cells sp + 0x98 (pp + 0x4d14) and sp + 0xd8
   (pp) and the pp block's bytes to the cut; s2 = fl, s4 = len, s8 = pp and s11 = pp + 0x4000 are callee-saved
   across malloc. No function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1 Tac_b8.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout Spa.
Import ListNotations.
Open Scope Z_scope.

(* The bytes after the first one. *)
Lemma m01_ba_tl : forall m a b l, bytes_at rsegs m a (b :: l) -> bytes_at rsegs m (a + 1) l.
Proof.
  intros m a b l (H1 & H2 & H). cbn [length] in H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply H. cbn [length]. lia.
Qed.

(* The bytes after the first k (all of them when fewer). *)
Lemma m01_ba_skipn : forall k m a l, bytes_at rsegs m a l ->
  bytes_at rsegs m (a + Z.min (Z.of_nat k) (Z.of_nat (length l))) (skipn k l).
Proof.
  induction k as [|k IH]; intros m a l H.
  - cbn [skipn]. replace (a + Z.min (Z.of_nat 0) (Z.of_nat (length l))) with a by lia. exact H.
  - destruct l as [|b l].
    + cbn [skipn length]. replace (a + Z.min (Z.of_nat (S k)) (Z.of_nat 0)) with a by lia. exact H.
    + cbn [skipn length]. pose proof (IH m (a + 1) l (m01_ba_tl m a b l H)) as H'.
      replace (a + Z.min (Z.of_nat (S k)) (Z.of_nat (S (length l))))
        with (a + 1 + Z.min (Z.of_nat k) (Z.of_nat (length l))) by lia.
      exact H'.
Qed.

Lemma m01_u8_rng : forall g i, 0 <= g_u8 g i < 256.
Proof.
  intros g i. unfold g_u8. destruct (nth_error (g_in g) i) as [b|]; [exact (b1_byte_rng b) | lia].
Qed.

Lemma m01_rest_len : forall g, Z.of_nat (length (g_rest g)) = g_k g.
Proof. intros g. unfold g_rest, g_k, g_n. rewrite length_skipn. lia. Qed.

Lemma m01_rec_wf : forall g, pod_rec_wf (g_rec g).
Proof.
  intros g. unfold g_rec. apply (pod_build_wf (g_rest g) _ (snd (pod_build (g_rest g)))).
  apply surjective_pairing.
Qed.

Lemma m01_len_bound : forall g, 8 <= g_len g <= 5440.
Proof. intros g. destruct (buf_header (g_rec g) (m01_rec_wf g)) as (_ & _ & _ & H). exact H. Qed.

Lemma m01_pp_len : forall g, Z.of_nat (length (pp_bytes (g_rec g))) = POD_PROPS.
Proof. intros g. rewrite (length_pp_bytes (g_rec g) (m01_rec_wf g)). reflexivity. Qed.

(* ---- The run: K13110 to malloc's entry with ra = 0x1420c ---- *)
Definition m01_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (rest : list byte) (fl mask buflen b3 b4 b5 b6 pp lo : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s9' s10' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 RATE_CHECK) sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (rate_len rest))
                  a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 fl) s3' (Z_to_bv 64 (rate_len rest)) s5' s6' s7'
                  (Z_to_bv 64 pp) s9' s10' (Z_to_bv 64 (pp + POD_LEN_OFF)) t3' t4' t5' t6')
             F (Z_to_bv 64 0x16a7c) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pp (pp_bytes (fst (pod_build rest))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 b3)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 mask)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x38) (le8 (Z_to_bv 64 fl)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x98) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0xd8) (le8 (Z_to_bv 64 pp)) /\
    Frame.munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
    Frame.wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

Lemma m01_evt : rate_build_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s7 = Z_to_bv 64 src -> s1 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s2 = Z_to_bv 64 fl -> s5 = Z_to_bv 64 mask -> s4 = Z_to_bv 64 b3 ->
    bytes_at rsegs m (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) ->
    0 <= fl < 256 -> 0 <= mask < 256 -> 0 <= buflen < 24 ->
    0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
    s3 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
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
    evt rsegs (m01_post sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 pp lo)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATE_BUILD) fc None m (seg_rom rsegs)).
Proof.
  intros BUILD ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rest junk fl mask buflen b3 b4 b5 b6 src pp lo
    E10 Hpp0 Hpp16 E23 E9 E18 E21 E20 HC30 HC28 HC20 HC18 Hfl Hmk Hbl Hb3 Hb4 Hb5 Hb6 E19 E8
    Hsrc0 HBY HRW HROM HSEP HSL HPL ST HMID HSP16 HROMS HREL HMI.
  eapply evt_cut.
  - eapply BUILD with (rest := rest) (junk := junk) (fl := fl) (mask := mask) (buflen := buflen)
      (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) (src := src) (pp := pp) (lo := lo); eassumption.
  - intros ms' POST.
    destruct POST as (ra' & t0' & t1' & t2' & s0' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s5' &
                      s6' & s7' & s9' & s10' & t3' & t4' & t5' & t6' & m' & -> & HB & HK8 & HK10 & HK18 & HK20 &
                      HK28 & HK30 & HK38 & HK98 & HKd8 & MU & WM & MIv & ST2).
    unfold RATE_MALLOC2. step. apply evt_done.
    unfold m01_post. do 23 eexists.
    split; [reflexivity|]. split; [exact HB|]. split; [exact HK8|]. split; [exact HK10|].
    split; [exact HK18|]. split; [exact HK20|]. split; [exact HK28|]. split; [exact HK30|].
    split; [exact HK38|]. split; [exact HK98|]. split; [exact HKd8|].
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
Hypothesis BUILD : rate_build_contract.

Lemma seg_M01 : S_M01 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   five segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF BUILD.
  unfold S_M01. intros H1 g c (pp & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hpp0 & Hpp16 & H23 & H9 & H18 & H21 & HC30 & H20 & HC28 & HC20 & HC18 & H19 & H8).
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
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 592).
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
      { rewrite Esrc, Hempv. intros HH.
        assert (Eb : match find_segment rsegs 0x30100 1 with Some _ => true | None => false end = true)
          by (vm_compute; reflexivity).
        rewrite HH in Eb. discriminate Eb. }
      rewrite Erest. cbn [length].
      split; [apply sl_bytes_nil; rewrite Esrc; lia|].
      split; [rewrite Esrc; lia|].
      split; [rewrite Esrc, Hempv; lia|].
      destruct (Z_lt_dec (g_src g) pp) as [Hl|Hl]; [left; lia|].
      destruct (Z_lt_dec (g_src g) (pp + POD_PROPS)) as [Hr|Hr];
        [exfalso; apply HQ; apply HNOSEG; lia | right; lia].
    - destruct (b1_in_all B APIf ra empty FF g (hb_pp pp) L A regs mem md HFR HP Hn0)
        as (Hinb' & Hp4096 & Hpac & HBYT).
      pose proof (m01_ba_skipn 7 _ _ _ HBYT) as HB7.
      assert (HD : fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (g_p g, g_n g) \/
                   fst (g_p g, g_n g) + snd (g_p g, g_n g) <= fst (pp, POD_PROPS)).
      { first [ exact (b1_sep B APIf ra empty g [] (pp, POD_PROPS) [] L A regs mem md (g_p g, g_n g)
                         HFR HP ltac:(cbn [app]; exact Hinb'))
              | exact (b1_sep B APIf ra empty FF g [] (pp, POD_PROPS) [] L A regs mem md (g_p g, g_n g)
                         HFR HP ltac:(cbn [app]; exact Hinb')) ]. }
      cbn [fst snd] in HD.
      assert (Esrc : g_src g = g_p g + Z.min 7 (Z.of_nat (length (g_in g)))) by reflexivity.
      assert (Elen : Z.of_nat (length (g_rest g)) = g_n g - Z.min 7 (g_n g)).
      { unfold g_rest, g_n. rewrite length_skipn. lia. }
      rewrite Elen, Esrc. unfold g_rest. unfold g_n in *.
      split; [exact HB7|]. split; [lia|]. split; [lia|]. lia. }
  destruct HSRC as (HBY & Hsrc0 & Hsrcc & HSEP).
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x13110) mem md
            (m01_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (@fp_regs fx') (@fp_csr fx')
               (normalize rsegs mem) (g_rest g) (g_fl g) (g_mask g) (g_buflen g) (g_b3 g) (g_b4 g) (g_b5 g)
               (g_b6 g) pp (g_S g - 65536)) _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply (m01_evt BUILD) with (junk := junk) (src := g_src g).
    + exact H10.
    + exact Hpp0.
    + exact Hpp16.
    + exact H23.
    + rewrite Hlen. exact H9.
    + exact H18.
    + exact H21.
    + exact H20.
    + rewrite Hspu. exact (bytes_at_normalize rsegs mem _ _ HMI HC30).
    + rewrite Hspu. exact (bytes_at_normalize rsegs mem _ _ HMI HC28).
    + rewrite Hspu. exact (bytes_at_normalize rsegs mem _ _ HMI HC20).
    + rewrite Hspu. exact (bytes_at_normalize rsegs mem _ _ HMI HC18).
    + exact (m01_u8_rng g 0).
    + exact (m01_u8_rng g 1).
    + unfold g_buflen. apply Z.mod_pos_bound. lia.
    + exact (m01_u8_rng g 3).
    + exact (m01_u8_rng g 4).
    + exact (m01_u8_rng g 5).
    + exact (m01_u8_rng g 6).
    + exact H19.
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
    + rewrite Hspu. replace (g_S g - 592) with (g_S g + (-37) * 16) by lia.
      rewrite Z_mod_plus_full. exact HS16.
    + rewrite Hspu. unfold FRAME_LOCALS. intros a Ha.
      apply (b8_seg_rom_hi B APIf ra empty FF). lia.
    + intros a Ha. apply (b8_relro_norm B APIf ra empty FF mem a HRL HMI0).
      unfold RELRO_TBL, RELRO_TBL_END in Ha. lia.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m0 & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                    m'' & HE & HB & HK8 & HK10 & HK18 & HK20 & HK28 & HK30 & HK38 & HK98 & HKd8 &
                    MU & WM & MIv & ST2).
    injection HE; intros; subst.
    rewrite Hspu in MU, HK8, HK10, HK18, HK20, HK28, HK30, HK38, HK98, HKd8.
    unfold MID_STACK, FRAME_LOCALS in MU.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    pose proof (b1_out _ m' _ _ Hrel HB) as HB'.
    pose proof (b1_out _ m' _ _ Hrel HK8) as HK8'.
    pose proof (b1_out _ m' _ _ Hrel HK10) as HK10'.
    pose proof (b1_out _ m' _ _ Hrel HK18) as HK18'.
    pose proof (b1_out _ m' _ _ Hrel HK20) as HK20'.
    pose proof (b1_out _ m' _ _ Hrel HK28) as HK28'.
    pose proof (b1_out _ m' _ _ Hrel HK30) as HK30'.
    pose proof (b1_out _ m' _ _ Hrel HK38) as HK38'.
    pose proof (b1_out _ m' _ _ Hrel HK98) as HK98'.
    pose proof (b1_out _ m' _ _ Hrel HKd8) as HKd8'.
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
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 RATE_CHECK) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 (g_len g)) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g (hb_pp pp) L A regs' m' md regs' (g_len g));
      [exact HFR' | exact HP | unfold hb_pp; cbn [length]; lia
       | unfold hb_bytes, hb_pp; cbn [map fold_right snd]; unfold POD_PROPS; lia
       | reflexivity | reflexivity | reflexivity
       | rewrite E1; apply YK0s.ret_ok_even; rewrite MState.unsigned_lit by (unfold RATE_CHECK; lia);
         unfold RATE_CHECK; reflexivity
       | exact E10' | lia |].
    intros L' A' regs'' mem'' md' res HF2 HP2 RP H10' Hres0 Hres16 HKF HKB.
    rewrite E1. apply H1. exists pp, res, fx', L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF2|]. split; [exact HP2|].
    unfold rg.
    split; [exact H10'|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [etransitivity; [exact (RP 20 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 24 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 27 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 18 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split.
    { apply (b1_ba_mbyte m'); [exact HK8'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HK10'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HK18'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HK20'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HK28'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HK30'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HK38'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HK98'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HKd8'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    apply (b1_ba_mbyte m'); [exact HB'|].
    intros i Hi. rewrite (m01_pp_len g) in Hi. apply (HKB pp POD_PROPS i Hinpp). exact Hi.
Qed.

End M01.
