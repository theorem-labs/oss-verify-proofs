(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 265 of its 295 lines of code are new or changed and 544 lines of the source are left out. *)
(* Segment M01 of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (plain): [0x13158, 0x141e4), K13158 -> K141e4
   (Prog/LLVMFuzzerTestOneInput_c.v's S_M01).
   Ported from reac-pw/fuzz_role's Prog/Seg/M01.v at rate's addresses,
   registers and frame cells. The body is rate_build_contract's evt (the inlined pod builder of pod.h:382-449),
   taken as a Section hypothesis and run on the normalized memory with Tac_slot.sl_run, as libreac/fuzz_ctrl's
   released Prog/Seg/F02.v (origin/ossv/recipes 25e3d17bdb50) runs f02_evt. Its premises come from FR at K13158:
   the input after the 7-byte header g_rest at g_src (the input block's bytes, unchanged since ENTRY by FR's
   entry-block clause and GV's blk_data; for the empty input the cursor is `empty`, which lies in an image segment
   and so apart from the pp block), the seven header values of Inv_K13158 (s6, s9, s10, s7, the cell sp + 0x30,
   s11, s4), the live block (pp, 19744) writable (Tac_b1.b1_hb) and outside the image (b1_blk_rom), the stack region
   [S - 65536, S - 104) (Tac_slot.sl_fr_stk), the two pointer tables of .data.rel.ro (Tac_b8.b8_relro_norm),
   mem_inv.
   The evt ends at 0x141e0 `jal malloc`; one step takes it to malloc's entry 0x16694 with ra = 0x141e4 and the
   request a0 = pp->len (8 <= len <= 5440 by the shared model's pod_build_wf / Pod.Spa.buf_header), and
   Tac_b1.b1_malloc_call runs the call from hb = [(pp, 19744)]. Its kept-bytes clauses carry the frame cells
   sp + 0x28, sp + 0x70, sp + 0x80, sp + 0xb0 and the pp block's bytes to the cut, and its regs_preserved the
   callee-saved s1, s2, s4, s6, s7, s9, s10, s11. The run's writes, [S - 544 - 4096, S - 104) (MID_STACK is 4096
   here, inside FR's stack window [S - 65536, S)) and the pp block, keep FR (Tac_b1.b1_fr_hb).
   seg_M01_stmt_holds checks that the closed lemma is RateEnd.seg_M01_stmt. No function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require RateEnd.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout Spa.
Import ListNotations.
Open Scope Z_scope.

(* The bytes after the first one. *)
Lemma m01_ba_tl : forall m a b l, bytes_at rsegs m a (b :: l) -> bytes_at rsegs m (a + 1) l.
Proof.
  intros m a b l (H1 & H2 & H). cbn [length] in H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply H. cbn [length]. lia.
Qed.

(* The bytes after the first k ones (all of them when the list is shorter). *)
Lemma m01_ba_skipn : forall k m a l, bytes_at rsegs m a l ->
  bytes_at rsegs m (a + Z.of_nat (Nat.min k (length l))) (skipn k l).
Proof.
  induction k as [|k IH]; intros m a l H.
  - cbn [Nat.min skipn]. replace (a + Z.of_nat 0) with a by lia. exact H.
  - destruct l as [|b l].
    + cbn [Nat.min skipn length]. replace (a + Z.of_nat 0) with a by lia. exact H.
    + cbn [skipn length Nat.min].
      replace (a + Z.of_nat (S (Nat.min k (length l)))) with (a + 1 + Z.of_nat (Nat.min k (length l))) by lia.
      exact (IH m (a + 1) l (m01_ba_tl m a b l H)).
Qed.

(* The input after the 7-byte header: its length is the ghost's byte count. *)
Lemma m01_rest_len : forall g, Z.of_nat (length (g_rest g)) = g_k g.
Proof. intros g. unfold g_rest, g_k, g_n. rewrite length_skipn. lia. Qed.

(* A header byte (fuzz_u8: the input's byte or 0). *)
Lemma m01_u8_rng : forall g i, 0 <= g_u8 g i < 256.
Proof.
  intros g i. unfold g_u8. destruct (nth_error (g_in g) i) as [b|]; [exact (b1_byte_rng b) | lia].
Qed.

(* The record pod_build makes of the input is well formed, so 8 <= pp->len <= 5440 and pp_bytes is 19744 bytes. *)
Lemma m01_rec_wf : forall g, pod_rec_wf (g_rec g).
Proof.
  intros g. unfold g_rec. apply (pod_build_wf (g_rest g) _ (snd (pod_build (g_rest g)))).
  apply surjective_pairing.
Qed.

Lemma m01_len_bound : forall g, 8 <= g_len g <= 5440.
Proof. intros g. destruct (buf_header (g_rec g) (m01_rec_wf g)) as (_ & _ & _ & H). exact H. Qed.

Lemma m01_pp_len : forall g, Z.of_nat (length (pp_bytes (g_rec g))) = POD_PROPS.
Proof. intros g. rewrite (length_pp_bytes (g_rec g) (m01_rec_wf g)). reflexivity. Qed.

(* ---- The run: K13158 to malloc's entry with ra = 0x141e4 ---- *)
Definition m01_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (rest : list byte) (fl mask buflen b3 b4 b5 b6 pp lo : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s8' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 RATE_CHECK) sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pp) (Z_to_bv 64 (rate_len rest))
                  a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (b4 * 256)) s3' (Z_to_bv 64 (rate_len rest)) s5' (Z_to_bv 64 fl) (Z_to_bv 64 b3) s8'
                  (Z_to_bv 64 mask) (Z_to_bv 64 buflen) (Z_to_bv 64 b5) t3' t4' t5' t6')
             F (Z_to_bv 64 0x16694) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pp (pp_bytes (fst (pod_build rest))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b6 * 256))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0xb0) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    Frame.munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
    Frame.wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

Lemma m01_evt : rate_build_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s5 = Z_to_bv 64 src -> s0 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s6 = Z_to_bv 64 fl -> s9 = Z_to_bv 64 mask -> s10 = Z_to_bv 64 buflen -> s7 = Z_to_bv 64 b3 ->
    bytes_at rsegs m (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 (b4 * 256))) ->
    s11 = Z_to_bv 64 b5 -> s4 = Z_to_bv 64 (b6 * 256) ->
    0 <= fl < 256 -> 0 <= mask < 256 -> 0 <= buflen < 24 ->
    0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
    s3 = Z_to_bv 64 POD_PROPS -> s1 = Z_to_bv 64 0x5000 ->
    0 < src -> bytes_at rsegs m src rest ->
    rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] ->
    (forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None) ->
    (src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src) ->
    src + Z.of_nat (length rest) <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs (m01_post sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 pp lo)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATE_BUILD) fc None m (seg_rom rsegs)).
Proof.
  intros BUILD ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rest junk fl mask buflen b3 b4 b5 b6 src pp lo E10 Hpp0 Hpp16 E21 E8 E22 E25 E26 E23 HC30 E27 E20
    Hfl Hmask Hbl Hb3 Hb4 Hb5 Hb6 E19 E9 Hsrc0 HBY HRW HROM HSEP HSL HPL ST HMID HSP16 HROMS HREL HMI.
  eapply evt_cut.
  - eapply BUILD with (rest := rest) (junk := junk) (fl := fl) (mask := mask) (buflen := buflen) (b3 := b3)
      (b4 := b4) (b5 := b5) (b6 := b6) (src := src) (pp := pp) (lo := lo); eassumption.
  - intros ms' POST.
    destruct POST as (ra' & t0' & t1' & t2' & s0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s5' & s8' &
                      t3' & t4' & t5' & t6' & m' & -> & HB & HC28 & HC70 & HC80 & HCB0 & MU & WM & MIv & ST2).
    unfold RATE_MALLOC2. step. apply evt_done.
    unfold m01_post. do 19 eexists.
    split; [reflexivity|]. split; [exact HB|]. split; [exact HC28|]. split; [exact HC70|].
    split; [exact HC80|]. split; [exact HCB0|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MIv | exact ST2].
Qed.

(* ---- The segment ---- *)
Section M01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis BUILD : rate_build_contract.

Lemma seg_M01 : S_M01 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   five segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF BUILD.
  unfold S_M01. intros H1 g c (pp & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hpp0 & Hpp16 & H21 & H8 & H22 & H25 & H26 & H23 & HC30 & H27 & H20 & H19 & H9).
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
  (* The pp block's cells on the normalized memory. *)
  destruct (sl_rw_of_stk _ _ _ pp (Z.to_nat POD_PROPS) STb ltac:(lia) ltac:(unfold POD_PROPS; lia))
    as (junk & HRW).
  (* No image segment holds a byte of the pp block. *)
  assert (HNOSEG : forall a, pp <= a < pp + POD_PROPS -> find_segment rsegs a 1 = None).
  { intros a Ha. exact (b1_blk_noseg B APIf ra empty FF L A mem md pp POD_PROPS a HM
                          (b1_in_hb _ _ _ _ HP Hinpp) Ha). }
  (* The input after the header at the cursor, and its separation from the pp block. *)
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
      { rewrite Esrc, Hempv.
        match goal with |- find_segment ?s ?a ?n <> None =>
          assert (Hb : match find_segment s a n with Some _ => true | None => false end = true)
            by (vm_compute; reflexivity);
          destruct (find_segment s a n); [discriminate | discriminate Hb] end. }
      rewrite Erest. cbn [length].
      split; [apply sl_bytes_nil; rewrite Esrc; lia|].
      split; [rewrite Esrc; lia|].
      split; [rewrite Esrc, Hempv; lia|].
      destruct (Z_lt_dec (g_src g) pp) as [Hl|Hl]; [left; lia|].
      destruct (Z_lt_dec (g_src g) (pp + POD_PROPS)) as [Hr|Hr];
        [exfalso; apply HQ; apply HNOSEG; lia | right; lia].
    - destruct (b1_in_all B APIf ra empty FF g (hb_pp pp) L A regs mem md HFR HP Hn0)
        as (Hinb' & Hp4096 & Hpac & HBYT).
      assert (HD : fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (g_p g, g_n g) \/
                   fst (g_p g, g_n g) + snd (g_p g, g_n g) <= fst (pp, POD_PROPS)).
      { first [ exact (b1_sep B APIf ra empty g [] (pp, POD_PROPS) [] L A regs mem md (g_p g, g_n g)
                         HFR HP ltac:(cbn [app]; exact Hinb'))
              | exact (b1_sep B APIf ra empty FF g [] (pp, POD_PROPS) [] L A regs mem md (g_p g, g_n g)
                         HFR HP ltac:(cbn [app]; exact Hinb')) ]. }
      cbn [fst snd] in HD.
      assert (HB7 : bytes_at rsegs mem (g_src g) (g_rest g)).
      { unfold g_rest.
        replace (g_src g) with (g_p g + Z.of_nat (Nat.min 7 (length (g_in g))))
          by (unfold g_src, g_n; rewrite Nat2Z.inj_min; reflexivity).
        exact (m01_ba_skipn 7 _ _ _ HBYT). }
      unfold g_k in Hlen.
      split; [exact HB7|]. unfold g_src. split; [lia|]. split; [lia|]. lia. }
  destruct HSRC as (HBY & Hsrc0 & Hsrcc & HSEP).
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x13158) mem md
            (m01_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (@fp_regs fx') (@fp_csr fx')
               (normalize rsegs mem) (g_rest g) (g_fl g) (g_mask g) (g_buflen g) (g_b3 g) (g_b4 g) (g_b5 g)
               (g_b6 g) pp (g_S g - 65536)) _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply (m01_evt BUILD) with (junk := junk) (src := g_src g).
    + exact H10.
    + exact Hpp0.
    + exact Hpp16.
    + exact H21.
    + rewrite Hlen. exact H8.
    + exact H22.
    + exact H25.
    + exact H26.
    + exact H23.
    + rewrite Hspu. exact (bytes_at_normalize rsegs mem _ _ HMI HC30).
    + exact H27.
    + exact H20.
    + exact (m01_u8_rng g 0).
    + exact (m01_u8_rng g 1).
    + unfold g_buflen. apply Z.mod_pos_bound. lia.
    + exact (m01_u8_rng g 3).
    + exact (m01_u8_rng g 4).
    + exact (m01_u8_rng g 5).
    + exact (m01_u8_rng g 6).
    + exact H19.
    + exact H9.
    + exact Hsrc0.
    + exact (bytes_at_normalize rsegs mem _ _ HMI HBY).
    + exact HRW.
    + intros a Ha. apply HROM. lia.
    + exact HSEP.
    + lia.
    + lia.
    + rewrite Hspu. unfold FRAME_LOCALS. apply (b8_stk_sub _ _ _ _ _ _ ST); lia.
    + rewrite Hspu. unfold MID_STACK. lia.
    + rewrite Hspu. exact Hsp16.
    + rewrite Hspu. unfold FRAME_LOCALS. intros a Ha.
      apply (b8_seg_rom_hi B APIf ra empty FF). lia.
    + intros a Ha. apply (b8_relro_norm B APIf ra empty FF mem a HRL HMI0).
      unfold RELRO_TBL, RELRO_TBL_END in Ha. lia.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m0 & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' &
                    HE & HB & HC28 & HC70 & HC80 & HCB0 & MU & WM & MIv & ST2).
    injection HE; intros; subst.
    rewrite Hspu in MU, HC28, HC70, HC80, HCB0. unfold MID_STACK, FRAME_LOCALS in MU.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    pose proof (b1_out _ m' _ _ Hrel HB) as HB'.
    pose proof (b1_out _ m' _ _ Hrel HC28) as HC28'.
    pose proof (b1_out _ m' _ _ Hrel HC70) as HC70'.
    pose proof (b1_out _ m' _ _ Hrel HC80) as HC80'.
    pose proof (b1_out _ m' _ _ Hrel HCB0) as HCB0'.
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
       | rewrite E1; unfold RATE_CHECK; vm_compute; reflexivity | exact E10' | lia |].
    intros L' A' regs'' mem'' md' res HF2 HP2 RP H10' Hres0 Hres16 HKF HKB.
    rewrite E1. apply H1. exists pp, res, fx', L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF2|]. split; [exact HP2|].
    unfold rg.
    split; [exact H10'|]. split; [exact Hres0|]. split; [exact Hres16|].
    (* s4 = len, s1 = pp, s6 = fl, s9 = mask, s10 = buflen, s7 = b3, s2 = b4 << 8, s11 = b5: callee-saved. *)
    split; [etransitivity; [exact (RP 20 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 9 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 22 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 25 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 26 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 23 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 18 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 27 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    (* The frame cells sp + 0x28, 0x70, 0x80, 0xb0 and the pp block: malloc's kept bytes. *)
    split.
    { apply (b1_ba_mbyte m'); [exact HC28'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HC70'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HC80'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HCB0'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    apply (b1_ba_mbyte m'); [exact HB'|].
    intros i Hi. rewrite (m01_pp_len g) in Hi. apply (HKB pp POD_PROPS i Hinpp). exact Hi.
Qed.

End M01.

(* The closed lemma is the slot's premise RateEnd.seg_M01_stmt. *)
Lemma seg_M01_stmt_holds : RateEnd.seg_M01_stmt.
Proof. exact @seg_M01. Qed.
