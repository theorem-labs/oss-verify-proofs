(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 246 of its 282 lines of code are new or changed and 538 lines of the source are left out. *)
(* Segment M01 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan): [0x13090, 0x140e0], K13090 -> K140e4
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_M01).
   reac-pw/fuzz_role's U/Prog/Seg/M01.v with headamp's numbers: the frame is 608 bytes, the cursor is s6 at
   g_src g = data + min(2, n) (two bytes consumed: the null flag and cap), cap is in s3, the cell sp + 0x10 holds
   1 - null, malloc is 0x1693c, and the cut's cells are sp + 0x8 (cap), sp + 0x10 (1 - null), sp + 0x68
   (pp + 0x4d14), sp + 0x70 (pp) and sp + 0x78 (pp + 0x4000). headamp_build_contract is a Section hypothesis, run on
   the normalized memory with Tac_slot.sl_run (rest := g_rest g, nl := g_null g, cap := g_cap g, lo := S - 65536);
   its premises come from FR at K13090 (the input tail at the cursor, the live pp block, the stack region, the
   .data.rel.ro tables, mem_inv). The evt ends at 0x140e0 `jal malloc` with a0 = len; one step takes it to malloc's
   entry with ra = 0x140e4, and Tac_b1.b1_malloc_call runs the call from hb = [(pp, 19744)], whose kept-bytes clauses
   carry the five frame cells and the pp block's bytes to the cut. No function is proved here. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor.
Import ListNotations.
Open Scope Z_scope.

(* The bytes after the first k. *)
Lemma m01_ba_skip : forall m a l k, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k l).
Proof.
  intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite firstn_length_le in H by exact Hk. exact H.
Qed.

(* The cursor after the two fuzz_u8 reads: k = min(2, n) bytes consumed. *)
Lemma m01_src_rest : forall l, exists k, snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 l))) = skipn k l /\
  Z.of_nat k = Z.min 2 (Z.of_nat (length l)).
Proof.
  intros [|b0 [|b1 l]]; [exists 0%nat | exists 1%nat | exists 2%nat];
    cbn [Cursor.fuzz_u8 snd skipn length]; (split; [reflexivity | lia]).
Qed.

(* The bytes left after the two fuzz_u8 reads: n - min(2, n) (SlotInv.g_rest / g_k at l = the input). *)
Lemma m01_rest_len : forall l, Z.of_nat (length (snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 l))))) =
  Z.of_nat (length l) - Z.min 2 (Z.of_nat (length l)).
Proof.
  intros l. destruct l as [|b0 [|b1 l]]; cbn [Cursor.fuzz_u8 snd length]; lia.
Qed.

Lemma m01_rec_wf : forall inp, pod_rec_wf (head_rec inp).
Proof.
  intros inp. unfold head_rec. apply (pod_build_wf inp _ (snd (pod_build inp))).
  apply surjective_pairing.
Qed.

Lemma m01_len_bound : forall inp, 8 <= head_len inp <= 5440.
Proof. intros inp. destruct (buf_header (head_rec inp) (m01_rec_wf inp)) as (_ & _ & _ & H). exact H. Qed.

Lemma m01_pp_len : forall inp, Z.of_nat (length (pp_bytes (head_rec inp))) = POD_PROPS.
Proof. intros inp. rewrite (length_pp_bytes (head_rec inp) (m01_rec_wf inp)). reflexivity. Qed.

(* cap = the second input byte mod 10 (SlotInv.g_cap at l = the input). *)
Lemma m01_cap : forall l, 0 <= fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 l))) mod 10 <= 9.
Proof.
  intros l. pose proof (Z.mod_pos_bound (fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 l)))) 10 ltac:(lia)). lia.
Qed.

(* null = bit 0 of the first input byte (SlotInv.g_null at l = the input). *)
Lemma m01_nl : forall l, 0 <= Z.land (fst (Cursor.fuzz_u8 l)) 1 <= 1.
Proof.
  intros l.
  assert (E : Z.land (fst (Cursor.fuzz_u8 l)) 1 = fst (Cursor.fuzz_u8 l) mod 2)
    by (apply (Z.land_ones (fst (Cursor.fuzz_u8 l)) 1); lia).
  rewrite E. pose proof (Z.mod_pos_bound (fst (Cursor.fuzz_u8 l)) 2 ltac:(lia)). lia.
Qed.

(* ---- The run: K13090 to malloc's entry with ra = 0x140e4 ---- *)
Definition m01_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (rest : list byte) (nl cap pp lo : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s9' s10' s11' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 HEAD_DUP_POD) sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (head_len rest))
                  a1' a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 (head_len rest)) s4' s5' s6'
                  (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9' s10' s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0x1693c) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pp (pp_bytes (head_rec rest)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 cap)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 (1 - nl))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    Frame.munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
    Frame.wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

Lemma m01_evt : headamp_build_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (nl cap src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s6 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s3 = Z_to_bv 64 cap -> 0 <= cap <= 9 -> 0 <= nl <= 1 ->
    bytes_at rsegs m (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 (1 - nl))) ->
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
    evt rsegs (m01_post sp gp tp F fc m rest nl cap pp lo)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_BUILD) fc None m (seg_rom rsegs)).
Proof.
  intros BUILD ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rest junk nl cap src pp lo E10 Hpp0 Hpp16 E22 E18 E19 Hcap Hnl HNL E9 E8 Hsrc0 HBY HRW HROM HSEP HSL HPL
    ST HMID HSP16 HROMS HREL HMI.
  eapply evt_cut.
  - eapply BUILD with (rest := rest) (junk := junk) (nl := nl) (cap := cap) (src := src) (pp := pp) (lo := lo);
      eassumption.
  - intros ms' POST.
    destruct POST as (ra' & t0' & t1' & t2' & s0' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s4' &
                      s5' & s6' & s9' & s10' & s11' & t3' & t4' & t5' & t6' & m' & -> & HB & HC08 & HC10 & HC68 &
                      HC70 & HC78 & MU & WM & MIv & ST2).
    unfold HEAD_MALLOC2. step. apply evt_done.
    unfold m01_post. do 24 eexists.
    split; [reflexivity|]. split; [exact HB|]. split; [exact HC08|]. split; [exact HC10|]. split; [exact HC68|].
    split; [exact HC70|]. split; [exact HC78|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MIv | exact ST2].
Qed.

(* ---- The segment ---- *)
Section M01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Hypothesis BUILD : headamp_build_contract.

Lemma seg_M01 : S_M01 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF BUILD.
  unfold S_M01. intros H1 g c (pp & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP (H10 & Hpp0 & Hpp16 & H22 & H18 & H19 & HNL & H9 & H8).
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
  assert (Hlen : Z.of_nat (length (g_rest g)) = g_k g) by exact (m01_rest_len (g_in g)).
  assert (Hlb : 8 <= g_len g <= 5440) by exact (m01_len_bound (g_rest g)).
  assert (Hcap : 0 <= g_cap g <= 9) by exact (m01_cap (g_in g)).
  assert (Hnl : 0 <= g_null g <= 1) by exact (m01_nl (g_in g)).
  assert (Hppl : Z.of_nat (length (pp_bytes (g_rec g))) = POD_PROPS) by exact (m01_pp_len (g_rest g)).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 608).
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
      destruct (m01_src_rest (g_in g)) as (k & Erest & Ek).
      assert (Esrc : g_src g = g_p g + Z.of_nat k) by (unfold g_src, g_n; lia).
      assert (Erest' : g_rest g = skipn k (g_in g)) by (unfold g_rest; exact Erest).
      assert (Hk : (k <= length (g_in g))%nat) by (unfold g_n in *; lia).
      assert (Elen : g_src g + Z.of_nat (length (g_rest g)) = g_p g + g_n g).
      { rewrite Erest', length_skipn, Esrc. unfold g_n. lia. }
      assert (HD : fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (g_p g, g_n g) \/
                   fst (g_p g, g_n g) + snd (g_p g, g_n g) <= fst (pp, POD_PROPS)).
      { first [ exact (b1_sep B APIf ra empty g [] (pp, POD_PROPS) [] L A regs mem md (g_p g, g_n g)
                         HFR HP ltac:(cbn [app]; exact Hinb'))
              | exact (b1_sep B APIf ra empty FF g [] (pp, POD_PROPS) [] L A regs mem md (g_p g, g_n g)
                         HFR HP ltac:(cbn [app]; exact Hinb')) ]. }
      cbn [fst snd] in HD.
      split; [rewrite Erest', Esrc; exact (m01_ba_skip mem (g_p g) (g_in g) k HBYT Hk)|].
      split; [lia|]. split; [lia|]. lia. }
  destruct HSRC as (HBY & Hsrc0 & Hsrcc & HSEP).
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x13090) mem md
            (m01_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (@fp_regs fx') (@fp_csr fx')
               (normalize rsegs mem) (g_rest g) (g_null g) (g_cap g) pp (g_S g - 65536)) _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply (m01_evt BUILD) with (junk := junk) (src := g_src g).
    + exact H10.
    + exact Hpp0.
    + exact Hpp16.
    + exact H22.
    + rewrite Hlen. exact H18.
    + exact H19.
    + exact Hcap.
    + exact Hnl.
    + rewrite Hspu. exact (bytes_at_normalize rsegs mem _ _ HMI HNL).
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
    + rewrite Hspu. unfold MID_STACK, PARSE_STACK. lia.
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
                    m'' & HE & HB & HC08 & HC10 & HC68 & HC70 & HC78 & MU & WM & MIv & ST2).
    injection HE; intros; subst.
    rewrite Hspu in MU, HC08, HC10, HC68, HC70, HC78. unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in MU.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    pose proof (b1_out _ m' _ _ Hrel HB) as HB'.
    pose proof (b1_out _ m' _ _ Hrel HC08) as HC08'.
    pose proof (b1_out _ m' _ _ Hrel HC10) as HC10'.
    pose proof (b1_out _ m' _ _ Hrel HC68) as HC68'.
    pose proof (b1_out _ m' _ _ Hrel HC70) as HC70'.
    pose proof (b1_out _ m' _ _ Hrel HC78) as HC78'.
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
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 HEAD_DUP_POD) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
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
    split; [etransitivity; [exact (RP 19 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 23 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 24 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split.
    { apply (b1_ba_mbyte m'); [exact HC08'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HC10'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HC68'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HC70'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HC78'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    apply (b1_ba_mbyte m'); [exact HB'|].
    intros i Hi. rewrite Hppl in Hi. apply (HKB pp POD_PROPS i Hinpp). exact Hi.
Qed.

End M01.
