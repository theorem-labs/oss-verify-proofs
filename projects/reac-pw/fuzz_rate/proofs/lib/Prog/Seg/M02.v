(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 132 of its 154 lines of code are new or changed and 552 lines of the source are left out. *)
(* Segment M02 of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (plain): [0x141e4, 0x14504), K141e4 -> K14504
   (Prog/LLVMFuzzerTestOneInput_c.v's S_M02).
   Ported from reac-pw/fuzz_role's Prog/Seg/M02.v with rate's numbers.
   The body is rate_check_contract's evt (the copy into the pod block, the property parse, expect_rate inlined with
   its three checks, the decide loop's two rounds and check_code(MALFORMED)), taken as a Section hypothesis. Its
   callees include the soft-float routines of pod_nearest, whose contracts are stated over the CJ memory invariant,
   so the evt runs on MemNorm.normalize_cj of the cut's memory (which has MemNorm.task_mem by
   MemNorm.mem_inv_cj_normalize). Role's m02_* helpers and the composition role's seg_M02 does inline are
   Seg/Tac_fp.v's sl_cj_keep .. sl_run_fp_cj and sl_mid_fp_blk; here sl_mid_fp_blk runs the evt with hb = hb_pod g
   pod pp and the written block (pod, g_len g).
   The premises come from FR at K141e4: the cut's registers and cells (sp = S - 544), the record's bytes in the pp
   block, the pod block's cells (live, so present and writable, outside the image and below TASK_SIZE: sl_blk_cj),
   the stack region [S - 65536, S - 104) (sl_stk_cj), the block separation (Tac_b1.b1_sep), the header values'
   ranges (g_u8 is a byte or 0; buflen is mod 24), frm_zero from the cut. The run writes
   [S - 544 - 4096, S - 544 + 0x1b8) = [S - 4640, S - 104) and the pod block, inside [S - SLOT_K, S - 104) and the
   block, so FR carries over (Tac_b1.b1_fr_hb inside sl_mid_fp_blk); it ends at its own FP state with rounding mode
   0, the FP state of the cut it closes. No function is proved here. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require RateEnd.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 Tac_fp.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_u8's value: a byte, or 0 when no byte is left. *)
Lemma m02_u8_rng : forall g i, 0 <= g_u8 g i < 256.
Proof.
  intros g i. unfold g_u8. destruct (nth_error (g_in g) i) as [b|]; [exact (b1_byte_rng b) | lia].
Qed.

Section M02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis CHECK : rate_check_contract.

Lemma seg_M02 : S_M02 B APIf ra empty.
Proof.
  unfold S_M02. intros H1 g c (pp & pod & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hpod0 & Hpod16 & H20 & H9 & H22 & H25 & H26 & H23 & H18 & H27 & HB28 & HB70 & HB80 & HBb0 & HBpp).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  assert (Hinpod : In (pod, g_len g) (hb_pod g pod pp)) by (left; reflexivity).
  assert (Hinpp : In (pp, POD_PROPS) (hb_pod g pod pp)) by (right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g (hb_pod g pod pp) pod (g_len g) L A regs mem md HFR HP Hinpod)
    as (STpod & Hpod4096 & Hpodc).
  destruct (b1_hb B APIf ra empty FF g (hb_pod g pod pp) pp POD_PROPS L A regs mem md HFR HP Hinpp)
    as (STpp & Hpp4096 & Hppc).
  pose proof (b1_blk_rom B APIf ra empty FF g (hb_pod g pod pp) pod (g_len g) L A regs mem md HFR HP Hinpod)
    as HROMpod.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI0 & HRL & HM & _).
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSKc & HS47c & _).
  pose proof alloc_ceiling_value as HAC.
  assert (Hlen0 : 0 <= g_len g) by (unfold g_len; lia).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 544).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (ERL : rate_len (g_rest g) = g_len g) by reflexivity.
  assert (EREC : fst (pod_build (g_rest g)) = g_rec g) by reflexivity.
  (* The pod block's cells on the CJ-normalized memory. *)
  assert (STpodcj : stk rsegs (MemNorm.normalize_cj rsegs mem) pod (pod + g_len g))
    by exact (sl_blk_cj B APIf ra empty FF L A mem md pod (g_len g) HM (b1_in_hb _ _ _ _ HP Hinpod)).
  destruct (sl_rw_of_stk _ _ _ pod (Z.to_nat (g_len g)) STpodcj ltac:(lia) ltac:(lia)) as (junk & HRWcj).
  (* The two blocks are apart. *)
  assert (HSEP : pod + g_len g <= pp \/ pp + POD_PROPS <= pod).
  { assert (HD : fst (pod, g_len g) + snd (pod, g_len g) <= fst (pp, POD_PROPS) \/
                 fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (pod, g_len g)).
    { first [ exact (b1_sep B APIf ra empty g [] (pod, g_len g) [(pp, POD_PROPS)] L A regs mem md
                       (pp, POD_PROPS) HFR HP ltac:(cbn [app]; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [] (pod, g_len g) [(pp, POD_PROPS)] L A regs mem md
                       (pp, POD_PROPS) HFR HP ltac:(cbn [app]; left; reflexivity)) ]. }
    cbn [fst snd] in HD. lia. }
  eapply (sl_mid_fp_blk B APIf ra empty FF fx' g (hb_pod g pod pp) pod (g_len g) L A regs mem md
            (Z_to_bv 64 0x141e4) _ _ HFR HP Hinpod).
  - rewrite sl_mkR_of.
    apply CHECK with (inp := g_rest g) (junk := junk) (fl := g_fl g) (mask := g_mask g) (buflen := g_buflen g)
      (b3 := g_b3 g) (b4 := g_b4 g) (b5 := g_b5 g) (b6 := g_b6 g) (pp := pp) (pod := pod)
      (lo := g_S g - 65536).
    + exact H10.
    + exact Hpod0.
    + exact Hpod16.
    + rewrite ERL. exact H20.
    + exact H9.
    + exact H22.
    + exact H25.
    + exact H26.
    + exact H23.
    + exact H18.
    + exact H27.
    + exact (m02_u8_rng g 0%nat).
    + exact (m02_u8_rng g 1%nat).
    + unfold g_buflen. apply Z.mod_pos_bound. lia.
    + exact (m02_u8_rng g 3%nat).
    + exact (m02_u8_rng g 4%nat).
    + exact (m02_u8_rng g 5%nat).
    + exact (m02_u8_rng g 6%nat).
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB28].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB70].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB80].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HBb0].
    + rewrite EREC. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | | exact HBpp].
      rewrite (length_pp_bytes (g_rec g)).
      * unfold PP_SIZE, TASK_SIZE. unfold POD_PROPS in Hppc. lia.
      * apply (pod_build_wf (g_rest g) _ (snd (pod_build (g_rest g)))). apply surjective_pairing.
    + rewrite ERL. exact HRWcj.
    + rewrite ERL. intros a Ha. apply HROMpod. lia.
    + rewrite ERL. exact HSEP.
    + rewrite ERL. lia.
    + lia.
    + rewrite Hspu. unfold FRAME_LOCALS. apply sl_stk_cj; [exact HMI | unfold SL_TOP; lia
        | unfold TASK_SIZE; lia |].
      intros a Ha. rewrite <- SEGS. apply Hwin. lia.
    + rewrite Hspu. unfold MID_STACK. lia.
    + rewrite Hspu. Z.div_mod_to_equations. lia.
    + unfold STACK_LO_MIN. lia.
    + rewrite Hspu. lia.
    + rewrite Hspu. unfold FRAME_LOCALS. intros a Ha.
      apply (b8_seg_rom_hi B APIf ra empty FF). lia.
    + exact Hfrm.
    + exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
    + exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
  - (* The run's end state: its pc and registers, frm_zero, the footprint inside [S - SLOT_K, S - 104) and the pod
       block, sp, gp, tp kept. *)
    intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
               F0 & fc0 & m0 & -> & Hfrm' & _ & MU & WM & _ & _).
    do 5 eexists. split; [reflexivity|]. split; [exact Hfrm'|].
    split; [|split; [reflexivity | split; reflexivity]].
    eexists. split; [exact MU|]. split; [exact WM|].
    intros xw Hx HO. rewrite Hspu in HO. unfold MID_STACK, FRAME_LOCALS in HO. rewrite ERL in HO.
    cbn [Frame.outside] in HO. unfold SLOT_K, SLOT_STACK.
    assert (D1 : g_S g - 544 - 4096 <= xw < g_S g - 544 + 0x1b8 \/
                 ~ (g_S g - 544 - 4096 <= xw < g_S g - 544 + 0x1b8)) by lia.
    assert (D2 : pod <= xw < pod + g_len g \/ ~ (pod <= xw < pod + g_len g)) by lia.
    destruct D1 as [D1|D1]; [left; lia|].
    destruct D2 as [D2|D2]; [right; exact D2|].
    exfalso. apply HO. split; [exact D1 | split; [exact D2 | exact I]].
  - (* The cut K14504 at the run's FP state: s3 = pod, s9 = mask, s10 = buflen, the cell sp + 0x80 = pp. *)
    intros R F' pc' fc' m0' regs' m' HQ Hx Hrel Hsame Hfrm' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                    ? & F0 & fc0 & m'' & HE & _ & HB80' & _ & _ & _ & _).
    injection HE; intros; subst.
    apply H1. exists pp, pod, (mkFP F0 fc0), L, A, regs', m', md.
    split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact HFR'|]. split; [exact HP|].
    unfold rg. split; [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    rewrite Hspu in HB80'. unfold fsp, SLOT_FRAME.
    exact (MemNorm.bytes_at_rel_cj rsegs m' _ _ _ Hrel HB80').
Qed.

End M02.

(* The segment lemma as Prog/RateEnd.v states it. *)
Theorem seg_M02_stmt_holds : RateEnd.seg_M02_stmt.
Proof.
  unfold RateEnd.seg_M02_stmt. intros fx rc B APIf LS SH SK ra empty FF CHECK.
  exact (seg_M02 B APIf ra empty FF CHECK).
Qed.
