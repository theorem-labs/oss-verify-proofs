(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 143 of its 165 lines of code are new or changed and 552 lines of the source are left out. *)
(* Segment M02 of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (UBSan): [0x1420c, 0x14614), K1420c -> K14614
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_M02).
   The plain segment (lib/Prog/Seg/M02.v) with the UBSan numbers, ported from reac-pw/fuzz_role's U/Prog/Seg/M02.v: the frame is 592 bytes (sp = S - 592, FRAME_LOCALS 0x1e8); pp is s8,
   pp + 0x4000 is s11, fl is s2; the header values are in the cells sp + 8 .. sp + 0x38, pp + 0x4d14 in sp + 0x98 and
   pp in sp + 0xd8; rate_check_contract takes one premise more, reac_rate_refuse_code's codes[] table
   [CODES_TBL, CODES_TBL_END) = [0x1edc0, 0x1ede8) in .data.rel.ro, which reads as the image on the CJ-normalized
   memory by the frame's relro clause (Seg/Tac_fp.sl_relro_cj: frame_RELRO's block [0x1ecb8, 0x1ee78) holds it).
   The evt runs on MemNorm.normalize_cj of the cut's memory through Seg/Tac_fp.sl_mid_fp_blk with hb = hb_pod g pod
   pp and the written block (pod, g_len g); it writes [S - 592 - 4096, S - 104) and the pod block and ends at its own
   FP state with rounding mode 0, the FP state of the cut it closes (K14614: s3 = pod, s10 = mask, the cells
   sp + 0x30 = buflen and sp + 0xd8 = pp). No function is proved here. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require RateEnd.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 Tac_fp.
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
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Hypothesis CHECK : rate_check_contract.

Lemma seg_M02 : S_M02 B APIf ra empty.
Proof.
  unfold S_M02. intros H1 g c (pp & pod & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hpod0 & Hpod16 & H20 & H24 & H27 & H18 & HB08 & HB10 & HB18 & HB20 & HB28 & HB30 & HB38 & HB98 & HBd8
     & HBpp).
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
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 592).
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
            (Z_to_bv 64 0x1420c) _ _ HFR HP Hinpod).
  - rewrite sl_mkR_of.
    apply CHECK with (inp := g_rest g) (junk := junk) (fl := g_fl g) (mask := g_mask g) (buflen := g_buflen g)
      (b3 := g_b3 g) (b4 := g_b4 g) (b5 := g_b5 g) (b6 := g_b6 g) (pp := pp) (pod := pod)
      (lo := g_S g - 65536).
    + exact H10.
    + exact Hpod0.
    + exact Hpod16.
    + rewrite ERL. exact H20.
    + exact H24.
    + exact H27.
    + exact H18.
    + exact (m02_u8_rng g 0%nat).
    + exact (m02_u8_rng g 1%nat).
    + unfold g_buflen. apply Z.mod_pos_bound. lia.
    + exact (m02_u8_rng g 3%nat).
    + exact (m02_u8_rng g 4%nat).
    + exact (m02_u8_rng g 5%nat).
    + exact (m02_u8_rng g 6%nat).
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB08].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB10].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB18].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB20].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB28].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB30].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB38].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB98].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HBd8].
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
    + (* codes[] reads as the image: frame_RELRO's block [0x1ecb8, 0x1ee78) holds [0x1edc0, 0x1ede8). *)
      intros a Ha. apply (sl_relro_cj B APIf ra empty FF mem a HRL HMI0).
      unfold CODES_TBL, CODES_TBL_END in Ha. lia.
    + exact Hfrm.
    + exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
    + exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
  - (* The run's end state: its pc and registers, frm_zero, the footprint inside [S - SLOT_K, S - 104) and the pod
       block, sp, gp, tp kept. *)
    intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
               ? & F0 & fc0 & m0 & -> & Hfrm' & _ & _ & MU & WM & _ & _).
    do 5 eexists. split; [reflexivity|]. split; [exact Hfrm'|].
    split; [|split; [reflexivity | split; reflexivity]].
    eexists. split; [exact MU|]. split; [exact WM|].
    intros xw Hx HO. rewrite Hspu in HO. unfold MID_STACK, FRAME_LOCALS in HO. rewrite ERL in HO.
    cbn [Frame.outside] in HO. unfold SLOT_K, SLOT_STACK.
    assert (D1 : g_S g - 592 - 4096 <= xw < g_S g - 592 + 0x1e8 \/
                 ~ (g_S g - 592 - 4096 <= xw < g_S g - 592 + 0x1e8)) by lia.
    assert (D2 : pod <= xw < pod + g_len g \/ ~ (pod <= xw < pod + g_len g)) by lia.
    destruct D1 as [D1|D1]; [left; lia|].
    destruct D2 as [D2|D2]; [right; exact D2|].
    exfalso. apply HO. split; [exact D1 | split; [exact D2 | exact I]].
  - (* The cut K14614 at the run's FP state: s3 = pod, s10 = mask, the cells sp + 0x30 = buflen, sp + 0xd8 = pp. *)
    intros R F' pc' fc' m0' regs' m' HQ Hx Hrel Hsame Hfrm' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                    ? & ? & F0 & fc0 & m'' & HE & _ & HB30' & HBd8' & _ & _ & _ & _).
    injection HE; intros; subst.
    apply H1. exists pp, pod, (mkFP F0 fc0), L, A, regs', m', md.
    split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact HFR'|]. split; [exact HP|].
    unfold rg. split; [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    rewrite Hspu in HB30', HBd8'. unfold fsp, SLOT_FRAME.
    split.
    + exact (MemNorm.bytes_at_rel_cj rsegs m' _ _ _ Hrel HB30').
    + exact (MemNorm.bytes_at_rel_cj rsegs m' _ _ _ Hrel HBd8').
Qed.

End M02.

(* The segment lemma as U/Prog/RateEnd.v states it. *)
Theorem seg_M02_stmt_holds : RateEnd.seg_M02_stmt.
Proof.
  unfold RateEnd.seg_M02_stmt. intros fx rc B APIf LS SH SK ra empty FF CHECK.
  exact (seg_M02 B APIf ra empty FF CHECK).
Qed.
