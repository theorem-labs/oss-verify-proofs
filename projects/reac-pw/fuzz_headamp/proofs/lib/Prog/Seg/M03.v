(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module names changed; 310 of its 339 lines of code are new or changed and 545 lines of the source are left out. *)
(* Segment M03 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (plain): [0x14080, 0x14168), K14080 -> K14168
   (Prog/LLVMFuzzerTestOneInput_c.v's S_M03).
   The body is headamp_check_contract's evt (memset(out), the property parse with strtol under it, the three checks
   on the answer, expect_of inlined with pod_nearest's soft-float calls, the four checks against x, first's request),
   taken as a Section hypothesis. Its soft-float callees take MemNorm.task_mem, so the evt runs on
   MemNorm.normalize_cj of the cut's memory (task_mem by MemNorm.mem_inv_cj_normalize), as reac-pw/fuzz_role's
   Prog/Seg/M02.v runs role_check_contract; m03_run_cj is Tac_slot.sl_run_fp with that normalization (role's
   m02_run_cj). The run writes the FP registers and accrues fflags, so it ends at its own FP state with rounding mode
   0, which is the FP state of the cut it closes.
   The premises come from FR at K14080: the cut's registers and frame cells, the record in the pp block and its
   buffer in the pod block (the cut's facts, below TASK_SIZE so kept by normalize_cj), the out block's cells (live,
   so present and writable: m03_blk_cj), the three blocks pairwise apart (Tac_b1.b1_sep) and below the stack region
   [S - 65536, S - 128) (SegFacts.sf_stk_cj), errno's cell (each of errno's four bytes, tp - 164 = 0x3017c, is in a
   writable image segment with initial bytes, so it reads and is writable on any memory: SegFacts.sf_errno_cells;
   PARSE_ERRNO tp is errno_addr B by Tac_errno.te_parse_tp), the SSP GOT slot 0x1eea8 and guard 0x50490 from the
   allocator relation's statics (SegFacts.sf_ssp), the separations of errno and the SSP cells from the blocks
   (block bytes are outside the image, those cells inside it: SegFacts.sf_apart), frm0 from the cut's frm_zero.
   The run writes [sp - 528, sp + 0x1b0), the out block and errno: FR is lifted by Tac_errno.sl_fr_run_hb_errno with
   the footprint Tac_errno.te_fp3. One step then takes `jal malloc` at 0x14164 (ra = 0x14168) with
   a0 = first_req rc (rc <= cap <= 9 by Pod/Headamp.v parse_props_total), and Tac_b1.b1_malloc_call runs the call
   from hb = [(out, ..); (pod, ..); (pp, ..)]; its kept-bytes clauses carry the frame cell sp + 0x58, the pod block
   (kept by the check run: apart from every region it writes) and out's bytes to the cut; errno's cell holds on any
   memory. No function is proved here. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 Tac_errno SegFacts.
Import ListNotations.
Open Scope Z_scope.

(* ---- The run: K14080 to malloc's entry with ra = 0x14168 ---- *)
Definition m03_post (sp gp tp : word) (m : word -> option byte) (nl cap pp pod out : Z) (inp : list byte)
    (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s7' s9' s10' s11' t3' t4' t5' t6' : word)
         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 HEAD_DUP_FIRST) sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pod)
                  (Z_to_bv 64 (first_req (ans_rc (head_ans nl cap inp)))) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 (OUT_LEN cap))
                  (Z_to_bv 64 (if nl =? 1 then 0 else pod)) (Z_to_bv 64 (ans_rc (head_ans nl cap inp))) s7'
                  (Z_to_bv 64 (3 * Z.max (ans_rc (head_ans nl cap inp)) 0)) s9' s10' s11' t3' t4' t5' t6')
             F' (Z_to_bv 64 0x1643c) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    bytes_at rsegs m' out (out_after cap (head_ans nl cap inp)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x58) (le8 (Z_to_bv 64 pp)) /\
    Frame.munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                 (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] m m' /\
    Frame.wmono rsegs m m'.

Section M03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis CHECK : headamp_check_contract.

(* A live block's bytes on the CJ-normalized memory (Tac_b1.b1_blk with normalize_cj). *)
Lemma m03_blk_cj : forall L A mem md a n, aa_MR (APIf rc) L A mem md -> In (a, n) (blocks L A) ->
  stk rsegs (MemNorm.normalize_cj rsegs mem) a (a + n).
Proof.
  intros L A mem md a n HM Hin.
  pose proof Hin as Hin0. apply blocks_In in Hin0 as (p & Ep & Hp).
  destruct (mr_blocks_range B _ (aa_laws (APIf rc)) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2.
  pose proof alloc_ceiling_value as Hac.
  split; [lia|]. split; [lia|].
  intros x Hx.
  destruct (mr_blocks B _ (aa_laws (APIf rc)) L A mem md p n (x - a) HM Hp ltac:(lia)) as ([b Hb] & _).
  rewrite Ep in Hb. replace (a + (x - a)) with x in Hb by lia.
  pose proof (b1_blk_noseg B APIf ra empty FF L A mem md a n x HM Hin ltac:(lia)) as Hns.
  assert (Hcj : MemNorm.cj_drop rsegs (wa x) = false).
  { apply sf_cj_keep.
    - rewrite wa_unsigned by lia. unfold TASK_SIZE. lia.
    - rewrite wa_unsigned by lia. exact Hns. }
  assert (E : MemNorm.normalize_cj rsegs mem (wa x) = Some b)
    by (unfold MemNorm.normalize_cj; rewrite Hcj; exact Hb).
  split.
  - exact (YL01.present_writable rsegs _ x (ex_intro _ b E)).
  - exists b. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

(* A live block of hb holds no image byte. *)
Lemma m03_blk_nimg : forall g hb phi n L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  forall a, phi <= a < phi + n -> ~ in_img B a.
Proof.
  intros g hb phi n L A regs mem md HFR HP Hin a Ha Hi.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (b1_in_hb _ _ _ _ HP Hin) as HinL. apply blocks_In in HinL as (p & Ep & Hp).
  apply (ax_blocks_img (b1_ax B APIf ra empty FF) L A mem md p n (a - phi) HM Hp ltac:(lia)).
  rewrite Ep. replace (phi + (a - phi)) with a by lia. exact Hi.
Qed.

(* Tac_slot.sl_run_fp with MemNorm.normalize_cj (reac-pw/fuzz_role's m02_run_cj). *)
Lemma m03_run_cj : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (MemNorm.normalize_cj rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> MemNorm.mem_rel_cj rsegs m' m0' ->
     MemNorm.cj_same rsegs mem m' ->
     SR rsegs (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SR_canon rsegs _ (fun s => exists s0, Q s0 /\ MemNorm.ms_rel_cj rsegs s s0 /\
                                          MemNorm.cj_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (@YK11.mkst fx' regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)).
    apply MemNorm.evt_normalize_cj; [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *.
    subst cr cf cp cs cv cc co.
    destruct (sl_eqv_mkst R F pc' fc cm (seg_rom rsegs) ms' Heq) as [Ems Hx].
    rewrite Ems.
    exact (HK R F pc' fc m0' HQ _ cm Hx E8 Hsame).
Qed.

Lemma seg_M03 : S_M03 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF CHECK.
  unfold S_M03. intros H1 g c (pp & pod & out & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hout0 & Hout16 & H8 & H9 & Hpod0 & Hpod16 & H18 & H20 & H23 & H24 & HB50 & HB58 & HBpp & HBpod).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  assert (Hinout : In (out, OUT_LEN (g_cap g)) (hb_out g out pod pp)) by (left; reflexivity).
  assert (Hinpod : In (pod, g_len g) (hb_out g out pod pp)) by (right; left; reflexivity).
  assert (Hinpp : In (pp, POD_PROPS) (hb_out g out pod pp)) by (right; right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g (hb_out g out pod pp) out (OUT_LEN (g_cap g)) L A regs mem md HFR HP Hinout)
    as (STout & Hout4096 & Houtc).
  destruct (b1_hb B APIf ra empty FF g (hb_out g out pod pp) pod (g_len g) L A regs mem md HFR HP Hinpod)
    as (STpod & Hpod4096 & Hpodc).
  destruct (b1_hb B APIf ra empty FF g (hb_out g out pod pp) pp POD_PROPS L A regs mem md HFR HP Hinpp)
    as (STpp & Hpp4096 & Hppc).
  pose proof (b1_blk_rom B APIf ra empty FF g (hb_out g out pod pp) out (OUT_LEN (g_cap g)) L A regs mem md
                HFR HP Hinout) as HROMout.
  pose proof (m03_blk_nimg g (hb_out g out pod pp) out (OUT_LEN (g_cap g)) L A regs mem md HFR HP Hinout)
    as HNIout.
  pose proof (m03_blk_nimg g (hb_out g out pod pp) pod (g_len g) L A regs mem md HFR HP Hinpod) as HNIpod.
  pose proof (m03_blk_nimg g (hb_out g out pod pp) pp POD_PROPS L A regs mem md HFR HP Hinpp) as HNIpp.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI0 & HRL & HM & _).
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSKc & HS47c & _).
  pose proof alloc_ceiling_value as HAC.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin).
  pose proof (sf_len_bound (g_rest g) : 8 <= g_len g <= 5440) as Hlb.
  pose proof (sf_cap_rng (g_in g) : 0 <= g_cap g <= 9) as Hcap.
  pose proof (sf_null_rng (g_in g) : 0 <= g_null g <= 1) as Hnl.
  pose proof (sf_rc_bound (g_null g) (g_cap g) (g_rest g) ltac:(lia)) as Hrc.
  change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g) in Hrc.
  destruct (te_parse_tp B APIf ra empty FF g _ L A regs mem md HFR) as (Etp4 & Etp).
  pose proof (sl_errno_val B APIf ra empty FF) as Eerr.
  pose proof (sl_errno B APIf ra empty FF) as Herrc.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 560).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (ERL : head_len (g_rest g) = g_len g) by reflexivity.
  assert (EREC : head_rec (g_rest g) = g_rec g) by reflexivity.
  (* The out block's cells on the CJ-normalized memory. *)
  assert (STcj : stk rsegs (MemNorm.normalize_cj rsegs mem) out (out + OUT_LEN (g_cap g)))
    by exact (m03_blk_cj L A mem md out (OUT_LEN (g_cap g)) HM (b1_in_hb _ _ _ _ HP Hinout)).
  destruct (sl_rw_of_stk _ _ _ out (Z.to_nat (OUT_LEN (g_cap g))) STcj ltac:(lia) ltac:(unfold OUT_LEN in *; lia))
    as (junk & HRWcj).
  (* The three blocks are pairwise apart. *)
  assert (HSop : out + OUT_LEN (g_cap g) <= pod \/ pod + g_len g <= out).
  { assert (HD : fst (out, OUT_LEN (g_cap g)) + snd (out, OUT_LEN (g_cap g)) <= fst (pod, g_len g) \/
                 fst (pod, g_len g) + snd (pod, g_len g) <= fst (out, OUT_LEN (g_cap g))).
    { first [ exact (b1_sep B APIf ra empty g [] (out, OUT_LEN (g_cap g)) [(pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (pod, g_len g) HFR HP ltac:(cbn [app]; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [] (out, OUT_LEN (g_cap g)) [(pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (pod, g_len g) HFR HP ltac:(cbn [app]; left; reflexivity)) ]. }
    cbn [fst snd] in HD. lia. }
  assert (HSopp : out + OUT_LEN (g_cap g) <= pp \/ pp + POD_PROPS <= out).
  { assert (HD : fst (out, OUT_LEN (g_cap g)) + snd (out, OUT_LEN (g_cap g)) <= fst (pp, POD_PROPS) \/
                 fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (out, OUT_LEN (g_cap g))).
    { first [ exact (b1_sep B APIf ra empty g [] (out, OUT_LEN (g_cap g)) [(pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (pp, POD_PROPS) HFR HP ltac:(cbn [app]; right; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [] (out, OUT_LEN (g_cap g)) [(pod, g_len g); (pp, POD_PROPS)]
                       L A regs mem md (pp, POD_PROPS) HFR HP ltac:(cbn [app]; right; left; reflexivity)) ]. }
    cbn [fst snd] in HD. lia. }
  assert (HSpp : pod + g_len g <= pp \/ pp + POD_PROPS <= pod).
  { assert (HD : fst (pod, g_len g) + snd (pod, g_len g) <= fst (pp, POD_PROPS) \/
                 fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (pod, g_len g)).
    { first [ exact (b1_sep B APIf ra empty g [(out, OUT_LEN (g_cap g))] (pod, g_len g) [(pp, POD_PROPS)]
                       L A regs mem md (pp, POD_PROPS) HFR HP ltac:(cbn [app]; right; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [(out, OUT_LEN (g_cap g))] (pod, g_len g) [(pp, POD_PROPS)]
                       L A regs mem md (pp, POD_PROPS) HFR HP ltac:(cbn [app]; right; left; reflexivity)) ]. }
    cbn [fst snd] in HD. lia. }
  (* errno and the SSP cells on the CJ-normalized memory. *)
  destruct (sf_errno_cells (MemNorm.normalize_cj rsegs mem)) as (ev0 & HERR0).
  destruct (b1_syms B APIf ra empty FF) as (_ & _ & _ & Eguard & Egot & _).
  destruct (sf_ssp B _ (b1_ax B APIf ra empty FF) SEGS Egot Eguard L A mem md HM) as (HSSP1 & gv & Hgv & HSSP2).
  assert (HSSP1cj : bytes_at rsegs (MemNorm.normalize_cj rsegs mem) PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD))).
  { apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold PARSE_SSP_GOT, TASK_SIZE; lia
      | exact HSSP1]. }
  assert (HSSP2cj : bytes_at rsegs (MemNorm.normalize_cj rsegs mem) PARSE_SSP_GUARD (le8 (Z_to_bv 64 gv))).
  { apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold PARSE_SSP_GUARD, TASK_SIZE; lia
      | exact HSSP2]. }
  (* errno and the SSP cells are apart from the out and pod blocks. *)
  assert (HEout : 0x3017c + 4 <= out \/ out + OUT_LEN (g_cap g) <= 0x3017c).
  { apply (sf_apart (in_img B) out (out + OUT_LEN (g_cap g)) 0x3017c 4);
      [unfold OUT_LEN; lia | lia | exact HNIout | exact (sf_errno_in B SEGS)]. }
  assert (HEpod : 0x3017c + 4 <= pod \/ pod + g_len g <= 0x3017c).
  { apply (sf_apart (in_img B) pod (pod + g_len g) 0x3017c 4);
      [lia | lia | exact HNIpod | exact (sf_errno_in B SEGS)]. }
  assert (HEpp : 0x3017c + 4 <= pp \/ pp + POD_PROPS <= 0x3017c).
  { apply (sf_apart (in_img B) pp (pp + POD_PROPS) 0x3017c 4);
      [unfold POD_PROPS; lia | lia | exact HNIpp | exact (sf_errno_in B SEGS)]. }
  assert (HGout : 0x1eea8 + 8 <= out \/ out + OUT_LEN (g_cap g) <= 0x1eea8).
  { apply (sf_apart (in_img B) out (out + OUT_LEN (g_cap g)) 0x1eea8 8);
      [unfold OUT_LEN; lia | lia | exact HNIout | exact (sf_got_in B SEGS)]. }
  assert (HUout : 0x50490 + 8 <= out \/ out + OUT_LEN (g_cap g) <= 0x50490).
  { apply (sf_apart (in_img B) out (out + OUT_LEN (g_cap g)) 0x50490 8);
      [unfold OUT_LEN; lia | lia | exact HNIout | exact (sf_guard_in B SEGS)]. }
  rewrite Eerr in Etp. change (0x30220 - 164) with 0x3017c in Etp.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (m03_run_cj fx' regs (Z_to_bv 64 0x14080) mem md
            (m03_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (MemNorm.normalize_cj rsegs mem)
               (g_null g) (g_cap g) pp pod out (g_rest g)) _ Hh Hl HMI).
  - rewrite sl_mkR_of. eapply evt_cut.
    + apply CHECK with (inp := g_rest g) (junk := junk) (nl := g_null g) (cap := g_cap g) (pp := pp) (pod := pod)
        (out := out) (lo := g_S g - 65536) (ev := ev0) (can := Z_to_bv 64 gv).
      * exact H10.
      * lia.
      * exact Hout16.
      * exact H8.
      * exact H9.
      * exact H18.
      * exact H20.
      * exact H23.
      * exact H24.
      * exact Hnl.
      * exact Hcap.
      * rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low;
          [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia | exact HB50].
      * rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low;
          [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia | exact HB58].
      * rewrite EREC. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | | exact HBpp].
        rewrite (sf_pp_len (g_rest g) : Z.of_nat (length (pp_bytes (g_rec g))) = POD_PROPS).
        unfold TASK_SIZE. unfold POD_PROPS in *. lia.
      * lia.
      * exact Hpod16.
      * rewrite EREC. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | | exact HBpod].
        change (Z.of_nat (length (buf (g_rec g)))) with (g_len g). unfold TASK_SIZE. lia.
      * exact HRWcj.
      * exact HROMout.
      * rewrite ERL. exact HSop.
      * exact HSopp.
      * rewrite ERL. exact HSpp.
      * lia.
      * rewrite ERL. lia.
      * unfold POD_PROPS in *. lia.
      * rewrite Hspu. unfold FRAME_LOCALS. apply sf_stk_cj; [exact HMI | unfold SL_TOP; lia | unfold TASK_SIZE; lia |].
        intros a Ha. rewrite <- SEGS. apply Hwin. lia.
      * rewrite Hspu. unfold MID_STACK, PARSE_STACK. lia.
      * rewrite Hspu. Z.div_mod_to_equations. lia.
      * rewrite Hspu. unfold FRAME_LOCALS. intros a Ha.
        apply (b8_seg_rom_hi B APIf ra empty FF). lia.
      * rewrite Etp. exact HERR0.
      * rewrite Etp, Hspu, ERL. unfold FRAME_LOCALS. cbn [disjoint_from].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
      * exact HSSP1cj.
      * exact HSSP2cj.
      * rewrite Etp, Hspu. unfold FRAME_LOCALS, PARSE_SSP_GOT. cbn [disjoint_from].
        split; [lia|]. split; [lia|]. split; [lia | exact I].
      * rewrite Etp, Hspu. unfold FRAME_LOCALS, PARSE_SSP_GUARD. cbn [disjoint_from].
        split; [lia|]. split; [lia|]. split; [lia | exact I].
      * exact Hfrm.
      * exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
      * exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
    + intros ms' POST.
      destruct POST as (ra' & t0' & t1' & t2' & s0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s7' & s9' & s10' &
                        s11' & t3' & t4' & t5' & t6' & F' & fc' & m' & ev' & -> & Hfrm' & HBout & HB58' & HERR' &
                        MU & WM & MIv & ST2).
      unfold HEAD_MALLOC4. step. apply evt_done.
      unfold m03_post. do 22 eexists.
      split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact HBout|]. split; [exact HB58'|].
      split; [exact MU | exact WM].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F0 & fc0 & m0 & -> & _).
    do 5 eexists. reflexivity.
  - intros R F' pc' fc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F0 & fc0 & m'' &
                    HE & Hfrm' & HBout & HB58' & MU & WM).
    injection HE; intros; subst.
    change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g) in *.
    rewrite Hspu in MU, HB58'. rewrite Etp in MU. unfold MID_STACK, PARSE_STACK, FRAME_LOCALS in MU.
    pose proof (MemNorm.mem_rel_cj_normalize rsegs mem HMI) as HR0.
    pose proof (MemNorm.munch_rel_cj rsegs _ mem (MemNorm.normalize_cj rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (MemNorm.wmono_rel_cj rsegs mem (MemNorm.normalize_cj rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (MemNorm.ro_agree_same_cj rsegs mem m' HMI Hsame) as Hro'.
    (* The bytes the next cut keeps, on the memory after the run. *)
    pose proof (MemNorm.bytes_at_rel_cj rsegs m' _ _ _ Hrel HBout) as HBout'.
    pose proof (MemNorm.bytes_at_rel_cj rsegs m' _ _ _ Hrel HB58') as HB58''.
    assert (HBpod' : bytes_at rsegs m' pod (buf (g_rec g))).
    { apply (bytes_at_transport rsegs _ mem m' pod _ HBpod MU').
      change (Z.of_nat (length (buf (g_rec g)))) with (g_len g). cbn [disjoint_from].
      split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    (* FR across the run: the window, the out block and errno. *)
    assert (HFR' : FR B APIf ra empty g (hb_out g out pod pp) L A regs' m' md).
    { apply (sl_fr_run_hb_errno B APIf ra empty FF g (hb_out g out pod pp) out (OUT_LEN (g_cap g)) L A regs mem md
               regs' m' _ HFR HP Hinout MU' WM' Hro').
      - intros xx Hxx HO.
        assert (HEB : 0x3017c = errno_addr B) by (rewrite Eerr; reflexivity).
        first [ apply (te_fp3 B g (g_S g - 560 - (0xa0 + 0x120 + 0x50)) (g_S g - 560 + 0x1b0) out
                         (OUT_LEN (g_cap g)) out (OUT_LEN (g_cap g)) 0x3017c xx)
              | apply (te_fp3 B APIf ra empty FF g (g_S g - 560 - (0xa0 + 0x120 + 0x50)) (g_S g - 560 + 0x1b0) out
                         (OUT_LEN (g_cap g)) out (OUT_LEN (g_cap g)) 0x3017c xx) ];
          [unfold SLOT_K, SLOT_STACK; lia | lia | lia | lia | exact HEB | exact HO].
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x14168) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 (first_req (ans_rc (g_ans g))))
      by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    pose proof (sf_first_req (ans_rc (g_ans g)) ltac:(lia)) as Hfr.
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g (hb_out g out pod pp) L A regs' m' md regs'
             (first_req (ans_rc (g_ans g))));
      [exact HFR' | exact HP | unfold hb_out, hb_pod; cbn [length]; lia
       | unfold hb_bytes, hb_out, hb_pod; cbn [map fold_right snd]; unfold OUT_LEN, POD_PROPS; lia
       | reflexivity | reflexivity | reflexivity
       | rewrite E1; vm_compute; reflexivity | exact E10' | lia |].
    intros L' A' regs'' mem'' md' res HF2 HP2 RP H10' Hres0 Hres16 HKF HKB.
    rewrite E1. apply H1.
    exists pp, pod, out, res, (first_req (ans_rc (g_ans g))).
    exists (mkFP F0 fc0), L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact HF2|]. split; [exact HP2|].
    unfold rg.
    split; [exact H10'|]. split; [exact Hres0|]. split; [exact Hres16|]. split; [reflexivity|].
    split; [etransitivity; [exact (RP 9 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [exact Hpod0|]. split; [exact Hpod16|].
    split; [etransitivity; [exact (RP 18 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 19 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [exact Hout0|]. split; [exact Hout16|].
    split; [etransitivity; [exact (RP 20 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 21 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 22 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 24 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split.
    { unfold fsp, SLOT_FRAME. apply (b1_ba_mbyte m'); [exact HB58''|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HBpod'|]. intros i Hi. exact (HKB pod (g_len g) i Hinpod Hi). }
    split.
    { apply (b1_ba_mbyte m'); [exact HBout'|]. intros i Hi.
      rewrite (sf_out_after_len (g_cap g) (g_ans g) ltac:(lia)
                 (sf_ans_ok (g_null g) (g_cap g) (g_rest g) ltac:(lia))) in Hi.
      exact (HKB out (OUT_LEN (g_cap g)) i Hinout Hi). }
    rewrite Eerr. exact (sf_errno_cells mem'').
Qed.

End M03.
