(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 277 of its 306 lines of code are new or changed and 545 lines of the source are left out. *)
(* Segment M03 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan): [0x14118, 0x147e0], K14118 -> K147e0
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_M03).
   headamp_check_contract is a Section hypothesis. It runs on MemNorm.normalize_cj of the cut's memory (its
   soft-float callees are stated over the CJ memory invariant), from 0x14118 `beqz a0` to 0x147dc with a0 = first's
   request, at its own FP state with rounding mode 0; one step takes 0x147dc `jal malloc` to malloc's entry with
   ra = 0x147e0. Its premises come from FR at K14118: the frame cells, the pp and pod blocks, the out block's cells,
   the stack region, errno as a C4 cell apart from the stack region and the three blocks, strtol's SSP cells
   (M03_cells.v), mem_inv and task_mem of the CJ memory. Tac_errno.sl_mid_fp_hb_errno_cj runs it and carries FR
   across it with errno in the write set (the stack below the frame's locals, the out block, errno; te_fp3); the pod
   block's bytes follow by the run's munch. Then Tac_b1.b1_malloc_call runs malloc(first_req rc) from
   hb = [out; pod; pp]: its kept-bytes clauses carry the cell sp + 0x70, the pod block and the out block (out_after)
   to the cut, and errno is a cell again by FR's errno clause. The helper lemmas are stated over plain inputs.
   No function is proved here. *)
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

(* ---- The CJ normalization keeps every byte the segment reads (fuzz_role's U M02 forms) ---- *)
Lemma m03_cj_keep : forall (w : word), bv_unsigned w < TASK_SIZE ->
  find_segment rsegs (bv_unsigned w) 1 = None -> MemNorm.cj_drop rsegs w = false.
Proof.
  intros w Ht Hns. apply MemNorm.cj_drop_false_intro; [|right; exact Ht].
  unfold Mem.ro_addr. rewrite Hns. reflexivity.
Qed.

Lemma m03_cj_hi : forall (w : word), SL_TOP <= bv_unsigned w -> bv_unsigned w < TASK_SIZE ->
  MemNorm.cj_drop rsegs w = false.
Proof.
  intros w Hlo Ht. apply m03_cj_keep; [exact Ht|].
  destruct (find_segment rsegs (bv_unsigned w) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (sl_find_top (bv_unsigned w) 1 seg E). unfold SL_TOP in *. lia.
Qed.

Lemma m03_stk_cj : forall m lo hi, ro_agree rsegs m -> SL_TOP <= lo -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) ->
  stk rsegs (MemNorm.normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi Hro Hlo Hhi H.
  assert (Htask : TASK_SIZE < 2 ^ 64) by (unfold TASK_SIZE; lia).
  apply sl_stk_of_writable; [exact Hlo | lia|].
  intros a Ha. unfold writable_at.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply MState.unsigned_lit; unfold SL_TOP in *; lia).
  rewrite (MemNorm.wview_rel_cj rsegs m _ (Z_to_bv 64 a) (MemNorm.mem_rel_cj_normalize rsegs m Hro)
             (m03_cj_hi (Z_to_bv 64 a) ltac:(rewrite Hu; unfold SL_TOP in *; lia) ltac:(rewrite Hu; lia))).
  exact (H a Ha).
Qed.

(* ---- The run: the check segment, then one step through 0x147dc `jal malloc` ---- *)
Definition m03_post (sp gp tp : word) (m : word -> option byte) (inp : list byte) (nl cap pp pod out : Z)
    (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s7' s9' s10' s11' t3' t4' t5' t6' : word)
         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 HEAD_DUP_FIRST) sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pod)
                  (Z_to_bv 64 (first_req (ans_rc (head_ans nl cap inp)))) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 (OUT_LEN cap))
                  (Z_to_bv 64 (if nl =? 1 then 0 else pod)) (Z_to_bv 64 (ans_rc (head_ans nl cap inp))) s7'
                  (Z_to_bv 64 (3 * Z.max (ans_rc (head_ans nl cap inp)) 0)) s9' s10' s11' t3' t4' t5' t6')
             F' (Z_to_bv 64 0x1693c) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    bytes_at rsegs m' out (out_after cap (head_ans nl cap inp)) /\
    bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 pp)) /\
    Frame.munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                 (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] m m' /\
    Frame.wmono rsegs m m'.

Section M03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Hypothesis CHECK : headamp_check_contract.

(* A live block's bytes on the CJ-normalized memory. *)
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
  { apply m03_cj_keep.
    - rewrite wa_unsigned by lia. unfold TASK_SIZE. lia.
    - rewrite wa_unsigned by lia. exact Hns. }
  assert (E : MemNorm.normalize_cj rsegs mem (wa x) = Some b)
    by (unfold MemNorm.normalize_cj; rewrite Hcj; exact Hb).
  split.
  - exact (YL01.present_writable rsegs _ x (ex_intro _ b E)).
  - exists b. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

Lemma seg_M03 : S_M03 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   six segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF CHECK.
  unfold S_M03. intros H1 g c (pp & pod & out & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hout0 & Hout16 & H8 & H9 & Hpod0 & Hpod16 & H18 & H20 & H23 & HB10 & HB68 & HB70 & HB78 & HBpp &
     HBpod).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  assert (Hcap : 0 <= g_cap g <= 9) by exact (mc_cap_rng _).
  assert (Hnl : 0 <= g_null g <= 1) by exact (mc_null_rng _).
  assert (Hlb : 8 <= g_len g <= 5440) by exact (mc_len_bound _).
  assert (Hrc0 : -1 <= ans_rc (g_ans g) <= g_cap g) by exact (mc_rc_rng _ _ _ (proj1 Hcap)).
  assert (Hrc : -1 <= ans_rc (g_ans g) <= 9) by lia.
  destruct (mc_first_req (ans_rc (g_ans g)) Hrc) as (Hfr1 & Hfr2 & Hfr3).
  assert (Hinout : In (out, OUT_LEN (g_cap g)) (hb_out g out pod pp)) by (left; reflexivity).
  assert (Hinpod : In (pod, g_len g) (hb_out g out pod pp)) by (right; left; reflexivity).
  assert (Hinpp : In (pp, POD_PROPS) (hb_out g out pod pp)) by (right; right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g _ out (OUT_LEN (g_cap g)) L A regs mem md HFR HP Hinout)
    as (STo & Ho4096 & Hoc).
  destruct (b1_hb B APIf ra empty FF g _ pod (g_len g) L A regs mem md HFR HP Hinpod) as (STp & Hp4096 & Hpc).
  destruct (b1_hb B APIf ra empty FF g _ pp POD_PROPS L A regs mem md HFR HP Hinpp) as (STpp & Hpp4096 & Hppc).
  assert (Sop : out + OUT_LEN (g_cap g) <= pod \/ pod + g_len g <= out).
  { assert (HD : fst (out, OUT_LEN (g_cap g)) + snd (out, OUT_LEN (g_cap g)) <= fst (pod, g_len g) \/
                 fst (pod, g_len g) + snd (pod, g_len g) <= fst (out, OUT_LEN (g_cap g))).
    { eapply b1_sep with (hb1 := []) (hb2 := [(pod, g_len g); (pp, POD_PROPS)]);
        first [exact HFR | exact HP | exact FF | (cbn [app]; left; reflexivity)]. }
    cbn [fst snd] in HD. exact HD. }
  assert (Sopp : out + OUT_LEN (g_cap g) <= pp \/ pp + POD_PROPS <= out).
  { assert (HD : fst (out, OUT_LEN (g_cap g)) + snd (out, OUT_LEN (g_cap g)) <= fst (pp, POD_PROPS) \/
                 fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (out, OUT_LEN (g_cap g))).
    { eapply b1_sep with (hb1 := []) (hb2 := [(pod, g_len g); (pp, POD_PROPS)]);
        first [exact HFR | exact HP | exact FF | (cbn [app]; right; left; reflexivity)]. }
    cbn [fst snd] in HD. exact HD. }
  assert (Spp : pod + g_len g <= pp \/ pp + POD_PROPS <= pod).
  { assert (HD : fst (pod, g_len g) + snd (pod, g_len g) <= fst (pp, POD_PROPS) \/
                 fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (pod, g_len g)).
    { eapply b1_sep with (hb1 := [(out, OUT_LEN (g_cap g))]) (hb2 := [(pp, POD_PROPS)]);
        first [exact HFR | exact HP | exact FF | (cbn [app]; right; left; reflexivity)]. }
    cbn [fst snd] in HD. exact HD. }
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI0 & HRL & HM & _ & _ & _ & _ & _ & _ & _ & Herr & _).
  destruct (mc_errno_cj B APIf ra empty FF mem HMI Herr) as (ev & HERR).
  destruct (mc_ssp_cj B APIf ra empty FF L A mem md HM HMI) as (HGOT & can & HGRD).
  destruct (te_parse_tp B APIf ra empty FF g _ L A regs mem md HFR) as (Etp & EPE).
  pose proof (mc_errno_val B APIf ra empty FF) as Eerr.
  pose proof (mc_errno_blk B APIf ra empty FF L A mem md pod (g_len g) HM (b1_in_hb _ _ _ _ HP Hinpod) ltac:(lia))
    as DEpod.
  pose proof (mc_errno_blk B APIf ra empty FF L A mem md out _ HM (b1_in_hb _ _ _ _ HP Hinout)
                ltac:(unfold OUT_LEN; lia)) as DEout.
  pose proof (mc_errno_blk B APIf ra empty FF L A mem md pp POD_PROPS HM (b1_in_hb _ _ _ _ HP Hinpp)
                ltac:(unfold POD_PROPS; lia)) as DEpp.
  pose proof (mc_got_blk B APIf ra empty FF L A mem md out _ HM (b1_in_hb _ _ _ _ HP Hinout)
                ltac:(unfold OUT_LEN; lia)) as DGout.
  pose proof (mc_guard_blk B APIf ra empty FF L A mem md out _ HM (b1_in_hb _ _ _ _ HP Hinout)
                ltac:(unfold OUT_LEN; lia)) as DDout.
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSKc & HS47c & _).
  pose proof alloc_ceiling_value as HAC.
  pose proof (sl_errno B APIf ra empty FF) as Herrc.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 608).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (STocj : stk rsegs (MemNorm.normalize_cj rsegs mem) out (out + OUT_LEN (g_cap g)))
    by exact (m03_blk_cj L A mem md out _ HM (b1_in_hb _ _ _ _ HP Hinout)).
  destruct (sl_rw_of_stk _ _ _ out (Z.to_nat (OUT_LEN (g_cap g))) STocj ltac:(lia) ltac:(unfold OUT_LEN in *; lia))
    as (junk & HRWcj).
  assert (HBpodcj : bytes_at rsegs (MemNorm.normalize_cj rsegs mem) pod (buf (g_rec g))).
  { apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | | exact HBpod].
    change (Z.of_nat (length (buf (g_rec g)))) with (g_len g). unfold TASK_SIZE. lia. }
  eapply (sl_mid_fp_hb_errno_cj B APIf ra empty FF g _ out (OUT_LEN (g_cap g)) L A regs mem md (Z_to_bv 64 0x14118)
            (m03_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (MemNorm.normalize_cj rsegs mem)
               (g_rest g) (g_null g) (g_cap g) pp pod out) _ HFR HP Hinout).
  - rewrite sl_mkR_of.
    eapply evt_cut.
    + apply CHECK with (inp := g_rest g) (junk := junk) (nl := g_null g) (cap := g_cap g) (pp := pp) (pod := pod)
        (out := out) (lo := g_S g - 65536) (ev := ev) (can := can).
      * exact H10.
      * lia.
      * exact Hout16.
      * exact H8.
      * exact H9.
      * exact H18.
      * exact H20.
      * exact H23.
      * exact Hnl.
      * exact Hcap.
      * rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low;
          [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia | exact HB10].
      * rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low;
          [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia | exact HB68].
      * rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low;
          [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia | exact HB70].
      * rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low;
          [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia | exact HB78].
      * apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | | exact HBpp].
        rewrite (length_pp_bytes (head_rec (g_rest g)) (mc_rec_wf (g_rest g))).
        unfold PP_SIZE, TASK_SIZE, POD_PROPS in *. lia.
      * lia.
      * exact Hpod16.
      * exact HBpodcj.
      * exact HRWcj.
      * intros a Ha. exact (b1_blk_rom B APIf ra empty FF g _ out _ L A regs mem md HFR HP Hinout a Ha).
      * exact Sop.
      * exact Sopp.
      * exact Spp.
      * lia.
      * change (head_len (g_rest g)) with (g_len g). lia.
      * unfold POD_PROPS in *. lia.
      * rewrite Hspu. unfold FRAME_LOCALS.
        apply m03_stk_cj; [exact HMI | unfold SL_TOP; lia | unfold TASK_SIZE; lia |].
        intros a Ha. rewrite <- SEGS. apply Hwin. lia.
      * rewrite Hspu. unfold MID_STACK, PARSE_STACK. lia.
      * rewrite Hspu. Z.div_mod_to_equations. lia.
      * rewrite Hspu. unfold FRAME_LOCALS. intros a Ha.
        apply (b8_seg_rom_hi B APIf ra empty FF). lia.
      * rewrite EPE. exact HERR.
      * rewrite EPE, Hspu. change (head_len (g_rest g)) with (g_len g). cbn [disjoint_from].
        repeat split; lia.
      * unfold PARSE_SSP_GOT, PARSE_SSP_GUARD. exact HGOT.
      * unfold PARSE_SSP_GUARD. exact HGRD.
      * rewrite EPE, Eerr, Hspu. unfold PARSE_SSP_GOT. cbn [disjoint_from].
        repeat split; lia.
      * rewrite EPE, Eerr, Hspu. unfold PARSE_SSP_GUARD. cbn [disjoint_from].
        repeat split; lia.
      * exact Hfrm.
      * exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
      * exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
    + intros ms' POST.
      destruct POST as (ra1 & t01 & t11 & t21 & s01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & s71 & s91 & s101 &
                        s111 & t31 & t41 & t51 & t61 & F1 & fc1 & m1 & ev1 & -> & Hfrm1 & HBo & HB70o & _ & MU &
                        WM & _ & _).
      unfold HEAD_MALLOC4. step. apply evt_done.
      unfold m03_post. do 22 eexists.
      split; [reflexivity|]. split; [exact Hfrm1|]. split; [exact HBo|]. split; [exact HB70o|].
      split; [exact MU | exact WM].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F0 & fc0 & m0 & -> &
               Hfrm0 & _ & _ & MU0 & WM0).
    do 5 eexists. split; [reflexivity|]. split; [exact Hfrm0|].
    split; [|split; [reflexivity | split; reflexivity]].
    eexists. split; [exact MU0|]. split; [exact WM0|].
    intros y0 Hy0 HO. rewrite Hspu in HO.
    apply te_fp3 with (lo := g_S g - 608 - MID_STACK) (hi := g_S g - 608 + FRAME_LOCALS) (o := out)
      (k := OUT_LEN (g_cap g)) (E := PARSE_ERRNO (YK11.getr regs 4)).
    + unfold SLOT_K, SLOT_STACK, MID_STACK, PARSE_STACK. lia.
    + unfold FRAME_LOCALS. lia.
    + lia.
    + lia.
    + exact EPE.
    + exact HO.
  - intros R F' pc' fc' m0' regs' m' HQ Hx Hrel Hfrm'' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F0 & fc0 & m'' &
                    HE & Hfrm' & HBo & HB70o & MU & WM).
    injection HE; intros; subst.
    rewrite Hspu in MU, HB70o.
    pose proof (MemNorm.bytes_at_rel_cj rsegs m' _ _ _ Hrel HBo) as HBo'.
    pose proof (MemNorm.bytes_at_rel_cj rsegs m' _ _ _ Hrel HB70o) as HB70'.
    assert (HBpod' : bytes_at rsegs m' pod (buf (g_rec g))).
    { apply (MemNorm.bytes_at_rel_cj rsegs m' _ _ _ Hrel).
      apply (b8_ba_munch rsegs _ (MemNorm.normalize_cj rsegs mem) _ pod _ HBpodcj MU).
      change (Z.of_nat (length (buf (g_rec g)))) with (g_len g). intros i Hi.
      rewrite EPE, Eerr. unfold MID_STACK, PARSE_STACK, FRAME_LOCALS, OUT_LEN in *. cbn [Frame.outside].
      repeat split; lia. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 HEAD_DUP_FIRST) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10 : YK11.getr regs' 10 = Z_to_bv 64 (first_req (ans_rc (g_ans g))))
      by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply (b1_malloc_call B APIf ra empty FF g (hb_out g out pod pp) L A regs' m' md regs'
             (first_req (ans_rc (g_ans g))));
      [exact HFR' | exact HP | cbn [length hb_out hb_pod]; lia
       | unfold hb_bytes, hb_out, hb_pod; cbn [map fold_right snd]; unfold OUT_LEN, POD_PROPS; lia
       | reflexivity | reflexivity | reflexivity
       | rewrite E1; vm_compute; reflexivity | exact E10 | lia |].
    intros L' A' regs'' mem'' md' res HF2 HP2 RP H10' Hres0 Hres16 HKF HKB.
    rewrite E1. unfold HEAD_DUP_FIRST.
    lazymatch goal with
    | |- SR _ (mkCfg (@YK11.mkst ?f _ _ _ _) _) _ =>
        apply H1; exists pp, pod, out, res, (first_req (ans_rc (g_ans g))), f, L', A', regs'', mem'', md'
    end.
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
    { apply (b1_ba_mbyte m'); [exact HB70'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HBpod'|]. intros i Hi.
      change (Z.of_nat (length (buf (g_rec g)))) with (g_len g) in Hi.
      exact (HKB pod (g_len g) i Hinpod Hi). }
    split.
    { apply (b1_ba_mbyte m'); [exact HBo'|]. intros i Hi.
      pose proof (mc_out_len (g_null g) (g_cap g) (g_rest g) (proj1 Hcap)) as Eo.
      change (head_ans (g_null g) (g_cap g) (g_rest g)) with (g_ans g) in Eo.
      rewrite Eo in Hi.
      exact (HKB out (OUT_LEN (g_cap g)) i Hinout Hi). }
    pose proof HF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Herr2 & _).
    exact (mc_errno_rw B APIf ra empty FF mem'' Herr2).
Qed.

End M03.
