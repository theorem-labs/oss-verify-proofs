(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 455 of its 574 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 184 of its 219 lines of code are new or changed and 539 lines of the source are left out. *)
(* Segment M02 of reac-pw/fuzz_role LLVMFuzzerTestOneInput (UBSan): [0x13f34, 0x141b4], K13f34 -> K141b4
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_M02).
   The plain segment (lib/Prog/Seg/M02.v) with the UBSan numbers: the frame is 544 bytes, pp is s8, pp + 0x4000 is
   s7, the cut's cells are sp + 0x10 (the flags byte), sp + 0x68 (pp) and sp + 0x70 (pp + 0x4d14), and
   role_check_contract takes one premise more, reac_role_refuse_code's codes[] table in .data.rel.ro
   (m02_relro_cj). The evt runs on MemNorm.normalize_cj of the cut's memory (its soft-float callees are stated over
   the CJ memory invariant) and ends at its own FP state with rounding mode 0, which is the FP state of the cut it
   closes. No function is proved here. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(* ---- The CJ normalization keeps every byte the segment reads ---- *)
Lemma m02_cj_keep : forall (w : word), bv_unsigned w < TASK_SIZE ->
  find_segment rsegs (bv_unsigned w) 1 = None -> MemNorm.cj_drop rsegs w = false.
Proof.
  intros w Ht Hns. apply MemNorm.cj_drop_false_intro; [|right; exact Ht].
  unfold Mem.ro_addr. rewrite Hns. reflexivity.
Qed.

Lemma m02_cj_hi : forall (w : word), SL_TOP <= bv_unsigned w -> bv_unsigned w < TASK_SIZE ->
  MemNorm.cj_drop rsegs w = false.
Proof.
  intros w Hlo Ht. apply m02_cj_keep; [exact Ht|].
  destruct (find_segment rsegs (bv_unsigned w) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (sl_find_top (bv_unsigned w) 1 seg E). unfold SL_TOP in *. lia.
Qed.

Lemma m02_stk_cj : forall m lo hi, ro_agree rsegs m -> SL_TOP <= lo -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) ->
  stk rsegs (MemNorm.normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi Hro Hlo Hhi H.
  assert (Htask : TASK_SIZE < 2 ^ 64) by (unfold TASK_SIZE; lia).
  apply sl_stk_of_writable; [exact Hlo | lia|].
  intros a Ha. unfold writable_at.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply MState.unsigned_lit; unfold SL_TOP in *; lia).
  rewrite (MemNorm.wview_rel_cj rsegs m _ (Z_to_bv 64 a) (MemNorm.mem_rel_cj_normalize rsegs m Hro)
             (m02_cj_hi (Z_to_bv 64 a) ltac:(rewrite Hu; unfold SL_TOP in *; lia) ltac:(rewrite Hu; lia))).
  exact (H a Ha).
Qed.

Section M02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Hypothesis CHECK : role_check_contract.

(* A live block's bytes on the CJ-normalized memory. *)
Lemma m02_blk_cj : forall L A mem md a n, aa_MR (APIf rc) L A mem md -> In (a, n) (blocks L A) ->
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
  { apply m02_cj_keep.
    - rewrite wa_unsigned by lia. unfold TASK_SIZE. lia.
    - rewrite wa_unsigned by lia. exact Hns. }
  assert (E : MemNorm.normalize_cj rsegs mem (wa x) = Some b)
    by (unfold MemNorm.normalize_cj; rewrite Hcj; exact Hb).
  split.
  - exact (YL01.present_writable rsegs _ x (ex_intro _ b E)).
  - exists b. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

(* Tac_b8.b8_relro_norm with MemNorm.normalize_cj: the codes[] table reads as the image. *)
Lemma m02_relro_cj : forall mem a, relro B mem -> MI B mem -> 0x1e0f0 <= a < 0x1e0f0 + 424 ->
  mrd rsegs (MemNorm.normalize_cj rsegs mem) (wa a) = seg_rom rsegs (wa a).
Proof.
  intros mem a HR HMI Ha. unfold MI in HMI. rewrite (b8_segs B APIf ra empty FF) in HMI.
  rewrite (MemNorm.mrd_normalize_cj rsegs mem (wa a) HMI
             ltac:(right; right; rewrite wa_unsigned by lia; unfold TASK_SIZE; lia)).
  change (mrd rsegs mem (wa a)) with (mbyte rsegs mem a).
  unfold relro, G_img_c in HR. rewrite (b8_segs B APIf ra empty FF) in HR. apply HR.
  exists 0x1e0f0, 424. split; [left; reflexivity | lia].
Qed.

(* Tac_slot.sl_run_fp with MemNorm.normalize_cj. *)
Lemma m02_run_cj : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
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

Lemma seg_M02 : S_M02 B APIf ra empty.
Proof.
  unfold S_M02. intros H1 g c (pp & pod & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hpod0 & Hpod16 & H18 & H24 & H23 & HB10 & HB68 & HB70 & HBpp).
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
  assert (ERL : role_len (g_rest g) = g_len g) by reflexivity.
  assert (EREC : fst (pod_build (g_rest g)) = g_rec g) by reflexivity.
  assert (STpodcj : stk rsegs (MemNorm.normalize_cj rsegs mem) pod (pod + g_len g))
    by exact (m02_blk_cj L A mem md pod (g_len g) HM (b1_in_hb _ _ _ _ HP Hinpod)).
  destruct (sl_rw_of_stk _ _ _ pod (Z.to_nat (g_len g)) STpodcj ltac:(lia) ltac:(lia)) as (junk & HRWcj).
  assert (HSEP : pod + g_len g <= pp \/ pp + POD_PROPS <= pod).
  { assert (HD : fst (pod, g_len g) + snd (pod, g_len g) <= fst (pp, POD_PROPS) \/
                 fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (pod, g_len g)).
    { first [ exact (b1_sep B APIf ra empty g [] (pod, g_len g) [(pp, POD_PROPS)] L A regs mem md
                       (pp, POD_PROPS) HFR HP ltac:(cbn [app]; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [] (pod, g_len g) [(pp, POD_PROPS)] L A regs mem md
                       (pp, POD_PROPS) HFR HP ltac:(cbn [app]; left; reflexivity)) ]. }
    cbn [fst snd] in HD. lia. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (m02_run_cj fx' regs (Z_to_bv 64 0x13f34) mem md _ _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply CHECK with (inp := g_rest g) (junk := junk) (fl := g_fl g) (pp := pp) (pod := pod)
      (lo := g_S g - 65536).
    + exact H10.
    + exact Hpod0.
    + exact Hpod16.
    + rewrite ERL. exact H18.
    + exact H24.
    + exact H23.
    + unfold g_fl. destruct (g_in g) as [|b l]; [lia | exact (b1_byte_rng b)].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB10].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB68].
    + rewrite Hspu. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia
        | exact HB70].
    + rewrite EREC. apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | | exact HBpp].
      rewrite (length_pp_bytes (g_rec g)).
      * unfold PP_SIZE, TASK_SIZE. unfold POD_PROPS in Hppc. lia.
      * apply (pod_build_wf (g_rest g) _ (snd (pod_build (g_rest g)))). apply surjective_pairing.
    + rewrite ERL. exact HRWcj.
    + rewrite ERL. intros a Ha. apply HROMpod. lia.
    + rewrite ERL. exact HSEP.
    + rewrite ERL. lia.
    + lia.
    + rewrite Hspu. unfold FRAME_LOCALS. apply m02_stk_cj; [exact HMI | unfold SL_TOP; lia
        | unfold TASK_SIZE; lia |].
      intros a Ha. rewrite <- SEGS. apply Hwin. lia.
    + rewrite Hspu. unfold MID_STACK. lia.
    + rewrite Hspu. Z.div_mod_to_equations. lia.
    + rewrite Hspu. unfold FRAME_LOCALS. intros a Ha.
      apply (b8_seg_rom_hi B APIf ra empty FF). lia.
    + intros a Ha. apply (m02_relro_cj mem a HRL HMI0).
      unfold CODES_TBL, CODES_TBL_END in Ha. lia.
    + exact Hfrm.
    + exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
    + exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
               ? & F0 & fc0 & m0 & -> & _).
    do 5 eexists. reflexivity.
  - intros R F' pc' fc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                    ? & ? & F0 & fc0 & m'' & HE & Hfrm' & MU & WM & MIv & ST2).
    injection HE; intros; subst.
    rewrite Hspu in MU. unfold MID_STACK, FRAME_LOCALS in MU.
    pose proof (MemNorm.mem_rel_cj_normalize rsegs mem HMI) as HR0.
    pose proof (MemNorm.munch_rel_cj rsegs _ mem (MemNorm.normalize_cj rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (MemNorm.wmono_rel_cj rsegs mem (MemNorm.normalize_cj rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (MemNorm.ro_agree_same_cj rsegs mem m' HMI Hsame) as Hro'.
    assert (HFR' : FR B APIf ra empty g (hb_pod g pod pp) L A regs' m' md).
    { apply (b1_fr_hb B APIf ra empty FF g (hb_pod g pod pp) pod (g_len g) L A regs mem md regs' m'
               HFR HP Hinpod).
      - intros a Ha Hs Hb. unfold SLOT_K, SLOT_STACK in Hs. apply MU'.
        rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
        split; [lia | split; [lia | exact I]].
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    rewrite <- SEGS. apply H1. exists pp, pod, (mkFP F0 fc0), L, A, regs', m', md.
    split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact HFR'|]. split; [exact HP|].
    unfold rg. split.
    + rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End M02.
