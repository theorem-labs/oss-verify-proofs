(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 165 of its 193 lines of code are new or changed and 547 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/M02.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_role's U/Prog/SegCF/M02.v, as libreac/fuzz_ctrl's
   released U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg ->
   SegCF, the segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the
   allocator contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Segment M02 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan): [0x140e4, 0x14114], K140e4 -> K14118
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_M02): pod = fuzz_dup(pp->buf, len), then out's malloc.
   headamp_dup_pod_contract (inp := g_rest g) is a Section hypothesis, run on the normalized memory with
   Tac_slot.sl_run; its premises come from FR and the cut's facts at K140e4 (a0 = pod, s3 = len, s8 = pp, the cell
   sp + 0x8 = cap, the pp block = pp_bytes r, the pod block live and apart from the pp block). The evt ends at 0x14114
   `jal malloc`; one step takes it to malloc's entry (0x1693c) with ra = 0x14118 and the request a0 = 3 cap + 3. The
   run writes only the pod block, so Tac_b1.b1_fr_hb lifts FR over it, and Tac_b1.b1_malloc_call runs the call from
   hb = [(pod, len); (pp, 19744)] to hb = [(out, 3 cap + 3); (pod, len); (pp, 19744)]; its kept-bytes clauses carry
   the frame cells sp + 0x10, sp + 0x68, sp + 0x70, sp + 0x78 and the pp and pod blocks to the cut.
   The segment glue follows reac-pw/fuzz_role's U/Prog/Seg/M01.v (a contract run on the normalized memory, lifted
   over the one block it writes, then malloc). No function is proved here. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1 Tac_b8.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor.
Import ListNotations.
Open Scope Z_scope.

Lemma m02_rec_wf : forall inp, pod_rec_wf (head_rec inp).
Proof.
  intros inp. unfold head_rec. apply (pod_build_wf inp _ (snd (pod_build inp))).
  apply surjective_pairing.
Qed.

Lemma m02_len_bound : forall inp, 8 <= head_len inp <= 5440.
Proof. intros inp. destruct (buf_header (head_rec inp) (m02_rec_wf inp)) as (_ & _ & _ & H). exact H. Qed.

Lemma m02_pp_len : forall inp, Z.of_nat (length (pp_bytes (head_rec inp))) = POD_PROPS.
Proof. intros inp. rewrite (length_pp_bytes (head_rec inp) (m02_rec_wf inp)). reflexivity. Qed.

(* cap = the second input byte mod 10 (SlotInv.g_cap at l = the input). *)
Lemma m02_cap : forall l, 0 <= fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 l))) mod 10 <= 9.
Proof.
  intros l. pose proof (Z.mod_pos_bound (fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 l)))) 10 ltac:(lia)). lia.
Qed.

(* ---- The run: K140e4 to malloc's entry with ra = 0x14118 ---- *)
Definition m02_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (s3 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : word -> option byte) (inp : list byte) (cap pod : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 HEAD_CHECK) sp gp tp t0' t1' t2' (Z_to_bv 64 (3 * cap)) (Z_to_bv 64 pod)
                  (Z_to_bv 64 (OUT_LEN cap)) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 cap) s3 (Z_to_bv 64 (OUT_LEN cap)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x1693c) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pod (buf (head_rec inp)) /\
    Frame.munch [(pod, pod + head_len inp)] m m' /\ Frame.wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma m02_evt : headamp_dup_pod_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (cap pp pod : Z),
    a0 = Z_to_bv 64 pod -> pod <> 0 ->
    s3 = Z_to_bv 64 (head_len inp) -> s8 = Z_to_bv 64 pp -> 0 <= cap <= 9 ->
    bytes_at rsegs m (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 cap)) ->
    bytes_at rsegs m pp (pp_bytes (head_rec inp)) ->
    rw_cells rsegs m pod [CB (Z.to_nat (head_len inp)) junk] ->
    (pod + head_len inp <= pp \/ pp + POD_PROPS <= pod) ->
    mem_inv rsegs m ->
    evt rsegs (m02_post sp gp tp F fc s3 s5 s6 s7 s8 s9 s10 s11 m inp cap pod)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_DUP_POD) fc None m (seg_rom rsegs)).
Proof.
  intros DUPPOD ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m inp junk cap pp pod E10 Hpod0 E19 E24 Hcap HC8 HPP HRW HSEP HMI.
  eapply evt_cut.
  - eapply DUPPOD with (inp := inp) (junk := junk) (cap := cap) (pp := pp) (pod := pod); eassumption.
  - intros ms' POST.
    destruct POST as (ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      -> & HB & MU & WM & MIv).
    unfold HEAD_MALLOC3. step. apply evt_done.
    unfold m02_post. do 15 eexists.
    split; [reflexivity|]. split; [exact HB|]. split; [exact MU|]. split; [exact WM | exact MIv].
Qed.

(* ---- The segment ---- *)
Section M02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.
Hypothesis DUPPOD : headamp_dup_pod_contract.

Lemma seg_M02 : S_M02 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF DUPPOD.
  unfold S_M02. intros H1 g c (pp & pod & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hpod0 & Hpod16 & H19 & H23 & H24 & HC08 & HC10 & HC68 & HC70 & HC78 & HPP).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  assert (Hinpod : In (pod, g_len g) (hb_pod g pod pp)) by (left; reflexivity).
  assert (Hinpp : In (pp, POD_PROPS) (hb_pod g pod pp)) by (right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g (hb_pod g pod pp) pod (g_len g) L A regs mem md HFR HP Hinpod)
    as (STb & Hpod4096 & Hpodc).
  destruct (b1_hb B APIf ra empty FF g (hb_pod g pod pp) pp POD_PROPS L A regs mem md HFR HP Hinpp)
    as (_ & Hpp4096 & Hppc).
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSKc & HS47c & _).
  pose proof alloc_ceiling_value as HAC.
  assert (Hlb : 8 <= g_len g <= 5440) by exact (m02_len_bound (g_rest g)).
  assert (Hcap : 0 <= g_cap g <= 9) by exact (m02_cap (g_in g)).
  assert (Hppl : Z.of_nat (length (pp_bytes (g_rec g))) = POD_PROPS) by exact (m02_pp_len (g_rest g)).
  assert (HSEP : pod + g_len g <= pp \/ pp + POD_PROPS <= pod).
  { assert (HD : fst (pod, g_len g) + snd (pod, g_len g) <= fst (pp, POD_PROPS) \/
                 fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (pod, g_len g)).
    { first [ exact (b1_sep B APIf ra empty g [] (pod, g_len g) [(pp, POD_PROPS)] L A regs mem md (pp, POD_PROPS)
                       HFR HP ltac:(cbn [app]; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [] (pod, g_len g) [(pp, POD_PROPS)] L A regs mem md
                       (pp, POD_PROPS) HFR HP ltac:(cbn [app]; left; reflexivity)) ]. }
    cbn [fst snd] in HD. exact HD. }
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 608).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  destruct (sl_rw_of_stk _ _ _ pod (Z.to_nat (g_len g)) STb ltac:(lia) ltac:(lia)) as (junk & HRW).
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x140e4) mem md
            (m02_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (@fp_regs fx') (@fp_csr fx')
               (YK11.getr regs 19) (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23)
               (YK11.getr regs 24) (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27)
               (normalize rsegs mem) (g_rest g) (g_cap g) pod) _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply (m02_evt DUPPOD) with (junk := junk) (pp := pp).
    + exact H10.
    + exact Hpod0.
    + exact H19.
    + exact H24.
    + exact Hcap.
    + rewrite Hspu. exact (bytes_at_normalize rsegs mem _ _ HMI HC08).
    + exact (bytes_at_normalize rsegs mem _ _ HMI HPP).
    + exact HRW.
    + exact HSEP.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m0 & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & HB & MU & WM & MIv).
    injection HE; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    pose proof (b1_out _ m' _ _ Hrel HB) as HB'.
    (* Bytes outside the pod block: from the cut's memory to the run's. *)
    assert (KEEP : forall a bs, bytes_at rsegs mem a bs ->
                     (a + Z.of_nat (length bs) <= pod \/ pod + g_len g <= a) -> bytes_at rsegs m' a bs).
    { intros a bs Hb Hd. apply (b1_keep _ mem _ m' a bs HMI MU Hrel); [|exact Hb].
      cbn [Frame.disjoint_from]. split; [exact Hd | exact I]. }
    assert (HFR' : FR B APIf ra empty g (hb_pod g pod pp) L A regs' m' md).
    { apply (b1_fr_hb B APIf ra empty FF g (hb_pod g pod pp) pod (g_len g) L A regs mem md regs' m' HFR HP Hinpod).
      - intros a Ha Hs Hb. apply MU'. rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
        split; [exact Hb | exact I].
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 HEAD_CHECK) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 (OUT_LEN (g_cap g)))
      by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g (hb_pod g pod pp) L A regs' m' md regs' (OUT_LEN (g_cap g)));
      [exact HFR' | exact HP | unfold hb_pod; cbn [length]; lia
       | unfold hb_bytes, hb_pod; cbn [map fold_right snd]; unfold POD_PROPS; lia
       | reflexivity | reflexivity | reflexivity
       | rewrite E1; vm_compute; reflexivity | exact E10' | unfold OUT_LEN; lia |].
    intros L' A' regs'' mem'' md' res HF2 HP2 RP H10' Hres0 Hres16 HKF HKB.
    rewrite E1. apply H1. exists pp, pod, res, fx', L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF2|]. split; [exact HP2|].
    unfold rg, fsp, SLOT_FRAME.
    split; [exact H10'|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [etransitivity; [exact (RP 8 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 9 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [exact Hpod0|]. split; [exact Hpod16|].
    split; [etransitivity; [exact (RP 18 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 20 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
    split; [etransitivity; [exact (RP 23 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); exact H23|].
    split.
    { apply (b1_ba_mbyte m'); [apply KEEP; [exact HC10 | rewrite length_le8; lia]|].
      intros i Hi. rewrite length_le8 in Hi. apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [apply KEEP; [exact HC68 | rewrite length_le8; lia]|].
      intros i Hi. rewrite length_le8 in Hi. apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [apply KEEP; [exact HC70 | rewrite length_le8; lia]|].
      intros i Hi. rewrite length_le8 in Hi. apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [apply KEEP; [exact HC78 | rewrite length_le8; lia]|].
      intros i Hi. rewrite length_le8 in Hi. apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [apply KEEP; [exact HPP | rewrite Hppl; lia]|].
      intros i Hi. rewrite Hppl in Hi. apply (HKB pp POD_PROPS i Hinpp). exact Hi. }
    apply (b1_ba_mbyte m'); [exact HB'|].
    intros i Hi. apply (HKB pod (g_len g) i Hinpod). exact Hi.
Qed.

End M02.
