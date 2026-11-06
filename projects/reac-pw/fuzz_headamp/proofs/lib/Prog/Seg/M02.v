(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module names changed; 157 of its 180 lines of code are new or changed and 551 lines of the source are left out. *)
(* Segment M02 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (plain): [0x1404c, 0x14080), K1404c -> K14080
   (Prog/LLVMFuzzerTestOneInput_c.v's S_M02).
   The body is headamp_dup_pod_contract's evt (pod = fuzz_dup(pp->buf, len): fuzz.h:75-78 and the size of out,
   fuzz_headamp.c:326), taken as a Section hypothesis and run on the normalized memory with Tac_slot.sl_run, in the
   form of reac-pw/fuzz_role's Prog/Seg/M01.v. Its premises come from FR at K1404c: the record's pp_bytes at pp (the
   cut), the live block (pod, len) writable (Tac_b1.b1_hb), the pod and pp blocks apart (Tac_b1.b1_sep), mem_inv.
   The evt ends at 0x1407c `jal malloc`; one step takes it to malloc's entry with ra = 0x14080 and the request
   a0 = 3 cap + 3 <= 30, and Tac_b1.b1_malloc_call runs the call from hb = [(pod, len); (pp, 19744)]. Its kept-bytes
   clauses carry the frame cells sp + 0x50, sp + 0x58 and both blocks' bytes to the cut. The run writes only the pod
   block, which keeps FR (Tac_b1.b1_fr_hb). No function is proved here. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 SegFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor.
Import ListNotations.
Open Scope Z_scope.

(* ---- The run: K1404c to malloc's entry with ra = 0x14080 ---- *)
Definition m02_post (sp gp tp s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (inp : list byte) (cap pod : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 HEAD_CHECK) sp gp tp t0' t1' t2' (Z_to_bv 64 (3 * cap)) (Z_to_bv 64 pod)
                  (Z_to_bv 64 (OUT_LEN cap)) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 cap) s3 (Z_to_bv 64 (OUT_LEN cap)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x1643c) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pod (buf (head_rec inp)) /\
    Frame.munch [(pod, pod + head_len inp)] m m' /\ Frame.wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma m02_evt : headamp_dup_pod_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (cap pp pod : Z),
    a0 = Z_to_bv 64 pod -> pod <> 0 ->
    s4 = Z_to_bv 64 (head_len inp) -> s5 = Z_to_bv 64 pp -> s6 = Z_to_bv 64 cap -> 0 <= cap <= 9 ->
    bytes_at rsegs m pp (pp_bytes (head_rec inp)) ->
    rw_cells rsegs m pod [CB (Z.to_nat (head_len inp)) junk] ->
    (pod + head_len inp <= pp \/ pp + POD_PROPS <= pod) ->
    mem_inv rsegs m ->
    evt rsegs (m02_post sp gp tp s3 s5 s6 s7 s8 s9 s10 s11 F fc m inp cap pod)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_DUP_POD) fc None m (seg_rom rsegs)).
Proof.
  intros DUPP ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m inp junk cap pp pod E10 Hpod0 E20 E21 E22 Hcap HPP HRW HSEP HMI.
  eapply evt_cut.
  - eapply DUPP with (inp := inp) (junk := junk) (cap := cap) (pp := pp) (pod := pod); eassumption.
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
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis DUPP : headamp_dup_pod_contract.

Lemma seg_M02 : S_M02 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF DUPP.
  unfold S_M02. intros H1 g c (pp & pod & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP
    (H10 & Hpod0 & Hpod16 & H20 & H21 & H22 & H23 & H24 & HC50 & HC58 & HPP).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  assert (Hinpod : In (pod, g_len g) (hb_pod g pod pp)) by (left; reflexivity).
  assert (Hinpp : In (pp, POD_PROPS) (hb_pod g pod pp)) by (right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g (hb_pod g pod pp) pod (g_len g) L A regs mem md HFR HP Hinpod)
    as (STb & Hpod4096 & Hpodc).
  destruct (b1_hb B APIf ra empty FF g (hb_pod g pod pp) pp POD_PROPS L A regs mem md HFR HP Hinpp)
    as (_ & Hpp4096 & Hppc).
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI0 & HRL & HM & _).
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSKc & HS47c & _).
  pose proof alloc_ceiling_value as HAC.
  pose proof (sf_len_bound (g_rest g) : 8 <= g_len g <= 5440) as Hlb.
  pose proof (sf_cap_rng (g_in g) : 0 <= g_cap g <= 9) as Hcap.
  pose proof (sf_pp_len (g_rest g) : Z.of_nat (length (pp_bytes (g_rec g))) = POD_PROPS) as Hppl.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  (* The pod block's cells on the normalized memory. *)
  destruct (sl_rw_of_stk _ _ _ pod (Z.to_nat (g_len g)) STb ltac:(lia) ltac:(lia)) as (junk & HRW).
  (* The pod and pp blocks are apart. *)
  assert (HSEP : pod + g_len g <= pp \/ pp + POD_PROPS <= pod).
  { assert (HD : fst (pod, g_len g) + snd (pod, g_len g) <= fst (pp, POD_PROPS) \/
                 fst (pp, POD_PROPS) + snd (pp, POD_PROPS) <= fst (pod, g_len g)).
    { first [ exact (b1_sep B APIf ra empty g [] (pod, g_len g) [(pp, POD_PROPS)] L A regs mem md (pp, POD_PROPS)
                       HFR HP ltac:(cbn [app]; left; reflexivity))
            | exact (b1_sep B APIf ra empty FF g [] (pod, g_len g) [(pp, POD_PROPS)] L A regs mem md
                       (pp, POD_PROPS) HFR HP ltac:(cbn [app]; left; reflexivity)) ]. }
    cbn [fst snd] in HD. exact HD. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x1404c) mem md
            (m02_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (YK11.getr regs 19)
               (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24)
               (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27)
               (@fp_regs fx') (@fp_csr fx') (normalize rsegs mem) (g_rest g) (g_cap g) pod) _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply (m02_evt DUPP) with (junk := junk) (pp := pp).
    + exact H10.
    + exact Hpod0.
    + exact H20.
    + exact H21.
    + exact H22.
    + exact Hcap.
    + exact (bytes_at_normalize rsegs mem _ _ HMI HPP).
    + exact HRW.
    + exact HSEP.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0 & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' &
                    HE & HB & MU & WM & MIv).
    injection HE; intros; subst.
    change (head_len (g_rest g)) with (g_len g) in MU.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    pose proof (b1_out _ m' _ _ Hrel HB) as HB'.
    (* The frame cells and the pp block: apart from the pod block, so untouched by the run. *)
    assert (HC50' : bytes_at rsegs m' (g_S g - 560 + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF)))).
    { apply (b1_keep _ mem _ m' _ _ HMI MU Hrel); [|exact HC50].
      rewrite length_le8. cbn [Frame.disjoint_from]. split; [lia | exact I]. }
    assert (HC58' : bytes_at rsegs m' (g_S g - 560 + 0x58) (le8 (Z_to_bv 64 pp))).
    { apply (b1_keep _ mem _ m' _ _ HMI MU Hrel); [|exact HC58].
      rewrite length_le8. cbn [Frame.disjoint_from]. split; [lia | exact I]. }
    assert (HPP' : bytes_at rsegs m' pp (pp_bytes (g_rec g))).
    { apply (b1_keep _ mem _ m' _ _ HMI MU Hrel); [|exact HPP].
      rewrite Hppl. cbn [Frame.disjoint_from]. split; [lia | exact I]. }
    assert (HFR' : FR B APIf ra empty g (hb_pod g pod pp) L A regs' m' md).
    { apply (b1_fr_hb B APIf ra empty FF g (hb_pod g pod pp) pod (g_len g) L A regs mem md regs' m' HFR HP Hinpod).
      - intros a Ha Hs Hb. apply MU'.
        rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
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
       | rewrite E1; unfold HEAD_CHECK; vm_compute; reflexivity | exact E10' | unfold OUT_LEN; lia |].
    intros L' A' regs'' mem'' md' res HF2 HP2 RP H10' Hres0 Hres16 HKF HKB.
    rewrite E1. apply H1. exists pp, pod, res, fx', L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF2|]. split; [exact HP2|].
    unfold rg.
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
    split; [etransitivity; [exact (RP 24 ltac:(unfold callee_saved; lia))|];
            rewrite (sl_getr_eqv _ _ _ Hx); exact H24|].
    split.
    { apply (b1_ba_mbyte m'); [exact HC50'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HC58'|]. intros i Hi. rewrite length_le8 in Hi.
      apply HKF. unfold fsp, SLOT_FRAME. lia. }
    split.
    { apply (b1_ba_mbyte m'); [exact HPP'|].
      intros i Hi. rewrite Hppl in Hi. apply (HKB pp POD_PROPS i Hinpp). exact Hi. }
    apply (b1_ba_mbyte m'); [exact HB'|].
    intros i Hi. apply (HKB pod (g_len g) i Hinpod). exact Hi.
Qed.

End M02.
