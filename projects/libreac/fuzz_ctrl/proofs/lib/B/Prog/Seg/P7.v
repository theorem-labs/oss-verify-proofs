(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 193 of its 213 lines of code are new or changed and 376 lines of the source are left out. *)
(* Segment P7 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81d80, 0x81da4], 9
   instructions, cut Inv_B81d80 (v1.9 pc 0x81d80) -> cut Inv_B81da8 (v1.9 pc 0x81da8) (plan-asan-ubsan.md
   section 2, row P7).  rule 24: no function proved (a slot segment).
     0x81d80 li s2,-1; 0x81d84 beq a0,s2,0x81d8c   taken: a0 = -1, the reac_ctrl_identity_reply result (the
                                                    fall-through 0x81d88 j 0x82fa4 is not reached);
     0x81d8c ld a0,208(s1); li a1,0; li a2,0; ld a3,88(s1); ld a4,80(s1); ld a5,72(s1)
                                                    the four spilled record pointers, a1 = a2 = 0;
     0x81da4 jal reac_ctrl_identity_fragment@0x859e4.
   With a1 = 0 the callee refuses (fg_class = FgRefuse): it returns -1, keeps s2 and the other callee-saved
   registers, and writes only its stack window [sp - 4672, sp) (reac_ctrl_identity_fragment_c.v, a Section
   hypothesis, never its code).  The range has no instrumented shadow check and no UBSan trap.
   p7_evt is the Lib-level run; seg_P7 runs it on the normalized memory (the callee needs mem_inv) and moves FRA /
   ENT across the window by Tac_bp7.bp7_call; Tac_bp7.bp7_keep carries the rest of the exit cut (our[], PRO, the
   spill [A + 64], the code byte's and the kind-name table's addressable bytes, PL0), which the window misses.
   v1.9.0 against the patched image: the pcs move +0x88, the four loads read [A + 208] / [A + 88] / [A + 80] /
   [A + 72] (patched [A + 240] / [A + 96] / [A + 88] / [A + 80]) and the code pointer is s8 (patched s11). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the refused call: with fr = 0 the class is FgRefuse ---- *)
Lemma p7_refuse0 : forall f pa pp pn len st g, fg_class f 0 pa pp pn len st g = FgRefuse.
Proof. intros. unfold fg_class. rewrite (Z.eqb_refl 0), Bool.orb_true_r. reflexivity. Qed.

(* ---- the run: li s2,-1; beq (taken); the four loads and two li; jal reac_ctrl_identity_fragment ---- *)
Lemma p7_evt : reac_ctrl_identity_fragment_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Ab f pa pp pn : Z),
    sp = Z_to_bv 64 S -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 (-1) ->
    0 <= f < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    0 <= Ab -> Ab + 248 <= 2 ^ 64 -> 0 <= S < 2 ^ 64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_FRAGMENT_K -> S <= APPMEM_END ->
    ro_cells rsegs m (Ab + 208) [C8 (Z_to_bv 64 f)] ->
    ro_cells rsegs m (Ab + 88) [C8 (Z_to_bv 64 pa)] ->
    ro_cells rsegs m (Ab + 80) [C8 (Z_to_bv 64 pp)] ->
    ro_cells rsegs m (Ab + 72) [C8 (Z_to_bv 64 pn)] ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_FRAGMENT_K) S ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81da8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (-1) /\ getr R 18 = Z_to_bv 64 (-1) /\
         munch [(S - 4672, S)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S - 4672) S)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d80) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S Ab f pa pp pn -> -> -> Hf Hpa Hpp Hpn HA0 HA64 HS HSal Hlo Hhi RO208 RO88 RO80 RO72 HST HMI HAC HSW
    HRB HRM HGC HC254 HC255.
  pose proof FRAG as HC. unfold reac_ctrl_identity_fragment_contract, REAC_CTRL_IDENTITY_FRAGMENT in HC.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; exact HS).
  step. (* 0x81d80 li s2,-1 *)
  step. (* 0x81d84 beq a0,s2,0x81d8c *)
  if_true.
  step. (* 0x81d8c ld a0,208(s1) *)
  step. step. (* li a1,0; li a2,0 *)
  step. step. step. (* ld a3,88(s1); ld a4,80(s1); ld a5,72(s1) *)
  step. (* 0x81da4 jal reac_ctrl_identity_fragment *)
  eapply evt_cut.
  { eapply HC with (f := f) (fr := 0) (len := 0) (pa := pa) (pp := pp) (pn := pn)
      (st := repeat (Z_to_bv 8 0) 72) (g := repeat (Z_to_bv 8 0) 50).
    all: rewrite ?EU.
    all: try reflexivity.
    all: try assumption.
    all: try (intros _ HH; exfalso; apply HH; reflexivity).
    all: try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI' & ST' & _ & _ & _).
  subst ms'.
  rewrite p7_refuse0 in MU |- *. cbn [fg_fp] in MU. change (fg_ret FgRefuse) with (-1).
  rewrite EU in MU, ST'. unfold REAC_CTRL_IDENTITY_FRAGMENT_K in MU, ST'.
  replace (ret_pc (Z_to_bv 64 0x81da8)) with (Z_to_bv 64 0x81da8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 12 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_bp Tac_bp7.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module KNC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_kind_name_c.
Open Scope Z_scope.

(* The one place this file takes the generated runtime cell list asan_cf_cells apart (a Theorem Labs lane 15:32Z): the GOT
   slot of the flags record and its bytes 240 .. 260. *)
Lemma p7_cf : forall m, asan_cf_cells m ->
  bytes_at rsegs m RT_GOT_CF (le8 (Z_to_bv 64 RT_CF)) /\
  bytes_at rsegs m (RT_CF + 240) (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0]).
Proof. intros m (H1 & _ & _ & _ & _ & _ & H7 & _). exact (conj H1 H7). Qed.

Section P7.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee reac_ctrl_identity_fragment (FRAG@0x81da4), taken on its lib/B contract, never on its code. *)
Hypothesis FRAG : reac_ctrl_identity_fragment_contract.

Lemma seg_P7 : Hcut B APIf ra (Inv_B81da8 B APIf ra) -> Hcut B APIf ra (Inv_B81d80 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & Ha0 & HPRO &
                    (f & H208) & (pa & H88) & (pp & H80) & (pn & H72) & H64 & H24 & HADc & HADk & HPL).
  subst c.
  destruct (bp7_fra B APIf ra g fr regs mem md HFRA)
    as (A & Hr9 & Hsplo & HspA & HA448 & HfrA & Hspm & Happ & Hfr0 & Hfrm & Hplace).
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (_ & Hstkw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm' & Haspz & _).
  rewrite Haspz in Hsplo, HspA, Hspm, Hplace, Hstkw.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HK : REAC_CTRL_IDENTITY_FRAGMENT_K = 4672) by reflexivity.
  assert (HGT : AC.GT <= fr) by exact (proj1 (fra_app B APIf ra g fr [] regs mem md HFRA)).
  unfold AC.GT, HIGHMEM_BEG, APPMEM_END in HGT, Hsplo, HA448.
  (* the four spills read by the loads, at FRA's spill base A *)
  assert (SPA : forall off v, 0 <= off <= 440 -> spill regs mem off v -> q64 mem (A + off) v).
  { intros off v Hoff (A1 & HA1 & Hq).
    assert (HA1e : A1 = A) by (apply (bp_spill_A regs mem off v A A1 HA1 Hq Hr9); lia).
    subst A1. exact Hq. }
  pose proof (SPA 208 f ltac:(lia) H208) as Hq208.
  pose proof (SPA 88 pa ltac:(lia) H88) as Hq88.
  pose proof (SPA 80 pp ltac:(lia) H80) as Hq80.
  pose proof (SPA 72 pn ltac:(lia) H72) as Hq72.
  (* the runtime's cells the callee reads (P6's p6 derivation) *)
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL0.
  destruct (p7_cf mem (AsanRTInv.RT_cf_cells _ _ _ HRT)) as (HGOTCF & HCF240).
  assert (HRBc : bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)))
    by (apply (AsanRTInv.real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity).
  assert (HRMc : bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)))
    by (apply (AsanRTInv.real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity).
  assert (HC254 : bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1]).
  { pose proof (bp_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HC255 : bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1]).
  { pose proof (bp_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  assert (TB0 : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  destruct (stk_split rsegs mem (sp - FN_STACK) (sp - 4672) sp Hstkw ltac:(lia)) as (_ & HSTKw).
  pose proof (bp_stk_rel mem (normalize rsegs mem) (sp - 4672) sp HR0 ltac:(lia) HSTKw) as HSTKwn.
  pose proof (u64_range (Z_to_bv 64 f)) as Hf0r. pose proof (u64_range (Z_to_bv 64 pa)) as Hpa0r.
  pose proof (u64_range (Z_to_bv 64 pp)) as Hpp0r. pose proof (u64_range (Z_to_bv 64 pn)) as Hpn0r.
  set (f0 := bv_unsigned (Z_to_bv 64 f)).
  set (pa0 := bv_unsigned (Z_to_bv 64 pa)).
  set (pp0 := bv_unsigned (Z_to_bv 64 pp)).
  set (pn0 := bv_unsigned (Z_to_bv 64 pn)).
  assert (RO208 : ro_cells rsegs (normalize rsegs mem) (A + 208) [C8 (Z_to_bv 64 f0)])
    by (subst f0; rewrite MState.Z_to_bv_bv_unsigned; apply bp_ro8; apply TB0; exact Hq208).
  assert (RO88 : ro_cells rsegs (normalize rsegs mem) (A + 88) [C8 (Z_to_bv 64 pa0)])
    by (subst pa0; rewrite MState.Z_to_bv_bv_unsigned; apply bp_ro8; apply TB0; exact Hq88).
  assert (RO80 : ro_cells rsegs (normalize rsegs mem) (A + 80) [C8 (Z_to_bv 64 pp0)])
    by (subst pp0; rewrite MState.Z_to_bv_bv_unsigned; apply bp_ro8; apply TB0; exact Hq80).
  assert (RO72 : ro_cells rsegs (normalize rsegs mem) (A + 72) [C8 (Z_to_bv 64 pn0)])
    by (subst pn0; rewrite MState.Z_to_bv_bv_unsigned; apply bp_ro8; apply TB0; exact Hq72).
  (* the write set: the callee window *)
  assert (HIN : bp7_in fr (AC.aspZ regs) 4672 [(sp - 4672, sp)]).
  { intros x Hx. cbn [LF.outside] in Hx. left. rewrite Haspz. lia. }
  assert (HDJ : rt_disjoint [(sp - 4672, sp)]).
  { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN.
    cbn [disjoint_from]. repeat split; first [exact I | lia]. }
  (* the callee's memory premises on the normalized memory *)
  pose proof (mem_inv_normalize rsegs mem) as HMIn.
  pose proof (bp_cells_rel mem (normalize rsegs mem) HR0 HAC0) as HACn.
  pose proof (bp_srw_rel mem (normalize rsegs mem) HR0 HSW0) as HSWn.
  pose proof (TB0 _ _ HRBc) as HRBn. pose proof (TB0 _ _ HRMc) as HRMn.
  assert (HGCn : bytes_at rsegs (normalize rsegs mem) GOT_CF (le8 (wa CF))) by exact (TB0 _ _ HGOTCF).
  pose proof (TB0 _ _ HC254) as HC254n. pose proof (TB0 _ _ HC255) as HC255n.
  unfold a0v, rg in Ha0, Hr9.
  rewrite SEGS.
  apply (bp7_call B APIf ra empty FF g fr regs mem md 0x81d80 0x81da8 4672 [(sp - 4672, sp)]
    (fun R m0' => getr R 10 = Z_to_bv 64 (-1) /\ getr R 18 = Z_to_bv 64 (-1) /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25)
    (Post B APIf ra g) HFRA HENT ltac:(lia) HIN HDJ).
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p7_evt FRAG) with (S := sp) (Ab := A) (f := f0) (pa := pa0) (pp := pp0) (pn := pn0).
      all: rewrite ?HK.
      all: try assumption.
      all: try (apply u64_range).
      all: try lia.
      all: unfold HIGHMEM_BEG, APPMEM_END; lia.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P23' & P24' & P25' & P26' & P10' & P18' &
                  MUq & WMq & STq).
      exists R, (Z_to_bv 64 0x81da8), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P26'|].
      split; [exact MUq|]. split; [exact WMq|].
      split; [intros x Hx; cbn [LF.outside] in Hx; apply (bp7_rd_stk m' (sp - 4672) sp x STq); lia|].
      split; [exact P10'|]. split; [exact P18'|]. split; [exact P23'|]. split; [exact P24' | exact P25'].
  - intros R m0' regs' mem' md' (Q10 & Q18 & Q23 & Q24 & Q25) Hreg E9 HRel HFRA' HENT' MU WM.
    destruct (bp7_keep B APIf ra g fr regs regs' mem mem' md 4672 [(sp - 4672, sp)] HFRA ltac:(lia) HIN MU E9
                ltac:(rewrite Hreg; exact Q23) ltac:(rewrite Hreg; exact Q25))
      as (KAD & KSP & KOUR & KPRO & KPL0).
    rewrite <- SEGS. apply Hexit. exists regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact (KOUR HOUR)|].
    split; [unfold a0v, rg; rewrite Hreg; exact Q10|].
    split; [exact (KPRO HPRO)|].
    split; [unfold rg; rewrite Hreg; exact Q18|].
    split; [exact (KSP 64 _ ltac:(lia) H64)|].
    split; [unfold rg in *; rewrite Hreg, Q24; exact H24|].
    split; [exact (KAD _ _ HADc)|].
    split; [exact (KAD _ _ HADk) | exact (KPL0 HPL)].
Qed.

End P7.
