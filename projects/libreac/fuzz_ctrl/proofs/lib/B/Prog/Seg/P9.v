(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 114 of its 134 lines of code are new or changed and 376 lines of the source are left out. *)
(* Segment P9 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81dbc, 0x81dd0], 6
   instructions, cut Inv_B81dbc (v1.9 pc 0x81dbc) -> cut Inv_B81dd4 (v1.9 pc 0x81dd4) (plan-asan-ubsan.md
   section 2, row P9).  rule 24: no function proved (a slot segment).
     0x81dbc li s2,-1; 0x81dc0 beq a0,s2,0x81dc8   taken: a0 = -1, the result of the first reac_ports_parse call
                                                    (the fall-through 0x81dc4 j 0x82fa4 is not reached);
     0x81dc8 li a0,0; 0x81dcc li a1,0; 0x81dd0 jal reac_ports_parse@0x883d0.
   With p = q = 0 the callee parses nothing (ports_ok 0 0 bs = false): it returns -1, keeps s2 and the other
   callee-saved registers, and writes only its 16-byte stack frame [sp - 16, sp) (reac_ports_parse_c.v, a Section
   hypothesis, never its code).  The range has no instrumented shadow check and no UBSan trap.
   p9_evt is the Lib-level run; seg_P9 runs it on the normalized memory and moves FRA / ENT across the frame by
   Tac_bp7.bp7_call; Tac_bp7.bp7_keep carries the rest of the exit cut (our[], PRO, s8 = fr + 3040, the code byte's
   and the kind-name table's addressable bytes, PL0).  v1.9.0 against the patched image: the pcs move +0x88 and
   the code pointer is s8 (patched s11). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ports_parse_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the call with null arguments: ports_ok is false ---- *)
Lemma p9_nok : forall bs, ports_ok 0 0 bs = false.
Proof. intros bs. reflexivity. Qed.

(* ---- the run: li s2,-1; beq (taken); li a0,0; li a1,0; jal reac_ports_parse ---- *)
Lemma p9_evt : reac_ports_parse_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
    sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (-1) -> 16 <= S < 2 ^ 64 ->
    stk rsegs m (S - 16) S ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81dd4) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (-1) /\ getr R 18 = Z_to_bv 64 (-1) /\
         munch [(S - 16, S)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S - 16) S)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81dbc) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S -> -> HS HST.
  pose proof PP as HC. unfold reac_ports_parse_contract, REAC_PORTS_PARSE in HC.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  step. (* 0x81dbc li s2,-1 *)
  step. (* 0x81dc0 beq a0,s2,0x81dc8 *)
  if_true.
  step. step. (* 0x81dc8 li a0,0; 0x81dcc li a1,0 *)
  step. (* 0x81dd0 jal reac_ports_parse *)
  eapply evt_cut.
  { eapply HC with (p := 0) (q := 0) (lo := S - 16) (bs := @nil byte).
    all: rewrite ?EU.
    all: try reflexivity.
    all: try assumption.
    all: try (intros HH; exfalso; apply HH; reflexivity).
    all: try (unfold REAC_PORTS_PARSE_FRAME; lia).
    all: lia. }
  intros ms' PO. unfold reac_ports_parse_post in PO.
  destruct PO as (t0' & t1' & t2' & t3' & t4' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' &
                  E & WM & _ & ST' & HP).
  subst ms'. rewrite p9_nok in HP |- *. rewrite EU in HP, ST'. unfold REAC_PORTS_PARSE_FRAME in HP.
  replace (ret_pc (Z_to_bv 64 0x81dd4)) with (Z_to_bv 64 0x81dd4)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 12 (split; [reflexivity|]).
  split; [exact HP|]. split; [exact WM | exact ST'].
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

Section P9.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee reac_ports_parse (PARSE@0x81dd0), taken on its lib/B contract, never on its code. *)
Hypothesis PP : reac_ports_parse_contract.

Lemma seg_P9 : Hcut B APIf ra (Inv_B81dd4 B APIf ra) -> Hcut B APIf ra (Inv_B81dbc B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & Ha0 & HPRO & H24 & HADc & HADk & HPL).
  subst c.
  destruct (bp7_fra B APIf ra g fr regs mem md HFRA)
    as (A & Hr9 & Hsplo & HspA & HA448 & HfrA & Hspm & Happ & Hfr0 & Hfrm & Hplace).
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (_ & Hstkw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm' & Haspz & _).
  rewrite Haspz in Hsplo, HspA, Hspm, Hplace, Hstkw.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  unfold HIGHMEM_BEG, APPMEM_END in Hsplo, HA448.
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  destruct (stk_split rsegs mem (sp - FN_STACK) (sp - 16) sp Hstkw ltac:(lia)) as (_ & HSTKw).
  pose proof (bp_stk_rel mem (normalize rsegs mem) (sp - 16) sp HR0 ltac:(lia) HSTKw) as HSTKwn.
  (* the write set: the callee's frame *)
  assert (HIN : bp7_in fr (AC.aspZ regs) 16 [(sp - 16, sp)]).
  { intros x Hx. cbn [LF.outside] in Hx. left. rewrite Haspz. lia. }
  assert (HDJ : rt_disjoint [(sp - 16, sp)]).
  { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN.
    cbn [disjoint_from]. repeat split; first [exact I | lia]. }
  unfold a0v, rg in Ha0.
  rewrite SEGS.
  apply (bp7_call B APIf ra empty FF g fr regs mem md 0x81dbc 0x81dd4 16 [(sp - 16, sp)]
    (fun R m0' => getr R 10 = Z_to_bv 64 (-1) /\ getr R 18 = Z_to_bv 64 (-1) /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25)
    (Post B APIf ra g) HFRA HENT ltac:(lia) HIN HDJ).
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p9_evt PP) with (S := sp).
      all: try assumption.
      all: lia.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P23' & P24' & P25' & P26' & P10' & P18' &
                  MUq & WMq & STq).
      exists R, (Z_to_bv 64 0x81dd4), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P26'|].
      split; [exact MUq|]. split; [exact WMq|].
      split; [intros x Hx; cbn [LF.outside] in Hx; apply (bp7_rd_stk m' (sp - 16) sp x STq); lia|].
      split; [exact P10'|]. split; [exact P18'|]. split; [exact P23'|]. split; [exact P24' | exact P25'].
  - intros R m0' regs' mem' md' (Q10 & Q18 & Q23 & Q24 & Q25) Hreg E9 HRel HFRA' HENT' MU WM.
    destruct (bp7_keep B APIf ra g fr regs regs' mem mem' md 16 [(sp - 16, sp)] HFRA ltac:(lia) HIN MU E9
                ltac:(rewrite Hreg; exact Q23) ltac:(rewrite Hreg; exact Q25))
      as (KAD & KSP & KOUR & KPRO & KPL0).
    rewrite <- SEGS. apply Hexit. exists regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact (KOUR HOUR)|].
    split; [unfold a0v, rg; rewrite Hreg; exact Q10|].
    split; [unfold rg; rewrite Hreg; exact Q18|].
    split; [exact (KPRO HPRO)|].
    split; [unfold rg in *; rewrite Hreg, Q24; exact H24|].
    split; [exact (KAD _ _ HADc)|].
    split; [exact (KAD _ _ HADk) | exact (KPL0 HPL)].
Qed.

End P9.
