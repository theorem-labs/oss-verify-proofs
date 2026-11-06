(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names and numbers changed; 147 of its 169 lines of code are new or changed and 374 lines of the source are left out. *)
(* Segment P10 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81dd4, 0x81de4], 4
   instructions, cut Inv_B81dd4 (v1.9 pc 0x81dd4) -> cut Inv_B81de8 (v1.9 pc 0x81de8) (plan-asan-ubsan.md
   section 2, row P10).  rule 24: no function proved (a slot segment).
     0x81dd4 beq a0,s2,0x81ddc   taken: a0 = -1, the result of the second reac_ports_parse call, and s2 = -1 (the
                                 fall-through 0x81dd8 j 0x82fa4 is not reached);
     0x81ddc li a0,0; 0x81de0 mv a1,s8 (s8 = fr + 3040, the code byte); 0x81de4 jal reac_ports_unknown@0x88628.
   With p = 0 the callee finds no port record (pu_ok 0 bs = false): it returns -1, writes 0 to the code byte at
   c = fr + 3040, keeps the callee-saved registers, and writes only its 16-byte stack frame [sp - 16, sp) and that
   byte (reac_ports_unknown_c.v, a Section hypothesis, never its code).  The range has no instrumented shadow check
   and no UBSan trap.
   p10_evt is the Lib-level run; seg_P10 runs it on the normalized memory and moves FRA / ENT across the write set
   by Tac_bp7.bp7_call; Tac_bp7.bp7_keep carries the rest of the exit cut (our[], PRO, the code byte's and the
   kind-name table's addressable bytes, PL0); the exit's b8 (fr + 3040) 0 is the callee's post.  v1.9.0 against
   the patched image: the pcs move +0x88, the code byte is fr + 3040 through s8 (patched fr + 2960 through s11). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ports_unknown_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the call with a null port record: pu_ok is false ---- *)
Lemma p10_nok : forall bs, pu_ok 0 bs = false.
Proof. intros bs. reflexivity. Qed.

(* ---- the run: beq (taken); li a0,0; mv a1,s8; jal reac_ports_unknown ---- *)
Lemma p10_evt : reac_ports_unknown_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Cc : Z),
    sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (-1) -> s2 = Z_to_bv 64 (-1) -> s8 = Z_to_bv 64 Cc ->
    16 <= S < 2 ^ 64 -> 0 < Cc < 2 ^ 64 ->
    stk rsegs m (S - 16) S -> wr_at rsegs m Cc 1 -> (Cc + 1 <= S - 16 \/ S <= Cc) ->
    asan_cells m -> shadow_rw m -> addressable m Cc 1 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(S - 16, S); (Cc, Cc + 1)] x) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81de8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (-1) /\
         munch [(S - 16, S); (Cc, Cc + 1)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S - 16) S /\
         bytes_at rsegs m' Cc [Z_to_bv 8 0])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81dd4) fc None m (seg_rom rsegs)).
Proof.
  intros PU ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S Cc -> -> -> -> HS HC0 HST HWR HSEP HAC HSW HAD HOUT.
  pose proof PU as HC. unfold reac_ports_unknown_contract, REAC_PORTS_UNKNOWN in HC.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 Cc) = Cc) by (apply MState.unsigned_lit; lia).
  assert (ECz : (Cc =? 0) = false) by (apply Z.eqb_neq; lia).
  step. (* 0x81dd4 beq a0,s2,0x81ddc *)
  if_true.
  step. (* 0x81ddc li a0,0 *)
  step. (* 0x81de0 mv a1,s8 *)
  step. (* 0x81de4 jal reac_ports_unknown *)
  eapply evt_cut.
  { eapply HC with (p := 0) (c := Cc) (lo := S - 16) (bs := @nil byte).
    all: unfold reac_ports_unknown_W, REAC_PORTS_UNKNOWN_FRAME.
    all: rewrite ?EU, ?EC, ?ECz.
    all: try reflexivity.
    all: try assumption.
    all: try (intros HH; exfalso; apply HH; reflexivity).
    all: try (intros _; split; [assumption | split; [intros HH; exfalso; apply HH; reflexivity | lia]]).
    all: try (intros _; assumption).
    all: lia. }
  intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & m' & E & MU & WM & ST' & _ & HB).
  subst ms'.
  unfold reac_ports_unknown_W, REAC_PORTS_UNKNOWN_FRAME in MU. rewrite EU, ECz in MU. rewrite EU in ST'.
  pose proof (HB ltac:(lia)) as HB0. rewrite p10_nok in HB0.
  replace (ret_pc (Z_to_bv 64 0x81de8)) with (Z_to_bv 64 0x81de8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 11 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM|]. split; [exact ST' | exact HB0].
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

Section P10.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee reac_ports_unknown (UNKNOWN@0x81de4), taken on its lib/B contract, never on its code. *)
Hypothesis PU : reac_ports_unknown_contract.

Lemma seg_P10 : Hcut B APIf ra (Inv_B81de8 B APIf ra) -> Hcut B APIf ra (Inv_B81dd4 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & Ha0 & H18 & HPRO & H24 & HADc & HADk &
                    HPL).
  subst c.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct (bp7_fra B APIf ra g fr regs mem md HFRA)
    as (A & Hr9 & Hsplo & HspA & HA448 & HfrA & Hspm & Happ & Hfr0 & Hfrm & Hplace).
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (_ & Hstkw).
  pose proof (bp_frame_stk B APIf ra g fr [] regs mem md HFRA) as Hfstk.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm' & Haspz & _).
  rewrite Haspz in Hsplo, HspA, Hspm, Hplace, Hstkw.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (Hsep : fr + 3136 <= sp - 16 \/ sp <= fr) by (apply Hplace; lia).
  assert (HGT : AC.GT <= fr) by exact (proj1 (fra_app B APIf ra g fr [] regs mem md HFRA)).
  assert (Hcapp : app_mem (fr + 3040)) by (apply Happ; lia).
  unfold AC.GT, HIGHMEM_BEG, APPMEM_END in HGT, Hsplo, HA448.
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0. pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  destruct (stk_split rsegs mem (sp - FN_STACK) (sp - 16) sp Hstkw ltac:(lia)) as (_ & HSTKw).
  pose proof (bp_stk_rel mem (normalize rsegs mem) (sp - 16) sp HR0 ltac:(lia) HSTKw) as HSTKwn.
  (* the code byte: one writable frame byte, addressable (the entry cut) *)
  destruct (stk_split rsegs mem fr (fr + 3040) (fr + 3136) Hfstk ltac:(lia)) as (_ & Hs1).
  destruct (stk_split rsegs mem (fr + 3040) (fr + 3041) (fr + 3136) Hs1 ltac:(lia)) as (Hcb & _).
  pose proof (bp_stk_rel mem (normalize rsegs mem) (fr + 3040) (fr + 3041) HR0 ltac:(lia) Hcb) as Hcbn.
  pose proof (bp_wr_stk _ _ _ Hcbn) as HWRn. replace (fr + 3041 - (fr + 3040)) with 1 in HWRn by lia.
  pose proof (bp_addr_rel mem (normalize rsegs mem) _ _ HR0 HADc) as HADcn.
  pose proof (bp_cells_rel mem (normalize rsegs mem) HR0 HAC0) as HACn.
  pose proof (bp_srw_rel mem (normalize rsegs mem) HR0 HSW0) as HSWn.
  (* the write set: the callee's frame and the code byte *)
  assert (HOUTC : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            LF.outside [(sp - 16, sp); (fr + 3040, fr + 3040 + 1)] x).
  { intros x Hx. cbn [LF.outside].
    unfold in_shadow, GOT_CELL_K, CELL_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hcapp.
    split; [lia|]. split; [lia | exact I]. }
  assert (HIN : bp7_in fr (AC.aspZ regs) 16 [(sp - 16, sp); (fr + 3040, fr + 3040 + 1)]).
  { intros x Hx. cbn [LF.outside] in Hx. rewrite Haspz. lia. }
  assert (HDJ : rt_disjoint [(sp - 16, sp); (fr + 3040, fr + 3040 + 1)]).
  { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN.
    cbn [disjoint_from]. repeat split; first [exact I | lia]. }
  unfold a0v, rg in Ha0, H18, H24.
  rewrite SEGS.
  apply (bp7_call B APIf ra empty FF g fr regs mem md 0x81dd4 0x81de8 16
    [(sp - 16, sp); (fr + 3040, fr + 3040 + 1)]
    (fun R m0' => getr R 10 = Z_to_bv 64 (-1) /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       bytes_at rsegs m0' (fr + 3040) [Z_to_bv 8 0])
    (Post B APIf ra g) HFRA HENT ltac:(lia) HIN HDJ).
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p10_evt PU) with (S := sp) (Cc := fr + 3040).
      all: try assumption.
      all: lia.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P23' & P24' & P25' & P26' & P10' &
                  MUq & WMq & STq & HBq).
      exists R, (Z_to_bv 64 0x81de8), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P26'|].
      split; [exact MUq|]. split; [exact WMq|].
      split.
      { intros x Hx. cbn [LF.outside] in Hx.
        destruct (Z_lt_le_dec x sp) as [Hx1|Hx1]; [destruct (Z_lt_le_dec x (sp - 16)) as [Hx2|Hx2]|].
        - apply (bp_ba_rd m' (fr + 3040) [Z_to_bv 8 0] x HBq). cbn [length Z.of_nat]. lia.
        - apply (bp7_rd_stk m' (sp - 16) sp x STq). lia.
        - apply (bp_ba_rd m' (fr + 3040) [Z_to_bv 8 0] x HBq). cbn [length Z.of_nat]. lia. }
      split; [exact P10'|]. split; [exact P23'|]. split; [exact P24'|]. split; [exact P25' | exact HBq].
  - intros R m0' regs' mem' md' (Q10 & Q23 & Q24 & Q25 & QB) Hreg E9 HRel HFRA' HENT' MU WM.
    destruct (bp7_keep B APIf ra g fr regs regs' mem mem' md 16 [(sp - 16, sp); (fr + 3040, fr + 3040 + 1)]
                HFRA ltac:(lia) HIN MU E9 ltac:(rewrite Hreg; exact Q23) ltac:(rewrite Hreg; exact Q25))
      as (KAD & KSP & KOUR & KPRO & KPL0).
    rewrite <- SEGS. apply Hexit. exists regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact (KOUR HOUR)|].
    split; [unfold a0v, rg; rewrite Hreg; exact Q10|].
    split; [exact (KPRO HPRO)|].
    split; [unfold b8; exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) QB)|].
    split; [split; [unfold rg; rewrite Hreg, Q24; exact H24 | exact (KAD _ _ HADc)]|].
    split; [exact (KAD _ _ HADk) | exact (KPL0 HPL)].
Qed.

End P10.
