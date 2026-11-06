(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_pool_config (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions): it proves a Theorem Labs lane's
   `tsup_pool_config_spec` (lib/B/Prog/sup_pool_config_c.v, a working branch 707acd856cb; the same text as at
   f490061c104) in the form of
   cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract
   listing up to each call, the runtime's rules at the runtime calls (__asan_stack_malloc_0, the snprintf wrapper,
   the frame's release by its flag byte), the callee contracts record_c, arg_s_c, rec_shape_of_c and answer_c at the
   program calls (through cl_callS_wide / cl_callS_na), the return through paj_ret_at, and apost_base at the end.

   It is the B re-walk of the A walk lib/A/Prog/sup_pool_config.v (a working branch c4f188792bb),
   whose B code differs: B calls record() and arg_s() where A inlined record() and called xstrdup, and B inlines
   arg_i, so this function owns arg_i's class-0 side-stack frame (64 bytes, b = frame + 32) and its snprintf. The
   frame code (prologue, realignment `andi sp,sp,-32`, __asan_stack_malloc_0, header and shadow f1 f1 f1 f1 | f8 f8 |
   f3 f3, b unpoisoned around the snprintf and the second arg_s, the release through the flag byte) is arg_i's ASan
   walk's (lib/A/Prog/arg_i.v, a working branch 12dc52bfe84) and answer_code's ASan walk's
   (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71); the B kit usage is socket_send's B walk
   (lib/B/Prog/socket_send.v, a working branch a470f91dbfb).

   Report and trap edges: none. The function has no `jal __asan_report_*`, no `unimp`, no UBSan handler call
   (capstone over the pin's .symtab, gen/traps.B.summary row `sup_pool_config 0`). Its branches: 0x8bf30 `beqz a2`
   on the use-after-return flag, read through the GOT word 0xa5fa8 at the record's const cell 0xb0c40 (= 1, lib/B/YF0m.v
   z4 (ANum 0xb0c40) 0x1, AR's const-cell law al_const; the executor decides it not taken); 0x8bf4c `bnez s2` and
   0x8c040 `beqz s2` on the side-stack frame (nonzero, __asan_stack_malloc_0's post; decided by the frame atom's
   fact), so the real-stack fallback 0x8bf50-0x8bf68 with its page probe and the real-stack release 0x8c074-0x8c090
   are not reached. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config.v, with its module paths and module names changed; 234 of its 315 lines of code are new or changed and 1983 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s10k.v, with its module paths and module names changed; 139 of its 175 lines of code are new or changed and 279 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the three short exits of segment A7 of reac_segconf_parse_file's
   walk (segment A7's proof, 2026-10-30), the first end-to-end use of the seed pf_a7_q.v:
     a7_fun : A7_S_FUN B                                                   (pf_a7_m.v)
     a7_clr : forall n, HA_TAIL B n -> forall f0, H_CLR (fx := f0) B n      (pf_pieces.v)
     a7_rs3 : forall n, HA_TAIL B n -> forall f0, H_RS3 (fx := f0) B n      (pf_pieces.v)
  The code (the unit's internal record, commit dfb49d6ad789,
  path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s):
     FUN 0x88064  mv s4, zero          (then TAIL 0x88068)
     CLR 0x880fc  mv s4, zero
     RS3 0x88100  ld s3, 0x98(s1)      (s3 = SH + 8, the spill slot of 0x87b90)
         0x88104  j 0x88068            (TAIL)
   Each exit seeds the state at its cut with pf_a7_q.v's a7_seed (bw = false: no region is writable, so the
   memory after the run is the memory before it), runs to TAIL with one plain run (PaLibF.v paj_run_to_sh, as
   cross_check_s3.v does; no inline check, no call) and applies H_TAIL at the ambient FP state at the next line's
   offset pf_next (p_s v) o, line number ln + 1, with the same d.
   What INV_TAIL asks beyond INV_CLR / INV_RS3 / INV_FUN, and where each piece comes from:
     - the measure length (skipn (pf_next s o) s) < n: pfA_facts.pf_next_skipn_lt with pf_mid's bound;
     - pf_lctx s (pf_next s o) (ln + 1) d: pf_mid's third conjunct, as it stands;
     - pf_st with cur (CLR / FUN: cur = None from pf_st0, pf_cur_ok _ None is True);
     - s3 = SH + 8 (19): RS3 / CLR from the load at 0x88100; FUN keeps it (INV_FUN's PF_RL);
     - s4 = pf_cur_ptr c cur (20): CLR / FUN set it to 0 = pf_cur_ptr c None; RS3 keeps cur';
     - s5 = t + pf_next s o (21) and s10 = ln + 1 (26): PF_RM, kept;
     - s2 = '#', s8 = c, s11 = SH and pf_fi's sp, gp, tp, s0, s1, s6: kept.
   The post pf_postm B v (cf, cur, nm) o ln is H_TAIL's post at that offset and line number, by unfolding.
   No Section hypothesis: the three runs call nothing. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_k pf_a7_m pf_a7_q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* membership in a concrete list whose wanted element is syntactically there *)
Local Ltac a7c_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* a run that writes nothing: no region of a7_ss _ false has a write window *)
Local Ltac a7c_awr :=
  unfold a7_ss, a7_regions; cbn [ss_mem];
  repeat (apply awr_ok_cons_ro; [unfold a7_saved_r, a7_slot_r, a7_sh_r, a7_buf_r; cbn [YP09.r_wlo YP09.r_whi]; lia|]);
  apply awr_ok_nil.
Local Ltac a7c_mem HF Hmem msx memx :=
  assert (Hmem : ms_mem msx = memx);
  [ apply functional_extensionality; intros x; unfold frame_of in HF; rewrite HF; [reflexivity|];
    intros (r & Hr & Ha); unfold a7_ss, a7_regions in Hr; cbn [ss_mem In] in Hr;
    destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    unfold a7_saved_r, a7_slot_r, a7_sh_r, a7_buf_r in Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia
  | ].
(* a register list whose every member the run kept, read from the cut's own list *)
Local Ltac a7c_kept KEEP SRC :=
  rewrite KEEP by a7c_in; eapply a5_rg_get; [exact SRC | cbn [PF_RL PF_RM a5_FI app]; a7c_in].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Section x.
Context {fx : YK11.FPState}.

(* TAIL from the state a short exit reaches: INV_TAIL at the next line's offset and line number *)
Lemma a7c_tail : forall n v pos lyc Sc Wc rX rX' memc mdc mdc' cf cur nm o ln d,
  H_TAIL B n ->
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn (pf_next (p_s v) o) (p_s v))) ->
  pf_rg rX' (a5_FI B v) ->
  pf_rg rX' (PF_RL v pos ++ PF_RM v o ln ++ [(20, pf_cur_ptr (p_c v) cur)]) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_TAIL) rX' memc mdc') (pf_postm B v (cf, cur, nm) o ln).
Proof.
intros n v pos lyc Sc Wc rX rX' memc mdc mdc' cf cur nm o ln d HT HB HJ HMID HST HFI HRG.
destruct HB as (HCX & (_ & Hly & Hfs & Hperm & Hsaved & Hflag & Hfrm & _) & HOBJ & HSL & HFSH).
destruct HMID as (Ho & Hlen & Hlctx).
unfold pf_postm.
apply (HT v pos lyc Sc Wc rX' memc mdc' cf cur nm (pf_next (p_s v) o) (ln + 1) d).
unfold INV_TAIL.
split; [|split; [exact Hlctx|split; [|split; [exact HST|exact HRG]]]].
- split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
  exact (conj HJ (conj Hly (conj Hfs (conj Hperm (conj Hsaved (conj Hflag (conj Hfrm HFI))))))).
- pose proof (pf_next_skipn_lt (p_s v) o Ho). lia.
Qed.

(* s3 after the reload at 0x88100: SH + 8 *)
Lemma a7c_sh8 : forall v pos lyc Sc Wc rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  Z_to_bv 64 (bv_unsigned (ew (a7_E rX v pos) 33) + 8) = w64 (pf_SH v pos + 8).
Proof.
intros v pos lyc Sc Wc rX memc mdc HB.
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G11 & G12).
unfold kLowMemEnd, kHighShadowEnd in *.
rewrite a7_ew_SH, unsigned_lit_small by lia. reflexivity.
Qed.

(* RS3 0x88100: ld s3, 0x98(s1); j TAIL *)
Lemma a7c_rs3 : forall n, HA_TAIL B n -> H_RS3 B n.
Proof.
intros n HT. unfold H_RS3. intros v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d (HB & HMID & HST & HRG).
pose proof (a7_seed B v pos lyc Sc Wc rX memc mdc PF_RS3 false HB) as HS.
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof (a7c_sh8 v pos lyc Sc Wc rX memc mdc HB) as SH8.
pose proof HB as (_ & (HJ & _) & _).
assert (HEI : img_env VAL A_LIM (a7_E rX v pos)) by apply a7_E_img.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
change (cfg_at SEGS (BASE + PF_RS3) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + PF_RS3)) memc (seg_rom SEGS)) mdc).
paj_run_to_sh RUNTOP HS HJ PF_TAIL.
- a7c_awr.
- a7c_mem HF Hmem ms memc.
  pmkst HS. rewrite Hmem in HJ |- *.
  pose proof (a7_regs_kept rX v pos _ _ _ [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 26; 27] HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  apply (a7c_tail n v pos lyc Sc Wc rX (ms_regs ms) memc mdc _ cf cur' nm o ln d (HT fx) HB HJ HMID HST).
  + unfold a5_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: a7c_kept KEEP HFI.
  + unfold PF_RL, PF_RM, pf_rg. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: try (a7c_kept KEEP HRG; fail).
    prreg HS (Z_to_bv 5 19) R19. rewrite R19. exact SH8.
Qed.

(* CLR 0x880fc: mv s4, zero; then RS3's two instructions *)
Lemma a7c_clr : forall n, HA_TAIL B n -> H_CLR B n.
Proof.
intros n HT. unfold H_CLR. intros v pos lyc Sc Wc rX memc mdc cf nm o ln d (HB & HMID & HST0 & HRG).
pose proof (a7_seed B v pos lyc Sc Wc rX memc mdc PF_CLR false HB) as HS.
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof (a7c_sh8 v pos lyc Sc Wc rX memc mdc HB) as SH8.
pose proof HB as (_ & (HJ & _) & _).
assert (HST : pf_st v pos (rdW Wc memc) cf None nm (length (skipn (pf_next (p_s v) o) (p_s v)))).
{ destruct HST0 as (H1 & H2 & H3). exact (conj H1 (conj I (conj H2 H3))). }
assert (HEI : img_env VAL A_LIM (a7_E rX v pos)) by apply a7_E_img.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
change (cfg_at SEGS (BASE + PF_CLR) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + PF_CLR)) memc (seg_rom SEGS)) mdc).
paj_run_to_sh RUNTOP HS HJ PF_TAIL.
- a7c_awr.
- a7c_mem HF Hmem ms memc.
  pmkst HS. rewrite Hmem in HJ |- *.
  pose proof (a7_regs_kept rX v pos _ _ _ [2; 3; 4; 8; 9; 18; 21; 22; 24; 26; 27] HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  apply (a7c_tail n v pos lyc Sc Wc rX (ms_regs ms) memc mdc _ cf None nm o ln d (HT fx) HB HJ HMID HST).
  + unfold a5_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: a7c_kept KEEP HFI.
  + unfold PF_RL, PF_RM, pf_rg. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: try (a7c_kept KEEP HRG; fail).
    * prreg HS (Z_to_bv 5 19) R19. rewrite R19. exact SH8.
    * prreg HS (Z_to_bv 5 20) R20. rewrite R20. reflexivity.
Qed.

(* FUN 0x88064: mv s4, zero; TAIL *)
Lemma a7c_fun : forall n, HA_TAIL B n -> H_FUN B n.
Proof.
intros n HT. unfold H_FUN. intros v pos lyc Sc Wc rX memc mdc cf nm o ln d (HB & HMID & HST0 & HRG).
pose proof (a7_seed B v pos lyc Sc Wc rX memc mdc A7_FUN false HB) as HS.
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (_ & (HJ & _) & _).
assert (HST : pf_st v pos (rdW Wc memc) cf None nm (length (skipn (pf_next (p_s v) o) (p_s v)))).
{ destruct HST0 as (H1 & H2 & H3). exact (conj H1 (conj I (conj H2 H3))). }
assert (HEI : img_env VAL A_LIM (a7_E rX v pos)) by apply a7_E_img.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
change (cfg_at SEGS (BASE + A7_FUN) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + A7_FUN)) memc (seg_rom SEGS)) mdc).
paj_run_to_sh RUNTOP HS HJ PF_TAIL.
- a7c_awr.
- a7c_mem HF Hmem ms memc.
  pmkst HS. rewrite Hmem in HJ |- *.
  pose proof (a7_regs_kept rX v pos _ _ _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 26; 27] HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  apply (a7c_tail n v pos lyc Sc Wc rX (ms_regs ms) memc mdc _ cf None nm o ln d (HT fx) HB HJ HMID HST).
  + unfold a5_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: a7c_kept KEEP HFI.
  + unfold PF_RL, PF_RM, pf_rg. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: try (a7c_kept KEEP HRG; fail).
    prreg HS (Z_to_bv 5 20) R20. rewrite R20. reflexivity.
Qed.

End x.

(** ** The statements pf_a7.v's a7_assemble applies *)
Theorem a7_fun : A7_S_FUN B.
Proof. intros f0 n HT. exact (a7c_fun (fx := f0) n HT). Qed.

Theorem a7_clr : forall n, HA_TAIL B n -> forall f0 : YK11.FPState, H_CLR (fx := f0) B n.
Proof. intros n HT f0. exact (a7c_clr (fx := f0) n HT). Qed.

Theorem a7_rs3 : forall n, HA_TAIL B n -> forall f0 : YK11.FPState, H_RS3 (fx := f0) B n.
Proof. intros n HT f0. exact (a7c_rs3 (fx := f0) n HT). Qed.

End e.
End f.
End d.
