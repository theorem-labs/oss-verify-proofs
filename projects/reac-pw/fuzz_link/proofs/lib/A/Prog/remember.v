(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 289 of its 324 lines of code are new or changed and 1270 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_msg0_a.v, with its module paths and module names changed; 397 of its 434 lines of code are new or changed and 287 lines of the source are left out. *)
(* remember (reac_served_mark.c:38-47) on image A (fuzz_link.asan 0x89db4, 288 bytes; listing
   (internal path) (internal record, sha256 e02062b286f1)): THE WALK of
   lib/A/Prog/remember_c.v `remember_acontract` (link_amem.v's `aleaf_fx`: K = REMEMBER_AK = 8256, EV = 0, SIDE = [],
   the write set the marks block, the read set the name).

     remember_aproof : remember_acontract SK pa_segs PCAP_RLO PCAP_RHI B

   The pieces: lib/A/Prog/rememberEntry.v (the entry and loop-head symbolic states), lib/A/Prog/rememberPost.v
   (the byte algebra of the Post), lib/A/Prog/rememberKept.v (the two kept clauses for a heap write set),
   lib/A/Prog/rememberCalls.v (`rem_strcmp_call` at +0x64 and `rem_snp_tail`, the TAIL jump at +0xf4),
   lib/A/Prog/rememberLoop.v (`rem_lentry`, the loop state rebuilt from the machine registers),
   lib/A/Prog/rememberAppend.v (`rem_append_tail`, the append at a count n <= 31 from the tail-jump config;
   `rem_ret_leaf`, the `ret` that leaves the block as it was) and lib/A/Prog/rememberLoopRun.v (`rem_loop`, the
   strcmp loop by induction on the slots left, from the call config of turn i).

   This file: the entry run +0x00..+0x50 (both `awr_ok_x` write-window obligations), the branch `blez s4` at
   +0x50; on n <= 0 the append run +0xa8..+0xf4 and `rem_append_tail` at n = 0; on n > 0 the run to the first
   call +0x64, the loop invariant read off that state (registers, the frame's eight saved words, the count
   word, the memory outside the window), and `rem_loop` at turn 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs LinkMfDefs LinkSnpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c remember_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  rememberPost rememberEntry rememberKept rememberCalls LinkWalkMkCr rememberAppend rememberLoop rememberLoopRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis HV : LinkVals (L := link_listing).
Hypothesis STRCMP : RtString.astrcmp_realizes pa_segs B (pa_sigma LS___interceptor_trampoline_strcmp).
Hypothesis SNP : asnprintf_link_realizes pa_segs B PCAP_RLO PCAP_RHI LA_W_SNPRINTF.
(* The stack-protector pair musl's vsnprintf reads (LinkSnpDef.v `asnprintf_link_fpre`) is not a field of
   PAImg: the .got word 0xa2658 is a row of AR's const table (reached through `PcapSyms B`) and the guard
   object's bytes are the image's. Both are lib/A/Prog/LinkWalkMkCr.v's `link_guard_got` / `link_guard_val`,
   which take exactly these two hypotheses. *)
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Theorem remember_aproof : remember_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
unfold remember_acontract, aleaf_fx.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD Hfrm0 HP.
pose proof HPRE as HPRE0.
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof HJ as HJ0.
destruct HP as (gbs & nm & HMK & HWF & HLED & HBLK & Hqnz & HNM & Hlen & HNMrt & Hapart & HFMT & HFMTrt).
pose proof HLED as (HLEDin & HIMG).
pose proof HBLK as (Hp0 & Hpm & Hpra & Hphv & Hptail & Hpap).
pose proof HNMrt as (Hq0 & Hql & Hqm & Hqra & Hqhv & Hqtail & Hqap).
pose proof HMK as (HMKb & HMKlen).
pose proof HMKb as (HMKbytes & HMKwr).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HIMG as HOFF. unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HOFF.
destruct (re_aj_bounds SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
  as (Hceil & H47 & HXO & Hpres).
assert (HSZ : Z.of_nat (length gbs) = MK_SIZE) by exact HMKlen.
assert (HEI : img_env pa_val A_LIM (Eimg (Ereg regs (r_extra (mk_n gbs))))) by apply Eimg_env.
(* the entry symbolic state and its one shadow entry *)
assert (HS : st_ok_pi pa_segs pa_val (Eimg (Ereg regs (r_extra (mk_n gbs)))) r_ss
   (restrict (w_H W) (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_remember)) memc (seg_rom pa_segs)))).
{ exact (rem_entry SK B LAWS TL G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (aarg regs 0) (aarg regs 1) (mk_n gbs) gbs nm HJ Hal16 Hwlo Hwhi eq_refl eq_refl HMK HWF eq_refl
    HBLK HLED HNM HNMrt). }
assert (SHOK : sh_ok pa_segs rBx rSH (Eimg (Ereg regs (r_extra (mk_n gbs)))) (rdW W memc))
  by exact (rem_shok W memc regs (aarg regs 0) (mk_n gbs) eq_refl HBLK).
assert (HCFG : cfg_at pa_segs REMEMBER_A regs memc mdc
             = mkCfg (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_remember)) memc (seg_rom pa_segs)) mdc).
{ unfold cfg_at. rewrite (lv_text HV). reflexivity. }
rewrite HCFG.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (BR := paj_branch (PI := PI)).
pose (RET := paj_ret_at (PL := PL_link) (PI := PI)).
assert (HspE : bv_unsigned (ew (Eimg (Ereg regs (r_extra (mk_n gbs)))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (Hp10E : bv_unsigned (ew (Eimg (Ereg regs (r_extra (mk_n gbs)))) 10) = aarg regs 0).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). reflexivity. }
(* the prologue, the shadow base, the instrumented check of m->n and the load, up to `blez s4` (+0x50) *)
paj_run_tok RUN HS HJ SHOK rSpan.
{ (* the write windows: the frame, and the four bytes of m->n *)
  pose proof HspE as Hsp. pose proof Hp10E as Hp10.
  unfold r_ss. cbn [ss_mem].
  unfold r_regions, stack_region, got_regionP, bcell_regionP, mk_region.
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    rewrite Hsp in Ha. left. split; [left; lia | lia]. }
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite Hp10 in Ha.
  apply (Hajw a). unfold remember_awr.
  exists (aivl (aarg regs 0) MK_SIZE). split; [left; reflexivity|].
  unfold in_zr, aivl. cbn [fst snd].
  replace (aarg regs 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold MK_SIZE in *. lia. }
(* ---- the branch `blez s4` (+0x50): n <= 0 goes straight to the append ---- *)
psrr_branch_tok RUN BR HS SHOK rSpan.
{ (* n <= 0: the list is empty, the append path +0xa8 .. +0xf4 *)
  paj_run_tok RUN HS HJ SHOK rSpan.
  { match goal with
    | |- awr_ok_x ?E' _ _ _ _ _ _ _ _ _ _ _ =>
      assert (Hsp2 : bv_unsigned (ew E' 2) = spZ regs)
        by (rewrite !ew_ewset_other by lia; rewrite Eimg_low by (unfold A_TEXT; lia);
            rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
      assert (Hp2 : bv_unsigned (ew E' 10) = aarg regs 0)
        by (rewrite !ew_ewset_other by lia; rewrite Eimg_low by (unfold A_TEXT; lia);
            rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); reflexivity)
    end.
    cbn [ss_mem add_cond].
    apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite Hsp2 in Ha. left. split; [left; lia | lia]. }
    apply awr_ok_x_cons;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    rewrite Hp2 in Ha.
    apply (Hajw a). unfold remember_awr.
    exists (aivl (aarg regs 0) MK_SIZE). split; [left; reflexivity|].
    unfold in_zr, aivl. cbn [fst snd].
    replace (aarg regs 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold MK_SIZE in *. lia. }
  (* The two runs wrote only the frame [sp - 64, sp) and the count word [p, p + 4): `frame_of` of each run
     (its write windows are the two regions with a non-empty window) composes to that. *)
  lazymatch type of HFr0 with
  | frame_of ?E2 _ _ _ =>
    assert (Hsp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite !ew_ewset_other by lia; exact HspE);
    assert (Hp2 : bv_unsigned (ew E2 10) = aarg regs 0) by (rewrite !ew_ewset_other by lia; exact Hp10E)
  end.
  assert (KEEPm : forall a, 0 <= a < 2 ^ 64 ->
            ~ (spZ regs - 64 <= a < spZ regs) -> ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
            mbyte pa_segs (rdW W (ms_mem ms0)) a = mbyte pa_segs (rdW W memc) a).
  { intros a Ha H1 H2.
    assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
    unfold mbyte.
    rewrite (HFr0 (Z_to_bv 64 a)).
    - rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
      rewrite Hu. intros (r & Hin & Hr).
      unfold r_ss in Hin. cbn [ss_mem] in Hin. unfold r_regions in Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
        unfold stack_region, got_regionP, bcell_regionP, mk_region in Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?HspE, ?Hp10E in Hr; unfold MK_SIZE in *; lia.
    - rewrite Hu. intros (r & Hin & Hr).
      cbn [ss_mem add_cond In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Hsp2, ?Hp2 in Hr; unfold MK_SIZE in *; lia. }
  (* ---- the count is 0 on this arm (`blez s4` taken, and marks_wf gives 0 <= n) ---- *)
  assert (Hnr : 0 <= mk_n gbs <= 32)
    by (pose proof (amk_n_range gbs HWF) as X; unfold MARKS_MAX in X; exact X).
  assert (E33 : ew (Ereg regs (r_extra (mk_n gbs))) 33 = Z_to_bv 64 (mk_n gbs))
    by exact (ew_Ereg_extra regs (r_extra (mk_n gbs)) 1).
  assert (Hn0 : mk_n gbs = 0).
  { revert Hc. cbn [sv_denot].
    rewrite !ew_ewset_other by lia. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite E33.
    rewrite Z.add_0_r, unsigned_lit_small by lia.
    cbn [branch_taken]. unfold bv_lts.
    rewrite !bv_signed_small by (rewrite unsigned_lit_small; lia).
    rewrite !unsigned_lit_small by lia.
    intros H. destruct (Z.ltb_spec 0 (mk_n gbs)); cbn in H; [discriminate | lia]. }
  pmkst HS.
  prreg HS (Z_to_bv 5 10) Hr10. prreg HS (Z_to_bv 5 11) Hr11.
  prreg HS (Z_to_bv 5 12) Hr12. prreg HS (Z_to_bv 5 13) Hr13.
  prreg HS (Z_to_bv 5 1) Hr1. prreg HS (Z_to_bv 5 2) Hr2.
  prreg HS (Z_to_bv 5 3) Hr3. prreg HS (Z_to_bv 5 4) Hr4.
  cbn [A_TEXT A_LIM Nat.leb andb] in Hr10, Hr11, Hr12, Hr13, Hr1, Hr2, Hr3, Hr4.
  rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), E33, Hn0 in Hr10.
  replace (alu64 ALU_SLL (Z_to_bv 64 0) (Z_to_bv 64 4)) with (Z_to_bv 64 0) in Hr10 by reflexivity.
  change (bv_unsigned (getr regs 10)) with (aarg regs 0) in Hr10.
  assert (Hpb : aarg regs 0 + 524 <= 2 ^ 47 - 1)
    by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [_ Hx]]; lia).
  rewrite alu_add_small in Hr10 by (unfold M64; lia).
  rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl) in Hr13.
  rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl) in Hr1.
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in Hr2.
  rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in Hr3.
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in Hr4.
  assert (HFMTa : pa_val 302 = LA_FMT_S).
  { change 302%nat with (A_OBJ 61). rewrite (lv_obj HV 61%nat ltac:(unfold link_nobj; lia)). reflexivity. }
  rewrite HFMTa in Hr12.
  (* ---- the marks block at the tail memory: the count word is the store's, the rest is memc's ---- *)
  lazymatch type of HS with
  | st_ok _ ?Ex ?ss _ =>
    pose proof (st_ok_region_nth Ex ss _ 3%nat _ HS eq_refl) as HRG;
    assert (HE33x : ew Ex 33 = Z_to_bv 64 (mk_n gbs))
      by (rewrite !ew_ewset_other by lia; rewrite Eimg_low by (unfold A_TEXT; lia); exact E33);
    assert (HE10x : bv_unsigned (ew Ex 10) = aarg regs 0)
      by (rewrite !ew_ewset_other by lia; exact Hp10E);
    pose proof (field_of_region_any Ex (rdW W (ms_mem ms0)) 10%nat (aarg regs 0) _ 0 MK_SIZE 0 4 0 4%N
                  (SOff 33 1) HRG HE10x ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HCNT;
    replace (bv_unsigned (sv_denot Ex (SOff 33 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in HCNT
      by (cbn [sv_denot]; rewrite HE33x, Hn0; reflexivity)
  end.
  (* presence only grows across the two runs *)
  assert (PRG : forall x, apresent (w_H W) memc x -> apresent (w_H W) (ms_mem ms0) x).
  { intros x (Hh & b & Hb).
    assert (Hx1 : mrestrict (w_H W) memc (Z_to_bv 64 x) <> None)
      by (unfold mrestrict; rewrite Hh, Hb; discriminate).
    pose proof (HG _ Hx1) as Hx2. pose proof (HG0 _ Hx2) as Hx3.
    unfold mrestrict in Hx3. rewrite Hh in Hx3.
    split; [exact Hh|].
    destruct (ms_mem ms0 (Z_to_bv 64 x)) as [b'|] eqn:Em; [exists b'; reflexivity | contradiction]. }
  (* the callee-saved registers at the tail call are the entry's *)
  assert (HAP1 : aregs_preserved regs (ms_regs ms0)).
  { lazymatch type of HS with
    | st_ok _ ?Ex ?ss _ =>
      apply (aregs_preserved_of_st_ok pa_segs (w_H W) Ex ss _ regs (r_extra (mk_n gbs)) HS)
    end.
    - split; [intros nn Hnn; rewrite !ew_ewset_other by lia; apply Eimg_low; unfold A_TEXT; lia
             | reflexivity].
    - vm_compute. reflexivity. }
  assert (Hnames0 : mk_names gbs = [])
    by (apply length_zero_iff_nil; rewrite amk_names_length, Hn0; reflexivity).
  (* ---- the TAIL jump +0xf4 into wrapper_snprintf: the append at n = 0 ---- *)
  assert (HSIG : pa_sigma LS___interceptor_trampoline_snprintf = LA_W_SNPRINTF)
    by (rewrite (lv_sigma HV); reflexivity).
  rewrite HSIG.
  eapply (rem_append_tail SK B LAWS SNP TB HSEGS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
            regs gbs nm (ms_regs ms0) (ms_mem ms0) _ HJ0 HGok HROD Hraw Hra4 Hgp Htp Hal16 Hwlo Hwhi Hajw Hnro
            Hfrm0 HMK HWF HLED HBLK Hqnz HNM Hlen HNMrt Hapart HFMT HFMTrt).
  - lia.
  - rewrite Hnames0. reflexivity.
  - exact HJ.
  - repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - exact HAP1.
  - exact Hr1.
  - rewrite Hn0. unfold w64, MK_NAME, MARK_LEN.
    replace (aarg regs 0 + (4 + 16 * 0)) with (aarg regs 0 + 4 + 0) by lia. exact Hr10.
  - exact Hr11.
  - exact Hr12.
  - unfold w64, aarg, argZ. rewrite Z_to_bv_bv_unsigned. exact Hr13.
  - intros a Ha H1 H2. apply KEEPm; [exact Ha | lia | exact H2].
  - intros kk Hkk. rewrite Hn0.
    replace (aarg regs 0 + Z.of_nat kk) with (aarg regs 0 + 0 + Z.of_nat kk) by lia.
    exact (HCNT kk Hkk).
  - exact PRG. }
(* ---- n > 0: the strcmp loop +0x5c .. +0x7c, entered at its first call, then lib/A/Prog/rememberLoopRun.v
   `rem_loop` at turn 0 ---- *)
  assert (Hnr : 0 <= mk_n gbs <= 32)
    by (pose proof (amk_n_range gbs HWF) as X; unfold MARKS_MAX in X; exact X).
  assert (E33 : ew (Ereg regs (r_extra (mk_n gbs))) 33 = Z_to_bv 64 (mk_n gbs))
    by exact (ew_Ereg_extra regs (r_extra (mk_n gbs)) 1).
  assert (Hnpos : 0 < mk_n gbs).
  { revert Hc. cbn [sv_denot].
    rewrite !ew_ewset_other by lia. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite E33.
    rewrite Z.add_0_r, unsigned_lit_small by lia.
    cbn [branch_taken]. unfold bv_lts.
    rewrite !bv_signed_small by (rewrite unsigned_lit_small; lia).
    rewrite !unsigned_lit_small by lia.
    intros H. destruct (Z.ltb_spec 0 (mk_n gbs)); cbn in H; [lia | discriminate]. }
  (* the prologue of the loop (+0x54, +0x58) and its first call at +0x64 *)
  paj_run_tok RUN HS HJ SHOK rSpan.
  { match goal with
    | |- awr_ok_x ?E' _ _ _ _ _ _ _ _ _ _ _ =>
      assert (Hsp2 : bv_unsigned (ew E' 2) = spZ regs)
        by (rewrite !ew_ewset_other by lia; exact HspE);
      assert (Hp2 : bv_unsigned (ew E' 10) = aarg regs 0)
        by (rewrite !ew_ewset_other by lia; exact Hp10E)
    end.
    cbn [ss_mem add_cond].
    apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite Hsp2 in Ha. left. split; [left; lia | lia]. }
    apply awr_ok_x_cons;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    rewrite Hp2 in Ha.
    apply (Hajw a). unfold remember_awr.
    exists (aivl (aarg regs 0) MK_SIZE). split; [left; reflexivity|].
    unfold in_zr, aivl. cbn [fst snd].
    replace (aarg regs 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold MK_SIZE in *. lia. }
pmkst HS.
  (* the bytes the two runs did not write: all but the frame and the count word *)
  lazymatch type of HFr0 with
  | frame_of ?E2 _ _ _ =>
    assert (Hsp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite !ew_ewset_other by lia; exact HspE);
    assert (Hp2 : bv_unsigned (ew E2 10) = aarg regs 0) by (rewrite !ew_ewset_other by lia; exact Hp10E)
  end.
  assert (KEEPm : forall a, 0 <= a < 2 ^ 64 ->
            ~ (spZ regs - 64 <= a < spZ regs) -> ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
            mbyte pa_segs (rdW W (ms_mem ms0)) a = mbyte pa_segs (rdW W memc) a).
  { intros a Ha H1 H2.
    assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
    unfold mbyte.
    rewrite (HFr0 (Z_to_bv 64 a)).
    - rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
      rewrite Hu. intros (r & Hin & Hr).
      unfold r_ss in Hin. cbn [ss_mem] in Hin. unfold r_regions in Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
        unfold stack_region, got_regionP, bcell_regionP, mk_region in Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?HspE, ?Hp10E in Hr; unfold MK_SIZE in *; lia.
    - rewrite Hu. intros (r & Hin & Hr).
      cbn [ss_mem add_cond In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Hsp2, ?Hp2 in Hr; unfold MK_SIZE in *; lia. }
  assert (HnV : val_mem pa_segs (rdW W memc) (aarg regs 0) 4 (mk_n gbs))
    by exact (amk_n_val pa_segs _ _ gbs HMK).
  assert (G10 : getr regs 10 = Z_to_bv 64 (aarg regs 0))
    by (change (aarg regs 0) with (bv_unsigned (getr regs 10)); symmetry; apply Z_to_bv_bv_unsigned).
  assert (G11 : getr regs 11 = Z_to_bv 64 (aarg regs 1))
    by (change (aarg regs 1) with (bv_unsigned (getr regs 11)); symmetry; apply Z_to_bv_bv_unsigned).
  (* the frame words, the count word and the callee-saved registers, read off the state at the call *)
  lazymatch type of HS with
  | st_ok _ ?Ex ?ss (restrict _ ?msx) =>
    assert (UspX : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite !ew_ewset_other by lia; exact HspE);
    assert (UpX : bv_unsigned (ew Ex 10) = aarg regs 0) by (rewrite !ew_ewset_other by lia; exact Hp10E);
    assert (VF : forall (r : nat) (rb : bv 5), Z.of_nat r = bv_unsigned rb -> (r < 32)%nat ->
              bv_unsigned (sv_denot Ex (SOff r 0)) mod 2 ^ (8 * Z.of_N 8) = bv_unsigned (getr regs rb))
      by (intros r rb Hrb Hr32; cbn [sv_denot]; rewrite !ew_ewset_other by lia;
          rewrite Eimg_low by (unfold A_TEXT; lia);
          rewrite (ew_Ereg_nat regs _ r rb Hrb), Z.add_0_r, Z_to_bv_bv_unsigned;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_small; exact (rl_u64 (getr regs rb)));
    assert (VN0 : bv_unsigned (sv_denot Ex (SOff 33 0)) mod 2 ^ (8 * Z.of_N 4) = mk_n gbs)
      by (cbn [sv_denot]; rewrite !ew_ewset_other by lia; rewrite Eimg_low by (unfold A_TEXT; lia);
          rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia;
          change (2 ^ (8 * Z.of_N 4)) with 4294967296; apply Z.mod_small; lia);
    assert (HAEx : env_agree 32 (Ereg regs (r_extra (mk_n gbs))) Ex)
      by (split; [intros nn Hnn; rewrite !ew_ewset_other by lia; apply Eimg_low; unfold A_TEXT; lia
                 | reflexivity]);
    pose proof (st_ok_region_nth Ex ss _ 0%nat _ HS eq_refl) as HRG0;
    pose proof (st_ok_region_nth Ex ss _ 3%nat _ HS eq_refl) as HRG3;
    assert (HCNTf : val_mem pa_segs (rdW W (ms_mem msx)) (aarg regs 0) 4 (mk_n gbs))
      by (pose proof (field_of_region_any Ex _ 10%nat (aarg regs 0) _ _ _ _ _ 0 4%N (SOff 33 0) HRG3 UpX
                        ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as X;
          rewrite VN0 in X; cbn [ms_mem restrict] in X;
          intros kk Hkk; pose proof (X kk Hkk) as Y; rewrite Z.add_0_r in Y; exact Y);
    let FRW od e rr rb :=
      (pose proof (field_of_region_any Ex _ 2%nat (spZ regs) _ _ _ _ _ od 8%N e HRG0 UspX
                     ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as X;
       rewrite (VF rr rb eq_refl ltac:(lia)) in X; cbn [ms_mem restrict] in X;
       match goal with |- val_mem _ _ ?ad _ _ => replace ad with (spZ regs + od) by lia end;
       exact X) in
    assert (F0 : val_mem pa_segs (rdW W (ms_mem msx)) (spZ regs - 64 + 0) 8 (bv_unsigned (getr regs 22)))
      by (FRW (-64) (SOff 22 0) 22%nat (22%bv : bv 5));
    assert (F1 : val_mem pa_segs (rdW W (ms_mem msx)) (spZ regs - 64 + 8) 8 (bv_unsigned (getr regs 21)))
      by (FRW (-56) (SOff 21 0) 21%nat (21%bv : bv 5));
    assert (F2 : val_mem pa_segs (rdW W (ms_mem msx)) (spZ regs - 64 + 16) 8 (bv_unsigned (getr regs 20)))
      by (FRW (-48) (SOff 20 0) 20%nat (20%bv : bv 5));
    assert (F3 : val_mem pa_segs (rdW W (ms_mem msx)) (spZ regs - 64 + 24) 8 (bv_unsigned (getr regs 19)))
      by (FRW (-40) (SOff 19 0) 19%nat (19%bv : bv 5));
    assert (F4 : val_mem pa_segs (rdW W (ms_mem msx)) (spZ regs - 64 + 32) 8 (bv_unsigned (getr regs 18)))
      by (FRW (-32) (SOff 18 0) 18%nat (18%bv : bv 5));
    assert (F5 : val_mem pa_segs (rdW W (ms_mem msx)) (spZ regs - 64 + 40) 8 (bv_unsigned (getr regs 9)))
      by (FRW (-24) (SOff 9 0) 9%nat (9%bv : bv 5));
    assert (F6 : val_mem pa_segs (rdW W (ms_mem msx)) (spZ regs - 64 + 48) 8 (bv_unsigned (getr regs 8)))
      by (FRW (-16) (SOff 8 0) 8%nat (8%bv : bv 5));
    assert (F7 : val_mem pa_segs (rdW W (ms_mem msx)) (spZ regs - 64 + 56) 8 (bv_unsigned (getr regs 1)))
      by (FRW (-8) (SOff 1 0) 1%nat (1%bv : bv 5));
    assert (RS0 : forall r, r = 3 \/ r = 4 \/ 23 <= r <= 27 ->
              getr (ms_regs msx) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
      by (intros r Hr; assert (Hr' : r = 3 \/ r = 4 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
          destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
          match goal with |- getr _ (Z_to_bv 5 ?rr) = _ =>
            exact (regs_kept_of_st_ok pa_segs Ex ss (restrict (w_H W) msx) regs (r_extra (mk_n gbs))
                     [Z_to_bv 5 rr] HS HAEx ltac:(vm_compute; reflexivity) (Z_to_bv 5 rr) (or_introl eq_refl))
          end)
  end.
  assert (UN0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
            aview pa_segs (w_H W) (ms_mem ms0) a = aview pa_segs (w_H W) memc a).
  { intros a Ha Hn.
    destruct (Z_lt_le_dec a (aarg regs 0)) as [Hlt | Hge];
      [|destruct (Z_lt_le_dec a (aarg regs 0 + 4)) as [Hlt4 | Hge4]].
    - unfold aview. rewrite (KEEPm a Ha ltac:(lia) ltac:(lia)). reflexivity.
    - unfold aview. replace a with (aarg regs 0 + Z.of_nat (Z.to_nat (a - aarg regs 0))) by lia.
      rewrite (HCNTf (Z.to_nat (a - aarg regs 0)) ltac:(lia)), (HnV (Z.to_nat (a - aarg regs 0)) ltac:(lia)).
      reflexivity.
    - unfold aview. rewrite (KEEPm a Ha ltac:(lia) ltac:(lia)). reflexivity. }
  prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 2) Q2'. prreg HS (Z_to_bv 5 8) Q8.
  prreg HS (Z_to_bv 5 9) Q9. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
  prreg HS (Z_to_bv 5 18) Q18. prreg HS (Z_to_bv 5 19) Q19. prreg HS (Z_to_bv 5 20) Q20.
  prreg HS (Z_to_bv 5 21) Q21. prreg HS (Z_to_bv 5 22) Q22.
  cbn [A_TEXT A_LIM Nat.leb andb] in Q1, Q2', Q8, Q9, Q10, Q11, Q18, Q19, Q20, Q21, Q22.
  (* ---- the loop from turn 0 ---- *)
  assert (Hpb : aarg regs 0 + 524 <= 2 ^ 47 - 1)
    by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [_ Hx]]; lia).
  eapply (rem_loop SK B LAWS HV STRCMP SNP TB HSEGS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
            regs gbs nm HJ0 HGok HROD Hraw Hra4 Hgp Htp Hal16 Hwlo Hwhi Hajw Hnro Hfrm0 HMK HWF HLED HBLK Hqnz HNM
            Hlen HNMrt Hapart HFMT HFMTrt (Z.to_nat (mk_n gbs)) 0).
  - lia.
  - lia.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 1)); [reflexivity|].
    rewrite Q1, unsigned_lit_small by (pose proof (pa_val_range 240); lia). reflexivity.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 2)); [reflexivity|].
    rewrite Q2', (ew_Ereg_nat regs _ 2 2%bv eq_refl). unfold spZ. f_equal; try lia.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 8)); [reflexivity|].
    rewrite Q8, (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact G10.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 9)); [reflexivity|].
    rewrite Q9, (ew_Ereg_nat regs _ 11 11%bv eq_refl). exact G11.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 10)); [reflexivity|].
    rewrite Q10, (ew_Ereg_nat regs _ 10 10%bv eq_refl), G10, unsigned_lit_small by lia. f_equal. lia.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 11)); [reflexivity|].
    rewrite Q11, (ew_Ereg_nat regs _ 11 11%bv eq_refl). exact G11.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 18)); [reflexivity|].
    rewrite Q18, (ew_Ereg_nat regs _ 10 10%bv eq_refl), G10, unsigned_lit_small by lia. f_equal. lia.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 19)); [reflexivity|].
    rewrite Q19, (ew_Ereg_nat regs _ 10 10%bv eq_refl), G10, unsigned_lit_small by lia. reflexivity.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 20)); [reflexivity|].
    rewrite Q20, E33. reflexivity.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 21)); [reflexivity|].
    rewrite Q21, (ew_Ereg_nat regs _ 10 10%bv eq_refl), G10.
    rewrite (ew_Ereg_extra regs (r_extra (mk_n gbs)) 0 : ew _ 32 = _). cbn [nth r_extra].
    rewrite rl_srl3 by lia.
    assert (Hd8 : 0 <= aarg regs 0 / 8 < 2 ^ 44)
      by (pose proof (Z.div_pos (aarg regs 0) 8 ltac:(lia) ltac:(lia));
          split; [lia | apply Z.div_lt_upper_bound; lia]).
    rewrite alu_add_small by (unfold M64, RSB; lia). f_equal. lia.
  - transitivity (getr (ms_regs ms0) (Z_to_bv 5 22)); [reflexivity|].
    rewrite Q22, E33. f_equal. lia.
  - exact RS0.
  - exact F0.
  - exact F1.
  - exact F2.
  - exact F3.
  - exact F4.
  - exact F5.
  - exact F6.
  - exact F7.
  - exact UN0.
  - intros x Hx. apply HG0. apply HG. exact Hx.
  - exact HJ.
  - repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - intros j Hj. lia.
Qed.

End b.
End a.

About remember_aproof.
Print Assumptions remember_aproof.
