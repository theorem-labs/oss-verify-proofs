(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 207 of its 243 lines of code are new or changed and 1269 lines of the source are left out. *)
(* remember (reac_served_mark.c:38-47) on image A (fuzz_link.asan 0x89db4, 288 bytes; listing
   (internal path) (internal record, sha256 e02062b286f1)): THE ENTRY STATE of the walk of
   lib/A/Prog/remember_c.v `remember_acontract`, and the facts the walk carries from the Pre to the memories it
   sees later. The walk itself is lib/A/Prog/remember.v; the byte algebra of its Post is
   lib/A/Prog/rememberPost.v; the two call steps are lib/A/Prog/rememberCalls.v.

   The symbolic entry state (Section e below):
   - regions: the frame [sp - 64, sp) (`stack_region 64`, the eight 8-byte saves at +0x04..+0x20), the .got cell
     of the shadow base (`got_regionP`, object A_OBJ 1 = 0xa19d0) and the base cell it names
     (`bcell_regionP 32`, object A_OBJ 64 = 0xaa438, whose word is the atom 32 pinned to SHADOW_OFF), and the
     marks block at a0 (atom 10), whose first four bytes are the count `m->n` (the atom 33) and whose write
     window is exactly those four bytes (the store +0xc8 `sw a3, 0(s0)`; snprintf's 16 bytes are written by the
     callee, not by the run);
   - facts: sp in [2 ^ 46, 2 ^ 47) and 16-aligned (the journal's window is above `alloc_ceiling` and below
     2 ^ 47), the block's address in [4096, 2 ^ 47 - 525] (`amem_range`, and AR's block law on the ledger fact),
     the name's address in [1, 2 ^ 47), the shadow base pinned (AR's const law), and the count in [0, 32]
     (`marks_wf`);
   - one shadow entry, `mkSHE 10 0 4`: the four bytes of `m->n`, which the two instrumented checks (+0x3c for the
     load, +0xa8 for the store) read through s5. With it the token rule resolves both checks with no obligation
     (`covered`), and `cells_safe_b` admits the block's write window (`window_covered`), which is what lets the
     walk keep ONE fact for the block whether it lies below kLowMemEnd or above kHighMemBeg (`amem_range` gives
     the disjunction; `app_apart` holds on both arms).

   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c remember_c rememberPost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the shadow base, the span the runner checks its windows against (pcap's), and the entry's regions *)
Definition RSB : Z := 0x7fff8000.
Definition rBx : sv := SOff 32 0.
Definition rSpan : Z * Z := (RSB, RSB + 2 ^ 44 - 1).
Definition rSH : list shent := [mkSHE 10%nat 0 4].

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis HV : LinkVals (L := link_listing).

(* the marks block: the count word is the only part the RUN writes *)
Definition mk_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 MK_SIZE 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition r_regions : smem := [stack_region 64; got_regionP; bcell_regionP 32; mk_region].
Definition r_facts : facts :=
   mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 525) 0);
           (11%nat, mkAF 1 (2 ^ 47 - 1) 0); (32%nat, mkAF RSB RSB 0); (33%nat, mkAF 0 32 0)] [] [].
Definition r_ss : sstate := mkSS AF_remember sr_atoms r_regions None r_facts.
(* the two extra atoms the entry env names: the shadow base and the count *)
Definition r_extra (n : Z) : list word := [Z_to_bv 64 RSB; Z_to_bv 64 n].

(* ==========================================================================
   The LOOP-HEAD state (+0x5c), rebuilt at every iteration
   ==========================================================================
   The loop body is `mv a0, s2; mv a1, s1; jal wrapper_strcmp`, so between two iterations only the machine
   registers change; the symbolic state is rebuilt from them, with the eight saved words of the frame as the
   extra atoms 34..41 (the entry's ra and s0..s6, which the epilogue restores and which `aregs_preserved`
   needs), the shadow base as atom 32 and the count as atom 33.
   s5 keeps the SHAPE the instrumented check needs: `match_x` (YCbn.v:77) reads the shadow address
   `Bx + x >> 3` and gives back x, so the store check at +0xa8 (and the slow block at +0x10c, which tests
   `s0 & 7`) resolves against the shadow entry of atom 8 = s0 = the block. Every other register is its own
   atom: the loop needs no fact about s2 (it only hands it to the wrapper) nor about s6 (the two branches on
   it are the generic rule, not the token rule). *)
Definition frame_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 64 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 41 0)); YP09.mkChunk 8 (CVal 8 (SOff 40 0));
     YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0));
     YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0));
     YP09.mkChunk 48 (CVal 8 (SOff 35 0)); YP09.mkChunk 56 (CVal 8 (SOff 34 0))].
Definition mk_region_loop : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 MK_SIZE 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
(* the .got cell and the base cell are NOT regions here: the shadow base was loaded before the loop and
   lives in s5, so nothing after +0x5c reads them. *)
Definition l_regions : smem := [frame_region; mk_region_loop].
Definition l_facts : facts :=
   mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 (2 ^ 47 - 525) 0);
           (9%nat, mkAF 1 (2 ^ 47 - 1) 0); (32%nat, mkAF RSB RSB 0); (33%nat, mkAF 0 32 0)] [] [].
Definition l_sr : list sv :=
  sr_set sr_atoms (Z_to_bv 5 21) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 32 0)).
(* the same state at any offset of the loop: +0x5c (the head) and +0x68 (just after the call) *)
Definition l_ss_at (off : Z) : sstate := mkSS off l_sr l_regions None l_facts.
Definition l_ss : sstate := l_ss_at (AF_remember + 0x5c).
Definition lSH : list shent := [mkSHE 8%nat 0 4].
(* the ten extra atoms: the shadow base, the count, and the eight words the frame holds *)
Definition l_extra (n : Z) (regs : bvmap 5 word) : list word :=
  [Z_to_bv 64 RSB; Z_to_bv 64 n; getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19;
   getr regs 20; getr regs 21; getr regs 22].

(* the journal's bounds a walk needs (model_decide.v aj_bounds) *)
Lemma re_aj_bounds : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47 /\ 0 <= XO /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
split; [lia|]. split; [lia|]. split; [exact HXO|]. intros a Ha. apply Hpres. lia.
Qed.

(* the AR inside a journal *)
Lemma rem_aj_AR : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR pa_segs B lyc Sc W memc mdc.
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (_ & _ & (memS & HJ & _) & _).
exact (proj1 HJ).
Qed.

(* a byte view is a byte: the walk reads `mbyte` facts off `aview` facts and back *)
Lemma rem_mbyte_of_aview : forall (W : world pa_segs) (m : word -> option byte) a v,
  0 <= v < 256 -> aview pa_segs (w_H W) m a = Some v -> mbyte pa_segs (rdW W m) a = Some (Z_to_bv 8 v).
Proof.
intros W m a v Hv H. unfold aview in H.
destruct (mbyte pa_segs (rdW W m) a) as [b|] eqn:E; [|discriminate H].
cbn [option_map] in H. injection H as <-. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rem_aview_of_mbyte : forall (W : world pa_segs) (m : word -> option byte) a b,
  mbyte pa_segs (rdW W m) a = Some b -> aview pa_segs (w_H W) m a = Some (bv_unsigned b).
Proof. intros W m a b H. unfold aview. rewrite H. reflexivity. Qed.

(* and the same equality, transported: two memories with the same views have the same bytes *)
Lemma rem_mbyte_eq_of_aview_eq : forall (W : world pa_segs) (m m' : word -> option byte) a,
  aview pa_segs (w_H W) m' a = aview pa_segs (w_H W) m a ->
  mbyte pa_segs (rdW W m') a = mbyte pa_segs (rdW W m) a.
Proof.
intros W m m' a H. unfold aview in H.
destruct (mbyte pa_segs (rdW W m') a) as [b'|] eqn:E'; destruct (mbyte pa_segs (rdW W m) a) as [b|] eqn:E;
  cbn [option_map] in H; try discriminate H; [|reflexivity].
injection H as H. f_equal. apply bv_eq. exact H.
Qed.

(* ==========================================================================
   The entry state holds at the call
   ========================================================================== *)
Lemma rem_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q n gbs nm,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REMEMBER_AK -> spZ regs <= sp0 ->
  aarg regs 0 = p -> aarg regs 1 = q ->
  amarks_at pa_segs (rdW W memc) p gbs -> marks_wf gbs -> mk_n gbs = n ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memc) p -> amarks_ledger (ablocks B lyc Sc) p ->
  acstr_at pa_segs (rdW W memc) q nm ->
  astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memc) q nm ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs (r_extra n))) r_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_remember)) memc (seg_rom pa_segs))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q n gbs nm
  HJ Hal16 Hwlo Hwhi Hp Hq HMK HWF Hn HBLK HLED HNM HNMrt.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
destruct (re_aj_bounds G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
  as (Hceil & H47 & HXO & Hpres).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
assert (HIT : YImgTop.IMG_TOP = 0x654000) by reflexivity.
(* the block is off the image (the ledger fact) and at or above 4096 (AR's block law) *)
destruct HLED as (HLEDin & HOFF).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc p MK_SIZE HAR HLEDin) as (_ & H4096 & _).
unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HOFF.
pose proof HBLK as (Hp0 & Hpm & Hpra & Hphv & Hptail & Hpap).
pose proof HNMrt as (Hq0 & Hql & Hqm & _ & _ & _ & Hqap).
pose proof HMK as (HMKb & HMKlen).
pose proof HMKb as (HMKbytes & HMKwr).
pose proof (amk_n_range gbs HWF) as Hnr. rewrite Hn in Hnr. unfold MARKS_MAX in Hnr.
pose proof (amk_n_val pa_segs (rdW W memc) p gbs HMK) as HnV. rewrite Hn in HnV.
assert (Hpbound : p + 524 <= 2 ^ 47 - 1).
{ unfold amem_range, MK_SIZE in Hpm. destruct Hpm as [Hx | [_ Hx]]; lia. }
assert (Hqbound : q + Z.of_nat (length nm) + 8 <= 2 ^ 47 - 1).
{ unfold amem_range in Hqm. destruct Hqm as [Hx | [_ Hx]]; lia. }
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 64%nat ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1%nat ltac:(lia)) as HgotR.
unfold PcapImgEnd.pcap_img_end in HcellR, HgotR.
set (E := Eimg (Ereg regs (r_extra n))).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (r_extra n)) m)
  by (intros m Hm; subst E; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 RSB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (pa_val (A_OBJ 1)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 (pa_val (A_OBJ 64)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; rewrite <- Hp; reflexivity).
assert (U11 : bv_unsigned (ew E 11) = q) by (rewrite E11; rewrite <- Hq; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold r_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold r_regions, stack_region, got_regionP, bcell_regionP, mk_region.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable pa_segs). apply Hpres. lia.
  + fold E. rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 1)) 0 8 (SOff (A_OBJ 64) 0) (pa_val (A_OBJ 64)));
    [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 64)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VB (A_OBJ 64) (pa_val (A_OBJ 64)) Ecell) by (pose proof (pa_val_range (A_OBJ 64)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 64)) 0 8 (SOff 32 0) RSB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold RSB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kcell).
  + cbn [base_val]. fold E. rewrite U10.
    unfold MK_SIZE in *.
    split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hpm; lia|].
    split.
    * intros o Ho. cbn [ms_mem restrict mkst]. apply HMKwr. unfold MK_SIZE. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val pa_segs E _ p 0 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | cbn; lia | cbn; lia | cbn [ms_mem restrict mkst]; rewrite Z.add_0_r; exact HnV].
- apply pairwise_disjoint_of_extents.
  unfold r_regions, stack_region, got_regionP, bcell_regionP, mk_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
  rewrite (VB (A_OBJ 64) (pa_val (A_OBJ 64)) Ecell) by (pose proof (pa_val_range (A_OBJ 64)); lia).
  cbn [base_val]. rewrite Usp, U10.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold MK_SIZE, apart_frame in *.
  revert Hwlo Hwhi Hceil H47 C1a C1b HKv HIT HOFF H4096 Hpap HcellR HgcD HgotR. clear. intros.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [r_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, U10, U11, E32, E33, !unsigned_lit_small by (unfold RSB; lia).
  try change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  revert Hwlo Hwhi Hceil H47 HKv HIT H4096 Hal16 Hpbound Hqbound Hq0 Hnr C1a C1b. clear. unfold RSB. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | lia].
Qed.

(* the one shadow entry: the four bytes of m->n, which the two instrumented checks read *)
Lemma rem_shok : forall (W : world pa_segs) memc regs p n,
  aarg regs 0 = p -> amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memc) p ->
  sh_ok pa_segs rBx rSH (Eimg (Ereg regs (r_extra n))) (rdW W memc).
Proof.
intros W memc regs p n Hp HBLK.
pose proof HBLK as (Hp0 & Hpm & Hpra & _ & _ & _).
set (E := Eimg (Ereg regs (r_extra n))).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (r_extra n)) m)
  by (intros m Hm; subst E; apply Eimg_low; exact Hm).
assert (E10 : ew E 10 = getr regs 10)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 RSB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Hp' : bv_unsigned (getr regs 10) = p) by exact Hp.
assert (Hpb : p + 524 <= 2 ^ 47 - 1).
{ pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold amem_range, MK_SIZE in Hpm. destruct Hpm as [Hx | [_ Hx]]; lia. }
assert (UB : U E rBx = RSB).
{ unfold rBx. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold RSB; lia).
  apply zcanon_id. unfold RSB, M64. lia. }
assert (UM : U E (SOff 10 0) = p).
{ rewrite U_SOff, E10, Z.add_0_r, Hp'. apply zcanon_id. unfold M64. lia. }
apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, UM, Z.add_0_r.
split.
- intros x Hx. exact (Hpra x ltac:(unfold MK_SIZE; lia)).
- intros a Ha. cbn [Z.min Z.max] in Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold amem_range, MK_SIZE in Hpm. unfold RSB.
  destruct Hpm as [Hx | [Hy Hx]]; lia.
Qed.

End e.
