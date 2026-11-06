(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry of descriptors_panel_get's walk (plugin-hostd/fuzz_command.asan) and the two arms of the inlined record(), from 0x8d10c to the join at 0x8d180, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment proved from the next one's statement) with the shared seed pieces of lib/A/Prog/RecBTemplate.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_panel_get_s7.v, with its module paths and module names changed; 448 of its 495 lines of code are new or changed and 850 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3; 0x86140), the segment S_MF_HDRB (HFIND 0x865c0 ->
   TAIL 0x86820): the new entry's own code, from the inner cut MFB_NEWE 0x86b54 to the inner cut MFB_RMSET 0x86b8c
   (mf_hdrb_2.v). A walk lane of the image-B m_file-family owner's G2B (a piece agent). proves no function (kind: segment lemma of
   m_file's image-B walk). `hb7_newe : forall n, MFB_RMSET_F B n -> MFB_NEWE_F B n`.
   ADAPTED from image A's lib/A/Prog/m_file_s_hdrb_7.v (the image-A m_file-family lane, a piece agent): the same
   proof shape at image B's registers, frame cells and pcs, plus image B's two UBSan trap branches, which image A
   does not have.

   THE CODE (the neutral listing of m_file in image B lines 647-660):
     0x86b54 `lb a1,0(a1)`, `bnez`  the instrumented check (a load of the shadow byte at ((c + 0x2000) >> 3) + the
                                    shadow base, which 0x86b04-0x86b08 left in a1, and a compare) of the 4-byte
                                    store at c + 0x2000; the slow path 0x86d78-0x86d84 rejoins at 0x86b5c or
                                    reaches the error path (a call of an errpath_* entry, 0x86f4c-0x86f50), which
                                    the proof shows is not reached
     0x86b5c `addi a1,a0,1`         a1 := n + 1 (a0 = n = |seg mcc|, the load of c->n at 0x86b18)
     0x86b60 `sw a1,0(s6)`          c->n := n + 1 (s6 = c + 0x2000, mf_regs_at)
     0x86b64 `li a1,33`
     0x86b68 `bgeu a0,a1` -> unimp  the UBSan bound of c->seg[n]: not taken, because 0 <= n < 32 < 33 (the path's
                                    test 0x86b1c and sa_mconf's bound); hb7_ub_b68 refutes the taken edge
     0x86b6c `slli a0,a0,0x8`       a0 := 256 n
     0x86b70 `ld a1,16(s1)`         a1 := ~c, the frame cell 16(s1) (mf_cells)
     0x86b74 `bltu a1,a0` -> unimp  the UBSan pointer overflow of c + 256 n: not taken, because c + 9236 <= 2 ^ 64
                                    (mf_core's sa_addr of the block) and 256 n < 9236, so 2 ^ 64 - 1 - c >= 256 n;
                                    hb7_ub_b74 refutes the taken edge
     0x86b78 `add s5,s9,a0`         s5 := g = c + 256 n = &c->seg[n] (s9 = c)
     0x86b7c .. 0x86b84             a2 := 256, a0 := s5, a1 := 0
     0x86b88 `jal 0x55e08`          the checked memset entry: memset(&c->seg[n], 0, 256), back at 0x86b8c
   The two `unimp` edges go to 0x86e84; neither is stepped over: each is refuted at its branch.

   THE PROOF. m_file_sd.v's mf_seed at MFB_NEWE (the frame cells and 152(s1) as chunks), the frame-cell region made
   read-only (this piece stores no frame cell), a1 re-shaped to mf_shx 33 MC_N and s6 to SOff 33 MC_N (their
   denotations are the statement's values, mf_denot_shx) so the token executor reads the load at 0x86b54 as the
   check of the store at 0x86b60, a writable region of the count cell [c + 0x2000, c + 0x2004) at atom 33, and
   mf_she_blk's shadow entry of the block (hi = 9144), which decides the check. Three token runs, cut at the two
   trap branches (paj_branch, then the taken edge refuted); the one store is in M_FILE_FP (hb_fp_cnt) and in the
   live block (awr_ok). kept_of_frame: the runs changed the count cell only; the final region gives c->n = n + 1.
   The call is aj_intrin_atS (OSet) under the Section hypothesis AMEMSET; its destination facts come from the AR of
   the run's final state (amem_range / range_addressable / shadow_hull_vis _of_block, the block's bytes present
   hence writable) and from mf_hdrb_3.v's hb3_entry_wr (awr_byte: n < |seg| of the final model, hb_fin_grows).
   After it: m_file_k.v's mf_keep_art carries the cut facts (the bytes outside the count cell, the entry and the
   call's window below s1 are kept); the block's bytes are the entry's bytes BS with the count and the 256 zero
   bytes written (hb_bytes_upd twice), which encode m_set_segs mcc (mc_seg mcc ++ [mseg0 []]) by mconf_enc_append
   and hb_mseg_enc_zero, after hb7_upd_comm reorders the two writes; the model equation is hb_mh_find_new. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m m_file_sd
  m_file_mdl m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_hdrb_1 mf_hdrb_2 mf_hdrb_3 mf_hdrb_4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* two writes at disjoint offsets commute (image A's hb7_upd_comm, the image-A m_file-family lane's plain draft mf_line_hdrb.v;
   it names no image number). mconf_enc_append (mf_hdrb_1.v) writes the entry first and the count second; the code
   stores the count (0x86b60) before the memset of the entry (0x86b88). *)
Lemma hb7_upd_comm : forall (cs X1 X2 : list byte) k1 k2, (k1 + length X1 <= k2)%nat ->
  (k2 + length X2 <= length cs)%nat ->
  Mem.upd_bytes (Mem.upd_bytes cs k2 X2) k1 X1 = Mem.upd_bytes (Mem.upd_bytes cs k1 X1) k2 X2.
Proof.
intros cs X1 X2 k1 k2 H1 H2.
assert (L1 : length (Mem.upd_bytes cs k2 X2) = length cs) by (apply Mem.upd_bytes_length; lia).
assert (L2 : length (Mem.upd_bytes cs k1 X1) = length cs) by (apply Mem.upd_bytes_length; lia).
assert (L3 : length (Mem.upd_bytes (Mem.upd_bytes cs k2 X2) k1 X1) = length cs)
  by (rewrite Mem.upd_bytes_length; [exact L1 | rewrite L1; lia]).
assert (L4 : length (Mem.upd_bytes (Mem.upd_bytes cs k1 X1) k2 X2) = length cs)
  by (rewrite Mem.upd_bytes_length; [exact L2 | rewrite L2; lia]).
apply mcx_nth_ext. intros i.
destruct (Nat.lt_ge_cases i (length cs)) as [Hi|Hi].
- rewrite (Mem.upd_bytes_nth (Mem.upd_bytes cs k2 X2) k1 X1 i) by (rewrite L1; lia).
  rewrite (Mem.upd_bytes_nth cs k2 X2 i) by lia.
  rewrite (Mem.upd_bytes_nth (Mem.upd_bytes cs k1 X1) k2 X2 i) by (rewrite L2; lia).
  rewrite (Mem.upd_bytes_nth cs k1 X1 i) by lia.
  destruct (Nat.leb_spec k1 i), (Nat.ltb_spec i (k1 + length X1)), (Nat.leb_spec k2 i),
    (Nat.ltb_spec i (k2 + length X2)); cbn [andb]; first [reflexivity | lia].
- rewrite (proj2 (nth_error_None _ i)) by (rewrite L3; lia).
  rewrite (proj2 (nth_error_None _ i)) by (rewrite L4; lia). reflexivity.
Qed.

(* the state's form, computed *)
Ltac hb7_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* a register of a run's final state, its denotation NOT normalized (prreg without prreg_norm) *)
Ltac hb7_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* ===================================== the two UBSan trap branches =====================================
   both compare values the symbolic state holds; each taken edge is refuted here and never stepped over *)
(* the word of a `not` cell (m_file_sd.v's mf_notx, as the state holds it after vm_compute) *)
Lemma hb7_U_not : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
  U E (SAlu ALU_SUB (SLit (-1)) (SOff n k)) = 2 ^ 64 - 1 - (x + k).
Proof.
intros E n x k Hn Hx Hxk.
change (SAlu ALU_SUB (SLit (-1)) (SOff n k)) with (mf_notx n k).
unfold U. rewrite (mf_denot_not E n x k Hn Hx Hxk). apply unsigned_lit_small. lia.
Qed.
(* the word of `slli a0,a0,0x8` *)
Lemma hb7_U_sll8 : forall E (n : nat) x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 32 ->
  U E (SAlu ALU_SLL (SOff n 0) (SLit 8)) = 256 * x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu, U_SLit, U_SOff, Hn.
rewrite (unsigned_lit_small x) by lia. rewrite Z.add_0_r.
cbn [zalu_raw]. rewrite (zcanon_id 8) by (unfold M64; lia). change (Z.land 8 63) with 8.
rewrite (zcanon_id x) by (unfold M64; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* 0x86b68 `bgeu a0,a1` (a0 = n, a1 = 33): the UBSan bound of c->seg[n], not taken because n < 32 *)
Lemma hb7_ub_b68 : forall E (n : nat) x, ew E n = Z_to_bv 64 x -> 0 <= x < 32 ->
  branch_taken BC_GEU (sv_denot E (SOff n 0)) (sv_denot E (SLit 33)) = false.
Proof.
intros E n x Hn Hx. rewrite branch_geu_U, (U_atom E n x Hn ltac:(lia)), U_lit by lia.
apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
Qed.
(* 0x86b74 `bltu a1,a0` (a1 = ~c, a0 = 256 n): the UBSan pointer overflow of c + 256 n, not taken because
   c + 9236 <= 2 ^ 64 and 256 n < 9236 *)
Lemma hb7_ub_b74 : forall E (nc nn : nat) c x, ew E nc = Z_to_bv 64 c -> ew E nn = Z_to_bv 64 x ->
  0 <= c -> 0 <= x < 32 -> c + 9236 <= 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_SUB (SLit (-1)) (SOff nc 0)))
    (sv_denot E (SAlu ALU_SLL (SOff nn 0) (SLit 8))) = false.
Proof.
intros E nc nn c x Hc Hx Hc0 Hx32 Hcb.
rewrite branch_ltu_U, (hb7_U_not E nc c 0 Hc ltac:(lia) ltac:(lia)), (hb7_U_sll8 E nn x Hx ltac:(lia)).
apply Z.ltb_ge. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a value a chunk holds, read through the reader *)
Lemma hb7_sa_val : forall H (mem : word -> option byte) a n x,
val_mem SEGS (mrestrict H mem) a n x -> sa_val (aview SEGS H mem) a n x.
Proof.
intros H mem a n x Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
try unfold YG0f.le_byte; try unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.
(* 256 bytes the checked memset set to 0 *)
Lemma hb7_zero256 : forall (rd : reader) g, (forall i, 0 <= i < 256 -> rd (g + i) = Some (0 mod 256)) ->
sa_bytes rd g (repeat seg_spec.ZERO 256).
Proof.
intros rd g H i Hi. rewrite repeat_length in Hi. rewrite (H (Z.of_nat i) ltac:(lia)).
rewrite (nth_indep _ ZB0 seg_spec.ZERO) by (rewrite repeat_length; lia). rewrite nth_repeat. reflexivity.
Qed.
(* a cell carried to a memory the reader agrees with on its bytes *)
Lemma hb7_val_keep : forall (W W' : world SEGS) m m' a (nb : nat) val,
(forall x, a <= x < a + Z.of_nat nb -> rdW W' m' x = rdW W m x) ->
val_mem SEGS (mrestrict (w_H W) m) a nb val -> val_mem SEGS (mrestrict (w_H W') m') a nb val.
Proof.
intros W W' m m' a nb val K Hv k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k) (K (a + Z.of_nat k) ltac:(lia))).
exact (Hv k Hk).
Qed.

Section e.
Variable B : asyms.
(* the listing's objects against the image's addresses (m_file_sd.v's seed reads m_key.words through it) *)
Hypothesis VOBJS : seg_val_objs.
(* the checked memset entry, at the listing's call target, at every FP state (the kit's text, lib/B/YG0d.v) *)
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

Lemma hb7_body : forall n, MFB_RMSET_stmt B n -> MFB_NEWE_stmt B n.
Proof.
intros n RMSET. unfold MFB_NEWE_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest o nm
  CX LS FRM CORE CELLS RA Hlen Hne LOOP HNM HFIND H32 HFIN R10 R11 S192 R26 R27 NP.
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V120 & HMC & HAD & HTL).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & Hheap0 & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
change (spZ (mv_regs v)) with (mv_sp v) in *.
rewrite HSTK in Hslo.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (hb_mconf_bounds _ _ _ HMC) as (HB32 & _).
pose proof LOOP as (_ & _ & _ & HLstr & HLad & Hcurok & Hk0 & _).
(* where things lie *)
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_flag _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (_ & _ & HFLapp & HFLc).
pose proof (hb3_heap_now B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc _ _ CORE Hheap0) as Hheap.
destruct Hheap as (bb & bm & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bb bm 1 pos HAR Hbin Hfin) as Hsep.
change (fs_frame_bytes 1) with 128 in *. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
unfold in_app in HFLapp, HFapp, Hbapp.
unfold seg_spec.SEG_M_SIZE in Hb2.
(* s1 = (sp0 - 320) & -32 *)
assert (Hs1u : mf_s1 (mv_sp v) = mv_sp v - 320 - (mv_sp v - 320) mod 32) by reflexivity.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as Hs1m.
destruct (mf_s1_facts B v CX) as (Hs1d & Hs32 & Hsc). rewrite HSTK in Hsc.
assert (Po16 : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0).
{ destruct Hs1d as [E1 | E1]; rewrite E1.
  - replace (mv_sp v - 320 - mv_sp v) with ((-20) * 16) by lia. apply Z_mod_mult.
  - replace (mv_sp v - 336 - mv_sp v) with ((-21) * 16) by lia. apply Z_mod_mult. }
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
set (nn := length (mc_seg mcc)) in *.
assert (Hnn : 0 <= Z.of_nat nn < 32) by lia.
set (g := seg_spec.mseg_addr (mv_c v) nn) in *.
assert (Hg : g = mv_c v + 256 * Z.of_nat nn) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; reflexivity).
(* the model: m_find found nothing and n < 32, so mh_find appends mseg0 nm and sets its gen *)
pose proof (hb_mh_find_new mcc nm (line + 1) HFIND H32) as HMN. cbv zeta in HMN. rewrite HMN in HFIN.
change (mc_gen (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm]))) with (mc_gen mcc) in HFIN.
assert (HL : length (mc_seg (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) nn (ms_with_gen (mc_gen mcc))))
  = S nn).
{ unfold m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length, length_app. cbn [length]. lia. }
assert (Hjl : (nn < length (mc_seg (mf_final v)))%nat).
{ rewrite <- HFIN.
  assert (Hst : mf_cur_ok (fst (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) nn (ms_with_gen (mc_gen mcc)),
    Some nn)) (snd (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) nn (ms_with_gen (mc_gen mcc)), Some nn))).
  { cbn [fst snd mf_cur_ok]. rewrite HL. lia. }
  destruct (hb_fin_grows _ line rest Hst) as [G _]. cbn [fst] in G. rewrite HL in G. exact G. }
(* ===================================== the seed at MFB_NEWE ===================================== *)
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Hcurok) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as Hnp.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] MFB_NEWE
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp
  ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] 9144 CX CORE
  ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as SHE.
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) [] 1 ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth mf_extra map app] in E32, E33.
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E34, E36.
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS0, SHE, E32, E33, E34, E36.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros; apply mfE_reg; assumption).
clearbody E.
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat nn)) by (rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity).
assert (E25 : ew E 25 = Z_to_bv 64 (mv_c v)) by (rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8).
{ rewrite E36. apply unsigned_lit_small.
  pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)). rewrite HSB. lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9144] E (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; apply Forall_cons; [exact SHE | apply Forall_nil]).
(* the frame cells read-only: this piece stores no frame cell *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS1 end.
clear HS0 HR1. hb7_norm HS1.
(* a1 = the shadow byte address of c->n, in the shape 0x86b04-0x86b08 formed it *)
apply (ast_ok_pi_set_reg_fp E _ _ (11%bv : bv 5) (mf_shx 33 seg_spec.MC_N)) in HS1;
  [| reflexivity | cbn [ms_regs restrict mkst]; rewrite R11;
     rewrite (mf_denot_shx E 33 (mv_c v) seg_spec.MC_N E33 E32) by (unfold seg_spec.MC_N; lia); reflexivity ].
hb7_norm HS1.
(* s6 = c + 0x2000, as the count cell's atom and offset *)
apply (ast_ok_pi_set_reg_fp E _ _ (22%bv : bv 5) (SOff 33 seg_spec.MC_N)) in HS1;
  [| reflexivity | cbn [ms_regs restrict mkst]; rewrite R22; unfold w64; rewrite denot_lit_U; f_equal;
     rewrite U_SOff, E33, (unsigned_lit_small (mv_c v)) by lia;
     rewrite zcanon_id by (unfold M64, seg_spec.MC_N; lia); unfold seg_spec.MC_N; reflexivity ].
hb7_norm HS1.
(* the count cell c->n, writable *)
assert (RN : region_ok SEGS E
  (ms_mem (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + MFB_NEWE)) memc (seg_rom SEGS))))
  (YP09.mkRegion (Some 33%nat) 8192 8196 8192 8196 [])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o' Ho'. cbn [restrict ms_mem mkst].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR Hbin) as (_ & _ & _ & _ & Hbp & _).
  apply (apresent_writable SEGS). exact (proj1 (Hbp (mv_c v + o') ltac:(lia))). }
assert (DN : all_disjoint E (YP09.mkRegion (Some 33%nat) 8192 8196 8192 8196 [])
  (ss_mem (ltac:(lazymatch type of HS1 with st_ok_pi _ _ _ ?ss _ => exact ss end)))).
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U33, ?U2, ?U8, ?U34, ?U36.
  pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)).
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. rewrite HSB. repeat split; first [exact I | lia]. }
pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 33%nat) 8192 8196 8192 8196 []) HS1
  ltac:(vm_compute; reflexivity) RN DN) as HS.
clear HS1 RN DN. hb7_norm HS.
unfold mf_at.
(* ===================================== run 1: 0x86b54 .. 0x86b68 =====================================
   the check of the store, c->n := n + 1, the UBSan bound test *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    - apply hb_fp_cnt. unfold seg_spec.MC_N, seg_spec.MC_REFUSED. lia.
    - exists bb, bm. split; [exact Hbin | lia]. }
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (md1 := d) in *; clearbody md1 end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mv_c v + 8192 <= a < mv_c v + 8196) ->
  rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha HnC.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms1) (fun x => mv_c v + 8192 <= x < mv_c v + 8196) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; lia] |]).
  destruct Hinw. }
clear HF HFr HG.
(* the trap 0x86b68 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- exfalso. rewrite (hb7_ub_b68 E 10 (Z.of_nat nn) E10 ltac:(lia)) in Hc. discriminate.
- (* ===================================== run 2: 0x86b6c .. 0x86b74 ===================================== *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
      let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
    eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
      - apply hb_fp_cnt. unfold seg_spec.MC_N, seg_spec.MC_REFUSED. lia.
      - exists bb, bm. split; [exact Hbin | lia]. }
    repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (md2 := d) in *; clearbody md2 end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mv_c v + 8192 <= a < mv_c v + 8196) ->
    rdW Wc (ms_mem ms2) a = rdW Wc (ms_mem ms1) a).
  { intros a Ha HnC.
    refine (kept_of_frame E _ (w_H Wc) (ms_mem ms1) (ms_mem ms2)
      (fun x => mv_c v + 8192 <= x < mv_c v + 8196) HFr _ a Ha HnC).
    intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
    repeat (destruct Hinw as [Hq | Hinw];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; lia] |]).
    destruct Hinw. }
  clear HF HFr HG.
  (* the trap 0x86b74 *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + exfalso.
    lazymatch goal with H : branch_taken BC_LTU _ _ = true |- _ =>
      rewrite (hb7_ub_b74 E 33 10 (mv_c v) (Z.of_nat nn) E33 E10 ltac:(lia) ltac:(lia) ltac:(lia)) in H;
      discriminate end.
  + (* ============================ run 3: 0x86b78 .. 0x86b88, into the memset ============================ *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
        let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
      eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
      { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
        - apply hb_fp_cnt. unfold seg_spec.MC_N, seg_spec.MC_REFUSED. lia.
        - exists bb, bm. split; [exact Hbin | lia]. }
      repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
    lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (md3 := d) in *; clearbody md3 end.
    lazymatch type of HS with
    | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3
    | st_ok _ _ _ (restrict _ ?m) => rename m into ms3
    end.
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mv_c v + 8192 <= a < mv_c v + 8196) ->
      rdW Wc (ms_mem ms3) a = rdW Wc (ms_mem ms2) a).
    { intros a Ha HnC.
      refine (kept_of_frame E _ (w_H Wc) (ms_mem ms2) (ms_mem ms3)
        (fun x => mv_c v + 8192 <= x < mv_c v + 8196) HFr _ a Ha HnC).
      intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
      repeat (destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; lia] |]).
      destruct Hinw. }
    clear HF HFr HG.
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (mv_c v + 8192 <= a < mv_c v + 8196) ->
      rdW Wc (ms_mem ms3) a = rdW Wc memc a).
    { intros a Ha Hn0. rewrite (K3 a Ha Hn0), (K2 a Ha Hn0). exact (K1 a Ha Hn0). }
    (* c->n = n + 1 at the run's memory *)
    assert (VN : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms3)) (mv_c v + 8192) 4 (Z.of_nat nn + 1)).
    { pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
      pose proof (field_of_region_any E _ 33 (mv_c v) _ 8192 8196 8192 8196 8192 4%N (SOff 10 1) HR0 U33
        ltac:(cbn [YP09.r_chunks In]; tauto) ltac:(cbn; lia)) as V.
      change (N.to_nat 4) with 4%nat in V.
      replace (bv_unsigned (sv_denot E (SOff 10 1)) mod 2 ^ (8 * Z.of_N 4)) with (Z.of_nat nn + 1) in V; [exact V|].
      change (bv_unsigned (sv_denot E (SOff 10 1))) with (U E (SOff 10 1)). rewrite U_SOff, E10.
      rewrite unsigned_lit_small by lia.
      rewrite zcanon_id by (unfold M64; lia). rewrite Z.mod_small; [reflexivity | cbn; lia]. }
    pose proof HJ as (HART & _).
    pmkst HS.
    hb7_reg HS (10%bv : bv 5) Q10. hb7_reg HS (21%bv : bv 5) Q21.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
    prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    (* a0 = s5 = g = c + 256 n *)
    assert (P10 : getr (ms_regs ms3) 10 = w64 g).
    { rewrite Q10. unfold w64. rewrite denot_lit_U. f_equal.
      rewrite U_SAlu, (hb7_U_sll8 E 10 (Z.of_nat nn) E10 ltac:(lia)), U_SOff, E25.
      rewrite (unsigned_lit_small (mv_c v)) by lia.
      cbn [zalu_raw]. rewrite (zcanon_id (mv_c v + 0)) by (unfold M64; lia).
      rewrite zcanon_id by (unfold M64; lia). rewrite Hg. lia. }
    assert (P21 : getr (ms_regs ms3) 21 = w64 g) by (rewrite Q21, <- Q10; exact P10).
    (* the registers of every cut are kept *)
    assert (RAT : mf_regs_at B v lyc pos (ms_regs ms3)).
    { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms3) RA).
      - rewrite Q2. apply EE. reflexivity.
      - rewrite Q3. apply EE. reflexivity.
      - rewrite Q4. apply EE. reflexivity.
      - rewrite Q8. apply EE. reflexivity.
      - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
      - rewrite Q18, E32, R18. reflexivity.
      - rewrite Q23. apply EE. reflexivity.
      - rewrite Q24. apply EE. reflexivity.
      - rewrite Q19. apply EE. reflexivity.
      - rewrite Q22, R22, E33, (unsigned_lit_small (mv_c v)) by lia.
        first [reflexivity | unfold w64, seg_spec.MC_N; reflexivity].
      - rewrite Q25. apply EE. reflexivity. }
    assert (Qsp : spZ (ms_regs ms3) = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)).
    { unfold spZ. rewrite Q2, (EE 2%nat 2%bv eq_refl), R2. unfold w64.
      rewrite unsigned_lit_small by lia. lia. }
    (* ===================================== 0x86b88: the checked memset ===================================== *)
    eapply SRr_bind.
    { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA SS___asan_memset) (AMEMSET fx) Wc (ms_regs ms3)
        (ms_mem ms3) SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
        (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc md3 0 g 0 256
        (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + MFB_RMSET)) HJ).
      - exact P10.
      - rewrite Q11. reflexivity.
      - rewrite Q12. reflexivity.
      - lia.
      - lia.
      - lia.
      - exact Qsp.
      - exact Po16.
      - lia.
      - unfold ESTACK. rewrite HSTK. lia.
      - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact R3.
      - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact R4.
      - rewrite Q1. unfold MFB_RMSET. reflexivity.
      - apply ret_ok_codeptr_v; [unfold MFB_RMSET, AF_m_file; lia | reflexivity].
      - intros a Ha. split.
        + exact (proj1 (hb3_entry_wr B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc nn a CX CORE Hjl H32 Ha)).
        + unfold ESTACK. lia.
      - intros a Ha _ _. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HART Hbin) as (_ & _ & _ & _ & Hbp & _).
        apply (apresent_writable SEGS). exact (proj1 (Hbp a ltac:(lia))).
      - apply (amem_range_of_block SEGS B LAWS _ _ _ _ _ bb bm g 256 HART Hbin); lia.
      - apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bb bm g 256 HART Hbin); lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bb bm g 256 HART Hbin); lia.
      - exact I. }
    cbv beta. intros W3 c3 _ (-> & regs2 & mem2 & md4 & -> & HJ2 & HP2 & _ & HSET & HKEEP2 & _ & _).
    cbv beta iota in HSET.
    (* every byte outside the count cell, the entry and the call's window is kept *)
    assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - 4096 <= a < mf_s1 (mv_sp v)) ->
      ~ ((mv_c v + 8192 <= a < mv_c v + 8196) \/ (g <= a < g + 256)) -> rdW Wc mem2 a = rdW Wc memc a).
    { intros a Ha HnW HnE.
      rewrite HKEEP2; [| exact Ha | intros Hq; apply HnE; right; exact Hq | unfold ESTACK; lia].
      apply K; [exact Ha | intros Hq; apply HnE; left; exact Hq]. }
    (* the block holds the model with one more entry, the empty one *)
    assert (MC' : sa_mconf (rdW Wc mem2) (mv_c v) (m_set_segs mcc (mc_seg mcc ++ [mseg0 []]))).
    { destruct HMC as (BS & HBS & HENC).
      pose proof (mconf_enc_bounds _ _ _ HENC) as (HBSl & _).
      assert (HLB : Z.of_nat (length BS) = 9236) by (rewrite HBSl; reflexivity). clear HBSl.
      assert (HKN : Z.of_nat (Z.to_nat seg_spec.MC_N) = 8192) by reflexivity.
      set (L4 := Mem.le4 (Z_to_bv 64 (Z.of_nat nn + 1))).
      assert (HL4 : length L4 = 4%nat) by apply Mem.length_le4.
      assert (KL : (Z.to_nat seg_spec.MC_N + length L4 <= length BS)%nat).
      { apply (proj2 (Nat2Z.inj_le _ _)). rewrite Nat2Z.inj_add, HKN, HLB, HL4. cbn. lia. }
      assert (KE : (256 * nn + length (repeat seg_spec.ZERO 256) <= Z.to_nat seg_spec.MC_N)%nat).
      { apply (proj2 (Nat2Z.inj_le _ _)). rewrite Nat2Z.inj_add, Nat2Z.inj_mul, HKN, repeat_length.
        change (Z.of_nat 256) with 256. lia. }
      pose proof (mconf_enc_append false mcc BS (mseg0 []) (repeat seg_spec.ZERO 256) HENC H32 hb_mseg_enc_zero) as ENC'.
      fold nn L4 in ENC'.
      rewrite <- (hb7_upd_comm BS (repeat seg_spec.ZERO 256) L4 (256 * nn) (Z.to_nat seg_spec.MC_N) KE KL) in ENC'.
      eexists. split; [|exact ENC'].
      assert (HBS1 : sa_bytes (rdW Wc (ms_mem ms3)) (mv_c v) (Mem.upd_bytes BS (Z.to_nat seg_spec.MC_N) L4)).
      { apply (hb_bytes_upd (rdW Wc memc) (rdW Wc (ms_mem ms3)) (mv_c v) BS (Z.to_nat seg_spec.MC_N));
          [exact HBS | | exact KL |].
        - rewrite HKN. apply hb_bytes_of_val; [lia|].
          exact (hb7_sa_val (w_H Wc) (ms_mem ms3) (mv_c v + 8192) 4 (Z.of_nat nn + 1) VN).
        - intros a Ha HnC. rewrite HKN, HL4 in HnC. rewrite HLB in Ha.
          apply K; [lia | change (Z.of_nat 4) with 4 in HnC; lia]. }
      assert (HLn : length (Mem.upd_bytes BS (Z.to_nat seg_spec.MC_N) L4) = length BS)
        by (apply Mem.upd_bytes_length; exact KL).
      apply (hb_bytes_upd (rdW Wc (ms_mem ms3)) (rdW Wc mem2) (mv_c v) _ (256 * nn)); [exact HBS1 | | |].
      - replace (mv_c v + Z.of_nat (256 * nn)) with g
          by (rewrite Nat2Z.inj_mul; change (Z.of_nat 256) with 256; lia).
        apply hb7_zero256. exact HSET.
      - rewrite HLn. apply (proj2 (Nat2Z.inj_le _ _)). rewrite Nat2Z.inj_add, Nat2Z.inj_mul, HLB, repeat_length.
        change (Z.of_nat 256) with 256. lia.
      - intros a Ha HnG. rewrite repeat_length, Nat2Z.inj_mul in HnG. rewrite HLn, HLB in Ha.
        change (Z.of_nat 256) with 256 in HnG.
        apply HKEEP2; [lia | lia | unfold ESTACK; lia]. }
    destruct (mf_keep_art B v lyc Sc Wc (ms_regs ms3) memc mdc pos MF_LOW_OFF mcc cur regs2 mem2 md4
      (mf_s1 (mv_sp v) - 4096) (mf_s1 (mv_sp v))
      (fun a => (mv_c v + 8192 <= a < mv_c v + 8196) \/ (g <= a < g + 256))
      (m_set_segs mcc (mc_seg mcc ++ [mseg0 []]))
      CX CORE CELLS RAT HJ2 HP2 ltac:(rewrite HSTK; lia) ltac:(lia) KW
      ltac:(intros a [Ha | Ha]; unfold seg_spec.SEG_M_SIZE; lia) MC')
      as (CORE' & CELLS' & RA' & NPK & LOOPK).
    (* 192(s1) is neither in the call's window nor in the block *)
    assert (S192' : mf_slot v mem2 Wc 192 (p + Z.of_nat o)).
    { unfold mf_slot in S192 |- *.
      apply (hb7_val_keep Wc Wc memc mem2 _ 8 _); [|exact S192].
      intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KW; [lia | lia|].
      intros [Hq | Hq]; lia. }
    (* s5, s10 and s11 are callee-saved: the checked memset keeps them *)
    assert (R21' : getr regs2 21 = w64 g)
      by (transitivity (getr (ms_regs ms3) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact P21]).
    assert (R26' : getr regs2 26 = w64 (Z.of_nat (length nm))).
    { transitivity (getr (ms_regs ms3) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia))|].
      rewrite Q26, (EE 26%nat 26%bv eq_refl). exact R26. }
    assert (R27' : getr regs2 27 = w64 (line + 1)).
    { transitivity (getr (ms_regs ms3) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia))|].
      rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27. }
    (* ===================================== 0x86b8c: MFB_RMSET ===================================== *)
    apply (RMSET v lyc Sc Wc regs2 mem2 md4 pos mcc mcc cur line p rest o nm CX LS FRM CORE' CELLS' RA').
    * exact Hlen.
    * exact Hne.
    * exact (LOOPK _ _ _ _ _ LOOP).
    * exact (hb4_mod_head_of (mv_k0 v) mcc cur Hcurok Hk0).
    * exact HNM.
    * exact H32.
    * apply hb7_zero256. exact HSET.
    * exact HFIN.
    * exact R21'.
    * exact S192'.
    * exact R26'.
    * exact R27'.
    * exact (NPK _ NP).
Qed.

End e.
End f.
End d.

(* ============================ the same statement at every FP state ============================
   the checked memset keeps the FP state *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
Lemma hb7_newe : forall n, MFB_RMSET_F B n -> MFB_NEWE_F B n.
Proof. intros n RMSET fx0. exact (hb7_body (fx := fx0) B VOBJS AMEMSET n (RMSET fx0)). Qed.
End i.
End h.
End g.

About hb7_newe.
Print Assumptions hb7_newe.
