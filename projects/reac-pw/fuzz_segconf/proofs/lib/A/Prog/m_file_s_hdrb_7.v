(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 316 of its 359 lines of code are new or changed and 410 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), the segment S_MF_HDRB (MF-CUTS-A.md section 4): the new entry's
   own code, from the inner cut MFH_NEWE 0x86bfc to the inner cut MFH_RMSET 0x86c30 (m_file_s_hdrb_2.v). Lane
   the HDRB segment lane of the G2 walk owner's G2, piece the HDRB new-entry sub-lane. `hb7_newe : forall n, MFH_RMSET_F B n -> MFH_NEWE_F B n`.

   THE CODE (listing dis/m_file.fuzz_segconf.asan.s):
     0x86bfc `mv s7,s6`             s7 := line + 1
     0x86c00 `lb a1,0(a1)`, `bnez`  the instrumented check (a load of the shadow byte at ((c + 0x2000) >> 3) + the
                                    shadow base, which 0x86b90-0x86b94 left in a1, and a compare) of the 4-byte store
                                    at c + 0x2000; the slow path 0x86e30-0x86e3c rejoins at 0x86c08 or reaches the
                                    error path (a call of an errpath_* entry, 0x87038), which the proof shows is not
                                    reached
     0x86c08 .. 0x86c14             a1 := n + 1, a0 := 256 n, a2 := 88(s1) = c + 0x2000, `sw` c->n := n + 1
     0x86c18 .. 0x86c28             s6 := 128(s1) = c, s11 := c + 256 n = &c->seg[n], a0 := s11, a1 := 0, a2 := 256
     0x86c2c `jal`                  the checked memset entry: memset(&c->seg[n], 0, 256), back at 0x86c30

   THE PROOF. m_file_sd.v's mf_seed at MFH_NEWE (the cells and 144(s1) as chunks), the spill slots made read-only
   (nothing here stores a slot), a1 re-shaped to mf_shx 33 MC_N (its denotation is the statement's
   SHADOW_OFF + (c + MC_N) / 8, mf_denot_shx) so the token executor reads the load at 0x86c00 as a check, a
   writable region of the count cell [c + 0x2000, c + 0x2004) at atom 33, and mf_she_blk's shadow entry of the block
   (hi = 9144), which decides the check. One token run (paj_run_tok) goes to the memset entry with the jal done;
   its one store is in M_FILE_FP (hb_fp_cnt) and in the live block (awr_ok). kept_of_frame: the run changed the count
   cell only; its final region gives c->n = n + 1. The call is aj_intrin_atS (OSet) under the Section hypothesis
   AMEMSET; its destination facts come from AR at the run's final state (amem_range / range_addressable /
   shadow_hull_vis _of_block, the block's bytes present hence writable) and from m_file_s_hdrb_3.v's hb3_entry_wr
   (awr_byte: in M_FILE_FP since n < |seg| of the final model, hb_fin_grows). After it: m_file_k.v's mf_keep_art
   carries the cut facts (the bytes outside the count cell, the entry and the call's window below s1 are kept); the
   block's bytes are the entry's bytes BS with the count and the 256 zero bytes written (hb_bytes_upd twice), which
   encode m_set_segs mcc (mc_seg mcc ++ [mseg0 []]) by mconf_enc_append and hb_mseg_enc_zero, after hb7_upd_comm
   reorders the two writes; the model equation is hb_mh_find_new. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_mdl m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_hdrb_1 m_file_s_hdrb_2 m_file_s_hdrb_3 m_file_s_hdrb_4.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* two writes at disjoint offsets commute; the statement of hb_upd_comm, the plain / image-B owner's plain lib/Prog/mf_line_hdrb.v:141
   at commit bdb945544a62. mconf_enc_append (m_file_s_hdrb_1.v) writes the entry first and the
   count second; the code stores the count (0x86c14) before the memset of the entry (0x86c2c). *)
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
(* a register of a run's final state, its denotation not normalized (prreg without prreg_norm) *)
Ltac hb7_reg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

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

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.

Lemma hb7_newe_at : forall n, MFH_RMSET_stmt B n -> MFH_NEWE_stmt B n.
Proof.
intros n RMSET. unfold MFH_NEWE_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest o nm CX LS FRM CORE CELLS RA R24 Hn Hne LOOP HNM HFIND
  H32 MOD R10 R11 R21 R20 R22 NP.
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V112 & HMC & HAD & HTL).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & Hheap0 & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in Hslo.
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
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (hb_mconf_bounds _ _ _ HMC) as (HB32 & _).
pose proof LOOP as (_ & _ & _ & HLstr & HLad & Hcurok & Hk0 & _).
pose proof HLad as (HLp0 & HLp63 & _).
set (sp0 := mv_sp v) in *. set (c := mv_c v) in *. set (F := frame_addr lyc 1 pos) in *.
set (s1 := mf_s1 sp0) in *. set (nn := length (mc_seg mcc)) in *.
unfold mv_sp in sp0. fold sp0 in Hstk, Hal16, Hslo, Hshi.
assert (Hs1 : s1 = sp0 - 288 - sp0 mod 32 /\ (sp0 mod 32 = 0 \/ sp0 mod 32 = 16)).
{ unfold s1, mf_s1. replace ((sp0 - 288) mod 32) with (sp0 mod 32)
    by (rewrite Zminus_mod; change (288 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  split; [reflexivity|]. pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)).
  pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
destruct Hs1 as [Hs1a Hs1b].
unfold seg_spec.SEG_M_SIZE in Hb2.
assert (Hcur : 0 <= mf_cur_ptr c cur < 2 ^ 64).
{ destruct cur as [i|]; cbn [mf_cur_ptr]; [|lia]. cbn [mf_cur_ok] in Hcurok. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia. }
assert (Hnp : 0 <= mf_next p rest < 2 ^ 64) by (unfold mf_next; lia).
(* the seed at NEWE, the cells and 144(s1) *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] MFH_NEWE true true []
  false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (SHE : shent_ok SEGS (SOff 32 0) E (mrestrict (w_H Wc) memc) (mkSHE 33 0 9144))
  by (subst E; apply (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc); [exact CX | exact CORE | unfold seg_spec.SEG_M_SIZE; lia]).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold c F in E33, E34, E36.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (U2 : bv_unsigned (ew E 2) = s1)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = sp0)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + F / 8)
  by (rewrite E36; apply unsigned_lit_small; rewrite HSB; pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)); pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
(* the spill slots read-only: this piece stores no slot *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS1 end.
clear HS0 HR1. hb7_norm HS1.
(* a1 = the shadow byte address of c->n, in the shape 0x86b90-0x86b94 formed it *)
apply (ast_ok_pi_set_reg_fp E _ _ (11%bv : bv 5) (mf_shx 33 seg_spec.MC_N)) in HS1;
  [| reflexivity | cbn [ms_regs restrict mkst]; rewrite R11;
     rewrite (mf_denot_shx E 33 c seg_spec.MC_N E33 E32) by (unfold seg_spec.MC_N; lia); reflexivity ].
hb7_norm HS1.
(* the count cell c->n, writable *)
assert (HS2 := st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 33%nat) 8192 8196 8192 8196 []) HS1
  ltac:(vm_compute; reflexivity)).
clear HS1.
lapply HS2; clear HS2; [intros HS2|].
2:{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o' Ho'. cbn [restrict ms_mem mkst].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR Hbin) as (_ & _ & _ & _ & Hbp & _).
    apply (apresent_writable SEGS). exact (proj1 (Hbp (c + o') ltac:(lia))). }
lapply HS2; clear HS2; [intros HS2|].
2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U33, ?U2, ?U8, ?U34, ?U36.
    pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. rewrite HSB. repeat split; first [exact I | lia]. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9144] E (mrestrict (w_H Wc) memc)) by (constructor; [exact SHE | constructor]).
(* the model: m_find found nothing and n < 32, so mh_find appends mseg0 nm and sets its gen *)
pose proof (hb_mh_find_new mcc nm (line + 1) HFIND H32) as HMN. cbv zeta in HMN. rewrite HMN in MOD.
change (mc_gen (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm]))) with (mc_gen mcc) in MOD.
assert (Enn : nn = length (mc_seg mcc)) by reflexivity.
assert (Ec : c = mv_c v) by reflexivity. assert (Esp0 : sp0 = mv_sp v) by reflexivity.
assert (Es1 : s1 = mf_s1 (mv_sp v)) by reflexivity. assert (EF : F = frame_addr lyc 1 pos) by reflexivity.
assert (HL : length (mc_seg (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) nn (ms_with_gen (mc_gen mcc))))
  = S nn).
{ unfold m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length, length_app. cbn [length]. lia. }
assert (Hjl : (nn < length (mc_seg (mf_final v)))%nat).
{ rewrite <- MOD.
  assert (Hst : mf_cur_ok (fst (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) nn (ms_with_gen (mc_gen mcc)),
    Some nn)) (snd (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) nn (ms_with_gen (mc_gen mcc)), Some nn))).
  { cbn [fst snd mf_cur_ok]. rewrite HL. lia. }
  destruct (hb_fin_grows _ line rest Hst) as [G _]. cbn [fst] in G. rewrite HL in G. exact G. }
set (g := seg_spec.mseg_addr c nn) in *.
assert (Hg : g = c + 256 * Z.of_nat nn) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; reflexivity).
unfold mf_at.
(* 0x86bfc .. 0x86c2c: s7 = line + 1, the check of c->n, c->n = n + 1, s11 = g = c + 256 n, the arguments of the
   checked memset, and the jal *)
paj_run_tok RUN HS2 HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat c); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    - apply hb_fp_cnt. unfold seg_spec.MC_N, seg_spec.MC_REFUSED. lia.
    - exists bb, bm. split; [exact Hbin | lia]. }
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
(* the run wrote the count cell only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8192 <= a < c + 8196) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnC. refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms) (fun x => c + 8192 <= x < c + 8196) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; lia] |]).
  destruct Hinw. }
(* c->n = n + 1 *)
assert (VN : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (c + 8192) 4 (Z.of_nat nn + 1)).
{ pose proof (st_ok_region_nth E _ _ 0 _ HS2 eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
  pose proof (field_of_region_any E _ 33 c _ 8192 8196 8192 8196 8192 4%N (SOff 10 1) HR0 U33
    ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V.
  change (N.to_nat 4) with 4%nat in V.
  replace (bv_unsigned (sv_denot E (SOff 10 1)) mod 2 ^ (8 * Z.of_N 4)) with (Z.of_nat nn + 1) in V; [exact V|].
  change (bv_unsigned (sv_denot E (SOff 10 1))) with (U E (SOff 10 1)). rewrite U_SOff.
  rewrite (EE 10%nat 10%bv eq_refl), R10. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite zcanon_id by (unfold M64; lia). rewrite Z.mod_small; [reflexivity | cbn; lia]. }
pmkst HS2.
prreg HS2 (1%bv : bv 5) Q1. prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4.
prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (11%bv : bv 5) Q11. prreg HS2 (12%bv : bv 5) Q12.
prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (21%bv : bv 5) Q21.
prreg HS2 (22%bv : bv 5) Q22. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (25%bv : bv 5) Q25.
prreg HS2 (26%bv : bv 5) Q26.
hb7_reg HS2 (10%bv : bv 5) Q10. hb7_reg HS2 (27%bv : bv 5) Q27.
(* s11 = a0 = c + 256 n, no wrap *)
assert (G10 : sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 8)) (SOff 33 0)) = Z_to_bv 64 g).
{ rewrite denot_lit_U. f_equal. rewrite !U_SAlu, U_SLit, !U_SOff.
  rewrite (EE 10%nat 10%bv eq_refl), R10, E33. unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  cbn [zalu_raw]. rewrite (zcanon_id 8) by (unfold M64; lia). change (Z.land 8 63) with 8.
  rewrite (zcanon_id (Z.of_nat nn)) by (unfold M64; lia). rewrite (zcanon_id c) by (unfold M64; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite (zcanon_id (Z.of_nat nn * 256)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). rewrite Hg. lia. }
rewrite G10 in Q10, Q27.
assert (RAT : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity.
  - rewrite Q26. apply EE. reflexivity. }
assert (Qsp : spZ (ms_regs ms) = sp0 + (s1 - sp0)) by (unfold spZ; rewrite Q2, U2; lia).
pose proof (hb3_heap_now B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc _ _ CORE Hheap0) as (bc & mc & Hbc & Hbc1 & Hbc2).
pose proof HJ as (HART & _).
(* 0x55d7c, the checked memset entry: memset(g, 0, 256), back at 0x86c30 = MFH_RMSET *)
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA SS___asan_memset) (AMEMSET fx) Wc (ms_regs ms) (ms_mem ms)
    SegInstA.STK_m_file sp0 (M_FILE_FP c (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v)
    [(1, pos)] lyc Sc mdw 0 g 0 256 (s1 - sp0) (Z_to_bv 64 (BASE + MFH_RMSET)) HJ).
  - exact Q10.
  - rewrite Q11. reflexivity.
  - rewrite Q12. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact Qsp.
  - replace (s1 - sp0) with (- (288 + sp0 mod 32)) by lia. destruct Hs1b as [-> | ->]; reflexivity.
  - lia.
  - rewrite HSTK. unfold ESTACK. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact R3.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact R4.
  - rewrite Q1. unfold MFH_RMSET. reflexivity.
  - apply ret_ok_codeptr_v; [unfold MFH_RMSET, AF_m_file; lia | reflexivity].
  - intros a Ha. split.
    + exact (proj1 (hb3_entry_wr B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc nn a CX CORE Hjl H32 Ha)).
    + unfold ESTACK. lia.
  - intros a Ha _ _. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HART Hbin) as (_ & _ & _ & _ & Hbp & _).
    apply (apresent_writable SEGS). exact (proj1 (Hbp a ltac:(lia))).
  - apply (amem_range_of_block SEGS B LAWS _ _ _ _ _ bb bm g 256 HART Hbin); lia.
  - apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bb bm g 256 HART Hbin); lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bb bm g 256 HART Hbin); lia.
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HSET & HKEEP2 & _ & _).
cbv beta iota in HSET.
(* every byte outside the count cell, the entry and the call's window is kept *)
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 - 4096 <= a < s1) ->
  ~ ((c + 8192 <= a < c + 8196) \/ (g <= a < g + 256)) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha HnW HnE. rewrite HKEEP2; [| exact Ha | intros Hq; apply HnE; right; exact Hq | unfold ESTACK; lia].
  apply K1; [exact Ha | intros Hq; apply HnE; left; exact Hq]. }
(* the block holds the model with one more entry, the empty one *)
assert (MC' : sa_mconf (rdW Wc mem2) c (m_set_segs mcc (mc_seg mcc ++ [mseg0 []]))).
{ destruct HMC as (BS & HBS & HENC).
  pose proof (mconf_enc_bounds _ _ _ HENC) as (HBSl & _).
  (* the offsets in Z: lia does not read the nat numerals 8192 and 9236 *)
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
  assert (HBS1 : sa_bytes (rdW Wc (ms_mem ms)) c (Mem.upd_bytes BS (Z.to_nat seg_spec.MC_N) L4)).
  { apply (hb_bytes_upd (rdW Wc memc) (rdW Wc (ms_mem ms)) c BS (Z.to_nat seg_spec.MC_N)); [exact HBS | | exact KL |].
    - rewrite HKN. apply hb_bytes_of_val; [lia|].
      exact (hb7_sa_val (w_H Wc) (ms_mem ms) (c + 8192) 4 (Z.of_nat nn + 1) VN).
    - intros a Ha HnC. rewrite HKN, HL4 in HnC. rewrite HLB in Ha.
      apply K1; [lia | change (Z.of_nat 4) with 4 in HnC; lia]. }
  assert (HL1 : length (Mem.upd_bytes BS (Z.to_nat seg_spec.MC_N) L4) = length BS) by (apply Mem.upd_bytes_length; exact KL).
  apply (hb_bytes_upd (rdW Wc (ms_mem ms)) (rdW Wc mem2) c _ (256 * nn)); [exact HBS1 | | |].
  - replace (c + Z.of_nat (256 * nn)) with g by (rewrite Nat2Z.inj_mul; change (Z.of_nat 256) with 256; lia).
    apply hb7_zero256. exact HSET.
  - rewrite HL1. apply (proj2 (Nat2Z.inj_le _ _)). rewrite Nat2Z.inj_add, Nat2Z.inj_mul, HLB, repeat_length.
    change (Z.of_nat 256) with 256. lia.
  - intros a Ha HnG. rewrite repeat_length, Nat2Z.inj_mul in HnG. rewrite HL1, HLB in Ha.
    change (Z.of_nat 256) with 256 in HnG.
    apply HKEEP2; [lia | lia | unfold ESTACK; lia]. }
destruct (mf_keep_art B v lyc Sc Wc (ms_regs ms) memc mdc pos MF_LOW_OFF mcc cur regs2 mem2 md2 (s1 - 4096) s1
  (fun a => (c + 8192 <= a < c + 8196) \/ (g <= a < g + 256)) (m_set_segs mcc (mc_seg mcc ++ [mseg0 []]))
  CX CORE CELLS RAT HJ2 HP2 ltac:(rewrite HSTK; lia) ltac:(lia) KW ltac:(intros a [Ha | Ha]; unfold seg_spec.SEG_M_SIZE; lia) MC')
  as (CORE' & CELLS' & RA' & NPK & LOOPK).
(* s4, s5, s6, s7, s8, s11 are callee-saved: the checked memset keeps them *)
assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23 = getr (ms_regs ms) 23) by exact (HP2 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
apply (RMSET v lyc Sc Wc regs2 mem2 md2 pos mcc mcc cur line p rest o nm CX LS FRM CORE' CELLS' RA').
- rewrite P24, Q24, (EE 24%nat 24%bv eq_refl). exact R24.
- exact Hn.
- exact Hne.
- exact (LOOPK _ _ _ _ _ LOOP).
- unfold hb_mod. split; [exact Hcurok|]. split; [exact Hk0|]. lia.
- exact HNM.
- exact H32.
- apply hb7_zero256. exact HSET.
- exact MOD.
- rewrite P27, Q27. reflexivity.
- rewrite P21, Q21, (EE 21%nat 21%bv eq_refl). exact R21.
- rewrite P20, Q20, (EE 20%nat 20%bv eq_refl). exact R20.
- rewrite P22, Q22, E33. reflexivity.
- rewrite P23, Q23, (EE 22%nat 22%bv eq_refl). exact R22.
- exact (NPK _ NP).
Qed.

End e.
End f.
End d.

(* at every FP state (m_file_s_hdrb_2.v's _F forms): the checked memset keeps the FP state *)
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
Lemma hb7_newe : forall n, MFH_RMSET_F B n -> MFH_NEWE_F B n.
Proof. intros n RMSET fx0. exact (hb7_newe_at (fx := fx0) B VOBJS AMEMSET n (RMSET fx0)). Qed.
End i.
End h.
End g.

About hb7_newe.
Print Assumptions hb7_newe.
