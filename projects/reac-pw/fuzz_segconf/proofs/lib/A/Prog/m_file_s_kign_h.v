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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 418 of its 463 lines of code are new or changed and 408 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), segment S_MF_KIGNP, piece ki_s_hit: the hit path of the ignore
   key, KI_HIT 0x869e8 (lib/A/Prog/m_file_s_kign_m.v) to KDONE 0x86cd0. The KIGNP segment lane of the G2 walk owner's G2, sub-lane
   the KIGNP hit sub-lane. proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's KI_HIT piece).

   THE CODE (listing m_file.fuzz_segconf.asan.s lines 717-739):
     0x869e8-0x869f8 the check of g->ignore (a3 = g = &c->seg[gi]; store4, slow path 0x86da0); 0x869fc g->ignore = s6
     0x86a00-0x86a14 the check of g->ignore_set (store4, slow path 0x86db0), s5 = 128(s1) = c
     0x86a18-0x86a1c g->ignore_set = 1
     0x86a20-0x86a30 a0 = g + 156, a2 = "%s" (object 14), a1 = 96, a3 = 64(s1) = &c->reading
     0x86a34 jal snprintf (m_file_sn.v mf_snp_field_call)
     0x86a38 s6 = s8 = line + 1; 0x86a3c s8 = 104(s1) = FAKE; 0x86a40 j 0x86cd0 (KDONE).
   THE PROOF: ki_hit_run, one seed (m_file_sd.v mf_seed) with the slot region made read-only, a3 pinned to atom 37
   (the 136(s1) value g), g's 8 bytes [24, 32) at atom 37 (written), the fact HPTR 4 on atom 37 and the shadow entry
   mkSHE 37 0 40 (the executor's `covered` asks 28 + 8 <= the entry's end); one token run to the snprintf call.
   ki_ret_kdone: the three instructions at 0x86a38 from KDONE's statement, at any FP state (a second seed, the slots
   read-only). ki_s_hit joins them with snprintf's step: the block holds m_upd mcc gi (ms_with_ignore b reading)
   (m_file_s_kign_e.v ki_e_mconf_ign), the cut facts are carried by m_file_k.v's mf_keep_art (the callee window
   [s1 - CMD_SNP_K, s1), the stored bytes and the file string inside the block), the loop moves to the next line
   (mf_loop_next), and KDONE's statement is taken at the FP state fx1 the call returns. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_mdl m_file_sd m_file_k m_file_sn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_kign_t m_file_s_kign_m m_file_s_kign_e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x86a38, snprintf's return: `mv s6,s8` *)
Definition KI_RET : Z := AF_m_file + 0xb7c.

(* c->reading as sa_mconf holds it: a C string of fewer than 96 bytes, its bytes and NUL at c + MC_READING *)
Lemma ki_h_reading : forall (rd : reader) c mc, sa_mconf rd c mc ->
  sa_zs rd (c + seg_spec.MC_READING) (mc_reading mc ++ [0]) /\ (length (mc_reading mc) < 96)%nat /\
  ~ In 0 (mc_reading mc).
Proof.
intros rd c mc (bs & HB & HE).
destruct HE as (HL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hf & Hlt & Hn0 & Hfz)).
unfold seg_spec.SEG_M_SIZE in HL. unfold seg_spec.fldz, seg_spec.fld in Hf, Hfz.
set (o := Z.to_nat seg_spec.MC_READING) in *. set (k := Z.to_nat 96) in *.
assert (Ho : Z.of_nat o = seg_spec.MC_READING) by (unfold o; apply Z2Nat.id; unfold seg_spec.MC_READING; lia).
assert (Hk : Z.of_nat k = 96) by (unfold k; apply Z2Nat.id; lia).
split; [|split; [exact Hlt | exact Hn0]].
intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
replace (c + seg_spec.MC_READING + Z.of_nat j) with (c + Z.of_nat (o + j)) by (rewrite Nat2Z.inj_add, Ho; lia).
unfold seg_spec.MC_READING in Ho.
rewrite HB by lia. f_equal.
rewrite <- Hfz. rewrite ki_e_nth_firstn by lia. unfold seg_spec.zs.
rewrite nth_indep with (d' := bv_unsigned ZB0)
  by (rewrite length_map, length_firstn, length_skipn; apply Nat.min_glb_lt; lia).
rewrite map_nth, ki_e_nth_firstn by lia. rewrite ki_e_nth_skipn. reflexivity.
Qed.

(* n bytes of the restricted memory read through the ASan reader *)
Lemma ki_sa_of_val : forall segs H mem a n v,
  val_mem segs (mrestrict H mem) a n v -> sa_val (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* the run's regions: g's ignore and ignore_set at atom 37 (written), the slots read-only; the shadow entry of g's
   first 40 bytes *)
Definition ki_g : YP09.region := YP09.mkRegion (Some 37%nat) 24 32 24 32 [].
Definition ki_slots : YP09.region := YP09.mkRegion (Some 2%nat) 24 160 24 24 (mf_chunk112 :: mf_cell_chunks).
Definition ki_SH : list shent := [mkSHE 37 0 40].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* an atom holding x, as a symbolic value *)
Lemma ki_atom_val : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n x k Hn Hx. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by exact Hx. reflexivity. Qed.
(* a register whose symbolic value is atom n + k, or a literal *)
Lemma ki_reg : forall E ss (H : word -> bool) ms (r : bv 5) n k,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n k ->
  getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n) + k).
Proof. intros E ss H ms r n k HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.
Lemma ki_reg_lit : forall E ss (H : word -> bool) ms (r : bv 5) z,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros E ss H ms r z HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.
Lemma ki_reg_pi : forall E ss (H : word -> bool) ms (r : bv 5) n k,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n k ->
  getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n) + k).
Proof. intros E ss H ms r n k HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr. reflexivity. Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* the state at snprintf's entry (the jal executed) *)
Definition ki_call_st (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(pos : Z) (gi : nat) (line : Z) (b : bool) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem3 md3 0 /\
(forall a, 0 <= a < 2 ^ 64 ->
 ~ (seg_spec.mseg_addr (mv_c v) gi + 24 <= a < seg_spec.mseg_addr (mv_c v) gi + 32) ->
 rdW Wc mem3 a = rdW Wc memc a) /\
sa_val (rdW Wc mem3) (seg_spec.mseg_addr (mv_c v) gi + 24) 4 (seg_spec.b2z b) /\
sa_val (rdW Wc mem3) (seg_spec.mseg_addr (mv_c v) gi + 28) 4 1 /\
getr regs3 1 = Z_to_bv 64 (BASE + KI_RET) /\
getr regs3 10 = w64 (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_IGNORE_FILE) /\ getr regs3 11 = w64 96 /\
getr regs3 12 = w64 (SegInstA.seg_litA_fz F_s) /\ getr regs3 13 = w64 (mv_c v + seg_spec.MC_READING) /\
mf_regs_at B v lyc pos regs3 /\ getr regs3 24 = w64 (line + 1) /\ getr regs3 21 = w64 (mv_c v).

(* 0x869e8 to snprintf's entry *)
Lemma ki_hit_run : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ov vl : nat) (vv : list Z) (b : bool),
  ki_vbase B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
  (gi < length (mc_seg (mf_final v)))%nat ->
  getr regs1 13 = w64 (seg_spec.mseg_addr (mv_c v) gi) -> getr regs1 22 = w64 (seg_spec.b2z b) ->
  (forall regs3 mem3 md3, ki_call_st v lyc Sc Wc memc pos gi line b regs3 mem3 md3 ->
    SRr SEGS Wc (mkCfg (mkst regs3 (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) mem3 (seg_rom SEGS)) md3)
      (MF_POST B v)) ->
  mf_at B v Wc regs1 memc mdc KI_HIT.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv b VB HGF R13 R22 KC.
destruct VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & Hov & Hvv & NP & R21 & R20 & R24).
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HMA & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _).
unfold mf_cur_ok in LCUR.
pose proof HMC as (bs & _ & (HL & HL32 & _)).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in Sp1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (c := mv_c v) in *.
set (g := seg_spec.mseg_addr c gi) in *.
assert (Hg : g = c + 256 * Z.of_nat gi) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
unfold seg_spec.SEG_M_SIZE in *.
assert (Hgi32 : (gi < 32)%nat) by lia.
assert (Hcur : 0 <= mf_cur_ptr c (Some gi) < 2 ^ 64) by (unfold mf_cur_ptr; fold g; lia).
(* the seed, its slots read-only *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) 0 [] KI_HIT true false []
  false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun H => ltac:(discriminate H)) ltac:(lia)
  ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
set (E := mfE regs1 v lyc pos (Some gi) 0 []) in *.
assert (HS1 : st_ok_pi SEGS VAL E (mkSS KI_HIT sr_mf [ki_slots] None mf_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KI_HIT)) memc (seg_rom SEGS)))).
{ refine (st_ok_pi_submem E _ _ [ki_slots] HS0 _ eq_refl).
  cbn [ss_mem ss_mf]. unfold mf_regions. apply submem_drop. apply submem_keep; [|apply submem_nil].
  unfold subregion, ki_slots, mf_r_slots. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros ch Hch. rewrite !app_nil_r. exact Hch. }
clear HS0.
(* a3 pinned to atom 37 (the cur cell's value g) *)
pose proof (mfE_extra regs1 v lyc pos (Some gi) 0 [] 5 ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app mf_cur_ptr] in E37. fold E c g in E37.
assert (Hg64 : 0 <= g < 2 ^ 64) by lia.
assert (D13 : sv_denot E (SOff 37 0) = getr regs1 13)
  by (rewrite (ki_atom_val E 37 g 0 E37 Hg64), Z.add_0_r, R13; reflexivity).
pose proof (ast_ok_pi_set_reg_fp E _ _ (13%bv : bv 5) (SOff 37 0) HS1 eq_refl D13) as HS2.
clear HS1.
assert (Hs1r : alloc_ceiling + 8000 <= mf_s1 (mv_sp v) <= 2 ^ 47) by (destruct Ss1 as [E1 | E1]; rewrite E1; lia).
assert (E2 : ew E 2 = Z_to_bv 64 (mf_s1 (mv_sp v)))
  by (unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) 0 [] 2 2%bv eq_refl), R2; reflexivity).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v)) by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = g) by (rewrite E37; apply unsigned_lit_small; lia).
assert (B37 : base_val E (Some 37%nat) = g) by (cbn [base_val]; exact U37).
(* g's ignore and ignore_set *)
assert (GOK : region_ok SEGS E (mrestrict (w_H Wc) memc) ki_g).
{ unfold region_ok, ki_g. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B37.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hbpres (g + o) ltac:(lia))). }
assert (GDIS : all_disjoint E ki_g [ki_slots]).
{ apply all_disjoint_of_extents. unfold ki_g, ki_slots, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B37, B2.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ ki_g HS2 eq_refl GOK GDIS) as HS3.
clear HS2.
assert (F37 : afact_ok E 37 (HPTR 4)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite U37.
  split; [lia|]. split; [|lia]. change (2 ^ 4) with 16. rewrite Hg.
  replace (c + 256 * Z.of_nat gi) with ((c / 16 + 16 * Z.of_nat gi) * 16) by (pose proof (Z.div_mod c 16 ltac:(lia)); lia).
  apply Z_mod_mult. }
pose proof (st_ok_pi_add_fact E _ _ 37 (HPTR 4) HS3 F37) as HS.
clear HS3.
(* the shadow entry of the two checks: g's first 40 bytes, inside the block *)
assert (SHOK : sh_ok SEGS (SOff 32 0) ki_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, ki_SH. apply Forall_cons; [|apply Forall_nil].
  apply (mf_she_at E Wc memc 37 g 40 (mfE_U32 regs1 v lyc pos (Some gi) 0 []) E37 ltac:(lia) ltac:(lia)).
  - destruct (mf_addr_sub _ c 9236 g 40 HMA ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & _ & HRA & _). exact HRA.
  - intros x Hx. apply (mf_blk_app B v CX). unfold seg_spec.SEG_M_SIZE. fold c. lia. }
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
(* 0x869e8 .. 0x86a34: the two checks and stores, s5, snprintf's arguments; the jal *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 37%nat g); [reflexivity | exact U37 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + exists (c, seg_spec.mseg_addr c (length (mc_seg (mf_final v)))). split; [left; reflexivity|].
      cbn [fst snd]. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia.
    + exists bc, mbc. split; [exact Hbc | lia].
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with HSx : st_ok _ E _ (restrict _ ?mB) |- _ => rename mB into ms3; rename HSx into HS3 end.
(* the registers at the jal *)
lazymatch type of HS3 with st_ok _ _ ?ssx _ =>
  assert (QR : forall (r : bv 5) n0 k0, sr_get (ss_regs ssx) r = SOff n0 k0 ->
    getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0))
    by (intros r n0 k0 Hr; exact (ki_reg E ssx (w_H Wc) ms3 r n0 k0 HS3 Hr));
  assert (QL : forall (r : bv 5) z, sr_get (ss_regs ssx) r = SLit z -> getr (ms_regs ms3) r = Z_to_bv 64 z)
    by (intros r z Hr; exact (ki_reg_lit E ssx (w_H Wc) ms3 r z HS3 Hr))
end.
assert (QA : forall (r : bv 5) n0 x k0, ew E n0 = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0) -> getr (ms_regs ms3) r = Z_to_bv 64 (x + k0))
  by (intros r n0 x k0 Hn0 Hx Hr; rewrite Hr, Hn0, unsigned_lit_small by exact Hx; reflexivity).
assert (QS : forall (r : bv 5) n0, ew E n0 = getr regs1 r ->
  getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + 0) -> getr (ms_regs ms3) r = getr regs1 r)
  by (intros r n0 Hn0 Hr; rewrite Hr, Z.add_0_r, Hn0; apply Z_to_bv_bv_unsigned).
pose proof (mfE_extra regs1 v lyc pos (Some gi) 0 [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) 0 [] 1 ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth mf_extra map app] in E32, E33. fold E in E32, E33. fold c in E33.
assert (E255 : ew E 255 = Z_to_bv 64 (SegInstA.seg_litA_fz F_s)).
{ unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) 0 [] 255 ltac:(unfold A_TEXT, A_LIM; lia)).
  change 255%nat with (A_OBJ 14). rewrite <- (mf_lit_obj VOBJS F_s 14 ltac:(left; reflexivity)). reflexivity. }
assert (HFs : 0 <= SegInstA.seg_litA_fz F_s < 2 ^ 64) by (rewrite sn_fs_at; lia).
pose proof (QR 1%bv 240%nat 7428 eq_refl) as Q1. rewrite (img_env_codeptr E HEI 7428) in Q1.
pose proof (QA 2%bv 2%nat _ 0 E2 ltac:(lia) (QR 2%bv 2%nat 0 eq_refl)) as Q2.
pose proof (QS 3%bv 3%nat (mfE_reg regs1 v lyc pos (Some gi) 0 [] 3 3%bv eq_refl) (QR 3%bv 3%nat 0 eq_refl)) as Q3.
pose proof (QS 4%bv 4%nat (mfE_reg regs1 v lyc pos (Some gi) 0 [] 4 4%bv eq_refl) (QR 4%bv 4%nat 0 eq_refl)) as Q4.
pose proof (QS 8%bv 8%nat (mfE_reg regs1 v lyc pos (Some gi) 0 [] 8 8%bv eq_refl) (QR 8%bv 8%nat 0 eq_refl)) as Q8.
pose proof (QA 9%bv 2%nat _ 0 E2 ltac:(lia) (QR 9%bv 2%nat 0 eq_refl)) as Q9.
pose proof (QA 10%bv 37%nat _ 156 E37 Hg64 (QR 10%bv 37%nat 156 eq_refl)) as Q10.
pose proof (QL 11%bv 96 eq_refl) as Q11.
pose proof (QA 12%bv 255%nat _ 0 E255 HFs (QR 12%bv 255%nat 0 eq_refl)) as Q12.
pose proof (QA 13%bv 33%nat _ 9140 E33 ltac:(lia) (QR 13%bv 33%nat 9140 eq_refl)) as Q13.
pose proof (QA 18%bv 32%nat _ 0 E32 ltac:(unfold SHADOW_OFF; lia) (QR 18%bv 32%nat 0 eq_refl)) as Q18.
pose proof (QS 19%bv 19%nat (mfE_reg regs1 v lyc pos (Some gi) 0 [] 19 19%bv eq_refl) (QR 19%bv 19%nat 0 eq_refl)) as Q19.
pose proof (QA 21%bv 33%nat _ 0 E33 ltac:(lia) (QR 21%bv 33%nat 0 eq_refl)) as Q21.
pose proof (QS 24%bv 24%nat (mfE_reg regs1 v lyc pos (Some gi) 0 [] 24 24%bv eq_refl) (QR 24%bv 24%nat 0 eq_refl)) as Q24.
pose proof (QS 25%bv 25%nat (mfE_reg regs1 v lyc pos (Some gi) 0 [] 25 25%bv eq_refl) (QR 25%bv 25%nat 0 eq_refl)) as Q25.
pose proof (QS 26%bv 26%nat (mfE_reg regs1 v lyc pos (Some gi) 0 [] 26 26%bv eq_refl) (QR 26%bv 26%nat 0 eq_refl)) as Q26.
rewrite !Z.add_0_r in Q2, Q9, Q12, Q18, Q21.
(* the bytes: kept outside g's 8 bytes; g->ignore = b, g->ignore_set = 1 *)
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 24 <= a < g + 32) -> rdW Wc (ms_mem ms3) a = rdW Wc memc a).
{ intros a Ha Hna.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms3) (fun x => g + 24 <= x < g + 32) HFr _ a Ha Hna).
  intros bb wlo whi x Hin Hr. cbv beta. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [rewrite U37 in Hr; lia | lia] |]).
  destruct Hin. }
assert (E22 : ew E 22 = Z_to_bv 64 (seg_spec.b2z b))
  by (unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) 0 [] 22 22%bv eq_refl), R22; reflexivity).
assert (Hb32 : 0 <= seg_spec.b2z b < 2 ^ 32) by (destruct b; cbn; lia).
assert (D22 : sv_denot E (SOff 22 0) = Z_to_bv 64 (seg_spec.b2z b))
  by (rewrite (ki_atom_val E 22 (seg_spec.b2z b) 0 E22 ltac:(lia)), Z.add_0_r; reflexivity).
pose proof (st_ok_region_nth E _ (restrict (w_H Wc) ms3) 0 _ HS3 eq_refl) as HR0.
pose proof (field_of_region E _ 37 g _ 24 32 24 32 24 4%N (SOff 22 0) (seg_spec.b2z b) HR0 U37
  ltac:(right; left; reflexivity) D22 ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hb32)
  ltac:(cbn; lia)) as VR.
pose proof (field_of_region E _ 37 g _ 24 32 24 32 28 4%N (SLit 1) 1 HR0 U37
  ltac:(left; reflexivity) eq_refl ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia)
  ltac:(cbn; lia)) as VRS.
change (N.to_nat 4) with 4%nat in VR, VRS.
(* the call *)
pmkst HS3.
apply KC. unfold ki_call_st.
split; [exact HJ|].
split; [exact KP|].
split; [exact (ki_sa_of_val SEGS (w_H Wc) (ms_mem ms3) _ _ _ VR)|].
split; [exact (ki_sa_of_val SEGS (w_H Wc) (ms_mem ms3) _ _ _ VRS)|].
split; [rewrite Q1; reflexivity|].
split; [rewrite Q10; reflexivity|].
split; [rewrite Q11; reflexivity|].
split; [rewrite Q12; reflexivity|].
split; [rewrite Q13; reflexivity|].
split.
{ unfold mf_regs_at, w64. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q25, Q26.
  split; [reflexivity|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [reflexivity|].
  split; [reflexivity|]. split; [exact R19|]. split; [exact R25 | exact R26]. }
split; [rewrite Q24; exact R24|].
rewrite Q21. reflexivity.
Qed.

(* 0x86a38 `mv s6,s8`, `ld s8,104(s1)`, `j 0x86cd0`: KDONE's statement holds three instructions earlier, with
   s8 = the line number and s5 = c *)
Lemma ki_ret_kdone : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z),
  MF_KDONE_stmt B n ->
  mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
  getr regs1 24 = w64 line ->
  (length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
  fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
  mf_np v memc Wc p -> getr regs1 21 = w64 (mv_c v) ->
  mf_at B v Wc regs1 memc mdc KI_RET.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest KD CX LS FRM CORE CELLS RA R24 Hn LOOP FIN NP R21.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur CX CORE LCUR) as Hcur.
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin1) as (F1 & F2 & _).
change (fs_frame_bytes 1) with 128 in F2.
pose proof asan_consts as (C1 & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc cur 0 [] KI_RET true false []
  false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun H => ltac:(discriminate H)) ltac:(lia)
  ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
set (E := mfE regs1 v lyc pos cur 0 []) in *.
assert (HS : st_ok_pi SEGS VAL E (mkSS KI_RET sr_mf [ki_slots] None mf_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KI_RET)) memc (seg_rom SEGS)))).
{ refine (st_ok_pi_submem E _ _ [ki_slots] HS0 _ eq_refl).
  cbn [ss_mem ss_mf]. unfold mf_regions. apply submem_drop. apply submem_keep; [|apply submem_nil].
  unfold subregion, ki_slots, mf_r_slots. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros ch Hch. rewrite !app_nil_r. exact Hch. }
clear HS0.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KDONE.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* no byte changed *)
assert (HMEQ : forall x, ms_mem ms x = memc x).
{ intros x. apply HF. intros (rr & Hin & Hx). vm_compute in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur (ms_mem ms) _ CX CORE CELLS HJ EQV)
  as (C1' & C2' & C3' & C4').
(* the registers at KDONE: s6 = the line, s8 = FAKE, the rest kept *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  assert (QR : forall (r : bv 5) n0 k0, sr_get (ss_regs ssx) r = SOff n0 k0 ->
    getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0))
    by (intros r n0 k0 Hr; exact (ki_reg_pi E ssx (w_H Wc) ms r n0 k0 HS Hr)) end.
assert (QK : forall (r : bv 5) (n0 : nat) (r0 : bv 5), getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n0) + 0) ->
  Z.of_nat n0 = bv_unsigned r0 -> getr (ms_regs ms) r = getr regs1 r0).
{ intros r n0 r0 Hr Hn0. rewrite Hr, Z.add_0_r. unfold E. rewrite (mfE_reg regs1 v lyc pos cur 0 [] n0 r0 Hn0).
  apply Z_to_bv_bv_unsigned. }
assert (QA : forall (r : bv 5) n0 x, ew E n0 = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n0) + 0) -> getr (ms_regs ms) r = Z_to_bv 64 x)
  by (intros r n0 x Hn0 Hx Hr; rewrite Hr, Hn0, unsigned_lit_small, Z.add_0_r by exact Hx; reflexivity).
pose proof (mfE_extra regs1 v lyc pos cur 0 [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos cur 0 [] 2 ltac:(unfold A_TEXT; lia)) as E34.
cbn [Nat.add nth mf_extra map app] in E32, E34. fold E in E32, E34.
pose proof (QK 2%bv 2%nat 2%bv (QR 2%bv 2%nat 0 eq_refl) eq_refl) as Q2.
pose proof (QK 3%bv 3%nat 3%bv (QR 3%bv 3%nat 0 eq_refl) eq_refl) as Q3.
pose proof (QK 4%bv 4%nat 4%bv (QR 4%bv 4%nat 0 eq_refl) eq_refl) as Q4.
pose proof (QK 8%bv 8%nat 8%bv (QR 8%bv 8%nat 0 eq_refl) eq_refl) as Q8.
pose proof (QK 9%bv 2%nat 2%bv (QR 9%bv 2%nat 0 eq_refl) eq_refl) as Q9.
pose proof (QA 18%bv 32%nat _ E32 ltac:(unfold SHADOW_OFF; lia) (QR 18%bv 32%nat 0 eq_refl)) as Q18.
pose proof (QK 19%bv 19%nat 19%bv (QR 19%bv 19%nat 0 eq_refl) eq_refl) as Q19.
pose proof (QK 21%bv 21%nat 21%bv (QR 21%bv 21%nat 0 eq_refl) eq_refl) as Q21.
pose proof (QK 22%bv 24%nat 24%bv (QR 22%bv 24%nat 0 eq_refl) eq_refl) as Q22.
pose proof (QA 24%bv 34%nat _ E34 ltac:(lia) (QR 24%bv 34%nat 0 eq_refl)) as Q24.
pose proof (QK 25%bv 25%nat 25%bv (QR 25%bv 25%nat 0 eq_refl) eq_refl) as Q25.
pose proof (QK 26%bv 26%nat 26%bv (QR 26%bv 26%nat 0 eq_refl) eq_refl) as Q26.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with MF_KDONE by (unfold MF_KDONE, AF_m_file; reflexivity) end.
refine (KD v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest CX LS FRM C1' C2' _ _ Hn (C4' _ _ _ _ _ LOOP)
  FIN (C3' _ NP) _ _).
- apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA Q2 Q3 Q4 Q8); [rewrite Q9, R2, R9; reflexivity | | exact Q19
    | exact Q25 | exact Q26].
  rewrite Q18, R18. reflexivity.
- rewrite Q24. reflexivity.
- exact (eq_trans Q21 R21).
- exact (eq_trans Q22 R24).
Qed.
End e.
End f.
End d.

Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
(* the shared Section hypotheses this piece uses *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) SegInstA.gotwA SegInstA.guardA.

(* KI_HIT 0x869e8: the ignore stores, snprintf of c->reading into g->ignore_file, `j` to KDONE *)
Lemma ki_s_hit : forall n, MF_KDONE_F B n -> KI_HIT_stmt B n.
Proof.
intros n KD. unfold KI_HIT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv b VB FIN R13 R22.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & Hov & Hvv & NP & R21 & R20 & R24).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _). unfold mf_cur_ok in LCUR.
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V112 & HMC & HMA & HMT).
destruct (ki_h_reading _ _ _ HMC) as (HZR & Hrl & Hr0).
set (r := mc_reading mcc) in *.
rewrite (ki_snp_reading r Hrl Hr0) in FIN.
set (mcc' := m_upd mcc gi (ms_with_ignore b r)) in *.
destruct (ki_upd_cnt mcc gi (ms_with_ignore b r)) as (U1 & U2 & U3 & U4 & _).
(* the entry is one of the final model's *)
assert (Hfin : (gi < length (mc_seg (mf_final v)))%nat).
{ assert (HC : mf_cur_ok (fst (mcc', Some gi)) (snd (mcc', Some gi)))
    by (cbn [fst snd]; unfold mf_cur_ok, mcc'; rewrite U1; exact LCUR).
  destruct (m_lines_ok (lines (mf_rest rest)) (mcc', Some gi) (line + 1) HC) as [[G _] _].
  unfold mf_fin in FIN. rewrite FIN in G. cbn [fst] in G. unfold mcc' in G. rewrite U1 in G. lia. }
apply (ki_hit_run B VOBJS n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv b VB Hfin R13 R22).
intros regs3 mem3 md3 (HJ3 & KP3 & VR3 & VRS3 & Q1 & Q10 & Q11 & Q12 & Q13 & RA3 & Q24 & Q21).
(* where things lie *)
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _).
pose proof HJ3 as (HAR3 & _). pose proof HJ as (HAR & _).
pose proof HMC as (bs0 & _ & (_ & HL32 & _)).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbm).
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in Sp1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hs1r : mv_sp v - 304 <= mf_s1 (mv_sp v) <= mv_sp v - 288) by (destruct Ss1 as [E1|E1]; rewrite E1; lia).
assert (HKR : KI_RET = 7428) by reflexivity.
assert (HKK : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
assert (Hg : seg_spec.mseg_addr (mv_c v) gi = mv_c v + 256 * Z.of_nat gi)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
unfold seg_spec.SEG_M_SIZE in *.
assert (Hgi32 : (gi < 32)%nat) by lia.
(* c->reading at the call state *)
assert (HZR3 : sa_zs (rdW Wc mem3) (mv_c v + seg_spec.MC_READING) (r ++ [0])).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  rewrite KP3; [exact (HZR j ltac:(rewrite length_app; cbn [length]; lia)) | unfold seg_spec.MC_READING; lia
    | unfold seg_spec.MC_READING; lia]. }
assert (HSA3 : sa_addr (rdW Wc mem3) (mv_c v) 9236).
{ destruct HMA as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR3 Hbc); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR3 Hbc); lia. }
assert (HST3 : sa_tail (rdW Wc mem3) (mv_c v + 9236 - 1)).
{ intros x Hx. pose proof (Z.mod_pos_bound (mv_c v + 9236 - 1) 8 ltac:(lia)).
  rewrite KP3; [exact (HMT x Hx) | lia | lia]. }
(* 0x86a34: snprintf(g->ignore_file, 96, "%s", c->reading) *)
pose proof RA3 as (R2' & R3' & R4' & R8' & R9' & R18' & R19' & R25' & R26').
apply (mf_snp_field_call B SSP RELRO ASNPRINTF v lyc Sc Wc regs3 mem3 md3 pos gi r seg_spec.MS_IGNORE_FILE KI_RET
  (or_intror eq_refl) CX LS FRM HJ3 HPerm HSA3 HST3 HZR3 Hrl Hr0 Hgi32 Hfin R2' R3' R4' Q1
  ltac:(rewrite HKR; lia) ltac:(rewrite HKR; reflexivity) Q10 Q11 Q12 Q13).
intros fx1 regs2 mem2 md2 Hfx HJ2 HP2 HZF HK2.
rewrite HKK in HK2. unfold seg_spec.MS_IGNORE_FILE in HZF, HK2.
(* what the run and snprintf wrote: g's ignore / ignore_set, snprintf's window, the field *)
set (EW := fun a => (seg_spec.mseg_addr (mv_c v) gi + 24 <= a < seg_spec.mseg_addr (mv_c v) gi + 32) \/
  (seg_spec.mseg_addr (mv_c v) gi + 156 <= a < seg_spec.mseg_addr (mv_c v) gi + 156 + Z.of_nat (length r) + 1)).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - 8192 <= a < mf_s1 (mv_sp v)) -> ~ EW a ->
  rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha H1 H2. rewrite (HK2 a Ha H1);
    [apply KP3; [exact Ha | intros Hc; apply H2; unfold EW; left; exact Hc]
    | intros Hc; apply H2; unfold EW; right; exact Hc]. }
assert (HEW : forall a, EW a -> mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE).
{ intros a [H | H]; unfold seg_spec.SEG_M_SIZE; lia. }
(* the block after the two stores and snprintf holds mcc' *)
assert (MC2 : sa_mconf (rdW Wc mem2) (mv_c v) mcc').
{ apply (ki_e_mconf_ign (rdW Wc memc) (rdW Wc mem2) (mv_c v) mcc gi b r HMC LCUR Hrl Hr0).
  - intros x Hx H1 H2. unfold seg_spec.SEG_M_SIZE in Hx. apply KW; [lia | lia |].
    intros [H | H]; [apply H1 | apply H2]; exact H.
  - intros kk Hkk. rewrite (HK2 (seg_spec.mseg_addr (mv_c v) gi + 24 + Z.of_nat kk)); [exact (VR3 kk Hkk) | lia | lia | lia].
  - intros kk Hkk. rewrite (HK2 (seg_spec.mseg_addr (mv_c v) gi + 28 + Z.of_nat kk)); [exact (VRS3 kk Hkk) | lia | lia | lia].
  - exact HZF.
  - intros x v0 Hx. exact (ki_aview_byte SEGS (w_H Wc) mem2 x v0 Hx). }
(* every cut fact at the return *)
destruct (mf_keep_art B v lyc Sc Wc regs3 memc mdc pos MF_LOW_ON mcc (Some gi) regs2 mem2 md2
  (mf_s1 (mv_sp v) - 8192) (mf_s1 (mv_sp v)) EW mcc' CX CORE CELLS RA3 HJ2 HP2 ltac:(lia) ltac:(lia) KW HEW MC2)
  as (CORE2 & CELLS2 & RA2 & NPk & LPk).
pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP2.
assert (LOOPn : mf_loop v Wc mem2 mcc' (Some gi) (line + 1) (mf_next p rest) (mf_rest rest)).
{ apply (mf_loop_next v Wc mem2 mcc (Some gi) line p rest mcc' (Some gi) LOOP2 Hne); unfold mcc';
    [rewrite U3; lia | rewrite U4; lia | rewrite U2; lia | unfold mf_cur_ok; rewrite U1; exact LCUR]. }
pose proof (NPk (mf_next p rest) NP) as NP2.
assert (Hn2 : (length (mf_rest rest) < n)%nat).
{ destruct (mf_break_snd rest) as (_ & Bk2 & _). pose proof (Bk2 Hne) as Bk. unfold mf_rest. lia. }
assert (G : forall rr, acallee_saved rr -> getr regs2 (Z_to_bv 5 rr) = getr regs3 (Z_to_bv 5 rr)) by exact HP2.
assert (P24 : getr regs2 24 = getr regs3 24) by exact (G 24 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr regs3 21) by exact (G 21 ltac:(unfold acallee_saved; lia)).
exact (ki_ret_kdone (fx := fx1) B VOBJS n v lyc Sc Wc regs2 mem2 md2 pos mcc' (Some gi) (line + 1) (mf_next p rest)
  (mf_rest rest) (KD fx1) CX LS (fxrel_frm0 fx fx1 FRM Hfx) CORE2 CELLS2 RA2
  ltac:(rewrite P24; exact Q24) Hn2 LOOPn FIN NP2 ltac:(rewrite P21; exact Q21)).
Qed.
End e2.
End f2.
End d2.
