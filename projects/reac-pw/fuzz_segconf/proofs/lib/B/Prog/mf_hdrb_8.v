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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 425 of its 474 lines of code are new or changed and 404 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3; 0x86140), the segment S_MF_HDRB (HFIND 0x865c0 ->
   TAIL 0x86820): its NOT-FOUND ARM, NFIND -> NEWE or RREF2. A walk lane of the image-B m_file-family owner's G2B (a piece agent).
   proves no function (kind: segment lemma of m_file's image-B walk).
     hb8_nfind  0x86b04 (MFB_NFIND) -> 0x86b54 (MFB_NEWE) or 0x86b4c (MFB_RREF2)
   ADAPTED from image A's lib/A/Prog/m_file_s_hdrb.v hb_nfind_at (the image-A m_file-family lane, 
   commit b807fd22027f) at image B's registers, frame cells and pcs.
   WHAT THE CODE DOES (the neutral listing of m_file in image B lines 627-646):
     0x86b04-0x86b14  the instrumented check of the 4-byte load of c->n: a load of the shadow byte at
                      ((c + 0x2000) >> 3) + the shadow base, formed from s6 = c + 0x2000 (image A loads c + 0x2000
                      from 88(s1)), and `bnez` to the slow path 0x86d58-0x86d64; the error path (a call of
                      errpath_load4, 0x86f40-0x86f44) is not reached: the shadow byte is 0 (the block's shadow
                      entry, m_file_sd.v's mf_she_blk), so the `bnez` is not taken; a3 = 32 (image A: s3 = 0x20)
     0x86b18          `lw a0,0(s6)`: n = |seg mcc| (mf_hdrb_1.v's hb_rd_n)
     0x86b1c          `blt a0,a3`: n < 32 goes to 0x86b54 = MFB_NEWE (a0 = n, a1 = the shadow byte address of c->n
                      as the code formed it, memory unchanged); else n = 32 (hb_mconf_bounds)
     0x86b20-0x86b3c  `ld a0,24(s1)` (c + 0x2004), the instrumented check of c->overflow (slow path
                      0x86d68-0x86d74, error path 0x86f48, not reached), `lw`, `addi 1`, `sw` (overflow + 1; the store
                      reuses the load's check; M_FILE_FP holds the byte, mf_hdrb_1.v's hb_fp_cnt)
     0x86b40-0x86b48  a0 = s9 = c, a1 = s11 = line + 1, `jal m_refuse` (m_file_rf.v's mf_refuse_step at listing
                      offset AF_m_file + 0xa08, the block holding mc_set_overflow (overflow + 1) mcc, the line loop at
                      the head's model mcc: both have mcc's refused), back at 0x86b4c = MFB_RREF2.
   No UBSan trap branch lies in this code (the three branches go to the slow paths 0x86d58 / 0x86d68 and to
   0x86b54).
   THE SYMBOLIC STATE: m_file_sd.v's mf_seed at MFB_NFIND with xs = [n; overflow] (atoms 52, 53), the frame cells
   (region 1) made read-only, s6 pinned to atom 33 + 0x2000 (so `srli a1,s6,3; add a1,a1,s2; lb` reads as the check
   of c + 0x2000), c->n a read-only region at atom 33 [0x2000, 0x2004); on the overflow side c->overflow a writable
   region at atom 33 [0x2004, 0x2008). The shadow entry of the block [c, c + 9144) covers both checks.
   POSITIONAL NAMES checked against image B's listing, m_file_m.v and m_file_sd.v (what each object IS): the pcs
   0x86b04 / 0x86b48 / 0x86b4c / 0x86b54 and listing offsets 0x9c4 / 0xa08 / 0xa0c / 0xa14; the registers x10 a0,
   x11 a1, x20 s4 (511), x22 s6 (c + 0x2000), x25 s9 (c), x26 s10 (|nm|), x27 s11 (line + 1), x2 x3 x4 x8 x9 x18 x19
   x23 x24 of mf_regs_at; the frame cells 24(s1) (c + 0x2004), 136(s1) (cur), 152(s1) (np), 192(s1) (the name),
   120(s1) (FB); frame size 320 and STK_m_file 8,592; the seed atoms 32 SB, 33 c, 34 FB, 36 SF, 52 / 53 (xs), region
   1 (the frame cells [16, 216)); the offsets MC_N 0x2000, MC_OVERFLOW 0x2004. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YL08 YN1f YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegObj SegGlob SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m
  m_file_mdl m_file_sd m_file_k m_file_rf mf_hdrb_1 mf_hdrb_2 mf_hdrb_3 mf_hdrb_4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the `jal m_refuse` of the overflow path, 0x86b48 (listing offset = AF_m_file + (pc - 0x86140)) *)
Definition HB8_JREF2 : Z := AF_m_file + 0xa08.

(* ===================================== word and byte arithmetic ===================================== *)
(* `lw` of a 32-bit value below 2 ^ 31 is the value *)
Lemma hb8_lw_small : forall z, 0 <= z < 2 ^ 31 -> sext 64 (bv_extract 0 32 (Z_to_bv 64 z)) = Z_to_bv 64 z.
Proof. intros z Hz. apply sext32_small. lia. Qed.

(* `blt a0,a3` with a3 = 32 and 0 <= a0 <= 32 *)
Lemma hb8_blt32 : forall x, 0 <= x <= 32 -> branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 32) = (x <? 32).
Proof.
intros x Hx. assert (H : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/ x = 16 \/ x = 17 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27 \/ x = 28 \/ x = 29 \/ x = 30 \/ x = 31 \/ x = 32) by lia.
repeat (destruct H as [-> | H]; [vm_compute; reflexivity | ]). subst x. vm_compute. reflexivity.
Qed.

(* the block after the store of overflow: the model with overflow = z *)
Section mo.
Import seg_spec Mem.
Open Scope Z_scope.
Lemma hb8_mconf_ov : forall (rd rd2 : reader) c mc z, sa_mconf rd c mc ->
  (forall a, c <= a < c + seg_spec.SEG_M_SIZE -> ~ (c + seg_spec.MC_OVERFLOW <= a < c + seg_spec.MC_OVERFLOW + 4) ->
   rd2 a = rd a) ->
  sa_val rd2 (c + seg_spec.MC_OVERFLOW) 4 z -> 0 <= z < 2 ^ 32 -> sa_mconf rd2 c (mc_set_overflow z mc).
Proof.
intros rd rd2 c mc z (bs & HB & He) HK HV Hz.
destruct (mconf_enc_bounds _ _ _ He) as (Hlen & _).
assert (Hl : Z.of_nat (length bs) = 9236) by (rewrite Hlen; reflexivity).
exists (upd_bytes bs (Z.to_nat seg_spec.MC_OVERFLOW) (le4 (Z_to_bv 64 z))). split.
- apply (hb_bytes_upd rd rd2 c bs (Z.to_nat seg_spec.MC_OVERFLOW) (le4 (Z_to_bv 64 z)) HB).
  + replace (c + Z.of_nat (Z.to_nat seg_spec.MC_OVERFLOW)) with (c + seg_spec.MC_OVERFLOW)
      by (unfold seg_spec.MC_OVERFLOW; lia).
    apply hb_bytes_of_val; assumption.
  + apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, length_le4, Hl. unfold seg_spec.MC_OVERFLOW. lia.
  + intros a Ha Hn. rewrite length_le4 in Hn. rewrite Hl in Ha. apply HK.
    * unfold seg_spec.SEG_M_SIZE. lia.
    * unfold seg_spec.MC_OVERFLOW in *. lia.
- apply mconf_enc_overflow; assumption.
Qed.
End mo.

Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a 4-byte chunk of a region: its low 32 bits, whatever its upper bits *)
Lemma hb8_field4 : forall E m n b cs lo hi wlo whi od e z,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 4 e)) cs -> bv_unsigned (sv_denot E e) mod 2 ^ 32 = z ->
  val_mem SEGS m (b + od) 4 z.
Proof.
intros E m n b cs lo hi wlo whi od e z (_ & _ & _ & H4) Hb Hin Hz.
pose proof (proj1 (Forall_forall _ _) H4 _ Hin) as HC. cbn [base_val YP09.r_base] in HC. rewrite Hb in HC.
intros k Hk. destruct (HC (Z.of_nat k) ltac:(cbn; lia)) as (bt & Hc & Hm).
cbn [cbyte YP09.c_val c_off] in Hc, Hm. injection Hc as <-. rewrite Hm. f_equal.
rewrite <- Hz. rewrite <- YN1f.le_byte_low4 by lia. symmetry. apply YL08.le_byte_of_word. lia.
Qed.

(* a 4-byte value of the restricted memory, read through the reader *)
Lemma hb8_sa_val4 : forall (H : word -> bool) (m : word -> option byte) a z, 0 <= z < 2 ^ 32 ->
  val_mem SEGS (mrestrict H m) a 4 z -> sa_val (aview SEGS H m) a 4 z.
Proof.
intros H m a z Hz Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256.
unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* a symbolic value that is an atom denotes the atom's word *)
Lemma hb8_denot_atom : forall E n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Section i.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the Section hypotheses (the HDRB piece plan's texts; m_file_rf.v's SIGP / SSP / RELRO / M_REFUSE verbatim) *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.

(* ===================================== where the mconf block lies ===================================== *)
(* the block c lies below the stack window (s1 = (sp0 - 320) & -32), apart from the side-stack frame and from its
   shadow *)
Lemma hb8_geo : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
4096 <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\
mv_c v mod 16 = 0 /\
mv_c v + seg_spec.SEG_M_SIZE + 8192 <= mf_s1 (mv_sp v) /\ mf_s1 (mv_sp v) + 320 <= mv_sp v /\
(mv_c v + seg_spec.SEG_M_SIZE <= frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 128 <= mv_c v) /\
(mv_c v + seg_spec.SEG_M_SIZE <= SHADOW_OFF + frame_addr lyc 1 pos / 8 \/
 SHADOW_OFF + frame_addr lyc 1 pos / 8 + 16 <= mv_c v) /\
4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling /\ mv_sp v <= 2 ^ 47.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX CORE.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & Hheap & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hslo.
destruct Hheap as (bb & bm & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR0 Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq].
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (Hbin2 : In (bb, bm) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbin).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bb bm 1 pos HAR Hbin2 Hfin) as Hsep.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
change (fs_frame_bytes 1) with 128 in *.
pose proof (mf_blk_app B v CX (mv_c v) ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as A0.
pose proof (mf_blk_app B v CX (mv_c v + seg_spec.SEG_M_SIZE - 1) ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as A1.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
set (F := frame_addr lyc 1 pos) in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
set (sp0 := mv_sp v) in *. unfold mv_sp in sp0. fold sp0 in Hstk, Hal16, Hslo, Hshi, H47.
pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as M32.
unfold mf_s1. unfold seg_spec.SEG_M_SIZE in *. unfold SHADOW_OFF in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hc16|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* the five base atoms of the seed *)
Lemma hb8_bases : forall v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_regs_base v regs1 ->
base_val (mfE regs1 v lyc pos cur np xs) (Some 2%nat) = mf_s1 (mv_sp v) /\
base_val (mfE regs1 v lyc pos cur np xs) (Some 8%nat) = mv_sp v /\
base_val (mfE regs1 v lyc pos cur np xs) (Some 33%nat) = mv_c v /\
base_val (mfE regs1 v lyc pos cur np xs) (Some 34%nat) = frame_addr lyc 1 pos /\
base_val (mfE regs1 v lyc pos cur np xs) (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs CX CORE RB.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof RB as (R2 & R8 & R9 & R18).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in *.
pose proof (mfE_extra regs1 v lyc pos cur np xs 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos cur np xs 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos cur np xs 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E33, E34, E36.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
assert (HF8 : 0 <= frame_addr lyc 1 pos / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
set (sp0 := mv_sp v) in *. unfold mv_sp in sp0. fold sp0 in Hstk, Hal16, Hslo, Hshi, H47.
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hslo.
split; [|split; [|split; [|split]]]; cbn [base_val].
- rewrite (mfE_reg regs1 v lyc pos cur np xs 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small.
  unfold mf_s1. pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)). lia.
- rewrite (mfE_reg regs1 v lyc pos cur np xs 8 8%bv eq_refl), R8. unfold w64. apply unsigned_lit_small. lia.
- rewrite E33. apply unsigned_lit_small. lia.
- rewrite E34. apply unsigned_lit_small. lia.
- rewrite E36. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
Qed.

(* a byte of the counters n .. refused of the block is one the walk may write and is writable *)
Lemma hb8_blk_wr : forall v lyc Sc Wc memc mdc pos lowsh mcc a,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
mv_c v + seg_spec.MC_N <= a < mv_c v + seg_spec.MC_REFUSED + 4 ->
awr_byte SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (ablocks B (mv_ly v) (mv_S v))
  (ablocks B lyc Sc) (frames (mv_S v)) lyc [(1, pos)] a /\
writable_at SEGS (mrestrict (w_H Wc) memc) a.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc a CX CORE Ha.
assert (Hblk : exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n).
{ apply (hb3_blk_in B v lyc Sc Wc memc mdc pos lowsh mcc a CX CORE).
  unfold seg_spec.MC_N, seg_spec.MC_REFUSED, seg_spec.SEG_M_SIZE in *. lia. }
split.
- unfold awr_byte. right; left. split; [|exact Hblk]. apply hb_fp_cnt. exact Ha.
- destruct Hblk as (b & n & Hin & Hr). pose proof CORE as (HJ & _). destruct HJ as (HAR & _).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b n HAR Hin) as (_ & _ & _ & _ & Hb & _).
  destruct (Hb a Hr) as [Hp _]. eapply YCbq.apresent_writable. exact Hp.
Qed.

(* the tactics of the walk *)
Ltac hb8_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
end.
(* a register the run did not change: the same symbolic value before and after *)
Ltac hb8_same HS0 HS r :=
lazymatch type of HS0 with st_ok_pi _ _ ?E0 ?ss0 (restrict ?H0 ?ms0) =>
  let A := fresh "A" in let B' := fresh "B" in
  hb8_reg HS0 r A; hb8_reg HS r B'; rewrite B'; rewrite <- A; reflexivity
end.
Ltac hb8_norm HS := lazymatch type of HS with
| st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
Ltac hb8_awr_norm := lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
  let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
Ltac hb8_awr_ro := repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* a run whose regions are all read-only changed no byte *)
Ltac hb8_kept0 K := lazymatch goal with
| HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m1 a = aview SEGS H m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs H m0 m1 (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hin Hr; cbn [windows map ss_mem] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia | ]); destruct Hin
  | ] end.
Ltac hb8_pc pc := lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?k)) _ _) _) _ =>
  let Hk := fresh in assert (Hk : k = pc) by (vm_compute; reflexivity); rewrite Hk; clear Hk end.

Section j.
Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ===================================== hb8_nfind: 0x86b04, m_find found nothing =====================================
   the seed at MFB_NFIND with xs = [n; overflow] (atoms 52, 53); the frame cells read-only, s6 pinned to atom 33 +
   0x2000, c->n a read-only region at atom 33; the shadow entry of the block [c, c + 9144) covers every check *)
Lemma hb8_nfind_at : forall n, MFB_NEWE_F B n -> MFB_RREF2_F B n -> MFB_NFIND_stmt B n.
Proof.
intros n NEWE RREF2 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest o nm CX LS FRM CORE CELLS RA Hlen Hne LOOP
  HNM HFN HFIN SLOT R26 R20 R27 NP.
unfold mf_at.
pose proof CORE as (HJ & HPm & VFL & VSH & VSV & V112 & HMC & HMA & HMT).
destruct (hb_mconf_bounds _ _ _ HMC) as (Bseg & Bkept & Bgen & Bref & Bov & Bsg).
pose proof LOOP as (_ & _ & _ & _ & _ & Lcur & Lk0 & Lline0 & Lline & Lref & Lov).
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Lcur) as HCUR.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as HNP.
destruct (hb8_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G13).
unfold seg_spec.SEG_M_SIZE in G2, G5, G7, G8.
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as G11.
pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as G12.
set (nn := Z.of_nat (length (mc_seg mcc))) in *.
set (xs := [nn; mc_overflow mcc]).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs MFB_NFIND
  true true [] false false [] false CX CORE (mf_regs_base_of B v lyc pos regs1 RA) (fun _ => CELLS) HCUR (fun _ => NP)
  HNP ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs 9144 CX CORE
  ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as SH33.
destruct (hb8_bases v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs CX CORE
  (mf_regs_base_of B v lyc pos regs1 RA)) as (B2 & B8 & B33 & B34 & B36).
cbn [base_val] in B2, B8, B33, B34, B36.
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest) xs 0 ltac:(unfold A_TEXT; lia)) as E52.
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest) xs 1 ltac:(unfold A_TEXT; lia)) as E53.
cbn [Nat.add nth xs] in E52, E53.
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) xs 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) xs 0 ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E33, E32.
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (mfE regs1 v lyc pos cur (mf_next p rest) xs) k = getr regs1 r) by (intros; apply mfE_reg; assumption).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) xs) in HS, SH33, B2, B8, B33, B34, B36, E52, E53, E33, E32, ER.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9144] E (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; apply Forall_cons; [exact SH33 | apply Forall_nil]).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clearbody E. clear SH33.
(* the frame cells read-only, s6 = atom 33 + 0x2000, the region of c->n *)
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS eq_refl
  eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow SEGS E _ _ 0 0 (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) ltac:(intros o' Ho'; lia))) as HS1.
clear HS.
apply (ast_ok_pi_set_reg_fp E _ _ (22%bv : bv 5) (SOff 33 8192)) in HS1;
  [| reflexivity | cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; cbn [ms_regs restrict mkst];
     rewrite R22; reflexivity].
rename HS1 into HS2.
hb8_norm HS2.
set (rN := YP09.mkRegion (Some 33%nat) 0x2000 0x2004 0 0 [YP09.mkChunk 0x2000 (CVal 4 (SOff 52 0))]).
assert (RN : region_ok SEGS E (mrestrict (w_H Wc) memc) rN).
{ unfold region_ok, rN. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B33.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (mv_c v) 0x2000 4 (SOff 52 0) nn).
  - apply hb8_denot_atom. exact E52.
  - cbn. lia.
  - cbn. lia.
  - exact (val_mem_of_rd32 SEGS (w_H Wc) memc (mv_c v + 0x2000) nn (hb_rd_n _ _ _ HMC)). }
assert (DN : all_disjoint E rN (ss_mem (ltac:(lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => exact ss end)))).
{ apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold zdisj, extent_of_region, rN.
  cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?B2, ?B8, ?B33, ?B34, ?B36.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ rN HS2 eq_refl RN DN) as HS. clear HS2 RN DN.
hb8_norm HS.
pose proof HS as HS0.
(* run 1: 0x86b04 .. 0x86b1c, the check and the load of c->n, stopped at `blt a0,a3` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ hb8_awr_norm. hb8_awr_ro. }
hb8_kept0 K1.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md1 := d) in *; clearbody md1 end.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms1) md1 CX CORE CELLS HJ K1)
  as (CORE1 & CELLS1 & NPK1 & LOOPK1).
pose proof (NPK1 _ NP) as NP1. pose proof (LOOPK1 _ _ _ _ _ LOOP) as LOOP1. clear NPK1 LOOPK1.
pose proof CORE1 as (_ & _ & _ & VSH1 & _ & _ & HMC1 & _).
pose proof CELLS1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
(* the test `blt a0,a3` (a0 = n, a3 = 32) *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n < 32: to the new entry *)
  assert (Hlt : (length (mc_seg mcc) < 32)%nat).
  { change (sv_denot E (SExt true 32 (SOff 52 0))) with (sext 64 (bv_extract 0 32 (sv_denot E (SOff 52 0)))) in Hc.
    rewrite (hb8_denot_atom E 52 _ E52), hb8_lw_small in Hc by (unfold nn; lia).
    change (sv_denot E (SLit 32)) with (Z_to_bv 64 32) in Hc.
    rewrite hb8_blt32 in Hc by (unfold nn; lia). apply Z.ltb_lt in Hc. unfold nn in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MFB_NEWE.
  { hb8_awr_norm. hb8_awr_ro. }
  hb8_kept0 K2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md2 := d) in *; clearbody md2 end.
  destruct (mf_keep_run0 B v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc cur (ms_mem ms2) md2 CX CORE1 CELLS1 HJ K2)
    as (CORE2 & CELLS2 & NPK2 & LOOPK2).
  assert (SLOT2 : mf_slot v (ms_mem ms2) Wc 192 (p + Z.of_nat o)).
  { unfold mf_slot in *. apply (mf_val_keep Wc Wc memc (ms_mem ms2) (fun _ => False) _ 8 _).
    - intros a Ha _. rewrite (K2 a Ha). exact (K1 a Ha).
    - lia.
    - change (Z.of_nat 8) with 8. lia.
    - intros k _ [].
    - exact SLOT. }
  hb8_reg HS (10%bv : bv 5) Q10.
  change (sv_denot E (SExt true 32 (SOff 52 0))) with (sext 64 (bv_extract 0 32 (sv_denot E (SOff 52 0)))) in Q10.
  rewrite (hb8_denot_atom E 52 _ E52), hb8_lw_small in Q10 by (unfold nn; lia).
  hb8_reg HS (11%bv : bv 5) Q11.
  change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 8192) (SLit 3)) (SOff 32 0)) with (mf_shx 33 8192) in Q11.
  rewrite (mf_denot_shx E 33 (mv_c v) 8192 E33 E32 ltac:(lia) ltac:(lia) ltac:(lia)) in Q11.
  assert (Q2 : getr (ms_regs ms2) 2 = getr regs1 2) by (hb8_same HS0 HS (2%bv : bv 5)).
  assert (Q3 : getr (ms_regs ms2) 3 = getr regs1 3) by (hb8_same HS0 HS (3%bv : bv 5)).
  assert (Q4 : getr (ms_regs ms2) 4 = getr regs1 4) by (hb8_same HS0 HS (4%bv : bv 5)).
  assert (Q8 : getr (ms_regs ms2) 8 = getr regs1 8) by (hb8_same HS0 HS (8%bv : bv 5)).
  assert (Q9 : getr (ms_regs ms2) 9 = getr regs1 9) by (hb8_same HS0 HS (9%bv : bv 5)).
  assert (Q18 : getr (ms_regs ms2) 18 = getr regs1 18) by (hb8_same HS0 HS (18%bv : bv 5)).
  assert (Q23 : getr (ms_regs ms2) 23 = getr regs1 23) by (hb8_same HS0 HS (23%bv : bv 5)).
  assert (Q24 : getr (ms_regs ms2) 24 = getr regs1 24) by (hb8_same HS0 HS (24%bv : bv 5)).
  assert (Q19 : getr (ms_regs ms2) 19 = getr regs1 19) by (hb8_same HS0 HS (19%bv : bv 5)).
  assert (Q22 : getr (ms_regs ms2) 22 = getr regs1 22) by (hb8_same HS0 HS (22%bv : bv 5)).
  assert (Q25 : getr (ms_regs ms2) 25 = getr regs1 25) by (hb8_same HS0 HS (25%bv : bv 5)).
  assert (Q26 : getr (ms_regs ms2) 26 = getr regs1 26) by (hb8_same HS0 HS (26%bv : bv 5)).
  assert (Q27 : getr (ms_regs ms2) 27 = getr regs1 27) by (hb8_same HS0 HS (27%bv : bv 5)).
  pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms2) RA Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q19 Q22 Q25) as RA2.
  pmkst HS. hb8_pc MFB_NEWE.
  exact (NEWE fx v lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 pos mcc cur line p rest o nm CX LS FRM CORE2 CELLS2 RA2
    Hlen Hne (LOOPK2 _ _ _ _ _ LOOP1) HNM HFN Hlt HFIN Q10 Q11 SLOT2
    ltac:(rewrite Q26; exact R26) ltac:(rewrite Q27; exact R27) (NPK2 _ NP1)).
- (* 32 <= n: overflow + 1 and m_refuse *)
  assert (Hge : (32 <= length (mc_seg mcc))%nat).
  { change (sv_denot E (SExt true 32 (SOff 52 0))) with (sext 64 (bv_extract 0 32 (sv_denot E (SOff 52 0)))) in Hc.
    rewrite (hb8_denot_atom E 52 _ E52), hb8_lw_small in Hc by (unfold nn; lia).
    change (sv_denot E (SLit 32)) with (Z_to_bv 64 32) in Hc.
    rewrite hb8_blt32 in Hc by (unfold nn; lia). apply Z.ltb_ge in Hc. unfold nn in Hc. lia. }
  assert (Hov1 : mc_overflow mcc + 1 < 2 ^ 32)
    by (destruct rest as [|r0 rr]; [congruence | cbn [length] in Lov; lia]).
  hb8_norm HS.
  set (rO := YP09.mkRegion (Some 33%nat) 0x2004 0x2008 0x2004 0x2008 [YP09.mkChunk 0x2004 (CVal 4 (SOff 53 0))]).
  assert (RO1 : region_ok SEGS E (mrestrict (w_H Wc) (ms_mem ms1)) rO).
  { unfold region_ok, rO. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B33. split; [lia|]. split; [lia|]. split.
    - intros o' Ho'. exact (proj2 (hb8_blk_wr v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc (mv_c v + o') CX CORE1
        ltac:(unfold seg_spec.MC_N, seg_spec.MC_REFUSED; lia))).
    - apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (mv_c v) 0x2004 4 (SOff 53 0) (mc_overflow mcc)).
      + apply hb8_denot_atom. exact E53.
      + cbn. lia.
      + cbn. lia.
      + exact (val_mem_of_rd32 SEGS (w_H Wc) (ms_mem ms1) (mv_c v + 0x2004) _ (hb_rd_overflow _ _ _ HMC1)). }
  assert (DO : all_disjoint E rO (ss_mem (ltac:(lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => exact ss end)))).
  { apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold zdisj, extent_of_region, rO.
    cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?B2, ?B8, ?B33, ?B34, ?B36.
    repeat split; lia. }
  pose proof (st_ok_pi_add_region E _ _ rO HS eq_refl RO1 DO) as HS3. clear HS RO1 DO. rename HS3 into HS.
  hb8_norm HS.
  (* run 2: 0x86b20 .. 0x86b48, the check, the load and the store of c->overflow, a0 = s9 = c, a1 = s11 = line + 1 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HB8_JREF2.
  { hb8_awr_norm.
    eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v));
    [ reflexivity | exact B33
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
      exact (proj1 (hb8_blk_wr v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc a CX CORE1
        ltac:(unfold seg_spec.MC_N, seg_spec.MC_REFUSED; lia)))
    | ].
    hb8_awr_ro. }
  (* the store: overflow + 1 in c->overflow *)
  assert (VOV : bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 53 0)) (SLit 1))) mod 2 ^ 32 =
    mc_overflow mcc + 1).
  { change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 53 0)) (SLit 1))) with
      (alu64 ALU_ADD (sext 64 (bv_extract 0 32 (sv_denot E (SOff 53 0)))) (Z_to_bv 64 1)).
    rewrite (hb8_denot_atom E 53 _ E53). rewrite YN0d.ctr_chunk_mod by lia. apply Z.mod_small. lia. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?m) =>
    pose proof (st_ok_pi_region_nth E ssx _ 0 _ HS eq_refl) as HR0; rename m into ms2 end.
  pose proof (hb8_field4 E _ 33 (mv_c v) _ _ _ _ _ 0x2004 _ (mc_overflow mcc + 1) HR0 B33 ltac:(left; reflexivity) VOV)
    as VO.
  clear HR0 VOV.
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md2 := d) in *; clearbody md2 end.
  set (RWo := fun a => mv_c v + seg_spec.MC_OVERFLOW <= a < mv_c v + seg_spec.MC_OVERFLOW + 4).
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ RWo a -> aview SEGS H m1 a = aview SEGS H m0 a);
    [ intros a Ha Hn; refine (kept_of_frame Ex rs H m0 m1 RWo HFr _ a Ha Hn);
      intros bb wlo whi x Hin Hr; cbn [windows map ss_mem] in Hin;
      destruct Hin as [Hq | Hin];
      [ injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite B33 in Hr; unfold RWo, seg_spec.MC_OVERFLOW; lia | ];
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia | ]); destruct Hin
    | ] end.
  set (mco := mc_set_overflow (mc_overflow mcc + 1) mcc).
  assert (MC2 : sa_mconf (rdW Wc (ms_mem ms2)) (mv_c v) mco).
  { apply (hb8_mconf_ov (rdW Wc (ms_mem ms1)) _ (mv_c v) mcc (mc_overflow mcc + 1) HMC1).
    - intros a Ha Hn. apply K2; [unfold seg_spec.SEG_M_SIZE in Ha; lia | exact Hn].
    - apply hb8_sa_val4; [lia | exact VO].
    - lia. }
  assert (VSH2 : forall i, 4 <= i < 12 ->
    val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms2)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
  { intros i Hi. apply (mf_val_keep Wc Wc (ms_mem ms1) (ms_mem ms2) RWo _ 1 _ K2).
    - unfold SHADOW_OFF. lia.
    - change (Z.of_nat 1) with 1. unfold SHADOW_OFF in *. lia.
    - intros k Hk Hr. change (Z.of_nat 1) with 1 in Hk. unfold RWo, seg_spec.MC_OVERFLOW in Hr. lia.
    - exact (VSH1 i Hi). }
  assert (V136' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms2)) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur)).
  { apply (mf_val_keep Wc Wc (ms_mem ms1) (ms_mem ms2) RWo _ 8 _ K2).
    - lia.
    - change (Z.of_nat 8) with 8. lia.
    - intros k Hk Hr. change (Z.of_nat 8) with 8 in Hk. unfold RWo, seg_spec.MC_OVERFLOW in Hr. lia.
    - exact V136. }
  destruct (mf_keep_run_s B v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc cur (ms_mem ms2) md2 RWo MF_LOW_OFF cur mco
    CX CORE1 CELLS1 HJ K2) as (CORE2 & CELLS2 & LOOPK2).
  { intros a Ha. unfold mf_rw. right; left. unfold RWo, seg_spec.MC_OVERFLOW, seg_spec.SEG_M_SIZE in *. lia. }
  { intros a Ha Hs. exfalso. unfold RWo, seg_spec.MC_OVERFLOW in Ha. lia. }
  { exact VSH2. }
  { exact V136'. }
  { exact MC2. }
  assert (NP2 : mf_np v (ms_mem ms2) Wc (mf_next p rest)).
  { unfold mf_np, mf_slot in *. apply (mf_val_keep Wc Wc (ms_mem ms1) (ms_mem ms2) RWo _ 8 _ K2).
    - lia.
    - change (Z.of_nat 8) with 8. lia.
    - intros k Hk Hr. change (Z.of_nat 8) with 8 in Hk. unfold RWo, seg_spec.MC_OVERFLOW in Hr. lia.
    - exact NP1. }
  pose proof (LOOPK2 _ _ _ _ _ LOOP1) as LOOP2.
  (* the registers at the `jal`: a0 = s9 = c, a1 = s11 = line + 1 *)
  hb8_reg HS (10%bv : bv 5) Q10. rewrite (hb8_denot_atom E 25 _ (ER 25%nat 25%bv eq_refl)), R25 in Q10.
  hb8_reg HS (11%bv : bv 5) Q11. rewrite (hb8_denot_atom E 27 _ (ER 27%nat 27%bv eq_refl)), R27 in Q11.
  assert (Q2 : getr (ms_regs ms2) 2 = getr regs1 2) by (hb8_same HS0 HS (2%bv : bv 5)).
  assert (Q3 : getr (ms_regs ms2) 3 = getr regs1 3) by (hb8_same HS0 HS (3%bv : bv 5)).
  assert (Q4 : getr (ms_regs ms2) 4 = getr regs1 4) by (hb8_same HS0 HS (4%bv : bv 5)).
  assert (Q8 : getr (ms_regs ms2) 8 = getr regs1 8) by (hb8_same HS0 HS (8%bv : bv 5)).
  assert (Q9 : getr (ms_regs ms2) 9 = getr regs1 9) by (hb8_same HS0 HS (9%bv : bv 5)).
  assert (Q18 : getr (ms_regs ms2) 18 = getr regs1 18) by (hb8_same HS0 HS (18%bv : bv 5)).
  assert (Q23 : getr (ms_regs ms2) 23 = getr regs1 23) by (hb8_same HS0 HS (23%bv : bv 5)).
  assert (Q24 : getr (ms_regs ms2) 24 = getr regs1 24) by (hb8_same HS0 HS (24%bv : bv 5)).
  assert (Q19 : getr (ms_regs ms2) 19 = getr regs1 19) by (hb8_same HS0 HS (19%bv : bv 5)).
  assert (Q22 : getr (ms_regs ms2) 22 = getr regs1 22) by (hb8_same HS0 HS (22%bv : bv 5)).
  assert (Q25 : getr (ms_regs ms2) 25 = getr regs1 25) by (hb8_same HS0 HS (25%bv : bv 5)).
  assert (Q20 : getr (ms_regs ms2) 20 = getr regs1 20) by (hb8_same HS0 HS (20%bv : bv 5)).
  assert (Q27 : getr (ms_regs ms2) 27 = getr regs1 27) by (hb8_same HS0 HS (27%bv : bv 5)).
  pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms2) RA Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q19 Q22 Q25) as RA2.
  pose proof RA2 as ((R2' & R3' & R4' & R8' & _) & _).
  (* the model after m_refuse *)
  pose proof HFIN as HFIN'. rewrite (hb_mh_find_full mcc nm (line + 1) HFN Hge) in HFIN'. fold mco in HFIN'.
  pmkst HS. hb8_pc HB8_JREF2.
  apply (mf_refuse_step (fx := fx) B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 pos MF_LOW_OFF
    mco mcc false cur line p rest (mf_next p rest) HB8_JREF2 CX LS FRM
    (mf_corek_of_core B v lyc Sc Wc (ms_mem ms2) md2 pos MF_LOW_OFF mco CORE2) CELLS2 NP2 R2' R3' R4' R8' LOOP2 Hne
    eq_refl Lk0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Q10 Q11
    (mf_kept_le_refuse mco (line + 1) false None (line + 1) (lines (mf_rest rest)) (mf_final v) I HFIN')).
  intros fx1 ly2 S2 W2 regs3 mem3 md3 HFX LS3 CORE3 CELLS3 NP3 LOOP3 HCS.
  assert (Ely : ly2 = lyc) by (destruct LS3 as (E1 & _); destruct LS as (E2 & _); congruence). subst ly2.
  replace (HB8_JREF2 + 4) with MFB_RREF2 by (vm_compute; reflexivity).
  assert (H20 : getr regs3 20 = getr (ms_regs ms2) 20) by exact (HCS 20 ltac:(unfold acallee_saved; lia)).
  assert (H27 : getr regs3 27 = getr (ms_regs ms2) 27) by exact (HCS 27 ltac:(unfold acallee_saved; lia)).
  exact (RREF2 fx1 v lyc S2 W2 regs3 mem3 md3 pos mcc (m_refuse mco (line + 1) false) cur line p rest CX LS3
    (fxrel_frm0 fx fx1 FRM HFX) CORE3 CELLS3 (mf_regs_at_kept B v lyc pos (ms_regs ms2) regs3 RA2 HCS)
    Hlen Hne LOOP3 (hb4_mod_overflow (mv_k0 v) mcc (line + 1) Lk0) HFIN'
    ltac:(rewrite H20, Q20; exact R20) ltac:(rewrite H27, Q27; exact R27) NP3).
Qed.
End j.

(* the piece at every FP state (mf_hdrb_2.v's _F form) *)
Lemma hb8_nfind : forall n, MFB_NEWE_F B n -> MFB_RREF2_F B n -> MFB_NFIND_F B n.
Proof. intros n NEWE RREF2 fx0. exact (hb8_nfind_at (fx := fx0) n NEWE RREF2). Qed.
(* inside the Sections: the piece's Section hypotheses as its assumptions *)
Print Assumptions hb8_nfind.
End i.
End h.
End g.
About hb8_nfind.
Print Assumptions hb8_nfind.
