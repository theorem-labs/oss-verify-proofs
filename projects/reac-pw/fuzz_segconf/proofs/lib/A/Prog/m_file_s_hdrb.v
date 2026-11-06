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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 914 of its 958 lines of code are new or changed and 409 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), the segment S_MF_HDRB (MF-CUTS-A.md section 4): the m_find call,
   the not-found test, and THE SEGMENT, `s_mf_hdrb : S_MF_HDRB B`, chained from all its pieces. The HDRB segment lane of
   the G2 walk owner's G2 (pieces the HDRB top sub-lane and the chain). proves no function (kind: segment lemma of m_file's walk).
     hb_nfind  0x86b8c (MFH_NFIND) -> 0x86bfc (MFH_NEWE) or 0x86bd8 (MFH_RREF2): the instrumented check of the load of
               c->n (a load of the shadow byte at ((c + 0x2000) >> 3) + the shadow base and a compare; the error path,
               a call of errpath_load4, is not reached), the load, the test n < 32 (s3 = 0x20) to the new entry; on the
               overflow side the instrumented check of c->overflow, its load and store (overflow + 1; the store reuses
               the load's check) and m_refuse(c, line + 1) at 0x86bd4 (m_file_rf.v's MF_REFUSE_STEP).
     hb_hfind  0x86abc (MF_HFIND) -> 0x86c50 (MFH_JOIN), 0x86b18 (MFH_RREF1) or 0x86b8c (MFH_NFIND): m_find(c, name,
               |name|) at 0x86ac8 (m_find_c.v's contract through PaCall.cl_callS), the test of its result at 0x86acc;
               found (a0 = &c->seg[i]): the instrumented checks of g->gen and c->gen, the two loads, cur := g
               (136(s1)), the test g->gen <> c->gen to the join, else m_refuse(c, line + 1) at 0x86b14.
   The model steps are m_file_s_hdrb_1.v's hb_mh_find_* and m_file_s_hdrb_4.v's hb4_mod_*; the callee premises are
   m_file_s_hdrb_3.v's; the symbolic state at every start is m_file_sd.v's mf_seed (the spill slots read-only, or
   writable at 136(s1) only on the found path, and the cells of the block a read-only region at atom 33, but for
   c->overflow); the cut facts across a run or a call are m_file_k.v's mf_keep_run0 / mf_keep_run_s / mf_keep_call0;
   both m_refuse calls are m_file_rf.v's mf_refuse_step.
   Section hypotheses (the shared list, only those used): VOBJS, SIGP, SSP, RELRO, the two callees at every FP
   state, M_FIND (m_find_contract) and M_REFUSE (m_refuse_contract), and for the chain the two checked intrinsics
   AMEMCPY / AMEMSET (aintrin_realizes OCpy / OSet at the listing's targets), which m_file_s_hdrb_6.v and _7.v use.
     s_mf_hdrb  S_MF_HDRB B = forall n, MF_TAIL_F B n -> MF_HFIND_F B n, chained backwards from the tail through
               m_file_s_hdrb_5.v (JOIN, RREF2 from TAIL; RREF1, RMCPY from JOIN), _6.v (RMSET from RMCPY), _7.v (NEWE
               from RMSET), hb_nfind (NFIND from NEWE and RREF2) and hb_hfind (HFIND from JOIN, RREF1 and NFIND). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YL08 YN1f YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaNoChain PaArt PaFx SegObj SegGlob SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m
  m_file_mdl m_file_sd m_file_k m_file_rf m_file_s_hdrb_1 m_file_s_hdrb_2 m_file_s_hdrb_3 m_file_s_hdrb_4
  m_file_s_hdrb_5 m_file_s_hdrb_6 m_file_s_hdrb_7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the `jal` sites of this segment (listing offset = AF_m_file + (pc - 0x85ebc)) *)
Definition HB_JFIND : Z := AF_m_file + 0xc0c.   (* 0x86ac8 jal m_find *)
Definition HB_JREF1 : Z := AF_m_file + 0xc58.   (* 0x86b14 jal m_refuse, the found path *)
Definition HB_JREF2 : Z := AF_m_file + 0xd18.   (* 0x86bd4 jal m_refuse, the overflow path *)

(* ===================================== word and byte arithmetic ===================================== *)
(* `lw` of a 32-bit value below 2 ^ 31 is the value *)
Lemma hb_lw_small : forall z, 0 <= z < 2 ^ 31 -> sext 64 (bv_extract 0 32 (Z_to_bv 64 z)) = Z_to_bv 64 z.
Proof. intros z Hz. apply sext32_small. lia. Qed.
(* `lw` is injective on 32-bit values *)
Lemma hb_lw_inj : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  sext 64 (bv_extract 0 32 (Z_to_bv 64 x)) = sext 64 (bv_extract 0 32 (Z_to_bv 64 y)) -> x = y.
Proof.
intros x y Hx Hy E. rewrite !b_lw_val in E. unfold v_lw in E.
rewrite (unsigned_lit_small x), (unsigned_lit_small y) in E by lia.
apply (f_equal (@bv_unsigned 64)) in E. rewrite !Z_to_bv_unsigned in E.
unfold bv_wrap, bv_swrap, bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
change (bv_half_modulus 32) with (2 ^ 31) in E. change (bv_modulus 32) with (2 ^ 32) in E.
Z.div_mod_to_equations. lia.
Qed.


(* `blt a0,s3` with s3 = 32 and 0 <= a0 <= 32 *)
Lemma hb_blt32 : forall x, 0 <= x <= 32 -> branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 32) = (x <? 32).
Proof.
intros x Hx. assert (H : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/ x = 16 \/ x = 17 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27 \/ x = 28 \/ x = 29 \/ x = 30 \/ x = 31 \/ x = 32) by lia.
repeat (destruct H as [-> | H]; [vm_compute; reflexivity | ]). subst x. vm_compute. reflexivity.
Qed.

(* the block after the store of overflow: the model with overflow = z *)
Section mo.
Import seg_spec Mem.
Open Scope Z_scope.
Lemma hb_mconf_ov : forall (rd rd2 : reader) c mc z, sa_mconf rd c mc ->
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


(* `bne a0,a1` on two `lw` of 32-bit values *)
Lemma hb_bne_gen : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  branch_taken BC_NE (sext 64 (bv_extract 0 32 (Z_to_bv 64 x))) (sext 64 (bv_extract 0 32 (Z_to_bv 64 y))) =
  negb (x =? y).
Proof.
intros x y Hx Hy. cbn [branch_taken]. f_equal.
destruct (Z.eqb_spec x y) as [-> | Hne]; [apply bv_eqb_refl|].
apply bv_eqb_neq. intros E. apply Hne. exact (hb_lw_inj x y Hx Hy E).
Qed.
(* an atom plus an offset *)
Lemma hb_denot_off : forall E n x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n x k H Hx. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hx. reflexivity. Qed.

(* the cursor of a line-loop fact: any cursor that names an entry of the model *)
Lemma hb_loop_cur : forall {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing} v Wc memc mc cur cur' line p rest,
  mf_loop v Wc memc mc cur line p rest -> mf_cur_ok mc cur' -> mf_loop v Wc memc mc cur' line p rest.
Proof.
intros rc SK PI v Wc memc mc cur cur' line p rest (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11) Hc.
exact (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 (conj Hc (conj L7 (conj L8 (conj L9 (conj L10 L11)))))))))).
Qed.
(* an edit of one entry keeps the number of entries and the kept refusals *)
Lemma hb_upd_sizes : forall c i f, length (mc_seg (m_upd c i f)) = length (mc_seg c) /\
  length (mc_kept (m_upd c i f)) = length (mc_kept c).
Proof. intros c i f. unfold m_upd, m_set_segs. cbn [mc_seg mc_kept]. rewrite upd_nth_length. split; reflexivity. Qed.

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
Lemma hb_field4 : forall E m n b cs lo hi wlo whi od e z,
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
Lemma hb_sa_val4 : forall (H : word -> bool) (m : word -> option byte) a z, 0 <= z < 2 ^ 32 ->
  val_mem SEGS (mrestrict H m) a 4 z -> sa_val (aview SEGS H m) a 4 z.
Proof.
intros H m a z Hz Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256.
unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

Section i.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
(* the callees, at every FP state *)
Hypothesis M_FIND : forall fx0 : YK11.FPState, m_find_contract (fx := fx0) SEGS B (BASE + AF_m_find)
  SegInstA.STK_m_find SegInstA.RLO_A SegInstA.RHI_A.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.
(* the two checked intrinsics, at every FP state (only the chain s_mf_hdrb uses them, through m_file_s_hdrb_6.v's
   checked memcpy and _7.v's checked memset) *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).

(* ===================================== where the mconf block lies ===================================== *)
(* the block c lies below the stack window, apart from the side-stack frame and from its shadow *)
Lemma hb_geo : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
4096 <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\
mv_c v mod 16 = 0 /\
mv_c v + seg_spec.SEG_M_SIZE + 8192 <= mf_s1 (mv_sp v) /\ mf_s1 (mv_sp v) + 288 <= mv_sp v /\
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
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in Hslo.
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
pose proof (Z.mod_pos_bound (sp0 - 288) 32 ltac:(lia)) as M32.
unfold mf_s1. unfold seg_spec.SEG_M_SIZE in *. unfold SHADOW_OFF in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hc16|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* the five base atoms of the seed *)
Lemma hb_bases : forall v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs,
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
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in Hslo.
split; [|split; [|split; [|split]]]; cbn [base_val].
- rewrite (mfE_reg regs1 v lyc pos cur np xs 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small.
  unfold mf_s1. pose proof (Z.mod_pos_bound (sp0 - 288) 32 ltac:(lia)). lia.
- rewrite (mfE_reg regs1 v lyc pos cur np xs 8 8%bv eq_refl), R8. unfold w64. apply unsigned_lit_small. lia.
- rewrite E33. apply unsigned_lit_small. lia.
- rewrite E34. apply unsigned_lit_small. lia.
- rewrite E36. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
Qed.

(* a byte of the block is one the walk may write and is writable *)
Lemma hb_blk_wr : forall v lyc Sc Wc memc mdc pos lowsh mcc a,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
mv_c v + seg_spec.MC_N <= a < mv_c v + seg_spec.MC_REFUSED + 4 ->
awr_byte SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (ablocks B (mv_ly v) (mv_S v))
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

(* a symbolic value that is an atom denotes the atom's word *)
Lemma hb_denot_atom : forall E n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* the tactics of the walk *)
Ltac hb_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
end.
(* a register the run did not change: the same symbolic value before and after *)
Ltac hb_same HS0 HS r :=
lazymatch type of HS0 with st_ok_pi _ _ ?E0 ?ss0 (restrict ?H0 ?ms0) =>
  let A := fresh "A" in let B' := fresh "B" in
  hb_reg HS0 r A; hb_reg HS r B'; rewrite B'; rewrite <- A; reflexivity
end.
Ltac hb_norm HS := lazymatch type of HS with
| st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
Ltac hb_awr_norm := lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
  let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
Ltac hb_awr_ro := repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* a run whose regions are all read-only changed no byte *)
Ltac hb_kept0 K := lazymatch goal with
| HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m1 a = aview SEGS H m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs H m0 m1 (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hin Hr; cbn [windows map ss_mem] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia | ]); destruct Hin
  | ] end.
Ltac hb_pc pc := lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?k)) _ _) _) _ =>
  let Hk := fresh in assert (Hk : k = pc) by (vm_compute; reflexivity); rewrite Hk; clear Hk end.


Section j.
Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ===================================== hb_nfind: 0x86b8c, m_find found nothing =====================================
   the seed at MFH_NFIND with xs = [n; overflow] (atoms 52, 53); the spill slots read-only, s3 pinned to 0x20, c->n a
   read-only region at atom 33; the shadow entry of the block [c, c + 9144) covers every check *)
Lemma hb_nfind_at : forall n, MFH_NEWE_F B n -> MFH_RREF2_F B n -> MFH_NFIND_stmt B n.
Proof.
intros n NEWE RREF2 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest o nm CX LS FRM CORE CELLS RA R24 Hlen Hne LOOP
  HNM HFN HFIN R21 R20 R22 R23 NP.
unfold mf_at.
pose proof CORE as (HJ & HPm & VFL & VSH & VSV & V112 & HMC & HMA & HMT).
destruct (hb_mconf_bounds _ _ _ HMC) as (Bseg & Bkept & Bgen & Bref & Bov & Bsg).
pose proof LOOP as (_ & _ & _ & _ & _ & Lcur & Lk0 & Lline0 & Lline & Lref & Lov).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Lcur) as HCUR.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as HNP.
destruct (hb_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G13).
unfold seg_spec.SEG_M_SIZE in G2, G5, G7, G8.
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as G11.
pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as G12.
set (nn := Z.of_nat (length (mc_seg mcc))) in *.
set (xs := [nn; mc_overflow mcc]).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs MFH_NFIND
  true true [] false false [] false CX CORE (mf_regs_base_of B v lyc pos regs1 RA) (fun _ => CELLS) HCUR (fun _ => NP)
  HNP ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs 9144 CX CORE
  ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as SH33.
destruct (hb_bases v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs CX CORE
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
(* the spill slots read-only, s3 = 0x20, the region of c->n *)
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS eq_refl
  eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow SEGS E _ _ 0 0 (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) ltac:(intros o' Ho'; lia))) as HS1.
clear HS.
pose proof (st_ok_pi_pin_reg' E _ _ (19%bv : bv 5) 0x20 HS1 R19 eq_refl) as HS2. clear HS1.
hb_norm HS2.
set (rN := YP09.mkRegion (Some 33%nat) 0x2000 0x2004 0 0 [YP09.mkChunk 0x2000 (CVal 4 (SOff 52 0))]).
assert (RN : region_ok SEGS E (mrestrict (w_H Wc) memc) rN).
{ unfold region_ok, rN. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B33.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (mv_c v) 0x2000 4 (SOff 52 0) nn).
  - apply hb_denot_atom. exact E52.
  - cbn. lia.
  - cbn. lia.
  - exact (val_mem_of_rd32 SEGS (w_H Wc) memc (mv_c v + 0x2000) nn (hb_rd_n _ _ _ HMC)). }
assert (DN : all_disjoint E rN (ss_mem (ltac:(lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => exact ss end)))).
{ apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold zdisj, extent_of_region, rN.
  cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?B2, ?B8, ?B33, ?B34, ?B36.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ rN HS2 eq_refl RN DN) as HS. clear HS2 RN DN.
hb_norm HS.
pose proof HS as HS0.
(* run 1: 0x86b8c .. 0x86ba4, the check and the load of c->n, stopped at `blt a0,s3` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ hb_awr_norm. hb_awr_ro. }
hb_kept0 K1.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md1 := d) in *; clearbody md1 end.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms1) md1 CX CORE CELLS HJ K1)
  as (CORE1 & CELLS1 & NPK1 & LOOPK1).
pose proof (NPK1 _ NP) as NP1. pose proof (LOOPK1 _ _ _ _ _ LOOP) as LOOP1. clear NPK1 LOOPK1 K1.
pose proof CORE1 as (_ & _ & _ & VSH1 & _ & _ & HMC1 & _).
pose proof CELLS1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
(* the test `blt a0,s3` (a0 = n, s3 = 32) *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n < 32: to the new entry *)
  assert (Hlt : (length (mc_seg mcc) < 32)%nat).
  { change (sv_denot E (SExt true 32 (SOff 52 0))) with (sext 64 (bv_extract 0 32 (sv_denot E (SOff 52 0)))) in Hc.
    rewrite (hb_denot_atom E 52 _ E52), hb_lw_small in Hc by (unfold nn; lia).
    change (sv_denot E (SLit 32)) with (Z_to_bv 64 32) in Hc.
    rewrite hb_blt32 in Hc by (unfold nn; lia). apply Z.ltb_lt in Hc. unfold nn in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MFH_NEWE.
  { hb_awr_norm. hb_awr_ro. }
  hb_kept0 K2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md2 := d) in *; clearbody md2 end.
  destruct (mf_keep_run0 B v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc cur (ms_mem ms2) md2 CX CORE1 CELLS1 HJ K2)
    as (CORE2 & CELLS2 & NPK2 & LOOPK2).
  hb_reg HS (10%bv : bv 5) Q10.
  change (sv_denot E (SExt true 32 (SOff 52 0))) with (sext 64 (bv_extract 0 32 (sv_denot E (SOff 52 0)))) in Q10.
  rewrite (hb_denot_atom E 52 _ E52), hb_lw_small in Q10 by (unfold nn; lia).
  hb_reg HS (11%bv : bv 5) Q11.
  change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 8192) (SLit 3)) (SOff 32 0)) with (mf_shx 33 8192) in Q11.
  rewrite (mf_denot_shx E 33 (mv_c v) 8192 E33 E32 ltac:(lia) ltac:(lia) ltac:(lia)) in Q11.
  assert (Q2 : getr (ms_regs ms2) 2 = getr regs1 2) by (hb_same HS0 HS (2%bv : bv 5)).
  assert (Q3 : getr (ms_regs ms2) 3 = getr regs1 3) by (hb_same HS0 HS (3%bv : bv 5)).
  assert (Q4 : getr (ms_regs ms2) 4 = getr regs1 4) by (hb_same HS0 HS (4%bv : bv 5)).
  assert (Q8 : getr (ms_regs ms2) 8 = getr regs1 8) by (hb_same HS0 HS (8%bv : bv 5)).
  assert (Q9 : getr (ms_regs ms2) 9 = getr regs1 9) by (hb_same HS0 HS (9%bv : bv 5)).
  assert (Q18 : getr (ms_regs ms2) 18 = getr regs1 18) by (hb_same HS0 HS (18%bv : bv 5)).
  assert (Q19 : getr (ms_regs ms2) 19 = getr regs1 19) by (hb_same HS0 HS (19%bv : bv 5)).
  assert (Q20 : getr (ms_regs ms2) 20 = getr regs1 20) by (hb_same HS0 HS (20%bv : bv 5)).
  assert (Q21 : getr (ms_regs ms2) 21 = getr regs1 21) by (hb_same HS0 HS (21%bv : bv 5)).
  assert (Q22 : getr (ms_regs ms2) 22 = getr regs1 22) by (hb_same HS0 HS (22%bv : bv 5)).
  assert (Q24 : getr (ms_regs ms2) 24 = getr regs1 24) by (hb_same HS0 HS (24%bv : bv 5)).
  assert (Q25 : getr (ms_regs ms2) 25 = getr regs1 25) by (hb_same HS0 HS (25%bv : bv 5)).
  assert (Q26 : getr (ms_regs ms2) 26 = getr regs1 26) by (hb_same HS0 HS (26%bv : bv 5)).
  pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms2) RA Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q25 Q26) as RA2.
  pmkst HS. hb_pc MFH_NEWE.
  exact (NEWE fx v lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 pos mcc cur line p rest o nm CX LS FRM CORE2 CELLS2 RA2
    ltac:(rewrite Q24; exact R24) Hlen Hne (LOOPK2 _ _ _ _ _ LOOP1) HNM HFN Hlt HFIN Q10 Q11
    ltac:(rewrite Q21; exact R21) ltac:(rewrite Q20; exact R20) ltac:(rewrite Q22; exact R22) (NPK2 _ NP1)).
- (* 32 <= n: overflow + 1 and m_refuse *)
  assert (Hge : (32 <= length (mc_seg mcc))%nat).
  { change (sv_denot E (SExt true 32 (SOff 52 0))) with (sext 64 (bv_extract 0 32 (sv_denot E (SOff 52 0)))) in Hc.
    rewrite (hb_denot_atom E 52 _ E52), hb_lw_small in Hc by (unfold nn; lia).
    change (sv_denot E (SLit 32)) with (Z_to_bv 64 32) in Hc.
    rewrite hb_blt32 in Hc by (unfold nn; lia). apply Z.ltb_ge in Hc. unfold nn in Hc. lia. }
  assert (Hov1 : mc_overflow mcc + 1 < 2 ^ 32)
    by (destruct rest as [|r0 rr]; [congruence | cbn [length] in Lov; lia]).
  hb_norm HS.
  set (rO := YP09.mkRegion (Some 33%nat) 0x2004 0x2008 0x2004 0x2008 [YP09.mkChunk 0x2004 (CVal 4 (SOff 53 0))]).
  assert (RO1 : region_ok SEGS E (mrestrict (w_H Wc) (ms_mem ms1)) rO).
  { unfold region_ok, rO. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B33. split; [lia|]. split; [lia|]. split.
    - intros o' Ho'. exact (proj2 (hb_blk_wr v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc (mv_c v + o') CX CORE1
        ltac:(unfold seg_spec.MC_N, seg_spec.MC_REFUSED; lia))).
    - apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (mv_c v) 0x2004 4 (SOff 53 0) (mc_overflow mcc)).
      + apply hb_denot_atom. exact E53.
      + cbn. lia.
      + cbn. lia.
      + exact (val_mem_of_rd32 SEGS (w_H Wc) (ms_mem ms1) (mv_c v + 0x2004) _ (hb_rd_overflow _ _ _ HMC1)). }
  assert (DO : all_disjoint E rO (ss_mem (ltac:(lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => exact ss end)))).
  { apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold zdisj, extent_of_region, rO.
    cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?B2, ?B8, ?B33, ?B34, ?B36.
    repeat split; lia. }
  pose proof (st_ok_pi_add_region E _ _ rO HS eq_refl RO1 DO) as HS3. clear HS RO1 DO. rename HS3 into HS.
  hb_norm HS.
  (* run 2: 0x86ba8 .. 0x86bd4, the check, the load and the store of c->overflow, a0 = c, a1 = line + 1 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HB_JREF2.
  { hb_awr_norm.
    eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v));
    [ reflexivity | exact B33
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
      exact (proj1 (hb_blk_wr v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc a CX CORE1
        ltac:(unfold seg_spec.MC_N, seg_spec.MC_REFUSED; lia)))
    | ].
    hb_awr_ro. }
  (* the store: overflow + 1 in c->overflow *)
  assert (VOV : bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 53 0)) (SLit 1))) mod 2 ^ 32 =
    mc_overflow mcc + 1).
  { change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 53 0)) (SLit 1))) with
      (alu64 ALU_ADD (sext 64 (bv_extract 0 32 (sv_denot E (SOff 53 0)))) (Z_to_bv 64 1)).
    rewrite (hb_denot_atom E 53 _ E53). rewrite YN0d.ctr_chunk_mod by lia. apply Z.mod_small. lia. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?m) =>
    pose proof (st_ok_pi_region_nth E ssx _ 0 _ HS eq_refl) as HR0; rename m into ms2 end.
  pose proof (hb_field4 E _ 33 (mv_c v) _ _ _ _ _ 0x2004 _ (mc_overflow mcc + 1) HR0 B33 ltac:(left; reflexivity) VOV)
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
  { apply (hb_mconf_ov (rdW Wc (ms_mem ms1)) _ (mv_c v) mcc (mc_overflow mcc + 1) HMC1).
    - intros a Ha Hn. apply K2; [unfold seg_spec.SEG_M_SIZE in Ha; lia | exact Hn].
    - apply hb_sa_val4; [lia | exact VO].
    - lia. }
  assert (RWB : forall a, RWo a -> mv_c v + 9236 + 8192 <= mf_s1 (mv_sp v) /\ mv_c v <= a < mv_c v + 9236)
    by (intros a Ha; unfold RWo, seg_spec.MC_OVERFLOW in Ha; split; lia).
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
  { unfold mf_np in *. apply (mf_val_keep Wc Wc (ms_mem ms1) (ms_mem ms2) RWo _ 8 _ K2).
    - lia.
    - change (Z.of_nat 8) with 8. lia.
    - intros k Hk Hr. change (Z.of_nat 8) with 8 in Hk. unfold RWo, seg_spec.MC_OVERFLOW in Hr. lia.
    - exact NP1. }
  pose proof (LOOPK2 _ _ _ _ _ LOOP1) as LOOP2.
  (* the registers at the `jal`: a0 = s5 = c, a1 = s6 = line + 1 *)
  hb_reg HS (10%bv : bv 5) Q10. rewrite (hb_denot_atom E 33 _ E33) in Q10.
  hb_reg HS (11%bv : bv 5) Q11. rewrite (hb_denot_atom E 22 _ (ER 22%nat 22%bv eq_refl)), R22 in Q11.
  hb_reg HS (21%bv : bv 5) Q21. rewrite (hb_denot_atom E 33 _ E33) in Q21.
  assert (Q2 : getr (ms_regs ms2) 2 = getr regs1 2) by (hb_same HS0 HS (2%bv : bv 5)).
  assert (Q3 : getr (ms_regs ms2) 3 = getr regs1 3) by (hb_same HS0 HS (3%bv : bv 5)).
  assert (Q4 : getr (ms_regs ms2) 4 = getr regs1 4) by (hb_same HS0 HS (4%bv : bv 5)).
  assert (Q8 : getr (ms_regs ms2) 8 = getr regs1 8) by (hb_same HS0 HS (8%bv : bv 5)).
  assert (Q9 : getr (ms_regs ms2) 9 = getr regs1 9) by (hb_same HS0 HS (9%bv : bv 5)).
  assert (Q18 : getr (ms_regs ms2) 18 = getr regs1 18) by (hb_same HS0 HS (18%bv : bv 5)).
  assert (Q19 : getr (ms_regs ms2) 19 = getr regs1 19) by (hb_same HS0 HS (19%bv : bv 5)).
  assert (Q22 : getr (ms_regs ms2) 22 = getr regs1 22) by (hb_same HS0 HS (22%bv : bv 5)).
  assert (Q24 : getr (ms_regs ms2) 24 = getr regs1 24) by (hb_same HS0 HS (24%bv : bv 5)).
  assert (Q25 : getr (ms_regs ms2) 25 = getr regs1 25) by (hb_same HS0 HS (25%bv : bv 5)).
  assert (Q26 : getr (ms_regs ms2) 26 = getr regs1 26) by (hb_same HS0 HS (26%bv : bv 5)).
  pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms2) RA Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q25 Q26) as RA2.
  pose proof RA2 as (R2' & R3' & R4' & R8' & _).
  (* the model after m_refuse *)
  pose proof HFIN as HFIN'. rewrite (hb_mh_find_full mcc nm (line + 1) HFN Hge) in HFIN'. fold mco in HFIN'.
  pmkst HS. hb_pc HB_JREF2.
  apply (mf_refuse_step (fx := fx) B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 pos MF_LOW_OFF
    mco mcc false cur line p rest (mf_next p rest) HB_JREF2 CX LS FRM
    (mf_corek_of_core B v lyc Sc Wc (ms_mem ms2) md2 pos MF_LOW_OFF mco CORE2) CELLS2 NP2 R2' R3' R4' R8' LOOP2 Hne
    eq_refl Lk0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Q10 Q11
    (mf_kept_le_refuse mco (line + 1) false None (line + 1) (lines (mf_rest rest)) (mf_final v) I HFIN')).
  intros fx1 ly2 S2 W2 regs3 mem3 md3 HFX LS3 CORE3 CELLS3 NP3 LOOP3 HCS.
  assert (Ely : ly2 = lyc) by (destruct LS3 as (E1 & _); destruct LS as (E2 & _); congruence). subst ly2.
  replace (HB_JREF2 + 4) with MFH_RREF2 by (vm_compute; reflexivity).
  assert (H21 : getr regs3 21 = getr (ms_regs ms2) 21) by exact (HCS 21 ltac:(unfold acallee_saved; lia)).
  assert (H22 : getr regs3 22 = getr (ms_regs ms2) 22) by exact (HCS 22 ltac:(unfold acallee_saved; lia)).
  assert (H24 : getr regs3 24 = getr (ms_regs ms2) 24) by exact (HCS 24 ltac:(unfold acallee_saved; lia)).
  exact (RREF2 fx1 v lyc S2 W2 regs3 mem3 md3 pos mcc (m_refuse mco (line + 1) false) cur line p rest CX LS3
    (fxrel_frm0 fx fx1 FRM HFX) CORE3 CELLS3 (mf_regs_at_kept B v lyc pos (ms_regs ms2) regs3 RA2 HCS)
    ltac:(rewrite H24, Q24; exact R24) Hlen Hne LOOP3 (hb4_mod_overflow (mv_k0 v) mcc (line + 1) Lk0) HFIN'
    ltac:(rewrite H21; exact Q21) ltac:(rewrite H22, Q22; exact R22) NP3).
Qed.

(* ===================================== hb_hfind: 0x86abc, m_find =====================================
   the seed at MF_HFIND with no extra atom, the spill slots read-only; one run to the `jal m_find` (no instrumented
   check on the way); the call by PaCall.cl_callS; at the return 0x86acc a new seed, with m_find's result split *)
Lemma hb_hfind_at : forall n, MFH_JOIN_F B n -> MFH_RREF1_F B n -> MFH_NFIND_F B n -> MF_HFIND_stmt B n.
Proof.
intros n JOIN RREF1 NFIND v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest o nm CX LS FRM CORE CELLS RA R24 Hlen Hne
  LOOP Hnm Hon Hfs HFIN R21 R20 R22 R23 NP.
assert (HNM : hb_nm rest o nm) by exact (conj Hnm (conj Hon Hfs)).
unfold mf_at.
pose proof CORE as (HJ & HPm & VFL & VSH & VSV & V112 & HMC & HMA & HMT).
destruct (hb_mconf_bounds _ _ _ HMC) as (Bseg & Bkept & Bgen & Bref & Bov & Bsg).
pose proof LOOP as (_ & _ & _ & _ & _ & Lcur & Lk0 & Lline0 & Lline & Lref & Lov).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Lcur) as HCUR.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as HNP.
destruct (hb_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G13).
unfold seg_spec.SEG_M_SIZE in G2, G5, G7, G8.
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as G11.
pose proof (Z.mul_div_le (frame_addr lyc 1 pos) 8 ltac:(lia)) as G14.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
destruct (hb3_find_pre B v lyc Sc Wc memc mdc pos mcc cur line p rest o nm CX CORE LOOP HNM) as (_ & Hzs & Hname & Hn64).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] MF_HFIND
  true true [] false false [] false CX CORE (mf_regs_base_of B v lyc pos regs1 RA) (fun _ => CELLS) HCUR (fun _ => NP)
  HNP ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) [] 1 ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth mf_extra map app] in E33.
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (mfE regs1 v lyc pos cur (mf_next p rest) []) k = getr regs1 r) by (intros; apply mfE_reg; assumption).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS, E33, ER.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clearbody E.
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS eq_refl
  eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow SEGS E _ _ 0 0 (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) ltac:(intros o' Ho'; lia))) as HS1.
clear HS. rename HS1 into HS. hb_norm HS.
pose proof HS as HS0.
(* run: 0x86abc .. 0x86ac8, a0 = c (128(s1)), a1 = s5, a2 = s4, the `jal m_find` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ hb_awr_norm. hb_awr_ro. }
hb_kept0 K1. clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms1 end.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md1 := d) in *; clearbody md1 end.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms1) md1 CX CORE CELLS HJ K1)
  as (CORE1 & CELLS1 & NPK1 & LOOPK1).
pose proof (NPK1 _ NP) as NP1. pose proof (LOOPK1 _ _ _ _ _ LOOP) as LOOP1. clear NPK1 LOOPK1 K1.
(* the registers at m_find's entry: a0 = c, a1 = the name, a2 = its length, ra = BASE + MFH_RFIND *)
hb_reg HS (10%bv : bv 5) A10. rewrite (hb_denot_atom E 33 _ E33) in A10.
hb_reg HS (11%bv : bv 5) A11. rewrite (hb_denot_atom E 21 _ (ER 21%nat 21%bv eq_refl)), R21 in A11.
hb_reg HS (12%bv : bv 5) A12. rewrite (hb_denot_atom E 20 _ (ER 20%nat 20%bv eq_refl)), R20 in A12.
assert (HRF : MFH_RFIND = 7576) by (vm_compute; reflexivity).
hb_reg HS (1%bv : bv 5) A1. change (SOff 240 7576) with (SOff A_TEXT MFH_RFIND) in A1.
rewrite (codeptr_val E MFH_RFIND HEI) in A1.
assert (Q2 : getr (ms_regs ms1) 2 = getr regs1 2) by (hb_same HS0 HS (2%bv : bv 5)).
assert (Q3 : getr (ms_regs ms1) 3 = getr regs1 3) by (hb_same HS0 HS (3%bv : bv 5)).
assert (Q4 : getr (ms_regs ms1) 4 = getr regs1 4) by (hb_same HS0 HS (4%bv : bv 5)).
assert (Q8 : getr (ms_regs ms1) 8 = getr regs1 8) by (hb_same HS0 HS (8%bv : bv 5)).
assert (Q9 : getr (ms_regs ms1) 9 = getr regs1 9) by (hb_same HS0 HS (9%bv : bv 5)).
assert (Q18 : getr (ms_regs ms1) 18 = getr regs1 18) by (hb_same HS0 HS (18%bv : bv 5)).
assert (Q19 : getr (ms_regs ms1) 19 = getr regs1 19) by (hb_same HS0 HS (19%bv : bv 5)).
assert (Q20 : getr (ms_regs ms1) 20 = getr regs1 20) by (hb_same HS0 HS (20%bv : bv 5)).
assert (Q21 : getr (ms_regs ms1) 21 = getr regs1 21) by (hb_same HS0 HS (21%bv : bv 5)).
assert (Q22 : getr (ms_regs ms1) 22 = getr regs1 22) by (hb_same HS0 HS (22%bv : bv 5)).
assert (Q23 : getr (ms_regs ms1) 23 = getr regs1 23) by (hb_same HS0 HS (23%bv : bv 5)).
assert (Q24 : getr (ms_regs ms1) 24 = getr regs1 24) by (hb_same HS0 HS (24%bv : bv 5)).
assert (Q25 : getr (ms_regs ms1) 25 = getr regs1 25) by (hb_same HS0 HS (25%bv : bv 5)).
assert (Q26 : getr (ms_regs ms1) 26 = getr regs1 26) by (hb_same HS0 HS (26%bv : bv 5)).
pose proof (mf_regs_at_of B v lyc pos regs1 (ms_regs ms1) RA Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q25 Q26) as RA1.
assert (SIGF : SIGMA SS_m_find = BASE + AF_m_find).
{ rewrite (SIGP SS_m_find) by (unfold seg_prog_syms; cbn [In]; tauto). first [reflexivity | f_equal; vm_compute; reflexivity]. }
pmkst HS. rewrite SIGF.
(* the call: PaCall.cl_callS with m_find's contract *)
destruct (mf_s1_facts B v CX) as (Hs1 & Hs1m & Hceil).
pose proof (mf_sp_at B v lyc pos (ms_regs ms1) CX RA1) as Hsp1.
assert (Hsp : spZ (ms_regs ms1) = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) by lia.
assert (Ho16 : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0).
{ destruct Hs1 as [E1 | E1]; rewrite E1.
  - replace (mv_sp v - 288 - mv_sp v) with (-18 * 16) by lia. apply Z_mod_mult.
  - replace (mv_sp v - 304 - mv_sp v) with (-19 * 16) by lia. apply Z_mod_mult. }
destruct (mf_chain_at B v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc (ms_regs ms1) CX CORE1 RA1) as (ch1 & CH1).
pose proof (mf_rod_now B RELRO v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc CX CORE1) as ROD1.
pose proof (mf_nev B v lyc Sc Wc (ms_mem ms1) md1 pos MF_LOW_OFF mcc CX CORE1) as NEV1.
destruct (hb3_find_pre B v lyc Sc Wc (ms_mem ms1) md1 pos mcc cur line p rest o nm CX CORE1 LOOP1 HNM)
  as (FPRE1 & _ & _ & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (HSTK1 : SegInstA.STK_m_find = 8240) by reflexivity.
eapply SRr_bind.
{ apply (cl_callS B LAWS Wc (ms_regs ms1) (ms_mem ms1) (Z_to_bv 64 (BASE + AF_m_find)) SegInstA.STK_m_file (mv_sp v)
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)]
    lyc Sc md1 0 SegInstA.STK_m_find [] EV_m_find (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + MFH_RFIND)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 (m_find_ptr (mv_c v) mcc (seg_spec.zs (seg_spec.zb nm))) /\
       sa_kept SEGS Wc (ms_mem ms1) W2 mem2 (ms_regs ms1) SegInstA.STK_m_find (fun _ => False) /\
       sa_noalloc B lyc Sc ly2 S2)
    HJ Hsp Ho16).
  - destruct Hs1 as [E1 | E1]; rewrite E1; lia.
  - rewrite HSTK1. lia.
  - rewrite HSTK, HSTK1. destruct Hs1 as [E1 | E1]; rewrite E1; lia.
  - pose proof RA1 as (_ & R3' & _). exact R3'.
  - pose proof RA1 as (_ & _ & R4' & _). exact R4'.
  - exact A1.
  - apply ret_ok_codeptr_v; rewrite HRF; [lia | reflexivity].
  - rewrite unsigned_lit_small by (rewrite HRF; lia). rewrite HRF. lia.
  - replace (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) with (spZ (ms_regs ms1)) by lia. exact CH1.
  - intros HPRE1. eapply SRr_mono.
    + apply (M_FIND fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 ch1 (mv_c v) (p + Z.of_nat o) (Z.of_nat (length nm))
        mcc (seg_spec.zb nm) HPRE1 ROD1 A10 ltac:(lia) A11 Hname A12 Hn64 FPRE1).
      unfold EV_m_find. exact NEV1.
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, A1; reflexivity|]. split; [exact HJc|].
      split; [exact HPr | exact HK].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (A0 & HKP & HNA)).
destruct (mf_keep_call0 B v lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 pos MF_LOW_OFF mcc cur ly3 S3 W3 regs3 mem3 md3
  (0 + EV_m_find) SegInstA.STK_m_find CX CORE1 CELLS1 RA1 HJo ltac:(unfold EV_m_find; lia) HP3 HNA
  ltac:(rewrite HSTK1; unfold SegInstA.STK_fuzz_catalogue_row, ESTACK; lia) HKP)
  as (Ely3 & LSK & CORE3 & CELLS3 & RA3 & NPK3 & LOOPK3).
subst ly3. pose proof (LSK LS) as LS3. pose proof (NPK3 _ NP1) as NP3. pose proof (LOOPK3 _ _ _ _ _ LOOP1) as LOOP3.
clear LSK NPK3 LOOPK3 HJi HKP HNA.
rewrite Hzs in A0. unfold m_find_ptr in A0.
assert (P20 : getr regs3 20 = getr regs1 20) by (rewrite <- Q20; exact (HP3 20 ltac:(unfold acallee_saved; lia))).
assert (P21 : getr regs3 21 = getr regs1 21) by (rewrite <- Q21; exact (HP3 21 ltac:(unfold acallee_saved; lia))).
assert (P22 : getr regs3 22 = getr regs1 22) by (rewrite <- Q22; exact (HP3 22 ltac:(unfold acallee_saved; lia))).
assert (P23 : getr regs3 23 = getr regs1 23) by (rewrite <- Q23; exact (HP3 23 ltac:(unfold acallee_saved; lia))).
assert (P24 : getr regs3 24 = getr regs1 24) by (rewrite <- Q24; exact (HP3 24 ltac:(unfold acallee_saved; lia))).
replace (0 + EV_m_find) with 0 in HJo by (unfold EV_m_find; lia).
repeat match goal with H : context [E] |- _ => clear H end. clear E.
destruct (m_find mcc nm) as [i|] eqn:Ef.
2:{ (* not found: a0 = 0, the `beqz` to MFH_NFIND *)
  pose proof (mf_seed B VOBJS v lyc S3 W3 regs3 mem3 md3 pos MF_LOW_OFF mcc cur (mf_next p rest) [] MFH_RFIND
    true true [] false false [] false CX CORE3 (mf_regs_base_of B v lyc pos regs3 RA3) (fun _ => CELLS3) HCUR
    (fun _ => NP3) HNP ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
  set (E := mfE regs3 v lyc pos cur (mf_next p rest) []) in HS.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
  clearbody E.
  pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS eq_refl
    eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ _ 0 0 (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) ltac:(intros o' Ho'; lia))) as HS1.
  clear HS.
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS. clear HS1.
  hb_norm HS. pose proof HS as HS0.
  paj_run_to_tok RUNTO HS HJo SHOK Bspan MFH_NFIND.
  { hb_awr_norm. hb_awr_ro. }
  hb_kept0 K4. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms4 end.
  lazymatch type of HJo with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md4 := d) in *; clearbody md4 end.
  destruct (mf_keep_run0 B v lyc S3 W3 mem3 md3 pos MF_LOW_OFF mcc cur (ms_mem ms4) md4 CX CORE3 CELLS3 HJo K4)
    as (CORE4 & CELLS4 & NPK4 & LOOPK4).
  assert (T2 : getr (ms_regs ms4) 2 = getr regs3 2) by (hb_same HS0 HS (2%bv : bv 5)).
  assert (T3 : getr (ms_regs ms4) 3 = getr regs3 3) by (hb_same HS0 HS (3%bv : bv 5)).
  assert (T4 : getr (ms_regs ms4) 4 = getr regs3 4) by (hb_same HS0 HS (4%bv : bv 5)).
  assert (T8 : getr (ms_regs ms4) 8 = getr regs3 8) by (hb_same HS0 HS (8%bv : bv 5)).
  assert (T9 : getr (ms_regs ms4) 9 = getr regs3 9) by (hb_same HS0 HS (9%bv : bv 5)).
  assert (T18 : getr (ms_regs ms4) 18 = getr regs3 18) by (hb_same HS0 HS (18%bv : bv 5)).
  assert (T19 : getr (ms_regs ms4) 19 = getr regs3 19) by (hb_same HS0 HS (19%bv : bv 5)).
  assert (T20 : getr (ms_regs ms4) 20 = getr regs3 20) by (hb_same HS0 HS (20%bv : bv 5)).
  assert (T21 : getr (ms_regs ms4) 21 = getr regs3 21) by (hb_same HS0 HS (21%bv : bv 5)).
  assert (T22 : getr (ms_regs ms4) 22 = getr regs3 22) by (hb_same HS0 HS (22%bv : bv 5)).
  assert (T23 : getr (ms_regs ms4) 23 = getr regs3 23) by (hb_same HS0 HS (23%bv : bv 5)).
  assert (T24 : getr (ms_regs ms4) 24 = getr regs3 24) by (hb_same HS0 HS (24%bv : bv 5)).
  assert (T25 : getr (ms_regs ms4) 25 = getr regs3 25) by (hb_same HS0 HS (25%bv : bv 5)).
  assert (T26 : getr (ms_regs ms4) 26 = getr regs3 26) by (hb_same HS0 HS (26%bv : bv 5)).
  pose proof (mf_regs_at_of B v lyc pos regs3 (ms_regs ms4) RA3 T2 T3 T4 T8 T9 T18 T19 T25 T26) as RA4.
  pmkst HS. hb_pc MFH_NFIND.
  exact (NFIND fx v lyc S3 W3 (ms_regs ms4) (ms_mem ms4) md4 pos mcc cur line p rest o nm CX LS3 FRM CORE4 CELLS4 RA4
    ltac:(rewrite T24, P24; exact R24) Hlen Hne (LOOPK4 _ _ _ _ _ LOOP3) HNM Ef HFIN
    ltac:(rewrite T21, P21; exact R21) ltac:(rewrite T20, P20; exact R20) ltac:(rewrite T22, P22; exact R22)
    ltac:(rewrite T23, P23; exact R23) (NPK4 _ NP3)). }
(* found: a0 = g = &c->seg[i]; the seed at MFH_RFIND with xs = [g; g->gen; c->gen] (atoms 52, 53, 54) *)
pose proof (m_find_lt mcc nm i Ef) as Hi.
assert (Hi32 : Z.of_nat i <= 31) by lia.
set (g := seg_spec.mseg_addr (mv_c v) i) in *.
assert (Hg : g = mv_c v + 256 * Z.of_nat i) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
set (ggen := ms_gen (nth i (mc_seg mcc) mseg_d)).
pose proof (Bsg i Hi) as Bgg. fold ggen in Bgg.
set (xs := [g; ggen; mc_gen mcc]).
pose proof CORE3 as (_ & _ & _ & VSH3 & _ & _ & HMC3 & HMA3 & _).
pose proof (mf_seed B VOBJS v lyc S3 W3 regs3 mem3 md3 pos MF_LOW_OFF mcc cur (mf_next p rest) xs MFH_RFIND
  true true [] false false [] false CX CORE3 (mf_regs_base_of B v lyc pos regs3 RA3) (fun _ => CELLS3) HCUR
  (fun _ => NP3) HNP ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (mf_she_blk B v lyc S3 W3 regs3 mem3 md3 pos MF_LOW_OFF mcc cur (mf_next p rest) xs 9144 CX CORE3
  ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as SH33.
destruct (hb_bases v lyc S3 W3 regs3 mem3 md3 pos MF_LOW_OFF mcc cur (mf_next p rest) xs CX CORE3
  (mf_regs_base_of B v lyc pos regs3 RA3)) as (B2 & B8 & B33 & B34 & B36).
cbn [base_val] in B2, B8, B33, B34, B36.
pose proof (mfE_xs regs3 v lyc pos cur (mf_next p rest) xs 0 ltac:(unfold A_TEXT; lia)) as E52.
pose proof (mfE_xs regs3 v lyc pos cur (mf_next p rest) xs 1 ltac:(unfold A_TEXT; lia)) as E53.
pose proof (mfE_xs regs3 v lyc pos cur (mf_next p rest) xs 2 ltac:(unfold A_TEXT; lia)) as E54.
cbn [Nat.add nth xs] in E52, E53, E54.
pose proof (mfE_extra regs3 v lyc pos cur (mf_next p rest) xs 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs3 v lyc pos cur (mf_next p rest) xs 0 ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E33, E32.
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (mfE regs3 v lyc pos cur (mf_next p rest) xs) k = getr regs3 r) by (intros; apply mfE_reg; assumption).
pose proof (mfE_U32 regs3 v lyc pos cur (mf_next p rest) xs) as U32.
set (E := mfE regs3 v lyc pos cur (mf_next p rest) xs) in HS, SH33, B2, B8, B33, B34, B36, E52, E53, E54, E33, E32, ER, U32.
assert (SH52 : shent_ok SEGS (SOff 32 0) E (mrestrict (w_H W3) mem3) (mkSHE 52 0 260)).
{ apply (mf_she_at E W3 mem3 52 g 260 U32 E52); [lia | lia | |].
  - destruct (hb3_addr_sub _ (mv_c v) seg_spec.SEG_M_SIZE g 260 HMA3 ltac:(lia) ltac:(lia)
      ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as (_ & _ & _ & RA52 & _). exact RA52.
  - intros x Hx. apply (mf_blk_app B v CX x). unfold seg_spec.SEG_M_SIZE; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9144; mkSHE 52 0 260] E (mrestrict (w_H W3) mem3))
  by (unfold sh_ok; apply Forall_cons; [exact SH33 | apply Forall_cons; [exact SH52 | apply Forall_nil]]).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clearbody E. clear SH33 SH52.
assert (B52 : bv_unsigned (ew E 52) = g) by (rewrite E52; apply unsigned_lit_small; lia).
(* 136(s1) writable (cur := g at 0x86b00), a0 = atom 52, the fact on atom 52, the two gen cells *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as RS.
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 136 144) HS
  eq_refl eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow SEGS E _ _ 136 144 RS ltac:(intros o' Ho'; destruct RS as (_ & _ & RW & _); apply RW; cbn; lia)))
  as HS1.
clear HS RS.
pose proof (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SOff 52 0) HS1 eq_refl
  ltac:(rewrite (hb_denot_atom E 52 _ E52); exact (eq_sym A0))) as HS2. clear HS1.
pose proof (st_ok_pi_add_fact E _ _ 52 (HPTR 4) HS2
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite B52; split; [lia|]; split; [|lia];
        change (2 ^ 4) with 16; rewrite Hg;
        replace (mv_c v + 256 * Z.of_nat i) with ((mv_c v / 16 + 16 * Z.of_nat i) * 16)
          by (pose proof (Z.div_mod (mv_c v) 16 ltac:(lia)); lia);
        apply Z_mod_mult)) as HS3. clear HS2.
hb_norm HS3.
set (rG := YP09.mkRegion (Some 33%nat) 9136 9140 0 0 [YP09.mkChunk 9136 (CVal 4 (SOff 54 0))]).
assert (RG : region_ok SEGS E (mrestrict (w_H W3) mem3) rG).
{ unfold region_ok, rG. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B33.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (mv_c v) 9136 4 (SOff 54 0) (mc_gen mcc)).
  - apply hb_denot_atom. exact E54.
  - cbn. lia.
  - cbn. lia.
  - exact (val_mem_of_rd32 SEGS (w_H W3) mem3 (mv_c v + 9136) _ (hb_rd_gen _ _ _ HMC3)). }
assert (DG : all_disjoint E rG (ss_mem (ltac:(lazymatch type of HS3 with st_ok_pi _ _ _ ?ss _ => exact ss end)))).
{ apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold zdisj, extent_of_region, rG.
  cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?B2, ?B8, ?B33, ?B34, ?B36.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ rG HS3 eq_refl RG DG) as HS4. clear HS3 RG DG. hb_norm HS4.
set (rE := YP09.mkRegion (Some 52%nat) 252 256 0 0 [YP09.mkChunk 252 (CVal 4 (SOff 53 0))]).
assert (RE : region_ok SEGS E (mrestrict (w_H W3) mem3) rE).
{ unfold region_ok, rE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B52.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ g 252 4 (SOff 53 0) ggen).
  - apply hb_denot_atom. exact E53.
  - cbn. lia.
  - cbn. lia.
  - exact (val_mem_of_rd32 SEGS (w_H W3) mem3 (g + 252) _ (hb_rd_seg_gen _ _ _ i HMC3 Hi)). }
assert (DE : all_disjoint E rE (ss_mem (ltac:(lazymatch type of HS4 with st_ok_pi _ _ _ ?ss _ => exact ss end)))).
{ apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold zdisj, extent_of_region, rE.
  cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?B2, ?B8, ?B33, ?B34, ?B36, ?B52.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ rE HS4 eq_refl RE DE) as HS. clear HS4 RE DE. hb_norm HS.
pose proof HS as HS0.
(* run: 0x86acc .. 0x86b08, the `beqz`, the checks of g->gen and c->gen, the loads, cur := g; stopped at `bne` *)
paj_run_tok RUN HS HJo SHOK Bspan.
{ hb_awr_norm.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
  [ reflexivity | rewrite B2; lia
  | cbn [YP09.r_wlo]; rewrite HSTK; destruct Hs1 as [E1 | E1]; rewrite E1; lia
  | cbn [YP09.r_whi]; destruct Hs1 as [E1 | E1]; rewrite E1; lia | ].
  hb_awr_ro. }
(* what the run kept: everything but 136(s1) *)
set (RWs := fun a => mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144).
assert (Hs1b : mf_s1 (mv_sp v) + 304 >= mv_sp v) by (destruct Hs1 as [E1 | E1]; rewrite E1; lia).
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
  assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ RWs a -> aview SEGS H m1 a = aview SEGS H m0 a);
  [ intros a Ha Hn; refine (kept_of_frame Ex rs H m0 m1 RWs HFr _ a Ha Hn);
    intros bb wlo whi x Hin Hr; cbn [windows map ss_mem] in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?B2 in Hr; unfold RWs; lia | ]); destruct Hin
  | ] end.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms5 end.
lazymatch type of HJo with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md5 := d) in *; clearbody md5 end.
(* the test `bne a0,a1` (a0 = g->gen, a1 = c->gen) *)
psrr_branch_tok RUN BR HS SHOK Bspan;
  change (sv_denot E (SExt true 32 (SOff 53 0))) with (sext 64 (bv_extract 0 32 (sv_denot E (SOff 53 0)))) in Hc;
  change (sv_denot E (SExt true 32 (SOff 54 0))) with (sext 64 (bv_extract 0 32 (sv_denot E (SOff 54 0)))) in Hc;
  rewrite (hb_denot_atom E 53 _ E53), (hb_denot_atom E 54 _ E54), hb_bne_gen in Hc by lia.
- (* g->gen <> c->gen: to the join *)
  assert (Hgne : ggen <> mc_gen mcc) by (intros Heq; rewrite Heq, Z.eqb_refl in Hc; discriminate Hc).
  paj_run_to_tok RUNTO HS HJo SHOK Bspan MFH_JOIN.
  { hb_awr_norm.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
    [ reflexivity | rewrite B2; lia
    | cbn [YP09.r_wlo]; rewrite HSTK; destruct Hs1 as [E1 | E1]; rewrite E1; lia
    | cbn [YP09.r_whi]; destruct Hs1 as [E1 | E1]; rewrite E1; lia | ].
    hb_awr_ro. }
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    assert (K6 : forall a, 0 <= a < 2 ^ 64 -> ~ RWs a -> aview SEGS H m1 a = aview SEGS H m0 a);
    [ intros a Ha Hn; refine (kept_of_frame Ex rs H m0 m1 RWs HFr _ a Ha Hn);
      intros bb wlo whi x Hin Hr; cbn [windows map ss_mem] in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?B2 in Hr; unfold RWs; lia | ]); destruct Hin
    | ] end.
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms6 end.
  lazymatch type of HJo with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md6 := d) in *; clearbody md6 end.
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RWs a -> rdW W3 (ms_mem ms6) a = rdW W3 mem3 a)
    by (intros a Ha Hn; rewrite (K6 a Ha Hn); exact (K5 a Ha Hn)).
  clear K5 K6.
  (* the slot 136(s1) holds g *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    pose proof (st_ok_pi_region_nth E ssx _ 3 _ HS eq_refl) as HR3 end.
  pose proof (field_of_region E _ 2 (mf_s1 (mv_sp v)) _ _ _ _ _ 136 8 (SOff 52 0) g HR3 B2
    ltac:(cbn; repeat (first [left; reflexivity | right])) (hb_denot_atom E 52 _ E52) ltac:(cbn; lia) ltac:(cbn; lia))
    as V136g.
  clear HR3.
  assert (VSH6 : forall i0, 4 <= i0 < 12 ->
    val_mem SEGS (mrestrict (w_H W3) (ms_mem ms6)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i0) 1 MF_LOW_OFF).
  { intros i0 Hi0. apply (mf_val_keep W3 W3 mem3 (ms_mem ms6) RWs _ 1 _ K).
    - unfold SHADOW_OFF. lia.
    - change (Z.of_nat 1) with 1. unfold SHADOW_OFF in *. lia.
    - intros k Hk Hr. change (Z.of_nat 1) with 1 in Hk. unfold RWs, SHADOW_OFF in *. lia.
    - exact (VSH3 i0 Hi0). }
  assert (MC6 : sa_mconf (rdW W3 (ms_mem ms6)) (mv_c v) mcc).
  { apply (hb_mconf_keep (rdW W3 mem3) _ (mv_c v) mcc HMC3). intros a Ha. unfold seg_spec.SEG_M_SIZE in Ha.
    apply K; [lia | unfold RWs; lia]. }
  destruct (mf_keep_run_s B v lyc S3 W3 mem3 md3 pos MF_LOW_OFF mcc cur (ms_mem ms6) md6 RWs MF_LOW_OFF (Some i) mcc
    CX CORE3 CELLS3 HJo K) as (CORE6 & CELLS6 & LOOPK6).
  { intros a Ha. unfold mf_rw. do 5 right. unfold RWs in Ha. lia. }
  { intros a Ha Hs. right. unfold RWs in Ha. lia. }
  { exact VSH6. }
  { exact V136g. }
  { exact MC6. }
  assert (NP6 : mf_np v (ms_mem ms6) W3 (mf_next p rest)).
  { unfold mf_np in *. apply (mf_val_keep W3 W3 mem3 (ms_mem ms6) RWs _ 8 _ K).
    - lia.
    - change (Z.of_nat 8) with 8. lia.
    - intros k Hk Hr. change (Z.of_nat 8) with 8 in Hk. unfold RWs in Hr. lia.
    - exact NP3. }
  pose proof (LOOPK6 _ _ _ _ _ LOOP3) as LOOP6.
  assert (T2 : getr (ms_regs ms6) 2 = getr regs3 2) by (hb_same HS0 HS (2%bv : bv 5)).
  assert (T3 : getr (ms_regs ms6) 3 = getr regs3 3) by (hb_same HS0 HS (3%bv : bv 5)).
  assert (T4 : getr (ms_regs ms6) 4 = getr regs3 4) by (hb_same HS0 HS (4%bv : bv 5)).
  assert (T8 : getr (ms_regs ms6) 8 = getr regs3 8) by (hb_same HS0 HS (8%bv : bv 5)).
  assert (T9 : getr (ms_regs ms6) 9 = getr regs3 9) by (hb_same HS0 HS (9%bv : bv 5)).
  assert (T18 : getr (ms_regs ms6) 18 = getr regs3 18) by (hb_same HS0 HS (18%bv : bv 5)).
  assert (T19 : getr (ms_regs ms6) 19 = getr regs3 19) by (hb_same HS0 HS (19%bv : bv 5)).
  assert (T22 : getr (ms_regs ms6) 22 = getr regs3 22) by (hb_same HS0 HS (22%bv : bv 5)).
  assert (T24 : getr (ms_regs ms6) 24 = getr regs3 24) by (hb_same HS0 HS (24%bv : bv 5)).
  assert (T25 : getr (ms_regs ms6) 25 = getr regs3 25) by (hb_same HS0 HS (25%bv : bv 5)).
  assert (T26 : getr (ms_regs ms6) 26 = getr regs3 26) by (hb_same HS0 HS (26%bv : bv 5)).
  pose proof (mf_regs_at_of B v lyc pos regs3 (ms_regs ms6) RA3 T2 T3 T4 T8 T9 T18 T19 T25 T26) as RA6.
  hb_reg HS (21%bv : bv 5) U21. rewrite (hb_denot_atom E 33 _ E33) in U21.
  hb_reg HS (13%bv : bv 5) U13. rewrite (hb_denot_off E 33 (mv_c v) 9136 E33 ltac:(lia)) in U13.
  pose proof HFIN as HFINj. rewrite (hb_mh_find_ne mcc nm (line + 1) i Ef Hgne) in HFINj.
  pmkst HS. hb_pc MFH_JOIN.
  exact (JOIN fx v lyc S3 W3 (ms_regs ms6) (ms_mem ms6) md6 pos mcc mcc cur line p rest i CX LS3 FRM CORE6 CELLS6 RA6
    ltac:(rewrite T24, P24; exact R24) Hlen Hne LOOP6 (hb4_mod_keep (mv_k0 v) mcc i Hi Lk0) HFINj U13 U21
    ltac:(rewrite T22, P22; exact R22) NP6).
- (* g->gen = c->gen: m_refuse *)
  assert (Hgeq : ggen = mc_gen mcc) by (destruct (Z.eqb_spec ggen (mc_gen mcc)); [assumption | discriminate Hc]).
  paj_run_to_tok RUNTO HS HJo SHOK Bspan HB_JREF1.
  { hb_awr_norm.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
    [ reflexivity | rewrite B2; lia
    | cbn [YP09.r_wlo]; rewrite HSTK; destruct Hs1 as [E1 | E1]; rewrite E1; lia
    | cbn [YP09.r_whi]; destruct Hs1 as [E1 | E1]; rewrite E1; lia | ].
    hb_awr_ro. }
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    assert (K6 : forall a, 0 <= a < 2 ^ 64 -> ~ RWs a -> aview SEGS H m1 a = aview SEGS H m0 a);
    [ intros a Ha Hn; refine (kept_of_frame Ex rs H m0 m1 RWs HFr _ a Ha Hn);
      intros bb wlo whi x Hin Hr; cbn [windows map ss_mem] in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?B2 in Hr; unfold RWs; lia | ]); destruct Hin
    | ] end.
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms6 end.
  lazymatch type of HJo with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md6 := d) in *; clearbody md6 end.
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RWs a -> rdW W3 (ms_mem ms6) a = rdW W3 mem3 a)
    by (intros a Ha Hn; rewrite (K6 a Ha Hn); exact (K5 a Ha Hn)).
  clear K5 K6.
  (* the slot 136(s1) holds g *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    pose proof (st_ok_pi_region_nth E ssx _ 3 _ HS eq_refl) as HR3 end.
  pose proof (field_of_region E _ 2 (mf_s1 (mv_sp v)) _ _ _ _ _ 136 8 (SOff 52 0) g HR3 B2
    ltac:(cbn; repeat (first [left; reflexivity | right])) (hb_denot_atom E 52 _ E52) ltac:(cbn; lia) ltac:(cbn; lia))
    as V136g.
  clear HR3.
  assert (VSH6 : forall i0, 4 <= i0 < 12 ->
    val_mem SEGS (mrestrict (w_H W3) (ms_mem ms6)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i0) 1 MF_LOW_OFF).
  { intros i0 Hi0. apply (mf_val_keep W3 W3 mem3 (ms_mem ms6) RWs _ 1 _ K).
    - unfold SHADOW_OFF. lia.
    - change (Z.of_nat 1) with 1. unfold SHADOW_OFF in *. lia.
    - intros k Hk Hr. change (Z.of_nat 1) with 1 in Hk. unfold RWs, SHADOW_OFF in *. lia.
    - exact (VSH3 i0 Hi0). }
  assert (MC6 : sa_mconf (rdW W3 (ms_mem ms6)) (mv_c v) mcc).
  { apply (hb_mconf_keep (rdW W3 mem3) _ (mv_c v) mcc HMC3). intros a Ha. unfold seg_spec.SEG_M_SIZE in Ha.
    apply K; [lia | unfold RWs; lia]. }
  destruct (mf_keep_run_s B v lyc S3 W3 mem3 md3 pos MF_LOW_OFF mcc cur (ms_mem ms6) md6 RWs MF_LOW_OFF (Some i) mcc
    CX CORE3 CELLS3 HJo K) as (CORE6 & CELLS6 & LOOPK6).
  { intros a Ha. unfold mf_rw. do 5 right. unfold RWs in Ha. lia. }
  { intros a Ha Hs. right. unfold RWs in Ha. lia. }
  { exact VSH6. }
  { exact V136g. }
  { exact MC6. }
  assert (NP6 : mf_np v (ms_mem ms6) W3 (mf_next p rest)).
  { unfold mf_np in *. apply (mf_val_keep W3 W3 mem3 (ms_mem ms6) RWs _ 8 _ K).
    - lia.
    - change (Z.of_nat 8) with 8. lia.
    - intros k Hk Hr. change (Z.of_nat 8) with 8 in Hk. unfold RWs in Hr. lia.
    - exact NP3. }
  pose proof (LOOPK6 _ _ _ _ _ LOOP3) as LOOP6.
  assert (T2 : getr (ms_regs ms6) 2 = getr regs3 2) by (hb_same HS0 HS (2%bv : bv 5)).
  assert (T3 : getr (ms_regs ms6) 3 = getr regs3 3) by (hb_same HS0 HS (3%bv : bv 5)).
  assert (T4 : getr (ms_regs ms6) 4 = getr regs3 4) by (hb_same HS0 HS (4%bv : bv 5)).
  assert (T8 : getr (ms_regs ms6) 8 = getr regs3 8) by (hb_same HS0 HS (8%bv : bv 5)).
  assert (T9 : getr (ms_regs ms6) 9 = getr regs3 9) by (hb_same HS0 HS (9%bv : bv 5)).
  assert (T18 : getr (ms_regs ms6) 18 = getr regs3 18) by (hb_same HS0 HS (18%bv : bv 5)).
  assert (T19 : getr (ms_regs ms6) 19 = getr regs3 19) by (hb_same HS0 HS (19%bv : bv 5)).
  assert (T22 : getr (ms_regs ms6) 22 = getr regs3 22) by (hb_same HS0 HS (22%bv : bv 5)).
  assert (T24 : getr (ms_regs ms6) 24 = getr regs3 24) by (hb_same HS0 HS (24%bv : bv 5)).
  assert (T25 : getr (ms_regs ms6) 25 = getr regs3 25) by (hb_same HS0 HS (25%bv : bv 5)).
  assert (T26 : getr (ms_regs ms6) 26 = getr regs3 26) by (hb_same HS0 HS (26%bv : bv 5)).
  pose proof (mf_regs_at_of B v lyc pos regs3 (ms_regs ms6) RA3 T2 T3 T4 T8 T9 T18 T19 T25 T26) as RA6.
  hb_reg HS (21%bv : bv 5) U21. rewrite (hb_denot_atom E 33 _ E33) in U21.
  hb_reg HS (10%bv : bv 5) U10. rewrite (hb_denot_atom E 33 _ E33) in U10.
  hb_reg HS (11%bv : bv 5) U11. rewrite (hb_denot_atom E 22 _ (ER 22%nat 22%bv eq_refl)), P22, R22 in U11.
  pose proof RA6 as (R2' & R3' & R4' & R8' & _).
  pose proof (hb_mh_find_eq mcc nm (line + 1) i Ef Hgeq) as HEQ. cbv zeta in HEQ.
  pose proof HFIN as HFINe. rewrite HEQ in HFINe. clear HEQ.
  assert (HKEPT1 : (length (mc_kept (m_refuse mcc (line + 1) false)) <= length (mc_kept (mf_final v)))%nat).
  { destruct (hb_upd_sizes (m_refuse mcc (line + 1) false) i (ms_with_gen (mc_gen (m_refuse mcc (line + 1) false))))
      as (Us & Uk).
    rewrite <- Uk.
    apply (mf_kept_le_final (m_upd (m_refuse mcc (line + 1) false) i (ms_with_gen (mc_gen (m_refuse mcc (line + 1) false))))
      (Some i) (line + 1) (lines (mf_rest rest)) (mf_final v)); [| exact HFINe].
    cbn [mf_cur_ok]. rewrite Us. destruct (m_refuse_sizes mcc (line + 1) false) as (Eseg & _). rewrite Eseg. exact Hi. }
  pmkst HS. hb_pc HB_JREF1.
  apply (mf_refuse_step (fx := fx) B SIGP SSP RELRO M_REFUSE v lyc S3 W3 (ms_regs ms6) (ms_mem ms6) md6 pos MF_LOW_OFF
    mcc mcc false (Some i) line p rest (mf_next p rest) HB_JREF1 CX LS3 FRM
    (mf_corek_of_core B v lyc S3 W3 (ms_mem ms6) md6 pos MF_LOW_OFF mcc CORE6) CELLS6 NP6 R2' R3' R4' R8'
    (hb_loop_cur v W3 (ms_mem ms6) mcc cur (Some i) line p rest LOOP6 Hi) Hne eq_refl Lk0
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) U10 U11 HKEPT1).
  intros fx1 ly2 S2 W2 regs7 mem7 md7 HFX LS7 CORE7 CELLS7 NP7 LOOP7 HCS.
  assert (Ely : ly2 = lyc) by (destruct LS7 as (E1 & _); destruct LS3 as (E2 & _); congruence). subst ly2.
  replace (HB_JREF1 + 4) with MFH_RREF1 by (vm_compute; reflexivity).
  assert (H21 : getr regs7 21 = getr (ms_regs ms6) 21) by exact (HCS 21 ltac:(unfold acallee_saved; lia)).
  assert (H22 : getr regs7 22 = getr (ms_regs ms6) 22) by exact (HCS 22 ltac:(unfold acallee_saved; lia)).
  assert (H24 : getr regs7 24 = getr (ms_regs ms6) 24) by exact (HCS 24 ltac:(unfold acallee_saved; lia)).
  exact (RREF1 fx1 v lyc S2 W2 regs7 mem7 md7 pos mcc (m_refuse mcc (line + 1) false) (Some i) line p rest i CX LS7
    (fxrel_frm0 fx fx1 FRM HFX) CORE7 CELLS7 (mf_regs_at_kept B v lyc pos (ms_regs ms6) regs7 RA6 HCS)
    ltac:(rewrite H24, T24, P24; exact R24) Hlen Hne LOOP7
    (hb4_mod_refuse (mv_k0 v) mcc mcc (Some i) (line + 1) false (hb4_mod_keep (mv_k0 v) mcc i Hi Lk0) eq_refl)
    HFINe ltac:(rewrite H21; exact U21) ltac:(rewrite H22, T22, P22; exact R22) NP7).
Qed.
End j.

(* the two pieces of S_MF_HDRB at every FP state (m_file_s_hdrb_2.v's MFH_<cut>_F) *)
Lemma hb_nfind : forall n, MFH_NEWE_F B n -> MFH_RREF2_F B n -> MFH_NFIND_F B n.
Proof. intros n NEWE RREF2 fx0. exact (hb_nfind_at (fx := fx0) n NEWE RREF2). Qed.
Lemma hb_hfind : forall n, MFH_JOIN_F B n -> MFH_RREF1_F B n -> MFH_NFIND_F B n -> MF_HFIND_F B n.
Proof. intros n JOIN RREF1 NFIND fx0. exact (hb_hfind_at (fx := fx0) n JOIN RREF1 NFIND). Qed.

(* ================================ THE SEGMENT S_MF_HDRB ================================
   HFIND 0x86abc -> TAIL 0x86cf8, from the tail backwards: the join and the overflow return reach the tail
   (m_file_s_hdrb_5.v); the found path's refusal return and the new entry's memcpy return reach the join (_5.v); the
   new entry's memset return reaches the memcpy (_6.v); the new entry's own code reaches the memset (_7.v); the
   not-found arm reaches the new entry or the overflow return (hb_nfind); and the segment's head reaches the join,
   the found path's refusal or the not-found arm (hb_hfind). Each piece is at every FP state, because m_refuse's
   post is apost_baseF. *)
Theorem s_mf_hdrb : S_MF_HDRB B.
Proof.
unfold S_MF_HDRB. intros n HT.
pose proof (hb5_join B VOBJS n HT) as JOIN.
pose proof (hb5_rref2 B VOBJS n HT) as RREF2.
pose proof (hb5_rref1 B VOBJS n JOIN) as RREF1.
pose proof (hb5_rmcpy B VOBJS n JOIN) as RMCPY.
pose proof (hb6_rmset B VOBJS AMEMCPY n RMCPY) as RMSET.
pose proof (hb7_newe B VOBJS AMEMSET n RMSET) as NEWE.
pose proof (hb_nfind n NEWE RREF2) as NFIND.
exact (hb_hfind n JOIN RREF1 NFIND).
Qed.
(* inside the Sections: the segment's hypotheses as its assumptions *)
About s_mf_hdrb.
Print Assumptions s_mf_hdrb.
End i.
End h.
End g.

About hb_nfind.
About hb_hfind.
Print Assumptions hb_nfind.
Print Assumptions hb_hfind.
About s_mf_hdrb.
Print Assumptions s_mf_hdrb.
