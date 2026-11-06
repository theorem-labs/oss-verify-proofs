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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 503 of its 546 lines of code are new or changed and 410 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan): the sub-walk PROV2 of segment A8b of
   reac_segconf_parse_file's walk (lib/A/Prog/pf_pieces.v S_A8b's third part):
     0x889f0  jal <snprintf trampoline>   snprintf(&c->seg[gi].ignore_file, 0x60, "%s", c->reading)
     0x889f4  j 0x88068 (TAIL)
   PROV2 -> TAIL. Segment A8b's proof, by the G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk): this file proves one sub-walk of
   the walk-internal segment A8b, not a function of the binary. The lane's rule-24 record, with the pasted
   released-proof index output and the G3 walk owner's CONFIRM, is
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md
   (reuse verdict: none, written new).

   There is no inline check in these two instructions, so the plain executor is enough and the seed needs no
   region and no shadow entry: pf_a8b_d.pfa8b_seed serves at both pcs.

   THE TRANSPORT. The snprintf step (pf_a8b_t.pfa8b_aj_snprintf_atSF) returns the caller's journal, the bytes it
   wrote at the destination, and the keep clause "every byte outside [d, d + sn_len (n-1) T) and outside the
   callee's window [sp0 + o - CMD_SNP_K, sp0 + o) is unchanged". The destination lies inside the reader's block
   c and the window lies above alloc_ceiling, so pfp_kept below ("every byte outside the block c that is below
   alloc_ceiling, or at or above s1, is unchanged") is what the step gives and what every conjunct of pf_base
   needs: the text and the frame and the frame's shadow are below alloc_ceiling and outside the block, the spill
   slots and the saved registers are at or above s1, and the image (the literals, the catalogue, the read-only
   window RLO_A .. RHI_A and the stack-protector cells gotwA / guardA) lies in [0x10000, kImgEnd), which no byte
   of a live block meets (YCbq.off_img of the block, SegPaLib.blk_off_imgP). That is why pfp_move takes NEITHER
   SSPX NOR VRO, where pf_a6_k's a6_base_move (written for a refuse call, whose post keeps no allocator byte)
   must take both. The block's own bytes are not transported: sa_rconf at the exit comes from
   pf_a8b_m.pfa8b_rconf_prov2 over what the call wrote, and the block's shadow from AR at the exit state
   (pf_a6_k.a6_heap_addr).
   Section hypothesis: SNP, the released row 4 (RtFormat.asnprintf_realizes at the listing's snprintf
   trampoline, gotwA, guardA) at every FP state. Nothing else. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a5_k pf_a6_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a8b_d pf_a8b_k pf_a8b_m pf_a8b_t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** Register numerals: the kit states a register as a bv 5 literal, pf_rg as Z_to_bv 5 of a Z *)
Lemma pfp_bv5 : forall (z : Z) (r : bv 5), bv_unsigned r = z -> Z_to_bv 5 z = r.
Proof.
intros z r <-. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma pfp_getr : forall (regs : bvmap 5 word) (z : Z) (r : bv 5) (w : word),
  bv_unsigned r = z -> getr regs (Z_to_bv 5 z) = w -> getr regs r = w.
Proof. intros regs z r w Hz H. rewrite <- (pfp_bv5 z r Hz). exact H. Qed.

(** ** What this call writes, as a list of bytes: snprintf(dst, 0x60, "%s", T) with a NUL-free T under 96 bytes
    writes exactly T and its NUL *)
Lemma pfp_sn_eq : forall (T : list Z), ~ In 0 T -> Z.of_nat (length T) < 96 ->
  sn_bytes (0x60 - 1) T = snprintf_s 96 F_s [AS T] ++ [0].
Proof.
intros T Hn Hl. unfold sn_bytes. rewrite (pfa8b_snprintf_cap 96 T Hn Hl).
f_equal. apply firstn_all2. change (Z.to_nat (0x60 - 1)) with 95%nat. lia.
Qed.
Lemma pfp_sn_len : forall (T : list Z), ~ In 0 T -> Z.of_nat (length T) < 96 ->
  sn_len (0x60 - 1) T = Z.of_nat (length (snprintf_s 96 F_s [AS T])) + 1.
Proof.
intros T Hn Hl. unfold sn_len. rewrite (pfp_sn_eq T Hn Hl), length_app. cbn [length]. lia.
Qed.
Lemma pfp_sn_le : forall (N : Z) (T : list Z), 0 <= N -> sn_len N T <= N + 1.
Proof.
intros N T HN. unfold sn_len, sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia.
Qed.
(* the registers the jal and the tail jump leave untouched (everything but ra) *)
Definition PFP_RL : list (bv 5) :=
  map (Z_to_bv 5) [2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 24; 26; 27].
Ltac pfp_in := try unfold PF_RL; try unfold PF_RM; cbn [app In];
  repeat (first [left; reflexivity | right]).
Lemma pfp_set_fs_id : forall S : astate, exists f, S = set_fs f S.
Proof. intros S. exists (st_fs S). destruct S; reflexivity. Qed.
Lemma pfp_nm_eq : forall (rd rd' : reader) a nm, pf_nm rd a nm -> 0 <= a ->
  (forall x, a <= x < a + 16 -> rd' x = rd x) -> pf_nm rd' a nm.
Proof.
intros rd rd' a nm (f & Hb & He) Ha K. exists f. split; [|exact He].
intros i Hi. pose proof (proj1 He) as Hl. rewrite K by lia. exact (Hb i Hi).
Qed.


(** ** Sub-ranges of an addressable range *)
Lemma pfp_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' -> q' + n' <= q + n ->
  sa_addr rd q' n'.
Proof.
intros rd q n q' n' (A0 & A1 & A2 & A3 & A4) H1 H2 H3.
split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
split; [exact (range_addressable_sub _ _ q n q' n' A3 H1 H3)|].
intros Hn s Hs. apply (A4 ltac:(lia)).
pose proof (YCbq.shadow_mono q q' H1) as M1.
pose proof (YCbq.shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
pose proof (Z.div_le_mono (shadow_addr q) (shadow_addr q') 8 ltac:(lia) M1) as D1.
pose proof (Z.div_le_mono (shadow_addr (q' + n' - 1)) (shadow_addr (q + n - 1)) 8 ltac:(lia) M2) as D2.
lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(** ** The spine state over a reader that agrees on the block and on cur_name *)
Lemma pfp_st_eq : forall v pos (rd rd' : reader) cf cur nm k,
  pf_st v pos rd cf cur nm k ->
  0 <= p_c v -> p_c v + seg_spec.SEG_C_SIZE <= 2 ^ 64 ->
  0 <= pf_F v pos -> pf_F v pos + PF_O_CN + 16 <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     (p_c v <= a < p_c v + seg_spec.SEG_C_SIZE \/ pf_F v pos + PF_O_CN <= a < pf_F v pos + PF_O_CN + 16) ->
     rd' a = rd a) ->
  pf_st v pos rd' cf cur nm k.
Proof.
intros v pos rd rd' cf cur nm k ((bs & Hbs & Henc) & HC & (f & Hf & Hfe) & HN) Hc0 Hc1 HF0 HF1 K.
pose proof (proj1 Henc) as Hlb. pose proof (proj1 Hfe) as Hlf.
unfold seg_spec.SEG_C_SIZE in *.
assert (ECN : PF_O_CN = 32) by reflexivity.
split; [|split; [exact HC | split; [|exact HN]]].
- exists bs. split; [|exact Henc]. intros i Hi.
  assert (HA : 0 <= p_c v + Z.of_nat i < 2 ^ 64) by lia.
  assert (HD : p_c v <= p_c v + Z.of_nat i < p_c v + 16616 \/
               pf_F v pos + PF_O_CN <= p_c v + Z.of_nat i < pf_F v pos + PF_O_CN + 16) by lia.
  rewrite (K _ HA HD). exact (Hbs i Hi).
- exists f. split; [|exact Hfe]. intros i Hi.
  assert (HA : 0 <= pf_F v pos + PF_O_CN + Z.of_nat i < 2 ^ 64) by lia.
  assert (HD : p_c v <= pf_F v pos + PF_O_CN + Z.of_nat i < p_c v + 16616 \/
               pf_F v pos + PF_O_CN <= pf_F v pos + PF_O_CN + Z.of_nat i < pf_F v pos + PF_O_CN + 16) by lia.
  rewrite (K _ HA HD). exact (Hf i Hi).
Qed.

(** ** The register list over a register file that agrees on its registers *)
Lemma pfp_rg_eq : forall (r1 r2 : bvmap 5 word) L,
  pf_rg r1 L -> (forall rv, In rv L -> getr r2 (Z_to_bv 5 (fst rv)) = getr r1 (Z_to_bv 5 (fst rv))) ->
  pf_rg r2 L.
Proof.
intros r1 r2 L H K. unfold pf_rg in *. rewrite Forall_forall in H |- *.
intros rv Hin. cbv beta. rewrite (K rv Hin). exact (H rv Hin).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** The agreement a step of this sub-walk gives: the destination lies in the reader's block and the callee's
    window above alloc_ceiling, so every byte pf_base reads is kept. *)
Definition pfp_kept (v : pfv) (Wc : world SEGS) memc (W2 : world SEGS) mem2 : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) ->
    a < alloc_ceiling \/ pf_s1 v <= a -> rdW W2 mem2 a = rdW Wc memc a.

(** ** An image byte is kept: no byte of a live block lies in [0x10000, kImgEnd) *)
Lemma pfp_lit : forall (Wc : world SEGS) memc (W2 : world SEGS) mem2 a s,
  sa_lit SEGS B (rdW Wc memc) a s ->
  (forall x, in_img SEGS x -> rdW W2 mem2 x = rdW Wc memc x) ->
  sa_lit SEGS B (rdW W2 mem2) a s.
Proof.
intros Wc memc W2 mem2 a s (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi) K.
split; [exact Ha|]. split; [|split; [exact Hp | split; [exact Hr | exact Hi]]].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
rewrite K; [exact (Hz i Hi')|]. exact (proj1 (Hi (a + Z.of_nat i) ltac:(lia))).
Qed.
Lemma pfp_cat : forall (Wc : world SEGS) memc (W2 : world SEGS) mem2,
  sa_cat SEGS B (rdW Wc memc) catA ->
  (forall x, in_img SEGS x -> rdW W2 mem2 x = rdW Wc memc x) ->
  sa_cat SEGS B (rdW W2 mem2) catA.
Proof.
intros Wc memc W2 mem2 (Hp & Hi & Hrows) K. split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp.
split; [|exact (pfp_lit Wc memc W2 mem2 tp _ Hl K)].
rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2) (pin_spec.row_addr catA i)); [exact Htp|].
intros k Hk. apply K. refine (proj1 (Hi (pin_spec.row_addr catA i + k) _)).
unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. unfold pin_spec.CAT_N in Hn. lia.
Qed.

(** ** pf_base carried across a step whose only writes are inside the block c and inside the callee's window *)
Lemma pfp_move : forall (fx0 fx1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc Sc2 (W2 : world SEGS) regs2
  mem2 md2,
  pf_base (fx := fx0) B v pos lyc Sc Wc rX memc mdc sc ->
  fxrel fx0 fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc2 W2 mem2 md2 0 ->
  (exists f, Sc2 = set_fs f Sc) -> Permutation (ablocks B lyc Sc2) (ablocks B lyc Sc) ->
  pfp_kept v Wc memc W2 mem2 ->
  (forall r, In r [2; 3; 4; 8; 9; 22] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx1) B v pos lyc Sc2 W2 regs2 mem2 md2 sc.
Proof.
intros fx0 fx1 v pos lyc Sc Wc rX memc mdc sc Sc2 W2 regs2 mem2 md2 HB Hfx HJ2 [f2 HS2] HP2 K KR.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & Hly & Hinf & G & _).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof (a6_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (a6_frame B v pos lyc Sc Wc rX memc mdc HFI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
destruct HFI as (HJ & Hly' & (f0 & HSf) & HPerm & HSV & HFLW & HFRM & HRG).
destruct HOBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
pose proof (proj1 HJ2) as HAR2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
rewrite SPF in G1.
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
pose proof (blk_off_imgP B lyc Sc Wc memc mdc bc mc HAR Hinc) as HOI.
unfold YCbq.off_img in HOI. unfold seg_spec.SEG_C_SIZE in Hc2.
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hinc Hfin) as HSBF.
unfold zdisjoint in HSBF. cbn [fst snd] in HSBF. rewrite HFE in HSBF.
(* the three shapes of the agreement *)
assert (KLOW : forall a, 0x10000 <= a < kImgEnd -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. unfold kImgEnd in Ha.
  apply K; [lia | intros Hb; unfold seg_spec.SEG_C_SIZE in Hb; lia | left; lia]. }
assert (KIMG : forall a, in_img SEGS a -> rdW W2 mem2 a = rdW Wc memc a)
  by (intros a Ha; apply KLOW; exact (pa_img_range a Ha)).
assert (KHI : forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply K; [lia | intros Hb; unfold seg_spec.SEG_C_SIZE in Hb; lia | right; lia]. }
assert (KLO : forall a, 0 <= a < alloc_ceiling -> ~ (p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) ->
  rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hb. apply K; [lia | exact Hb | left; lia]. }
split; [exact HCX|].
split.
{ split; [exact HJ2|]. split; [exact Hly'|]. split; [exists f2; rewrite HS2, HSf; apply a5_set_fs2|].
  split; [exact (Permutation_trans HP2 HPerm)|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply KHI. lia. }
  split.
  { rewrite <- HFLW. apply rdword_ext. intros k Hk.
    apply KLO; [lia | intros Hb; unfold seg_spec.SEG_C_SIZE in Hb; lia]. }
  split; [exact (fxrel_frm0 fx0 fx1 HFRM Hfx)|].
  apply (pfp_rg_eq rX regs2); [exact HRG|].
  intros rv Hin. apply KR. cbn [In] in Hin |- *.
  repeat (destruct Hin as [<- | Hin]; [cbn [fst]; tauto|]). destruct Hin. }
split.
{ assert (HT2 : sa_heap B lyc Sc2 (p_t v) (pf_len v)) by exact (a6_heap_perm B lyc Sc lyc Sc2 _ _ HP2 HT).
  assert (HC2 : sa_heap B lyc Sc2 (p_c v) seg_spec.SEG_C_SIZE) by exact (a6_heap_perm B lyc Sc lyc Sc2 _ _ HP2 HC).
  destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_t v) (pf_len v) HAR HT ltac:(unfold pf_len; lia))
    as (bt & mt & Hint & Ht1 & Ht2 & Ht3 & Ht4 & Htapp).
  unfold pf_len in Ht2.
  pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)) as Hmd.
  unfold sa_disj, seg_spec.cstr_span, seg_spec.SEG_C_SIZE in HDJ.
  split.
  { destruct STR as ((Hz & Hn) & Htl). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite KLO; [exact (Hz i Hi) | lia | intros Hb; unfold seg_spec.SEG_C_SIZE in *; lia].
    - intros x Hx.
      apply (AR_block_word_vis SEGS B lyc Sc2 W2 mem2 md2 bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2).
      + exact (Permutation_in _ (Permutation_sym HP2) Hint).
      + lia.
      + lia. }
  split; [exact (a6_heap_addr B lyc Sc2 W2 mem2 md2 (p_t v) (pf_len v) HAR2 HT2 ltac:(unfold pf_len; lia))|].
  split; [exact HT2|].
  split; [exact (a6_heap_addr B lyc Sc2 W2 mem2 md2 (p_c v) seg_spec.SEG_C_SIZE HAR2 HC2
                   ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC2|].
  split; [exact (pfp_cat Wc memc W2 mem2 CAT KIMG)|].
  split; [intros x Hx; exact (pfp_lit Wc memc W2 mem2 _ _ (LITS x Hx) KIMG)|].
  split.
  { intros a Hro Ho He.
    assert (KR2 : rdW W2 mem2 a = rdW Wc memc a).
    { destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
      - apply KIMG. exists sg. split; [exact Hsg | exact Hr].
      - apply KLOW. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia. }
    rewrite KR2. exact (ROD a Hro Ho He). }
  destruct SSP as (S1 & g & S2). split.
  - rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2) gotwA); [exact S1|].
    intros k Hk. apply KLOW. unfold gotwA, kImgEnd. lia.
  - exists g. rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2) guardA); [exact S2|].
    intros k Hk. apply KLOW. unfold guardA, kImgEnd. lia. }
split.
{ apply (a6_sl_move (rdW Wc memc) (rdW W2 mem2) (pf_s1 v) (PF_SL v pos) HSL (a6_PF_SL_offs v pos));
    [lia | lia |]. intros a Ha. apply KHI. lia. }
intros i Hi. rewrite KLO; [exact (HFSH i Hi) | | ].
- rewrite G10. unfold SHADOW_OFF in *. unfold kLowMemEnd, kHighShadowEnd in *.
  assert (HD : pf_F v pos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (HD2 : alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in HD2.
  assert (HD0 : 0 <= pf_F v pos / 8) by (apply Z.div_pos; lia).
  lia.
- intros Hb. unfold seg_spec.SEG_C_SIZE in Hb.
  apply (a6_band_not_app bc (req_size mc) (pf_SH v pos + i) Hcapp); [|lia].
  rewrite G10. unfold SHADOW_OFF in *.
  assert (HD : pf_F v pos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (HD2 : alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in HD2.
  assert (HD0 : 0 <= pf_F v pos / 8) by (apply Z.div_pos; lia).
  lia.
Qed.
(** ** The sub-walk *)
Section c. Context {fx : YK11.FPState}.
(* the released row 4 at the listing's snprintf trampoline, at every FP state *)
Hypothesis SNP : forall fx0 : YK11.FPState,
  RtFormat.asnprintf_realizes (fx := fx0) SEGS B (SIGMA SS___interceptor_trampoline_snprintf) gotwA guardA.

Lemma pfa8b_prov2 : forall n : nat, HA_TAIL B n -> H_PROV2 (fx := fx) B n.
Proof.
intros n HTAIL v pos lyc Sc Wc rX memc mdc cf nm o ln dd bb gi HINV.
destruct HINV as (HB & HMID & HST & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hinf & G & _).
pose proof (a6_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (a6_frame B v pos lyc Sc Wc rX memc mdc HFI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (proj1 HFI) as HJ.
pose proof HOBJ as (STR & AT & HTt & AC & HC & CAT & LITS & ROD & SSP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
rewrite SPF in G1.
destruct (pfa8b_o_ok v G3) as (Ho16 & Hole & Hoge).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
(* the numbers of the record and of the field this call writes *)
assert (HCS : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (HRN : seg_spec.RC_N = 11392) by reflexivity.
assert (HRDa : seg_spec.RC_READING = 16512) by reflexivity.
assert (ECN : PF_O_CN = 32) by reflexivity.
assert (EIGN : seg_spec.RS_IGNORE_FILE = 256) by reflexivity.
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(lia))
  as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
pose proof (blk_off_imgP B lyc Sc Wc memc mdc bc mc HAR Hinc) as HOI.
unfold YCbq.off_img in HOI.
pose proof HST as (HRC0 & HCur0 & HNM0 & HCnt0).
assert (Hgilt : (gi < length (rc_seg cf))%nat).
{ cbn in HCur0. unfold pf_prov_mid, r_upd, r_set_segs in HCur0. cbn [rc_seg] in HCur0.
  rewrite upd_nth_len in HCur0. exact HCur0. }
assert (Hgi32 : (gi < 32)%nat).
{ destruct HRC0 as (bs0 & _ & Henc0). pose proof (proj1 (proj2 Henc0)) as Hle32.
  unfold pf_prov_mid, r_upd, r_set_segs in Hle32. cbn [rc_seg] in Hle32.
  rewrite upd_nth_len in Hle32. lia. }
assert (Hgz : 0 <= Z.of_nat gi <= 31) by lia.
assert (HDIb : seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE = p_c v + 356 * Z.of_nat gi + 256)
  by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_IGNORE_FILE; lia).
destruct (pfa8b_prov_mid_fields bb cf gi Hgilt) as (Erd & Egen & Elen & Eign).
(* the reading string *)
assert (HTrng : Forall (fun z => 0 <= z < 256) (rc_reading cf))
  by (rewrite <- Erd; exact (pfa8b_reading_rng (rdW Wc memc) (p_c v) _ HRC0)).
assert (HTlen : Z.of_nat (length (rc_reading cf)) < 96).
{ destruct HRC0 as (bs0 & _ & Henc0).
  destruct Henc0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _).
  rewrite <- Erd. pose proof (proj1 (proj2 Hrd)) as Hlt. lia. }
assert (HTnul : ~ In 0 (rc_reading cf)).
{ destruct HRC0 as (bs0 & _ & Henc0).
  destruct Henc0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _).
  rewrite <- Erd. exact (proj1 (proj2 (proj2 Hrd))). }
(* ---------------- the seed and the run to the call ---------------- *)
unfold cfg_at. change (w64 (BASE + PF_PROV2)) with (Z_to_bv 64 (BASE + PF_PROV2)).
pose proof (pfa8b_seed PF_PROV2 Wc rX memc) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg rX []) (Eimg (Ereg rX [])))
  by (split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
revert HS HEI HA0. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI HA0.
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ apply awr_ok_nil. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [| exact Ha | tauto].
  intros bq wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
assert (RKZ : forall r, In r [2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 24; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr.
  apply (regs_kept_of_st_ok SEGS E _ _ rX (@nil word) PFP_RL HS HA0 ltac:(vm_compute; reflexivity)).
  unfold PFP_RL. apply in_map. exact Hr. }
pmkst HS.
prreg HS (1%bv : bv 5) R1.
(* the cut's facts at the call's state *)
assert (HB1 : pf_base (fx := fx) B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy mdc) mat mdc) PF_SC_LINE).
{ apply (pfp_move fx fx v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) _
    HB (fxrel_refl fx) HJ (pfp_set_fs_id Sc) (Permutation_refl _));
  [ intros a Ha _ _; apply KM1; exact Ha
  | intros r Hr; apply RKZ; cbn in Hr |- *; tauto ]. }
pose proof HB1 as (HCX1 & HFI1 & HOBJ1 & HSL1 & HFSH1).
pose proof HOBJ1 as (STR1 & AT1 & HTt1 & AC1 & HC1 & CAT1 & LITS1 & ROD1 & SSP1).
pose proof (proj1 HFI1) as HJ1. pose proof (proj1 HJ1) as HAR1.
destruct HFI1 as (_ & _ & _ & _ & _ & _ & HFRM1 & HRG1).
assert (HST1 : pf_st v pos (rdW Wc (ms_mem ms)) (pf_prov_mid (PIgn bb) cf gi) (Some gi) nm
  (length (skipn (pf_next (p_s v) o) (p_s v)))).
{ apply (pfp_st_eq v pos (rdW Wc memc) _ _ _ _ _ HST);
  [ lia | lia | lia | lia | intros a Ha _; apply KM1; exact Ha ]. }
pose proof HST1 as (HRC1 & _ & HNM1 & _).
(* the register values at the call *)
assert (Q2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ rewrite <- (pfp_bv5 2 (2%bv : bv 5) ltac:(reflexivity)).
  exact (a5_rg_get (ms_regs ms) _ 2 (pf_s1 v) HRG1 ltac:(pfp_in)). }
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite <- (pfp_bv5 3 (3%bv : bv 5) ltac:(reflexivity)).
  exact (a5_rg_get (ms_regs ms) _ 3 (as_gp B) HRG1 ltac:(pfp_in)). }
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite <- (pfp_bv5 4 (4%bv : bv 5) ltac:(reflexivity)).
  exact (a5_rg_get (ms_regs ms) _ 4 (as_tp B) HRG1 ltac:(pfp_in)). }
assert (QA : forall r x, In (r, x) (PF_RL v pos ++ PF_RM v o ln ++
    [(20, seg_spec.rseg_addr (p_c v) gi);
     (10, seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE); (11, 0x60);
     (12, seg_litA_rc F_s); (13, p_c v + seg_spec.RC_READING)]) ->
  In r [2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 24; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = w64 x).
{ intros r x Hin Hr. rewrite (RKZ r Hr). exact (a5_rg_get rX _ r x HRG Hin). }
assert (Q10 : getr (ms_regs ms) 10 = w64 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE)).
{ rewrite <- (pfp_bv5 10 (10%bv : bv 5) ltac:(reflexivity)). apply QA; [pfp_in | cbn; tauto]. }
assert (Q11 : getr (ms_regs ms) 11 = w64 0x60).
{ rewrite <- (pfp_bv5 11 (11%bv : bv 5) ltac:(reflexivity)). apply QA; [pfp_in | cbn; tauto]. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_s)).
{ rewrite <- (pfp_bv5 12 (12%bv : bv 5) ltac:(reflexivity)). apply QA; [pfp_in | cbn; tauto]. }
assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (p_c v + seg_spec.RC_READING))
  by (apply QA; [pfp_in | cbn; tauto]).
assert (Qsp : spZ (ms_regs ms) = pf_s1 v)
  by (unfold spZ; rewrite Q2; apply a6_w64_u; lia).
(* the addressability of the written field and of the reading field *)
pose proof (pfp_addr_sub (rdW Wc (ms_mem ms)) (p_c v) seg_spec.SEG_C_SIZE
  (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE) 104 AC1 ltac:(lia) ltac:(lia) ltac:(lia)) as ADI.
pose proof (pfp_addr_sub (rdW Wc (ms_mem ms)) (p_c v) seg_spec.SEG_C_SIZE
  (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE) 0x60 AC1 ltac:(lia) ltac:(lia) ltac:(lia)) as ADI2.
pose proof (pfp_addr_sub (rdW Wc (ms_mem ms)) (p_c v) seg_spec.SEG_C_SIZE
  (p_c v + seg_spec.RC_READING) (Z.of_nat (length (rc_reading cf)) + 1) AC1
  ltac:(lia) ltac:(lia) ltac:(lia)) as ARD.
pose proof (pfp_addr_sub (rdW Wc (ms_mem ms)) (p_c v) seg_spec.SEG_C_SIZE
  (p_c v + seg_spec.RC_READING) (Z.of_nat (length (rc_reading cf)) + 8) AC1
  ltac:(lia) ltac:(lia) ltac:(lia)) as ARD8.
assert (HRDstr : sa_str (rdW Wc (ms_mem ms)) (p_c v + seg_spec.RC_READING) (rc_reading cf)).
{ rewrite <- Erd. exact (pfa8b_reading_str (rdW Wc (ms_mem ms)) (p_c v) _ HRC1 ltac:(lia)). }
(* the format literal *)
assert (HFs : seg_litA_rc F_s = 0x21340) by (vm_compute; reflexivity).
pose proof (LITS1 F_s ltac:(unfold PARSE_FILE_LITS; cbn [In]; left; reflexivity)) as HLIT.
pose proof HLIT as (Hfp0 & Hfstr & Hfpin & _ & _).
assert (Hfadr : sa_addr (rdW Wc (ms_mem ms)) (seg_litA_rc F_s) 3).
{ pose proof (Hfpin lyc Sc Wc (ms_mem ms) _ HAR1) as HX.
  rewrite pfa8b_F_s_len in HX. exact HX. }
(* ---------------- the call ---------------- *)
eapply SRr_bind.
{ eapply (pfa8b_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA _ (SNP _)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE) 0x60 (seg_litA_rc F_s) (rc_reading cf)
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + 15552)));
  [ exact HJ
  | exact Q10
  | exact Q11
  | exact Q12
  | lia
  | lia
  | lia
  | lia
  | exact Ho16
  | exact Hole
  | unfold CMD_SNP_K, ESTACK; lia
  | exact Q3
  | exact Q4
  | exact R1
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | (* awr_byte *) intros a Ha; split;
      [ right; left; split;
        [ apply pfa8b_fp_block; lia
        | exists bc, mc; split; [exact Hinc | lia] ]
      | unfold CMD_SNP_K, ESTACK; lia ]
  | (* writable_at *) intros a Ha _ Hd; exfalso; destruct Hd as [(_ & Himg) | Hsp];
      [ exact (blk_img SEGS B LAWS lyc Sc Wc (ms_mem ms) _ bc mc a HAR1 Hinc ltac:(lia) Himg)
      | unfold CMD_SNP_K, ESTACK in *; lia ]
  | (* amem_range *) exact (proj1 (proj2 (proj2 ADI)))
  | (* range_addressable *) exact (proj1 (proj2 (proj2 (proj2 ADI2))))
  | (* shadow_hull_vis *) exact (proj2 (proj2 (proj2 (proj2 ADI2))) ltac:(lia))
  | (* off_img *) pose proof (pfp_sn_le (0x60 - 1) (rc_reading cf) ltac:(lia));
      unfold YCbq.off_img; lia
  | unfold CMD_IMG_HI, kImgEnd, CMD_SNP_K, ESTACK; lia
  | exact SSP1
  | unfold gotwA; lia
  | unfold gotwA, CMD_IMG_HI, kImgEnd; lia
  | unfold guardA; lia
  | unfold guardA, CMD_IMG_HI, kImgEnd; lia
  | unfold gotwA, CMD_IMG_LO; lia
  | unfold guardA, CMD_IMG_LO; lia
  | (* FR_cmd *)
    pose proof (pfp_sn_le (0x60 - 1) (rc_reading cf) ltac:(lia)) as HSNL;
    apply (pfa8b_FR_s_regs (rdW Wc (ms_mem ms)) _ (seg_litA_rc F_s) (p_c v + seg_spec.RC_READING)
      (rc_reading cf) (ms_regs ms));
    [ unfold argZ; change (10 + 3) with 13; rewrite Q13; apply a6_w64_u; lia
    | lia
    | unfold CMD_IMG_LO; lia
    | unfold CMD_GOTW; lia
    | exact Hfstr
    | exact Hfadr
    | unfold snp_out; rewrite Qsp; repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd];
        unfold CMD_SNP_K, ESTACK; lia|]); apply Forall_nil
    | lia
    | exact (pfa8b_bytes_range_aview SEGS (w_H Wc) (ms_mem ms) _ _ HRDstr)
    | lia
    | exact HRDstr
    | exact ARD
    | exact (proj1 (proj2 (proj2 ARD8)))
    | unfold snp_out; rewrite Qsp;
      pose proof (Z.mod_pos_bound (- (p_c v + seg_spec.RC_READING + Z.of_nat (length (rc_reading cf)) + 1)) 8
        ltac:(lia));
      unfold seg_spec.cstr_span;
      repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd];
        unfold CMD_SNP_K, ESTACK; lia|]); apply Forall_nil ]
  | lia
  | exact (a5_rom B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) _ PF_SC_LINE HB1)
  | exact HFRM1 ]. }
(* ---------------- after the call ---------------- *)
cbv beta. intros W3 c3 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HP2 & H10 & Hby & Hkeep & Hpres
  & Hsame).
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
(* the tail jump 0x889f4 *)
pose proof (pfa8b_seed (fx := fx1) 15552 Wc regs2 mem2) as HS2.
pose proof (pfp_sn_le (0x60 - 1) (rc_reading cf) ltac:(lia)) as HSNL.
pose proof (pfa8b_sn96_len (rc_reading cf)) as H96.
pose proof (pfp_sn_len (rc_reading cf) HTnul HTlen) as HL.
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hinc Hfin) as HSBF.
unfold zdisjoint in HSBF. cbn [fst snd] in HSBF. rewrite HFE in HSBF.
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (HA2 : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 [])))
  by (split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
clear HS HEI HA0 HFr HF HG.
revert HS2 HEI2 HA2. generalize (Eimg (Ereg regs2 [])) as E2. intros E2 HS2 HEI2 HA2.
rename ms into ms1.
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HS2 HJ2 PF_TAIL.
{ apply awr_ok_nil. }
assert (KM3 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc mem2 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E2 _ (w_H Wc) mem2 (ms_mem ms) (fun _ => False) HFr);
    [| exact Ha | tauto].
  intros bq wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
assert (RK3 : forall r, In r [2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 24; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r Hr.
  apply (regs_kept_of_st_ok_pi E2 _ _ regs2 (@nil word) PFP_RL HS2 HA2 ltac:(vm_compute; reflexivity)).
  unfold PFP_RL. apply in_map. exact Hr. }
pmkst HS2.
(* the agreement from the cut to the final state *)
assert (KFIN : pfp_kept v Wc memc Wc (ms_mem ms)).
{ intros a Ha Hb Hlo. rewrite (KM3 a Ha).
  rewrite (Hkeep a Ha ltac:(lia) ltac:(unfold CMD_SNP_K, ESTACK in *; lia)). apply KM1. exact Ha. }
assert (RFIN : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. rewrite (RK3 r ltac:(cbn in Hr |- *; tauto)).
  rewrite (HP2 r ltac:(unfold acallee_saved; cbn in Hr; lia)).
  apply RKZ. cbn in Hr |- *; tauto. }
(* the exit record *)
assert (HBYT : forall k, (k <= length (snprintf_s 96 F_s [AS (rc_reading cf)]))%nat ->
  rdW Wc (ms_mem ms) (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE + Z.of_nat k) =
  Some (nth k (snprintf_s 96 F_s [AS (rc_reading cf)] ++ [0]) 0)).
{ intros k Hk.
  rewrite (KM3 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE + Z.of_nat k) ltac:(lia)).
  rewrite (Hby (Z.of_nat k) ltac:(lia)).
  rewrite (pfp_sn_eq (rc_reading cf) HTnul HTlen), Nat2Z.id. reflexivity. }
assert (HRCF : sa_rconf (rdW Wc (ms_mem ms)) (p_c v) (pf_prov_fin (PIgn bb) cf gi)).
{ apply (pfa8b_rconf_prov2 (rdW Wc (ms_mem ms1)) _ (p_c v) cf gi bb HRC1 Hgilt ltac:(lia)); [|exact HBYT].
  intros x Hx Hnf. rewrite (KM3 x ltac:(lia)).
  apply (Hkeep x ltac:(lia) ltac:(lia) ltac:(unfold CMD_SNP_K, ESTACK in *; lia)). }
(* the exit cut *)
pose proof (proj2 (proj2 HMID)) as HLCTX.
pose proof (pfA_facts.L_next_holds (p_s v) o (proj1 HMID)) as (_ & Hnext1 & Hnext2 & _).
apply (HTAIL fx1 v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) _ (pf_prov_fin (PIgn bb) cf gi) (Some gi) nm
  (pf_next (p_s v) o) (ln + 1) dd).
split.
{ apply (pfp_move fx fx1 v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) _
    HB Hfx1 HJ2 (pfp_set_fs_id Sc) (Permutation_refl _) KFIN);
  intros r Hr; apply RFIN; cbn in Hr |- *; tauto. }
split; [exact HLCTX|].
split.
{ pose proof (proj1 (proj2 HMID)) as Hle. rewrite !length_skipn. rewrite length_skipn in Hle. lia. }
split.
{ split; [exact HRCF|]. split.
  { unfold pf_cur_ok, pf_prov_fin, r_upd, r_set_segs. cbn [rc_seg]. rewrite upd_nth_len. exact Hgilt. }
  split.
  { apply (pfp_nm_eq (rdW Wc (ms_mem ms1)) _ _ _ HNM1); [lia|].
    intros x Hx. rewrite (KM3 x ltac:(lia)).
    apply (Hkeep x ltac:(lia)); [lia | unfold CMD_SNP_K, ESTACK in *; lia]. }
  unfold pf_cnt in HCnt0 |- *. unfold pf_prov_fin, pf_prov_mid, r_upd, r_set_segs in HCnt0 |- *.
  cbn [rc_refused rc_overflow] in HCnt0 |- *. exact HCnt0. }
apply (pfp_rg_eq rX (ms_regs ms)).
- apply (a5_rg_incl rX (PF_RL v pos ++ PF_RM v o ln ++
    [(20, seg_spec.rseg_addr (p_c v) gi);
     (10, seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE); (11, 0x60);
     (12, seg_litA_rc F_s); (13, p_c v + seg_spec.RC_READING)]));
    [| exact HRG].
  intros rv Hin. revert Hin. unfold PF_RL, PF_RM. cbn [app In pf_cur_ptr]. intros Hin.
  repeat (destruct Hin as [<- | Hin]; [pfp_in|]). destruct Hin.
- intros rv Hin. apply RFIN.
  revert Hin. unfold PF_RL. cbn [app In]. cbn [pf_cur_ptr].
  intros Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst]; tauto|]). destruct Hin.
Qed.
End c.


End e.
End f.
End d.
