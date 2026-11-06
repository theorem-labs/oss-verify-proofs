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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 199 of its 243 lines of code are new or changed and 409 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the SEEDS of the LONG walk of segment A6 of
   reac_segconf_parse_file's walk (lib/A/Prog/pf_pieces.v H_LONG, 0x87e2c -> the REF3 cut 0x87e74). Segment
   A6's proof (its LONG walk), 2026-10-30. No instruction is walked here; lib/A/Prog/pf_a6_l.v runs from them.
   The form is segment A7's mid-walk seed pf_a7_q.v a7_seed (commit 7831f455a1ce), which is
   fuzz_command's check_reply_sd.v cr_seed on this listing: from the cut facts `pf_base B v pos lyc Sc Wc rX memc mdc
   PF_SC_LINE` it builds the symbolic state at a listing offset, every register its own atom (sr_atoms), with the
   regions and facts the run from there reads.
     a6l_seed0  at LONG 0x87e2c (PF_LONG): region slot s1 + 0xa8 (atom 9), which holds strspn's set
                seg_litA_rc [SP; TAB; CR] = 0x21380 (PF_SL; `ld a1, 0xa8(s1)` at 0x87e30). The plain run from it
                stops at the jal 0x87e34 to the strspn trampoline (PRS_call SS___interceptor_trampoline_strspn).
     a6l_seedA  at 0x87e38 (PF_LONG + 12, after the call), span >= len: region slot s1 + 0xa0, which holds F_long's
                literal seg_litA_rc F_long = 0x213a0 (`ld a2, 0xa0(s1)` at 0x87e70), and the fact a0 >=u s7
                (`bgeu a0, s7` 0x87e38 taken). The plain run from it reaches PF_REF3.
     a6l_seedB  at 0x87e38, span < len: the slot s1 + 0xa0, the text byte at[span] as a one-byte region at the
                extra atom 32 (its value the extra atom 33), the facts atom 22 = SHADOW_OFF exactly (check #3's
                shadow base, sh_static_ok), atom 32 a pointer, atom 33 a byte, a0 <u s7, and the alias
                s9 + a0 = atom 32 (`add a0, s9, a0` 0x87e3c). The token run from it (Bx = SOff 22 0, the shadow
                entry [mkSHE 32 0 1]) reaches PF_REF3.
   The three runs were measured by two probe files of segment A6's proof (logs build-20261030T172709Z and
   build-20261030T182028Z, the lane's notes, not in the tree). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The literals the two slots hold (SegInstA's map, PF_SL) *)
Lemma a6l_lit_set : seg_litA_rc [SP; TAB; CR] = 0x21380.
Proof. vm_compute. reflexivity. Qed.
Lemma a6l_lit_long : seg_litA_rc F_long = 0x213a0.
Proof. vm_compute. reflexivity. Qed.

(** ** The symbolic states (see the head comment) *)
Definition a6l_slot8 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xa8 0xb0 0xa8 0xa8 [YP09.mkChunk 0xa8 (CVal 8 (SLit 0x21380))].
Definition a6l_slot0 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xa0 0xa8 0xa0 0xa0 [YP09.mkChunk 0xa0 (CVal 8 (SLit 0x213a0))].
Definition a6l_byte : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition a6l_ss0 : sstate := mkSS PF_LONG sr_atoms [a6l_slot8] None (mkFacts [] [] []).
Definition a6l_GA : facts := mkFacts [] [mkAC BC_GEU (SOff 10 0) (SOff 23 0)] [].
Definition a6l_ssA : sstate := mkSS (PF_LONG + 12) sr_atoms [a6l_slot0] None a6l_GA.
Definition a6l_GB : facts :=
  mkFacts [(22%nat, mkAF SB SB 0); (32%nat, PTR 0); (33%nat, mkAF 0 255 0)]
    [mkAC BC_LTU (SOff 10 0) (SOff 23 0)]
    [(SAlu ALU_ADD (SOff 25 0) (SOff 10 0), SOff 32 0)].
Definition a6l_ssB : sstate := mkSS (PF_LONG + 12) sr_atoms [a6l_slot0; a6l_byte] None a6l_GB.
(* check #3's shadow base (s6, pf_fi) and its shadow entry: the text byte at[span] *)
Definition a6l_Bx : sv := SOff 22 0.
Definition a6l_SH : list shent := [mkSHE 32 0 1].

(** ** One byte of the reader as a one-byte chunk (pf_a7_q.v a7q_val_mem1, after pf_a12.v's a12_val_mem1) *)
Lemma a6l_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma a6l_val_mem1 : forall (H : word -> bool) (mem : word -> option byte) a z,
  aview SEGS H mem a = Some z -> 0 <= z < 256 -> val_mem SEGS (mrestrict H mem) a 1 z.
Proof.
intros H mem a z Hv Hz k Hk. assert (k = 0%nat) as -> by lia.
destruct (aview_byte SEGS H mem a z Hv) as (b & Hb & Hvb & _).
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
rewrite le_byte_small by (cbn; lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Hvb.
symmetry. apply a6l_byte_self.
Qed.

(* the seeds' environment: atoms 0 .. 31 the registers rX, 32 + j the extra words (a named Definition, so that the
   step tactics' cbn leaves it folded, as pf_a7_q.v's a7_E) *)
Definition a6l_E (rX : bvmap 5 word) (extra : list word) : env := Eimg (Ereg rX extra).
Lemma a6l_E_img : forall rX extra, img_env VAL A_LIM (a6l_E rX extra).
Proof. intros rX extra. unfold a6l_E. apply Eimg_env. Qed.
Lemma a6l_E_agree : forall rX extra, env_agree 32 (Ereg rX extra) (a6l_E rX extra).
Proof.
intros rX extra. split; [|reflexivity].
intros n Hn. unfold a6l_E. apply Eimg_low. unfold A_TEXT. lia.
Qed.
(* atom k < 32 is register k; atom 32 + j is extra's j-th word *)
Lemma a6l_ew_reg : forall (rX : bvmap 5 word) extra k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (a6l_E rX extra) k = getr rX r.
Proof. intros rX extra k r Hk. unfold a6l_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.
Lemma a6l_ew_extra : forall (rX : bvmap 5 word) extra j, (32 + j < A_TEXT)%nat ->
  ew (a6l_E rX extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros rX extra j Hj. unfold a6l_E. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.
(* the registers a run leaves as their own atoms keep the seed's values (pf_a7_q.v a7_regs_kept) *)
Lemma a6l_regs_kept : forall rX extra ss (H : word -> bool) ms (l : list Z),
  st_ok_pi SEGS VAL (a6l_E rX extra) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    (map (Z_to_bv 5) l) = true ->
  forall k, In k l -> getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k).
Proof.
intros rX extra ss H ms l HS Hl k Hk.
exact (regs_kept_of_st_ok_pi (a6l_E rX extra) ss (restrict H ms) rX extra (map (Z_to_bv 5) l) HS
  (a6l_E_agree rX extra) Hl (Z_to_bv 5 k) (in_map _ _ _ Hk)).
Qed.

(* a slot of PF_SL as the one-chunk region at atom 9 = s1 *)
Lemma a6l_slot_ok : forall (E : env) (H : word -> bool) mem s1 off z,
  bv_unsigned (ew E 9) = s1 -> 0 <= s1 -> s1 + 0x100 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 0x100 -> 0 <= z < 2 ^ 64 ->
  rdword (aview SEGS H mem) (s1 + off) = Some z ->
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 9%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SLit z))]).
Proof.
intros E H mem s1 off z U9 Hs0 Hs1 Ho0 Ho1 Hz Hw.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS _ _ s1 off 8%N (SLit z) z).
- reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- lia.
- exact (val_mem_of_rdword SEGS H mem _ _ Hw).
Qed.

Section e.
Variable B : asyms.

(* the numbers of a cut state the seeds use: s1 (atoms 2, 9), SHADOW_OFF (atom 22), the two slots *)
Lemma a6l_cut_nums : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  alloc_ceiling + 0x100 <= pf_s1 v /\ pf_s1 v + 0x100 <= 2 ^ 47 /\
  getr rX (Z_to_bv 5 9) = w64 (pf_s1 v) /\ getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF /\
  rdword (rdW Wc memc) (pf_s1 v + 0xa0) = Some (seg_litA_rc F_long) /\
  rdword (rdW Wc memc) (pf_s1 v + 0xa8) = Some (seg_litA_rc [SP; TAB; CR]).
Proof.
intros v pos lyc Sc Wc rX memc mdc HB.
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HRG.
destruct HB as (_ & _ & _ & HSL & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
split; [lia|]. split; [lia|].
split; [eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]|].
split; [eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]|].
split.
- exact (proj1 (Forall_forall _ _) HSL (0xa0, seg_litA_rc F_long)
    ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right]))).
- exact (proj1 (Forall_forall _ _) HSL (0xa8, seg_litA_rc [SP; TAB; CR])
    ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right]))).
Qed.

(** ** The seed at LONG *)
Lemma a6l_seed0 : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  st_ok_pi SEGS VAL (a6l_E rX []) a6l_ss0
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_LONG)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc HB.
destruct (a6l_cut_nums v pos lyc Sc Wc rX memc mdc HB) as (N1 & N2 & R9 & _ & _ & H8).
pose proof asan_consts as (Hac & _).
assert (U9 : bv_unsigned (ew (a6l_E rX []) 9) = pf_s1 v).
{ rewrite (a6l_ew_reg rX [] 9 (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
rewrite a6l_lit_set in H8.
rewrite restrict_mkst_fx. unfold a6l_ss0. apply pa_entry_st_ok_full.
- exact (regs_ok_Eimg_Ereg rX []).
- vm_compute. reflexivity.
- constructor; [|constructor].
  exact (a6l_slot_ok _ (w_H Wc) memc (pf_s1 v) 0xa8 0x21380 U9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) H8).
- cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
- split; [exact I | split; exact I].
Qed.

(** ** The seed after the call, span >= len *)
Lemma a6l_seedA : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc sp len,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  getr rX 10 = w64 sp -> getr rX 23 = w64 len -> 0 <= sp < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> len <= sp ->
  st_ok_pi SEGS VAL (a6l_E rX []) a6l_ssA
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (PF_LONG + 12))) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc sp len HB R10 R23 Hsp Hlen Hle.
destruct (a6l_cut_nums v pos lyc Sc Wc rX memc mdc HB) as (N1 & N2 & R9 & _ & H0 & _).
pose proof asan_consts as (Hac & _).
set (E := a6l_E rX []).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v).
{ unfold E. rewrite (a6l_ew_reg rX [] 9 (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (E10 : ew E 10 = Z_to_bv 64 sp) by (unfold E; rewrite (a6l_ew_reg rX [] 10 10%bv eq_refl); exact R10).
assert (E23 : ew E 23 = Z_to_bv 64 len) by (unfold E; rewrite (a6l_ew_reg rX [] 23 23%bv eq_refl); exact R23).
rewrite a6l_lit_long in H0.
rewrite restrict_mkst_fx. unfold a6l_ssA. apply pa_entry_st_ok_full.
- exact (regs_ok_Eimg_Ereg rX []).
- vm_compute. reflexivity.
- constructor; [|constructor].
  exact (a6l_slot_ok _ (w_H Wc) memc (pf_s1 v) 0xa0 0x213a0 U9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) H0).
- cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
- split; [exact I|]. split; [|exact I].
  cbn [a6l_GA f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_geu_U, (U_atom E 10 sp E10 Hsp), (U_atom E 23 len E23 Hlen).
  apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.

(** ** The seed after the call, span < len, with the text byte at[span] *)
Lemma a6l_seedB : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc sp len at0 b,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  getr rX 10 = w64 sp -> getr rX 23 = w64 len -> getr rX 25 = w64 at0 ->
  0 <= sp < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> 0 <= at0 < 2 ^ 64 -> sp < len ->
  4096 <= at0 + sp < alloc_ceiling ->
  rdW Wc memc (at0 + sp) = Some b -> 0 <= b < 256 ->
  st_ok_pi SEGS VAL (a6l_E rX [Z_to_bv 64 (at0 + sp); Z_to_bv 64 b]) a6l_ssB
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (PF_LONG + 12))) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc sp len at0 b HB R10 R23 R25 Hsp Hlen Hat Hlt Hx Hb Hbr.
destruct (a6l_cut_nums v pos lyc Sc Wc rX memc mdc HB) as (N1 & N2 & R9 & R22 & H0 & _).
pose proof alloc_ceiling_lt as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := a6l_E rX [Z_to_bv 64 (at0 + sp); Z_to_bv 64 b]).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v).
{ unfold E. rewrite (a6l_ew_reg rX _ 9 (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (E10 : ew E 10 = Z_to_bv 64 sp) by (unfold E; rewrite (a6l_ew_reg rX _ 10 10%bv eq_refl); exact R10).
assert (E23 : ew E 23 = Z_to_bv 64 len) by (unfold E; rewrite (a6l_ew_reg rX _ 23 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = Z_to_bv 64 at0) by (unfold E; rewrite (a6l_ew_reg rX _ 25 25%bv eq_refl); exact R25).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E; rewrite (a6l_ew_reg rX _ 22 (Z_to_bv 5 22) eq_refl); exact R22).
assert (E32 : ew E 32 = Z_to_bv 64 (at0 + sp)) by (unfold E; exact (a6l_ew_extra rX _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 b) by (unfold E; exact (a6l_ew_extra rX _ 1 ltac:(unfold A_TEXT; lia))).
assert (U32 : bv_unsigned (ew E 32) = at0 + sp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = b) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SB) by (rewrite E22; unfold SB, SHADOW_OFF; apply unsigned_lit_small; lia).
rewrite a6l_lit_long in H0.
rewrite restrict_mkst_fx. unfold a6l_ssB. apply pa_entry_st_ok_full.
- exact (regs_ok_Eimg_Ereg rX _).
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + exact (a6l_slot_ok _ (w_H Wc) memc (pf_s1 v) 0xa0 0x213a0 U9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) H0).
  + unfold region_ok, a6l_byte.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ (at0 + sp) 0 1%N (SOff 33 0) b).
    * cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. exact E33.
    * change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    * lia.
    * rewrite Z.add_0_r. exact (a6l_val_mem1 (w_H Wc) memc _ b Hb Hbr).
- cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  unfold a6l_slot0, a6l_byte. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U32. split; [split; [right; lia | exact I] | split; exact I].
- split.
  + cbn [a6l_GB f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite U22, U32, U33. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
    repeat split; lia.
  + split.
    * cbn [a6l_GB f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_ltu_U, (U_atom E 10 sp E10 Hsp), (U_atom E 23 len E23 Hlen).
      apply Z.ltb_lt. exact Hlt.
    * cbn [a6l_GB f_alias alias_ok]. split; [|exact I].
      apply bv_eq. change (U E (SAlu ALU_ADD (SOff 25 0) (SOff 10 0)) = U E (SOff 32 0)).
      rewrite U_SAlu, (U_atom E 25 at0 E25 Hat), (U_atom E 10 sp E10 Hsp), (U_atom E 32 (at0 + sp) E32 ltac:(lia)).
      cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.

End e.
End f.
End d.
