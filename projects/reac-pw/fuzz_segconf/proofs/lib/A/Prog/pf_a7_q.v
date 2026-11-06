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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 189 of its 232 lines of code are new or changed and 410 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the mid-walk SEED of segment A7 of reac_segconf_parse_file's
   walk (segment A7's proof, 2026-10-30). From pf_pieces.v's frame part `pf_base B v pos lyc Sc Wc rX memc
   mdc PF_SC_LINE`, which every cut of A7 carries (HDR, CLR, RS3, and pf_a7_m.v's FUN, CLOSE, UNK, KWOK), it builds
   the symbolic state of the walk at ANY listing offset pc:
     a7_seed : pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
               st_ok_pi SEGS VAL (a7_E rX v pos) (a7_ss pc bw)
                 (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
   The form is plugin-hostd/fuzz_command's check_reply_sd.v cr_seed (origin/ossv/recipes 501c0d516c69) on this
   listing, as segconf's own trim_t.v tf_entry and cross_check_s3.v cc3_seed write it.

   THE ATOMS of a7_E rX v pos (read them with the a7_ew_* lemmas, never by unfolding the environment):
      0 .. 31  the registers rX at the seed (sr_atoms: the state names every register by its own atom)
      32       F  = pf_F v pos, the class-5 frame                          (a7_ew_F)
      33       SH = pf_SH v pos = shadow_addr F, the frame's first shadow cell (a7_ew_SH)
      34 .. 46 the entry's ra, s0, s1, s2 .. s11, in the order of PF_SAVED   (a7_ew_saved)
      240 ..   the image's values (Eimg; a7_E_img)
   Atom 8 is sp0 (s0 = sp0, pf_fi), atoms 2 and 9 are s1 (sp = s1, pf_fi), atom 22 is SHADOW_OFF (s6, pf_fi): it
   is the shadow base of every inline check of A7, so a token run takes Bx = a7_Bx = SOff 22 0.

   THE REGIONS of a7_ss pc bw (index: base atom, [lo, hi), write window, chunks):
      0  a7_saved_r  atom 8,  [-104, 0),        read-only, slot j at -8 - 8 j holds atom 34 + j (pf_saved)
      1  a7_slot_r   atom 9,  [0x98, 0xa0),     read-only, the spill slot s1 + 0x98 holds SOff 33 8 = SH + 8 (PF_SL;
                                                reloaded into s3 at 0x88100 and 0x8832c)
      2  a7_sh_r     atom 33, [0, 144),         read-only, cell i holds SLit (pf_shb PF_SC_LINE i) (pf_fsh): the
                                                frame's 144 shadow cells with buf in scope. Read-only, so a token
                                                run keeps sh_static_ok (AWALK-FORM.md pitfall 3); A7 writes no
                                                shadow byte.
      3  a7_buf_r bw atom 32, [0x40, 0x240),    buf (F + PF_O_BUF, 512 bytes), no chunk; writable iff bw = true
                                                (A7 stores the NUL at 0x880bc; trim stores one inside its call).
                                                A token run over a writable buf needs an SH entry that covers the
                                                window (cells_safe_b): a7_SH_buf = [mkSHE 32 0x40 0x240].
                                                A run that writes nothing takes bw = false: then the memory after
                                                the run is the memory before it (pf_a7_cr.v).
   THE FACTS: atom 2 and 9 (s1) in [2^46, 2^47] 32-aligned, atom 8 (sp0) in [2^46, 2^47] 16-aligned, atom 22 = SB
   exactly (span_in_band), atom 32 (F) PTR 5, atom 33 (SH) in [SB + 512, SB + 2^44] 4-aligned.
   Slot 0xb0 (the cut's cur, only INV_HDR / INV_CLOSE state it) is not in the state: no instruction of A7 reads
   it and no exit cut of A7 names it.

   The geometry (sp0, s1, F, SH) is pf_a5_k.v's a5_geo. *)
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
  pf_pieces pf_a5_k pf_a7_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The frame's shadow cells are bytes *)
Lemma a7_shb_range : forall sc i, 0 <= pf_shb sc i < 256.
Proof.
intros sc i. unfold pf_shb, pf_io.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.

(** ** The symbolic state of A7 (see the head comment) *)
Definition a7_saved_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (34 + j) 0))) (seq 0 13).
Definition a7_saved_r : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 a7_saved_chunks.
Definition a7_slot_r : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x98 0xa0 0 0 [YP09.mkChunk 0x98 (CVal 8 (SOff 33 8))].
Definition a7_sh_chunks : list YP09.chunk :=
  map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (pf_shb PF_SC_LINE (Z.of_nat i))))) (seq 0 144).
Definition a7_sh_r : YP09.region := YP09.mkRegion (Some 33%nat) 0 144 0 0 a7_sh_chunks.
Definition a7_buf_r (bw : bool) : YP09.region :=
  YP09.mkRegion (Some 32%nat) PF_O_BUF (PF_O_BUF + 512) PF_O_BUF (if bw then PF_O_BUF + 512 else PF_O_BUF) [].
Definition a7_regions (bw : bool) : smem := [a7_saved_r; a7_slot_r; a7_sh_r; a7_buf_r bw].
Definition a7_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
            (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SB SB 0); (32%nat, PTR 5);
            (33%nat, mkAF (SB + 512) (SB + 2 ^ 44) 2) ] [] [].
Definition a7_ss (pc : Z) (bw : bool) : sstate := mkSS pc sr_atoms (a7_regions bw) None a7_facts.
(* the shadow base of the inline checks (s6) and the shadow entry that covers buf's window *)
Definition a7_Bx : sv := SOff 22 0.
Definition a7_SH_buf : list shent := [mkSHE 32 PF_O_BUF (PF_O_BUF + 512)].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** The environment *)
Definition a7_extra (v : pfv) (pos : Z) : list word :=
  map (Z_to_bv 64) [pf_F v pos; pf_SH v pos] ++ map (fun r => getr (p_regs v) (Z_to_bv 5 r)) PF_SAVED.
Definition a7_E (rX : bvmap 5 word) (v : pfv) (pos : Z) : env := Eimg (Ereg rX (a7_extra v pos)).

Lemma a7_E_img : forall rX v pos, img_env VAL A_LIM (a7_E rX v pos).
Proof. intros rX v pos. unfold a7_E. apply Eimg_env. Qed.

Lemma a7_E_agree : forall rX v pos, env_agree 32 (Ereg rX (a7_extra v pos)) (a7_E rX v pos).
Proof.
intros rX v pos. split; [|reflexivity].
intros n Hn. unfold a7_E. apply Eimg_low. unfold A_TEXT. lia.
Qed.

(* atom k < 32 is register k at the seed *)
Lemma a7_ew_reg : forall rX v pos k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (a7_E rX v pos) k = getr rX r.
Proof. intros rX v pos k r Hk. unfold a7_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.

Lemma a7_ew_extra : forall rX v pos j, (j < 15)%nat ->
  ew (a7_E rX v pos) (32 + j) = nth j (a7_extra v pos) (Z_to_bv 64 0).
Proof. intros rX v pos j Hj. unfold a7_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Lemma a7_ew_F : forall rX v pos, ew (a7_E rX v pos) 32 = Z_to_bv 64 (pf_F v pos).
Proof. intros rX v pos. exact (a7_ew_extra rX v pos 0 ltac:(lia)). Qed.

Lemma a7_ew_SH : forall rX v pos, ew (a7_E rX v pos) 33 = Z_to_bv 64 (pf_SH v pos).
Proof. intros rX v pos. exact (a7_ew_extra rX v pos 1 ltac:(lia)). Qed.

(* atom 34 + j is the entry's value of the register PF_SAVED saves in slot j *)
Lemma a7_ew_saved : forall rX v pos j r, nth_error PF_SAVED j = Some r ->
  ew (a7_E rX v pos) (34 + j) = getr (p_regs v) (Z_to_bv 5 r).
Proof.
intros rX v pos j r Hr.
assert (Hj : (j < length PF_SAVED)%nat) by (apply nth_error_Some; rewrite Hr; discriminate).
cbn [length PF_SAVED] in Hj.
change (34 + j)%nat with (32 + (2 + j))%nat. rewrite a7_ew_extra by lia.
unfold a7_extra. cbn [map app nth Nat.add].
apply nth_error_nth. rewrite nth_error_map, Hr. reflexivity.
Qed.

(* the registers a run leaves as their own atoms keep the seed's values *)
Lemma a7_regs_kept : forall rX v pos ss (H : word -> bool) ms (l : list Z),
  st_ok_pi SEGS VAL (a7_E rX v pos) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    (map (Z_to_bv 5) l) = true ->
  forall k, In k l -> getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k).
Proof.
intros rX v pos ss H ms l HS Hl k Hk.
exact (regs_kept_of_st_ok_pi (a7_E rX v pos) ss (restrict H ms) rX (a7_extra v pos) (map (Z_to_bv 5) l) HS
  (a7_E_agree rX v pos) Hl (Z_to_bv 5 k) (in_map _ _ _ Hk)).
Qed.

(** ** One byte of the reader as a one-byte chunk (after pf_a12.v's a12_val_mem1) *)
Lemma a7q_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma a7q_val_mem1 : forall (H : word -> bool) (mem : word -> option byte) a z,
  aview SEGS H mem a = Some z -> 0 <= z < 256 -> val_mem SEGS (mrestrict H mem) a 1 z.
Proof.
intros H mem a z Hv Hz k Hk. assert (k = 0%nat) as -> by lia.
destruct (aview_byte SEGS H mem a z Hv) as (b & Hb & Hvb & _).
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
rewrite le_byte_small by (cbn; lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Hvb.
symmetry. apply a7q_byte_self.
Qed.

Section e.
Variable B : asyms.

(* the part of a cut of A7 that pf_a7_d.v's a7_st names, out of pf_base *)
Lemma a7_st_of_base : forall v pos lyc Sc Wc rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> a7_st B v pos lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc (HCX & (HJ & Hly & _ & Hperm & _) & HOBJ & _ & HFSH).
constructor; [exact HCX | exact HJ | exact Hly | exact Hperm | exact HOBJ | exact HFSH].
Qed.

(** ** The seed *)
Lemma a7_seed : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc (pc : Z) (bw : bool),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  st_ok_pi SEGS VAL (a7_E rX v pos) (a7_ss pc bw)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc pc bw HB.
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & HFP & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HRG.
destruct HB as (_ & (_ & _ & _ & _ & Hsaved & _) & _ & HSL & HFSH).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v))
  by (eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (R8 : getr rX (Z_to_bv 5 8) = w64 (pf_sp0 v))
  by (eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v))
  by (eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF)
  by (eapply a5_rg_get; [exact HRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
assert (H98 : rdword (rdW Wc memc) (pf_s1 v + 0x98) = Some (pf_SH v pos + 8)).
{ exact (proj1 (Forall_forall _ _) HSL (0x98, pf_SH v pos + 8)
    ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right]))). }
set (sp0 := pf_sp0 v) in *. set (s1 := pf_s1 v) in *. set (F := pf_F v pos) in *. set (SH := pf_SH v pos) in *.
assert (HF8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
  pose proof (Z.div_mod F 32 ltac:(lia)). lia. }
set (q := F / 8) in *.
unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *.
assert (U2 : bv_unsigned (ew (a7_E rX v pos) 2) = s1).
{ rewrite (a7_ew_reg rX v pos 2 (Z_to_bv 5 2) eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (U8 : bv_unsigned (ew (a7_E rX v pos) 8) = sp0).
{ rewrite (a7_ew_reg rX v pos 8 (Z_to_bv 5 8) eq_refl), R8. unfold w64. apply unsigned_lit_small. lia. }
assert (U9 : bv_unsigned (ew (a7_E rX v pos) 9) = s1).
{ rewrite (a7_ew_reg rX v pos 9 (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (U22 : bv_unsigned (ew (a7_E rX v pos) 22) = SB).
{ rewrite (a7_ew_reg rX v pos 22 (Z_to_bv 5 22) eq_refl), R22. unfold w64, SB. apply unsigned_lit_small. lia. }
assert (U32 : bv_unsigned (ew (a7_E rX v pos) 32) = F).
{ rewrite a7_ew_F. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew (a7_E rX v pos) 33) = SH).
{ rewrite a7_ew_SH. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold a7_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- destruct bw; vm_compute; reflexivity.
- unfold a7_regions. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  + (* the 13 saved registers *)
    unfold region_ok, a7_saved_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros ch Hch. unfold a7_saved_chunks in Hch. apply in_map_iff in Hch.
    destruct Hch as (j & <- & Hj). apply in_seq in Hj.
    destruct (nth_error PF_SAVED j) as [r|] eqn:Hr.
    2: { exfalso. apply nth_error_None in Hr. cbn [length PF_SAVED] in Hr. lia. }
    apply (chunk_ok_val SEGS _ _ sp0 _ 8%N _ (bv_unsigned (getr (p_regs v) (Z_to_bv 5 r)))).
    * cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. exact (a7_ew_saved rX v pos j r Hr).
    * exact (bv_unsigned_in_range 64 _).
    * lia.
    * replace (sp0 + (-8 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ (Hsaved j r Hr)).
  + (* the spill slot s1 + 0x98 *)
    unfold region_ok, a7_slot_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ s1 0x98 8%N (SOff 33 8) (SH + 8)).
    * cbn [sv_denot]. rewrite a7_ew_SH, unsigned_lit_small by lia. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ H98).
  + (* the frame's 144 shadow cells, buf in scope *)
    unfold region_ok, a7_sh_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros ch Hch. unfold a7_sh_chunks in Hch. apply in_map_iff in Hch.
    destruct Hch as (i & <- & Hi). apply in_seq in Hi.
    pose proof (a7_shb_range PF_SC_LINE (Z.of_nat i)) as Hz.
    apply (chunk_ok_val SEGS _ _ SH (Z.of_nat i) 1%N (SLit (pf_shb PF_SC_LINE (Z.of_nat i)))
      (pf_shb PF_SC_LINE (Z.of_nat i))).
    * reflexivity.
    * change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    * lia.
    * apply a7q_val_mem1; [apply HFSH; lia | exact Hz].
  + (* buf, writable iff bw *)
    unfold region_ok, a7_buf_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. unfold PF_O_BUF. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. destruct bw; [|lia].
    apply (apresent_writable SEGS). apply HFP. lia.
- (* the four regions are apart *)
  unfold a7_regions, a7_saved_r, a7_slot_r, a7_sh_r, a7_buf_r.
  cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite U8, U9, U32, U33. unfold PF_O_BUF.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  destruct G9 as [_ [G9 | [G9a G9b]]]; repeat split; lia.
- (* the facts *)
  split; [|split; exact I].
  cbn [a7_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U9, U22, U32, U33.
  assert (HSH4 : SH mod 4 = 0).
  { rewrite G10. replace (2147450880 + q) with ((536862720 + F / 32) * 4)
      by (pose proof (Z.div_mod F 32 ltac:(lia)); unfold q in *; lia).
    apply Z_mod_mult. }
  try change (2 ^ 5) with 32. try change (2 ^ 4) with 16. try change (2 ^ 2) with 4.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  rewrite G3, G5, G8. unfold SB. repeat split; lia.
Qed.

End e.
End f.
End d.
