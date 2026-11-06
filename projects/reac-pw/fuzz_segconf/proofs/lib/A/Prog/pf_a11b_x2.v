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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 527 of its 576 lines of code are new or changed and 404 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A11b of reac_segconf_parse_file's walk, the
   half KEXIT 0x886c8 -> LOWOUT 0x88774 (43 instructions: 9 up to and including the jal, 34 after it).
   Part of segment A11b's proof, by the G3 walk owner, 2026-10-30.

   THE CODE (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s), with F the class-5 frame and SH its shadow:
     0x886c8  auipc a0,0xfff99 ; addi a2,a0,0x1b8   a2 = 0x21880 = seg_litA_rc F_badmodel (listing object 65)
     0x886d0  ld s8,0x90(s1)    s8 = c          0x886d4 mv a0,s8     a0 = c
     0x886d8  mv a1,s10         a1 = lineno = ln + 1
     0x886dc  ld a3,0x50(s1)    a3 = cur_name = F + PF_O_CN
     0x886e0  ld a4,0x18(s1)    a4 = the value pointer vp
     0x886e4  ld a5,0x78(s1)    a5 = known = F + PF_O_KNOWN
     0x886e8  jal 0x88da4 <refuse>                   -> returns at 0x886ec
     0x886ec  addi a0,zero,-8
     0x886f0 .. 0x88768  31 x `sb a0,X(s11)`         known (cells 0x64..0x81) and ntok (cell 0x8a) OUT of
                                                     scope: the frame's scope moves PF_SC_KN -> PF_SC_L146
     0x8876c  ld s3,0x98(s1)    s3 = SH + 8 (PF_RL's value, restored)
     0x88770  ld s4,0xb0(s1)    s4 = &c->seg[gi]
     0x88774  LOWOUT
   So the walk is: one plain run KEXIT -> the jal (it writes nothing), the call, then a SECOND plain run from
   a fresh seed at 0x886ec to LOWOUT over the 31 shadow cells, then INV_LOWOUT and HA_LOWOUT.

   THE CALL. refuse's premises besides afn_pre are the closed site lemma of lib/A/Prog/pf_a11b_x1.v
   (`x1_refuse_site_ok_886e8`, VERIFY rule 1j-bis, no Section hypothesis). The call rule is
   `PaFx.cl_callSF`, the F form, because refuse's post is `apost_baseF`: it returns at an FP state of its own
   (the vsnprintf inside it), and the rest of the segment is proved at THAT state and lifted back with
   `srr_apost_baseF_lift`. The frame chain is `pf_a5_k.a5_chain` (not `achain_low`: in parse_file s0 IS sp0).
   After the call the heap facts are RE-DERIVED from the exit state's AR, because refuse's post has no keep
   clause (refuse_c.v:53-56): that is `pf_a6_k.a6_keeps_refuse` + `a6_base_move`, and THOSE TWO are the only
   reason this file takes the Section hypotheses SSPX and VRO (they are Section hypotheses of pf_a6_k.v;
   the image-A owner's route A discharges them from SegRecCells.seg_rec_cells after listing stage 2). Everything
   before and after the call is hypothesis-free: the 31 shadow stores use lib/A/Prog/pf_a11b_x.v's
   `x_base_sh` / `x_st_sh`, which carry sa_ssp and arodata_okP over the image range with no hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a5_k pf_a6_k pf_a11b_d pf_a11b_f pf_a11b_x pf_a11b_x1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The listing offset where the refuse call returns (0x886ec) *)
Definition PF_KR : Z := AF_reac_segconf_parse_file + 0xc74.


(** ** PF_SC_KN and PF_SC_L146 differ at the cells 0x64 .. 0x81 and 0x8a only *)
Lemma x2_shb_outkn : forall i, i < 100 \/ (130 <= i < 138) \/ 139 <= i ->
  pf_shb PF_SC_L146 i = pf_shb PF_SC_KN i.
Proof.
intros i H. unfold pf_shb, PF_SC_L146, PF_SC_KN.
cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct (i <? 4); [reflexivity|]. destruct (i <? 6); [reflexivity|].
destruct (i <? 8); [reflexivity|]. destruct (i <? 72); [reflexivity|].
destruct (i <? 80); [reflexivity|]. destruct (i <? 88); [reflexivity|].
destruct (i <? 92); [reflexivity|]. destruct (i <? 95); [reflexivity|].
destruct (i <? 100) eqn:E9; [reflexivity|]. apply Z.ltb_ge in E9.
destruct (i <? 130) eqn:EA; [exfalso; apply Z.ltb_lt in EA; lia|]. apply Z.ltb_ge in EA.
destruct (i <? 138) eqn:EB; [reflexivity|]. apply Z.ltb_ge in EB.
destruct (i <? 139) eqn:EC; [exfalso; apply Z.ltb_lt in EC; lia | reflexivity].
Qed.
Lemma x2_shb_l146_at : forall i, 0x64 <= i < 0x82 \/ i = 0x8a -> pf_shb PF_SC_L146 i = 0xf8.
Proof.
intros i H. unfold pf_shb, PF_SC_L146, pf_io. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct H as [H | ->].
- replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 6) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 72) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 80) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 88) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 92) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 95) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 100) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i <? 130) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
- vm_compute. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(** ** The realignment, sharper than pf_a5_k's a5_G: sp0 is 16-aligned, so s1 = (sp0 - 0x140) & -32 is
    sp0 - 320 or sp0 - 336, never lower. The call rule needs STK_refuse - (s1 - sp0) <= STK_parse_file,
    that is 12464 + (sp0 - s1) <= 12800. *)
Lemma x2_o16 : forall v, pf_sp0 v mod 16 = 0 ->
  pf_sp0 v - 336 <= pf_s1 v <= pf_sp0 v - 320 /\ (pf_s1 v - pf_sp0 v) mod 16 = 0.
Proof.
intros v H16. unfold pf_s1.
set (x := pf_sp0 v) in *.
pose proof (Z.mod_pos_bound (x - 0x140) 32 ltac:(lia)) as M.
assert (H16' : (x - 0x140) mod 16 = 0)
  by (replace (x - 0x140) with (x + (-20) * 16) by lia; rewrite Z_mod_plus_full; exact H16).
assert (Hm : ((x - 0x140) mod 32) mod 16 = 0).
{ rewrite (Z.mod_mod_divide (x - 0x140) 32 16 ltac:(exists 2; reflexivity)). exact H16'. }
pose proof (Z.div_mod ((x - 0x140) mod 32) 16 ltac:(lia)) as Dm.
pose proof (Z.mod_pos_bound ((x - 0x140) mod 32) 16 ltac:(lia)) as Mm.
assert (Hc : (x - 0x140) mod 32 = 0 \/ (x - 0x140) mod 32 = 16) by lia.
split; [lia|].
destruct Hc as [E | E]; rewrite E.
- replace (x - 0x140 - 0 - x) with ((-20) * 16) by lia. apply Z_mod_mult.
- replace (x - 0x140 - 16 - x) with ((-21) * 16) by lia. apply Z_mod_mult.
Qed.

(** ** The symbolic states of the two runs
    KEXIT: one READ-ONLY region on the s1 atom (9) with the four slots the four `ld` read; no store.
    0x886ec: the same for the two slots reloaded at 0x8876c / 0x88770, and TWO WRITABLE regions on the s11
    atom (27), over the shadow cells 0x64 .. 0x81 and over the cell 0x8a, that the 31 `sb` write. *)
Definition x2_ke_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x18 0x98 0 0
    [YP09.mkChunk 0x18 (CVal 8 (SOff 32 0));
     YP09.mkChunk 0x50 (CVal 8 (SOff 33 PF_O_CN));
     YP09.mkChunk 0x78 (CVal 8 (SOff 33 PF_O_KNOWN));
     YP09.mkChunk 0x90 (CVal 8 (SOff 34 0))].
Definition x2_ke_ss : sstate := mkSS PF_KEXIT sr_atoms [x2_ke_slots] None (mkFacts [] [] []).
Definition x2_kr_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x98 0xb8 0 0
    [YP09.mkChunk 0x98 (CVal 8 (SOff 27 8)); YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0))].
(* TWO shadow regions, not one interval: the 31 stores hit cells 0x64..0x81 and 0x8a, and the eight cells
   0x82..0x89 between them are NOT written, so a single window [0x64, 0x8b) would lose them at pf_fsh. *)
Definition x2_kr_ss : sstate :=
  mkSS PF_KR sr_atoms [x2_kr_slots; x_sh_r 0x64 0x82; x_sh_r 0x8a 0x8b] None (mkFacts [] [] []).
Section e.
Variable B : asyms.
(* the program callee, at the listing's entry and image A's numbers (the image-A owner's ruling 16:54Z) *)
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the abstract instance (SegObj.v) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (the contract writer's route A, the shape of
   lib/A/Prog/reac_segconf_parse.v:137). TAKEN ONLY FOR pf_a6_k.a6_base_move AFTER THE refuse CALL: refuse's
   post gives only its journal, the journal keeps an image byte only when it is not an owned static
   (YCbq.v:479), and whether gotwA / guardA are owned statics is a record fact of listing stage 2
   (SegRecCells.seg_rec_cells). VRO is taken for the same step, for a6_base_move's arodata_okP. *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the object atom of 0x21880 = seg_litA_rc F_badmodel (SegAddr.v seg_objs index 65, A_OBJ i = 241 + i;
   the auipc / addi pair at 0x886c8 denotes it) *)
Lemma x2_badmodel_atom : forall E, img_env VAL A_LIM E -> ew E 306%nat = w64 (seg_litA_rc F_badmodel).
Proof.
intros E HE. rewrite (img_env_atomP E 306%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 306%nat with (A_OBJ 65). rewrite (OBJ 65%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64. f_equal. all: vm_compute; reflexivity.
Qed.

(** ** The seed at KEXIT: the four slots the four `ld` read, read-only *)
Lemma x2_ke_seed : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc sc vp,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x18, vp)] -> 0 <= vp < 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 vp; w64 (pf_F v pos); w64 (p_c v)])) x2_ke_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KEXIT)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc vp HB HSL18 Hvp.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & Hly & Hfin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof alloc_ceiling_lt as Hac.
pose proof HB as (HCX & _ & HOBJ & HSL & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc sc HB) as HFIRG.
assert (Hc0 : 0 <= p_c v < 2 ^ 64).
{ pose proof HCX as (_ & _ & _ & Hc64 & _). lia. }
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v))
  by (eapply a5_rg_get; [exact HFIRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
set (E := Eimg (Ereg rX [w64 vp; w64 (pf_F v pos); w64 (p_c v)])).
assert (EX : forall j, (j < 3)%nat ->
  ew E (32 + j) = nth j [w64 vp; w64 (pf_F v pos); w64 (p_c v)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v).
{ subst E.
  rewrite (ew_Eimg_Ereg_nat rX [w64 vp; w64 (pf_F v pos); w64 (p_c v)] 9%nat (Z_to_bv 5 9) eq_refl), R9.
  unfold w64. apply unsigned_lit_small. lia. }
assert (U32 : bv_unsigned (ew E 32) = vp).
{ replace 32%nat with (32 + 0)%nat by reflexivity. rewrite (EX 0%nat ltac:(lia)). cbn [nth].
  unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = pf_F v pos).
{ replace 33%nat with (32 + 1)%nat by reflexivity. rewrite (EX 1%nat ltac:(lia)). cbn [nth].
  unfold w64. apply unsigned_lit_small. lia. }
assert (U34 : bv_unsigned (ew E 34) = p_c v).
{ replace 34%nat with (32 + 2)%nat by reflexivity. rewrite (EX 2%nat ltac:(lia)). cbn [nth].
  unfold w64. apply unsigned_lit_small. lia. }
assert (S18 : rdword (rdW Wc memc) (pf_s1 v + 0x18) = Some vp)
  by (exact (proj1 (Forall_forall _ _) HSL18 (0x18, vp) ltac:(cbn [In]; tauto))).
assert (S50 : rdword (rdW Wc memc) (pf_s1 v + 0x50) = Some (pf_F v pos + PF_O_CN))
  by (exact (proj1 (Forall_forall _ _) HSL (0x50, pf_F v pos + PF_O_CN)
       ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right])))).
assert (S78 : rdword (rdW Wc memc) (pf_s1 v + 0x78) = Some (pf_F v pos + PF_O_KNOWN))
  by (exact (proj1 (Forall_forall _ _) HSL (0x78, pf_F v pos + PF_O_KNOWN)
       ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right])))).
assert (S90 : rdword (rdW Wc memc) (pf_s1 v + 0x90) = Some (p_c v))
  by (exact (proj1 (Forall_forall _ _) HSL (0x90, p_c v)
       ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right])))).
rewrite restrict_mkst_fx. unfold x2_ke_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, x2_ke_slots.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x18 8%N (SOff 32 0) vp);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    apply val_mem_of_rdword. exact S18.
  + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x50 8%N (SOff 33 PF_O_CN) (pf_F v pos + PF_O_CN));
      [cbn [sv_denot]; rewrite U33; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold PF_O_CN; lia | cbn; lia |].
    apply val_mem_of_rdword. exact S50.
  + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x78 8%N (SOff 33 PF_O_KNOWN) (pf_F v pos + PF_O_KNOWN));
      [cbn [sv_denot]; rewrite U33; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold PF_O_KNOWN; lia | cbn; lia |].
    apply val_mem_of_rdword. exact S78.
  + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x90 8%N (SOff 34 0) (p_c v));
      [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    apply val_mem_of_rdword. exact S90.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [exact I | split; exact I].
Qed.

(** ** The seed at 0x886ec: the two slots reloaded, and the 31 shadow cells as a writable region *)
Lemma x2_kr_seed : forall (fxq : YK11.FPState) v pos lyc Sc (Wc : world SEGS) rX memc mdc sc gi,
  pf_base (fx := fxq) B v pos lyc Sc Wc rX memc mdc sc ->
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, seg_spec.rseg_addr (p_c v) gi)] ->
  getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos) ->
  0 <= seg_spec.rseg_addr (p_c v) gi < 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 (seg_spec.rseg_addr (p_c v) gi)])) x2_kr_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KR)) memc (seg_rom SEGS))).
Proof.
intros fxq v pos lyc Sc Wc rX memc mdc sc gi HB HSLb R27 Hgi.
pose proof (a5_geo (fx := fxq) B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & Hly & Hfin & G & _ & HSHP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof alloc_ceiling_lt as Hac.
unfold kLowMemEnd, kHighShadowEnd in G11, G12.
pose proof HB as (_ & _ & _ & HSL & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc sc HB) as HFIRG.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v))
  by (eapply a5_rg_get; [exact HFIRG | unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])]).
set (E := Eimg (Ereg rX [w64 (seg_spec.rseg_addr (p_c v) gi)])).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v).
{ subst E.
  rewrite (ew_Eimg_Ereg_nat rX [w64 (seg_spec.rseg_addr (p_c v) gi)] 9%nat (Z_to_bv 5 9) eq_refl), R9.
  unfold w64. apply unsigned_lit_small. lia. }
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos).
{ subst E.
  rewrite (ew_Eimg_Ereg_nat rX [w64 (seg_spec.rseg_addr (p_c v) gi)] 27%nat (Z_to_bv 5 27) eq_refl), R27.
  unfold w64. apply unsigned_lit_small. lia. }
assert (U32 : bv_unsigned (ew E 32) = seg_spec.rseg_addr (p_c v) gi).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth].
  unfold w64. apply unsigned_lit_small. lia. }
assert (S98 : rdword (rdW Wc memc) (pf_s1 v + 0x98) = Some (pf_SH v pos + 8))
  by (exact (proj1 (Forall_forall _ _) HSL (0x98, pf_SH v pos + 8)
       ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right])))).
assert (Sb0 : rdword (rdW Wc memc) (pf_s1 v + 0xb0) = Some (seg_spec.rseg_addr (p_c v) gi))
  by (exact (proj1 (Forall_forall _ _) HSLb (0xb0, seg_spec.rseg_addr (p_c v) gi) ltac:(cbn [In]; tauto))).
rewrite restrict_mkst_fx. unfold x2_kr_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold region_ok, x2_kr_slots.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x98 8%N (SOff 27 8) (pf_SH v pos + 8));
        [cbn [sv_denot]; rewrite U27; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      apply val_mem_of_rdword. exact S98.
    * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0xb0 8%N (SOff 32 0) (seg_spec.rseg_addr (p_c v) gi));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      apply val_mem_of_rdword. exact Sb0.
  + unfold region_ok, x_sh_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HSHP. lia.
  + unfold region_ok, x_sh_r.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HSHP. lia.
- apply pairwise_disjoint_of_extents. unfold x2_kr_slots, x_sh_r, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U27. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [exact I | split; exact I].
Qed.

(** ** 0x886ec -> LOWOUT: the 31 shadow stores and the two reloads, at ANY FP state
    This is the whole second half of the segment, and it takes NO Section hypothesis: the scope move
    PF_SC_KN -> PF_SC_L146 goes through pf_a11b_x.v's hypothesis-free x_base_sh / x_st_sh. *)
Lemma x2_after_ok : forall (fxq : YK11.FPState) n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi,
  H_LOWOUT (fx := fxq) B n ->
  pf_base (fx := fxq) B v pos lyc Sc Wc rX memc mdc PF_SC_KN ->
  pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn (pf_next (p_s v) o) (p_s v))) ->
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, seg_spec.rseg_addr (p_c v) gi)] ->
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KR) rX memc mdc)
      (pf_postm (fx := fxq) B v (cf, Some gi, nm) o ln).
Proof.
intros fxq n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi HLOW HB HMID HST HSLb HRG.
pose proof (a5_geo (fx := fxq) B v pos lyc Sc Wc rX memc mdc PF_SC_KN HB)
  as (HAR & Hly & Hfin & G & HFP & HSHP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof alloc_ceiling_lt as Hac.
unfold kLowMemEnd, kHighShadowEnd in G11, G12.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof (a5_fi_regs (fx := fxq) B v pos lyc Sc Wc rX memc mdc PF_SC_KN HB) as HFIRG.
pose proof (proj1 HFI) as HJ0.
pose proof HMID as (HMo & HMn & HMlctx).
pose proof HOBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
assert (Hgi : 0 <= seg_spec.rseg_addr (p_c v) gi < 2 ^ 64).
{ pose proof HST as (RC & COK & _).
  destruct RC as (bs & _ & Henc). destruct Henc as (Hlen & Hn32 & _).
  cbn [pf_cur_ok] in COK. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.SEG_C_SIZE in *. lia. }
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos)).
{ eapply a5_rg_get; [exact HRG|]. unfold PF_RM. cbn [app In].
  repeat (first [left; reflexivity | right]). }
(* the seed and the run *)
pose proof (x2_kr_seed fxq v pos lyc Sc Wc rX memc mdc PF_SC_KN gi HB HSLb R27 Hgi) as HS.
set (E := Eimg (Ereg rX [w64 (seg_spec.rseg_addr (p_c v) gi)])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos).
{ subst E.
  rewrite (ew_Eimg_Ereg_nat rX [w64 (seg_spec.rseg_addr (p_c v) gi)] 27%nat (Z_to_bv 5 27) eq_refl), R27.
  unfold w64. apply unsigned_lit_small. lia. }
unfold cfg_at. change (w64 (BASE + PF_KR)) with (Z_to_bv 64 (BASE + PF_KR)).
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fxq) B LAWS) HS HJ0 PF_LOWOUT.
{ intros a (r & Hr & Ha). unfold x2_kr_ss, x2_kr_slots, x_sh_r in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia| |];
  rewrite U27 in Ha;
  right; right; right; left; exists 5, pos; (split; [left; reflexivity|]); right;
  unfold in_zr; cbn [fst snd]; rewrite Hly;
  change (fs_frame_bytes 5 / 8) with 256; unfold pf_SH, pf_F in Ha; lia. }
pmkst HS.
(* what the run kept: everything off the two shadow windows *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((pf_SH v pos + 0x64 <= a < pf_SH v pos + 0x82) \/ (pf_SH v pos + 0x8a <= a < pf_SH v pos + 0x8b)) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs := SEGS) E (ss_mem x2_kr_ss) (w_H Wc) memc (ms_mem ms)
    (fun x => (pf_SH v pos + 0x64 <= x < pf_SH v pos + 0x82) \/ (pf_SH v pos + 0x8a <= x < pf_SH v pos + 0x8b))
    HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-;
    cbn [base_val] in Hrr; [lia | rewrite U27 in Hrr; lia | rewrite U27 in Hrr; lia]. }
assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 0 <= a < pf_SH v pos + 256) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply KEEP; [exact Ha|]. intros [HH | HH]; lia. }
(* the 31 bytes the run stored, each 0xf8 *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx _ =>
    pose proof (st_ok_pi_region_nth Ex ssx _ 1%nat _ HS eq_refl) as HR1;
    pose proof (st_ok_pi_region_nth Ex ssx _ 2%nat _ HS eq_refl) as HR2
end.
cbn [ms_mem restrict] in HR1, HR2.
assert (HV8 : bv_unsigned (sv_denot E (SLit 18446744073709551608)) mod 256 = 0xf8)
  by (vm_compute; reflexivity).
assert (VSH : forall i, (0x64 <= i < 0x82 \/ i = 0x8a) ->
  rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0xf8).
{ intros i Hi.
  assert (Hc : In i [100; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116;
                     117; 118; 119; 120; 121; 122; 123; 124; 125; 126; 127; 128; 129; 138])
    by (cbn [In]; lia).
  cbn [In] in Hc.
  repeat (destruct Hc as [<- | Hc]); try (exfalso; exact Hc);
    rewrite <- HV8;
    first
      [ eapply (x_byte1 E (w_H Wc) (ms_mem ms) 27%nat (pf_SH v pos)); [exact HR1 | exact U27 |];
        cbn [In]; repeat (first [left; reflexivity | right]); fail
      | eapply (x_byte1 E (w_H Wc) (ms_mem ms) 27%nat (pf_SH v pos)); [exact HR2 | exact U27 |];
        cbn [In]; repeat (first [left; reflexivity | right]) ]. }
(* the new frame shadow: known and ntok out of scope *)
assert (HFSH2 : pf_fsh (rdW Wc (ms_mem ms)) (pf_SH v pos) PF_SC_L146).
{ intros i Hi.
  destruct (Z_lt_le_dec i 0x64) as [Hl | Hl].
  { rewrite KEEP by lia. rewrite (x2_shb_outkn i ltac:(lia)). exact (HFSH i Hi). }
  destruct (Z_lt_le_dec i 0x82) as [Hu | Hu].
  { rewrite (VSH i ltac:(lia)). f_equal. symmetry. apply x2_shb_l146_at. lia. }
  destruct (Z.eq_dec i 0x8a) as [-> | Hne].
  { rewrite (VSH 0x8a ltac:(lia)). rewrite (x2_shb_l146_at 0x8a ltac:(lia)). reflexivity. }
  rewrite KEEP by lia. rewrite (x2_shb_outkn i ltac:(lia)). exact (HFSH i Hi). }
(* the registers *)
prreg HS (10%bv : bv 5) P10. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 21; 22; 24; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)).
{ intros k Hk.
  apply (regs_kept_of_st_ok_pi E _ _ rX [w64 (seg_spec.rseg_addr (p_c v) gi)]
           (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 21; 22; 24; 26; 27]) HS).
  - split; [intros nn Hnn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity.
  - apply in_map. exact Hk. }
assert (EW32 : ew E 32 = w64 (seg_spec.rseg_addr (p_c v) gi)).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (Bv10 : Z_to_bv 5 10 = (10%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (Bv19 : Z_to_bv 5 19 = (19%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (Bv20 : Z_to_bv 5 20 = (20%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
(* pf_base at the new state, with known and ntok out of scope *)
assert (HB2 : pf_base (fx := fxq) B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy mdc) mat mdc) PF_SC_L146).
{ apply (x_base_sh (fx := fxq) B v pos lyc Sc Wc rX memc mdc PF_SC_KN _ _ _ PF_SC_L146 HB HJ0);
    [| | exact HFSH2].
  - apply (x_keeps_sh (fx := fxq) B v pos lyc Sc Wc rX memc mdc PF_SC_KN _ 0 256 HB ltac:(lia) ltac:(lia)).
    exact KEEPF.
  - unfold pf_rg, a5_FI in *. rewrite Forall_forall in HFIRG |- *. intros rv Hin.
    rewrite (RK (fst rv)); [exact (HFIRG rv Hin)|].
    unfold a5_FI in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
(* pf_st at the new reader (the count is already the next line's: the refusal took its unit before 0x886ec) *)
assert (HST2 : pf_st v pos (rdW Wc (ms_mem ms)) cf (Some gi) nm (length (skipn (pf_next (p_s v) o) (p_s v))))
  by exact (x_st_sh (fx := fxq) B v pos lyc Sc Wc rX memc mdc PF_SC_KN (ms_mem ms) cf (Some gi) nm _ HB
    ltac:(intros a Ha Hn; apply KEEPF; [exact Ha | lia]) HST).
(* the exit: INV_LOWOUT *)
apply (HLOW v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)
  cf nm o ln d gi).
unfold INV_LOWOUT.
split; [exact HB2|]. split; [exact HMID|]. split; [exact HST2|].
unfold pf_rg. apply Forall_forall. intros rv Hin.
unfold PF_RL, PF_RM in Hin. cbn [In app] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]; cbn [fst snd].
- rewrite (RK 18 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG|]. cbn [In app]; tauto.
- rewrite Bv19, P19, U27. reflexivity.
- rewrite (RK 24 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG|]. cbn [In app]; tauto.
- rewrite (RK 27 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG|]. cbn [In app]; tauto.
- rewrite (RK 21 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG|].
  unfold PF_RM. cbn [In app]; tauto.
- rewrite (RK 26 ltac:(cbn [In]; tauto)). eapply a5_rg_get; [exact HRG|].
  unfold PF_RM. cbn [In app]; tauto.
- rewrite Bv20, P20. exact EW32.
- rewrite Bv10, P10. unfold w64. apply bv_eq. vm_compute. reflexivity.
Qed.

(** ** KEXIT 0x886c8 -> LOWOUT: pfx_kexit_ok
    The run to the jal (it writes nothing), the call (x1_refuse_site_ok_886e8 + cl_callSF + REF), the rebuild
    after it at the returned FP state (a6_keeps_refuse + a6_base_move: the ONLY use of VRO and SSPX), and
    x2_after_ok at that FP state, lifted back by srr_apost_baseF_lift. The shape is piece A7's
    lib/A/Prog/pf_a7_u.v at commit 89bf60b43b36 (the call at 0x880f8), with one difference:
    this run loads s8 = c (0x886d0), so the callee-saved registers are NOT all the cut's, and the run's kept
    registers are listed (RKC) instead of aregs_preserved_of_st_ok. *)
Theorem pfx_kexit_ok : forall n : nat, HA_LOWOUT B n -> H_KEXIT B n.
Proof.
intros n HLOW v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HINV.
pose proof HINV as (HB & HMID & HST & HVAL & HINB & HKN & HSLb & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_KN HB) as (HAR & Hly & Hfin & G & HFP & HSHP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof alloc_ceiling_lt as Hac.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
unfold kLowMemEnd, kHighShadowEnd in G11, G12.
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_KN HB) as HFIRG.
destruct (a5_chain B v pos lyc Sc Wc rX memc mdc PF_SC_KN HB) as [ch1 HCH].
pose proof HB as (HCX & (HJ0 & Hly' & HFS & HPERM & HSV & HFL & HFRM & _) & HOBJ & HSL & HFSH).
pose proof HOBJ as (_ & _ & _ & _ & HCH0 & _).
pose proof HMID as (HMo & HMn & HMlctx).
pose proof (a6_s1 (pf_sp0 v) G3) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HCH0
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & _).
assert (Hc0 : 0 <= p_c v < 2 ^ 64) by (pose proof HCX as (_ & _ & _ & Hc64 & _); lia).
assert (Hvp : 0 <= vp < 2 ^ 64).
{ pose proof HINB as [Hb1 Hb2]. unfold PF_O_BUF in Hb1, Hb2.
  pose proof (Nat2Z.is_nonneg (length val)). lia. }
assert (R26 : getr rX (Z_to_bv 5 26) = w64 (ln + 1)).
{ eapply a5_rg_get; [exact HRG|]. unfold PF_RM. cbn [app In].
  repeat (first [left; reflexivity | right]). }
(* ---------------- the run: KEXIT to the jal ---------------- *)
pose proof (x2_ke_seed v pos lyc Sc Wc rX memc mdc PF_SC_KN vp HB
  ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd];
        exact (proj1 (Forall_forall _ _) HSLb (0x18, vp) ltac:(cbn [In]; tauto))) Hvp) as HS.
set (E := Eimg (Ereg rX [w64 vp; w64 (pf_F v pos); w64 (p_c v)])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall j, (j < 3)%nat ->
  ew E (32 + j) = nth j [w64 vp; w64 (pf_F v pos); w64 (p_c v)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EW32 : ew E 32 = w64 vp) by exact (EX 0%nat ltac:(lia)).
assert (EW33 : ew E 33 = w64 (pf_F v pos)) by exact (EX 1%nat ltac:(lia)).
assert (EW34 : ew E 34 = w64 (p_c v)) by exact (EX 2%nat ltac:(lia)).
assert (EW26 : ew E 26 = w64 (ln + 1)).
{ subst E. rewrite (ew_Eimg_Ereg_nat rX [w64 vp; w64 (pf_F v pos); w64 (p_c v)] 26%nat (Z_to_bv 5 26) eq_refl).
  exact R26. }
unfold cfg_at. change (w64 (BASE + PF_KEXIT)) with (Z_to_bv 64 (BASE + PF_KEXIT)).
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ0.
{ intros a (r & Hr & Ha). unfold x2_ke_ss, x2_ke_slots in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
(* the run wrote nothing *)
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & Ha). unfold x2_ke_ss, x2_ke_slots in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite Hmem in HJ0 |- *.
clear HF HFr HG.
(* the registers at the call *)
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
prreg HS (15%bv : bv 5) Q15. prreg HS (24%bv : bv 5) Q24.
assert (RKC : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)).
{ intros k Hk.
  apply (regs_kept_of_st_ok SEGS E _ _ rX [w64 vp; w64 (pf_F v pos); w64 (p_c v)]
           (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]) HS).
  - split; [intros nn Hnn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity.
  - apply in_map. exact Hk. }
assert (C1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PF_KR)).
{ rewrite Q1. unfold PF_KR, AF_reac_segconf_parse_file. reflexivity. }
assert (C10 : getr (ms_regs ms) 10 = w64 (p_c v)) by (rewrite Q10; exact EW34).
assert (C11 : getr (ms_regs ms) 11 = w64 (ln + 1)) by (rewrite Q11; exact EW26).
assert (C12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_badmodel))
  by (rewrite Q12; exact (x2_badmodel_atom E HEI)).
assert (C13 : getr (ms_regs ms) 13 = w64 (pf_F v pos + PF_O_CN)).
{ rewrite Q13, EW33. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (C14 : getr (ms_regs ms) 14 = w64 vp) by (rewrite Q14; exact EW32).
assert (C15 : getr (ms_regs ms) 15 = w64 (pf_F v pos + PF_O_KNOWN)).
{ rewrite Q15, EW33. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ transitivity (getr rX (Z_to_bv 5 2)); [exact (RKC 2 ltac:(cbn [In]; tauto))|].
  exact (a5_rg_get rX _ 2 _ HFIRG ltac:(cbn [a5_FI In]; tauto)). }
assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ transitivity (getr rX (Z_to_bv 5 3)); [exact (RKC 3 ltac:(cbn [In]; tauto))|].
  exact (a5_rg_get rX _ 3 _ HFIRG ltac:(cbn [a5_FI In]; tauto)). }
assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ transitivity (getr rX (Z_to_bv 5 4)); [exact (RKC 4 ltac:(cbn [In]; tauto))|].
  exact (a5_rg_get rX _ 4 _ HFIRG ltac:(cbn [a5_FI In]; tauto)). }
assert (C8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v)).
{ transitivity (getr rX (Z_to_bv 5 8)); [exact (RKC 8 ltac:(cbn [In]; tauto))|].
  exact (a5_rg_get rX _ 8 _ HFIRG ltac:(cbn [a5_FI In]; tauto)). }
assert (Csp : spZ (ms_regs ms) = pf_s1 v).
{ unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
(* pf_base at the call state: its memory is the cut's, its journal the run's *)
assert (HBc : pf_base B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_KN).
{ split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
  refine (conj HJ0 (conj Hly' (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM _))))))).
  unfold pf_rg in HFIRG |- *. rewrite Forall_forall in HFIRG |- *. intros rv Hin.
  rewrite (RKC (fst rv)); [exact (HFIRG rv Hin)|].
  unfold a5_FI in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
(* VERIFY rule 1j-bis at 0x886e8: refuse_contract's premises besides afn_pre, pf_a11b_x1.v's site lemma *)
pose proof (x1_refuse_site_ok_886e8 B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (ms_regs ms) HINV
  C10 C11 C12 C13 C14 C15) as (ROD & _ & Hc64 & _ & Hl64 & _ & Hf64 & RPRE & ROOM & EV).
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) memc _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0
    STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_KR)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known]) /\
       sa_noalloc B lyc Sc ly2 S2) HJ0).
  - rewrite Csp. lia.
  - exact S1d.
  - lia.
  - rewrite SRF. lia.
  - rewrite SRF, SPF. pose proof (x2_o16 v G3) as (HO1 & _). lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [unfold PF_KR, AF_reac_segconf_parse_file; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold PF_KR, AF_reac_segconf_parse_file; lia).
    unfold PF_KR, AF_reac_segconf_parse_file. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (REF fx lyc Sc Wc (ms_regs ms) memc mdq ch1 (p_c v) (ln + 1) (seg_litA_rc F_badmodel) (ln + 1) cf
        F_badmodel [AS nm; AS val; AS known] HPRE1 ROD C10 Hc64 C11 Hl64 C12 Hf64 RPRE ROOM EV). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ a Ha)|].
    apply a6_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
(* back at 0x886ec, at the FP state fx1 refuse returned *)
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
unfold PF_MISSPOST, pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
destruct HNA2 as (HP2b & Hly2 & HS2).
pose proof (a6_keeps_refuse B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_KN cf ly2 S2 W2 mem2 md2 EV_refuse
  HBc HJc2 HP2b) as HK.
pose proof HK as (K1 & _ & _ & K4).
(* pf_base at the returned state: the heap facts re-derived from AR there (a6_base_move) *)
assert (HB2 : pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 PF_SC_KN).
{ apply (a6_base_move (fx := fx) B VRO SSPX fx1 v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_KN ly2 S2 W2 regs2
    mem2 md2 HBc Hfx1 HJ2 Hly2 HS2 HP2b HK).
  intros r Hr. apply HP2. unfold acallee_saved. cbn [In] in Hr. lia. }
(* the spine after the refusal, at the next line's count *)
assert (HST2 : pf_st v pos (rdW W2 mem2) (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known]) (Some gi) nm
  (length (skipn (pf_next (p_s v) o) (p_s v)))).
{ pose proof HST as (_ & COK & NM & CNT).
  split; [exact HRC2|]. split.
  { cbn [pf_cur_ok] in COK |- *.
    rewrite (proj1 (refuse_proj cf (ln + 1) F_badmodel [AS nm; AS val; AS known])). exact COK. }
  split.
  { apply (a6_nm_move v pos (rdW Wc memc) _ nm NM). intros a Ha. apply K4. left. exact Ha. }
  exact (pf_cnt_refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known] (length (skipn o (p_s v))) _
           (pf_next_skipn_lt (p_s v) o HMo) CNT). }
(* the s4 slot, above s1, is not refuse's *)
assert (HSLb2 : pf_sl (rdW W2 mem2) (pf_s1 v) [(0xb0, seg_spec.rseg_addr (p_c v) gi)]).
{ apply (a6_sl_move (rdW Wc memc) _ (pf_s1 v) _
    ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd];
          exact (proj1 (Forall_forall _ _) HSLb (0xb0, seg_spec.rseg_addr (p_c v) gi) ltac:(cbn [In]; tauto)))).
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst]. lia.
  - lia.
  - lia.
  - exact K1. }
(* the registers: callee-saved across refuse, and the run's before it (s8 = c from the run) *)
assert (Bv24 : Z_to_bv 5 24 = (24%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (HRG2 : pf_rg regs2 ([(18, 0x23); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln)).
{ unfold pf_rg. apply Forall_forall. intros rv Hin. unfold PF_RM in Hin. cbn [In app] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [fst snd].
  - rewrite (HP2 18 ltac:(unfold acallee_saved; lia)), (RKC 18 ltac:(cbn [In]; tauto)).
    eapply a5_rg_get; [exact HRG|]. cbn [app In]; tauto.
  - rewrite (HP2 24 ltac:(unfold acallee_saved; lia)), Bv24, Q24. exact EW34.
  - rewrite (HP2 27 ltac:(unfold acallee_saved; lia)), (RKC 27 ltac:(cbn [In]; tauto)).
    eapply a5_rg_get; [exact HRG|]. cbn [app In]; tauto.
  - rewrite (HP2 21 ltac:(unfold acallee_saved; lia)), (RKC 21 ltac:(cbn [In]; tauto)).
    eapply a5_rg_get; [exact HRG|]. unfold PF_RM. cbn [app In]; tauto.
  - rewrite (HP2 26 ltac:(unfold acallee_saved; lia)), (RKC 26 ltac:(cbn [In]; tauto)).
    eapply a5_rg_get; [exact HRG|]. unfold PF_RM. cbn [app In]; tauto. }
exact (x2_after_ok fx1 n v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known])
  nm o ln d gi (HLOW fx1) HB2 HMID HST2 HSLb2 HRG2).
Qed.

End e.
End f.
End d.
