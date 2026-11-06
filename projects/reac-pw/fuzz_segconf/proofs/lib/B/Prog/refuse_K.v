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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 110 of its 141 lines of code are new or changed and 422 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...): the cut points of
   refuse's image-B walk and the statements of its segments. The image-B refuse walk lane of the image-B G3 walk owner, 2026-10-30; the
   segment shape is plugin-hostd/fuzz_command lib/B/Prog/numberB.v / numberR.v's (origin/ossv/recipes 501c0d516c69):
   a segment lemma takes a symbolic state at a cut pc (st_ok_pi), the journal since refuse's entry, the atom
   equations, and the semantic facts the rest of the walk needs, and proves the contract's post.

   Cuts (image-B pcs, refuse.fuzz_segconf.asan-ubsan.s; BASE + RB_* of refuse_E.v):
   - RB_PRE 0x894ac (n_refusals < 8, after the head): ss_pre. The two where arms (0x894a0) differ only in a2
     (reading[0] or the .str.1 page) and a3 (where): ss_pre has a2, a3 as the fresh atoms 1100, 1101.
   - RB_REL 0x89544 (the frame release; the n >= 8 exit 0x89458, the k > 199 exit 0x894e8 and the fall-through after
     0x89540): ss_rel0 keeps only what the release and the epilogue read: sp = sp1 (atom 33), gp, tp, s0 = sp - 48,
     s2 = s7 = the frame (atom 1028), s8 = its shadow (1041), s11 (never written); every other register is a fresh
     atom 1200 + i; the regions are the frame's shadow and its words [0, 32) (read-only, no chunks), its words
     [40, 64) with the flag pointer at 56, and the twelve saved registers at sp - 144 .. sp - 56.
   Atom bands: the head's fresh atoms are 1024..1041; RB_PRE's canonical ones 1100, 1101; a segment from RB_PRE
   uses 1300 and up (and none in 1200..1222); RB_REL's canonical ones 1200..1222. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16 YM05 YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c refuse_E.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the canonical states ======================================== *)
(* RB_PRE: a2 and a3 fresh (atoms 1100, 1101), every region kept, the conditions of the head dropped *)
Definition RB_PRE_CLOB : list (bv 5) := [12; 13]%bv.
Definition rb_canon_pre (ss : sstate) : sstate :=
set_facts (ss_after_stretch ss (ss_mem ss) 1100 RB_PRE_CLOB RB_PRE) (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss))).
Definition ss_pre : sstate := Eval vm_compute in rb_canon_pre ss_r5F1.
Lemma ss_pre_of_1 : rb_canon_pre ss_r5F1 = ss_pre. Proof. vm_compute. reflexivity. Qed.
Lemma ss_pre_of_0 : rb_canon_pre ss_r5F0 = ss_pre. Proof. vm_compute. reflexivity. Qed.
(* RB_REL *)
Definition RB_REL_CLOB : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 25; 26; 28; 29; 30; 31]%bv.
Definition rel_r_fsh : YP09.region := YP09.mkRegion (Some 1041%nat) 0 8 0 0 [].
Definition rel_r_fra : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 0 [].
Definition rel_r_frc : YP09.region := YP09.mkRegion (Some 1028%nat) 40 64 40 40 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))].
Definition rel_r_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-144) 0 (-144) (-144)
[YP09.mkChunk (-144) (CVal 8 (SOff 26 0)); YP09.mkChunk (-136) (CVal 8 (SOff 25 0)); YP09.mkChunk (-128) (CVal 8 (SOff 24 0));
 YP09.mkChunk (-120) (CVal 8 (SOff 23 0)); YP09.mkChunk (-112) (CVal 8 (SOff 22 0)); YP09.mkChunk (-104) (CVal 8 (SOff 21 0));
 YP09.mkChunk (-96) (CVal 8 (SOff 20 0)); YP09.mkChunk (-88) (CVal 8 (SOff 19 0)); YP09.mkChunk (-80) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 9 0)); YP09.mkChunk (-64) (CVal 8 (SOff 8 0)); YP09.mkChunk (-56) (CVal 8 (SOff 1 0))].
Definition rel_regions : smem := [rel_r_fsh; rel_r_fra; rel_r_frc; rel_r_stk].
Definition rel_atoms : list (nat * afact) :=
[ (1041%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3); (1040%nat, mkAF 4096 (2 ^ 47) 0); (1028%nat, mkAF 4096 (2 ^ 47) 6);
  (2%nat, mkAF (2^46) (2^47) 4); (33%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF SB SB 0) ].
Definition rb_canon_rel (ss : sstate) : sstate :=
set_facts (ss_after_stretch ss rel_regions 1200 RB_REL_CLOB RB_REL) (mkFacts rel_atoms [] []).
Definition ss_rel0 : sstate := Eval vm_compute in rb_canon_rel ss_r3T.
Lemma ss_rel0_of_T : rb_canon_rel ss_r3T = ss_rel0. Proof. vm_compute. reflexivity. Qed.

(* ================================ the canonicalization step (one lemma) ================================ *)
(* a state at its own pc, with the clobber list's registers made fresh atoms k.., the regions cut to rs (each
   a subregion of a region of the state, in order) and the facts to a subset *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Lemma rb_region_kept_same : forall E m r, region_kept SEGS E m m r.
Proof. intros E m r. split; intros a _; [reflexivity | intros Hw; exact Hw]. Qed.
Lemma rb_canon_ok : forall (H : word -> bool) E ss ms k clob rs retk fa cs al,
st_ok_pi SEGS VAL E ss (restrict H ms) -> ss_resv ss = None -> ss_pc ss = retk ->
ss_atoms_p (pband k (k + length clob)) ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_p (pband k (k + length clob)) rs = true ->
submemb rs (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
(forall x, In x fa -> In x (f_atoms (ss_facts ss))) -> (forall x, In x cs -> In x (f_conds (ss_facts ss))) ->
(forall x, In x al -> In x (f_alias (ss_facts ss))) ->
st_ok_pi SEGS VAL (havoc E k (map (getr (ms_regs ms)) clob))
(set_facts (ss_after_stretch ss rs k clob retk) (mkFacts fa cs al)) (restrict H ms).
Proof.
intros H E ss ms k clob rs retk fa cs al HS Hrv Hpc Hat Hwf Hnc Hmat Hsub Hnd Hnz Hfa Hcs Hal.
pose proof (st_ok_pi_restrict_mkst H E ss ms HS Hrv) as Hms.
assert (HS' : st_ok SEGS E (abs_ss VAL ss) (restrict H ms)) by exact HS.
pose proof (st_ok_pi_after_stretch_hi k E (abs_ss VAL ss) (restrict H ms) (ms_regs ms) (mrestrict H (ms_mem ms)) rs retk clob HS'
  ltac:(destruct ss; exact Hrv) ltac:(destruct ss; exact Hat) Hwf Hnc Hmat (submemb_sound _ _ ltac:(destruct ss; exact Hsub)) Hnd Hnz
  ltac:(intros r _; reflexivity) ltac:(apply Forall_forall; intros r _; apply rb_region_kept_same)) as HS2.
assert (Heq : ss_after_stretch (abs_ss VAL ss) rs k clob retk = ss_after_stretch ss rs k clob retk) by (destruct ss; reflexivity).
rewrite Heq in HS2.
assert (Hm2 : mkst (ms_regs ms) (Z_to_bv 64 (BASE + retk)) (mrestrict H (ms_mem ms)) (seg_rom SEGS) = restrict H ms).
{ transitivity (restrict H (mkst (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (ms_mem ms) (seg_rom SEGS))).
  - rewrite restrict_mkst_fx, Hpc. reflexivity.
  - f_equal. symmetry. exact Hms. }
rewrite Hm2 in HS2.
pose proof (st_ok_pi_facts_incl3 _ _ _ fa cs al HS2 Hfa Hcs Hal) as HS3.
exact HS3.
Qed.
End k.

(* ======================================== the segment statements ======================================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the contract's post (refuse_c.v refuse_contract), at the FP state of this section *)
Definition RB_POST (STK : Z) (regs : bvmap 5 word) ly S W mem md (c : Z) (rcs rcs2 : rconf) :=
apost_baseF SEGS B STK (refuse_W c rcs) regs ly S W mem md EV_refuse
(fun ly' S' W' regs' mem' md' => sa_rconf (rdW W' mem') c rcs2 /\ sa_noalloc B ly S ly' S').
(* the release (0x89544 .. ret): from ss_rel0 with the journal since the entry (own = the class-0 frame), the
   block's state rcs2 at the release kept to the return *)
Definition RB_REL_stmt : Prop :=
forall STK ly S W (regs : bvmap 5 word) mem md ch c rcs rcs2 ms md3 S2 fpos Ev,
afn_pre SEGS B STK ly S W regs mem md ch -> 176 <= STK ->
sa_heap B ly S c seg_spec.SEG_C_SIZE ->
img_env VAL A_LIM Ev ->
st_ok_pi SEGS VAL Ev ss_rel0 (restrict (w_H W) ms) ->
ajournal SEGS B STK (spZ regs) (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 W (ms_mem ms) md3 0 ->
frames S2 = (0, fpos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> (exists f, S2 = set_fs f S) ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev n = getr regs r) ->
ew Ev 32 = Z_to_bv 64 SB -> ew Ev 33 = Z_to_bv 64 (rsp1 (spZ regs)) ->
ew Ev 1028 = Z_to_bv 64 (frame_addr ly 0 fpos) -> ew Ev 1040 = Z_to_bv 64 (flag_addr ly 0 fpos) ->
ew Ev 1041 = Z_to_bv 64 (SB + frame_addr ly 0 fpos / 8) ->
sa_rconf (rdW W (ms_mem ms)) c rcs2 ->
SRr SEGS W (mkCfg ms md3) (RB_POST STK regs ly S W mem md c rcs rcs2).
(* the contract's premises at the entry, as one conjunction (refuse_c.v refuse_contract, :145-155) *)
Definition rb_cx (STK RLO RHI : Z) (lit : list Z -> Z) (gotw guard : Z) ly S W (regs : bvmap 5 word) mem md ch
(c line fp ln : Z) (rcs : rconf) (f : list Z) (args : list SegModel.arg) : Prop :=
afn_pre SEGS B STK ly S W regs mem md ch /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
getr regs 10 = w64 c /\ 0 <= c < 2 ^ 64 /\ getr regs 11 = w64 line /\ 0 <= line < 2 ^ 64 /\
getr regs 12 = w64 fp /\ 0 <= fp < 2 ^ 64 /\
refuse_pre SEGS B lit gotw guard ly S regs (rdW W mem) c line fp
  [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] rcs ln f args /\
sa_room S /\ st_nev S + EV_refuse <= EV_MAX.
(* the prefix and the text (0x894ac .. 0x89544, both snprintf arms and vsnprintf), then the release: from ss_pre
   with the journal since the entry; the block as at the entry but refused + 1; n_refusals < 8; the where pointer
   (atom 1101) c->reading or the literal "reac-pw.conf"; the stack-protector cells at ms (the head takes them from
   SSPX right after the frame take, where the journal's image clause cannot keep them, and keeps them to ms) *)
Definition RB_PRE_stmt (STK RLO RHI : Z) (lit : list Z -> Z) (gotw guard : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch c line fp ln rcs f args ms md2 S2 fpos Ev,
rb_cx STK RLO RHI lit gotw guard ly S W regs mem md ch c line fp ln rcs f args ->
160 + 16 + 3 * ESTACK <= STK ->
(length (rc_refusal rcs) < 8)%nat ->
img_env VAL A_LIM Ev ->
st_ok_pi SEGS VAL Ev ss_pre (restrict (w_H W) ms) ->
ajournal SEGS B STK (spZ regs) (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 W (ms_mem ms) md2 0 ->
frames S2 = (0, fpos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> (exists f0, S2 = set_fs f0 S) ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev n = getr regs r) ->
ew Ev 32 = Z_to_bv 64 SB -> ew Ev 33 = Z_to_bv 64 (rsp1 (spZ regs)) -> ew Ev 34 = Z_to_bv 64 (as_uar_cell B) ->
ew Ev 35 = Z_to_bv 64 (Z.of_nat (length (rc_refusal rcs))) -> ew Ev 36 = Z_to_bv 64 (rc_refused rcs) ->
ew Ev 37 = Z_to_bv 64 (SegModel.hd0 (rc_reading rcs)) ->
ew Ev 1028 = Z_to_bv 64 (frame_addr ly 0 fpos) -> ew Ev 1040 = Z_to_bv 64 (flag_addr ly 0 fpos) ->
ew Ev 1041 = Z_to_bv 64 (SB + frame_addr ly 0 fpos / 8) ->
ew Ev 1101 = Z_to_bv 64 (if SegModel.hd0 (rc_reading rcs) =? 0 then lit SegModel.S_base else c + seg_spec.RC_READING) ->
(forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
  rdW W (ms_mem ms) (c + i) = rdW W mem (c + i)) ->
rd32 (rdW W (ms_mem ms)) (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1) ->
sa_ssp (rdW W (ms_mem ms)) gotw guard ->
SRr SEGS W (mkCfg ms md2) (RB_POST STK regs ly S W mem md c rcs (SegModel.refuse rcs ln f args)).
End e.
End f.
End d.
