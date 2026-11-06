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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 78 of its 107 lines of code are new or changed and 424 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...): the kit of
   refuse's prefix walk (0x894ac .. 0x89544) - the symbolic states of its two cut points, the statement of its
   second half, and the small state tactics the two proof files share. A sub-lane of the image-B refuse walk lane (the image-B G3 walk owner),
   2026-10-30.

   proves no function (kind: statement text). ADAPTED from plugin-hostd/fuzz_command lib/B/Prog/numberE.v /
   numberK.v (origin/ossv/recipes 501c0d516c69, the state tactics n_find / n_rewin / n_keep_regions and the cut
   statement form) and from lib/B/Prog/refuse_E.v / refuse_K.v of this lane's own base.

   THE CODE (refuse.fuzz_segconf.asan-ubsan.s lines 111-148). From RB_PRE (0x894ac) the token run reaches the
   `blez s4` at 0x894b0 and stops (atom 11 = line has the range [0, 2^31-1], which does not decide it). Both arms
   are real and both call the snprintf wrapper:
     line <= 0 : 0x894d0 .. 0x894e0, a2 = object 72 (0x21ac0 "%s: "), jal at 0x894e0, return 0x894e4 = RB_TEXT;
     line >  0 : 0x894b4 .. 0x894c8, a2 = object 71 (0x21aa0 "%s:%d: "), a4 = line, jal at 0x894c8, return
                 0x894cc, then `j 0x894e4`.
   At the call both arms have the same memory and the same non-clobbered registers, so one canonical state
   ss_txt at RB_TEXT serves both: the clobbered registers become the fresh atoms 1300 .. 1315 (a0 = atom 1304 =
   the snprintf result k), the regions kept are the frame's shadow, its three word regions, the saved registers
   and the spilled va words, and the block's n_refusals / refused cells, and the branch condition is dropped. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c refuse_E refuse_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== state tactics (numberE.v's, under the rbp_ prefix) ============================== *)
(* the index of the region with base atom b and low offset lo *)
Fixpoint rbp_find (rs : smem) (b : nat) (lo : Z) (i : nat) : nat :=
match rs with
| [] => i
| r :: rs' => if (match YP09.r_base r with Some k => Nat.eqb k b | None => false end) && (YP09.r_lo r =? lo) then i
              else rbp_find rs' b lo (S i)
end.
Ltac rbp_norm HS := lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* replace the state of HS by the (convertible) named state `target` *)
Ltac rbp_to HS target :=
lazymatch type of HS with
| st_ok_pi ?sg ?vl ?E ?ss ?ms =>
  let Q := fresh "Qeq" in assert (Q : ss = target) by (vm_compute; reflexivity); rewrite Q in HS; clear Q
| st_ok ?sg ?E ?ss ?ms =>
  let Q := fresh "Qeq" in assert (Q : ss = target) by (vm_compute; reflexivity); rewrite Q in HS; clear Q end.
(* give the region with base atom b and low offset lo the write window [wlo, whi) *)
Ltac rbp_rewin HS bse lo wlo whi wtac :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
let i := eval vm_compute in (rbp_find (ss_mem ssx) bse lo 0) in
let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r wlo whi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; wtac))) as HS3;
clear HS; rename HS3 into HS; rbp_norm HS end.
(* an opaque wrapper for the address facts the disjointness goals use *)
Definition rbp_nam (P : Prop) : Prop := P.
Ltac rbp_zl := lazymatch goal with AM : rbp_nam _ |- _ => revert AM end;
clear; unfold rbp_nam, off_img, zone2, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB; intros;
repeat match goal with H : _ /\ _ |- _ => destruct H end; lia.

(* ============================== the two runs of the prefix and the cut state ============================== *)
(* the text the first snprintf prints: SegModel's address prefix *)
Definition rbp_T1 (rcs : rconf) (ln : Z) : list Z :=
SegModel.fmt (SegModel.r_addr_fmt ln) (SegModel.r_addr_args rcs ln).
(* the fresh atoms of the snprintf return (a0 = k is atom 1300 + 4) *)
Definition rbp_KS : nat := 1300%nat.
(* 0x894cc: where the line > 0 arm returns, before its `j` to RB_TEXT *)
Definition RB_SNP_RET : Z := AF_refuse + 0x1d4.
Definition rbp_tok (ss : sstate) : sstate :=
sh_ss (fst (sym_runN_pi_tok seg_tpi seg_tw (rb_K ss) (SOff 32 0) Bspan rb_SH FUEL ss)).
(* the token run from RB_PRE stops at the `blez s4` (0x894b0) *)
Definition ss_p0 : sstate := Eval vm_compute in rbp_tok ss_pre.
(* line <= 0 and line > 0: each run stops at its `jal` to the snprintf trampoline *)
Definition ss_pT : sstate := Eval vm_compute in rbp_tok (add_cond ss_p0 (mkAC BC_GE (SLit 0) (SOff 11 0))).
Definition ss_pF : sstate := Eval vm_compute in rbp_tok (add_cond ss_p0 (mkAC (neg_bc BC_GE) (SLit 0) (SOff 11 0))).
(* the regions the call keeps: the frame's shadow, its three word regions, the saved registers and the spilled
   va words, and the block's n_refusals / refused cells (the GOT and flag cells and reading[0] are not read
   again and are dropped) *)
Definition rbp_keepi : list nat := [0; 1; 2; 3; 5; 11]%nat.
Definition rbp_rs : smem := Eval vm_compute in pick (ss_mem ss_pre) rbp_keepi.
Definition rbp_fx : facts := mkFacts (f_atoms (ss_facts ss_pre)) [] (f_alias (ss_facts ss_pre)).
Definition ss_txt : sstate := Eval vm_compute in set_facts (ss_after_call ss_pT rbp_rs rbp_KS RB_TEXT) rbp_fx.
(* the line > 0 arm reaches the same state: its call returns at RB_SNP_RET and the `j` only moves the pc *)
Definition ss_txtF : sstate := Eval vm_compute in ss_after_call ss_pF rbp_rs rbp_KS RB_SNP_RET.
Lemma ss_txt_of_F : set_facts (fst (sym_run_toN_pi seg_tpi FUEL RB_TEXT ss_txtF)) rbp_fx = ss_txt.
Proof. vm_compute. reflexivity. Qed.
Lemma ss_txtF_run : snd (sym_run_toN_pi seg_tpi FUEL RB_TEXT ss_txtF) = PRS_running.
Proof. vm_compute. reflexivity. Qed.

(* ============================== the statement of the second half ============================== *)
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
(* The walk from RB_TEXT (0x894e4) to the return: the `k >u 199` test, the ap slot, the UBSan trap T4, the
   vsnprintf call, checks 4 and 5, the trap T5, the n_refusals store and the release.
   What it is given at RB_TEXT: the contract's premises at the entry (rb_cx), the canonical state ss_txt, the
   journal since the entry, the environment's atoms, the stack-protector cells at this state, and what the first
   snprintf did - the block is the entry's apart from c->refused (now + 1) and the written prefix of the slot,
   which holds the address text T1 and its NUL, and a0 (atom 1304) is |T1|. *)
Definition RBP_TXT_stmt (STK RLO RHI : Z) (lit : list Z -> Z) (gotw guard : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch c line fp ln rcs f args ms md2 S2 fpos Ev,
rb_cx B STK RLO RHI lit gotw guard ly S W regs mem md ch c line fp ln rcs f args ->
160 + 16 + 3 * ESTACK <= STK ->
(length (rc_refusal rcs) < 8)%nat ->
img_env VAL A_LIM Ev ->
st_ok_pi SEGS VAL Ev ss_txt (restrict (w_H W) ms) ->
ajournal SEGS B STK (spZ regs) (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 W (ms_mem ms) md2 0 ->
frames S2 = (0, fpos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> (exists f0, S2 = set_fs f0 S) ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev n = getr regs r) ->
ew Ev 32 = Z_to_bv 64 SB -> ew Ev 33 = Z_to_bv 64 (rsp1 (spZ regs)) ->
ew Ev 35 = Z_to_bv 64 (Z.of_nat (length (rc_refusal rcs))) ->
ew Ev 36 = Z_to_bv 64 (rc_refused rcs) ->
ew Ev 1028 = Z_to_bv 64 (frame_addr ly 0 fpos) -> ew Ev 1040 = Z_to_bv 64 (flag_addr ly 0 fpos) ->
ew Ev 1041 = Z_to_bv 64 (SB + frame_addr ly 0 fpos / 8) ->
ew Ev 1304 = Z_to_bv 64 (Z.of_nat (length (rbp_T1 rcs ln))) ->
sa_ssp (rdW W (ms_mem ms)) gotw guard ->
(forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
  ~ (seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) <= i <
     seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat (length (rbp_T1 rcs ln)) + 1) ->
  rdW W (ms_mem ms) (c + i) = rdW W mem (c + i)) ->
rd32 (rdW W (ms_mem ms)) (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1) ->
sa_zs (rdW W (ms_mem ms)) (seg_spec.refusal_addr c (length (rc_refusal rcs))) (rbp_T1 rcs ln ++ [0]) ->
SRr SEGS W (mkCfg ms md2) (RB_POST B STK regs ly S W mem md c rcs (SegModel.refuse rcs ln f args)).
End e.
End f.
End d.
