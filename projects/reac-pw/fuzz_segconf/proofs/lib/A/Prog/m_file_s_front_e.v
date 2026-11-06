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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 815 of its 870 lines of code are new or changed and 398 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_FRONT, the segment's two end pieces.
   e: 0x860f4-0x8610c and the three short-line tests (MF-CUTS-A.md section 4). a7 = the next line's address
   (s7, or s4 + 1 when strchr found a '\n'), a0 = s7 - s11 = the line's length L, s6 = line + 1; `bge a1,a0`
   with a1 = 511 sends a line of 512 bytes or more to MF_LONG; else `bgeu s11,s7` twice (the comment scan and
   the strip are both empty when L = 0) reaches FR_ST with i0 = j0 = 0, and a line with L > 0 reaches the
   comment loop FR_CL at index 0 (a3 = 0, a6 = ';').
   st: 0x862a4-0x862c8. `beq s11,s7` sends an empty stripped line to MF_TAIL (the next line). Else the first
   byte of the stripped line is checked (the instrumented check at 0x862b0: a load of the shadow byte at
   (s11 >> 3) + the shadow base and a compare; its error path, the call of errpath_load1 0x86fe0, is not
   reached because the text is addressable) and loaded, the next line's address is stored in 144(s1),
   a2 = s7 - s11 = j0 - i0, and `bne a0,a1` with a1 = '[' splits MF_HDR from MF_KEY.
   The e piece reads no byte and stores nothing (its state is the registers alone); the st piece reads one
   text byte and writes the 8 bytes of 144(s1), so its cut facts are carried by m_file_k.v's mf_keep_run_s.
   The FRONT segment lane of the G2 walk owner's G2. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_front_mdl m_file_s_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_k m_file_s_front_g.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* e's state and st's state when the stripped line is empty: the registers alone *)
Definition ss_fe : sstate := mkSS FR_E sr_atoms [] None (mkFacts [] [] []).
Definition ss_fs0 : sstate := mkSS FR_ST sr_atoms [] None (mkFacts [] [] []).
(* st's state when it is not: the byte at s11 (atom 32), read-only, and the slot 144(s1), written *)
Definition fs_text : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition fs_slot : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 144 152 [].
Definition fs_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF SB SB 0); (27%nat, PTR 0); (32%nat, mkAF 0 255 0)] [] [].
Definition ss_fs1 : sstate := mkSS FR_ST sr_atoms [fs_text; fs_slot] None fs_facts.

(* a signed branch on two values below 2^63 *)
Lemma fe_bge_U : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof.
intros E a b Ha Hb. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite !YK11.bv_signed_small by exact Ha || exact Hb. reflexivity.
Qed.
(* `sub rd,a,b` as the executor forms it *)
Lemma fe_U_sub : forall E a b,
  U E (SAlu ALU_ADD a (SMd M_MUL b (SLit (-1)))) = (U E a - U E b) mod 2 ^ 64.
Proof.
intros E a b. rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
assert (Hm1 : (-1) mod 2 ^ 64 = 2 ^ 64 - 1) by (vm_compute; reflexivity).
rewrite Hm1, Z.add_mod_idemp_r by lia.
replace (U E a + U E b * (2 ^ 64 - 1)) with (U E a - U E b + U E b * 2 ^ 64) by ring.
apply Z_mod_plus_full.
Qed.
(* the first byte of a nonempty slice *)
Lemma fe_hd0_slice : forall (l : list Z) a b, (a < b <= length l)%nat -> hd0 (slice a b l) = nth a l 0.
Proof.
intros l a b Hab. unfold slice.
assert (HS : exists x r, skipn a l = x :: r).
{ destruct (skipn a l) as [|x r] eqn:E; [|exists x, r; reflexivity].
  exfalso. pose proof (length_skipn a l) as HL. rewrite E in HL. cbn [length] in HL. lia. }
destruct HS as (x & r & HE).
assert (Hx : nth 0 (skipn a l) 0 = nth a l 0) by (rewrite mf_nth_skipn; f_equal; lia).
rewrite HE in Hx. cbn [nth] in Hx.
rewrite HE. replace (b - a)%nat with (S (b - a - 1)) by lia. cbn [firstn hd0]. exact Hx.
Qed.

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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the write goal of a run whose regions are all read-only *)
Ltac fr_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* after such a run: the reader is the piece's start reader (MEQ), byte for byte *)
Ltac fr_meq :=
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1),
    MEQ : forall a, aview _ _ ?m0 a = aview _ _ ?mc a |- _ =>
    let M := fresh "M" in
    pose proof (fr_aview_ro _ rs H m0 m1 HFr ltac:(vm_compute; reflexivity)) as M;
    let MEQ' := fresh "MEQ" in
    assert (MEQ' : forall a, aview SEGS H m1 a = aview SEGS H mc a) by (intros a; rewrite M; apply MEQ);
    clear M MEQ HFr; rename MEQ' into MEQ end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* a register of the run's state as the symbolic value the state gives it (not normalized: SAluw / SMd stay) *)
Ltac fe_preg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

(* ======================================== piece e ======================================== *)
Section pe.
Variables (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z).
Hypothesis HLONG : MF_LONG_stmt B n.
Hypothesis HCL : forall i, FR_CL_stmt B n i.
Hypothesis HST : FR_ST_stmt B n.
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis R27 : getr regs1 27 = w64 p.
Hypothesis R22 : getr regs1 22 = w64 line.
Hypothesis R23 : getr regs1 23 = w64 (p + Z.of_nat (length (mf_line rest))).
Hypothesis R20 : getr regs1 20 = w64 (fr_nl p rest).

Definition fe_E : env := Eimg (Ereg regs1 []).

Lemma fe_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew fe_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold fe_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma fe_HAE : env_agree 32 (Ereg regs1 []) fe_E.
Proof. unfold fe_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma fe_R19 : getr regs1 19 = w64 0x20.
Proof.
pose proof CTX as (_ & _ & _ & _ & _ & RA & _). destruct RA as (_ & _ & _ & _ & _ & _ & R19 & _). exact R19.
Qed.

Lemma fe_tf : 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\
  0 <= p + Z.of_nat (length (mf_line rest)) < 2 ^ 64 /\ 0 <= p < 2 ^ 64 /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\
  (length (mf_line rest) <= length rest)%nat /\ rest <> [].
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & _ & _ & _).
pose proof (fr_line_len rest) as HLL. pose proof alloc_ceiling_value as [[_ HAC] _].
pose proof CTX as (_ & _ & _ & _ & _ & _ & _ & _ & Hne & LOOP & _).
pose proof LOOP as (_ & _ & _ & _ & _ & _ & _ & HL0 & HL1 & _).
split; [exact H1|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact HL0|]. split; [exact HL1|]. split; [exact HLL | exact Hne].
Qed.
Lemma fe_nl_rng : 0 <= fr_nl p rest /\ fr_nl p rest + 1 < 2 ^ 64.
Proof.
pose proof fe_tf as (T1 & T2 & T3 & T4 & _). pose proof alloc_ceiling_value as [[_ HAC] _].
unfold fr_nl. destruct (existsb (fun b => b =? NL) rest); lia.
Qed.
Lemma fe_nl_cases :
  (fr_nl p rest = 0 /\ mf_next p rest = p + Z.of_nat (length (mf_line rest))) \/
  (fr_nl p rest = p + Z.of_nat (length (mf_line rest)) /\
   mf_next p rest = p + Z.of_nat (length (mf_line rest)) + 1).
Proof.
unfold fr_nl. destruct (fr_next_cases p rest) as [(He & Hn)|(He & Hn & _)]; rewrite He.
- right. split; [reflexivity | exact Hn].
- left. split; [reflexivity | exact Hn].
Qed.
Lemma fe_next_of_nl0 : fr_nl p rest = 0 -> mf_next p rest = p + Z.of_nat (length (mf_line rest)).
Proof.
intros H0. destruct fe_nl_cases as [(_ & Hn)|(He & _)]; [exact Hn|].
exfalso. pose proof fe_tf as (T1 & _). rewrite He in H0. lia.
Qed.
Lemma fe_next_of_nlS : fr_nl p rest <> 0 -> mf_next p rest = fr_nl p rest + 1.
Proof.
intros H0. destruct fe_nl_cases as [(He & _)|(He & Hn)]; [congruence|]. rewrite He. exact Hn.
Qed.

(* the atoms' values at the piece's one environment (the piece makes no fresh atom) *)
Lemma fe_U27 : U fe_E (SOff 27 0) = p.
Proof.
pose proof fe_tf as (_ & _ & _ & T4 & _).
apply U_atom; [rewrite (fe_EN 27%nat 27%bv eq_refl) by lia; exact R27 | lia].
Qed.
Lemma fe_U23 : U fe_E (SOff 23 0) = p + Z.of_nat (length (mf_line rest)).
Proof.
pose proof fe_tf as (_ & _ & T3 & _).
apply U_atom; [rewrite (fe_EN 23%nat 23%bv eq_refl) by lia; exact R23 | lia].
Qed.
Lemma fe_U22 : U fe_E (SOff 22 0) = line.
Proof.
pose proof fe_tf as (_ & _ & _ & _ & T5 & T6 & _).
apply U_atom; [rewrite (fe_EN 22%nat 22%bv eq_refl) by lia; exact R22 | lia].
Qed.
Lemma fe_U20 : U fe_E (SOff 20 0) = fr_nl p rest.
Proof.
pose proof fe_nl_rng as (N1 & N2).
apply U_atom; [rewrite (fe_EN 20%nat 20%bv eq_refl) by lia; exact R20 | lia].
Qed.
Lemma fe_U20o : U fe_E (SOff 20 1) = fr_nl p rest + 1.
Proof.
pose proof fe_nl_rng as (N1 & N2).
apply fr_U_atom_off; [rewrite (fe_EN 20%nat 20%bv eq_refl) by lia; exact R20 | lia | lia].
Qed.
Lemma fe_U22w : U fe_E (SAluw ALU_ADD (SOff 22 0) (SLit 1)) = line + 1.
Proof.
pose proof fe_tf as (_ & _ & _ & _ & T5 & T6 & _).
rewrite U_of_S, S_SAluw, fe_U22, (U_lit fe_E 1) by lia. cbn [zalu_raw].
rewrite (Z.mod_small line (2 ^ 32)) by lia. rewrite (Z.mod_small 1 (2 ^ 32)) by lia.
rewrite swrap32_id by lia. apply wrap64_id. unfold M64. lia.
Qed.
Lemma fe_UL : U fe_E (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 27 0) (SLit (-1)))) =
  Z.of_nat (length (mf_line rest)).
Proof.
pose proof fe_tf as (T1 & T2 & T3 & T4 & _).
rewrite fe_U_sub, fe_U23, fe_U27.
replace (p + Z.of_nat (length (mf_line rest)) - p) with (Z.of_nat (length (mf_line rest))) by ring.
apply Z.mod_small. lia.
Qed.

(* the three branch conditions as facts of the line *)
Lemma fe_breq : forall b, branch_taken BC_EQ (sv_denot fe_E (SOff 20 0)) (sv_denot fe_E (SLit 0)) = b ->
  b = (fr_nl p rest =? 0).
Proof. intros b H. rewrite <- H, branch_eq_U, fe_U20, (U_lit fe_E 0) by lia. reflexivity. Qed.
Lemma fe_brge : forall b,
  branch_taken BC_GE (sv_denot fe_E (SLit 511))
    (sv_denot fe_E (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 27 0) (SLit (-1))))) = b ->
  b = negb (511 <? Z.of_nat (length (mf_line rest))).
Proof.
intros b H. pose proof fe_tf as (T1 & T2 & T3 & T4 & _).
pose proof alloc_ceiling_value as [[_ HAC] _]. rewrite <- H, fe_bge_U.
- rewrite (U_lit fe_E 511) by lia. rewrite fe_UL. reflexivity.
- rewrite (U_lit fe_E 511) by lia. lia.
- rewrite fe_UL. lia.
Qed.
Lemma fe_brgeu : forall b, branch_taken BC_GEU (sv_denot fe_E (SOff 27 0)) (sv_denot fe_E (SOff 23 0)) = b ->
  b = negb (p <? p + Z.of_nat (length (mf_line rest))).
Proof. intros b H. rewrite <- H, branch_geu_U, fe_U27, fe_U23. reflexivity. Qed.

Lemma fe_seed : st_ok_pi SEGS VAL fe_E ss_fe
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_E)) memc (seg_rom SEGS))).
Proof.
rewrite restrict_mkst_fx. unfold ss_fe. apply pa_entry_st_ok_full.
- unfold fe_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [cbn; first [exact I | constructor] | split; [exact I | exact I]].
Qed.

(* the three exits of the piece, from the cut statements it leaves to *)
Lemma fe_to_long : forall regs2 mem2 md2,
  fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  getr regs2 27 = w64 p ->
  getr regs2 23 = w64 (p + Z.of_nat (length (mf_line rest))) ->
  getr regs2 17 = w64 (mf_next p rest) ->
  getr regs2 22 = w64 (line + 1) ->
  (512 <= length (mf_line rest))%nat ->
  mf_at B v Wc regs2 mem2 md2 MF_LONG.
Proof.
intros regs2 mem2 md2 CTX2 Q27 Q23 Q17 Q22 HGE.
destruct CTX2 as (CX & LS & FRM & CORE & CELLS & RA & Q24 & Hn & Hne & LOOP & EQ & Q21).
apply (HLONG v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest);
  [exact CX | exact LS | exact FRM | exact CORE | exact CELLS | exact RA | exact Q24 | exact Hn | exact Hne
  | exact LOOP | exact HGE | exact (fr_eq_long (mcc, cur) line rest (mf_final v) Hne EQ)
  | exact Q27 | exact Q23 | exact Q17 | exact Q22 | exact Q21].
Qed.
Lemma fe_to_cl0 : forall regs2 mem2 md2,
  fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest ->
  getr regs2 27 = w64 p ->
  getr regs2 23 = w64 (p + Z.of_nat (length (mf_line rest))) ->
  getr regs2 16 = w64 59 ->
  getr regs2 12 = w64 (p + Z.of_nat 0) ->
  getr regs2 10 = w64 (p + Z.of_nat 0) ->
  getr regs2 13 = w64 (- Z.of_nat 0) ->
  (0 < length (mf_line rest))%nat ->
  mf_at B v Wc regs2 mem2 md2 FR_CL.
Proof.
intros regs2 mem2 md2 CTX2 SH2 Q27 Q23 Q16 Q12 Q10 Q13 Hi.
apply (HCL 0%nat v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest);
  [exact CTX2 | exact SH2 | exact Q27 | exact Q23 | exact Q16 | exact Q12 | exact Q10 | exact Q13 | exact Hi
  | intros k Hk; lia].
Qed.
Lemma fe_to_st0 : forall regs2 mem2 md2,
  fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest ->
  getr regs2 27 = w64 (p + Z.of_nat 0) ->
  getr regs2 23 = w64 (p + Z.of_nat 0) ->
  (length (mf_line rest) = 0)%nat ->
  mf_at B v Wc regs2 mem2 md2 FR_ST.
Proof.
intros regs2 mem2 md2 CTX2 SH2 Q27 Q23 HL0.
apply (HST v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest 0%nat 0%nat);
  [exact CTX2 | exact SH2 | exact Q27 | exact Q23 | lia |].
assert (HE : mf_line rest = []) by (apply length_zero_iff_nil; exact HL0).
unfold fr_cut. rewrite HE. reflexivity.
Qed.

Ltac fe_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (fr_awr; fail); fr_meq end.
Ltac fe_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (fr_awr; fail); fr_meq end.
Ltac fe_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
(* a stop: the head's facts by fr_ctx_run, the kept registers by HK, K proves what the point adds *)
Ltac fe_leaf H K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 []) Ecur) by (env_agree_chain fe_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (FR_KEPT ++ [19; 23; 27]%bv) HS HAE2
      ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    pmkst HS;
    eapply H;
    [ eapply fr_ctx_run; [exact CTX | exact HJ | exact MEQ
      | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
      | rewrite (HK 19%bv ltac:(cbv; tauto)); exact fe_R19]
    | .. ]; K HS HK
  end.
(* a7 = the next line's address, on the two arms of `beqz s4` *)
Ltac fe_a7_eq HS :=
  let R := fresh "R" in fe_preg HS (17%bv : bv 5) R;
  rewrite R, (denot_lit_U fe_E), fe_U23; unfold w64; f_equal;
  symmetry; apply fe_next_of_nl0; assumption.
Ltac fe_a7_ne HS :=
  let R := fresh "R" in fe_preg HS (17%bv : bv 5) R;
  rewrite R, (denot_lit_U fe_E), fe_U20o; unfold w64; f_equal;
  symmetry; apply fe_next_of_nlS; assumption.
(* s6 = line + 1 *)
Ltac fe_s6 HS :=
  let R := fresh "R" in fe_preg HS (22%bv : bv 5) R;
  rewrite R, (denot_lit_U fe_E), fe_U22w; reflexivity.
(* everything after `mv a7,..`: the long-line test, then the two empty tests *)
Ltac fe_rest KA7 :=
  fe_run; fe_branch;
  [ lazymatch goal with H : branch_taken BC_GE _ _ = true |- _ =>
      let HL := fresh "HLT" in pose proof (fe_brge true H) as HL; symmetry in HL;
      apply Bool.negb_true_iff, Z.ltb_ge in HL end;
    fe_run; fe_branch;
    [ lazymatch goal with H : branch_taken BC_GEU _ _ = true |- _ =>
        let HZ := fresh "HZ" in pose proof (fe_brgeu true H) as HZ; symmetry in HZ;
        apply Bool.negb_true_iff, Z.ltb_ge in HZ end;
      fe_runto FR_ST;
      fe_leaf fe_to_st0 ltac:(fun HS HK =>
        first
        [ split; [fe_s6 HS | split; [KA7 HS | lia]]
        | rewrite (HK 27%bv ltac:(cbv; tauto)), R27; f_equal; lia
        | rewrite (HK 23%bv ltac:(cbv; tauto)), R23; f_equal; lia
        | lia ])
    | lazymatch goal with H : branch_taken BC_GEU _ _ = false |- _ =>
        let HZ := fresh "HZ" in pose proof (fe_brgeu false H) as HZ; symmetry in HZ;
        apply Bool.negb_false_iff, Z.ltb_lt in HZ end;
      fe_runto FR_CL;
      fe_leaf fe_to_cl0 ltac:(fun HS HK =>
        first
        [ split; [fe_s6 HS | split; [KA7 HS | lia]]
        | rewrite (HK 27%bv ltac:(cbv; tauto)), R27; reflexivity
        | rewrite (HK 23%bv ltac:(cbv; tauto)), R23; reflexivity
        | let R := fresh "R" in fe_preg HS (16%bv : bv 5) R;
          rewrite R, (denot_lit_U fe_E), (U_lit fe_E 59) by lia; reflexivity
        | let R := fresh "R" in fe_preg HS (12%bv : bv 5) R;
          rewrite R, (denot_lit_U fe_E), fe_U27; unfold w64; f_equal; lia
        | let R := fresh "R" in fe_preg HS (10%bv : bv 5) R;
          rewrite R, (denot_lit_U fe_E), fe_U27; unfold w64; f_equal; lia
        | let R := fresh "R" in fe_preg HS (13%bv : bv 5) R;
          rewrite R, (denot_lit_U fe_E), (U_lit fe_E 0) by lia; unfold w64; f_equal; lia
        | lia ]) ]
  | lazymatch goal with H : branch_taken BC_GE _ _ = false |- _ =>
      let HG := fresh "HGE" in pose proof (fe_brge false H) as HG; symmetry in HG;
      apply Bool.negb_false_iff, Z.ltb_lt in HG end;
    fe_runto MF_LONG;
    fe_leaf fe_to_long ltac:(fun HS HK =>
      first
      [ rewrite (HK 27%bv ltac:(cbv; tauto)), R27; reflexivity
      | rewrite (HK 23%bv ltac:(cbv; tauto)), R23; reflexivity
      | KA7 HS
      | fe_s6 HS
      | lia ]) ].

Lemma fe_step : mf_at B v Wc regs1 memc mdc FR_E.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof fe_seed as HS.
assert (HEI : img_env VAL A_LIM fe_E) by (unfold fe_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] fe_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
unfold mf_at.
fe_run; fe_branch.
- pose proof (fe_breq true Hc) as HN0. symmetry in HN0. apply Z.eqb_eq in HN0.
  fe_rest fe_a7_eq.
- pose proof (fe_breq false Hc) as HN0. symmetry in HN0. apply Z.eqb_neq in HN0.
  fe_rest fe_a7_ne.
Qed.
End pe.

Lemma fr_e : forall n, MF_LONG_stmt B n -> (forall i, FR_CL_stmt B n i) -> FR_ST_stmt B n -> FR_E_stmt B n.
Proof.
intros n HLONG HCL HST v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX R27 R22 R23 R20.
exact (fe_step n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest HLONG HCL HST CTX R27 R22 R23 R20).
Qed.

(* ======================================== piece st ======================================== *)
Section pst.
Variables (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z) (i0 j0 : nat).
Hypothesis HTAIL : MF_TAIL_stmt B n.
Hypothesis HHDR : MF_HDR_stmt B n.
Hypothesis HKEY : MF_KEY_stmt B n.
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis SH : fr_short regs1 line p rest.
Hypothesis R27 : getr regs1 27 = w64 (p + Z.of_nat i0).
Hypothesis R23 : getr regs1 23 = w64 (p + Z.of_nat j0).
Hypothesis Hij : (i0 <= j0 <= length (mf_line rest))%nat.
Hypothesis HSL : slice i0 j0 (mf_line rest) = h_strip (fr_cut rest).

Lemma fs_tf : 4096 <= p /\ p + Z.of_nat (length rest) + 1 <= alloc_ceiling /\
  (length (mf_line rest) <= length rest)%nat /\
  0 <= p + Z.of_nat i0 < 2 ^ 64 /\ 0 <= p + Z.of_nat j0 < 2 ^ 64 /\
  p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\ rest <> [] /\
  alloc_ceiling <= 140737479966720.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & _ & _ & _).
pose proof (fr_line_len rest) as HLL. pose proof alloc_ceiling_value as [[_ HAC] _].
pose proof CTX as (_ & _ & _ & _ & _ & _ & _ & _ & Hne & _).
split; [exact H1|]. split; [exact H2|]. split; [exact HLL|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hne | lia].
Qed.
Lemma fs_s1 : (2 ^ 46 <= mf_s1 (mv_sp v) <= 2 ^ 47)%Z /\ mf_s1 (mv_sp v) mod 32 = 0 /\
  (mv_sp v - 304 <= mf_s1 (mv_sp v) <= mv_sp v - 288) /\
  alloc_ceiling + 8256 <= mf_s1 (mv_sp v) /\
  (forall a, mv_sp v - 8560 <= a < mv_sp v -> apresent (w_H Wc) memc a).
Proof.
pose proof CTX as (CX & _ & _ & CORE & _).
pose proof CORE as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (mf_s1_facts B v CX) as (HS1 & HS1m & HSceil).
destruct (mf_sp0 B v CX) as (_ & Hsp47 & _).
pose proof alloc_ceiling_value as [[HAClo HAChi] _].
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in Hpres, HSceil.
split; [lia|]. split; [exact HS1m|]. split; [lia|]. split; [lia | exact Hpres].
Qed.

(* the exits of the piece *)
Lemma fs_to_tail : forall regs2 mem2 md2,
  fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest ->
  getr regs2 17 = w64 (mf_next p rest) ->
  h_strip (fr_cut rest) = [] ->
  mf_at B v Wc regs2 mem2 md2 MF_TAIL.
Proof.
intros regs2 mem2 md2 CTX2 SH2 Q17 HE.
destruct CTX2 as (CX & LS & FRM & CORE & CELLS & RA & Q24 & Hn & Hne & LOOP & EQ & Q21).
destruct SH2 as (Q22 & _ & HL512).
pose proof LOOP as (_ & _ & _ & _ & _ & Hcur & _).
pose proof (fr_mf_rest_lt rest Hne) as HR.
apply (HTAIL v lyc Sc Wc regs2 mem2 md2 pos mcc cur (line + 1) (mf_next p rest) (mf_rest rest));
  [exact CX | exact LS | exact FRM | exact CORE | exact CELLS | exact RA | exact Q24 | lia | | | exact Q17
  | exact Q21 | exact Q22].
- eapply mf_loop_next; [exact LOOP | exact Hne | lia | lia | lia | exact Hcur].
- exact (fr_eq_empty mcc cur line rest (mf_final v) Hne EQ HL512 HE).
Qed.
Lemma fs_to_hdr : forall regs2 mem2 md2,
  fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest ->
  mf_np v mem2 Wc (mf_next p rest) ->
  getr regs2 27 = w64 (p + Z.of_nat i0) -> getr regs2 23 = w64 (p + Z.of_nat j0) ->
  getr regs2 12 = w64 (Z.of_nat (j0 - i0)) ->
  (i0 < j0)%nat -> nth i0 (mf_line rest) 0 = LBR ->
  mf_at B v Wc regs2 mem2 md2 MF_HDR.
Proof.
intros regs2 mem2 md2 CTX2 SH2 NP Q27 Q23 Q12 Hlt HB.
destruct CTX2 as (CX & LS & FRM & CORE & CELLS & RA & Q24 & Hn & Hne & LOOP & EQ & Q21).
destruct SH2 as (Q22 & Q17 & HL512).
assert (HD : hd0 (h_strip (h_cut_comment (mf_line rest))) = LBR).
{ change (h_cut_comment (mf_line rest)) with (fr_cut rest). rewrite <- HSL.
  rewrite (fe_hd0_slice (mf_line rest) i0 j0 ltac:(lia)). exact HB. }
apply (HHDR v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest i0 j0);
  [exact CX | exact LS | exact FRM | exact CORE | exact CELLS | exact RA | exact Q24 | exact Hn | exact Hne
  | exact LOOP | exact HL512 | exact Hlt | lia | exact HSL | exact HB
  | exact (fr_eq_hdr mcc cur line rest (mf_final v) Hne EQ HL512 HD)
  | exact Q27 | exact Q23 | exact Q12 | exact Q17 | exact NP | exact Q22 | exact Q21].
Qed.
Lemma fs_to_key : forall regs2 mem2 md2,
  fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest ->
  mf_np v mem2 Wc (mf_next p rest) ->
  getr regs2 27 = w64 (p + Z.of_nat i0) -> getr regs2 23 = w64 (p + Z.of_nat j0) ->
  getr regs2 12 = w64 (Z.of_nat (j0 - i0)) ->
  (i0 < j0)%nat -> nth i0 (mf_line rest) 0 <> LBR ->
  mf_at B v Wc regs2 mem2 md2 MF_KEY.
Proof.
intros regs2 mem2 md2 CTX2 SH2 NP Q27 Q23 Q12 Hlt HB.
destruct CTX2 as (CX & LS & FRM & CORE & CELLS & RA & Q24 & Hn & Hne & LOOP & EQ & Q21).
destruct SH2 as (Q22 & Q17 & HL512).
assert (HD : hd0 (h_strip (h_cut_comment (mf_line rest))) = nth i0 (mf_line rest) 0).
{ change (h_cut_comment (mf_line rest)) with (fr_cut rest). rewrite <- HSL.
  apply (fe_hd0_slice (mf_line rest) i0 j0). lia. }
assert (HNE : h_strip (h_cut_comment (mf_line rest)) <> []).
{ change (h_cut_comment (mf_line rest)) with (fr_cut rest). rewrite <- HSL.
  intros Hx. pose proof (fr_slice_length (mf_line rest) i0 j0 ltac:(lia)) as HLn.
  rewrite Hx in HLn. cbn [length] in HLn. lia. }
apply (HKEY v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest i0 j0);
  [exact CX | exact LS | exact FRM | exact CORE | exact CELLS | exact RA | exact Q24 | exact Hn | exact Hne
  | exact LOOP | exact HL512 | exact Hlt | lia | exact HSL | exact HB
  | exact (fr_eq_key mcc cur line rest (mf_final v) Hne EQ HL512 HNE ltac:(rewrite HD; exact HB))
  | exact Q27 | exact Q23 | exact Q12 | exact Q17 | exact NP | exact Q22 | exact Q21].
Qed.

(* --- the stripped line is empty: straight to the next line --- *)
Section pst0.
Hypothesis Heq : i0 = j0.
Definition fs0_E : env := Eimg (Ereg regs1 []).

Lemma fs0_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew fs0_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold fs0_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma fs0_HAE : env_agree 32 (Ereg regs1 []) fs0_E.
Proof. unfold fs0_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma fs0_R19 : getr regs1 19 = w64 0x20.
Proof.
pose proof CTX as (_ & _ & _ & _ & _ & RA & _). destruct RA as (_ & _ & _ & _ & _ & _ & R19 & _). exact R19.
Qed.
Lemma fs0_U27 : U fs0_E (SOff 27 0) = p + Z.of_nat i0.
Proof.
pose proof fs_tf as (_ & _ & _ & T4 & _).
apply U_atom; [rewrite (fs0_EN 27%nat 27%bv eq_refl) by lia; exact R27 | lia].
Qed.
Lemma fs0_U23 : U fs0_E (SOff 23 0) = p + Z.of_nat j0.
Proof.
pose proof fs_tf as (_ & _ & _ & _ & T5 & _).
apply U_atom; [rewrite (fs0_EN 23%nat 23%bv eq_refl) by lia; exact R23 | lia].
Qed.
Lemma fs0_breq : forall b,
  branch_taken BC_EQ (sv_denot fs0_E (SOff 27 0)) (sv_denot fs0_E (SOff 23 0)) = b ->
  b = (p + Z.of_nat i0 =? p + Z.of_nat j0).
Proof. intros b H. rewrite <- H, branch_eq_U, fs0_U27, fs0_U23. reflexivity. Qed.
Lemma fs0_seed : st_ok_pi SEGS VAL fs0_E ss_fs0
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_ST)) memc (seg_rom SEGS))).
Proof.
rewrite restrict_mkst_fx. unfold ss_fs0. apply pa_entry_st_ok_full.
- unfold fs0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [cbn; first [exact I | constructor] | split; [exact I | exact I]].
Qed.

Lemma fs_step0 : mf_at B v Wc regs1 memc mdc FR_ST.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof fs0_seed as HS.
assert (HEI : img_env VAL A_LIM fs0_E) by (unfold fs0_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] fs0_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
assert (HEMPTY : h_strip (fr_cut rest) = []).
{ rewrite <- HSL. unfold slice. rewrite Heq, Nat.sub_diag. reflexivity. }
unfold mf_at.
lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
- (* taken: the next line *)
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_TAIL; try (fr_awr; fail); fr_meq end.
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- _ =>
    assert (HAE2 : env_agree 32 (Ereg regs1 []) Ecur) by (env_agree_chain fs0_HAE);
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (FR_KEPT ++ [17; 19; 22; 23; 27]%bv) HS HAE2
      ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    pmkst HS;
    pose proof SH as (Q22 & Q17 & HL512);
    eapply fs_to_tail;
    [ eapply fr_ctx_run; [exact CTX | exact HJ | exact MEQ
      | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
      | rewrite (HK 19%bv ltac:(cbv; tauto)); exact fs0_R19]
    | split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact Q22
      | split; [rewrite (HK 17%bv ltac:(cbv; tauto)); exact Q17 | exact HL512]]
    | rewrite (HK 17%bv ltac:(cbv; tauto)); exact Q17
    | exact HEMPTY ] end.
- (* not taken: impossible, the two cursors are equal *)
  exfalso. pose proof (fs0_breq false Hc) as HB. symmetry in HB.
  apply Z.eqb_neq in HB. apply HB. rewrite Heq. reflexivity.
Qed.
End pst0.

(* --- the stripped line is not empty: the '[' test --- *)
Section pst1.
Hypothesis Hlt : (i0 < j0)%nat.
Definition fs_b : Z := nth i0 (mf_line rest) 0.
Definition fs_E : env := Eimg (Ereg regs1 [Z_to_bv 64 fs_b]).
Definition fs_RW (a : Z) : Prop := mf_s1 (mv_sp v) + 144 <= a < mf_s1 (mv_sp v) + 152.

Lemma fs_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew fs_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold fs_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma fs_HAE : env_agree 32 (Ereg regs1 [Z_to_bv 64 fs_b]) fs_E.
Proof. unfold fs_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma fs_E32 : ew fs_E 32 = Z_to_bv 64 fs_b.
Proof. unfold fs_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma fs_byte : rdW Wc memc (p + Z.of_nat i0) = Some fs_b /\ 0 <= fs_b < 256.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & BY & BR8 & _).
split; [apply BY; lia | apply BR8; lia].
Qed.
Lemma fs_rad : forall x, p <= x < p + Z.of_nat (length rest) + 1 ->
  range_addressable (rdW Wc memc) SHADOW_OFF x 1.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & _ & RAD).
intros x Hx y Hy. apply RAD. lia.
Qed.
Lemma fs_U9x : bv_unsigned (ew fs_E 9) = mf_s1 (mv_sp v).
Proof.
pose proof fs_s1 as (HS1 & _ & _ & _).
pose proof CTX as (_ & _ & _ & _ & _ & RA & _). pose proof RA as (_ & _ & _ & _ & R9 & _).
rewrite (fs_EN 9%nat 9%bv eq_refl) by lia. rewrite R9. unfold w64. apply unsigned_lit_small. lia.
Qed.
Lemma fs_UX : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew fs_E k) ->
  U Ex (SOff 27 0) = p + Z.of_nat i0 /\ U Ex (SOff 18 0) = SHADOW_OFF /\
  U Ex (SOff 23 0) = p + Z.of_nat j0 /\ U Ex (SOff 32 0) = fs_b /\ U Ex (SOff 9 0) = mf_s1 (mv_sp v).
Proof.
intros Ex HEx.
pose proof fs_tf as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
pose proof fs_byte as (BY & HB).
pose proof fs_s1 as (HS1 & _ & _ & _).
pose proof CTX as (_ & _ & _ & _ & _ & RA & _). pose proof RA as (_ & _ & _ & _ & R9 & R18 & _).
split; [apply U_atom; [rewrite HEx, (fs_EN 27%nat 27%bv eq_refl) by lia; exact R27 | lia]|].
split; [apply U_atom; [rewrite HEx, (fs_EN 18%nat 18%bv eq_refl) by lia; exact R18 | unfold SHADOW_OFF; lia]|].
split; [apply U_atom; [rewrite HEx, (fs_EN 23%nat 23%bv eq_refl) by lia; exact R23 | lia]|].
split; [apply U_atom; [rewrite HEx by lia; exact fs_E32 | lia]|].
apply U_atom; [rewrite HEx, (fs_EN 9%nat 9%bv eq_refl) by lia; exact R9 | lia].
Qed.

Lemma fs_seed1 : st_ok_pi SEGS VAL fs_E ss_fs1
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_ST)) memc (seg_rom SEGS))).
Proof.
pose proof fs_tf as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
pose proof fs_byte as (BY & HB).
pose proof fs_s1 as (HS1 & HS1m & HS1d & HSc & Hpres).
pose proof CTX as (_ & _ & _ & _ & _ & RA & _). pose proof RA as (_ & _ & _ & _ & R9 & R18 & _).
rewrite restrict_mkst_fx. unfold ss_fs1. apply pa_entry_st_ok_full.
- unfold fs_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok, fs_text.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (fs_EN 27%nat 27%bv eq_refl), R27 by lia. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS fs_E _ (p + Z.of_nat i0) 0 1 (SOff 32 0) fs_b);
      [cbn [sv_denot]; rewrite fs_E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (fr_val_mem1 _ _ _ _ BY).
  + unfold region_ok, fs_slot.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (fs_EN 9%nat 9%bv eq_refl), R9 by lia. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, fs_text, fs_slot.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (fs_EN 27%nat 27%bv eq_refl), (fs_EN 9%nat 9%bv eq_refl), R27, R9 by lia.
  unfold w64. rewrite !unsigned_lit_small by lia.
  repeat match goal with |- _ /\ _ => split end.
  all: first [exact I | left; lia].
- split; [|split; [exact I | exact I]].
  cbn [fs_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite (fs_EN 9%nat 9%bv eq_refl), (fs_EN 18%nat 18%bv eq_refl), (fs_EN 27%nat 27%bv eq_refl) by lia.
  rewrite R9, R18, R27, fs_E32.
  unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end.
  all: first [exact I | reflexivity | exact HS1m | lia].
Qed.
Lemma fs_ew9 : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew fs_E k) ->
  bv_unsigned (ew Ex 9) = mf_s1 (mv_sp v).
Proof. intros Ex HEx. rewrite HEx by lia. exact fs_U9x. Qed.
(* the write goal: the text byte is read-only, 144(s1) is a slot of the callee window below sp0 *)
Ltac fs_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat (mf_s1 (mv_sp v) - mv_sp v));
  [ reflexivity
  | lazymatch goal with |- bv_unsigned (ew ?Ey 9) = _ =>
      rewrite (fs_ew9 Ey ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)) end; ring
  | cbn [YP09.r_wlo]; pose proof fs_s1 as (_ & _ & ?HD & _);
    assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity; lia
  | cbn [YP09.r_whi]; pose proof fs_s1 as (_ & _ & ?HD & _); lia
  | apply awr_ok_nil ].
(* the check obligation of the byte at s11 *)
Ltac fs_obl :=
  lazymatch goal with
  | MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- range_addressable _ (U ?Ex (SOff 18 0)) (U ?Ex ?x) _ =>
    let UXO := fresh "UXO" in
    pose proof (fs_UX Ex ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)) as UXO;
    let A1 := fresh "a" in let A2 := fresh "a" in let A3 := fresh "a" in
    let A4 := fresh "a" in let A5 := fresh "a" in
    destruct UXO as (A1 & A2 & A3 & A4 & A5);
    rewrite <- (aview_rd_of SEGS);
    apply (fr_ra_eq (aview SEGS (w_H Wc) memc)); [intros; first [apply MEQ | reflexivity] |];
    rewrite ?A2, ?A1; apply fs_rad; pose proof fs_tf as (?T1 & ?T2 & ?T3 & _); lia
  end.
Ltac fs_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.

Lemma fs_nextr : 0 <= mf_next p rest < 2 ^ 64.
Proof.
pose proof CTX as (CX & _ & _ & CORE & _ & _ & _ & _ & _ & LOOP & _).
exact (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP).
Qed.
Lemma fs_U17 : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew fs_E k) ->
  U Ex (SOff 17 0) = mf_next p rest.
Proof.
intros Ex HEx. pose proof fs_nextr as HR. pose proof SH as (_ & Q17 & _).
apply U_atom; [rewrite HEx, (fs_EN 17%nat 17%bv eq_refl) by lia; exact Q17 | lia].
Qed.
Lemma fs_U12 : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew fs_E k) ->
  U Ex (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 27 0) (SLit (-1)))) = Z.of_nat (j0 - i0).
Proof.
intros Ex HEx. pose proof fs_tf as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
destruct (fs_UX Ex HEx) as (A1 & _ & A3 & _ & _).
rewrite fe_U_sub, A3, A1.
replace (p + Z.of_nat j0 - (p + Z.of_nat i0)) with (Z.of_nat j0 - Z.of_nat i0) by ring.
rewrite <- Nat2Z.inj_sub by lia. apply Z.mod_small. lia.
Qed.
Lemma fs_R19 : getr regs1 19 = w64 0x20.
Proof.
pose proof CTX as (_ & _ & _ & _ & _ & RA & _). destruct RA as (_ & _ & _ & _ & _ & _ & R19 & _). exact R19.
Qed.
Lemma fs_breq : forall b,
  branch_taken BC_EQ (sv_denot fs_E (SOff 27 0)) (sv_denot fs_E (SOff 23 0)) = b ->
  b = (p + Z.of_nat i0 =? p + Z.of_nat j0).
Proof.
intros b H. rewrite <- H, branch_eq_U.
destruct (fs_UX fs_E ltac:(intros k Hk; reflexivity)) as (A1 & _ & A3 & _ & _).
rewrite A1, A3. reflexivity.
Qed.
Lemma fs_brne : forall Ex b, (forall k, (k < 1024)%nat -> ew Ex k = ew fs_E k) ->
  branch_taken BC_NE (sv_denot Ex (SOff 32 0)) (sv_denot Ex (SLit 91)) = b ->
  b = negb (fs_b =? 91).
Proof.
intros Ex b HEx H. rewrite <- H, branch_ne_U.
destruct (fs_UX Ex HEx) as (_ & _ & _ & A4 & _).
rewrite A4, (U_lit Ex 91) by lia. reflexivity.
Qed.

(* the head's facts across the piece's run: it writes only the 8 bytes of 144(s1) *)
Lemma fs_carry : forall regs2 mem2 md2,
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
    (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ fs_RW a -> rdW Wc mem2 a = rdW Wc memc a) ->
  (forall r, In r FR_KEPT -> getr regs2 r = getr regs1 r) -> getr regs2 19 = w64 0x20 ->
  fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n.
Proof.
intros regs2 mem2 md2 HJ2 KRW KEEP R19'.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & RA & R24 & Hn & Hne & LOOP & EQ & R21).
pose proof RA as (_ & _ & _ & _ & _ & _ & R19 & _).
pose proof fs_s1 as (HS1 & HS1m & HS1d & HSc & _).
pose proof fs_tf as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
pose proof CORE as (HJ0 & HPerm & VFL & VSH & VSV & V112 & HMC & HADDR & HTL).
pose proof HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & _).
pose proof CELLS as (C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C104 & C120 & C128 & C136 & C152).
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
unfold seg_spec.SEG_M_SIZE in Hbc2, Bk2.
assert (RWok : forall a, fs_RW a -> mf_rw v lyc pos a)
  by (intros a Ha; unfold fs_RW in Ha; unfold mf_rw; lia).
assert (RWS : mf_rws v fs_RW) by (intros a Ha _; unfold fs_RW in Ha; lia).
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) mem2) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
{ intros i Hi. apply (mf_val_keep Wc Wc memc mem2 fs_RW _ 1 _ KRW);
  [ unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia
  | intros k Hk Hx; unfold fs_RW in Hx; unfold SHADOW_OFF in Hx; lia | exact (VSH i Hi) ]. }
assert (V136' : val_mem SEGS (mrestrict (w_H Wc) mem2) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur)).
{ apply (mf_val_keep Wc Wc memc mem2 fs_RW _ 8 _ KRW);
  [ lia | change (Z.of_nat 8) with 8; lia | intros k Hk Hx; unfold fs_RW in Hx; lia | exact C136 ]. }
assert (MC' : sa_mconf (rdW Wc mem2) (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc mem2 fs_RW _ _ KRW);
  [ lia | unfold seg_spec.SEG_M_SIZE; lia
  | intros a Ha Hx; unfold fs_RW in Hx; unfold seg_spec.SEG_M_SIZE in Ha; lia | exact HMC ]. }
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur mem2 md2 fs_RW MF_LOW_OFF cur mcc
  CX CORE CELLS HJ2 KRW RWok RWS VSH' V136' MC') as (C1 & C2 & C3).
refine (conj CX (conj LS (conj FRM (conj C1 (conj C2 (conj _ (conj _ (conj Hn (conj Hne
  (conj (C3 _ _ _ _ _ LOOP) (conj EQ _))))))))))).
- apply (mf_regs_at_of B v lyc pos regs1 regs2 RA); try (apply KEEP; cbv; tauto).
  rewrite R19', R19. reflexivity.
- rewrite (KEEP 24%bv ltac:(cbv; tauto)). exact R24.
- rewrite (KEEP 21%bv ltac:(cbv; tauto)). exact R21.
Qed.

(* the run keeps every byte outside 144(s1) *)
Ltac fs_keep :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1),
    KR : forall a, 0 <= a < 2 ^ 64 -> ~ fs_RW a -> aview _ _ ?m0 a = aview _ _ memc a |- _ =>
    let K2 := fresh "KRW" in
    let aa := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ fs_RW a -> aview SEGS Hh m1 a = aview SEGS Hh memc a);
    [ intros aa Ha Hn;
      transitivity (aview SEGS Hh m0 aa);
      [ refine (kept_of_frame Ex rs Hh m0 m1 fs_RW HFr _ aa Ha Hn);
        let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in
        let xx := fresh "xx" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
        intros bb wl wh xx Hin Hr;
        let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin;
        cbn [In] in Hin;
        repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
          [ injection Hq as <- <- <-; cbn [base_val] in Hr;
            first [ exfalso; lia
                  | unfold fs_RW;
                    rewrite (fs_ew9 Ex ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity))
                      in Hr; exact Hr ] | ]);
        destruct Hin
      | apply KR; assumption ]
    | clear KR HFr; rename K2 into KRW ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac fs_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ2 SHOK Bspan; try (fs_awr; fail); try (fs_obl; fail); fs_keep end.
Ltac fs_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan stop; try (fs_awr; fail); try (fs_obl; fail); fs_keep end.
(* a stop at MF_HDR or MF_KEY: the head's facts, 144(s1), the kept registers; K proves what the cut adds *)
Ltac fs_leaf H K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    KR : forall a, 0 <= a < 2 ^ 64 -> ~ fs_RW a -> aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 [Z_to_bv 64 fs_b]) Ecur) by (env_agree_chain fs_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (FR_KEPT ++ [17; 19; 22; 23; 27]%bv) HS HAE2
      ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    let HAG := fresh "HAG" in
    assert (HAG : forall k, (k < 1024)%nat -> ew Ecur k = ew fs_E k)
      by (intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity);
    let HNP := fresh "HNP" in
    assert (HNP : mf_np v (ms_mem ms) Wc (mf_next p rest));
    [ unfold mf_np;
      let HR := fresh "HR" in
      pose proof (st_ok_pi_region_nth Ecur _ (restrict (w_H Wc) ms) 1%nat _ HS eq_refl) as HR;
      cbn [restrict ms_mem] in HR;
      eapply (field_of_region Ecur _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 144 8%N _ (mf_next p rest) HR);
      [ exact (fs_ew9 Ecur HAG)
      | cbn; left; reflexivity
      | rewrite denot_lit_U, (fs_U17 Ecur HAG); reflexivity
      | cbn; pose proof fs_nextr; lia
      | cbn; lia ]
    | ];
    pmkst HS;
    let Q22 := fresh "Q22" in let Q17 := fresh "Q17" in let HL512 := fresh "HL512" in
    pose proof SH as (Q22 & Q17 & HL512);
    eapply H;
    [ eapply fs_carry; [exact HJ2 | exact KR
      | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
      | rewrite (HK 19%bv ltac:(cbv; tauto)); exact fs_R19]
    | split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact Q22
      | split; [rewrite (HK 17%bv ltac:(cbv; tauto)); exact Q17 | exact HL512]]
    | exact HNP
    | rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27
    | rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23
    | .. ]; K HS HK HAG
  end.

Lemma fs_step1 : mf_at B v Wc regs1 memc mdc FR_ST.
Proof.
pose proof CTX as (_ & _ & _ & (HJ2 & _) & _).
pose proof fs_seed1 as HS.
assert (HEI : img_env VAL A_LIM fs_E) by (unfold fs_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] fs_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
assert (KRW : forall a, 0 <= a < 2 ^ 64 -> ~ fs_RW a -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a)
  by (intros a _ _; reflexivity).
assert (HLBR : LBR = 91) by reflexivity.
unfold mf_at.
fs_branch.
- exfalso. pose proof (fs_breq true Hc) as HB. symmetry in HB. apply Z.eqb_eq in HB. lia.
- fs_run. fs_branch.
  + lazymatch goal with Hx : branch_taken BC_NE (sv_denot ?Ex _) _ = true |- _ =>
      pose proof (fs_brne Ex true
        ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity) Hx) as HB end;
    symmetry in HB; apply Bool.negb_true_iff, Z.eqb_neq in HB;
    fs_runto MF_KEY;
    fs_leaf fs_to_key ltac:(fun HS HK HAG =>
      first
      [ exact Hlt
      | let R := fresh "R" in fe_preg HS (12%bv : bv 5) R; rewrite R;
        lazymatch goal with |- sv_denot ?Ex _ = _ => rewrite (denot_lit_U Ex), (fs_U12 Ex HAG) end;
        reflexivity
      | unfold fs_b in HB; first [exact HB | rewrite HLBR; exact HB] ]).
  + lazymatch goal with Hx : branch_taken BC_NE (sv_denot ?Ex _) _ = false |- _ =>
      pose proof (fs_brne Ex false
        ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity) Hx) as HB end;
    symmetry in HB; apply Bool.negb_false_iff, Z.eqb_eq in HB;
    fs_runto MF_HDR;
    fs_leaf fs_to_hdr ltac:(fun HS HK HAG =>
      first
      [ exact Hlt
      | let R := fresh "R" in fe_preg HS (12%bv : bv 5) R; rewrite R;
        lazymatch goal with |- sv_denot ?Ex _ = _ => rewrite (denot_lit_U Ex), (fs_U12 Ex HAG) end;
        reflexivity
      | unfold fs_b in HB; first [exact HB | rewrite HLBR; exact HB] ]).
Qed.
End pst1.

Lemma fs_step : mf_at B v Wc regs1 memc mdc FR_ST.
Proof.
destruct (Nat.eq_dec i0 j0) as [E|NE]; [exact (fs_step0 E) | exact (fs_step1 ltac:(lia))].
Qed.
End pst.

Lemma fr_st : forall n, MF_TAIL_stmt B n -> MF_HDR_stmt B n -> MF_KEY_stmt B n -> FR_ST_stmt B n.
Proof.
intros n HTAIL HHDR HKEY v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i0 j0 CTX SH R27 R23 Hij HSL.
exact (fs_step n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i0 j0 HTAIL HHDR HKEY CTX SH R27 R23 Hij HSL).
Qed.
End e.
End f.
End d.

(* the two pieces rest on no axiom of their own: B is the walk's symbol record, and fx / rc / SK / PI the
   file's Context *)
Print Assumptions fr_e.
Print Assumptions fr_st.
