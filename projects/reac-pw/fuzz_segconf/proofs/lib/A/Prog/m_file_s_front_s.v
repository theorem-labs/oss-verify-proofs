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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 765 of its 824 lines of code are new or changed and 394 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_FRONT, pieces cx / sf / sm / sb: the strip of the line's
   comment cut cut = h_cut_comment (mf_line rest), C = |cut| (MF-CUTS-A.md section 4: 0x861fc-0x862a0).
   cx  0x861fc-0x86204: s7 = a2 = p + C; C = 0 goes to 0x8624c (FR_SM, i0 = 0), else a0 = s11 = p, to 0x86208.
   sf  0x86208-0x86248, at k < C: the instrumented check of a0 = p + k (a load of the shadow byte at (a0 >> 3) + the
       shadow base and a compare; its error path, the call at 0x86f80, is not reached because the text is
       addressable), the byte cut[k] (`lbu a1,0(s11)`), not blank (> ' ', or its bit of the mask s9 = 0x100002200 is
       0) to 0x8624c with i0 = k, else k + 1, or at k + 1 = C `mv s11,s7` and 0x8624c with i0 = C.
   sm  0x8624c-0x86258: i0 = C goes to 0x862a4 (FR_ST, the stripped line is empty), else a1 = s11, a0 = s7 - 1, to the
       backward strip at j = C.
   sb  0x8625c-0x862a0, at j with i0 < j: the check of a0 = p + j - 1 (error path 0x86f84 not reached), the byte
       cut[j - 1] (`lbu a3,0(a2)`, a2 = s7 - 1), not blank to 0x862a4 with j0 = j, else s7 = p + j - 1 and the pass
       at j - 1 while i0 < j - 1; j - 1 = i0 cannot be blank (cut[i0] is not), so 0x862a0 is not reached.
   Each pass runs over a state of the registers and the one text byte it reads, as m_file_s_front_cl.v; no pass
   stores, so the head's facts are carried by fr_ctx_run. The FRONT segment lane of the G2 walk owner's G2 (its strip sub-lane). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_front_mdl m_file_s_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_front_g.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the cut is no longer than the line *)
Lemma fs_C_le : forall rest, (fr_C rest <= length (mf_line rest))%nat.
Proof. intros rest. unfold fr_C, fr_cut. exact (proj1 (fr_cut_len (mf_line rest))). Qed.
(* the stripped line as the strip's two indices give it *)
Lemma fs_strip_slice : forall rest i j, (i <= j <= fr_C rest)%nat -> all_blank (fr_cut rest) 0 i ->
  (i = fr_C rest \/ blank (nth i (fr_cut rest) 0) = false) -> all_blank (fr_cut rest) j (fr_C rest) ->
  (j = i \/ blank (nth (j - 1) (fr_cut rest) 0) = false) ->
  slice i j (mf_line rest) = h_strip (fr_cut rest).
Proof.
intros rest i j Hij H0 Hs H1 He. unfold fr_C, fr_cut in *.
rewrite (fr_h_strip_idx _ i j) by assumption. symmetry. apply fr_cut_slice. lia.
Qed.
(* the blank test of a byte b <= ' ' (atom 32) by the mask s9 (atom 25): `srl; andi 1` *)
Lemma fs_mask_U : forall E b, U E (SOff 25 0) = MF_BLANK -> U E (SOff 32 0) = b -> 0 <= b <= 32 ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SOff 25 0) (SOff 32 0)) (SLit 1)) = if blank b then 1 else 0.
Proof.
intros E b H25 H32 Hb. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw]. rewrite H25, H32.
assert (Hn : exists m, b = Z.of_nat m /\ (m <= 32)%nat) by (exists (Z.to_nat b); split; lia).
destruct Hn as [m [-> Hm]]. clear H32 Hb.
do 33 (destruct m as [|m]; [vm_compute; reflexivity|]). lia.
Qed.
(* 0x86250-0x86254 `sub a1,s11,s7; add a1,s7,a1` as the executor leaves it: s7 * 2^64 + s11 *)
Lemma fs_mul0_add : forall E a b, sv_denot E (SAlu ALU_ADD (SMd M_MUL a (SLit 18446744073709551616)) b) = sv_denot E b.
Proof.
intros E a b. apply U_inj. rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw].
change (zcanon 18446744073709551616) with 0. rewrite Z.mul_0_r. change (zcanon 0) with 0. rewrite Z.add_0_l.
apply zcanon_id. exact (U_range E b).
Qed.
Ltac prreg_mul0 HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    rewrite fs_mul0_add in Hr; cbn [ms_regs restrict mkst] in Hr; prreg_norm Hr
  end.

(* the passes' states *)
Definition fs_facts0 : facts := mkFacts [] [] [].
(* sf: s11 (x27) is the cursor p + k, the byte cut[k] is atom 32 *)
Definition fs_sf_text : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition fs_sf_facts : facts :=
  mkFacts [(10%nat, PTR 0); (27%nat, PTR 0); (18%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)] [] [].
(* sb: s7 (x23) is p + j, the byte cut[j - 1] (at s7 - 1) is atom 32 *)
Definition fs_sb_text : YP09.region :=
  YP09.mkRegion (Some 23%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 32 0))].
Definition fs_sb_facts : facts :=
  mkFacts [(10%nat, PTR 0); (23%nat, PTR 0); (18%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)] [] [].

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

(* the write goal of a run: the passes' regions are read-only *)
Ltac fs_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* after a run: the reader is the pass's start reader (MEQ), byte for byte *)
Ltac fs_meq :=
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1),
    MEQ : forall a, aview _ _ ?m0 a = aview _ _ ?mc a |- _ =>
    let M := fresh "M" in
    pose proof (fr_aview_ro _ rs H m0 m1 HFr ltac:(vm_compute; reflexivity)) as M;
    let MEQ' := fresh "MEQ" in
    assert (MEQ' : forall a, aview SEGS H m1 a = aview SEGS H mc a) by (intros a; rewrite M; apply MEQ);
    clear M MEQ HFr; rename MEQ' into MEQ end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* ============================== cx: 0x861fc-0x86204 ============================== *)
Section cx.
Variables (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z).
Hypothesis HSF : forall k, FR_SF_stmt B n k.
Hypothesis HSM : FR_SM_stmt B n.
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis SH : fr_short regs1 line p rest.
Hypothesis R27 : getr regs1 27 = w64 p.
Hypothesis R12 : getr regs1 12 = w64 (p + Z.of_nat (fr_C rest)).

Definition cx_E : env := Eimg (Ereg regs1 []).

Lemma cx_tf : 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\
  (fr_C rest <= length (mf_line rest))%nat /\ (length (mf_line rest) < 512)%nat.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & _ & _ & _).
pose proof (fr_line_len rest) as HLL. pose proof (fs_C_le rest) as HC. pose proof SH as (_ & _ & HL512).
split; [exact H1|]. split; [lia|]. split; [exact HC | exact HL512].
Qed.
Lemma cx_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew cx_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold cx_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma cx_HAE : env_agree 32 (Ereg regs1 []) cx_E.
Proof. unfold cx_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma cx_UX : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew cx_E k) ->
  U Ex (SOff 27 0) = p /\ U Ex (SOff 12 0) = p + Z.of_nat (fr_C rest).
Proof.
intros Ex HEx. pose proof cx_tf as (T1 & T2 & T3 & T4). pose proof alloc_ceiling_value as [[_ HAC] _].
split; [apply U_atom; [rewrite HEx, (cx_EN 27%nat 27%bv eq_refl) by lia; exact R27 | lia]|].
apply U_atom; [rewrite HEx, (cx_EN 12%nat 12%bv eq_refl) by lia; exact R12 | lia].
Qed.
Lemma cx_seed : st_ok_pi SEGS VAL cx_E
  (mkSS FR_CX (sr_set sr_atoms (19%bv : bv 5) (SLit 32)) [] None fs_facts0)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_CX)) memc (seg_rom SEGS))).
Proof.
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & R19 & _) & _).
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL cx_E (mkSS FR_CX sr_atoms [] None fs_facts0)
  (mkst regs1 (Z_to_bv 64 (BASE + FR_CX)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  + unfold cx_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor.
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [exact I | split; [exact I | exact I]]. }
exact (st_ok_pi_pin_reg' cx_E _ _ (19%bv : bv 5) 32 HS0 R19 eq_refl).
Qed.
(* the piece's two exits *)
Lemma cx_SM : forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest -> getr regs2 27 = w64 p -> getr regs2 23 = w64 (p + Z.of_nat (fr_C rest)) ->
  fr_C rest = 0%nat -> mf_at B v Wc regs2 mem2 md2 FR_SM.
Proof.
intros regs2 mem2 md2 C2 S2 Q27 Q23 HC0.
apply (HSM v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest 0%nat C2 S2);
  [replace (p + Z.of_nat 0) with p by lia; exact Q27 | exact Q23 | lia | intros ?k ?Hk; lia | left; lia].
Qed.
Lemma cx_SF : forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest -> getr regs2 27 = w64 p -> getr regs2 10 = w64 p ->
  getr regs2 23 = w64 (p + Z.of_nat (fr_C rest)) -> (0 < fr_C rest)%nat -> mf_at B v Wc regs2 mem2 md2 FR_SF.
Proof.
intros regs2 mem2 md2 C2 S2 Q27 Q10 Q23 HC.
apply (HSF 0%nat v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest C2 S2);
  [replace (p + Z.of_nat 0) with p by lia; exact Q27 | replace (p + Z.of_nat 0) with p by lia; exact Q10
  | exact Q23 | exact HC | intros ?k ?Hk; lia].
Qed.

Ltac cx_ux UXN :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
    pose proof (cx_UX Ex ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)) as UXN end.
Ltac cx_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (fs_awr; fail); fs_meq end.
Ltac cx_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (fs_awr; fail); fs_meq end.
Ltac cx_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
Ltac cx_cond :=
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = _ |- _ =>
    let UXc := fresh "UXc" in cx_ux UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in
    destruct UXc as (a1 & a2);
    rewrite ?branch_eq_U, ?branch_ne_U, ?branch_geu_U, ?branch_ltu_U in Hc;
    rewrite ?a1, ?a2 in Hc; clear a1 a2
  end.
Ltac cx_leaf H K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 []) Ecur) by (env_agree_chain cx_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (FR_KEPT ++ [17; 22; 27]%bv) HS HAE2
      ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    let R19x := fresh "R19x" in prreg HS (19%bv : bv 5) R19x;
    pmkst HS;
    let R22 := fresh "R22" in let R17 := fresh "R17" in let HL512 := fresh "HL512" in
    pose proof SH as (R22 & R17 & HL512);
    eapply H;
    [ eapply fr_ctx_run; [exact CTX | exact HJ | exact MEQ | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
      | rewrite R19x; reflexivity]
    | split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact R22 |
       split; [rewrite (HK 17%bv ltac:(cbv; tauto)); exact R17 | exact HL512]]
    | .. ]; K HS HK
  end.

Lemma cx_step : mf_at B v Wc regs1 memc mdc FR_CX.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof cx_seed as HS.
assert (HEI : img_env VAL A_LIM cx_E) by (unfold cx_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] cx_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
unfold mf_at.
cx_run; cx_branch.
- cx_cond. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
  cx_runto FR_SM.
  cx_leaf cx_SM ltac:(fun HS HK => first
    [ rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27
    | let R := fresh in prreg HS (23%bv : bv 5) R; rewrite R, (cx_EN 12%nat 12%bv eq_refl), R12 by lia; reflexivity
    | lia ]).
- cx_cond. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
  cx_runto FR_SF.
  cx_leaf cx_SF ltac:(fun HS HK => first
    [ rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27
    | let R := fresh in prreg HS (10%bv : bv 5) R; rewrite R, (cx_EN 27%nat 27%bv eq_refl), R27 by lia; reflexivity
    | let R := fresh in prreg HS (23%bv : bv 5) R; rewrite R, (cx_EN 12%nat 12%bv eq_refl), R12 by lia; reflexivity
    | lia ]).
Qed.
End cx.

(* ============================== sm: 0x8624c-0x86258 ============================== *)
Section sm.
Variables (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z) (i0 : nat).
Hypothesis HSB : forall j, FR_SB_stmt B n j.
Hypothesis HST : FR_ST_stmt B n.
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis SH : fr_short regs1 line p rest.
Hypothesis R27 : getr regs1 27 = w64 (p + Z.of_nat i0).
Hypothesis R23 : getr regs1 23 = w64 (p + Z.of_nat (fr_C rest)).
Hypothesis Hi0 : (i0 <= fr_C rest)%nat.
Hypothesis Hab : all_blank (fr_cut rest) 0 i0.
Hypothesis Hst : i0 = fr_C rest \/ blank (nth i0 (fr_cut rest) 0) = false.

Definition sm_E : env := Eimg (Ereg regs1 []).

Lemma sm_tf : 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\
  (fr_C rest <= length (mf_line rest))%nat /\ (length (mf_line rest) < 512)%nat.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & _ & _ & _).
pose proof (fr_line_len rest) as HLL. pose proof (fs_C_le rest) as HC. pose proof SH as (_ & _ & HL512).
split; [exact H1|]. split; [lia|]. split; [exact HC | exact HL512].
Qed.
Lemma sm_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew sm_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold sm_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma sm_HAE : env_agree 32 (Ereg regs1 []) sm_E.
Proof. unfold sm_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma sm_UX : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew sm_E k) ->
  U Ex (SOff 27 0) = p + Z.of_nat i0 /\ U Ex (SOff 23 0) = p + Z.of_nat (fr_C rest).
Proof.
intros Ex HEx. pose proof sm_tf as (T1 & T2 & T3 & T4). pose proof alloc_ceiling_value as [[_ HAC] _].
split; [apply U_atom; [rewrite HEx, (sm_EN 27%nat 27%bv eq_refl) by lia; exact R27 | lia]|].
apply U_atom; [rewrite HEx, (sm_EN 23%nat 23%bv eq_refl) by lia; exact R23 | lia].
Qed.
Lemma sm_seed : st_ok_pi SEGS VAL sm_E
  (mkSS FR_SM (sr_set sr_atoms (19%bv : bv 5) (SLit 32)) [] None fs_facts0)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_SM)) memc (seg_rom SEGS))).
Proof.
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & R19 & _) & _).
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL sm_E (mkSS FR_SM sr_atoms [] None fs_facts0)
  (mkst regs1 (Z_to_bv 64 (BASE + FR_SM)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  + unfold sm_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor.
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [exact I | split; [exact I | exact I]]. }
exact (st_ok_pi_pin_reg' sm_E _ _ (19%bv : bv 5) 32 HS0 R19 eq_refl).
Qed.
(* the piece's two exits: the stripped line is empty (i0 = C), or the backward strip at j = C *)
Lemma sm_ST : forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest -> getr regs2 27 = w64 (p + Z.of_nat i0) ->
  getr regs2 23 = w64 (p + Z.of_nat (fr_C rest)) -> (fr_C rest <= i0)%nat -> mf_at B v Wc regs2 mem2 md2 FR_ST.
Proof.
intros regs2 mem2 md2 C2 S2 Q27 Q23 HC. pose proof (fs_C_le rest) as HCL.
apply (HST v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest i0 (fr_C rest) C2 S2 Q27 Q23); [lia|].
apply fs_strip_slice; [lia | exact Hab | left; lia | intros ?k ?Hk; lia | left; lia].
Qed.
Lemma sm_SB : forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest -> getr regs2 27 = w64 (p + Z.of_nat i0) -> getr regs2 11 = w64 (p + Z.of_nat i0) ->
  getr regs2 23 = w64 (p + Z.of_nat (fr_C rest)) -> getr regs2 10 = w64 (p + Z.of_nat (fr_C rest) - 1) ->
  (i0 < fr_C rest)%nat -> mf_at B v Wc regs2 mem2 md2 FR_SB.
Proof.
intros regs2 mem2 md2 C2 S2 Q27 Q11 Q23 Q10 HC.
apply (HSB (fr_C rest) v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest i0 C2 S2 Q27 Q11 Q23 Q10);
  [lia | exact Hab | destruct Hst as [E|E]; [lia | exact E] | intros ?k ?Hk; lia].
Qed.

Ltac sm_ux UXN :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
    pose proof (sm_UX Ex ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)) as UXN end.
Ltac sm_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (fs_awr; fail); fs_meq end.
Ltac sm_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (fs_awr; fail); fs_meq end.
Ltac sm_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
Ltac sm_cond :=
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = _ |- _ =>
    let UXc := fresh "UXc" in sm_ux UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in
    destruct UXc as (a1 & a2);
    rewrite ?branch_eq_U, ?branch_ne_U, ?branch_geu_U, ?branch_ltu_U in Hc;
    rewrite ?a1, ?a2 in Hc; clear a1 a2
  end.
Ltac sm_leaf H K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 []) Ecur) by (env_agree_chain sm_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (FR_KEPT ++ [17; 22; 23; 27]%bv) HS HAE2
      ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    let R19x := fresh "R19x" in prreg HS (19%bv : bv 5) R19x;
    pmkst HS;
    let R22 := fresh "R22" in let R17 := fresh "R17" in let HL512 := fresh "HL512" in
    pose proof SH as (R22 & R17 & HL512);
    eapply H;
    [ eapply fr_ctx_run; [exact CTX | exact HJ | exact MEQ | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
      | rewrite R19x; reflexivity]
    | split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact R22 |
       split; [rewrite (HK 17%bv ltac:(cbv; tauto)); exact R17 | exact HL512]]
    | .. ]; K HS HK
  end.

Lemma sm_step : mf_at B v Wc regs1 memc mdc FR_SM.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof sm_seed as HS.
assert (HEI : img_env VAL A_LIM sm_E) by (unfold sm_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] sm_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
unfold mf_at.
sm_run; sm_branch.
- sm_cond. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
  sm_runto FR_ST.
  sm_leaf sm_ST ltac:(fun HS HK => first
    [ rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27
    | rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23
    | lia ]).
- sm_cond. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
  sm_runto FR_SB.
  sm_leaf sm_SB ltac:(fun HS HK =>
    pose proof sm_tf as (T1 & T2 & T3 & T4); pose proof alloc_ceiling_value as [[_ HAC] _];
    first
    [ rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27
    | let R := fresh in prreg_mul0 HS (11%bv : bv 5) R; rewrite R, (sm_EN 27%nat 27%bv eq_refl), R27 by lia;
      reflexivity
    | rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23
    | let R := fresh in prreg HS (10%bv : bv 5) R; rewrite R, (sm_EN 23%nat 23%bv eq_refl), R23 by lia;
      unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
    | lia ]).
Qed.
End sm.

(* ============================== sf: 0x86208-0x86248 ============================== *)
Section sf.
Variables (n k : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z).
Hypothesis HSM : FR_SM_stmt B n.
Hypothesis HNX : FR_SF_stmt B n (S k).
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis SH : fr_short regs1 line p rest.
Hypothesis R27 : getr regs1 27 = w64 (p + Z.of_nat k).
Hypothesis R10 : getr regs1 10 = w64 (p + Z.of_nat k).
Hypothesis R23 : getr regs1 23 = w64 (p + Z.of_nat (fr_C rest)).
Hypothesis Hk : (k < fr_C rest)%nat.
Hypothesis Hab : all_blank (fr_cut rest) 0 k.

Definition sf_b : Z := nth k (mf_line rest) 0.
Definition sf_E : env := Eimg (Ereg regs1 [Z_to_bv 64 sf_b]).

Lemma sf_tf : 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\
  (fr_C rest <= length (mf_line rest))%nat /\ (length (mf_line rest) < 512)%nat /\ 0 <= sf_b < 256 /\
  rdW Wc memc (p + Z.of_nat k) = Some sf_b /\ nth k (fr_cut rest) 0 = sf_b.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & BY & BR8 & _).
pose proof (fr_line_len rest) as HLL. pose proof (fs_C_le rest) as HC. pose proof SH as (_ & _ & HL512).
split; [exact H1|]. split; [lia|]. split; [exact HC|]. split; [exact HL512|].
split; [apply BR8; lia|]. split; [apply BY; lia|].
unfold fr_cut, sf_b. apply fr_cut_nth. exact Hk.
Qed.
Lemma sf_rad : forall x, p <= x < p + Z.of_nat (length (mf_line rest)) ->
  range_addressable (rdW Wc memc) SHADOW_OFF x 1.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & _ & RAD).
pose proof (fr_line_len rest) as HLL. intros x Hx y Hy. apply RAD. lia.
Qed.
Lemma sf_EN : forall k' (r : bv 5), Z.of_nat k' = bv_unsigned r -> (k' < 32)%nat -> ew sf_E k' = getr regs1 r.
Proof. intros k' r Hk' Hk32. unfold sf_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk'. Qed.
Lemma sf_HAE : env_agree 32 (Ereg regs1 [Z_to_bv 64 sf_b]) sf_E.
Proof. unfold sf_E. split; [intros k' Hk'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma sf_UX : forall Ex, (forall k', (k' < 1024)%nat -> ew Ex k' = ew sf_E k') ->
  U Ex (SOff 32 0) = sf_b /\ U Ex (SOff 25 0) = MF_BLANK /\ U Ex (SOff 23 0) = p + Z.of_nat (fr_C rest) /\
  U Ex (SOff 10 0) = p + Z.of_nat k /\ U Ex (SOff 10 1) = p + Z.of_nat k + 1 /\
  U Ex (SOff 27 0) = p + Z.of_nat k /\ U Ex (SOff 18 0) = SHADOW_OFF.
Proof.
intros Ex HEx. pose proof sf_tf as (T1 & T2 & T3 & T4 & T5 & _).
pose proof alloc_ceiling_value as [[_ HAC] _]. pose proof Hk as Hk'.
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & _ & R25 & _) & _).
split; [apply U_atom; [rewrite HEx by lia; unfold sf_E; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs1 _ 0) | lia]|].
split; [apply U_atom; [rewrite HEx, (sf_EN 25%nat 25%bv eq_refl) by lia; exact R25 | unfold MF_BLANK; lia]|].
split; [apply U_atom; [rewrite HEx, (sf_EN 23%nat 23%bv eq_refl) by lia; exact R23 | lia]|].
split; [apply U_atom; [rewrite HEx, (sf_EN 10%nat 10%bv eq_refl) by lia; exact R10 | lia]|].
split; [apply fr_U_atom_off; [rewrite HEx, (sf_EN 10%nat 10%bv eq_refl) by lia; exact R10 | lia | lia]|].
split; [apply U_atom; [rewrite HEx, (sf_EN 27%nat 27%bv eq_refl) by lia; exact R27 | lia]|].
apply U_atom; [rewrite HEx, (sf_EN 18%nat 18%bv eq_refl) by lia; exact R18 | unfold SHADOW_OFF; lia].
Qed.
Lemma sf_seed : st_ok_pi SEGS VAL sf_E
  (mkSS FR_SF (sr_set sr_atoms (19%bv : bv 5) (SLit 32)) [fs_sf_text] None fs_sf_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_SF)) memc (seg_rom SEGS))).
Proof.
pose proof sf_tf as (T1 & T2 & T3 & T4 & T5 & BY & _).
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & R19 & _) & _).
pose proof alloc_ceiling_value as [[_ HAC] _]. pose proof Hk as Hk'.
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL sf_E (mkSS FR_SF sr_atoms [fs_sf_text] None fs_sf_facts)
  (mkst regs1 (Z_to_bv 64 (BASE + FR_SF)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  + unfold sf_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor]. unfold region_ok, fs_sf_text.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (sf_EN 27%nat 27%bv eq_refl), R27 by lia. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS sf_E _ (p + Z.of_nat k) 0 1 (SOff 32 0) sf_b);
      [cbn [sv_denot]; unfold sf_E; rewrite Eimg_low by (unfold A_TEXT; lia);
       rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (fr_val_mem1 _ _ _ _ BY).
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [fs_sf_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite (sf_EN 10%nat 10%bv eq_refl), (sf_EN 27%nat 27%bv eq_refl), (sf_EN 18%nat 18%bv eq_refl) by lia.
    rewrite R10, R27, R18. unfold sf_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_extra regs1 _ 0). cbn [nth].
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
    clear - T1 T2 T3 T5 HAC Hk'. repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity.
    all: lia. }
exact (st_ok_pi_pin_reg' sf_E _ _ (19%bv : bv 5) 32 HS0 R19 eq_refl).
Qed.
(* the pass's three exits: not blank at k (i0 = k), blank at k with k + 1 < C (the next k), or with k + 1 = C *)
Lemma sf_SMk : forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest -> getr regs2 27 = w64 (p + Z.of_nat k) ->
  getr regs2 23 = w64 (p + Z.of_nat (fr_C rest)) -> blank sf_b = false -> mf_at B v Wc regs2 mem2 md2 FR_SM.
Proof.
intros regs2 mem2 md2 C2 S2 Q27 Q23 HNB. pose proof sf_tf as (_ & _ & _ & _ & _ & _ & HCB).
apply (HSM v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest k C2 S2 Q27 Q23);
  [lia | exact Hab | right; rewrite HCB; exact HNB].
Qed.
Lemma sf_SMC : forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest -> getr regs2 27 = w64 (p + Z.of_nat (fr_C rest)) ->
  getr regs2 23 = w64 (p + Z.of_nat (fr_C rest)) -> blank sf_b = true -> S k = fr_C rest ->
  mf_at B v Wc regs2 mem2 md2 FR_SM.
Proof.
intros regs2 mem2 md2 C2 S2 Q27 Q23 HB HSk. pose proof sf_tf as (_ & _ & _ & _ & _ & _ & HCB).
apply (HSM v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest (fr_C rest) C2 S2 Q27 Q23); [lia | | left; reflexivity].
intros k' Hk'. destruct (Nat.eq_dec k' k) as [->|Hne]; [rewrite HCB; exact HB | apply Hab; lia].
Qed.
Lemma sf_SF : forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest -> getr regs2 27 = w64 (p + Z.of_nat (S k)) ->
  getr regs2 10 = w64 (p + Z.of_nat (S k)) -> getr regs2 23 = w64 (p + Z.of_nat (fr_C rest)) ->
  blank sf_b = true -> (S k < fr_C rest)%nat -> mf_at B v Wc regs2 mem2 md2 FR_SF.
Proof.
intros regs2 mem2 md2 C2 S2 Q27 Q10 Q23 HB HSk. pose proof sf_tf as (_ & _ & _ & _ & _ & _ & HCB).
apply (HNX v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest C2 S2 Q27 Q10 Q23 HSk).
intros k' Hk'. destruct (Nat.eq_dec k' k) as [->|Hne]; [rewrite HCB; exact HB | apply Hab; lia].
Qed.

Ltac sf_ux UXN :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
    pose proof (sf_UX Ex ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)) as UXN end.
Ltac sf_obl :=
  lazymatch goal with
  | MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- range_addressable _ (U ?Ex (SOff 18 0)) (U ?Ex ?x) _ =>
    let UXO := fresh "UXO" in sf_ux UXO;
    let UX10 := fresh "UX10" in let UX18 := fresh "UX18" in
    destruct UXO as (_ & _ & _ & UX10 & _ & _ & UX18);
    rewrite <- (aview_rd_of SEGS);
    apply (fr_ra_eq (aview SEGS (w_H Wc) memc)); [intros; first [apply MEQ | reflexivity] |];
    rewrite ?UX18, ?UX10; apply sf_rad; pose proof Hk; pose proof sf_tf as (_ & _ & ?T3 & _); lia end.
Ltac sf_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (fs_awr; fail); try (sf_obl; fail); fs_meq end.
Ltac sf_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (fs_awr; fail); try (sf_obl; fail); fs_meq end.
Ltac sf_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
Ltac sf_cond :=
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = _ |- _ =>
    let UXc := fresh "UXc" in sf_ux UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in let a3 := fresh "a" in let a4 := fresh "a" in
    let a5 := fresh "a" in let a6 := fresh "a" in let a7 := fresh "a" in
    destruct UXc as (a1 & a2 & a3 & a4 & a5 & a6 & a7);
    rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc;
    rewrite ?a1, ?a2, ?a3, ?a4, ?a5, ?a6, ?a7 in Hc;
    repeat match type of Hc with context [U Ex (SLit ?z)] => rewrite (U_lit Ex z) in Hc by lia end;
    clear a1 a2 a3 a4 a5 a6 a7
  end.
(* the mask test (`beqz a1` after `srl a1,s9,a1; andi a1,a1,1`) as the byte's blankness *)
Ltac sf_mask :=
  sf_cond;
  lazymatch goal with Hc : (U ?Ex (SAlu _ _ _) =? _) = _ |- _ =>
    let UXc := fresh "UXc" in sf_ux UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in destruct UXc as (a1 & a2 & _);
    let Hb := fresh "Hb" in
    assert (Hb : 0 <= sf_b <= 32) by (pose proof sf_tf as (_ & _ & _ & _ & ?T5 & _); lia);
    rewrite (fs_mask_U Ex sf_b a2 a1 Hb) in Hc; clear a1 a2 Hb
  end.
Ltac sf_leaf H K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 [Z_to_bv 64 sf_b]) Ecur) by (env_agree_chain sf_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (FR_KEPT ++ [17; 22; 23]%bv) HS HAE2
      ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    let R19x := fresh "R19x" in prreg HS (19%bv : bv 5) R19x;
    pmkst HS;
    let R22 := fresh "R22" in let R17 := fresh "R17" in let HL512 := fresh "HL512" in
    pose proof SH as (R22 & R17 & HL512);
    eapply H;
    [ eapply fr_ctx_run; [exact CTX | exact HJ | exact MEQ | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
      | rewrite R19x; reflexivity]
    | split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact R22 |
       split; [rewrite (HK 17%bv ltac:(cbv; tauto)); exact R17 | exact HL512]]
    | .. ]; K HS HK
  end.
(* the registers at a stop of the pass *)
Ltac sf_k HS HK :=
  pose proof sf_tf as (T1 & T2 & T3 & T4 & T5 & _); pose proof alloc_ceiling_value as [[_ HAC] _]; pose proof Hk;
  first
  [ rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23
  | let R := fresh in prreg HS (27%bv : bv 5) R;
    first [ rewrite R, (sf_EN 27%nat 27%bv eq_refl), R27 by lia | rewrite R, (sf_EN 23%nat 23%bv eq_refl), R23 by lia ];
    first [ reflexivity | unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia ]
  | let R := fresh in prreg HS (10%bv : bv 5) R; rewrite R, (sf_EN 10%nat 10%bv eq_refl), R10 by lia;
    unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
  | assumption
  | lia ].

Lemma sf_step : mf_at B v Wc regs1 memc mdc FR_SF.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof sf_seed as HS.
assert (HEI : img_env VAL A_LIM sf_E) by (unfold sf_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] sf_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
unfold mf_at.
sf_run; sf_branch.
- (* 0x8621c `bltu s3,a1` taken: the byte is above ' ', not blank *)
  sf_cond. apply Z.ltb_lt in Hc.
  assert (HNB : blank sf_b = false) by (apply fr_blank_gt32; exact Hc).
  sf_runto FR_SM. sf_leaf sf_SMk ltac:(fun HS HK => sf_k HS HK).
- sf_cond. apply Z.ltb_ge in Hc. rename Hc into H32.
  sf_run; sf_branch.
  + (* 0x86228 `beqz a1` taken: its mask bit is 0, not blank *)
    sf_mask. revert Hc. destruct (blank sf_b) eqn:HNB; intros Hc; cbn in Hc; [discriminate Hc|].
    sf_runto FR_SM. sf_leaf sf_SMk ltac:(fun HS HK => sf_k HS HK).
  + sf_mask. revert Hc. destruct (blank sf_b) eqn:HB; intros Hc; cbn in Hc; [|discriminate Hc]. clear Hc.
    sf_run; sf_branch.
    * (* 0x86234 `bne s7,a0` taken: k + 1 < C *)
      sf_cond. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
      sf_runto FR_SF. sf_leaf sf_SF ltac:(fun HS HK => sf_k HS HK).
    * (* k + 1 = C: 0x86248 `mv s11,s7` *)
      sf_cond. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
      sf_runto FR_SM. sf_leaf sf_SMC ltac:(fun HS HK => sf_k HS HK).
Qed.
End sf.

(* ============================== sb: 0x8625c-0x862a0 ============================== *)
Section sb.
Variables (n j : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z) (i0 : nat).
Hypothesis HST : FR_ST_stmt B n.
Hypothesis HNX : FR_SB_stmt B n j.
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis SH : fr_short regs1 line p rest.
Hypothesis R27 : getr regs1 27 = w64 (p + Z.of_nat i0).
Hypothesis R11 : getr regs1 11 = w64 (p + Z.of_nat i0).
Hypothesis R23 : getr regs1 23 = w64 (p + Z.of_nat (S j)).
Hypothesis R10 : getr regs1 10 = w64 (p + Z.of_nat (S j) - 1).
Hypothesis Hij : (i0 < S j <= fr_C rest)%nat.
Hypothesis Hab : all_blank (fr_cut rest) 0 i0.
Hypothesis Hnb : blank (nth i0 (fr_cut rest) 0) = false.
Hypothesis HabR : all_blank (fr_cut rest) (S j) (fr_C rest).

Definition sb_b : Z := nth j (mf_line rest) 0.
Definition sb_E : env := Eimg (Ereg regs1 [Z_to_bv 64 sb_b]).

Lemma sb_tf : 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\
  (fr_C rest <= length (mf_line rest))%nat /\ (length (mf_line rest) < 512)%nat /\ 0 <= sb_b < 256 /\
  rdW Wc memc (p + Z.of_nat j) = Some sb_b /\ nth j (fr_cut rest) 0 = sb_b.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & BY & BR8 & _).
pose proof (fr_line_len rest) as HLL. pose proof (fs_C_le rest) as HC. pose proof SH as (_ & _ & HL512).
split; [exact H1|]. split; [lia|]. split; [exact HC|]. split; [exact HL512|].
split; [apply BR8; lia|]. split; [apply BY; lia|].
unfold fr_cut, sb_b. apply fr_cut_nth. pose proof Hij as Hij'. unfold fr_C, fr_cut in Hij'. lia.
Qed.
Lemma sb_rad : forall x, p <= x < p + Z.of_nat (length (mf_line rest)) ->
  range_addressable (rdW Wc memc) SHADOW_OFF x 1.
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & _ & RAD).
pose proof (fr_line_len rest) as HLL. intros x Hx y Hy. apply RAD. lia.
Qed.
Lemma sb_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew sb_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold sb_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma sb_HAE : env_agree 32 (Ereg regs1 [Z_to_bv 64 sb_b]) sb_E.
Proof. unfold sb_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma sb_UX : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew sb_E k) ->
  U Ex (SOff 32 0) = sb_b /\ U Ex (SOff 25 0) = MF_BLANK /\ U Ex (SOff 27 0) = p + Z.of_nat i0 /\
  U Ex (SOff 23 (-1)) = p + Z.of_nat (S j) + -1 /\ U Ex (SOff 10 0) = p + Z.of_nat (S j) - 1 /\
  U Ex (SOff 18 0) = SHADOW_OFF.
Proof.
intros Ex HEx. pose proof sb_tf as (T1 & T2 & T3 & T4 & T5 & _).
pose proof alloc_ceiling_value as [[_ HAC] _]. pose proof Hij as Hij'.
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & _ & R25 & _) & _).
split; [apply U_atom; [rewrite HEx by lia; unfold sb_E; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs1 _ 0) | lia]|].
split; [apply U_atom; [rewrite HEx, (sb_EN 25%nat 25%bv eq_refl) by lia; exact R25 | unfold MF_BLANK; lia]|].
split; [apply U_atom; [rewrite HEx, (sb_EN 27%nat 27%bv eq_refl) by lia; exact R27 | lia]|].
split; [apply fr_U_atom_off; [rewrite HEx, (sb_EN 23%nat 23%bv eq_refl) by lia; exact R23 | lia | lia]|].
split; [apply U_atom; [rewrite HEx, (sb_EN 10%nat 10%bv eq_refl) by lia; exact R10 | lia]|].
apply U_atom; [rewrite HEx, (sb_EN 18%nat 18%bv eq_refl) by lia; exact R18 | unfold SHADOW_OFF; lia].
Qed.
Lemma sb_seed : st_ok_pi SEGS VAL sb_E
  (mkSS FR_SB (sr_set sr_atoms (19%bv : bv 5) (SLit 32)) [fs_sb_text] None fs_sb_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_SB)) memc (seg_rom SEGS))).
Proof.
pose proof sb_tf as (T1 & T2 & T3 & T4 & T5 & BY & _).
pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & R18 & R19 & _) & _).
pose proof alloc_ceiling_value as [[_ HAC] _]. pose proof Hij as Hij'.
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL sb_E (mkSS FR_SB sr_atoms [fs_sb_text] None fs_sb_facts)
  (mkst regs1 (Z_to_bv 64 (BASE + FR_SB)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  + unfold sb_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor]. unfold region_ok, fs_sb_text.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (sb_EN 23%nat 23%bv eq_refl), R23 by lia. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS sb_E _ (p + Z.of_nat (S j)) (-1) 1 (SOff 32 0) sb_b);
      [cbn [sv_denot]; unfold sb_E; rewrite Eimg_low by (unfold A_TEXT; lia);
       rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    replace (p + Z.of_nat (S j) + -1) with (p + Z.of_nat j) by lia. exact (fr_val_mem1 _ _ _ _ BY).
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [fs_sb_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite (sb_EN 10%nat 10%bv eq_refl), (sb_EN 23%nat 23%bv eq_refl), (sb_EN 18%nat 18%bv eq_refl) by lia.
    rewrite R10, R23, R18. unfold sb_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_extra regs1 _ 0). cbn [nth].
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
    clear - T1 T2 T3 T5 HAC Hij'. repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity.
    all: lia. }
exact (st_ok_pi_pin_reg' sb_E _ _ (19%bv : bv 5) 32 HS0 R19 eq_refl).
Qed.
(* the pass's exits: not blank at j - 1 (the stripped line ends at j), blank with i0 < j - 1 (the pass at j - 1);
   blank with j - 1 = i0 cannot be *)
Lemma sb_ST : forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest -> getr regs2 27 = w64 (p + Z.of_nat i0) ->
  getr regs2 23 = w64 (p + Z.of_nat (S j)) -> blank sb_b = false -> mf_at B v Wc regs2 mem2 md2 FR_ST.
Proof.
intros regs2 mem2 md2 C2 S2 Q27 Q23 HNB. pose proof sb_tf as (_ & _ & _ & _ & _ & _ & HCB).
pose proof (fs_C_le rest) as HCL.
apply (HST v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest i0 (S j) C2 S2 Q27 Q23); [lia|].
apply fs_strip_slice; [lia | exact Hab | right; exact Hnb | exact HabR |].
right. replace (S j - 1)%nat with j by lia. rewrite HCB. exact HNB.
Qed.
Lemma sb_SB : forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
  fr_short regs2 line p rest -> getr regs2 27 = w64 (p + Z.of_nat i0) -> getr regs2 11 = w64 (p + Z.of_nat i0) ->
  getr regs2 23 = w64 (p + Z.of_nat j) -> getr regs2 10 = w64 (p + Z.of_nat j - 1) ->
  blank sb_b = true -> (i0 < j)%nat -> mf_at B v Wc regs2 mem2 md2 FR_SB.
Proof.
intros regs2 mem2 md2 C2 S2 Q27 Q11 Q23 Q10 HB Hlt. pose proof sb_tf as (_ & _ & _ & _ & _ & _ & HCB).
apply (HNX v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest i0 C2 S2 Q27 Q11 Q23 Q10);
  [lia | exact Hab | exact Hnb |].
intros k Hk. destruct (Nat.eq_dec k j) as [->|Hne]; [rewrite HCB; exact HB | apply HabR; lia].
Qed.
Lemma sb_no : blank sb_b = true -> (j <= i0)%nat -> False.
Proof.
intros HB Hle. pose proof sb_tf as (_ & _ & _ & _ & _ & _ & HCB).
assert (E : i0 = j) by lia. rewrite E, HCB in Hnb. congruence.
Qed.

Ltac sb_ux UXN :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
    pose proof (sb_UX Ex ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)) as UXN end.
Ltac sb_obl :=
  lazymatch goal with
  | MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- range_addressable _ (U ?Ex (SOff 18 0)) (U ?Ex ?x) _ =>
    let UXO := fresh "UXO" in sb_ux UXO;
    let UX10 := fresh "UX10" in let UX18 := fresh "UX18" in
    destruct UXO as (_ & _ & _ & _ & UX10 & UX18);
    rewrite <- (aview_rd_of SEGS);
    apply (fr_ra_eq (aview SEGS (w_H Wc) memc)); [intros; first [apply MEQ | reflexivity] |];
    rewrite ?UX18, ?UX10; apply sb_rad; pose proof Hij; pose proof sb_tf as (_ & _ & ?T3 & _); lia end.
Ltac sb_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (fs_awr; fail); try (sb_obl; fail); fs_meq end.
Ltac sb_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (fs_awr; fail); try (sb_obl; fail); fs_meq end.
Ltac sb_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
Ltac sb_cond :=
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = _ |- _ =>
    let UXc := fresh "UXc" in sb_ux UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in let a3 := fresh "a" in let a4 := fresh "a" in
    let a5 := fresh "a" in let a6 := fresh "a" in
    destruct UXc as (a1 & a2 & a3 & a4 & a5 & a6);
    rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc;
    rewrite ?a1, ?a2, ?a3, ?a4, ?a5, ?a6 in Hc;
    repeat match type of Hc with context [U Ex (SLit ?z)] => rewrite (U_lit Ex z) in Hc by lia end;
    clear a1 a2 a3 a4 a5 a6
  end.
Ltac sb_mask :=
  sb_cond;
  lazymatch goal with Hc : (U ?Ex (SAlu _ _ _) =? _) = _ |- _ =>
    let UXc := fresh "UXc" in sb_ux UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in destruct UXc as (a1 & a2 & _);
    let Hb := fresh "Hb" in
    assert (Hb : 0 <= sb_b <= 32) by (pose proof sb_tf as (_ & _ & _ & _ & ?T5 & _); lia);
    rewrite (fs_mask_U Ex sb_b a2 a1 Hb) in Hc; clear a1 a2 Hb
  end.
Ltac sb_leaf H K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 [Z_to_bv 64 sb_b]) Ecur) by (env_agree_chain sb_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (FR_KEPT ++ [11; 17; 22; 27]%bv) HS HAE2
      ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    let R19x := fresh "R19x" in prreg HS (19%bv : bv 5) R19x;
    pmkst HS;
    let R22 := fresh "R22" in let R17 := fresh "R17" in let HL512 := fresh "HL512" in
    pose proof SH as (R22 & R17 & HL512);
    eapply H;
    [ eapply fr_ctx_run; [exact CTX | exact HJ | exact MEQ | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
      | rewrite R19x; reflexivity]
    | split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact R22 |
       split; [rewrite (HK 17%bv ltac:(cbv; tauto)); exact R17 | exact HL512]]
    | .. ]; K HS HK
  end.
Ltac sb_k HS HK :=
  pose proof sb_tf as (T1 & T2 & T3 & T4 & T5 & _); pose proof alloc_ceiling_value as [[_ HAC] _]; pose proof Hij;
  first
  [ rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27
  | rewrite (HK 11%bv ltac:(cbv; tauto)); exact R11
  | let R := fresh in prreg HS (23%bv : bv 5) R; rewrite R, (sb_EN 23%nat 23%bv eq_refl), R23 by lia;
    first [ reflexivity | unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia ]
  | let R := fresh in prreg HS (10%bv : bv 5) R; rewrite R, (sb_EN 10%nat 10%bv eq_refl), R10 by lia;
    unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
  | assumption
  | lia ].

Lemma sb_step : mf_at B v Wc regs1 memc mdc FR_SB.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof sb_seed as HS.
assert (HEI : img_env VAL A_LIM sb_E) by (unfold sb_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] sb_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
unfold mf_at.
sb_run; sb_branch.
- (* 0x86274 `bltu s3,a3` taken: the byte is above ' ', not blank *)
  sb_cond. apply Z.ltb_lt in Hc.
  assert (HNB : blank sb_b = false) by (apply fr_blank_gt32; exact Hc).
  sb_runto FR_ST. sb_leaf sb_ST ltac:(fun HS HK => sb_k HS HK).
- sb_cond. apply Z.ltb_ge in Hc. rename Hc into H32.
  sb_run; sb_branch.
  + (* 0x86280 `beqz a3` taken: its mask bit is 0, not blank *)
    sb_mask. revert Hc. destruct (blank sb_b) eqn:HNB; intros Hc; cbn in Hc; [discriminate Hc|].
    sb_runto FR_ST. sb_leaf sb_ST ltac:(fun HS HK => sb_k HS HK).
  + sb_mask. revert Hc. destruct (blank sb_b) eqn:HB; intros Hc; cbn in Hc; [|discriminate Hc]. clear Hc.
    sb_run; sb_branch.
    * (* 0x8628c `bltu s11,a2` taken: i0 < j - 1 *)
      sb_cond. apply Z.ltb_lt in Hc.
      sb_runto FR_SB. sb_leaf sb_SB ltac:(fun HS HK => sb_k HS HK).
    * (* j - 1 <= i0: cut[i0] would be blank *)
      sb_cond. apply Z.ltb_ge in Hc. exfalso. apply sb_no; [exact HB | lia].
Qed.
End sb.

(* ============================== the pieces ============================== *)
Lemma fr_cx : forall n, (forall k, FR_SF_stmt B n k) -> FR_SM_stmt B n -> FR_CX_stmt B n.
Proof.
intros n HSF HSM v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX SH R27 R12.
eapply cx_step; eassumption.
Qed.
Lemma fr_sf_step : forall n k, FR_SM_stmt B n -> FR_SF_stmt B n (S k) -> FR_SF_stmt B n k.
Proof.
intros n k HSM HNX v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX SH R27 R10 R23 Hk Hab.
eapply sf_step; eassumption.
Qed.
(* every index of the forward strip, from its exit (by induction on 512 - k: k < C <= L < 512) *)
Lemma fr_sf : forall n, FR_SM_stmt B n -> forall k, FR_SF_stmt B n k.
Proof.
intros n HSM.
assert (HD : forall d k, (512 - d <= k)%nat -> FR_SF_stmt B n k).
{ induction d as [|d IH]; intros k Hd.
  - intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX SH. destruct SH as (_ & _ & HL).
    pose proof (fs_C_le rest). intros. exfalso. lia.
  - destruct (Nat.le_gt_cases (512 - d) k) as [Hle | Hlt]; [exact (IH k Hle)|].
    apply fr_sf_step; [exact HSM | apply IH; lia]. }
intros k. apply (HD 512%nat k). lia.
Qed.
Lemma fr_sm : forall n, (forall j, FR_SB_stmt B n j) -> FR_ST_stmt B n -> FR_SM_stmt B n.
Proof.
intros n HSB HST v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i0 CTX SH R27 R23 Hi0 Hab Hst.
eapply sm_step; eassumption.
Qed.
Lemma fr_sb_step : forall n j, FR_ST_stmt B n -> FR_SB_stmt B n j -> FR_SB_stmt B n (S j).
Proof.
intros n j HST HNX v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i0 CTX SH R27 R11 R23 R10 Hij Hab Hnb HabR.
eapply sb_step; eassumption.
Qed.
(* every index of the backward strip (j = 0 has no state: i0 < j) *)
Lemma fr_sb : forall n, FR_ST_stmt B n -> forall j, FR_SB_stmt B n j.
Proof.
intros n HST j. induction j as [|j IH].
- intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i0 CTX SH R27 R11 R23 R10 Hij. exfalso. lia.
- apply fr_sb_step; assumption.
Qed.
End e.
End f.
End d.

Print Assumptions fr_sf.
Print Assumptions fr_sb.
