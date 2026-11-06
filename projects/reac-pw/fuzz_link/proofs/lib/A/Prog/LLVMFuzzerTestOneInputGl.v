(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 1580 of its 1645 lines of code are new or changed and 339 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): the 64-turn g_names
   loop of its walk, +0x32c .. +0x3b4, and the odd table's set-up +0x3b8 .. +0x404 that the loop's exit
   falls into. The cut interface is lib/A/Prog/LLVMFuzzerTestOneInputDefs.v; the shared data of the two
   set-up loops is lib/A/Prog/LLVMFuzzerTestOneInputSu.v.

     lf_gl : forall POST, lf_from .. POST (lf_ol_inv .. 0) -> forall j, 0 <= j < 64 ->
             lf_from .. POST (lf_gl_inv .. j)

   THE TURN (offsets from 0x827d4):
   +0x32c  s4 := s8 - 2 = j; a1 := 8; a0 := s5 = g_names + 8 j; a2 := s6 = .str "nl%d"; a3 := s4 = j
   +0x340  snprintf(g_names + 8 j, 8, "nl%d", j)                     (the call; LF_sn_ra = +0x344)
   +0x344  a0 := s4 & 0xf; `beq a0, 0xf` -> +0x3a8: the turn appends nothing when j mod 16 = 15
   +0x350  a0 := g_nl.n_if; a0 := g_nl + NK_IF_NAME + 8 n_if; the instrumented check of its shadow byte
           (+0x364 reads the shadow base out of the slot at s1 + 0xf8), then `sd s5, 0(a0)`
   +0x37c  n_if := n_if + 1; a0 := g_nl + NK_IF_INDEX + 4 n_if; the instrumented check; `sw s8, 0(a0)`
   +0x3a8  s7 := s7 - 1; s8 := s8 + 1; s5 := s5 + 8; `bnez s7` back to +0x32c
   +0x3b8  `j +0x3cc`, then the odd table's set-up, which ends at +0x408 = LF_ol with lf_ol_inv 0.
   The run before the call is one symbolic run from the cut (gl_entry). The call is lib/A/Prog/
   LLVMFuzzerTestOneInputSnp.v `lf_snp_at`. After it the walk starts a second symbolic run from a state built at
   the return (gl_mid): the two table slots g_nl + NK_IF_NAME + 8 n_if and g_nl + NK_IF_INDEX + 4 n_if are
   computed from the loaded n_if, so each is an atom of its own (35, 36) with its region, and the engine's
   expression for each address is pinned to the atom (gl_pin_name, gl_pin_index). The two instrumented checks
   leave two obligations, the addressability of the slot, which AR's zero shadow of g_nl gives at every state
   (LinkWalkZsh.v zsh_gnl, through Su.v lf_ra_sub); so neither error path (+0x374, +0x3c8) is reached.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0n YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit link_aro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkPi LinkWalkZsh BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkSnpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs LLVMFuzzerTestOneInputSu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require LLVMFuzzerTestOneInputSnp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the symbolic entry state of a turn (+0x32c) ------------------------------------------------------- *)
(* atom 32 = the shadow base (read out of the slot at s1 + LS_SHB), atom 34 = the turn's index j *)
Definition GL_SHB_R : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_SHB (LS_SHB + 8) 0 0 [YP09.mkChunk LS_SHB (CVal 8 (SOff 32 0))].
Definition GL_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0); (34%nat, mkAF 0 63 0)] [] [].
(* s8 holds j + 2; giving the turn's index its own atom (34) lets the engine fold the 32-bit
   `addiw s4, s8, -2` of +0x32c back to the atom, so the snprintf argument is the atom itself. *)
Definition GL_SS0 : sstate := mkSS LF_gl sr_atoms [GL_SHB_R] None GL_FACTS.
Definition GL_SS : sstate := mkSS LF_gl (sr_set sr_atoms 24 (SOff 34 2)) [GL_SHB_R] None GL_FACTS.
Definition GL_EXTRA (j : Z) : list word := map (Z_to_bv 64) [SB; 0; j].

(* ---- the symbolic state at snprintf's return (+0x344) -------------------------------------------------- *)
(* atoms: 32 the shadow base, 33 g_nl.n_if, 34 j, 35 / 36 the two table slots n_if names, 37 the slot at
   s1 + LS_WA (the frame's first object, which +0x404 loads into s10) *)
Definition gl_aname (nif : Z) : Z := LA_G_NL + NK_IF_NAME + 8 * nif.
Definition gl_aidx (nif : Z) : Z := LA_G_NL + NK_IF_INDEX + 4 * nif.
Definition GL_WA_R : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_WA (LS_WA + 8) 0 0 [YP09.mkChunk LS_WA (CVal 8 (SOff 37 0))].
Definition GL_O50_R : YP09.region := YP09.mkRegion (Some 9%nat) LS_ODD (LS_ODD + 8) LS_ODD (LS_ODD + 8) [].
Definition GL_NIF_R : YP09.region :=
  YP09.mkRegion (Some 26%nat) 0x670 0x674 0x670 0x674 [YP09.mkChunk 0x670 (CVal 4 (SOff 33 0))].
Definition GL_NAME_R : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 8 [].
Definition GL_IDX_R : YP09.region := YP09.mkRegion (Some 36%nat) 0 4 0 4 [].
Definition GL2_MEM : smem := [GL_SHB_R; GL_WA_R; GL_O50_R; GL_NIF_R; GL_NAME_R; GL_IDX_R].
Definition GL2_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (26%nat, mkAF (LA_G_NL + 0x42000) (LA_G_NL + 0x42000) 3);
           (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 60 0); (34%nat, mkAF 0 63 0);
           (35%nat, mkAF (gl_aname 0) (gl_aname 60) 3); (36%nat, mkAF (gl_aidx 0) (gl_aidx 60) 2)] [] [].
Definition GL2_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 20 (SOff 34 0)) 24 (SOff 34 2)) 25 (SLit 0x42530)) 27 (SLit 0x422b0).
Definition GL2_SS0 : sstate := mkSS LF_sn_ra sr_atoms GL2_MEM None GL2_FACTS.
Definition GL2_SS : sstate := mkSS LF_sn_ra GL2_REGS GL2_MEM None GL2_FACTS.
Definition GL2_EXTRA (nif j wa : Z) : list word :=
  map (Z_to_bv 64) [SB; nif; j; gl_aname nif; gl_aidx nif; wa].

(* a callee-saved register across a call *)
Lemma gl_pres_reg : forall (regsA regsB : bvmap 5 word) (r : bv 5),
  aregs_preserved regsA regsB -> acallee_saved (bv_unsigned r) -> getr regsB r = getr regsA r.
Proof. intros regsA regsB r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

(* a word read back through a reader that agrees on its eight bytes *)
Lemma gl_rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  replace (rd' a) with (rd a) by (rewrite <- (Z.add_0_r a); symmetry; apply H; lia).
  rewrite (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* ---- pure list and arithmetic facts of the turn ---- *)
Lemma gl_nth_firstn : forall {A : Type} (l : list A) k i, (i < k)%nat ->
  nth_error (firstn k l) i = nth_error l i.
Proof.
  intros A l. induction l as [|x l IH]; intros k i H.
  - rewrite firstn_nil. reflexivity.
  - destruct k as [|k]; [lia|]. destruct i as [|i]; cbn [firstn nth_error]; [reflexivity|].
    apply IH. lia.
Qed.

Lemma gl_nth_map : forall (l : list Z) k, (k < length l)%nat ->
  nth_error (map (fun z => Z_to_bv 8 z) l) k = Some (Z_to_bv 8 (nth k l 0)).
Proof.
  intros l. induction l as [|z l IH]; intros [|k] Hk; cbn [length map nth_error nth] in *;
    [lia | lia | reflexivity | apply IH; lia].
Qed.

Lemma gl_nth_of_error : forall {A : Type} (l : list A) n (x d : A), nth_error l n = Some x -> nth n l d = x.
Proof.
  intros A l. induction l as [|y l IH]; intros [|n] x d H; cbn [nth_error nth] in *; try discriminate.
  - injection H as <-. reflexivity.
  - apply IH. exact H.
Qed.

Lemma gl_zb_neq : forall z, 0 < z < 256 -> Z_to_bv 8 z <> Z_to_bv 8 0.
Proof.
  intros z Hz H. apply (f_equal bv_unsigned) in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 8) with 256 in H.
  rewrite (Z.mod_small z) in H by lia. rewrite Z.mod_0_l in H by lia. lia.
Qed.

(* the name of a turn has no NUL in it *)
Lemma gl_gname_nz : forall k, 0 <= k < 100 -> ~ In (zb 0) (lf_gname k).
Proof.
  intros k Hk H. unfold lf_gname in H. apply in_map_iff in H as (z & Hz & Hin).
  apply (gl_zb_neq z); [|exact Hz].
  unfold lf_gname_z, lf_dec2 in Hin.
  pose proof (Z.div_pos k 10 ltac:(lia) ltac:(lia)) as Hq0.
  pose proof (Z.mod_pos_bound k 10 ltac:(lia)) as Hr.
  assert (Hd : k / 10 < 10) by (apply Z.div_lt_upper_bound; lia).
  destruct (k <? 10) eqn:E; cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [lia|]); destruct Hin.
Qed.

(* entry e is written at turn e + e / 15, which is before turn j when e is before the turn's count *)
Lemma gl_kof_lt : forall e j, 0 <= e -> 0 <= j < 64 -> e < j - j / 16 -> e + e / 15 < j.
Proof.
  intros e j He Hj H.
  pose proof (Z.div_pos e 15 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos j 16 ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* the turn's test +0x34c: `andi a0, s4, 0xf; beq a0, 0xf` with s4 = j *)
Lemma gl_br_skip : forall E j, ew E 34 = Z_to_bv 64 j -> 0 <= j < 64 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff 34 0) (SLit 15))) (sv_denot E (SLit 15)) = (j mod 16 =? 15).
Proof.
  intros E j H Hj. rewrite branch_eq_U, U_and_lit by lia.
  rewrite (U_atom E 34 j H) by lia. rewrite U_lit by lia.
  change (Z.land j 15) with (Z.land j (Z.ones 4)). rewrite Z.land_ones by lia. reflexivity.
Qed.

(* the back edge +0x3b4: `bnez s7` with s7 = 64 - j - 1 *)
Lemma gl_br_back : forall E j, ew E 23 = Z_to_bv 64 (64 - j) -> 0 <= j < 64 ->
  branch_taken BC_NE (sv_denot E (SOff 23 (-1))) (sv_denot E (SLit 0)) = negb (63 - j =? 0).
Proof.
  intros E j H Hj. rewrite branch_ne_U, (U_atom_off E 23 (64 - j) (-1) H) by lia. rewrite U_lit by lia.
  replace (64 - j + -1) with (63 - j) by lia. reflexivity.
Qed.

(* THE TWO PINS: the engine's expression for each table slot (+0x35c `add a0, a1, a0` with a1 = s2 + s11 and
   a0 = n_if << 3; +0x390 with a1 = s2 + s9 and a0 = n_if << 2) is the slot's own atom. *)
Lemma gl_pin_name : forall E nif, ew E 18 = Z_to_bv 64 LA_G_NL -> ew E 33 = Z_to_bv 64 nif ->
  ew E 35 = Z_to_bv 64 (gl_aname nif) -> 0 <= nif <= 60 ->
  sv_denot E (SAlu ALU_ADD (SOff 18 271024) (SAlu ALU_SLL (SOff 33 0) (SLit 3))) = sv_denot E (SOff 35 0).
Proof.
  intros E nif H18 H33 H35 Hn. rewrite !denot_lit_U. f_equal.
  rewrite U_SAlu, U_SAlu, U_SLit. cbn [zalu_raw].
  rewrite (U_atom_off E 18 LA_G_NL 271024 H18) by (unfold LA_G_NL; lia).
  rewrite (U_atom E 33 nif H33) by lia.
  rewrite (U_atom E 35 (gl_aname nif) H35) by (unfold gl_aname, LA_G_NL, NK_IF_NAME; lia).
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold zcanon, M64. rewrite (Z.mod_small (nif * 8)) by lia.
  rewrite Z.mod_small by (unfold LA_G_NL; lia). unfold gl_aname, NK_IF_NAME. lia.
Qed.

Lemma gl_pin_index : forall E nif, ew E 18 = Z_to_bv 64 LA_G_NL -> ew E 33 = Z_to_bv 64 nif ->
  ew E 36 = Z_to_bv 64 (gl_aidx nif) -> 0 <= nif <= 60 ->
  sv_denot E (SAlu ALU_ADD (SOff 18 271664) (SAlu ALU_SLL (SOff 33 0) (SLit 2))) = sv_denot E (SOff 36 0).
Proof.
  intros E nif H18 H33 H36 Hn. rewrite !denot_lit_U. f_equal.
  rewrite U_SAlu, U_SAlu, U_SLit. cbn [zalu_raw].
  rewrite (U_atom_off E 18 LA_G_NL 271664 H18) by (unfold LA_G_NL; lia).
  rewrite (U_atom E 33 nif H33) by lia.
  rewrite (U_atom E 36 (gl_aidx nif) H36) by (unfold gl_aidx, LA_G_NL, NK_IF_INDEX; lia).
  change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  unfold zcanon, M64. rewrite (Z.mod_small (nif * 4)) by lia.
  rewrite Z.mod_small by (unfold LA_G_NL; lia). unfold gl_aidx, NK_IF_INDEX. lia.
Qed.

(* the bytes the runs after the call may change: the slot at s1 + LS_ODD, g_nl.n_if and the two table slots *)
Definition gl_XW (sp1 nif a : Z) : Prop :=
  ~ (0 <= a < 2 ^ 64) \/ (sp1 + LS_ODD <= a < sp1 + LS_ODD + 8) \/
  (LA_G_NL + NK_N_IF <= a < LA_G_NL + NK_N_IF + 4) \/
  (gl_aname nif <= a < gl_aname nif + 8) \/ (gl_aidx nif <= a < gl_aidx nif + 4).

(* the bytes the turn may change at all: the snprintf destination and its window, and gl_XW *)
Definition gl_X (sp1 j nif a : Z) : Prop :=
  ~ (0 <= a < 2 ^ 64) \/
  (LA_G_NAMES + 8 * j <= a < LA_G_NAMES + 8 * j + 8) \/
  (sp1 - LINK_SNP_STK <= a < sp1) \/
  (sp1 + LS_ODD <= a < sp1 + LS_ODD + 8) \/
  (LA_G_NL + NK_N_IF <= a < LA_G_NL + NK_N_IF + 4) \/
  (gl_aname nif <= a < gl_aname nif + 8) \/ (gl_aidx nif <= a < gl_aidx nif + 4).

(* a byte outside g_names, g_nl, the snprintf window and the odd slot is outside gl_X *)
Definition gl_out (sp1 a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ ~ (LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE) /\
  ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE) /\
  ~ (sp1 - LINK_SNP_STK <= a < sp1) /\ ~ (sp1 + LS_ODD <= a < sp1 + LS_ODD + 8).

Lemma gl_out_X : forall sp1 j nif a, 0 <= j < 64 -> 0 <= nif <= 60 ->
  gl_out sp1 a -> ~ gl_X sp1 j nif a.
Proof.
  intros sp1 j nif a Hj Hn (H0 & H1 & H2 & H3 & H4).
  unfold gl_X, gl_aname, gl_aidx, LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE, NK_IF_NAME,
    NK_IF_INDEX, NK_N_IF in *. lia.
Qed.

(* a present byte is writable *)
Lemma gl_apresent_writable : forall segs (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> writable_at segs (mrestrict H m) a.
Proof. intros segs H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* a byte of the view, and the memory it comes from *)
Lemma gl_present_of_mbyte : forall segs (H : word -> bool) (mem : word -> option byte) a,
  mbyte segs (mrestrict H mem) a <> None ->
  apresent H mem a \/ seg_rom segs (Z_to_bv 64 a) <> None.
Proof.
  intros segs H mem a Hm. unfold mbyte, mrestrict in Hm.
  destruct (H (Z_to_bv 64 a)) eqn:EH; [right; exact Hm|].
  destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Em;
    [left; split; [exact EH | exists b; exact Em] | right; exact Hm].
Qed.
Lemma gl_mbyte_of_rom : forall segs (H : word -> bool) (mem : word -> option byte) a,
  seg_rom segs (Z_to_bv 64 a) <> None -> mbyte segs (mrestrict H mem) a <> None.
Proof.
  intros segs H mem a Hr. unfold mbyte, mrestrict.
  destruct (H (Z_to_bv 64 a)); [exact Hr|].
  destruct (mem (Z_to_bv 64 a)); [discriminate | exact Hr].
Qed.
Lemma gl_mbyte_of_apresent : forall segs (H : word -> bool) (mem : word -> option byte) a,
  apresent H mem a -> mbyte segs (mrestrict H mem) a <> None.
Proof.
  intros segs H mem a (Hh & b & Hb). unfold mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
Lemma gl_apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a Hg (Hh & b & Hb).
  assert (Hne : mrestrict H m (Z_to_bv 64 a) <> None)
    by (unfold mrestrict; rewrite Hh, Hb; discriminate).
  pose proof (Hg _ Hne) as H'. unfold mrestrict in H'. rewrite Hh in H'.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E';
    [split; [exact Hh | exists b'; exact E'] | exfalso; apply H'; reflexivity].
Qed.
Lemma gl_apresent_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m x = mrestrict H m' x) -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a He Hp. apply (gl_apresent_grows H m m' a); [|exact Hp].
  intros x Hx. rewrite <- He. exact Hx.
Qed.
Lemma gl_mbyte_of_aview : forall segs (H : word -> bool) (m : word -> option byte) a v,
  aview segs H m a = Some v -> mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
  intros segs H m a v Hv. unfold aview in Hv.
  destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:E; [|discriminate].
  cbn [option_map] in Hv. injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* denotations of the registers the turn leaves *)
Lemma gl_den_off0 : forall E n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma gl_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof.
  intros E z. rewrite denot_lit_U, U_SLit. apply Z_to_bv64_eq_mod.
  unfold zcanon, M64. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma gl_den_a7 : forall E b v, ew E 32 = Z_to_bv 64 b -> ew E 248 = Z_to_bv 64 v ->
  0 <= b < 2 ^ 64 -> 0 <= v -> v + 8 < 2 ^ 64 -> 0 <= b + (v + 8) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 248 8) (SLit 3)))
    = Z_to_bv 64 (b + (v + 8) / 8).
Proof.
  intros E b v H32 H248 Hb Hv Hv8 Hsum. rewrite denot_lit_U. f_equal.
  assert (Hd : 0 <= (v + 8) / 8) by (apply Z.div_pos; lia).
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 3) 63) with 3.
  rewrite (U_atom_off E 32 b 0 H32 ltac:(lia) ltac:(lia)).
  rewrite (U_atom_off E 248 v 8 H248 ltac:(lia) ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite Z.add_0_r.
  unfold zcanon, M64.
  rewrite ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* a run's frame extends the agreement of the memories off X, when X holds the run's windows *)
Lemma gl_kagree_step : forall segs E rs (m1 m2 m3 : word -> option byte) (X : Z -> Prop),
  kagree segs X m1 m2 -> frame_of E rs m2 m3 ->
  (forall a, ~ X a -> 0 <= a < 2 ^ 64) ->
  (forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a -> X a) ->
  kagree segs X m1 m3.
Proof.
  intros segs E rs m1 m2 m3 X H12 HF HX HW a Ha.
  rewrite <- (H12 a Ha). unfold mbyte. pose proof (HX a Ha) as Hr.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros Hin. exact (Ha (HW a Hr Hin)).
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
(* the journal's window is present *)
Lemma gl_aj_present : forall segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR segs B lyc Sc W memc mdc /\ (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
  intros segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (HSTK & HXO & (memS & HJ & _) & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  split; [exact HAR|]. intros a Ha. apply Hpres. lia.
Qed.

#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

#[local] Notation FROM POST GI :=
  (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Notation GL j := (lf_gl_inv B MT MS la_nul j).
#[local] Notation OL j := (lf_ol_inv B MT MS la_nul j).

(* the image instance's facts, as every walk of this slice takes them *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis LV : LinkVals.
Hypothesis HSEGS : pa_segs = AB1v.tfibsegs.
(* snprintf (lib/A/Rt/LinkSnpDef.v), at every FP state the loop reaches: lib/A/Rt/LinkSnp.v `link_snprintf`
   discharges it (it holds at any FP state); lib/A/Prog/LLVMFuzzerTestOneInputSnp.v `lf_snp_at` applies it at
   the g_names site. *)
Hypothesis SNP : forall fy : YK11.FPState,
  @asnprintf_link_realizes fy rc SEGS B PCAP_RLO PCAP_RHI LA_W_SNPRINTF.

Lemma gl_vals : VAL (A_OBJ 1) = LA_GOT_SHADOW /\ VAL (A_OBJ 64) = LA_SHADOW_CELL /\ BASE = link_text.
Proof.
  split; [rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity | exact (lv_text LV)].
Qed.

(* the realigned stack pointer lies high on the real stack and is 32-aligned *)
Lemma gl_sp1 : forall (cx : lcx) (fp k2 : Z) ly3 S3 (W3 : world SEGS) (memc : word -> option byte) md3,
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 memc md3 k2 ->
  2 ^ 46 <= lf_sp1 cx /\ lf_sp1 cx + 256 <= 2 ^ 47 /\ lf_sp1 cx mod 32 = 0 /\ lf_sp1 cx mod 16 = 0 /\
  lf_sp1 cx + 416 <= spZ (c_regs cx) /\ spZ (c_regs cx) - LLVMF_STK <= lf_sp1 cx - LINK_SNP_STK.
Proof.
intros cx fp k2 ly3 S3 W3 memc md3 HJ.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
rewrite !Z.add_0_r in Hsp0al, Hslo, Hshi.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
unfold lf_sp1.
pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME; lia) Hsp0al) as (Hr1 & Hr2 & Hr3).
unfold LF_MFRAME, LLVMF_STK, LINK_SNP_STK, ESTACK in *.
repeat split; lia.
Qed.

(* THE ENTRY STATE of a turn: the invariant's registers are the engine's atoms, the shadow base is the
   slot's word. *)
Lemma gl_entry : forall (cx : lcx) (fy : YK11.FPState) (j : Z) (W3 : world SEGS) (ms3 : machine_state),
  0 <= j < 64 ->
  2 ^ 46 <= lf_sp1 cx -> lf_sp1 cx + 256 <= 2 ^ 47 -> lf_sp1 cx mod 32 = 0 ->
  lf_core cx ms3 ->
  getr (ms_regs ms3) 24 = w64 (j + 2) ->
  lf_slot cx W3 ms3 LS_SHB SHADOW_OFF ->
  st_ok_pi (fx := fy) SEGS VAL (Eimg (Ereg (ms_regs ms3) (GL_EXTRA j))) GL_SS
    (restrict (w_H W3) (@YK11.mkst fy (ms_regs ms3) (w64 (BASE + LF_gl)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
intros cx fy j W3 ms3 Hj Hlo Hhi Hal HCORE R24 HSHB.
pose proof HCORE as (R2 & R8 & R9 & R3 & R4).
set (E := Eimg (Ereg (ms_regs ms3) (GL_EXTRA j))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) (GL_EXTRA j)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = w64 (lf_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx)
  by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = Z_to_bv 64 j)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 2)).
assert (HS0 : st_ok_pi (fx := fy) SEGS VAL E GL_SS0
    (restrict (w_H W3) (@YK11.mkst fy (ms_regs ms3) (w64 (BASE + LF_gl)) (ms_mem ms3) (seg_rom SEGS)))).
{
rewrite restrict_mkst_fx. unfold GL_SS0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold GL_SHB_R.
  apply Forall_cons; [|apply Forall_nil]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. fold E. rewrite U9.
  split; [unfold LS_SHB; lia|]. split; [unfold LS_SHB; lia|].
  split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (lf_sp1 cx) LS_SHB 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SB; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
    | change (Z.of_N 8) with 8; lia |].
  rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HSHB).
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]].
  cbn [GL_FACTS f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E32, E34, U9.
  rewrite !unsigned_lit_small by (unfold SB; lia).
  repeat match goal with |- _ /\ _ => split end; first [exact I | unfold SB; lia].
}
exact (st_ok_pi_set_reg E GL_SS0 _ (24%bv) (SOff 34 2) HS0 ltac:(cbv; discriminate)
         ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite R24, E34;
               rewrite unsigned_lit_small by lia; reflexivity)).
Qed.

(* the writable image objects the turn touches, at any memory *)
Lemma gl_gnl_w : forall (m : word -> option byte) a,
  LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS m a.
Proof.
  intros m a Ha. pose proof (LA_G_NL_writable m a ltac:(unfold NK_SIZE in Ha; lia)) as Hw.
  rewrite <- HSEGS in Hw. exact Hw.
Qed.
Lemma gl_gnames_w : forall (m : word -> option byte) a,
  LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> writable_at SEGS m a.
Proof.
  intros m a Ha. pose proof (LA_G_NAMES_writable m a ltac:(unfold G_NAMES_SIZE in Ha; lia)) as Hw.
  rewrite <- HSEGS in Hw. exact Hw.
Qed.

(* THE STATE AT SNPRINTF'S RETURN (+0x344): the two table slots are atoms of their own (35, 36) *)
Lemma gl_mid : forall (fy : YK11.FPState) (cx : lcx) (W : world SEGS) (regs : bvmap 5 word) mem (nif j wa : Z),
  0 <= j < 64 -> 0 <= nif <= 60 -> 0 <= wa < 2 ^ 64 ->
  2 ^ 46 <= lf_sp1 cx -> lf_sp1 cx + 256 <= 2 ^ 47 -> lf_sp1 cx mod 32 = 0 ->
  getr regs 9 = w64 (lf_sp1 cx) -> getr regs 20 = w64 j -> getr regs 24 = w64 (j + 2) ->
  getr regs 25 = w64 0x42530 -> getr regs 26 = w64 (LA_G_NL + 0x42000) -> getr regs 27 = w64 0x422b0 ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_SHB) = Some SHADOW_OFF ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_WA) = Some wa ->
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_N_IF) 4 nif ->
  (forall i, 0 <= i < 8 -> writable_at SEGS (rdW W mem) (lf_sp1 cx + LS_ODD + i)) ->
  st_ok_pi (fx := fy) SEGS VAL (Eimg (Ereg regs (GL2_EXTRA nif j wa))) GL2_SS
    (restrict (w_H W) (@YK11.mkst fy regs (w64 (BASE + LF_sn_ra)) mem (seg_rom SEGS))).
Proof.
intros fy cx W regs mem nif j wa Hj Hnif Hwa Hlo Hhi Hal R9 R20 R24 R25 R26 R27 MSHB MWA MNIF MO50.
set (E := Eimg (Ereg regs (GL2_EXTRA nif j wa))).
assert (EA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; exact (ew_Eimg_Ereg_nat regs _ n r Hn)).
assert (EX : forall k, (k < 6)%nat -> ew E (32 + k) = nth k (GL2_EXTRA nif j wa) (Z_to_bv 64 0)).
{ intros k Hk. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia).
  do 6 (destruct k as [|k]; [exact (ew_Ereg_extra regs _ _)|]). lia. }
assert (E9 : ew E 9 = w64 (lf_sp1 cx)) by (rewrite (EA 9%nat 9%bv eq_refl); exact R9).
assert (E26 : ew E 26 = w64 (LA_G_NL + 0x42000)) by (rewrite (EA 26%nat 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 nif) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 j) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (gl_aname nif)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (gl_aidx nif)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 wa) by exact (EX 5%nat ltac:(lia)).
assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx)
  by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = LA_G_NL + 0x42000)
  by (rewrite E26; unfold w64; apply unsigned_lit_small; unfold LA_G_NL; lia).
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = nif) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = j) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = gl_aname nif)
  by (rewrite E35; apply unsigned_lit_small; unfold gl_aname, LA_G_NL, NK_IF_NAME; lia).
assert (U36 : bv_unsigned (ew E 36) = gl_aidx nif)
  by (rewrite E36; apply unsigned_lit_small; unfold gl_aidx, LA_G_NL, NK_IF_INDEX; lia).
assert (U37 : bv_unsigned (ew E 37) = wa) by (rewrite E37; apply unsigned_lit_small; lia).
assert (HS0 : st_ok_pi (fx := fy) SEGS VAL E GL2_SS0
    (restrict (w_H W) (@YK11.mkst fy regs (w64 (BASE + LF_sn_ra)) mem (seg_rom SEGS)))).
{
rewrite restrict_mkst_fx. unfold GL2_SS0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold GL2_MEM.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
    [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]];
    unfold region_ok, GL_SHB_R, GL_WA_R, GL_O50_R, GL_NIF_R, GL_NAME_R, GL_IDX_R;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold E.
  + rewrite U9. split; [unfold LS_SHB; lia|]. split; [unfold LS_SHB; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (lf_sp1 cx) LS_SHB 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SB; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
      | change (Z.of_N 8) with 8; lia |].
    rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ MSHB).
  + rewrite U9. split; [unfold LS_WA; lia|]. split; [unfold LS_WA; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (lf_sp1 cx) LS_WA 8 (SOff 37 0) wa);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
      | change (Z.of_N 8) with 8; lia |].
    exact (val_mem_of_rdword SEGS (w_H W) mem _ _ MWA).
  + rewrite U9. split; [unfold LS_ODD; lia|]. split; [unfold LS_ODD; lia|].
    split; [|apply Forall_nil].
    intros o Ho. replace (lf_sp1 cx + o) with (lf_sp1 cx + LS_ODD + (o - LS_ODD)) by lia.
    apply MO50. unfold LS_ODD in *. lia.
  + rewrite U26. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
    split; [intros o Ho; apply gl_gnl_w; unfold LA_G_NL, NK_SIZE; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (LA_G_NL + 0x42000) 0x670 4 (SOff 33 0) nif);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
      | change (Z.of_N 4) with 4; lia |].
    replace (LA_G_NL + 0x42000 + 0x670) with (LA_G_NL + NK_N_IF) by (unfold NK_N_IF; lia).
    change (N.to_nat 4) with 4%nat. exact MNIF.
  + rewrite U35. split; [unfold gl_aname, LA_G_NL, NK_IF_NAME; lia|].
    split; [unfold gl_aname, LA_G_NL, NK_IF_NAME; lia|].
    split; [|apply Forall_nil].
    intros o Ho. apply gl_gnl_w. unfold gl_aname, NK_IF_NAME, NK_SIZE. lia.
  + rewrite U36. split; [unfold gl_aidx, LA_G_NL, NK_IF_INDEX; lia|].
    split; [unfold gl_aidx, LA_G_NL, NK_IF_INDEX; lia|].
    split; [|apply Forall_nil].
    intros o Ho. apply gl_gnl_w. unfold gl_aidx, NK_IF_INDEX, NK_SIZE. lia.
- apply pairwise_disjoint_of_extents.
  unfold GL2_MEM, GL_SHB_R, GL_WA_R, GL_O50_R, GL_NIF_R, GL_NAME_R, GL_IDX_R, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U26, U35, U36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold LS_SHB, LS_WA, LS_ODD, gl_aname, gl_aidx, LA_G_NL, NK_IF_NAME, NK_IF_INDEX.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [GL2_FACTS f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite U9, U26, U32, U33, U34, U35, U36.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 2) with 4.
  rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  unfold gl_aname, gl_aidx, LA_G_NL, NK_IF_NAME, NK_IF_INDEX, SB.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
}
pose proof (st_ok_pi_set_reg E GL2_SS0 _ (20%bv) (SOff 34 0) HS0 ltac:(cbv; discriminate)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite R20, E34;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS1.
pose proof (st_ok_pi_set_reg E _ _ (24%bv) (SOff 34 2) HS1 ltac:(cbv; discriminate)
  ltac:(cbn [sv_denot ms_regs restrict mkst ss_regs ss_pc ss_mem ss_resv ss_facts]; rewrite R24, E34;
        rewrite unsigned_lit_small by lia; reflexivity)) as HS2.
pose proof (st_ok_pi_set_reg E _ _ (25%bv) (SLit 0x42530) HS2 ltac:(cbv; discriminate)
  ltac:(cbn [sv_denot ms_regs restrict mkst ss_regs ss_pc ss_mem ss_resv ss_facts]; rewrite R25;
        reflexivity)) as HS3.
exact (st_ok_pi_set_reg E _ _ (27%bv) (SLit 0x422b0) HS3 ltac:(cbv; discriminate)
  ltac:(cbn [sv_denot ms_regs restrict mkst ss_regs ss_pc ss_mem ss_resv ss_facts]; rewrite R27;
        reflexivity)).
Qed.

(* ==========================================================================
   THE TURN'S DATA: g_nl's interface table and g_names after the turn
   ========================================================================== *)

Lemma gl_mem_next : forall (m0 m3 : word -> option byte) (sp1 j nif : Z) (app : bool) (kbs : list byte),
  0 <= j < 64 -> nif = j - j / 16 -> app = negb (j mod 16 =? 15) -> 2 ^ 46 <= sp1 ->
  kagree SEGS (gl_X sp1 j nif) m0 m3 ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> mbyte SEGS m3 a <> None) ->
  (forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> mbyte SEGS m3 a <> None) ->
  (forall i, 0 <= i <= Z.of_nat (length (lf_gname_z j)) ->
     mbyte SEGS m3 (LA_G_NAMES + 8 * j + i) =
       Some (Z_to_bv 8 (nth (Z.to_nat i) (lf_gname_z j ++ [0]) 0))) ->
  val_mem SEGS m3 (LA_G_NL + NK_N_IF) 4 (if app then nif + 1 else nif) ->
  (app = true -> val_mem SEGS m3 (gl_aname nif) 8 (LA_G_NAMES + 8 * j)) ->
  (app = true -> val_mem SEGS m3 (gl_aidx nif) 4 (j + 2)) ->
  nk_n_if kbs = Z.of_nat (length (lf_tab_at nif)) ->
  aiftab_at SEGS m0 LA_G_NL kbs (lf_tab_at nif) ->
  lf_ifp m0 nif ->
  (forall q, 0 <= q < NK_SIZE -> ~ (NK_IF_NAME <= q < NK_IF_NAME + 640) ->
     ~ (NK_IF_INDEX <= q < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= q < NK_N_IF + 4) ->
     val_mem SEGS m0 (LA_G_NL + q) 1 0) ->
  lf_gnames_at j m0 ->
  exists kbs' : list byte,
    anlk_at SEGS m3 LA_G_NL kbs' /\
    nk_n_if kbs' = Z.of_nat (length (lf_tab_at (j + 1 - (j + 1) / 16))) /\
    aiftab_at SEGS m3 LA_G_NL kbs' (lf_tab_at (j + 1 - (j + 1) / 16)) /\
    lf_ifp m3 (j + 1 - (j + 1) / 16) /\
    (forall q, 0 <= q < NK_SIZE -> ~ (NK_IF_NAME <= q < NK_IF_NAME + 640) ->
       ~ (NK_IF_INDEX <= q < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= q < NK_N_IF + 4) ->
       val_mem SEGS m3 (LA_G_NL + q) 1 0) /\
    lf_gnames_at (j + 1) m3 /\ lf_gnames_w m3.
Proof.
intros m0 m3 sp1 j nif app kbs Hj Hnif Happ Hsp HK HPNL HPGN HBY HN HNAME HIDX
  HNIF HTAB HIFP HZERO HGN.
pose proof (lf_cnt_range j Hj) as Hcr.
pose proof (lf_gname_z_len j ltac:(lia)) as HL.
assert (Hn' : j + 1 - (j + 1) / 16 = (if app then nif + 1 else nif)).
{ rewrite Happ. destruct (j mod 16 =? 15) eqn:E; cbn [negb].
  - apply Z.eqb_eq in E. rewrite Hnif. apply lf_cnt_step_skip; [lia | exact E].
  - apply Z.eqb_neq in E. rewrite Hnif. apply lf_cnt_step_keep; [lia | exact E]. }
rewrite Hn'.
set (n' := (if app then nif + 1 else nif)) in *.
assert (Happ0 : app = true -> j mod 16 <> 15).
{ intros Ha. rewrite Ha in Happ. destruct (j mod 16 =? 15) eqn:E; [discriminate Happ|].
  apply Z.eqb_neq. exact E. }
assert (Hn'r : 0 <= n' <= 60).
{ unfold n'. destruct app eqn:Ea; [|lia]. pose proof (Happ0 eq_refl) as H15. rewrite Hnif. lia. }
assert (Hnle : nif <= n') by (unfold n'; destruct app; lia).
(* ---- g_nl's bytes after the turn ---- *)
set (kbs' := abytes_of SEGS m3 LA_G_NL (Z.to_nat NK_SIZE)).
assert (HB3 : abytes SEGS m3 LA_G_NL kbs').
{ apply abytes_of_abytes; [unfold LA_G_NL; lia
  | rewrite Z2Nat.id by (unfold NK_SIZE; lia); unfold LA_G_NL, NK_SIZE; lia |].
  intros i Hi. destruct (mbyte SEGS m3 (LA_G_NL + Z.of_nat i)) as [b|] eqn:Eb; [exists b; reflexivity|].
  exfalso. apply (HPNL (LA_G_NL + Z.of_nat i)); [unfold NK_SIZE in *; lia | exact Eb]. }
assert (HKL : Z.of_nat (length kbs') = NK_SIZE)
  by (unfold kbs'; rewrite abytes_of_length; apply Z2Nat.id; unfold NK_SIZE; lia).
assert (HANL : anlk_at SEGS m3 LA_G_NL kbs').
{ split; [split; [exact HB3|] | exact HKL].
  rewrite HKL. intros i Hi. apply gl_gnl_w. lia. }
assert (FLD : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= NK_SIZE ->
    0 <= v < 2 ^ (8 * Z.of_nat n) -> val_mem SEGS m3 (LA_G_NL + off) n v ->
    rdn kbs' off (Z.of_nat n) = v).
{ intros off n v H0 H1 Hv HV.
  apply (rdn_of_vals _ off n v H0);
    [unfold kbs'; rewrite abytes_of_length; unfold NK_SIZE in *; lia | exact Hv |].
  intros k Hk. unfold kbs'. apply abytes_of_nth; [unfold NK_SIZE in *; lia|].
  replace (LA_G_NL + Z.of_nat (Z.to_nat off + k)) with (LA_G_NL + off + Z.of_nat k) by lia.
  exact (HV k Hk). }
assert (HLEN' : length (lf_tab_at n') = Z.to_nat n').
{ pose proof (lf_tab_at_len (Z.to_nat n') ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. exact H. }
assert (HNIF' : nk_n_if kbs' = n').
{ unfold nk_n_if, fld_u32.
  exact (FLD NK_N_IF 4%nat n' ltac:(unfold NK_N_IF; lia) ltac:(unfold NK_N_IF, NK_SIZE; lia)
           ltac:(cbn [Z.of_nat]; change (2 ^ (8 * 4)) with (2 ^ 32); lia) HN). }
assert (HNIFZ : nk_n_if kbs' = Z.of_nat (length (lf_tab_at n'))) by (rewrite HNIF', HLEN'; lia).
assert (Hpre : forall k, (k < Z.to_nat nif)%nat ->
    nth_error (lf_tab_at n') k = nth_error (lf_tab_at nif) k).
{ intros k Hk. unfold lf_tab_at. rewrite !gl_nth_firstn by lia. reflexivity. }
(* ---- the entries of the table the turn leaves alone ---- *)
assert (HOLD : forall i nm ix, (i < Z.to_nat nif)%nat -> nth_error (lf_tab_at nif) i = Some (nm, ix) ->
    0 <= ix < 2 ^ 31 /\
    exists p, au64_at SEGS m3 (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p /\ p <> 0 /\
              acstr_at SEGS m3 p nm /\ au32_at SEGS m3 (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat i) ix).
{ intros i nm ix Hlt Hi.
  destruct HTAB as (_ & _ & HT). destruct (HT i nm ix Hi) as (Hix & p & Hp & Hp0 & Hs & Hidx).
  destruct (HIFP (Z.of_nat i) ltac:(lia)) as (q & Hq & Hq1 & _).
  assert (Hqv : q = LA_G_NAMES + 8 * (Z.of_nat i + Z.of_nat i / 15)) by (apply Hq1; lia).
  assert (Hkk : Z.of_nat i + Z.of_nat i / 15 < j) by (apply gl_kof_lt; lia).
  assert (Hk0 : 0 <= Z.of_nat i + Z.of_nat i / 15)
    by (pose proof (Z.div_pos (Z.of_nat i) 15 ltac:(lia) ltac:(lia)); lia).
  pose proof Hs as ((Hp0' & Hplen & _) & _). rewrite length_app in Hplen. cbn [length] in Hplen.
  assert (Hpq : p = q).
  { pose proof (val_mem8_mod SEGS m0 _ p q Hp Hq) as Hm.
    rewrite (Z.mod_small p) in Hm by lia.
    rewrite (Z.mod_small q) in Hm by (rewrite Hqv; unfold LA_G_NAMES; lia). exact Hm. }
  assert (Hi2 : nth_error lf_tab i = Some (nm, ix))
    by (unfold lf_tab_at in Hi; rewrite <- (gl_nth_firstn lf_tab (Z.to_nat nif) i ltac:(lia)); exact Hi).
  pose proof (lf_tab_entry i nm ix Hi2) as (_ & H4 & _).
  assert (Hnm4 : (length nm <= 4)%nat) by (apply H4; lia).
  split; [exact Hix|]. exists p. split.
  - apply (au64_keep SEGS _ m0 m3 _ p HK); [|exact Hp].
    intros k Hk8. unfold gl_X, gl_aname, gl_aidx, LA_G_NL, LA_G_NAMES, NK_IF_NAME, NK_IF_INDEX,
      NK_N_IF, LINK_SNP_STK, ESTACK, LS_ODD. lia.
  - split; [exact Hp0|]. split.
    + apply (acstr_keep SEGS _ m0 m3 p nm HK); [|exact Hs].
      intros k Hk8. rewrite Hpq, Hqv.
      unfold gl_X, gl_aname, gl_aidx, LA_G_NL, LA_G_NAMES, NK_IF_NAME, NK_IF_INDEX, NK_N_IF,
        LINK_SNP_STK, ESTACK, LS_ODD. lia.
    + apply (au32_keep SEGS _ m0 m3 _ ix HK); [|exact Hidx].
      intros k Hk4. unfold gl_X, gl_aname, gl_aidx, LA_G_NL, LA_G_NAMES, NK_IF_NAME, NK_IF_INDEX,
        NK_N_IF, LINK_SNP_STK, ESTACK, LS_ODD. lia. }
(* ---- the entry the appending turn writes ---- *)
assert (HNEW : app = true ->
    nif + nif / 15 = j /\
    nth_error (lf_tab_at n') (Z.to_nat nif) = Some (lf_gname j, j + 2) /\
    au64_at SEGS m3 (LA_G_NL + NK_IF_NAME + 8 * nif) (LA_G_NAMES + 8 * j) /\
    acstr_at SEGS m3 (LA_G_NAMES + 8 * j) (lf_gname j) /\
    au32_at SEGS m3 (LA_G_NL + NK_IF_INDEX + 4 * nif) (j + 2)).
{ intros Ha. pose proof (Happ0 Ha) as H15.
  assert (Hnif60 : nif < 60) by (rewrite Hnif; lia).
  assert (Hkof : lf_k_of (Z.to_nat nif) = Z.to_nat j) by (rewrite Hnif; apply lf_k_of_of; lia).
  assert (Hkj : nif + nif / 15 = j).
  { unfold lf_k_of in Hkof. apply (f_equal Z.of_nat) in Hkof.
    rewrite Nat2Z.inj_add, Nat2Z.inj_div in Hkof.
    rewrite !Z2Nat.id in Hkof by lia. change (Z.of_nat 15) with 15 in Hkof. exact Hkof. }
  assert (Htabn : nth_error lf_tab (Z.to_nat nif) = Some (lf_gname j, j + 2)).
  { rewrite (lf_tab_nth_g (Z.to_nat nif) ltac:(lia)), Hkof, Z2Nat.id by lia. reflexivity. }
  pose proof (lf_tab_at_len (Z.to_nat nif) ltac:(lia)) as Hl. rewrite Z2Nat.id in Hl by lia.
  split; [exact Hkj|]. split.
  { assert (Hn'eq : n' = Z.of_nat (Z.to_nat nif) + 1) by (unfold n'; rewrite Ha; lia).
    rewrite Hn'eq, (lf_tab_at_succ (Z.to_nat nif) (lf_gname j, j + 2) ltac:(lia)).
    rewrite (Z2Nat.id nif) by lia.
    rewrite nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. cbn [nth_error].
    rewrite (gl_nth_of_error lf_tab (Z.to_nat nif) _ (lf_gname j, j + 2) Htabn). reflexivity. }
  split; [replace (LA_G_NL + NK_IF_NAME + 8 * nif) with (gl_aname nif) by (unfold gl_aname; lia);
          exact (HNAME Ha)|].
  split.
  { split; [|apply gl_gname_nz; lia].
    assert (Hlen8 : length (lf_gname j ++ [zb 0]) = S (length (lf_gname_z j)))
      by (rewrite length_app; cbn [length]; unfold lf_gname; rewrite length_map; lia).
    split; [unfold LA_G_NAMES; lia|].
    rewrite Hlen8.
    split; [unfold LA_G_NAMES; lia|].
    intros i Hi.
    replace (lf_gname j ++ [zb 0]) with (map (fun z : Z => Z_to_bv 8 z) (lf_gname_z j ++ [0]))
      by (unfold lf_gname; rewrite map_app; reflexivity).
    rewrite gl_nth_map by (rewrite length_app; cbn [length]; lia).
    rewrite (HBY (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity. }
  replace (LA_G_NL + NK_IF_INDEX + 4 * nif) with (gl_aidx nif) by (unfold gl_aidx; lia).
  exact (HIDX Ha). }
exists kbs'. split; [exact HANL|]. split; [exact HNIFZ|].
split.
{ split; [exact HNIFZ|]. split; [rewrite HLEN'; lia|].
  intros i nm ix Hi.
  assert (Hib : (i < length (lf_tab_at n'))%nat)
    by (apply nth_error_Some; rewrite Hi; discriminate).
  rewrite HLEN' in Hib.
  destruct (lt_dec i (Z.to_nat nif)) as [Hlt | Hge].
  - rewrite (Hpre i Hlt) in Hi. exact (HOLD i nm ix Hlt Hi).
  - assert (Ha : app = true) by (unfold n' in Hib; destruct app; [reflexivity | lia]).
    assert (Hieq : i = Z.to_nat nif) by (unfold n' in Hib; rewrite Ha in Hib; lia).
    subst i. destruct (HNEW Ha) as (Hkj & Htn & HNm & HSt & HIx).
    rewrite Htn in Hi. injection Hi as <- <-.
    split; [lia|]. exists (LA_G_NAMES + 8 * j). rewrite Z2Nat.id by lia.
    split; [exact HNm|]. split; [unfold LA_G_NAMES; lia|]. split; [exact HSt | exact HIx]. }
split.
{ intros e He.
  destruct (Z.lt_ge_cases e nif) as [Hlt | Hge].
  - destruct (HIFP e ltac:(lia)) as (q & Hq & Hq1 & Hq2).
    assert (Hqv : q = LA_G_NAMES + 8 * (e + e / 15)) by (apply Hq1; lia).
    assert (Hkk : e + e / 15 < j) by (apply gl_kof_lt; lia).
    exists q. split; [|split; [exact Hq1 | intros H60; lia]].
    apply (au64_keep SEGS _ m0 m3 _ q HK); [|exact Hq].
    intros k Hk8. unfold gl_X, gl_aname, gl_aidx, LA_G_NL, LA_G_NAMES, NK_IF_NAME, NK_IF_INDEX,
      NK_N_IF, LINK_SNP_STK, ESTACK, LS_ODD. lia.
  - assert (Ha : app = true) by (unfold n' in He; destruct app; [reflexivity | lia]).
    assert (Heq : e = nif) by (unfold n' in He; rewrite Ha in He; lia).
    subst e. destruct (HNEW Ha) as (Hkj & _ & HNm & _ & _).
    exists (LA_G_NAMES + 8 * j).
    split; [exact HNm|]. split; [intros _; rewrite Hkj; reflexivity | intros H60; lia]. }
split.
{ intros q Hq H1 H2 H3.
  apply (val_mem_keep SEGS _ m0 m3 _ 1%nat 0 HK); [|exact (HZERO q Hq H1 H2 H3)].
  intros k Hk. unfold gl_X, gl_aname, gl_aidx, LA_G_NL, LA_G_NAMES, NK_IF_NAME, NK_IF_INDEX,
    NK_N_IF, NK_SIZE, LINK_SNP_STK, ESTACK, LS_ODD in *. lia. }
split.
{ intros k Hk.
  destruct (Z.lt_ge_cases k j) as [Hlt | Hge].
  - destruct (HGN k ltac:(lia)) as (rest & Hb & Hlen). exists rest. split; [|exact Hlen].
    apply (abytes_keep SEGS _ m0 m3 _ _ HK); [|exact Hb].
    intros i Hi. rewrite Hlen in Hi.
    unfold gl_X, gl_aname, gl_aidx, LA_G_NL, LA_G_NAMES, NK_IF_NAME, NK_IF_INDEX, NK_N_IF,
      LINK_SNP_STK, ESTACK, LS_ODD. lia.
  - assert (Hkj : k = j) by lia. subst k.
    set (B8 := abytes_of SEGS m3 (LA_G_NAMES + 8 * j) 8).
    assert (HB8 : abytes SEGS m3 (LA_G_NAMES + 8 * j) B8).
    { apply abytes_of_abytes; [unfold LA_G_NAMES; lia | cbn [Z.of_nat]; unfold LA_G_NAMES; lia |].
      intros i Hi. destruct (mbyte SEGS m3 (LA_G_NAMES + 8 * j + Z.of_nat i)) as [b|] eqn:Eb;
        [exists b; reflexivity|].
      exfalso. apply (HPGN (LA_G_NAMES + 8 * j + Z.of_nat i));
        [unfold G_NAMES_SIZE; lia | exact Eb]. }
    assert (HB8l : length B8 = 8%nat) by (unfold B8; apply abytes_of_length).
    assert (HLgz : length (lf_gname j) = length (lf_gname_z j)) by (unfold lf_gname; apply length_map).
    assert (HF : firstn (S (length (lf_gname j))) B8 = lf_gname j ++ [zb 0]).
    { apply lw_list_ext.
      - rewrite length_firstn, HB8l, length_app. cbn [length]. lia.
      - intros i Hi. rewrite length_firstn, HB8l in Hi.
        rewrite gl_nth_firstn by lia.
        replace (lf_gname j ++ [zb 0]) with (map (fun z : Z => Z_to_bv 8 z) (lf_gname_z j ++ [0]))
          by (unfold lf_gname; rewrite map_app; reflexivity).
        rewrite gl_nth_map by (rewrite length_app; cbn [length]; lia).
        unfold B8. apply abytes_of_nth; [lia|].
        rewrite (HBY (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity. }
    exists (skipn (S (length (lf_gname j))) B8).
    assert (HEq : lf_gname j ++ Z_to_bv 8 0 :: skipn (S (length (lf_gname j))) B8 = B8).
    { replace (lf_gname j ++ Z_to_bv 8 0 :: skipn (S (length (lf_gname j))) B8)
        with ((lf_gname j ++ [zb 0]) ++ skipn (S (length (lf_gname j))) B8)
        by (rewrite <- app_assoc; reflexivity).
      rewrite <- HF. apply firstn_skipn. }
    rewrite HEq. split; [exact HB8 | exact HB8l]. }
exists (abytes_of SEGS m3 LA_G_NAMES (Z.to_nat G_NAMES_SIZE)).
split; [rewrite abytes_of_length; apply Z2Nat.id; unfold G_NAMES_SIZE; lia|].
split.
- apply abytes_of_abytes; [unfold LA_G_NAMES; lia
  | rewrite Z2Nat.id by (unfold G_NAMES_SIZE; lia); unfold LA_G_NAMES, G_NAMES_SIZE; lia |].
  intros i Hi. destruct (mbyte SEGS m3 (LA_G_NAMES + Z.of_nat i)) as [b|] eqn:Eb;
    [exists b; reflexivity|].
  exfalso. apply (HPGN (LA_G_NAMES + Z.of_nat i)); [unfold G_NAMES_SIZE in *; lia | exact Eb].
- rewrite abytes_of_length, Z2Nat.id by (unfold G_NAMES_SIZE; lia).
  intros i Hi. apply gl_gnames_w. lia.
Qed.

(* ==========================================================================
   THE TURN'S FRAME: the clauses of lf_setup_inv the turn leaves alone
   ========================================================================== *)

Lemma gl_la_w : forall (m : word -> option byte) a,
  LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 304 -> writable_at SEGS m a.
Proof.
  intros m a Ha.
  pose proof (writable_at_of_wseg AB1v.tfibsegs m LA_LONG_ALIAS 304 ltac:(unfold LA_LONG_ALIAS; lia)
    ltac:(unfold LA_LONG_ALIAS; lia) ltac:(vm_compute; reflexivity) a Ha) as Hw.
  rewrite <- HSEGS in Hw. exact Hw.
Qed.

(* a read-only byte is neither in g_names nor in g_nl nor on the stack *)
Lemma gl_ro_out : forall sp1 a, 2 ^ 46 <= sp1 -> in_roP SEGS PCAP_RLO PCAP_RHI a -> gl_out sp1 a.
Proof.
  intros sp1 a Hro0 Hro. pose proof (in_roP_low a Hro) as Hlow. unfold kLowMemEnd in Hlow.
  split; [lia|].
  split; [|split; [|split; [unfold LINK_SNP_STK, ESTACK; lia | unfold LS_ODD; lia]]].
  - intros Hc. apply (LA_G_not_ro a); [|rewrite <- HSEGS; exact Hro].
    apply (inG_of_In LA_G LA_G_NAMES 512 a); [cbn [LA_G In]; right; right; left; reflexivity|].
    unfold G_NAMES_SIZE in Hc. lia.
  - intros Hc. apply (LA_G_not_ro a); [|rewrite <- HSEGS; exact Hro].
    apply (inG_of_In LA_G LA_G_NL 271992 a); [cbn [LA_G In]; right; left; reflexivity|].
    unfold NK_SIZE in Hc. lia.
Qed.

Lemma gl_setup_keep : forall (cx : lcx) (fp k2 : Z) (j nif : Z) ly3 S3 T3
    (W3 : world SEGS) (ms3 ms' : machine_state) (md3 md' : Model),
  0 <= j < 64 -> 0 <= nif <= 60 ->
  2 ^ 46 <= lf_sp1 cx -> lf_sp1 cx + 256 <= 2 ^ 47 ->
  lf_sp1 cx + 416 <= spZ (c_regs cx) ->
  alloc_ceiling <= spZ (c_regs cx) - LLVMF_STK ->
  spZ (c_regs cx) - LLVMF_STK <= lf_sp1 cx - LINK_SNP_STK ->
  4096 <= lf_F cx fp -> lf_F cx fp + 1024 <= alloc_ceiling -> off_img (lf_F cx fp) 1024 ->
  la_nul = LA_NUL ->
  (forall a, amf_fp MS T3 a -> gl_out (lf_sp1 cx) a) ->
  (forall a, c_p cx <= a < c_p cx + c_n cx -> gl_out (lf_sp1 cx) a) ->
  kagree SEGS (gl_X (lf_sp1 cx) j nif) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slot cx W3 ms3 LS_SHB SHADOW_OFF -> lf_slot cx W3 ms3 LS_FK (lf_F cx fp) ->
  lf_slot cx W3 ms3 LS_F (lf_F cx fp) -> lf_slot cx W3 ms3 LS_F0 (lf_F cx fp) ->
  lf_slot cx W3 ms3 LS_WA (lf_F cx fp + LO_WA) ->
  lf_slot cx W3 ms3 LS_B160 (lf_F cx fp + LO_B160) ->
  lf_slot cx W3 ms3 LS_B1A0 (lf_F cx fp + LO_B1A0) ->
  lf_slot cx W3 ms3 LS_B2E0 (lf_F cx fp + LO_B2E0) ->
  lf_slot cx W3 ms3 LS_B330 (lf_F cx fp + LO_B330) ->
  lf_cur cx W3 ms3 (c_p cx) (c_n cx) ->
  lf_jbk B MT MS la_nul cx fp k2 0 0 0%nat 0 ly3 S3 W3 ms3 md3 T3 [] ->
  lf_odd_at (rdW W3 (ms_mem ms3)) -> lf_texts_at (rdW W3 (ms_mem ms3)) ->
  lf_la_at (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W3 ms' /\ lf_header cx fp W3 ms' /\ lf_fshadow cx fp W3 ms' LF_SH0 /\
  lf_slot cx W3 ms' LS_SHB SHADOW_OFF /\ lf_slot cx W3 ms' LS_FK (lf_F cx fp) /\
  lf_slot cx W3 ms' LS_F (lf_F cx fp) /\ lf_slot cx W3 ms' LS_F0 (lf_F cx fp) /\
  lf_slot cx W3 ms' LS_WA (lf_F cx fp + LO_WA) /\
  lf_slot cx W3 ms' LS_B160 (lf_F cx fp + LO_B160) /\
  lf_slot cx W3 ms' LS_B1A0 (lf_F cx fp + LO_B1A0) /\
  lf_slot cx W3 ms' LS_B2E0 (lf_F cx fp + LO_B2E0) /\
  lf_slot cx W3 ms' LS_B330 (lf_F cx fp + LO_B330) /\
  lf_cur cx W3 ms' (c_p cx) (c_n cx) /\
  lf_jbk B MT MS la_nul cx fp k2 0 0 0%nat 0 ly3 S3 W3 ms' md' T3 [] /\
  lf_odd_at (rdW W3 (ms_mem ms')) /\ lf_texts_at (rdW W3 (ms_mem ms')) /\
  lf_la_at (rdW W3 (ms_mem ms')).
Proof.
intros cx fp k2 j nif ly3 S3 T3 W3 ms3 ms' md3 md' Hj Hnif Hlo Hhi Hsp0 Hceil Hband
  HF0 HF1 HFimg Hnul HAMF HPAY HK Hfd Hfs
  HSAVED HHDR HFSH HSHB HFK HSF HSF0 HWA HB160 HB1A0 HB2E0 HB330 HCUR HJBK HODD HTX HLA.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HX : forall a, gl_out (lf_sp1 cx) a -> ~ gl_X (lf_sp1 cx) j nif a)
  by (intros a Ha; exact (gl_out_X _ j nif a Hj Hnif Ha)).
assert (HRO : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ gl_X (lf_sp1 cx) j nif a)
  by (intros a Ha; apply HX; apply (gl_ro_out (lf_sp1 cx) a); [lia | exact Ha]).
assert (HSTK : forall a, (lf_sp1 cx + 0x18 <= a < lf_sp1 cx + LS_ODD) \/
    (lf_sp1 cx + LS_ODD + 8 <= a < lf_sp1 cx + 0x140) \/
    (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) -> ~ gl_X (lf_sp1 cx) j nif a).
{ intros a Ha. apply HX. unfold gl_out, LS_ODD, LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE,
    LINK_SNP_STK, ESTACK, LLVMF_STK in *. repeat split; lia. }
assert (HFR : forall a, lf_F cx fp <= a < lf_F cx fp + 1024 -> ~ gl_X (lf_sp1 cx) j nif a).
{ intros a Ha. apply HX.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg.
  unfold gl_out, LS_ODD, LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE, LINK_SNP_STK, ESTACK,
    LLVMF_STK in *. repeat split; lia. }
assert (HSH : forall a, lf_SH cx fp <= a < lf_SH cx fp + 112 -> ~ gl_X (lf_sp1 cx) j nif a).
{ intros a Ha. apply HX. unfold lf_SH, shadow_of_addr, SHADOW_OFF in Ha.
  assert (Hq : 0 <= lf_F cx fp / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold gl_out, LS_ODD, LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE, LINK_SNP_STK, ESTACK,
    LLVMF_STK in *. repeat split; lia. }
split.
{ eapply lf_saved_keep; [exact HK | | exact HSAVED].
  intros a Ha. apply HSTK. unfold lf_saved_fp in Ha. right; right; exact Ha. }
split.
{ eapply lf_header_keep; [exact HK | | exact HHDR].
  intros a Ha. apply HFR. unfold lf_header_fp in Ha.
  rewrite (proj1 LF_frame_slot) in Ha. lia. }
split.
{ eapply lf_fshadow_keep; [exact HK | | exact HFSH].
  intros a Ha. apply HSH. unfold lf_fshadow_fp in Ha.
  rewrite LF_SH0_len in Ha. change (Z.of_nat LF_NSH) with 112 in Ha. lia. }
assert (SLOT : forall off v, (0x18 <= off /\ off + 8 <= LS_ODD) \/ (LS_ODD + 8 <= off /\ off <= 0x138) ->
    lf_slot cx W3 ms3 off v -> lf_slot cx W3 ms' off v).
{ intros off v Hoff H. eapply lf_slot_keep; [exact HK | | exact H].
  intros i Hi. apply HSTK. unfold LS_ODD in *. lia. }
split; [apply (SLOT LS_SHB); [unfold LS_SHB, LS_ODD; lia | exact HSHB]|].
split; [apply (SLOT LS_FK); [unfold LS_FK, LS_ODD; lia | exact HFK]|].
split; [apply (SLOT LS_F); [unfold LS_F, LS_ODD; lia | exact HSF]|].
split; [apply (SLOT LS_F0); [unfold LS_F0, LS_ODD; lia | exact HSF0]|].
split; [apply (SLOT LS_WA); [unfold LS_WA, LS_ODD; lia | exact HWA]|].
split; [apply (SLOT LS_B160); [unfold LS_B160, LS_ODD; lia | exact HB160]|].
split; [apply (SLOT LS_B1A0); [unfold LS_B1A0, LS_ODD; lia | exact HB1A0]|].
split; [apply (SLOT LS_B2E0); [unfold LS_B2E0, LS_ODD; lia | exact HB2E0]|].
split; [apply (SLOT LS_B330); [unfold LS_B330, LS_ODD; lia | exact HB330]|].
split.
{ eapply lf_cur_keep; [exact HK | | exact HCUR].
  intros a Ha. apply HSTK. unfold lf_cur_fp in Ha. unfold LS_ODD. right; left; lia. }
split.
{ eapply lf_jbk_keep; [exact HK | exact Hfd | exact Hfs | | exact HJBK].
  intros a Ha. unfold lf_jbk_fp in Ha.
  destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - apply HX. exact (HAMF a Ha).
  - apply HX. rewrite Hnul in Ha.
    unfold gl_out, LA_NUL, LA_LONG_ALIAS, LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE, LS_ODD,
      LINK_SNP_STK, ESTACK, LLVMF_STK in *. repeat split; lia.
  - exact (HRO a Ha).
  - apply HX. apply HPAY. exact Ha. }
split; [eapply lf_odd_at_keep; [exact HK | exact HRO | exact HODD]|].
split; [eapply lf_texts_at_keep; [exact HK | exact HRO | exact HTX]|].
eapply lf_la_at_keep; [exact HK | | | exact HLA].
- intros i Hi _. apply gl_la_w. lia.
- intros a Ha. apply HX.
  unfold gl_out, LA_LONG_ALIAS, LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE, LS_ODD,
    LINK_SNP_STK, ESTACK, LLVMF_STK in *. repeat split; lia.
Qed.

(* ==========================================================================
   THE TURN'S CUT: the clauses of the invariant after the turn
   ========================================================================== *)

Record gl_ctx (cx : lcx) (fp j nif : Z) (T3 : list (Z * Z)) (W3 : world SEGS)
    (ms3 msF : machine_state) : Prop := mkGLC {
  glc_j : 0 <= j < 64;
  glc_nif : nif = j - j / 16;
  glc_lo : 2 ^ 46 <= lf_sp1 cx;
  glc_hi : lf_sp1 cx + 256 <= 2 ^ 47;
  glc_sp0 : lf_sp1 cx + 416 <= spZ (c_regs cx);
  glc_ceil : alloc_ceiling <= spZ (c_regs cx) - LLVMF_STK;
  glc_band : spZ (c_regs cx) - LLVMF_STK <= lf_sp1 cx - LINK_SNP_STK;
  glc_F0 : 4096 <= lf_F cx fp;
  glc_F1 : lf_F cx fp + 1024 <= alloc_ceiling;
  glc_Fimg : off_img (lf_F cx fp) 1024;
  glc_nul : la_nul = LA_NUL;
  glc_amf : forall a, amf_fp MS T3 a -> gl_out (lf_sp1 cx) a;
  glc_pay : forall a, c_p cx <= a < c_p cx + c_n cx -> gl_out (lf_sp1 cx) a;
  glc_K : kagree SEGS (gl_X (lf_sp1 cx) j nif) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msF));
  glc_pnl : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> mbyte SEGS (rdW W3 (ms_mem msF)) a <> None;
  glc_pgn : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE ->
              mbyte SEGS (rdW W3 (ms_mem msF)) a <> None;
  glc_by : forall i, 0 <= i <= Z.of_nat (length (lf_gname_z j)) ->
             mbyte SEGS (rdW W3 (ms_mem msF)) (LA_G_NAMES + 8 * j + i) =
               Some (Z_to_bv 8 (nth (Z.to_nat i) (lf_gname_z j ++ [0]) 0));
  glc_n : val_mem SEGS (rdW W3 (ms_mem msF)) (LA_G_NL + NK_N_IF) 4
            (if negb (j mod 16 =? 15) then nif + 1 else nif);
  glc_name : negb (j mod 16 =? 15) = true ->
               val_mem SEGS (rdW W3 (ms_mem msF)) (gl_aname nif) 8 (LA_G_NAMES + 8 * j);
  glc_idx : negb (j mod 16 =? 15) = true ->
              val_mem SEGS (rdW W3 (ms_mem msF)) (gl_aidx nif) 4 (j + 2)
}.

Lemma gl_cut_next : forall (cx : lcx) (fp k2 j nif : Z) ly3 S3 T3
    (W3 : world SEGS) (ms3 msF : machine_state) (md3 mdF : Model) (kbs : list byte),
  gl_ctx cx fp j nif T3 W3 ms3 msF ->
  m_fds mdF = m_fds md3 -> m_fs mdF = m_fs md3 ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slot cx W3 ms3 LS_SHB SHADOW_OFF -> lf_slot cx W3 ms3 LS_FK (lf_F cx fp) ->
  lf_slot cx W3 ms3 LS_F (lf_F cx fp) -> lf_slot cx W3 ms3 LS_F0 (lf_F cx fp) ->
  lf_slot cx W3 ms3 LS_WA (lf_F cx fp + LO_WA) ->
  lf_slot cx W3 ms3 LS_B160 (lf_F cx fp + LO_B160) ->
  lf_slot cx W3 ms3 LS_B1A0 (lf_F cx fp + LO_B1A0) ->
  lf_slot cx W3 ms3 LS_B2E0 (lf_F cx fp + LO_B2E0) ->
  lf_slot cx W3 ms3 LS_B330 (lf_F cx fp + LO_B330) ->
  lf_cur cx W3 ms3 (c_p cx) (c_n cx) ->
  lf_jbk B MT MS la_nul cx fp k2 0 0 0%nat 0 ly3 S3 W3 ms3 md3 T3 [] ->
  lf_odd_at (rdW W3 (ms_mem ms3)) -> lf_texts_at (rdW W3 (ms_mem ms3)) ->
  lf_la_at (rdW W3 (ms_mem ms3)) ->
  nk_n_if kbs = Z.of_nat (length (lf_tab_at nif)) ->
  aiftab_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs (lf_tab_at nif) ->
  lf_ifp (rdW W3 (ms_mem ms3)) nif ->
  (forall q, 0 <= q < NK_SIZE -> ~ (NK_IF_NAME <= q < NK_IF_NAME + 640) ->
     ~ (NK_IF_INDEX <= q < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= q < NK_N_IF + 4) ->
     val_mem SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + q) 1 0) ->
  lf_gnames_at j (rdW W3 (ms_mem ms3)) ->
  exists kbs' : list byte,
    (lf_saved cx W3 msF /\ lf_header cx fp W3 msF /\ lf_fshadow cx fp W3 msF LF_SH0 /\
     lf_slot cx W3 msF LS_SHB SHADOW_OFF /\ lf_slot cx W3 msF LS_FK (lf_F cx fp) /\
     lf_slot cx W3 msF LS_F (lf_F cx fp) /\ lf_slot cx W3 msF LS_F0 (lf_F cx fp) /\
     lf_slot cx W3 msF LS_WA (lf_F cx fp + LO_WA) /\
     lf_slot cx W3 msF LS_B160 (lf_F cx fp + LO_B160) /\
     lf_slot cx W3 msF LS_B1A0 (lf_F cx fp + LO_B1A0) /\
     lf_slot cx W3 msF LS_B2E0 (lf_F cx fp + LO_B2E0) /\
     lf_slot cx W3 msF LS_B330 (lf_F cx fp + LO_B330) /\
     lf_cur cx W3 msF (c_p cx) (c_n cx) /\
     lf_jbk B MT MS la_nul cx fp k2 0 0 0%nat 0 ly3 S3 W3 msF mdF T3 [] /\
     lf_odd_at (rdW W3 (ms_mem msF)) /\ lf_texts_at (rdW W3 (ms_mem msF)) /\
     lf_la_at (rdW W3 (ms_mem msF))) /\
    anlk_at SEGS (rdW W3 (ms_mem msF)) LA_G_NL kbs' /\
    nk_n_if kbs' = Z.of_nat (length (lf_tab_at (j + 1 - (j + 1) / 16))) /\
    aiftab_at SEGS (rdW W3 (ms_mem msF)) LA_G_NL kbs' (lf_tab_at (j + 1 - (j + 1) / 16)) /\
    lf_ifp (rdW W3 (ms_mem msF)) (j + 1 - (j + 1) / 16) /\
    (forall q, 0 <= q < NK_SIZE -> ~ (NK_IF_NAME <= q < NK_IF_NAME + 640) ->
       ~ (NK_IF_INDEX <= q < NK_IF_INDEX + 320) -> ~ (NK_N_IF <= q < NK_N_IF + 4) ->
       val_mem SEGS (rdW W3 (ms_mem msF)) (LA_G_NL + q) 1 0) /\
    lf_gnames_at (j + 1) (rdW W3 (ms_mem msF)) /\ lf_gnames_w (rdW W3 (ms_mem msF)).
Proof.
intros cx fp k2 j nif ly3 S3 T3 W3 ms3 msF md3 mdF kbs C Hfd Hfs
  HSAVED HHDR HFSH HSHB HFK HSF HSF0 HWA HB160 HB1A0 HB2E0 HB330 HCUR HJBK HODD HTX HLA
  HNIF HTAB HIFP HZERO HGN.
destruct C as [Cj Cnif Clo Chi Csp0 Cceil Cband CF0 CF1 CFimg Cnul Camf Cpay CK Cpnl Cpgn Cby Cn
  Cname Cidx].
pose proof (lf_cnt_range j Cj) as Hcr.
assert (Hnifr : 0 <= nif <= 60) by (rewrite Cnif; lia).
destruct (gl_mem_next (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msF)) (lf_sp1 cx) j nif
  (negb (j mod 16 =? 15)) kbs Cj Cnif eq_refl Clo CK Cpnl Cpgn Cby Cn Cname Cidx
  HNIF HTAB HIFP HZERO HGN)
  as (kbs' & HANL' & HNIF' & HTAB' & HIFP' & HZERO' & HGN' & HGW').
exists kbs'. split.
- exact (gl_setup_keep cx fp k2 j nif ly3 S3 T3 W3 ms3 msF md3 mdF Cj Hnifr Clo Chi
    Csp0 Cceil Cband CF0 CF1 CFimg Cnul Camf Cpay CK Hfd Hfs
    HSAVED HHDR HFSH HSHB HFK HSF HSF0 HWA HB160 HB1A0 HB2E0 HB330 HCUR HJBK HODD HTX HLA).
- split; [exact HANL'|]. split; [exact HNIF'|]. split; [exact HTAB'|]. split; [exact HIFP'|].
  split; [exact HZERO'|]. split; [exact HGN' | exact HGW'].
Qed.

(* the cut lf_gl_inv (j + 1), from the cut at j and the state the turn's runs leave *)
Lemma gl_gl_build : forall (cx : lcx) (fy fy' : YK11.FPState) (fp k2 j nif : Z) ly3 S3
    (W3 : world SEGS) (ms3 msF : machine_state) (md3 mdF : Model),
  j < 63 ->
  gl_ctx cx fp j nif (c_T cx) W3 ms3 msF ->
  m_fds mdF = m_fds md3 -> m_fs mdF = m_fs md3 ->
  lf_shape fy' LF_gl msF -> lf_core cx msF ->
  getr (ms_regs msF) 18 = w64 LA_G_NL ->
  getr (ms_regs msF) 19 = w64 (lf_SH cx fp) ->
  getr (ms_regs msF) 21 = w64 (LA_G_NAMES + 8 * (j + 1)) ->
  getr (ms_regs msF) 22 = w64 LA_STR ->
  getr (ms_regs msF) 23 = w64 (64 - (j + 1)) ->
  getr (ms_regs msF) 24 = w64 (j + 1 + 2) ->
  getr (ms_regs msF) 25 = w64 0x42530 ->
  getr (ms_regs msF) 26 = w64 (LA_G_NL + 0x42000) ->
  getr (ms_regs msF) 27 = w64 0x422b0 ->
  lf_gl_inv B MT MS la_nul j cx fy fp k2 ly3 S3 W3 ms3 md3 ->
  lf_gl_inv B MT MS la_nul (j + 1) cx fy' fp k2 ly3 S3 W3 msF mdF.
Proof.
intros cx fy fy' fp k2 j nif ly3 S3 W3 ms3 msF md3 mdF Hlt C Hfd Hfs HSH HCO
  R18 R19 R21 R22 R23 R24 R25 R26 R27 GI.
destruct GI as (kbs & Hj' & HSET & Q18 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 &
  HNK & HNIF & HTAB & HIFP & HZERO & HGN).
destruct HSET as (HSHAPE & HCORE & HSAVED & HHDR & HFSH & QR19 & HSHB & HFK & HSF & HSF0 & HWA &
  HB160 & HB1A0 & HB2E0 & HB330 & HCUR & HJBK & HGW & HODD & HTX & HLA).
pose proof C as [Cj Cnif _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
rewrite <- Cnif in HNIF, HTAB, HIFP.
destruct (gl_cut_next cx fp k2 j nif ly3 S3 (c_T cx) W3 ms3 msF md3 mdF kbs C Hfd Hfs
  HSAVED HHDR HFSH HSHB HFK HSF HSF0 HWA HB160 HB1A0 HB2E0 HB330 HCUR HJBK HODD HTX HLA
  HNIF HTAB HIFP HZERO HGN)
  as (kbs' & (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17)
      & HANL' & HNIF' & HTAB' & HIFP' & HZERO' & HGN' & HGW').
exists kbs'. split; [lia|].
split.
{ split; [exact HSH|]. split; [exact HCO|]. split; [exact K1|]. split; [exact K2|].
  split; [exact K3|]. split; [exact R19|]. split; [exact K4|]. split; [exact K5|].
  split; [exact K6|]. split; [exact K7|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K10|]. split; [exact K11|]. split; [exact K12|]. split; [exact K13|].
  split; [exact K14|]. split; [exact HGW'|]. split; [exact K15|]. split; [exact K16 | exact K17]. }
split; [exact R18|]. split; [exact R21|]. split; [exact R22|]. split; [exact R23|].
split; [exact R24|]. split; [exact R25|]. split; [exact R26|]. split; [exact R27|].
split; [exact HANL'|]. split; [exact HNIF'|]. split; [exact HTAB'|]. split; [exact HIFP'|].
split; [exact HZERO' | exact HGN'].
Qed.

(* the cut lf_ol_inv 0, from the cut at j = 63 *)
Lemma gl_ol_build : forall (cx : lcx) (fy fy' : YK11.FPState) (fp k2 j nif : Z) ly3 S3
    (W3 : world SEGS) (ms3 msF : machine_state) (md3 mdF : Model),
  j = 63 ->
  gl_ctx cx fp j nif (c_T cx) W3 ms3 msF ->
  m_fds mdF = m_fds md3 -> m_fs mdF = m_fs md3 ->
  lf_shape fy' LF_ol msF -> lf_core cx msF ->
  getr (ms_regs msF) 18 = w64 LA_G_NL ->
  getr (ms_regs msF) 19 = w64 (lf_SH cx fp) ->
  getr (ms_regs msF) 26 = w64 (lf_F cx fp + LO_WA) ->
  getr (ms_regs msF) 27 = w64 SHADOW_OFF ->
  lf_slot cx W3 msF LS_ODD LA_ODD ->
  getr (ms_regs msF) 11 = w64 (- 8 - 8 * 0) -> getr (ms_regs msF) 12 = w64 (101 + 0) ->
  getr (ms_regs msF) 13 = w64 (LA_G_NL + 0x42000) -> getr (ms_regs msF) 14 = w64 0x422b0 ->
  getr (ms_regs msF) 15 = w64 0x42530 -> getr (ms_regs msF) 16 = w64 (LA_ODD + 8 + 8 * 0) ->
  getr (ms_regs msF) 17 = w64 (SHADOW_OFF + (LA_ODD + 8 + 8 * 0) / 8) ->
  getr (ms_regs msF) 5 = w64 (- 0x28) ->
  lf_gl_inv B MT MS la_nul j cx fy fp k2 ly3 S3 W3 ms3 md3 ->
  lf_ol_inv B MT MS la_nul 0 cx fy' fp k2 ly3 S3 W3 msF mdF.
Proof.
intros cx fy fy' fp k2 j nif ly3 S3 W3 ms3 msF md3 mdF Hj63 C Hfd Hfs HSH HCO
  R18 R19 R26 R27 RODD R11 R12 R13 R14 R15 R16 R17 R5 GI.
destruct GI as (kbs & Hj' & HSET & Q18 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 &
  HNK & HNIF & HTAB & HIFP & HZERO & HGN).
destruct HSET as (HSHAPE & HCORE & HSAVED & HHDR & HFSH & QR19 & HSHB & HFK & HSF & HSF0 & HWA &
  HB160 & HB1A0 & HB2E0 & HB330 & HCUR & HJBK & HGW & HODD & HTX & HLA).
pose proof C as [Cj Cnif _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
rewrite <- Cnif in HNIF, HTAB, HIFP.
destruct (gl_cut_next cx fp k2 j nif ly3 S3 (c_T cx) W3 ms3 msF md3 mdF kbs C Hfd Hfs
  HSAVED HHDR HFSH HSHB HFK HSF HSF0 HWA HB160 HB1A0 HB2E0 HB330 HCUR HJBK HODD HTX HLA
  HNIF HTAB HIFP HZERO HGN)
  as (kbs' & (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17)
      & HANL' & HNIF' & HTAB' & HIFP' & HZERO' & HGN' & HGW').
subst j.
change (63 + 1 - (63 + 1) / 16) with 60 in HNIF', HTAB', HIFP'.
change (63 + 1) with 64 in HGN'.
exists kbs'. split; [lia|].
split.
{ split; [exact HSH|]. split; [exact HCO|]. split; [exact K1|]. split; [exact K2|].
  split; [exact K3|]. split; [exact R19|]. split; [exact K4|]. split; [exact K5|].
  split; [exact K6|]. split; [exact K7|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K10|]. split; [exact K11|]. split; [exact K12|]. split; [exact K13|].
  split; [exact K14|]. split; [exact HGW'|]. split; [exact K15|]. split; [exact K16 | exact K17]. }
split; [exact R18|]. split; [exact R26|]. split; [exact R27|]. split; [exact RODD|].
split; [exact R11|]. split; [exact R12|]. split; [exact R13|]. split; [exact R14|].
split; [exact R15|]. split; [exact R16|]. split; [exact R17|]. split; [exact R5|].
split; [exact HANL'|]. split; [exact HNIF'|]. split; [exact HTAB'|]. split; [exact HIFP'|].
split; [exact HZERO' | exact HGN'].
Qed.

(* ---- the tactics of the runs after the call ---- *)
(* a register named by its number is callee-saved *)
Ltac gl_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] =>
    let x := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with x end; lia.
(* an atom of a run's environment below the run's tokens is the atom of E2 *)
Ltac gl_ew H := cbn [ew ewset extK Nat.eqb]; exact H.
(* the bases of the state's regions, in any environment of the runs after the call *)
Ltac gl_bases H :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset extK Nat.eqb] in H;
  let GU9 := ident:(GU9) in let GU26 := ident:(GU26) in let GU35 := ident:(GU35) in let GU36 := ident:(GU36) in
  rewrite ?GU9, ?GU26, ?GU35, ?GU36 in H.
(* the run's writable windows lie in the journal's window or in g_nl, a range of G *)
Ltac gl_awr :=
  lazymatch goal with |- awr_ok_x _ _ _ _ _ _ _ _ _ _ _ _ =>
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
          [ gl_bases Ha;
            first [ lia
                  | left; split; [unfold awr_byte; left; unfold LS_ODD in Ha; lia | lia]
                  | right; left; apply (inG_of_In G_HARNESS LA_G_NL 271992 a);
                    [unfold G_HARNESS; cbn [In]; left; reflexivity
                    | unfold gl_aname, gl_aidx, NK_IF_NAME, NK_IF_INDEX in Ha; lia] ]
          | ]);
  destruct Hin end.
(* the run's writable windows lie in gl_XW *)
Ltac gl_win :=
  let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hr := fresh "Hr" in
  let Hrr := fresh "Hrr" in
  intros a Ha (r & Hr & Hrr); vm_compute in Hr;
  repeat (destruct Hr as [<- | Hr]; [gl_bases Hrr; unfold gl_XW, LS_ODD, NK_N_IF; lia | ]);
  destruct Hr.
(* fold a run's frame and growth into the agreement since the call (KW) and the growth since the call (GW) *)
Ltac gl_acc :=
  lazymatch goal with
  | HFr : frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2),
    KW : kagree _ ?X ?m0 (mrestrict ?H ?m1),
    HGq : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2),
    GW : mem_grows ?m0 (mrestrict ?H ?m1) |- _ =>
      let K := fresh "KW" in
      pose proof (gl_kagree_step _ E rs _ _ _ X KW HFr
        ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold gl_XW in Ha; lia) ltac:(gl_win)) as K;
      let G := fresh "GW" in
      pose proof ((fun x Hx => HGq x (GW x Hx)) : mem_grows m0 (mrestrict H m2)) as G;
      clear KW GW HFr HGq; rename K into KW; rename G into GW
  end.
(* the instrumented check's obligation: the slot's bytes are addressable, as all of g_nl is at every state *)
Ltac gl_obl :=
  lazymatch goal with |- range_addressable (rd_of _ (mrestrict (w_H ?W) ?mem)) (U ?Ex _) _ _ =>
  let HJ := ident:(HJ) in let TB := ident:(TB) in
  let HAR := fresh "HAR" in
  destruct (gl_aj_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR & _);
  let Hra := fresh "Hra" in
  destruct (zsh_gnl _ TB _ _ _ _ _ _ HAR) as (Hra & _);
  rewrite <- (aview_rd_of _);
  let E2_32 := ident:(E2_32) in let E2_35 := ident:(E2_35) in let E2_36 := ident:(E2_36) in
  let Hnif := ident:(Hnif) in
  rewrite (U_atom Ex 32 SB ltac:(gl_ew E2_32)) by (unfold SB; lia); rewrite SB_SHADOW_OFF;
  first
  [ rewrite (U_atom Ex 35 _ ltac:(gl_ew E2_35)) by (unfold gl_aname, LA_G_NL, NK_IF_NAME; lia);
    apply (lf_ra_sub _ LA_G_NL NK_SIZE _ _ Hra); unfold gl_aname, NK_IF_NAME, NK_SIZE; lia
  | rewrite (U_atom Ex 36 _ ltac:(gl_ew E2_36)) by (unfold gl_aidx, LA_G_NL, NK_IF_INDEX; lia);
    apply (lf_ra_sub _ LA_G_NL NK_SIZE _ _ Hra); unfold gl_aidx, NK_IF_INDEX, NK_SIZE; lia ]
  end.
Ltac gl_side :=
  try (lazymatch goal with |- awr_ok_x _ _ _ _ _ _ _ _ _ _ _ _ => solve [gl_awr] end);
  try (lazymatch goal with |- range_addressable _ _ _ _ => solve [gl_obl] end).
Ltac gl_run :=
  let RUN := ident:(RUN) in let HS := ident:(HS) in let HJ := ident:(HJ) in let SHOK := ident:(SHOK) in
  paj_run_tok RUN HS HJ SHOK Bspan; gl_side.
Ltac gl_run_to stop :=
  let RUNTO := ident:(RUNTO) in let HS := ident:(HS) in let HJ := ident:(HJ) in let SHOK := ident:(SHOK) in
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; gl_side.


(* a register of the cut the turn reaches: an atom, an atom plus a constant, a literal *)
Ltac gl_rg r Ew :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
    rewrite (st_ok_pi_restrict_reg _ Ex ss msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e;
    apply gl_den_off0; gl_ew Ew
  end.
Ltac gl_rgo r n v c Ew :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
    rewrite (st_ok_pi_restrict_reg _ Ex ss msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e;
    rewrite (lf_sv_off Ex n v c ltac:(gl_ew Ew)
      ltac:(unfold LA_G_NAMES, LA_G_NL, LA_ODD, SHADOW_OFF; lia)
      ltac:(unfold LA_G_NAMES, LA_G_NL, LA_ODD, SHADOW_OFF; lia));
    unfold w64; f_equal; lia
  end.
Ltac gl_rgl r :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
    rewrite (st_ok_pi_restrict_reg _ Ex ss msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e;
    rewrite gl_den_lit; unfold w64; apply Z_to_bv64_eq_mod; vm_compute; reflexivity
  end.
(* the memory facts of the cut the turn reaches, from the call's post and the runs' frames *)
Ltac gl_mem_end :=
  let j := ident:(j) in let cx := ident:(cx) in let W3 := ident:(W3) in
  let ms3 := ident:(ms3) in let mem2 := ident:(mem2) in let kbs := ident:(kbs) in
  let PR2 := ident:(PR2) in let GW := ident:(GW) in let KW := ident:(KW) in
  let HBY := ident:(HBY) in let HM0NL := ident:(HM0NL) in let HM0GN := ident:(HM0GN) in
  let HKA02 := ident:(HKA02) in
  lazymatch goal with |- SRr _ _ (mkCfg ?msF _) _ =>
  assert (PRES : forall a, 0 <= a < 2 ^ 64 ->
      ~ (LA_G_NAMES + 8 * j <= a <= LA_G_NAMES + 8 * j + Z.of_nat (length (lf_gname_z j))) ->
      mbyte SEGS (rdW W3 (ms_mem ms3)) a <> None ->
      mbyte SEGS (rdW W3 (ms_mem msF)) a <> None)
    by (intros a Ha Hd Hm; destruct (PR2 a Ha Hd Hm) as [Hp | Hr];
        [apply gl_mbyte_of_apresent; exact (gl_apresent_grows (w_H W3) mem2 (ms_mem msF) a GW Hp)
        | apply gl_mbyte_of_rom; exact Hr]);
  assert (BYF : forall i, 0 <= i <= Z.of_nat (length (lf_gname_z j)) ->
      mbyte SEGS (rdW W3 (ms_mem msF)) (LA_G_NAMES + 8 * j + i) =
        Some (Z_to_bv 8 (nth (Z.to_nat i) (lf_gname_z j ++ [0]) 0)))
    by (intros i Hi;
        rewrite (KW (LA_G_NAMES + 8 * j + i)
          ltac:(unfold gl_XW, gl_aname, gl_aidx, LA_G_NAMES, LA_G_NL, NK_IF_NAME, NK_IF_INDEX,
                  NK_N_IF, LS_ODD in *; lia));
        apply gl_mbyte_of_aview; apply HBY; lia);
  assert (PNL : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
      mbyte SEGS (rdW W3 (ms_mem msF)) a <> None)
    by (intros a Ha; apply PRES;
        [unfold LA_G_NL, NK_SIZE in *; lia
        | unfold LA_G_NL, NK_SIZE, LA_G_NAMES in *; lia | exact (HM0NL a Ha)]);
  assert (PGN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE ->
      mbyte SEGS (rdW W3 (ms_mem msF)) a <> None);
  [ intros a Ha;
    destruct (Z.le_gt_cases (LA_G_NAMES + 8 * j) a) as [H1|H1];
    [ destruct (Z.le_gt_cases a (LA_G_NAMES + 8 * j + Z.of_nat (length (lf_gname_z j)))) as [H2|H2];
      [ pose proof (BYF (a - LA_G_NAMES - 8 * j) ltac:(lia)) as Hbb;
        replace (LA_G_NAMES + 8 * j + (a - LA_G_NAMES - 8 * j)) with a in Hbb by lia;
        rewrite Hbb; discriminate
      | apply PRES; [unfold LA_G_NAMES, G_NAMES_SIZE in *; lia | lia | exact (HM0GN a Ha)] ]
    | apply PRES; [unfold LA_G_NAMES, G_NAMES_SIZE in *; lia | lia | exact (HM0GN a Ha)] ] | ];
  assert (KX : kagree SEGS (gl_X (lf_sp1 cx) j (nk_n_if kbs))
      (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msF)));
  [ eapply kagree_mono; [| eapply kagree_trans; [exact HKA02 | exact KW] ];
    intros a Ha; cbv beta in Ha; unfold gl_X, gl_XW in *; lia | ]
  end.

(* ONE TURN: +0x32c .. +0x3b4, back to LF_gl at j + 1, or at j = 63 through +0x3b8 .. +0x404 to LF_ol *)
Lemma gl_turn : forall (POST : lcx -> world SEGS -> config -> Prop) j, 0 <= j < 64 ->
  FROM POST (OL 0) -> (j < 63 -> FROM POST (GL (j + 1))) -> FROM POST (GL j).
Proof.
intros POST j Hj HOL HNX cx fy fp k2 ly3 S3 W3 ms3 md3 HB HFX HJ HFR GI.
pose proof GI as GI0.
destruct GI0 as (kbs & Hj' & HSET & R18 & R21 & R22 & R23 & R24 & R25 & R26 & R27 &
  HNK & HNIF & HTAB & HIFP & HZERO & HGN).
destruct HSET as (HSHAPE & HCORE & HSAVED & HHDR & HFSH & R19 & HSHB & HFK & HSF & HSF0 & HWA &
  HB160 & HB1A0 & HB2E0 & HB330 & HCUR & HJBK & HGW & HODD & HTX & HLA).
pose proof HSHAPE as (HPC & HRESV & HSVC & HROM & HFRG & HFC).
pose proof HB as (HPRE & HFRM & HGX & HLAN & HMSE & HE0 & HE0sp & HCTXA & HMO).
pose proof HJBK as (J1 & J1b & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & JRO & J14 & J15).
pose proof (gl_sp1 cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 HJ) as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
pose proof HCORE as (R2 & R8 & R9 & R3 & R4).
assert (Hms : ms3 = @YK11.mkst fy (ms_regs ms3) (w64 (BASE + LF_gl)) (ms_mem ms3) (seg_rom SEGS))
  by (apply (lf_ms_shape fy SEGS); assumption).
pose proof (gl_entry cx fy j W3 ms3 Hj Hs1 Hs2 Hs3 HCORE R24 HSHB) as HS.
rewrite <- Hms in HS.
pose proof (paj_run_x (fx := fy) SK B LAWS G_HARNESS HGX 0 []) as RUN.
pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
remember (Eimg (Ereg (ms_regs ms3) (GL_EXTRA j))) as E0 eqn:HEdef.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HEdef; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E0 n = ew (Ereg (ms_regs ms3) (GL_EXTRA j)) n)
  by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
assert (EA0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr (ms_regs ms3) r)
  by (intros n r Hn; rewrite HEdef; exact (ew_Eimg_Ereg_nat (ms_regs ms3) _ n r Hn)).
assert (E01 : ew E0 1 = getr (ms_regs ms3) 1) by exact (EA0 1%nat 1%bv eq_refl).
assert (E03 : ew E0 3 = getr (c_regs cx) 3) by (rewrite (EA0 3%nat 3%bv eq_refl); exact R3).
assert (E04 : ew E0 4 = getr (c_regs cx) 4) by (rewrite (EA0 4%nat 4%bv eq_refl); exact R4).
assert (E02 : ew E0 2 = w64 (lf_sp1 cx)) by (rewrite (EA0 2%nat 2%bv eq_refl); exact R2).
assert (E09 : ew E0 9 = w64 (lf_sp1 cx)) by (rewrite (EA0 9%nat 9%bv eq_refl); exact R9).
assert (E021 : ew E0 21 = w64 (LA_G_NAMES + 8 * j)) by (rewrite (EA0 21%nat 21%bv eq_refl); exact R21).
assert (E022 : ew E0 22 = w64 LA_STR) by (rewrite (EA0 22%nat 22%bv eq_refl); exact R22).
assert (E025 : ew E0 25 = w64 0x42530) by (rewrite (EA0 25%nat 25%bv eq_refl); exact R25).
assert (E026 : ew E0 26 = w64 (LA_G_NL + 0x42000)) by (rewrite (EA0 26%nat 26%bv eq_refl); exact R26).
assert (E027 : ew E0 27 = w64 0x422b0) by (rewrite (EA0 27%nat 27%bv eq_refl); exact R27).
assert (E08 : ew E0 8 = w64 (spZ (c_regs cx))) by (rewrite (EA0 8%nat 8%bv eq_refl); exact R8).
assert (E018 : ew E0 18 = w64 LA_G_NL) by (rewrite (EA0 18%nat 18%bv eq_refl); exact R18).
assert (E019 : ew E0 19 = w64 (lf_SH cx fp)) by (rewrite (EA0 19%nat 19%bv eq_refl); exact R19).
assert (E023 : ew E0 23 = w64 (64 - j)) by (rewrite (EA0 23%nat 23%bv eq_refl); exact R23).
assert (E034 : ew E0 34 = w64 j)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 2)).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E0 (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef.
paj_run_tok RUN HS HJ SHOK Bspan.
- (* the entry state has no writable window *)
  unfold GL_SS, GL_SHB_R. cbn [ss_mem].
  apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|].
  apply awr_ok_x_nil.
- pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  pose proof HPRE as (HAFN & _). pose proof HAFN as (HAR0 & _ & _ & HGP & HTP & _).
  assert (Hsp : spZ (ms_regs ms) = lf_sp1 cx)
    by (unfold spZ; rewrite Q2, E02; unfold w64; apply unsigned_lit_small; lia).
  (* the run changed no byte: its only region has no writable window *)
  assert (HM01 : forall x, mrestrict (w_H W3) (ms_mem ms) x = mrestrict (w_H W3) (ms_mem ms3) x).
  { intros x. apply HFr. intros (r & Hr & Hrr). unfold GL_SS in Hr. cbn [ss_mem In] in Hr.
    destruct Hr as [<- | []]. unfold GL_SHB_R in Hrr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr.
    lia. }
  rewrite (lv_sigma LV LS___interceptor_trampoline_snprintf).
  change (link_sigma LS___interceptor_trampoline_snprintf) with LA_W_SNPRINTF.
  eapply SRr_bind.
  { eapply (@LLVMFuzzerTestOneInputSnp.lf_snp_at fy rc SK PI B LAWS TB HSEGS (SNP fy) 0 [] W3
      (ms_regs ms) (ms_mem ms) LLVMF_STK (spZ (c_regs cx))
      (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(LF_CID, fp)] ly3 S3 _ k2 _ j HGX HJ).
    - rewrite Hsp. exact Hs6.
    - rewrite Hsp. lia.
    - rewrite Hsp. exact Hs4.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q3, E03. exact HGP.
    - rewrite Q4, E04. exact HTP.
    - rewrite Q10. exact E021.
    - exact Q11.
    - rewrite Q12. exact E022.
    - rewrite Q13. exact E034.
    - exact Hj.
    - (* the read-only image: the run changed no byte *)
      assert (HRO : forall a, aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a)
        by (intros a; unfold aview, mbyte; rewrite HM01; reflexivity).
      intros a Hro Ho He. rewrite HRO. exact (JRO a Hro Ho He).
    - destruct HFX as (_ & [Hc | Hc]); [rewrite Hc; exact HFRM | exact Hc]. }
  cbv beta. intros W2 c2 Hwle (-> & fy' & regs2 & mem2 & md2 & -> & HFXY & HFRM2 & HJ2 & HPRES &
    HSAME & HA0 & HBY & HKEPT & HPRE2).
  (* ---- the registers at the call, read off the run before it, and kept by the call ---- *)
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  assert (HCS : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r Hr; exact (gl_pres_reg _ _ r HPRES Hr)).
  assert (P2 : getr regs2 2 = w64 (lf_sp1 cx))
    by (rewrite (HCS 2%bv) by gl_cs; rewrite Q2; exact E02).
  assert (P3 : getr regs2 3 = getr (c_regs cx) 3)
    by (rewrite (HCS 3%bv) by gl_cs; rewrite Q3; exact E03).
  assert (P4 : getr regs2 4 = getr (c_regs cx) 4)
    by (rewrite (HCS 4%bv) by gl_cs; rewrite Q4; exact E04).
  assert (P8 : getr regs2 8 = w64 (spZ (c_regs cx)))
    by (rewrite (HCS 8%bv) by gl_cs; rewrite Q8; exact E08).
  assert (P9 : getr regs2 9 = w64 (lf_sp1 cx))
    by (rewrite (HCS 9%bv) by gl_cs; rewrite Q9; exact E09).
  assert (P18 : getr regs2 18 = w64 LA_G_NL)
    by (rewrite (HCS 18%bv) by gl_cs; rewrite Q18; exact E018).
  assert (P19 : getr regs2 19 = w64 (lf_SH cx fp))
    by (rewrite (HCS 19%bv) by gl_cs; rewrite Q19; exact E019).
  assert (P20 : getr regs2 20 = w64 j)
    by (rewrite (HCS 20%bv) by gl_cs; rewrite Q20; exact E034).
  assert (P21 : getr regs2 21 = w64 (LA_G_NAMES + 8 * j))
    by (rewrite (HCS 21%bv) by gl_cs; rewrite Q21; exact E021).
  assert (P22 : getr regs2 22 = w64 LA_STR)
    by (rewrite (HCS 22%bv) by gl_cs; rewrite Q22; exact E022).
  assert (P23 : getr regs2 23 = w64 (64 - j))
    by (rewrite (HCS 23%bv) by gl_cs; rewrite Q23; exact E023).
  assert (P24 : getr regs2 24 = w64 (j + 2))
    by (rewrite (HCS 24%bv) by gl_cs; rewrite Q24, E034;
        unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  assert (P25 : getr regs2 25 = w64 0x42530)
    by (rewrite (HCS 25%bv) by gl_cs; rewrite Q25; exact E025).
  assert (P26 : getr regs2 26 = w64 (LA_G_NL + 0x42000))
    by (rewrite (HCS 26%bv) by gl_cs; rewrite Q26; exact E026).
  assert (P27 : getr regs2 27 = w64 0x422b0)
    by (rewrite (HCS 27%bv) by gl_cs; rewrite Q27; exact E027).
  (* ---- the descriptors and the file system across the call ---- *)
  assert (FD2 : m_fds md2 = m_fds md3 /\ m_fs md2 = m_fs md3).
  { rewrite (same_but_materialized_wvb _ _ HSAME). rewrite ?lf_wvb_fds, ?lf_wvb_fs. split; reflexivity. }
  (* ---- the memory at the return: the snprintf post over the run's unchanged memory ---- *)
  pose proof (lf_gname_z_len j ltac:(lia)) as HGL.
  assert (HST1 : spZ (c_regs cx) - LLVMF_STK <= lf_sp1 cx) by (unfold LINK_SNP_STK, ESTACK in Hs6; lia).
  assert (HK02 : forall a, 0 <= a < 2 ^ 64 ->
      ~ (LA_G_NAMES + 8 * j <= a <= LA_G_NAMES + 8 * j + Z.of_nat (length (lf_gname_z j))) ->
      ~ (lf_sp1 cx - LINK_SNP_STK <= a < lf_sp1 cx) ->
      aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hd Hw. rewrite (HKEPT a Ha Hd) by (rewrite Hsp; exact Hw).
    unfold aview, mbyte. rewrite HM01. reflexivity. }
  assert (HKA02 : kagree SEGS (fun a => ~ (0 <= a < 2 ^ 64) \/
      (LA_G_NAMES + 8 * j <= a <= LA_G_NAMES + 8 * j + Z.of_nat (length (lf_gname_z j))) \/
      (lf_sp1 cx - LINK_SNP_STK <= a < lf_sp1 cx)) (rdW W3 (ms_mem ms3)) (rdW W3 mem2)).
  { apply kagree_of_aview. intros a Ha. apply HK02; lia. }
  assert (M1 : rdword (aview SEGS (w_H W3) mem2) (lf_sp1 cx + LS_SHB) = Some SHADOW_OFF).
  { rewrite (gl_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3))); [exact HSHB|].
    intros i Hi. apply HK02; unfold LS_SHB, LINK_SNP_STK, ESTACK, LA_G_NAMES in *; lia. }
  assert (M2 : rdword (aview SEGS (w_H W3) mem2) (lf_sp1 cx + LS_WA) = Some (lf_F cx fp + LO_WA)).
  { rewrite (gl_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3))); [exact HWA|].
    intros i Hi. apply HK02; unfold LS_WA, LINK_SNP_STK, ESTACK, LA_G_NAMES in *; lia. }
  assert (M3 : val_mem SEGS (rdW W3 mem2) (LA_G_NL + NK_N_IF) 4 (nk_n_if kbs)).
  { pose proof HNK as [[Hab Hwr] HL].
    assert (V0 : val_mem SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + NK_N_IF) 4 (nk_n_if kbs)).
    { unfold nk_n_if, fld_u32. change 4%nat with (N.to_nat 4).
      exact (val_mem_of_abytes SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs NK_N_IF (N.to_nat 4) Hab
               ltac:(unfold NK_N_IF; lia)
               ltac:(change (N.to_nat 4) with 4%nat; unfold NK_N_IF, NK_SIZE in *; lia)). }
    apply (val_mem_keep SEGS _ _ _ _ 4 _ HKA02); [|exact V0].
    intros k Hk. unfold LA_G_NL, NK_N_IF, LA_G_NAMES, LINK_SNP_STK, ESTACK in *. lia. }
  destruct (gl_aj_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (HAR2 & HWIN2).
  assert (M4 : forall i, 0 <= i < 8 -> writable_at SEGS (rdW W3 mem2) (lf_sp1 cx + LS_ODD + i)).
  { intros i Hi. apply gl_apresent_writable. apply HWIN2. unfold LS_ODD. lia. }
  pose proof (lf_cnt_range j Hj) as Hcr.
  assert (HNIF2 : nk_n_if kbs = j - j / 16).
  { rewrite HNIF. rewrite <- (Z2Nat.id (j - j / 16)) by lia.
    rewrite (lf_tab_at_len (Z.to_nat (j - j / 16)) ltac:(lia)). lia. }
  assert (Hnif : 0 <= nk_n_if kbs <= 60) by (rewrite HNIF2; lia).
  assert (HFXY2 : @BoxBase.fxr fx fy') by (exact (fxr_trans fx fy fy' HFX HFXY)).
  assert (HinF : In (LF_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem2 md2 LF_CID fp HAR2 HinF) as (HF4096 & HFceil & _).
  rewrite (proj1 LF_frame_slot), (J2 LF_CID fp) in HFceil. rewrite (J2 LF_CID fp) in HF4096.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hwa : 0 <= lf_F cx fp + LO_WA < 2 ^ 64) by (unfold lf_F, LO_WA; lia).
  pose proof (gl_mid fy' cx W3 regs2 mem2 (nk_n_if kbs) j (lf_F cx fp + LO_WA) Hj Hnif Hwa
    Hs1 Hs2 Hs3 P9 P20 P24 P25 P26 P27 M1 M2 M3 M4) as HS2.
  change (Z_to_bv 64 (BASE + 2380)) with (w64 (BASE + LF_sn_ra)).
  clear RUN BR.
  pose proof (paj_run_x (fx := fy') SK B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (paj_run_to_x (fx := fy') SK B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy') (PI := PI)) as BR.
  remember (Eimg (Ereg regs2 (GL2_EXTRA (nk_n_if kbs) j (lf_F cx fp + LO_WA)))) as E2 eqn:HE2def.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2def; apply Eimg_env).
  assert (EA2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
    by (intros n r Hn; rewrite HE2def; exact (ew_Eimg_Ereg_nat regs2 _ n r Hn)).
  assert (EX2 : forall k, (k < 6)%nat ->
      ew E2 (32 + k) = nth k (GL2_EXTRA (nk_n_if kbs) j (lf_F cx fp + LO_WA)) (Z_to_bv 64 0)).
  { intros k Hk. rewrite HE2def, Eimg_low by (unfold A_TEXT; lia).
    do 6 (destruct k as [|k]; [exact (ew_Ereg_extra regs2 _ _)|]). lia. }
  assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E2 (mrestrict (w_H W3) mem2)) by constructor.
  clear HE2def.
  assert (E2_2 : ew E2 2 = w64 (lf_sp1 cx)) by (rewrite (EA2 2%nat 2%bv eq_refl); exact P2).
  assert (E2_3 : ew E2 3 = getr (c_regs cx) 3) by (rewrite (EA2 3%nat 3%bv eq_refl); exact P3).
  assert (E2_4 : ew E2 4 = getr (c_regs cx) 4) by (rewrite (EA2 4%nat 4%bv eq_refl); exact P4).
  assert (E2_8 : ew E2 8 = w64 (spZ (c_regs cx))) by (rewrite (EA2 8%nat 8%bv eq_refl); exact P8).
  assert (E2_9 : ew E2 9 = w64 (lf_sp1 cx)) by (rewrite (EA2 9%nat 9%bv eq_refl); exact P9).
  assert (E2_18 : ew E2 18 = w64 LA_G_NL) by (rewrite (EA2 18%nat 18%bv eq_refl); exact P18).
  assert (E2_19 : ew E2 19 = w64 (lf_SH cx fp)) by (rewrite (EA2 19%nat 19%bv eq_refl); exact P19).
  assert (E2_21 : ew E2 21 = w64 (LA_G_NAMES + 8 * j)) by (rewrite (EA2 21%nat 21%bv eq_refl); exact P21).
  assert (E2_22 : ew E2 22 = w64 LA_STR) by (rewrite (EA2 22%nat 22%bv eq_refl); exact P22).
  assert (E2_23 : ew E2 23 = w64 (64 - j)) by (rewrite (EA2 23%nat 23%bv eq_refl); exact P23).
  assert (E2_26 : ew E2 26 = w64 (LA_G_NL + 0x42000)) by (rewrite (EA2 26%nat 26%bv eq_refl); exact P26).
  assert (E2_32 : ew E2 32 = Z_to_bv 64 SB) by exact (EX2 0%nat ltac:(lia)).
  assert (E2_33 : ew E2 33 = Z_to_bv 64 (nk_n_if kbs)) by exact (EX2 1%nat ltac:(lia)).
  assert (E2_34 : ew E2 34 = Z_to_bv 64 j) by exact (EX2 2%nat ltac:(lia)).
  assert (E2_35 : ew E2 35 = Z_to_bv 64 (gl_aname (nk_n_if kbs))) by exact (EX2 3%nat ltac:(lia)).
  assert (E2_36 : ew E2 36 = Z_to_bv 64 (gl_aidx (nk_n_if kbs))) by exact (EX2 4%nat ltac:(lia)).
  assert (E2_37 : ew E2 37 = Z_to_bv 64 (lf_F cx fp + LO_WA)) by exact (EX2 5%nat ltac:(lia)).
  clear EA2 EX2.
  assert (GU9 : bv_unsigned (ew E2 9) = lf_sp1 cx)
    by (rewrite E2_9; unfold w64; apply unsigned_lit_small; lia).
  assert (GU26 : bv_unsigned (ew E2 26) = LA_G_NL + 0x42000)
    by (rewrite E2_26; unfold w64; apply unsigned_lit_small; unfold LA_G_NL; lia).
  assert (GU35 : bv_unsigned (ew E2 35) = gl_aname (nk_n_if kbs))
    by (rewrite E2_35; apply unsigned_lit_small; unfold gl_aname, LA_G_NL, NK_IF_NAME; lia).
  assert (GU36 : bv_unsigned (ew E2 36) = gl_aidx (nk_n_if kbs))
    by (rewrite E2_36; apply unsigned_lit_small; unfold gl_aidx, LA_G_NL, NK_IF_INDEX; lia).
  clear HS SHOK HJ.
  rename HS2 into HS. rename SHOK2 into SHOK. rename HJ2 into HJ.
  assert (KW : kagree SEGS (gl_XW (lf_sp1 cx) (nk_n_if kbs)) (rdW W3 mem2) (rdW W3 mem2))
    by apply kagree_refl.
  assert (GW : mem_grows (rdW W3 mem2) (rdW W3 mem2)) by apply mem_grows_refl.
  (* ---- what the whole turn may not change, and the bytes it leaves present ---- *)
  assert (HCEIL : alloc_ceiling <= spZ (c_regs cx) - LLVMF_STK).
  { pose proof HJ as (HSTKx & HXOx & (memSx & HJix & _) & _).
    pose proof HJix as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkx & _).
    destruct Hstkx as (_ & _ & Hceilx & Hslox & Hshix & H47x & _).
    rewrite !Z.add_0_r in Hslox, Hshix. lia. }
  assert (HOUT : forall a, 0 <= a < 2 ^ 64 ->
      ~ (LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE) -> ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE) ->
      a < alloc_ceiling -> gl_out (lf_sp1 cx) a).
  { intros a Ha H1 H2 H3. unfold gl_out, LS_ODD, LINK_SNP_STK, ESTACK, LLVMF_STK in *.
    repeat split; try assumption; lia. }
  assert (HAMF : forall a, amf_fp MS (c_T cx) a -> gl_out (lf_sp1 cx) a).
  { intros a [Hh | [He | (f & n & Hin & Hf)]].
    - rewrite HMSE in Hh.
      cbv [amf_head_addr amf_ofl_head amf_sink_addr amf_say_addr amf_ofl_lock link_amf] in Hh.
      apply HOUT; unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE in *; lia.
    - rewrite HMSE in He.
      cbv [amf_env_addr amf_threaded amf_need_locks amf_ofl_lock link_amf] in He.
      apply HOUT; unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE in *; lia.
    - pose proof (J11 _ Hin) as Hb.
      destruct (al_blocks SEGS B LAWS ly3 S3 W3 mem2 md2 f n HAR2 Hb)
        as (Hal0 & H4096 & Hce & _ & _ & _ & Hnr).
      pose proof (blk_off_imgP B ly3 S3 W3 mem2 md2 f n HAR2 Hb) as Hoff.
      pose proof (req_size_pos n ltac:(lia)) as (Hq1 & Hq2).
      assert (Hn : n = AMF_BLOCK).
      { destruct J8 as [(_ & HT) | (f0 & _ & HT & _)]; rewrite HT in Hin;
          [destruct Hin | destruct Hin as [Heq | []]; injection Heq as _ Heq2; lia]. }
      subst n. unfold AMF_BLOCK in *.
      unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
      apply HOUT; unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE in *; lia. }
  assert (HPAY : forall a, c_p cx <= a < c_p cx + c_n cx -> gl_out (lf_sp1 cx) a).
  { intros a Ha.
    pose proof HPRE as (HAFN2 & _ & _ & _ & HPB & _).
    pose proof HAFN2 as (HARp & _).
    destruct HPB as [(Hn0 & Hp0) | (Hn0 & Hb)]; [lia|].
    destruct (al_blocks SEGS B LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      (c_p cx) (c_n cx) HARp Hb) as (Hal0 & H4096 & Hce & _ & _ & _ & Hnr).
    pose proof (blk_off_imgP B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      (c_p cx) (c_n cx) HARp Hb) as Hoff.
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (Hq1 & Hq2).
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
    apply HOUT; unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_SIZE in *; lia. }
  assert (HFIN : In (LF_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem2 md2 LF_CID fp HAR2 HFIN) as (HFa & HFb & _).
  rewrite (proj1 LF_frame_slot), (J2 LF_CID fp) in HFb. rewrite (J2 LF_CID fp) in HFa.
  pose proof (frm_off_imgP B ly3 S3 W3 mem2 md2 LF_CID fp HAR2 HFIN) as HFimg.
  rewrite (proj1 LF_frame_slot), (J2 LF_CID fp) in HFimg.
  (* the bytes of g_nl and g_names at the cut *)
  assert (HM0NL : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
      mbyte SEGS (rdW W3 (ms_mem ms3)) a <> None).
  { intros a Ha. pose proof HNK as ((Hab & _) & HL). destruct Hab as (_ & _ & Hb).
    replace a with (LA_G_NL + Z.of_nat (Z.to_nat (a - LA_G_NL))) by lia.
    rewrite (Hb (Z.to_nat (a - LA_G_NL)) ltac:(lia)).
    destruct (nth_error kbs (Z.to_nat (a - LA_G_NL))) eqn:Ee; [discriminate|].
    apply nth_error_None in Ee. lia. }
  assert (HM0GN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE ->
      mbyte SEGS (rdW W3 (ms_mem ms3)) a <> None).
  { intros a Ha. destruct HGW as (junk & Hjl & (Hab & _)). destruct Hab as (_ & _ & Hb).
    replace a with (LA_G_NAMES + Z.of_nat (Z.to_nat (a - LA_G_NAMES))) by lia.
    rewrite (Hb (Z.to_nat (a - LA_G_NAMES)) ltac:(unfold G_NAMES_SIZE in *; lia)).
    destruct (nth_error junk (Z.to_nat (a - LA_G_NAMES))) eqn:Ee; [discriminate|].
    apply nth_error_None in Ee. unfold G_NAMES_SIZE in *. lia. }
  assert (PR2 : forall a, 0 <= a < 2 ^ 64 ->
      ~ (LA_G_NAMES + 8 * j <= a <= LA_G_NAMES + 8 * j + Z.of_nat (length (lf_gname_z j))) ->
      mbyte SEGS (rdW W3 (ms_mem ms3)) a <> None ->
      apresent (w_H W3) mem2 a \/ seg_rom SEGS (Z_to_bv 64 a) <> None).
  { intros a Ha Hd Hm.
    destruct (gl_present_of_mbyte SEGS (w_H W3) (ms_mem ms3) a Hm) as [Hp | Hr]; [|right; exact Hr].
    left. apply HPRE2; [exact Ha | | exact Hd].
    apply (gl_apresent_mr (w_H W3) (ms_mem ms3) (ms_mem ms) a); [intros x; symmetry; apply HM01 | exact Hp]. }
  (* ---- +0x344 .. +0x34c, and the turn's test ---- *)
  gl_run. gl_acc.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* j mod 16 = 15: the turn appends nothing *)
    assert (Hm15 : j mod 16 = 15)
      by (rewrite (gl_br_skip E2 j E2_34 Hj) in Hc; apply Z.eqb_eq; exact Hc).
    clear Hc.
    gl_run. gl_acc.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
        rewrite (gl_br_back Ex j ltac:(gl_ew E2_23) Hj) in Hc end.
      assert (Hlt : j < 63) by (apply negb_true_iff, Z.eqb_neq in Hc; lia).
      gl_run_to LF_gl. gl_acc.
      gl_mem_end.
      lazymatch goal with |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      assert (FDF : m_fds mdF = m_fds md3 /\ m_fs mdF = m_fs md3)
        by (rewrite ?lf_wvb_fds, ?lf_wvb_fs; exact FD2);
      assert (VN : val_mem SEGS (rdW W3 (ms_mem msF)) (LA_G_NL + NK_N_IF) 4 (nk_n_if kbs))
        by (spregion HS 3%nat HR3;
            pose proof (field_of_region (segs := SEGS) _ _ 26%nat (LA_G_NL + 0x42000) _ _ _ _ _
              1648 4%N (SOff 33 0) (nk_n_if kbs) HR3 ltac:(gl_ew GU26)
              ltac:(cbn [In]; left; reflexivity)
              ltac:(exact (gl_den_off0 _ 33%nat _ ltac:(gl_ew E2_33)))
              ltac:(cbn; lia) ltac:(cbn; lia)) as HV;
            replace (LA_G_NL + 0x42000 + 1648) with (LA_G_NL + NK_N_IF) in HV by (unfold NK_N_IF; lia);
            exact HV);
      assert (C : gl_ctx cx fp j (nk_n_if kbs) (c_T cx) W3 ms3 msF)
        by (constructor;
            [ exact Hj | exact HNIF2 | exact Hs1 | exact Hs2 | exact Hs5 | exact HCEIL | exact Hs6
            | exact HFa | exact HFb | exact HFimg | exact HLAN | exact HAMF | exact HPAY
            | exact KX | exact PNL | exact PGN | exact BYF
            | replace (j mod 16 =? 15) with true by (symmetry; apply Z.eqb_eq; exact Hm15);
              cbn [negb]; exact VN
            | intros Hcc; rewrite (proj2 (Z.eqb_eq _ _) Hm15) in Hcc; cbn [negb] in Hcc; discriminate
            | intros Hcc; rewrite (proj2 (Z.eqb_eq _ _) Hm15) in Hcc; cbn [negb] in Hcc; discriminate ]);
      apply (HNX Hlt cx fy' fp k2 ly3 S3 W3 msF mdF HB HFXY2 HJ HFR);
      apply (gl_gl_build cx fy fy' fp k2 j (nk_n_if kbs) ly3 S3 W3 ms3 msF md3 mdF Hlt C
        (proj1 FDF) (proj2 FDF));
      [ exact (lf_shape_of_st_ok fy' W3 _ _ _ HS eq_refl)
      | split; [gl_rg (2%bv : bv 5) E2_2 | split; [gl_rg (8%bv : bv 5) E2_8 | split; [gl_rg (9%bv : bv 5) E2_9 |
          split; [gl_rg (3%bv : bv 5) E2_3 | gl_rg (4%bv : bv 5) E2_4]]]]
      | gl_rg (18%bv : bv 5) E2_18 | gl_rg (19%bv : bv 5) E2_19
      | gl_rgo (21%bv : bv 5) 21%nat (LA_G_NAMES + 8 * j) 8 E2_21
      | gl_rg (22%bv : bv 5) E2_22
      | gl_rgo (23%bv : bv 5) 23%nat (64 - j) (-1) E2_23
      | gl_rgo (24%bv : bv 5) 34%nat j 3 E2_34
      | gl_rgl (25%bv : bv 5) | gl_rg (26%bv : bv 5) E2_26 | gl_rgl (27%bv : bv 5)
      | exact GI ]
      end.
    * lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
        rewrite (gl_br_back Ex j ltac:(gl_ew E2_23) Hj) in Hc end.
      assert (Hj63 : j = 63) by (apply negb_false_iff, Z.eqb_eq in Hc; lia).
      gl_run_to LF_ol. gl_acc.
      gl_mem_end.
      assert (HODDV : VAL 248%nat = LA_ODD)
        by (change (248%nat) with (A_OBJ 7);
            rewrite (lv_obj LV 7) by (unfold link_nobj; lia); reflexivity).
      lazymatch goal with |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      assert (FDF : m_fds mdF = m_fds md3 /\ m_fs mdF = m_fs md3)
        by (rewrite ?lf_wvb_fds, ?lf_wvb_fs; exact FD2);
      assert (E248 : forall Ex : env, img_env VAL A_LIM Ex -> ew Ex 248 = Z_to_bv 64 LA_ODD)
        by (intros Ex HEx; rewrite (img_env_atomP Ex 248%nat HEx ltac:(unfold A_TEXT, A_LIM; lia));
            rewrite HODDV; reflexivity);
      assert (VN : val_mem SEGS (rdW W3 (ms_mem msF)) (LA_G_NL + NK_N_IF) 4 (nk_n_if kbs))
        by (spregion HS 3%nat HR3;
            pose proof (field_of_region (segs := SEGS) _ _ 26%nat (LA_G_NL + 0x42000) _ _ _ _ _
              1648 4%N (SOff 33 0) (nk_n_if kbs) HR3 ltac:(gl_ew GU26)
              ltac:(cbn [In]; left; reflexivity)
              ltac:(exact (gl_den_off0 _ 33%nat _ ltac:(gl_ew E2_33)))
              ltac:(cbn; lia) ltac:(cbn; lia)) as HV;
            replace (LA_G_NL + 0x42000 + 1648) with (LA_G_NL + NK_N_IF) in HV by (unfold NK_N_IF; lia);
            exact HV);
      assert (VODD : lf_slot cx W3 msF LS_ODD LA_ODD)
        by (spregion HS 2%nat HR2;
            pose proof (field_of_region (segs := SEGS) _ _ 9%nat (lf_sp1 cx) _ _ _ _ _
              80 8%N (SOff 248 0) LA_ODD HR2 ltac:(gl_ew GU9)
              ltac:(cbn [In]; left; reflexivity)
              ltac:(lazymatch goal with |- sv_denot ?Ex _ = _ =>
                      exact (gl_den_off0 Ex _ _ (E248 Ex ltac:(assumption))) end)
              ltac:(cbn; unfold LA_ODD; lia) ltac:(cbn; lia)) as HV;
            unfold lf_slot, lf_at, LS_ODD;
            apply rdword_of_val_mem; [exact HV | unfold LA_ODD; lia]);
      assert (C : gl_ctx cx fp j (nk_n_if kbs) (c_T cx) W3 ms3 msF)
        by (constructor;
            [ exact Hj | exact HNIF2 | exact Hs1 | exact Hs2 | exact Hs5 | exact HCEIL | exact Hs6
            | exact HFa | exact HFb | exact HFimg | exact HLAN | exact HAMF | exact HPAY
            | exact KX | exact PNL | exact PGN | exact BYF
            | replace (j mod 16 =? 15) with true by (symmetry; apply Z.eqb_eq; exact Hm15);
              cbn [negb]; exact VN
            | intros Hcc; rewrite (proj2 (Z.eqb_eq _ _) Hm15) in Hcc; cbn [negb] in Hcc; discriminate
            | intros Hcc; rewrite (proj2 (Z.eqb_eq _ _) Hm15) in Hcc; cbn [negb] in Hcc; discriminate ]);
      apply (HOL cx fy' fp k2 ly3 S3 W3 msF mdF HB HFXY2 HJ HFR);
      apply (gl_ol_build cx fy fy' fp k2 j (nk_n_if kbs) ly3 S3 W3 ms3 msF md3 mdF Hj63 C
        (proj1 FDF) (proj2 FDF));
      [ exact (lf_shape_of_st_ok fy' W3 _ _ _ HS eq_refl)
      | split; [gl_rg (2%bv : bv 5) E2_2 | split; [gl_rg (8%bv : bv 5) E2_8 | split; [gl_rg (9%bv : bv 5) E2_9 |
          split; [gl_rg (3%bv : bv 5) E2_3 | gl_rg (4%bv : bv 5) E2_4]]]]
      | gl_rg (18%bv : bv 5) E2_18 | gl_rg (19%bv : bv 5) E2_19 | gl_rg (26%bv : bv 5) E2_37 | gl_rg (27%bv : bv 5) E2_32
      | exact VODD
      | gl_rgl (11%bv : bv 5) | gl_rgl (12%bv : bv 5)
      | gl_rgo (13%bv : bv 5) 18%nat LA_G_NL 270336 E2_18 | gl_rgl (14%bv : bv 5) | gl_rgl (15%bv : bv 5)
      | lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
          rewrite (st_ok_pi_restrict_reg _ Ex ss msx (16%bv : bv 5) HS);
          let e := eval vm_compute in (sr_get (ss_regs ss) (16%bv : bv 5)) in
          change (sr_get (ss_regs ss) (16%bv : bv 5)) with e;
          rewrite (lf_sv_off Ex 248%nat LA_ODD 8 (E248 Ex ltac:(assumption))
            ltac:(unfold LA_ODD; lia) ltac:(unfold LA_ODD; lia));
          unfold w64; f_equal; lia end
      | lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
          rewrite (st_ok_pi_restrict_reg _ Ex ss msx (17%bv : bv 5) HS);
          let e := eval vm_compute in (sr_get (ss_regs ss) (17%bv : bv 5)) in
          change (sr_get (ss_regs ss) (17%bv : bv 5)) with e;
          rewrite (gl_den_a7 Ex SB LA_ODD ltac:(gl_ew E2_32) (E248 Ex ltac:(assumption))
            ltac:(unfold SB; lia) ltac:(unfold LA_ODD; lia) ltac:(unfold LA_ODD; lia)
            ltac:(unfold SB, LA_ODD; cbn; lia));
          rewrite <- SB_SHADOW_OFF; unfold w64; f_equal; lia end
      | gl_rgl (5%bv : bv 5) | exact GI ]
      end.
  + (* j mod 16 <> 15: the turn appends (g_names + 8 j, j + 2) *)
    assert (Hm15 : j mod 16 <> 15)
      by (rewrite (gl_br_skip E2 j E2_34 Hj) in Hc; apply Z.eqb_neq; exact Hc).
    clear Hc.
    gl_run_to (AF_LLVMFuzzerTestOneInput + 0x360). gl_acc.
    prreg_raw HS (10%bv : bv 5) A10.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss ?msx =>
      pose proof (st_ok_pi_set_reg Ex ss msx 10%bv (SOff 35 0) HS ltac:(cbv; discriminate)
        ltac:(cbn [ms_regs restrict]; rewrite A10;
              apply (gl_pin_name Ex (nk_n_if kbs)); [gl_ew E2_18 | gl_ew E2_33 | gl_ew E2_35 | exact Hnif])) as HSp
    end.
    clear HS A10. rename HSp into HS.
    gl_run_to (AF_LLVMFuzzerTestOneInput + 0x394). gl_acc.
    prreg_raw HS (10%bv : bv 5) A10.
    (* the engine's address at +0x390 is the index slot's atom *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss ?msx =>
      pose proof (st_ok_pi_set_reg Ex ss msx 10%bv (SOff 36 0) HS ltac:(cbv; discriminate)
        ltac:(cbn [ms_regs restrict]; rewrite A10;
              apply (gl_pin_index Ex (nk_n_if kbs)); [gl_ew E2_18 | gl_ew E2_33 | gl_ew E2_36 | exact Hnif])) as HSp
    end.
    clear HS A10. rename HSp into HS.
    gl_run. gl_acc.
    (* the back edge *)
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
        rewrite (gl_br_back Ex j ltac:(gl_ew E2_23) Hj) in Hc end.
      assert (Hlt : j < 63) by (apply negb_true_iff, Z.eqb_neq in Hc; lia).
      gl_run_to LF_gl. gl_acc.
      gl_mem_end.
      lazymatch goal with |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      assert (FDF : m_fds mdF = m_fds md3 /\ m_fs mdF = m_fs md3)
        by (rewrite ?lf_wvb_fds, ?lf_wvb_fs; exact FD2);
      assert (VN : val_mem SEGS (rdW W3 (ms_mem msF)) (LA_G_NL + NK_N_IF) 4 (nk_n_if kbs + 1))
        by (spregion HS 3%nat HR3;
            pose proof (field_of_region (segs := SEGS) _ _ 26%nat (LA_G_NL + 0x42000) _ _ _ _ _
              1648 4%N (SOff 33 1) (nk_n_if kbs + 1) HR3 ltac:(gl_ew GU26)
              ltac:(cbn [In]; left; reflexivity)
              ltac:(exact (lf_sv_off _ 33%nat (nk_n_if kbs) 1 ltac:(gl_ew E2_33) ltac:(lia) ltac:(lia)))
              ltac:(cbn; lia) ltac:(cbn; lia)) as HV;
            replace (LA_G_NL + 0x42000 + 1648) with (LA_G_NL + NK_N_IF) in HV by (unfold NK_N_IF; lia);
            exact HV);
      assert (VNAME : val_mem SEGS (rdW W3 (ms_mem msF)) (gl_aname (nk_n_if kbs)) 8
                        (LA_G_NAMES + 8 * j))
        by (spregion HS 4%nat HR4;
            pose proof (field_of_region (segs := SEGS) _ _ 35%nat (gl_aname (nk_n_if kbs)) _ _ _ _ _
              0 8%N (SOff 21 0) (LA_G_NAMES + 8 * j) HR4 ltac:(gl_ew GU35)
              ltac:(cbn [In]; left; reflexivity)
              ltac:(exact (gl_den_off0 _ 21%nat _ ltac:(gl_ew E2_21)))
              ltac:(cbn; unfold LA_G_NAMES; lia) ltac:(cbn; lia)) as HV;
            rewrite Z.add_0_r in HV; exact HV);
      assert (VIDX : val_mem SEGS (rdW W3 (ms_mem msF)) (gl_aidx (nk_n_if kbs)) 4 (j + 2))
        by (spregion HS 5%nat HR5;
            pose proof (field_of_region (segs := SEGS) _ _ 36%nat (gl_aidx (nk_n_if kbs)) _ _ _ _ _
              0 4%N (SOff 34 2) (j + 2) HR5 ltac:(gl_ew GU36)
              ltac:(cbn [In]; left; reflexivity)
              ltac:(exact (lf_sv_off _ 34%nat j 2 ltac:(gl_ew E2_34) ltac:(lia) ltac:(lia)))
              ltac:(cbn; lia) ltac:(cbn; lia)) as HV;
            rewrite Z.add_0_r in HV; exact HV);
      assert (C : gl_ctx cx fp j (nk_n_if kbs) (c_T cx) W3 ms3 msF)
        by (constructor;
            [ exact Hj | exact HNIF2 | exact Hs1 | exact Hs2 | exact Hs5 | exact HCEIL | exact Hs6
            | exact HFa | exact HFb | exact HFimg | exact HLAN | exact HAMF | exact HPAY
            | exact KX | exact PNL | exact PGN | exact BYF
            | replace (j mod 16 =? 15) with false by (symmetry; apply Z.eqb_neq; exact Hm15);
              cbn [negb]; exact VN
            | intros _; exact VNAME | intros _; exact VIDX ]);
      apply (HNX Hlt cx fy' fp k2 ly3 S3 W3 msF mdF HB HFXY2 HJ HFR);
      apply (gl_gl_build cx fy fy' fp k2 j (nk_n_if kbs) ly3 S3 W3 ms3 msF md3 mdF Hlt C
        (proj1 FDF) (proj2 FDF));
      [ exact (lf_shape_of_st_ok fy' W3 _ _ _ HS eq_refl)
      | split; [gl_rg (2%bv : bv 5) E2_2 | split; [gl_rg (8%bv : bv 5) E2_8 | split; [gl_rg (9%bv : bv 5) E2_9 |
          split; [gl_rg (3%bv : bv 5) E2_3 | gl_rg (4%bv : bv 5) E2_4]]]]
      | gl_rg (18%bv : bv 5) E2_18 | gl_rg (19%bv : bv 5) E2_19
      | gl_rgo (21%bv : bv 5) 21%nat (LA_G_NAMES + 8 * j) 8 E2_21
      | gl_rg (22%bv : bv 5) E2_22
      | gl_rgo (23%bv : bv 5) 23%nat (64 - j) (-1) E2_23
      | gl_rgo (24%bv : bv 5) 34%nat j 3 E2_34
      | gl_rgl (25%bv : bv 5) | gl_rg (26%bv : bv 5) E2_26 | gl_rgl (27%bv : bv 5)
      | exact GI ]
      end.
    * exfalso.
      lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
        rewrite (gl_br_back Ex j ltac:(gl_ew E2_23) Hj) in Hc end.
      apply negb_false_iff, Z.eqb_eq in Hc. apply Hm15. replace j with 63 by lia. reflexivity.
Qed.

(* THE LOOP: by induction on the turns left *)
Lemma lf_gl : forall POST, FROM POST (OL 0) -> forall j, 0 <= j < 64 -> FROM POST (GL j).
Proof.
  intros POST HOL.
  assert (IND : forall (n : nat) j, 0 <= j < 64 -> 64 - j = Z.of_nat n -> FROM POST (GL j)).
  { induction n as [|n IH]; intros j Hj Hn; [lia|].
    apply (gl_turn POST j Hj HOL). intros Hlt. apply (IH (j + 1)); lia. }
  intros j Hj. apply (IND (Z.to_nat (64 - j)) j Hj). lia.
Qed.

End w.
