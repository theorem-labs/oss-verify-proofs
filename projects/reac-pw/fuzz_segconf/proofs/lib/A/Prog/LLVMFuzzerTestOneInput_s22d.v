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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 649 of its 691 lines of code are new or changed and 411 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): piece 4 of segment S14 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s22d: the parent
   loop of the inlined m_split, 0x85a18 <- 0x85a78 (dis:827-855), the statement s22_p4_stmt of
   LLVMFuzzerTestOneInput_s22k.v.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; checker (fresh, read-only): CONFIRM; none: written new)

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s43.v (origin/ossv/recipes
   501c0d516c69, the trim loop: one seed per pass holding only what the pass reads, the symbolic engine's runs and
   their branches, the loop by induction on its counter). One pass, from 0x85a18 with t bytes checked:
     0x85a18  srli/add/lb/bnez  check 34 of name[t] at a0 = &m->seg[i] + t (a token: the 1-byte obligation, closed
                                from m's block; the slow block 0x85a80 `andi; bge; j 85a28` is the token's)
     0x85a28  lbu a3,0(a2)      the byte b (a2 = a0: the region at atom 10)
     0x85a34  bltu (b-48)&255, t0 = 10           a digit: on to 0x85a6c (SegModel.isdigit, s22_dig_b)
     0x85a48  bltu ((b&~32)-65)&255, 26          a letter: on to 0x85a6c (s22_alpha_b)
     0x85a58  bltu 50, (b&255)-45                outside [45, 95]: to 0x85b88 (s22_pk_out)
     0x85a5c  ld 136(s1) = the mask; bit b - 45; beqz to 0x85b88 (s22_mask_bit, s22_pk_rest)
     0x85a6c  a1, a0, a2 by one; bnez a1 back to 0x85a18 (the next pass, the induction hypothesis), else
     0x85a7c  j 0x85a8c = S22_VM (every byte of firstn di name passed: m_split gives (firstn di name, vid))
     0x85b88  li s4,4; j 0x859c4 = S22_JOIN (a byte failed: m_split is None, turn i adds nothing).
   The pass stores nothing: every region of its seed is read-only, so the reader after each run is the reader
   before it (p_view_ro), and s22_inv moves to the new registers and memory by p_inv_kept. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YI09 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s22k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the seed of a pass at 0x85a18 ======================= *)
(* the shadow base is a5 (atom 15); the byte name[t] at a0 = a2 (atom 10) is atom 32; the mask at 136(s1)
   (atom 9) is the literal LT_MASK; t0 = 10 *)
Definition PBx : sv := SOff 15 0.
Definition Pspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition p_byte : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition p_mask : YP09.region :=
  YP09.mkRegion (Some 9%nat) 136 144 136 136 [YP09.mkChunk 136 (CVal 8 (SLit LT_MASK))].
Definition p_facts : facts :=
  mkFacts [ (10%nat, mkAF 4096 0x7fffffffffff 0); (15%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0) ]
    [] [].
Definition p_sregs : list sv := sr_set (sr_set sr_atoms (5%bv : bv 5) (SLit 10)) (12%bv : bv 5) (SOff 10 0).
Definition ss_p : sstate := mkSS S22_VP p_sregs [p_byte; p_mask] None p_facts.
(* every region of a state is read-only *)
Definition p_ro (rs : smem) : bool := forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs.
(* the registers a pass keeps (s4 = 20 apart: the failure path sets it to 4) *)
Definition p_KR : list (bv 5) := [2; 3; 4; 8; 9; 15; 16; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition p_kept (sr : list sv) (l : list (bv 5)) : bool :=
  forallb (fun r => sv_eqb (sr_get sr r) (SOff (Z.to_nat (bv_unsigned r)) 0)) l.
Definition p_agree (E E0 : env) : Prop := forall n, (n < 32)%nat -> ew E n = ew E0 n.
Definition p_ev (E0 : env) (regs : bvmap 5 word) : Prop :=
  forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r.

Ltac p_in := unfold p_KR; repeat first [left; reflexivity | right].
Ltac p_vm := vm_compute; reflexivity.
Ltac p_ag := unfold p_agree; intros ?q ?Hq; repeat (rewrite ew_ewset_other by lia); reflexivity.
Ltac p_e32 E32 := repeat (rewrite ew_ewset_other by lia); exact E32.

(* ======================= the engine's terms of the byte tests ======================= *)
Lemma p_mod256 : forall x, (x mod 2 ^ 64) mod 256 = x mod 256.
Proof.
intros x. rewrite (Z.div_mod x (2 ^ 64)) at 2 by lia.
rewrite Z.add_comm. replace (2 ^ 64 * (x / 2 ^ 64)) with ((2 ^ 56 * (x / 2 ^ 64)) * 256) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma p_U_and255 : forall E a, U E (SAlu ALU_AND a (SLit 255)) = U E a mod 256.
Proof. intros E a. rewrite U_and_lit by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma p_U_add_lit : forall E a c, U E (SAlu ALU_ADD a (SLit c)) = (U E a + c) mod 2 ^ 64.
Proof. intros E a c. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. unfold zcanon, M64. apply Zplus_mod_idemp_r. Qed.
(* 0x85a2c .. 0x85a30: (b - 48) & 255 *)
Lemma p_U_dig : forall E b, ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_AND (SOff 32 (-48)) (SLit 255)) = (b - 48) mod 256.
Proof.
intros E b H Hb. rewrite p_U_and255. rewrite U_SOff, H, unsigned_lit_small by lia. unfold zcanon, M64.
rewrite p_mod256. f_equal; lia.
Qed.
(* 0x85a38 .. 0x85a40: ((b & ~32) - 65) & 255 *)
Lemma p_U_alpha : forall E b, ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 0) (SLit (-33))) (SLit (-65))) (SLit 255)) =
  (Z.land b 18446744073709551583 - 65) mod 256.
Proof.
intros E b H Hb. rewrite p_U_and255, p_U_add_lit. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 32 b H) by lia. rewrite U_SLit.
change (zcanon (-33)) with 18446744073709551583.
pose proof (Z_land_upper b 18446744073709551583 ltac:(lia)) as HL.
rewrite (zcanon_id (Z.land b 18446744073709551583)) by (unfold M64; lia).
rewrite p_mod256. f_equal; lia.
Qed.
(* 0x85a4c .. 0x85a50: (b & 255) - 45 *)
Lemma p_U_rng : forall E b, ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 0) (SLit 255)) (SLit (-45))) = (b - 45) mod 2 ^ 64.
Proof.
intros E b H Hb. rewrite p_U_add_lit, p_U_and255, (U_atom E 32 b H) by lia.
rewrite (Z.mod_small b 256) by lia. f_equal; lia.
Qed.
(* 0x85a60 .. 0x85a64: bit b - 45 of the mask *)
Lemma p_U_mask : forall E b, ew E 32 = Z_to_bv 64 b -> 45 <= b <= 95 ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SLit 1125899906850819)
         (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 0) (SLit 255)) (SLit (-45)))) (SLit 1)) =
  Z.land (Z.shiftr S22_MASK (b - 45)) 1.
Proof.
intros E b H Hb. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw].
rewrite (p_U_rng E b H) by lia. rewrite U_lit by lia.
rewrite (Z.mod_small (b - 45) (2 ^ 64)) by lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite (Z.mod_small (b - 45) (2 ^ 6)) by lia.
rewrite zcanon_id; [reflexivity|].
pose proof (Z.pow_pos_nonneg 2 (b - 45) ltac:(lia) ltac:(lia)) as Hp.
rewrite Z.shiftr_div_pow2 by lia. unfold M64. split; [apply Z.div_pos; lia|].
apply (Z.le_lt_trans _ 1125899906850819); [|lia]. apply Z.div_le_upper_bound; lia.
Qed.

(* the five tests as facts about b *)
Lemma p_dig_c : forall E b c,
  branch_taken BC_LTU (sv_denot E (SAlu ALU_AND (SOff 32 (-48)) (SLit 255))) (sv_denot E (SLit 10)) = c ->
  ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 -> SegModel.isdigit b = c.
Proof.
intros E b c Hc H Hb. rewrite branch_ltu_U, (p_U_dig E b H Hb), U_lit in Hc by lia.
rewrite <- (s22_dig_b b Hb). exact Hc.
Qed.
Lemma p_alpha_c : forall E b c,
  branch_taken BC_LTU
    (sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 0) (SLit (-33))) (SLit (-65))) (SLit 255)))
    (sv_denot E (SLit 26)) = c ->
  ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 -> s22_alpha b = c.
Proof.
intros E b c Hc H Hb. rewrite branch_ltu_U, (p_U_alpha E b H Hb), U_lit in Hc by lia.
rewrite <- (s22_alpha_b b Hb). exact Hc.
Qed.
Lemma p_rng_t : forall E b,
  branch_taken BC_LTU (sv_denot E (SLit 50))
    (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 0) (SLit 255)) (SLit (-45)))) = true ->
  ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 -> b < 45 \/ 95 < b.
Proof.
intros E b Hc H Hb. rewrite branch_ltu_U, U_lit, (p_U_rng E b H Hb) in Hc by lia. apply Z.ltb_lt in Hc.
destruct (Z.ltb_spec b 45) as [Hlt|Hge]; [left; exact Hlt|right].
rewrite Z.mod_small in Hc by lia. lia.
Qed.
Lemma p_rng_f : forall E b,
  branch_taken BC_LTU (sv_denot E (SLit 50))
    (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 0) (SLit 255)) (SLit (-45)))) = false ->
  ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 -> 45 <= b <= 95.
Proof.
intros E b Hc H Hb. rewrite branch_ltu_U, U_lit, (p_U_rng E b H Hb) in Hc by lia. apply Z.ltb_ge in Hc.
destruct (Z.ltb_spec b 45) as [Hlt|Hge].
- exfalso. rewrite <- (Z_mod_plus_full (b - 45) 1 (2 ^ 64)) in Hc. rewrite Z.mod_small in Hc by lia. lia.
- rewrite Z.mod_small in Hc by lia. lia.
Qed.
Lemma p_mask_c : forall E b c,
  branch_taken BC_EQ
    (sv_denot E (SAlu ALU_AND (SAlu ALU_SRL (SLit 1125899906850819)
       (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 0) (SLit 255)) (SLit (-45)))) (SLit 1)))
    (sv_denot E (SLit 0)) = c ->
  ew E 32 = Z_to_bv 64 b -> 45 <= b <= 95 -> s22_pkr b = negb c.
Proof.
intros E b c Hc H Hb. rewrite branch_eq_U, (p_U_mask E b H Hb), U_lit in Hc by lia.
rewrite (s22_mask_bit (b - 45)) in Hc by lia. unfold s22_pkr.
destruct (((b - 45 =? 0) || (b - 45 =? 1) || (b - 45 =? 13) || (b - 45 =? 50))%bool); cbn in Hc; subst c; reflexivity.
Qed.

(* ======================= m_split at the loop's two exits ======================= *)
Lemma p_split_some : forall nm di vid,
  SegModel.nulfree nm -> SegModel.strrchr nm 46 = Some di -> (di <> 0)%nat ->
  SegModel.m_digits (skipn (S di) nm) 0 = Some vid -> 1 <= vid ->
  forallb SegModel.h_parent_ok (firstn di nm) = true ->
  SegModel.m_split nm = Some (firstn di nm, vid).
Proof.
intros nm di vid Hnf Hs Hd0 Hdg Hv Hall.
assert (Hne : SegModel.hd0 (skipn (S di) nm) <> 0).
{ case_eq (skipn (S di) nm).
  - intros Esk. rewrite Esk in Hdg. cbn in Hdg. injection Hdg as <-. exfalso. lia.
  - intros q r Esk. cbn [SegModel.hd0]. intros Hq. apply Hnf.
    rewrite <- (firstn_skipn (S di) nm). rewrite Esk. apply in_or_app. right. left. exact Hq. }
unfold SegModel.m_split. rewrite Hs. cbv beta iota.
destruct (Nat.eqb_spec di 0) as [E0|_]; [exfalso; lia|].
destruct (Z.eqb_spec (SegModel.hd0 (skipn (S di) nm)) 0) as [E1|_]; [contradiction|].
cbn [orb]. rewrite Hdg. cbv beta iota.
destruct (Z.ltb_spec vid 1) as [E2|_]; [exfalso; lia|]. rewrite Hall. reflexivity.
Qed.
Lemma p_split_none : forall nm di vid t,
  SegModel.strrchr nm 46 = Some di -> SegModel.m_digits (skipn (S di) nm) 0 = Some vid ->
  (t < di)%nat -> (di < length nm)%nat -> SegModel.h_parent_ok (nth t nm 0) = false ->
  SegModel.m_split nm = None.
Proof.
intros nm di vid t Hs Hdg Ht Hdl Hf. unfold SegModel.m_split. rewrite Hs. cbv beta iota.
destruct ((di =? 0)%nat || (SegModel.hd0 (skipn (S di) nm) =? 0))%bool; [reflexivity|].
rewrite Hdg. cbv beta iota. destruct (vid <? 1); [reflexivity|].
rewrite (s22_forallb_false SegModel.h_parent_ok (firstn di nm) t 0); [reflexivity | rewrite length_firstn; lia |].
rewrite nth_firstn. destruct (Nat.ltb_spec t di); [exact Hf | exfalso; lia].
Qed.

(* ======================= a reader that equals another everywhere keeps every fact ======================= *)
Section k.
Variables (rd rd' : reader).
Hypothesis K : forall a, rd' a = rd a.
Lemma k_bytes : forall a bs, sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros a bs H j Hj. rewrite K. exact (H j Hj). Qed.
Lemma k_zs : forall a l, sa_zs rd a l -> sa_zs rd' a l.
Proof. intros a l H j Hj. rewrite K. exact (H j Hj). Qed.
Lemma k_val : forall a n v, sa_val rd a n v -> sa_val rd' a n v.
Proof. intros a n v H j Hj. rewrite K. exact (H j Hj). Qed.
Lemma k_word : forall a, rdword rd' a = rdword rd a.
Proof. intros a. apply rdword_ext. intros j _. apply K. Qed.
Lemma k_ra : forall sb a n, range_addressable rd sb a n -> range_addressable rd' sb a n.
Proof. intros sb a n H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. rewrite K. split; [exact Hs | exact Ho]. Qed.
Lemma k_hull : forall a n, shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof. intros a n H s Hs. rewrite K. exact (H s Hs). Qed.
Lemma k_addr : forall a n, sa_addr rd a n -> sa_addr rd' a n.
Proof.
intros a n (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [exact (k_ra _ _ _ H4)|]. intros Hn. exact (k_hull _ _ (H5 Hn)).
Qed.
Lemma k_rconf : forall a x, sa_rconf rd a x -> sa_rconf rd' a x.
Proof. intros a x (bs & H1 & H2). exists bs. split; [exact (k_bytes _ _ H1) | exact H2]. Qed.
Lemma k_mconf : forall a x, sa_mconf rd a x -> sa_mconf rd' a x.
Proof. intros a x (bs & H1 & H2). exists bs. split; [exact (k_bytes _ _ H1) | exact H2]. Qed.
Lemma k_rtab : forall a x, sa_rtab rd a x -> sa_rtab rd' a x.
Proof. intros a x (bs & H1 & H2). exists bs. split; [exact (k_bytes _ _ H1) | exact H2]. Qed.
Lemma k_mtab : forall a x, sa_mtab rd a x -> sa_mtab rd' a x.
Proof. intros a x (bs & H1 & H2). exists bs. split; [exact (k_bytes _ _ H1) | exact H2]. Qed.
End k.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run over read-only regions leaves every byte as it was *)
Lemma p_view_ro : forall E rs H (m m' : word -> option byte),
  p_ro rs = true -> frame_of E rs (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hro Hf a. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). unfold p_ro in Hro. rewrite forallb_forall in Hro. pose proof (Hro r Hin) as Hq.
apply Z.leb_le in Hq. lia.
Qed.
Ltac p_mem W mem K :=
  lazymatch goal with HFr : frame_of ?E ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    let K2 := fresh "K" in
    assert (K2 : forall x, aview SEGS (w_H W) m2 x = aview SEGS (w_H W) mem x)
      by (intros x; rewrite (p_view_ro E rs (w_H W) m1 m2 ltac:(vm_compute; reflexivity) HFr x); apply K);
    clear K HFr; rename K2 into K
  end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end.

(* a one-byte field from a byte of the reader *)
Lemma p_val1 : forall H mem a b, 0 <= b < 256 -> aview SEGS H mem a = Some b -> val_mem SEGS (mrestrict H mem) a 1 b.
Proof.
intros H mem a b Hb Hv k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H mem) a) as [x|] eqn:Ex; cbn in Hv; [|discriminate Hv].
injection Hv as Hx. try rewrite Ex.
rewrite (le_byte_small b 1 0) by first [lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia].
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite <- Hx, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* registers after a run: an atom kept, a literal, an atom plus an offset *)
Lemma p_keep : forall E E0 ss (ms : machine_state) H (regs : bvmap 5 word) l,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> p_agree E E0 -> p_ev E0 regs ->
  p_kept (ss_regs ss) l = true -> forall r, In r l -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E E0 ss ms H regs l HS HAG EV Hl r Hr. unfold p_kept in Hl. rewrite forallb_forall in Hl.
pose proof (sv_eqb_eq _ _ (Hl r Hr)) as Hq.
pose proof (bv_unsigned_in_range 5 r) as R5. change (bv_modulus 5) with 32 in R5.
rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hq. cbn [sv_denot].
rewrite (HAG (Z.to_nat (bv_unsigned r)) ltac:(lia)).
rewrite (EV (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id by lia; reflexivity)), Z.add_0_r.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma p_reg_lit : forall E ss (ms : machine_state) H (r : bv 5) z,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = w64 z.
Proof. intros E ss ms H r z HS Hs. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs. reflexivity. Qed.
Lemma p_reg_off : forall E E0 ss (ms : machine_state) H (r : bv 5) n c v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n c ->
  ew E n = ew E0 n -> ew E0 n = w64 v -> getr (ms_regs ms) r = w64 (v + c).
Proof.
intros E E0 ss ms H r n c v HS Hs H1 H2. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs. cbn [sv_denot].
rewrite H1, H2. unfold w64. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
(* the state a run stops in, as the configuration a cut statement names *)
Lemma p_at : forall (W : world SEGS) E ss (ms : machine_state) md Q pc,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  SRr SEGS W (cfg_at SEGS (BASE + pc) (ms_regs ms) (ms_mem ms) md) Q -> SRr SEGS W (mkCfg ms md) Q.
Proof. intros W E ss ms md Q pc HS Hr Hpc H. rewrite (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hr), Hpc. exact H. Qed.
(* check 34: name[t] is a byte of the model block m *)
Lemma p_obl : forall (W : world SEGS) mem E m a,
  ew E 15 = Z_to_bv 64 SHADOW_OFF -> ew E 10 = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
  range_addressable (rdW W mem) SHADOW_OFF m seg_spec.SEG_M_SIZE -> m <= a -> a + 1 <= m + seg_spec.SEG_M_SIZE ->
  range_addressable (rdW W mem) (U E PBx) (U E (SOff 10 0)) 1.
Proof.
intros W mem E m a H15 H10 Ha HR H1 H2. unfold PBx.
rewrite (U_atom E 15 SHADOW_OFF H15) by (unfold SHADOW_OFF; lia). rewrite (U_atom E 10 a H10) by lia.
apply (range_addressable_sub _ _ m seg_spec.SEG_M_SIZE); [exact HR | lia | lia].
Qed.
(* the byte name[t] of the segment's name, at &m->seg[i] + t *)
Lemma p_byte_at : forall cx i c m (rd : reader) t di,
  lt_cm rd c m (x_run cx) -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = Some di -> (t < di)%nat ->
  exists b, nth t (SegModel.ms_name (x_seg cx i)) 0 = b /\ rd (seg_spec.mseg_addr m i + Z.of_nat t) = Some b /\
  (t < 15)%nat /\ (i < 32)%nat.
Proof.
intros cx i c m rd t di Hcm Hi Hs Ht.
destruct (s22_name_str cx i c m rd Hcm Hi) as ((Hz & _) & Hl16 & Hnf).
pose proof (SegModel.strrchr_lt _ _ _ Hs) as Hdl. rewrite (SegModel.cut_nul_id _ Hnf) in Hdl.
exists (nth t (SegModel.ms_name (x_seg cx i)) 0). split; [reflexivity|]. split.
- rewrite (Hz t) by (rewrite length_app; cbn [length]; lia). f_equal. apply app_nth1. lia.
- split; [lia|]. destruct Hcm as (_ & (bs & _ & (_ & Hn32 & _))). unfold x_mcF in Hi. lia.
Qed.

(* the seed: the pass's state at 0x85a18 is an instance of ss_p *)
Lemma p_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem a b s1v,
  getr regs 5 = w64 10 -> getr regs 9 = w64 s1v -> getr regs 10 = w64 a -> getr regs 12 = w64 a ->
  getr regs 15 = w64 SHADOW_OFF ->
  4096 <= a <= 0x7fffffffffff -> 0 <= b < 256 -> 0 <= s1v -> s1v + 144 <= 2 ^ 64 -> a + 1 <= s1v + 136 ->
  rdW W mem a = Some b -> rdword (rdW W mem) (s1v + 136) = Some LT_MASK ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 b])) ss_p
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_VP)) mem (seg_rom SEGS))).
Proof.
intros W regs mem a b s1v H5 H9 H10 H12 H15 Ra Rb Rs0 Rs1 Hd HV HM.
set (E := Eimg (Ereg regs [Z_to_bv 64 b])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 s1v) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 a) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E15 : ew E 15 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 15%nat 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 b)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
unfold ss_p. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold p_sregs.
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite H12. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite H5. reflexivity. }
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, p_byte.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ a 0 1 (SOff 32 0) b);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (p_val1 (w_H W) mem a b Rb HV).
  + unfold region_ok, p_mask.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ s1v 136 8 (SLit LT_MASK) LT_MASK); [reflexivity | unfold LT_MASK; lia | lia |].
    exact (val_mem_of_rdword SEGS _ _ _ _ HM).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. unfold extent_of_region, zdisj.
  cbn [p_byte p_mask YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd].
  rewrite E9, E10, !unsigned_lit_small by lia.
  split; [split; [left; lia | exact I] | split; exact I].
- split; [|split; exact I]. cbn [f_atoms atoms_ok p_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E15, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* s22_inv at a later state with the same journal, the same frame registers and the same reader *)
Lemma p_inv_kept : forall cx i c m tab mt o L ly S W regs mem md k acc regs' mem' md',
  s22_inv B MT cx i c m tab mt o L ly S W regs mem md k acc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  s22_inv B MT cx i c m tab mt o L ly S W regs' mem' md' k acc.
Proof.
intros cx i c m tab mt o L ly S W regs mem md k acc regs' mem' md' HI HJ' K2 K3 K4 K8 K9 K.
destruct HI as (Hi & Hd & (HF & Himg & Hbl & Hbud) & Hc & Hm & Htb & Hmt & Hsl & Hcm & Htabs).
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & Hsv & H0 & H8 & H16 & HFL & H176 & Hzs).
pose proof (k_word _ _ K) as KW.
assert (KH : forall a n, lt_hblk B ly S (rdW W mem) a n -> lt_hblk B ly S (rdW W mem') a n).
{ intros a n (G1 & G2 & G3 & G4). split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  exact (k_addr _ _ K _ _ G4). }
split; [exact Hi|]. split; [exact Hd|]. split.
{ split; [|split; [|split; [exact Hbl | exact Hbud]]].
  - split; [exact HJ'|]. rewrite K2, K3, K4, K8, K9.
    split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
    split; [intros j r Hj; rewrite KW; exact (Hsv j r Hj)|].
    rewrite !KW. split; [exact H0|]. split; [exact H8|]. split; [exact H16|]. split; [exact HFL|].
    split; [exact H176|]. exact (k_zs _ _ K _ _ Hzs).
  - exact (s10_lt_img_kept B IMGS BSYM cx W mem' (rdW W mem) (proj1 HJ') (fun a _ _ _ => K a) Himg). }
split; [exact (KH _ _ Hc)|]. split; [exact (KH _ _ Hm)|]. split; [exact (KH _ _ Htb)|].
split; [exact (KH _ _ Hmt)|].
split; [intros o0 v Hin; rewrite KW; exact (Hsl o0 v Hin)|].
split.
{ destruct Hcm as [C1 C2]. split; [exact (k_rconf _ _ K _ _ C1) | exact (k_mconf _ _ K _ _ C2)]. }
destruct Htabs as (T1 & T2 & T3 & T4 & T5 & T6).
split; [exact T1|]. split; [exact (k_rtab _ _ K _ _ T2)|]. split; [exact (k_bytes _ _ K _ _ T3)|].
split; [exact (k_val _ _ K _ _ _ T4)|]. split; [exact (k_mtab _ _ K _ _ T5) | exact T6].
Qed.

(* the head of the parent loop with t bytes checked, at most n bytes left: S22_VP_stmt's premises, with the two
   registers a pass re-reads (t0 and a2) apart *)
Definition p_ctx (i t : nat) (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc c m tab mt : Z)
  (di : nat) (vid : Z) : Prop :=
  lt_base B MT cx /\ sa_frm0 /\
  s22_inv B MT cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc /\
  SegModel.ms_ignore (x_seg cx i) = false /\
  SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = Some di /\ (di <> 0)%nat /\
  SegModel.m_digits (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) 0 = Some vid /\
  1 <= vid <= 4094 /\ (t < di)%nat /\
  forallb SegModel.h_parent_ok (firstn t (SegModel.ms_name (x_seg cx i))) = true /\
  getr regs 10 = w64 (seg_spec.mseg_addr m i + Z.of_nat t) /\
  getr regs 11 = w64 (Z.of_nat di - Z.of_nat t) /\
  getr regs 15 = w64 SHADOW_OFF /\ getr regs 16 = w64 m /\ getr regs 18 = w64 vid /\
  getr regs 19 = w64 (seg_spec.mseg_addr m i) /\ getr regs 20 = w64 (Z.of_nat di) /\
  getr regs 21 = w64 (x_sh cx) /\ getr regs 24 = w64 tab /\ s22_rk m i regs.
Definition p_vp_at (i t n : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (di : nat) (vid : Z),
  (di <= t + n)%nat -> p_ctx i t cx ly S W regs mem md k acc c m tab mt di vid ->
  getr regs 5 = w64 10 -> getr regs 12 = w64 (seg_spec.mseg_addr m i + Z.of_nat t) ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_VP) regs mem md) (lt_post B MT cx).

(* ---- the three ways out of a pass ---- *)
(* bnez a1 taken (0x85a78): byte t passed and t + 1 < di, the next pass *)
Lemma p_exit_next : forall i t n cx ly S W regs mem md k acc c m tab mt di vid E0 E ss (ms : machine_state) mdF,
  p_vp_at i (Datatypes.S t) n -> (di <= t + Datatypes.S n)%nat ->
  p_ctx i t cx ly S W regs mem md k acc c m tab mt di vid ->
  SegModel.h_parent_ok (nth t (SegModel.ms_name (x_seg cx i)) 0) = true ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> p_agree E E0 -> p_ev E0 regs ->
  ss_pc ss = S22_VP -> ss_resv ss = None -> p_kept (ss_regs ss) p_KR = true ->
  sr_get (ss_regs ss) 5%bv = SLit 10 -> sr_get (ss_regs ss) 10%bv = SOff 10 1 ->
  sr_get (ss_regs ss) 11%bv = SOff 11 (-1) -> sr_get (ss_regs ss) 12%bv = SOff 10 1 ->
  sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
  branch_taken BC_NE (sv_denot E (SOff 11 (-1))) (sv_denot E (SLit 0)) = true ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W (ms_mem ms) mdF k ->
  (forall a, rdW W (ms_mem ms) a = rdW W mem a) ->
  SRr SEGS W (mkCfg ms mdF) (lt_post B MT cx).
Proof.
intros i t n cx ly S W regs mem md k acc c m tab mt di vid E0 E ss ms mdF HIH Hdn PC Hpk HS HAG EV Hpc Hrv HKP
  S5 S10 S11 S12 S20 Hc HJ' K.
pose proof PC as (HBASE & HFRM & HINV & Hign & Hstr & Hdi0 & Hdig & Hvid & Htdi & Hall & R10 & R11 & R15 & R16 & R18
  & R19 & R20 & R21 & R24 & HRK).
pose proof (p_keep E E0 ss ms (w_H W) regs p_KR HS HAG EV HKP) as PK.
pose proof (p_inv_kept cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc (ms_regs ms) (ms_mem ms)
  mdF HINV HJ' (PK 2%bv ltac:(p_in)) (PK 3%bv ltac:(p_in)) (PK 4%bv ltac:(p_in)) (PK 8%bv ltac:(p_in))
  (PK 9%bv ltac:(p_in)) K) as HINV'.
pose proof HINV as (Hi & _ & _ & _ & _ & _ & _ & _ & Hcm & _).
destruct (s22_name_str cx i c m (rdW W mem) Hcm Hi) as (_ & Hl16 & Hnf).
pose proof (SegModel.strrchr_lt _ _ _ Hstr) as Hdl. rewrite (SegModel.cut_nul_id _ Hnf) in Hdl.
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat di - Z.of_nat t))
  by (rewrite (HAG 11%nat ltac:(lia)), (EV 11%nat 11%bv eq_refl); exact R11).
assert (Ht1 : (Datatypes.S t < di)%nat).
{ rewrite branch_ne_U, (U_atom_off E 11 (Z.of_nat di - Z.of_nat t) (-1) E11) in Hc by lia.
  rewrite U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
assert (Hall' : forallb SegModel.h_parent_ok (firstn (Datatypes.S t) (SegModel.ms_name (x_seg cx i))) = true).
{ rewrite (s22_firstn_S _ t 0) by lia. rewrite forallb_app, Hall. cbn [forallb andb]. rewrite Hpk. reflexivity. }
destruct HRK as (K22 & K23 & K25 & K26 & K27).
apply (p_at W E ss ms mdF _ S22_VP HS Hrv Hpc).
apply (HIH cx ly S W (ms_regs ms) (ms_mem ms) mdF k acc c m tab mt di vid ltac:(lia)).
- refine (conj HBASE (conj HFRM (conj HINV' (conj Hign (conj Hstr (conj Hdi0 (conj Hdig (conj Hvid (conj Ht1
    (conj Hall' _)))))))))).
  split.
  { rewrite (p_reg_off E E0 ss ms (w_H W) 10%bv 10 1 (seg_spec.mseg_addr m i + Z.of_nat t) HS S10
      (HAG 10%nat ltac:(lia)) ltac:(rewrite (EV 10%nat 10%bv eq_refl); exact R10)).
    unfold w64. f_equal; lia. }
  split.
  { rewrite (p_reg_off E E0 ss ms (w_H W) 11%bv 11 (-1) (Z.of_nat di - Z.of_nat t) HS S11
      (HAG 11%nat ltac:(lia)) ltac:(rewrite (EV 11%nat 11%bv eq_refl); exact R11)).
    unfold w64. f_equal; lia. }
  split; [rewrite (PK 15%bv ltac:(p_in)); exact R15|].
  split; [rewrite (PK 16%bv ltac:(p_in)); exact R16|].
  split; [rewrite (PK 18%bv ltac:(p_in)); exact R18|].
  split; [rewrite (PK 19%bv ltac:(p_in)); exact R19|].
  split.
  { rewrite (p_reg_off E E0 ss ms (w_H W) 20%bv 20 0 (Z.of_nat di) HS S20
      (HAG 20%nat ltac:(lia)) ltac:(rewrite (EV 20%nat 20%bv eq_refl); exact R20)).
    rewrite Z.add_0_r. reflexivity. }
  split; [rewrite (PK 21%bv ltac:(p_in)); exact R21|].
  split; [rewrite (PK 24%bv ltac:(p_in)); exact R24|].
  split; [rewrite (PK 22%bv ltac:(p_in)); exact K22|]. split; [rewrite (PK 23%bv ltac:(p_in)); exact K23|].
  split; [rewrite (PK 25%bv ltac:(p_in)); exact K25|]. split; [rewrite (PK 26%bv ltac:(p_in)); exact K26|].
  rewrite (PK 27%bv ltac:(p_in)); exact K27.
- exact (p_reg_lit E ss ms (w_H W) 5%bv 10 HS S5).
- rewrite (p_reg_off E E0 ss ms (w_H W) 12%bv 10 1 (seg_spec.mseg_addr m i + Z.of_nat t) HS S12
    (HAG 10%nat ltac:(lia)) ltac:(rewrite (EV 10%nat 10%bv eq_refl); exact R10)).
  unfold w64. f_equal; lia.
Qed.

(* bnez a1 not taken (0x85a78), j 0x85a8c: byte t was the last one, t + 1 = di; m_split succeeded *)
Lemma p_exit_vm : forall i t cx ly S W regs mem md k acc c m tab mt di vid E0 E ss (ms : machine_state) mdF,
  S22_VM_stmt B MT i ->
  p_ctx i t cx ly S W regs mem md k acc c m tab mt di vid ->
  SegModel.h_parent_ok (nth t (SegModel.ms_name (x_seg cx i)) 0) = true ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> p_agree E E0 -> p_ev E0 regs ->
  ss_pc ss = S22_VM -> ss_resv ss = None -> p_kept (ss_regs ss) p_KR = true ->
  sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
  branch_taken BC_NE (sv_denot E (SOff 11 (-1))) (sv_denot E (SLit 0)) = false ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W (ms_mem ms) mdF k ->
  (forall a, rdW W (ms_mem ms) a = rdW W mem a) ->
  SRr SEGS W (mkCfg ms mdF) (lt_post B MT cx).
Proof.
intros i t cx ly S W regs mem md k acc c m tab mt di vid E0 E ss ms mdF HVM PC Hpk HS HAG EV Hpc Hrv HKP S20 Hc HJ' K.
pose proof PC as (HBASE & HFRM & HINV & Hign & Hstr & Hdi0 & Hdig & Hvid & Htdi & Hall & R10 & R11 & R15 & R16 & R18
  & R19 & R20 & R21 & R24 & HRK).
pose proof (p_keep E E0 ss ms (w_H W) regs p_KR HS HAG EV HKP) as PK.
pose proof (p_inv_kept cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc (ms_regs ms) (ms_mem ms)
  mdF HINV HJ' (PK 2%bv ltac:(p_in)) (PK 3%bv ltac:(p_in)) (PK 4%bv ltac:(p_in)) (PK 8%bv ltac:(p_in))
  (PK 9%bv ltac:(p_in)) K) as HINV'.
pose proof HINV as (Hi & _ & _ & _ & _ & _ & _ & _ & Hcm & _).
destruct (s22_name_str cx i c m (rdW W mem) Hcm Hi) as (_ & Hl16 & Hnf).
pose proof (SegModel.strrchr_lt _ _ _ Hstr) as Hdl. rewrite (SegModel.cut_nul_id _ Hnf) in Hdl.
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat di - Z.of_nat t))
  by (rewrite (HAG 11%nat ltac:(lia)), (EV 11%nat 11%bv eq_refl); exact R11).
assert (Ht1 : (Datatypes.S t = di)%nat).
{ rewrite branch_ne_U, (U_atom_off E 11 (Z.of_nat di - Z.of_nat t) (-1) E11) in Hc by lia.
  rewrite U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
assert (Hall' : forallb SegModel.h_parent_ok (firstn (Datatypes.S t) (SegModel.ms_name (x_seg cx i))) = true).
{ rewrite (s22_firstn_S _ t 0) by lia. rewrite forallb_app, Hall. cbn [forallb andb]. rewrite Hpk. reflexivity. }
rewrite Ht1 in Hall'.
pose proof (p_split_some _ di vid Hnf Hstr Hdi0 Hdig ltac:(lia) Hall') as Hsplit.
destruct HRK as (K22 & K23 & K25 & K26 & K27).
apply (p_at W E ss ms mdF _ S22_VM HS Hrv Hpc).
apply (HVM cx ly S W (ms_regs ms) (ms_mem ms) mdF k acc c m tab mt di vid HBASE HFRM HINV' Hign Hsplit ltac:(lia) Hvid).
- rewrite (PK 15%bv ltac:(p_in)); exact R15.
- rewrite (PK 18%bv ltac:(p_in)); exact R18.
- rewrite (PK 19%bv ltac:(p_in)); exact R19.
- rewrite (p_reg_off E E0 ss ms (w_H W) 20%bv 20 0 (Z.of_nat di) HS S20
    (HAG 20%nat ltac:(lia)) ltac:(rewrite (EV 20%nat 20%bv eq_refl); exact R20)).
  rewrite Z.add_0_r. reflexivity.
- rewrite (PK 21%bv ltac:(p_in)); exact R21.
- rewrite (PK 24%bv ltac:(p_in)); exact R24.
- split; [rewrite (PK 22%bv ltac:(p_in)); exact K22|]. split; [rewrite (PK 23%bv ltac:(p_in)); exact K23|].
  split; [rewrite (PK 25%bv ltac:(p_in)); exact K25|]. split; [rewrite (PK 26%bv ltac:(p_in)); exact K26|].
  rewrite (PK 27%bv ltac:(p_in)); exact K27.
Qed.

(* 0x85b88 li s4,4; j 0x859c4: byte t failed; m_split is None and turn i adds nothing *)
Lemma p_exit_join : forall i t cx ly S W regs mem md k acc c m tab mt di vid E0 E ss (ms : machine_state) mdF,
  S22_JOIN_stmt B MT i ->
  p_ctx i t cx ly S W regs mem md k acc c m tab mt di vid ->
  SegModel.h_parent_ok (nth t (SegModel.ms_name (x_seg cx i)) 0) = false ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> p_agree E E0 -> p_ev E0 regs ->
  ss_pc ss = S22_JOIN -> ss_resv ss = None -> p_kept (ss_regs ss) p_KR = true ->
  sr_get (ss_regs ss) 20%bv = SLit 4 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W (ms_mem ms) mdF k ->
  (forall a, rdW W (ms_mem ms) a = rdW W mem a) ->
  SRr SEGS W (mkCfg ms mdF) (lt_post B MT cx).
Proof.
intros i t cx ly S W regs mem md k acc c m tab mt di vid E0 E ss ms mdF HJN PC Hpk HS HAG EV Hpc Hrv HKP S20 HJ' K.
pose proof PC as (HBASE & HFRM & HINV & Hign & Hstr & Hdi0 & Hdig & Hvid & Htdi & Hall & R10 & R11 & R15 & R16 & R18
  & R19 & R20 & R21 & R24 & HRK).
pose proof (p_keep E E0 ss ms (w_H W) regs p_KR HS HAG EV HKP) as PK.
pose proof (p_inv_kept cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc (ms_regs ms) (ms_mem ms)
  mdF HINV HJ' (PK 2%bv ltac:(p_in)) (PK 3%bv ltac:(p_in)) (PK 4%bv ltac:(p_in)) (PK 8%bv ltac:(p_in))
  (PK 9%bv ltac:(p_in)) K) as HINV'.
pose proof HINV as (Hi & Hd0 & _ & _ & _ & _ & _ & _ & Hcm & _).
destruct (s22_name_str cx i c m (rdW W mem) Hcm Hi) as (_ & _ & Hnf).
pose proof (SegModel.strrchr_lt _ _ _ Hstr) as Hdl. rewrite (SegModel.cut_nul_id _ Hnf) in Hdl.
pose proof (p_split_none _ di vid t Hstr Hdig Htdi Hdl Hpk) as Hsplit.
pose proof (s22_decl_step_skip (SegModel.mc_seg (x_mcF cx)) i (x_tab0 cx) (x_cap cx) Hi Hd0 (or_intror Hsplit))
  as Hdecl.
destruct HRK as (K22 & K23 & K25 & K26 & K27).
apply (p_at W E ss ms mdF _ S22_JOIN HS Hrv Hpc).
apply (HJN cx ly S W (ms_regs ms) (ms_mem ms) mdF k acc c m tab mt HBASE HFRM Hdecl HINV').
- rewrite (PK 15%bv ltac:(p_in)); exact R15.
- rewrite (PK 16%bv ltac:(p_in)); exact R16.
- exact (p_reg_lit E ss ms (w_H W) 20%bv 4 HS S20).
- rewrite (PK 21%bv ltac:(p_in)); exact R21.
- rewrite (PK 24%bv ltac:(p_in)); exact R24.
- split; [rewrite (PK 22%bv ltac:(p_in)); exact K22|]. split; [rewrite (PK 23%bv ltac:(p_in)); exact K23|].
  split; [rewrite (PK 25%bv ltac:(p_in)); exact K25|]. split; [rewrite (PK 26%bv ltac:(p_in)); exact K26|].
  rewrite (PK 27%bv ltac:(p_in)); exact K27.
Qed.

(* ---- one pass: from 0x85a18 with t bytes checked to the next pass, to S22_VM or to the join ---- *)
Lemma p_pass : forall i t n, S22_JOIN_stmt B MT i -> S22_VM_stmt B MT i -> p_vp_at i (S t) n -> p_vp_at i t (S n).
Proof.
intros i t n HJN HVM HIH cx ly S W regs mem md k acc c m tab mt di vid Hdn PC R5 R12.
pose proof PC as (HBASE & _ & HINV & _ & Hstr & _ & _ & _ & Htdi & _ & R10 & _ & R15 & _).
pose proof HINV as (Hi & _ & (HFR & _) & _ & Hm & _ & _ & Hsl & Hcm & _).
pose proof HFR as (HJ & _ & _ & _ & _ & R9 & _).
pose proof (proj1 HJ) as HAR.
(* the byte name[t] *)
destruct (p_byte_at cx i c m (rdW W mem) t di Hcm Hi Hstr Htdi) as (b & Hbv & Hrdb & Ht15 & Hi32).
pose proof (sa_aview_rng _ _ _ _ _ Hrdb) as Rb.
(* where it lies: in m, below the allocator's ceiling, below the stack and s1 *)
destruct Hm as (HinM & Hm4096 & _ & (_ & _ & _ & HraM & _)).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HinM) as (_ & _ & HMc & _).
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as (_ & Hreq).
pose proof HBASE as ((_ & _ & _ & _ & _ & Hstk & _) & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (Hs1 : x_sp0 cx - 352 < x_s1 cx <= x_sp0 cx - 320)
  by (unfold x_s1, LT_FRAME; pose proof (Z.mod_pos_bound (x_sp0 cx - 320) 32 ltac:(lia)); lia).
unfold x_sp0 in Hs1.
assert (HA : 4096 <= seg_spec.mseg_addr m i + Z.of_nat t <= 0x7fffffffffff /\
             seg_spec.mseg_addr m i + Z.of_nat t + 1 <= x_s1 cx + 136 /\
             m <= seg_spec.mseg_addr m i + Z.of_nat t /\
             seg_spec.mseg_addr m i + Z.of_nat t + 1 <= m + seg_spec.SEG_M_SIZE /\
             0 <= x_s1 cx /\ x_s1 cx + 144 <= 2 ^ 64).
{ unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE in *. lia. }
destruct HA as (HA1 & HA2 & HA3 & HA4 & HA5 & HA6).
(* the seed *)
pose proof (p_seed W regs mem (seg_spec.mseg_addr m i + Z.of_nat t) b (x_s1 cx) R5 R9 R10 R12 R15 HA1 Rb HA5 HA6 HA2
  Hrdb (Hsl 136 LT_MASK ltac:(unfold s22_L; apply in_or_app; right; repeat first [left; reflexivity | right])))
  as HS.
pose proof (Eimg_env (Ereg regs [Z_to_bv 64 b])) as HEI.
assert (EV : p_ev (Eimg (Ereg regs [Z_to_bv 64 b])) regs) by (intros q r Hq; apply ew_Eimg_Ereg_nat; exact Hq).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 b])) 32 = Z_to_bv 64 b)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E10 : ew (Eimg (Ereg regs [Z_to_bv 64 b])) 10 = Z_to_bv 64 (seg_spec.mseg_addr m i + Z.of_nat t))
  by (rewrite (EV 10%nat 10%bv eq_refl); exact R10).
assert (E15 : ew (Eimg (Ereg regs [Z_to_bv 64 b])) 15 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EV 15%nat 15%bv eq_refl); exact R15).
remember (Eimg (Ereg regs [Z_to_bv 64 b])) as E0 eqn:HE0. clear HE0.
assert (SHOK : sh_ok SEGS PBx [] E0 (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (K : forall x, rdW W mem x = rdW W mem x) by reflexivity.
unfold cfg_at. change (w64 (BASE + S22_VP)) with (Z_to_bv 64 (BASE + S22_VP)).
(* 0x85a18 .. 0x85a34: check 34 of name[t] (a token: its slow block 0x85a80 is the token's), the byte, the digit
   test; the run stops at bltu a4,t0 *)
paj_run_tok RUN HS HJ SHOK Pspan.
{ exact (p_obl W mem E0 m (seg_spec.mseg_addr m i + Z.of_nat t) E15 E10 ltac:(lia) HraM HA3 HA4). }
{ awr_ok_tac. }
p_mem W mem K.
psrr_branch_tok RUN BR HS SHOK Pspan.
- (* a digit: parent_ok *)
  pose proof (p_dig_c _ b true Hc ltac:(p_e32 E32) Rb) as Hd. clear Hc.
  assert (Hpk : SegModel.h_parent_ok b = true) by (rewrite (s22_pk_split b Rb), Hd; reflexivity).
  rewrite <- Hbv in Hpk.
  (* 0x85a6c .. 0x85a78: a1, a0, a2 by one; bnez a1 *)
  paj_run_tok RUN HS HJ SHOK Pspan.
  { awr_ok_tac. }
  p_mem W mem K.
  psrr_branch_tok RUN BR HS SHOK Pspan.
  + paj_run_to_tok RUNTO HS HJ SHOK Pspan S22_VP.
    { awr_ok_tac. }
    p_mem W mem K.
    exact (p_exit_next i t n cx ly S W regs mem md k acc c m tab mt di vid E0 _ _ _ _ HIH Hdn PC Hpk HS ltac:(p_ag) EV
      ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) Hc HJ K).
  + paj_run_to_tok RUNTO HS HJ SHOK Pspan S22_VM.
    { awr_ok_tac. }
    p_mem W mem K.
    exact (p_exit_vm i t cx ly S W regs mem md k acc c m tab mt di vid E0 _ _ _ _ HVM PC Hpk HS ltac:(p_ag) EV
      ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) Hc HJ K).
- (* not a digit *)
  pose proof (p_dig_c _ b false Hc ltac:(p_e32 E32) Rb) as Hd. clear Hc.
  (* 0x85a38 .. 0x85a48: the letter test; the run stops at bltu a4,a7 *)
  paj_run_tok RUN HS HJ SHOK Pspan.
  { awr_ok_tac. }
  p_mem W mem K.
  psrr_branch_tok RUN BR HS SHOK Pspan.
  + (* a letter: parent_ok *)
    pose proof (p_alpha_c _ b true Hc ltac:(p_e32 E32) Rb) as Ha. clear Hc.
    assert (Hpk : SegModel.h_parent_ok b = true) by (rewrite (s22_pk_split b Rb), Hd, Ha; reflexivity).
    rewrite <- Hbv in Hpk.
    paj_run_tok RUN HS HJ SHOK Pspan.
    { awr_ok_tac. }
    p_mem W mem K.
    psrr_branch_tok RUN BR HS SHOK Pspan.
    * paj_run_to_tok RUNTO HS HJ SHOK Pspan S22_VP.
      { awr_ok_tac. }
      p_mem W mem K.
      exact (p_exit_next i t n cx ly S W regs mem md k acc c m tab mt di vid E0 _ _ _ _ HIH Hdn PC Hpk HS ltac:(p_ag) EV
        ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) Hc HJ K).
    * paj_run_to_tok RUNTO HS HJ SHOK Pspan S22_VM.
      { awr_ok_tac. }
      p_mem W mem K.
      exact (p_exit_vm i t cx ly S W regs mem md k acc c m tab mt di vid E0 _ _ _ _ HVM PC Hpk HS ltac:(p_ag) EV
        ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) Hc HJ K).
  + (* neither: the range test *)
    pose proof (p_alpha_c _ b false Hc ltac:(p_e32 E32) Rb) as Ha. clear Hc.
    paj_run_tok RUN HS HJ SHOK Pspan.
    { awr_ok_tac. }
    p_mem W mem K.
    psrr_branch_tok RUN BR HS SHOK Pspan.
    * (* b outside [45, 95]: not parent_ok; li s4,4 and the join *)
      pose proof (p_rng_t _ b Hc ltac:(p_e32 E32) Rb) as Hout. clear Hc.
      pose proof (s22_pk_out b Rb Hd Ha Hout) as Hpk. rewrite <- Hbv in Hpk.
      paj_run_to_tok RUNTO HS HJ SHOK Pspan S22_JOIN.
      { awr_ok_tac. }
      p_mem W mem K.
      exact (p_exit_join i t cx ly S W regs mem md k acc c m tab mt di vid E0 _ _ _ _ HJN PC Hpk HS ltac:(p_ag) EV
        ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) HJ K).
    * (* b in [45, 95]: the mask's bit b - 45 *)
      pose proof (p_rng_f _ b Hc ltac:(p_e32 E32) Rb) as Hin. clear Hc.
      paj_run_tok RUN HS HJ SHOK Pspan.
      { awr_ok_tac. }
      p_mem W mem K.
      psrr_branch_tok RUN BR HS SHOK Pspan.
      -- (* the bit is 0: not parent_ok; li s4,4 and the join *)
         pose proof (p_mask_c _ b true Hc ltac:(p_e32 E32) Hin) as Hmk. clear Hc.
         assert (Hpk : SegModel.h_parent_ok b = false) by (rewrite (s22_pk_rest b Rb Hd Ha); exact Hmk).
         rewrite <- Hbv in Hpk.
         paj_run_to_tok RUNTO HS HJ SHOK Pspan S22_JOIN.
         { awr_ok_tac. }
         p_mem W mem K.
         exact (p_exit_join i t cx ly S W regs mem md k acc c m tab mt di vid E0 _ _ _ _ HJN PC Hpk HS ltac:(p_ag) EV
           ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) HJ K).
      -- (* the bit is 1: parent_ok *)
         pose proof (p_mask_c _ b false Hc ltac:(p_e32 E32) Hin) as Hmk. clear Hc.
         assert (Hpk : SegModel.h_parent_ok b = true) by (rewrite (s22_pk_rest b Rb Hd Ha); exact Hmk).
         rewrite <- Hbv in Hpk.
         paj_run_tok RUN HS HJ SHOK Pspan.
         { awr_ok_tac. }
         p_mem W mem K.
         psrr_branch_tok RUN BR HS SHOK Pspan.
         ++ paj_run_to_tok RUNTO HS HJ SHOK Pspan S22_VP.
            { awr_ok_tac. }
            p_mem W mem K.
            exact (p_exit_next i t n cx ly S W regs mem md k acc c m tab mt di vid E0 _ _ _ _ HIH Hdn PC Hpk HS
              ltac:(p_ag) EV ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm)
              ltac:(p_vm) Hc HJ K).
         ++ paj_run_to_tok RUNTO HS HJ SHOK Pspan S22_VM.
            { awr_ok_tac. }
            p_mem W mem K.
            exact (p_exit_vm i t cx ly S W regs mem md k acc c m tab mt di vid E0 _ _ _ _ HVM PC Hpk HS ltac:(p_ag) EV
              ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) ltac:(p_vm) Hc HJ K).
Qed.

(* the parent loop: by induction on the bytes left, di - t *)
Lemma s22_p4 : s22_p4_stmt B MT.
Proof using All.
intros i HJN HVM.
assert (G : forall n t, p_vp_at i t n).
{ intros n. induction n as [|n IH]; intros t.
  - intros cx ly S W regs mem md k acc c m tab mt di vid Hdn PC. exfalso.
    destruct PC as (_ & _ & _ & _ & _ & _ & _ & _ & Htdi & _). lia.
  - exact (p_pass i t n HJN HVM (IH (S t))). }
intros cx ly S W regs mem md k acc c m tab mt di t vid HBASE HFRM HINV Hign Hstr Hdi0 Hdig Hvid Htdi Hall
  R5 R10 R11 R12 R15 R16 R18 R19 R20 R21 R24 HRK.
apply (G di t cx ly S W regs mem md k acc c m tab mt di vid ltac:(lia)); [|exact R5 | exact R12].
exact (conj HBASE (conj HFRM (conj HINV (conj Hign (conj Hstr (conj Hdi0 (conj Hdig (conj Hvid (conj Htdi (conj Hall
  (conj R10 (conj R11 (conj R15 (conj R16 (conj R18 (conj R19 (conj R20 (conj R21 (conj R24 HRK))))))))))))))))))).
Qed.

End e.
End f.
End d.
Print Assumptions s22_p4.
