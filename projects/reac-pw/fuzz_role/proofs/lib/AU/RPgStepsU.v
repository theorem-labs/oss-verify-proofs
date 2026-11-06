(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b (its hd_reg_is lemma and the run-to-the-call form of hd_A / hd_B) for reac-pw/fuzz_headamp image A, segment M04b (C8 0x83764 -> C9 0x83794); every pc, register, cell and callee is headamp's, and the three runs end in block posts (lib/A/HPgSteps.v hd_blk_post). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04b.v, with its module paths and module names changed; 816 of its 893 lines of code are new or changed and 399 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgStepsB.v at dda1ad05d6e (its PART 2, the
   trap-step lemmas of the UBSan trap branches and the two trap sites it runs, and its PART 5, the pod_write_ent
   call adapter and the three site-premise lemmas) for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module
   paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs, the prefix rtsb_ -> rl_ and rtb_ -> rlt_; every
   pc, table, register and literal is role B's; four more trap sites are run end to end (the alignment shape at
   0x80374, the equality shape at 0x822a4, and role B's own put32 / patch32 blocks), and the shared block kit
   (rl_blk_post, rl_wpost, rl_caller_saved, the class-4 frame lemmas) is taken from lib/AU/RPgSteps.v. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address below is measured on its
   unstripped twin sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, whose loaded bytes are
   the same): the UBSan trap steps and the pod_write_ent call of the image-B walk of LLVMFuzzerTestOneInput
   (0x80020). Proves no function (kind: segment lemma). It continues lib/AU/RPgSteps.v (PARTS 1, 3, 4).

   PART 2. THE TRAP STEPS (85 branches whose other arm reaches only the `unimp` 0x82604; the `unimp` 0x82610,
   after `jal abort`, is never reached). Image B is built with UBSan as well as the memory-checking runtime, so
   every pointer sum, every array index and the one division of the function carries a test whose other arm is
   that `unimp`. The engine decides a branch by itself when the facts of its symbolic state settle the compare
   (YP0m decide_cond / YP0e decide_cond2: first cond_assumed over f_conds, then the interval arithmetic of
   sv_range over f_atoms); so a walk lane that carries the right atom range or condition fact steps over a trap
   branch with no lemma at all. Where a lane has only the Z-level fact, PART 2a turns it into the branch's bv
   value, which st_ok_add_cond then puts into the state as a cond fact (the arm the engine must take), and
   PART 2b shows six real sites run end to end.
   The eight shapes of role B's 85 branches (counted on the measured trap list; one lemma each, the `unimp` arm of
   the other branch form follows by branch_taken_neg):
     T1 (31 sites) `addi t,c,1; bltu one,t -> on` or `bgeu one,t -> trap`  rlt_po1      (0 < c, c + 1 < 2^64)
     T2 (10)       `not t,b; bgeu t,o -> on`                               rlt_not_le   (b + o < 2^64)
     T3 (22)       `ld t,(R+c); bgeu t,o -> on` with the cell = ~x         rlt_not_le   (x + o < 2^64)
     T4 (8)        `bltu i,16385 -> on`, `srli t,i,14; bnez t -> trap`     rlt_ltu_lit  (i < 16385), rlt_shr_small
     T5 (10)       small literal bounds, `bne`, `beq`                      rlt_ltu_lit / rlt_geu_lit / rlt_ne_lit
     T6 (2)        `addiw t,x,1; blt t,x -> trap`                          rlt_addiw_inc (0 <= x < 2^31 - 1)
     T7 (1)        `andi a0,a5,7; beqz a0 -> on` (pp & 7, pod.h:387)       rlt_and7     (p mod 8 = 0)
     T8 (1)        `ld a7,0(s6); addi a7,a7,-8; beqz a7 -> trap`           rlt_ne8      (8 < l)
   Every one of the eight shapes is run on a real site. PART 2b proves the six whose facts the engine settles by
   itself: 0x80274-0x80280 (T1, the first of E01: the cursor's pointer-overflow test before data[0]),
   0x80370-0x80378 (T7, pp's alignment), 0x803d8-0x803f0 (T4 + T3, the B-only put32 pair of pod.h:388),
   0x81e7c-0x81e94 (T4 + T3, the B-only patch32 pair of pod.h:440), 0x8204c-0x82054 (T8, the B-only
   divide-by-zero of pod.h:443) and 0x822a4 (T5, the record index against 33). PART 2c proves the other three,
   whose compare the engine cannot settle from an atom range alone (it refutes an equality from disjoint ranges
   but proves none, and sv_range has no case for `xori -1` or for the 32-bit `addiw`): 0x820e4-0x820f0 (T4's
   `srli` form with T3, pod.h:446), 0x8117c-0x81184 (T2, fuzz.h:63) and 0x81930-0x81934 (T6, pod.h:432). There
   the lemma puts the shape's value into the state as a condition fact (YP06 st_ok_add_cond / _neg) and the
   engine then takes the live arm; a walk lane does the same mid-run.

   PART 5. THE pod_write_ent CALL. Image B keeps pod_write_ent(pp, e) out of line at 0x82bac and calls it where
   image A inlines it: 0x80818 (pod.h:404, the shape-7 Int pod e at F + 0xf0), 0x81908 (pod.h:430, the count
   loop's e62 at F + 0x210, after the capacity guard `bltu a1,a0` 0x818fc) and 0x81c08 (pod.h:416, the Int-7
   value e42 at F + 0x180). Its contract is lib/AU/PweSpec.v's pod_write_ent_specX. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import PweSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* =============================== PART 2a. the trap-step lemmas (8 shapes) ===============================
   Each lemma gives the bv value of the branch at a trap site from the Z fact the walk lane carries; the lane
   puts it into its symbolic state with YP06 st_ok_add_cond (the arm the engine then takes) or reads it after a
   concrete split. The other branch form of the same shape (the one whose TAKEN arm is the `unimp`) is the
   negation, by YP0m branch_taken_neg: branch_taken (neg_bc c) a b = negb (branch_taken c a b). *)

(* the unsigned compare of two literals in range: the shape of T4, and of the small-literal bounds of T5 *)
Lemma rlt_ltu_lit : forall i c, 0 <= i -> i < c -> c < 2 ^ 64 -> branch_taken BC_LTU (w64 i) (w64 c) = true.
Proof.
intros i c H0 H1 H2. cbn [branch_taken]. unfold bv_ltu, w64.
rewrite !unsigned_lit_small by lia. apply Z.ltb_lt. lia.
Qed.
(* its mirror: the compare is false, so a `bltu` to the trap is not taken *)
Lemma rlt_geu_lit : forall i c, 0 <= i -> i <= c -> c < 2 ^ 64 -> branch_taken BC_LTU (w64 c) (w64 i) = false.
Proof.
intros i c H0 H1 H2. cbn [branch_taken]. unfold bv_ltu, w64.
rewrite !unsigned_lit_small by lia. apply Z.ltb_ge. lia.
Qed.
(* T1 (31 sites, fuzz.h:42): the cursor's pointer-overflow test `addi t,c,1; bltu one,t`. The input block starts
   above 0 and ends below 2^63, so c + 1 neither wraps nor is below 2. *)
Lemma rlt_po1 : forall c, 0 < c -> c + 1 < 2 ^ 64 -> branch_taken BC_LTU (w64 1) (w64 (c + 1)) = true.
Proof. intros c H0 H1. apply rlt_ltu_lit; lia. Qed.
Lemma rlt_po1_geu : forall c, 0 < c -> c + 1 < 2 ^ 64 -> branch_taken BC_GEU (w64 1) (w64 (c + 1)) = false.
Proof.
intros c H0 H1. change BC_GEU with (neg_bc BC_LTU). rewrite branch_taken_neg, (rlt_po1 c H0 H1). reflexivity.
Qed.
(* the 64-bit complement as the `not` instruction and the precomputed cells hold it *)
Lemma rlt_lnot_w64 : forall b, 0 <= b < 2 ^ 64 -> w64 (Z.lnot b) = w64 (2 ^ 64 - 1 - b).
Proof.
intros b Hb. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (Z.lnot b) with ((2 ^ 64 - 1 - b) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite Z_mod_plus_full. reflexivity.
Qed.
(* T2 (10 sites) and T3 (22 sites): `bgeu ~b, o` tests that b + o does not wrap. The complement is in a register
   (`not t,b`, fuzz.h:63 and the table reads) or in a real-frame cell written earlier (R+0xf8 = ~pp, R+0xc8 =
   ~(F+0xa0), R+0xe0 = ~(pp+0x4014), R+0xf0 = ~(F+0x218)). *)
Lemma rlt_not_le : forall b o, 0 <= b < 2 ^ 64 -> 0 <= o -> b + o < 2 ^ 64 ->
branch_taken BC_GEU (w64 (Z.lnot b)) (w64 o) = true.
Proof.
intros b o Hb Ho Hbo. rewrite (rlt_lnot_w64 b Hb).
change BC_GEU with (neg_bc BC_LTU). rewrite branch_taken_neg.
rewrite (rlt_geu_lit o (2 ^ 64 - 1 - b) ltac:(lia) ltac:(lia) ltac:(lia)). reflexivity.
Qed.
Lemma rlt_not_ltu : forall b o, 0 <= b < 2 ^ 64 -> 0 <= o -> b + o < 2 ^ 64 ->
branch_taken BC_LTU (w64 (Z.lnot b)) (w64 o) = false.
Proof.
intros b o Hb Ho Hbo. pose proof (rlt_not_le b o Hb Ho Hbo) as H.
change BC_GEU with (neg_bc BC_LTU) in H. rewrite branch_taken_neg in H.
destruct (branch_taken BC_LTU (w64 (Z.lnot b)) (w64 o)); [discriminate H | reflexivity].
Qed.
(* T4's other form (0x820e8, pod.h:446): `srli t,i,14; bnez t` traps unless i < 16384 *)
Lemma rlt_shr_small : forall i, 0 <= i < 16384 -> branch_taken BC_NE (w64 (Z.shiftr i 14)) (w64 0) = false.
Proof.
intros i Hi. assert (E : Z.shiftr i 14 = 0).
{ rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2 ^ 14) with 16384. lia. }
rewrite E. cbn [branch_taken]. rewrite negb_false_iff. unfold bv_eqb. apply Z.eqb_refl.
Qed.
(* T5's equality forms: `beq a3,s5 -> trap` with s5 = 33 (0x822a4, pod.h:137) and `bne a2,t0 -> on` with t0 = 4
   (0x80cfc, pod.h:240) *)
Lemma rlt_ne_lit : forall x c, 0 <= x < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> x <> c ->
branch_taken BC_EQ (w64 x) (w64 c) = false /\ branch_taken BC_NE (w64 x) (w64 c) = true.
Proof.
intros x c Hx Hc Hne.
assert (E : bv_eqb (w64 x) (w64 c) = false).
{ apply bv_eqb_false_iff. intros Heq. apply Hne.
  apply (f_equal bv_unsigned) in Heq. unfold w64 in Heq. rewrite !unsigned_lit_small in Heq by lia. exact Heq. }
cbn [branch_taken]. rewrite E. split; [reflexivity | reflexivity].
Qed.
(* T6 (2 sites, pod.h:432 at 0x81934 and pod.h:142 at 0x82374): `addiw t,x,1; blt t,x` traps on a signed 32-bit
   overflow of x + 1 *)
Lemma rlt_sext32_small : forall x, 0 <= x < 2 ^ 31 -> bv_signed (w64 x) = x.
Proof.
intros x Hx. unfold w64. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma rlt_addiw_inc : forall x, 0 <= x -> x < 2 ^ 31 - 1 -> branch_taken BC_LT (w64 (x + 1)) (w64 x) = false.
Proof.
intros x H0 H1. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite (rlt_sext32_small (x + 1) ltac:(lia)), (rlt_sext32_small x ltac:(lia)).
apply Z.ltb_ge. lia.
Qed.
(* T7 (1 site, 0x80374, pod.h:387): `andi a0,a5,7; beqz a0` traps unless pp is 8-aligned *)
Lemma rlt_and7 : forall p, 0 <= p -> p mod 8 = 0 -> Z.land p 7 = 0.
Proof.
intros p Hp Hm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
change (2 ^ 3) with 8. exact Hm.
Qed.
Lemma rlt_and7_eq : forall p, 0 <= p -> p mod 8 = 0 -> branch_taken BC_EQ (w64 (Z.land p 7)) (w64 0) = true.
Proof.
intros p H0 Hm. rewrite (rlt_and7 p H0 Hm). cbn [branch_taken]. unfold bv_eqb. apply Z.eqb_refl.
Qed.
(* T8 (1 site, 0x82054, pod.h:443, B only): `ld a7,0(s6); addi a7,a7,-8; beqz a7` is the divide-by-zero test of
   fuzz_u16() % (pp->len - 8). The guard `bltu s8,9` 0x81f30 gives 8 < len on this path, and nothing stores to
   pp + 0x4000 between the read 0x81f28 and the reload 0x8204c, so len - 8 <> 0. *)
Lemma rlt_ne8 : forall l, 8 < l -> l < 2 ^ 64 + 8 -> branch_taken BC_EQ (w64 (l - 8)) (w64 0) = false.
Proof.
intros l H0 H1. cbn [branch_taken]. apply bv_eqb_false_iff. intros Heq.
apply (f_equal bv_unsigned) in Heq. unfold w64 in Heq.
rewrite !unsigned_lit_small in Heq by lia. lia.
Qed.

(* ================= PART 2b. six trap sites, run end to end on image B's own code =================
   The engine decides every branch below by itself from the atom range or the alignment the state carries;
   none needs a cond fact. Each is a block lemma in the shape of a callee contract (RPgSteps rl_blk_post). *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ---- T1 at 0x80274 .. 0x80280 (E01, fuzz.h:42 before data[0]) ----
     0x80274 addi s4,s5,1 / 0x80278 li a0,1 / 0x8027c bltu a0,s4 -> 0x80284 / 0x80280 j 0x82604 (unimp)
   s5 = the input pointer. The fact is the input block's: 0 < c and c + 1 < 2^64, which the entry contract gives
   (0 < data, data + n <= 2^63). *)
Definition rl_t1_tbl : ctable := build_table rsegs 0x80274 4 TEmpty.
Lemma rl_t1_tbl_ok : table_ok rsegs rl_t1_tbl.
Proof. apply build_table_ok0. lia. Qed.
(* The atom bound is a closed numeral: the engine decides `bltu 1, c + 1` by computing over sv_range, so a bound
   that mentions c would leave the compare symbolic and the run would not reach 0x80284. *)
Definition rl_t1_facts : facts := mkFacts [ (21%nat, mkAF 1 18446744073709551614 0) ] [] [].
Lemma rl_trap_8027c : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (c : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 21 = w64 c -> 0 < c -> c + 1 < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs 0x80274 regs memc mdc)
(rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x80284 [10; 20]%bv
  (fun regs2 => getr regs2 20 = w64 (c + 1) /\ getr regs2 10 = w64 1)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs c HJ H21 Hc0 Hc1.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E21 : ew (Ereg regs jt_extra) 21 = Z_to_bv 64 c)
  by (rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (HS : st_ok rsegs (Ereg regs jt_extra) (mkSS 0x80274 sr_atoms [] None rl_t1_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80274) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rl_t1_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E21, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs jt_extra) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs jt_extra) (Ereg regs jt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 0x80274) with (Z_to_bv 64 0x80274).
aj_run_to_tok rl_t1_tbl_ok HS HJ SHOK JTspan 0x80284.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs jt_extra (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  let e20 := eval vm_compute in (sr_get (ss_regs ssf) (20%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
  change (sr_get (ss_regs ssf) (20%bv : bv 5)) with e20 end.
split.
- cbn [sv_denot]. rewrite E21. unfold w64. rewrite unsigned_lit_small by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
- reflexivity.
Qed.

(* ---- T7 at 0x80370 .. 0x80378 (M01.pre1, pod.h:387) ----
     0x80370 andi a0,a5,7 / 0x80374 beqz a0 -> 0x8037c / 0x80378 j 0x82604 (unimp)
   a5 = pp, the harness's own block, 16-aligned by the allocator. The engine folds `andi` on an atom whose
   alignment fact is 3 (YP0m s_and_ptr: the mask 7 is below 2^3) to the literal 0, and then decides the `beqz`. *)
Definition rl_t7_tbl : ctable := build_table rsegs 0x80370 2 TEmpty.
Lemma rl_t7_tbl_ok : table_ok rsegs rl_t7_tbl.
Proof. apply build_table_ok0. lia. Qed.
Definition rl_t7_facts : facts := mkFacts [ (15%nat, mkAF 1 9223372036854775807 3) ] [] [].
Lemma rl_trap_80374 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (pp : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 15 = w64 pp -> 0 < pp -> pp <= 2 ^ 63 - 1 -> pp mod 8 = 0 ->
SRr rsegs W (cfg_at rsegs 0x80370 regs memc mdc)
(rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x8037c [10]%bv
  (fun regs2 => getr regs2 10 = w64 0)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs pp HJ H15 Hp0 Hp1 Hal.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E15 : ew (Ereg regs jt_extra) 15 = Z_to_bv 64 pp)
  by (rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (HS : st_ok rsegs (Ereg regs jt_extra) (mkSS 0x80370 sr_atoms [] None rl_t7_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80370) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rl_t7_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E15, unsigned_lit_small by lia. change (2 ^ 3) with 8.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | exact Hal]. }
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs jt_extra) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs jt_extra) (Ereg regs jt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 0x80370) with (Z_to_bv 64 0x80370).
aj_run_to_tok rl_t7_tbl_ok HS HJ SHOK JTspan 0x8037c.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs jt_extra (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10 end.
first [reflexivity | (cbn [sv_denot]; unfold w64; reflexivity)].
Qed.

(* ---- T5 at 0x822a4 (M02, pod.h:137) ----
     0x822a4 beq a3,s5 -> 0x82604 (unimp) / 0x822a8 bltu s6,s7
   a3 = at, the index of the record the scan is at; s5 = 33, the literal the record count cannot reach. The
   engine decides the `beq` from the index atom's range [0, 32] and the literal. *)
Definition rl_t5_tbl : ctable := build_table rsegs 0x822a4 1 TEmpty.
Lemma rl_t5_tbl_ok : table_ok rsegs rl_t5_tbl.
Proof. apply build_table_ok0. lia. Qed.
Definition rl_t5_facts : facts := mkFacts [ (13%nat, mkAF 0 32 0) ] [] [].
Lemma rl_trap_822a4 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (at_ : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 13 = w64 at_ -> getr regs 21 = w64 33 -> 0 <= at_ <= 32 ->
SRr rsegs W (cfg_at rsegs 0x822a4 regs memc mdc)
(rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x822a8 [21]%bv
  (fun regs2 => getr regs2 21 = w64 33)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs at_ HJ H13 H21 Hat.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E13 : ew (Ereg regs jt_extra) 13 = Z_to_bv 64 at_)
  by (rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (HS0 : st_ok rsegs (Ereg regs jt_extra) (mkSS 0x822a4 sr_atoms [] None rl_t5_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x822a4) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rl_t5_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E13, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
pose proof (st_ok_pin_lit rsegs _ _ _ (21%bv : bv 5) 33 HS0 eq_refl H21) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs jt_extra) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs jt_extra) (Ereg regs jt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 0x822a4) with (Z_to_bv 64 0x822a4).
aj_run_to_tok rl_t5_tbl_ok HS HJ SHOK JTspan 0x822a8.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs jt_extra (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e21 := eval vm_compute in (sr_get (ss_regs ssf) (21%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (21%bv : bv 5)) with e21 end.
first [reflexivity | (cbn [sv_denot]; unfold w64; reflexivity)].
Qed.

(* ---- T8 at 0x8204c .. 0x82054 (M01.post, pod.h:443; B only) ----
     0x8204c ld a7,0(s6) / 0x82050 addi a7,a7,-8 / 0x82054 beqz a7 -> 0x82604 (unimp) / 0x82058 beqz a5
   s6 = &pp->len; the cell holds len. The guard `bltu s8,9` 0x81f30 gives len >= 9 on this path, and no store
   between 0x81f28 and 0x8204c writes pp + 0x4000, so the reload is the same len (the plan's risk 5). The `ld`
   carries no instrumented check of its own: the check at 0x82044 precedes it. *)
Definition rl_t8_tbl : ctable := build_table rsegs 0x8204c 3 TEmpty.
Lemma rl_t8_tbl_ok : table_ok rsegs rl_t8_tbl.
Proof. apply build_table_ok0. lia. Qed.
(* closed numerals, as T1's: the engine decides `beqz (len - 8)` by computing over sv_range *)
Definition rl_t8_facts : facts := mkFacts [ (33%nat, mkAF 9 9223372036854775808 0) ] [] [].
Definition rl_t8_extra (l : Z) : list word := [Z_to_bv 64 JT_SB; Z_to_bv 64 l].
Definition rl_t8_region : YP09.region :=
YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Lemma rl_trap_82054 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (a l : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 22 = w64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) a 8 l -> 8 < l -> l <= 2 ^ 63 ->
SRr rsegs W (cfg_at rsegs 0x8204c regs memc mdc)
(rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x82058 [17]%bv
  (fun regs2 => getr regs2 17 = w64 (l - 8))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs a l HJ H22 Ha0 Ha1 Hval Hl0 Hl1.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E22 : ew (Ereg regs (rl_t8_extra l)) 22 = Z_to_bv 64 a)
  by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E33 : ew (Ereg regs (rl_t8_extra l)) 33 = Z_to_bv 64 l) by exact (ew_Ereg_extra regs _ 1).
assert (HSoff : sv_denot (Ereg regs (rl_t8_extra l)) (SOff 33 0) = Z_to_bv 64 l).
{ apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r. rewrite !unsigned_lit_small by lia.
  unfold zcanon, M64. apply Z.mod_small. lia. }
assert (HREG : region_ok rsegs (Ereg regs (rl_t8_extra l)) (mrestrict (w_H W) memc) rl_t8_region).
{ unfold region_ok, rl_t8_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E22, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val rsegs (Ereg regs (rl_t8_extra l)) (mrestrict (w_H W) memc) a 0 8 (SOff 33 0) l).
  - exact HSoff.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - rewrite Z.add_0_r. exact Hval. }
assert (HS : st_ok rsegs (Ereg regs (rl_t8_extra l)) (mkSS 0x8204c sr_atoms [rl_t8_region] None rl_t8_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8204c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HREG | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rl_t8_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E33, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs (rl_t8_extra l)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (rl_t8_extra l)) (Ereg regs (rl_t8_extra l))) by apply env_agree_refl.
unfold cfg_at. change (w64 0x8204c) with (Z_to_bv 64 0x8204c).
aj_run_to_tok rl_t8_tbl_ok HS HJ SHOK JTspan 0x82058.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (rl_t8_extra l) (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a0; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a0)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]];
  unfold rl_t8_region in Hr; cbn in Hr; lia. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e17 := eval vm_compute in (sr_get (ss_regs ssf) (17%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (17%bv : bv 5)) with e17 end.
cbn [sv_denot]. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

(* ---- T4 + T3 at 0x803d8 .. 0x803f0 (M01.pre1, pod.h:179 inside pod_put32 at pod.h:388; B only) ----
     0x803d8 lui a0,0x4 / 0x803dc addiw a0,a0,1 (a0 = 16385)
     0x803e0 bltu a7,a0 -> 0x803e8 / 0x803e4 j 0x82604 (unimp)       a7 = len: the bounds half
     0x803e8 ld a0,0xf8(s1) (= ~pp) / 0x803ec bgeu a0,a7 -> 0x803f4 / 0x803f0 j 0x82604  the pointer half
   The UBSan build of the plain image folds this put (len = 0 after the memset of pp), so it has no twin branch;
   the facts are the build invariant's len <= 5440 and the complement cell's range, which pp + 19744 <= 2^63
   gives. This is the first of the plan's five B-only traps. *)
Definition rl_put32_tbl : ctable := build_table rsegs 0x803d8 7 TEmpty.
Lemma rl_put32_tbl_ok : table_ok rsegs rl_put32_tbl.
Proof. apply build_table_ok0. lia. Qed.
Definition rl_put32_facts : facts :=
mkFacts [ (17%nat, mkAF 0 5440 0); (33%nat, mkAF 9223372036854775808 18446744073709551615 0) ] [] [].
Definition rl_put32_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 248 256 0 0 [YP09.mkChunk 248 (CVal 8 (SOff 33 0))].
Lemma rl_trap_803e0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (R len npp : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 9 = w64 R -> getr regs 17 = w64 len -> 0 <= len -> len <= 5440 ->
0 <= R -> R + 256 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 248) 8 npp ->
9223372036854775808 <= npp -> npp <= 18446744073709551615 ->
SRr rsegs W (cfg_at rsegs 0x803d8 regs memc mdc)
(rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x803f4 [10]%bv
  (fun regs2 => getr regs2 10 = w64 npp)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R len npp HJ H9 H17 Hl0 Hl1 HR0 HR1 Hval Hn0 Hn1.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E9 : ew (Ereg regs (rl_t8_extra npp)) 9 = Z_to_bv 64 R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E17 : ew (Ereg regs (rl_t8_extra npp)) 17 = Z_to_bv 64 len)
  by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
assert (E33 : ew (Ereg regs (rl_t8_extra npp)) 33 = Z_to_bv 64 npp) by exact (ew_Ereg_extra regs _ 1).
assert (HREG : region_ok rsegs (Ereg regs (rl_t8_extra npp)) (mrestrict (w_H W) memc) rl_put32_region).
{ unfold region_ok, rl_put32_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val rsegs (Ereg regs (rl_t8_extra npp)) (mrestrict (w_H W) memc) R 248 8 (SOff 33 0) npp).
  - apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r. rewrite !unsigned_lit_small by lia.
    unfold zcanon, M64. apply Z.mod_small. lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - exact Hval. }
assert (HS : st_ok rsegs (Ereg regs (rl_t8_extra npp))
  (mkSS 0x803d8 sr_atoms [rl_put32_region] None rl_put32_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x803d8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HREG | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rl_put32_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E17, E33, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs (rl_t8_extra npp)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (rl_t8_extra npp)) (Ereg regs (rl_t8_extra npp))) by apply env_agree_refl.
unfold cfg_at. change (w64 0x803d8) with (Z_to_bv 64 0x803d8).
aj_run_to_tok rl_put32_tbl_ok HS HJ SHOK JTspan 0x803f4.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (rl_t8_extra npp) (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a0; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a0)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]];
  unfold rl_put32_region in Hr; cbn in Hr; lia. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10 end.
unfold w64. apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r.
rewrite !unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* ---- T4 + T3 at 0x81e7c .. 0x81e94 (M01.post, pod.h:197 inside pod_patch32 at pod.h:440; B only) ----
     0x81e7c lui a0,0x4 / 0x81e80 addiw a0,a0,1 (a0 = 16385)
     0x81e84 ld a4,0x30(s1) (= pp + top) / 0x81e88 ld a5,0x28(s1) (= top)
     0x81e8c bgeu a5,a0 -> 0x82604 (unimp)       the bounds half
     0x81e90 ld a0,0xf8(s1) (= ~pp) / 0x81e94 bltu a0,a5 -> 0x82604 (unimp)     the pointer half
   U writes this top word at pp + 0 with no check (it folds top = 0), so these two have no twin branch either:
   the plan's B-only traps 2 and 3. The facts are top <= 5440 and the complement cell's range. *)
Definition rl_patch32_tbl : ctable := build_table rsegs 0x81e7c 7 TEmpty.
Lemma rl_patch32_tbl_ok : table_ok rsegs rl_patch32_tbl.
Proof. apply build_table_ok0. lia. Qed.
Definition rl_patch32_facts : facts :=
mkFacts [ (33%nat, mkAF 0 5440 0); (35%nat, mkAF 9223372036854775808 18446744073709551615 0) ] [] [].
Definition rl_extra3 (a b c : Z) : list word :=
[Z_to_bv 64 JT_SB; Z_to_bv 64 a; Z_to_bv 64 b; Z_to_bv 64 c].
Definition rl_patch32_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 40 256 0 0
  [YP09.mkChunk 40 (CVal 8 (SOff 33 0)); YP09.mkChunk 48 (CVal 8 (SOff 34 0));
   YP09.mkChunk 248 (CVal 8 (SOff 35 0))].
Lemma rl_trap_81e8c : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (R top other npp : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 9 = w64 R ->
0 <= R -> R + 256 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 40) 8 top ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 48) 8 other ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 248) 8 npp ->
0 <= top -> top <= 5440 ->
9223372036854775808 <= npp -> npp <= 18446744073709551615 ->
0 <= other < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs 0x81e7c regs memc mdc)
(rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x81e98 [10; 14; 15]%bv
  (fun regs2 => getr regs2 14 = w64 other /\ getr regs2 15 = w64 top /\ getr regs2 10 = w64 npp)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R top other npp
  HJ H9 HR0 HR1 Vtop Voth Vnpp Ht0 Ht1 Hn0 Hn1 Ho.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
set (EX := rl_extra3 top other npp) in *.
assert (E9 : ew (Ereg regs EX) 9 = Z_to_bv 64 R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E33 : ew (Ereg regs EX) 33 = Z_to_bv 64 top) by exact (ew_Ereg_extra regs _ 1).
assert (E34 : ew (Ereg regs EX) 34 = Z_to_bv 64 other) by exact (ew_Ereg_extra regs _ 2).
assert (E35 : ew (Ereg regs EX) 35 = Z_to_bv 64 npp) by exact (ew_Ereg_extra regs _ 3).
assert (Hden : forall n v, ew (Ereg regs EX) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot (Ereg regs EX) (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn Hv. apply bv_eq. rewrite denot_SOff, Hn, Z.add_0_r.
  rewrite !unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia. }
assert (HREG : region_ok rsegs (Ereg regs EX) (mrestrict (w_H W) memc) rl_patch32_region).
{ unfold region_ok, rl_patch32_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho'; lia|].
  repeat (apply Forall_cons); try apply Forall_nil.
  - apply (chunk_ok_val rsegs (Ereg regs EX) (mrestrict (w_H W) memc) R 40 8 (SOff 33 0) top);
    [apply Hden; [exact E33 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vtop].
  - apply (chunk_ok_val rsegs (Ereg regs EX) (mrestrict (w_H W) memc) R 48 8 (SOff 34 0) other);
    [apply Hden; [exact E34 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Voth].
  - apply (chunk_ok_val rsegs (Ereg regs EX) (mrestrict (w_H W) memc) R 248 8 (SOff 35 0) npp);
    [apply Hden; [exact E35 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vnpp]. }
assert (HS : st_ok rsegs (Ereg regs EX)
  (mkSS 0x81e7c sr_atoms [rl_patch32_region] None rl_patch32_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81e7c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HREG | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rl_patch32_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E33, E35, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs EX) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs EX) (Ereg regs EX)) by apply env_agree_refl.
unfold cfg_at. change (w64 0x81e7c) with (Z_to_bv 64 0x81e7c).
aj_run_to_tok rl_patch32_tbl_ok HS HJ SHOK JTspan 0x81e98.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs EX (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a0; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a0)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]];
  unfold rl_patch32_region in Hr; cbn in Hr; lia. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  let e14 := eval vm_compute in (sr_get (ss_regs ssf) (14%bv : bv 5)) in
  let e15 := eval vm_compute in (sr_get (ss_regs ssf) (15%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
  change (sr_get (ss_regs ssf) (14%bv : bv 5)) with e14;
  change (sr_get (ss_regs ssf) (15%bv : bv 5)) with e15 end.
split; [unfold w64; apply Hden; [exact E34 | lia]|].
split; [unfold w64; apply Hden; [exact E33 | lia]|].
unfold w64; apply Hden; [exact E35 | lia].
Qed.

(* ================= PART 2c. three trap sites that need their condition as a cond fact =================
   The engine cannot settle these three branches from an atom range (no sv_range case for a shift, for
   `xori -1` or for the 32-bit `addiw`). Each proof puts the branch's condition into the symbolic state with
   YP06 st_ok_add_cond (taken arm) or st_ok_add_cond_neg (fall-through arm) before the run: the acond is the
   instruction's own branch_cond (or its negation) over the exact sv the engine holds in the two registers at
   the branch, so YP0m cond_assumed answers the engine's query there. The value of that sv comes from the
   PART 2a shape lemma. *)

(* ---- T4 (`srli` form) + T3 at 0x820e4 .. 0x820f0 (M01's corruption loop, pod.h:446) ----
     0x820e4 srli t0,a1,0xe / 0x820e8 bnez t0 -> 0x82604 (unimp)                the bounds half
     0x820ec ld t0,0xf8(s1) (= ~pp) / 0x820f0 bltu t0,a1 -> 0x82604 (unimp)      the pointer half
   a1 = the byte offset into pp's buffer, s1 = R, the real frame. The walk carries off < 16384, so off >> 14 = 0
   and the `bnez` falls through (rlt_shr_small); the engine holds t0 = SAlu ALU_SRL (SOff 11 0) (SLit 14) and
   x0 = SLit 0 at 0x820e8, and that pair goes in as the cond fact. The `bltu` is decided by the ranges: the
   complement cell is in [2^63, 2^64 - 1] (pp + 19744 <= 2^63) and off is in [0, 16383]. *)
Definition rl_820e8_tbl : ctable := build_table rsegs 0x820e4 4 TEmpty.
Lemma rl_820e8_tbl_ok : table_ok rsegs rl_820e8_tbl.
Proof. apply build_table_ok0. lia. Qed.
Definition rl_820e8_facts : facts :=
mkFacts [ (11%nat, mkAF 0 16383 0); (33%nat, mkAF 9223372036854775808 18446744073709551615 0) ] [] [].
Lemma rl_trap_820e8 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (R off npp : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 9 = w64 R -> getr regs 11 = w64 off -> 0 <= off <= 16383 ->
0 <= R -> R + 256 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 248) 8 npp ->
9223372036854775808 <= npp -> npp <= 18446744073709551615 ->
SRr rsegs W (cfg_at rsegs 0x820e4 regs memc mdc)
(rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x820f4 [5]%bv
  (fun regs2 => getr regs2 5 = w64 npp)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R off npp HJ H9 H11 Hoff HR0 HR1 Hval Hn0 Hn1.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E9 : ew (Ereg regs (rl_t8_extra npp)) 9 = Z_to_bv 64 R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E11 : ew (Ereg regs (rl_t8_extra npp)) 11 = Z_to_bv 64 off)
  by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E33 : ew (Ereg regs (rl_t8_extra npp)) 33 = Z_to_bv 64 npp) by exact (ew_Ereg_extra regs _ 1).
assert (HREG : region_ok rsegs (Ereg regs (rl_t8_extra npp)) (mrestrict (w_H W) memc) rl_put32_region).
{ unfold region_ok, rl_put32_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val rsegs (Ereg regs (rl_t8_extra npp)) (mrestrict (w_H W) memc) R 248 8 (SOff 33 0) npp).
  - apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r. rewrite !unsigned_lit_small by lia.
    unfold zcanon, M64. apply Z.mod_small. lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - exact Hval. }
assert (HS0 : st_ok rsegs (Ereg regs (rl_t8_extra npp))
  (mkSS 0x820e4 sr_atoms [rl_put32_region] None rl_820e8_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x820e4) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HREG | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rl_820e8_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E11, E33, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
(* the value of t0 at the branch, then the cond fact: the `bnez` is not taken *)
assert (Ev : sv_denot (Ereg regs (rl_t8_extra npp)) (SAlu ALU_SRL (SOff 11 0) (SLit 14)) = w64 (Z.shiftr off 14)).
{ cbn [sv_denot]. rewrite E11, unsigned_lit_small, Z.add_0_r by lia. rewrite zalu64_sound.
  unfold zalu64, w64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
  rewrite (zcanon_small off) by lia. change (Z.land (zcanon 14) 63) with 14. reflexivity. }
pose proof (st_ok_add_cond_neg rsegs _ _ _ BC_NE (SAlu ALU_SRL (SOff 11 0) (SLit 14)) (SLit 0) HS0
  ltac:(rewrite Ev; change (sv_denot _ (SLit 0)) with (w64 0); exact (rlt_shr_small off ltac:(lia)))) as HS.
clear HS0.
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs (rl_t8_extra npp)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (rl_t8_extra npp)) (Ereg regs (rl_t8_extra npp))) by apply env_agree_refl.
unfold cfg_at. change (w64 0x820e4) with (Z_to_bv 64 0x820e4).
aj_run_to_tok rl_820e8_tbl_ok HS HJ SHOK JTspan 0x820f4.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (rl_t8_extra npp) (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a0; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a0)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]];
  unfold rl_put32_region in Hr; cbn in Hr; lia. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e5 := eval vm_compute in (sr_get (ss_regs ssf) (5%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (5%bv : bv 5)) with e5 end.
unfold w64. apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r.
rewrite !unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* ---- T2 at 0x8117c .. 0x81184 (case 5 of ent_build, fuzz.h:63) ----
     0x8117c not a0,s2 / 0x81180 bgeu a0,s8 -> 0x81188 / 0x81184 j 0x82604 (unimp)
   s2 = the cursor c, s8 = the count n of bytes it takes. `not a0,s2` is `xori a0,s2,-1`, which the engine keeps
   as SAlu ALU_XOR (SOff 18 0) (SLit (-1)); the `bgeu` is taken because c + n does not wrap (rlt_not_le), and
   that compare over (the complement, SOff 24 0) goes in as the cond fact. The input block gives c + n < 2^64. *)
Definition rl_81180_tbl : ctable := build_table rsegs 0x8117c 3 TEmpty.
Lemma rl_81180_tbl_ok : table_ok rsegs rl_81180_tbl.
Proof. apply build_table_ok0. lia. Qed.
Definition rl_81180_facts : facts := mkFacts [] [] [].
Lemma rl_trap_81180 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (c n : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 18 = w64 c -> getr regs 24 = w64 n -> 0 <= c -> 0 <= n -> c + n < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs 0x8117c regs memc mdc)
(rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x81188 [10]%bv
  (fun regs2 => getr regs2 10 = w64 (Z.lnot c))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs c n HJ H18 H24 Hc Hn Hcn.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E18 : ew (Ereg regs jt_extra) 18 = Z_to_bv 64 c)
  by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E24 : ew (Ereg regs jt_extra) 24 = Z_to_bv 64 n)
  by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (HS0 : st_ok rsegs (Ereg regs jt_extra) (mkSS 0x8117c sr_atoms [] None rl_81180_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8117c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [exact I | split; [exact I | exact I]]. }
(* the value of a0 at the branch (the 64-bit complement of c), then the cond fact: the `bgeu` is taken *)
assert (Ev : sv_denot (Ereg regs jt_extra) (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) = w64 (Z.lnot c)).
{ cbn [sv_denot]. rewrite E18, unsigned_lit_small, Z.add_0_r by lia. rewrite zalu64_sound.
  unfold zalu64, w64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
  rewrite (zcanon_small c) by lia. change (zcanon (-1)) with (Z.ones 64).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, Z.lxor_spec, Z.lnot_spec by lia.
  destruct (Z.testbit c i), (Z.testbit (Z.ones 64) i); reflexivity. }
assert (Eb : sv_denot (Ereg regs jt_extra) (SOff 24 0) = w64 n).
{ cbn [sv_denot]. rewrite E24, unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
pose proof (st_ok_add_cond rsegs _ _ _ BC_GEU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 24 0) HS0
  ltac:(rewrite Ev, Eb; exact (rlt_not_le c n ltac:(lia) ltac:(lia) ltac:(lia)))) as HS.
clear HS0.
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs jt_extra) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs jt_extra) (Ereg regs jt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 0x8117c) with (Z_to_bv 64 0x8117c).
aj_run_to_tok rl_81180_tbl_ok HS HJ SHOK JTspan 0x81188.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs jt_extra (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10 end.
exact Ev.
Qed.

(* ---- T6 at 0x81930 .. 0x81934 (the record write, pod.h:432) ----
     0x81930 addiw a2,a0,1 / 0x81934 blt a2,a0 -> 0x82604 (unimp)
   a0 = n_ent, the record count the `lw` before the block read. The engine keeps a2 as the 32-bit sum
   SAluw ALU_ADD (SOff 10 0) (SLit 1); the record count is at most 32, so n + 1 does not overflow 32 bits and
   the `blt` falls through (rlt_addiw_inc); that compare over (the sum, SOff 10 0) goes in as the cond fact. *)
Definition rl_81934_tbl : ctable := build_table rsegs 0x81930 2 TEmpty.
Lemma rl_81934_tbl_ok : table_ok rsegs rl_81934_tbl.
Proof. apply build_table_ok0. lia. Qed.
Definition rl_81934_facts : facts := mkFacts [] [] [].
Lemma rl_trap_81934 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (n : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 10 = w64 n -> 0 <= n <= 32 ->
SRr rsegs W (cfg_at rsegs 0x81930 regs memc mdc)
(rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x81938 [12]%bv
  (fun regs2 => getr regs2 12 = w64 (n + 1))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs n HJ H10 Hn.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E10 : ew (Ereg regs jt_extra) 10 = Z_to_bv 64 n)
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HS0 : st_ok rsegs (Ereg regs jt_extra) (mkSS 0x81930 sr_atoms [] None rl_81934_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81930) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [exact I | split; [exact I | exact I]]. }
(* the value of a2 at the branch (n + 1 in 32 bits, sign-extended), then the cond fact: the `blt` is not taken *)
assert (Ev : sv_denot (Ereg regs jt_extra) (SAluw ALU_ADD (SOff 10 0) (SLit 1)) = w64 (n + 1)).
{ cbn [sv_denot]. rewrite E10, unsigned_lit_small, Z.add_0_r by lia. rewrite zalu32_sound.
  unfold zalu32, w64. rewrite Z_to_bv64_canon. cbn [zalu_raw]. unfold zu32, M32.
  rewrite (Z.mod_small n) by lia. change (1 mod 2 ^ 32) with 1.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. f_equal. lia. }
assert (Eb : sv_denot (Ereg regs jt_extra) (SOff 10 0) = w64 n).
{ cbn [sv_denot]. rewrite E10, unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
pose proof (st_ok_add_cond_neg rsegs _ _ _ BC_LT (SAluw ALU_ADD (SOff 10 0) (SLit 1)) (SOff 10 0) HS0
  ltac:(rewrite Ev, Eb; exact (rlt_addiw_inc n ltac:(lia) ltac:(lia)))) as HS.
clear HS0.
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs jt_extra) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs jt_extra) (Ereg regs jt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 0x81930) with (Z_to_bv 64 0x81930).
aj_run_to_tok rl_81934_tbl_ok HS HJ SHOK JTspan 0x81938.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs jt_extra (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e12 := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e12 end.
exact Ev.
Qed.
End d.
End b.

(* ============================== PART 5. the pod_write_ent call adapter (B only) ==============================
   Image B keeps pod_write_ent(pp, e) out of line at 0x82bac and calls it where image A inlines it: 0x80818
   (pod.h:404, the shape-7 Int pod e at F + 0xf0), 0x81908 (pod.h:430, the count loop's e62 at F + 0x210, after
   the capacity guard `bltu a1,a0` 0x818fc) and 0x81c08 (pod.h:416, the Int-7 value e42 at F + 0x180). At all
   three a0 = pp and a1 is the object's address: at 0x80814 a0 is loaded from the real-frame cell R+0x140; at
   0x81900 it is `mv a0,a5` and at 0x81c04 `mv a0,s8`, where a5 and s8 hold pp (s8 loaded from R+0x140 at 0x809bc).
   Its contract is lib/AU/PweSpec.v's pod_write_ent_specX: a plain callee contract (no side-stack frame), whose
   post is pw_post with the float state kept, E = pwe_E pp len e and T = T_pwe_STK = 48 + ESTACK. rl_pwe_post
   is that post's text, so a walk lane discharges the hypothesis of rl_pwe_at with the contract itself.
   rl_pwe_at turns it into the rl_wpost shape at the return pc (clobbering the caller-saved registers, writing
   pwe_E and the callee's stack window); rl_pwe_seq chains it after a block that stops at 0x82bac with ra = the
   return pc, as RPgSteps' rl_intrin_seq does for the intrinsics.
   rl_pwe_site collects the premises the contract asks of the object e at F + off from what a walk lane has:
   the class-4 frame (F mod 32 = 0, in_app F 1024), the object's offset and the lane's shadow facts over it
   (lib/AU/RPgMem.v's rm_B_ra_e / _e42 / _e62 give the range_addressable and the hull), the record's
   well-formedness (Pod/Model ent_wf, which gives pwe_len e <= 56 and the three e_* premises) and the build
   invariant's len. *)
Definition PWE_ENT : Z := 0x82bac.
Definition PWE_OFF_E : Z := 0xf0.
Definition PWE_OFF_E42 : Z := 0x180.
Definition PWE_OFF_E62 : Z := 0x210.
Definition PWE_RA_SHAPE7 : Z := 0x8081c.
Definition PWE_RA_COUNT : Z := 0x8190c.
Definition PWE_RA_INT7 : Z := 0x81c0c.

(* n = |enc_pod e| is at most 56 and the three e_* premises, from Pod/Model's ent_wf *)
Lemma rl_pwe_len_of_wf : forall e, Model.ent_wf e ->
0 <= pwe_len e <= 56 /\ Z.of_nat (length (Model.e_body e)) = Model.e_size e /\
Model.e_size e <= Layout.ENT_SIZE - 8 /\ 0 <= Model.e_type e < 2 ^ 32.
Proof.
intros e He. pose proof (Model.enc_pod_len_bound e He) as [Hle _].
destruct He as (Ht & Hb & Hs). unfold pwe_len.
split; [split; [lia | exact Hle]|].
split; [rewrite Hb; apply Z2Nat.id; lia|].
split; [unfold Layout.ENT_SIZE; lia | exact Ht].
Qed.
(* the two ways a call site bounds len + n: the build invariant len <= 5440, or the capacity guard at 0x818fc *)
Lemma rl_pwe_len_small : forall len e, 0 <= len -> len <= 5440 -> Model.ent_wf e ->
len + pwe_len e <= Layout.POD_BUF_MAX.
Proof.
intros len e H0 H1 He. destruct (rl_pwe_len_of_wf e He) as [[Hn0 Hn1] _].
unfold Layout.POD_BUF_MAX. lia.
Qed.
Lemma rl_pwe_len_guard : forall len e, 0 <= len -> len + 112 <= Layout.POD_BUF_MAX -> Model.ent_wf e ->
len + pwe_len e <= Layout.POD_BUF_MAX.
Proof.
intros len e H0 H1 He. destruct (rl_pwe_len_of_wf e He) as [[Hn0 Hn1] _].
unfold Layout.POD_BUF_MAX in *. lia.
Qed.

Section c5. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the object premises of the contract at a frame object F + off, and the two separations *)
Lemma rl_pwe_site : forall F off q pp (sp : Z),
F mod 32 = 0 -> in_app F 1024 -> q = F + off -> 0 <= off -> off mod 8 = 0 ->
off + Layout.ENT_SIZE < 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) ->
(F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
0 <= q /\ q mod 8 = 0 /\ amem_range q Layout.ENT_SIZE /\
(pp + Layout.PP_SIZE <= q \/ q + Layout.ENT_SIZE <= pp) /\
(q + Layout.ENT_SIZE <= sp - T_pwe_STK \/ sp <= q).
Proof.
intros F off q pp sp Hm Ha -> Ho0 Ho8 Hoff Hpp Hsp.
destruct (rl_fbounds F Hm Ha) as (H4096 & Hceil & _ & _ & _ & Hamr).
assert (Hq8 : (F + off) mod 8 = 0).
{ destruct (rl_fdiv F Hm) as [E1 _]. pose proof (Z.div_mod off 8 ltac:(lia)) as Eo.
  rewrite Ho8, Z.add_0_r in Eo. rewrite E1, Eo.
  replace (32 * (F / 32) + 8 * (off / 8)) with ((4 * (F / 32) + off / 8) * 8) by ring. apply Z_mod_mult. }
split; [lia|]. split; [exact Hq8|].
split; [apply Hamr; [lia | unfold Layout.ENT_SIZE; lia | unfold Layout.ENT_SIZE in *; lia]|].
split; [unfold Layout.PP_SIZE, Layout.ENT_SIZE in *; lia|].
unfold Layout.ENT_SIZE in *. lia.
Qed.

(* The premises pod_write_ent_specX asks of the object and of len, at each of image B's three call sites.
   The caller supplies the frame's geometry (the class-4 law), the heap block's and the callee stack's
   separation from the frame, the build invariant's len, and the record's well-formedness; the lemma does the
   offset arithmetic and the length bound. The pp premises are PweSpec's own pwe_pp_of_block and
   pwe_awr_fresh, and the shadow premises of the object are lib/AU/RPgMem.v's rm_B_ra_e / _e42 / _e62. *)
Definition rl_pwe_site_concl (F off pp sp len : Z) (e : Model.ent) : Prop :=
0 <= F + off /\ (F + off) mod 8 = 0 /\ amem_range (F + off) Layout.ENT_SIZE /\
(pp + Layout.PP_SIZE <= F + off \/ F + off + Layout.ENT_SIZE <= pp) /\
(F + off + Layout.ENT_SIZE <= sp - T_pwe_STK \/ sp <= F + off) /\
len + pwe_len e <= Layout.POD_BUF_MAX /\
Z.of_nat (length (Model.e_body e)) = Model.e_size e /\ Model.e_size e <= Layout.ENT_SIZE - 8 /\
0 <= Model.e_type e < 2 ^ 32.
Lemma rl_pwe_site_of : forall F off pp sp len e,
F mod 32 = 0 -> in_app F 1024 -> 0 <= off -> off mod 8 = 0 -> off + Layout.ENT_SIZE < 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) -> (F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
Model.ent_wf e -> len + pwe_len e <= Layout.POD_BUF_MAX ->
rl_pwe_site_concl F off pp sp len e.
Proof.
intros F off pp sp len e Hm Ha Ho0 Ho8 Hoff Hpp Hsp He Hlen.
destruct (rl_pwe_site F off (F + off) pp sp Hm Ha eq_refl Ho0 Ho8 Hoff Hpp Hsp)
  as (Hq0 & Hq8 & Hamr & Hsep1 & Hsep2).
destruct (rl_pwe_len_of_wf e He) as (_ & Hb & Hs & Ht).
unfold rl_pwe_site_concl.
repeat (split; [assumption|]). exact Ht.
Qed.
(* 0x80818 (pod.h:404): the shape-7 Int pod e at F + 0xf0; len <= 5440 from the build invariant *)
Lemma rl_pwe_site_80818 : forall F pp sp len e,
F mod 32 = 0 -> in_app F 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) -> (F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
0 <= len -> len <= 5440 -> Model.ent_wf e ->
rl_pwe_site_concl F PWE_OFF_E pp sp len e.
Proof.
intros F pp sp len e Hm Ha Hpp Hsp Hl0 Hl1 He.
apply rl_pwe_site_of; try assumption.
- unfold PWE_OFF_E; lia.
- unfold PWE_OFF_E; reflexivity.
- unfold PWE_OFF_E, Layout.ENT_SIZE; lia.
- exact (rl_pwe_len_small len e Hl0 Hl1 He).
Qed.
(* 0x81908 (pod.h:430): the count loop's e62 at F + 0x210; the capacity guard `bltu a1,a0` 0x818fc gives
   len + 112 <= 16384 on the arm that calls *)
Lemma rl_pwe_site_81908 : forall F pp sp len e,
F mod 32 = 0 -> in_app F 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) -> (F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
0 <= len -> len + 112 <= Layout.POD_BUF_MAX -> Model.ent_wf e ->
rl_pwe_site_concl F PWE_OFF_E62 pp sp len e.
Proof.
intros F pp sp len e Hm Ha Hpp Hsp Hl0 Hl1 He.
apply rl_pwe_site_of; try assumption.
- unfold PWE_OFF_E62; lia.
- unfold PWE_OFF_E62; reflexivity.
- unfold PWE_OFF_E62, Layout.ENT_SIZE; lia.
- exact (rl_pwe_len_guard len e Hl0 Hl1 He).
Qed.
(* 0x81c08 (pod.h:416): the Int-7 value e42 at F + 0x180; len <= 5440 from the build invariant *)
Lemma rl_pwe_site_81c08 : forall F pp sp len e,
F mod 32 = 0 -> in_app F 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) -> (F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
0 <= len -> len <= 5440 -> Model.ent_wf e ->
rl_pwe_site_concl F PWE_OFF_E42 pp sp len e.
Proof.
intros F pp sp len e Hm Ha Hpp Hsp Hl0 Hl1 He.
apply rl_pwe_site_of; try assumption.
- unfold PWE_OFF_E42; lia.
- unfold PWE_OFF_E42; reflexivity.
- unfold PWE_OFF_E42, Layout.ENT_SIZE; lia.
- exact (rl_pwe_len_small len e Hl0 Hl1 He).
Qed.

Context {SK : YI16.sink_head}.
Section d5.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* lib/AU/PweSpec.v's pw_post at this unit's call sites, word for word: the hypothesis of rl_pwe_at is what
   pod_write_ent_specX concludes, so a walk lane passes the contract itself. *)
Definition rl_pwe_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model)
(pp len : Z) (e : Model.ent) (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world rsegs -> config -> Prop :=
fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx2 regs2 (getr regs 1) mem2 (seg_rom rsegs)) md2 /\ (fun f => f = fx) fx2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_pwe_STK <= a < spZ regs) -> ~ pwe_E pp len e a ->
aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
R W2 regs2 mem2.
(* the call as one block from 0x82bac to the return pc *)
Lemma rl_pwe_at : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (pp len retpc o : Z)
  (e : Model.ent) (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
getr regs 1 = w64 retpc -> spZ regs = sp0 + o ->
SRr rsegs W (cfg_at rsegs PWE_ENT regs memc mdc)
  (rl_pwe_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pp len e R) ->
SRr rsegs W (cfg_at rsegs PWE_ENT regs memc mdc)
  (rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc retpc rl_caller_saved
    (fun a => pwe_E pp len e a \/ (sp0 + o - T_pwe_STK <= a < sp0 + o)) R).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pp len retpc o e R Hra Hsp HC.
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & -> & HJ2 & HP & Hf & Hp & Hio & Hmo & Hkept & HR).
rewrite Hsp in Hkept.
exists ly2, S2, regs2, mem2, md2.
split; [rewrite Hra; reflexivity|].
split; [exact HJ2|].
split.
{ intros r Hr0 Hn. rewrite <- (Z_to_bv_bv_unsigned 5 r).
  rewrite (HP (bv_unsigned r) (rl_callee r Hr0 Hn)). rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact Hf|]. split; [exact Hp|]. split; [exact Hio|]. split; [exact Hmo|].
split.
{ intros a Ha Hn. apply Hkept; [exact Ha | intros X; apply Hn; right; exact X | intros X; apply Hn; left; exact X]. }
exact HR.
Qed.
(* a block that stops at 0x82bac with ra = retpc, then the call: one block to retpc *)
Lemma rl_pwe_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob (Wr : Z -> Prop)
  (R1 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) (pp len retpc o : Z) (e : Model.ent)
  (R2 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc PWE_ENT clob Wr R1) ->
(forall ly1 S1 W1 regs1 mem1 md1,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k -> R1 W1 regs1 mem1 ->
  getr regs1 1 = w64 retpc /\ spZ regs1 = sp0 + o /\
  SRr rsegs W1 (cfg_at rsegs PWE_ENT regs1 mem1 md1)
    (rl_pwe_post STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pp len e R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc retpc (clob ++ rl_caller_saved)
    (fun a => Wr a \/ pwe_E pp len e a \/ (sp0 + o - T_pwe_STK <= a < sp0 + o)) R2).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob Wr R1 pp len retpc o e R2 H1 Hpre.
eapply SRr_bind; [exact H1|].
intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
destruct (Hpre ly1 S1 W1 regs1 mem1 md1 HJ1 HR1) as (Hra & Hsp & HC).
eapply SRr_mono.
{ exact (rl_pwe_at STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pp len retpc o e R2 Hra Hsp HC). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|].
split.
{ intros r Hr0 Hn. rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply in_or_app; right; exact X)).
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply in_or_app; left; exact X]. }
split; [rewrite Hf2; exact Hf1|].
split; [eapply Permutation_trans; [exact Hp2 | exact Hp1]|].
split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2)|].
split.
{ intros a Ha Hn.
  rewrite (Hm2 a Ha ltac:(intros X; apply Hn; destruct X as [X|X]; [right; left; exact X | right; right; exact X])).
  apply Hm1; [exact Ha | intros X; apply Hn; left; exact X]. }
exact HR2.
Qed.
End d5.
End c5.
