(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run plumbing of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 964efd2f474 (cfg_keep, cfg_kwr_ro and the same_io chain of cfg_leaf, as l_keep, l_kwr and l_post) and of proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at b0f706c04a1 (awr_stk, as l_awr: the writable window is the frame [F, F + 0x60) at atom 2), for a segment of reac_role_prop_parse's walk that starts and ends at the cuts of lib/A/RPgParseBase.v; the entry states, exits, string lemmas and the walk below are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v at afaa3cb55c1d; for reac-pw/fuzz_rate's reac_rate_prop_parse at image A: module paths and the rl_ / Role names changed to rate's (rt_cstr, rt_fxk, Rate.harness_parse, Rate.RATE_KEY, RtPgStrcmp's rt_cstr_args and cstr_at_of_rt_cstr; kept_run and same_io_wvb from RtPgParseBase), the pcs and image constants are fuzz_rate.asan's (key 0x21720, strcmp wrapper 0x4219c), and on the three next-child paths the foreach back edge 0x84728 beqz is the taken side to L2 (its fall-through 0x8472c j 0x84554 is the impossible one). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgParseL.v; 499 of its 567 lines of code are new or changed and 845 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v at afaa3cb55c1d for reac-pw/fuzz_rate's
   reac_rate_prop_parse: module paths and the rl_ / Role names changed to rate's; the pcs are image A's of
   fuzz_rate.asan; the find loop's back edge is 0x845cc beqz -> L1 (taken: the next pass) with 0x845d0 j 0x84554
   (not taken: impossible, r' = 0 mod 4). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgParseF.v at f7246d55e8c3 for image B
   (fuzz_rate.asan-ubsan); the image is lib/AU/Img0.v's and the cut vocabulary lib/AU/RtPgParseBaseB.v's; the pcs are
   image B's; P + 8 is in a1 (atom 11) at L1, image A's a0; the ret 0 leaves go through 0x84804 li a0,0; the trap
   branch 0x848ac is new and image A's alignment branch 0x84638 is gone. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgParseFB.v, with its module paths and module names changed; 1564 of its 1625 lines of code are new or changed and 506 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/ParseValue.v at 3e9fc5c8969 (pv_range,
   pv_body, pv_res_big, pv_res_bad, pv_res_bool, pv_res_int, pv_res_flt: the model of value_pod_to_byte and
   value_in_range) with module paths changed and the names prefixed hv_; the engine form of the value read in the
   form of proofs/reac-pw/fuzz_role/lib/A/RPgParseK.v at afaa3cb55c1 (the entry split on the child's size, the pod
   region with the size / type / body chunks, asm_eq / U_asm for the four body bytes put together, br_big / br_ty)
   and the step chain of the double instructions in the form of proofs/reac-pw/fuzz_role/lib/A/RPgParseFV.v at
   afaa3cb55c1 (fvw_auipc, fvw_beq_tk / fvw_beq_ft, fvw_jal0, fv_getr_upd / fv_getr_set), restated for headamp's
   cut states (lib/A/HPgParseCut.v) and the frame hole (lib/A/HPgHole.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgParseVal.v, with its module paths, module names and numbers changed; 509 of its 634 lines of code are new or changed and 1500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseK.v at d428443238a; for image B
   (fuzz_role.asan-ubsan): the image is lib/AU/Img0.v's and the cut vocabulary lib/AU/RPgParseBase.v's (kept_run and
   same_io_wvb from there); the pcs are image B's; the key slot at L2 and the Int value at T are in a1 (register 11),
   image A's a0. *)
(* Segment K of reac_role_prop_parse's walk on image B (fuzz_role.asan-ubsan): from K 0x833bc (strcmp's return)
   through the next-child step to L2, or the value read to T (Int) / FV (Float) / ret -1; proves RPgParseBase's
   segK_stmt. *)
(* The code (fuzz_role.asan-ubsan, pinned sha256 b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0):
     0x833bc beqz a0,0x83438                      strcmp's result rv
   rv <> 0 (the key is not "reac.cfg.role"):
     0x833c0 a1 = 0; 0x833c4 lb a0,0(s8) (the shadow byte of s1, s8 = (s1 >> 3) + s3 from 0x83314); slow path
     0x833fc .. 0x83408 (error-path call 0x836b4 not reached); 0x833cc lwu a0,0(s1) = CS; s1 += ((CS + 7) | 7) + 1;
     0x833e4 bnez (s1 & 3) -> 0x831e8 (never taken: P = 0 mod 16, c = 0 mod 4, the step a multiple of 8);
     0x833e8 j 0x83300 = L2 with c' = c + round_up8 (8 + CS) and the key slot a1 empty.
   rv = 0 (the value of the key): 0x83438 the shadow byte of s1 again (slow path 0x83638 .., error-path call 0x83648);
     0x83440 CS = lwu 0(s1); 0x83448 CS >> 20 <> 0 -> 0x83594 ret -1; the type at s1 + 4 (instrumented, error-path
     call 0x83658); CS >= 4 and type 4: the instrumented lw of s1 + 8 (error-path call 0x83668), then T 0x83488 with
     a1 = the 32-bit value sign-extended; CS < 4 or type not 4 / 6: ret -1; type 6 and CS >= 4: the 1-byte checks of
     s1 + 8 and s1 + 11 (error-path calls 0x8368c, 0x836a0), four lbu, the 4 bytes put together, sw a0,8(sp),
     FV 0x83524 (a2 = 0x10518 from 0x83518 auipc).
   No branch of this segment goes to the `unimp` 0x835c8 (T's 0x8349c / 0x834a4 are segment T's).
   The engine reads the pod at s1 = P + c as a region of atom 9: CS (atom 43), type (44) and, when CS >= 4, the 4
   value bytes (45); one shadow entry covers the bytes it checks. The walk is split on CS >= 4 at the entry. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YA0d YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Cursor Model Accessors Spa Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require reac_role_prop_parse.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec RPgStrcmp.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the entry state ======================================= *)
(* s8 holds the shadow address of s1 (0x83314 srli s8,s1,3; 0x83318 add s8,s8,s3) *)
Definition s8_sv : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 19 0).
Definition k_regs : list sv := sr_set sr_atoms (24%bv : bv 5) s8_sv.
Definition k_hi (big : bool) : Z := if big then 12 else 8.
(* the child at s1: its size CS, its type and (CS >= 4) its 4 body bytes, read-only *)
Definition pod_region (big : bool) : YP09.region :=
YP09.mkRegion (Some 9%nat) 0 (k_hi big) 0 0
([YP09.mkChunk 0 (CVal 4 (SOff 43 0)); YP09.mkChunk 4 (CVal 4 (SOff 44 0))] ++
 if big then [YP09.mkChunk 8 (CVal 4 (SOff 45 0))] else []).
Definition k_facts (big : bool) : facts :=
mkFacts [(2%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (9%nat, mkAF 0 (2 ^ 47 - 12) 2); (19%nat, mkAF SBr SBr 0);
         (43%nat, if big then mkAF 4 (2 ^ 32 - 1) 0 else mkAF 0 3 0); (44%nat, mkAF 0 (2 ^ 32 - 1) 0);
         (45%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ssK (big : bool) : sstate := mkSS PC_K k_regs [frame_region []; pod_region big] None (k_facts big).
Definition shK (big : bool) : list shent := [mkSHE 9 0 (k_hi big)].
(* the segment's own env values (atoms 43, 44, 45) *)
Definition k_L (x : pctx) (c : Z) : list word :=
[w64 (Spa.u32_at (x_bs x) c); w64 (Spa.u32_at (x_bs x) (c + 4)); w64 (Spa.u32_at (x_bs x) (c + 8))].
Definition k_big (x : pctx) (c : Z) : bool := 4 <=? Spa.u32_at (x_bs x) c.

(* the values the engine leaves: s1 of the next child, the 4 bytes of the Float body put together *)
Abbreviation s1n_sv := (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SAlu ALU_OR (SOff 43 7) (SLit 7))) (SLit 1)) (only parsing).
Abbreviation asm_sv := (SAlu ALU_OR
  (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL (SOff 45 0) (SLit 24)) (SLit 24))
     (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL (SOff 45 0) (SLit 16))) (SLit 16)))
  (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL (SOff 45 0) (SLit 8))) (SLit 8))
     (SExt false 8 (SOff 45 0)))) (only parsing).

(* the registers a continuing leaf finds as at the cut *)
Definition k_keep_ok (sr : list sv) : bool :=
forallb (fun p => sv_eqb (sr_get sr (fst p)) (SOff (snd p) 0))
[((2%bv : bv 5), 2%nat); (Z_to_bv 5 3, 3%nat); (Z_to_bv 5 4, 4%nat); ((8%bv : bv 5), 8%nat); ((19%bv : bv 5), 19%nat);
 (Z_to_bv 5 25, 25%nat); (Z_to_bv 5 26, 26%nat); (Z_to_bv 5 27, 27%nat); ((18%bv : bv 5), 18%nat);
 ((20%bv : bv 5), 20%nat); ((21%bv : bv 5), 21%nat); ((22%bv : bv 5), 22%nat); ((23%bv : bv 5), 23%nat)].

(* ======================================= the model ======================================= *)
Lemma walk_res_fuel : forall bs body size c n m k, 0 <= c ->
(Z.to_nat (body + size - c) < n)%nat -> (Z.to_nat (body + size - c) < m)%nat ->
walk_res bs body size c n k = walk_res bs body size c m k.
Proof.
intros bs body size c n m k H0 Hn Hm. unfold reac_role_prop_parse.walk_res.
rewrite (Spa.struct_children_fuel bs body size c n m H0 Hn Hm). reflexivity.
Qed.

Lemma child_in_facts : forall x r c, child_in x r c ->
r + 16 <= c /\ c + 8 + Spa.u32_at (x_bs x) c <= r + 16 + Spa.u32_at (x_bs x) (r + 8).
Proof.
intros x r c H. unfold child_in, Spa.pod_is_inside, Spa.ptr_type_inside, Spa.ptrinside, Spa.ptr_remaining in H.
repeat match goal with Hx : (_ && _) = true |- _ => apply andb_prop in Hx as [? ?] end.
repeat match goal with Hx : (_ <=? _) = true |- _ => apply Z.leb_le in Hx end.
lia.
Qed.

(* rv <> 0: the key at ck is not "reac.cfg.role"; the walk goes on at the next child with the key slot empty *)
Lemma k_next_model : forall x r c ck rv, 0 <= c ->
child_in x r c -> key_ok x ck -> (rv = 0 <-> l2_key (x_bs x) (Some ck) = Some Role.ROLE_KEY) -> rv <> 0 ->
x_res x = walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c (l2_fuel x r c) (l2_key (x_bs x) (Some ck)) ->
x_res x = walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c))
  (l2_fuel x r (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c))) None.
Proof.
intros x r c ck rv Hc0 Hin Hk Hrv Hne HW.
pose proof (child_in_facts x r c Hin) as [H1 H2].
pose proof (u32_at_range (x_bs x) c) as HCS.
pose proof (reac_role_prop_parse.pb_lor7 (Spa.u32_at (x_bs x) c) ltac:(lia)) as (R1 & R2 & _).
rewrite HW. unfold l2_fuel at 1. rewrite reac_role_prop_parse.walk_res_step.
unfold child_in in Hin. rewrite Hin.
destruct Hk as (_ & _ & Hs).
destruct (l2_key (x_bs x) (Some ck)) as [k'|] eqn:Ek; [|unfold l2_key in Ek; contradiction].
destruct (Cursor.bytes_eqb k' Role.ROLE_KEY) eqn:Eb.
- apply Cursor.bytes_eqb_eq in Eb. subst k'. exfalso. apply Hne. apply Hrv. reflexivity.
- unfold l2_fuel. apply walk_res_fuel; lia.
Qed.

(* rv = 0: the key is "reac.cfg.role"; the answer is the value read of the child at c *)
Lemma k_val_model : forall x r c ck rv,
child_in x r c -> (rv = 0 <-> l2_key (x_bs x) (Some ck) = Some Role.ROLE_KEY) -> rv = 0 ->
x_res x = walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c (l2_fuel x r c) (l2_key (x_bs x) (Some ck)) ->
x_res x = Role.spa_role_value (Spa.child_at (x_bs x) c).
Proof.
intros x r c ck rv Hin Hrv H0 HW. rewrite HW, (proj1 Hrv H0). unfold l2_fuel.
rewrite reac_role_prop_parse.walk_res_step. unfold child_in in Hin. rewrite Hin.
assert (E : Cursor.bytes_eqb Role.ROLE_KEY Role.ROLE_KEY = true) by (apply Cursor.bytes_eqb_eq; reflexivity).
rewrite E. reflexivity.
Qed.

(* ======================================= the engine's values ======================================= *)
Ltac kpeel := repeat rewrite ew_ewset_other by lia.
(* rewrite every innermost zcanon whose argument lia bounds *)
Ltac zc_in := repeat match goal with |- context [zcanon ?t] =>
  lazymatch t with context [zcanon _] => fail | _ => rewrite (zcanon_id t) by (unfold M64; lia) end end.

Lemma br_rv : forall E rv, ew E 10 = Z_to_bv 64 rv -> -1 <= rv <= 1 ->
branch_taken BC_EQ (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = (rv =? 0).
Proof.
intros E rv H Hr. rewrite branch_eq_U, U_SOff, H, U_SLit.
assert (rv = -1 \/ rv = 0 \/ rv = 1) as [-> | [-> | ->]] by lia; vm_compute; reflexivity.
Qed.

Lemma U_s1n : forall E p cs, ew E 9 = Z_to_bv 64 p -> ew E 43 = Z_to_bv 64 cs -> 0 <= p -> 0 <= cs < 2 ^ 32 ->
p + cs + 16 < 2 ^ 64 -> U E s1n_sv = p + Spa.round_up8 (8 + cs).
Proof.
intros E p cs H9 H43 Hp Hcs Hs. pose proof (reac_role_prop_parse.pb_lor7 cs ltac:(lia)) as (R1 & R2 & _).
rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 9 p H9) by lia. rewrite U_SOff, H43, unsigned_lit_small by lia. rewrite !U_SLit.
zc_in. lia.
Qed.

Lemma br_align : forall E p cs, ew E 9 = Z_to_bv 64 p -> ew E 43 = Z_to_bv 64 cs -> 0 <= p -> 0 <= cs < 2 ^ 32 ->
p + cs + 16 < 2 ^ 64 -> p mod 4 = 0 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND s1n_sv (SLit 3))) (sv_denot E (SLit 0)) = false.
Proof.
intros E p cs H9 H43 Hp Hcs Hs H4. pose proof (reac_role_prop_parse.pb_lor7 cs ltac:(lia)) as (_ & R2 & R3).
rewrite branch_ne_U, U_SAlu, (U_s1n E p cs H9 H43 Hp Hcs Hs), !U_SLit. cbn [zalu_raw].
change (zcanon 3) with 3. change (zcanon 0) with 0.
assert (L : Z.land (p + Spa.round_up8 (8 + cs)) 3 = 0).
{ change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite <- R2. lia. }
rewrite L. reflexivity.
Qed.

Lemma br_big : forall E cs, ew E 43 = Z_to_bv 64 cs -> 0 <= cs < 2 ^ 32 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_SRL (SOff 43 0) (SLit 20))) (sv_denot E (SLit 0)) = negb (cs <? 2 ^ 20).
Proof.
intros E cs H Hc. rewrite branch_ne_U, U_SAlu, (U_atom E 43 cs H) by lia. rewrite !U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 20) 63) with 20. change (zcanon 0) with 0.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576.
rewrite zcanon_id by (unfold M64; lia). f_equal.
destruct (Z.ltb_spec cs 1048576); [apply Z.eqb_eq | apply Z.eqb_neq]; lia.
Qed.

Lemma br_ty : forall E ty k, ew E 44 = Z_to_bv 64 ty -> 0 <= ty < 2 ^ 32 -> 0 <= k < 2 ^ 31 ->
branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 44 0))) (sv_denot E (SLit k)) = negb (ty =? k).
Proof.
intros E ty k H Hty Hk. rewrite branch_ne_U, U_SExt, (U_atom E 44 ty H) by lia. rewrite U_SLit. cbv iota. f_equal.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small ty) by lia.
rewrite (zcanon_id k) by (unfold M64; lia).
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
unfold zcanon, M64.
destruct (Z.ltb_spec ty (2 ^ 31)).
- rewrite (Z.mod_small (ty + 2 ^ 31)) by lia. replace (ty + 2 ^ 31 - 2 ^ 31) with ty by lia.
  rewrite Z.mod_small by lia. reflexivity.
- replace (ty + 2 ^ 31) with ((ty - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (ty - 2 ^ 31)) by lia.
  replace (ty - 2 ^ 31 - 2 ^ 31) with ((ty + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec (ty + (2 ^ 64 - 2 ^ 32)) k); destruct (Z.eqb_spec ty k); first [reflexivity | lia].
Qed.

Lemma a0_int : forall E b, ew E 45 = Z_to_bv 64 b -> 0 <= b < 2 ^ 32 ->
sv_denot E (SExt true 32 (SOff 45 0)) = w64 (Accessors.s32 b).
Proof.
intros E b H Hb. rewrite denot_lit_U. unfold w64. apply Z_to_bv64_eq_mod.
rewrite U_SExt, (U_atom E 45 b H) by lia. cbv iota. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small b) by lia. unfold zcanon, M64. rewrite Z.mod_mod by lia. f_equal.
unfold Accessors.s32, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec b (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- replace (b + 2 ^ 31) with ((b - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

(* the 4 bytes of a u32 put together by shifts and ors *)
Lemma asm_eq : forall b, 0 <= b < 2 ^ 32 ->
Z.lor (Z.lor (Z.shiftl (Z.shiftr b 24) 24) (Z.shiftl (Z.shiftr b 16 mod 2 ^ 8) 16))
      (Z.lor (Z.shiftl (Z.shiftr b 8 mod 2 ^ 8) 8) (b mod 2 ^ 8)) = b.
Proof.
intros b Hb. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
destruct (Z.lt_ge_cases i 8) as [H8|H8]; [|destruct (Z.lt_ge_cases i 16) as [H16|H16];
  [|destruct (Z.lt_ge_cases i 24) as [H24|H24]]].
- rewrite (Z.shiftl_spec_low (Z.shiftr b 24) 24 i) by lia.
  rewrite (Z.shiftl_spec_low (Z.shiftr b 16 mod 2 ^ 8) 16 i) by lia.
  rewrite (Z.shiftl_spec_low (Z.shiftr b 8 mod 2 ^ 8) 8 i) by lia.
  rewrite (Z.mod_pow2_bits_low b 8 i) by lia. reflexivity.
- rewrite (Z.shiftl_spec_low (Z.shiftr b 24) 24 i) by lia.
  rewrite (Z.shiftl_spec_low (Z.shiftr b 16 mod 2 ^ 8) 16 i) by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 8 mod 2 ^ 8) 8 i) by lia.
  rewrite (Z.mod_pow2_bits_low (Z.shiftr b 8) 8 (i - 8)) by lia.
  rewrite (Z.shiftr_spec b 8 (i - 8)) by lia. replace (i - 8 + 8) with i by lia.
  rewrite (Z.mod_pow2_bits_high b 8 i) by lia. destruct (Z.testbit b i); reflexivity.
- rewrite (Z.shiftl_spec_low (Z.shiftr b 24) 24 i) by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 16 mod 2 ^ 8) 16 i) by lia.
  rewrite (Z.mod_pow2_bits_low (Z.shiftr b 16) 8 (i - 16)) by lia.
  rewrite (Z.shiftr_spec b 16 (i - 16)) by lia. replace (i - 16 + 16) with i by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 8 mod 2 ^ 8) 8 i) by lia.
  rewrite (Z.mod_pow2_bits_high (Z.shiftr b 8) 8 (i - 8)) by lia.
  rewrite (Z.mod_pow2_bits_high b 8 i) by lia. destruct (Z.testbit b i); reflexivity.
- rewrite (Z.shiftl_spec (Z.shiftr b 24) 24 i) by lia.
  rewrite (Z.shiftr_spec b 24 (i - 24)) by lia. replace (i - 24 + 24) with i by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 16 mod 2 ^ 8) 16 i) by lia.
  rewrite (Z.mod_pow2_bits_high (Z.shiftr b 16) 8 (i - 16)) by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 8 mod 2 ^ 8) 8 i) by lia.
  rewrite (Z.mod_pow2_bits_high (Z.shiftr b 8) 8 (i - 8)) by lia.
  rewrite (Z.mod_pow2_bits_high b 8 i) by lia. destruct (Z.testbit b i); reflexivity.
Qed.

Lemma U_asm : forall E b, ew E 45 = Z_to_bv 64 b -> 0 <= b < 2 ^ 32 -> U E asm_sv = b.
Proof.
intros E b H Hb.
assert (U0 : U E (SOff 45 0) = b) by (apply U_atom; [exact H | lia]).
assert (Rs : forall k, 0 <= k -> 0 <= Z.shiftr b k <= b).
{ intros k Hk. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]. assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) in Hk; lia). nia. }
assert (Us : forall k, 0 <= k < 64 -> U E (SAlu ALU_SRL (SOff 45 0) (SLit k)) = Z.shiftr b k).
{ intros k Hk. rewrite U_SAlu, U0, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id k) by (unfold M64; lia).
  replace (Z.land k 63) with k by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small; [reflexivity|]; change (2 ^ 6) with 64; lia).
  pose proof (Rs k ltac:(lia)). apply zcanon_id. unfold M64. lia. }
assert (Ue : forall e v, U E e = v -> U E (SExt false 8 e) = v mod 2 ^ 8).
{ intros e v Hv. rewrite U_SExt, Hv. cbv iota. change (2 ^ Z.of_N 8) with (2 ^ 8).
  apply zcanon_id. pose proof (Z.mod_pos_bound v (2 ^ 8) ltac:(lia)). unfold M64. lia. }
assert (Ul : forall e v k, U E e = v -> 0 <= k < 64 -> 0 <= Z.shiftl v k < 2 ^ 32 -> U E (SAlu ALU_SLL e (SLit k)) = Z.shiftl v k).
{ intros e v k Hv Hk Hr. rewrite U_SAlu, Hv, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id k) by (unfold M64; lia).
  replace (Z.land k 63) with k by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small; [reflexivity|]; change (2 ^ 6) with 64; lia).
  apply zcanon_id. unfold M64. lia. }
assert (Uo : forall e1 e2 v1 v2, U E e1 = v1 -> U E e2 = v2 -> 0 <= v1 < 2 ^ 32 -> 0 <= v2 < 2 ^ 32 ->
  U E (SAlu ALU_OR e1 e2) = Z.lor v1 v2 /\ 0 <= Z.lor v1 v2 < 2 ^ 32).
{ intros e1 e2 v1 v2 H1 H2 R1 R2. pose proof (YO0a.lor_range v1 v2 32 R1 R2) as R.
  split; [|exact R]. rewrite U_SAlu, H1, H2. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. }
assert (Bm : forall v, 0 <= v mod 2 ^ 8 < 2 ^ 8) by (intros v; apply Z.mod_pos_bound; lia).
assert (Bl : forall v k, 0 <= v < 2 ^ 8 -> 0 <= k <= 24 -> 0 <= Z.shiftl v k < 2 ^ (8 + k)).
{ intros v k Hv Hk. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). nia. }
assert (B24 : 0 <= Z.shiftr b 24 < 2 ^ 8).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
pose proof (Bl _ 24 B24 ltac:(lia)) as L3.
pose proof (Bl _ 16 (Bm (Z.shiftr b 16)) ltac:(lia)) as L2.
pose proof (Bl _ 8 (Bm (Z.shiftr b 8)) ltac:(lia)) as L1.
change (2 ^ (8 + 24)) with (2 ^ 32) in L3.
assert (L2' : 0 <= Z.shiftl (Z.shiftr b 16 mod 2 ^ 8) 16 < 2 ^ 32) by (change (2 ^ (8 + 16)) with (2 ^ 24) in L2; lia).
assert (L1' : 0 <= Z.shiftl (Z.shiftr b 8 mod 2 ^ 8) 8 < 2 ^ 32) by (change (2 ^ (8 + 8)) with (2 ^ 16) in L1; lia).
assert (L0 : 0 <= b mod 2 ^ 8 < 2 ^ 32) by (pose proof (Bm b); lia).
destruct (Uo _ _ _ _ (Ul _ _ 24 (Us 24 ltac:(lia)) ltac:(lia) L3)
  (Ul _ _ 16 (Ue _ _ (Us 16 ltac:(lia))) ltac:(lia) L2') L3 L2') as [UA RA].
destruct (Uo _ _ _ _ (Ul _ _ 8 (Ue _ _ (Us 8 ltac:(lia))) ltac:(lia) L1') (Ue _ _ U0) L1' L0) as [UB RB].
destruct (Uo _ _ _ _ UA UB RA RB) as [UC _]. rewrite UC. apply asm_eq. exact Hb.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* ======================================= small facts ======================================= *)
Lemma k_region0 : forall E ss ms (H : word -> bool) r0, st_ok rsegs E ss (restrict H ms) ->
nth_error (ss_mem ss) 0 = Some r0 -> region_ok rsegs E (mrestrict H (ms_mem ms)) r0.
Proof.
intros E ss ms H r0 HS Hr. pose proof (st_ok_mem_ok rsegs E ss _ HS) as (_ & HF & _). cbn [ms_mem restrict] in HF.
eapply Forall_forall; [exact HF|]. exact (nth_error_In _ _ Hr).
Qed.

Lemma k_fv_val : forall x E (m : word -> option byte) b,
region_ok rsegs E m (frame_region [YP09.mkChunk 8 (CVal 4 asm_sv)]) ->
base_val E (Some 2%nat) = x_F x -> ew E 45 = Z_to_bv 64 b -> 0 <= b < 2 ^ 32 ->
val_mem rsegs m (x_F x + 8) 4 b.
Proof.
intros x E m b HR Hb H45 Hbr. unfold region_ok, frame_region in HR. cbn [YP09.r_base YP09.r_chunks app] in HR.
rewrite Hb in HR. destruct HR as (_ & _ & _ & HC). apply Forall_cons_iff in HC as [HC _].
apply (val_of_chunk_ok rsegs E m (x_F x) 8 4 asm_sv b HC); [rewrite denot_lit_U, (U_asm E b H45 Hbr); reflexivity | cbn; lia | cbn; lia].
Qed.

Lemma srr_at_cut : forall (W : world rsegs) E ss ms md Q, st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
SRr rsegs W (cfg_at rsegs (ss_pc ss) (ms_regs ms) (ms_mem ms) md) Q -> SRr rsegs W (mkCfg ms md) Q.
Proof. intros W E ss ms md Q HS Hrv H. rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv). exact H. Qed.

Lemma k_reg : forall x regs2 L E ss ms (H : word -> bool) (r : bv 5) (n : nat),
st_ok rsegs E ss (restrict H ms) -> sv_eqb (sr_get (ss_regs ss) r) (SOff n 0) = true -> (n < 43)%nat ->
(forall n, (n < 43)%nat -> ew E n = ew (cut_env x regs2 L) n) -> Z.of_nat n = bv_unsigned r ->
getr (ms_regs ms) r = getr regs2 r.
Proof.
intros x regs2 L E ss ms H r n HS Hs Hn HE Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS). rewrite (sv_eqb_denot E _ _ Hs), sv_denot_SOff0, (HE n Hn).
apply cut_env_reg. exact Hr.
Qed.

(* a state's write windows: none, or inside the frame region (atom 2 = F) *)
Definition k_wr_ok (rs : smem) : bool :=
forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
  (obase_eqb (YP09.r_base r) (Some 2%nat) && (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? FRAME))) rs.
Lemma k_kept_step : forall x E rs (H : word -> bool) (m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) -> aview rsegs H m1 a = aview rsegs H (x_memc x) a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) -> k_wr_ok rs = true -> bv_unsigned (ew E 2) = x_F x ->
forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) -> aview rsegs H m2 a = aview rsegs H (x_memc x) a.
Proof.
intros x E rs H m1 m2 K F Hok H2.
apply (kept_run (fun a => x_sp x - T_parse_STK <= a < x_sp x) E rs H (x_memc x) m1 m2 K F).
intros a (r & Hin & Hb). cbv beta. unfold k_wr_ok in Hok. pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hr.
cbv beta in Hr. destruct (YP09.r_whi r <=? YP09.r_wlo r) eqn:Ero; [apply Z.leb_le in Ero; lia|]. cbn [orb] in Hr.
apply andb_prop in Hr as [Hr Hhi]. apply andb_prop in Hr as [Hb2 Hlo]. apply Z.leb_le in Hhi. apply Z.leb_le in Hlo.
destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate Hb2]. cbn [obase_eqb] in Hb2. apply Nat.eqb_eq in Hb2. subst n.
cbn [base_val] in Hb. rewrite H2 in Hb. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia.
Qed.

Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma pre_frm : forall x, pre_ok B x -> YK0o.frm_zero (@fp_csr fx).
Proof. intros x (_ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
Lemma pre_ret : forall x, pre_ok B x -> YK0s.ret_ok (getr (x_regs x) 1).
Proof. intros x ((_ & H & _) & _). exact H. Qed.

(* the env at the entry *)
Lemma k_env : forall x r c ck rv regs2 mem2 md2, K_at B x r c ck rv regs2 mem2 md2 ->
ew (cut_env x regs2 (k_L x c)) 2 = Z_to_bv 64 (x_F x) /\ ew (cut_env x regs2 (k_L x c)) 9 = Z_to_bv 64 (x_P x + c) /\
ew (cut_env x regs2 (k_L x c)) 10 = Z_to_bv 64 rv /\ ew (cut_env x regs2 (k_L x c)) 19 = Z_to_bv 64 SHADOW_OFF /\
ew (cut_env x regs2 (k_L x c)) 43 = Z_to_bv 64 (Spa.u32_at (x_bs x) c) /\
ew (cut_env x regs2 (k_L x c)) 44 = Z_to_bv 64 (Spa.u32_at (x_bs x) (c + 4)) /\
ew (cut_env x regs2 (k_L x c)) 45 = Z_to_bv 64 (Spa.u32_at (x_bs x) (c + 8)).
Proof.
intros x r c ck rv regs2 mem2 md2 ((_ & _ & _ & _ & H2 & _ & _ & H19) & (H9 & _) & _ & H10 & _).
split; [rewrite (cut_env_reg x regs2 (k_L x c) 2 2%bv eq_refl); exact H2|].
split; [rewrite (cut_env_reg x regs2 (k_L x c) 9 9%bv eq_refl); exact H9|].
split; [rewrite (cut_env_reg x regs2 (k_L x c) 10 10%bv eq_refl); exact H10|].
split; [rewrite (cut_env_reg x regs2 (k_L x c) 19 19%bv eq_refl); exact H19|].
split; [exact (cut_env_seg x regs2 (k_L x c) 0)|].
split; [exact (cut_env_seg x regs2 (k_L x c) 1)|].
exact (cut_env_seg x regs2 (k_L x c) 2).
Qed.

(* the pod's bounds at the entry *)
Lemma k_bounds : forall x r c ck rv regs2 mem2 md2, pre_ok B x -> K_at B x r c ck rv regs2 mem2 md2 ->
0 < x_P x /\ x_P x mod 16 = 0 /\ x_P x + x_len x < 2 ^ 47 /\ 16 <= r + 16 <= c /\ c mod 4 = 0 /\
c + 8 + Spa.u32_at (x_bs x) c <= r + 16 + Spa.u32_at (x_bs x) (r + 8) /\
r + 16 + Spa.u32_at (x_bs x) (r + 8) <= x_len x /\
(x_P x + x_len x <= x_F x \/ x_F x + 96 <= x_P x) /\
0x7fff7f800000 <= x_F x /\ x_F x + 96 <= x_sp0 x /\ x_sp0 x <= 2 ^ 47 /\ x_F x mod 16 = 0 /\
x_sp0 x - x_STK x <= x_F x /\ x_F x = x_sp x - 96 /\ T_parse_STK = 8288.
Proof.
intros x r c ck rv regs2 mem2 md2 Hpre (_ & _ & _ & _ & (Hr16 & _ & _ & _ & HrVS) & Hc16 & Hc4 & Hin & _).
pose proof (child_in_facts x r c Hin) as [_ Hc2].
pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & _ & HP63 & _ & _ & _ & HAM & HDJ).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal16 & Hwin).
pose proof (amem_range_bounds (x_P x) (x_len x) ltac:(lia) ltac:(lia) HAM) as Hhm.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HT : T_parse_STK = 8288) by reflexivity.
assert (HF : x_F x = x_sp x - 96) by reflexivity.
rewrite HT in *. rewrite C4 in Hhm. unfold x_len in *. lia.
Qed.

(* ---------------------------------- the entry ---------------------------------- *)
Lemma pod_region_ok : forall x r c ck rv regs2 mem2 md2 big, pre_ok B x -> K_at B x r c ck rv regs2 mem2 md2 ->
(big = true -> 4 <= Spa.u32_at (x_bs x) c) ->
region_ok rsegs (cut_env x regs2 (k_L x c)) (mrestrict (w_H (x_W x)) mem2) (pod_region big).
Proof.
intros x r c ck rv regs2 mem2 md2 big Hpre HK Hbig.
pose proof (k_env x r c ck rv regs2 mem2 md2 HK) as (_ & E9 & _ & _ & E43 & E44 & E45).
pose proof (k_bounds x r c ck rv regs2 mem2 md2 Hpre HK) as (HP0 & _ & Hhm & Hc16 & _ & Hc2 & HrVS & _).
pose proof (pod_at_cut B x regs2 mem2 md2 Hpre (proj1 HK)) as (HG & _ & _).
pose proof (u32_at_range (x_bs x) c) as R0. pose proof (u32_at_range (x_bs x) (c + 4)) as R4.
pose proof (u32_at_range (x_bs x) (c + 8)) as R8.
unfold region_ok, pod_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
assert (Hb9 : base_val (cut_env x regs2 (k_L x c)) (Some 9%nat) = x_P x + c)
by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
rewrite Hb9.
split; [lia|]. split; [destruct big; [specialize (Hbig eq_refl)|]; unfold k_hi; lia|]. split; [intros o Ho; lia|].
assert (C0 : YP09.chunk_ok rsegs (cut_env x regs2 (k_L x c)) (mrestrict (w_H (x_W x)) mem2) (x_P x + c)
  (YP09.mkChunk 0 (CVal 4 (SOff 43 0)))).
{ apply chunk_ok_val with (v := Spa.u32_at (x_bs x) c); [rewrite sv_denot_SOff0; exact E43 | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. apply pod_u32; [exact HG | lia | lia]. }
assert (C4 : YP09.chunk_ok rsegs (cut_env x regs2 (k_L x c)) (mrestrict (w_H (x_W x)) mem2) (x_P x + c)
  (YP09.mkChunk 4 (CVal 4 (SOff 44 0)))).
{ apply chunk_ok_val with (v := Spa.u32_at (x_bs x) (c + 4)); [rewrite sv_denot_SOff0; exact E44 | cbn; lia | cbn; lia |].
  rewrite <- Z.add_assoc. apply pod_u32; [exact HG | lia | lia]. }
destruct big; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; try exact C0; try exact C4.
specialize (Hbig eq_refl).
apply chunk_ok_val with (v := Spa.u32_at (x_bs x) (c + 8)); [rewrite sv_denot_SOff0; exact E45 | cbn; lia | cbn; lia |].
rewrite <- Z.add_assoc. apply pod_u32; [exact HG | lia | lia].
Qed.

Lemma k_entry : forall x r c ck rv regs2 mem2 md2 big, pre_ok B x -> K_at B x r c ck rv regs2 mem2 md2 ->
(4 <=? Spa.u32_at (x_bs x) c) = big ->
st_ok rsegs (cut_env x regs2 (k_L x c)) (ssK big)
  (restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_K) mem2 (seg_rom rsegs))) /\
sh_ok rsegs PBx (shK big) (cut_env x regs2 (k_L x c)) (mrestrict (w_H (x_W x)) mem2).
Proof.
intros x r c ck rv regs2 mem2 md2 big Hpre HK Hbig.
pose proof (k_env x r c ck rv regs2 mem2 md2 HK) as (E2 & E9 & E10 & E19 & E43 & E44 & E45).
pose proof (k_bounds x r c ck rv regs2 mem2 md2 Hpre HK)
  as (HP0 & HP16 & Hhm & Hc16 & Hc4 & Hc2 & HrVS & HDJ & HF0 & HF96 & H47 & HF16 & Hwin & HF & HT).
pose proof HK as (HFI & _ & H24 & _).
pose proof (u32_at_range (x_bs x) c) as R0. pose proof (u32_at_range (x_bs x) (c + 4)) as R4.
pose proof (u32_at_range (x_bs x) (c + 8)) as R8.
assert (Hb : big = true -> 4 <= Spa.u32_at (x_bs x) c) by (intros ->; apply Z.leb_le; exact Hbig).
assert (Hs : big = false -> Spa.u32_at (x_bs x) c < 4) by (intros ->; apply Z.leb_gt; exact Hbig).
assert (U9 : U (cut_env x regs2 (k_L x c)) (SOff 9 0) = x_P x + c) by (apply U_atom; [exact E9 | lia]).
assert (U19 : U (cut_env x regs2 (k_L x c)) PBx = SHADOW_OFF) by (apply U_atom; [exact E19 | unfold SHADOW_OFF; lia]).
split.
- rewrite restrict_mkst_fx. unfold ssK.
  change (cut_env x regs2 (k_L x c)) with (Ereg regs2 (w64 SBr :: saved_vals (x_regs x) ++ k_L x c)).
  apply (entry_st_ok_full rsegs); fold (cut_env x regs2 (k_L x c)).
  + unfold k_regs. apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |].
    rewrite H24. rewrite denot_lit_U. unfold w64. f_equal. unfold s8_sv, s8_val.
    rewrite !U_SAlu, U9. rewrite (U_atom _ 19 SHADOW_OFF E19) by (unfold SHADOW_OFF; lia). rewrite U_SLit. cbn [zalu_raw].
    change (Z.land (zcanon 3) 63) with 3.
    assert (0 <= Z.shiftr (x_P x + c) 3 <= x_P x + c).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
    unfold SHADOW_OFF in *. zc_in. reflexivity.
  + destruct big; vm_compute; reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * exact (frame_region_ok B x regs2 mem2 md2 (k_L x c) [] HFI Hpre (Forall_nil _)).
    * exact (pod_region_ok x r c ck rv regs2 mem2 md2 big Hpre HK Hb).
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, frame_region, pod_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9, !unsigned_lit_small by lia.
    unfold FRAME. split; [split; [|exact I] | split; [exact I | exact I]].
    destruct big; unfold k_hi; [specialize (Hb eq_refl) | specialize (Hs eq_refl)]; lia.
  + unfold facts_ok, k_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E19, E43, E44, E45, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SBr, SHADOW_OFF.
    destruct big; cbn [af_lo af_hi af_al2]; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
    [specialize (Hb eq_refl) | specialize (Hs eq_refl)];
    (repeat split; try lia; try exact I).
- unfold sh_ok, shK. apply Forall_cons; [|apply Forall_nil].
  apply (shent_pod B x regs2 mem2 md2 _ PBx 9 c 0 (k_hi big) Hpre HFI U19 U9); [lia | | destruct big; unfold k_hi; lia].
  destruct big; unfold k_hi; [specialize (Hb eq_refl) | ]; lia.
Qed.

(* ---------------------------------- the leaves ---------------------------------- *)
(* a `ret` from the epilogue with a0 = rcv and nothing stored *)
Lemma k_ret_leaf : forall x regs2 L E ss ms md rcv, pre_ok B x ->
st_ok rsegs E ss (restrict (w_H (x_W x)) ms) -> ss_resv ss = None ->
clookup parse_tbl (ss_pc ss) = Some RET_WORD_r ->
(forall n, (n < 43)%nat -> ew E n = ew (cut_env x regs2 L) n) ->
leaf_sr_ok (ss_regs ss) = true ->
getr regs2 2 = w64 (x_F x) ->
(forall r, r = 3 \/ r = 4 \/ r = 25 \/ r = 26 \/ r = 27 -> getr regs2 (Z_to_bv 5 r) = getr (x_regs x) (Z_to_bv 5 r)) ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
  (x_lyc x) (x_Sc x) (x_W x) (ms_mem ms) md (x_k x) ->
same_io (x_mdc x) md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 aview rsegs (w_H (x_W x)) (ms_mem ms) a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
getr (ms_regs ms) 10 = w64 rcv -> x_res x = (None, rcv) ->
SRr rsegs (x_W x) (mkCfg ms md) (PPOST B MT x false).
Proof.
intros x regs2 L E ss ms md rcv Hpre HS Hrv Hpc HE Hok H2 Hcs HJ Hio KE R10 Hres.
pose proof (leaf_regs B x regs2 L E ss ms (w_H (x_W x)) Hpre HS HE Hok H2 Hcs) as [Hpr Hra].
pose proof (pre_ret x Hpre) as Hret. unfold YK0s.ret_ok in Hret.
apply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx (x_W x) E ss ms md _ HS Hrv Hpc).
intros mat. rewrite Hra, Hret.
apply (ppost_intro B MT MTL x false fx (ms_regs ms) (ms_mem ms)).
- apply (ajournal_materialize rsegs B LAWS parse_segs_low). exact HJ.
- eapply same_io_trans; [exact Hio | apply same_io_wvb].
- exact Hpr.
- apply rl_fxk_refl. exact (pre_frm x Hpre).
- intros a Ha Hn _. exact (KE a Ha Hn).
- change (rl_parse_res false (x_bs x)) with (x_res x). rewrite Hres. exact R10.
- change (rl_parse_res false (x_bs x)) with (x_res x). rewrite Hres. exact I.
Qed.

(* the facts every cut carries, at a continuing leaf *)
Lemma k_FI : forall x regs2 mem2 md2 L E ss ms mdF cs, pre_ok B x -> FI B x regs2 mem2 md2 ->
st_ok rsegs E ss (restrict (w_H (x_W x)) ms) ->
(forall n, (n < 43)%nat -> ew E n = ew (cut_env x regs2 L) n) ->
k_keep_ok (ss_regs ss) = true ->
nth_error (ss_mem ss) 0 = Some (frame_region cs) ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
  (x_lyc x) (x_Sc x) (x_W x) (ms_mem ms) mdF (x_k x) ->
same_io (x_mdc x) mdF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 aview rsegs (w_H (x_W x)) (ms_mem ms) a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
FI B x (ms_regs ms) (ms_mem ms) mdF.
Proof.
intros x regs2 mem2 md2 L E ss ms mdF cs Hpre HFI HS HE Hk Hfr HJ Hio KE.
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal16 & Hwin).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HFI as (_ & _ & _ & _ & H2 & Hcs & H8 & H19).
assert (KR : forall (r : bv 5) n, In (r, n) [((2%bv : bv 5), 2%nat); (Z_to_bv 5 3, 3%nat); (Z_to_bv 5 4, 4%nat);
  ((8%bv : bv 5), 8%nat); ((19%bv : bv 5), 19%nat); (Z_to_bv 5 25, 25%nat); (Z_to_bv 5 26, 26%nat);
  (Z_to_bv 5 27, 27%nat); ((18%bv : bv 5), 18%nat); ((20%bv : bv 5), 20%nat); ((21%bv : bv 5), 21%nat);
  ((22%bv : bv 5), 22%nat); ((23%bv : bv 5), 23%nat)] ->
  Z.of_nat n = bv_unsigned r -> (n < 43)%nat -> getr (ms_regs ms) r = getr regs2 r).
{ intros r n Hin Hr Hn. apply (k_reg x regs2 L E ss ms (w_H (x_W x)) r n HS); [|exact Hn | exact HE | exact Hr].
  unfold k_keep_ok in Hk. exact (proj1 (forallb_forall _ _) Hk (r, n) Hin). }
assert (HR : region_ok rsegs E (mrestrict (w_H (x_W x)) (ms_mem ms)) (frame_region cs))
by exact (k_region0 E ss ms (w_H (x_W x)) _ HS Hfr).
split; [exact HJ|]. split; [exact Hio|]. split; [exact KE|]. split.
- apply (saved_of_frame_region x E _ cs HR).
  + cbn [base_val]. rewrite (HE 2%nat) by lia. rewrite (cut_env_reg x regs2 L 2 2%bv eq_refl), H2. unfold w64.
    apply unsigned_lit_small. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia.
  + intros j Hj. rewrite (HE (33 + j)%nat) by lia. apply cut_env_saved. exact Hj.
- split; [rewrite (KR 2%bv 2%nat) by (first [cbn; tauto | reflexivity | lia]); exact H2|].
  split; [intros r Hr; destruct Hr as [-> | [-> | [-> | [-> | ->]]]];
    (lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
       let n := eval vm_compute in (Z.to_nat k) in
       rewrite (KR (Z_to_bv 5 k) n) by (first [cbn; tauto | reflexivity | lia]) end; apply Hcs; tauto)|].
  split; [rewrite (KR 8%bv 8%nat) by (first [cbn; tauto | reflexivity | lia]); exact H8|].
  rewrite (KR 19%bv 19%nat) by (first [cbn; tauto | reflexivity | lia]); exact H19.
Qed.

(* ---------------------------------- the walk's plumbing ---------------------------------- *)
(* the write windows of a run: the frame region [F, F + 0x60) inside the caller's stack window; the pod is
   read-only *)
Ltac k_awr X B2 :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (x_F X - x_sp0 X));
[ reflexivity | kpeel; rewrite B2; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil] ].
(* the kept bytes across one run: its write windows (k_wr_ok: read-only, or inside the frame region at atom 2) lie in
   the callee's stack [sp - T_parse_STK, sp) *)
Ltac k_keep X B2 :=
match goal with F : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  match goal with K : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
    let K' := fresh "KE" in
    pose proof (k_kept_step X _ _ _ _ _ K F ltac:(vm_compute; reflexivity) ltac:(kpeel; exact B2)) as K';
    clear K F; rename K' into KE end end;
repeat match goal with F : frame_of _ _ _ _ |- _ => clear F end;
repeat match goal with G : mem_grows _ _ |- _ => clear G end;
repeat match goal with J : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progress rewrite wvb_collapse in J end.
(* one engine run (to its next stop, or to the pc stop) with its two obligations *)
Ltac k_run X B2 :=
match goal with HS : st_ok _ _ _ _ |- _ => match goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
match goal with SH : sh_ok _ _ _ _ _ |- _ => aj_run_tok parse_tbl_ok HS HJ SH RTBspan; [k_awr X B2 | k_keep X B2]
end end end.
Ltac k_run_to X B2 stop :=
match goal with HS : st_ok _ _ _ _ |- _ => match goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
match goal with SH : sh_ok _ _ _ _ _ |- _ => aj_run_to_tok parse_tbl_ok HS HJ SH RTBspan stop; [k_awr X B2 | k_keep X B2]
end end end.
(* both sides of the branch the engine stopped at; Hc names its condition *)
Ltac k_branch Hc :=
match goal with HS : st_ok _ _ _ _ |- _ => match goal with SH : sh_ok _ _ _ _ _ |- _ =>
  srr_branch_tok parse_tbl_ok HS SH RTBspan;
  match goal with
  | C : branch_taken _ _ _ = true |- _ => rename C into Hc
  | C : branch_taken _ _ _ = false |- _ => rename C into Hc
  end end end.
(* a register at the stop, as the engine's value *)
Ltac k_reg_of r :=
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ?ms) |- _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
rewrite (st_ok_restrict_reg segs H E ss ms r HS : getr (ms_regs ms) r = sv_denot E e) end.
(* the epilogue's `ret` with a0 = rcv *)
Ltac k_ret X R2 L0 Hpre H2 Hcs Hio0 rcv Hres :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let R10 := fresh "R10" in rreg HS (10%bv : bv 5) R10;
apply (k_ret_leaf X R2 L0 _ _ ms _ rcv Hpre HS eq_refl ltac:(vm_compute; reflexivity)
  ltac:(intros n Hn; kpeel; reflexivity) ltac:(vm_compute; reflexivity) H2 Hcs HJ
  ltac:(eapply same_io_trans; [exact Hio0 | apply same_io_wvb]) KE
  ltac:(rewrite R10; unfold w64; apply Z_to_bv64_eq_mod; reflexivity) Hres)
end.
(* the stop at a cut: the machine state is the cut's configuration *)
Ltac k_at_cut X :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ => apply (srr_at_cut (x_W X) _ _ ms _ _ HS eq_refl) end.
(* the cut's FI from the stop state *)
Ltac k_fi X R2 M2 D2 L0 cs Hpre HFI Hio0 :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
apply (k_FI X R2 M2 D2 L0 _ _ ms _ cs Hpre HFI HS ltac:(intros n Hn; kpeel; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ
  ltac:(eapply same_io_trans; [exact Hio0 | apply same_io_wvb]) KE)
end.
(* a register the run left as at the cut *)
Ltac k_kept X R2 L0 r n :=
lazymatch goal with HS : st_ok _ _ _ (restrict ?H ?ms) |- _ =>
rewrite (k_reg X R2 L0 _ _ ms H r n HS ltac:(vm_compute; reflexivity) ltac:(lia)
  ltac:(intros m Hm; kpeel; reflexivity) eq_refl) end.
Ltac kside := first [kpeel; assumption | lia].

(* ---------------------------------- the segment ---------------------------------- *)
Theorem segK_ok : segK_stmt B MT.
Proof using MTL LAWS.
intros x r c ck rv Hpre HL2 HT HFV regs2 mem2 md2 HK.
unfold L2_ok in HL2. unfold T_ok in HT. unfold FV_ok in HFV.
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
pose proof (k_env x r c ck rv regs2 mem2 md2 HK) as (E2 & E9 & E10 & E19 & E43 & E44 & E45).
pose proof (k_bounds x r c ck rv regs2 mem2 md2 Hpre HK)
  as (HP0 & HP16 & Hhm & Hc16 & Hc4 & Hc2 & HrVS & _ & HF0 & HSP0 & H47 & HF16 & HWIN & HF96 & HT8).
pose proof HK as (HFI & (L9 & L18 & L20 & L21 & L22 & L23) & _ & _ & Hst & _ & _ & Hin & Hkey & Hrv & Hrv0 & HW).
pose proof HFI as (HJ & Hio & KE & _ & H2 & Hcs & _ & _).
pose proof (pre_frm x Hpre) as Hfrm.
pose proof (u32_at_range (x_bs x) c) as RCS. pose proof (u32_at_range (x_bs x) (c + 4)) as RTY.
pose proof (u32_at_range (x_bs x) (c + 8)) as RBV.
pose proof (reac_role_prop_parse.pb_lor7 (Spa.u32_at (x_bs x) c) ltac:(lia)) as (RU1 & RU2 & RU3).
assert (B2 : bv_unsigned (ew (cut_env x regs2 (k_L x c)) 2) = x_F x) by (rewrite E2; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 PC_K) with (Z_to_bv 64 PC_K).
destruct (4 <=? Spa.u32_at (x_bs x) c) eqn:Hbig;
  destruct (k_entry x r c ck rv regs2 mem2 md2 _ Hpre HK Hbig) as [HS SHOK];
  [apply Z.leb_le in Hbig | apply Z.leb_gt in Hbig].
- (* CS >= 4 *)
  (* 0x833bc: stop at beqz a0 *)
  k_run x B2. k_branch Hb1.
  + (* rv = 0: the value read *)
    rewrite (br_rv _ rv) in Hb1 by kside. apply Z.eqb_eq in Hb1.
    pose proof (k_val_model x r c ck rv Hin Hrv0 Hb1 HW) as Hres.
    k_run x B2. k_branch Hb2.
    * (* 0x83448: CS >= 2^20, 0x83594 ret -1 *)
      rewrite (br_big _ (Spa.u32_at (x_bs x) c)) in Hb2 by kside. apply negb_true_iff, Z.ltb_ge in Hb2.
      assert (Hres' : x_res x = (None, -1)) by (rewrite Hres; apply reac_role_prop_parse.pc_res_big; lia).
      k_run x B2. k_ret x regs2 (k_L x c) Hpre H2 Hcs Hio (-1) Hres'.
    * rewrite (br_big _ (Spa.u32_at (x_bs x) c)) in Hb2 by kside. apply negb_false_iff, Z.ltb_lt in Hb2.
      k_run x B2. k_branch Hb3.
      -- (* 0x83470: type <> 4 *)
         rewrite (br_ty _ (Spa.u32_at (x_bs x) (c + 4)) 4) in Hb3 by kside. apply negb_true_iff, Z.eqb_neq in Hb3.
         k_run x B2. k_branch Hb4.
         ++ (* 0x834cc: type <> 6, 0x83594 ret -1 *)
            rewrite (br_ty _ (Spa.u32_at (x_bs x) (c + 4)) 6) in Hb4 by kside. apply negb_true_iff, Z.eqb_neq in Hb4.
            assert (Hres' : x_res x = (None, -1))
            by (rewrite Hres; apply reac_role_prop_parse.pc_res_bad; [lia | right; split; lia]).
            k_run x B2. k_ret x regs2 (k_L x c) Hpre H2 Hcs Hio (-1) Hres'.
         ++ (* type 6: the Float path to FV *)
            rewrite (br_ty _ (Spa.u32_at (x_bs x) (c + 4)) 6) in Hb4 by kside. apply negb_false_iff, Z.eqb_eq in Hb4.
            k_run_to x B2 PC_FV. k_at_cut x.
            apply (HFV (Spa.u32_at (x_bs x) (c + 8))).
            split; [k_fi x regs2 mem2 md2 (k_L x c) [YP09.mkChunk 8 (CVal 4 asm_sv)] Hpre HFI Hio|].
            split.
            { lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
              apply (k_fv_val x _ _ _ (k_region0 _ _ ms (w_H (x_W x)) (frame_region [YP09.mkChunk 8 (CVal 4 asm_sv)])
                HS ltac:(vm_compute; reflexivity))); [cbn [base_val]; kpeel; exact B2 | kpeel; exact E45 | lia] end. }
            split; [k_reg_of (12%bv : bv 5); reflexivity|].
            split; [lia|].
            rewrite Hres. apply reac_role_prop_parse.pc_res_flt; lia.
      -- (* type 4: the Int path to T *)
         rewrite (br_ty _ (Spa.u32_at (x_bs x) (c + 4)) 4) in Hb3 by kside. apply negb_false_iff, Z.eqb_eq in Hb3.
         k_run_to x B2 PC_T. k_at_cut x.
         apply (HT (Accessors.s32 (Spa.u32_at (x_bs x) (c + 8))) fx).
         split; [k_fi x regs2 mem2 md2 (k_L x c) (@nil YP09.chunk) Hpre HFI Hio|].
         split; [k_reg_of (11%bv : bv 5); apply a0_int; [kpeel; exact E45 | lia]|].
         split; [apply Accessors.s32_range; lia|].
         split; [apply rl_fxk_refl; exact Hfrm|].
         rewrite Hres. apply reac_role_prop_parse.pc_res_int; lia.
  + (* rv <> 0: the next child *)
    rewrite (br_rv _ rv) in Hb1 by kside. apply Z.eqb_neq in Hb1.
    pose proof (k_next_model x r c ck rv ltac:(lia) Hin Hkey Hrv0 Hb1 HW) as Hres.
    k_run x B2. k_branch Hb2.
    * rewrite (br_align _ (x_P x + c) (Spa.u32_at (x_bs x) c)) in Hb2 by kside. discriminate Hb2.
    * k_run_to x B2 PC_L2. k_at_cut x.
      apply (HL2 (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c)) None ltac:(lia)).
      split; [k_fi x regs2 mem2 md2 (k_L x c) (@nil YP09.chunk) Hpre HFI Hio|].
      split.
      { split; [|split; [|split; [|split; [|split]]]].
        - k_reg_of (9%bv : bv 5). rewrite denot_lit_U, (U_s1n _ (x_P x + c) (Spa.u32_at (x_bs x) c)) by kside.
          unfold w64. f_equal. lia.
        - k_kept x regs2 (k_L x c) (18%bv : bv 5) 18%nat. exact L18.
        - k_kept x regs2 (k_L x c) (20%bv : bv 5) 20%nat. exact L20.
        - k_kept x regs2 (k_L x c) (21%bv : bv 5) 21%nat. exact L21.
        - k_kept x regs2 (k_L x c) (22%bv : bv 5) 22%nat. exact L22.
        - k_kept x regs2 (k_L x c) (23%bv : bv 5) 23%nat. exact L23. }
      split; [k_reg_of (11%bv : bv 5); reflexivity|].
      split; [exact Hst|]. split; [lia|]. split; [lia|]. split; [intros ck' Hck; discriminate Hck|].
      exact Hres.
- (* CS < 4 *)
  k_run x B2. k_branch Hb1.
  + (* rv = 0: CS < 4, ret -1 *)
    rewrite (br_rv _ rv) in Hb1 by kside. apply Z.eqb_eq in Hb1.
    pose proof (k_val_model x r c ck rv Hin Hrv0 Hb1 HW) as Hres.
    k_run x B2. k_branch Hb2.
    * rewrite (br_big _ (Spa.u32_at (x_bs x) c)) in Hb2 by kside. apply negb_true_iff, Z.ltb_ge in Hb2. lia.
    * rewrite (br_big _ (Spa.u32_at (x_bs x) c)) in Hb2 by kside. apply negb_false_iff, Z.ltb_lt in Hb2.
      assert (Hres' : x_res x = (None, -1))
      by (rewrite Hres; apply reac_role_prop_parse.pc_res_bad; [lia | left; lia]).
      k_run x B2. k_ret x regs2 (k_L x c) Hpre H2 Hcs Hio (-1) Hres'.
  + (* rv <> 0: the next child *)
    rewrite (br_rv _ rv) in Hb1 by kside. apply Z.eqb_neq in Hb1.
    pose proof (k_next_model x r c ck rv ltac:(lia) Hin Hkey Hrv0 Hb1 HW) as Hres.
    k_run x B2. k_branch Hb2.
    * rewrite (br_align _ (x_P x + c) (Spa.u32_at (x_bs x) c)) in Hb2 by kside. discriminate Hb2.
    * k_run_to x B2 PC_L2. k_at_cut x.
      apply (HL2 (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c)) None ltac:(lia)).
      split; [k_fi x regs2 mem2 md2 (k_L x c) (@nil YP09.chunk) Hpre HFI Hio|].
      split.
      { split; [|split; [|split; [|split; [|split]]]].
        - k_reg_of (9%bv : bv 5). rewrite denot_lit_U, (U_s1n _ (x_P x + c) (Spa.u32_at (x_bs x) c)) by kside.
          unfold w64. f_equal. lia.
        - k_kept x regs2 (k_L x c) (18%bv : bv 5) 18%nat. exact L18.
        - k_kept x regs2 (k_L x c) (20%bv : bv 5) 20%nat. exact L20.
        - k_kept x regs2 (k_L x c) (21%bv : bv 5) 21%nat. exact L21.
        - k_kept x regs2 (k_L x c) (22%bv : bv 5) 22%nat. exact L22.
        - k_kept x regs2 (k_L x c) (23%bv : bv 5) 23%nat. exact L23. }
      split; [k_reg_of (11%bv : bv 5); reflexivity|].
      split; [exact Hst|]. split; [lia|]. split; [lia|]. split; [intros ck' Hck; discriminate Hck|].
      exact Hres.
Qed.

End b.
