(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* lib/B/W_traps.v: the image-B trap-refutation kit of fuzz_reply.asan-ubsan.  Proves no function (kind: segment
   lemma): every lemma here is bit-vector arithmetic over the symbolic engine's values; no image, no address.

   UBSan in this pin is TRAP mode (no __ubsan_handle_* symbol in either image's nm): every check is an inline branch
   to an `unimp`.  A B walk that runs the engine (W_kit's psrr_branch_tok, W_frame's psrr_branch_pi; both apply
   W_kit's paj_branch) stops at such a branch only when the runner cannot decide it, and on the trap edge it holds
     Hc : branch_taken c (sv_denot E a) (sv_denot E b) = true.
   Each trap_* closer concludes  branch_taken c (sv_denot E a) (sv_denot E b) = false, so the walk closes the edge with
     rewrite (trap_<shape> E ...) in Hc; discriminate.
   Premises are values in YP0e.U (unsigned) / YP0e.Sg (signed), which YI04's U_atom / U_atom_off / U_lit give from
   `ew E n = Z_to_bv 64 v`, and the walk's own bound facts (lia closes the arithmetic premise from them).  In
   a Theorem Labs lane's lemmas they come in the order: the base, then the pointer or index, then the bounds.  BTrapKit's
   lemmas take the branch's operands in the branch's order (rs1, then rs2), then the bounds, so trap_ptr_wrap_atom's
   call is gsl_wrap's call.  Each premise set is the weakest that refutes its trap for the values a walk holds
   (int32 shapes: for a sign-extended int32 operand).

   Two layers, one kit: the code from the first Require through trap_dbl_guard is a Theorem Labs lane's kit
   (a working branch 73bb5b07501 / c7bdec020ef, byte for byte, 32 lemmas; its 50 sites in
   TRAPS-CENSUS.md (sha256 b33c2b52103e; internal record));
   the section after it is BTrapKit's (the WRAP family, trap_seat, the seat values).  Where a cut keeps a computed
   check result in an atom, or the engine folded part of a check with the state's facts, the trap_U_* / trap_S_*
   value lemmas give that result's value, and trap_nonnull (beqz) / trap_bnez_zero (bnez) close the branch on it.

   MEASURED (a Theorem Labs lane W4, a working branch 9f0cd2ef50e): gestures_end has 10 trap edges and gesture_model
   6; in EACH function the runner decided every trap edge but ONE, from the seat's atom facts, and the one left was a
   pointer-overflow WRAP (gestures_end 0x826a4 `bltu held+8i, held`, lib/B/W_gse_loop.v gsl_wrap; gesture_model
   0x8612c `bltu ~LINE, js+1`, lib/B/W_gm_found.v).  W8Add's check_bounded (a working branch
   7e062bb9b9c): the same, once the one-time flags sat in the loop-head facts.  So: seat the facts below, and cite the
   WRAP family for what is left.

   THE SEAT RECIPE (YP0m.facts: f_atoms / f_conds / f_alias of the cut's sstate):
   R1 every pointer atom gets  mkAF 4096 140737479966720 3  (lo >= 1: `beqz p`, snez / seqz and the null-consistency
      xor / beq are decided; al2 3: `andi p,7; bnez` is decided; hi = the ASan user ceiling: the constant wraps
      `bgeu 1,p+1`, `li t,-k; bgeu p,t`, `beq p,-k`, `bltu p,k+1` are decided by ranges).  An int* (the result of
      __errno_location) needs al2 2 for `andi p,3; bnez`.  A 16-byte block start may carry al2 4.
   R2 a derived pointer base + off (held + 8i, P + 56i, line + js) gets ITS OWN atom with R1's fact, and both sum
      orders go in f_alias: (SAlu ALU_ADD (SOff b 0) (SOff o 0), SOff p 0) and (SAlu ALU_ADD (SOff o 0) (SOff b 0),
      SOff p 0); the offset atom gets al2 3 when the element is 8 bytes.  Then the derived pointer's null, alignment
      and null-consistency checks are decided (W4 gsl_facts: atoms 32 = held, 33 = held + 8i, 21 = 8i).
   R3 one-time flags computed once before a loop (snez base; andi 7 / seqz / and) sit as  mkAF 1 1 0  atoms; their
      values at the seat are trap_w_snez / trap_w_base_ok (W8: a4 and a6, so `beqz a6` 0x856fc was decided).
      A negated value held across a loop (~LINE, -len) sits as an atom too: trap_w_not gives ~P; with -len's range
      [2^64 - max, 2^64 - min] the neg wrap `bltu -len, LINE` is decided (W4 gesture_model 0x860e0).
   R4 int32 values (counts, indices) get an int32-safe range (e.g. mkAF 0 (2^26) 0), also when they come from a
      memory chunk (make the chunk's value an atom): YP0e.s_aluw3 then turns addiw / addw / subw into the 64-bit op
      and the same-atom compare decides the int32 traps [from the engine's code (aluw_is_alu, decide_lts); not yet
      measured on a B walk].  Otherwise cite trap_addw1 / trap_decw / trap_decw_sext / trap_subw / trap_dbl_guard.
   R5 the runner CANNOT decide an unsigned compare of two different atoms whose ranges overlap: the WRAP check
      `bltu p,base` with a symbolic offset, `not base; bltu ~base,off`, and the `sltu` inside the signed-index check.
      Cite trap_ptr_wrap_atom / trap_ptr_bltu / trap_ptr_wrap_not / trap_ptr_sovf at the first copy; the runner keeps
      the branch condition in f_conds, so a later copy in the same run is decided (W4 0x826f0).  In a loop, seat the
      no-wrap condition once: trap_seat (trap_ptr_wrap_atom ...) : acond_ok E (mkAC BC_GEU p base) discharges the
      seat's conds_ok, and every pass is decided.  A trap on the NOT-TAKEN edge (check_shape_ends 0x85a0c,
      drain 0x839e0) is refuted by trap_seat of the opposite closer.

   CENSUS (all 28 functions of the program text 0x82344-0x86794, from fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) of the pinned
   asan-ubsan ELF sha256 10ffb5f9...; every conditional branch to an `unimp` plus the two whose not-taken edge reaches
   one; full table with each branch's slice: TRAPS-ALL.md (sha256 c90982171c9b; internal record); check_bounded,
   list_find, next_line, list_drop, list_push, list_free and source_reset agree with TRAPS-CENSUS.md (sha256 b33c2b52103e; internal record)):
     drain 49, LLVMFuzzerTestOneInput 32, relay_instance_gone 24, list_push 19, check_shape_ends 18, relay_remove 14,
     list_drop 14, send_line 11, gestures_end 10, relay_finish 7, relay_add 6, check_no_loss 6, gesture_model 6,
     next_line 5, list_find 5, check_bounded 3, relay_source 3, relay_reads 3, op_add 2, source_reset 2,
     check_no_loss_read 2, list_free 2, wake 1; none in relay_event, check_shape_done, gesture_end, check_shape_event,
     has_prefix.  Total 244.

   shape (count)             instructions                     cited lemma (R = runner decides after the recipe)
                                                                                                 example site
   NON-NULL (56)             beqz v                           R1; trap_nonnull                  gestures_end 0x82644
   ALIGN8 (50)               andi r,x,7; bnez r               R1 / R2; trap_align8              gestures_end 0x8264c
   WRAP bltu (32)            bltu p,base (p = base + off)     trap_ptr_wrap_atom / trap_ptr_bltu  gestures_end 0x826a4
   NULL-CONS xor (27)        snez; seqz; xor; beqz            R1 / R2; trap_null_xor / trap_null_xor_folded
                                                                                                 check_bounded 0x856f8
   NULL-CONS beq (13)        snez; seqz; beq                  R1 / R2; trap_null_beq            list_drop 0x85bb0
   WRAP signed index (11)    slti; sltu; xor; xori 1; beqz    trap_ptr_sovf + trap_U_sltu_ge    list_drop 0x85bc4
   WRAP p+1 (9)              addi t,p,1; bgeu one,t           R1; trap_ptr_inc                  LLVMFuzzerTestOneInput 0x845e8
   INT32 +1 (7)              addiw t,s,1; blt t,s             R4; trap_addw1                    list_drop 0x85c1c
   INT32 -1 (7)              addiw t,x,-1; bge t,x            R4; trap_decw                     list_free 0x866d4
   ALIGN4 (5)                andi r,x,3; bnez r               R1 (al2 2); trap_align4           send_line 0x82930
   WRAP not (5)              not t,base; bltu t,off           R3; trap_ptr_wrap_not             gesture_model 0x8612c
   BASE ALIGNED+NON-NULL (4) andi 7; seqz; snez; and; beqz    R3; trap_base_ok / trap_w_base_ok check_bounded 0x856fc
   WRAP const (2)            li t,-k; bgeu p,t                R1; trap_ptr_wrap_k               gesture_model 0x860a0
   WRAP p+k = 0 (2)          li t,-k; beq p,t                 R1; trap_br_eq (wake 0x82570: two literals)
                                                                                                 drain 0x83a64
   INT32 doubling (2)        lui t,0x40000; addw; bltz        R4; trap_dbl_guard                list_push 0x853bc
   INT32 +k / add (2)        addiw t,s,100; blt / addw; add; bne
                                                              R4; trap_br_lt / trap_br_ne       op_add 0x85244
   literal (2)               li r,1; beqz r                   decided, no stop                  send_line 0x82988
   WRAP p-k (1)              bltu p,k+1                       R1; trap_ptr_bltu                 check_shape_ends 0x859b4
   WRAP p+1 = 0, ft (1)      li t,-1; bne p,t; j unimp        R1; trap_seat (trap_br_eq ...)    drain 0x839e0
   WRAP neg (1)              neg t,off; bltu t,base           R3; trap_ptr_wrap_neg             gesture_model 0x860e0
   INT32 == INT_MAX (1)      beq i,0x7fffffff                 R4; trap_br_eq                    relay_instance_gone 0x830ec
   INT32 sub (1)             sub; subw; bne                   R4; trap_subw                     list_drop 0x85c64
   INT32 -1 sext (1)         sext.w; addiw -1; bge            R4; trap_decw_sext                list_drop 0x85c70
   INT32 -1, ft (1)          addiw t,x,-1; blt t,x; unimp     R4; trap_seat (trap_decw ...)     check_shape_ends 0x85a0c
   ALIGN8 pair (1)           or; andi 7; bnez                 R2; trap_align8_pair              list_drop 0x85c84

   Strings in image B: `.str.N` labels MOVE between the images (A's .str.8 is "%s %d ", B's is "end"), so match
   string objects by CONTENT, never by label. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- The branch conditions in the U / Sg vocabulary. *)
Lemma trap_br_eq : forall E a b, branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (U E a =? U E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_eqb, U. reflexivity. Qed.
Lemma trap_br_ne : forall E a b, branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (U E a =? U E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_eqb, U. reflexivity. Qed.
Lemma trap_br_ltu : forall E a b, branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_ltu, U. reflexivity. Qed.
Lemma trap_br_lt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. rewrite bv_lts_signed. reflexivity. Qed.
Lemma trap_br_ge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. rewrite bv_lts_signed. reflexivity. Qed.

(* ---- Wrap helpers. *)
Lemma trap_swrap32 : forall a b, a mod 2 ^ 32 = b mod 2 ^ 32 -> bv_swrap 32 a = bv_swrap 32 b.
Proof.
intros a b H. rewrite <- (bv_swrap_wrap 32 a), <- (bv_swrap_wrap 32 b).
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite H. reflexivity.
Qed.
Lemma trap_swrap64 : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> bv_swrap 64 a = bv_swrap 64 b.
Proof.
intros a b H. rewrite <- (bv_swrap_wrap 64 a), <- (bv_swrap_wrap 64 b).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite H. reflexivity.
Qed.
Lemma trap_mod32_of_S : forall E v j, Sg E v = j -> U E v mod 2 ^ 32 = j mod 2 ^ 32.
Proof.
intros E v j Hv. rewrite U_of_S, Hv. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
Qed.

(* ---- Value lemmas: what a check instruction computes, from its operands' values. *)
(* andi r,a,7 *)
Lemma trap_U_andi7 : forall E a x, U E a = x -> U E (SAlu ALU_AND a (SLit 7)) = x mod 8.
Proof.
intros E a x Ha. rewrite U_SAlu, U_SLit, Ha. cbn [zalu_raw].
rewrite (zcanon_id 7) by (unfold M64; lia).
assert (H7 : Z.land x 7 = x mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
rewrite H7. apply zcanon_id. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). unfold M64. lia.
Qed.
(* snez r,b  (sltu r,x0,b) *)
Lemma trap_U_snez : forall E b y, U E b = y -> y <> 0 -> U E (SAlu ALU_SLTU (SLit 0) b) = 1.
Proof.
intros E b y Hb Hy. pose proof (U_range E b) as R. rewrite Hb in R.
rewrite U_SAlu, U_SLit, Hb. cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia).
destruct (0 <? y) eqn:E1; [reflexivity | apply Z.ltb_ge in E1; lia].
Qed.
(* seqz r,p  (sltiu r,p,1) *)
Lemma trap_U_seqz : forall E p x, U E p = x -> x <> 0 -> U E (SAlu ALU_SLTU p (SLit 1)) = 0.
Proof.
intros E p x Hp Hx. pose proof (U_range E p) as R. rewrite Hp in R.
rewrite U_SAlu, U_SLit, Hp. cbn [zalu_raw]. rewrite (zcanon_id 1) by (unfold M64; lia).
destruct (x <? 1) eqn:E1; [apply Z.ltb_lt in E1; lia | reflexivity].
Qed.
Lemma trap_U_seqz0 : forall E p, U E p = 0 -> U E (SAlu ALU_SLTU p (SLit 1)) = 1.
Proof. intros E p Hp. rewrite U_SAlu, U_SLit, Hp. reflexivity. Qed.
(* add p,b,o with no unsigned wrap *)
Lemma trap_U_add : forall E b o y z, U E b = y -> U E o = z -> y + z < 2 ^ 64 -> U E (SAlu ALU_ADD b o) = y + z.
Proof.
intros E b o y z Hb Ho Hyz. pose proof (U_range E b) as Rb. pose proof (U_range E o) as Ro.
rewrite Hb in Rb. rewrite Ho in Ro.
rewrite U_SAlu, Hb, Ho. cbn [zalu_raw]. apply zcanon_id. unfold M64 in *. lia.
Qed.
(* sltu d,p,o where p is not below o (o: the base, or the offset of p = base + offset) *)
Lemma trap_U_sltu_ge : forall E o p z x, U E o = z -> U E p = x -> z <= x -> U E (SAlu ALU_SLTU p o) = 0.
Proof.
intros E o p z x Ho Hp Hzx. rewrite U_SAlu, Ho, Hp. cbn [zalu_raw].
destruct (x <? z) eqn:E1; [apply Z.ltb_lt in E1; lia | reflexivity].
Qed.
(* slti c,i,0 of a non-negative index *)
Lemma trap_U_sltz : forall E i j, Sg E i = j -> 0 <= j -> U E (SAlu ALU_SLT i (SLit 0)) = 0.
Proof.
intros E i j Hi Hj. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite <- (S_of_U E i), Hi.
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite (swrap64_id 0) by (unfold half64; lia).
destruct (j <? 0) eqn:E1; [apply Z.ltb_lt in E1; lia | reflexivity].
Qed.
(* sub r,a,b with no signed 64-bit overflow *)
Lemma trap_S_sub : forall E a b x y, Sg E a = x -> Sg E b = y -> - 2 ^ 63 <= x - y < 2 ^ 63 ->
Sg E (SAlu ALU_SUB a b) = x - y.
Proof.
intros E a b x y Ha Hb Hxy. rewrite S_SAlu. cbn [zalu_raw]. rewrite (U_of_S E a), (U_of_S E b), Ha, Hb.
rewrite (trap_swrap64 _ (x - y)).
- apply swrap64_id. unfold half64. lia.
- unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). symmetry. apply Zminus_mod.
Qed.
(* xor (snez b) (seqz p): 1 exactly when b and p are both null or both not *)
Lemma trap_U_null_xor : forall E b p y x, U E b = y -> U E p = x -> (y = 0 <-> x = 0) ->
U E (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) b) (SAlu ALU_SLTU p (SLit 1))) = 1.
Proof.
intros E b p y x Hb Hp Hyx. pose proof (U_range E b) as Rb. pose proof (U_range E p) as Rp.
rewrite Hb in Rb. rewrite Hp in Rp.
rewrite !U_SAlu, !U_SLit, Hb, Hp. cbn [zalu_raw].
rewrite (zcanon_id 0), (zcanon_id 1) by (unfold M64; lia).
destruct (0 <? y) eqn:E1; destruct (x <? 1) eqn:E2;
[apply Z.ltb_lt in E1, E2 | apply Z.ltb_lt in E1; apply Z.ltb_ge in E2
| apply Z.ltb_ge in E1; apply Z.ltb_lt in E2 | apply Z.ltb_ge in E1, E2];
first [reflexivity | exfalso; unfold M64 in *; lia].
Qed.
(* and (seqz (andi b 7)) (snez b): 1 exactly when b is 8-aligned and not null *)
Lemma trap_U_base_ok : forall E b y, U E b = y -> y mod 8 = 0 -> y <> 0 ->
U E (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND b (SLit 7)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) b)) = 1.
Proof.
intros E b y Hb H8 H0. rewrite U_SAlu. cbn [zalu_raw].
rewrite (trap_U_seqz0 E _ (eq_trans (trap_U_andi7 E b y Hb) H8)), (trap_U_snez E b y Hb H0).
reflexivity.
Qed.

(* ---- Branch closers on a computed value. *)
(* beqz v -> unimp, v not null (also: any beqz on a value the walk knows is not 0) *)
Lemma trap_nonnull : forall E b y, U E b = y -> y <> 0 ->
branch_taken BC_EQ (sv_denot E b) (sv_denot E (SLit 0)) = false.
Proof.
intros E b y Hb Hy. rewrite trap_br_eq, Hb, U_SLit, (zcanon_id 0) by (unfold M64; lia).
apply Z.eqb_neq. exact Hy.
Qed.
(* bnez c -> unimp, on a value the walk knows is 0 *)
Lemma trap_bnez_zero : forall E c, U E c = 0 ->
branch_taken BC_NE (sv_denot E c) (sv_denot E (SLit 0)) = false.
Proof. intros E c Hc. rewrite trap_br_ne, Hc, U_SLit. reflexivity. Qed.

(* ---- The trap shapes. *)
(* ALIGN8: andi r,a,7; bnez r -> unimp. *)
Lemma trap_align8 : forall E a x, U E a = x -> x mod 8 = 0 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND a (SLit 7))) (sv_denot E (SLit 0)) = false.
Proof. intros E a x Ha Hx. rewrite trap_br_ne, (trap_U_andi7 E a x Ha), U_SLit, Hx. reflexivity. Qed.
(* ALIGN8 of a pair: or t,a,b; andi t,t,7; bnez t -> unimp. *)
Lemma trap_align8_pair : forall E a b x y, U E a = x -> U E b = y -> x mod 8 = 0 -> y mod 8 = 0 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SAlu ALU_OR a b) (SLit 7))) (sv_denot E (SLit 0)) = false.
Proof.
intros E a b x y Ha Hb Hx Hy.
apply (trap_align8 E (SAlu ALU_OR a b) (U E (SAlu ALU_OR a b)) eq_refl).
rewrite U_SAlu, Ha, Hb. cbn [zalu_raw]. unfold zcanon, M64.
rewrite Z.mod_mod_divide by (exists (2 ^ 61); reflexivity).
change 8 with (2 ^ 3). rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
change (2 ^ 3) with 8. rewrite Hx, Hy. reflexivity.
Qed.
(* POINTER OVERFLOW: bltu p,base -> unimp, p = base + offset with no wrap (e.g. y = P, x = P + 56 i). *)
Lemma trap_ptr_bltu : forall E b p y x, U E b = y -> U E p = x -> y <= x ->
branch_taken BC_LTU (sv_denot E p) (sv_denot E b) = false.
Proof. intros E b p y x Hb Hp Hyx. rewrite trap_br_ltu, Hp, Hb. apply Z.ltb_ge. lia. Qed.
(* NULL CONSISTENCY: snez s,base; seqz c,p; xor c,s,c; beqz c -> unimp. *)
Lemma trap_null_xor : forall E b p y x, U E b = y -> U E p = x -> (y = 0 <-> x = 0) ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) b) (SAlu ALU_SLTU p (SLit 1))))
(sv_denot E (SLit 0)) = false.
Proof. intros E b p y x Hb Hp Hyx. exact (trap_nonnull E _ 1 (trap_U_null_xor E b p y x Hb Hp Hyx) ltac:(lia)). Qed.
(* NULL CONSISTENCY, beq form: snez s,base; seqz c,p; beq s,c -> unimp. *)
Lemma trap_null_beq : forall E b p y x, U E b = y -> U E p = x -> (y = 0 <-> x = 0) ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_SLTU (SLit 0) b)) (sv_denot E (SAlu ALU_SLTU p (SLit 1))) = false.
Proof.
intros E b p y x Hb Hp Hyx. pose proof (U_range E b) as Rb. pose proof (U_range E p) as Rp.
rewrite Hb in Rb. rewrite Hp in Rp.
rewrite trap_br_eq, !U_SAlu, !U_SLit, Hb, Hp. cbn [zalu_raw].
rewrite (zcanon_id 0), (zcanon_id 1) by (unfold M64; lia).
destruct (0 <? y) eqn:E1; destruct (x <? 1) eqn:E2;
[apply Z.ltb_lt in E1, E2 | apply Z.ltb_lt in E1; apply Z.ltb_ge in E2
| apply Z.ltb_ge in E1; apply Z.ltb_lt in E2 | apply Z.ltb_ge in E1, E2];
first [reflexivity | exfalso; unfold M64 in *; lia].
Qed.
(* BASE ALIGNED AND NOT NULL: andi t,b,7; seqz t,t; snez s,b; and a,t,s; beqz a -> unimp. *)
Lemma trap_base_ok : forall E b y, U E b = y -> y mod 8 = 0 -> y <> 0 ->
branch_taken BC_EQ
(sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND b (SLit 7)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) b)))
(sv_denot E (SLit 0)) = false.
Proof. intros E b y Hb H8 H0. exact (trap_nonnull E _ 1 (trap_U_base_ok E b y Hb H8 H0) ltac:(lia)). Qed.
(* POINTER OVERFLOW, signed index: slti s,i,0; sltu c,p,o; xor (either order); xori 1; beqz -> unimp.
   s and c are the two compares' values; the walk gives both as 0 by trap_U_sltz (0 <= i) and trap_U_sltu_ge
   (p = base + offset with no wrap, o the base or the offset). *)
Lemma trap_ptr_sovf : forall E s c v, U E s = v -> U E c = v ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_XOR (SAlu ALU_XOR s c) (SLit 1))) (sv_denot E (SLit 0)) = false.
Proof.
intros E s c v Hs Hc. apply (trap_nonnull E _ 1); [|lia].
rewrite U_SAlu, U_SAlu, Hs, Hc, U_SLit. cbn [zalu_raw]. rewrite Z.lxor_nilpotent. reflexivity.
Qed.
(* INT32 +1 OVERFLOW: addiw t,s,1; blt t,s -> unimp. *)
Lemma trap_addw1 : forall E s j, Sg E s = j -> - 2 ^ 31 <= j < 2 ^ 31 - 1 ->
branch_taken BC_LT (sv_denot E (SAluw ALU_ADD s (SLit 1))) (sv_denot E s) = false.
Proof.
intros E s j Hs Hj. rewrite trap_br_lt, S_SAluw, Hs, U_SLit. cbn [zalu_raw].
rewrite (trap_mod32_of_S E s j Hs). rewrite (zcanon_id 1) by (unfold M64; lia).
rewrite (trap_swrap32 _ (j + 1)).
- rewrite swrap32_id by lia. apply Z.ltb_ge. lia.
- rewrite (Z.mod_small 1 (2 ^ 32)) by lia. apply Z.add_mod_idemp_l. lia.
Qed.
(* INT32 SUB OVERFLOW: sub a,n,i; subw b,n,i; bne b,a -> unimp. *)
Lemma trap_subw : forall E n i a b, Sg E n = a -> Sg E i = b -> - 2 ^ 31 <= a - b < 2 ^ 31 ->
branch_taken BC_NE (sv_denot E (SAluw ALU_SUB n i)) (sv_denot E (SAlu ALU_SUB n i)) = false.
Proof.
intros E n i a b Hn Hi Hab.
assert (Hw : Sg E (SAluw ALU_SUB n i) = a - b).
{ rewrite S_SAluw. cbn [zalu_raw]. rewrite (trap_mod32_of_S E n a Hn), (trap_mod32_of_S E i b Hi).
  rewrite (trap_swrap32 _ (a - b)); [apply swrap32_id; lia|]. symmetry. apply Zminus_mod. }
assert (Hd : Sg E (SAlu ALU_SUB n i) = a - b) by (apply (trap_S_sub E n i a b Hn Hi); lia).
rewrite trap_br_ne, (U_of_S E (SAluw ALU_SUB n i)), (U_of_S E (SAlu ALU_SUB n i)), Hw, Hd, Z.eqb_refl.
reflexivity.
Qed.
(* INT32 -1 OVERFLOW on a sign-extended int32: addiw t,x,-1; bge t,x -> unimp. *)
Lemma trap_decw : forall E x j, Sg E x = j -> - 2 ^ 31 < j < 2 ^ 31 ->
branch_taken BC_GE (sv_denot E (SAluw ALU_ADD x (SLit (-1)))) (sv_denot E x) = false.
Proof.
intros E x j Hx Hj. rewrite trap_br_ge, S_SAluw, Hx, U_SLit. cbn [zalu_raw].
rewrite (trap_mod32_of_S E x j Hx).
rewrite (trap_swrap32 _ (j - 1)).
- rewrite swrap32_id by lia. replace (j - 1 <? j) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- change (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1). rewrite Z.add_mod_idemp_l by lia.
  replace (j + (2 ^ 32 - 1)) with (j - 1 + 1 * 2 ^ 32) by lia. apply Z_mod_plus_full.
Qed.
(* INT32 -1 OVERFLOW on the low word of a 64-bit value: sext.w s,x; addiw t,x,-1; bge t,s -> unimp. *)
Lemma trap_decw_sext : forall E x j, Sg E x = j -> - 2 ^ 31 < j < 2 ^ 31 ->
branch_taken BC_GE (sv_denot E (SAluw ALU_ADD x (SLit (-1)))) (sv_denot E (SAluw ALU_ADD x (SLit 0))) = false.
Proof.
intros E x j Hx Hj.
assert (Hm : Sg E (SAluw ALU_ADD x (SLit (-1))) = j - 1).
{ rewrite S_SAluw, U_SLit. cbn [zalu_raw]. rewrite (trap_mod32_of_S E x j Hx).
  rewrite (trap_swrap32 _ (j - 1)); [apply swrap32_id; lia|].
  change (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1). rewrite Z.add_mod_idemp_l by lia.
  replace (j + (2 ^ 32 - 1)) with (j - 1 + 1 * 2 ^ 32) by lia. apply Z_mod_plus_full. }
assert (H0 : Sg E (SAluw ALU_ADD x (SLit 0)) = j).
{ rewrite S_SAluw, U_SLit. cbn [zalu_raw]. rewrite (trap_mod32_of_S E x j Hx).
  rewrite (trap_swrap32 _ j); [apply swrap32_id; lia|].
  change (zcanon 0 mod 2 ^ 32) with 0. rewrite Z.add_0_r. apply Z.mod_mod. lia. }
rewrite trap_br_ge, Hm, H0. replace (j - 1 <? j) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
(* INT32 DOUBLING GUARD: lui t,0x40000; addw t,r,t; bltz t -> unimp (traps iff r + 2^30 overflows int32). *)
Lemma trap_dbl_guard : forall E r c, Sg E r = c -> - 2 ^ 30 <= c < 2 ^ 30 ->
branch_taken BC_LT (sv_denot E (SAluw ALU_ADD r (SLit 1073741824))) (sv_denot E (SLit 0)) = false.
Proof.
intros E r c Hr Hc. rewrite trap_br_lt, S_SAluw, S_SLit, U_SLit. cbn [zalu_raw].
rewrite (trap_mod32_of_S E r c Hr).
rewrite (trap_swrap32 _ (c + 2 ^ 30)).
- rewrite swrap32_id by lia. rewrite (swrap64_id 0) by (unfold half64; lia). apply Z.ltb_ge. lia.
- change (zcanon 1073741824 mod 2 ^ 32) with (2 ^ 30). apply Z.add_mod_idemp_l. lia.
Qed.

(* ==== The WRAP family (R5) and the seat helpers (R1-R3), BTrapKit 2026-10-29.  Each WRAP lemma takes the walk's
   own bound facts: the base's value, the offset's value, and base + offset below 2^64. *)
Lemma trap_br_geu : forall E a b, branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_ltu, U. reflexivity. Qed.
(* WRAP, atom form: bltu p,base -> unimp with p = base + d held in its own atom (gestures_end 0x826a4: atom 33 =
   held + 8i, atom 32 = held, W4's gsl_wrap; check_bounded 0x856ec: atom 6 = P + 56i, atom 12 = P). *)
Lemma trap_ptr_wrap_atom : forall E p b hp d, ew E p = Z_to_bv 64 (hp + d) -> ew E b = Z_to_bv 64 hp ->
0 <= hp -> 0 <= d -> hp + d < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SOff p 0)) (sv_denot E (SOff b 0)) = false.
Proof.
intros E p b hp d Hp Hb H0 H1 H2.
apply (trap_ptr_bltu E (SOff b 0) (SOff p 0) hp (hp + d)); [| |lia].
- rewrite U_SOff, Hb, unsigned_lit, Z.add_0_r. unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
- rewrite U_SOff, Hp, unsigned_lit, Z.add_0_r. unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.
Lemma trap_lxor_mod64 : forall a b, Z.lxor (a mod 2 ^ 64) (b mod 2 ^ 64) mod 2 ^ 64 = Z.lxor a b mod 2 ^ 64.
Proof.
intros a b. apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low, !Z.lxor_spec, !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
(* not b  (xori t,b,-1) *)
Lemma trap_U_not : forall E b y, U E b = y -> U E (SAlu ALU_XOR b (SLit (-1))) = 2 ^ 64 - 1 - y.
Proof.
intros E b y Hb. pose proof (U_range E b) as R. rewrite Hb in R. unfold M64 in R.
rewrite U_SAlu, U_SLit, Hb. cbn [zalu_raw]. unfold zcanon, M64.
rewrite <- (Z.mod_small y (2 ^ 64)) at 1 by lia.
rewrite trap_lxor_mod64, Z.lxor_m1_r. unfold Z.lnot. rewrite <- Z.sub_1_r.
replace (- y - 1) with ((2 ^ 64 - 1 - y) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* WRAP, not form: not t,base; bltu t,off -> unimp (taken iff base + off >= 2^64).  t = ~base is the engine's
   SAlu ALU_XOR base (SLit (-1)) (value: trap_U_not) or a seated atom (trap_w_not); gesture_model 0x8612c:
   ~LINE < js + 1 is refuted by LINE + len <= 140737479966720. *)
Lemma trap_ptr_wrap_not : forall E t o y z, U E t = 2 ^ 64 - 1 - y -> U E o = z -> y + z < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E t) (sv_denot E o) = false.
Proof. intros E t o y z Ht Ho Hyz. rewrite trap_br_ltu, Ht, Ho. apply Z.ltb_ge. lia. Qed.
(* WRAP, neg form: neg t,off; bltu t,base -> unimp (0 < off; taken iff base + off > 2^64); gesture_model 0x860e0,
   where the runner decided it from -len's seated range. *)
Lemma trap_ptr_wrap_neg : forall E t b z y, U E t = 2 ^ 64 - z -> U E b = y -> 0 < z -> y + z <= 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E t) (sv_denot E b) = false.
Proof. intros E t b z y Ht Hb Hz Hyz. rewrite trap_br_ltu, Ht, Hb. apply Z.ltb_ge. lia. Qed.
(* WRAP, constant: li t,-k; bgeu p,t -> unimp (p + k wraps); gesture_model 0x860a0 (k = 13), drain 0x83a24. *)
Lemma trap_ptr_wrap_k : forall E p t y k, U E p = y -> U E t = 2 ^ 64 - k -> y + k < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E p) (sv_denot E t) = false.
Proof. intros E p t y k Hp Ht Hyk. rewrite trap_br_geu, Hp, Ht. apply negb_false_iff. apply Z.ltb_lt. lia. Qed.
(* WRAP, p + 1: addi t,p,1; bgeu one,t -> unimp (taken iff t <= 1: p null or p + 1 wraps);
   LLVMFuzzerTestOneInput 0x845e8 (one = s7 = 1, t = p + 1 with 0 < p < 2^64 - 1). *)
Lemma trap_ptr_inc : forall E o t x, U E o = 1 -> U E t = x -> 2 <= x ->
branch_taken BC_GEU (sv_denot E o) (sv_denot E t) = false.
Proof. intros E o t x Ho Ht Hx. rewrite trap_br_geu, Ho, Ht. apply negb_false_iff. apply Z.ltb_lt. lia. Qed.
(* NULL-CONS xor after the runner folded seqz p to 0 (p >= 4096), with the base's snez flag held in atom n = 1:
   beqz (xor a4 0) (check_bounded 0x856f8; W8Add's cb_xor1). *)
Lemma trap_U_null_xor_folded : forall E n, ew E n = Z_to_bv 64 1 -> U E (SAlu ALU_XOR (SOff n 0) (SLit 0)) = 1.
Proof. intros E n H. rewrite U_SAlu, U_SOff, H, unsigned_lit, U_SLit. reflexivity. Qed.
Lemma trap_null_xor_folded : forall E n, ew E n = Z_to_bv 64 1 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit 0))) (sv_denot E (SLit 0)) = false.
Proof. intros E n H. exact (trap_nonnull E _ 1 (trap_U_null_xor_folded E n H) ltac:(lia)). Qed.
(* ALIGN4: andi r,a,3; bnez r -> unimp (an int*, e.g. __errno_location's result: send_line 0x82930) *)
Lemma trap_U_andi3 : forall E a x, U E a = x -> U E (SAlu ALU_AND a (SLit 3)) = x mod 4.
Proof.
intros E a x Ha. rewrite U_SAlu, U_SLit, Ha. cbn [zalu_raw].
rewrite (zcanon_id 3) by (unfold M64; lia).
assert (H3 : Z.land x 3 = x mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
rewrite H3. apply zcanon_id. pose proof (Z.mod_pos_bound x 4 ltac:(lia)). unfold M64. lia.
Qed.
Lemma trap_align4 : forall E a x, U E a = x -> x mod 4 = 0 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND a (SLit 3))) (sv_denot E (SLit 0)) = false.
Proof. intros E a x Ha Hx. rewrite trap_br_ne, (trap_U_andi3 E a x Ha), U_SLit, Hx. reflexivity. Qed.
(* A closer as a SEAT CONDITION (R5: f_conds of a loop head) or as the taken polarity of a trap on a NOT-TAKEN
   edge (check_shape_ends 0x85a0c blt; drain 0x839e0 bne): YP0m.acond_ok is  branch_taken ... = true. *)
Lemma trap_seat : forall E c a b, branch_taken c (sv_denot E a) (sv_denot E b) = false ->
acond_ok E (mkAC (neg_bc c) a b).
Proof. intros E c a b H. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_taken_neg, H. reflexivity. Qed.
(* ---- Word values of one-time flags at a seat (R3), in W8Add's cb_snez / cb_al8nz form. *)
(* snez a4,P *)
Lemma trap_w_snez : forall P, 0 < P < 2 ^ 64 -> alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 P) = Z_to_bv 64 1.
Proof.
intros P HP. rewrite zalu64_sound. f_equal. unfold zalu64, zcanon, M64. cbn [zalu_raw].
rewrite Zmod_0_l, (Z.mod_small P) by lia. destruct (Z.ltb_spec 0 P); [reflexivity | lia].
Qed.
(* andi a0,P,7; seqz a0,a0; snez a4,P; and a6,a0,a4 *)
Lemma trap_w_base_ok : forall P, 0 < P < 2 ^ 64 -> P mod 8 = 0 ->
alu64 ALU_AND (alu64 ALU_SLTU (alu64 ALU_AND (Z_to_bv 64 P) (Z_to_bv 64 7)) (Z_to_bv 64 1))
  (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 P)) = Z_to_bv 64 1.
Proof.
intros P HP H8. rewrite (trap_w_snez P HP).
assert (HA : alu64 ALU_AND (Z_to_bv 64 P) (Z_to_bv 64 7) = Z_to_bv 64 0).
{ rewrite zalu64_sound. f_equal. unfold zalu64, zcanon, M64. cbn [zalu_raw].
  rewrite (Z.mod_small P) by lia. change (7 mod 2 ^ 64) with 7.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite H8. reflexivity. }
rewrite HA, !zalu64_sound. reflexivity.
Qed.
(* not t,P  (a negated pointer held across a loop, e.g. gesture_model's ~LINE) *)
Lemma trap_w_not : forall P, 0 <= P < 2 ^ 64 ->
alu64 ALU_XOR (Z_to_bv 64 P) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - P).
Proof.
intros P HP. rewrite zalu64_sound. f_equal. unfold zalu64, zcanon, M64. cbn [zalu_raw].
rewrite trap_lxor_mod64, Z.lxor_m1_r. unfold Z.lnot. rewrite <- Z.sub_1_r.
replace (- P - 1) with ((2 ^ 64 - 1 - P) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
