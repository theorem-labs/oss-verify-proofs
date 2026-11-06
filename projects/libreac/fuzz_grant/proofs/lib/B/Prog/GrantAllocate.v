(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_grant_allocate on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) walk of reac_grant_allocate at 0x85554 over lib/B/Prog's walk layer, proving walk_reac_grant_allocate of lib/B/Prog/GrantBContracts.v. Image B's code is NOT image A's: it is 24 bytes (six instructions) longer, so this walk adds the two UBSan trap guards 0x8557c and 0x85588 with their refutations and replaces image A's test of 48 against the sum by image B's test of 47 against the sum minus one; the shadow-base cell is image B's object 35, not image A's object 32, and the image bound is IMG_LO_B / IMG_TOP_B, never the shared kit's off_img. *)
(* Ported from lib/A/Prog/GrantAllocate.v at a working branch 5aae1e8a0ce (blob 0ebaef01219f627a2dd18f946391d189bbd1a964; that branch's AB01 is 1e6f4323d1efa3d368a2c4473c33f1e6e5acedba, the current generation). Closure check at that commit: the file's whole transitive Require closure inside proofs/libreac/fuzz_grant is 152 files, and `grep -cE "Admitted|admit\b|Axiom|Parameter"` over all 152 gives 0 hits. *)
(* reac_grant_allocate on IMAGE B (fuzz_grant.asan-ubsan, bin/ sha256 fde52226dc48, symbols 5a5ee7c02b4e):
   the walk of `Theorem pb_reac_grant_allocate : walk_reac_grant_allocate B`, whose contract
   (tb_reac_grant_allocate_spec) is the Definition in lib/B/Prog/GrantBContracts.v.  Ported from image A's walk
   lib/A/Prog/GrantAllocate.v (entry 0x84860); every address, word and constant below is image B's, read from
   lib/B/Prog/GrantList.v, and the image facts are image B's (IMG_LO_B / IMG_TOP_B of GrantTop.v, object 1 the
   GOT word 0x9d6d0 and object 35 the shadow-base cell 0xa5978).

   Entry 0x85554 = BASE + AF_reac_grant_allocate (0x4b18), 42 instructions, frame 16 (`addi sp,sp,-16`, ra at
   sp + 8).  a0 = p, a1 = base, a2 = width; a3 holds the result, -1 from 0x8555c.  The four returns of -1 are
   0x85560 (`blt a1,zero`), 0x85564 (`beq a0,zero`, refuted by the fact 4096 <= p of slot 10), 0x85570
   (`bltu a4,a5` with a4 = sext32 (width - 41) and a5 = 2^64 - 40: width not in 1..40) and 0x85590
   (`blt a5,a4` with a5 = 47 and a4 = sext32 (base + width - 1): base + width > 48).

   IMAGE B ADDS TWO GUARDS image A has not, because it is the UBSan build; both jump to the trap `unimp`
   0x855e0 and both are refuted here under the contract's int32 and overflow premises:
     0x8557c  `bne a5,a4`  with a5 = addw a1,a2 (0x85578) and a4 = add a1,a2 (0x85574) - the 32-bit sum
              differs from the 64-bit sum (gba_cond_ovf1);
     0x85588  `bge a4,a5`  with a4 = sext32 (sum - 1) (0x85584) and a5 = sext32 sum (0x85580) - the
              decremented sum is not below the sum (gba_cond_ovf2).
   Image A tests 48 against the sum itself; image B tests 47 against sum - 1 (gba_cond_b48).

   The two stores are checked: the GOT word object 1 (0x85594 / 0x85598), the shadow-base cell object 35
   (0x8559c), the shadow byte of p (0x855a8) and of p + 1 (0x855c0).  Each report branch (0x855ec and
   0x855f8, the last slot, which falls through into reac_grant_build_sweep 0x855fc) is refuted from the
   contract's `bytes_ok W memc p 2`, which the walk engine carries as the shadow entry mkSHE 10 0 2. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YO0a YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- boolean / arithmetic plumbing (image A's GrantAllocate.v, name-prefixed) ---------------------------- *)
Ltac gba_zbool :=
repeat match goal with
| H : negb _ = true |- _ => apply Bool.negb_true_iff in H
| H : negb _ = false |- _ => apply Bool.negb_false_iff in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
| H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
| H : (_ && _) = false |- _ => apply Bool.andb_false_iff in H; destruct H
end.
Ltac gba_unwrap :=
unfold bv_swrap, bv_wrap, zcanon, M64 in *;
try change (bv_modulus 64) with (2 ^ 64) in *; try change (bv_modulus 32) with (2 ^ 32) in *;
try change (bv_half_modulus 64) with (2 ^ 63) in *; try change (bv_half_modulus 32) with (2 ^ 31) in *.
Ltac gba_lits :=
change (2 ^ 64) with 18446744073709551616 in *; change (2 ^ 32) with 4294967296 in *;
change (2 ^ 31) with 2147483648 in *; change (2 ^ 63) with 9223372036854775808 in *.
Ltac gba_ifs := repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; gba_zbool; lia.

(* ---- the denotation of the four symbolic shapes this function's branches compare ------------------------- *)
Lemma gba_u_off : forall E n z v, ew E n = Z_to_bv 64 v ->
bv_unsigned (sv_denot E (SOff n z)) = (v + z) mod 2 ^ 64.
Proof.
intros E n z v H. cbn [sv_denot]. rewrite H, !lit64_unsigned, Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma gba_u_lit : forall E z, bv_unsigned (sv_denot E (SLit z)) = z mod 2 ^ 64.
Proof. intros E z. cbn [sv_denot]. apply lit64_unsigned. Qed.
Lemma gba_u_add : forall E a b,
bv_unsigned (sv_denot E (SAlu ALU_ADD a b))
= (bv_unsigned (sv_denot E a) + bv_unsigned (sv_denot E b)) mod 2 ^ 64.
Proof. intros E a b. cbn [sv_denot]. rewrite alu64_add. unfold add64. reflexivity. Qed.
Lemma gba_u_addw : forall E a b,
bv_unsigned (sv_denot E (SAluw ALU_ADD a b))
= sx32 (bv_unsigned (sv_denot E a) + bv_unsigned (sv_denot E b)).
Proof. intros E a b. cbn [sv_denot]. rewrite addw_rr_unsigned. unfold addw. reflexivity. Qed.
Lemma gba_s64_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> s64 (bv_unsigned (Z_to_bv 64 z)) = z.
Proof.
intros z Hz. rewrite lit64_unsigned. unfold s64.
destruct (Z_lt_le_dec z 0) as [Hn|Hn].
- rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (z + 1 * 2 ^ 64) (2 ^ 63)); lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.

(* ---- 0x85560 `blt a1,zero`: base < 0 ---------------------------------------------------------------------- *)
Lemma gba_cond_bb : forall E b, ew E 11 = Z_to_bv 64 b -> int32 b ->
branch_taken BC_LT (sv_denot E (SOff 11 0)) (sv_denot E (SLit 0)) = (b <? 0).
Proof.
intros E b H Hb. unfold int32 in Hb. rewrite branch_lt.
cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (gba_s64_lit b ltac:(lia)), (gba_s64_lit 0 ltac:(lia)). reflexivity.
Qed.

(* ---- 0x85570 `bltu a4,a5`, a4 = sext32 (width - 41), a5 = 2^64 - 40: width not in 1..40 -------------------- *)
Lemma gba_cond_bw : forall E x, ew E 12 = Z_to_bv 64 x -> int32 x ->
branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SLit (-41))))
  (sv_denot E (SLit 18446744073709551576)) = negb ((1 <=? x) && (x <=? 40)).
Proof.
intros E x H Hx. unfold int32 in Hx.
assert (Q : (if branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SLit (-41))))
  (sv_denot E (SLit 18446744073709551576)) then 1 else 0)
= (if (1 <=? x) && (x <=? 40) then 0 else 1)).
{ rewrite branch_ltu_U. unfold U. cbn [sv_denot].
rewrite addw_rr_unsigned, H, Z.add_0_r, !Z_to_bv_unsigned. gba_unwrap. gba_lits.
rewrite (Z.mod_mod x 18446744073709551616) by lia.
rewrite (addw_congr (x mod 18446744073709551616) x (-41 mod 18446744073709551616) (-41))
by (change (2 ^ 32) with 4294967296; apply mod64_mod32).
replace (18446744073709551576 mod 18446744073709551616) with 18446744073709551576 by reflexivity.
unfold addw.
destruct (Z.leb_spec 1 x) as [Ha|Ha]; destruct (Z.leb_spec x 40) as [Hb|Hb]; cbn [andb].
- replace (x + -41) with (- (41 - x)) by lia. rewrite sx32_neg_small by (gba_lits; lia). gba_lits. gba_ifs.
- rewrite sx32_small by (gba_lits; lia). gba_ifs.
- destruct (Z.leb_spec (41 - 2147483648) x) as [Hc|Hc].
+ replace (x + -41) with (- (41 - x)) by lia. rewrite sx32_neg_small by (gba_lits; lia). gba_lits. gba_ifs.
+ rewrite (sx32_congr (x + -41) (x + -41 + 4294967296))
by (change (2 ^ 32) with 4294967296; symmetry;
replace (x + -41 + 4294967296) with ((x + -41) + 1 * 4294967296) by lia; apply Z.mod_add; lia).
rewrite sx32_small by (gba_lits; lia). gba_ifs.
- exfalso. lia. }
destruct (branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SLit (-41))))
  (sv_denot E (SLit 18446744073709551576)));
destruct ((1 <=? x) && (x <=? 40)); cbn in Q |- *; first [reflexivity | discriminate Q].
Qed.

(* ---- the value of image B's two sums, under the premises the earlier branches leave ------------------------ *)
Section gba_sums.
Variable E : env.
Variables b x : Z.
Hypothesis H11 : ew E 11 = Z_to_bv 64 b.
Hypothesis H12 : ew E 12 = Z_to_bv 64 x.
Hypothesis Hb : 0 <= b < 2 ^ 31.
Hypothesis Hx : 1 <= x <= 40.
Hypothesis Hs : b + x < 2 ^ 31.
Lemma gba_v11 : bv_unsigned (sv_denot E (SOff 11 0)) = b.
Proof. rewrite (gba_u_off E 11 0 b H11), Z.add_0_r. apply Z.mod_small. lia. Qed.
Lemma gba_v12 : bv_unsigned (sv_denot E (SOff 12 0)) = x.
Proof. rewrite (gba_u_off E 12 0 x H12), Z.add_0_r. apply Z.mod_small. lia. Qed.
(* 0x85574 `add a4,a1,a2` *)
Lemma gba_vsum : bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 11 0) (SOff 12 0))) = b + x.
Proof. rewrite gba_u_add, gba_v11, gba_v12. apply Z.mod_small. lia. Qed.
(* 0x85578 `addw a5,a1,a2` *)
Lemma gba_vsumw : bv_unsigned (sv_denot E (SAluw ALU_ADD (SOff 11 0) (SOff 12 0))) = b + x.
Proof. rewrite gba_u_addw, gba_v11, gba_v12. apply sx32_small. lia. Qed.
(* 0x85580 `addiw a5,a4,0` *)
Lemma gba_vsum0 :
bv_unsigned (sv_denot E (SAluw ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SLit 0))) = b + x.
Proof.
rewrite gba_u_addw, gba_vsum, gba_u_lit.
replace (0 mod 2 ^ 64) with 0 by reflexivity. rewrite Z.add_0_r. apply sx32_small. lia.
Qed.
(* 0x85584 `addiw a4,a4,-1` *)
Lemma gba_vsum1 :
bv_unsigned (sv_denot E (SAluw ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SLit (-1)))) = b + x - 1.
Proof.
rewrite gba_u_addw, gba_vsum, gba_u_lit.
rewrite (sx32_congr (b + x + (-1) mod 2 ^ 64) (b + x - 1)).
- apply sx32_small. lia.
- replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  replace (b + x + (2 ^ 64 - 1)) with ((b + x - 1) + 2 ^ 32 * 2 ^ 32) by lia.
  apply Z.mod_add. lia.
Qed.
(* 0x8557c `bne a5,a4`: the trap guard, false *)
Lemma gba_cond_ovf1 :
branch_taken BC_NE (sv_denot E (SAluw ALU_ADD (SOff 11 0) (SOff 12 0)))
  (sv_denot E (SAlu ALU_ADD (SOff 11 0) (SOff 12 0))) = false.
Proof.
rewrite branch_ne, gba_vsum, gba_vsumw, Z.eqb_refl. reflexivity.
Qed.
(* 0x85588 `bge a4,a5`: the trap guard, false *)
Lemma gba_cond_ovf2 :
branch_taken BC_GE (sv_denot E (SAluw ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SLit (-1))))
  (sv_denot E (SAluw ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SLit 0))) = false.
Proof.
rewrite branch_ge, gba_vsum0, gba_vsum1, !s64_small by lia.
apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
Qed.
(* 0x85590 `blt a5,a4` with a5 = 47: base + width > 48 *)
Lemma gba_cond_b48 :
branch_taken BC_LT (sv_denot E (SLit 47))
  (sv_denot E (SAluw ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SLit (-1))))
= negb (b + x <=? 48).
Proof.
rewrite branch_lt, gba_vsum1. cbn [sv_denot].
rewrite (gba_s64_lit 47 ltac:(lia)), (s64_small (b + x - 1)) by lia.
destruct (Z.ltb_spec 47 (b + x - 1)); destruct (Z.leb_spec (b + x) 48); cbn [negb];
first [reflexivity | lia].
Qed.
End gba_sums.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section B0.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Lemma gba_val_mem1 : forall (Ez : env) (m : word -> option byte) (q off : Z) (e : sv) (z : Z),
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk off (CVal 1 e)) -> sv_denot Ez e = Z_to_bv 64 z ->
YI04.val_mem SEGS m (q + off) 1%nat (z mod 256).
Proof.
intros Ez m q off e z Hc Hz kk Hk.
assert (Hk0 : kk = 0%nat) by lia. subst kk.
destruct (Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-.
rewrite !Z.add_0_r in Hb2. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb2. f_equal.
unfold YP09.byte_of_word, le_byte. rewrite Hz, Z_to_bv_unsigned.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. change (2 ^ 8) with 256.
rewrite !Z.shiftr_0_r.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
change (2 ^ 8) with 256. rewrite Z.shiftr_0_r. rewrite !Z.mod_mod by lia.
symmetry. apply Zmod_div_mod; [lia | lia | exists (2 ^ 56); reflexivity].
Qed.
Lemma gba_aview_of_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) ->
aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hq. unfold aview, YP09.mbyte. rewrite Hq. reflexivity. Qed.
Lemma gba_garr8_two : forall (Ez : env) (m : word -> option byte) (q a c : Z) (ea ec : sv),
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk 0 (CVal 1 ea)) ->
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk 1 (CVal 1 ec)) ->
sv_denot Ez ea = Z_to_bv 64 a -> sv_denot Ez ec = Z_to_bv 64 c ->
garr8 SEGS m q [a mod 256; c mod 256].
Proof.
intros Ez m q a c ea ec H0 H1 Ha Hc j Hj.
cbn [length] in Hj.
destruct j as [|j]; [|destruct j as [|j]; [|cbn in Hj; lia]].
- cbn [nth]. split; [|pose proof (Z.mod_pos_bound a 256 ltac:(lia)); lia].
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  pose proof (gba_val_mem1 Ez m q 0 ea a H0 Ha) as Hv. rewrite Z.add_0_r in Hv. exact Hv.
- cbn [nth]. split; [|pose proof (Z.mod_pos_bound c 256 ltac:(lia)); lia].
  cbn [Z.of_nat]. exact (gba_val_mem1 Ez m q 1 ec c H1 Hc).
Qed.

Section C0.
Variable B : asyms.

(* ---- the symbolic entry state: image B's frame 16, the GOT word, the cell and the caller's two bytes ------ *)
Definition gba_Bx : sv := SOff 32 0.
Definition gba_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gba_out : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 2 0 2 [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0))].
Definition gba_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; gba_out ].
Definition gba_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 8) 0);
(32%nat, mkAF SB SB 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0) ] [] [].
Definition gba_ss : sstate := mkSS AF_reac_grant_allocate sr_atoms gba_regions None gba_facts.
Definition gba_SH : list shent := [ mkSHE 10 0 2 ].
Definition gba_extra (v0 v1 : Z) : list word := map (Z_to_bv 64) [SB; v0; v1].
Definition gba_E (regs : bvmap 5 word) (v0 v1 : Z) : env := Eimg (Ereg regs (gba_extra v0 v1)).

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Lemma gba_entry :
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p v0 v1 : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 p ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_grant_allocate -> spZ regs <= sp0 ->
p + 2 <= 2 ^ 47 - 8 -> (spZ regs <= p \/ p + 2 <= spZ regs - STK_reac_grant_allocate) ->
(p + 2 <= IMG_LO_B \/ IMG_TOP_B <= p) -> (forall x, p <= x < p + 2 -> app_addr x) ->
(forall a, p <= a < p + 2 -> apresent (w_H W) memc a) ->
bytes_ok W memc p 2 ->
garr8 SEGS (mrestrict (w_H W) memc) p [v0; v1] ->
st_ok_pi SEGS VAL (gba_E regs v0 v1) gba_ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_grant_allocate)) memc (seg_rom SEGS)))
/\ sh_ok SEGS gba_Bx gba_SH (gba_E regs v0 v1) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p v0 v1
HJ H10 Hal16 Hwlo Hwhi Hphi Hpside Hoff Happ Hppr HRA HG01.
pose proof IMG_LO_B_val as HILO. pose proof IMG_TOP_B_val as HIHI.
rewrite HILO, HIHI in Hoff.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_grant_allocate = 4112) by reflexivity.
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof (app_addr_below_ceil p (Happ p ltac:(lia))) as Hp0.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 35%nat ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1%nat ltac:(lia)) as HgotR.
rewrite HILO, HIHI in HcellR, HgotR.
pose proof pa_B_ok as HBASE.
destruct (HG01 0%nat ltac:(cbn; lia)) as [Mv0 Rv0]. cbn [nth] in Mv0, Rv0.
destruct (HG01 1%nat ltac:(cbn; lia)) as [Mv1 Rv1]. cbn [nth] in Mv1, Rv1.
cbn [Z.of_nat] in Mv0, Mv1. rewrite Z.add_0_r in Mv0.
rewrite restrict_mkst_fx.
set (E := gba_E regs v0 v1).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (gba_extra v0 v1)) n)
by (intros n Hn; subst E; unfold gba_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 v0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 v1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E1g : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold gba_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E35g : ew E (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35))) by (subst E; unfold gba_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hpg1 : p + 2 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= p) by lia.
assert (Hpg35 : p + 2 <= VAL (A_OBJ 35) \/ VAL (A_OBJ 35) + 8 <= p) by lia.
split.
- unfold gba_ss. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold gba_regions, gba_out, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
[cbn [sv_denot]; rewrite E35g, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) E35g) by (pose proof (pa_val_range (A_OBJ 35)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 gba_Bx SB);
[cbn [sv_denot gba_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
* rewrite (VB 10%nat p E10) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); apply Hppr; lia|].
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val SEGS E _ p 0 1 (SOff 33 0) v0);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Mv0.
-- apply (chunk_ok_val SEGS E _ p 1 1 (SOff 34 0) v1);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv1].
+ apply pairwise_disjoint_of_extents.
unfold gba_regions, gba_out, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat p E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) E35g) by (pose proof (pa_val_range (A_OBJ 35)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hsp46 HcellR HgcD HgotR Hpg1 Hpg35 Hp0 Hphi Hpside C1 C3 WS Hstk0. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [gba_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hsp46 Hal16 Hp0 Hphi Rv0 Rv1. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, gba_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) memc E gba_Bx 10%nat p 2 p 0 2 HRA).
+ unfold U, gba_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. change (Z.min 0 2) with 0 in Hx. change (Z.max 0 2) with 2 in Hx.
pose proof (Happ x ltac:(lia)) as Hax. unfold app_addr in Hax.
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Ltac gba_awr sp0v spv pv Usp E10 HpW :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc ly own) end;
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0v));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite Usp; lia
| cbn; lia | cbn; lia | ];
apply awr_ok_cons_ro; [cbn; lia|];
apply awr_ok_cons_ro; [cbn; lia|];
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat pv);
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E10; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; exact (proj1 (HpW aa ltac:(lia)))
| apply awr_ok_nil ].

(* Each branch hypothesis the engine leaves, rewritten to a statement about base and width; the two UBSan
   guards 0x8557c / 0x85588 become `false = true` on the arm that reaches the trap 0x855e0. *)
Ltac gba_conds b x E11 E12 Hb32 Hc32 Hovf :=
repeat match goal with
| H : branch_taken BC_LT (sv_denot ?Ez (SOff 11 0)) (sv_denot ?Ez (SLit 0)) = _ |- _ =>
  rewrite (gba_cond_bb Ez b
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E11) Hb32) in H
| H : branch_taken BC_LTU (sv_denot ?Ez (SAluw ALU_ADD (SOff 12 0) (SLit (-41))))
        (sv_denot ?Ez (SLit 18446744073709551576)) = _ |- _ =>
  rewrite (gba_cond_bw Ez x
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E12) Hc32) in H
| H : branch_taken BC_NE (sv_denot ?Ez (SAluw ALU_ADD (SOff 11 0) (SOff 12 0)))
        (sv_denot ?Ez (SAlu ALU_ADD (SOff 11 0) (SOff 12 0))) = _ |- _ =>
  rewrite (gba_cond_ovf1 Ez b x
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E11)
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E12)
    ltac:(unfold int32 in Hb32; lia) ltac:(lia)
    ltac:(pose proof (Hovf ltac:(lia) ltac:(lia)); lia)) in H
| H : branch_taken BC_GE (sv_denot ?Ez (SAluw ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SLit (-1))))
        (sv_denot ?Ez (SAluw ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SLit 0))) = _ |- _ =>
  rewrite (gba_cond_ovf2 Ez b x
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E11)
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E12)
    ltac:(unfold int32 in Hb32; lia) ltac:(lia)
    ltac:(pose proof (Hovf ltac:(lia) ltac:(lia)); lia)) in H
| H : branch_taken BC_LT (sv_denot ?Ez (SLit 47))
        (sv_denot ?Ez (SAluw ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SLit (-1)))) = _ |- _ =>
  rewrite (gba_cond_b48 Ez b x
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E11)
    ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E12)
    ltac:(unfold int32 in Hb32; lia) ltac:(lia)
    ltac:(pose proof (Hovf ltac:(lia) ltac:(lia)); lia)) in H
end; try discriminate; gba_zbool.

Lemma gba_walk : tb_reac_grant_allocate_spec B.
Proof.
unfold tb_reac_grant_allocate_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p base w v0 v1
HJ Hra Hra4 Hgp Htp H10 H11 H12 Hb32 Hc32 Hovf Hal16 Hwlo Hwhi Hphi Hpside Hoff Happ HpW HRA HG01.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof IMG_LO_B_val as HILO. pose proof IMG_TOP_B_val as HIHI.
assert (WS : STK_reac_grant_allocate = 4112) by reflexivity.
assert (Hppr : forall a, p <= a < p + 2 -> apresent (w_H W) memc a)
by (intros a Ha; exact (proj1 (proj2 (HpW a Ha)))).
destruct (gba_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p v0 v1
HJ H10 Hal16 Hwlo Hwhi Hphi Hpside Hoff Happ Hppr HRA HG01) as [HS SHOK].
rewrite HILO, HIHI in Hoff.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (app_addr_below_ceil p (Happ p ltac:(lia))) as Hp0.
assert (Rv0 : 0 <= v0 < 256) by exact (proj2 (HG01 0%nat ltac:(cbn; lia))).
assert (Rv1 : 0 <= v1 < 256) by exact (proj2 (HG01 1%nat ltac:(cbn; lia))).
remember (gba_E regs v0 v1) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold gba_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (gba_extra v0 v1)) n)
by (intros n Hn; subst E; unfold gba_E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 base) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 w) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E33 : ew E 33 = Z_to_bv 64 v0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 v1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (gba_extra v0 v1)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; unfold gba_E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_reac_grant_allocate)) with (Z_to_bv 64 (BASE + AF_reac_grant_allocate)).
let rec go := idtac;
lazymatch goal with HSx : st_ok_pi _ _ _ _ _, HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
paj_run_tok RUN HSx HJx SHOK gba_span; [gba_awr sp0 (spZ regs) p Usp E10 HpW |];
lazymatch goal with
| HSy : st_ok_pi _ _ _ ?ss _ |- _ =>
let K := eval vm_compute in (run_K A_LIM gba_Bx gba_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K gba_Bx gba_span gba_SH (start K gba_Bx gba_span gba_SH ss) end in
let pc := eval vm_compute in (ss_pc ss) in
lazymatch why with
| SR_jalr _ =>
let HFI := fresh "HFI" in
destruct (fits base w) eqn:HFI;
[ try (exfalso; unfold fits in HFI; gba_zbool; gba_zbool; gba_zbool; gba_zbool; lia)
| try (exfalso; unfold fits in HFI; gba_zbool; gba_zbool; gba_zbool; gba_zbool; lia) ];
lazymatch goal with HSz : st_ok_pi _ _ _ _ (restrict _ ?msc), HJz : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
prreg HSz (10%bv : bv 5) R10; prreg HSz (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HSz eq_refl ltac:(vm_compute; reflexivity));
let mq := fresh "mat" in intros mq;
split; [reflexivity|];
exists (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJz|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (gba_extra v0 v1) HSz);
[ split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; apply (proj1 HAE); lia
| cbn [ed ewset]; apply (proj2 HAE)]
| vm_compute; reflexivity ]|];
split; [cbn [ms_regs]; rewrite R10, HFI; apply bv_eq; vm_compute; reflexivity|];
rewrite HFI;
lazymatch type of HSz with
| st_ok_pi ?sg ?vl ?Ez ?ssx (restrict ?Hh ?msy) =>
let HMO := fresh "HMO" in
pose proof (st_ok_mem_ok sg Ez (abs_ss vl ssx) (restrict Hh msy) HSz) as HMO;
cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO;
destruct HMO as (_ & HMO & _);
let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
apply Forall_inv_tail in HMO; apply Forall_inv_tail in HMO; apply Forall_inv_tail in HMO;
apply Forall_inv in HMO;
destruct HMO as (_ & _ & _ & HMO);
let Hc1 := fresh "Hch" in let Hc2 := fresh "Hch" in
pose proof (Forall_inv HMO) as Hc1; pose proof (Forall_inv (Forall_inv_tail HMO)) as Hc2;
let Hb10 := fresh "Hb10" in
assert (Hb10 : base_val Ez (Some 10%nat) = p)
by (cbn [base_val]; rewrite ?ew_ewset_other by lia; rewrite E10; apply unsigned_lit_small; lia);
cbn [YP09.r_base YP09.c_off YP09.c_val] in Hc1, Hc2; rewrite Hb10 in Hc1, Hc2;
let D33 := fresh "D" in let D34 := fresh "D" in let D11 := fresh "D" in let D12 := fresh "D" in
assert (D33 : sv_denot Ez (SOff 33 0) = Z_to_bv 64 v0)
by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
assert (D34 : sv_denot Ez (SOff 34 0) = Z_to_bv 64 v1)
by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
assert (D11 : sv_denot Ez (SOff 11 0) = Z_to_bv 64 base)
by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
assert (D12 : sv_denot Ez (SOff 12 0) = Z_to_bv 64 w)
by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
split;
[ first [ exact (gba_garr8_two Ez _ p base w _ _ Hc1 Hc2 D11 D12)
| exact (gba_garr8_two Ez _ p base w _ _ Hc2 Hc1 D11 D12)
| (replace [v0; v1] with [v0 mod 256; v1 mod 256] by (rewrite (Z.mod_small v0 256), (Z.mod_small v1 256) by lia; reflexivity);
first [ exact (gba_garr8_two Ez _ p v0 v1 _ _ Hc1 Hc2 D33 D34)
| exact (gba_garr8_two Ez _ p v0 v1 _ _ Hc2 Hc1 D33 D34) ]) ]
| ];
let HM := fresh "HM" in
assert (HM : forall xx : word, ~ (spZ regs - STK_reac_grant_allocate <= bv_unsigned xx < spZ regs) ->
~ (p <= bv_unsigned xx < p + 2) -> mrestrict Hh (ms_mem msy) xx = mrestrict Hh memc xx);
[ intros xx HA HB; rewrite WS in HA;
repeat match goal with
| Hf : frame_of ?Ew ?rsw (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- mrestrict ?Hq ?mB xx = _ =>
rewrite (Hf xx ltac:(let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [Hin | Hin];
[ subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
rewrite ?ew_ewset_other in Hr by lia; rewrite ?Usp, ?E10 in Hr;
rewrite ?unsigned_lit_small in Hr by lia; lia |]);
destruct Hin)); clear Hf
end; reflexivity
| ];
let HGr := fresh "HGr" in
assert (HGr : mem_grows (mrestrict Hh memc) (mrestrict Hh (ms_mem msy)));
[ repeat match goal with
| Hg : mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mC) =>
first [ exact Hg | eapply mem_grows_trans; [exact Hg |] ]
end; apply mem_grows_refl
| ];
unfold tcj_kept;
split;
[ intros aa Haa Hww Hee; apply gba_aview_of_eq; apply HM;
rewrite unsigned_lit_small by lia; lia |];
split;
[ intros bb mm ii Hin Hii Hee;
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb mm HAR Hin) as (_ & Hb4096 & Hbceil & _);
apply gba_aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; lia |];
split;
[ intros aa Hin _ _; pose proof (pa_img_range aa Hin) as Hir;
rewrite HILO, HIHI in Hir;
apply gba_aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; lia |];
split;
[ intros cid pos aa Hin Hrr Hee;
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _);
pose proof (fs_frame_bytes_nonneg cid) as Hfb;
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hs1;
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2;
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb) as Hs3;
unfold in_zr, frame_rng in Hrr; cbn [fst snd] in Hrr;
apply gba_aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; destruct Hrr as [Hrr|Hrr]; lia |];
split;
[ intros aa _ _ Hpr; exact (apresent_grows Hh memc (ms_mem msy) aa HGr Hpr) |];
intros aa Haa;
pose proof HJz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _);
apply Hpres2; lia
end
end
| SR_branch _ _ _ =>
psrr_branch_tok RUN BR HSy SHOK gba_span;
[ gba_conds base w E11 E12 Hb32 Hc32 Hovf; go | gba_conds base w E11 E12 Hb32 Hc32 Hovf; go ]
| _ => idtac "STUCK" pc why; fail
end
end end in go.
Qed.
End C0.
End B0.
End A.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg grant_listing}.
Variable B : asyms.
Theorem pb_reac_grant_allocate : walk_reac_grant_allocate B.
Proof.
unfold walk_reac_grant_allocate, hyps_reac_grant_allocate, RT_LAWS, RT_PALIB.
intros [HL HT]. exact (gba_walk B HL HT).
Qed.
End W.
