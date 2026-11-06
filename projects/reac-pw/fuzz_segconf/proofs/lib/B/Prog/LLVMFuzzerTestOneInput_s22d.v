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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 513 of its 557 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/LLVMFuzzerTestOneInput_s22b.v, with its module names changed; 554 of its 656 lines of code are new or changed and 455 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece d (p4) of
   segment S14 of the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0): the parent loop
   of the inlined m_split, 0x85c58 .. 0x85ccc (back edge 0x85cbc), from the cut S22_VP to S22_JOIN or S22_VM.

   proves function LLVMFuzzerTestOneInput (segment S14 piece only; reuse search, rule 24: released units, the earlier
   proof delivery and working heads; the result is recorded with the commissioning brief; none: written new)

   One turn of the loop at t (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s:936-965):
     0x85c58  bltu a3, a1 (the UBSan trap: ~(M + 256 i) < t): decided in the run by the ranges of atoms 13 and 11
     0x85c5c .. 0x85c6c  check 33 (the shadow byte of M + 256 i + t, slow path 0x85cc4): a token, the obligation
              range_addressable [M + 256 i + t, +1) closed from m's heap block
     0x85c70 .. 0x85c74  the byte b := name[t] (s6 + a1 = atom 32 by the seed's alias, its byte atom 33)
     0x85c80  bltu ((b - 48) & 255), t0 = 10         a digit       -> 0x85cb8
     0x85c94  bltu (((b & ~32) - 65) & 255), 26     a letter      -> 0x85cb8
     0x85ca4  bltu 50, (b & 255) - 45               out of range  -> JOIN 0x85b58
     0x85cb4  beqz (144(s1) >> (b - 45)) & 1        not in the mask -> JOIN 0x85b58
     0x85cb8 .. 0x85cbc  a1 := t + 1; bne a2 (= di), a1 -> VP (t + 1), else j 0x85cd0 = VM
   No store: every run keeps memory (no write window), so the invariant s22_inv carries over by s22d_inv_kept.
   The atoms of the seed: registers 0 .. 31 (sr_atoms), 32 = M + 256 i + t, 33 = b. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
SegSyms SegList SegPa SegPaLib PaLibG PaSB PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s22k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the seed at 0x85c58 (S22_VP) ======================= *)
(* a6 (16) is the shadow base; the name's byte t at atom 32 (s6 + a1 and s11 + a1 name it), its value atom 33; the
   mask slot 144(s1) (atom 9 is s1) *)
Definition VPx : sv := SOff 16 0.
Definition VPspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition vp_byte : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition vp_mask : YP09.region :=
  YP09.mkRegion (Some 9%nat) 144 152 144 144 [YP09.mkChunk 144 (CVal 8 (SLit LT_MASK))].
Definition vp_facts : facts :=
  mkFacts [ (11%nat, mkAF 0 15 0); (13%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0);
            (16%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF 0 255 0) ]
    []
    [ (SAlu ALU_ADD (SOff 27 0) (SOff 11 0), SOff 32 0); (SAlu ALU_ADD (SOff 22 0) (SOff 11 0), SOff 32 0) ].
Definition ss_vp : sstate := mkSS S22_VP sr_atoms [vp_byte; vp_mask] None vp_facts.
(* the registers every run of the turn leaves as they were *)
Definition s22d_KL : list (bv 5) := [2; 3; 4; 5; 8; 9; 12; 13; 16; 19; 20; 21; 22; 23; 24; 26; 27]%bv.
Ltac s22d_in := unfold s22d_KL; cbn [In]; repeat (first [left; reflexivity | right]).

(* ======================= arithmetic of the byte tests ======================= *)
Lemma s22d_m256 : forall z, (z mod 2 ^ 64) mod 256 = z mod 256.
Proof.
intros z. rewrite (Z.mod_eq z (2 ^ 64)) by lia. change (2 ^ 64) with 18446744073709551616.
replace (z - 18446744073709551616 * (z / 18446744073709551616))
  with (z + (- (72057594037927936 * (z / 18446744073709551616))) * 256) by ring.
apply Z_mod_plus_full.
Qed.

Lemma s22d_land255 : forall z, Z.land (z mod 2 ^ 64) 255 = z mod 256.
Proof.
intros z. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. apply s22d_m256.
Qed.

Lemma s22d_range_t : forall b, 0 <= b < 256 -> (50 <? (b - 45) mod 2 ^ 64) = true -> b < 45 \/ 95 < b.
Proof.
intros b Rb H. destruct (Z.lt_ge_cases b 45) as [Hl|Hg]; [left; exact Hl|right].
rewrite Z.mod_small in H by lia. apply Z.ltb_lt in H. lia.
Qed.

Lemma s22d_range_f : forall b, 0 <= b < 256 -> (50 <? (b - 45) mod 2 ^ 64) = false -> 45 <= b <= 95.
Proof.
intros b Rb H. apply Z.ltb_ge in H. destruct (Z.lt_ge_cases b 45) as [Hl|Hg].
- replace (b - 45) with ((b - 45 + 2 ^ 64) + (-1) * 2 ^ 64) in H by lia.
  rewrite Z_mod_plus_full, Z.mod_small in H by lia. lia.
- rewrite Z.mod_small in H by lia. lia.
Qed.

Section u.
Variable E : env.
Variable b : Z.
Hypothesis E33 : ew E 33 = Z_to_bv 64 b.
Hypothesis Rb : 0 <= b < 256.

Lemma s22d_U33 : forall c, U E (SOff 33 c) = (b + c) mod 2 ^ 64.
Proof. intros c. rewrite U_SOff, E33, unsigned_lit_small by lia. reflexivity. Qed.

(* 0x85c78 .. 0x85c80 *)
Lemma s22d_dig : ew E 5 = Z_to_bv 64 10 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_AND (SOff 33 (-48)) (SLit 255))) (sv_denot E (SOff 5 0)) =
  SegModel.isdigit b.
Proof.
intros H5. rewrite branch_ltu_U, (U_and_lit E _ 255) by lia.
rewrite s22d_U33, s22d_land255, (U_atom E 5 10 H5) by lia. exact (s22_dig_b b Rb).
Qed.

(* 0x85c84 .. 0x85c94 *)
Lemma s22d_alpha :
  branch_taken BC_LTU
    (sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SOff 33 0) (SLit (-33))) (SLit (-65))) (SLit 255)))
    (sv_denot E (SLit 26)) = s22_alpha b.
Proof.
rewrite branch_ltu_U, (U_and_lit E _ 255), (U_lit E 26) by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite (s22d_U33 0), !U_SLit.
unfold zcanon, M64. rewrite Z.add_0_r, (Z.mod_small b) by lia.
change ((-33) mod 2 ^ 64) with 18446744073709551583. change ((-65) mod 2 ^ 64) with 18446744073709551551.
pose proof (Z_land_upper b 18446744073709551583 ltac:(lia)) as HL.
rewrite (Z.mod_small (Z.land b 18446744073709551583)) by lia.
replace (Z.land b 18446744073709551583 + 18446744073709551551)
  with (Z.land b 18446744073709551583 - 65 + 1 * 2 ^ 64) by lia.
rewrite Z_mod_plus_full, s22d_land255. exact (s22_alpha_b b Rb).
Qed.

(* (b & 255) - 45, the operand of 0x85ca4 and the shift of 0x85cac *)
Lemma s22d_UX : U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 33 0) (SLit 255)) (SLit (-45))) = (b - 45) mod 2 ^ 64.
Proof.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_and_lit E _ 255) by lia. rewrite (s22d_U33 0), U_SLit.
unfold zcanon, M64. rewrite Z.add_0_r, (Z.mod_small b) by lia.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. rewrite (Z.mod_small b 256) by lia.
change ((-45) mod 2 ^ 64) with 18446744073709551571.
replace (b + 18446744073709551571) with (b - 45 + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full.
Qed.

(* 0x85c98 .. 0x85ca4 *)
Lemma s22d_range :
  branch_taken BC_LTU (sv_denot E (SLit 50))
    (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 33 0) (SLit 255)) (SLit (-45)))) =
  (50 <? (b - 45) mod 2 ^ 64).
Proof. rewrite branch_ltu_U, (U_lit E 50) by lia. rewrite s22d_UX. reflexivity. Qed.

(* 0x85ca8 .. 0x85cb4: bit b - 45 of the mask *)
Lemma s22d_mask : 45 <= b <= 95 ->
  branch_taken BC_EQ
    (sv_denot E (SAlu ALU_AND (SAlu ALU_SRL (SLit 1125899906850819)
       (SAlu ALU_ADD (SAlu ALU_AND (SOff 33 0) (SLit 255)) (SLit (-45)))) (SLit 1)))
    (sv_denot E (SLit 0)) = negb (s22_pkr b).
Proof.
intros Hb. rewrite branch_eq_U, (U_and_lit E _ 1), (U_lit E 0) by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite s22d_UX, (U_lit E 1125899906850819) by lia.
rewrite (Z.mod_small (b - 45) (2 ^ 64)) by lia.
replace (Z.land (b - 45) 63) with (b - 45)
  by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; change (2 ^ 6) with 64; rewrite Z.mod_small by lia;
      reflexivity).
assert (HS0 : 0 <= Z.shiftr 1125899906850819 (b - 45) < 2 ^ 64).
{ rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (b - 45) ltac:(lia) ltac:(lia)) as HP.
  split; [apply Z.div_pos; lia|].
  apply (Z.le_lt_trans _ 1125899906850819); [apply Z.div_le_upper_bound; lia | lia]. }
rewrite (zcanon_small (Z.shiftr 1125899906850819 (b - 45))) by lia.
change 1125899906850819 with S22_MASK. rewrite (s22_mask_bit (b - 45)) by lia.
unfold s22_pkr. destruct (_ || _ || _ || _)%bool; reflexivity.
Qed.
End u.

(* 0x85cbc: bne a2, a1 with a2 = di, a1 = t + 1 *)
Lemma s22d_next : forall E (di t : nat), ew E 12 = Z_to_bv 64 (Z.of_nat di) -> ew E 11 = Z_to_bv 64 (Z.of_nat t) ->
  (di < 16)%nat -> (t < 16)%nat ->
  branch_taken BC_NE (sv_denot E (SOff 12 0)) (sv_denot E (SOff 11 1)) = negb (Z.of_nat di =? Z.of_nat t + 1).
Proof.
intros E di t H12 H11 Hd Ht. rewrite branch_ne_U.
rewrite (U_atom E 12 (Z.of_nat di) H12), (U_atom_off E 11 (Z.of_nat t) 1 H11) by lia. reflexivity.
Qed.

Lemma s22d_den11 : forall E t, ew E 11 = Z_to_bv 64 (Z.of_nat t) -> (t <= 15)%nat ->
  sv_denot E (SOff 11 1) = w64 (Z.of_nat (Datatypes.S t)).
Proof.
intros E t H Ht. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
change (U E (SOff 11 1) = Z.of_nat (Datatypes.S t)). rewrite (U_atom_off E 11 (Z.of_nat t) 1 H) by lia. lia.
Qed.

Lemma s22d_le1 : forall z, 0 <= z < 256 -> YO0f.le_byte z 1 0 = z.
Proof.
intros z Hz. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================= reader facts kept by a reader that agrees everywhere ======================= *)
Section r.
Variables rd rd' : reader.
Hypothesis RE : forall a, rd' a = rd a.
Lemma s22d_word : forall a, rdword rd' a = rdword rd a.
Proof. intros a. unfold rdword. rewrite !RE. reflexivity. Qed.
Lemma s22d_bytes : forall a bs, sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros a bs H j Hj. rewrite RE. exact (H j Hj). Qed.
Lemma s22d_zs : forall a l, sa_zs rd a l -> sa_zs rd' a l.
Proof. intros a l H j Hj. rewrite RE. exact (H j Hj). Qed.
Lemma s22d_val : forall a n v, sa_val rd a n v -> sa_val rd' a n v.
Proof. intros a n v H j Hj. rewrite RE. exact (H j Hj). Qed.
Lemma s22d_strz : forall p s, sa_strz rd p s -> sa_strz rd' p s.
Proof. intros p s [H1 H2]. split; [exact (s22d_zs _ _ H1) | exact H2]. Qed.
Lemma s22d_tail : forall e, sa_tail rd e -> sa_tail rd' e.
Proof. intros e H x Hx. rewrite RE. exact (H x Hx). Qed.
Lemma s22d_str : forall p s, sa_str rd p s -> sa_str rd' p s.
Proof. intros p s [H1 H2]. split; [exact (s22d_strz _ _ H1) | exact (s22d_tail _ H2)]. Qed.
Lemma s22d_lit : forall segs B a s, sa_lit segs B rd a s -> sa_lit segs B rd' a s.
Proof. intros segs B a s (H1 & H2 & H3). split; [exact H1|]. split; [exact (s22d_str _ _ H2) | exact H3]. Qed.
Lemma s22d_cat : forall segs B cat, sa_cat segs B rd cat -> sa_cat segs B rd' cat.
Proof.
intros segs B cat (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros j Hj. destruct (H3 j Hj) as (tp & Ht & Hl). exists tp. rewrite s22d_word.
split; [exact Ht | exact (s22d_lit _ _ _ _ Hl)].
Qed.
Lemma s22d_ssp : forall g gd, sa_ssp rd g gd -> sa_ssp rd' g gd.
Proof.
intros g gd [H1 [x H2]]. split; [rewrite s22d_word; exact H1 | exists x; rewrite s22d_word; exact H2].
Qed.
Lemma s22d_rtab : forall a t, sa_rtab rd a t -> sa_rtab rd' a t.
Proof. intros a t (bs & Hb & He). exists bs. split; [exact (s22d_bytes _ _ Hb) | exact He]. Qed.
Lemma s22d_mtab : forall a t, sa_mtab rd a t -> sa_mtab rd' a t.
Proof. intros a t (bs & Hb & He). exists bs. split; [exact (s22d_bytes _ _ Hb) | exact He]. Qed.
Lemma s22d_rconf : forall a r, sa_rconf rd a r -> sa_rconf rd' a r.
Proof. intros a r (bs & Hb & He). exists bs. split; [exact (s22d_bytes _ _ Hb) | exact He]. Qed.
Lemma s22d_mconf : forall a r, sa_mconf rd a r -> sa_mconf rd' a r.
Proof. intros a r (bs & Hb & He). exists bs. split; [exact (s22d_bytes _ _ Hb) | exact He]. Qed.
Lemma s22d_guard : forall tab cap, sa_guardtab rd tab cap -> sa_guardtab rd' tab cap.
Proof. intros tab cap H. exact (s22d_bytes _ _ H). Qed.
Lemma s22d_raddr : forall a n, range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof. intros a n H x Hx. rewrite RE. exact (H x Hx). Qed.
Lemma s22d_hull : forall x n, shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof. intros x n H s Hs. rewrite RE. exact (H s Hs). Qed.
Lemma s22d_addr : forall q n, sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [exact (s22d_raddr _ _ H4) | intros Hn; exact (s22d_hull _ _ (H5 Hn))].
Qed.
Lemma s22d_ro : forall segs rlo rhi B, arodata_okP segs rlo rhi B rd -> arodata_okP segs rlo rhi B rd'.
Proof. intros segs rlo rhi B H a H1 H2 H3. rewrite RE. exact (H a H1 H2 H3). Qed.
Lemma s22d_GI : forall L j, ltoi_GI L j rd -> ltoi_GI L j rd'.
Proof. intros L j H x Hx. rewrite RE. exact (H x Hx). Qed.
Lemma s22d_mfw : forall segs B w, m_file_c.mf_words segs B rd w -> m_file_c.mf_words segs B rd' w.
Proof.
intros segs B w (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros j Hj. destruct (H3 j Hj) as (wp & Hw & Hl). exists wp. rewrite s22d_word.
split; [exact Hw | exact (s22d_lit _ _ _ _ Hl)].
Qed.
Lemma s22d_mfr : forall segs B w, m_file_c.mf_roles segs B rd w -> m_file_c.mf_roles segs B rd' w.
Proof.
intros segs B w (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros j Hj. exact (s22d_val _ _ _ (H3 j Hj)).
Qed.
Lemma s22d_himg : forall segs B L M C Wd R G Gd f g,
  seg_himg segs B L M C Wd R G Gd f g rd -> seg_himg segs B L M C Wd R G Gd f g rd'.
Proof.
intros segs B L M C Wd R G Gd f g H. unfold seg_himg in H |- *.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
split; [exact (s22d_val _ _ _ H1)|]. split; [exact H2|].
split; [intros s Hs; destruct (H3 s Hs) as [Hl Ha]; split; [exact (s22d_lit _ _ _ _ Hl) | exact Ha]|].
split; [intros s Hs; destruct (H4 s Hs) as [Hl Ha]; split; [exact (s22d_lit _ _ _ _ Hl) | exact Ha]|].
split; [exact (s22d_cat _ _ _ H5)|]. split; [exact H6|].
split; [exact (s22d_mfw _ _ _ H7)|]. split; [exact (s22d_mfr _ _ _ H8)|].
split; [exact (s22d_ssp _ _ H9) | exact H10].
Qed.
End r.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run with no write window keeps every byte of the view *)
Lemma s22d_keep : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hw a. apply aview_eq_of. apply HF. intros (r & Hr & Ha).
rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.

Lemma s22d_vm1 : forall H mem a v, aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H mem) a) as [bb|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as <-.
rewrite s22d_le1 by (pose proof (bv_unsigned_in_range 8 bb) as R; change (bv_modulus 8) with 256 in R; lia).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Definition vp_E (regs : bvmap 5 word) (a b : Z) : env := Eimg (Ereg regs [Z_to_bv 64 a; Z_to_bv 64 b]).

Lemma s22d_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 adr (t : nat) b,
  getr regs 9 = w64 s1 -> getr regs 11 = w64 (Z.of_nat t) -> getr regs 13 = w64 (lt_not adr) ->
  getr regs 16 = w64 SHADOW_OFF -> getr regs 22 = w64 adr -> getr regs 27 = w64 adr ->
  4096 <= adr -> adr + Z.of_nat t + 1 <= 140737479966720 -> (t <= 15)%nat ->
  adr + Z.of_nat t + 1 <= s1 + 144 -> s1 + 152 <= 2 ^ 64 ->
  rdW W mem (adr + Z.of_nat t) = Some b -> rdword (rdW W mem) (s1 + 144) = Some LT_MASK ->
  st_ok_pi SEGS VAL (vp_E regs (adr + Z.of_nat t) b) ss_vp
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_VP)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 adr t b H9 H11 H13 H16 H22 H27 Ha1 Ha2 Ht Hd Hs1 HV HM.
pose proof (sa_aview_rng _ _ _ _ _ HV) as Rb.
set (E := vp_E regs (adr + Z.of_nat t) b).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat t)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E13 : ew E 13 = Z_to_bv 64 (lt_not adr)) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E16 : ew E 16 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 16%nat 16%bv eq_refl); exact H16).
assert (E22 : ew E 22 = Z_to_bv 64 adr) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E27 : ew E 27 = Z_to_bv 64 adr) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 (adr + Z.of_nat t))
  by (subst E; unfold vp_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b)
  by (subst E; unfold vp_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HRO : regs_ok E sr_atoms regs) by (subst E; unfold vp_E; apply regs_ok_Eimg_Ereg).
clearbody E. unfold lt_not, SHADOW_OFF in *.
unfold ss_vp. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact HRO.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold YP09.region_ok, vp_byte.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (adr + Z.of_nat t) 0 1 (SOff 33 0) b).
    * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    * cbn. lia.
    * rewrite Z.add_0_r. exact (s22d_vm1 _ _ _ _ HV).
  + unfold YP09.region_ok, vp_mask.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ s1 144 8 (SLit LT_MASK) LT_MASK).
    * reflexivity.
    * unfold LT_MASK. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * exact (val_mem_of_rdword SEGS (w_H W) mem _ _ HM).
- cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
  unfold extent_disjoint, vp_byte, vp_mask. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E32, E9, !unsigned_lit_small by lia. left. lia.
- split; [|split].
  + cbn [atoms_ok vp_facts f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E11, E13, E16, E32, E33, !unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
  + exact I.
  + cbn [alias_ok vp_facts f_alias]. split; [|split; [|exact I]]; apply U_inj; rewrite U_SAlu; cbn [zalu_raw].
    * rewrite (U_atom E 27 adr E27), (U_atom E 11 _ E11), (U_atom E 32 _ E32) by lia. apply zcanon_small. lia.
    * rewrite (U_atom E 22 adr E22), (U_atom E 11 _ E11), (U_atom E 32 _ E32) by lia. apply zcanon_small. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ======================= the invariant across a run that writes nothing ======================= *)
Lemma s22d_slots : forall cx rd rd' L, (forall a, rd' a = rd a) -> lt_slots cx rd L -> lt_slots cx rd' L.
Proof. intros cx rd rd' L RE H o v Hin. rewrite (s22d_word _ _ RE). exact (H o v Hin). Qed.

Lemma s22d_hblk : forall ly S rd rd' a n, (forall a, rd' a = rd a) -> lt_hblk B ly S rd a n -> lt_hblk B ly S rd' a n.
Proof.
intros ly S rd rd' a n RE (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
exact (s22d_addr _ _ RE _ _ H4).
Qed.

Lemma s22d_img : forall cx rd rd', (forall a, rd' a = rd a) -> lt_img B cx rd -> lt_img B cx rd'.
Proof.
intros cx rd rd' RE (H1 & H2 & H3). split; [exact (s22d_ro _ _ RE _ _ _ _ H1)|].
split; [exact (s22d_himg _ _ RE _ _ _ _ _ _ _ _ _ _ _ H2) | exact (s22d_GI _ _ RE _ _ H3)].
Qed.

Lemma s22d_cm : forall rd rd' c m st, (forall a, rd' a = rd a) -> lt_cm rd c m st -> lt_cm rd' c m st.
Proof. intros rd rd' c m st RE [H1 H2]. split; [exact (s22d_rconf _ _ RE _ _ H1) | exact (s22d_mconf _ _ RE _ _ H2)]. Qed.

Lemma s22d_tabs : forall cx rd rd' tab mt t, (forall a, rd' a = rd a) -> lt_tabs cx rd tab mt t -> lt_tabs cx rd' tab mt t.
Proof.
intros cx rd rd' tab mt t RE (H1 & H2 & H3 & H4 & H5 & H6).
split; [exact H1|]. split; [exact (s22d_rtab _ _ RE _ _ H2)|]. split; [exact (s22d_guard _ _ RE _ _ H3)|].
split; [exact (s22d_val _ _ RE _ _ _ H4)|]. split; [exact (s22d_mtab _ _ RE _ _ H5) | exact H6].
Qed.

Lemma s22d_frame_kept : forall cx ly S (W : world SEGS) regs mem md k o regs' mem' md',
  lt_frame B cx ly S W regs mem md k o ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_frame B cx ly S W regs' mem' md' k o.
Proof.
intros cx ly S W regs mem md k o regs' mem' md' HF HJ' RE E2 E3 E4 E8 E9.
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & H0 & H8 & H16 & HW & H200 & Hsh & H184).
split; [exact HJ'|]. rewrite E2, E3, E4, E8, E9.
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split; [intros j r Hj; rewrite (s22d_word _ _ RE); exact (HSV j r Hj)|].
rewrite !(s22d_word _ _ RE).
split; [exact H0|]. split; [exact H8|]. split; [exact H16|]. split; [exact HW|]. split; [exact H200|].
split; [exact (s22d_zs _ _ RE _ _ Hsh) | exact H184].
Qed.

Lemma s22d_inv_kept : forall cx i c m tab mt o ly S (W : world SEGS) regs mem md k acc regs' mem' md',
  s22_inv B MT cx i c m tab mt o ly S W regs mem md k acc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  s22_inv B MT cx i c m tab mt o ly S W regs' mem' md' k acc.
Proof.
intros cx i c m tab mt o ly S W regs mem md k acc regs' mem' md' HI HJ' RE E2 E3 E4 E8 E9.
destruct HI as (Hi & Hd & (HF & HIMG & HBL & HBUD) & Hc & Hm & Ht & Hmt & HSL & HCM & HTB).
split; [exact Hi|]. split; [exact Hd|].
split; [split; [exact (s22d_frame_kept _ _ _ _ _ _ _ _ _ _ _ _ HF HJ' RE E2 E3 E4 E8 E9)|]
          ; split; [exact (s22d_img _ _ _ RE HIMG) | split; [exact HBL | exact HBUD]]|].
split; [exact (s22d_hblk _ _ _ _ _ _ RE Hc)|]. split; [exact (s22d_hblk _ _ _ _ _ _ RE Hm)|].
split; [exact (s22d_hblk _ _ _ _ _ _ RE Ht)|]. split; [exact (s22d_hblk _ _ _ _ _ _ RE Hmt)|].
split; [exact (s22d_slots _ _ _ _ RE HSL)|].
split; [exact (s22d_cm _ _ _ _ _ RE HCM) | exact (s22d_tabs _ _ _ _ _ _ RE HTB)].
Qed.

(* ======================= the tactics of a turn ======================= *)
(* after a run: chain its frame fact onto K (the view at the new state = the view at the turn's start) *)
Ltac s22d_keep_step K :=
  lazymatch type of K with forall a, aview ?sg ?h _ a = aview _ _ ?m0 a =>
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ ?m2) |- _ =>
  let K' := fresh "K" in
  assert (K' : forall a, aview sg h m2 a = aview sg h m0 a)
    by (intros a; rewrite (s22d_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a); apply K);
  clear HFr K; rename K' into K;
  repeat match goal with
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end
  end end.

(* the registers the runs keep, at the state of HS *)
Ltac s22d_kr HS AG KR :=
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ s22d_KL HS AG ltac:(vm_compute; reflexivity)) as KR;
  cbn [ms_regs restrict] in KR.

(* register 11 at the state of HS *)
Ltac s22d_r11 HS P :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms 11%bv HS) as P;
  let e := eval vm_compute in (sr_get (ss_regs ss) 11%bv) in change (sr_get (ss_regs ss) 11%bv) with e in P end.

(* a byte that passed (0x85cb8 .. 0x85cc0): t + 1 < di -> VP (t + 1), else VM *)
Ltac s22d_pass HS HJ SHOK K F11 F12 AG1 END_VP END_VM di t Hp :=
  paj_run_tok RUN HS HJ SHOK VPspan; [awr_ok_tac|];
  s22d_keep_step K;
  psrr_branch_tok RUN BR HS SHOK VPspan;
  [ let Hn := fresh "Hn" in
    assert (Hn : negb (Z.of_nat di =? Z.of_nat t + 1) = true)
      by (rewrite <- (s22d_next _ di t F12 F11 ltac:(lia) ltac:(lia)); assumption);
    paj_run_to_tok RUNTO HS HJ SHOK VPspan S22_VP; [awr_ok_tac|];
    s22d_keep_step K; pmkst HS;
    let KR := fresh "KR" in s22d_kr HS AG1 KR;
    let P := fresh "P11" in s22d_r11 HS P;
    rewrite (s22d_den11 _ t F11 ltac:(lia)) in P;
    apply (END_VP _ _ _ Hp ltac:(apply negb_true_iff, Z.eqb_neq in Hn; lia) HJ K KR P)
  | let Hn := fresh "Hn" in
    assert (Hn : negb (Z.of_nat di =? Z.of_nat t + 1) = false)
      by (rewrite <- (s22d_next _ di t F12 F11 ltac:(lia) ltac:(lia)); assumption);
    paj_run_to_tok RUNTO HS HJ SHOK VPspan S22_VM; [awr_ok_tac|];
    s22d_keep_step K; pmkst HS;
    let KR := fresh "KR" in s22d_kr HS AG1 KR;
    apply (END_VM _ _ _ Hp ltac:(apply negb_false_iff, Z.eqb_eq in Hn; lia) HJ K KR) ].

(* a byte that failed: JOIN *)
Ltac s22d_fail HS HJ SHOK K AG1 END_J Hp :=
  paj_run_to_tok RUNTO HS HJ SHOK VPspan S22_JOIN; [awr_ok_tac|];
  s22d_keep_step K; pmkst HS;
  let KR := fresh "KR" in s22d_kr HS AG1 KR;
  apply (END_J _ _ _ Hp HJ K KR).

(* ======================= one turn of the parent loop ======================= *)
Lemma s22d_turn : forall i, S22_JOIN_stmt B MT i -> S22_VM_stmt B MT i ->
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (di t : nat) (vid : Z),
  lt_base B MT cx -> sa_frm0 ->
  s22_inv B MT cx i c m tab mt LFO_NV ly S W regs mem md k acc ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = Some di -> (di <> 0)%nat ->
  SegModel.m_digits (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) 0 = Some vid ->
  1 <= vid <= 4094 ->
  (t < di)%nat ->
  forallb SegModel.h_parent_ok (firstn t (SegModel.ms_name (x_seg cx i))) = true ->
  getr regs 5 = w64 10 -> getr regs 11 = w64 (Z.of_nat t) -> getr regs 12 = w64 (Z.of_nat di) ->
  getr regs 13 = w64 (lt_not (seg_spec.mseg_addr m i)) -> getr regs 16 = w64 SHADOW_OFF ->
  getr regs 19 = w64 (seg_spec.mseg_addr m i) -> getr regs 21 = w64 vid -> getr regs 23 = w64 (Z.of_nat di) ->
  getr regs 24 = w64 m ->
  s22_rk m i regs ->
  (forall regs' mem' md',
     s22_inv B MT cx i c m tab mt LFO_NV ly S W regs' mem' md' k acc ->
     (Datatypes.S t < di)%nat ->
     forallb SegModel.h_parent_ok (firstn (Datatypes.S t) (SegModel.ms_name (x_seg cx i))) = true ->
     getr regs' 5 = w64 10 -> getr regs' 11 = w64 (Z.of_nat (Datatypes.S t)) -> getr regs' 12 = w64 (Z.of_nat di) ->
     getr regs' 13 = w64 (lt_not (seg_spec.mseg_addr m i)) -> getr regs' 16 = w64 SHADOW_OFF ->
     getr regs' 19 = w64 (seg_spec.mseg_addr m i) -> getr regs' 21 = w64 vid -> getr regs' 23 = w64 (Z.of_nat di) ->
     getr regs' 24 = w64 m -> s22_rk m i regs' ->
     SRr SEGS W (cfg_at SEGS (BASE + S22_VP) regs' mem' md') (lt_post B MT cx)) ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_VP) regs mem md) (lt_post B MT cx).
Proof.
intros i HJOIN HVM cx ly S W regs mem md k acc c m tab mt di t vid HB Hfrm Hinv Hign Hstr Hdi Hdig Hvid Ht Hall
  R5 R11 R12 R13 R16 R19 R21 R23 R24 Hrk HNEXT.
(* ---- the facts of the turn ---- *)
pose proof Hinv as (Hi & Hdecl & HCORE & _ & Hmb & _ & _ & HSL & HCM & _).
pose proof HCORE as (HFRM & _ & _ & _).
pose proof HFRM as (HJ & R2 & _ & _ & _ & R9 & _).
pose proof (proj1 HJ) as HAR.
pose proof Hmb as (Hinm & Hm4096 & _ & _).
pose proof Hrk as (R20 & R22 & R26 & R27).
destruct (s22_name_str cx i c m (rdW W mem) HCM Hi) as (Hnstr & Hnlen & Hnnf).
assert (Hn32 : (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat).
{ destruct HCM as [_ (bs & _ & _ & Hn32 & _)]. exact Hn32. }
assert (Hdin : (di < length (SegModel.ms_name (x_seg cx i)))%nat).
{ pose proof (SegModel.strrchr_lt _ _ _ Hstr) as Hl. rewrite SegModel.cut_nul_id in Hl by exact Hnnf. exact Hl. }
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR Hinm) as (_ & _ & Hmceil & _).
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hreq].
unfold seg_spec.SEG_M_SIZE in Hreq, Hmceil.
pose proof alloc_ceiling_value as [[CL CH] _].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
destruct HSTK as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hs1 : x_sp0 cx - 352 - 31 <= x_s1 cx <= x_sp0 cx - 352).
{ unfold x_s1, LT_FRAME. pose proof (Z.mod_pos_bound (x_sp0 cx - 352) 32 ltac:(lia)). lia. }
assert (Hadr : seg_spec.mseg_addr m i = m + 256 * Z.of_nat i)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (HMASK : rdword (rdW W mem) (x_s1 cx + 144) = Some LT_MASK).
{ apply HSL. apply in_or_app. right. unfold LT_LD. cbn [In].
  right; right; right; right; right; right; right; left; reflexivity. }
remember (nth t (SegModel.ms_name (x_seg cx i)) 0) as b eqn:Hbdef.
assert (HV : rdW W mem (seg_spec.mseg_addr m i + Z.of_nat t) = Some b).
{ destruct Hnstr as [Hzs _]. rewrite (Hzs t ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite app_nth1 by lia. rewrite Hbdef. reflexivity. }
pose proof (sa_aview_rng _ _ _ _ _ HV) as Rb.
unfold STK_LLVMFuzzerTestOneInput in Hslo.
(* ---- the three exits of the turn ---- *)
assert (END_VP : forall regs' mem' md', SegModel.h_parent_ok b = true -> (Datatypes.S t < di)%nat ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  (forall r, In r s22d_KL -> getr regs' r = getr regs r) ->
  getr regs' 11 = w64 (Z.of_nat (Datatypes.S t)) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + S22_VP)) mem' (seg_rom SEGS)) md') (lt_post B MT cx)).
{ intros regs' mem' md' Hp Hlt HJ' RE KR P11.
  pose proof (s22d_inv_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv HJ' RE
    (KR 2%bv ltac:(s22d_in)) (KR 3%bv ltac:(s22d_in)) (KR 4%bv ltac:(s22d_in)) (KR 8%bv ltac:(s22d_in))
    (KR 9%bv ltac:(s22d_in))) as Hinv'.
  apply (HNEXT regs' mem' md' Hinv' Hlt).
  - rewrite (s22_firstn_S _ t 0) by lia. rewrite forallb_app, Hall. cbn [forallb]. rewrite <- Hbdef, Hp.
    reflexivity.
  - rewrite KR by s22d_in. exact R5.
  - exact P11.
  - rewrite KR by s22d_in. exact R12.
  - rewrite KR by s22d_in. exact R13.
  - rewrite KR by s22d_in. exact R16.
  - rewrite KR by s22d_in. exact R19.
  - rewrite KR by s22d_in. exact R21.
  - rewrite KR by s22d_in. exact R23.
  - rewrite KR by s22d_in. exact R24.
  - split; [rewrite KR by s22d_in; exact R20|]. split; [rewrite KR by s22d_in; exact R22|].
    split; [rewrite KR by s22d_in; exact R26 | rewrite KR by s22d_in; exact R27]. }
assert (END_VM : forall regs' mem' md', SegModel.h_parent_ok b = true -> Datatypes.S t = di ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  (forall r, In r s22d_KL -> getr regs' r = getr regs r) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + S22_VM)) mem' (seg_rom SEGS)) md') (lt_post B MT cx)).
{ intros regs' mem' md' Hp Heq HJ' RE KR.
  pose proof (s22d_inv_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv HJ' RE
    (KR 2%bv ltac:(s22d_in)) (KR 3%bv ltac:(s22d_in)) (KR 4%bv ltac:(s22d_in)) (KR 8%bv ltac:(s22d_in))
    (KR 9%bv ltac:(s22d_in))) as Hinv'.
  assert (Hfa : forallb SegModel.h_parent_ok (firstn di (SegModel.ms_name (x_seg cx i))) = true).
  { rewrite <- Heq, (s22_firstn_S _ t 0) by lia. rewrite forallb_app, Hall. cbn [forallb].
    rewrite <- Hbdef, Hp. reflexivity. }
  assert (Hhd : SegModel.hd0 (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) <> 0).
  { pose proof Hdig as Hd'.
    destruct (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) as [|q r] eqn:Es.
    - try rewrite Es in Hd'. cbn in Hd'. injection Hd' as Hv0. lia.
    - cbn [SegModel.hd0]. intros Hq. apply Hnnf.
      rewrite <- (firstn_skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))). apply in_or_app. right.
      rewrite Es. left. exact Hq. }
  apply (HVM cx ly S W regs' mem' md' k acc c m tab mt di vid HB Hfrm Hinv' Hign).
  - exact (s22_split_some _ di vid Hstr Hdi Hhd Hdig (proj1 Hvid) Hfa).
  - lia.
  - exact Hvid.
  - rewrite KR by s22d_in. exact R19.
  - rewrite KR by s22d_in. exact R21.
  - rewrite KR by s22d_in. exact R23.
  - rewrite KR by s22d_in. exact R24.
  - split; [rewrite KR by s22d_in; exact R20|]. split; [rewrite KR by s22d_in; exact R22|].
    split; [rewrite KR by s22d_in; exact R26 | rewrite KR by s22d_in; exact R27]. }
assert (END_J : forall regs' mem' md', SegModel.h_parent_ok b = false ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  (forall r, In r s22d_KL -> getr regs' r = getr regs r) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + S22_JOIN)) mem' (seg_rom SEGS)) md') (lt_post B MT cx)).
{ intros regs' mem' md' Hp HJ' RE KR.
  pose proof (s22d_inv_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv HJ' RE
    (KR 2%bv ltac:(s22d_in)) (KR 3%bv ltac:(s22d_in)) (KR 4%bv ltac:(s22d_in)) (KR 8%bv ltac:(s22d_in))
    (KR 9%bv ltac:(s22d_in))) as Hinv'.
  assert (Hff : forallb SegModel.h_parent_ok (firstn di (SegModel.ms_name (x_seg cx i))) = false).
  { apply (s22_forallb_false SegModel.h_parent_ok _ t 0).
    - rewrite length_firstn. lia.
    - rewrite nth_firstn. destruct (Nat.ltb_spec t di) as [_|Hge]; [rewrite <- Hbdef; exact Hp | lia]. }
  pose proof (s22_split_none_parent _ di vid Hstr Hdig Hff) as Hsp.
  assert (Hx : x_decl cx (Datatypes.S i) = x_decl cx i).
  { unfold x_decl. apply s22_decl_step_skip; [exact Hi | exact (proj1 Hdecl) | right; exact Hsp]. }
  apply (HJOIN cx ly S W regs' mem' md' k acc c m tab mt HB Hfrm Hx Hinv').
  - rewrite KR by s22d_in. exact R16.
  - rewrite KR by s22d_in. exact R24.
  - split; [rewrite KR by s22d_in; exact R20|]. split; [rewrite KR by s22d_in; exact R22|].
    split; [rewrite KR by s22d_in; exact R26 | rewrite KR by s22d_in; exact R27]. }
(* ---- the seed ---- *)
pose proof (s22d_seed W regs mem (x_s1 cx) (seg_spec.mseg_addr m i) t b R9 R11 R13 R16 R22 R27
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HV HMASK) as HS.
assert (HEI : img_env VAL A_LIM (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b)) by apply Eimg_env.
assert (AG : env_agree 32 (Ereg regs [Z_to_bv 64 (seg_spec.mseg_addr m i + Z.of_nat t); Z_to_bv 64 b])
               (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b)).
{ split; [intros n Hn; unfold vp_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
          ew (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b) n = getr regs r)
  by (intros n r Hn; unfold vp_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E5 : ew (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b) 5 = Z_to_bv 64 10)
  by (rewrite (EE 5%nat 5%bv eq_refl); exact R5).
assert (E11 : ew (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b) 11 = Z_to_bv 64 (Z.of_nat t))
  by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E12 : ew (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b) 12 = Z_to_bv 64 (Z.of_nat di))
  by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E16 : ew (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b) 16 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E32 : ew (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b) 32 =
              Z_to_bv 64 (seg_spec.mseg_addr m i + Z.of_nat t))
  by (unfold vp_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b) 33 = Z_to_bv 64 b)
  by (unfold vp_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (SHOK : sh_ok SEGS VPx [] (vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b) (mrestrict (w_H W) mem))
  by (unfold sh_ok; constructor).
clear EE.
set (E := vp_E regs (seg_spec.mseg_addr m i + Z.of_nat t) b) in *. clearbody E.
assert (K : forall a, rdW W mem a = rdW W mem a) by reflexivity.
unfold cfg_at. change (w64 (BASE + S22_VP)) with (Z_to_bv 64 (BASE + S22_VP)).
(* ---- 0x85c58 .. 0x85c80: the trap (decided), check 33, the byte, the digit test ---- *)
paj_run_tok RUN HS HJ SHOK VPspan.
{ cbn [ms_mem mkst]. rewrite (U_atom E 32 (seg_spec.mseg_addr m i + Z.of_nat t) E32) by lia.
  apply (obl_of_block SEGS B LAWS ly S W mem md E VPx _ 1 m seg_spec.SEG_M_SIZE HAR Hinm).
  - unfold VPx. apply U_atom; [exact E16 | unfold SHADOW_OFF; lia].
  - lia.
  - unfold seg_spec.SEG_M_SIZE in *. lia. }
{ awr_ok_tac. }
s22d_keep_step K.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (E1 := Ev) in * end.
assert (F5 : ew E1 5 = Z_to_bv 64 10) by (unfold E1; rewrite !ew_ewset_other by lia; exact E5).
assert (F11 : ew E1 11 = Z_to_bv 64 (Z.of_nat t)) by (unfold E1; rewrite !ew_ewset_other by lia; exact E11).
assert (F12 : ew E1 12 = Z_to_bv 64 (Z.of_nat di)) by (unfold E1; rewrite !ew_ewset_other by lia; exact E12).
assert (F33 : ew E1 33 = Z_to_bv 64 b) by (unfold E1; rewrite !ew_ewset_other by lia; exact E33).
assert (AG1 : env_agree 32 (Ereg regs [Z_to_bv 64 (seg_spec.mseg_addr m i + Z.of_nat t); Z_to_bv 64 b]) E1).
{ unfold E1. split; [intros n Hn; rewrite !ew_ewset_other by lia; exact (proj1 AG n Hn) | exact (proj2 AG)]. }
clearbody E1.
psrr_branch_tok RUN BR HS SHOK VPspan.
- (* a digit *)
  assert (Hp : SegModel.h_parent_ok b = true).
  { assert (Hd : SegModel.isdigit b = true) by (rewrite <- (s22d_dig E1 b F33 Rb F5); assumption).
    rewrite (s22_pk_split b Rb), Hd. reflexivity. }
  s22d_pass HS HJ SHOK K F11 F12 AG1 END_VP END_VM di t Hp.
- assert (Hd : SegModel.isdigit b = false) by (rewrite <- (s22d_dig E1 b F33 Rb F5); assumption).
  (* 0x85c84 .. 0x85c94: the letter test *)
  paj_run_tok RUN HS HJ SHOK VPspan.
  { awr_ok_tac. }
  s22d_keep_step K.
  psrr_branch_tok RUN BR HS SHOK VPspan.
  + (* a letter *)
    assert (Hp : SegModel.h_parent_ok b = true).
    { assert (Ha : s22_alpha b = true) by (rewrite <- (s22d_alpha E1 b F33 Rb); assumption).
      rewrite (s22_pk_split b Rb), Ha, orb_true_r. reflexivity. }
    s22d_pass HS HJ SHOK K F11 F12 AG1 END_VP END_VM di t Hp.
  + assert (Ha : s22_alpha b = false) by (rewrite <- (s22d_alpha E1 b F33 Rb); assumption).
    (* 0x85c98 .. 0x85ca4: b - 45 <= 50 *)
    paj_run_tok RUN HS HJ SHOK VPspan.
    { awr_ok_tac. }
    s22d_keep_step K.
    psrr_branch_tok RUN BR HS SHOK VPspan.
    * (* out of [45, 95]: JOIN *)
      assert (Hp : SegModel.h_parent_ok b = false).
      { assert (Hr : (50 <? (b - 45) mod 2 ^ 64) = true) by (rewrite <- (s22d_range E1 b F33 Rb); assumption).
        exact (s22_pk_out b Rb Hd Ha (s22d_range_t b Rb Hr)). }
      s22d_fail HS HJ SHOK K AG1 END_J Hp.
    * assert (Hr : (50 <? (b - 45) mod 2 ^ 64) = false) by (rewrite <- (s22d_range E1 b F33 Rb); assumption).
      pose proof (s22d_range_f b Rb Hr) as Hin.
      (* 0x85ca8 .. 0x85cb4: bit b - 45 of the mask *)
      paj_run_tok RUN HS HJ SHOK VPspan.
      { awr_ok_tac. }
      s22d_keep_step K.
      psrr_branch_tok RUN BR HS SHOK VPspan.
      -- (* the bit is 0: JOIN *)
         assert (Hp : SegModel.h_parent_ok b = false).
         { assert (Hk : negb (s22_pkr b) = true) by (rewrite <- (s22d_mask E1 b F33 Rb Hin); assumption).
           rewrite (s22_pk_rest b Rb Hd Ha). apply negb_true_iff. exact Hk. }
         s22d_fail HS HJ SHOK K AG1 END_J Hp.
      -- assert (Hp : SegModel.h_parent_ok b = true).
         { assert (Hk : negb (s22_pkr b) = false) by (rewrite <- (s22d_mask E1 b F33 Rb Hin); assumption).
           rewrite (s22_pk_rest b Rb Hd Ha). apply negb_false_iff. exact Hk. }
         s22d_pass HS HJ SHOK K F11 F12 AG1 END_VP END_VM di t Hp.
Qed.

(* ======================= the loop: by induction on di - t ======================= *)
Lemma s22_p4 : s22_p4_stmt B MT.
Proof.
intros i HJOIN HVM. unfold S22_VP_stmt.
intros cx ly S W regs mem md k acc c m tab mt di t vid.
remember (di - t)%nat as n eqn:Hn. revert t regs mem md Hn.
induction n as [|n IH]; intros t regs mem md Hn HB Hfrm Hinv Hign Hstr Hdi Hdig Hvid Ht Hall
  R5 R11 R12 R13 R16 R19 R21 R23 R24 Hrk; [lia|].
apply (s22d_turn i HJOIN HVM cx ly S W regs mem md k acc c m tab mt di t vid HB Hfrm Hinv Hign Hstr Hdi Hdig
  Hvid Ht Hall R5 R11 R12 R13 R16 R19 R21 R23 R24 Hrk).
intros regs' mem' md' Hinv' Ht' Hall' R5' R11' R12' R13' R16' R19' R21' R23' R24' Hrk'.
exact (IH (Datatypes.S t) regs' mem' md' ltac:(lia) HB Hfrm Hinv' Hign Hstr Hdi Hdig Hvid Ht' Hall'
  R5' R11' R12' R13' R16' R19' R21' R23' R24' Hrk').
Qed.

End e.
End f.
End d.
