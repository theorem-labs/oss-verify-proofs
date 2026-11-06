(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmitDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryAdmitDefs.v, with its module names changed; 1111 of its 1170 lines of code are new or changed and 221 lines of the source are left out. *)
(* The read of the input's header in fuzz_grant's entry function LLVMFuzzerTestOneInput
   on the ASan build: the slots 0x80944 .. 0x8098c, the out-of-line blocks the read
   jumps to (0x80dcc .. 0x80e0c, 0x81930 .. 0x81984) and the slow paths of the four
   shadow checks (0x81a14 .. 0x81a1c, 0x81a64 .. 0x81a68, 0x81a98 .. 0x81a9c,
   0x81ab8 .. 0x81abc).

   The block reads up to four bytes of the caller's input and leaves the four fields of
   `GrantSlotPlan.header` behind: the 16-bit field in the spill slot 24, the channel in
   the slot 64, the rows in the slot 16, the cursor in s10, the bytes left in s7 and the
   sign-extended base in s11.

   Each byte is read through the memory-checking runtime's inline check of the shadow
   byte of its address: `a = (p + i) >> 3 + SHADOW_OFF`, `lb s, 0(a)`, and the error
   path (a call of `__asan_report_load1`) behind `beqz s` / `andi (p + i), 7` / `bge`.
   The four bytes lie in the caller's input block, whose shadow the allocator keeps
   (`AR_shadow_law`): the shadow byte of the block's first granule is the block's size
   when that is under 8 and 0 otherwise, so every check goes back to its load and no
   error path is reached. The input pointer is 16-byte aligned, so all four bytes share
   that granule.

   The walk is one run of the plain engine per size of the input: 0, 1, 2, 3, 4 .. 7
   (one run, the size and the shadow byte as atoms of the range [4, 7]) and 8 and up. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaRun PaShadow PaStep PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
YC1g YC1h YC88 GrantFrame YC45 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan Seg_head.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the model: the four bytes the read may touch, and the header they give ---- *)
(* The j-th byte of the input, 0 past its end, as `GrantSlotPlan.rd8` reads it. *)
Definition hd_byte (pl : list byte) (j : nat) : Z :=
  if (j <? length pl)%nat then GrantSlotPlan.pbz pl j else 0.
(* The shadow byte of the input block's first granule. *)
Definition hd_s (n : Z) : Z := if n <? 8 then n else 0.

Lemma hd_byte_rng : forall pl j, 0 <= hd_byte pl j < 256.
Proof.
  intros pl j. unfold hd_byte. destruct (j <? length pl)%nat; [apply Seg_head.pbz_range | lia].
Qed.

Lemma hd_byte_lt : forall pl j, (j < length pl)%nat -> hd_byte pl j = GrantSlotPlan.pbz pl j.
Proof. intros pl j H. unfold hd_byte. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity. Qed.

Lemma hd_h0 : forall pl, Z.of_nat (length pl) = 0 ->
  GrantSlotPlan.header pl = GrantSlotPlan.mkhdr 0 0 0 0.
Proof. intros pl H. apply Seg_head.header_0. lia. Qed.

Lemma hd_h1 : forall pl, Z.of_nat (length pl) = 1 ->
  GrantSlotPlan.header pl = GrantSlotPlan.mkhdr (hd_byte pl 0) 0 0 1.
Proof.
  intros pl H. rewrite (Seg_head.header_1 pl ltac:(lia)), (hd_byte_lt pl 0 ltac:(lia)). reflexivity.
Qed.

Lemma hd_h2 : forall pl, Z.of_nat (length pl) = 2 ->
  GrantSlotPlan.header pl = GrantSlotPlan.mkhdr (hd_byte pl 0 + 256 * hd_byte pl 1) 0 0 2.
Proof.
  intros pl H. rewrite (Seg_head.header_2 pl ltac:(lia)),
    (hd_byte_lt pl 0 ltac:(lia)), (hd_byte_lt pl 1 ltac:(lia)). reflexivity.
Qed.

Lemma hd_h3 : forall pl, Z.of_nat (length pl) = 3 ->
  GrantSlotPlan.header pl = GrantSlotPlan.mkhdr (hd_byte pl 0 + 256 * hd_byte pl 1) (hd_byte pl 2) 0 3.
Proof.
  intros pl H. rewrite (Seg_head.header_3 pl ltac:(lia)),
    (hd_byte_lt pl 0 ltac:(lia)), (hd_byte_lt pl 1 ltac:(lia)), (hd_byte_lt pl 2 ltac:(lia)). reflexivity.
Qed.

Lemma hd_h4 : forall pl, 4 <= Z.of_nat (length pl) ->
  GrantSlotPlan.header pl =
  GrantSlotPlan.mkhdr (hd_byte pl 0 + 256 * hd_byte pl 1) (hd_byte pl 2) (hd_byte pl 3) 4.
Proof.
  intros pl H. rewrite (Seg_head.header_4 pl ltac:(lia)),
    (hd_byte_lt pl 0 ltac:(lia)), (hd_byte_lt pl 1 ltac:(lia)),
    (hd_byte_lt pl 2 ltac:(lia)), (hd_byte_lt pl 3 ltac:(lia)). reflexivity.
Qed.

(* ---- the two machine-level readings of the header's 16-bit field ---- *)
Lemma hd_lor : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.lor (zcanon (Z.shiftl b1 8)) b0 = b0 + 256 * b1.
Proof.
  intros b0 b1 H0 H1. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
  apply Seg_head.lor16; lia.
Qed.

Lemma hd_sgn : forall x, bv_signed (Z_to_bv 64 x) = bv_swrap 64 x.
Proof.
  intros x. rewrite signed_is_swrap_unsigned, Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma hd_swrap_canon : forall x, bv_swrap 64 (zcanon x) = bv_swrap 64 x.
Proof.
  intros x. unfold bv_swrap, bv_wrap, zcanon, M64.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* the denotation of a literal and of an atom with an offset *)
Lemma hd_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z Hz. rewrite denot_lit_U. f_equal. apply U_lit. exact Hz. Qed.

Lemma hd_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  0 <= v + c < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
  intros E n v c Hn Hv Hvc. rewrite denot_lit_U. f_equal.
  rewrite U_SOff, Hn, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* `or s11, (a0 << 8), s11`: the two bytes as the header's 16-bit field. *)
Lemma hd_or8 : forall E b0 b1,
  ew E 35%nat = Z_to_bv 64 b0 -> ew E 36%nat = Z_to_bv 64 b1 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 36%nat 0) (SLit 8)) (SOff 35%nat 0)) =
  Z_to_bv 64 (b0 + 256 * b1).
Proof.
  intros E b0 b1 E35 E36 H0 H1.
  rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 35%nat b0 E35 ltac:(lia)).
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 36%nat b1 E36 ltac:(lia)), U_SLit.
  change (Z.land (zcanon 8) 63) with 8.
  rewrite hd_lor by lia.
  apply zcanon_id. unfold M64. lia.
Qed.

(* `slli 0x30` then `srai 0x30`: the 16-bit field, sign-extended. *)
Lemma hd_sext : forall E (e : sv) u,
  sv_denot E e = Z_to_bv 64 u -> 0 <= u < 65536 ->
  sv_denot E (SAlu ALU_SRA (SAlu ALU_SLL e (SLit 48)) (SLit 48)) =
  Z_to_bv 64 (GrantSlotPlan.sext16 u).
Proof.
  intros E e u He Hu.
  assert (HU : U E e = u) by (unfold U; rewrite He; apply unsigned_lit_small; lia).
  rewrite <- (Seg_head.sext16_mach u Hu).
  rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (Z.land (zcanon 48) 63) with 48.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (Z.land (zcanon 48) 63) with 48.
  rewrite HU, hd_swrap_canon, Z_to_bv64_canon, hd_sgn. reflexivity.
Qed.

(* ---- the symbolic state at 0x80944 ---- *)
(* Atoms (GrantEntrySeat.v's numbering): 0..31 the registers the call started from, 32
   SHADOW_OFF, 60 the realigned stack pointer, 516 the frame, 528 its flag, 529 its
   shadow bytes; this phase's own: 33 the input pointer, 34 the address of the shadow
   byte of its first granule, 35..38 the four bytes the read may touch, 39 the input's
   size, 40 that shadow byte, and 61 + r the register r at the cut. *)
Definition hd_sr (x20 : sv) : list sv :=
  [ SLit 0; SOff 62 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 66 0; SOff 67 0; SOff 68 0;
    SOff 2 0; SOff 60 0; SOff 71 0; SOff 72 0; SOff 73 0; SOff 74 0; SOff 75 0; SOff 76 0;
    SOff 77 0; SOff 78 0; SOff 33 0; SOff 516 0; x20; SOff 516 0; SOff 529 0; SOff 84 0;
    SOff 32 0; SOff 86 0; SOff 87 0; SOff 88 0; SOff 89 0; SOff 90 0; SOff 91 0; SOff 92 0 ].
(* The spill slots: only the frame, in the slot 176, is known here. *)
Definition hd_spill : YP09.region := ge_spill_region [YP09.mkChunk 176 (CVal 8 (SOff 516 0))].
(* The bytes of the input the read may touch, and the shadow byte that guards them. *)
Definition hd_bytes (m : nat) : list YP09.chunk :=
  map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (35 + j) 0))) (seq 0 m).
Definition hd_rin (m : nat) : YP09.region := YP09.mkRegion (Some 33%nat) 0 (Z.of_nat m) 0 0 (hd_bytes m).
Definition hd_rsh (sh : sv) : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 sh)].
Definition hd_extra (m : nat) (sh : sv) : YP09.smem :=
  match m with O => [] | S _ => [hd_rin m; hd_rsh sh] end.
(* The address of each byte's shadow byte is the address of the granule's shadow byte. *)
Definition hd_alias (m : nat) : list (sv * sv) :=
  map (fun j => (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33%nat (Z.of_nat j)) (SLit 3)) (SOff 32%nat 0),
                 SOff 34%nat 0)) (seq 0 m).
Definition hd_atoms (slo shi nlo nhi : Z) : list (nat * afact) :=
  [(33%nat, mkAF 4096 140737479966720 4); (39%nat, mkAF nlo nhi 0); (40%nat, mkAF slo shi 0)]
  ++ map (fun j => ((35 + j)%nat, mkAF 0 255 0)) (seq 0 4).
Definition hd_G (m : nat) (slo shi nlo nhi : Z) : facts :=
  mkFacts (hd_atoms slo shi nlo nhi) [] (hd_alias m).
Definition hd_mem (m : nat) (sh : sv) : YP09.smem :=
  ge_saved_region :: hd_spill :: ge_frame_region []
  :: ge_shadow_region 0 0 (ge_sh_chunks GSH_entry) :: ge_obj_regions ++ hd_extra m sh.
Definition hd_ss0 (m : nat) (sh x20 : sv) (slo shi nlo nhi : Z) : sstate :=
  mkSS GP_hdr (hd_sr x20) (hd_mem m sh) None (hd_G m slo shi nlo nhi).

Lemma hd_wf : forall m sh, (m <= 4)%nat -> YP09.regions_wf (hd_mem m sh) = true.
Proof. intros m sh Hm. destruct m as [|[|[|[|[|m]]]]]; try lia; vm_compute; reflexivity. Qed.
(* The same regions as the seat gives them, before the slot 176 is named. *)
Definition hd_mem0 (m : nat) (sh : sv) : YP09.smem :=
  ge_saved_region :: ge_spill_region [] :: ge_frame_region []
  :: ge_shadow_region 0 0 (ge_sh_chunks GSH_entry) :: ge_obj_regions ++ hd_extra m sh.

Lemma hd_wf0 : forall m sh, (m <= 4)%nat -> YP09.regions_wf (hd_mem0 m sh) = true.
Proof. intros m sh Hm. destruct m as [|[|[|[|[|m]]]]]; try lia; vm_compute; reflexivity. Qed.


Lemma hd_gsh_len : length GSH_entry = GE_NSH.
Proof. vm_compute. reflexivity. Qed.

Lemma hd_gsh_bytes : Forall (fun v => 0 <= v < 256) GSH_entry.
Proof.
  apply Forall_forall. intros v Hv.
  assert (H : forallb (fun v => andb (Z.leb 0 v) (Z.ltb v 256)) GSH_entry = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H v Hv) as Hb.
  apply andb_prop in Hb as [H1 H2]. split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

(* The environment the phase runs in. *)
Definition hd_env (cx : ecx) (fp : Z) (regs : bvmap 5 word) : env :=
  Eimg (mkEnv (fun n =>
    if (n <? 33)%nat then ew (c_E0 cx) n
    else if (n =? 33)%nat then Z_to_bv 64 (c_p cx)
    else if (n =? 34)%nat then Z_to_bv 64 (SHADOW_OFF + c_p cx / 8)
    else if (n <? 39)%nat then Z_to_bv 64 (hd_byte (c_pl cx) (n - 35))
    else if (n =? 39)%nat then Z_to_bv 64 (c_n cx)
    else if (n =? 40)%nat then Z_to_bv 64 (hd_s (c_n cx))
    else if (n =? 60)%nat then Z_to_bv 64 (c_sp1 cx)
    else if ((61 <=? n) && (n <? 93))%nat then getr regs (Z_to_bv 5 (Z.of_nat (n - 61)))
    else if (n =? 516)%nat then Z_to_bv 64 (gF cx fp)
    else if (n =? 528)%nat then Z_to_bv 64 (gFL cx fp)
    else if (n =? 529)%nat then Z_to_bv 64 (gSH cx fp)
    else Z_to_bv 64 0) (fun _ => [])).

Lemma hd_env_low : forall cx fp regs n, (n < 33)%nat -> ew (hd_env cx fp regs) n = ew (c_E0 cx) n.
Proof.
  intros cx fp regs n Hn. unfold hd_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew].
  rewrite (proj2 (Nat.ltb_lt n 33) Hn). reflexivity.
Qed.

Lemma hd_env_33 : forall cx fp regs, ew (hd_env cx fp regs) 33%nat = Z_to_bv 64 (c_p cx).
Proof. intros. unfold hd_env. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.

Lemma hd_env_34 : forall cx fp regs,
  ew (hd_env cx fp regs) 34%nat = Z_to_bv 64 (SHADOW_OFF + c_p cx / 8).
Proof. intros. unfold hd_env. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.

Lemma hd_env_b : forall cx fp regs j, (j < 4)%nat ->
  ew (hd_env cx fp regs) (35 + j)%nat = Z_to_bv 64 (hd_byte (c_pl cx) j).
Proof.
  intros cx fp regs j Hj. unfold hd_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew].
  replace ((35 + j) <? 33)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace ((35 + j) =? 33)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((35 + j) =? 34)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((35 + j) <? 39)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (35 + j - 35)%nat with j by lia. reflexivity.
Qed.

Lemma hd_env_39 : forall cx fp regs, ew (hd_env cx fp regs) 39%nat = Z_to_bv 64 (c_n cx).
Proof. intros. unfold hd_env. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.

Lemma hd_env_40 : forall cx fp regs, ew (hd_env cx fp regs) 40%nat = Z_to_bv 64 (hd_s (c_n cx)).
Proof. intros. unfold hd_env. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.

Lemma hd_env_60 : forall cx fp regs, ew (hd_env cx fp regs) 60%nat = Z_to_bv 64 (c_sp1 cx).
Proof. intros. unfold hd_env. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.

Lemma hd_env_reg : forall cx fp regs (r : bv 5), (Z.to_nat (bv_unsigned r) <> 0)%nat ->
  ew (hd_env cx fp regs) (61 + Z.to_nat (bv_unsigned r))%nat = getr regs r.
Proof.
  intros cx fp regs r Hr. pose proof (bv_unsigned_in_range 5 r) as R.
  change (bv_modulus 5) with 32 in R.
  unfold hd_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew].
  replace ((61 + Z.to_nat (bv_unsigned r)) <? 33)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace ((61 + Z.to_nat (bv_unsigned r)) =? 33)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((61 + Z.to_nat (bv_unsigned r)) =? 34)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((61 + Z.to_nat (bv_unsigned r)) <? 39)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace ((61 + Z.to_nat (bv_unsigned r)) =? 39)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((61 + Z.to_nat (bv_unsigned r)) =? 40)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((61 + Z.to_nat (bv_unsigned r)) =? 60)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((61 <=? 61 + Z.to_nat (bv_unsigned r)) && (61 + Z.to_nat (bv_unsigned r) <? 93))%nat with true
    by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  rewrite Nat2Z.inj_sub by lia. rewrite Nat2Z.inj_add, Z2Nat.id by lia. rewrite Z.mod_small; lia.
Qed.

Lemma hd_env_hi : forall cx fp regs n, (512 <= n)%nat ->
  ew (hd_env cx fp regs) n =
  if (n =? 516)%nat then Z_to_bv 64 (gF cx fp)
  else if (n =? 528)%nat then Z_to_bv 64 (gFL cx fp)
  else if (n =? 529)%nat then Z_to_bv 64 (gSH cx fp)
  else Z_to_bv 64 0.
Proof.
  intros cx fp regs n Hn. unfold hd_env. cbn [Eimg ew].
  replace ((A_TEXT <=? n) && (n <? A_LIM))%nat%bool with false
    by (symmetry; apply andb_false_intro2; apply Nat.ltb_ge; unfold A_LIM; lia).
  replace (n <? 33)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (n =? 33)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (n =? 34)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (n <? 39)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (n =? 39)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (n =? 40)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (n =? 60)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((61 <=? n) && (n <? 93))%nat with false
    by (symmetry; apply andb_false_intro2; apply Nat.ltb_ge; lia).
  reflexivity.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

Lemma hd_env_E : forall cx fp regs, ge_base B MT cx -> ge_E cx fp (hd_env cx fp regs).
Proof.
  intros cx fp regs HB.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H32 & _).
  split; [exact (hd_env_low cx fp regs)|].
  split; [unfold GA_SB; rewrite (hd_env_low cx fp regs 32%nat ltac:(lia)); exact H32|].
  split; [exact (hd_env_60 cx fp regs)|].
  unfold GA_F, GA_FL, GA_FSH. rewrite !(hd_env_hi cx fp regs) by lia. cbn.
  split; [reflexivity|]. split; reflexivity.
Qed.

(* ---- the shadow byte of the input block's first granule ---- *)
Lemma hd_shadow : forall ly S (W : world SEGS) mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
  aview SEGS (w_H W) mem (SHADOW_OFF + p / 8) = Some (hd_s n).
Proof.
  intros ly S W mem md p n HAR Hin Hn.
  destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [Hbs _].
  destruct Hbs as (Hp8 & Hrq & Hc).
  assert (Hreq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  rewrite Hreq in Hc.
  assert (Hb : 0 <= 0 < (n + 7) / 8).
  { split; [lia|]. apply Z.div_str_pos. lia. }
  pose proof (Hc 0 Hb) as H0. unfold shadow_of_addr in H0. rewrite Z.add_0_r in H0.
  rewrite H0. f_equal. unfold hd_s. destruct (Z.ltb_spec n 8) as [Hlt|Hge].
  - rewrite (Z.div_small n 8) by lia. cbn. apply Z.mod_small. lia.
  - replace (0 <? n / 8) with true by (symmetry; apply Z.ltb_lt; apply Z.div_str_pos; lia).
    reflexivity.
Qed.

(* ---- the alias that names the shadow byte of each of the four bytes ---- *)
Lemma hd_alias_ok : forall E p j,
  ew E 33%nat = Z_to_bv 64 p -> 0 <= p < 2 ^ 47 -> p mod 8 = 0 -> 0 <= j < 8 ->
  ew E 32%nat = Z_to_bv 64 SHADOW_OFF ->
  ew E 34%nat = Z_to_bv 64 (SHADOW_OFF + p / 8) ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33%nat j) (SLit 3)) (SOff 32%nat 0)) =
  sv_denot E (SOff 34%nat 0).
Proof.
  intros E p j E33 Hp Hp8 Hj E32 E34.
  assert (Hd0 : 0 <= p / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : p / 8 <= p) by (apply Z.div_le_upper_bound; lia).
  assert (Hdiv : (p + j) / 8 = p / 8).
  { pose proof (Z.div_mod p 8 ltac:(lia)) as D. rewrite Hp8, Z.add_0_r in D.
    symmetry. apply (Z.div_unique (p + j) 8 (p / 8) j); lia. }
  apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3.
  rewrite (U_SOff E 33%nat j), E33, (unsigned_lit_small p) by lia.
  rewrite (zcanon_id (p + j)) by (unfold M64; lia).
  rewrite Hdiv.
  rewrite (U_atom E 32%nat SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)).
  rewrite (U_atom E 34%nat (SHADOW_OFF + p / 8) E34 ltac:(unfold SHADOW_OFF; lia)).
  rewrite (zcanon_id (p / 8 + SHADOW_OFF)) by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* ---- a word a region of the spill slots carries ---- *)
Lemma hd_slot : forall cx (W : world SEGS) (ms : machine_state) E cs lo hi wlo whi off e v,
  YP09.region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) (YP09.mkRegion (Some 60%nat) lo hi wlo whi cs) ->
  ew E 60%nat = Z_to_bv 64 (c_sp1 cx) -> 0 <= c_sp1 cx < 2 ^ 64 ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  gslot cx W ms off v.
Proof.
  intros cx W ms E cs lo hi wlo whi off e v HR E60 Hsp Hin He Hv.
  unfold gslot. apply (rdword_of_val_mem SEGS (w_H W) (ms_mem ms)); [|exact Hv].
  change 8%nat with (N.to_nat 8).
  apply (field_of_region E (mrestrict (w_H W) (ms_mem ms)) 60%nat (c_sp1 cx) cs lo hi wlo whi
           off 8%N e v HR ltac:(rewrite E60; apply unsigned_lit_small; lia) Hin He
           ltac:(cbn [Z.of_N]; change (8 * 8) with 64; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.

(* ---- the bytes of the caller's input, kept across the run ---- *)
Lemma hd_garr : forall (W : world SEGS) (m m' : word -> option byte) p (l : list Z),
  (forall j, (j < length l)%nat ->
     mrestrict (w_H W) m' (Z_to_bv 64 (p + Z.of_nat j)) =
     mrestrict (w_H W) m (Z_to_bv 64 (p + Z.of_nat j))) ->
  garr8 SEGS (mrestrict (w_H W) m) p l -> garr8 SEGS (mrestrict (w_H W) m') p l.
Proof.
  intros W m m' p l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  apply (val_mem_moved SEGS (w_H W) (w_H W) m m' (p + Z.of_nat j) (p + Z.of_nat j) 1
           (nth j l 0)); [|exact Hv].
  intros kk Hkk. assert (kk = 0) by lia. subst kk. rewrite !Z.add_0_r.
  apply aview_eq_of. exact (Hk j Hj).
Qed.

(* ---- the right to write what the phase writes ---- *)
Lemma hd_awr : forall cx fp E m sh ly3 S3,
  ew E 60%nat = Z_to_bv 64 (c_sp1 cx) -> ew E 516%nat = Z_to_bv 64 (gF cx fp) ->
  0 <= c_sp1 cx < 2 ^ 64 ->
  spZ (c_regs cx) - 319 <= c_sp1 cx <= spZ (c_regs cx) - 288 ->
  0 <= gF cx fp < 2 ^ 64 -> frame_addr ly3 GE_CID fp = gF cx fp ->
  awr_ok E (hd_mem m sh) GE_STK (spZ (c_regs cx)) []
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(GE_CID, fp)].
Proof.
  intros cx fp E m sh ly3 S3 E60 E516 Hsp1r Hsp1 HFr HFa.
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  assert (HEXTRA : awr_ok E (hd_extra m sh) GE_STK (spZ (c_regs cx)) []
            (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(GE_CID, fp)]).
  { destruct m as [|m']; cbn [hd_extra]; [apply awr_ok_nil|].
    apply awr_ok_cons_ro; [unfold hd_rin; cbn [YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [unfold hd_rsh; cbn [YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_nil. }
  unfold hd_mem, ge_obj_regions. cbn [app].
  apply awr_ok_cons_ro; [unfold ge_saved_region; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 60%nat (c_sp1 cx - spZ (c_regs cx)));
    [ unfold hd_spill, ge_spill_region; reflexivity
    | rewrite E60; rewrite unsigned_lit_small by lia; lia
    | unfold hd_spill, ge_spill_region; cbn [YP09.r_wlo]; unfold GE_STK; lia
    | unfold hd_spill, ge_spill_region; cbn [YP09.r_whi]; lia
    | ].
  apply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 516%nat (gF cx fp));
    [ unfold ge_frame_region, fframe_region; reflexivity
    | rewrite E516; apply unsigned_lit_small; lia
    | unfold ge_frame_region, fframe_region; cbn [YP09.r_wlo YP09.r_whi];
      intros a Ha; right; right; right; exists GE_CID, fp;
      split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
      rewrite HFa; rewrite Hfb in Ha |- *; lia
    | ].
  apply awr_ok_cons_ro;
    [unfold ge_shadow_region, fshadow_region; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold got_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold uar_got_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold uar_cell_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  exact HEXTRA.
Qed.

(* ---- the addresses the phase writes: the spill slots and the frame ---- *)
Lemma hd_notw : forall cx fp E m sh a,
  ew E 60%nat = Z_to_bv 64 (c_sp1 cx) -> ew E 516%nat = Z_to_bv 64 (gF cx fp) ->
  0 <= c_sp1 cx < 2 ^ 64 -> 0 <= gF cx fp < 2 ^ 64 ->
  ~ (c_sp1 cx <= a < c_sp1 cx + 184) -> ~ (gF cx fp <= a < gF cx fp + 1024) ->
  ~ YP09.in_wrange E (hd_mem m sh) a.
Proof.
  intros cx fp E m sh a E60 E516 Hsp Hf Hns Hnf (r & Hin & Ha).
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  assert (HS : YP09.base_val E (Some 60%nat) = c_sp1 cx)
    by (cbn [YP09.base_val]; rewrite E60; apply unsigned_lit_small; lia).
  assert (HF : YP09.base_val E (Some 516%nat) = gF cx fp)
    by (cbn [YP09.base_val]; rewrite E516; apply unsigned_lit_small; lia).
  unfold hd_mem, ge_obj_regions, hd_spill, ge_spill_region, ge_saved_region,
    ge_frame_region, fframe_region, ge_shadow_region, fshadow_region,
    got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP,
    GA_SP, GA_SP1, GA_F, GA_FL, GA_FSH in Hin.
  destruct m as [|m']; cbn [hd_extra app In] in Hin; unfold hd_rin, hd_rsh in Hin;
    repeat (destruct Hin as [<-|Hin]); try (destruct Hin);
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Ha;
    rewrite ?HS, ?HF, ?Hfb in Ha; try lia.
Qed.

Lemma hd_env_516 : forall cx fp regs, ew (hd_env cx fp regs) 516%nat = Z_to_bv 64 (gF cx fp).
Proof. intros. rewrite (hd_env_hi cx fp regs 516%nat ltac:(lia)). reflexivity. Qed.

Lemma hd_env_b0 : forall cx fp regs,
  ew (hd_env cx fp regs) 35%nat = Z_to_bv 64 (hd_byte (c_pl cx) 0).
Proof. intros. exact (hd_env_b cx fp regs 0%nat ltac:(lia)). Qed.

Lemma hd_env_b1 : forall cx fp regs,
  ew (hd_env cx fp regs) 36%nat = Z_to_bv 64 (hd_byte (c_pl cx) 1).
Proof. intros. exact (hd_env_b cx fp regs 1%nat ltac:(lia)). Qed.

Lemma hd_env_b2 : forall cx fp regs,
  ew (hd_env cx fp regs) 37%nat = Z_to_bv 64 (hd_byte (c_pl cx) 2).
Proof. intros. exact (hd_env_b cx fp regs 2%nat ltac:(lia)). Qed.

Lemma hd_env_b3 : forall cx fp regs,
  ew (hd_env cx fp regs) 38%nat = Z_to_bv 64 (hd_byte (c_pl cx) 3).
Proof. intros. exact (hd_env_b cx fp regs 3%nat ltac:(lia)). Qed.

Lemma hd_env_529 : forall cx fp regs, ew (hd_env cx fp regs) 529%nat = Z_to_bv 64 (gSH cx fp).
Proof. intros. rewrite (hd_env_hi cx fp regs 529%nat ltac:(lia)). reflexivity. Qed.

Lemma hd_env_32 : forall cx fp regs, ge_base B MT cx ->
  ew (hd_env cx fp regs) 32%nat = Z_to_bv 64 SHADOW_OFF.
Proof.
  intros cx fp regs HB.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H32 & _).
  rewrite (hd_env_low cx fp regs 32%nat ltac:(lia)). exact H32.
Qed.

(* ---- the seat: the phase's machine state as the engine's symbolic state ---- *)
Lemma hd_seat : forall cx fp (W3 : world SEGS) ly3 S3 md3 k,
  ge_base B MT cx -> frames S3 = [(GE_CID, fp)] ->
  forall (ms3 : machine_state) acc (m : nat) (sh x20 : sv) slo shi nlo nhi,
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  GI_hdr B cx fp k acc ly3 S3 W3 ms3 md3 ->
  (m <= 4)%nat -> Z.of_nat m <= c_n cx ->
  sv_denot (hd_env cx fp (ms_regs ms3)) x20 = Z_to_bv 64 (c_n cx) ->
  (m <> 0%nat -> sv_denot (hd_env cx fp (ms_regs ms3)) sh = Z_to_bv 64 (hd_s (c_n cx))) ->
  nlo <= c_n cx <= nhi -> slo <= hd_s (c_n cx) <= shi ->
  st_ok_pi SEGS VAL (hd_env cx fp (ms_regs ms3)) (hd_ss0 m sh x20 slo shi nlo nhi)
    (restrict (w_H W3) ms3).
Proof.
  intros cx fp W3 ly3 S3 md3 k HB HFR ms3 acc m sh x20 slo shi nlo nhi HJ HI Hm4 Hmn Hx20 Hsh Hn Hs.
  destruct HI as (Hbody & Hk & Hacc & Hblk & Hn26 & R18 & R20 & R19 & R21 & R22 & R24 & S176).
  pose proof Hbody as (_ & _ & _ & _ & _ & _ & Hgr & _ & _ & _ & _ & Hinp).
  pose proof Hgr as (P2 & P8 & P9 & P3 & P4).
  pose proof HB as (HPRE & H10 & H11 & Hpn & _ & _ & _ & _ & _ & _ & HE0 & Husp & H32 & _).
  pose proof HJ as (HAR3 & _).
  pose proof (ge_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HSHeq).
  pose proof (ge_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (Hs0 & Hs1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 1 ltac:(lia)) as Ho1.
  pose proof (pa_obj_img 32 ltac:(lia)) as Ho32. pose proof (pa_obj_img 33 ltac:(lia)) as Ho33.
  assert (Hsp1r : 0 <= c_sp1 cx < 2 ^ 64) by lia.
  (* the input pointer and its block *)
  assert (HP : 4096 <= c_p cx /\ c_p cx + 1 <= 140737479966720 /\ c_p cx mod 16 = 0 /\
               (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3) /\
                              c_p cx + c_n cx <= alloc_ceiling /\
                              in_app (c_p cx) (req_size (c_n cx)) /\
                              off_img (c_p cx) (req_size (c_n cx)))).
  { destruct Hpn as [(Hn0 & Hp0) | (Hnp & Hin0)].
    - rewrite Hp0. unfold GE_EMPTY.
      split; [lia|]. split; [lia|]. split; [reflexivity | intros; lia].
    - assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hblk; exact Hin0).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (Hm16 & Hp4096 & Hpceil & Hpapp & _).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
      pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hin) as Hpimg.
      split; [lia|]. split; [lia|]. split; [exact Hm16|].
      intros _. split; [exact Hin|]. split; [lia|]. split; [exact Hpapp | exact Hpimg]. }
  destruct HP as (HP0 & HP1 & HP16 & HPblk).
  assert (HP8 : c_p cx mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in HP16; [|lia].
    destruct HP16 as [q Hq]. exists (2 * q). lia. }
  assert (HPd0 : 0 <= c_p cx / 8) by (apply Z.div_pos; lia).
  assert (HPd1 : c_p cx / 8 <= 17592184995840)
    by (apply Z.div_le_upper_bound; lia).
  (* the environment *)
  remember (hd_env cx fp (ms_regs ms3)) as E eqn:HEdef.
  assert (HE : ge_E cx fp E) by (subst E; apply hd_env_E; exact HB).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E33 : ew E 33%nat = Z_to_bv 64 (c_p cx)) by (subst E; apply hd_env_33).
  assert (E34 : ew E 34%nat = Z_to_bv 64 (SHADOW_OFF + c_p cx / 8)) by (subst E; apply hd_env_34).
  assert (EB : forall j, (j < 4)%nat -> ew E (35 + j)%nat = Z_to_bv 64 (hd_byte (c_pl cx) j))
    by (subst E; apply hd_env_b).
  assert (E39 : ew E 39%nat = Z_to_bv 64 (c_n cx)) by (subst E; apply hd_env_39).
  assert (E40 : ew E 40%nat = Z_to_bv 64 (hd_s (c_n cx))) by (subst E; apply hd_env_40).
  assert (EREG : forall r : bv 5, (Z.to_nat (bv_unsigned r) <> 0)%nat ->
                   ew E (61 + Z.to_nat (bv_unsigned r))%nat = getr (ms_regs ms3) r)
    by (subst E; apply hd_env_reg).
  clear HEdef.
  pose proof HE as (AG & E32 & E60 & E516 & E528 & E529).
  unfold GA_SB in E32. unfold GA_SP1 in E60. unfold GA_F in E516.
  unfold GA_FL in E528. unfold GA_FSH in E529.
  assert (HSHr : 0 <= hd_s (c_n cx) < 256).
  { unfold hd_s. destruct (Z.ltb_spec (c_n cx) 8); lia. }
  (* the register file *)
  assert (HREG : regs_ok E (hd_sr x20) (ms_regs ms3)).
  { assert (Q2 : getr (ms_regs ms3) 2 = sv_denot E (SOff 60%nat 0))
      by (rewrite ge_sv_SOff0, E60; exact P2).
    assert (Q9 : getr (ms_regs ms3) 9 = sv_denot E (SOff 60%nat 0))
      by (rewrite ge_sv_SOff0, E60; exact P9).
    assert (Q8 : getr (ms_regs ms3) 8 = sv_denot E (SOff 2%nat 0)).
    { rewrite ge_sv_SOff0, (AG 2%nat ltac:(lia)), (HE0 2%nat 2%bv eq_refl), P8.
      unfold w64, spZ. apply Z_to_bv_bv_unsigned. }
    assert (Q3 : getr (ms_regs ms3) 3 = sv_denot E (SOff 3%nat 0))
      by (rewrite ge_sv_SOff0, (AG 3%nat ltac:(lia)), (HE0 3%nat 3%bv eq_refl); exact P3).
    assert (Q4 : getr (ms_regs ms3) 4 = sv_denot E (SOff 4%nat 0))
      by (rewrite ge_sv_SOff0, (AG 4%nat ltac:(lia)), (HE0 4%nat 4%bv eq_refl); exact P4).
    assert (Q18 : getr (ms_regs ms3) 18 = sv_denot E (SOff 33%nat 0))
      by (rewrite ge_sv_SOff0, E33; exact R18).
    assert (Q19 : getr (ms_regs ms3) 19 = sv_denot E (SOff 516%nat 0))
      by (rewrite ge_sv_SOff0, E516; exact R19).
    assert (Q20 : getr (ms_regs ms3) 20 = sv_denot E x20) by (rewrite Hx20; exact R20).
    assert (Q21 : getr (ms_regs ms3) 21 = sv_denot E (SOff 516%nat 0))
      by (rewrite ge_sv_SOff0, E516; exact R21).
    assert (Q22 : getr (ms_regs ms3) 22 = sv_denot E (SOff 529%nat 0))
      by (rewrite ge_sv_SOff0, E529; exact R22).
    assert (Q24 : getr (ms_regs ms3) 24 = sv_denot E (SOff 32%nat 0))
      by (rewrite ge_sv_SOff0, E32; exact R24).
    apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r) =>
          let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
        first [ exact Q2 | exact Q9 | exact Q8 | exact Q3 | exact Q4 | exact Q18 | exact Q19
              | exact Q20 | exact Q21 | exact Q22 | exact Q24
              | rewrite getr_zero; reflexivity
              | rewrite ge_sv_SOff0; symmetry;
                lazymatch goal with |- ew _ _ = getr _ ?rr =>
                  exact (EREG rr ltac:(vm_compute; discriminate)) end ]
      | ]).
    destruct Hr. }
  (* the regions of the input's bytes and of their shadow byte *)
  assert (HBYTE : forall j, (j < m)%nat ->
    val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx + Z.of_nat j) 1 (hd_byte (c_pl cx) j)).
  { intros j Hj.
    assert (Hjl : (j < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat)
      by (rewrite length_map; unfold c_n in Hmn; lia).
    destruct (Hinp j Hjl) as [Hv _].
    replace (hd_byte (c_pl cx) j) with (nth j (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0);
      [exact Hv|].
    rewrite length_map in Hjl. rewrite (hd_byte_lt (c_pl cx) j Hjl). unfold GrantSlotPlan.pbz.
    rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
    apply (map_nth (fun b : byte => bv_unsigned b)). }
  assert (HEX : Forall (YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3))) (hd_extra m sh)).
  { destruct m as [|m']; cbn [hd_extra]; [apply Forall_nil|].
    assert (Hmpos : (0 < S m')%nat) by lia.
    assert (Hnpos : 0 < c_n cx) by lia.
    destruct (HPblk Hnpos) as (Hin & Hceil & Happ & Himg).
    apply Forall_cons.
    { unfold YP09.region_ok, hd_rin.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite E33, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc. unfold hd_bytes in Hc.
      apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
      apply (chunk_ok_val SEGS E _ (c_p cx) (Z.of_nat j) 1 (SOff (35 + j)%nat 0)
               (hd_byte (c_pl cx) j)).
      - rewrite ge_sv_SOff0, (EB j ltac:(lia)). reflexivity.
      - pose proof (hd_byte_rng (c_pl cx) j). change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      - cbn. lia.
      - cbn [N.to_nat]. apply HBYTE. lia. }
    apply Forall_cons; [|apply Forall_nil].
    { unfold YP09.region_ok, hd_rsh.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite E34, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (SHADOW_OFF + c_p cx / 8) 0 1 sh (hd_s (c_n cx))).
      - exact (Hsh ltac:(discriminate)).
      - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      - cbn. lia.
      - cbn [N.to_nat]. rewrite Z.add_0_r.
        exact (proj1 (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms3) (SHADOW_OFF + c_p cx / 8)
                 (hd_s (c_n cx))
                 (hd_shadow ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR3 Hin Hnpos))). } }
  (* the seat, with no spill chunks, then the slot the phase knows *)
  assert (HS0 : st_ok_pi SEGS VAL E
    (ge_ss cx fp GP_hdr (hd_sr x20) GSH_entry (ge_slot_chunks []) [] 0 0 (hd_extra m sh)
       (hd_G m slo shi nlo nhi)) (restrict (w_H W3) ms3)).
  { apply (ge_seat B MT LAWS TL TLF cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR);
      [ exact HE | exact HEI | exact Hbody | exact HREG | apply Forall_nil | apply Forall_nil
      | lia | lia | | exact HEX | | | ].
    - change (YP09.regions_wf (hd_mem0 m sh) = true). apply hd_wf0. exact Hm4.
    - destruct m as [|m']; cbn [hd_extra YP09.pairwise_disjoint YP09.all_disjoint]; repeat split.
      assert (Hnpos : 0 < c_n cx) by lia.
      destruct (HPblk Hnpos) as (Hin & Hceil & Happ & Himg).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
      unfold YP09.extent_disjoint, hd_rin, hd_rsh.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite E33, E34, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
    - destruct m as [|m']; cbn [hd_extra].
      + apply Forall_forall. intros r _. exact I.
      + assert (Hnpos : 0 < c_n cx) by lia.
        destruct (HPblk Hnpos) as (Hin & Hceil & Happ & Himg).
        pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ GE_CID fp HAR3 Hin
                      (ge_fin fp S3 HFR)) as Hpf.
        rewrite (ge_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) in Hpf.
        change (fs_frame_bytes GE_CID) with 1024 in Hpf.
        unfold zdisjoint in Hpf. cbn [fst snd] in Hpf.
        destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 (ge_fin fp S3 HFR)) as (HFal & _).
        rewrite (ge_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) in HFal.
        assert (HF8 : gF cx fp mod 8 = 0).
        { apply Z.mod_divide; [lia|]. apply Z.mod_divide in HFal; [|lia].
          destruct HFal as [q Hq]. exists (4 * q). lia. }
        pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)) as HFq. rewrite HF8, Z.add_0_r in HFq.
        pose proof (Z.div_mod (c_p cx) 8 ltac:(lia)) as HPq. rewrite HP8, Z.add_0_r in HPq.
        assert (HFd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
        assert (HFd1 : gF cx fp / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
        pose proof (ge_base_sp B MT cx fp HB E HE) as Ub2.
        cbn [YP09.base_val] in Ub2. unfold GA_SP in Ub2.
        assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> YP09.base_val E (Some n) = VAL n).
        { intros n Hn'. cbn [YP09.base_val]. rewrite (img_env_atomP E n HEI Hn').
          apply unsigned_lit_small. apply pa_val_range. }
        unfold ge_regions0, ge_saved_region, ge_spill_region, ge_frame_region, fframe_region,
          ge_shadow_region, fshadow_region, ge_obj_regions, got_regionP, bcell_regionP,
          uar_got_regionP, uar_cell_regionP, hd_rin, hd_rsh,
          GA_SP, GA_SP1, GA_F, GA_FL, GA_FSH.
        repeat apply Forall_cons; try apply Forall_nil;
          cbn [YP09.all_disjoint]; repeat split; unfold YP09.extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi].
        all: rewrite ?Ub2, ?(EA (A_OBJ 1)), ?(EA (A_OBJ 32)), ?(EA (A_OBJ 0)), ?(EA (A_OBJ 33))
               by (unfold A_OBJ, A_TEXT, A_LIM; lia).
        all: cbn [YP09.base_val]; rewrite ?Ub2, ?E33, ?E34, ?E60, ?E516, ?E529.
        all: unfold w64; rewrite ?unsigned_lit_small by (unfold SHADOW_OFF; lia).
        all: change (fs_frame_bytes GE_CID) with 1024; change (1024 / 8) with 128.
        all: rewrite ?HSHeq.
        all: unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia.
    - split; [|split; [exact I|]].
      + unfold hd_G, hd_atoms. cbn [f_atoms app map seq atoms_ok]. unfold afact_ok.
        cbn [af_lo af_hi af_al2].
        rewrite E33, E39, E40, !(EB 0%nat), !(EB 1%nat), !(EB 2%nat), !(EB 3%nat) by lia.
        change (35 + 0)%nat with 35%nat in *. change (35 + 1)%nat with 36%nat in *.
        change (35 + 2)%nat with 37%nat in *. change (35 + 3)%nat with 38%nat in *.
        rewrite !unsigned_lit_small by (pose proof (hd_byte_rng (c_pl cx) 0);
          pose proof (hd_byte_rng (c_pl cx) 1); pose proof (hd_byte_rng (c_pl cx) 2);
          pose proof (hd_byte_rng (c_pl cx) 3); lia).
        change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
        pose proof (hd_byte_rng (c_pl cx) 0). pose proof (hd_byte_rng (c_pl cx) 1).
        pose proof (hd_byte_rng (c_pl cx) 2). pose proof (hd_byte_rng (c_pl cx) 3).
        repeat match goal with |- _ /\ _ => split end; try lia.
      + unfold hd_G. cbn [f_alias].
        destruct m as [|[|[|[|[|m']]]]]; try lia; cbn [hd_alias map seq alias_ok];
          repeat split;
          apply (hd_alias_ok E (c_p cx)); try assumption; try lia. }
  (* the slot the phase knows: the frame, in the slot 176 *)
  pose proof (st_ok_pi_region_nth E _ _ 1%nat _ HS0 eq_refl) as RSP.
  cbn [ms_mem restrict] in RSP.
  assert (RS : YP09.region_ok SEGS E (ms_mem (restrict (w_H W3) ms3)) hd_spill).
  { cbn [ms_mem restrict]. destruct RSP as (Hr1 & Hr2 & Hr3 & _).
    unfold hd_spill, ge_spill_region in *.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
    split; [exact Hr1|]. split; [exact Hr2|]. split; [exact Hr3|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (YP09.base_val E (Some 60%nat)) 176 8 (SOff 516%nat 0) (gF cx fp)).
    - rewrite ge_sv_SOff0, E516. reflexivity.
    - cbn [Z.of_N]. change (8 * 8) with 64. lia.
    - cbn [Z.of_N]. lia.
    - cbn [YP09.base_val N.to_nat]. rewrite E60, unsigned_lit_small by lia.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S176. }
  pose proof (ast_ok_pi_set_region E _ _ 1%nat _ hd_spill HS0 eq_refl eq_refl
    ltac:(change (YP09.regions_wf (hd_mem m sh) = true); apply hd_wf; exact Hm4) RS) as HS1.
  exact HS1.
Qed.

(* ---- the landing: the engine's state at 0x8098c back as the phase's memory ---- *)
Lemma hd_fin : forall cx fp (W3 : world SEGS) ly3 S3 k,
  ge_base B MT cx -> frames S3 = [(GE_CID, fp)] ->
  forall (ms4 : machine_state) md4 E sr extra G,
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms4) md4 k ->
  ge_E cx fp E ->
  st_ok_pi SEGS VAL E
    (mkSS GP_mallocT sr (ge_saved_region :: ge_spill_region [] :: ge_frame_region []
       :: ge_shadow_region 0 0 (ge_sh_chunks GSH_entry) :: ge_obj_regions ++ extra) None G)
    (restrict (w_H W3) ms4) ->
  sr_get sr 2 = SOff GA_SP1 0 -> sr_get sr 8 = SOff GA_SP 0 -> sr_get sr 9 = SOff GA_SP1 0 ->
  sr_get sr 3 = SOff 3%nat 0 -> sr_get sr 4 = SOff 4%nat 0 ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms4)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  ge_body cx fp GP_mallocT W3 ms4 GSH_entry.
Proof.
  intros cx fp W3 ly3 S3 k HB HFR ms4 md4 E sr extra G HJ HE HS H2 H8 H9 H3 H4 Hgarr.
  apply (ge_land B MT LAWS cx fp W3 ms4 ly3 S3 md4 k HB HJ HFR E GP_mallocT sr GSH_entry []
           [] 0 0 extra G HE); try assumption.
  - exact hd_gsh_len.
  - exact hd_gsh_bytes.
Qed.

(* ---- the invariant at 0x8098c, from what the run leaves ---- *)
Lemma hd_out : forall cx fp k acc ly3 S3 (W3 : world SEGS) (ms4 : machine_state) md4,
  ge_body cx fp GP_mallocT W3 ms4 GSH_entry ->
  k <= 0 -> acc <= 0 ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) -> c_n cx < 2 ^ 26 ->
  getr (ms_regs ms4) 19 = w64 (gF cx fp) -> getr (ms_regs ms4) 21 = w64 (gF cx fp) ->
  getr (ms_regs ms4) 22 = w64 (gSH cx fp) -> getr (ms_regs ms4) 24 = w64 SHADOW_OFF ->
  getr (ms_regs ms4) 26 =
    w64 (c_p cx + Z.of_nat (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) ->
  getr (ms_regs ms4) 23 =
    w64 (c_n cx - Z.of_nat (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) ->
  getr (ms_regs ms4) 27 = w64 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))) ->
  gslot cx W3 ms4 16 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) ->
  gslot cx W3 ms4 24 (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx))) ->
  gslot cx W3 ms4 64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) ->
  gslot cx W3 ms4 176 (gF cx fp) ->
  GI_mallocT B cx fp k acc ly3 S3 W3 ms4 md4.
Proof. intros. unfold GI_mallocT. repeat (split; [assumption|]). assumption. Qed.

(* A register of the engine's state, with its value as a symbolic expression. *)
Ltac hd_reg HS r H :=
  pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as H;
  cbn [ms_regs restrict] in H;
  lazymatch type of H with context [sr_get ?s ?rr] =>
    let v := eval vm_compute in (sr_get s rr) in change (sr_get s rr) with v in H end.
Ltac hd_in := cbn [In]; repeat (first [now left | right]).

(* ---- the phase ---- *)
Theorem ge_hdr_read : forall POST,
  ge_from B MT POST (GI_mallocT B) -> ge_from B MT POST (GI_hdr B).
Proof.
  intros POST HM cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  unfold ge_from in HM.
  pose proof HI as (Hbody & Hk & Hacc & Hblk & Hn26 & R18 & R20 & R19 & R21 & R22 & R24 & S176).
  pose proof Hbody as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinp).
  pose proof HB as (HPRE & H10 & H11 & Hpn & _ & _ & _ & _ & _ & _ & HE0 & Husp & H32 & _).
  pose proof HJ as (HAR3 & _).
  pose proof (ge_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR)
    as (HF0 & HFc & HFia & HFo & HSHeq).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (hd_byte_rng (c_pl cx) 0) as Hb0. pose proof (hd_byte_rng (c_pl cx) 1) as Hb1.
  pose proof (hd_byte_rng (c_pl cx) 2) as Hb2. pose proof (hd_byte_rng (c_pl cx) 3) as Hb3.
  assert (HE : ge_E cx fp (hd_env cx fp (ms_regs ms3))) by (apply hd_env_E; exact HB).
  assert (HEI : img_env VAL A_LIM (hd_env cx fp (ms_regs ms3))) by apply Eimg_env.
  assert (HFA : frame_addr ly3 GE_CID fp = gF cx fp)
    by (apply (ge_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ)).
  assert (HN0 : 0 <= c_n cx) by (unfold c_n; lia).
  (* the caller's input block, when the input is not empty *)
  assert (HPblk : 0 < c_n cx ->
            4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\
            (gF cx fp + 1024 <= c_p cx \/ c_p cx + c_n cx <= gF cx fp)).
  { intros Hpos. destruct Hpn as [(Hn0 & _) | (Hnp & Hin0)]; [lia|].
    assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hblk; exact Hin0).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ GE_CID fp HAR3 Hin
                  (ge_fin fp S3 HFR)) as Hpf.
    rewrite HFA in Hpf. change (fs_frame_bytes GE_CID) with 1024 in Hpf.
    unfold zdisjoint in Hpf. cbn [fst snd] in Hpf.
    split; [lia|]. split; lia. }
  assert (HP64 : 4096 <= c_p cx /\ c_p cx + 8 <= 2 ^ 47).
  { destruct Hpn as [(Hn0 & Hp0) | (Hnp & Hin0)].
    - rewrite Hp0. unfold GE_EMPTY. lia.
    - assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hblk; exact Hin0).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hp4096 & Hpceil & _).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [Hq1 _]. lia. }
  destruct HP64 as (HP4096 & HP47).
  assert (Hcase : c_n cx = 0 \/ c_n cx = 1 \/ c_n cx = 2 \/ c_n cx = 3 \/
                  (4 <= c_n cx <= 7) \/ 8 <= c_n cx) by lia.
  destruct Hcase as [Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]].

  - (* the input is empty: no byte is read, every field is 0 *)
    pose proof (hd_seat cx fp W3 ly3 S3 md3 k HB HFR ms3 acc 0%nat (SLit 0) (SLit 0) 0 7 0 0
                  HJ HI ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
                  ltac:(rewrite Hc; apply hd_lit; lia)
                  ltac:(intros Hne; exfalso; apply Hne; reflexivity)
                  ltac:(lia) ltac:(unfold hd_s; rewrite Hc; cbn; lia)) as HS.
    pose proof (hd_h0 (c_pl cx) ltac:(unfold c_n in Hc; lia)) as Hhdr.
    paj_run_to_sh RUNTOP HS HJ 0x2dc.
    { apply (hd_awr cx fp (hd_env cx fp (ms_regs ms3)) 0%nat (SLit 0) ly3 S3);
        [ apply hd_env_60 | apply hd_env_516 | lia | lia | lia | exact HFA ]. }
    hd_reg HS (19%bv : bv 5) Q19. hd_reg HS (21%bv : bv 5) Q21.
    hd_reg HS (22%bv : bv 5) Q22. hd_reg HS (24%bv : bv 5) Q24.
    hd_reg HS (23%bv : bv 5) Q23. hd_reg HS (26%bv : bv 5) Q26.
    hd_reg HS (27%bv : bv 5) Q27.
    pose proof (st_ok_pi_region_nth (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ HS eq_refl) as RSP.
    cbn [ms_mem restrict] in RSP.
    pose proof (ast_ok_pi_set_region (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ (ge_spill_region [])
                  HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
                  ltac:(cbn [ms_mem restrict]; destruct RSP as (Ha & Hb & Hw & _);
                        unfold ge_spill_region;
                        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
                        split; [exact Ha|]; split; [exact Hb|]; split;
                        [exact Hw | apply Forall_nil])) as HS2.
    lazymatch goal with |- SRr _ _ (mkCfg ?ms4 ?md4) _ =>
      apply (HM cx fp k acc ly3 S3 W3 ms4 md4 HB HJ HFR HMO);
      apply (hd_out cx fp k acc ly3 S3 W3 ms4 md4) end.
    + apply (hd_fin cx fp W3 ly3 S3 k HB HFR _ _ (hd_env cx fp (ms_regs ms3)) _ _ _ HJ HE HS2);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | ].
      apply (hd_garr W3 (ms_mem ms3) _ (c_p cx) _); [|exact Hinp].
      intros j Hj. rewrite length_map in Hj. exfalso. unfold c_n in Hc. lia.
    + lia.
    + lia.
    + exact Hblk.
    + exact Hn26.
    + rewrite Q19, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q21, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q22, ge_sv_SOff0, hd_env_529. reflexivity.
    + rewrite Q24, ge_sv_SOff0, (hd_env_32 cx fp (ms_regs ms3) HB). reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q26, (hd_off _ 33%nat (c_p cx) 0 (hd_env_33 cx fp (ms_regs ms3)) ltac:(lia)
                      ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q23, (hd_lit _ 0 ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. unfold GrantSlotPlan.h_base.
      cbn [GrantSlotPlan.h_u16 GrantSlotPlan.sext16].
      rewrite Q27, (hd_lit _ 0 ltac:(lia)); try reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_rows].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 16 (SLit 0) 0 RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply hd_lit; lia) ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_u16].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 24 (SLit 0) 0 RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply hd_lit; lia) ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_in].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 64 (SLit 0) 0 RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply hd_lit; lia) ltac:(lia)).
    + apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 176 (SOff 516%nat 0)
               (gF cx fp) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(rewrite ge_sv_SOff0; apply hd_env_516) ltac:(lia)).

  - (* one byte: the low half of the 16-bit field *)
    pose proof (hd_seat cx fp W3 ly3 S3 md3 k HB HFR ms3 acc 1%nat (SLit 1) (SLit 1) 0 7 1 1
                  HJ HI ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
                  ltac:(rewrite Hc; apply hd_lit; lia)
                  ltac:(intros _; rewrite Hc; change (hd_s 1) with 1; apply hd_lit; lia)
                  ltac:(lia) ltac:(rewrite Hc; change (hd_s 1) with 1; lia)) as HS.
    pose proof (hd_h1 (c_pl cx) ltac:(unfold c_n in Hc; lia)) as Hhdr.
    destruct (HPblk ltac:(lia)) as (HpA & HpB & HpC).
    paj_run_to_sh RUNTOP HS HJ 0x2dc.
    { apply (hd_awr cx fp (hd_env cx fp (ms_regs ms3)) 1%nat (SLit 1) ly3 S3);
        [ apply hd_env_60 | apply hd_env_516 | lia | lia | lia | exact HFA ]. }
    hd_reg HS (19%bv : bv 5) Q19. hd_reg HS (21%bv : bv 5) Q21.
    hd_reg HS (22%bv : bv 5) Q22. hd_reg HS (24%bv : bv 5) Q24.
    hd_reg HS (23%bv : bv 5) Q23. hd_reg HS (26%bv : bv 5) Q26.
    hd_reg HS (27%bv : bv 5) Q27.
    pose proof (st_ok_pi_region_nth (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ HS eq_refl) as RSP.
    cbn [ms_mem restrict] in RSP.
    pose proof (ast_ok_pi_set_region (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ (ge_spill_region [])
                  HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
                  ltac:(cbn [ms_mem restrict]; destruct RSP as (Ha & Hb & Hw & _);
                        unfold ge_spill_region;
                        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
                        split; [exact Ha|]; split; [exact Hb|]; split;
                        [exact Hw | apply Forall_nil])) as HS2.
    lazymatch goal with |- SRr _ _ (mkCfg ?ms4 ?md4) _ =>
      apply (HM cx fp k acc ly3 S3 W3 ms4 md4 HB HJ HFR HMO);
      apply (hd_out cx fp k acc ly3 S3 W3 ms4 md4) end.
    + apply (hd_fin cx fp W3 ly3 S3 k HB HFR _ _ (hd_env cx fp (ms_regs ms3)) _ _ _ HJ HE HS2);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | ].
      apply (hd_garr W3 (ms_mem ms3) _ (c_p cx) _); [|exact Hinp].
      intros j Hj. rewrite length_map in Hj.
      apply (HFr (Z_to_bv 64 (c_p cx + Z.of_nat j))).
      rewrite unsigned_lit_small by (unfold c_n in *; lia).
      apply (hd_notw cx fp (hd_env cx fp (ms_regs ms3)) 1%nat (SLit 1));
        [ apply hd_env_60 | apply hd_env_516 | lia | lia
        | unfold c_n in *; lia | unfold c_n in *; lia ].
    + lia.
    + lia.
    + exact Hblk.
    + exact Hn26.
    + rewrite Q19, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q21, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q22, ge_sv_SOff0, hd_env_529. reflexivity.
    + rewrite Q24, ge_sv_SOff0, (hd_env_32 cx fp (ms_regs ms3) HB). reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q26, (hd_off _ 33%nat (c_p cx) 1 (hd_env_33 cx fp (ms_regs ms3)) ltac:(lia)
                      ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q23, (hd_lit _ 0 ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. unfold GrantSlotPlan.h_base. cbn [GrantSlotPlan.h_u16].
      rewrite (Seg_head.sext16_small (hd_byte (c_pl cx) 0) ltac:(lia)).
      rewrite Q27, ge_sv_SOff0, hd_env_b0. reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_rows].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 16 (SLit 0) 0 RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply hd_lit; lia) ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_u16].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 24 (SOff 35%nat 0)
               (hd_byte (c_pl cx) 0) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia)
               ltac:(hd_in) ltac:(rewrite ge_sv_SOff0; apply hd_env_b0) ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_in].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 64 (SLit 0) 0 RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply hd_lit; lia) ltac:(lia)).
    + apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 176 (SOff 516%nat 0)
               (gF cx fp) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(rewrite ge_sv_SOff0; apply hd_env_516) ltac:(lia)).

  - (* two bytes: the whole 16-bit field *)
    pose proof (hd_seat cx fp W3 ly3 S3 md3 k HB HFR ms3 acc 2%nat (SLit 2) (SLit 2) 0 7 2 2
                  HJ HI ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
                  ltac:(rewrite Hc; apply hd_lit; lia)
                  ltac:(intros _; rewrite Hc; change (hd_s 2) with 2; apply hd_lit; lia)
                  ltac:(lia) ltac:(rewrite Hc; change (hd_s 2) with 2; lia)) as HS.
    pose proof (hd_h2 (c_pl cx) ltac:(unfold c_n in Hc; lia)) as Hhdr.
    destruct (HPblk ltac:(lia)) as (HpA & HpB & HpC).
    paj_run_to_sh RUNTOP HS HJ 0x2dc.
    { apply (hd_awr cx fp (hd_env cx fp (ms_regs ms3)) 2%nat (SLit 2) ly3 S3);
        [ apply hd_env_60 | apply hd_env_516 | lia | lia | lia | exact HFA ]. }
    hd_reg HS (19%bv : bv 5) Q19. hd_reg HS (21%bv : bv 5) Q21.
    hd_reg HS (22%bv : bv 5) Q22. hd_reg HS (24%bv : bv 5) Q24.
    hd_reg HS (23%bv : bv 5) Q23. hd_reg HS (26%bv : bv 5) Q26.
    hd_reg HS (27%bv : bv 5) Q27.
    pose proof (st_ok_pi_region_nth (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ HS eq_refl) as RSP.
    cbn [ms_mem restrict] in RSP.
    pose proof (ast_ok_pi_set_region (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ (ge_spill_region [])
                  HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
                  ltac:(cbn [ms_mem restrict]; destruct RSP as (Ha & Hb & Hw & _);
                        unfold ge_spill_region;
                        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
                        split; [exact Ha|]; split; [exact Hb|]; split;
                        [exact Hw | apply Forall_nil])) as HS2.
    lazymatch goal with |- SRr _ _ (mkCfg ?ms4 ?md4) _ =>
      apply (HM cx fp k acc ly3 S3 W3 ms4 md4 HB HJ HFR HMO);
      apply (hd_out cx fp k acc ly3 S3 W3 ms4 md4) end.
    + apply (hd_fin cx fp W3 ly3 S3 k HB HFR _ _ (hd_env cx fp (ms_regs ms3)) _ _ _ HJ HE HS2);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | ].
      apply (hd_garr W3 (ms_mem ms3) _ (c_p cx) _); [|exact Hinp].
      intros j Hj. rewrite length_map in Hj.
      apply (HFr (Z_to_bv 64 (c_p cx + Z.of_nat j))).
      rewrite unsigned_lit_small by (unfold c_n in *; lia).
      apply (hd_notw cx fp (hd_env cx fp (ms_regs ms3)) 2%nat (SLit 2));
        [ apply hd_env_60 | apply hd_env_516 | lia | lia
        | unfold c_n in *; lia | unfold c_n in *; lia ].
    + lia.
    + lia.
    + exact Hblk.
    + exact Hn26.
    + rewrite Q19, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q21, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q22, ge_sv_SOff0, hd_env_529. reflexivity.
    + rewrite Q24, ge_sv_SOff0, (hd_env_32 cx fp (ms_regs ms3) HB). reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q26, (hd_off _ 33%nat (c_p cx) 2 (hd_env_33 cx fp (ms_regs ms3)) ltac:(lia)
                      ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q23, (hd_lit _ 0 ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. unfold GrantSlotPlan.h_base. cbn [GrantSlotPlan.h_u16].
      rewrite Q27, (hd_sext (hd_env cx fp (ms_regs ms3)) _
                      (hd_byte (c_pl cx) 0 + 256 * hd_byte (c_pl cx) 1)
                      (hd_or8 (hd_env cx fp (ms_regs ms3)) _ _
                         (hd_env_b0 cx fp (ms_regs ms3)) (hd_env_b1 cx fp (ms_regs ms3)) Hb0 Hb1)
                      ltac:(lia)); try reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_rows].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 16 (SLit 0) 0 RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply hd_lit; lia) ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_u16].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 24
               (SAlu ALU_OR (SAlu ALU_SLL (SOff 36%nat 0) (SLit 8)) (SOff 35%nat 0))
               (hd_byte (c_pl cx) 0 + 256 * hd_byte (c_pl cx) 1) RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply (hd_or8 (hd_env cx fp (ms_regs ms3)));
                     [ apply hd_env_b0 | apply hd_env_b1 | lia | lia ])
               ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_in].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 64 (SLit 0) 0 RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply hd_lit; lia) ltac:(lia)).
    + apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 176 (SOff 516%nat 0)
               (gF cx fp) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(rewrite ge_sv_SOff0; apply hd_env_516) ltac:(lia)).

  - (* three bytes: the 16-bit field and the channel *)
    pose proof (hd_seat cx fp W3 ly3 S3 md3 k HB HFR ms3 acc 3%nat (SLit 3) (SLit 3) 0 7 3 3
                  HJ HI ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
                  ltac:(rewrite Hc; apply hd_lit; lia)
                  ltac:(intros _; rewrite Hc; change (hd_s 3) with 3; apply hd_lit; lia)
                  ltac:(lia) ltac:(rewrite Hc; change (hd_s 3) with 3; lia)) as HS.
    pose proof (hd_h3 (c_pl cx) ltac:(unfold c_n in Hc; lia)) as Hhdr.
    destruct (HPblk ltac:(lia)) as (HpA & HpB & HpC).
    paj_run_to_sh RUNTOP HS HJ 0x2dc.
    { apply (hd_awr cx fp (hd_env cx fp (ms_regs ms3)) 3%nat (SLit 3) ly3 S3);
        [ apply hd_env_60 | apply hd_env_516 | lia | lia | lia | exact HFA ]. }
    hd_reg HS (19%bv : bv 5) Q19. hd_reg HS (21%bv : bv 5) Q21.
    hd_reg HS (22%bv : bv 5) Q22. hd_reg HS (24%bv : bv 5) Q24.
    hd_reg HS (23%bv : bv 5) Q23. hd_reg HS (26%bv : bv 5) Q26.
    hd_reg HS (27%bv : bv 5) Q27.
    pose proof (st_ok_pi_region_nth (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ HS eq_refl) as RSP.
    cbn [ms_mem restrict] in RSP.
    pose proof (ast_ok_pi_set_region (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ (ge_spill_region [])
                  HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
                  ltac:(cbn [ms_mem restrict]; destruct RSP as (Ha & Hb & Hw & _);
                        unfold ge_spill_region;
                        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
                        split; [exact Ha|]; split; [exact Hb|]; split;
                        [exact Hw | apply Forall_nil])) as HS2.
    lazymatch goal with |- SRr _ _ (mkCfg ?ms4 ?md4) _ =>
      apply (HM cx fp k acc ly3 S3 W3 ms4 md4 HB HJ HFR HMO);
      apply (hd_out cx fp k acc ly3 S3 W3 ms4 md4) end.
    + apply (hd_fin cx fp W3 ly3 S3 k HB HFR _ _ (hd_env cx fp (ms_regs ms3)) _ _ _ HJ HE HS2);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | ].
      apply (hd_garr W3 (ms_mem ms3) _ (c_p cx) _); [|exact Hinp].
      intros j Hj. rewrite length_map in Hj.
      apply (HFr (Z_to_bv 64 (c_p cx + Z.of_nat j))).
      rewrite unsigned_lit_small by (unfold c_n in *; lia).
      apply (hd_notw cx fp (hd_env cx fp (ms_regs ms3)) 3%nat (SLit 3));
        [ apply hd_env_60 | apply hd_env_516 | lia | lia
        | unfold c_n in *; lia | unfold c_n in *; lia ].
    + lia.
    + lia.
    + exact Hblk.
    + exact Hn26.
    + rewrite Q19, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q21, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q22, ge_sv_SOff0, hd_env_529. reflexivity.
    + rewrite Q24, ge_sv_SOff0, (hd_env_32 cx fp (ms_regs ms3) HB). reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q26, (hd_off _ 33%nat (c_p cx) 3 (hd_env_33 cx fp (ms_regs ms3)) ltac:(lia)
                      ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q23, (hd_lit _ 0 ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. unfold GrantSlotPlan.h_base. cbn [GrantSlotPlan.h_u16].
      rewrite Q27, (hd_sext (hd_env cx fp (ms_regs ms3)) _
                      (hd_byte (c_pl cx) 0 + 256 * hd_byte (c_pl cx) 1)
                      (hd_or8 (hd_env cx fp (ms_regs ms3)) _ _
                         (hd_env_b0 cx fp (ms_regs ms3)) (hd_env_b1 cx fp (ms_regs ms3)) Hb0 Hb1)
                      ltac:(lia)); try reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_rows].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 16 (SLit 0) 0 RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply hd_lit; lia) ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_u16].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 24
               (SAlu ALU_OR (SAlu ALU_SLL (SOff 36%nat 0) (SLit 8)) (SOff 35%nat 0))
               (hd_byte (c_pl cx) 0 + 256 * hd_byte (c_pl cx) 1) RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply (hd_or8 (hd_env cx fp (ms_regs ms3)));
                     [ apply hd_env_b0 | apply hd_env_b1 | lia | lia ])
               ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_in].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 64 (SOff 37%nat 0)
               (hd_byte (c_pl cx) 2) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia)
               ltac:(hd_in) ltac:(rewrite ge_sv_SOff0; apply hd_env_b2) ltac:(lia)).
    + apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 176 (SOff 516%nat 0)
               (gF cx fp) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(rewrite ge_sv_SOff0; apply hd_env_516) ltac:(lia)).

  - (* four to seven bytes: the whole header, the granule's shadow byte is the size *)
    pose proof (hd_seat cx fp W3 ly3 S3 md3 k HB HFR ms3 acc 4%nat (SOff 40%nat 0) (SOff 39%nat 0)
                  4 7 4 7 HJ HI ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
                  ltac:(rewrite ge_sv_SOff0; apply hd_env_39)
                  ltac:(intros _; rewrite ge_sv_SOff0; apply hd_env_40)
                  ltac:(lia)
                  ltac:(unfold hd_s; rewrite (proj2 (Z.ltb_lt (c_n cx) 8) ltac:(lia)); lia)) as HS.
    pose proof (hd_h4 (c_pl cx) ltac:(unfold c_n in Hc; lia)) as Hhdr.
    destruct (HPblk ltac:(lia)) as (HpA & HpB & HpC).
    paj_run_to_sh RUNTOP HS HJ 0x2dc.
    { apply (hd_awr cx fp (hd_env cx fp (ms_regs ms3)) 4%nat (SOff 40%nat 0) ly3 S3);
        [ apply hd_env_60 | apply hd_env_516 | lia | lia | lia | exact HFA ]. }
    hd_reg HS (19%bv : bv 5) Q19. hd_reg HS (21%bv : bv 5) Q21.
    hd_reg HS (22%bv : bv 5) Q22. hd_reg HS (24%bv : bv 5) Q24.
    hd_reg HS (23%bv : bv 5) Q23. hd_reg HS (26%bv : bv 5) Q26.
    hd_reg HS (27%bv : bv 5) Q27.
    pose proof (st_ok_pi_region_nth (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ HS eq_refl) as RSP.
    cbn [ms_mem restrict] in RSP.
    pose proof (ast_ok_pi_set_region (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ (ge_spill_region [])
                  HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
                  ltac:(cbn [ms_mem restrict]; destruct RSP as (Ha & Hb & Hw & _);
                        unfold ge_spill_region;
                        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
                        split; [exact Ha|]; split; [exact Hb|]; split;
                        [exact Hw | apply Forall_nil])) as HS2.
    lazymatch goal with |- SRr _ _ (mkCfg ?ms4 ?md4) _ =>
      apply (HM cx fp k acc ly3 S3 W3 ms4 md4 HB HJ HFR HMO);
      apply (hd_out cx fp k acc ly3 S3 W3 ms4 md4) end.
    + apply (hd_fin cx fp W3 ly3 S3 k HB HFR _ _ (hd_env cx fp (ms_regs ms3)) _ _ _ HJ HE HS2);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | ].
      apply (hd_garr W3 (ms_mem ms3) _ (c_p cx) _); [|exact Hinp].
      intros j Hj. rewrite length_map in Hj.
      apply (HFr (Z_to_bv 64 (c_p cx + Z.of_nat j))).
      rewrite unsigned_lit_small by (unfold c_n in *; lia).
      apply (hd_notw cx fp (hd_env cx fp (ms_regs ms3)) 4%nat (SOff 40%nat 0));
        [ apply hd_env_60 | apply hd_env_516 | lia | lia
        | unfold c_n in *; lia | unfold c_n in *; lia ].
    + lia.
    + lia.
    + exact Hblk.
    + exact Hn26.
    + rewrite Q19, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q21, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q22, ge_sv_SOff0, hd_env_529. reflexivity.
    + rewrite Q24, ge_sv_SOff0, (hd_env_32 cx fp (ms_regs ms3) HB). reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q26, (hd_off _ 33%nat (c_p cx) 4 (hd_env_33 cx fp (ms_regs ms3)) ltac:(lia)
                      ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q23, (hd_off _ 39%nat (c_n cx) (-4) (hd_env_39 cx fp (ms_regs ms3)) ltac:(lia)
                      ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. unfold GrantSlotPlan.h_base. cbn [GrantSlotPlan.h_u16].
      rewrite Q27, (hd_sext (hd_env cx fp (ms_regs ms3)) _
                      (hd_byte (c_pl cx) 0 + 256 * hd_byte (c_pl cx) 1)
                      (hd_or8 (hd_env cx fp (ms_regs ms3)) _ _
                         (hd_env_b0 cx fp (ms_regs ms3)) (hd_env_b1 cx fp (ms_regs ms3)) Hb0 Hb1)
                      ltac:(lia)); try reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_rows].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 16 (SOff 38%nat 0)
               (hd_byte (c_pl cx) 3) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia)
               ltac:(hd_in) ltac:(rewrite ge_sv_SOff0; apply hd_env_b3) ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_u16].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 24
               (SAlu ALU_OR (SAlu ALU_SLL (SOff 36%nat 0) (SLit 8)) (SOff 35%nat 0))
               (hd_byte (c_pl cx) 0 + 256 * hd_byte (c_pl cx) 1) RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply (hd_or8 (hd_env cx fp (ms_regs ms3)));
                     [ apply hd_env_b0 | apply hd_env_b1 | lia | lia ])
               ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_in].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 64 (SOff 37%nat 0)
               (hd_byte (c_pl cx) 2) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia)
               ltac:(hd_in) ltac:(rewrite ge_sv_SOff0; apply hd_env_b2) ltac:(lia)).
    + apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 176 (SOff 516%nat 0)
               (gF cx fp) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(rewrite ge_sv_SOff0; apply hd_env_516) ltac:(lia)).

  - (* eight bytes or more: the whole header, the granule is marked usable *)
    pose proof (hd_seat cx fp W3 ly3 S3 md3 k HB HFR ms3 acc 4%nat (SLit 0) (SOff 39%nat 0)
                  0 0 8 (2 ^ 26 - 1) HJ HI ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
                  ltac:(rewrite ge_sv_SOff0; apply hd_env_39)
                  ltac:(intros _; unfold hd_s;
                        rewrite (proj2 (Z.ltb_ge (c_n cx) 8) ltac:(lia)); apply hd_lit; lia)
                  ltac:(lia)
                  ltac:(unfold hd_s;
                        rewrite (proj2 (Z.ltb_ge (c_n cx) 8) ltac:(lia)); lia)) as HS.
    pose proof (hd_h4 (c_pl cx) ltac:(unfold c_n in Hc; lia)) as Hhdr.
    destruct (HPblk ltac:(lia)) as (HpA & HpB & HpC).
    paj_run_to_sh RUNTOP HS HJ 0x2dc.
    { apply (hd_awr cx fp (hd_env cx fp (ms_regs ms3)) 4%nat (SLit 0) ly3 S3);
        [ apply hd_env_60 | apply hd_env_516 | lia | lia | lia | exact HFA ]. }
    hd_reg HS (19%bv : bv 5) Q19. hd_reg HS (21%bv : bv 5) Q21.
    hd_reg HS (22%bv : bv 5) Q22. hd_reg HS (24%bv : bv 5) Q24.
    hd_reg HS (23%bv : bv 5) Q23. hd_reg HS (26%bv : bv 5) Q26.
    hd_reg HS (27%bv : bv 5) Q27.
    pose proof (st_ok_pi_region_nth (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ HS eq_refl) as RSP.
    cbn [ms_mem restrict] in RSP.
    pose proof (ast_ok_pi_set_region (hd_env cx fp (ms_regs ms3)) _ _ 1%nat _ (ge_spill_region [])
                  HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
                  ltac:(cbn [ms_mem restrict]; destruct RSP as (Ha & Hb & Hw & _);
                        unfold ge_spill_region;
                        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
                        split; [exact Ha|]; split; [exact Hb|]; split;
                        [exact Hw | apply Forall_nil])) as HS2.
    lazymatch goal with |- SRr _ _ (mkCfg ?ms4 ?md4) _ =>
      apply (HM cx fp k acc ly3 S3 W3 ms4 md4 HB HJ HFR HMO);
      apply (hd_out cx fp k acc ly3 S3 W3 ms4 md4) end.
    + apply (hd_fin cx fp W3 ly3 S3 k HB HFR _ _ (hd_env cx fp (ms_regs ms3)) _ _ _ HJ HE HS2);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | ].
      apply (hd_garr W3 (ms_mem ms3) _ (c_p cx) _); [|exact Hinp].
      intros j Hj. rewrite length_map in Hj.
      apply (HFr (Z_to_bv 64 (c_p cx + Z.of_nat j))).
      rewrite unsigned_lit_small by (unfold c_n in *; lia).
      apply (hd_notw cx fp (hd_env cx fp (ms_regs ms3)) 4%nat (SLit 0));
        [ apply hd_env_60 | apply hd_env_516 | lia | lia
        | unfold c_n in *; lia | unfold c_n in *; lia ].
    + lia.
    + lia.
    + exact Hblk.
    + exact Hn26.
    + rewrite Q19, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q21, ge_sv_SOff0, hd_env_516. reflexivity.
    + rewrite Q22, ge_sv_SOff0, hd_env_529. reflexivity.
    + rewrite Q24, ge_sv_SOff0, (hd_env_32 cx fp (ms_regs ms3) HB). reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q26, (hd_off _ 33%nat (c_p cx) 4 (hd_env_33 cx fp (ms_regs ms3)) ltac:(lia)
                      ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_pos].
      rewrite Q23, (hd_off _ 39%nat (c_n cx) (-4) (hd_env_39 cx fp (ms_regs ms3)) ltac:(lia)
                      ltac:(lia)); try (f_equal; lia).
    + rewrite Hhdr. unfold GrantSlotPlan.h_base. cbn [GrantSlotPlan.h_u16].
      rewrite Q27, (hd_sext (hd_env cx fp (ms_regs ms3)) _
                      (hd_byte (c_pl cx) 0 + 256 * hd_byte (c_pl cx) 1)
                      (hd_or8 (hd_env cx fp (ms_regs ms3)) _ _
                         (hd_env_b0 cx fp (ms_regs ms3)) (hd_env_b1 cx fp (ms_regs ms3)) Hb0 Hb1)
                      ltac:(lia)); try reflexivity.
    + rewrite Hhdr. cbn [GrantSlotPlan.h_rows].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 16 (SOff 38%nat 0)
               (hd_byte (c_pl cx) 3) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia)
               ltac:(hd_in) ltac:(rewrite ge_sv_SOff0; apply hd_env_b3) ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_u16].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 24
               (SAlu ALU_OR (SAlu ALU_SLL (SOff 36%nat 0) (SLit 8)) (SOff 35%nat 0))
               (hd_byte (c_pl cx) 0 + 256 * hd_byte (c_pl cx) 1) RSP
               (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(apply (hd_or8 (hd_env cx fp (ms_regs ms3)));
                     [ apply hd_env_b0 | apply hd_env_b1 | lia | lia ])
               ltac:(lia)).
    + rewrite Hhdr. cbn [GrantSlotPlan.h_in].
      apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 64 (SOff 37%nat 0)
               (hd_byte (c_pl cx) 2) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia)
               ltac:(hd_in) ltac:(rewrite ge_sv_SOff0; apply hd_env_b2) ltac:(lia)).
    + apply (hd_slot cx W3 _ (hd_env cx fp (ms_regs ms3)) _ _ _ _ _ 176 (SOff 516%nat 0)
               (gF cx fp) RSP (hd_env_60 cx fp (ms_regs ms3)) ltac:(lia) ltac:(hd_in)
               ltac:(rewrite ge_sv_SOff0; apply hd_env_516) ltac:(lia)).
Qed.

End c.
End b.
End a.
