(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths, module names and addresses changed; 1508 of its 1616 lines of code are new or changed and 906 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW3a.v at 71c60c229b8d, for the same unit's
   image B (fuzz_rate.asan-ubsan): image B's pcs, registers and real-frame cells (the cursor is s2 = x18, the
   runtime's shadow offset s4 = x20, the bytes left s7 = x23, the property count cell R+0x118; the shape stays in a3
   and the third header byte is already spilled, so the head writes one cell instead of three); pp is not live in a
   register after the memset, so it is kept in R+0x168 and read back at the join; the object's header reads its
   values from R-relative cells; the five UBSan tests of the piece (two pointer-overflow guards of fuzz_u8, the
   `pp & 7` test of pod_put32 and its two bound tests) are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW3aB.v at df75d15c2f61, for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs, the shared
   names of lib/AU/RPgSeg.v, RPgMem.v and RPgSteps.v; role B's pcs, registers and real-frame cells (the cursor s4 = x20,
   the runtime's shadow offset s11 = x27, the bytes left s6 = x22, in.n in t3, pp's cell R+0x140, the property count
   R+0x108, the shadow address of &pp->len R+0x148, -0x3ffd R+0xc0, ~pp R+0xf8); C1 carries one real-frame cell (the
   flags byte); the head reads pp back into a5 itself (0x802fc, 0x80334), so its state holds the cell R+0x140 and the
   join carries a5 = pp, which the tail's state seats as pp's extra atom; &pp->len stays in s6 and is not spilled. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the piece W3a of the walk
   of LLVMFuzzerTestOneInput 0x80020, lib/AU/RPgSeg.v rs_piece_W3a_stmt. Proves no function (kind: segment lemma).

   THE CODE (C1 0x802c4 to the two header cuts B7 0x8045c and BO 0x804f0; pod.h:384-389, fuzz.h:37-43)
     0x802c4  bnez a0 (pp <> 0; its fall-through `j 0x82608` to the abort pair 0x82608 / 0x8260c is dead);
              0x802cc sd a0,0x140(s1): pp into the real frame
     0x802d0  a1 = 0; a2 = s2 = 19744; 0x802d8 jal 0x51608 (the runtime's memset): memset(pp, 0, 19744)
     0x802dc  beqz s6 -> 0x80328 (no input byte left)
     0x802e0  the shape byte: a0 = s4 + 1 and the pointer-overflow test `bltu a1,a0` (0x802e8), the cursor's shadow
              byte (`lb` 0x802f8; a5 = pp from R+0x140 at 0x802fc; `beqz` 0x80300; `j 0x82660`, the slow block
              `andi; bge -> report 0x82670; j 0x80308`), lbu, a3 = b0 & 7; `bne s6,1` -> 0x8033c
     0x80318  one byte: t3 = 0, R+0x108 := 0, s4 = s4 + 1
     0x80328  no byte: t3 = 0, a3 = 0, R+0x108 := 0, a5 = pp from R+0x140
     0x8033c  two bytes or more: the property-count byte at the cursor + 1 (its own overflow test 0x80340, shadow
              byte and slow block 0x826c4, report 0x826d0), t3 = s6 - 2, s4 = s4 + 2, R+0x108 := b1 & 3
     0x80370  `andi a0,a5,7; beqz` (pp is 8-aligned); s6 = pp + 0x4000, R+0x148 := its shadow address and the check
              of pp->len; a7 = len (= 0); R+0xc0 := -0x3ffd; a4 = ~pp into R+0xf8; a6 = pp + len; the capacity test
              `bgeu a2,a0` 0x803c0 (its other arm 0x803c4 is dead); the put's two UBSan tests (0x803e0 on len,
              0x803ec on ~pp), the two store checks of pp + 0 and pp + 3, four zero bytes, the check of pp->len and
              len := 4
     0x80458  `bne a3,a4` (a4 = 7) chooses BO 0x804f0, else B7 0x8045c
   Every instrumented check on the first block is covered by one shadow entry of the token engine
   (lib/Reusable/YCbn.v) over the whole block, which the allocator's law makes addressable. The two input reads have
   the `beqz t,+8; j L` shape the token path does not cover (lib/AU/RPgMem.v section 8): their shadow cell is carried
   as a one-byte REGION of the symbolic state, based on an extra atom whose value is the cell's address, with the
   alias fact ((s4 >> 3) + s11, that atom); then the load is an ordinary region load and raises no shadow
   obligation. The `beqz` and each slow block's `bge` are split with the engine's branch split, and the report arm of
   each dies by saddr_ok (RPgMem.rm_ra_slow_bv). Of the five UBSan tests, four are decided by the state's own atom
   ranges (the cursor's, len's and pp's) and the fifth, `bgeu ~pp,len` at 0x803ec, is split and its trap arm killed
   because no unsigned word is below 0.

   THE SPLIT. The piece is cut once more, at the join 0x80370 (w3a_mid), so that the three input-length arms are
   proved apart from the header block they share. The two bytes the third arm reads lie in ONE granule unless
   src mod 8 = 7, and two regions of the symbolic state may not overlap, so that arm is run twice: once with the
   second read aliased to the first read's cell (src mod 8 <> 7), once with a cell of its own (src mod 8 = 7). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgMem RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the code table and the engine's shadow parameters ============================== *)
(* 0x802c4 .. 0x80458 and the two slow blocks of the input reads *)
Definition w3a_tbl : ctable :=
  build_table rsegs 0x826c4 3 (build_table rsegs 0x82660 3 (build_table rsegs 0x802c4 102 TEmpty)).
Lemma w3a_tbl_ok : table_ok rsegs w3a_tbl.
Proof. apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.
(* the shadow base is s11's own atom (x27); one shadow entry: the first block, at the extra atom 32 (pp) *)
Definition W3Bx : sv := SOff 27 0.
Definition W3span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition W3SH : list shent := [mkSHE 32 0 PP_SIZE].
(* the bounds of the run's allocation ceiling (YG0f.ASAN_CEIL_range) *)
Definition W3CEIL_LO : Z := 0x7fff7f800000.
Definition W3CEIL_HI : Z := 0x7fffff800000.

(* ---- the regions of the head's runs (0x802dc -> 0x80370) ----
   the real-frame cell it writes (R+0x108 = the property count), the cell it reads pp back from (R+0x140, holding
   a0's atom: the memset returns pp in a0), the input bytes at the cursor (atoms 36, 37) and their shadow cells
   (atoms 32 / 33 and 34 / 35) *)
Definition w3a_rR108 : YP09.region := YP09.mkRegion (Some 9%nat) 0x108 0x110 0x108 0x110 [].
Definition w3a_rP : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x140 0x148 0 0 [YP09.mkChunk 0x140 (CVal 8 (SOff 10 0))].
Definition w3a_rIn0 : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition w3a_rIn1 : YP09.region := YP09.mkRegion (Some 20%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 37 0))].
Definition w3a_rC0 : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition w3a_rC1 : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition w3a_e0 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SOff 27 0).
Definition w3a_e1 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 1) (SLit 3)) (SOff 27 0).
Definition w3a_af0 : list (nat * afact) :=
  [(9%nat, mkAF W3CEIL_LO (2 ^ 47) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (20%nat, mkAF 1 (2 ^ 47) 0)].
(* the entry registers: their own atoms, but for the overrides ov (register, value) *)
Definition w3a_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.
Definition w3a_ssH (ov : list (bv 5 * sv)) (rs : smem) (fs : list (nat * afact)) (al : list (sv * sv)) : sstate :=
  mkSS 0x802dc (w3a_sr ov) ([w3a_rR108; w3a_rP] ++ rs) None (mkFacts (w3a_af0 ++ fs) [] al).
(* the extra atoms of a head run: the two shadow cells, their bytes and the two input bytes *)
Definition w3a_xs (src s0 src1 s1 b0 b1 : Z) : list word :=
  map (Z_to_bv 64) [shadow_of_addr SHADOW_OFF src; s0; src1; s1; b0; b1].

(* ---- the regions of the tail's run (0x80370 -> the header cuts) ----
   the first block's first bytes and its length word (atom 32 = pp, also a5's value), and the three real-frame cells
   it writes: R+0xf8 (~pp), R+0xc0 (-0x3ffd) and R+0x148 (the shadow address of &pp->len) *)
Definition w3a_rA : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [YP09.mkChunk 0 (CZero 8)].
Definition w3a_rB : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CZero 8)].
Definition w3a_rN : YP09.region := YP09.mkRegion (Some 9%nat) 0xf8 0x100 0xf8 0x100 [].
Definition w3a_rQ : YP09.region := YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0xc0 0xc8 [].
Definition w3a_rT : YP09.region := YP09.mkRegion (Some 9%nat) 0x148 0x150 0x148 0x150 [].
Definition w3a_ssT : sstate :=
  mkSS 0x80370 (w3a_sr [(Z_to_bv 5 15, SOff 32 0)]) [w3a_rA; w3a_rB; w3a_rN; w3a_rQ; w3a_rT] None
    (mkFacts [(9%nat, mkAF W3CEIL_LO (2 ^ 47) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
              (13%nat, mkAF 0 7 0); (32%nat, mkAF 4096 (W3CEIL_HI - PP_SIZE) 4)] [] []).
(* the shadow address of &pp->len, as the run computes it (0x80384, 0x80388) *)
Definition w3a_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 16384) (SLit 3)) (SOff 27 0).
(* ~pp, as `not a4,a5` leaves it *)
Definition w3a_nx : sv := SAlu ALU_XOR (SOff 32 0) (SLit (-1)).
(* the region of the state at C1: the cell the NULL test's successor writes (R+0x140 := pp) *)
Definition w3a_rM : YP09.region := YP09.mkRegion (Some 9%nat) 0x140 0x148 0x140 0x148 [].
Definition w3a_ssM : sstate :=
  mkSS 0x802c4 sr_atoms [w3a_rM] None
    (mkFacts [(10%nat, mkAF 4096 W3CEIL_HI 4); (9%nat, mkAF W3CEIL_LO (2 ^ 47) 4)] [] []).

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* =============================== small facts about values and lists =============================== *)
Lemma w3a_img_hdr : rs_img_hdr = zeros 16384 ++ le64 4 ++ zeros 3352.
Proof. vm_compute. reflexivity. Qed.
Lemma w3a_sh_P0 : rs_P0 = role_B_shA.
Proof. vm_compute. reflexivity. Qed.
Lemma w3a_land7 : forall v, 0 <= v -> Z.land v 7 = v mod 8.
Proof. intros v Hv. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma w3a_land3 : forall v, 0 <= v -> Z.land v 3 = v mod 4.
Proof. intros v Hv. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma w3a_nz : forall z, 0 < z < 32 -> Z_to_bv 5 z <> 0%bv.
Proof.
intros z Hz Hc. apply (f_equal (@bv_unsigned 5)) in Hc. rewrite Z_to_bv_unsigned in Hc.
unfold bv_wrap in Hc. change (bv_modulus 5) with 32 in Hc. rewrite Z.mod_small in Hc by lia.
change (@bv_unsigned 5 0%bv) with 0 in Hc. lia.
Qed.
Lemma w3a_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; cbn in *; [exact H2 | split; [apply H1 | apply IH; apply H1]].
Qed.
(* the complement `not a4,a5` leaves, as a Z *)
Lemma w3a_lnot_val : forall x, 0 <= x < 2 ^ 64 -> Z.lnot x mod 2 ^ 64 = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (Hl : Z.lnot x = (2 ^ 64 - 1 - x) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite Hl, Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma w3a_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (Ho : 2 ^ 64 - 1 = Z.ones 64) by (rewrite Z.ones_equiv; lia).
pose proof (w3a_lnot_val x Hx) as Hn.
rewrite <- Hn, Ho. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec.
destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
- rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
  destruct (Z.testbit x i); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia.
  rewrite (Z.bits_above_log2 x i); [reflexivity | lia |].
  assert (Hlog : Z.log2 x < 64).
  { destruct (Z.eq_dec x 0) as [->|Hx0]; [rewrite Z.log2_nonpos by lia; lia|].
    apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))). lia. }
  lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- values of the symbolic terms the runs produce ---- *)
Lemma w3a_U_lit : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> forall c, 0 <= v + c < 2 ^ 64 ->
  U E (SOff n c) = v + c.
Proof.
intros E n v Hn Hv c Hc. rewrite U_SOff, Hn, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma w3a_U_srl3 : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu, U_SLit, (w3a_U_lit E n v Hn Hv c Hc). cbn [zalu_raw].
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64.
split; [apply Z.div_pos; lia | apply (Z.le_lt_trans _ (v + c)); [apply Z.div_le_upper_bound; lia | lia]].
Qed.
Lemma w3a_den_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = w64 z.
Proof.
intros E z Hz. apply bv_eq. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)).
rewrite U_SLit, (zcanon_id z) by (unfold M64; lia). unfold w64. symmetry. apply unsigned_lit_small. lia.
Qed.
Lemma w3a_den_off : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c Hn Hv Hc. apply bv_eq. change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
rewrite (w3a_U_lit E n v Hn Hv c Hc). unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma w3a_den_off0 : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v.
Proof. intros E n v Hn Hv. rewrite (w3a_den_off E n v 0 Hn Hv) by lia. rewrite Z.add_0_r. reflexivity. Qed.
Lemma w3a_den_and : forall E (n : nat) v c m, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  0 <= m < 2 ^ 63 -> sv_denot E (SAlu ALU_AND (SOff n c) (SLit m)) = w64 (Z.land (v + c) m).
Proof.
intros E n v c m Hn Hv Hc Hm. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_AND (SOff n c) (SLit m)))) with (U E (SAlu ALU_AND (SOff n c) (SLit m))).
rewrite U_SAlu, U_SLit, (w3a_U_lit E n v Hn Hv c Hc). cbn [zalu_raw].
rewrite (zcanon_id m) by (unfold M64; lia).
pose proof (Z_land_upper (v + c) m ltac:(lia)). unfold w64. rewrite unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma w3a_den_sh : forall E pp, ew E 32 = Z_to_bv 64 pp -> ew E 27 = Z_to_bv 64 SHADOW_OFF -> 0 <= pp < 2 ^ 47 ->
  sv_denot E w3a_shx = w64 (shadow_addr (pp + 0x4000)).
Proof.
intros E pp H32 H27 Hpp. apply bv_eq.
change (bv_unsigned (sv_denot E w3a_shx)) with (U E w3a_shx). unfold w3a_shx.
rewrite U_SAlu, (w3a_U_srl3 E 32 pp 16384 H32 ltac:(lia) ltac:(lia)),
  (w3a_U_lit E 27 SHADOW_OFF H27 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)). cbn [zalu_raw].
pose proof (Z.div_pos (pp + 16384) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound (pp + 16384) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
unfold w64, shadow_addr, SHADOW_OFF in *. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma w3a_den_nx : forall E pp, ew E 32 = Z_to_bv 64 pp -> 0 <= pp < 2 ^ 63 ->
  sv_denot E w3a_nx = w64 (Z.lnot pp).
Proof.
intros E pp H32 Hpp. apply bv_eq.
change (bv_unsigned (sv_denot E w3a_nx)) with (U E w3a_nx). unfold w3a_nx.
rewrite U_SAlu, U_SLit, (w3a_U_lit E 32 pp H32 ltac:(lia) 0 ltac:(lia)). cbn [zalu_raw]. rewrite Z.add_0_r.
change (zcanon (-1)) with (2 ^ 64 - 1).
rewrite (w3a_lxor_ones pp ltac:(lia)).
pose proof (w3a_lnot_val pp ltac:(lia)) as Hn.
unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Hn.
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma w3a_lit_neg : forall E, sv_denot E (SLit 18446744073709535235) = w64 (-0x3ffd).
Proof. intros E. apply bv_eq. cbn [sv_denot]. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma w3a_lit_a2 : forall E, sv_denot E (SLit 18446744073709535239) = w64 (4 - 0x3ffd).
Proof. intros E. apply bv_eq. cbn [sv_denot]. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

(* ---- the two outcomes of `bne a3,a4` 0x80458 (a3 = the shape, a4 = 7) ---- *)
Lemma w3a_bne_eq : forall E (k : nat) s, ew E k = Z_to_bv 64 s -> 0 <= s <= 7 ->
  branch_taken BC_NE (sv_denot E (SOff k 0)) (sv_denot E (SLit 7)) = false -> s = 7.
Proof.
intros E k s Hk Hs Hc. destruct (Z.eq_dec s 7) as [->|Hne]; [reflexivity | exfalso].
rewrite (w3a_den_off0 E k s Hk ltac:(lia)), (w3a_den_lit E 7 ltac:(lia)) in Hc.
assert (Hcs : s = 0 \/ s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/ s = 5 \/ s = 6) by lia.
repeat (destruct Hcs as [-> | Hcs]; [vm_compute in Hc; discriminate|]). subst s. vm_compute in Hc. discriminate.
Qed.
Lemma w3a_bne_ne : forall E (k : nat) s, ew E k = Z_to_bv 64 s -> 0 <= s <= 7 ->
  branch_taken BC_NE (sv_denot E (SOff k 0)) (sv_denot E (SLit 7)) = true -> s <> 7.
Proof.
intros E k s Hk Hs Hc Heq. subst s.
rewrite (w3a_den_off0 E k 7 Hk ltac:(lia)), (w3a_den_lit E 7 ltac:(lia)) in Hc. vm_compute in Hc. discriminate.
Qed.
(* no unsigned word is below 0: the trap arm of `bgeu a0,a7` 0x803ec (a7 = len = 0) is dead *)
Lemma w3a_geu0 : forall E e, branch_taken BC_GEU (sv_denot E e) (sv_denot E (SLit 0)) = false -> False.
Proof.
intros E e Hc. cbn [branch_taken] in Hc. apply negb_false_iff in Hc. unfold bv_ltu in Hc.
apply Z.ltb_lt in Hc.
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)) in Hc. rewrite U_SLit in Hc.
change (zcanon 0) with 0 in Hc. pose proof (u64_range (sv_denot E e)). lia.
Qed.

(* ---- seating and reading the engine's states ---- *)
Lemma w3a_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (w3a_sr ov) regs.
Proof.
intros regs extra ov Hov. unfold w3a_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
  regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
  apply IH. apply regs_ok_pin; [exact Hsr | exact Hr0 | symmetry; exact Hv]. }
apply G. apply regs_ok_Ereg.
Qed.
Lemma w3a_reg_atom : forall E ss ms (H : word -> bool) regs extra (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms H regs extra r HS [HA _] Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r); lia). apply ew_Ereg_reg.
Qed.
Lemma w3a_region_nth : forall E ss ms i r,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma w3a_chunk8 : forall E m base off e v,
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = w64 v ->
val_mem rsegs m (base + off) 8 (v mod 2 ^ 64).
Proof.
intros E m base off e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
rewrite Hm. f_equal. injection Hb as <-. rewrite He. unfold byte_of_word, w64.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia.
reflexivity.
Qed.
Lemma w3a_slot : forall E m n b lo hi wlo whi cs od e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = w64 v -> val_mem rsegs m (b + od) 8 (v mod 2 ^ 64).
Proof.
intros E m n b lo hi wlo whi cs od e v (_ & _ & _ & Hcs) Hn Hc He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (w3a_chunk8 E m b od e v Hck He).
Qed.
Lemma w3a_zero_at : forall E H mem n b lo hi wlo whi cs od l i,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CZero l)) cs -> 0 <= i < l -> aview rsegs H mem (b + od + i) = Some 0.
Proof.
intros E H mem n b lo hi wlo whi cs od l i (_ & _ & _ & Hcs) Hn Hc Hi.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck i ltac:(cbn; lia)) as (bb & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
injection Hb as <-. unfold aview. rewrite Hm. reflexivity.
Qed.
Lemma w3a_lit_at : forall E H mem n b lo hi wlo whi cs od z,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CVal 1 (SLit z))) cs -> aview rsegs H mem (b + od) = Some (z mod 256).
Proof.
intros E H mem n b lo hi wlo whi cs od z (_ & _ & _ & Hcs) Hn Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
rewrite Z.add_0_r in Hm. injection Hb as <-. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold byte_of_word. cbn [sv_denot]. rewrite Z.shiftr_0_r, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 56). reflexivity.
Qed.
Lemma w3a_keep_run : forall E rs (H : word -> bool) (m1 m2 : word -> option byte) (Zn : Z -> Prop),
frame_of E rs (mrestrict H m1) (mrestrict H m2) -> (forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 Zn HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Lemma w3a_val_kept : forall H H' (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview rsegs H' m' x = aview rsegs H m x) ->
val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v K V k Hk. rewrite (mbyte_of_aview rsegs H H' m m' (a + Z.of_nat k)) by (apply K; lia).
exact (V k Hk).
Qed.

(* the report arm of a slow block: the shadow byte is not 0, so saddr_ok puts the offset in the granule below it *)
Lemma w3a_kill : forall E (n k : nat) (x s c : Z),
ew E n = Z_to_bv 64 x -> ew E k = Z_to_bv 64 s -> 0 <= x -> 0 <= c -> x + c < 2 ^ 64 -> 0 <= s < 2 ^ 64 ->
saddr_ok (x + c) s ->
branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = false ->
branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff n c) (SLit 7))) (sv_denot E (SOff k 0)) = true -> False.
Proof.
intros E n k x s c Hn Hk Hx Hc Hxc Hs Hok Heq Hge.
assert (Hs0 : s <> 0).
{ intros Hz. subst s. rewrite (w3a_den_off0 E k 0 Hk ltac:(lia)), (w3a_den_lit E 0 ltac:(lia)) in Heq.
  vm_compute in Heq. discriminate. }
rewrite (w3a_den_and E n x c 7 Hn ltac:(lia) ltac:(lia) ltac:(lia)) in Hge.
rewrite (w3a_den_off0 E k s Hk ltac:(lia)) in Hge.
rewrite (w3a_land7 (x + c) ltac:(lia)) in Hge.
cbv [branch_taken] in Hge. apply negb_true_iff in Hge.
unfold w64 in Hge. rewrite (rm_ra_slow_bv (x + c) s Hok Hs0) in Hge. discriminate.
Qed.

(* ---- the run plumbing ---- *)
Ltac w3a_foldE E := repeat match goal with |- context [ew ?EE ?n] =>
  lazymatch EE with E => fail | _ => change (ew EE n) with (ew E n) end end.
Ltac w3a_foldEH E H := repeat match type of H with context [ew ?EE ?n] =>
  lazymatch EE with E => fail | _ => change (ew EE n) with (ew E n) in H end end.
(* the write permission of a run's regions: the first block's two windows (a block made since the journal's start),
   the real frame's cells (the caller's stack window) and read-only regions *)
Ltac w3a_awr pp R Ub32 Ub9 Hppin Hfresh :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat lazymatch goal with
  | |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
  | |- awr_ok _ (YP09.mkRegion _ _ _ 0 0 _ :: _) _ _ _ _ _ _ _ => apply awr_ok_cons_ro; [cbn; lia|]
  | |- awr_ok _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat); [reflexivity | exact Ub32 | |];
      [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        replace a with (pp + (a - pp)) by lia;
        apply (rl_fresh_awr_n _ _ _ _ _ _ _ _ _ Hppin Hfresh); unfold PP_SIZE; lia | ]
  | |- awr_ok _ (YP09.mkRegion (Some 9%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | refine (eq_trans Ub9 _); lia | cbn; lia | cbn; lia |]
  end.
(* every window of a run's regions lies in the zone Zn *)
Ltac w3a_kwr E Ub32 Ub9 :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; w3a_foldEH E Hb;
    first [rewrite Ub32 in Hb | rewrite Ub9 in Hb | idtac]; lia | ]); destruct Hr.
Ltac w3a_sr HS :=
  lazymatch type of HS with st_ok _ _ ?s _ =>
  repeat match goal with |- context [sr_get (ss_regs ?ss) ?r] =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end end.
Ltac w3a_reg HS :=
  lazymatch type of HS with st_ok ?segs ?E ?s (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E s ms _ HS); w3a_sr HS end.
Ltac w3a_rgn HS i HR :=
  lazymatch type of HS with st_ok _ _ ?s _ =>
  let r := eval vm_compute in (nth_error (ss_mem s) i) in
  lazymatch r with Some ?rr => pose proof (w3a_region_nth _ s _ i rr HS ltac:(vm_compute; reflexivity)) as HR end end;
  cbn [ms_mem restrict] in HR.
Ltac w3a_in := repeat (first [left; reflexivity | right]).

(* the right-hand window (XR, 0x48, 0x118) of the build's write set (RPgImgA: hi_w1 role_himg_B, its fourth entry)
   holds every real-frame cell the piece writes: R+0xc0, R+0xf8, R+0x108, R+0x140 and R+0x148 *)
Ltac w3a_w1 := unfold rl_inw; cbn [hi_w1 role_himg_B];
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; cbn [fst snd rl_xv]; lia.

(* =============================== the piece =============================== *)
Section s.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the runtime's memset of the image (the target of the `jal` at 0x802d8; RPgSteps.RL_MEMSET) *)
Hypothesis W3_AMEMSET : aintrin_realizes rsegs B OSet 0x51608.

(* ---- what the piece reads off C1: the journal, the registers, the flags cell, the block, the input ---- *)
Record w3a_c1 (cx : rs_scx rsegs) (rest : list byte) : Prop := W3AC1 {
c1_J : ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx);
c1_r2 : getr (x_regs cx) 2 = w64 (e_R (x_e cx));
c1_r3 : getr (x_regs cx) 3 = w64 (as_gp B);
c1_r4 : getr (x_regs cx) 4 = w64 (as_tp B);
c1_S : e_S (x_e cx) = x_sp0 cx;
c1_R16 : e_R (x_e cx) mod 16 = 0;
c1_RS : e_R (x_e cx) + 0x200 <= e_S (x_e cx);
c1_STK : x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK;
c1_own : In (4, x_pos cx) (x_own cx);
c1_F : e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx);
c1_ppin : In (e_pp (x_e cx), PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx));
c1_fl : 0 <= e_fl (x_e cx) < 256;
c1_ppnew : ~ In (e_pp (x_e cx), PP_SIZE) (ablocks B (x_ly cx) (x_S cx));
c1_fsh : rl_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) role_B_shA;
c1_a0 : getr (x_regs cx) (Z_to_bv 5 10) = w64 (e_pp (x_e cx) + 0);
c1_s0 : getr (x_regs cx) (Z_to_bv 5 8) = w64 (e_S (x_e cx));
c1_s1 : getr (x_regs cx) (Z_to_bv 5 9) = w64 (e_R (x_e cx));
c1_s2 : getr (x_regs cx) (Z_to_bv 5 18) = w64 19744;
c1_s3 : getr (x_regs cx) (Z_to_bv 5 19) = w64 (shadow_addr (e_F (x_e cx)));
c1_s4 : getr (x_regs cx) (Z_to_bv 5 20) = w64 (e_src (x_e cx));
c1_s5 : getr (x_regs cx) (Z_to_bv 5 21) = w64 0x5000;
c1_s6 : getr (x_regs cx) (Z_to_bv 5 22) = w64 (e_left (x_e cx));
c1_s7 : getr (x_regs cx) (Z_to_bv 5 23) = w64 (e_F (x_e cx));
c1_s10 : getr (x_regs cx) (Z_to_bv 5 26) = w64 (e_F (x_e cx));
c1_s11 : getr (x_regs cx) (Z_to_bv 5 27) = w64 SHADOW_OFF;
c1_c40 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x40) 8
  (e_fl (x_e cx) mod 2 ^ 64);
c1_in : rs_in rsegs cx rest }.

Lemma w3a_c1_of : forall cx rest, rs_start_M01 rsegs B cx rest -> w3a_c1 cx rest.
Proof.
intros cx rest (HP & Hfsh & HL1 & _ & HIN).
destruct HP as (HJ & _ & H2 & H3 & H4 & HeS & HR16 & HRS & HSTK & Hown & HeF & _ & Hppne & Hppin & Hfl &
  _ & _ & _ & _ & _ & _ & Hfresh).
unfold rl_cut in HL1. cbn [hi_L1 role_himg_B] in HL1.
repeat rewrite Forall_cons_iff in HL1.
destruct HL1 as (A10 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A26 & A27 & C40 & _).
cbn [fst snd rl_at rl_xv] in A10, A8, A9, A18, A19, A20, A21, A22, A23, A26, A27, C40.
cbn [hi_cid hi_rsz hi_shA role_himg_B] in *.
constructor; assumption.
Qed.

(* the bounds the walk uses, from C1's journal and the allocator's block law *)
Lemma w3a_bounds : forall cx rest, w3a_c1 cx rest ->
let e := x_e cx in
e_pp e mod 16 = 0 /\ 4096 <= e_pp e /\ e_pp e + PP_SIZE <= alloc_ceiling /\
in_app (e_pp e) PP_SIZE /\ alloc_ceiling + T_SEG_STK <= e_R e /\ e_R e + 0x200 <= x_sp0 cx /\
x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\ x_sp0 cx - x_STK cx <= e_R e - T_SEG_STK /\
W3CEIL_LO <= alloc_ceiling <= W3CEIL_HI.
Proof.
intros cx rest HC e. pose proof (c1_J cx rest HC) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (c1_ppin cx rest HC)) as (Hm16 & H4096 & Hpc & Happ & _).
pose proof ASAN_CEIL_range as ((Ha1 & Ha2) & _). unfold ASAN_CEIL in Ha1, Ha2.
pose proof (c1_RS cx rest HC) as HRS. pose proof (c1_S cx rest HC) as HS. pose proof (c1_STK cx rest HC) as HSTK.
replace (req_size PP_SIZE) with PP_SIZE in Hpc, Happ by reflexivity.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in *. subst e. rewrite HS in HRS.
split; [exact Hm16|]. split; [exact H4096|]. split; [exact Hpc|]. split; [exact Happ|].
unfold PP_SIZE in *. repeat split; lia.
Qed.

(* the bytes of the block are present (the allocator's law), for the regions of the tail's run *)
Lemma w3a_present : forall cx rest, w3a_c1 cx rest -> forall ly S W mem md,
AR rsegs B ly S W mem md -> In (e_pp (x_e cx), PP_SIZE) (ablocks B ly S) ->
forall o, 0 <= o < PP_SIZE -> apresent (w_H W) mem (e_pp (x_e cx) + o).
Proof.
intros cx rest HC ly S W mem md HAR Hin o Ho.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpr & _).
replace (req_size PP_SIZE) with PP_SIZE in Hpr by reflexivity.
exact (proj1 (Hpr (e_pp (x_e cx) + o) ltac:(lia))).
Qed.

(* the frame for locals and its shadow bytes lie apart from the block, the real frame and the callees' stack *)
Lemma w3a_fsh_apart : forall cx rest, w3a_c1 cx rest -> forall i, 0 <= i < 88 ->
let a := shadow_addr (e_F (x_e cx)) + i in
0 <= a < 2 ^ 64 /\ ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE) /\
a < e_R (x_e cx) - T_SEG_STK.
Proof.
intros cx rest HC i Hi a.
pose proof (w3a_bounds cx rest HC) as (_ & H4096 & Hpc & Happ & HRlo & _ & _ & _ & _ & Hceil).
pose proof (c1_J cx rest HC) as HJ. pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, x_pos cx) (frames (x_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact (c1_own cx rest HC)).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) HAR Hin) as (HF1 & HF2 & _).
rewrite <- (c1_F cx rest HC) in HF1, HF2. change (fs_frame_bytes 4) with 1024 in HF2.
subst a. unfold shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, W3CEIL_LO, W3CEIL_HI,
  T_SEG_STK, ASTACK, PP_SIZE in *.
pose proof (Z.mul_div_le (e_F (x_e cx)) 8 ltac:(lia)).
pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)).
set (q := e_F (x_e cx) / 8) in *.
lia.
Qed.

(* 0x802c4 .. 0x802d4 (the NULL test, R+0x140 := pp, the memset's arguments) and the memset call: what C1 becomes
   at 0x802dc. The block is zero, R+0x140 and a0 hold pp, every byte outside the block and outside the callee's
   stack [R - ESTACK, R) is as at C1, and every callee-saved register keeps its C1 value. *)
Definition w3a_m1_post (cx : rs_scx rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem2 md2 (x_k cx) /\
same_io (x_mdc cx) md2 /\
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
 getr regs2 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs2 (Z_to_bv 5 10) = w64 (e_pp (x_e cx)) /\
val_mem rsegs (mrestrict (w_H (x_W cx)) mem2) (e_R (x_e cx) + 0x140) 8 (e_pp (x_e cx) mod 2 ^ 64) /\
(forall i, 0 <= i < PP_SIZE -> aview rsegs (w_H (x_W cx)) mem2 (e_pp (x_e cx) + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE) ->
 ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) -> ~ (e_R (x_e cx) + 0x140 <= a < e_R (x_e cx) + 0x148) ->
 aview rsegs (w_H (x_W cx)) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Lemma w3a_m1 : forall cx rest (Q : world rsegs -> config -> Prop),
w3a_c1 cx rest ->
(forall regs2 mem2 md2, w3a_m1_post cx regs2 mem2 md2 ->
  SRr rsegs (x_W cx) (cfg_at rsegs 0x802dc regs2 mem2 md2) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs (hi_c1 role_himg_B) (x_regs cx) (x_memc cx) (x_mdc cx)) Q.
Proof.
intros cx rest Q HC K.
pose proof (w3a_bounds cx rest HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof HC as [HJ H2 H3 H4 HeS HR16 _ _ _ _ Hppin _ Hfresh _ A10 _ A9 A18 _ _ _ _ _ _ _ _ _].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (pp := e_pp e) in *. set (R := e_R e) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof RPgSteps.rl_wx as Hwx. pose proof RPgSteps.rl_segs_low as Hsegs.
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
assert (HS : st_ok rsegs (Ereg regs []) w3a_ssM
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x802c4) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w3a_ssM. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rm_rw_region rsegs (Ereg regs []) (w_H W) memc 9 R);
      [ rewrite (ew_Ereg_nat regs [] 9 (Z_to_bv 5 9) eq_refl), A9; apply unsigned_lit_small; lia
      | lia | lia | intros o Ho; apply Hstkp; lia |]. apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs [] 10 (Z_to_bv 5 10) eq_refl), A10,
      (ew_Ereg_nat regs [] 9 (Z_to_bv 5 9) eq_refl), A9. unfold w64.
    rewrite !unsigned_lit_small by (unfold PP_SIZE, W3CEIL_HI in *; lia).
    change (2 ^ 4) with 16. rewrite Z.add_0_r.
    unfold PP_SIZE, W3CEIL_LO, W3CEIL_HI in *. repeat split; lia. }
assert (Ub9 : bv_unsigned (ew (Ereg regs []) 9%nat) = R)
  by (rewrite (ew_Ereg_nat regs [] 9 (Z_to_bv 5 9) eq_refl), A9; apply unsigned_lit_small; lia).
unfold cfg_at. cbn [hi_c1 role_himg_B]. change (w64 0x802c4) with (Z_to_bv 64 0x802c4).
aj_run_to w3a_tbl_ok HS HJ 0x51608.
{ w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Ra1. rreg HS (Z_to_bv 5 10) Ra10. rreg HS (Z_to_bv 5 11) Ra11. rreg HS (Z_to_bv 5 12) Ra12.
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. eapply (w3a_reg_atom _ _ ms (w_H W) regs [] (Z_to_bv 5 r) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
w3a_rgn HS 0%nat HR0.
assert (V140 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x140) 8 (pp mod 2 ^ 64)).
{ apply (w3a_slot _ _ 9 R _ _ _ _ _ 0x140 (SOff 10 0) pp HR0 Ub9); [w3a_in|].
  apply (w3a_den_off0 _ 10 pp); [rewrite (ew_Ereg_nat regs [] 10 (Z_to_bv 5 10) eq_refl), A10, Z.add_0_r;
    reflexivity | unfold PP_SIZE in *; lia]. }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
assert (HAR : AR rsegs B lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)) by exact (proj1 HJ).
assert (E2 : getr (ms_regs ms) (2%bv : bv 5) = getr regs (2%bv : bv 5))
  by (eapply (w3a_reg_atom _ _ ms (w_H W) regs [] _ HS HAE); vm_compute; reflexivity).
assert (E3 : getr (ms_regs ms) (3%bv : bv 5) = getr regs (3%bv : bv 5))
  by (eapply (w3a_reg_atom _ _ ms (w_H W) regs [] _ HS HAE); vm_compute; reflexivity).
assert (E4 : getr (ms_regs ms) (4%bv : bv 5) = getr regs (4%bv : bv 5))
  by (eapply (w3a_reg_atom _ _ ms (w_H W) regs [] _ HS HAE); vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (R - sp0)).
{ unfold spZ. rewrite E2, H2. unfold w64. rewrite unsigned_lit_small; [ring | lia]. }
destruct (rm_blk_ra rsegs B lyc Sc W (ms_mem ms) _ pp PP_SIZE pp PP_SIZE HAR Hppin ltac:(lia)
  ltac:(unfold req_size; cbn; lia)) as (Hra & Hhull).
eapply SRr_bind.
{ eapply (RPgSteps.rl_intrin_at B LAWS OSet 0x51608 W3_AMEMSET W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0
    mem0 md0 own lyc Sc _ k pp 0 PP_SIZE (R - sp0) (Z_to_bv 64 0x802dc) HJ).
  - refine (eq_trans Ra10 (eq_trans A10 _)). f_equal. lia.
  - exact Ra11.
  - exact (eq_trans Ra12 A18).
  - unfold PP_SIZE. lia.
  - lia.
  - unfold PP_SIZE in *. lia.
  - exact Hsp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - exact (eq_trans E3 H3).
  - exact (eq_trans E4 H4).
  - exact Ra1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (pp + (a - pp)) by lia.
      apply (rl_fresh_awr_n STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own pp PP_SIZE Hppin Hfresh);
        unfold PP_SIZE in *; lia.
    + unfold ESTACK. unfold PP_SIZE in *. lia.
  - eapply amem_range_of_block; [exact LAWS | exact HAR | exact Hppin | lia | unfold req_size; cbn; lia].
  - exact Hra.
  - exact Hhull.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hpres2 & Hsame2 & Ha02 & Hzero & Hkeep).
apply K. unfold w3a_m1_post.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_e].
try fold pp. try fold R.
split; [exact HJ2|].
split; [eapply same_io_trans; [apply RPgSteps.same_io_wvb | exact (same_io_materialized _ _ Hsame2)]|].
split.
{ intros r Hr. rewrite (Hpres2 r).
  - apply Rk. exact Hr.
  - cbn [In] in Hr. unfold acallee_saved.
    repeat (destruct Hr as [<- | Hr]; [lia|]). destruct Hr. }
split; [exact Ha02|].
split.
{ refine (w3a_val_kept _ _ _ _ _ _ _ _ V140). intros x Hx. apply Hkeep; unfold PP_SIZE, ESTACK in *; lia. }
split; [exact Hzero|].
intros a Ha Hnp Hns Hn140. transitivity (aview rsegs (w_H W) (ms_mem ms) a).
{ apply Hkeep; [exact Ha | exact Hnp |]. replace (sp0 + (R - sp0)) with R by lia. unfold ESTACK in *. lia. }
{ apply (w3a_keep_run (Ereg regs []) _ (w_H W) memc (ms_mem ms)
    (fun a => R + 0x140 <= a < R + 0x148) HFr); [w3a_kwr (Ereg regs []) Ub9 Ub9 | exact Ha | lia]. }
Qed.

(* =============================== the join 0x80370 =============================== *)
(* what the three input-length arms leave at 0x80370: the journal, the cursor and what is left of the input, the
   shape in a3, pp in a5 and in R+0x140, the property count in R+0x108, the zero block, and every other byte as at
   C1 *)
Definition w3a_mid (cx : rs_scx rsegs) (rest r : list byte) (sh np : Z)
(regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem3 md3 (x_k cx) /\
same_io (x_mdc cx) md3 /\
(forall q, In q [2; 3; 4; 8; 9; 19; 21; 23; 26; 27] ->
 getr regs3 (Z_to_bv 5 q) = getr (x_regs cx) (Z_to_bv 5 q)) /\
getr regs3 (Z_to_bv 5 13) = w64 sh /\
getr regs3 (Z_to_bv 5 20) = w64 (rs_cur rsegs cx rest r) /\
getr regs3 (Z_to_bv 5 28) = w64 (Z.of_nat (length r)) /\
getr regs3 (Z_to_bv 5 15) = w64 (e_pp (x_e cx)) /\
val_mem rsegs (mrestrict (w_H (x_W cx)) mem3) (e_R (x_e cx) + 0x108) 8 (np mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H (x_W cx)) mem3) (e_R (x_e cx) + 0x140) 8 (e_pp (x_e cx) mod 2 ^ 64) /\
(forall i, 0 <= i < PP_SIZE -> aview rsegs (w_H (x_W cx)) mem3 (e_pp (x_e cx) + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE) ->
 ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) -> ~ (e_R (x_e cx) + 0x140 <= a < e_R (x_e cx) + 0x148) ->
 ~ (e_R (x_e cx) + 0x108 <= a < e_R (x_e cx) + 0x110) ->
 aview rsegs (w_H (x_W cx)) mem3 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Lemma w3a_mid_of : forall cx rest r sh np regs2 mem2 md2 regs3 mem3 md3,
w3a_c1 cx rest -> w3a_m1_post cx regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem3 md3 (x_k cx) ->
same_io md2 md3 ->
(forall q, In q [2; 3; 4; 8; 9; 19; 21; 23; 26; 27] -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
getr regs3 (Z_to_bv 5 13) = w64 sh ->
getr regs3 (Z_to_bv 5 20) = w64 (rs_cur rsegs cx rest r) ->
getr regs3 (Z_to_bv 5 28) = w64 (Z.of_nat (length r)) ->
getr regs3 (Z_to_bv 5 15) = w64 (e_pp (x_e cx)) ->
val_mem rsegs (mrestrict (w_H (x_W cx)) mem3) (e_R (x_e cx) + 0x108) 8 (np mod 2 ^ 64) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) + 0x108 <= a < e_R (x_e cx) + 0x110) ->
 aview rsegs (w_H (x_W cx)) mem3 a = aview rsegs (w_H (x_W cx)) mem2 a) ->
w3a_mid cx rest r sh np regs3 mem3 md3.
Proof.
intros cx rest r sh np regs2 mem2 md2 regs3 mem3 md3 HC HM HJ3 Hio3 Hk3 H13 H20 H28 H15 V108 Hkeep3.
pose proof (w3a_bounds cx rest HC) as (_ & H4096 & Hpc & _ & HRlo & HRS & H47 & _ & _ & Hceil).
destruct HM as (HJ2 & Hio2 & Hk2 & _ & V140 & Hzero & Hkeep2).
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo.
unfold w3a_mid.
split; [exact HJ3|]. split; [exact (same_io_trans _ _ _ Hio2 Hio3)|].
split; [intros q Hq; rewrite (Hk3 q Hq); apply Hk2; cbn [In] in Hq |- *; tauto|].
split; [exact H13|]. split; [exact H20|]. split; [exact H28|]. split; [exact H15|]. split; [exact V108|].
split.
{ refine (w3a_val_kept _ _ _ _ _ _ _ _ V140). intros x Hx. apply Hkeep3; unfold PP_SIZE in *; lia. }
split.
{ intros i Hi. rewrite (Hkeep3 (e_pp (x_e cx) + i)); [apply Hzero | |];
  unfold PP_SIZE in *; lia. }
intros a Ha Hnp Hns H140 H108. rewrite (Hkeep3 a Ha H108). apply Hkeep2; assumption.
Qed.

(* =============================== the tail: 0x80370 to the header cuts =============================== *)
(* what the tail's run gives at a header cut, read off its last symbolic state *)
Definition w3a_leafT (cx : rs_scx rsegs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
(regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model) : Prop :=
let e := x_e cx in let H := w_H (x_W cx) in
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem4 md4 (x_k cx) /\
same_io md3 md4 /\
(forall q, In q [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31] ->
 getr regs4 (Z_to_bv 5 q) = getr regs3 (Z_to_bv 5 q)) /\
getr regs4 (Z_to_bv 5 10) = w64 4 /\ getr regs4 (Z_to_bv 5 11) = w64 0x4000 /\
getr regs4 (Z_to_bv 5 12) = w64 (4 - 0x3ffd) /\ getr regs4 (Z_to_bv 5 15) = w64 (e_pp e) /\
getr regs4 (Z_to_bv 5 16) = w64 (e_pp e) /\ getr regs4 (Z_to_bv 5 17) = w64 0 /\
getr regs4 (Z_to_bv 5 22) = w64 (e_pp e + 0x4000) /\
val_mem rsegs (mrestrict H mem4) (e_R e + 0xf8) 8 (Z.lnot (e_pp e) mod 2 ^ 64) /\
val_mem rsegs (mrestrict H mem4) (e_R e + 0xc0) 8 (-0x3ffd mod 2 ^ 64) /\
val_mem rsegs (mrestrict H mem4) (e_R e + 0x148) 8 (shadow_addr (e_pp e + 0x4000) mod 2 ^ 64) /\
(forall i, 0 <= i < 8 -> aview rsegs H mem4 (e_pp e + i) = Some 0) /\
val_mem rsegs (mrestrict H mem4) (e_pp e + 0x4000) 8 4 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp e <= a < e_pp e + 8) -> ~ (e_pp e + 0x4000 <= a < e_pp e + 0x4008) ->
 ~ (e_R e + 0xf8 <= a < e_R e + 0x100) -> ~ (e_R e + 0xc0 <= a < e_R e + 0xc8) ->
 ~ (e_R e + 0x148 <= a < e_R e + 0x150) ->
 aview rsegs H mem4 a = aview rsegs H mem3 a).

Lemma w3a_hdr_of : forall cx rest r sh np regs3 mem3 md3 regs4 mem4 md4,
w3a_c1 cx rest -> w3a_mid cx rest r sh np regs3 mem3 md3 -> w3a_leafT cx regs3 mem3 md3 regs4 mem4 md4 ->
rs_suffix rest r -> sh = rs_sh rest -> np = rs_np rest -> r = rs_r0 rest ->
rs_cut_hdr rsegs B MT cx rest r sh np (x_lyc cx) (x_Sc cx) (x_W cx) regs4 mem4 md4.
Proof.
intros cx rest r sh np regs3 mem3 md3 regs4 mem4 md4 HC HMID HL Hsuf Hsh Hnp Hr.
pose proof (w3a_bounds cx rest HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (w3a_fsh_apart cx rest HC) as HFA.
pose proof (c1_in cx rest HC) as HIN. pose proof (c1_fsh cx rest HC) as Hfsh.
pose proof (c1_r2 cx rest HC) as H2. pose proof (c1_s1 cx rest HC) as A9.
pose proof (c1_s0 cx rest HC) as A8. pose proof (c1_s3 cx rest HC) as A19.
pose proof (c1_s5 cx rest HC) as A21. pose proof (c1_s7 cx rest HC) as A23.
pose proof (c1_s10 cx rest HC) as A26. pose proof (c1_s11 cx rest HC) as A27.
pose proof (c1_c40 cx rest HC) as C40.
destruct HMID as (HJ3 & Hio3 & Hk3 & M13 & M20 & M28 & M15 & V108 & V140 & Hzero & Hkeep3).
destruct HL as (HJ4 & Hio4 & Hk4 & G10 & G11 & G12 & G15 & G16 & G17 & G22 & N0f8 & N0c0 & N148 & Hhdr8 & Vlen &
  Hkeep4).
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + PP_SIZE) -> ~ (R - ESTACK <= a < R) ->
  ~ (R + 0xc0 <= a < R + 0xc8) -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (R + 0x108 <= a < R + 0x110) ->
  ~ (R + 0x140 <= a < R + 0x148) -> ~ (R + 0x148 <= a < R + 0x150) ->
  aview rsegs (w_H (x_W cx)) mem4 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha Hp Hs Hc0 Hf8 H108 H140 H148.
  rewrite (Hkeep4 a Ha ltac:(unfold PP_SIZE in Hp; lia) ltac:(unfold PP_SIZE in Hp; lia) Hf8 Hc0 H148).
  exact (Hkeep3 a Ha Hp Hs H140 H108). }
assert (Rk : forall q, In q [2; 3; 4; 8; 9; 19; 21; 23; 26; 27] ->
  getr regs4 (Z_to_bv 5 q) = getr (x_regs cx) (Z_to_bv 5 q)).
{ intros q Hq. rewrite (Hk4 q ltac:(cbn [In] in Hq |- *; tauto)). apply Hk3. exact Hq. }
unfold rs_cut_hdr.
split; [|split; [|split; [|split; [|split; [exact HIN | split; [exact Hsuf|]]]]]].
- (* the journal and what the segment keeps *)
  unfold rs_core, rs_mid.
  split; [exact HJ4|].
  split; [intros q Hq; destruct Hq as [-> | [-> | ->]]; apply Rk; cbn [In]; w3a_in|].
  split; [reflexivity|]. split; [apply Permutation_refl|].
  split; [exact (same_io_trans _ _ _ Hio3 Hio4)|]. split; [apply mo_le_refl; exact MTL|].
  intros a Ha Hs HE. apply KEEP; [exact Ha | | | | | | |].
  + intros Hp. apply HE. right. exact Hp.
  + intros Hs'. apply Hs. unfold spZ. rewrite H2. unfold w64. rewrite unsigned_lit_small by lia.
    unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  + intros Hx. apply HE. left. w3a_w1.
  + intros Hx. apply HE. left. w3a_w1.
  + intros Hx. apply HE. left. w3a_w1.
  + intros Hx. apply HE. left. w3a_w1.
  + intros Hx. apply HE. left. w3a_w1.
- (* the values at the cut *)
  unfold rs_at_cx, rs_at, rs_L_hdr, rs_cur2. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rl_at rl_xv]; fold pp R.
  + exact G10.
  + exact G12.
  + exact G16.
  + exact G17.
  + rewrite (Rk 21 ltac:(cbn; tauto)). exact A21.
  + rewrite (Rk 8 ltac:(cbn; tauto)). exact A8.
  + rewrite (Rk 9 ltac:(cbn; tauto)). exact A9.
  + rewrite (Rk 19 ltac:(cbn; tauto)). exact A19.
  + rewrite (Rk 27 ltac:(cbn; tauto)). exact A27.
  + exact G22.
  + rewrite (Rk 23 ltac:(cbn; tauto)). exact A23.
  + rewrite (Rk 26 ltac:(cbn; tauto)). exact A26.
  + refine (w3a_val_kept _ _ _ _ _ _ _ _ V140). intros x Hx. apply Hkeep4;
      unfold PP_SIZE, ESTACK in *; lia.
  + refine (w3a_val_kept _ _ _ _ _ _ _ _ C40). intros x Hx. apply KEEP;
      unfold PP_SIZE, ESTACK in *; lia.
  + refine (w3a_val_kept _ _ _ _ _ _ _ _ V108). intros x Hx. apply Hkeep4;
      unfold PP_SIZE, ESTACK in *; lia.
  + exact N148.
  + exact N0c0.
  + exact G11.
  + exact N0f8.
  + exact G15.
  + exact (eq_trans (Hk4 20 ltac:(cbn; tauto)) M20).
  + exact (eq_trans (Hk4 28 ltac:(cbn; tauto)) M28).
- (* the frame's shadow bytes *)
  unfold rs_fsh_at. rewrite w3a_sh_P0.
  apply (rm_fsh_kept rsegs _ _ _ _ _ _ Hfsh). intros i Hi.
  change (Z.of_nat (length role_B_shA)) with 88 in Hi.
  destruct (HFA i ltac:(lia)) as (Ha & Hp & Hs). apply KEEP;
    unfold ESTACK, T_SEG_STK, ASTACK, PP_SIZE in *; lia.
- (* the block's bytes *)
  unfold rs_pp_at. fold pp. rewrite w3a_img_hdr.
  change (garr8 rsegs (mrestrict (w_H (x_W cx)) mem4) pp (rs_u8s (zeros 16384 ++ le64 4 ++ zeros 3352)))
    with (rm_bytes rsegs (w_H (x_W cx)) mem4 pp (zeros 16384 ++ le64 4 ++ zeros 3352)).
  apply rm_bytes_app. split; [|apply rm_bytes_app; split].
  + unfold zeros, NUL. apply rm_memset_bytes. intros i Hi. change (0 mod 256) with 0.
    change (Z.of_nat 16384) with 16384 in Hi.
    destruct (Z_lt_le_dec i 8) as [Hi8|Hi8]; [exact (Hhdr8 i ltac:(lia))|].
    rewrite (Hkeep4 (pp + i)) by (unfold PP_SIZE in *; lia). apply Hzero. unfold PP_SIZE; lia.
  + rewrite length_zeros. unfold le64. apply rm_bytes_of_val.
    change (Z.of_nat 16384) with 16384. replace (pp + 16384) with (pp + 0x4000) by lia. exact Vlen.
  + rewrite length_zeros, length_le64. unfold zeros, NUL. apply rm_memset_bytes. intros i Hi.
    change (Z.of_nat 3352) with 3352 in Hi. change (Z.of_nat 16384) with 16384. change (Z.of_nat 8) with 8.
    change (0 mod 256) with 0. replace (pp + 16384 + 8 + i) with (pp + (16392 + i)) by lia.
    rewrite (Hkeep4 (pp + (16392 + i))) by (unfold PP_SIZE in *; lia). apply Hzero.
    unfold PP_SIZE; lia.
- split; [exact Hsh|]. split; [exact Hnp | exact Hr].
Qed.

Lemma w3a_tail : forall cx POST rest r sh np regs3 mem3 md3,
w3a_c1 cx rest -> w3a_mid cx rest r sh np regs3 mem3 md3 ->
rs_suffix rest r -> sh = rs_sh rest -> np = rs_np rest -> r = rs_r0 rest ->
rs_from_B7 rsegs B MT cx POST rest -> rs_from_BO rsegs B MT cx POST rest ->
SRr rsegs (x_W cx) (cfg_at rsegs 0x80370 regs3 mem3 md3) POST.
Proof.
intros cx POST rest r sh np regs3 mem3 md3 HC HMID Hsuf Hsh Hnp Hr HB7 HBO.
pose proof (w3a_bounds cx rest HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (c1_ppin cx rest HC) as Hppin. pose proof (c1_ppnew cx rest HC) as Hfresh.
pose proof (c1_s1 cx rest HC) as A9. pose proof (c1_s11 cx rest HC) as A27.
pose proof (w3a_present cx rest HC) as HPR. pose proof (c1_R16 cx rest HC) as HR16.
pose proof HMID as HMID'.
destruct HMID' as (HJ & Hio & Hk & M13 & M20 & M28 & M15 & V108 & V140 & Hzero & Hkeep).
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
assert (Hsh7 : 0 <= sh <= 7).
{ subst sh. unfold rs_sh. pose proof (Z.mod_pos_bound (fst (Cursor.fuzz_u8 rest)) 8 ltac:(lia)). lia. }
pose proof RPgSteps.rl_wx as Hwx. pose proof RPgSteps.rl_segs_low as Hsegs.
set (E := Ereg regs3 [Z_to_bv 64 pp]).
assert (E9 : ew E 9%nat = Z_to_bv 64 R)
  by (subst E; rewrite (ew_Ereg_nat regs3 _ 9 (Z_to_bv 5 9) eq_refl), (Hk 9 ltac:(cbn; tauto)); exact A9).
assert (E27 : ew E 27%nat = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs3 _ 27 (Z_to_bv 5 27) eq_refl), (Hk 27 ltac:(cbn; tauto)); exact A27).
assert (E13 : ew E 13%nat = Z_to_bv 64 sh)
  by (subst E; rewrite (ew_Ereg_nat regs3 _ 13 (Z_to_bv 5 13) eq_refl); exact M13).
assert (E32 : ew E 32%nat = Z_to_bv 64 pp) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
assert (Ub9 : bv_unsigned (ew E 9%nat) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (Ub32 : bv_unsigned (ew E 32%nat) = pp)
  by (rewrite E32; apply unsigned_lit_small; unfold PP_SIZE in *; lia).
assert (HAR : AR rsegs B (x_lyc cx) (x_Sc cx) (x_W cx) mem3 md3) by exact (proj1 HJ).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
assert (HS : st_ok rsegs E w3a_ssT
  (restrict (w_H (x_W cx)) (mkst regs3 (Z_to_bv 64 0x80370) mem3 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w3a_ssT. apply (entry_st_ok_full rsegs); try fold E.
  - (* a5 = pp, seated as the extra atom 32 *)
    apply w3a_regs_ok. constructor; [|constructor]. split; [apply w3a_nz; lia|].
    cbn [fst snd]. rewrite M15. apply (w3a_den_off0 E 32 pp E32). unfold PP_SIZE in *; lia.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (rm_rw_region rsegs E (w_H (x_W cx)) mem3 32 pp);
        [exact Ub32 | lia | unfold PP_SIZE in *; lia
         | intros o Ho; exact (HPR _ _ _ _ _ HAR Hppin o ltac:(unfold PP_SIZE; lia)) |].
      constructor; [|constructor]. intros i Hi.
      cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len cbyte] in Hi |- *.
      exists (Z_to_bv 8 0). split; [reflexivity|]. apply rm_aview_mbyte. rewrite Z.add_0_r.
      exact (Hzero i ltac:(unfold PP_SIZE; lia)).
    + apply (rm_rw_region rsegs E (w_H (x_W cx)) mem3 32 pp);
        [exact Ub32 | lia | unfold PP_SIZE in *; lia
         | intros o Ho; exact (HPR _ _ _ _ _ HAR Hppin o ltac:(unfold PP_SIZE; lia)) |].
      constructor; [|constructor]. intros i Hi.
      cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len cbyte] in Hi |- *.
      exists (Z_to_bv 8 0). split; [reflexivity|]. apply rm_aview_mbyte.
      replace (pp + 16384 + i) with (pp + (16384 + i)) by lia.
      exact (Hzero (16384 + i) ltac:(unfold PP_SIZE; lia)).
    + apply (rm_rw_region rsegs E (w_H (x_W cx)) mem3 9 R); [exact Ub9 | lia | lia
        | intros o Ho; apply Hstkp; lia |]. apply Forall_nil.
    + apply (rm_rw_region rsegs E (w_H (x_W cx)) mem3 9 R); [exact Ub9 | lia | lia
        | intros o Ho; apply Hstkp; lia |]. apply Forall_nil.
    + apply (rm_rw_region rsegs E (w_H (x_W cx)) mem3 9 R); [exact Ub9 | lia | lia
        | intros o Ho; apply Hstkp; lia |]. apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map].
    unfold extent_of_region, w3a_rA, w3a_rB, w3a_rN, w3a_rQ, w3a_rT.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. w3a_foldE E. rewrite Ub32, Ub9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold PP_SIZE in *. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    w3a_foldE E. rewrite E9, E27, E13, E32.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF, PP_SIZE in *; lia).
    change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    unfold SHADOW_OFF, W3CEIL_LO, W3CEIL_HI, PP_SIZE in *. repeat split; lia. }
assert (SHOK : sh_ok rsegs W3Bx W3SH E (mrestrict (w_H (x_W cx)) mem3)).
{ constructor; [|constructor]. unfold W3Bx. split; cbn [she_m she_lo she_hi].
  + w3a_foldE E.
    rewrite (w3a_U_lit E 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)),
      (w3a_U_lit E 32 pp E32 ltac:(unfold PP_SIZE in *; lia) 0 ltac:(unfold PP_SIZE in *; lia)),
      !Z.add_0_r.
    rewrite <- (aview_rd_of rsegs). rewrite Z.sub_0_r.
    exact (proj1 (rm_blk_ra rsegs B (x_lyc cx) (x_Sc cx) (x_W cx) mem3 md3 pp PP_SIZE pp PP_SIZE
      HAR Hppin ltac:(lia) ltac:(reflexivity))).
  + unfold app_apart. intros a Ha. cbn [she_m she_lo she_hi] in Ha. w3a_foldE E. w3a_foldEH E Ha.
    rewrite (w3a_U_lit E 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)).
    rewrite (w3a_U_lit E 32 pp E32 ltac:(unfold PP_SIZE in *; lia) 0 ltac:(unfold PP_SIZE in *; lia)) in Ha.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, PP_SIZE in *. lia. }
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 pp]) E) by apply env_agree_refl.
unfold cfg_at. change (w64 0x80370) with (Z_to_bv 64 0x80370).
aj_run_to_tok w3a_tbl_ok HS HJ SHOK W3span 0x8045c.
{ w3a_awr pp R Ub32 Ub9 Hppin Hfresh. }
(* the second bound test of pod_put32, `bgeu a0,a7` 0x803ec (a0 = ~pp from R+0xf8, a7 = len = 0): no unsigned word
   is below 0 *)
srr_branch_tok w3a_tbl_ok HS SHOK W3span.
2:{ exfalso. exact (w3a_geu0 E _ Hc). }
aj_run_to_tok w3a_tbl_ok HS HJ SHOK W3span 0x8045c.
{ w3a_awr pp R Ub32 Ub9 Hppin Hfresh. }
srr_branch_tok w3a_tbl_ok HS SHOK W3span.
- (* the shape is not 7: the Object header BO *)
  pose proof (w3a_bne_ne E 13 sh E13 Hsh7 Hc0) as Hne.
  aj_run_to_tok w3a_tbl_ok HS HJ SHOK W3span 0x804f0.
  { w3a_awr pp R Ub32 Ub9 Hppin Hfresh. }
  pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms1 HS eq_refl) as Ems.
  cbn [ss_pc] in Ems. rewrite Ems.
  apply (HBO (x_lyc cx) (x_Sc cx) (x_W cx) (ms_regs ms1) (ms_mem ms1) _ r sh np);
    split; [|split; [|exact Hne]].
  2:{ unfold rs_at_cx, rs_at. repeat apply Forall_cons; try apply Forall_nil.
      cbn [fst snd rl_at rl_xv]. rewrite <- M13.
      eapply (w3a_reg_atom E _ ms1 (w_H (x_W cx)) regs3 _ _ HS (env_agree_refl 32 _));
        vm_compute; reflexivity. }
  apply (w3a_hdr_of cx rest r sh np regs3 mem3 md3 _ _ _ HC HMID); try assumption.
  w3a_rgn HS 0%nat HR0. w3a_rgn HS 1%nat HR1. w3a_rgn HS 2%nat HR2. w3a_rgn HS 3%nat HR3.
  w3a_rgn HS 4%nat HR4.
  unfold w3a_leafT. fold pp R.
  split; [exact HJ|]. split; [apply RPgSteps.same_io_wvb|].
  split.
  { intros q Hq. cbn [In] in Hq.
    repeat (destruct Hq as [<- | Hq];
      [eapply (w3a_reg_atom E _ ms1 (w_H (x_W cx)) regs3 _ _ HS (env_agree_refl 32 _)); vm_compute; reflexivity|]).
    destruct Hq. }
  split; [w3a_reg HS; reflexivity|].
  split; [w3a_reg HS; reflexivity|].
  split; [w3a_reg HS; apply w3a_lit_a2|].
  split; [w3a_reg HS; apply w3a_den_off0; [exact E32 | unfold PP_SIZE in *; lia]|].
  split; [w3a_reg HS; apply w3a_den_off0; [exact E32 | unfold PP_SIZE in *; lia]|].
  split; [w3a_reg HS; reflexivity|].
  split; [w3a_reg HS; apply (w3a_den_off E 32 pp 16384 E32); unfold PP_SIZE in *; lia|].
  split; [apply (w3a_slot E _ 9 R _ _ _ _ _ 0xf8 w3a_nx _ HR2 Ub9);
    [w3a_in | apply (w3a_den_nx E pp E32); unfold PP_SIZE in *; lia]|].
  split; [apply (w3a_slot E _ 9 R _ _ _ _ _ 0xc0 (SLit 18446744073709535235) _ HR3 Ub9);
    [w3a_in | apply w3a_lit_neg]|].
  split; [apply (w3a_slot E _ 9 R _ _ _ _ _ 0x148 w3a_shx _ HR4 Ub9);
    [w3a_in | apply (w3a_den_sh E pp E32 E27); unfold PP_SIZE in *; lia]|].
  split.
  { intros i Hi. assert (Hc8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ (4 <= i < 8)) by lia.
    destruct Hc8 as [-> | [-> | [-> | [-> | Hc8]]]].
    - exact (w3a_lit_at E _ _ 32 _ _ _ _ _ _ 0 0 HR0 Ub32 ltac:(w3a_in)).
    - exact (w3a_lit_at E _ _ 32 _ _ _ _ _ _ 1 0 HR0 Ub32 ltac:(w3a_in)).
    - exact (w3a_lit_at E _ _ 32 _ _ _ _ _ _ 2 0 HR0 Ub32 ltac:(w3a_in)).
    - exact (w3a_lit_at E _ _ 32 _ _ _ _ _ _ 3 0 HR0 Ub32 ltac:(w3a_in)).
    - replace i with (4 + (i - 4)) by lia. rewrite Z.add_assoc.
      exact (w3a_zero_at E _ _ 32 _ _ _ _ _ _ 4 4 (i - 4) HR0 Ub32 ltac:(w3a_in) ltac:(lia)). }
  split; [exact (w3a_slot E _ 32 pp _ _ _ _ _ 0x4000 (SLit 4) 4 HR1 Ub32 ltac:(w3a_in) eq_refl)|].
  intros a Ha H1 H2 H3 H4 H5. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms0) a).
  { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms0) (ms_mem ms1)
      (fun a => (pp <= a < pp + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf8 <= a < R + 0x100) \/
                (R + 0xc0 <= a < R + 0xc8) \/ (R + 0x148 <= a < R + 0x150))
      HFr1); [w3a_kwr E Ub32 Ub9 | exact Ha | lia]. }
  transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
  { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
      (fun a => (pp <= a < pp + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf8 <= a < R + 0x100) \/
                (R + 0xc0 <= a < R + 0xc8) \/ (R + 0x148 <= a < R + 0x150))
      HFr0); [w3a_kwr E Ub32 Ub9 | exact Ha | lia]. }
  { apply (w3a_keep_run E _ (w_H (x_W cx)) mem3 (ms_mem ms)
      (fun a => (pp <= a < pp + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf8 <= a < R + 0x100) \/
                (R + 0xc0 <= a < R + 0xc8) \/ (R + 0x148 <= a < R + 0x150))
      HFr); [w3a_kwr E Ub32 Ub9 | exact Ha | lia]. }
- (* the shape is 7: the shape-7 header B7 *)
  pose proof (w3a_bne_eq E 13 sh E13 Hsh7 Hc0) as Heq7.
  aj_run_to_tok w3a_tbl_ok HS HJ SHOK W3span 0x8045c.
  { w3a_awr pp R Ub32 Ub9 Hppin Hfresh. }
  pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms1 HS eq_refl) as Ems.
  cbn [ss_pc] in Ems. rewrite Ems.
  apply (HB7 (x_lyc cx) (x_Sc cx) (x_W cx) (ms_regs ms1) (ms_mem ms1) _ r np).
  unfold rs_cut_B7. rewrite <- Heq7.
  apply (w3a_hdr_of cx rest r sh np regs3 mem3 md3 _ _ _ HC HMID); try assumption.
  w3a_rgn HS 0%nat HR0. w3a_rgn HS 1%nat HR1. w3a_rgn HS 2%nat HR2. w3a_rgn HS 3%nat HR3.
  w3a_rgn HS 4%nat HR4.
  unfold w3a_leafT. fold pp R.
  split; [exact HJ|]. split; [apply RPgSteps.same_io_wvb|].
  split.
  { intros q Hq. cbn [In] in Hq.
    repeat (destruct Hq as [<- | Hq];
      [eapply (w3a_reg_atom E _ ms1 (w_H (x_W cx)) regs3 _ _ HS (env_agree_refl 32 _)); vm_compute; reflexivity|]).
    destruct Hq. }
  split; [w3a_reg HS; reflexivity|].
  split; [w3a_reg HS; reflexivity|].
  split; [w3a_reg HS; apply w3a_lit_a2|].
  split; [w3a_reg HS; apply w3a_den_off0; [exact E32 | unfold PP_SIZE in *; lia]|].
  split; [w3a_reg HS; apply w3a_den_off0; [exact E32 | unfold PP_SIZE in *; lia]|].
  split; [w3a_reg HS; reflexivity|].
  split; [w3a_reg HS; apply (w3a_den_off E 32 pp 16384 E32); unfold PP_SIZE in *; lia|].
  split; [apply (w3a_slot E _ 9 R _ _ _ _ _ 0xf8 w3a_nx _ HR2 Ub9);
    [w3a_in | apply (w3a_den_nx E pp E32); unfold PP_SIZE in *; lia]|].
  split; [apply (w3a_slot E _ 9 R _ _ _ _ _ 0xc0 (SLit 18446744073709535235) _ HR3 Ub9);
    [w3a_in | apply w3a_lit_neg]|].
  split; [apply (w3a_slot E _ 9 R _ _ _ _ _ 0x148 w3a_shx _ HR4 Ub9);
    [w3a_in | apply (w3a_den_sh E pp E32 E27); unfold PP_SIZE in *; lia]|].
  split.
  { intros i Hi. assert (Hc8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ (4 <= i < 8)) by lia.
    destruct Hc8 as [-> | [-> | [-> | [-> | Hc8]]]].
    - exact (w3a_lit_at E _ _ 32 _ _ _ _ _ _ 0 0 HR0 Ub32 ltac:(w3a_in)).
    - exact (w3a_lit_at E _ _ 32 _ _ _ _ _ _ 1 0 HR0 Ub32 ltac:(w3a_in)).
    - exact (w3a_lit_at E _ _ 32 _ _ _ _ _ _ 2 0 HR0 Ub32 ltac:(w3a_in)).
    - exact (w3a_lit_at E _ _ 32 _ _ _ _ _ _ 3 0 HR0 Ub32 ltac:(w3a_in)).
    - replace i with (4 + (i - 4)) by lia. rewrite Z.add_assoc.
      exact (w3a_zero_at E _ _ 32 _ _ _ _ _ _ 4 4 (i - 4) HR0 Ub32 ltac:(w3a_in) ltac:(lia)). }
  split; [exact (w3a_slot E _ 32 pp _ _ _ _ _ 0x4000 (SLit 4) 4 HR1 Ub32 ltac:(w3a_in) eq_refl)|].
  intros a Ha H1 H2 H3 H4 H5. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms0) a).
  { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms0) (ms_mem ms1)
      (fun a => (pp <= a < pp + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf8 <= a < R + 0x100) \/
                (R + 0xc0 <= a < R + 0xc8) \/ (R + 0x148 <= a < R + 0x150))
      HFr1); [w3a_kwr E Ub32 Ub9 | exact Ha | lia]. }
  transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
  { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
      (fun a => (pp <= a < pp + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf8 <= a < R + 0x100) \/
                (R + 0xc0 <= a < R + 0xc8) \/ (R + 0x148 <= a < R + 0x150))
      HFr0); [w3a_kwr E Ub32 Ub9 | exact Ha | lia]. }
  { apply (w3a_keep_run E _ (w_H (x_W cx)) mem3 (ms_mem ms)
      (fun a => (pp <= a < pp + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf8 <= a < R + 0x100) \/
                (R + 0xc0 <= a < R + 0xc8) \/ (R + 0x148 <= a < R + 0x150))
      HFr); [w3a_kwr E Ub32 Ub9 | exact Ha | lia]. }
Qed.

(* =============================== the head: 0x802dc to the join =============================== *)
(* the input bytes and their shadow cells, at the memory the memset left *)
Lemma w3a_byte_at2 : forall cx rest regs2 mem2 md2 i,
w3a_c1 cx rest -> w3a_m1_post cx regs2 mem2 md2 -> (i < length rest)%nat ->
aview rsegs (w_H (x_W cx)) mem2 (e_src (x_e cx) + Z.of_nat i) = Some (bv_unsigned (nth i rest (Z_to_bv 8 0))).
Proof.
intros cx rest regs2 mem2 md2 i HC HM Hi.
pose proof (w3a_bounds cx rest HC) as (_ & H4096 & Hpc & Happ & HRlo & HRS & H47 & _ & _ & Hceil).
pose proof (c1_in cx rest HC) as (Hleft & Hbytes & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hap).
destruct HM as (_ & _ & _ & _ & _ & _ & Hkeep2).
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo.
assert (HB : rm_bytes rsegs (w_H (x_W cx)) (x_memc cx) (e_src (x_e cx)) rest) by exact Hbytes.
rewrite Hkeep2; [exact (proj1 (rm_bytes_aview rsegs _ _ _ _) HB i Hi) | | | |].
- unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia.
- exact (proj2 (proj2 (Hap (e_src (x_e cx) + Z.of_nat i) ltac:(lia)))).
- pose proof (proj1 (Hap (e_src (x_e cx) + Z.of_nat i) ltac:(lia))) as Hns.
  unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
- pose proof (proj1 (proj2 (Hap (e_src (x_e cx) + Z.of_nat i) ltac:(lia)))) as Hnw.
  intros Hx. apply Hnw. w3a_w1.
Qed.

Lemma w3a_cell_at2 : forall cx rest regs2 mem2 md2 x,
w3a_c1 cx rest -> w3a_m1_post cx regs2 mem2 md2 -> 0 <= x < kHighMemEnd ->
aview rsegs (w_H (x_W cx)) mem2 (shadow_of_addr SHADOW_OFF x) =
aview rsegs (w_H (x_W cx)) (x_memc cx) (shadow_of_addr SHADOW_OFF x).
Proof.
intros cx rest regs2 mem2 md2 x HC HM Hx.
pose proof (w3a_bounds cx rest HC) as (_ & H4096 & Hpc & Happ & HRlo & HRS & H47 & _ & _ & Hceil).
destruct HM as (_ & _ & _ & _ & _ & _ & Hkeep2).
pose proof (rm_shadow_band x Hx) as Hband.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo.
apply Hkeep2.
- unfold kLowMemEnd, kHighMemBeg in Hband. lia.
- exact (rm_shadow_not_app x (e_pp (x_e cx)) PP_SIZE Hx Happ).
- intros Hc. apply (rm_shadow_not_high x (e_R (x_e cx) - ESTACK) Hx
    ltac:(unfold kHighMemBeg, ESTACK in *; lia)). lia.
- intros Hc. apply (rm_shadow_not_high x (e_R (x_e cx) + 0x140) Hx
    ltac:(unfold kHighMemBeg in *; lia)). lia.
Qed.

(* the input lies apart from the real-frame window the head reads and writes *)
Lemma w3a_in_apart_R : forall cx rest x, w3a_c1 cx rest ->
e_src (x_e cx) <= x < e_src (x_e cx) + e_left (x_e cx) ->
~ (e_R (x_e cx) + 0x48 <= x < e_R (x_e cx) + 0x160).
Proof.
intros cx rest x HC Hx. pose proof (c1_in cx rest HC) as (_ & _ & _ & _ & _ & _ & _ & Hap).
destruct (Hap x Hx) as (_ & Hnw & _). intros Hc. apply Hnw. w3a_w1.
Qed.

Lemma w3a_src_range : forall cx rest, w3a_c1 cx rest ->
0 < e_src (x_e cx) /\ e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 /\
(e_src (x_e cx) + e_left (x_e cx) <= kLowMemEnd - 1 \/ kHighMemBeg <= e_src (x_e cx)).
Proof.
intros cx rest HC. pose proof (c1_in cx rest HC) as (_ & _ & _ & _ & Hamr & Hsrc0 & _ & _).
unfold amem_range, kHighMemEnd in Hamr. unfold kLowMemEnd, kHighMemBeg in *. lia.
Qed.

Lemma w3a_div8_same : forall x, 0 <= x -> x mod 8 <> 7 -> (x + 1) / 8 = x / 8.
Proof.
intros x Hx Hne. pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
replace (x + 1) with (x / 8 * 8 + (x mod 8 + 1)) by lia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small (x mod 8 + 1) 8) by lia. lia.
Qed.
Lemma w3a_div8_next : forall x, 0 <= x -> x mod 8 = 7 -> (x + 1) / 8 = x / 8 + 1.
Proof.
intros x Hx He. pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm.
replace (x + 1) with ((x / 8 + 1) * 8 + 0) by lia.
rewrite Z.div_add_l by lia. rewrite Zdiv_0_l. lia.
Qed.

(* the alias that resolves a shadow load of the cursor to its cell *)
Lemma w3a_alias_cell : forall E (n : nat) src c sa,
ew E 20 = Z_to_bv 64 src -> ew E 27 = Z_to_bv 64 SHADOW_OFF -> ew E n = Z_to_bv 64 sa ->
0 <= src -> 0 <= c -> src + c < 2 ^ 47 -> sa = SHADOW_OFF + (src + c) / 8 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 c) (SLit 3)) (SOff 27 0)) = sv_denot E (SOff n 0).
Proof.
intros E n src c sa H20 H27 Hn Hs Hc Hsc Hsa. apply U_inj.
pose proof (Z.div_pos (src + c) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound (src + c) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
rewrite U_SAlu, (w3a_U_srl3 E 20 src c H20 ltac:(lia) ltac:(lia)),
  (w3a_U_lit E 27 SHADOW_OFF H27 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)),
  (w3a_U_lit E n sa Hn ltac:(unfold SHADOW_OFF in *; lia) 0 ltac:(unfold SHADOW_OFF in *; lia)).
cbn [zalu_raw]. rewrite !Z.add_0_r. rewrite Hsa.
rewrite (zcanon_id ((src + c) / 8 + SHADOW_OFF)) by (unfold M64, SHADOW_OFF in *; lia). lia.
Qed.

(* the symbolic state at 0x802dc, over the memory the memset left: the property-count cell R+0x108 (written) and
   pp's cell R+0x140 (read back into a5) first, then the arm's own regions rs *)
Lemma w3a_seatH : forall cx rest regs2 mem2 md2 ov rs fs al (xs : list word),
w3a_c1 cx rest -> w3a_m1_post cx regs2 mem2 md2 ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs2 xs) (snd p) = getr regs2 (fst p)) ov ->
regions_wf rs = true ->
Forall (region_ok rsegs (Ereg regs2 xs) (mrestrict (w_H (x_W cx)) mem2)) rs ->
pairwise_disjoint (Ereg regs2 xs) ([w3a_rR108; w3a_rP] ++ rs) ->
atoms_ok (Ereg regs2 xs) fs -> alias_ok (Ereg regs2 xs) al ->
st_ok rsegs (Ereg regs2 xs) (w3a_ssH ov rs fs al)
  (restrict (w_H (x_W cx)) (mkst regs2 (Z_to_bv 64 0x802dc) mem2 (seg_rom rsegs))).
Proof.
intros cx rest regs2 mem2 md2 ov rs fs al xs HC HM Hov Hwf Hrs Hpd Hfs Hal.
pose proof (w3a_bounds cx rest HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (c1_s1 cx rest HC) as A9. pose proof (c1_s11 cx rest HC) as A27.
pose proof (c1_s4 cx rest HC) as A20. pose proof (c1_R16 cx rest HC) as HR16.
pose proof (w3a_src_range cx rest HC) as (Hsrc0 & Hsrc47 & _).
pose proof HM as (HJ2 & Hio2 & Hk2 & Ha02 & V140 & Hzero & Hkeep2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
set (E := Ereg regs2 xs).
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
assert (E9 : ew E 9%nat = Z_to_bv 64 (e_R (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)); exact A9).
assert (E27 : ew E 27%nat = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), (Hk2 27 ltac:(cbn; tauto)); exact A27).
assert (E20 : ew E 20%nat = Z_to_bv 64 (e_src (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl), (Hk2 20 ltac:(cbn; tauto)); exact A20).
assert (E10 : ew E 10%nat = Z_to_bv 64 (e_pp (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact Ha02).
assert (Ub9 : bv_unsigned (ew E 9%nat) = e_R (x_e cx)) by (rewrite E9; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold w3a_ssH. apply (entry_st_ok_full rsegs); try fold E.
- apply w3a_regs_ok. exact Hov.
- change (regions_wf ([w3a_rR108; w3a_rP] ++ rs))
    with (region_wf w3a_rR108 && (region_wf w3a_rP && regions_wf rs))%bool.
  rewrite Hwf. vm_compute. reflexivity.
- apply Forall_app. split; [|exact Hrs].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (rm_rw_region rsegs E (w_H (x_W cx)) mem2 9 (e_R (x_e cx)));
      [exact Ub9 | lia | lia | intros o Ho; apply Hstkp; lia |]. apply Forall_nil.
  + apply (rm_ro_region rsegs E (w_H (x_W cx)) mem2 9 (e_R (x_e cx))); [exact Ub9 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ (e_R (x_e cx)) 0x140 8 (SOff 10 0) (e_pp (x_e cx) mod 2 ^ 64));
      [| pose proof (Z.mod_pos_bound (e_pp (x_e cx)) (2 ^ 64) ltac:(lia)); cbn; lia | cbn; lia | exact V140].
    apply bv_eq. rewrite denot_SOff, E10. rewrite unsigned_lit_small by (unfold PP_SIZE in *; lia).
    rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
- exact Hpd.
- split; [|split; [exact I | exact Hal]].
  assert (Hleft0 : 0 <= e_left (x_e cx)).
  { pose proof (c1_in cx rest HC) as (Hleft & _). rewrite Hleft. apply Zle_0_nat. }
  apply w3a_atoms_app; [|exact Hfs]. cbn [w3a_af0 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  w3a_foldE E. rewrite E9, E27, E20.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF, PP_SIZE in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
  unfold SHADOW_OFF, W3CEIL_LO, W3CEIL_HI, PP_SIZE in *. repeat split; lia.
Qed.

(* ---- no input byte left: `beqz s6` 0x802dc -> 0x80328 ---- *)
Lemma w3a_head0 : forall cx (Q : world rsegs -> config -> Prop) regs2 mem2 md2,
w3a_c1 cx [] -> w3a_m1_post cx regs2 mem2 md2 ->
(forall regs3 mem3 md3, w3a_mid cx [] [] 0 0 regs3 mem3 md3 ->
  SRr rsegs (x_W cx) (cfg_at rsegs 0x80370 regs3 mem3 md3) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs 0x802dc regs2 mem2 md2) Q.
Proof.
intros cx Q regs2 mem2 md2 HC HM K.
pose proof (w3a_bounds cx [] HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (c1_in cx [] HC) as (Hleft & _ & _ & _ & _ & _ & _ & _).
pose proof (c1_s6 cx [] HC) as A22.
pose proof (c1_ppin cx [] HC) as Hppin. pose proof (c1_ppnew cx [] HC) as Hfresh.
pose proof (c1_s1 cx [] HC) as A9.
pose proof (w3a_src_range cx [] HC) as (Hsrc0 & Hsrc47 & Hsrcband).
pose proof HM as (HJ2 & Hio2 & Hk2 & Ha02 & V140 & Hzero & Hkeep2).
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof RPgSteps.rl_wx as Hwx. pose proof RPgSteps.rl_segs_low as Hsegs.
set (E := Ereg regs2 (w3a_xs (e_src (x_e cx)) 0 0 0 0 0)).
assert (E9 : ew E 9%nat = Z_to_bv 64 R)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)); exact A9).
assert (E10 : ew E 10%nat = Z_to_bv 64 pp)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact Ha02).
assert (Ub9 : bv_unsigned (ew E 9%nat) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (Hs6 : getr regs2 (Z_to_bv 5 22) = w64 0)
  by (rewrite (Hk2 22 ltac:(cbn; tauto)), A22, Hleft; reflexivity).
pose proof (w3a_seatH cx [] regs2 mem2 md2 [(Z_to_bv 5 22, SLit 0)] [] [] []
  (w3a_xs (e_src (x_e cx)) 0 0 0 0 0) HC HM) as HS.
specialize (HS ltac:(constructor; [|constructor]; split;
  [apply w3a_nz; lia | cbn [fst snd]; rewrite Hs6; apply (w3a_den_lit E 0); lia])).
specialize (HS ltac:(reflexivity) ltac:(apply Forall_nil)).
specialize (HS ltac:(apply pairwise_disjoint_of_extents; cbn [app map];
  unfold extent_of_region, w3a_rR108, w3a_rP; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia)).
specialize (HS ltac:(exact I) ltac:(exact I)).
fold E in HS.
assert (SHOK : sh_ok rsegs W3Bx [] E (mrestrict (w_H (x_W cx)) mem2)) by apply Forall_nil.
unfold cfg_at. change (w64 0x802dc) with (Z_to_bv 64 0x802dc).
aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
{ w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
apply K. w3a_rgn HS 0%nat HR0.
apply (w3a_mid_of cx [] [] 0 0 regs2 mem2 md2 _ _ _ HC HM).
- exact HJ2.
- apply RPgSteps.same_io_wvb.
- intros q Hq. cbn [In] in Hq.
  repeat (destruct Hq as [<- | Hq];
    [eapply (w3a_reg_atom E _ ms (w_H (x_W cx)) regs2 _ _ HS (env_agree_refl 32 _)); vm_compute; reflexivity|]).
  destruct Hq.
- w3a_reg HS. apply (w3a_den_lit E 0). lia.
- w3a_reg HS. unfold rs_cur. cbn [length Z.of_nat]. rewrite Z.add_0_r, Z.sub_0_r.
  apply (w3a_den_off0 E 20 (e_src (x_e cx))).
  + subst E. rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl), (Hk2 20 ltac:(cbn; tauto)).
    exact (c1_s4 cx [] HC).
  + lia.
- w3a_reg HS. cbn [length Z.of_nat]. apply (w3a_den_lit E 0). lia.
- w3a_reg HS. apply (w3a_den_off0 E 10 pp E10). unfold PP_SIZE in *; lia.
- apply (w3a_slot E _ 9 R _ _ _ _ _ 0x108 (SLit 0) 0 HR0 Ub9); [w3a_in | apply (w3a_den_lit E 0); lia].
- intros a Ha H108. apply (w3a_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
    (fun a => R + 0x108 <= a < R + 0x110) HFr);
  [w3a_kwr E Ub9 Ub9 | exact Ha | lia].
Qed.

(* ---- the leaf of a head arm at 0x80370: the eight facts w3a_mid_of asks besides the kept bytes ---- *)
Ltac w3a_lf K HC HM HS HR0 E sht curt lent ppt npt :=
  apply K; w3a_rgn HS 0%nat HR0;
  apply (w3a_mid_of _ _ _ _ _ _ _ _ _ _ _ HC HM);
  [ assumption
  | apply RPgSteps.same_io_wvb
  | let q := fresh "q" in let Hq := fresh "Hq" in
    intros q Hq; cbn [In] in Hq;
    repeat (destruct Hq as [<- | Hq];
      [eapply (w3a_reg_atom E _ _ _ _ _ _ HS (env_agree_refl 32 _)); vm_compute; reflexivity|]);
    destruct Hq
  | w3a_reg HS; sht
  | w3a_reg HS; curt
  | w3a_reg HS; lent
  | w3a_reg HS; ppt
  | npt
  | ].

(* ---- exactly one input byte: the shape read, then `bne s6,1` 0x80314 -> 0x80318 ---- *)
Lemma w3a_head1 : forall cx (Q : world rsegs -> config -> Prop) b0 regs2 mem2 md2,
w3a_c1 cx [b0] -> w3a_m1_post cx regs2 mem2 md2 ->
(forall regs3 mem3 md3, w3a_mid cx [b0] [] (rs_sh [b0]) 0 regs3 mem3 md3 ->
  SRr rsegs (x_W cx) (cfg_at rsegs 0x80370 regs3 mem3 md3) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs 0x802dc regs2 mem2 md2) Q.
Proof.
intros cx Q b0 regs2 mem2 md2 HC HM K.
pose proof (w3a_bounds cx [b0] HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (c1_in cx [b0] HC) as (Hleft & _ & Hra & _ & Hamr & _ & _ & _).
pose proof (c1_s6 cx [b0] HC) as A22.
pose proof (c1_ppin cx [b0] HC) as Hppin. pose proof (c1_ppnew cx [b0] HC) as Hfresh.
pose proof (c1_s1 cx [b0] HC) as A9. pose proof (c1_s4 cx [b0] HC) as A20. pose proof (c1_s11 cx [b0] HC) as A27.
pose proof (w3a_src_range cx [b0] HC) as (Hsrc0 & Hsrc47 & Hsrcband).
cbn [length] in Hleft. change (Z.of_nat 1) with 1 in Hleft.
rewrite Hleft in Hsrc47, Hsrcband.
pose proof (w3a_in_apart_R cx [b0] (e_src (x_e cx)) HC ltac:(lia)) as Hap48.
pose proof HM as (HJ2 & Hio2 & Hk2 & Ha02 & V140 & Hzero & Hkeep2).
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof RPgSteps.rl_wx as Hwx. pose proof RPgSteps.rl_segs_low as Hsegs.
destruct (Hra (e_src (x_e cx)) ltac:(lia)) as (s0 & Hs0 & Hok0).
assert (Hs07 : 0 <= s0 <= 7).
{ destruct Hok0 as [->|(Hq1 & Hq2)]; [lia|].
  pose proof (Z.mod_pos_bound (e_src (x_e cx)) 8 ltac:(lia)). lia. }
pose proof (w3a_byte_at2 cx [b0] regs2 mem2 md2 0%nat HC HM ltac:(cbn; lia)) as Hb0at.
cbn [nth] in Hb0at. rewrite Z.add_0_r in Hb0at.
pose proof (w3a_cell_at2 cx [b0] regs2 mem2 md2 (e_src (x_e cx)) HC HM ltac:(unfold kHighMemEnd; lia)) as Hc0at.
rewrite Hs0 in Hc0at.
pose proof (rm_shadow_band (e_src (x_e cx)) ltac:(unfold kHighMemEnd; lia)) as Hband0.
unfold kLowMemEnd, kHighMemBeg in Hband0, Hsrcband.
pose proof (rm_byte_range b0) as Hb0r.
set (E := Ereg regs2 (w3a_xs (e_src (x_e cx)) s0 0 0 (bv_unsigned b0) 0)).
assert (E9 : ew E 9%nat = Z_to_bv 64 R)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)); exact A9).
assert (E27 : ew E 27%nat = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), (Hk2 27 ltac:(cbn; tauto)); exact A27).
assert (E20 : ew E 20%nat = Z_to_bv 64 (e_src (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl), (Hk2 20 ltac:(cbn; tauto)); exact A20).
assert (E10 : ew E 10%nat = Z_to_bv 64 pp)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact Ha02).
assert (E32 : ew E 32%nat = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (e_src (x_e cx))))
  by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33%nat = Z_to_bv 64 s0) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E36 : ew E 36%nat = Z_to_bv 64 (bv_unsigned b0)) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
assert (Ub9 : bv_unsigned (ew E 9%nat) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (Ub20 : bv_unsigned (ew E 20%nat) = e_src (x_e cx)) by (rewrite E20; apply unsigned_lit_small; lia).
assert (Ub32 : bv_unsigned (ew E 32%nat) = shadow_of_addr SHADOW_OFF (e_src (x_e cx)))
  by (rewrite E32; apply unsigned_lit_small; unfold shadow_of_addr in *; lia).
assert (Hs6 : getr regs2 (Z_to_bv 5 22) = w64 1)
  by (rewrite (Hk2 22 ltac:(cbn; tauto)), A22, Hleft; reflexivity).
pose proof (w3a_seatH cx [b0] regs2 mem2 md2 [(Z_to_bv 5 22, SLit 1)] [w3a_rIn0; w3a_rC0]
  [(33%nat, mkAF 0 7 0); (36%nat, mkAF 0 255 0)] [(w3a_e0, SOff 32 0)]
  (w3a_xs (e_src (x_e cx)) s0 0 0 (bv_unsigned b0) 0) HC HM) as HS.
specialize (HS ltac:(constructor; [|constructor]; split;
  [apply w3a_nz; lia | cbn [fst snd]; rewrite Hs6; apply (w3a_den_lit E 1); lia])).
specialize (HS ltac:(vm_compute; reflexivity)).
specialize (HS ltac:(constructor; [|constructor; [|constructor]]; unfold w3a_rIn0, w3a_rC0;
  [ apply (rm_ro_region rsegs E (w_H (x_W cx)) mem2 20 (e_src (x_e cx))); [exact Ub20 | lia | lia |];
    constructor; [|constructor];
    apply (chunk_ok_val rsegs E _ (e_src (x_e cx)) 0 1 (SOff 36 0) (bv_unsigned b0));
    [apply (w3a_den_off0 E 36 (bv_unsigned b0) E36); lia
    | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |];
    change (N.to_nat 1) with 1%nat; rewrite Z.add_0_r;
    exact (proj1 (rm_aview_val1 rsegs (w_H (x_W cx)) mem2 _ _ Hb0at))
  | exact (rm_cell_region rsegs E (w_H (x_W cx)) mem2 32 (shadow_of_addr SHADOW_OFF (e_src (x_e cx))) s0
      (SOff 33 0) Ub32 Hc0at (w3a_den_off0 E 33 s0 E33 ltac:(lia)) ltac:(unfold shadow_of_addr in *; lia)
      ltac:(unfold shadow_of_addr in *; lia)) ])).
specialize (HS ltac:(apply pairwise_disjoint_of_extents; cbn [app map];
  unfold extent_of_region, w3a_rR108, w3a_rP, w3a_rIn0, w3a_rC0;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  w3a_foldE E; rewrite Ub9, Ub20, Ub32; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  unfold shadow_of_addr in *; repeat split; lia)).
specialize (HS ltac:(cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2]; w3a_foldE E;
  rewrite E33, E36, !unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite !Z.mod_1_r;
  repeat split; lia)).
specialize (HS ltac:(cbn [alias_ok]; split; [|exact I]; unfold w3a_e0;
  apply (w3a_alias_cell E 32 (e_src (x_e cx)) 0 (shadow_of_addr SHADOW_OFF (e_src (x_e cx))) E20 E27 E32);
  [lia | lia | lia | unfold shadow_of_addr; rewrite Z.add_0_r; reflexivity])).
fold E in HS.
assert (SHOK : sh_ok rsegs W3Bx [] E (mrestrict (w_H (x_W cx)) mem2)) by apply Forall_nil.
unfold cfg_at. change (w64 0x802dc) with (Z_to_bv 64 0x802dc).
aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
{ w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
srr_branch_tok w3a_tbl_ok HS SHOK W3span.
- (* the shadow byte is 0: the check passes at once *)
  aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
  { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
  pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms0 HS eq_refl) as Ems.
  cbn [ss_pc] in Ems. rewrite Ems.
  w3a_lf K HC HM HS HR0 E
    ltac:(rewrite (w3a_den_and E 36 _ 0 7 E36); [ | lia | lia | lia];
          unfold rs_sh; cbn [Cursor.fuzz_u8 fst]; rewrite Z.add_0_r; rewrite w3a_land7 by lia; reflexivity)
    ltac:(rewrite (w3a_den_off E 20 _ 1 E20);
          [f_equal; unfold rs_cur; cbn [length Z.of_nat]; lia | lia | lia])
    ltac:(cbn [length Z.of_nat]; apply (w3a_den_lit E 0); lia)
    ltac:(apply (w3a_den_off0 E 10 _ E10); unfold PP_SIZE in *; lia)
    ltac:(apply (w3a_slot E _ 9 _ _ _ _ _ _ 0x108 (SLit 0) 0 HR0 Ub9); [w3a_in | apply (w3a_den_lit E 0); lia]).
  intros a Ha H108. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
  { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
      (fun x => R + 0x108 <= x < R + 0x110) HFr0); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
  { apply (w3a_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
      (fun x => R + 0x108 <= x < R + 0x110) HFr); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
- (* the shadow byte is not 0: the slow block 0x82660, then its `bge` *)
  aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
  { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
  srr_branch_tok w3a_tbl_ok HS SHOK W3span.
  + exfalso. exact (w3a_kill E 20 33 (e_src (x_e cx)) s0 0 E20 E33 ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hok0) Hc Hc0).
  + aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
    { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
    pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms1 HS eq_refl) as Ems.
    cbn [ss_pc] in Ems. rewrite Ems.
    w3a_lf K HC HM HS HR0 E
      ltac:(rewrite (w3a_den_and E 36 _ 0 7 E36); [ | lia | lia | lia];
            unfold rs_sh; cbn [Cursor.fuzz_u8 fst]; rewrite Z.add_0_r; rewrite w3a_land7 by lia; reflexivity)
      ltac:(rewrite (w3a_den_off E 20 _ 1 E20);
            [f_equal; unfold rs_cur; cbn [length Z.of_nat]; lia | lia | lia])
      ltac:(cbn [length Z.of_nat]; apply (w3a_den_lit E 0); lia)
      ltac:(apply (w3a_den_off0 E 10 _ E10); unfold PP_SIZE in *; lia)
      ltac:(apply (w3a_slot E _ 9 _ _ _ _ _ _ 0x108 (SLit 0) 0 HR0 Ub9); [w3a_in | apply (w3a_den_lit E 0); lia]).
    intros a Ha H108. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms0) a).
    { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms0) (ms_mem ms1)
        (fun x => R + 0x108 <= x < R + 0x110) HFr1); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
    transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
    { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
        (fun x => R + 0x108 <= x < R + 0x110) HFr0); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
    { apply (w3a_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
        (fun x => R + 0x108 <= x < R + 0x110) HFr); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
Qed.

(* ---- two input bytes or more: both the shape and the property count are read ---- *)
Ltac w3a_lf2 K HC HM HS HR0 E Ub9 E22 E20 E36 E37 E10 Hleft :=
  w3a_lf K HC HM HS HR0 E
    ltac:(rewrite (w3a_den_and E 36 _ 0 7 E36); [ | lia | lia | lia];
          unfold rs_sh; cbn [Cursor.fuzz_u8 fst]; rewrite Z.add_0_r; rewrite w3a_land7 by lia; reflexivity)
    ltac:(rewrite (w3a_den_off E 20 _ 2 E20);
          [f_equal; unfold rs_cur; cbn [length]; rewrite !Nat2Z.inj_succ; lia | lia | lia])
    ltac:(rewrite (w3a_den_off E 22 _ (-2) E22);
          [f_equal; rewrite Hleft; cbn [length]; rewrite !Nat2Z.inj_succ; lia | lia | lia])
    ltac:(apply (w3a_den_off0 E 10 _ E10); unfold PP_SIZE in *; lia)
    ltac:(apply (w3a_slot E _ 9 _ _ _ _ _ _ 0x108 (SAlu ALU_AND (SOff 37 0) (SLit 3)) _ HR0 Ub9);
          [w3a_in
          | rewrite (w3a_den_and E 37 _ 0 3 E37); [ | lia | lia | lia];
            unfold rs_np; cbn [Cursor.fuzz_u8 fst snd];
            rewrite Z.add_0_r; rewrite w3a_land3 by lia; reflexivity]).

Lemma w3a_head2 : forall cx (Q : world rsegs -> config -> Prop) b0 b1 rest2 regs2 mem2 md2,
w3a_c1 cx (b0 :: b1 :: rest2) -> w3a_m1_post cx regs2 mem2 md2 ->
(forall regs3 mem3 md3,
   w3a_mid cx (b0 :: b1 :: rest2) rest2 (rs_sh (b0 :: b1 :: rest2)) (rs_np (b0 :: b1 :: rest2)) regs3 mem3 md3 ->
   SRr rsegs (x_W cx) (cfg_at rsegs 0x80370 regs3 mem3 md3) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs 0x802dc regs2 mem2 md2) Q.
Proof.
intros cx Q b0 b1 rest2 regs2 mem2 md2 HC HM K.
set (rest := b0 :: b1 :: rest2) in *.
pose proof (w3a_bounds cx rest HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (c1_in cx rest HC) as (Hleft & _ & Hra & _ & Hamr & _ & _ & _).
pose proof (c1_s6 cx rest HC) as A22.
pose proof (c1_ppin cx rest HC) as Hppin. pose proof (c1_ppnew cx rest HC) as Hfresh.
pose proof (c1_s1 cx rest HC) as A9. pose proof (c1_s4 cx rest HC) as A20. pose proof (c1_s11 cx rest HC) as A27.
pose proof (w3a_src_range cx rest HC) as (Hsrc0 & Hsrc47 & Hsrcband).
assert (Hge2 : 2 <= e_left (x_e cx))
  by (rewrite Hleft; subst rest; cbn [length]; rewrite !Nat2Z.inj_succ; lia).
pose proof (w3a_in_apart_R cx rest (e_src (x_e cx)) HC ltac:(lia)) as Hap48.
pose proof (w3a_in_apart_R cx rest (e_src (x_e cx) + 1) HC ltac:(lia)) as Hap48'.
pose proof HM as (HJ2 & Hio2 & Hk2 & Ha02 & V140 & Hzero & Hkeep2).
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof RPgSteps.rl_wx as Hwx. pose proof RPgSteps.rl_segs_low as Hsegs.
destruct (Hra (e_src (x_e cx)) ltac:(lia)) as (s0 & Hs0 & Hok0).
destruct (Hra (e_src (x_e cx) + 1) ltac:(lia)) as (s1 & Hs1 & Hok1).
assert (Hs07 : 0 <= s0 <= 7).
{ destruct Hok0 as [->|(Hq1 & Hq2)]; [lia|].
  pose proof (Z.mod_pos_bound (e_src (x_e cx)) 8 ltac:(lia)). lia. }
assert (Hs17 : 0 <= s1 <= 7).
{ destruct Hok1 as [->|(Hq1 & Hq2)]; [lia|].
  pose proof (Z.mod_pos_bound (e_src (x_e cx) + 1) 8 ltac:(lia)). lia. }
pose proof (w3a_byte_at2 cx rest regs2 mem2 md2 0%nat HC HM ltac:(subst rest; cbn; lia)) as Hb0at.
pose proof (w3a_byte_at2 cx rest regs2 mem2 md2 1%nat HC HM ltac:(subst rest; cbn; lia)) as Hb1at.
subst rest. cbn [nth] in Hb0at, Hb1at. rewrite Z.add_0_r in Hb0at.
change (Z.of_nat 1) with 1 in Hb1at.
pose proof (w3a_cell_at2 cx (b0 :: b1 :: rest2) regs2 mem2 md2 (e_src (x_e cx)) HC HM
  ltac:(unfold kHighMemEnd; lia)) as Hc0at. rewrite Hs0 in Hc0at.
pose proof (w3a_cell_at2 cx (b0 :: b1 :: rest2) regs2 mem2 md2 (e_src (x_e cx) + 1) HC HM
  ltac:(unfold kHighMemEnd; lia)) as Hc1at. rewrite Hs1 in Hc1at.
pose proof (rm_shadow_band (e_src (x_e cx)) ltac:(unfold kHighMemEnd; lia)) as Hband0.
pose proof (rm_shadow_band (e_src (x_e cx) + 1) ltac:(unfold kHighMemEnd; lia)) as Hband1.
unfold kLowMemEnd, kHighMemBeg in Hband0, Hband1, Hsrcband.
pose proof (rm_byte_range b0) as Hb0r. pose proof (rm_byte_range b1) as Hb1r.
destruct (Z.eq_dec (e_src (x_e cx) mod 8) 7) as [Hm7 | Hm7].
- (* the two bytes lie in two granules: a cell of its own for each *)
  pose proof (w3a_div8_next (e_src (x_e cx)) ltac:(lia) Hm7) as Hdiv.
  set (E := Ereg regs2 (w3a_xs (e_src (x_e cx)) s0 (shadow_of_addr SHADOW_OFF (e_src (x_e cx) + 1)) s1
    (bv_unsigned b0) (bv_unsigned b1))).
  assert (E9 : ew E 9%nat = Z_to_bv 64 R)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)); exact A9).
  assert (E27 : ew E 27%nat = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), (Hk2 27 ltac:(cbn; tauto)); exact A27).
  assert (E22 : ew E 22%nat = Z_to_bv 64 (e_left (x_e cx)))
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 22 (Z_to_bv 5 22) eq_refl), (Hk2 22 ltac:(cbn; tauto)); exact A22).
  assert (E20 : ew E 20%nat = Z_to_bv 64 (e_src (x_e cx)))
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl), (Hk2 20 ltac:(cbn; tauto)); exact A20).
  assert (E10 : ew E 10%nat = Z_to_bv 64 pp)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact Ha02).
  assert (E32 : ew E 32%nat = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (e_src (x_e cx))))
    by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33%nat = Z_to_bv 64 s0) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E 34%nat = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (e_src (x_e cx) + 1)))
    by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
  assert (E35 : ew E 35%nat = Z_to_bv 64 s1) by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
  assert (E36 : ew E 36%nat = Z_to_bv 64 (bv_unsigned b0)) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
  assert (E37 : ew E 37%nat = Z_to_bv 64 (bv_unsigned b1)) by (subst E; exact (ew_Ereg_extra regs2 _ 5)).
  assert (Ub9 : bv_unsigned (ew E 9%nat) = R) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (Ub20 : bv_unsigned (ew E 20%nat) = e_src (x_e cx)) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (Ub32 : bv_unsigned (ew E 32%nat) = shadow_of_addr SHADOW_OFF (e_src (x_e cx)))
    by (rewrite E32; apply unsigned_lit_small; unfold shadow_of_addr in *; lia).
  assert (Ub34 : bv_unsigned (ew E 34%nat) = shadow_of_addr SHADOW_OFF (e_src (x_e cx) + 1))
    by (rewrite E34; apply unsigned_lit_small; unfold shadow_of_addr in *; lia).
  pose proof (w3a_seatH cx (b0 :: b1 :: rest2) regs2 mem2 md2 [] [w3a_rIn0; w3a_rIn1; w3a_rC0; w3a_rC1]
    [(22%nat, mkAF 2 (2 ^ 47) 0); (33%nat, mkAF 0 7 0); (35%nat, mkAF 0 7 0); (36%nat, mkAF 0 255 0);
     (37%nat, mkAF 0 255 0)]
    [(w3a_e0, SOff 32 0); (w3a_e1, SOff 34 0)]
    (w3a_xs (e_src (x_e cx)) s0 (shadow_of_addr SHADOW_OFF (e_src (x_e cx) + 1)) s1
       (bv_unsigned b0) (bv_unsigned b1)) HC HM) as HS.
  specialize (HS ltac:(apply Forall_nil)).
  specialize (HS ltac:(vm_compute; reflexivity)).
  specialize (HS ltac:(constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]];
    unfold w3a_rIn0, w3a_rIn1, w3a_rC0, w3a_rC1;
    [ apply (rm_ro_region rsegs E (w_H (x_W cx)) mem2 20 (e_src (x_e cx))); [exact Ub20 | lia | lia |];
      constructor; [|constructor];
      apply (chunk_ok_val rsegs E _ (e_src (x_e cx)) 0 1 (SOff 36 0) (bv_unsigned b0));
      [apply (w3a_den_off0 E 36 (bv_unsigned b0) E36); lia
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |];
      change (N.to_nat 1) with 1%nat; rewrite Z.add_0_r;
      exact (proj1 (rm_aview_val1 rsegs (w_H (x_W cx)) mem2 _ _ Hb0at))
    | apply (rm_ro_region rsegs E (w_H (x_W cx)) mem2 20 (e_src (x_e cx))); [exact Ub20 | lia | lia |];
      constructor; [|constructor];
      apply (chunk_ok_val rsegs E _ (e_src (x_e cx)) 1 1 (SOff 37 0) (bv_unsigned b1));
      [apply (w3a_den_off0 E 37 (bv_unsigned b1) E37); lia
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |];
      change (N.to_nat 1) with 1%nat;
      exact (proj1 (rm_aview_val1 rsegs (w_H (x_W cx)) mem2 _ _ Hb1at))
    | exact (rm_cell_region rsegs E (w_H (x_W cx)) mem2 32 (shadow_of_addr SHADOW_OFF (e_src (x_e cx))) s0
        (SOff 33 0) Ub32 Hc0at (w3a_den_off0 E 33 s0 E33 ltac:(lia)) ltac:(unfold shadow_of_addr in *; lia)
        ltac:(unfold shadow_of_addr in *; lia))
    | exact (rm_cell_region rsegs E (w_H (x_W cx)) mem2 34 (shadow_of_addr SHADOW_OFF (e_src (x_e cx) + 1)) s1
        (SOff 35 0) Ub34 Hc1at (w3a_den_off0 E 35 s1 E35 ltac:(lia)) ltac:(unfold shadow_of_addr in *; lia)
        ltac:(unfold shadow_of_addr in *; lia)) ])).
  specialize (HS ltac:(apply pairwise_disjoint_of_extents; cbn [app map];
    unfold extent_of_region, w3a_rR108, w3a_rP, w3a_rIn0, w3a_rIn1, w3a_rC0, w3a_rC1;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    w3a_foldE E; rewrite Ub9, Ub20, Ub32, Ub34; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj;
    cbn [fst snd]; unfold shadow_of_addr in *; repeat split; lia)).
  specialize (HS ltac:(cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2]; w3a_foldE E;
    rewrite E22, E33, E35, E36, E37, !unsigned_lit_small by lia;
    change (2 ^ 0) with 1; rewrite !Z.mod_1_r; repeat split; lia)).
  specialize (HS ltac:(cbn [alias_ok]; split; [|split; [|exact I]]; unfold w3a_e0, w3a_e1;
    [ apply (w3a_alias_cell E 32 (e_src (x_e cx)) 0 (shadow_of_addr SHADOW_OFF (e_src (x_e cx)))
        E20 E27 E32); [lia | lia | lia | unfold shadow_of_addr; rewrite Z.add_0_r; reflexivity]
    | apply (w3a_alias_cell E 34 (e_src (x_e cx)) 1 (shadow_of_addr SHADOW_OFF (e_src (x_e cx) + 1))
        E20 E27 E34); [lia | lia | lia | unfold shadow_of_addr; reflexivity] ])).
  fold E in HS.
  assert (SHOK : sh_ok rsegs W3Bx [] E (mrestrict (w_H (x_W cx)) mem2)) by apply Forall_nil.
  unfold cfg_at. change (w64 0x802dc) with (Z_to_bv 64 0x802dc).
  aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
  { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
  srr_branch_tok w3a_tbl_ok HS SHOK W3span.
  + (* the first shadow byte is 0 *)
    aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
    { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
    srr_branch_tok w3a_tbl_ok HS SHOK W3span.
    * (* the second is 0 too *)
      aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
      { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
      pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms1 HS eq_refl) as Ems.
      cbn [ss_pc] in Ems. rewrite Ems.
      w3a_lf2 K HC HM HS HR0 E Ub9 E22 E20 E36 E37 E10 Hleft.
      intros a Ha H108. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms0) a).
      { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms0) (ms_mem ms1)
          (fun x => R + 0x108 <= x < R + 0x110) HFr1); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
      transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
      { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
          (fun x => R + 0x108 <= x < R + 0x110) HFr0); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
      { apply (w3a_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
          (fun x => R + 0x108 <= x < R + 0x110) HFr); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
    * (* the second is not 0: its slow block 0x826c4 *)
      aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
      { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
      srr_branch_tok w3a_tbl_ok HS SHOK W3span.
      -- exfalso. exact (w3a_kill E 20 35 (e_src (x_e cx)) s1 1 E20 E35 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(lia) Hok1 Hc0 Hc1).
      -- aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
         { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
         pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms2 HS eq_refl) as Ems.
         cbn [ss_pc] in Ems. rewrite Ems.
         w3a_lf2 K HC HM HS HR0 E Ub9 E22 E20 E36 E37 E10 Hleft.
         intros a Ha H108. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms1) a).
         { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms1) (ms_mem ms2)
             (fun x => R + 0x108 <= x < R + 0x110) HFr2); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
         transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms0) a).
         { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms0) (ms_mem ms1)
             (fun x => R + 0x108 <= x < R + 0x110) HFr1); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
         transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
         { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
             (fun x => R + 0x108 <= x < R + 0x110) HFr0); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
         { apply (w3a_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
             (fun x => R + 0x108 <= x < R + 0x110) HFr); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
  + (* the first shadow byte is not 0: its slow block 0x82660 *)
    aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
    { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
    srr_branch_tok w3a_tbl_ok HS SHOK W3span.
    * exfalso. exact (w3a_kill E 20 33 (e_src (x_e cx)) s0 0 E20 E33 ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hok0) Hc Hc0).
    * aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
      { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
      srr_branch_tok w3a_tbl_ok HS SHOK W3span.
      -- aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
         { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
         pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms2 HS eq_refl) as Ems.
         cbn [ss_pc] in Ems. rewrite Ems.
         w3a_lf2 K HC HM HS HR0 E Ub9 E22 E20 E36 E37 E10 Hleft.
         intros a Ha H108. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms1) a).
         { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms1) (ms_mem ms2)
             (fun x => R + 0x108 <= x < R + 0x110) HFr2); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
         transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms0) a).
         { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms0) (ms_mem ms1)
             (fun x => R + 0x108 <= x < R + 0x110) HFr1); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
         transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
         { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
             (fun x => R + 0x108 <= x < R + 0x110) HFr0); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
         { apply (w3a_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
             (fun x => R + 0x108 <= x < R + 0x110) HFr); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
      -- aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
         { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
         srr_branch_tok w3a_tbl_ok HS SHOK W3span.
         ++ exfalso. exact (w3a_kill E 20 35 (e_src (x_e cx)) s1 1 E20 E35 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) Hok1 Hc1 Hc2).
         ++ aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
            { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
            pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms3 HS eq_refl) as Ems.
            cbn [ss_pc] in Ems. rewrite Ems.
            w3a_lf2 K HC HM HS HR0 E Ub9 E22 E20 E36 E37 E10 Hleft.
            intros a Ha H108. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms2) a).
            { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms2) (ms_mem ms3)
                (fun x => R + 0x108 <= x < R + 0x110) HFr3); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
            transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms1) a).
            { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms1) (ms_mem ms2)
                (fun x => R + 0x108 <= x < R + 0x110) HFr2); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
            transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms0) a).
            { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms0) (ms_mem ms1)
                (fun x => R + 0x108 <= x < R + 0x110) HFr1); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
            transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
            { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
                (fun x => R + 0x108 <= x < R + 0x110) HFr0); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
            { apply (w3a_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
                (fun x => R + 0x108 <= x < R + 0x110) HFr); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
- (* the two bytes lie in one granule: one cell, two aliases *)
  pose proof (w3a_div8_same (e_src (x_e cx)) ltac:(lia) Hm7) as Hdiv.
  assert (Hcell : shadow_of_addr SHADOW_OFF (e_src (x_e cx) + 1) = shadow_of_addr SHADOW_OFF (e_src (x_e cx)))
    by (unfold shadow_of_addr; rewrite Hdiv; reflexivity).
  assert (Hs10 : s1 = s0) by (rewrite Hcell in Hs1; rewrite Hs1 in Hs0; injection Hs0 as ->; reflexivity).
  subst s1.
  set (E := Ereg regs2 (w3a_xs (e_src (x_e cx)) s0 0 0 (bv_unsigned b0) (bv_unsigned b1))).
  assert (E9 : ew E 9%nat = Z_to_bv 64 R)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)); exact A9).
  assert (E27 : ew E 27%nat = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), (Hk2 27 ltac:(cbn; tauto)); exact A27).
  assert (E22 : ew E 22%nat = Z_to_bv 64 (e_left (x_e cx)))
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 22 (Z_to_bv 5 22) eq_refl), (Hk2 22 ltac:(cbn; tauto)); exact A22).
  assert (E20 : ew E 20%nat = Z_to_bv 64 (e_src (x_e cx)))
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl), (Hk2 20 ltac:(cbn; tauto)); exact A20).
  assert (E10 : ew E 10%nat = Z_to_bv 64 pp)
    by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact Ha02).
  assert (E32 : ew E 32%nat = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (e_src (x_e cx))))
    by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33%nat = Z_to_bv 64 s0) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
  assert (E36 : ew E 36%nat = Z_to_bv 64 (bv_unsigned b0)) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
  assert (E37 : ew E 37%nat = Z_to_bv 64 (bv_unsigned b1)) by (subst E; exact (ew_Ereg_extra regs2 _ 5)).
  assert (Ub9 : bv_unsigned (ew E 9%nat) = R) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (Ub20 : bv_unsigned (ew E 20%nat) = e_src (x_e cx)) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (Ub32 : bv_unsigned (ew E 32%nat) = shadow_of_addr SHADOW_OFF (e_src (x_e cx)))
    by (rewrite E32; apply unsigned_lit_small; unfold shadow_of_addr in *; lia).
  pose proof (w3a_seatH cx (b0 :: b1 :: rest2) regs2 mem2 md2 [] [w3a_rIn0; w3a_rIn1; w3a_rC0]
    [(22%nat, mkAF 2 (2 ^ 47) 0); (33%nat, mkAF 0 7 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0)]
    [(w3a_e0, SOff 32 0); (w3a_e1, SOff 32 0)]
    (w3a_xs (e_src (x_e cx)) s0 0 0 (bv_unsigned b0) (bv_unsigned b1)) HC HM) as HS.
  specialize (HS ltac:(apply Forall_nil)).
  specialize (HS ltac:(vm_compute; reflexivity)).
  specialize (HS ltac:(constructor; [|constructor; [|constructor; [|constructor]]];
    unfold w3a_rIn0, w3a_rIn1, w3a_rC0;
    [ apply (rm_ro_region rsegs E (w_H (x_W cx)) mem2 20 (e_src (x_e cx))); [exact Ub20 | lia | lia |];
      constructor; [|constructor];
      apply (chunk_ok_val rsegs E _ (e_src (x_e cx)) 0 1 (SOff 36 0) (bv_unsigned b0));
      [apply (w3a_den_off0 E 36 (bv_unsigned b0) E36); lia
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |];
      change (N.to_nat 1) with 1%nat; rewrite Z.add_0_r;
      exact (proj1 (rm_aview_val1 rsegs (w_H (x_W cx)) mem2 _ _ Hb0at))
    | apply (rm_ro_region rsegs E (w_H (x_W cx)) mem2 20 (e_src (x_e cx))); [exact Ub20 | lia | lia |];
      constructor; [|constructor];
      apply (chunk_ok_val rsegs E _ (e_src (x_e cx)) 1 1 (SOff 37 0) (bv_unsigned b1));
      [apply (w3a_den_off0 E 37 (bv_unsigned b1) E37); lia
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |];
      change (N.to_nat 1) with 1%nat;
      exact (proj1 (rm_aview_val1 rsegs (w_H (x_W cx)) mem2 _ _ Hb1at))
    | exact (rm_cell_region rsegs E (w_H (x_W cx)) mem2 32 (shadow_of_addr SHADOW_OFF (e_src (x_e cx))) s0
        (SOff 33 0) Ub32 Hc0at (w3a_den_off0 E 33 s0 E33 ltac:(lia)) ltac:(unfold shadow_of_addr in *; lia)
        ltac:(unfold shadow_of_addr in *; lia)) ])).
  specialize (HS ltac:(apply pairwise_disjoint_of_extents; cbn [app map];
    unfold extent_of_region, w3a_rR108, w3a_rP, w3a_rIn0, w3a_rIn1, w3a_rC0;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    w3a_foldE E; rewrite Ub9, Ub20, Ub32; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj;
    cbn [fst snd]; unfold shadow_of_addr in *; repeat split; lia)).
  specialize (HS ltac:(cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2]; w3a_foldE E;
    rewrite E22, E33, E36, E37, !unsigned_lit_small by lia;
    change (2 ^ 0) with 1; rewrite !Z.mod_1_r; repeat split; lia)).
  specialize (HS ltac:(cbn [alias_ok]; split; [|split; [|exact I]]; unfold w3a_e0, w3a_e1;
    [ apply (w3a_alias_cell E 32 (e_src (x_e cx)) 0 (shadow_of_addr SHADOW_OFF (e_src (x_e cx)))
        E20 E27 E32); [lia | lia | lia | unfold shadow_of_addr; rewrite Z.add_0_r; reflexivity]
    | apply (w3a_alias_cell E 32 (e_src (x_e cx)) 1 (shadow_of_addr SHADOW_OFF (e_src (x_e cx)))
        E20 E27 E32); [lia | lia | lia | unfold shadow_of_addr; rewrite Hdiv; reflexivity] ])).
  fold E in HS.
  assert (SHOK : sh_ok rsegs W3Bx [] E (mrestrict (w_H (x_W cx)) mem2)) by apply Forall_nil.
  unfold cfg_at. change (w64 0x802dc) with (Z_to_bv 64 0x802dc).
  aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
  { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
  srr_branch_tok w3a_tbl_ok HS SHOK W3span.
  + (* the shadow byte is 0: both checks pass at once *)
    aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
    { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
    pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms0 HS eq_refl) as Ems.
    cbn [ss_pc] in Ems. rewrite Ems.
    w3a_lf2 K HC HM HS HR0 E Ub9 E22 E20 E36 E37 E10 Hleft.
    intros a Ha H108. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
    { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
        (fun x => R + 0x108 <= x < R + 0x110) HFr0); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
    { apply (w3a_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
        (fun x => R + 0x108 <= x < R + 0x110) HFr); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
  + (* the shadow byte is not 0: both slow blocks *)
    aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
    { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
    srr_branch_tok w3a_tbl_ok HS SHOK W3span.
    * exfalso. exact (w3a_kill E 20 33 (e_src (x_e cx)) s0 0 E20 E33 ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hok0) Hc Hc0).
    * aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
      { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
      srr_branch_tok w3a_tbl_ok HS SHOK W3span.
      -- exfalso. exact (w3a_kill E 20 33 (e_src (x_e cx)) s0 1 E20 E33 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(lia) Hok1 Hc Hc1).
      -- aj_run_to_tok w3a_tbl_ok HS HJ2 SHOK W3span 0x80370.
         { w3a_awr pp R Ub9 Ub9 Hppin Hfresh. }
         pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E _ ms2 HS eq_refl) as Ems.
         cbn [ss_pc] in Ems. rewrite Ems.
         w3a_lf2 K HC HM HS HR0 E Ub9 E22 E20 E36 E37 E10 Hleft.
         intros a Ha H108. transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms1) a).
         { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms1) (ms_mem ms2)
             (fun x => R + 0x108 <= x < R + 0x110) HFr2); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
         transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms0) a).
         { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms0) (ms_mem ms1)
             (fun x => R + 0x108 <= x < R + 0x110) HFr1); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
         transitivity (aview rsegs (w_H (x_W cx)) (ms_mem ms) a).
         { apply (w3a_keep_run E _ (w_H (x_W cx)) (ms_mem ms) (ms_mem ms0)
             (fun x => R + 0x108 <= x < R + 0x110) HFr0); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
         { apply (w3a_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
             (fun x => R + 0x108 <= x < R + 0x110) HFr); [w3a_kwr E Ub9 Ub9 | exact Ha | lia]. }
Qed.

(* =============================== the piece lemma =============================== *)
Theorem rs_piece_W3a : rs_piece_W3a_stmt rsegs B MT.
Proof.
unfold rs_piece_W3a_stmt. intros cx POST rest HST HB7 HBO.
pose proof (w3a_c1_of cx rest HST) as HC.
apply (w3a_m1 cx rest POST HC). intros regs2 mem2 md2 HM.
destruct rest as [|b0 rest1].
- apply (w3a_head0 cx POST regs2 mem2 md2 HC HM). intros regs3 mem3 md3 HMID.
  exact (w3a_tail cx POST [] [] 0 0 regs3 mem3 md3 HC HMID
    ltac:(exists 0%nat; split; [cbn; lia | reflexivity]) eq_refl eq_refl eq_refl HB7 HBO).
- destruct rest1 as [|b1 rest2].
  + apply (w3a_head1 cx POST b0 regs2 mem2 md2 HC HM). intros regs3 mem3 md3 HMID.
    exact (w3a_tail cx POST [b0] [] (rs_sh [b0]) 0 regs3 mem3 md3 HC HMID
      ltac:(exists 1%nat; split; [cbn; lia | reflexivity]) eq_refl eq_refl eq_refl HB7 HBO).
  + apply (w3a_head2 cx POST b0 b1 rest2 regs2 mem2 md2 HC HM). intros regs3 mem3 md3 HMID.
    exact (w3a_tail cx POST (b0 :: b1 :: rest2) rest2 (rs_sh (b0 :: b1 :: rest2)) (rs_np (b0 :: b1 :: rest2))
      regs3 mem3 md3 HC HMID ltac:(exists 2%nat; split; [cbn; lia | reflexivity])
      eq_refl eq_refl eq_refl HB7 HBO).
Qed.

End s.
End b.
