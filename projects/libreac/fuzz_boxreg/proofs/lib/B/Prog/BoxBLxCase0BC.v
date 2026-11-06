(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 700 of its 746 lines of code are new or changed and 885 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase3SegA.v, with its module names changed; 757 of its 820 lines of code are new or changed and 683 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput, piece BC -> SC: from the cut
   C0_BC (0x80630, bcmp of the new row's MAC with ZERO returned 0) through the call strncmp at 0x80698 to the cut C0_SC
   (0x8069c, strncmp returned 0); BoxBLxCase0Defs.v holds the cuts.
   The code (offsets from 0x7ffac in the listing):
   - 0x80630 bnez a0 (a0 = 0 at the cut) and the ASan check of the row's pinned field (r + 56 n + 20): the engine
     decides both (a0 is the literal 0; the row's 56 bytes are a shadow entry over s7, the row's atom);
   - 0x80658 bne a0, a1: the pinned field (lw) against (s10 <s 0) ^ 1; the abort at 0x80fa4 is refuted with
     declare_placed (pinned = 1 when base >= 0, else 0);
   - 0x80664 bltz (slot 0x50 = base << 56): for base >= 0 the ASan check of the base field (engine) and
     0x8067c bne a0, s10, whose abort at 0x80fa4 is refuted with declare_placed (the base field is base);
   - 0x80684 beqz s8 (op & 8): a1 = the name (slot 0x60), or "" (A_OBJ 5); a0 = r + 56 n + 24, a2 = 31;
   - 0x80698 strncmp (lib/B/Rt/StrncmpDefB.v abstrncmp_realizes, lx_hyps' lh_strncmp): the row's name field holds
     firstn 31 of the given string and its NUL (Pau's decl_row / name_field and new_row_bytes), so the answer is 0.
   No instruction of the piece stores; the interceptor writes only inside [sp1 - 2 * ESTACK, sp1). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo BoxTailVis YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ YC1g YC1h YC85 BoxBRangeTaken.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs BoxBLxCase0Kit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd read_name_c printf_facts_c
  reac_boxreg_declare_c reac_boxreg_declare_inv LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the new row's bytes (Pau's declare model) ---- *)
Lemma c0bc_nth_bsub : forall (l : list byte) o w j d, 0 <= o -> 0 <= j < w ->
  nth (Z.to_nat j) (Boxreg.bsub l o w) d = nth (Z.to_nat (o + j)) l d.
Proof.
  intros l o w j d Ho Hj. unfold Boxreg.bsub.
  rewrite (rt_nth_firstn byte d (skipn (Z.to_nat o) l) (Z.to_nat w) (Z.to_nat j)) by lia.
  rewrite rt_nth_skipn. f_equal. lia.
Qed.

Lemma c0bc_row_rd4 : forall bs b k p s o v, length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 -> 0 <= o -> o + 4 <= 56 ->
  Boxreg.bsub (reac_boxreg_declare_c.decl_row b k p s) o 4 = Mem.le4 (Z_to_bv 64 v) -> - 2 ^ 31 <= v < 2 ^ 31 ->
  Boxreg.rd4 (c0_placed bs b k p s) (56 * Boxreg.bx_n bs + o) = v.
Proof.
  intros bs b k p s o v HL Hn Ho Ho4 Hrow Hv.
  apply BoxregUpd.rd4_le4; [exact Hv|]. unfold c0_placed.
  change (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s))
    with (reac_boxreg_declare_c.decl_bytes bs b k p s).
  rewrite LLVMFuzzerTestOneInput_case0.c0_row_bsub by lia. exact Hrow.
Qed.

Lemma c0bc_row_byte : forall bs b k p s o, length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 -> 0 <= o < 56 ->
  nth (Z.to_nat (56 * Boxreg.bx_n bs + o)) (c0_placed bs b k p s) (Z_to_bv 8 0) =
  nth (Z.to_nat o) (reac_boxreg_declare_c.decl_row b k p s) (Z_to_bv 8 0).
Proof.
  intros bs b k p s o HL Hn Ho.
  pose proof (LLVMFuzzerTestOneInput_case0.c0_row_bsub bs b k p s o 1 HL Hn ltac:(lia) ltac:(lia) ltac:(lia)) as E.
  pose proof (f_equal (fun l => nth 0 l (Z_to_bv 8 0)) E) as E2. cbv beta in E2.
  rewrite <- (Z2Nat.inj_0) in E2.
  rewrite !(c0bc_nth_bsub _ _ 1 0) in E2 by lia. rewrite !Z.add_0_r in E2. exact E2.
Qed.

(* The name field holds firstn 31 s and its NUL. *)
Lemma c0bc_name_field : forall (s : list Z) j, Forall (fun c => 0 < c < 256) s ->
  (j < length (firstn 31 s ++ [0%Z]))%nat ->
  bv_unsigned (nth j (reac_boxreg_declare_c.name_field s) (Z_to_bv 8 0)) = nth j (firstn 31 s ++ [0]) 0.
Proof.
  intros s j Hs Hj. rewrite length_app in Hj. cbn [length] in Hj.
  assert (Hf : Forall (fun c => 0 < c < 256) (firstn 31 s)).
  { rewrite <- (firstn_skipn 31 s) in Hs. apply Forall_app in Hs. exact (proj1 Hs). }
  unfold reac_boxreg_declare_c.name_field, printf_facts_c.pf_bytes.
  destruct (Nat.lt_ge_cases j (length (firstn 31 s))) as [Hlt | Hge].
  - rewrite app_nth1 by (rewrite length_map; exact Hlt). rewrite app_nth1 by exact Hlt.
    change (Z_to_bv 8 0) with (Z_to_bv 8 0 : byte). rewrite map_nth.
    rewrite Forall_forall in Hf. pose proof (Hf _ (nth_In _ 0 Hlt)) as Hc.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
  - assert (Ej : j = length (firstn 31 s)) by lia. subst j.
    rewrite app_nth2 by (rewrite length_map; lia). rewrite app_nth2 by lia.
    rewrite length_map, Nat.sub_diag. cbn [nth].
    destruct (32 - Nat.min (length s) 31)%nat as [|m] eqn:Em; [lia|]. cbn [repeat nth]. reflexivity.
Qed.

Lemma c0bc_row_name : forall bs b k p s j, length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 ->
  Forall (fun c => 0 < c < 256) s -> (j < length (firstn 31 s ++ [0%Z]))%nat ->
  bv_unsigned (nth (Z.to_nat (56 * Boxreg.bx_n bs + 24 + Z.of_nat j)) (c0_placed bs b k p s) (Z_to_bv 8 0)) =
  nth j (firstn 31 s ++ [0]) 0.
Proof.
  intros bs b k p s j HL Hn Hs Hj.
  assert (Hj32 : (j < 32)%nat) by (rewrite length_app, length_firstn in Hj; cbn [length] in Hj; lia).
  replace (56 * Boxreg.bx_n bs + 24 + Z.of_nat j) with (56 * Boxreg.bx_n bs + (24 + Z.of_nat j)) by lia.
  rewrite c0bc_row_byte by lia.
  pose proof (f_equal (fun l => nth j l (Z_to_bv 8 0)) (reac_boxreg_declare_inv.decl_row_name b k p s)) as E.
  cbv beta in E. replace j with (Z.to_nat (Z.of_nat j)) in E at 1 by lia.
  rewrite c0bc_nth_bsub in E by lia. rewrite E. exact (c0bc_name_field s j Hs Hj).
Qed.

(* strncmp (field, s, 31) = 0: the field holds firstn 31 s and its NUL. *)
Lemma c0bc_strn_eq : forall s, abfm_strn_eq 31 (firstn 31 s) s.
Proof.
  intros s. unfold abfm_strn_eq. rewrite !firstn_app, firstn_firstn, length_firstn.
  replace (Init.Nat.min 31 31) with 31%nat by reflexivity. f_equal. f_equal. lia.
Qed.

Lemma c0bc_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma c0bc_from_primary : forall n, 0 <= n <= 48 -> from_primary n = true.
Proof.
  intros n Hn.
  assert (H : forallb (fun z => from_primary z) (map Z.of_nat (seq 0 49)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat n). split; [lia | apply in_seq; lia].
Qed.

Lemma c0bc_mod8 : forall a q, a mod q = 0 -> q mod 8 = 0 -> 0 < q -> a mod 8 = 0.
Proof.
  intros a q Ha Hq Hq0. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hq; [|lia]. apply Z.mod_divide; [lia|].
  destruct Ha as [x Hx]. destruct Hq as [y Hy]. exists (x * y). lia.
Qed.

(* ---- the branches of the segment, on the values the cut gives ---- *)
Lemma c0bc_U_atom : forall E n z, ew E n = w64 z -> U E (SOff n 0) = z mod 2 ^ 64.
Proof.
  intros E n z H. rewrite U_SOff, H, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned.
  unfold zcanon, M64, bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_mod. lia.
Qed.

Lemma c0bc_in_byte : forall (P : Z -> bool) v, -128 <= v < 128 ->
  forallb P (map (fun n => Z.of_nat n - 128) (seq 0 256)) = true -> P v = true.
Proof.
  intros P v Hv H. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat (v + 128)).
  split; [lia | apply in_seq; lia].
Qed.

(* 0x80658 bne a0, a1: the pinned field (p = base >= 0) against (s10 <s 0) ^ 1. *)
Lemma c0bc_pin : forall b0, -128 <= b0 < 128 ->
  negb (zcanon (bv_swrap 32 (((if b0 <? 0 then 0 else 1) mod 2 ^ 64) mod 2 ^ Z.of_N 32)) =?
        zcanon (zalu_raw 63 64 ALU_XOR (zcanon (zalu_raw 63 64 ALU_SLT (b0 mod 2 ^ 64) (zcanon 0))) (zcanon 1))) = false.
Proof.
  intros b0 Hb.
  pose proof (c0bc_in_byte (fun z => negb (negb (zcanon (bv_swrap 32 (((if z <? 0 then 0 else 1) mod 2 ^ 64) mod 2 ^ Z.of_N 32)) =?
        zcanon (zalu_raw 63 64 ALU_XOR (zcanon (zalu_raw 63 64 ALU_SLT (z mod 2 ^ 64) (zcanon 0))) (zcanon 1))))) b0 Hb
    ltac:(vm_compute; reflexivity)) as H.
  cbv beta in H. apply negb_true_iff in H. exact H.
Qed.

(* 0x8067c bne a0, s10 (base >= 0): the row's base field against the given base. *)
Lemma c0bc_base_eq : forall z, 0 <= z < 128 -> zcanon (bv_swrap 32 (z mod 2 ^ 64 mod 2 ^ Z.of_N 32)) = z mod 2 ^ 64.
Proof.
  intros z Hz. rewrite (Z.mod_small z (2 ^ 64)) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
  rewrite (Z.mod_small z (2 ^ 32)) by lia. rewrite LLVMFuzzerTestOneInput_case0.c0_swrap_small by lia.
  apply zcanon_id. unfold M64. lia.
Qed.

(* ---- the segment's symbolic state at BC (0x80630) ---- *)
(* The shadow span (BoxBLxCase0Chk.v), the shadow base as the atom LA_SB (s2 overridden to it). *)
Definition C0BC_SB : Z := 0x7fff8000.
Definition C0BC_Bspan : Z * Z := (C0BC_SB, C0BC_SB + 2 ^ 44 - 1).
Definition C0BC_Bx : sv := SOff LA_SB 0.
(* s1 = the atom of sp, s2 = SHADOW_OFF's atom, a0 = 0 (bcmp's answer). *)
Definition C0BC_OV : list (bv 5 * sv) := LX_OV ++ [((10%bv : bv 5), SLit 0)].
(* The row r + 56 n is s7 (atom 23): its 56 bytes are addressable (the two ASan checks of the row). *)
Definition C0BC_SH : list shent := [mkSHE 23 0 56].
Definition C0BC_G : facts :=
  mkFacts [(LA_SB, mkAF 0x7fff8000 0x7fff8000 0); (23%nat, mkAF 4096 0x7fffff800000 0)] [] [].
(* The spill slots the segment reads: the fabric (0x30), the base shifted to the top byte (0x50), the name (0x60). *)
Definition c0bc_spill : YP09.region := YP09.mkRegion (Some LA_SP) 0x30 0x68 0 0
  [YP09.mkChunk 0x30 (CVal 8 (SOff 27 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 50 0));
   YP09.mkChunk 0x60 (CVal 8 (SOff 51 0))].
(* The row's base (+8) and pinned (+20) fields. *)
Definition c0bc_row : YP09.region := YP09.mkRegion (Some 23%nat) 8 24 0 0
  [YP09.mkChunk 8 (CVal 4 (SOff 48 0)); YP09.mkChunk 20 (CVal 4 (SOff 49 0))].
(* The segment's atoms 48 .. 51: the row's base field, its pinned field, the slot 0x50, the name. *)
Definition c0bc_ex (b p bsl nm : Z) : list word := [w64 b; w64 p; w64 bsl; w64 nm].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS : AR_laws SEGS B := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- strncmp's string premises, from AR and the bytes ---- *)
Lemma c0bc_val_mem1 : forall (W : world SEGS) mem a v, aview SEGS (w_H W) mem a = Some v ->
  val_mem SEGS (mrestrict (w_H W) mem) a 1 v /\ 0 <= v < 256.
Proof.
  intros W mem a v H. unfold aview in H.
  destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [c|] eqn:Hm; [|discriminate H].
  cbn [option_map] in H. injection H as <-.
  pose proof (bv_unsigned_in_range 8 c) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|lia].
  intros kk Hk. assert (kk = 0%nat) by lia. subst kk. replace (a + Z.of_nat 0) with a by lia. rewrite Hm. f_equal.
  rewrite le_byte_small by (cbn; lia). replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* A block of at most 48 bytes is a primary chunk: high memory, far below the ceiling. *)
Lemma c0bc_small_blk : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md ->
  In (q, n) (ablocks B ly S) -> 0 <= n <= 48 -> kHighMemBeg <= q /\ q + n + 4096 <= alloc_ceiling.
Proof.
  intros ly S W mem md q n HAR Hin Hn. pose proof HAR as (M & _).
  apply (proj1 (In_ablocks B ly S q n)) in Hin as (kc & Hk & Hst & Hu & Hr).
  pose proof (chunk_facts B ly S _ kc M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (req_size_pos (ck_req kc) ltac:(lia)) as [Q1 Q2].
  destruct (ck_beg kc) as [|off|r0 o|c0 q0]; try solve [destruct GG].
  - cbv zeta in GG. destruct GG as (Gc & Gfp & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
    pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
    unfold ASAN_CEIL in *. lia.
  - destruct GG as (_ & Gfp & _). rewrite Hr, (c0bc_from_primary n Hn) in Gfp. discriminate.
Qed.

(* A C string of at most 47 bytes in a heap block of L + 1 bytes (the name block). *)
Lemma c0bc_cstr_ok_blk : forall ly S (W : world SEGS) mem md q L (s : list Z),
  AR SEGS B ly S W mem md -> In (q, L + 1) (ablocks B ly S) -> 0 <= L <= 47 ->
  Z.of_nat (length s) <= L -> Forall (fun c => 0 < c < 256) s ->
  (forall j, (j < length (s ++ [0%Z]))%nat -> aview SEGS (w_H W) mem (q + Z.of_nat j) = Some (nth j (s ++ [0]) 0)) ->
  (forall j, 0 <= j <= L -> aview SEGS (w_H W) mem (q + j) <> None) ->
  abfm_cstr_ok SEGS W mem q s.
Proof.
  intros ly S W mem md q L s HAR Hq HL HsL Hpos Hbytes Hall.
  destruct (al_blocks _ _ LAWS ly S W mem md q (L + 1) HAR Hq) as (Hq16 & Hq4096 & Hqceil & Hqia & _).
  rewrite c0bc_req in Hqceil, Hqia by lia.
  destruct (c0bc_small_blk ly S W mem md q (L + 1) HAR Hq ltac:(lia)) as [Hhm Hsm].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod q 16 ltac:(lia)) as Dq. rewrite Hq16, Z.add_0_r in Dq.
  pose proof (Z.div_mod (Z.of_nat (length s)) 8 ltac:(lia)) as Ds.
  pose proof (Z.mod_pos_bound (Z.of_nat (length s)) 8 ltac:(lia)) as Dsb.
  assert (Hwe : q + Z.of_nat (length s) - (q + Z.of_nat (length s)) mod 8 + 8 = q + 8 * (Z.of_nat (length s) / 8) + 8).
  { rewrite Dq. replace (16 * (q / 16) + Z.of_nat (length s)) with
      (Z.of_nat (length s) + (2 * (q / 16)) * 8) by lia. rewrite Z.mod_add by lia. lia. }
  pose proof (Z.div_mod (L + 1 + 8 - 1) 8 ltac:(lia)) as Dl.
  pose proof (Z.mod_pos_bound (L + 1 + 8 - 1) 8 ltac:(lia)) as Dlb.
  split; [split|].
  - intros j Hj. exact (c0bc_val_mem1 W mem (q + Z.of_nat j) _ (Hbytes j Hj)).
  - eapply Forall_impl; [|exact Hpos]. intros c Hc. cbv beta in Hc. lia.
  - split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
    split; [right; unfold kHighMemEnd, ASAN_CEIL in *; pose proof ASAN_CEIL_range as [CR _]; unfold ASAN_CEIL in CR; lia|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md q (L + 1));
      [exact HAR | exact Hq | lia | rewrite c0bc_req by lia; lia]|].
    split; [apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md q (L + 1));
      [exact HAR | exact Hq | lia | rewrite c0bc_req by lia; lia | lia]|].
    intros a Ha. rewrite Hwe in Ha. destruct (Z_le_gt_dec a (q + L)) as [Hin | Hout].
    + replace a with (q + (a - q)) by lia. apply Hall. lia.
    + apply (absn_blk_tail_vis_ok SEGS B ly S W mem md q (L + 1) a HAR Hq). unfold round_up. lia.
Qed.

(* The new row's name field (inside the registry block) as strncmp's first string. *)
Lemma c0bc_cstr_ok_fld : forall ly S (W : world SEGS) mem md r rw (s : list Z),
  AR SEGS B ly S W mem md -> In (r, LX_REG) (ablocks B ly S) -> r <= rw -> rw + 56 <= r + 280 ->
  Forall (fun c => 0 < c < 256) s ->
  (forall j, (j < length (firstn 31 s ++ [0%Z]))%nat ->
     aview SEGS (w_H W) mem (rw + 24 + Z.of_nat j) = Some (nth j (firstn 31 s ++ [0]) 0)) ->
  (forall j, 0 <= j < LX_REG -> aview SEGS (w_H W) mem (r + j) <> None) ->
  abfm_cstr_ok SEGS W mem (rw + 24) (firstn 31 s).
Proof.
  intros ly S W mem md r rw s HAR Hr Hrw1 Hrw2 Hpos Hf Hall.
  destruct (al_blocks _ _ LAWS ly S W mem md r LX_REG HAR Hr) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  assert (Hl : Z.of_nat (length (firstn 31 s)) <= 31) by (rewrite length_firstn; lia).
  pose proof (Z.mod_pos_bound (rw + 24 + Z.of_nat (length (firstn 31 s))) 8 ltac:(lia)) as Dm.
  split; [split|].
  - intros j Hj. destruct (c0bc_val_mem1 W mem _ _ (Hf j Hj)) as [Hv Hb]. split; [exact Hv | exact Hb].
  - rewrite <- (firstn_skipn 31 s) in Hpos. apply Forall_app in Hpos as [Hpos _].
    eapply Forall_impl; [|exact Hpos]. intros c Hc. cbv beta in Hc. lia.
  - split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
    split; [apply (amem_range_of_block SEGS B LAWS ly S W mem md r LX_REG);
      [exact HAR | exact Hr | lia | change (req_size LX_REG) with 288; lia]|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md r LX_REG);
      [exact HAR | exact Hr | lia | change (req_size LX_REG) with 288; lia]|].
    split; [apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md r LX_REG);
      [exact HAR | exact Hr | lia | change (req_size LX_REG) with 288; lia | lia]|].
    intros a Ha. replace a with (r + (a - r)) by lia. apply Hall. unfold LX_REG. lia.
Qed.

(* ---- the image's "" (A_OBJ 5), strncmp's second string when op & 8 <> 0 ---- *)
Lemma c0bc_gshadow : forall ly S (W : world SEGS) g sz m md, In (g, sz) LX_GLOBS -> AR SEGS B ly S W m md ->
  aview SEGS (w_H W) m (shadow_addr (VAL (A_OBJ g))) = Some sz.
Proof.
  intros ly S W g sz m md Hin HAR. destruct HAR as (M & _).
  pose proof (am_const _ _ _ _ M) as C. rewrite Forall_forall in C.
  assert (Hc : In (z1 (ANum (shadow_addr (VAL (A_OBJ g)))) sz) (as_const B ly)).
  { apply (blx_cells B (lh_glob B MT HY) ly). unfold lx_glob_cells. apply in_flat_map.
    exists (g, sz). split; [exact Hin|]. cbn [fst snd]. left. reflexivity. }
  assert (Hsz : 0 <= sz < 256)
    by (cbv [LX_GLOBS In] in Hin; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]); destruct Hin).
  specialize (C _ Hc). unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
  specialize (C 0%nat ltac:(lia)). rewrite Z.add_0_r in C. rewrite C. f_equal.
  unfold le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. exact Hsz.
Qed.

Lemma c0bc_empty_ok : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
  abfm_cstr_ok SEGS W m (VAL (A_OBJ 5)) [].
Proof.
  intros ly S W m md HAR HRO.
  pose proof (lh_glob B MT HY) as GL. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hg : In (5%nat, 1) LX_GLOBS) by (unfold LX_GLOBS; cbn [In]; tauto).
  pose proof (blx_al B GL _ Hg) as Hal. pose proof (blx_marg B GL _ Hg) as Hmg. cbn [fst snd] in Hal, Hmg.
  pose proof (lx_rom_viewN B W m HRO) as HRVN.
  pose proof (blx_rom_bytes B GL (5%nat, [0]) ltac:(unfold LX_GLOB_BYTES; cbn [In]; tauto)) as Hrb.
  cbn [fst snd] in Hrb.
  pose proof (proj2 (proj1 (blx_rom_strs B GL))) as Hstr.
  set (q := VAL (A_OBJ 5)) in *.
  assert (Hp8 : q mod 8 = 0) by (apply (c0bc_mod8 _ 32); [exact Hal | reflexivity | lia]).
  assert (Hb0 : aview SEGS (w_H W) m q = Some 0).
  { destruct (Hrb 0 ltac:(cbn; lia)) as (Hrom & Ho & He & Hv). rewrite Z.add_0_r in Hrom, Ho, He, Hv.
    rewrite (HRVN _ Hrom Ho He), Hv. reflexivity. }
  unfold IMG_HI in Hmg.
  destruct (c0bc_val_mem1 W m q 0 Hb0) as [Hvm Hr].
  split; [split|].
  - intros j Hj. cbn [app length] in Hj |- *. destruct j as [|j]; [|exfalso; lia].
    cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. split; [exact Hvm | lia].
  - apply Forall_nil.
  - cbn [length Z.of_nat].
    split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
    split; [unfold amem_range, kLowMemEnd; left; lia|].
    split.
    { apply range_addressable_partial; [exact (c0bc_gshadow ly S W 5 1 m md Hg HAR) | | lia].
      exact Hp8. }
    split.
    { destruct (blx_marg B GL (5%nat, 1) Hg) as [M1 M2]. cbn [fst snd] in *.
      eapply ro_hull; [exact (blx_isv B GL) | exact HAR | lia | exact M1 | exact M2]. }
    intros a Ha. rewrite Z.add_0_r, Hp8, Z.sub_0_r in Ha.
    destruct (Hstr a) as (Hrom & Hsr).
    { unfold SnprintfDefB.absn_word_end. cbn [length Z.of_nat]. rewrite Z.add_0_r, Hp8, Z.sub_0_r. lia. }
    exact (lx_aview_some _ _ a Hsr).
Qed.

Lemma c0bc_img_atom : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = w64 (VAL n).
Proof. intros E n HE Hn. unfold w64. rewrite <- (HE n Hn). symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* A machine state at a cut, as the engine's entry state. *)
Lemma c0bc_shape : forall pc (W : world SEGS) ms,
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  restrict (w_H W) ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS).
Proof.
  intros pc W ms Hpc Hresv Hpend Hrom Hfregs Hfcsr.
  destruct ms as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
  subst. reflexivity.
Qed.

Ltac c0bc_awr := cbn [ss_mem add_cond]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* After a run over read-only regions: the memory is the one before (HM : ms_mem ms = the cut's memory). *)
Ltac c0bc_ro HM :=
  lazymatch goal with HFx : frame_of ?Ex ?rs ?m (ms_mem ?msn) |- _ =>
    let H := fresh "HMn" in
    pose proof (frame_of_read_only Ex rs m (ms_mem msn) eq_refl HFx) as H;
    rewrite HM in H; clear HM; rename H into HM end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* At the strncmp entry (the run stopped at the call): the registers the call lemma takes. *)
Ltac c0bc_tail HM HJ lem y H11 HY2 :=
  lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?m) |- _ =>
  pmkst HS; rewrite HM in HJ |- *;
  let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in let Q12 := fresh "Q12" in
  let Q25 := fresh "Q25" in let Q9 := fresh "Q9" in let Q18 := fresh "Q18" in let KR := fresh "KR" in
  let KR' := fresh "KR'" in
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (12%bv : bv 5) Q12; prreg HS (25%bv : bv 5) Q25; prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18;
  lazymatch Ex with lx_env ?cx0 ?fp0 ?regs0 ?ex0 =>
  pose proof (regs_kept_of_st_ok SEGS Ex _ _ regs0 (lx_xatoms cx0 fp0 ++ ex0)
    (map (Z_to_bv 5) [2; 3; 4; 8; 19; 20; 21; 22; 23; 26; 27]) HS) as KR;
  cbn [restrict ms_regs] in KR;
  specialize (KR ltac:(unfold lx_env; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]) eq_refl);
  assert (KR' : forall n, In n [2; 3; 4; 8; 19; 20; 21; 22; 23; 26; 27] ->
    getr (ms_regs m) (Z_to_bv 5 n) = getr regs0 (Z_to_bv 5 n)) by (let q := fresh "q" in let Hq := fresh "Hq" in
      intros q Hq; apply KR; apply in_map; exact Hq);
  clear KR;
  apply (lem (ms_regs m) _ y HJ);
  [ etransitivity; [exact (KR' 2 ltac:(cbn; tauto)) | assumption]
  | etransitivity; [exact (KR' 8 ltac:(cbn; tauto)) | assumption]
  | rewrite Q9, (lx_env_reg cx0 fp0 _ _ 2 (2%bv : bv 5)) by reflexivity; assumption
  | etransitivity; [exact (KR' 3 ltac:(cbn; tauto)) | assumption]
  | etransitivity; [exact (KR' 4 ltac:(cbn; tauto)) | assumption]
  | rewrite Q18; assumption
  | etransitivity; [exact (KR' 22 ltac:(cbn; tauto)) | assumption]
  | etransitivity; [exact (KR' 20 ltac:(cbn; tauto)) | assumption]
  | etransitivity; [exact (KR' 21 ltac:(cbn; tauto)) | assumption]
  | etransitivity; [exact (KR' 27 ltac:(cbn; tauto)) | assumption]
  | etransitivity; [exact (KR' 26 ltac:(cbn; tauto)) | assumption]
  | etransitivity; [exact (KR' 19 ltac:(cbn; tauto)) | assumption]
  | etransitivity; [exact (KR' 23 ltac:(cbn; tauto)) | assumption]
  | rewrite Q25; assumption
  | rewrite Q10; assumption
  | rewrite Q11; exact H11
  | rewrite Q12; reflexivity
  | exact Q1
  | exact HY2 ]
  end end.

(* ---- the cut BC's data, fixed for the whole segment ---- *)
Section c.
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Variable cx : lxcx.
Variables fp k acc : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable md3 : Model.
Variable pos : nat.
Variables r fab op nm want b p : Z.
Variable bs : list byte.
#[local] Notation K0 := (c0_nchv (lc_pl cx) pos).
#[local] Notation B0 := (c0_basev (lc_pl cx) pos).
#[local] Notation GS := (c0_gs (lc_pl cx) pos op).
#[local] Notation NK := (c0_nk (lc_pl cx) pos).
#[local] Notation NN := (Boxreg.bx_n bs).
#[local] Notation RW := (r + 56 * Boxreg.bx_n bs).
#[local] Notation BSL := ((c0_basev (lc_pl cx) pos * 2 ^ 56) mod 2 ^ 64).
#[local] Notation ROWB := (c0_placed bs b (c0_nchv (lc_pl cx) pos) p (c0_gs (lc_pl cx) pos op)).
#[local] Notation J3 := (fun (m : word -> option byte) (md : Model) =>
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m md k).
Hypothesis HB : lx_base B MT cx.
Hypothesis HJ3 : J3 (ms_mem ms3) md3.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].
Hypothesis HMO : mo_le MT (lc_S cx) S3 acc.
Hypothesis HSC : lx_from B MT POST (C0_SC B MT i).
Hypothesis HCOM : c0_com i cx fp W3 ms3 C0P_BC pos r fab op bs.
Hypothesis HNM : c0_nm B MT i cx k acc ly3 S3 W3 ms3 pos r nm.
Hypothesis R24 : getr (ms_regs ms3) 24 = w64 (Z.land op 8).
Hypothesis R26 : getr (ms_regs ms3) 26 = w64 B0.
Hypothesis S50 : lslot cx W3 ms3 0x50 BSL.
Hypothesis S60 : lslot cx W3 ms3 0x60 nm.
Hypothesis HWANT : LLVMFuzzerTestOneInput_case0.c0_want bs K0 B0 want.
Hypothesis Hwant : -1 <= want <= 40.
Hypothesis S20 : lslot cx W3 ms3 0x20 (want mod 2 ^ 64).
Hypothesis HPL : reac_boxreg_declare_c.declare_placed bs K0 B0 b p.
Hypothesis HREG : lreg W3 ms3 r ROWB.
Hypothesis R10 : getr (ms_regs ms3) 10 = w64 0.
Hypothesis R19 : getr (ms_regs ms3) 19 = w64 NN.
Hypothesis R23 : getr (ms_regs ms3) 23 = w64 RW.

(* ---- what the cut gives: the blocks, the row, the model ---- *)
Lemma c0bc_blk : In (r, LX_REG) (ablocks B ly3 S3) /\ In (nm, NK + 1) (ablocks B ly3 S3) /\
  (forall q n, In (q, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (q, n) (ablocks B ly3 S3)).
Proof.
  pose proof HNM as (_ & _ & HBL & _). rewrite HBL. split; [|split].
  - apply in_or_app. right. left. reflexivity.
  - apply in_or_app. right. right. left. reflexivity.
  - intros q n H. apply in_or_app. left. exact H.
Qed.

Lemma c0bc_model : length bs = 288%nat /\ 0 <= NN <= 4 /\ 0 <= b <= 127 /\
  p = (if B0 <? 0 then 0 else 1) /\ (0 <= B0 -> b = B0) /\ -128 <= B0 < 128 /\
  Forall (fun c => 0 < c < 256) GS.
Proof.
  pose proof HCOM as (_ & _ & _ & HINV & HFAB & _).
  pose proof HINV as ((HL & HB1 & HB2 & _) & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in *.
  pose proof (LLVMFuzzerTestOneInput_case0.c0_base_range (c0_pl0 (lc_pl cx) pos)) as HBr.
  unfold c0_basev. fold (c0_basev (lc_pl cx) pos).
  destruct HPL as ((_ & Hk2 & _) & Hn5 & [(Hb0 & -> & -> & _) | (Hb0 & -> & Hb & Hlf)]).
  - split; [exact HL|]. split; [lia|]. split; [unfold c0_basev in *; lia|].
    split; [replace (B0 <? 0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
    split; [intros _; reflexivity|]. split; [unfold c0_basev in *; lia|].
    unfold c0_gs. destruct (Z.land op 8 =? 0); [apply LLVMFuzzerTestOneInput_rn.nm_str_ok | apply Forall_nil].
  - destruct Hlf as [(Hm1 & _) | (_ & Hbk & _)]; [lia|].
    split; [exact HL|]. split; [lia|]. split; [lia|].
    split; [replace (B0 <? 0) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
    split; [intros H; lia|]. split; [unfold c0_basev in *; lia|].
    unfold c0_gs. destruct (Z.land op 8 =? 0); [apply LLVMFuzzerTestOneInput_rn.nm_str_ok | apply Forall_nil].
Qed.

Lemma c0bc_regs3 : lregs cx fp ms3 /\ getr (ms_regs ms3) 20 = w64 r /\
  getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\ getr (ms_regs ms3) 27 = w64 fab.
Proof.
  pose proof HCOM as (HBD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G20 & G21 & G27).
  pose proof HBD as (_ & _ & _ & _ & _ & _ & HREGS & _). tauto.
Qed.

Lemma c0bc_geo : r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ in_app r 288 /\
  0 <= lsp1 cx /\ alloc_ceiling + 32768 - 287 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47 /\ lsp1 cx mod 32 = 0.
Proof.
  pose proof c0bc_blk as (Hrin & _).
  pose proof HJ3 as (HAR & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR Hrin) as (Hr16 & Hr0 & Hrc & Hria & _).
  change (req_size LX_REG) with 288 in Hrc, Hria.
  pose proof (lx_sp_facts B MT cx HB) as (Hs16 & Hs0 & Hs1 & Hsp1 & Hs32).
  pose proof asan_consts as (C1 & _).
  split; [exact Hr16|]. split; [exact Hr0|]. split; [exact Hrc|]. split; [exact Hria|].
  split; [lia|]. split; [lia|]. split; [lia | exact Hs32].
Qed.

Lemma c0bc_row_vm : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (RW + 8) 4 b /\
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (RW + 20) 4 p.
Proof.
  pose proof c0bc_model as (HL & Hn & Hb & Hp & _ & _ & _).
  assert (HLr : length ROWB = 288%nat) by exact (LLVMFuzzerTestOneInput_case0.c0_decl_length bs b K0 p GS HL Hn).
  assert (E8 : Boxreg.rd4 ROWB (56 * NN + 8) = b).
  { apply c0bc_row_rd4; [exact HL | exact Hn | lia | lia | apply reac_boxreg_declare_inv.decl_row_base | lia]. }
  assert (E20 : Boxreg.rd4 ROWB (56 * NN + 20) = p).
  { apply c0bc_row_rd4; [exact HL | exact Hn | lia | lia | apply reac_boxreg_declare_inv.decl_row_pin
      | destruct (B0 <? 0); lia]. }
  split.
  - replace (RW + 8) with (r + (56 * NN + 8)) by lia.
    pose proof (rt_vm4 W3 (ms_mem ms3) r (56 * NN + 8) ROWB HLr ltac:(lia) ltac:(lia) ltac:(rewrite E8; lia) HREG) as H.
    rewrite E8 in H. exact H.
  - replace (RW + 20) with (r + (56 * NN + 20)) by lia.
    assert (Hp0 : 0 <= Boxreg.rd4 ROWB (56 * NN + 20)) by (rewrite E20; destruct (B0 <? 0); lia).
    pose proof (rt_vm4 W3 (ms_mem ms3) r (56 * NN + 20) ROWB HLr ltac:(lia) ltac:(lia) Hp0 HREG) as H.
    rewrite E20 in H. exact H.
Qed.

#[local] Notation EX := (c0bc_ex b p BSL nm).
#[local] Notation E3 := (lx_env cx fp (ms_regs ms3) (c0bc_ex b p BSL nm)).

Lemma c0bc_E : lx_E cx fp E3 /\ ew E3 48 = w64 b /\ ew E3 49 = w64 p /\ ew E3 50 = w64 BSL /\ ew E3 51 = w64 nm /\
  ew E3 23 = w64 RW /\ ew E3 27 = w64 fab /\ ew E3 LA_SB = w64 SHADOW_OFF.
Proof.
  pose proof c0bc_regs3 as (HREGS & G20 & G21 & G27).
  assert (HE : lx_E cx fp E3) by (apply lx_env_E; exact HREGS).
  pose proof HE as (_ & _ & _ & _ & _ & HE32 & _).
  split; [exact HE|].
  split; [exact (lx_env_ex cx fp (ms_regs ms3) EX 0 ltac:(lia))|].
  split; [exact (lx_env_ex cx fp (ms_regs ms3) EX 1 ltac:(lia))|].
  split; [exact (lx_env_ex cx fp (ms_regs ms3) EX 2 ltac:(lia))|].
  split; [exact (lx_env_ex cx fp (ms_regs ms3) EX 3 ltac:(lia))|].
  split; [rewrite (lx_env_reg cx fp _ _ 23 (23%bv : bv 5)) by reflexivity; exact R23|].
  split; [rewrite (lx_env_reg cx fp _ _ 27 (27%bv : bv 5)) by reflexivity; exact G27|].
  exact HE32.
Qed.

Lemma c0bc_seat : st_ok_pi SEGS VAL E3 (mkSS C0P_BC (lx_sr C0BC_OV) [c0bc_spill; c0bc_row] None C0BC_G)
    (restrict (w_H W3) ms3) /\
  sh_ok SEGS C0BC_Bx C0BC_SH E3 (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  pose proof c0bc_regs3 as (HREGS & G20 & G21 & G27).
  pose proof HCOM as (HBD & _ & _ & _ & _ & _ & _ & _ & HSL & _).
  pose proof HSL as (_ & _ & S30 & _).
  pose proof HBD as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & _).
  pose proof c0bc_model as (HL & Hn & Hb & Hp & _ & _ & _).
  pose proof c0bc_geo as (Hr16 & Hr0 & Hrc & Hria & Hsp0 & Hsp1 & Hsp2 & Hsp32).
  pose proof c0bc_blk as (Hrin & _).
  pose proof c0bc_row_vm as (VM8 & VM20).
  pose proof c0bc_E as (HE & E48 & E49 & E50 & E51 & E23 & E27 & E32).
  pose proof HJ3 as (HAR & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (RNG : forall off v, lslot cx W3 ms3 off v -> 0 <= v < 2 ^ 64)
    by (intros off v Hv; exact (c0_rdword_range _ _ _ _ Hv)).
  pose proof (RNG _ _ S30) as Hfab. pose proof (RNG _ _ S60) as Hnm. pose proof (RNG _ _ S50) as Hbsl.
  assert (U23 : bv_unsigned (ew E3 23) = RW) by (rewrite E23; apply unsigned_lit_small; lia).
  pose proof (lx_base_sp B MT cx fp HB E3 HE) as USP.
  split.
  - rewrite (c0bc_shape C0P_BC W3 ms3 Hpc Hresv Hsvc Hrom Hfreg Hfcsr).
    apply pa_entry_st_ok_full.
    + apply lx_regs_ok; [apply lx_regs_ok_atoms|]. unfold C0BC_OV. apply Forall_app. split.
      * exact (lx_ov_ok cx fp ms3 EX HREGS).
      * apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. rewrite R10. reflexivity.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold c0bc_spill, YP09.region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite USP.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        -- apply (chunk_ok_val SEGS E3 _ (lsp1 cx) 0x30 8 (SOff 27 0) fab); [exact (c0k_atom0 E3 27 fab E27 Hfab) | cbn; lia | cbn; lia |].
           apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S30.
        -- apply (chunk_ok_val SEGS E3 _ (lsp1 cx) 0x50 8 (SOff 50 0) BSL); [exact (c0k_atom0 E3 50 _ E50 Hbsl) | cbn; lia | cbn; lia |].
           apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S50.
        -- apply (chunk_ok_val SEGS E3 _ (lsp1 cx) 0x60 8 (SOff 51 0) nm); [exact (c0k_atom0 E3 51 _ E51 Hnm) | cbn; lia | cbn; lia |].
           apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S60.
      * unfold c0bc_row, YP09.region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite U23.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS E3 _ RW 8 4 (SOff 48 0) b); [exact (c0k_atom0 E3 48 b E48 ltac:(lia)) | cbn; lia | cbn; lia |].
           exact VM8.
        -- apply (chunk_ok_val SEGS E3 _ RW 20 4 (SOff 49 0) p);
             [exact (c0k_atom0 E3 49 p E49 ltac:(destruct (B0 <? 0); lia)) | cbn; destruct (B0 <? 0); lia | cbn; lia |].
           exact VM20.
    + cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; [|split; exact I]. split; [|exact I].
      unfold YP09.extent_disjoint, c0bc_spill, c0bc_row.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U23. fold (YP09.base_val E3 (Some LA_SP)). rewrite USP.
      right. lia.
    + split; [|split; exact I]. unfold C0BC_G. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, E23. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
      split; [repeat split; first [exact I | lia]|]. split; [repeat split; first [exact I | lia] | exact I].
  - unfold sh_ok, C0BC_SH, C0BC_Bx. apply Forall_cons; [|apply Forall_nil].
    apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E3 RW r LX_REG 0 56 23%nat HAR Hrin).
    + apply U_atom; [exact E32 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E23 | lia].
    + lia.
    + lia.
    + change (req_size LX_REG) with 288. lia.
Qed.

(* ---- strncmp's two strings ---- *)
Lemma c0bc_fld_ok : abfm_cstr_ok SEGS W3 (ms_mem ms3) (RW + 24) (firstn 31 GS).
Proof.
  pose proof c0bc_model as (HL & Hn & _ & _ & _ & _ & HGS).
  pose proof c0bc_blk as (Hrin & _).
  pose proof HJ3 as (HAR & _).
  apply (c0bc_cstr_ok_fld ly3 S3 W3 (ms_mem ms3) md3 r RW GS HAR Hrin ltac:(lia) ltac:(lia) HGS).
  - intros j Hj.
    assert (Hj32 : (j < 32)%nat) by (rewrite length_app, length_firstn in Hj; cbn [length] in Hj; lia).
    pose proof (HREG (56 * NN + 24 + Z.of_nat j) ltac:(unfold LX_REG; lia)) as Hv. unfold lview in Hv.
    replace (RW + 24 + Z.of_nat j) with (r + (56 * NN + 24 + Z.of_nat j)) by lia. rewrite Hv. f_equal.
    exact (c0bc_row_name bs b K0 p GS j HL Hn HGS Hj).
  - intros j Hj. pose proof (HREG j Hj) as Hv. unfold lview in Hv. rewrite Hv. discriminate.
Qed.

Lemma c0bc_name_ok : Z.land op 8 = 0 -> abfm_cstr_ok SEGS W3 (ms_mem ms3) nm GS.
Proof.
  intros H8.
  pose proof HNM as (_ & _ & _ & _ & _ & Hname & _).
  pose proof c0bc_blk as (_ & Hnin & _).
  pose proof HJ3 as (HAR & _).
  assert (HGS : GS = c0_s (lc_pl cx) pos) by (unfold c0_gs; rewrite H8; reflexivity). rewrite HGS.
  pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hnk.
  pose proof (LLVMFuzzerTestOneInput_rn.rn_name_len (c0_pl2 (lc_pl cx) pos)) as Hlen.
  assert (HNB : c0_nb (lc_pl cx) pos =
    printf_facts_c.pf_bytes (c0_s (lc_pl cx) pos ++ [0]) ++ LLVMFuzzerTestOneInput_rn.nm_rest (c0_nb (lc_pl cx) pos))
    by (unfold c0_s, c0_nb, c0_nk; apply LLVMFuzzerTestOneInput_rn.nm_split).
  assert (HL : Z.of_nat (length (c0_nb (lc_pl cx) pos)) = NK + 1).
  { unfold c0_nb, c0_nk. rewrite length_app. cbn [length]. lia. }
  pose proof (LLVMFuzzerTestOneInput_rn.nm_len (c0_s (lc_pl cx) pos)
    (LLVMFuzzerTestOneInput_rn.nm_rest (c0_nb (lc_pl cx) pos))) as HL2.
  rewrite <- HNB, HL in HL2.
  assert (Hs : Forall (fun c => 0 < c < 256) (c0_s (lc_pl cx) pos)) by apply LLVMFuzzerTestOneInput_rn.nm_str_ok.
  unfold c0_nk in *.
  apply (c0bc_cstr_ok_blk ly3 S3 W3 (ms_mem ms3) md3 nm (read_name_c.rn_k (c0_pl2 (lc_pl cx) pos))
    (c0_s (lc_pl cx) pos) HAR Hnin ltac:(lia) ltac:(lia) Hs).
  - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    pose proof (Hname (Z.of_nat j) ltac:(lia)) as Hv. unfold lview in Hv. rewrite Hv. f_equal.
    rewrite Nat2Z.id, HNB.
    rewrite app_nth1 by (unfold printf_facts_c.pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
    unfold printf_facts_c.pf_bytes. change (Z_to_bv 8 0) with (Z_to_bv 8 0 : byte). rewrite map_nth.
    assert (Hc : 0 <= nth j (c0_s (lc_pl cx) pos ++ [0]) 0 < 256).
    { destruct (Nat.lt_ge_cases j (length (c0_s (lc_pl cx) pos))) as [Hlt | Hge].
      - rewrite app_nth1 by exact Hlt. rewrite Forall_forall in Hs.
        pose proof (Hs _ (nth_In (c0_s (lc_pl cx) pos) 0 Hlt)). lia.
      - rewrite app_nth2 by exact Hge. replace (j - length (c0_s (lc_pl cx) pos))%nat with 0%nat by lia.
        cbn [nth]. lia. }
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact Hc.
  - intros j Hj. pose proof (Hname j Hj) as Hv. unfold lview in Hv. rewrite Hv. discriminate.
Qed.

(* ---- where the bytes the cut speaks about lie: never in strncmp's stack [sp1 - 8192, sp1) ---- *)
#[local] Notation RS := [(nm, NK + 1); (r, LX_REG)].

Lemma c0bc_kat_rng : forall a, c0_kat cx fp [] RS a -> 0 <= a < 2 ^ 64 /\ (a + 8192 < lsp1 cx \/ lsp1 cx <= a).
Proof.
  intros a Ha.
  pose proof c0bc_blk as (Hrin & Hnin & Hmono).
  pose proof HJ3 as (HAR & _).
  pose proof (lx_sp_facts B MT cx HB) as (Hs16 & Hs0 & Hs1 & Hsp1 & Hs32).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ3 HFR) as (HF0 & HFc & HFapp & _ & HF64 & HSHeq).
  pose proof asan_consts as (C1 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR Hrin) as (_ & Hr0 & Hrc & _).
  change (req_size LX_REG) with 288 in Hrc.
  pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hnk.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ nm (NK + 1) HAR Hnin) as (_ & Hq0 & Hqc & _).
  rewrite c0bc_req in Hqc by (unfold c0_nk; lia).
  assert (ESH : lSH cx fp + 64 <= alloc_ceiling /\ 0 <= lSH cx fp).
  { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. rewrite HSHeq. unfold SHADOW_OFF in *.
    assert (D0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
    destruct HFapp as [_ [Hlo | [Hhi1 Hhi2]]].
    - assert (lF cx fp / 8 <= 268430848) by (apply Z.div_le_upper_bound; lia). lia.
    - assert (lF cx fp / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). lia. }
  assert (HGin : lc_n cx = 0 \/ (0 < lc_n cx /\ 4096 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling)).
  { pose proof HB as (_ & _ & _ & Hin0 & _).
    destruct Hin0 as [H0 | (Hn & Hin)]; [left; exact (proj1 H0) | right].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ (lc_p cx) (lc_n cx) HAR (Hmono _ _ Hin)) as (_ & Hp0 & Hp1 & _).
    rewrite c0bc_req in Hp1 by lia. lia. }
  unfold c0_kat in Ha. unfold c0_nk, lc_n in *.
  destruct Ha as [[H _] | [H | [H | [H | H]]]].
  - split; lia.
  - destruct HGin as [Hn0 | (Hn & Hp0 & Hp1)]; split; lia.
  - split; lia.
  - split; lia.
  - apply Exists_exists in H as (q & Hq & Hqa). destruct Hq as [<- | [<- | []]]; cbn [fst snd] in Hqa;
      unfold LX_REG in *; split; lia.
Qed.

(* ---- the landing on SC (0x8069c) ---- *)
Lemma c0bc_land : forall (regs2 : bvmap 5 word) mem2 md2,
  J3 mem2 md2 -> c0_kept cx fp W3 [] RS (ms_mem ms3) mem2 ->
  getr regs2 2 = w64 (lsp1 cx) -> getr regs2 8 = w64 (lsp0 cx) -> getr regs2 9 = w64 (lsp1 cx) ->
  getr regs2 3 = getr (lc_regs cx) 3 -> getr regs2 4 = getr (lc_regs cx) 4 ->
  getr regs2 18 = w64 SHADOW_OFF -> getr regs2 22 = w64 (lSH cx fp) ->
  getr regs2 20 = w64 r -> getr regs2 21 = w64 (lF cx fp + 64) -> getr regs2 27 = w64 fab ->
  getr regs2 26 = w64 B0 -> getr regs2 10 = w64 0 -> getr regs2 19 = w64 NN ->
  getr regs2 23 = w64 RW -> getr regs2 25 = w64 (RW + 8) ->
  SRr SEGS W3 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + C0P_SC)) mem2 (seg_rom SEGS)) md2) (POST cx).
Proof.
  intros regs2 mem2 md2 HJ2 HK G2 G8 G9 G3 G4 G18 G22 G20 G21 G27 G26 G10 G19 G23 G25.
  pose proof c0bc_geo as (_ & _ & _ & _ & Hsp0 & Hsp1 & Hsp2 & _).
  assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
  set (ms' := mkst regs2 (Z_to_bv 64 (BASE + C0P_SC)) mem2 (seg_rom SEGS)).
  assert (HK' : c0_kept cx fp W3 [] RS (ms_mem ms3) (ms_mem ms')) by exact HK.
  destruct (c0_land B MT i cx fp k acc ly3 S3 W3 ms3 mem2 regs2 C0P_BC C0P_SC pos r fab op nm bs [] RS
    HB HCOM HNM (Forall_nil _) (or_introl eq_refl) HK G2 G8 G9 G3 G4 G18 G22 G20 G21 G27) as [HC HN].
  apply (HSC cx fp k acc ly3 S3 W3 ms' md2 HB HJ2 HFR HMO).
  exists pos, r, fab, op, nm, want, b, p, bs.
  split; [exact HC|]. split; [exact HN|]. split; [exact G26|].
  split; [exact (c0_slot_keep cx fp W3 [] RS ms3 ms' HK' Hsp 0x60 nm ltac:(lia) ltac:(lia) (Forall_nil _) S60)|].
  split; [exact HWANT|]. split; [exact Hwant|].
  split; [exact (c0_slot_keep cx fp W3 [] RS ms3 ms' HK' Hsp 0x20 _ ltac:(lia) ltac:(lia) (Forall_nil _) S20)|].
  split; [exact HPL|].
  split; [exact (c0_reg_keep cx fp W3 [] RS ms3 ms' HK' r ROWB ltac:(right; left; reflexivity) HREG)|].
  split; [exact G10|]. split; [exact G19|]. split; [exact G23 | exact G25].
Qed.

(* ---- the call strncmp (row + 24, given or "", 31) at 0x80698: lx_hyps' lh_strncmp (lib/B/Rt/StrncmpDefB.v) ----
   Its two read-only premises: rom_viewN is lx_base's arodata_okP, which the cut's journal keeps; rom_viewO comes
   from AR at the call and BLxLib's blx_pinned. The answer is 0: the row's name field holds firstn 31 of the given string and
   its NUL (c0bc_row_name, c0bc_strn_eq). The interceptor writes only inside [sp1 - 2 * ESTACK, sp1). *)
Lemma c0bc_call : forall (regsT : bvmap 5 word) mdT y,
  J3 (ms_mem ms3) mdT ->
  getr regsT 2 = w64 (lsp1 cx) -> getr regsT 8 = w64 (lsp0 cx) -> getr regsT 9 = w64 (lsp1 cx) ->
  getr regsT 3 = getr (lc_regs cx) 3 -> getr regsT 4 = getr (lc_regs cx) 4 ->
  getr regsT 18 = w64 SHADOW_OFF -> getr regsT 22 = w64 (lSH cx fp) ->
  getr regsT 20 = w64 r -> getr regsT 21 = w64 (lF cx fp + 64) -> getr regsT 27 = w64 fab ->
  getr regsT 26 = w64 B0 -> getr regsT 19 = w64 NN -> getr regsT 23 = w64 RW -> getr regsT 25 = w64 (RW + 8) ->
  getr regsT 10 = w64 (RW + 24) -> getr regsT 11 = w64 y -> getr regsT 12 = w64 31 ->
  getr regsT 1 = Z_to_bv 64 (BASE + C0P_SC) ->
  abfm_cstr_ok SEGS W3 (ms_mem ms3) y GS ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_strncmp)) (ms_mem ms3) (seg_rom SEGS)) mdT)
    (POST cx).
Proof.
  intros regsT mdT y HJ G2 G8 G9 G3 G4 G18 G22 G20 G21 G27 G26 G19 G23 G25 H10 H11 H12 Hra HY2.
  pose proof (lx_sp_facts B MT cx HB) as (Hs16 & Hs0 & Hs1 & Hsp1 & Hs32).
  pose proof asan_consts as (C1 & _).
  pose proof HB as ((_ & _ & _ & Hgp & Htp & Hstk & _) & _ & _ & _ & _ & Hfr0 & _ & _ & HRO0 & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & HSTAT & _ & HQT).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _). fold (lsp0 cx) in Hslo, Hshi.
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (Hsp : spZ regsT = lsp0 cx + (lsp1 cx - lsp0 cx)).
  { unfold spZ. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (Hsp1' : spZ regsT = lsp1 cx) by lia.
  assert (Ho16 : (lsp1 cx - lsp0 cx) mod 16 = 0).
  { apply Z.mod_divide in Hs16; [|lia]. apply Z.mod_divide in Hs32; [|lia]. apply Z.mod_divide; [lia|].
    destruct Hs16 as [x Hx]. destruct Hs32 as [z Hz]. exists (2 * z - x). lia. }
  assert (HPRE : abfm_ecall_pre_k SEGS B ABFM_STK_RT_STR ly3 S3 W3 regsT (ms_mem ms3) mdT).
  { split.
    { eapply (ecall_pre_at SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
        [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) mdT k regsT (lsp1 cx - lsp0 cx) HJ Hsp Ho16 ltac:(lia)
        ltac:(unfold LX_STK; rewrite Hes; lia));
        [rewrite Hra; apply ret_ok_codeptr_v; [unfold C0P_SC; lia | reflexivity] | rewrite G3; exact Hgp
        | rewrite G4; exact Htp]. }
    unfold ABFM_STK_RT_STR, ASAN_CEIL. rewrite Eslo, Hes, Hsp1'. unfold LX_STK in Hslo.
    split; [lia|]. split; [lia|].
    intros a Ha. apply HPRES. unfold LX_STK. lia. }
  assert (HRO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms3)))
    by exact (lx_arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO0).
  eapply SRr_bind.
  { exact (lh_strncmp B MT HY ly3 S3 W3 regsT (ms_mem ms3) mdT (RW + 24) y 31 (firstn 31 GS) GS HPRE
      (lx_rom_viewN B W3 (ms_mem ms3) HRO)
      (lx_rom_viewO B ly3 S3 W3 (ms_mem ms3) mdT (blx_pinned B (lh_glob B MT HY)) HAR)
      H10 H11 H12 ltac:(lia) c0bc_fld_ok HY2). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hmat & Hv10 & Hv & Hcmp & Hfr & Hpres2).
  assert (HJ2 : J3 mem2 md2).
  { cbv beta.
    eapply (ajournal_after_write SEGS B LAWS pa_segs_low LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx)
      (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) mdT k mem2 md2
      (fun a => spZ regsT - ABFM_STK_RT_STR <= a < spZ regsT) S3 [(LX_CID, fp)] HJ).
    - intros a Ha Hna. exact (Hfr a Ha Hna).
    - exact Hpres2.
    - exact Hmat.
    - intros a Ha. left. left. unfold ABFM_STK_RT_STR in Ha. rewrite Hsp1', Hes in Ha. unfold LX_STK. lia.
    - exact HAR2.
    - reflexivity.
    - reflexivity.
    - lia.
    - rewrite HFR, Hfr0. reflexivity.
    - exact HQT. }
  assert (HK : c0_kept cx fp W3 [] RS (ms_mem ms3) mem2).
  { intros a Ha. destruct (c0bc_kat_rng a Ha) as [Hr Hw].
    apply Hfr; [exact Hr|]. unfold ABFM_STK_RT_STR. rewrite Hsp1', Hes. lia. }
  replace (cfg_at SEGS (raZ regsT) regs2 mem2 md2) with (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + C0P_SC)) mem2 (seg_rom SEGS)) md2)
    by (unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (KP : forall n, acallee_saved n -> getr regs2 (Z_to_bv 5 n) = getr regsT (Z_to_bv 5 n)) by exact HP.
  apply (c0bc_land regs2 mem2 md2 HJ2 HK).
  - etransitivity; [exact (KP 2 ltac:(unfold acallee_saved; lia)) | exact G2].
  - etransitivity; [exact (KP 8 ltac:(unfold acallee_saved; lia)) | exact G8].
  - etransitivity; [exact (KP 9 ltac:(unfold acallee_saved; lia)) | exact G9].
  - etransitivity; [exact (KP 3 ltac:(unfold acallee_saved; lia)) | exact G3].
  - etransitivity; [exact (KP 4 ltac:(unfold acallee_saved; lia)) | exact G4].
  - etransitivity; [exact (KP 18 ltac:(unfold acallee_saved; lia)) | exact G18].
  - etransitivity; [exact (KP 22 ltac:(unfold acallee_saved; lia)) | exact G22].
  - etransitivity; [exact (KP 20 ltac:(unfold acallee_saved; lia)) | exact G20].
  - etransitivity; [exact (KP 21 ltac:(unfold acallee_saved; lia)) | exact G21].
  - etransitivity; [exact (KP 27 ltac:(unfold acallee_saved; lia)) | exact G27].
  - etransitivity; [exact (KP 26 ltac:(unfold acallee_saved; lia)) | exact G26].
  - rewrite Hv10. f_equal. apply (proj2 Hcmp). change (Z.to_nat 31) with 31%nat. exact (c0bc_strn_eq GS).
  - etransitivity; [exact (KP 19 ltac:(unfold acallee_saved; lia)) | exact G19].
  - etransitivity; [exact (KP 23 ltac:(unfold acallee_saved; lia)) | exact G23].
  - etransitivity; [exact (KP 25 ltac:(unfold acallee_saved; lia)) | exact G25].
Qed.

(* ---- the walk 0x80630 .. 0x80698 and the call ---- *)
Lemma c0bc_run : SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  pose proof c0bc_seat as [HS SHOK].
  pose proof HJ3 as HJ.
  pose proof c0bc_E as (HE & E48 & E49 & E50 & E51 & E23 & E27 & E32).
  pose proof c0bc_model as (HL & Hn & Hb & Hp & Hbb & HB0 & HGS).
  pose proof c0bc_regs3 as (HREGS & G20 & G21 & G27).
  pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
  pose proof c0bc_geo as (Hr16 & Hr0 & Hrc & Hria & _). pose proof asan_consts as (C1 & _).
  assert (E26 : ew E3 26 = w64 B0) by (rewrite (lx_env_reg cx fp _ _ 26 (26%bv : bv 5)) by reflexivity; exact R26).
  assert (E24 : ew E3 24 = w64 (Z.land op 8)) by (rewrite (lx_env_reg cx fp _ _ 24 (24%bv : bv 5)) by reflexivity; exact R24).
  assert (Hl8 : 0 <= Z.land op 8 < 2 ^ 64) by (destruct (LLVMFuzzerTestOneInput_case0.c0_op8 op) as [H8|H8]; rewrite H8; lia).
  assert (D24 : sv_denot E3 (SOff 24 0) = w64 (Z.land op 8)) by (apply c0k_atom0; [exact E24 | exact Hl8]).
  assert (Hbsl : 0 <= BSL < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (D50 : sv_denot E3 (SOff 50 0) = w64 (B0 * 2 ^ 56)) by (rewrite (c0k_atom0 E3 50 _ E50 Hbsl); apply c0k_w64_mod).
  assert (F10 : Z_to_bv 64 (bv_unsigned (ew E3 23) + 24) = w64 (RW + 24))
    by (rewrite E23; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  assert (F25 : Z_to_bv 64 (bv_unsigned (ew E3 23) + 8) = w64 (RW + 8))
    by (rewrite E23; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  assert (HEI : img_env VAL A_LIM E3) by apply lx_env_img.
  (* 0x80630 bnez a0 (a0 = 0: bcmp's answer) .. the ASan check of the row's pinned field, decided by the engine *)
  paj_run_tok RUN HS HJ SHOK C0BC_Bspan; [c0bc_awr|].
  pose proof (frame_of_read_only E3 [c0bc_spill; c0bc_row] (ms_mem ms3) (ms_mem ms) eq_refl HF) as HM. clear HF HFr HG.
  (* 0x80658 bne a0, a1: the pinned field is base >= 0 (declare_placed): the abort (0x80fa4) is refuted *)
  psrr_branch_tok RUN BR HS SHOK C0BC_Bspan.
  { rewrite branch_ne_U, U_SExt, !U_SAlu, !U_SLit in Hc.
    rewrite (c0bc_U_atom E3 49 p E49), (c0bc_U_atom E3 26 _ E26), Hp, (c0bc_pin _ HB0) in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK C0BC_Bspan; [c0bc_awr|]. c0bc_ro HM.
  (* 0x80664 bltz (slot 0x50 = base << 56) *)
  psrr_branch_tok RUN BR HS SHOK C0BC_Bspan.
  - (* base < 0: no base check, on to 0x80680 *)
    rewrite (c0k_br_lt E3 (SOff 50 0) (SLit 0) (B0 * 2 ^ 56) 0 D50 eq_refl ltac:(lia) ltac:(lia)) in Hc.
    apply Z.ltb_lt in Hc. assert (Hneg : B0 < 0) by lia. clear Hc.
    paj_run_tok RUN HS HJ SHOK C0BC_Bspan; [c0bc_awr|]. c0bc_ro HM.

            psrr_branch_tok RUN BR HS SHOK C0BC_Bspan.
            ** (* op & 8 = 0: strncmp (row name, name, 31) *)
               rewrite (c0k_br_eq E3 (SOff 24 0) (SLit 0) (Z.land op 8) 0 D24 eq_refl Hl8 ltac:(lia)) in Hc.
               apply Z.eqb_eq in Hc. rename Hc into H8.
               paj_run_tok RUN HS HJ SHOK C0BC_Bspan; [c0bc_awr|]. c0bc_ro HM.
               c0bc_tail HM HJ c0bc_call nm E51 (c0bc_name_ok H8).
            ** (* op & 8 <> 0: strncmp (row name, "", 31) *)
               rewrite (c0k_br_eq E3 (SOff 24 0) (SLit 0) (Z.land op 8) 0 D24 eq_refl Hl8 ltac:(lia)) in Hc.
               apply Z.eqb_neq in Hc. rename Hc into H8.
               assert (HGSn : GS = []) by (unfold c0_gs; destruct (Z.land op 8 =? 0) eqn:E8; [apply Z.eqb_eq in E8; lia | reflexivity]).
               paj_run_tok RUN HS HJ SHOK C0BC_Bspan; [c0bc_awr|]. c0bc_ro HM.
               pose proof (c0bc_img_atom E3 (A_OBJ 5) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as H11.
               pose proof HJ3 as (HAR3 & _).
               pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO0 & _).
               pose proof (c0bc_empty_ok ly3 S3 W3 (ms_mem ms3) md3 HAR3
                 (lx_arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HRO0)) as HY2.
               rewrite <- HGSn in HY2.
               c0bc_tail HM HJ c0bc_call (VAL (A_OBJ 5)) H11 HY2.
  - (* base >= 0: the ASan check of the row's base field (engine), then bne a0, s10 at 0x8067c *)
    rewrite (c0k_br_lt E3 (SOff 50 0) (SLit 0) (B0 * 2 ^ 56) 0 D50 eq_refl ltac:(lia) ltac:(lia)) in Hc.
    apply Z.ltb_ge in Hc. assert (Hpos : 0 <= B0) by lia. clear Hc.
    paj_run_tok RUN HS HJ SHOK C0BC_Bspan; [c0bc_awr|]. c0bc_ro HM.
    psrr_branch_tok RUN BR HS SHOK C0BC_Bspan.
    { rewrite branch_ne_U, U_SExt in Hc.
      rewrite (c0bc_U_atom E3 48 b E48), (c0bc_U_atom E3 26 _ E26), (Hbb Hpos), (c0bc_base_eq B0 ltac:(lia)), Z.eqb_refl in Hc.
      discriminate Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK C0BC_Bspan; [c0bc_awr|]. c0bc_ro HM.

            psrr_branch_tok RUN BR HS SHOK C0BC_Bspan.
            ** (* op & 8 = 0: strncmp (row name, name, 31) *)
               rewrite (c0k_br_eq E3 (SOff 24 0) (SLit 0) (Z.land op 8) 0 D24 eq_refl Hl8 ltac:(lia)) in Hc.
               apply Z.eqb_eq in Hc. rename Hc into H8.
               paj_run_tok RUN HS HJ SHOK C0BC_Bspan; [c0bc_awr|]. c0bc_ro HM.
               c0bc_tail HM HJ c0bc_call nm E51 (c0bc_name_ok H8).
            ** (* op & 8 <> 0: strncmp (row name, "", 31) *)
               rewrite (c0k_br_eq E3 (SOff 24 0) (SLit 0) (Z.land op 8) 0 D24 eq_refl Hl8 ltac:(lia)) in Hc.
               apply Z.eqb_neq in Hc. rename Hc into H8.
               assert (HGSn : GS = []) by (unfold c0_gs; destruct (Z.land op 8 =? 0) eqn:E8; [apply Z.eqb_eq in E8; lia | reflexivity]).
               paj_run_tok RUN HS HJ SHOK C0BC_Bspan; [c0bc_awr|]. c0bc_ro HM.
               pose proof (c0bc_img_atom E3 (A_OBJ 5) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as H11.
               pose proof HJ3 as (HAR3 & _).
               pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO0 & _).
               pose proof (c0bc_empty_ok ly3 S3 W3 (ms_mem ms3) md3 HAR3
                 (lx_arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HRO0)) as HY2.
               rewrite <- HGSn in HY2.
               c0bc_tail HM HJ c0bc_call (VAL (A_OBJ 5)) H11 HY2.
Qed.

End c.

(* ---- the segment BC -> SC ---- *)
Theorem c0_bc : forall POST i, lx_from B MT POST (C0_SC B MT i) -> lx_from B MT POST (C0_BC B MT i).
Proof.
  intros POST i HSC cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HBC.
  destruct HBC as (pos & r & fab & op & nm & want & b & p & bs & HCOM & HNM & R25 & R26 & S50 & S60 & HW & Hw & S20 &
    R24 & HPL & HREG & R10 & R19 & R23).
  exact (c0bc_run POST i cx fp k acc ly3 S3 W3 ms3 md3 pos r fab op nm want b p bs HB HJ HFR HMO HSC HCOM HNM
    R24 R26 S50 S60 HW Hw S20 HPL HREG R10 R19 R23).
Qed.
End a.
