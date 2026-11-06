(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v, with its module paths and module names changed; 1922 of its 1971 lines of code are new or changed and 78 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSteps.v at a58a6fc257b (parts 1, 2) and
   a6c23b42ca2 (part 3); ported to
   reac-pw/fuzz_headamp image A: module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec -> HPgBase / HPgCSpec, the
   rl_ prefix -> hd_; every image address relocated from role's image A to headamp's (the jump table 0x20e94 ->
   0x20e9c with its nine entries and targets measured from headamp's pinned bytes, the dispatch block 0x80b1c ->
   0x8183c, the two fuzz_u32 sites 0x80ee4 / 0x81454 -> 0x81c04 / 0x82174 and their ends 0x815e8 / 0x8163c ->
   0x82308 / 0x8235c, the code tables over 0x81c04 .. 0x82360 and 0x825bc .. 0x82838); the input-length cell of the
   two fuzz_u32 sites [s1+0xf8] -> [s1+0x118] (headamp's frame-slot map); img_wx, img_segs_low and same_io_wvb are
   stated here (role took them from its cfg walk file, which headamp has no twin of); part 3 (the scope-store
   sites) restated at headamp's fourteen sites, each measured on image A: role's ten builder sites relocated, role's
   role-object pair replaced by headamp's res and x sites, the run 0x82578 stated with the value it leaves in a1
   (hd_scope_stmtAx, hd_inc_a1, sv_addiw1), role's unused fsh_ss2 dropped, fsh_pts added for the 17-granule x
   sites. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgSteps.v, with its module paths and module names changed; 267 of its 332 lines of code are new or changed and 1906 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM3eRcBlk.v, with its addresses changed; 279 of its 333 lines of code are new or changed and 278 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the cell write of segment M03 of the walk of LLVMFuzzerTestOneInput (0x80c40), as one
   block lemma over a machine state in the shape of lib/AU/HPgSteps.v hdu_blk_postE (the journal extended, the
   registers outside clob kept, the frames, blocks, I/O state and meter as at the start, every byte outside the write
   set kept, and what the block computes). Proves no function (kind: segment lemma).

   THE CODE (43 words CELL 0x836e4 .. 0x8378c; R = s1 (x9), x = [R+0x138], cap = s4 (x20), the shadow offset s11 (x27))
     0x836e4 .. 0x836ec  a0 := [R+0x138] (x); a0 := lw [x+0x7c] (x->n, no instrumented check); bge a0,s4 -> RC 0x83850
     0x836f0 .. 0x836f4  li a3,9; bltu a3,a0 -> 0x83a14 (unimp)
     0x836f8 .. 0x83708  a0 := 12 n; a1 := [R+0xc0] (the one's complement of x + 4); bltu a1,a0 -> 0x83a14 (unimp)
     0x8370c .. 0x83724  a0 := [R+0xc8] (x + 4) + 12 n; the instrumented check of a0 (shadow byte (a0 >> 3) + s11,
                         bnez to the slow block 0x837ec); sw s5 (x21, the channel) at x + 4 + 12 n
     0x83728 .. 0x83764  a1 := lw [x+0x7c] again, the same two unimp tests; a2 := x + 4 + 12 n; the check of a2 + 4;
                         sw a6 (x16, the param) at x + 8 + 12 n
     0x83768 .. 0x8377c  the check of a2 + 8; sw s2 (x18, the value) at x + 12 + 12 n
     0x83780 .. 0x8378c  a1 := n + 1; sw a1 at x + 0x7c (no instrumented check); j LATCH 0x836b4
   The shadow bytes of x's 136 bytes are 0, so each check reads 0 and falls through: the slow blocks 0x837ec ..
   0x83818 and the unimp at 0x83a14 are never reached.

   HOW. Each arm is one run of the engine (lib/Reusable YCbn.v token runs, YCbq.v journal runs) over the 43 words,
   from an entry state whose registers are atoms and whose two extra atoms are x (32) and the cell R+0xc0 (33).
   The real-frame cells R+0xc0, R+0xc8, R+0x138 are one read-only region based at s1 (atom 9). n is split into its
   values, so x->n is the literal n and every address the code forms is atom 32 plus a literal; cap <= n and n < cap
   are told apart before the run, and atom 20's range (the closed numerals [n, n], or [n + 1, 9]) decides the `bge`.
   RC arm (cap <= n): x->n is a read-only region based at atom 32, and the run is a plain journal run to RC.
   LATCH arm (n < cap): the 12 bytes of cell n and x->n are two regions based at atom 32 whose write windows are
   exactly those bytes (they lie in the frame for locals the walk owns: YCbq awr_byte's in_frames case); the shadow
   base is s11 (atom 27, the fact SHADOW_OFF) and the shadow entry [x, x + 136) (YCbq.shent_ok_of_range) decides
   each instrumented check; atom 33's range [2^64 - 2^47, 2^64 - 1] decides the pointer-sum test. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSiteA HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSegM.   (* HPgSegM.hqu_not v = -1 - v *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition BC_CELL : Z := 0x836e4.
Definition BC_LATCH : Z := 0x836b4.
Definition BC_RC : Z := 0x83850.

(* ======================================= the code table ======================================= *)
(* the 43 words 0x836e4 .. 0x8378c; LATCH, RC, the slow blocks and the unimp lie outside them *)
Definition bc_tbl : ctable := build_table rsegs BC_CELL 43 TEmpty.
Lemma bc_tbl_ok : table_ok rsegs bc_tbl.
Proof. apply build_table_ok0. unfold BC_CELL. lia. Qed.

(* ======================================= the entry states ======================================= *)
(* the shadow base s11 (atom 27) and x's shadow entry (atom 32) *)
Definition bc_Bx : sv := SOff 27 0.
Definition bc_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition bc_SH : list shent := [mkSHE 32 0 136].
(* the extra atoms: x (32) and the cell R+0xc0 (33) *)
Definition bc_extra (x : Z) : list word := [w64 x; w64 (HPgSegM.hqu_not (x + 4) mod 2 ^ 64)].
(* the real-frame cells R+0xc0 (~(x + 4)), R+0xc8 (x + 4) and R+0x138 (x) *)
Definition bc_RR : YP09.region := YP09.mkRegion (Some 9%nat) 0xc0 0x140 0 0
  [YP09.mkChunk 0xc0 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xc8 (CVal 8 (SOff 32 4));
   YP09.mkChunk 0x138 (CVal 8 (SOff 32 0))].
(* x->n read only (the RC arm), cell n and x->n with their write windows (the LATCH arm) *)
Definition bc_RN_ro (n : Z) : YP09.region := YP09.mkRegion (Some 32%nat) 0x7c 0x80 0 0
  [YP09.mkChunk 0x7c (CVal 4 (SLit n))].
Definition bc_RC_w (n : Z) : YP09.region :=
  YP09.mkRegion (Some 32%nat) (4 + 12 * n) (16 + 12 * n) (4 + 12 * n) (16 + 12 * n) [].
Definition bc_RN_w (n : Z) : YP09.region := YP09.mkRegion (Some 32%nat) 0x7c 0x80 0x7c 0x80
  [YP09.mkChunk 0x7c (CVal 4 (SLit n))].
(* the facts: cap's range (the `bge`), the shadow base, x's range (the shadow entry's span), R+0xc0's range *)
Definition bc_facts_rc (n : Z) : facts := mkFacts [(20%nat, mkAF n n 0)] [] [].
Definition bc_facts_l (n : Z) : facts :=
  mkFacts [(20%nat, mkAF (n + 1) 9 0); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 4096 (2 ^ 47 - 456) 0); (33%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)] [] [].
Definition bc_regs_rc (n : Z) : smem := [bc_RR; bc_RN_ro n].
Definition bc_regs_l (n : Z) : smem := [bc_RR; bc_RC_w n; bc_RN_w n].
Definition bc_ss_rc (n : Z) : sstate := mkSS BC_CELL sr_atoms (bc_regs_rc n) None (bc_facts_rc n).
Definition bc_ss_l (n : Z) : sstate := mkSS BC_CELL sr_atoms (bc_regs_l n) None (bc_facts_l n).

Lemma bc_wf_rc : forall n, 0 <= n <= 9 -> regions_wf (bc_regs_rc n) = true.
Proof.
intros n Hn.
assert (H : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9) by lia.
destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma bc_wf_l : forall n, 0 <= n <= 8 -> regions_wf (bc_regs_l n) = true.
Proof.
intros n Hn.
assert (H : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8) by lia.
destruct H as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute; reflexivity.
Qed.

(* ======================================= values ======================================= *)
Section v. Context {fx : YK11.FPState}.
Lemma bc_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* a stored n-byte chunk read back as the low n bytes of the stored word *)
Lemma bc_val_of_chunk_w : forall E m base off (n : N) (e : sv),
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
val_mem rsegs m (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E m base off n e H Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. injection Hb1 as <-.
rewrite Hb2. f_equal. unfold YP09.byte_of_word.
assert (Hp : 0 < 2 ^ (8 * Z.of_N n)) by (apply Z.pow_pos_nonneg; lia).
rewrite le_byte_small; [| rewrite Hnn; apply Z.mod_pos_bound; exact Hp | lia].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
symmetry. apply HPgSiteA.hd_shr_mod; lia.
Qed.

(* a 4-byte chunk at base + off, read back at a *)
Lemma bc_cv4 : forall E m base off e a v,
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 4 e)) -> a = base + off ->
bv_unsigned (sv_denot E e) mod 2 ^ 32 = v -> val_mem rsegs m a 4 v.
Proof.
intros E m base off e a v Hc -> <-.
exact (bc_val_of_chunk_w E m base off 4 e Hc ltac:(cbn; lia)).
Qed.
End v.

(* the chunk at offset off of a region's chunk list *)
Ltac bc_get_chunk Hch off name :=
lazymatch type of Hch with Forall _ ?cs =>
  let r := eval vm_compute in (List.find (fun c => Z.eqb (YP09.c_off c) off) cs) in
  lazymatch r with Some ?c =>
    pose proof (proj1 (Forall_forall _ _) Hch c ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as name
  end end.

(* ======================================= the entry states are sound ======================================= *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma bc_entry_rc : forall (W : world rsegs) memc (regs : bvmap 5 word) (R x n : Z),
getr regs 9 = w64 R -> getr regs 20 = w64 n ->
4096 <= x -> x + 136 <= R -> R + 0x140 <= 2 ^ 47 -> 0 <= n <= 9 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 x ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 (HPgSegM.hqu_not (x + 4) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 (x + 4) ->
val_mem rsegs (mrestrict (w_H W) memc) (x + 0x7c) 4 n ->
st_ok rsegs (Ereg regs (bc_extra x)) (bc_ss_rc n)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 BC_CELL) memc (seg_rom rsegs))).
Proof.
intros W memc regs R x n H9 H20 Hx0 HxR HR Hn V138 Vc0 Vc8 Vn.
set (E := Ereg regs (bc_extra x)).
assert (E9u : bv_unsigned (ew E 9) = R)
  by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (E20u : bv_unsigned (ew E 20) = n)
  by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 x) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (HPgSegM.hqu_not (x + 4) mod 2 ^ 64)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E32u : bv_unsigned (ew E 32) = x) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (Z.mod_pos_bound (HPgSegM.hqu_not (x + 4)) (2 ^ 64) ltac:(lia)) as Hnx.
rewrite restrict_mkst_fx. unfold bc_ss_rc. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- exact (bc_wf_rc n Hn).
- change (Ereg regs (bc_extra x)) with E. unfold bc_regs_rc. constructor; [|constructor; [|constructor]].
  + unfold bc_RR. apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [exact E9u | lia | lia |].
    repeat apply Forall_cons; [..|apply Forall_nil].
    * apply (chunk_ok_val rsegs _ _ R 0xc0 8 (SOff 33 0) (HPgSegM.hqu_not (x + 4) mod 2 ^ 64));
        [rewrite bc_denot0; exact E33 | cbn; lia | cbn; lia | exact Vc0].
    * apply (chunk_ok_val rsegs _ _ R 0xc8 8 (SOff 32 4) (x + 4)); [| cbn; lia | cbn; lia | exact Vc8].
      cbn [sv_denot]. rewrite E32u. reflexivity.
    * apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 32 0) x); [rewrite bc_denot0; exact E32 | cbn; lia | cbn; lia | exact V138].
  + unfold bc_RN_ro. apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 32 x); [exact E32u | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ x 0x7c 4 (SLit n) n); [reflexivity | cbn; lia | cbn; lia | exact Vn].
- change (Ereg regs (bc_extra x)) with E. unfold bc_regs_rc.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [bc_RR bc_RN_ro YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite E9u, E32u.
  repeat split; first [exact I | lia].
- change (Ereg regs (bc_extra x)) with E.
  split; [|split; exact I]. cbn [bc_facts_rc f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20u. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
Qed.

Lemma bc_entry_l : forall (W : world rsegs) memc (regs : bvmap 5 word) (R x cap n : Z),
getr regs 9 = w64 R -> getr regs 20 = w64 cap -> getr regs 27 = w64 SHADOW_OFF ->
4096 <= x -> x + 136 <= R -> R + 0x140 <= 2 ^ 47 -> 0 <= n < cap -> cap <= 9 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 x ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 (HPgSegM.hqu_not (x + 4) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 (x + 4) ->
val_mem rsegs (mrestrict (w_H W) memc) (x + 0x7c) 4 n ->
(forall a, x + 4 <= a < x + 0x80 -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (bc_extra x)) (bc_ss_l n)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 BC_CELL) memc (seg_rom rsegs))).
Proof.
intros W memc regs R x cap n H9 H20 H27 Hx0 HxR HR Hn Hcap V138 Vc0 Vc8 Vn Hpres.
set (E := Ereg regs (bc_extra x)).
assert (E9u : bv_unsigned (ew E 9) = R)
  by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (E20u : bv_unsigned (ew E 20) = cap)
  by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20; apply unsigned_lit_small; lia).
assert (E27u : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 x) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (HPgSegM.hqu_not (x + 4) mod 2 ^ 64)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E32u : bv_unsigned (ew E 32) = x) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Hnx : HPgSegM.hqu_not (x + 4) mod 2 ^ 64 = 2 ^ 64 - 1 - (x + 4)) by (apply HPgSegM.hqu_not_mod; lia).
assert (E33u : bv_unsigned (ew E 33) = 2 ^ 64 - 1 - (x + 4))
  by (rewrite E33, Hnx; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold bc_ss_l. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- apply bc_wf_l. lia.
- change (Ereg regs (bc_extra x)) with E. unfold bc_regs_l. constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold bc_RR. apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [exact E9u | lia | lia |].
    repeat apply Forall_cons; [..|apply Forall_nil].
    * apply (chunk_ok_val rsegs _ _ R 0xc0 8 (SOff 33 0) (HPgSegM.hqu_not (x + 4) mod 2 ^ 64));
        [rewrite bc_denot0; exact E33 | rewrite Hnx; cbn; lia | cbn; lia | exact Vc0].
    * apply (chunk_ok_val rsegs _ _ R 0xc8 8 (SOff 32 4) (x + 4)); [| cbn; lia | cbn; lia | exact Vc8].
      cbn [sv_denot]. rewrite E32u. reflexivity.
    * apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 32 0) x); [rewrite bc_denot0; exact E32 | cbn; lia | cbn; lia | exact V138].
  + unfold bc_RC_w. apply (HPgMem.hm_rw_region rsegs _ (w_H W) memc 32 x); [exact E32u | lia | lia | |].
    * intros o Ho. apply Hpres. lia.
    * apply Forall_nil.
  + unfold bc_RN_w. apply (HPgMem.hm_rw_region rsegs _ (w_H W) memc 32 x); [exact E32u | lia | lia | |].
    * intros o Ho. apply Hpres. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ x 0x7c 4 (SLit n) n); [reflexivity | cbn; lia | cbn; lia | exact Vn].
- change (Ereg regs (bc_extra x)) with E. unfold bc_regs_l.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [bc_RR bc_RC_w bc_RN_w YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite E9u, E32u.
  repeat split; first [exact I | lia].
- change (Ereg regs (bc_extra x)) with E.
  split; [|split; exact I]. cbn [bc_facts_l f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20u, E27u, E32u, E33u. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
  repeat split; lia.
Qed.
End e.

(* ======================================= the run tactics ======================================= *)
Ltac bc_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.

(* the write-window obligation of the LATCH arm: R's cells are read-only, x's two windows lie in the frame *)
Ltac bc_awr Hawr E32u :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
apply awr_ok_cons_ro; [cbn; lia|];
eapply awr_ok_cons_gen;
  [reflexivity | exact E32u | let a := fresh "a" in let Ha := fresh "Ha" in
     intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hawr; lia | ];
eapply awr_ok_cons_gen;
  [reflexivity | exact E32u | let a := fresh "a" in let Ha := fresh "Ha" in
     intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hawr; lia | apply awr_ok_nil].

(* the clauses of the post every arm proves the same way: the config, the journal, the kept registers, the frames,
   the blocks, the I/O state and the meter *)
Ltac bc_post_common lyc Sc W regs clob :=
lazymatch goal with HS : st_ok _ _ ?ssf (restrict _ ?msf), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  red; exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ msf regs _ (w_H W) clob HS);
          [apply env_agree_refl | vm_compute; reflexivity]|];
  split; [reflexivity|]; split; [apply Permutation_refl|]; split; [bc_io|];
  split; [apply mo_le_refl; assumption|]
end.

(* the bytes outside the run's write windows *)
Ltac bc_frame E32u :=
lazymatch goal with HFr : YP09.frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  let a := fresh "a" in let Ha := fresh "Ha" in let HW := fresh "HW" in
  let rg := fresh "rg" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a Ha HW; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
  rewrite unsigned_lit_small by lia;
  intros (rg & Hin & Hr); apply HW; cbv beta;
  cbn [In ss_mem bc_ss_l bc_ss_rc bc_regs_l bc_regs_rc] in Hin;
  repeat (destruct Hin as [<-|Hin];
    [cbn [bc_RR bc_RC_w bc_RN_w bc_RN_ro YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr;
     rewrite ?E32u in Hr; lia|]);
  destruct Hin
end.

(* the register value a chunk holds *)
Ltac bc_regval :=
  f_equal; f_equal; rewrite bc_denot0; apply ew_Ereg_nat; reflexivity.

(* LATCH: the three cell words and x->n + 1, from x's two regions at the end of the run *)
Ltac bc_vals E32u :=
cbv beta;
lazymatch goal with HS : st_ok _ _ _ (restrict _ _) |- _ =>
  let HRC := fresh "HRC" in let HRN := fresh "HRN" in let HchC := fresh "HchC" in let HchN := fresh "HchN" in
  pose proof (st_ok_region_at _ _ _ 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRC;
  destruct HRC as (_ & _ & _ & HchC);
  cbn [YP09.r_base YP09.r_chunks YP09.base_val] in HchC; rewrite E32u in HchC;
  pose proof (st_ok_region_at _ _ _ 2%nat _ HS ltac:(vm_compute; reflexivity)) as HRN;
  destruct HRN as (_ & _ & _ & HchN);
  cbn [YP09.r_base YP09.r_chunks YP09.base_val] in HchN; rewrite E32u in HchN;
  lazymatch goal with |- val_mem _ _ (_ + 4 + 12 * ?nn) _ _ /\ _ =>
    let o1 := eval vm_compute in (4 + 12 * nn) in
    let o2 := eval vm_compute in (8 + 12 * nn) in
    let o3 := eval vm_compute in (12 + 12 * nn) in
    let C1 := fresh "C1" in let C2 := fresh "C2" in let C3 := fresh "C3" in let C4 := fresh "C4" in
    bc_get_chunk HchC o1 C1; bc_get_chunk HchC o2 C2; bc_get_chunk HchC o3 C3; bc_get_chunk HchN 124 C4;
    split; [eapply bc_cv4; [exact C1 | lia | bc_regval]|];
    split; [eapply bc_cv4; [exact C2 | lia | bc_regval]|];
    split; [eapply bc_cv4; [exact C3 | lia | bc_regval]|];
    eapply bc_cv4; [exact C4 | lia | cbn [sv_denot]; rewrite Z_to_bv_unsigned; vm_compute; reflexivity]
  end
end.

(* one value of n in the LATCH arm *)
Ltac bc_arm_l lyc Sc W regs Hawr E32u :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  SHOK : sh_ok _ _ _ _ _ |- _ =>
  (aj_run_to_tok bc_tbl_ok HS HJ SHOK bc_span BC_LATCH; [bc_awr Hawr E32u | ]);
  apply SRr_ret; right; split; [lia|];
  bc_post_common lyc Sc W regs ([10; 11; 12; 13]%bv : list (bv 5));
  split; [bc_frame E32u | bc_vals E32u]
end.

(* one value of n in the RC arm *)
Ltac bc_arm_rc lyc Sc W regs E32u :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  (aj_run_to bc_tbl_ok HS HJ BC_RC; [awr_ok_tac | ]);
  apply SRr_ret; left; split; [lia|];
  bc_post_common lyc Sc W regs ([10]%bv : list (bv 5));
  split; [bc_frame E32u | exact I]
end.

(* ======================================= the block ======================================= *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Lemma bc_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (pos R x cap n : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
In (4, pos) own -> frame_addr lyc 4 pos <= x -> x + 136 <= frame_addr lyc 4 pos + 1024 -> x mod 8 = 0 ->
getr regs 9 = w64 R -> getr regs 20 = w64 cap -> getr regs 27 = w64 SHADOW_OFF ->
4096 <= x -> x + 136 <= R -> R + 0x140 <= 2 ^ 47 ->
0 <= cap <= 9 -> 0 <= n <= cap ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 x ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 (HPgSegM.hqu_not (x + 4) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 (x + 4) ->
val_mem rsegs (mrestrict (w_H W) memc) (x + 0x7c) 4 n ->
(forall a, x <= a < x + 136 -> aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF a) = Some 0) ->
SRr rsegs W (cfg_at rsegs BC_CELL regs memc mdc)
 (fun W2 c2 =>
  (cap <= n /\ hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc BC_RC [10]%bv
     (fun _ => False) (fun _ _ _ => True) W2 c2) \/
  (n < cap /\ hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc BC_LATCH [10; 11; 12; 13]%bv
     (fun a => x + 4 + 12 * n <= a < x + 16 + 12 * n \/ x + 0x7c <= a < x + 0x80)
     (fun W2 regs2 mem2 =>
        val_mem rsegs (mrestrict (w_H W2) mem2) (x + 4 + 12 * n) 4 (bv_unsigned (getr regs 21) mod 2 ^ 32) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (x + 8 + 12 * n) 4 (bv_unsigned (getr regs 16) mod 2 ^ 32) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (x + 12 + 12 * n) 4 (bv_unsigned (getr regs 18) mod 2 ^ 32) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (x + 0x7c) 4 (n + 1)) W2 c2)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs pos R x cap n
  HJ Hown HxF0 HxF1 Hx8 H9 H20 H27 Hx4k HxR HR47 Hcap Hn V138 Vc0 Vc8 Vn Hsh.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hfin) as (_ & _ & HFb & _).
change (fs_frame_bytes 4) with 1024 in HFb.
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (_ & _ & HFapp).
change (fs_frame_bytes 4) with 1024 in HFapp.
assert (Hpres : forall a, x + 4 <= a < x + 0x80 -> apresent (w_H W) memc a)
  by (intros a Ha; exact (proj1 (HFb a ltac:(lia)))).
assert (Hawr : forall a, x + 4 <= a < x + 0x80 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ intros a Ha. right. right. right. exists 4, pos. split; [exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 4) with 1024. lia. }
assert (E27 : ew (Ereg regs (bc_extra x)) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew (Ereg regs (bc_extra x)) 32 = Z_to_bv 64 x) by exact (ew_Ereg_extra regs _ 0).
assert (E32u : bv_unsigned (ew (Ereg regs (bc_extra x)) 32) = x) by (rewrite E32; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 BC_CELL) with (Z_to_bv 64 BC_CELL).
destruct (Z_lt_le_dec n cap) as [Hlt|Hge].
- (* n < cap: the cell, x->n + 1, to LATCH *)
  pose proof (bc_entry_l W memc regs R x cap n H9 H20 H27 Hx4k HxR HR47 ltac:(lia) ltac:(lia) V138 Vc0 Vc8 Vn Hpres)
    as HS.
  assert (U27 : U (Ereg regs (bc_extra x)) bc_Bx = SHADOW_OFF) by (apply U_atom; [exact E27 | unfold SHADOW_OFF; lia]).
  assert (U32 : U (Ereg regs (bc_extra x)) (SOff 32 0) = x) by (apply U_atom; [exact E32 | lia]).
  assert (HRA : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF x 136).
  { intros a Ha. exists 0. split; [exact (Hsh a Ha) | left; reflexivity]. }
  assert (SHOK : sh_ok rsegs bc_Bx bc_SH (Ereg regs (bc_extra x)) (mrestrict (w_H W) memc)).
  { unfold sh_ok, bc_SH. constructor; [|constructor].
    apply (shent_ok_of_range rsegs (w_H W) memc _ bc_Bx 32 x 136 x 0 136 HRA U27 U32); [lia | lia |].
    intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF. lia. }
  clear U27 U32 HRA.
  assert (Hn9 : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8) by lia.
  destruct Hn9 as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; bc_arm_l lyc Sc W regs Hawr E32u.
- (* cap <= n: n = cap, to RC *)
  assert (Hc : cap = n) by lia. subst cap.
  pose proof (bc_entry_rc W memc regs R x n H9 H20 Hx4k HxR HR47 ltac:(lia) V138 Vc0 Vc8 Vn) as HS.
  assert (Hn10 : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9) by lia.
  destruct Hn10 as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; bc_arm_rc lyc Sc W regs E32u.
Qed.
End d.
End b.

Print Assumptions bc_blk.
