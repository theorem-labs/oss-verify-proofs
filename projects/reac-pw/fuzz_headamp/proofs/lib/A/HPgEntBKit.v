(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEntBKit.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths renamed, every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0), the real-frame cells by the plan's slot map (0x20>0x48, 0x70>0x98, 0x80>0xf0, 0xb0>0xd0, 0xc0>0xe0, 0xc8>0x68, 0xf0>0x110, 0xf8>0x118), the R-based regions re-cut for that layout (A [R+0x98, R+0xf8) read only; B [R+0x48, R+0x70) with the cell R+0x48 read only and [R+0x68, R+0x70) written; C [R+0x110, R+0x120)), the frame for locals of class 4 (1024 bytes), the real frame of 0x1e0 bytes, RPgCfgChanges.cfg_wx / cfg_segs_low -> HPgSteps.img_wx / img_segs_low. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the kit of the walk of ent_build's cases
   1, 4, 5 and 9 (pod.h:285-296, 326-339, 367-377) inside LLVMFuzzerTestOneInput, from the case entries 0x81cf8,
   0x81b88, 0x81d40, 0x81ea4 to the join J 0x8237c. Proves no function (kind: segment lemma).

   THE SYMBOLIC STATE AT A CASE ENTRY. The registers are their own atoms (sr_atoms). The extra atoms are
     32 = F (the frame for locals), 33 = the value of R+0xd0 (the shadow address of &pp->len),
     34 = the value of R+0x118 (what is left before the kind byte), 35 = the next input byte (0 when none).
   The regions are R-based (atom 9 = s1 = R) and F-based (atom 32):
     A  [R+0x98, R+0xf8)  read only: R+0x98 = s5, R+0xd0 = atom 33, R+0xe0 = F+0xf8, R+0xf0 = s11
     B  [R+0x48, R+0x70)  R+0x48 = F+0x100 read only; [R+0x68, R+0x70) written: case 1 spills the cursor there (0x81f90)
     C  [R+0x110, R+0x120) R+0x110 = F+0xf0 read only, R+0x118 = atom 34 written (in.n)
     E  [F+0xf0, F+0x158) written: e, all zero (ent_build's memset, 0x817e4)
     I  [s8, s8+1)        read only: the next input byte, atom 35 (only when one is left)
   The other R-relative cells lie outside every region, so a run keeps them (frame_of).
   THE SHADOW CHECKS. The shadow offset is s7 (atom 23, fact [K, K]); the token engine (lib/Reusable/YCbn.v)
   pays an input read with one obligation over the cursor (atom 24, fact [1, 2^47 - 1] from the cut's amem_range)
   and needs none for e: the shadow entry (atom 32, [0xf0, 0x158)) covers it (e is in scope at a case entry:
   granules 0x1e .. 0x2a of the frame's shadow are 0, HPgSeg.hs_PJ). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the pcs ---- *)
Definition EB_D1 : Z := 0x81cf8.
Definition EB_D4 : Z := 0x81b88.
Definition EB_D5 : Z := 0x81d40.
Definition EB_D9 : Z := 0x81ea4.
Definition EB_J : Z := 0x8237c.

(* ---- the code the engine reads: 0x81b80 .. 0x8237c (the cases and their tails) and 0x82664 .. 0x827a0 (the
   second tests of the checks, which the token engine decodes) ---- *)
Definition eb_tbl : ctable :=
  Eval vm_compute in (build_table rsegs 0x82664 80 (build_table rsegs 0x81b80 512 TEmpty)).
Lemma eb_tbl_ok : table_ok rsegs eb_tbl.
Proof.
  change eb_tbl with (build_table rsegs 0x82664 80 (build_table rsegs 0x81b80 512 TEmpty)).
  apply build_table_ok; [lia|]. apply build_table_ok0. lia.
Qed.
Definition eb_wx : wx_segs_nowrap rsegs := HPgSteps.img_wx.
Definition eb_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd := HPgSteps.img_segs_low.

(* ---- the shadow machinery: s7 is the offset, e is covered ---- *)
Definition EBx : sv := SOff 23 0.
Definition Espan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition eb_SH : list shent := [mkSHE 32 0xf0 0x158].
Definition eb_extra (F vb0 nl b : Z) : list word := [Z_to_bv 64 F; Z_to_bv 64 vb0; Z_to_bv 64 nl; Z_to_bv 64 b].

(* ---- the regions ---- *)
Definition eb_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0x98 0xf8 0 0
  [ YP09.mkChunk 0x98 (CVal 8 (SOff 21 0)); YP09.mkChunk 0xd0 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0xe0 (CVal 8 (SOff 32 0xf8)); YP09.mkChunk 0xf0 (CVal 8 (SOff 27 0)) ].
Definition eb_rB : YP09.region := YP09.mkRegion (Some 9%nat) 0x48 0x70 0x68 0x70
  [ YP09.mkChunk 0x48 (CVal 8 (SOff 32 0x100)) ].
Definition eb_rC : YP09.region := YP09.mkRegion (Some 9%nat) 0x110 0x120 0x118 0x120
  [ YP09.mkChunk 0x110 (CVal 8 (SOff 32 0xf0)); YP09.mkChunk 0x118 (CVal 8 (SOff 34 0)) ].
Definition eb_rE : YP09.region := YP09.mkRegion (Some 32%nat) 0xf0 0x158 0xf0 0x158 [YP09.mkChunk 0xf0 (CZero 104)].
Definition eb_rI : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition eb_regions (byte : bool) : smem :=
  if byte then [eb_rA; eb_rB; eb_rC; eb_rE; eb_rI] else [eb_rA; eb_rB; eb_rC; eb_rE].

(* ---- the facts: R in [alloc_ceiling, 2^47] 16-aligned (alloc_ceiling >= 0x7fff7f800000, YCbq.asan_consts), s7 = K,
   the cursor below 2^47, F below alloc_ceiling (<= 0x7fffff800000) ---- *)
Definition eb_atoms : list (nat * afact) :=
  [ (9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (24%nat, mkAF 1 (2 ^ 47 - 1) 0); (32%nat, mkAF 4096 0x7fffff800000 0) ].
Definition ss_eb (pc : Z) (byte : bool) : sstate :=
  mkSS pc sr_atoms (eb_regions byte) None (mkFacts eb_atoms [] []).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the value of an extra atom *)
Lemma eb_ew_extra : forall regs F vb0 nl b j v, nth j (eb_extra F vb0 nl b) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  ew (Ereg regs (eb_extra F vb0 nl b)) (32 + j) = Z_to_bv 64 v.
Proof. intros regs F vb0 nl b j v H. rewrite ew_Ereg_extra. exact H. Qed.
Lemma eb_U_reg : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs extra) n) = v.
Proof. intros regs extra n r v Hn Hr Hv. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. apply unsigned_lit_small. lia. Qed.

(* ---- the entry state ---- *)
Lemma eb_entry : forall pc (byte : bool) (W : world rsegs) (regs : bvmap 5 word) memc (R F cur vb0 nl b pp : Z),
  0 <= pc ->
  getr regs 9 = w64 R -> getr regs 23 = w64 SHADOW_OFF -> getr regs 24 = w64 cur ->
  getr regs 21 = w64 (pp + 0x4000) -> getr regs 27 = w64 pp ->
  alloc_ceiling <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 ->
  4096 <= F -> F + 1024 <= alloc_ceiling ->
  1 <= cur <= 2 ^ 47 - 1 -> 0 <= vb0 < 2 ^ 64 -> 0 <= nl < 2 ^ 64 -> 0 <= b < 256 ->
  0 <= pp -> pp + 0x4000 < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x48) 8 (F + 0x100) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 vb0 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xf8) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0xf0) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 nl ->
  (forall o, (0x68 <= o < 0x70 \/ 0x118 <= o < 0x120) -> apresent (w_H W) memc (R + o)) ->
  (forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0xf0 + i) = Some (Z_to_bv 8 0)) ->
  (forall o, 0 <= o < 104 -> apresent (w_H W) memc (F + 0xf0 + o)) ->
  (byte = true -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b /\ (cur + 1 <= R + 0x48 \/ R + 0x120 <= cur) /\
                  (cur + 1 <= F + 0xf0 \/ F + 0x158 <= cur)) ->
  st_ok rsegs (Ereg regs (eb_extra F vb0 nl b)) (ss_eb pc byte)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
  intros pc byte W regs memc R F cur vb0 nl b pp Hpc H9 H23 H24 H21 H27 HR1 HR2 HR3 HF1 HF2 Hc Hv Hn Hb Hpp1 Hpp2
    V20 V70 V80 Vb0 Vc0 Vf0 Vf8 Pw Ez Pe Hbyte.
  pose proof asan_consts as (Hceil & _).
  rewrite restrict_mkst_fx.
  set (E := Ereg regs (eb_extra F vb0 nl b)).
  assert (U9 : bv_unsigned (ew E 9) = R) by (exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (exact (eb_U_reg regs _ 23 23%bv _ eq_refl H23 ltac:(unfold SHADOW_OFF; lia))).
  assert (U24 : bv_unsigned (ew E 24) = cur) by (exact (eb_U_reg regs _ 24 24%bv cur eq_refl H24 ltac:(lia))).
  assert (U21 : bv_unsigned (ew E 21) = pp + 0x4000) by (exact (eb_U_reg regs _ 21 21%bv _ eq_refl H21 ltac:(lia))).
  assert (U27 : bv_unsigned (ew E 27) = pp) by (exact (eb_U_reg regs _ 27 27%bv pp eq_refl H27 ltac:(lia))).
  assert (U32 : bv_unsigned (ew E 32) = F).
  { subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth eb_extra]. apply unsigned_lit_small. lia. }
  assert (U33 : bv_unsigned (ew E 33) = vb0).
  { subst E. rewrite (ew_Ereg_extra regs _ 1). cbn [nth eb_extra]. apply unsigned_lit_small. lia. }
  assert (U34 : bv_unsigned (ew E 34) = nl).
  { subst E. rewrite (ew_Ereg_extra regs _ 2). cbn [nth eb_extra]. apply unsigned_lit_small. lia. }
  assert (U35 : bv_unsigned (ew E 35) = b).
  { subst E. rewrite (ew_Ereg_extra regs _ 3). cbn [nth eb_extra]. apply unsigned_lit_small. lia. }
  assert (RA : region_ok rsegs E (mrestrict (w_H W) memc) eb_rA).
  { unfold region_ok, eb_rA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val rsegs E _ R 0x98 8 (SOff 21 0) (pp + 0x4000));
        [cbn [sv_denot]; rewrite U21, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V70].
    - apply (chunk_ok_val rsegs E _ R 0xd0 8 (SOff 33 0) vb0);
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vb0].
    - apply (chunk_ok_val rsegs E _ R 0xe0 8 (SOff 32 0xf8) (F + 0xf8));
        [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vc0].
    - apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 27 0) pp);
        [cbn [sv_denot]; rewrite U27, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V80]. }
  assert (RB : region_ok rsegs E (mrestrict (w_H W) memc) eb_rB).
  { unfold region_ok, eb_rB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable rsegs); apply Pw; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val rsegs E _ R 0x48 8 (SOff 32 0x100) (F + 0x100));
      [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V20]. }
  assert (RC : region_ok rsegs E (mrestrict (w_H W) memc) eb_rC).
  { unfold region_ok, eb_rC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable rsegs); apply Pw; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val rsegs E _ R 0x110 8 (SOff 32 0xf0) (F + 0xf0));
        [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vf0].
    - apply (chunk_ok_val rsegs E _ R 0x118 8 (SOff 34 0) nl);
        [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vf8]. }
  assert (RE : region_ok rsegs E (mrestrict (w_H W) memc) eb_rE).
  { unfold region_ok, eb_rE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); replace (F + o) with (F + 0xf0 + (o - 0xf0)) by lia; apply Pe; lia|].
    apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
    replace (F + 0xf0 + i) with (F + 0xf0 + i) by lia. apply Ez. exact Hi. }
  unfold ss_eb. apply (entry_st_ok_full rsegs); try change (Ereg regs (eb_extra F vb0 nl b)) with E.
  - apply regs_ok_Ereg.
  - destruct byte; vm_compute; reflexivity.
  - destruct byte; unfold eb_regions; repeat apply Forall_cons; try apply Forall_nil; try assumption.
    destruct (Hbyte eq_refl) as (Vb & _ & _).
    unfold region_ok, eb_rI. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs E _ cur 0 1 (SOff 35 0) b);
      [cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity | change (8 * Z.of_N 1) with 8; lia | lia |].
    rewrite Z.add_0_r. exact Vb.
  - destruct byte; unfold eb_regions; apply pairwise_disjoint_of_extents;
      unfold eb_rA, eb_rB, eb_rC, eb_rE, eb_rI; cbn [map]; unfold extent_of_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
      try change (Ereg regs (eb_extra F vb0 nl b)) with E; rewrite ?U9, ?U32, ?U24.
    + destruct (Hbyte eq_refl) as (_ & D1 & D2). repeat split; first [exact I | lia].
    + repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [eb_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U23, U24, U32. repeat split; try lia;
      first [change (2 ^ 4) with 16; exact HR3 | change (2 ^ 0) with 1; apply Z.mod_1_r].
Qed.

(* ---- the shadow entry over e: e is in scope (granules 0x1e .. 0x2a are 0) and lies outside the shadow band ---- *)
Lemma eb_shok : forall (regs : bvmap 5 word) (H : word -> bool) mem F vb0 nl b,
  getr regs 23 = w64 SHADOW_OFF -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0xf0) 104 ->
  (forall a, F + 0xf0 <= a < F + 0x158 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)) ->
  sh_ok rsegs EBx eb_SH (Ereg regs (eb_extra F vb0 nl b)) (mrestrict H mem).
Proof.
  intros regs H mem F vb0 nl b H23 HF1 HF2 Hra Hap. pose proof asan_consts as (Hceil & _).
  set (E := Ereg regs (eb_extra F vb0 nl b)).
  assert (U23 : U E (SOff 23 0) = SHADOW_OFF).
  { apply U_atom; [subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl), H23; reflexivity | unfold SHADOW_OFF; lia]. }
  assert (U32 : U E (SOff 32 0) = F).
  { apply U_atom; [subst E; rewrite (ew_Ereg_extra regs _ 0); reflexivity | lia]. }
  apply Forall_cons; [|apply Forall_nil]. unfold shent_ok. cbn [she_m she_lo she_hi].
  unfold EBx. rewrite U23, U32. split.
  - rewrite <- (aview_rd_of rsegs). replace (F + 0xf0) with (F + 0xf0) by lia. exact Hra.
  - unfold app_apart. cbn [she_m she_lo she_hi]. unfold EBx. rewrite U23, U32. intros a Ha. apply Hap. lia.
Qed.

(* ---- reading the final state ---- *)
Lemma eb_region : forall E ss ms r, st_ok rsegs E ss ms -> In r (ss_mem ss) -> region_ok rsegs E (ms_mem ms) r.
Proof. intros E ss ms r HS Hin. exact (mem_ok_region rsegs E _ _ r (st_ok_mem_ok rsegs E ss ms HS) Hin). Qed.
Lemma eb_chunk_val : forall E m r off (n : N) e v,
  region_ok rsegs E m r -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem rsegs m (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
  intros E m r off n e v HR Hin He Hv Hn.
  exact (val_of_chunk_ok rsegs E m _ off n e v (region_ok_chunk rsegs E m r _ HR Hin) He Hv Hn).
Qed.
Lemma eb_chunk_zero : forall E m r off len,
  region_ok rsegs E m r -> In (YP09.mkChunk off (CZero len)) (YP09.r_chunks r) ->
  forall i, 0 <= i < len -> mbyte rsegs m (base_val E (YP09.r_base r) + off + i) = Some (Z_to_bv 8 0).
Proof.
  intros E m r off len HR Hin i Hi.
  destruct (region_ok_chunk rsegs E m r _ HR Hin i ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
  cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-. exact Hb2.
Qed.
End b.
