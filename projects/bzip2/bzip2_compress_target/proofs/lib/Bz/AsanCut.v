(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzIncs BzArr BzCMem BzCStream BzCState BzCSortF BzCSortM BzCHuff BzCMtf BzCBlock BzArrD BzCLemmas1 CmpMem CmpCut CmpCutMS AsanKit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SubRead.
  Variable segs : list Segment.
  (* [comment removed for export] *)
  Lemma rw_cells_read_sub : forall m A cs k c j n a,
    rw_cells segs m A cs -> cell_at cs k = Some c -> (j + n <= csize c)%nat -> a = wa (A + Z.of_nat k + Z.of_nat j) ->
    ov_read_bytes segs m a n = Some (firstn n (skipn j (cbytes c))).
  Proof.
    intros m A cs k c j n a [[Hwf Hb] _] Hc Hj ->.
    destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
    rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
    rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
    apply bytes_at_app in Hb. destruct Hb as [_ Hb].
    rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
    apply bytes_at_app in Hb. destruct Hb as [Hb _].
    apply (bytes_at_ov_read segs _ _ _ j n Hb). rewrite cbytes_length by assumption. exact Hj.
  Qed.
  (* [comment removed for export] *)
  Lemma rw_cells_read_byte3 : forall m A cs k w a,
    rw_cells segs m A cs -> cell_at cs k = Some (C4 w) -> a = wa (A + Z.of_nat k + 3) ->
    ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (bv_unsigned w / 16777216)].
  Proof.
    intros m A cs k w a H Hc ->.
    change 3 with (Z.of_nat 3).
    rewrite (rw_cells_read_sub m A cs k (C4 w) 3 1 _ H Hc ltac:(cbn; lia) eq_refl).
    cbn [cbytes]. rewrite le4_unsigned. reflexivity.
  Qed.
End SubRead.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Record acimg := ACI {
  aci_c : cimg;          (* [comment removed for export] *)
  aci_got_sh : Z;        (* [comment removed for export] *)
  aci_shvar : Z;         (* [comment removed for export] *)
  aci_got_uar : Z;       (* [comment removed for export] *)
  aci_uarvar : Z         (* [comment removed for export] *)
}.
Definition aci_segs (I : acimg) : list Segment := ci_segs (aci_c I).
Definition aci_hi (I : acimg) : Z := ci_hi (aci_c I).

(* [comment removed for export] *)
Definition A0C : acimg :=
  ACI (CI a0segs 0xc4000 [] 0xc06d0 0x81c24 0xc06b8 0xbf950 0x9df04 0x9d0c8 0x9c460 0x9aa30 0x97588 0x88a10 0x89c74 0x89e30 0x884f4 0x828cc 0x82468 0x61e000)
      0xbfa58 0xc9138 0xbfab0 0xc9140.

(* [comment removed for export] *)
Definition aconsts (I : acimg) (m : word -> option byte) : Prop :=
  ro_cells (aci_segs I) m (aci_got_sh I) [C8 (Z_to_bv 64 (aci_shvar I))] /\
  ro_cells (aci_segs I) m (aci_shvar I) [C8 (Z_to_bv 64 2147450880)].
Definition aconsts_uar (I : acimg) (m : word -> option byte) : Prop :=
  ro_cells (aci_segs I) m (aci_got_uar I) [C8 (Z_to_bv 64 (aci_uarvar I))] /\
  ro_cells (aci_segs I) m (aci_uarvar I) [C4 (Z_to_bv 64 1)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cctx_sh (segs : list Segment) (cx : cctx) (W : list (Z * Z)) (m0 : word -> option byte) : Prop :=
  shzW segs W m0 (c_E cx) (c_E cx + ESTATE_SIZE) /\
  shzW segs W m0 (c_A1 cx) (c_A1 cx + ARR1_SIZE) /\
  shzW segs W m0 (c_A2 cx) (c_A2 cx + ARR2_SIZE) /\
  shzW segs W m0 (c_FT cx) (c_FT cx + 262144) /\
  shpW segs W m0 (c_FT cx) (c_FT cx + 262148).

(* [comment removed for export] *)
Lemma cctx_sh_sub : forall segs cx W W' (m0 m1 : word -> option byte),
  cctx_sh segs cx W m0 -> munch W m0 m1 -> sub_fp W' W -> cctx_sh segs cx W' m1.
Proof.
  intros segs cx W W' m0 m1 (H1 & H2 & H3 & H4 & H5) MU SF. unfold cctx_sh.
  split; [exact (shzW_sub segs W W' m0 m1 _ _ _ _ H1 MU SF (Z.le_refl _) (Z.le_refl _))|].
  split; [exact (shzW_sub segs W W' m0 m1 _ _ _ _ H2 MU SF (Z.le_refl _) (Z.le_refl _))|].
  split; [exact (shzW_sub segs W W' m0 m1 _ _ _ _ H3 MU SF (Z.le_refl _) (Z.le_refl _))|].
  split; [exact (shzW_sub segs W W' m0 m1 _ _ _ _ H4 MU SF (Z.le_refl _) (Z.le_refl _))|].
  exact (shpW_sub segs W W' m0 m1 _ _ _ _ H5 MU SF (Z.le_refl _) (Z.le_refl _)).
Qed.

(* [comment removed for export] *)
Definition cimg_sh (I : acimg) (W : list (Z * Z)) (m0 : word -> option byte) : Prop :=
  shzW (aci_segs I) W m0 (ci_crc (aci_c I)) (ci_crc (aci_c I) + 1024).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition acimg_mem (I : acimg) (m : word -> option byte) (sv : word) : Prop :=
  ro_cells (aci_segs I) m (ci_got (aci_c I)) [C8 (Z_to_bv 64 (ci_stderrp (aci_c I)))] /\
  ro_cells (aci_segs I) m (ci_got (aci_c I) + 24) [C8 (Z_to_bv 64 (ci_crc (aci_c I)))] /\
  ro_cells (aci_segs I) m (ci_stderrp (aci_c I)) [C8 sv] /\
  rw_cells (aci_segs I) m (ci_crc (aci_c I)) (CB 1024 bz_crc_table_bytes :: ci_crcx (aci_c I)).

(* [comment removed for export] *)
Lemma acimg_crc : forall I m sv, acimg_mem I m sv -> rw_cells (aci_segs I) m (ci_crc (aci_c I)) [CB 1024 bz_crc_table_bytes].
Proof.
  intros I m sv (_ & _ & _ & H). change (CB 1024 bz_crc_table_bytes :: ci_crcx (aci_c I)) with ([CB 1024 bz_crc_table_bytes] ++ ci_crcx (aci_c I)) in H.
  apply rw_cells_app_iff_c in H. exact (proj1 H).
Qed.
Lemma acimg_crc_u32arr : forall I m sv, acimg_mem I m sv -> u32arr (aci_segs I) m (ci_crc (aci_c I)) crc_words.
Proof.
  intros I m sv H. eapply cb_u32arr; [apply crc_words_bytes| reflexivity| exact (acimg_crc I m sv H)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hbAssignCodes_aspec (I : acimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Ecode Elen cb lb minLen maxLen alphaSize NC NL lo : Z) (code len : zarr) (Jc Jl : list byte),
  let segs := aci_segs I in
  let W := [(Ecode + 4 * cb, Ecode + 4 * (cb + alphaSize)); (bv_unsigned sp - 16, bv_unsigned sp)] in
  a0 = Z_to_bv 64 (Ecode + 4 * cb) -> a1 = Z_to_bv 64 (Elen + lb) ->
  a2 = Z_to_bv 64 minLen -> a3 = Z_to_bv 64 maxLen -> a4 = Z_to_bv 64 alphaSize ->
  u32arr segs m Ecode (ovw code Jc NC) -> u8arr segs m Elen (ovb len Jl NL) -> mem_inv segs m ->
  stk segs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
  0 <= cb -> cb + alphaSize <= NC -> 0 <= lb -> lb + alphaSize <= NL -> 0 <= alphaSize <= 258 ->
  1 <= minLen <= 32 -> 0 <= maxLen <= 17 -> Ecode mod 4 = 0 -> 0 < Ecode -> Ecode + 4 * NC <= CEIL -> 0 < Elen -> Elen + NL <= CEIL ->
  apart Ecode (4 * NC) Elen NL ->
  bv_unsigned sp <= Ecode \/ Ecode + 4 * NC <= bv_unsigned sp - 16 -> bv_unsigned sp <= Elen \/ Elen + NL <= bv_unsigned sp - 16 ->
  (forall i, 0 <= i < alphaSize -> zdef len (lb + i) = true /\ minLen <= zget len (lb + i) <= maxLen) ->
  (* [comment removed for export] *)
  aconsts I m -> aci_hi I <= lo -> aci_hi I <= Ecode -> aci_hi I <= Elen ->
  shzW segs W m Ecode (Ecode + 4 * NC) -> shzW segs W m Elen (Elen + NL) ->
  evt segs (hbAssignCodes_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              Ecode (hbAssignCodes code len cb lb minLen maxLen alphaSize) Jc NC lo W m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_hbAssignCodes (aci_c I))) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gtU_apost (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A2 Bud : Z) (a2 : zarr) (r : bool * Z) (lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 x12 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(Bud, Bud + 4); (bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' lo (bv_unsigned sp)
    /\ a0 = Z_to_bv 64 (Z.b2z (fst r))
    /\ u8arr segs m' A2 (zb8 a2 ARR2_SIZE) /\ rw_cells segs m' Bud [C4 (Z_to_bv 64 (snd r))].

Definition gtU_aspec (I : acimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A2 qoff n i1 i2 budget Bud lo : Z) (a2z : zarr),
  let segs := aci_segs I in
  let W := [(Bud, Bud + 4); (bv_unsigned sp - 16, bv_unsigned sp)] in
  a0 = Z_to_bv 64 i1 -> a1 = Z_to_bv 64 i2 -> a2 = Z_to_bv 64 A2 -> a3 = Z_to_bv 64 (A2 + qoff) -> a4 = Z_to_bv 64 n -> a5 = Z_to_bv 64 Bud ->
  u8arr segs m A2 (zb8 a2z ARR2_SIZE) -> rw_cells segs m Bud [C4 (Z_to_bv 64 budget)] -> mem_inv segs m ->
  zbok a2z -> 0 <= i1 <= n + 14 -> 0 <= i2 <= n + 14 -> 10000 <= n <= NBLOCKMAX + 19 -> n + 34 <= qoff <= n + 35 ->
  (A2 + qoff) mod 2 = 0 -> 0 < A2 -> A2 + ARR2_SIZE <= CEIL -> 0 < Bud -> Bud + 4 <= 18446744073709551616 -> Bud mod 4 = 0 ->
  apart A2 ARR2_SIZE Bud 4 ->
  -2147483648 <= snd (mainGtU i1 i2 a2z qoff n budget) -> budget < 2147483648 ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
  bv_unsigned sp <= A2 \/ A2 + ARR2_SIZE <= bv_unsigned sp - 16 -> bv_unsigned sp <= Bud \/ Bud + 4 <= bv_unsigned sp - 16 ->
  aconsts I m -> aci_hi I <= lo -> aci_hi I <= A2 -> aci_hi I <= Bud ->
  shzW segs W m A2 (A2 + ARR2_SIZE) -> shpW segs W m Bud (Bud + 4) ->
  evt segs (gtU_apost segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A2 Bud a2z (mainGtU i1 i2 a2z qoff n budget) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_mainGtU (aci_c I))) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition add_pair_aspec (I : acimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (lo : Z) (sv : word),
  let segs := aci_segs I in
  let W := add_pair_W cx e ++ [(bv_unsigned sp - 16, bv_unsigned sp)] in
  a0 = Z_to_bv 64 (c_E cx) ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_E cx + 128) (ovb (e_inUse e) (jseg (c_J cx) 128 256) 256) ->
  u8arr segs m (c_A2 cx) (zb8 (e_arr2 e) ARR2_SIZE) -> acimg_mem I m sv ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> cctx_img (aci_c I) cx ->
  0 <= e_state_in_ch e < 256 -> 1 <= e_state_in_len e <= 255 -> 0 <= e_blockCRC e < 4294967296 ->
  0 <= e_nblock e -> e_nblock e + 5 <= ARR2_SIZE -> zdefr (e_inUse e) 0 256 -> zbok (e_arr2 e) ->
  (* [comment removed for export] *)
  aconsts I m -> cctx_sh segs cx W m -> cimg_sh I W m ->
  evt segs (add_pair_post segs cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_add_pair (aci_c I))) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bsW8_aspec (I : acimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (v lo : Z),
  let segs := aci_segs I in
  let W := bsW8_W cx e ++ [(bv_unsigned sp - 32, bv_unsigned sp)] in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = Z_to_bv 64 v -> 0 <= v < 256 ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE) ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) -> bw_ok (e_bw e) ->
  0 <= e_nblock e -> e_nblock e + bw_numZ (e_bw e) + 4 <= ARR2_SIZE ->
  (* [comment removed for export] *)
  aconsts I m -> cctx_sh segs cx W m ->
  evt segs (bsW8_post segs cx g e v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_bsW8 (aci_c I))) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bsPutUInt32_aspecS (I : acimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (u lo : Z),
  let segs := aci_segs I in
  let W := bsPutUInt32_W cx e ++ [(bv_unsigned sp - 32, bv_unsigned sp)] in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = sx32 (Z_to_bv 64 u) -> 0 <= u < 4294967296 ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE) ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) -> bw_ok (e_bw e) ->
  0 <= e_nblock e -> e_nblock e + bw_numZ (e_bw e) + 16 <= ARR2_SIZE ->
  (* [comment removed for export] *)
  aconsts I m -> cctx_sh segs cx W m ->
  evt segs (bsPutUInt32_post segs cx g e u ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_bsPutUInt32 (aci_c I))) fc None m (seg_rom segs)).

End ACeilS1.
