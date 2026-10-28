(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzIncs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Export ACeil ACeilTac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record cimg := CI {
  ci_segs : list Segment;
  ci_crc : Z;          (* [comment removed for export] *)
  ci_crcx : list cell; (* [comment removed for export] *)
  ci_got_crc : Z;      (* [comment removed for export] *)
  ci_assert_fail : Z;  (* [comment removed for export] *)
  ci_got : Z;          (* [comment removed for export] *)
  ci_stderrp : Z;      (* [comment removed for export] *)
  (* [comment removed for export] *)
  ci_hbAssignCodes : Z; ci_hbMakeCodeLengths : Z; ci_mainGtU : Z; ci_fallbackSort : Z; ci_blockSort : Z;
  ci_compressBlock : Z; ci_bsW8 : Z; ci_bsPutUInt32 : Z; ci_add_pair : Z; ci_handle_compress : Z; ci_bzCompress : Z;
  ci_hi : Z            (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition cimg_mem (I : cimg) (m : word -> option byte) (sv : word) : Prop :=
  rw_cells (ci_segs I) m (ci_got I) [C8 (Z_to_bv 64 (ci_stderrp I))] /\
  rw_cells (ci_segs I) m (ci_got I + 24) [C8 (Z_to_bv 64 (ci_crc I))] /\
  rw_cells (ci_segs I) m (ci_stderrp I) [C8 sv] /\
  rw_cells (ci_segs I) m (ci_crc I) (CB 1024 bz_crc_table_bytes :: ci_crcx I).
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)        (* [comment removed for export] *)        (* [comment removed for export] *)
(* [comment removed for export] *)        (* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *)       (* [comment removed for export] *)    (* [comment removed for export] *)
(* [comment removed for export] *)      (* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *) (* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *)    (* [comment removed for export] *) (* [comment removed for export] *)
(* [comment removed for export] *)    (* [comment removed for export] *)    (* [comment removed for export] *)
(* [comment removed for export] *)     (* [comment removed for export] *)    (* [comment removed for export] *)
(* [comment removed for export] *)  (* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)    (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)      (* [comment removed for export] *)
(* [comment removed for export] *)     (* [comment removed for export] *)    (* [comment removed for export] *)
(* [comment removed for export] *) Definition ESTATE_SIZE : Z := 55768.
(* [comment removed for export] *)
Definition FTAB_WORDS : Z := 65537.
Definition BZFILE_SIZE : Z := 5104.  Definition BZF_STRM : Z := 5016.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record cctx := CC {
  c_E : Z;            (* [comment removed for export] *)
  c_A1 : Z; c_A2 : Z; c_FT : Z;   (* [comment removed for export] *)
  c_bz : Z;           (* [comment removed for export] *)
  c_Fb : Z;           (* [comment removed for export] *)
  c_J : list byte;    (* [comment removed for export] *)
  c_Jbz : list byte   (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record eg := EG { g_aie : bool; g_sort : bool; g_mtf : bool; g_bs : bool; g_zbits : word }.
Definition eg_init (zb : word) : eg := EG false false false false zb.

(* [comment removed for export] *)
Definition jseg_def (J : list byte) (off n : Z) : list byte := firstn (Z.to_nat n) (skipn (Z.to_nat off) J).
Definition jseg_sig : { f : list byte -> Z -> Z -> list byte | f = jseg_def }. Proof. exists jseg_def; reflexivity. Qed.
Definition jseg : list byte -> Z -> Z -> list byte := proj1_sig jseg_sig.
Lemma jseg_eq : forall J off n, jseg J off n = firstn (Z.to_nat n) (skipn (Z.to_nat off) J).
Proof. intros. unfold jseg. rewrite (proj2_sig jseg_sig). reflexivity. Qed.
Lemma jseg_length : forall J off n, 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length J) -> Z.of_nat (length (jseg J off n)) = n.
Proof. intros. rewrite jseg_eq, firstn_length, skipn_length. lia. Qed.
Lemma jseg_length_nat : forall J off n, 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length J) -> length (jseg J off n) = Z.to_nat n.
Proof. intros. rewrite jseg_eq, firstn_length, skipn_length. lia. Qed.
Definition jw4 (J : list byte) (off : Z) : word := le_bytes_to_word (jseg J off 4).
End ACeilS1.

#[global] Opaque jw4.
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section Layout.
  Variable cx : cctx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx). Notation J := (c_J cx).

  (* [comment removed for export] *)
  Definition EHEAD1 (g : eg) (e : est) : list cell :=
    [C8 (Z_to_bv 64 (c_bz cx + BZF_STRM));
     C4 (Z_to_bv 64 (e_mode e)); C4 (Z_to_bv 64 (e_state e));
     C4 (if g_aie g then Z_to_bv 64 (e_avail_in_expect e) else jw4 J 16); C4 (jw4 J 20);
     C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 FT);
     C4 (if g_sort g then Z_to_bv 64 (e_origPtr e) else jw4 J 48); C4 (jw4 J 52);
     C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 A1); C8 (g_zbits g);
     C4 (Z_to_bv 64 WORKFACTOR); C4 (Z_to_bv 64 (e_state_in_ch e)); C4 (Z_to_bv 64 (e_state_in_len e));
     C4 (jw4 J 100); C4 (jw4 J 104);
     C4 (Z_to_bv 64 (e_nblock e)); C4 (Z_to_bv 64 NBLOCKMAX); C4 (Z_to_bv 64 (bw_numZ (e_bw e)));
     C4 (Z_to_bv 64 (e_state_out_pos e));
     C4 (if g_mtf g then Z_to_bv 64 (e_nInUse e) else jw4 J 124)].
  (* [comment removed for export] *)
  Definition EHEAD2 (g : eg) (e : est) : list cell :=
    [C4 (if g_bs g then Z_to_bv 64 (bw_buff (e_bw e)) else jw4 J 640);
     C4 (if g_bs g then Z_to_bv 64 (bw_live (e_bw e)) else jw4 J 644);
     C4 (Z_to_bv 64 (e_blockCRC e)); C4 (Z_to_bv 64 (e_combinedCRC e)); C4 (Z_to_bv 64 0);
     C4 (Z_to_bv 64 (e_blockNo e)); C4 (Z_to_bv 64 BLOCKSIZE100K);
     C4 (if g_mtf g then Z_to_bv 64 (e_nMTF e) else jw4 J 668)].

  Section WithSegs.
    Variable segs : list Segment.

    (* [comment removed for export] *)
    Definition emem (g : eg) (e : est) (m : word -> option byte) : Prop :=
      rw_cells segs m E (EHEAD1 g e) /\
      u8arr segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) /\
      u8arr segs m (E + 384) (ovb (e_unseqToSeq e) (jseg J 384 256) 256) /\
      rw_cells segs m (E + 640) (EHEAD2 g e) /\
      u32arr segs m (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) /\
      u8arr segs m (E + 1704) (ovb (e_selector e) (jseg J 1704 18002) 18002) /\
      u8arr segs m (E + 19706) (ovb (e_selectorMtf e) (jseg J 19706 18002) 18002) /\
      u8arr segs m (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) /\
      u32arr segs m (E + 39256) (ovw (e_code e) (jseg J 39256 6192) 1548) /\
      u32arr segs m (E + 45448) (ovw (e_rfreq e) (jseg J 45448 6192) 1548) /\
      u32arr segs m (E + 51640) (ovw (e_len_pack e) (jseg J 51640 4128) 1032).

    Lemma emem_intro : forall g e m,
      rw_cells segs m E (EHEAD1 g e) ->
      u8arr segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
      u8arr segs m (E + 384) (ovb (e_unseqToSeq e) (jseg J 384 256) 256) ->
      rw_cells segs m (E + 640) (EHEAD2 g e) ->
      u32arr segs m (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) ->
      u8arr segs m (E + 1704) (ovb (e_selector e) (jseg J 1704 18002) 18002) ->
      u8arr segs m (E + 19706) (ovb (e_selectorMtf e) (jseg J 19706 18002) 18002) ->
      u8arr segs m (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) ->
      u32arr segs m (E + 39256) (ovw (e_code e) (jseg J 39256 6192) 1548) ->
      u32arr segs m (E + 45448) (ovw (e_rfreq e) (jseg J 45448 6192) 1548) ->
      u32arr segs m (E + 51640) (ovw (e_len_pack e) (jseg J 51640 4128) 1032) ->
      emem g e m.
    Proof. intros. unfold emem. repeat (split; [assumption|]). assumption. Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition amem (e : est) (m : word -> option byte) : Prop :=
      u8arr segs m A1 (zb8 (e_arr1 e) ARR1_SIZE) /\ u8arr segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) /\ u32arr segs m FT (zw32 (e_ftab e) FTAB_WORDS).
    Lemma amem_intro : forall e m,
      u8arr segs m A1 (zb8 (e_arr1 e) ARR1_SIZE) -> u8arr segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) -> u32arr segs m FT (zw32 (e_ftab e) FTAB_WORDS) ->
      amem e m.
    Proof. intros. unfold amem. repeat (split; [assumption|]). assumption. Qed.
    Lemma amem_introF : forall m mo st aie a1 a2 ft op ch il nb sop niu inUse unseq b bcrc ccrc bno nmtf mtff sel selm len code rfreq lenp,
      u8arr segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr segs m FT (zw32 ft FTAB_WORDS) ->
      amem (EST mo st aie a1 a2 ft op ch il nb sop niu inUse unseq b bcrc ccrc bno nmtf mtff sel selm len code rfreq lenp) m.
    Proof. intros. unfold amem. cbn [e_arr1 e_arr2 e_ftab]. repeat (split; [assumption|]). assumption. Qed.
  End WithSegs.
End Layout.
End ACeilS2.


(* [comment removed for export] *)
Ltac open_emem EM :=
  let EH1 := fresh "EH1" in let INU := fresh "INU" in let UNS := fresh "UNS" in let EH2 := fresh "EH2" in
  let MTF := fresh "MTF" in let SEL := fresh "SEL" in let SLM := fresh "SLM" in let LEN := fresh "LEN" in
  let COD := fresh "COD" in let RFQ := fresh "RFQ" in let LNP := fresh "LNP" in
  cps_destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SLM & LEN & COD & RFQ & LNP);
  unfold EHEAD1, EHEAD2 in EH1, EH2.
Ltac open_amem AM :=
  let AR1 := fresh "AR1" in let AR2 := fresh "AR2" in let FTB := fresh "FTB" in
  cps_destruct AM as (AR1 & AR2 & FTB).
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACeilS3. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CEIL : Z := alloc_ceiling.
(* [comment removed for export] *)
Definition IMG_HI3 : Z := 0x47000.   (* [comment removed for export] *)

Definition cctx_ok (cx : cctx) : Prop :=
  let E := c_E cx in let A1 := c_A1 cx in let A2 := c_A2 cx in let FT := c_FT cx in let bz := c_bz cx in let Fb := c_Fb cx in
  (* [comment removed for export] *)
  0 < E /\ E + ESTATE_SIZE <= CEIL /\ 0 < A1 /\ A1 + ARR1_SIZE <= CEIL /\
  0 < A2 /\ A2 + ARR2_SIZE <= CEIL /\ 0 < FT /\ FT + 4 * FTAB_WORDS <= CEIL /\
  0 < bz /\ bz + BZFILE_SIZE <= CEIL /\ 0 < Fb /\ Fb + 1264 <= CEIL /\
  (* [comment removed for export] *)
  E mod 16 = 0 /\ A1 mod 16 = 0 /\ A2 mod 16 = 0 /\ FT mod 16 = 0 /\ bz mod 16 = 0 /\ Fb mod 16 = 0 /\
  (* [comment removed for export] *)
  Z.of_nat (length (c_J cx)) = ESTATE_SIZE /\ Z.of_nat (length (c_Jbz cx)) = BZFILE_SIZE.

(* [comment removed for export] *)
Definition IMG_LO3 : Z := 0x10000.
(* [comment removed for export] *)
Definition img_apart (hi a n : Z) : Prop := a + n <= IMG_LO3 \/ hi <= a.
Definition cctx_img (I : cimg) (cx : cctx) : Prop :=
  img_apart (ci_hi I) (c_E cx) ESTATE_SIZE /\ img_apart (ci_hi I) (c_A1 cx) ARR1_SIZE /\ img_apart (ci_hi I) (c_A2 cx) ARR2_SIZE /\
  img_apart (ci_hi I) (c_FT cx) (4 * FTAB_WORDS) /\ img_apart (ci_hi I) (c_bz cx) BZFILE_SIZE /\ img_apart (ci_hi I) (c_Fb cx) 1264.

(* [comment removed for export] *)
Definition apart (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.
Definition cctx_sep (cx : cctx) : Prop :=
  let E := c_E cx in let A1 := c_A1 cx in let A2 := c_A2 cx in let FT := c_FT cx in let bz := c_bz cx in let Fb := c_Fb cx in
  apart E ESTATE_SIZE A1 ARR1_SIZE /\ apart E ESTATE_SIZE A2 ARR2_SIZE /\ apart E ESTATE_SIZE FT (4 * FTAB_WORDS) /\
  apart E ESTATE_SIZE bz BZFILE_SIZE /\ apart E ESTATE_SIZE Fb 1264 /\
  apart A1 ARR1_SIZE A2 ARR2_SIZE /\ apart A1 ARR1_SIZE FT (4 * FTAB_WORDS) /\ apart A1 ARR1_SIZE bz BZFILE_SIZE /\ apart A1 ARR1_SIZE Fb 1264 /\
  apart A2 ARR2_SIZE FT (4 * FTAB_WORDS) /\ apart A2 ARR2_SIZE bz BZFILE_SIZE /\ apart A2 ARR2_SIZE Fb 1264 /\
  apart FT (4 * FTAB_WORDS) bz BZFILE_SIZE /\ apart FT (4 * FTAB_WORDS) Fb 1264 /\
  apart bz BZFILE_SIZE Fb 1264.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition est_ok (e : est) : Prop :=
  zbok (e_arr1 e) /\ zbok (e_arr2 e) /\
  (forall i, 0 <= zget (e_ftab e) i < 4294967296) /\
  0 <= e_nblock e <= NBLOCKMAX + 19 /\
  0 <= bw_numZ (e_bw e) /\ 0 <= e_state_out_pos e <= bw_numZ (e_bw e) /\
  (e_mode e = BZ_M_IDLE \/ e_mode e = BZ_M_RUNNING \/ e_mode e = BZ_M_FLUSHING \/ e_mode e = BZ_M_FINISHING) /\
  (e_state e = BZ_S_OUTPUT \/ e_state e = BZ_S_INPUT) /\
  0 <= e_state_in_ch e <= 256 /\ 0 <= e_state_in_len e <= 255 /\
  0 <= e_blockCRC e < 4294967296 /\ 0 <= e_combinedCRC e < 4294967296 /\
  1 <= e_blockNo e < 2147483647.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hbAssignCodes_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (Ecode : Z) (code' : zarr) (Jc : list byte) (NC lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ u32arr segs m' Ecode (ovw code' Jc NC).

Definition hbAssignCodes_spec (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Ecode Elen cb lb minLen maxLen alphaSize NC NL lo : Z) (code len : zarr) (Jc Jl : list byte),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (Ecode + 4 * cb) -> a1 = Z_to_bv 64 (Elen + lb) ->
  a2 = Z_to_bv 64 minLen -> a3 = Z_to_bv 64 maxLen -> a4 = Z_to_bv 64 alphaSize ->
  u32arr segs m Ecode (ovw code Jc NC) -> u8arr segs m Elen (ovb len Jl NL) -> mem_inv segs m ->
  stk segs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
  0 <= cb -> cb + alphaSize <= NC -> 0 <= lb -> lb + alphaSize <= NL -> 0 <= alphaSize <= 258 ->
  1 <= minLen <= 32 -> 0 <= maxLen <= 17 -> Ecode mod 4 = 0 -> 0 < Ecode -> Ecode + 4 * NC <= CEIL -> 0 < Elen -> Elen + NL <= CEIL ->
  apart Ecode (4 * NC) Elen NL ->
  bv_unsigned sp <= Ecode \/ Ecode + 4 * NC <= bv_unsigned sp - 16 -> bv_unsigned sp <= Elen \/ Elen + NL <= bv_unsigned sp - 16 ->
  (forall i, 0 <= i < alphaSize -> zdef len (lb + i) = true /\ minLen <= zget len (lb + i) <= maxLen) ->
  evt segs (hbAssignCodes_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              Ecode (hbAssignCodes code len cb lb minLen maxLen alphaSize) Jc NC lo
              [(Ecode + 4 * cb, Ecode + 4 * (cb + alphaSize)); (bv_unsigned sp - 16, bv_unsigned sp)] m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_hbAssignCodes I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
Fixpoint VB (j : nat) : Z := match j with O => 0 | S j' => 2 * (VB j' + 258) end.
Lemma VB_bound : forall j, (j <= 17)%nat -> 0 <= VB j <= 67632636.
Proof.
  intros j Hj. assert (G : forall k, (0 <= VB k /\ VB k = 516 * (2 ^ Z.of_nat k - 1))).
  { induction k as [|k IH]; [cbn; lia|]. cbn [VB]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. }
  destruct (G j) as [G1 G2]. rewrite G2.
  pose proof (Z.pow_le_mono_r 2 (Z.of_nat j) 17 ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j) ltac:(lia) ltac:(lia)).
  change (2^17) with 131072 in *. lia.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zbl (a : zarr) (nblock : Z) (b : bw) : zarr := zarr_of_list_at a nblock (bw_bytes b).

Lemma zarr_of_list_at_snoc : forall l a lo x,
  zarr_of_list_at a lo (l ++ [x]) = zset (zarr_of_list_at a lo l) (lo + Z.of_nat (length l)) x.
Proof.
  induction l as [|y l IH]; intros a lo x; cbn [zarr_of_list_at app length].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. f_equal. lia.
Qed.
Lemma zarr_to_list_ext : forall a a' lo n, (forall i, lo <= i < lo + Z.of_nat n -> zget a i = zget a' i) ->
  zarr_to_list a lo n = zarr_to_list a' lo n.
Proof.
  intros a a' lo n. revert lo. induction n as [|n IH]; intros lo H; cbn; [reflexivity|].
  rewrite H by lia. f_equal. apply IH. intros i Hi. apply H. lia.
Qed.
Lemma zarr_to_list_S_snoc : forall n a lo, zarr_to_list a lo (S n) = zarr_to_list a lo n ++ [zget a (lo + Z.of_nat n)].
Proof.
  induction n as [|n IH]; intros a lo.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - change (zarr_to_list a lo (S (S n))) with (zget a lo :: zarr_to_list a (lo + 1) (S n)).
    rewrite IH. change (zarr_to_list a lo (S n)) with (zget a lo :: zarr_to_list a (lo + 1) n).
    cbn [app]. f_equal. f_equal. f_equal. f_equal. lia.
Qed.
Lemma bw_bytes_emit : forall b, 0 <= bw_numZ b -> bw_bytes (bw_emit b) = bw_bytes b ++ [Z.shiftr (bw_buff b) 24].
Proof.
  intros b Hn. unfold bw_bytes, bw_emit. cbn [bw_zb bw_numZ bw_buff].
  replace (Z.to_nat (bw_numZ b + 1)) with (S (Z.to_nat (bw_numZ b))) by lia.
  rewrite zarr_to_list_S_snoc. replace (0 + Z.of_nat (Z.to_nat (bw_numZ b))) with (bw_numZ b) by lia.
  rewrite zget_zset_same. f_equal. apply zarr_to_list_ext. intros i Hi. rewrite zget_zset_other by lia. reflexivity.
Qed.
Lemma bw_bytes_length : forall b, length (bw_bytes b) = Z.to_nat (bw_numZ b).
Proof. intros. unfold bw_bytes. apply zarr_to_list_length. Qed.
Lemma zbl_emit : forall a n b, 0 <= bw_numZ b -> 0 <= bw_buff b < 4294967296 ->
  zbl a n (bw_emit b) = wr8 (zbl a n b) (n + bw_numZ b) (Z.shiftr (bw_buff b) 24).
Proof.
  intros a n b Hn Hb. unfold zbl. rewrite bw_bytes_emit by exact Hn. rewrite zarr_of_list_at_snoc, bw_bytes_length.
  unfold wr8. rewrite Z.mod_small by (apply bw_emit_byte; exact Hb). f_equal. lia.
Qed.
(* [comment removed for export] *)
Lemma zbl_same_bytes : forall a n b b', bw_numZ b' = bw_numZ b -> bw_zb b' = bw_zb b -> zbl a n b' = zbl a n b.
Proof. intros a n b b' H1 H2. unfold zbl, bw_bytes. rewrite H1, H2. reflexivity. Qed.
Lemma zbl_numZ0 : forall a n b, bw_numZ b = 0 -> zbl a n b = a.
Proof. intros a n b H. unfold zbl, bw_bytes. rewrite H. reflexivity. Qed.
Lemma zbok_zbl : forall a n b, zbok a -> 0 <= bw_numZ b -> (forall i, 0 <= i < bw_numZ b -> 0 <= zget (bw_zb b) i < 256) -> zbok (zbl a n b).
Proof.
  intros a n b Ha Hb Hz. unfold zbl. apply zbok_of_list_at; [exact Ha|].
  unfold bw_bytes. remember (Z.to_nat (bw_numZ b)) as c.
  assert (G : forall lo k, 0 <= lo -> lo + Z.of_nat k <= bw_numZ b -> Forall (fun v => 0 <= v < 256) (zarr_to_list (bw_zb b) lo k)).
  { intros lo k. revert lo. induction k as [|k IH]; intros lo H1 H2; cbn; constructor.
    - apply Hz. lia. - apply IH; lia. }
  apply G; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bsW8_post (segs : list Segment) (cx : cctx) (g : eg) (e : est) (v : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ let e' := est_set_bw e (bsW (e_bw e) 8 v) in
       rw_cells segs m' (c_E cx) (EHEAD1 cx g e') /\ rw_cells segs m' (c_E cx + 640) (EHEAD2 cx g e')
       /\ u8arr segs m' (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (bsW (e_bw e) 8 v)) ARR2_SIZE).

Definition bsW8_W (cx : cctx) (e : est) : list (Z * Z) :=
  [(c_E cx + 116, c_E cx + 120); (c_E cx + 640, c_E cx + 648);
   (c_A2 cx + e_nblock e + bw_numZ (e_bw e), c_A2 cx + e_nblock e + bw_numZ (e_bw e) + 4)].

Definition bsW8_spec (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (v lo : Z),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = Z_to_bv 64 v -> 0 <= v < 256 ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE) ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) -> bw_ok (e_bw e) ->
  0 <= e_nblock e -> e_nblock e + bw_numZ (e_bw e) + 4 <= ARR2_SIZE ->
  evt segs (bsW8_post segs cx g e v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (bsW8_W cx e) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_bsW8 I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FS_FRAME : Z := 3072.   (* [comment removed for export] *)

Definition fallbackSort_post (segs : list Segment) (cx : cctx) (e : est) (nblock : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ let r := fallbackSort (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew znew znew nblock in
       u8arr segs m' (c_A1 cx) (zb8 (fr_fm r) ARR1_SIZE) /\ u8arr segs m' (c_A2 cx) (zb8 (fr_ec r) ARR2_SIZE)
       /\ u32arr segs m' (c_FT cx) (zw32 (fr_bh r) FTAB_WORDS).

Definition fallbackSort_W (cx : cctx) (usp : Z) : list (Z * Z) :=
  [(c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS); (usp - FS_FRAME, usp)].

(* [comment removed for export] *)
Definition fallbackSort_spec (FSFACTS : zarr -> zarr -> zarr -> Z -> Prop) (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (e : est) (nblock lo : Z) (sv : word),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_A1 cx) -> a1 = Z_to_bv 64 (c_A2 cx) -> a2 = Z_to_bv 64 (c_FT cx) -> a3 = Z_to_bv 64 nblock -> a4 = Z_to_bv 64 0 ->
  u8arr segs m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) -> u8arr segs m (c_A2 cx) (zb8 (e_arr2 e) ARR2_SIZE) ->
  u32arr segs m (c_FT cx) (zw32 (e_ftab e) FTAB_WORDS) -> cimg_mem I m sv ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + FS_FRAME <= bv_unsigned sp -> CEIL <= lo -> bv_unsigned sp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx ->
  zbok (e_arr1 e) -> zbok (e_arr2 e) -> (forall i, 0 <= zget (e_ftab e) i < 4294967296) ->
  1 <= nblock <= NBLOCKMAX + 19 ->
  FSFACTS (e_arr1 e) (e_arr2 e) (e_ftab e) nblock ->
  evt segs (fallbackSort_post segs cx e nblock ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (fallbackSort_W cx (bv_unsigned sp)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_fallbackSort I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bsPutUInt32_post (segs : list Segment) (cx : cctx) (g : eg) (e : est) (u : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ let e' := est_set_bw e (bsPutUInt32 (e_bw e) u) in
       rw_cells segs m' (c_E cx) (EHEAD1 cx g e') /\ rw_cells segs m' (c_E cx + 640) (EHEAD2 cx g e')
       /\ u8arr segs m' (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (bsPutUInt32 (e_bw e) u)) ARR2_SIZE).

Definition bsPutUInt32_W (cx : cctx) (e : est) : list (Z * Z) :=
  [(c_E cx + 116, c_E cx + 120); (c_E cx + 640, c_E cx + 648);
   (c_A2 cx + e_nblock e + bw_numZ (e_bw e), c_A2 cx + e_nblock e + bw_numZ (e_bw e) + 16)].

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bs_needw_credit : forall f b, 8 * bw_numZ (bs_needw f b) + bw_live (bs_needw f b) = 8 * bw_numZ b + bw_live b.
Proof.
  induction f as [|f IH]; intros b; [reflexivity|]. cbn [bs_needw]. destruct (8 <=? bw_live b); [|reflexivity].
  rewrite IH. unfold bw_emit. cbn [bw_numZ bw_live]. lia.
Qed.
Lemma bsW_credit : forall b n v, 8 * bw_numZ (bsW b n v) + bw_live (bsW b n v) = 8 * bw_numZ b + bw_live b + n.
Proof. intros. unfold bsW. cbn [bw_numZ bw_live]. pose proof (bs_needw_credit BS_FUEL b). lia. Qed.
Lemma bsW_bytes : forall b n v, bw_numZ (bsW b n v) = bw_numZ (bs_needw BS_FUEL b) /\ bw_zb (bsW b n v) = bw_zb (bs_needw BS_FUEL b).
Proof. intros. split; reflexivity. Qed.
Lemma bsW8_ok : forall b v, bw_ok b -> 0 <= v -> bw_ok (bsW b 8 v) /\ bw_numZ b <= bw_numZ (bsW b 8 v) /\ 8 <= bw_live (bsW b 8 v) <= 15.
Proof.
  intros b v OK Hv. cps_destruct (bsW_facts b 8 v OK ltac:(lia) Hv) as (_ & OK' & L & N). split; [exact OK'|]. split; [exact N|].
  rewrite L. pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HM_FRAME : Z := 5328.   (* [comment removed for export] *)
Definition hbMakeCodeLengths_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (Elen : Z) (len' : zarr) (Jl : list byte) (NL lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ u8arr segs m' Elen (ovb len' Jl NL).
Definition hbMakeCodeLengths_spec (HMFACTS : zarr -> zarr -> Z -> Z -> Z -> Prop) (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Elen Efreq lb fb alphaSize NL NF lo : Z) (len freq : zarr) (Jl Jf : list byte) (sv : word),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (Elen + lb) -> a1 = Z_to_bv 64 (Efreq + 4 * fb) -> a2 = Z_to_bv 64 alphaSize -> a3 = Z_to_bv 64 17 ->
  u8arr segs m Elen (ovb len Jl NL) -> u32arr segs m Efreq (ovw freq Jf NF) -> cimg_mem I m sv -> mem_inv segs m ->
  stk segs m lo (bv_unsigned sp) -> lo + HM_FRAME <= bv_unsigned sp -> CEIL <= lo -> bv_unsigned sp mod 16 = 0 ->
  0 <= lb -> lb + alphaSize <= NL -> 0 <= fb -> fb + alphaSize <= NF -> 3 <= alphaSize <= 258 ->
  0 < Elen -> Elen + NL <= CEIL -> 0 < Efreq -> Efreq + 4 * NF <= CEIL -> Efreq mod 4 = 0 -> apart Elen NL Efreq (4 * NF) ->
  img_apart (ci_hi I) Elen NL -> img_apart (ci_hi I) Efreq (4 * NF) ->
  (forall v, 0 <= v < alphaSize -> zdef freq (fb + v) = true /\ 0 <= zget freq (fb + v) < 8388608) ->
  HMFACTS len freq lb fb alphaSize ->
  evt segs (hbMakeCodeLengths_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              Elen (hs_len (hbMakeCodeLengths len freq znew znew znew lb fb alphaSize 17)) Jl NL lo
              [(Elen + lb, Elen + lb + alphaSize); (bv_unsigned sp - HM_FRAME, bv_unsigned sp)] m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_hbMakeCodeLengths I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BS_STACK : Z := 8192.   (* [comment removed for export] *)
Definition blockSort_W (cx : cctx) (usp : Z) : list (Z * Z) :=
  [(c_E cx + 48, c_E cx + 52); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS);
   (usp - BS_STACK, usp)].
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CB_STACK : Z := 16384.
Definition compressBlock_W (cx : cctx) (usp : Z) : list (Z * Z) :=
  [(c_E cx, c_E cx + ESTATE_SIZE); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS);
   (usp - CB_STACK, usp)].
Definition eg_after_cb (cx : cctx) (g : eg) (e : est) : eg :=
  let nz := (0 <? e_nblock e) in
  EG (g_aie g) (g_sort g || nz) (g_mtf g || nz) true (Z_to_bv 64 (c_A2 cx + e_nblock e)).
Definition compressBlock_post (segs : list Segment) (I : cimg) (cx : cctx) (g : eg) (e : est) (is_last : bool) (sv : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ let e' := fst (compressBlock e is_last znew) in
       emem cx segs (eg_after_cb cx g e) e' m' /\ amem cx segs e' m' /\ cimg_mem I m' sv.
(* [comment removed for export] *)
Definition cb_pre (g : eg) (e : est) : Prop :=
  est_ok e /\ 0 <= e_nblock e <= NBLOCKMAX + 9 /\ zdefr (e_inUse e) 0 256 /\
  (forall j, 0 <= j < e_nblock e -> zget (e_inUse e) (rd8 (e_arr2 e) j) = 1) /\
  1 <= e_blockNo e /\ (e_blockNo e = 1 -> bw_numZ (e_bw e) = 0) /\
  (e_blockNo e = 1 \/ (g_bs g = true /\ bw_ok (e_bw e) /\ bw_numZ (e_bw e) = 0)).
Definition compressBlock_spec (CBFACTS : est -> Prop) (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (is_last : bool) (lo : Z) (sv : word),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_E cx) -> a1 = Z_to_bv 64 (if is_last then 1 else 0) ->
  emem cx segs g e m -> amem cx segs e m -> cimg_mem I m sv -> mem_inv segs m ->
  stk segs m lo (bv_unsigned sp) -> lo + CB_STACK <= bv_unsigned sp -> CEIL <= lo -> bv_unsigned sp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx -> cb_pre g e -> CBFACTS e ->
  evt segs (compressBlock_post segs I cx g e is_last sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (compressBlock_W cx (bv_unsigned sp)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_compressBlock I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wr_at_app_c : forall segs m A n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m A (n1 + n2) <-> wr_at segs m A n1 /\ wr_at segs m (A + n1) n2.
Proof.
  intros segs m A n1 n2 H1 H2. unfold wr_at. split.
  - cps_intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (A + n1 + i)%Z with (A + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & Hx) & (Ha2 & Hb2 & Hy)). repeat split; try lia.
    intros i Hi. destruct (Z_lt_le_dec i n1).
    + apply Hx. lia.
    + replace (A + i)%Z with (A + n1 + (i - n1))%Z by lia. apply Hy. lia.
Qed.
Lemma rw_cells_app_iff_c : forall segs m A pre post,
  rw_cells segs m A (pre ++ post) <-> rw_cells segs m A pre /\ rw_cells segs m (A + Z.of_nat (cells_size pre))%Z post.
Proof.
  intros segs m A pre post. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    rewrite (cells_bytes_length pre W1) in B2.
    rewrite Nat2Z.inj_add in WR. apply wr_at_app_c in WR; [|lia|lia]. destruct WR as [R1 R2].
    split; [ split; [ split; [exact W1 | exact B1] | exact R1 ] | split; [ split; [exact W2 | exact B2] | exact R2 ] ].
  - intros [[[W1 B1] R1] [[W2 B2] R2]].
    rewrite (cells_bytes_length pre W1). rewrite Nat2Z.inj_add.
    split; [ split; [ split; [exact W1 | exact W2] | split; [exact B1 | exact B2] ] |].
    apply wr_at_app_c; [lia|lia|]. split; [exact R1 | exact R2].
Qed.
(* [comment removed for export] *)
Lemma cimg_crc : forall I m sv, cimg_mem I m sv -> rw_cells (ci_segs I) m (ci_crc I) [CB 1024 bz_crc_table_bytes].
Proof.
  (intros I m sv; cps_intros (_ & _ & _ & H)). change (CB 1024 bz_crc_table_bytes :: ci_crcx I) with ([CB 1024 bz_crc_table_bytes] ++ ci_crcx I) in H.
  apply rw_cells_app_iff_c in H. exact (proj1 H).
Qed.
Lemma cimg_crc_u32arr : forall I m sv, cimg_mem I m sv -> u32arr (ci_segs I) m (ci_crc I) crc_words.
Proof.
  intros I m sv H. eapply cb_u32arr; [apply crc_words_bytes| reflexivity| exact (cimg_crc I m sv H)].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma crc_words_model : map bv_unsigned crc_words = crc32_table.
Proof. vm_compute. reflexivity. Qed.
Lemma crc32_table_length : length crc32_table = 256%nat.
Proof. reflexivity. Qed.
Lemma wnth_crc_words : forall i, 0 <= i < 256 -> wnth crc_words i = Z_to_bv 64 (crc32_tbl i).
Proof.
  intros i Hi. unfold crc32_tbl. rewrite <- crc_words_model. unfold wnth.
  rewrite <- (Z_to_bv_bv_unsigned (nth (Z.to_nat i) crc_words (Z_to_bv 64 0))). f_equal.
  change 0 with (bv_unsigned (Z_to_bv 64 0)) at 2. rewrite map_nth. reflexivity.
Qed.
Lemma crc32_tbl_range : forall i, 0 <= i < 256 -> 0 <= crc32_tbl i < 4294967296.
Proof.
  intros i Hi.
  assert (FA : forallb (fun z => (0 <=? z) && (z <? 4294967296)) crc32_table = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in FA. unfold crc32_tbl.
  assert (IN : In (nth (Z.to_nat i) crc32_table 0) crc32_table) by (apply nth_In; rewrite crc32_table_length; lia).
  specialize (FA _ IN). apply andb_prop in FA. destruct FA as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition add_pair_W (cx : cctx) (e : est) : list (Z * Z) :=
  [(c_E cx + 108, c_E cx + 112); (c_E cx + 648, c_E cx + 652); (c_E cx + 128, c_E cx + 384);
   (c_A2 cx + e_nblock e, c_A2 cx + e_nblock e + 5)].
Definition add_pair_post (segs : list Segment) (cx : cctx) (g : eg) (e : est)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ let e' := est_set_rl e (add_pair_to_block (est_rl e)) in
       rw_cells segs m' (c_E cx) (EHEAD1 cx g e') /\ rw_cells segs m' (c_E cx + 640) (EHEAD2 cx g e')
       /\ u8arr segs m' (c_E cx + 128) (ovb (e_inUse e') (jseg (c_J cx) 128 256) 256)
       /\ u8arr segs m' (c_A2 cx) (zb8 (e_arr2 e') ARR2_SIZE).
Definition add_pair_spec (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (lo : Z) (sv : word),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_E cx) ->
  rw_cells segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells segs m (c_E cx + 640) (EHEAD2 cx g e) ->
  u8arr segs m (c_E cx + 128) (ovb (e_inUse e) (jseg (c_J cx) 128 256) 256) ->
  u8arr segs m (c_A2 cx) (zb8 (e_arr2 e) ARR2_SIZE) -> cimg_mem I m sv ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> CEIL <= lo ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx ->
  0 <= e_state_in_ch e < 256 -> 1 <= e_state_in_len e <= 255 -> 0 <= e_blockCRC e < 4294967296 ->
  0 <= e_nblock e -> e_nblock e + 5 <= ARR2_SIZE -> zdefr (e_inUse e) 0 256 -> zbok (e_arr2 e) ->
  evt segs (add_pair_post segs cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (add_pair_W cx e) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_add_pair I)) fc None m (seg_rom segs)).

End ACeilS3.
(* [comment removed for export] *)
