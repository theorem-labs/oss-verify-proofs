(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts DecCut AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzDState BzDOut BzDOK DecCutF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export S0F_bzd_out.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Definition bzd_img_apart (ihi a n : Z) : Prop := (a + n <= 0x10000 \/ ihi <= a)%Z.

Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bzd_slots (S SHS : Z) (w0 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 : word) : list cell :=
  [C8 w0; C8 (Z_to_bv 64 4); C8 (Z_to_bv 64 4); C8 (Z_to_bv 64 3); C8 w32;
   C8 (Z_to_bv 64 (S + 3188)); C8 (Z_to_bv 64 (S + 52)); C8 (Z_to_bv 64 (SHS + 2)); C8 (Z_to_bv 64 (SHS + 5));
   C8 (Z_to_bv 64 (S + 20)); C8 (Z_to_bv 64 (S + 44)); C8 (Z_to_bv 64 (S + 3176)); C8 (Z_to_bv 64 (S + 28));
   C8 w104; C8 w112; C8 w120;
   C8 (Z_to_bv 64 (S + 3168)); C8 (Z_to_bv 64 (S + 3160)); C8 (Z_to_bv 64 (S + 3184)); C8 (Z_to_bv 64 (S + 12));
   C8 (Z_to_bv 64 SHS); C8 (Z_to_bv 64 100000); C8 (Z_to_bv 64 (SHS + 398));
   C8 w184; C8 w192; C8 w200; C8 w208;
   C8 (Z_to_bv 64 (SHS + 1)); C8 (Z_to_bv 64 (S + 8)); C8 (Z_to_bv 64 (S + 40));
   C8 w240; C8 w248;
   C8 (Z_to_bv 64 (S + 64080)); C8 (Z_to_bv 64 (S + 64)); C8 (Z_to_bv 64 (S + 24)); C8 (Z_to_bv 64 (S + 60)); C8 (Z_to_bv 64 (S + 1092))].

Section Ctx.
  Variable I : dimg.
  Let segs := di_segs I.
  Variable c : foctx.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)). Notation L16 := (b_ll16 (o_cx c)). Notation L4 := (b_ll4 (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation uspi := (bv_unsigned (o_SP c)).

  (* [comment removed for export] *)
  Definition foctx_okA (ihi : Z) : Prop :=
    (0 < S /\ S + 64144 <= alloc_ceiling) /\ (0 < STRM /\ STRM + 80 <= alloc_ceiling) /\
    (0 < DST /\ DST + dlen <= alloc_ceiling) /\ (0 <= dlen < 2^27) /\
    (alloc_ceiling <= uspi /\ uspi + 400 < 2^64) /\
    (S mod 16 = 0 /\ STRM mod 8 = 0) /\
    disj S 64144 STRM 80 /\ disj S 64144 DST dlen /\ disj STRM 80 DST dlen /\
    bzd_img_apart ihi S 64144 /\ bzd_img_apart ihi STRM 80 /\ bzd_img_apart ihi DST dlen /\ (65536 < ihi <= 0x7fff7000) /\
    jk_wf J /\ oent c.
  (* [comment removed for export] *)
  Definition foctx_okFA (ihi : Z) : Prop :=
    b_small cx = 0 /\ (0 < TT /\ TT + 400000 * n <= alloc_ceiling) /\
    disj S 64144 TT (400000 * n) /\ disj STRM 80 TT (400000 * n) /\ disj DST dlen TT (400000 * n) /\ bzd_img_apart ihi TT (400000 * n).
  (* [comment removed for export] *)
  Definition foctx_okSA (ihi : Z) : Prop :=
    b_small cx = 1 /\ (0 < L16 /\ L16 + 200000 * n <= alloc_ceiling) /\ (0 < L4 /\ L4 + 50000 * n <= alloc_ceiling) /\
    disj S 64144 L16 (200000 * n) /\ disj STRM 80 L16 (200000 * n) /\ disj DST dlen L16 (200000 * n) /\
    disj S 64144 L4 (50000 * n) /\ disj STRM 80 L4 (50000 * n) /\ disj DST dlen L4 (50000 * n) /\
    disj L16 (200000 * n) L4 (50000 * n) /\ bzd_img_apart ihi L16 (200000 * n) /\ bzd_img_apart ihi L4 (50000 * n).

  (* [comment removed for export] *)
  Definition FWBA : list ivl := FWB c ++ [(uspi, uspi + 296)].

  (* [comment removed for export] *)
  Definition FGOTA (m : word -> option byte) : Prop :=
    ro_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 (o_g1 c); C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))].
  Definition FROfA (m : word -> option byte) : Prop :=
    rw_cells segs m (S + 64036) (SAVE_CELLS (j_s1 J) snb (j_s2 J)) /\
    u32arr segs m TT (zw32 (d_tt d0) (100000 * n)) /\ u32arr segs m (di_crc I) crc_words /\ u32arr segs m (di_rnums I) rnums_words /\
    FGOTA m /\ mem_inv segs m.
  Definition FROsA (m : word -> option byte) : Prop :=
    rw_cells segs m (S + 64036) (SAVE_CELLS (j_s1 J) snb (j_s2 J)) /\
    u8arr segs m L16 (zh16 (d_ll16 d0) (200000 * n)) /\ u8arr segs m L4 (zb8 (d_ll4 d0) (50000 * n)) /\
    u32arr segs m (S + 1096) (zw32 (d_cftab d0) 257) /\
    u32arr segs m (di_crc I) crc_words /\ u32arr segs m (di_rnums I) rnums_words /\ FGOTA m /\ mem_inv segs m.

  (* [comment removed for export] *)
  Definition DSgA (m : word -> option byte) (Jx : jk) (d : dst) (s : dstrm) : Prop :=
    rw_cells segs m S (HEAD_CELLS (hd_of cx Jx d)) /\ rw_cells segs m (S + 1092) [C4 (Z_to_bv 64 (d_nused d))] /\
    rw_cells segs m (S + 3152) (MID_CELLS (mid_of cx d)) /\ rw_cells segs m STRM (STRM_CELLS (bs_of cx Jx s)).
  (* [comment removed for export] *)
  Definition DESTgA (m : word -> option byte) (s : dstrm) (dbytes rest : list byte) : Prop :=
    u8arr segs m DST dbytes /\ Z.of_nat (length dbytes) = dlen /\
    dbytes = map (Z_to_bv 8) (rev (s_out s)) ++ rest /\ Z.of_nat (length (s_out s)) = (dlen - s_avail_out s)%Z.

  (* [comment removed for export] *)
  Definition obz_sh (W : list ivl) (m0 : word -> option byte) : Prop :=
    shzW segs W m0 S (S + 64144) /\ shzW segs W m0 STRM (STRM + 80) /\ shpW segs W m0 DST (DST + dlen) /\
    shzW segs W m0 (di_crc I) (di_crc I + 1024) /\ shzW segs W m0 (di_rnums I) (di_rnums I + 2048) /\
    (b_small cx = 0 -> shzW segs W m0 TT (TT + 400000 * n)) /\
    (b_small cx = 1 -> shzW segs W m0 L16 (L16 + 200000 * n) /\ shzW segs W m0 L4 (L4 + 50000 * n)).
End Ctx.
End ACeilS1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import DecCutA A0F_decV.

(* [comment removed for export] *)
Notation A0RR c SHS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 t3 t4 t5 t6 :=
  (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (b_s (o_cx c))) a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 (b_s (o_cx c) + 16)) s3 s4 (Z_to_bv 64 SHS) (Z_to_bv 64 (b_s (o_cx c) + 12)) s7 (Z_to_bv 64 (b_s (o_cx c) + 3184))
       (Z_to_bv 64 2147450880) (Z_to_bv 64 (b_s (o_cx c) + 1096)) (Z_to_bv 64 (b_s (o_cx c) + 3152)) t3 t4 t5 t6) (only parsing).

Section ACeilS2. Context {ACEIL__ : ACeil}.
Section Conts.
  Variable c : foctx.
  Variable SHS : Z.                                 (* [comment removed for export] *)
  Variable w0 : word.                               (* [comment removed for export] *)
  Variable RO : (word -> option byte) -> Prop.      (* [comment removed for export] *)
  Notation S := (b_s (o_cx c)). Notation uspi := (bv_unsigned (o_SP c)).
  (* [comment removed for export] *)
  Definition A0_FKjoin : Prop :=
    forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 w32 w104 w112 w120 w184 w192 w200 w208 : word) (m : word -> option byte)
           (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      let d' := set8 (o_d c) oc ol nu k0 tp rn rt cb in let s' := smod (o_s c) out av tout in
      DSgA DI_A0 c m (jk_set_o (o_J c) tol toh) d' s' -> DESTgA DI_A0 c m s' dbytes rest ->
      rw_cells a0segs m uspi (bzd_slots S SHS w0 w32 w104 w112 w120 w184 w192 w200 w208 (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870))) ->
      RO m -> munch (FWBA c) (o_m0 c) m -> wmono a0segs (o_m0 c) m ->
      ojoin c d' s' ->
      evt a0segs (o_KQ c (0%Z, d', s'))
          (MS (A0RR c SHS (Z_to_bv 64 (SHS + 398)) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (SHS + -2147450878)) s3 s4 s7 t3 t4 t5 t6)
              (o_F c) (Z_to_bv 64 0x86f08) (o_fc c) None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition A0_FKexit : Prop :=
    forall (ra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x24 x25 x26 x27 t3 t4 t5 t6 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 : word)
           (m : word -> option byte)
           (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      let d' := set8 (o_d c) oc ol nu k0 tp rn rt cb in let s' := smod (o_s c) out av tout in
      DSgA DI_A0 c m (jk_set_o (o_J c) tol toh) d' s' -> DESTgA DI_A0 c m s' dbytes rest ->
      rw_cells a0segs m uspi (bzd_slots S SHS w0 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248) ->
      RO m -> munch (FWBA c) (o_m0 c) m -> wmono a0segs (o_m0 c) m ->
      oexit c d' s' ->
      evt a0segs (o_KQ c (1%Z, d', s'))
          (MS (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 (Z_to_bv 64 (-4)) x24 x25 x26 x27 t3 t4 t5 t6)
              (o_F c) (Z_to_bv 64 0x84320) (o_fc c) None m (seg_rom a0segs)).
End Conts.
End ACeilS2.
