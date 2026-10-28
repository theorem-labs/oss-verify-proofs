(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_HufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit2 HufWalkKit3.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg Stdio_kit AF_huf_fdw_kit AF_huf_w4s12_iface AF_huf_w4s1k AF_huf_w4s1kb AF_huf_w4s1x.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Notation amem := (word -> option byte).

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma w4s1_dctx_tr : forall RNG m m' P DT4 DBL DBH DST dcap tl W,
  w4s1_dctx RNG m P DT4 DBL DBH DST dcap tl -> munch W m m' -> appW W ->
  w4s1_dctx RNG m' P DT4 DBL DBH DST dcap tl.
Proof.
  intros RNG m m' P DT4 DBL DBH DST dcap tl W C MU AW.
  pose proof C as C0. w4s1_dctx_intro C0.
  unfold w4s1_dctx in *. destruct C as (U1 & C1 & C2 & U2 & C).
  split; [|split; [exact C1|split; [exact C2|split; [|exact C]]]].
  - destruct (Z_lt_le_dec DBL DBH) as [LT|GE].
    + eapply unpoisoned_appW; [exact U1|exact MU|exact AW|exact LT|lia].
    + destruct U1 as (Z1 & Z2 & _). split; [exact Z1|]. split; [exact Z2|]. intros G HG. lia.
  - destruct (Z_lt_le_dec DST (DST + dcap)) as [LT|GE].
    + eapply unpoisoned_appW; [exact U2|exact MU|exact AW|exact LT|lia].
    + destruct U2 as (Z1 & Z2 & _). split; [exact Z1|]. split; [exact Z2|]. intros G HG. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w4s1_ztab_tr : forall m m' A N st fs W, ztab_fact bsegs m A N st fs -> munch W m m' -> disjoint_from W A N ->
  0 <= A -> A + N <= 2^64 -> ztab_fact bsegs m' A N st fs.
Proof.
  intros m m' A N st fs W ZT MU DJ A0 AN z Hz lo hi FF.
  destruct (ZT z Hz lo hi FF) as (b & RD & B). exists b. split; [|exact B].
  assert (BA : bytes_at bsegs m z [b]).
  { split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i as [|i]; [|cbn in Hi; lia].
    cbn [nth_error]. cbn [rdn] in RD. unfold mrd. replace (z + Z.of_nat 0) with z by lia. change (wa z) with (Z_to_bv 64 z).
    destruct (match m (Z_to_bv 64 z) with Some b0 => Some b0 | None => seg_rom bsegs (Z_to_bv 64 z) end);
      [|discriminate]. inversion RD. reflexivity. }
  assert (DJ1 : disjoint_from W z (Z.of_nat (length [b]))).
  { clear - DJ Hz. cbn [length Z.of_nat Pos.of_succ_nat]. induction W as [|[x y] W IH]; [exact I|].
    cbn in DJ |- *. destruct DJ as [D1 D2]. split; [lia|exact (IH D2)]. }
  pose proof (bytes_at_transport bsegs W m m' z [b] BA MU DJ1) as T.
  pose proof (bytes_at_rdn bsegs m' z [b] 0 1 T ltac:(cbn; lia)) as R.
  replace (z + Z.of_nat 0) with z in R by lia. exact R.
Qed.


Lemma w4s1_src_tr : forall RNG m m' SS n SBL SBH W,
  w4s_src_ctx RNG m SS n SBL SBH -> munch W m m' -> mem_inv bsegs m' -> appW W -> disjoint_from W SS n ->
  w4s_src_ctx RNG m' SS n SBL SBH.
Proof.
  intros RNG m m' SS n SBL SBH W C MU MI' AW DJ.
  destruct C as (MI & (sbuf & SB & SL) & U & C).
  split; [exact MI'|]. split.
  - exists sbuf. split; [|exact SL]. eapply bytes_at_transport; [exact SB|exact MU|rewrite SL; exact DJ].
  - split; [|exact C].
    destruct (Z_lt_le_dec SBL SBH) as [LT|GE].
    + eapply unpoisoned_appW; [exact U|exact MU|exact AW|exact LT|lia].
    + destruct U as (Z1 & Z2 & _). split; [exact Z1|]. split; [exact Z2|]. intros G HG. lia.
Qed.

(* [comment removed for export] *)
Section W4S1C.
  Hypothesis DA : w4s1_decA_case.
  Hypothesis DB : w4s1_decB_case.
  Hypothesis RALL : w4s1_rall_case.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w4s1_ab : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 w0 : word) (pad1 pad2 pad3 pad4 tb : list byte) (obuf : list Z)
    (SP DST dcap e1 j DT tl rsv DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 : Z),
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl -> mem_inv bsegs mm ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  bytes_at bsegs mm (DT + 4) tb -> Z.of_nat (length tb) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) -> Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 (Z_to_bv 64 (tl + 256 * rsv)); C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 (DST + dcap - 3));
     C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DST + e1));
     C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> 0 <= j -> 0 <= e1 -> 3 * e1 + j + 4 <= dcap -> dcap <= 2^32 ->
  0 <= b1 <= 64 -> 0 <= b2 <= 64 -> 0 <= b3 <= 64 -> 0 <= b4 <= 64 ->
  0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
  4096 <= S1 + o1 <= 2^47 -> 4096 <= S2 + o2 <= 2^47 -> 4096 <= S3 + o3 <= 2^47 -> 4096 <= S4 + o4 <= 2^47 ->
  4096 <= DT <= 2^47 -> 2^20 <= SP <= 2^47 ->
  (forall (mm' : amem) (obuf' : list Z) (N1 N2 N3 N4 N5 N6 N7 N8 M1 M2 M3 M4 M5 M6 M7 M8 : Z)
          (y12 y13 y14 y15 y16 y21 y23 : word),
     munch [(DST, DST + dcap); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 (b1 + (N1 + N5) + (M1 + M5))); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 (b2 + (N2 + N6) + (M2 + M6))); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 (b3 + (N3 + N7) + (M3 + M7))); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 (b4 + (N4 + N8) + (M4 + M8))); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     0 <= N1 <= 12 -> 0 <= N2 <= 12 -> 0 <= N3 <= 12 -> 0 <= N4 <= 12 ->
     0 <= N5 <= 12 -> 0 <= N6 <= 12 -> 0 <= N7 <= 12 -> 0 <= N8 <= 12 ->
     0 <= M1 <= 12 -> 0 <= M2 <= 12 -> 0 <= M3 <= 12 -> 0 <= M4 <= 12 ->
     0 <= M5 <= 12 -> 0 <= M6 <= 12 -> 0 <= M7 <= 12 -> 0 <= M8 <= 12 ->
     evtF bsegs RNG Q
        (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 (b2 + (N2 + N6) + (M2 + M6)))
                 (Z_to_bv 64 (b3 + (N3 + N7) + (M3 + M7))) (Z_to_bv 64 (b4 + (N4 + N8) + (M4 + M8)))
                 (Z_to_bv 64 (j + (DST + e1) + 3)) (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) (Z_to_bv 64 (-20))
                 (Z_to_bv 64 (j + (DST + 3 * e1) + 3)) y12 y13 y14 y15 y16 (Z_to_bv 64 (b1 + (N1 + N5) + (M1 + M5)))
                 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 j) y21 (Z_to_bv 64 (j + (DST + 2 * e1) + 3)) y23
                 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 c4) (Z_to_bv 64 (2^62))
                 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (j + (DST + 3 * e1) + 2)))
            F (Z_to_bv 64 0x8a5f0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 b2) (Z_to_bv 64 b3) (Z_to_bv 64 b4) x8 x9
               (Z_to_bv 64 (-20)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 b1) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3))
               (Z_to_bv 64 j) (Z_to_bv 64 DST) x22 x23 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 c4) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1 * DT + -5)) x31)
          F (Z_to_bv 64 0x89de4) fc None mm (seg_rom bsegs)).
  Proof using DA DB.
    intros Q RNG mm F fc gp tp x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 w0 pad1 pad2 pad3 pad4 tb obuf
      SP DST dcap e1 j DT tl rsv DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4
      CX MI ZT TB TBL TLR OB OBL FRC D1 D2 D3 D4 TL RS J0 E0 JD DCB B1 B2 B3 B4 C1 C2 C3 C4 P1 P2 P3 P4 DTB SPB KAB.
    pose proof CX as CX0. w4s1_dctx_intro CX0.
    assert (AW : appW [(DST, DST + dcap); (SP + -376, SP + -336); (SP + -224, SP + -104)]).
    { unfold KLOW, KHIGH in *.
      apply appW_cons; [unfold KLOW, KHIGH, KXGoM.apart in *; lia|].
      apply appW_cons; [unfold KLOW, KHIGH, KXGoM.apart in *; lia|].
      apply appW_cons; [unfold KLOW, KHIGH, KXGoM.apart in *; lia|].
      apply Forall_nil.
      all: exact I. }
    eapply DA; try eassumption.
    intros mm1 obuf1 N1 N2 N3 N4 N5 N6 N7 N8 y6 y7 y9 y22 MU1 WM1 MI1 OB1 OBL1 RD1 RD2 RD3 RD4
      HN1 HN2 HN3 HN4 HN5 HN6 HN7 HN8.
    eapply DB.
    1: exact (w4s1_dctx_tr _ _ _ _ _ _ _ _ _ _ _ CX MU1 AW).
    1: exact MI1.
    1: eapply w4s1_ztab_tr; [exact ZT|exact MU1|cbn [disjoint_from]; unfold KXGoM.apart in *; lia|lia|lia].
    1: eapply bytes_at_transport; [exact TB|exact MU1|rewrite TBL; cbn [disjoint_from]; unfold KXGoM.apart in *; lia].
    1: exact TBL.
    1: exact TLR.
    1: exact OB1.
    1: exact OBL1.
    1: eapply rw_cells_transport; [exact FRC|exact MU1|exact WM1|cbn [disjoint_from cells_size csize]; unfold KXGoM.apart in *; lia].
    1-4: eassumption.
    all: try lia.
    intros mm2 obuf2 M1 M2 M3 M4 M5 M6 M7 M8 y12 y13 y14 y15 y16 y21 y23 MU2 WM2 MI2 OB2 OBL2 RE1 RE2 RE3 RE4
      HM1 HM2 HM3 HM4 HM5 HM6 HM7 HM8.
    eapply (KAB mm2 obuf2 N1 N2 N3 N4 N5 N6 N7 N8 M1 M2 M3 M4 M5 M6 M7 M8);
      [ eapply munch_trans; [exact MU1|exact MU2] | eapply wmono_trans; [exact WM1|exact WM2] | .. ]; eassumption.
  Qed.
  Lemma w4s1_core : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 w0 : word) (pad1 pad2 pad3 pad4 tb : list byte) (obuf : list Z)
    (SP DST dcap e1 j DT tl rsv DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 : Z)
    (SS n SBL SBH L1 L2 L3 L4 : Z),
  w4s1_dctx RNG mm (SP + -480) (DT + 4) DBL DBH DST dcap tl -> mem_inv bsegs mm ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  bytes_at bsegs mm (DT + 4) tb -> Z.of_nat (length tb) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST (map (Z_to_bv 8) obuf) -> Z.of_nat (length obuf) = dcap ->
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 (Z_to_bv 64 (tl + 256 * rsv)); C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 (DST + dcap - 3));
     C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 (DST + e1));
     C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -376) [C8 (Z_to_bv 64 c1); C4 (Z_to_bv 64 b1); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1)); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c2); C4 (Z_to_bv 64 b2); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2)); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
  rw_cells bsegs mm (SP + -184) [C8 (Z_to_bv 64 c3); C4 (Z_to_bv 64 b3); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3)); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c4); C4 (Z_to_bv 64 b4); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4)); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> 0 <= j -> 0 <= e1 -> 3 * e1 + j + 4 <= dcap -> dcap <= 2^32 ->
  0 <= b1 <= 64 -> 0 <= b2 <= 64 -> 0 <= b3 <= 64 -> 0 <= b4 <= 64 ->
  0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
  4096 <= S1 + o1 <= 2^47 -> 4096 <= S2 + o2 <= 2^47 -> 4096 <= S3 + o3 <= 2^47 -> 4096 <= S4 + o4 <= 2^47 ->
  4096 <= DT <= 2^47 -> 2^20 <= SP <= 2^47 ->
  w4s_src_ctx RNG mm SS n SBL SBH -> KXGoM.apart SS n (SP + -480) 480 -> KXGoM.apart SS n DST dcap ->
  0 <= o1 -> 0 <= o2 -> 0 <= o3 -> 0 <= o4 ->
  (o1 = 0 /\ 0 <= b1 <= 64) \/ (o1 + 8 <= L1 /\ 0 <= b1 <= 8) ->
  (o2 = 0 /\ 0 <= b2 <= 64) \/ (o2 + 8 <= L2 /\ 0 <= b2 <= 8) ->
  (o3 = 0 /\ 0 <= b3 <= 64) \/ (o3 + 8 <= L3 /\ 0 <= b3 <= 8) ->
  (o4 = 0 /\ 0 <= b4 <= 64) \/ (o4 + 8 <= L4 /\ 0 <= b4 <= 8) ->
  SS <= S1 -> S1 + L1 <= SS + n -> SS <= S2 -> S2 + L2 <= SS + n ->
  SS <= S3 -> S3 + L3 <= SS + n -> SS <= S4 -> S4 + L4 <= SS + n ->
  (forall (mm' : amem) (obuf' : list Z) (B1 B2 B3 B4 o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' : Z) (x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 (Z_to_bv 64 (tl + 256 * rsv)); C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 (DST + dcap - 3));
        C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 c3'); C8 (Z_to_bv 64 c2'); C8 (Z_to_bv 64 c1'); C8 (Z_to_bv 64 (DST + e1));
        C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1'); C4 (Z_to_bv 64 b1'); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1')); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2'); C4 (Z_to_bv 64 b2'); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2')); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     8 <= o1 -> o1' = o1 - B1 / 8 -> b1' = B1 mod 8 -> 8 <= o2 -> o2' = o2 - B2 / 8 -> b2' = B2 mod 8 ->
     8 <= o3 -> o3' = o3 - B3 / 8 -> b3' = B3 mod 8 -> 8 <= o4 -> o4' = o4 - B4 / 8 -> b4' = B4 mod 8 ->
     b1 <= B1 <= b1 + 48 -> b2 <= B2 <= b2 + 48 -> b3 <= B3 <= b3 + 48 -> b4 <= B4 <= b4 + 48 ->
     0 <= c1' < 2^64 -> 0 <= c2' < 2^64 -> 0 <= c3' < 2^64 -> 0 <= c4' < 2^64 ->
     3 * e1 + (j + 4) + 4 <= dcap ->
     evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 (S4 + o4')) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 b2') (Z_to_bv 64 b3') (Z_to_bv 64 b4') x8 x9
                (Z_to_bv 64 (-20)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 b1') (Z_to_bv 64 (S2 + o2')) (Z_to_bv 64 (S3 + o3'))
                (Z_to_bv 64 (j + 4)) (Z_to_bv 64 DST) x22 x23 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (S1 + o1')) (Z_to_bv 64 (DT + 4))
                (Z_to_bv 64 c4') (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1 * DT + -5)) x31)
           F (Z_to_bv 64 AW4_LHEAD) fc None mm' (seg_rom bsegs))) ->
  (forall (mm' : amem) (obuf' : list Z) (B1 B2 B3 B4 o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' : Z) (w40 w48 w56 : word)
          (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31 : word),
     munch [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST (map (Z_to_bv 8) obuf') -> Z.of_nat (length obuf') = dcap ->
     rw_cells bsegs mm' (SP + -480) [C8 w0; C8 (Z_to_bv 64 (tl + 256 * rsv)); C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 (DST + dcap - 3));
        C8 (Z_to_bv 64 e1); C8 w40; C8 w48; C8 w56; C8 (Z_to_bv 64 (DST + e1));
        C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 (Z_to_bv 64 (DST + dcap))] ->
     rw_cells bsegs mm' (SP + -376) [C8 (Z_to_bv 64 c1'); C4 (Z_to_bv 64 b1'); CB 4 pad1; C8 (Z_to_bv 64 (S1 + o1')); C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 (S1 + 8))] ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c2'); C4 (Z_to_bv 64 b2'); CB 4 pad2; C8 (Z_to_bv 64 (S2 + o2')); C8 (Z_to_bv 64 S2); C8 (Z_to_bv 64 (S2 + 8))] ->
     rw_cells bsegs mm' (SP + -184) [C8 (Z_to_bv 64 c3'); C4 (Z_to_bv 64 b3'); CB 4 pad3; C8 (Z_to_bv 64 (S3 + o3')); C8 (Z_to_bv 64 S3); C8 (Z_to_bv 64 (S3 + 8))] ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c4'); C4 (Z_to_bv 64 b4'); CB 4 pad4; C8 (Z_to_bv 64 (S4 + o4')); C8 (Z_to_bv 64 S4); C8 (Z_to_bv 64 (S4 + 8))] ->
     (o1 < 8 /\ o1' = o1 /\ b1' = B1) \/ (8 <= o1 /\ o1' = o1 - B1 / 8 /\ b1' = B1 mod 8) ->
     (o2 < 8 /\ o2' = o2 /\ b2' = B2) \/ (8 <= o2 /\ o2' = o2 - B2 / 8 /\ b2' = B2 mod 8) ->
     (o3 < 8 /\ o3' = o3 /\ b3' = B3) \/ (8 <= o3 /\ o3' = o3 - B3 / 8 /\ b3' = B3 mod 8) ->
     (o4 < 8 /\ o4' = o4 /\ b4' = B4) \/ (8 <= o4 /\ o4' = o4 - B4 / 8 /\ b4' = B4 mod 8) ->
     b1 <= B1 <= b1 + 48 -> b2 <= B2 <= b2 + 48 -> b3 <= B3 <= b3 + 48 -> b4 <= B4 <= b4 + 48 ->
     0 <= c1' < 2^64 -> 0 <= c2' < 2^64 -> 0 <= c3' < 2^64 -> 0 <= c4' < 2^64 ->
     evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + e1 + (j + 4))) x9
                (Z_to_bv 64 (-20)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + (j + 4))) (Z_to_bv 64 (tl + 256 * rsv))
                (Z_to_bv 64 (DST + 3 * e1 + (j + 4))) x21 (Z_to_bv 64 (DST + 2 * e1 + (j + 4))) (Z_to_bv 64 (DST + e1))
                (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) x28 x29 x30 x31)
           F (Z_to_bv 64 AW4_LFIN) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (SP + -480)) gp tp (Z_to_bv 64 b2) (Z_to_bv 64 b3) (Z_to_bv 64 b4) x8 x9
               (Z_to_bv 64 (-20)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 b1) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3))
               (Z_to_bv 64 j) (Z_to_bv 64 DST) x22 x23 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 c4) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1 * DT + -5)) x31)
          F (Z_to_bv 64 0x89de4) fc None mm (seg_rom bsegs)).
  Proof using DA DB RALL.
    intros Q RNG mm F fc gp tp x8 x9 x11 x12 x13 x14 x15 x16 x22 x23 x31 w0 pad1 pad2 pad3 pad4 tb obuf
      SP DST dcap e1 j DT tl rsv DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 b1 b2 b3 b4 c1 c2 c3 c4 SS n SBL SBH L1 L2 L3 L4
      CX MI ZT TB TBL TLR OB OBL FRC D1 D2 D3 D4 TL RS J0 E0 JD DCB HB1 HB2 HB3 HB4 C1 C2 C3 C4 P1 P2 P3 P4 DTB SPB
      SRC AP1 AP2 O1 O2 O3 O4 SH1 SH2 SH3 SH4 SL1 SU1 SL2 SU2 SL3 SU3 SL4 SU4 KL KF.
    pose proof CX as CX0. w4s1_dctx_intro CX0.
    assert (AW : appW [(DST, DST + dcap); (SP + -376, SP + -336); (SP + -224, SP + -104)]).
    { unfold KLOW, KHIGH in *.
      apply appW_cons; [unfold KLOW, KHIGH, KXGoM.apart in *; lia|].
      apply appW_cons; [unfold KLOW, KHIGH, KXGoM.apart in *; lia|].
      apply appW_cons; [unfold KLOW, KHIGH, KXGoM.apart in *; lia|].
      apply Forall_nil.
      all: exact I. }
    assert (SUB : sub_fp [(DST, DST + dcap); (SP + -376, SP + -336); (SP + -224, SP + -104)]
                         [(DST, DST + dcap); (SP + -440, SP + -416); (SP + -376, SP + -336); (SP + -224, SP + -104)]).
    { intros x HX. cbn [outside] in *. tauto. }
    eapply w4s1_ab. all: try (lazymatch goal with |- forall _, _ => fail | _ => eassumption end).
    intros mm2 obuf2 N1 N2 N3 N4 N5 N6 N7 N8 M1 M2 M3 M4 M5 M6 M7 M8 y12 y13 y14 y15 y16 y21 y23 MU2 WM2 MI2 OB2 OBL2
      RE1 RE2 RE3 RE4 HN1 HN2 HN3 HN4 HN5 HN6 HN7 HN8 HM1 HM2 HM3 HM4 HM5 HM6 HM7 HM8.
    pose proof (w4s1_dctx_tr _ _ _ _ _ _ _ _ _ _ _ CX MU2 AW) as CX2.
    assert (SRC2 : w4s_src_ctx RNG mm2 SS n SBL SBH).
    { eapply w4s1_src_tr; [exact SRC|exact MU2|exact MI2|exact AW|cbn [disjoint_from]; unfold KXGoM.apart in *; lia]. }
    assert (FR2 : rw_cells bsegs mm2 (SP + -480) [C8 w0; C8 (Z_to_bv 64 (tl + 256 * rsv)); C8 (Z_to_bv 64 (DST + 3 * e1));
       C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 e1); C8 (Z_to_bv 64 c3); C8 (Z_to_bv 64 c2); C8 (Z_to_bv 64 c1);
       C8 (Z_to_bv 64 (DST + e1)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * e1));
       C8 (Z_to_bv 64 (DST + dcap))]).
    { eapply rw_cells_transport; [exact FRC|exact MU2|exact WM2|cbn [disjoint_from cells_size csize]; unfold KXGoM.apart in *; lia]. }
    eapply (RALL Q RNG mm2 F fc gp tp y12 y13 y14 y15 y16 y21 y23 w0 pad1 pad2 pad3 pad4 obuf2 SP DST dcap e1 j DT tl rsv
              DBL DBH S1 S2 S3 S4 o1 o2 o3 o4 (b1 + (N1 + N5) + (M1 + M5)) (b2 + (N2 + N6) + (M2 + M6))
              (b3 + (N3 + N7) + (M3 + M7)) (b4 + (N4 + N8) + (M4 + M8)) c1 c2 c3 c4 SS n SBL SBH L1 L2 L3 L4).
    all: try (lazymatch goal with |- forall _, _ => fail | _ => first [exact CX2 | exact SRC2 | exact FR2 | eassumption | lia] end).
    - intros mm3 obuf3 o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' z8 z9 z11 z12 z13 z14 z15 z16 z22 z23 z31
        MU3 WM3 MI3 OB3 OBL3 FR3 R31 R32 R33 R34 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 Q1 Q2 Q3 Q4 JJ.
      eapply (KL mm3 obuf3 (b1 + (N1 + N5) + (M1 + M5)) (b2 + (N2 + N6) + (M2 + M6)) (b3 + (N3 + N7) + (M3 + M7))
                (b4 + (N4 + N8) + (M4 + M8)) o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4').
      1: eapply munch_trans; [eapply munch_weaken; [exact SUB|exact MU2]|exact MU3].
      1: eapply wmono_trans; [exact WM2|exact WM3].
      all: first [eassumption | lia].
    - intros mm3 obuf3 o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' w40 w48 w56
        z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z21 z25 z28 z29 z30 z31
        MU3 WM3 MI3 OB3 OBL3 FR3 R31 R32 R33 R34 G1 G2 G3 G4 Q1 Q2 Q3 Q4.
      eapply (KF mm3 obuf3 (b1 + (N1 + N5) + (M1 + M5)) (b2 + (N2 + N6) + (M2 + M6)) (b3 + (N3 + N7) + (M3 + M7))
                (b4 + (N4 + N8) + (M4 + M8)) o1' o2' o3' o4' b1' b2' b3' b4' c1' c2' c3' c4' w40 w48 w56).
      1: eapply munch_trans; [eapply munch_weaken; [exact SUB|exact MU2]|exact MU3].
      1: eapply wmono_trans; [exact WM2|exact WM3].
      all: first [eassumption | lia].
  Qed.
End W4S1C.
End CANSEC1.
