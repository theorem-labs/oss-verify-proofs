(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Gq_dither_l1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation DL0_W lined nl bufs1 bufs2 n1 := [(lined, lined + nl); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)]%Z (only parsing).
Notation ONE := (Z_to_bv 64 1) (only parsing).

(* [comment removed for export] *)
Definition dl_geom2 (lined nl bufs1 bufs2 n1 w : Z) : Prop :=
  dl_geom lined nl bufs1 n1 w
  /\ 0 < bufs2 /\ bufs2 mod 8 = 0 /\ bufs2 + n1 <= 2^47 /\ (bufs2 + n1 <= 0x7fff7000 \/ 0x10007fff8000 <= bufs2) /\ (bufs2 + n1 <= 0x10000 \/ SEGTOP_A <= bufs2)
  /\ (bufs2 + n1 <= lined \/ lined + nl <= bufs2) /\ (bufs2 + n1 <= bufs1 \/ bufs1 + n1 <= bufs2).

(* [comment removed for export] *)
Definition dl0_exit (ra sp gp tp a0 a2 a3 a4 a5 a7 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 bufs2 n1 w : Z) : machine_state -> Prop :=
  fun ms' => exists (s1' a1' s2' s3' s4' s5' s6' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (w - 1)) ONE (Z_to_bv 64 (-2147483648)) s1' a0 a1' a2 a3 a4 a5 (Z_to_bv 64 (w - 1)) a7
                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 (Z_to_bv 64 3) (Z_to_bv 64 2) ONE (Z_to_bv 64 134217727))
             F (Z_to_bv 64 0x9e8ec) fc None m' (seg_rom asegs)
    /\ munch (DL0_W lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl.

(* [comment removed for export] *)
Definition dl0_px_end (ra sp gp tp a4 a5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (j lined nl bufs1 bufs2 n1 w : Z) : machine_state -> Prop :=
  fun ms' => exists (s1' a1' s2' s3' s4' s5' s6' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 j) ONE (Z_to_bv 64 (-2147483648)) s1' (Z_to_bv 64 lined) a1' (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2)
                  a4 a5 (Z_to_bv 64 (w - 1)) (Z_to_bv 64 SHB) s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                  (Z_to_bv 64 3) (Z_to_bv 64 2) ONE (Z_to_bv 64 134217727))
             F (Z_to_bv 64 0x9e5d4) fc None m' (seg_rom asegs)
    /\ munch (DL0_W lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl.

(* [comment removed for export] *)
Lemma dl0_tail : forall (z : Z) (ra sp gp tp a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem)
    (j lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  0 <= j < w - 1 -> dl_geom2 lined nl bufs1 bufs2 n1 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  evt asegs (dl0_px_end ra sp gp tp a4 a5 s7 s8 s9 s10 s11 F fc m j lined nl bufs1 bufs2 n1 w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 j) ONE (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 z) (Z_to_bv 64 lined)
             (Z_to_bv 64 (Z.lxor (bufs2 + j + 1) 3)) (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2)
             a4 a5 (Z_to_bv 64 (w - 1)) (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 3) (Z_to_bv 64 2) ONE (Z_to_bv 64 134217727))
        F (Z_to_bv 64 0x9e5c0) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros HJ GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL.
  pose proof GEO as ((HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP)
                     & C0 & C8 & CHI & CSH & CSEG & SEP2 & SEP3). clear GEO.
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (DL0_W lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (lxor3_eq (bufs2 + j + 1)) as LXD.
  assert (IDXD : 0 <= Z.lxor (bufs2 + j + 1) 3 - bufs2 < n1) by (rewrite LXD; clear - HJ HW WN N4 C8; Z.div_mod_to_equations; lia).
  park_disj.
  lwalk [0x9e5d0; 0x9eb30; 0x9ea88].
  remember (Z.lxor (bufs2 + j + 1) 3 - bufs2) as ix eqn:EIX.   (* [comment removed for export] *)
  unfold parked in CSH, CSEG, SEP2, SEP3.                        (* [comment removed for export] *)
  arr_sb bufs2 ix (Z.lxor (bufs2 + j + 1) 3).
  lwalk [0x9e5d4].
  apply evt_done. unfold dl0_px_end. do 7 eexists.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    lazymatch goal with UBx : u8arr asegs mm bufs1 ?b1, UCx : u8arr asegs mm bufs2 ?b2, ULx : u32arr asegs mm lined ?wlx |- _ => exists mm, b1, b2, wlx end end.
  split; [reflexivity|].
  repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma dl0_tailk : forall (z : Z) (ra sp gp tp a4 a5 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 : word) F fc (m mm : mem)
    (j lined nl bufs1 bufs2 n1 w : Z) (bs1' bs2' : list byte) (wl' : list word),
  0 <= j < w - 1 -> dl_geom2 lined nl bufs1 bufs2 n1 w ->
  munch (DL0_W lined nl bufs1 bufs2 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
  u8arr asegs mm bufs1 bs1' -> Z.of_nat (length bs1') = n1 -> acc asegs mm bufs1 n1 ->
  u8arr asegs mm bufs2 bs2' -> Z.of_nat (length bs2') = n1 -> acc asegs mm bufs2 n1 ->
  u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
  evt asegs (dl0_px_end ra sp gp tp a4 a5 s7 s8 s9 s10 s11 F fc m j lined nl bufs1 bufs2 n1 w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 j) ONE (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 z) (Z_to_bv 64 lined)
           (Z_to_bv 64 (Z.lxor (bufs2 + j + 1) 3)) (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2)
           a4 a5 (Z_to_bv 64 (w - 1)) (Z_to_bv 64 SHB) s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
           (Z_to_bv 64 3) (Z_to_bv 64 2) ONE (Z_to_bv 64 134217727))
        F (Z_to_bv 64 0x9e5c0) fc None mm (seg_rom asegs)).
Proof.
  intros until wl'. intros HJ GEO MU1 WM1 MI1 UB1 UBL1 ACCB1 UC1 UCL1 ACCC1 UL1 ULL1 ACCL1.
  eapply evt_cut.
  - eapply (dl0_tail z) with (bs1 := bs1') (bs2 := bs2') (wl := wl'); try eassumption.
  - intros ms' PO. apply evt_done. unfold dl0_px_end in PO |- *.
    destruct PO as (s1'' & a1'' & s2'' & s3'' & s4'' & s5'' & s6'' & m' & bs1'' & bs2'' & wl'' & E & MU' & WM' & R).
    exists s1'', a1'', s2'', s3'', s4'', s5'', s6'', m', bs1'', bs2'', wl''.
    split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R].
Qed.

(* [comment removed for export] *)
Ltac gen_zreg r :=
  reg_val (Z_to_bv 5 r) ltac:(fun v => lazymatch v with
    | Z_to_bv 64 ?e => tryif is_var e then idtac else (let z := fresh "zv" in let E := fresh "Ezv" in remember e as z eqn:E in |- *; clear E)
    | _ => idtac end).

(* [comment removed for export] *)
Lemma dl0_body : forall (ra sp gp tp s1 a1 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem)
    (j lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  0 <= j < w - 1 -> dl_geom2 lined nl bufs1 bufs2 n1 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  evt asegs (dl0_px_end ra sp gp tp a4 a5 s7 s8 s9 s10 s11 F fc m j lined nl bufs1 bufs2 n1 w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 j) ONE (Z_to_bv 64 (-2147483648)) s1 (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2)
             a4 a5 (Z_to_bv 64 (w - 1)) (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 3) (Z_to_bv 64 2) ONE (Z_to_bv 64 134217727))
        F (Z_to_bv 64 0x9e5e0) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros HJ GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL.
  pose proof GEO as ((HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP)
                     & C0 & C8 & CHI & CSH & CSEG & SEP2 & SEP3).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (DL0_W lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (lxor3_eq (bufs1 + j)) as LX0.
  pose proof (lxor3_eq (bufs1 + j + 1)) as LX1.
  pose proof (lxor3_eq (bufs2 + j)) as LX2.
  pose proof (lxor3_eq (bufs2 + j + 1)) as LXD.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + j) 3 - bufs1 < n1) by (rewrite LX0; clear - HJ HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (IDX1 : 0 <= Z.lxor (bufs1 + j + 1) 3 - bufs1 < n1) by (rewrite LX1; clear - HJ HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (IDX2 : 0 <= Z.lxor (bufs2 + j) 3 - bufs2 < n1) by (rewrite LX2; clear - HJ HW WN N4 C8; Z.div_mod_to_equations; lia).
  assert (IDXD : 0 <= Z.lxor (bufs2 + j + 1) 3 - bufs2 < n1) by (rewrite LXD; clear - HJ HW WN N4 C8; Z.div_mod_to_equations; lia).
  park_disj.
  lwalk [0x9e60c; 0x9eb20; 0x9ea88].
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs1 (Z.lxor (bufs1 + j) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (bufs1 + j) 3 - bufs1)) with (Z.lxor (bufs1 + j) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs1) by (split; assumption).
  clear HB WB.
  lwalk [0x9e768; 0x9e618].
  brfork SG.
  - (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 8 ov) as OVR.
    lwalk [0x9e5d4; 0x9e770].
    brfork CL1.
    { (* [comment removed for export] *)
      apply evt_done. unfold dl0_px_end. do 7 eexists. exists m, bs1, bs2, wl. split; [reflexivity|].
      repeat (split; [assumption|]). assumption. }
    (* [comment removed for export] *)
    lwalk [0x9e7a4; 0x9eb60; 0x9ea88].
    destruct UB as [HB WB].
    destruct (bytes_at_read1 m bufs1 bs1 (Z.lxor (bufs1 + j + 1) 3 - bufs1) HB ltac:(lia)) as (rv & R).
    replace (bufs1 + (Z.lxor (bufs1 + j + 1) 3 - bufs1)) with (Z.lxor (bufs1 + j + 1) 3) in R by lia.
    lstep. clear R.
    assert (UB : u8arr asegs m bufs1 bs1) by (split; assumption).
    clear HB WB.
    lwalk [0x9e7cc; 0x9eb68; 0x9ea88].
    remember (Z.lxor (bufs1 + j + 1) 3 - bufs1) as ix1 eqn:EIX1.
    unfold parked in BSH, BSEG, SEP, SEP3.
    gen_zreg 20. gen_zreg 19. gen_zreg 9.          (* [comment removed for export] *)
    arr_sb bufs1 ix1 (Z.lxor (bufs1 + j + 1) 3).
    park_disj.
    (* [comment removed for export] *)
    lwalk [0x9e804; 0x9eb70; 0x9ea88].
    lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof UCx as [HB WB];
      destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + j) 3 - bufs2) HB ltac:(lia)) as (cv & R) end.
    replace (bufs2 + (Z.lxor (bufs2 + j) 3 - bufs2)) with (Z.lxor (bufs2 + j) 3) in R by lia.
    lstep. clear R HB WB.
    lwalk [0x9e820; 0x9e8e4; 0x9ea88].
    remember (Z.lxor (bufs2 + j) 3 - bufs2) as ix2 eqn:EIX2.
    unfold parked in CSH, CSEG, SEP2, SEP3.
    gen_zreg 20. gen_zreg 9.                        (* [comment removed for export] *)
    arr_sb bufs2 ix2 (Z.lxor (bufs2 + j) 3).
    park_disj.
    (* [comment removed for export] *)
    lwalk [0x9e5a8; 0x9eb18; 0x9ea88].
    lazymatch goal with K : shk ?mm ?b ?X |- _ =>
      assert (KY : shk mm b (Z.lxor X 3))
        by (unfold shk, shad in *; replace (Z.lxor X 3 / 8) with (X / 8) by (pose proof (lxor3_eq X) as LXx; rewrite LXx; clear; Z.div_mod_to_equations; lia); exact K);
      clear K end.
    shbr_inv.
    lwalk [0x9e5a8; 0x9eb18; 0x9ea88].
    lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof UCx as [HB WB];
      destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + j + 1) 3 - bufs2) HB ltac:(lia)) as (dv & R) end.
    replace (bufs2 + (Z.lxor (bufs2 + j + 1) 3 - bufs2)) with (Z.lxor (bufs2 + j + 1) 3) in R by lia.
    lstep. clear R HB WB.
    lwalk [0x9e5c0].
    gen_zreg 9.
    eapply dl0_tailk; eassumption.
  - (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 8 ov) as OVR.
    lwalk [0x9e628; 0x9ea88].
    replace (Z.land (j / 32) 134217727) with (j / 32)
      by (change 134217727 with (Z.ones 27); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; clear - HJ HW; Z.div_mod_to_equations; lia).
    replace (lined + j / 32 * 4) with (lined + 4 * (j / 32)) by (clear; lia).
    assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
    assert (JL : 0 <= j / 32 < nl / 4) by (clear - HJ HW WL L4; Z.div_mod_to_equations; lia).
    lwalk [0x9e658; 0x9eb28; 0x9ea88].
    destruct (u32arr_nth wl (j / 32) ltac:(lia)) as (dv & NTHD).
    pose proof (u32arr_read asegs m lined wl (j / 32) dv _ UL NTHD ltac:(lia) eq_refl) as R.
    lstep. clear R.
    lwalk [0x9e664].
    clear ULL.
    unfold parked in LSH, LSEG, SEP, SEP2.
    gen_zreg 20. gen_zreg 21.
    arr_sw lined (j / 32) (lined + 4 * (j / 32)).
    lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
    park_disj.
    lwalk [0x9e5d4; 0x9e66c].
    brfork CL2.
    { (* [comment removed for export] *)
      apply evt_done. unfold dl0_px_end. do 7 eexists.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with UBx : u8arr asegs mm bufs1 ?b1, UCx : u8arr asegs mm bufs2 ?b2, ULx : u32arr asegs mm lined ?wlx |- _ => exists mm, b1, b2, wlx end end.
      split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
    (* [comment removed for export] *)
    lwalk [0x9e694; 0x9eb38; 0x9ea88].
    lazymatch goal with UBx : u8arr asegs ?mm bufs1 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof UBx as [HB WB];
      destruct (bytes_at_read1 mm bufs1 bsx (Z.lxor (bufs1 + j + 1) 3 - bufs1) HB ltac:(lia)) as (rv & R) end.
    replace (bufs1 + (Z.lxor (bufs1 + j + 1) 3 - bufs1)) with (Z.lxor (bufs1 + j + 1) 3) in R by lia.
    lstep. clear R HB WB.
    lwalk [0x9e6b4; 0x9e6b0].                (* [comment removed for export] *)
    cut2f 0x9e6b4 (Z_to_bv 5 20) (Z_to_bv 5 18) (fun u1 _ : word => exists z : Z, u1 = Z_to_bv 64 z).
    { brfork MX1.
      - cut2f_done ltac:(eexists; reflexivity).
      - lstep. cut2f_done ltac:(eexists; reflexivity). }
    lazymatch goal with H : (exists z : Z, ?uu = Z_to_bv 64 z) |- _ => destruct H as (? & EU); subst uu end.
    lwalk [0x9e6c8; 0x9eb40; 0x9ea88].
    remember (Z.lxor (bufs1 + j + 1) 3 - bufs1) as ix1 eqn:EIX1.
    unfold parked in BSH, BSEG, SEP, SEP3.
    gen_zreg 20. gen_zreg 19. gen_zreg 9.
    arr_sb bufs1 ix1 (Z.lxor (bufs1 + j + 1) 3).
    park_disj.
    (* [comment removed for export] *)
    lwalk [0x9e6f4; 0x9eb48; 0x9ea88].
    lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof UCx as [HB WB];
      destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + j) 3 - bufs2) HB ltac:(lia)) as (cv & R) end.
    replace (bufs2 + (Z.lxor (bufs2 + j) 3 - bufs2)) with (Z.lxor (bufs2 + j) 3) in R by lia.
    lstep. clear R HB WB.
    lwalk [0x9e708; 0x9e704].
    cut2f 0x9e708 (Z_to_bv 5 20) (Z_to_bv 5 19) (fun u1 _ : word => exists z : Z, u1 = Z_to_bv 64 z).
    { brfork MX2.
      - cut2f_done ltac:(eexists; reflexivity).
      - lstep. cut2f_done ltac:(eexists; reflexivity). }
    lazymatch goal with H : (exists z : Z, ?uu = Z_to_bv 64 z) |- _ => destruct H as (? & EU); subst uu end.
    lwalk [0x9e71c; 0x9eb50; 0x9ea88].
    remember (Z.lxor (bufs2 + j) 3 - bufs2) as ix2 eqn:EIX2.
    unfold parked in CSH, CSEG, SEP2, SEP3.
    gen_zreg 20. gen_zreg 9.
    arr_sb bufs2 ix2 (Z.lxor (bufs2 + j) 3).
    park_disj.
    (* [comment removed for export] *)
    lwalk [0x9e744; 0x9eb58; 0x9ea88].
    lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof UCx as [HB WB];
      destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + j + 1) 3 - bufs2) HB ltac:(lia)) as (dv2 & R) end.
    replace (bufs2 + (Z.lxor (bufs2 + j + 1) 3 - bufs2)) with (Z.lxor (bufs2 + j + 1) 3) in R by lia.
    lstep. clear R HB WB.
    lwalk [0x9e5c0; 0x9e760].
    brfork MX3.
    + gen_zreg 9. eapply dl0_tailk; eassumption.
    + lwalk [0x9e5c0]. gen_zreg 9. eapply dl0_tailk; eassumption.
Qed.

(* [comment removed for export] *)
Lemma dl0_pixels : forall (k : nat) (j : Z)
    (ra sp gp tp s1 a1 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem)
    (lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  Z.of_nat k = w - 1 - j -> 0 <= j -> (1 <= k)%nat -> dl_geom2 lined nl bufs1 bufs2 n1 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  evt asegs (dl0_exit ra sp gp tp (Z_to_bv 64 lined) (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) a4 a5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11
               F fc m lined nl bufs1 bufs2 n1 w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 j) (Z_to_bv 64 j) ONE (Z_to_bv 64 (-2147483648)) s1 (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2)
             a4 a5 (Z_to_bv 64 (w - 1)) (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 3) (Z_to_bv 64 2) ONE (Z_to_bv 64 134217727))
        F (Z_to_bv 64 0x9e5e0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp s1 a1 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lined nl bufs1 bufs2 n1 w bs1 bs2 wl
    HK HJ HK1 GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL.
  { lia. }
  eapply evt_cut.
  { eapply dl0_body; try eassumption. lia. }
  intros ms' PO. unfold dl0_px_end in PO.
  destruct PO as (s1' & a1' & s2' & s3' & s4' & s5' & s6' & m' & bs1' & bs2' & wl' & -> & MU1 & WM1 & MI1 & UB1 & UBL1 & ACCB1 & UC1 & UCL1 & ACCC1 & UL1 & ULL1 & ACCL1).
  clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL.
  pose proof GEO as ((HW & _) & _).
  unfold SHB in *.
  lwalk [0x9e5e0; 0x9e8ec].
  destruct k as [|k].
  - assert (EJ : j + 1 = w - 1) by lia. rewrite EJ in *.
    brT. apply evt_done. unfold dl0_exit. do 7 eexists. exists m', bs1', bs2', wl'. split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
  - brF. eapply evt_cut.
    + eapply (IH (j + 1)) with (bs1 := bs1') (bs2 := bs2') (wl := wl'); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold dl0_exit in PO |- *.
      destruct PO as (s1'' & a1'' & s2'' & s3'' & s4'' & s5'' & s6'' & m'' & bs1'' & bs2'' & wl'' & E & MU' & WM' & R).
      exists s1'', a1'', s2'', s3'', s4'', s5'', s6'', m'', bs1'', bs2'', wl''.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition dl0_end (ra sp gp tp t1 t2 s0 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 bufs2 n1 : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' s1' a0' a1' a2' a3' a4' a5' a6' s2' s3' s4' s5' s6' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1' a0' a1' a2' a3' a4' a5' a6' a7 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9ea60) fc None m' (seg_rom asegs)
    /\ munch (DL0_W lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl.

(* [comment removed for export] *)
Lemma dl0_last : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  dl_geom2 lined nl bufs1 bufs2 n1 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  evt asegs (dl0_end ra sp gp tp t1 t2 s0 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lined nl bufs1 bufs2 n1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) a4 a5 (Z_to_bv 64 (w - 1))
             (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e8ec) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL.
  pose proof GEO as ((HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP)
                     & C0 & C8 & CHI & CSH & CSEG & SEP2 & SEP3). clear GEO.
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (DL0_W lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (lxor3_eq (w - 1 + bufs1)) as LX0.
  pose proof (lxor3_eq (w - 1 + bufs2)) as LX2.
  assert (IDX0 : 0 <= Z.lxor (w - 1 + bufs1) 3 - bufs1 < n1) by (rewrite LX0; clear - HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (IDX2 : 0 <= Z.lxor (w - 1 + bufs2) 3 - bufs2 < n1) by (rewrite LX2; clear - HW WN N4 C8; Z.div_mod_to_equations; lia).
  park_disj.
  (* [comment removed for export] *)
  lwalk [0x9e920; 0x9eab8; 0x9ea88].
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs1 (Z.lxor (w - 1 + bufs1) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (w - 1 + bufs1) 3 - bufs1)) with (Z.lxor (w - 1 + bufs1) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs1) by (split; assumption).
  clear HB WB.
  lwalk [0x9e9f0; 0x9e92c].
  brfork SG.
  - (* [comment removed for export] *)
    lwalk [0x9ea60; 0x9e9f8].
    brfork CL1.
    { apply evt_done. unfold dl0_end. do 14 eexists. exists m, bs1, bs2, wl. split; [reflexivity|].
      repeat (split; [assumption|]). assumption. }
    lwalk [0x9ea38; 0x9eae8; 0x9ea88].
    lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof UCx as [HB WB];
      destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (w - 1 + bufs2) 3 - bufs2) HB ltac:(lia)) as (cv & R) end.
    replace (bufs2 + (Z.lxor (w - 1 + bufs2) 3 - bufs2)) with (Z.lxor (w - 1 + bufs2) 3) in R by lia.
    lstep. clear R HB WB.
    lwalk [0x9ea5c; 0x9eaf4; 0x9ea88].
    remember (Z.lxor (w - 1 + bufs2) 3 - bufs2) as ix2 eqn:EIX2.
    unfold parked in CSH, CSEG, SEP2, SEP3.
    gen_zreg 11. gen_zreg 12. gen_zreg 13.
    arr_sb bufs2 ix2 (Z.lxor (w - 1 + bufs2) 3).
    lwalk [0x9ea60].
    apply evt_done. unfold dl0_end. do 14 eexists.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with UBx : u8arr asegs mm bufs1 ?b1, UCx : u8arr asegs mm bufs2 ?b2, ULx : u32arr asegs mm lined ?wlx |- _ => exists mm, b1, b2, wlx end end.
    split; [reflexivity|]. repeat (split; [assumption|]). assumption.
  - (* [comment removed for export] *)
    do 3 lstep.
    replace (bv_wrap 32 (w - 1)) with (w - 1) by (unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; clear - HW; lia).
    rewrite (Z.shiftr_div_pow2 (w - 1) 5) by (clear; lia). change (2 ^ 5) with 32.
    rewrite (swrap32_small ((w - 1) / 32)) by (clear - HW; Z.div_mod_to_equations; lia).
    replace (((w - 1) / 32) mod 18446744073709551616) with ((w - 1) / 32) by (symmetry; apply Z.mod_small; clear - HW; Z.div_mod_to_equations; lia).
    rewrite (Z.shiftl_mul_pow2 ((w - 1) / 32) 2) by (clear; lia). change (2 ^ 2) with 4.
    replace (lined + (w - 1) / 32 * 4) with (lined + 4 * ((w - 1) / 32)) by (clear; lia).
    assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
    assert (JL : 0 <= (w - 1) / 32 < nl / 4) by (clear - HW WL L4; Z.div_mod_to_equations; lia).
    lwalk [0x9e968; 0x9eacc; 0x9ea88].
    destruct (u32arr_nth wl ((w - 1) / 32) ltac:(lia)) as (dv & NTHD).
    pose proof (u32arr_read asegs m lined wl ((w - 1) / 32) dv _ UL NTHD ltac:(lia) eq_refl) as R.
    lstep. clear R.
    lwalk [0x9e978].
    clear ULL.
    unfold parked in LSH, LSEG, SEP, SEP2.
    gen_zreg 10. gen_zreg 15.
    arr_sw lined ((w - 1) / 32) (lined + 4 * ((w - 1) / 32)).
    lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
    park_disj.
    lwalk [0x9ea60; 0x9e980].
    brfork CL2.
    { apply evt_done. unfold dl0_end. do 14 eexists.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with UBx : u8arr asegs mm bufs1 ?b1, UCx : u8arr asegs mm bufs2 ?b2, ULx : u32arr asegs mm lined ?wlx |- _ => exists mm, b1, b2, wlx end end.
      split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
    lwalk [0x9e9b4; 0x9eadc; 0x9ea88].
    lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof UCx as [HB WB];
      destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (w - 1 + bufs2) 3 - bufs2) HB ltac:(lia)) as (cv & R) end.
    replace (bufs2 + (Z.lxor (w - 1 + bufs2) 3 - bufs2)) with (Z.lxor (w - 1 + bufs2) 3) in R by lia.
    lstep. clear R HB WB.
    lwalk [0x9e9d4; 0x9e9d0].
    cut2f 0x9e9d4 (Z_to_bv 5 11) (Z_to_bv 5 12) (fun u1 _ : word => exists z : Z, u1 = Z_to_bv 64 z).
    { brfork MX1.
      - cut2f_done ltac:(eexists; reflexivity).
      - lstep. cut2f_done ltac:(eexists; reflexivity). }
    lazymatch goal with H : (exists z : Z, ?uu = Z_to_bv 64 z) |- _ => destruct H as (? & EU); subst uu end.
    lwalk [0x9ea5c; 0x9e9ec; 0x9ea88].
    remember (Z.lxor (w - 1 + bufs2) 3 - bufs2) as ix2 eqn:EIX2.
    unfold parked in CSH, CSEG, SEP2, SEP3.
    gen_zreg 11. gen_zreg 12. gen_zreg 13.
    arr_sb bufs2 ix2 (Z.lxor (w - 1 + bufs2) 3).
    lwalk [0x9ea60].
    apply evt_done. unfold dl0_end. do 14 eexists.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with UBx : u8arr asegs mm bufs1 ?b1, UCx : u8arr asegs mm bufs2 ?b2, ULx : u32arr asegs mm lined ?wlx |- _ => exists mm, b1, b2, wlx end end.
    split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.
