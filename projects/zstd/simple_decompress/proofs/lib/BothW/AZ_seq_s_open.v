(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation SHB := 2147450880.
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B00 := (Z_to_bv 8 0).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma sq_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0xcb9f8 [C8 (Z_to_bv 64 0xd4300)] /\ rw_cells bsegs m 0xcb9a0 [C8 (Z_to_bv 64 0xd42f8)].
Proof.
  intros m R. split; (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
Definition SQSAVED (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition SQSH00 : list cell :=
  [C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00;
   C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].
Lemma shadow32_c1sQ : forall (m : amem) s,
  rw_cells bsegs m s [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells bsegs m s SQSH00.
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Definition SQSH0 : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1;
   C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8;
   C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].
Definition SQJSH0 : list byte := [BF1; BF1; BF1; BF1].
Definition SQJM : list byte := [BF8; BF8; BF8; BF8; BF8; BF8; BF8; BF8; BF8; BF8; BF8; BF8; BF8; BF8].
Definition SQJSH1 : list byte := [BF3; BF3; BF3; BF3; BF3; BF3; B00; B00; B00; B00; B00; B00; B00; B00].
Lemma sqsh0_blobs : forall (m : amem) s, rw_cells bsegs m s SQSH0 -> rw_cells bsegs m s [CB 4 SQJSH0; CB 14 SQJM; CB 14 SQJSH1].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Definition SQJFH (junk8 : list byte) : list byte :=
  cells_bytes [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x18f4c); C8 (Z_to_bv 64 0x902ac); CB 8 junk8].

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SPV lo : Z).
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPT : SPV + 16 < KEND.
  Hypothesis LOS : lo <= SPV - 400 - 4096.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition SFRB : Z := (SPV - 384) - (SPV - 384) mod 32.
  Lemma sfrb_props : SPV - 400 <= SFRB <= SPV - 384 /\ SFRB mod 32 = 0 /\ (SPV + -384) - (SPV + -384) mod 2^5 = SFRB.
  Proof. unfold SFRB. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma sq_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SPV -> mem_inv bsegs m ->
    rt_shbase m -> rw_cells bsegs m 0xcb9f8 [C8 (Z_to_bv 64 0xd4300)] -> rw_cells bsegs m 0xcb9a0 [C8 (Z_to_bv 64 0xd42f8)] ->
    rw_cells bsegs m 0xd4300 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA,
        ms' = MS (mkR (Z_to_bv 64 0x90330) (Z_to_bv 64 SFRB) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 SFRB)
                     (Z_to_bv 64 192) (Z_to_bv 64 0xd42f8) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     a2 a4 a3 a1 a0 a5 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 0x3f234) fc None m' (seg_rom bsegs)
        /\ munch [(SPV - 400, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPV + -104) (SQSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ rw_cells bsegs m' SFRB [CB 280 jA]
        /\ stk bsegs m' lo SFRB /\ stk bsegs m' (SFRB + 280) (SPV + -104))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0x902ac) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI SHBm GOT1 GOT2 SUA.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof sfrb_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SPV - 400, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 280%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
    release_frame FR1 ST (SPV + -104).
    destruct (stk_split bsegs _ lo (SFRB + 280) (SPV + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SFRB + 280) 280 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 280) with 280 in STL, FRA. replace (SFRB + 280 - 280) with SFRB in STL, FRA by lia.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT1 GOT2.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    apply evtF_done.
    eexists _, jA. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  (* [comment removed for export] *)
  Lemma sq_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs11 : word) m (FF FLG : Z)
      (j0 j1 j2 : word) (junk jA : list byte),
    rw_cells bsegs m SFRB [CB 280 jA] -> stk bsegs m lo SFRB ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    mem_inv bsegs m ->
    ablk FF (FF + 256) -> FF + 256 <= ATOP -> FF mod 256 = 0 -> rng RNG FF 256 -> rng RNG (shad FF) 32 ->
    evtF bsegs RNG (fun ms' => exists m' jds jp j144 j8 jA1 jA2,
        ms' = MS (mkR (Z_to_bv 64 0x90330) (Z_to_bv 64 SFRB) gp tp x5 (Z_to_bv 64 FF) x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SFRB)
                     (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 0x18f4c) (Z_to_bv 64 0x902ac) (Z_to_bv 64 (Z.shiftr FF 3))
                     (Z_to_bv 64 18446744073709551608) xs7 (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) (Z_to_bv 64 FF)
                     xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 SHB) xs11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x90408) fc None m' (seg_rom bsegs)
        /\ munch [(FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32); (SFRB, SFRB + 280)] m m'
        /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' SFRB [CB 240 jA1; C8 (Z_to_bv 64 FF); CB 32 jA2] /\ stk bsegs m' lo SFRB
        /\ rw_cells bsegs m' FF [CB 32 (SQJFH j8); CB 88 jds; CB 24 jp; CB 104 j144; C8 (Z_to_bv 64 FLG)]
        /\ rw_cells bsegs m' (Z.shiftr FF 3 + SHB) [CB 4 SQJSH0; CB 14 SQJM; CB 14 SQJSH1])
      (MS (mkR (Z_to_bv 64 0x90330) (Z_to_bv 64 SFRB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SFRB)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 SHB) xs11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x90330) fc None m (seg_rom bsegs)).
  Proof.
    intros until jA. intros FRA STL FFC SHF MI FH FC F256 RF RSF.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof sfrb_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    apply shadow32_c1sQ in SHF. unfold SQSH00 in SHF. replace (shad FF) with (Z.shiftr FF 3 + SHB) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : SHB <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    (* [comment removed for export] *)
    pose proof FFC as [[WFJ _] _]. cbn [cells_wf cell_wf] in WFJ. destruct WFJ as (_ & _ & _ & LJ & _).
    apply (rw_cells_split_CB bsegs _ _ [C8 j0; C8 j1; C8 j2] 224 _ [C8 (Z_to_bv 64 FLG)] [8; 88; 24; 104]%nat) in FFC; [| reflexivity].
    cbn [mk_CB_cells app] in FFC.
    pose proof (munch_refl [(FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32); (SFRB, SFRB + 280)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    (* [comment removed for export] *)
    pose proof FRA as [[WFA _] _]. cbn [cells_wf cell_wf] in WFA. destruct WFA as (LJA & _).
    apply (rw_cells_split_CB bsegs _ _ [] 280 _ [] [240; 8; 32]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 3 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    do 4 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    do 12 zstep.                                  (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    do 2 zstep.                                   (* [comment removed for export] *)
    do 2 zstep.                                   (* [comment removed for export] *)
    apply evtF_done.
    lazymatch type of FRA with rw_cells _ ?mf _ [CB 240 ?ja1; _; CB 32 ?ja2] =>
      exists mf, (take 88 (drop 8 junk)), (take 24 (drop 88 (drop 8 junk))), (take 104 (drop 24 (drop 88 (drop 8 junk)))), (take 8 junk), ja1, ja2 end.
    split; [reflexivity|]. split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|]. split; [exact MI|].
    split; [exact FRA|]. split; [exact STL|].
    split.
    { lazymatch type of FFC with rw_cells _ ?m0 _ _ => change (rw_cells bsegs m0 FF ([] ++ [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 102220); C8 (Z_to_bv 64 590508); CB 8 (take 8 junk)] ++
                                    [CB 88 (take 88 (drop 8 junk)); CB 24 (take 24 (drop 88 (drop 8 junk))); CB 104 (take 104 (drop 24 (drop 88 (drop 8 junk)))); C8 (Z_to_bv 64 FLG)])) in FFC;
      apply (rw_cells_merge bsegs m0 FF) in FFC; cbn [app cells_size csize Nat.add length] in FFC; exact FFC end. }
    apply sqsh0_blobs. exact SHF.
  Qed.
End S.
End CANSEC1.
