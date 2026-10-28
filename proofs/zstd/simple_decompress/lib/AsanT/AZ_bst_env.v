(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AZ_blk_iface AZ_blk_iface2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Notation zlen l := (Z.of_nat (length l)).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF2 := (Z_to_bv 8 18446744073709551602).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B04 := (Z_to_bv 8 4).
Notation B00 := (Z_to_bv 8 0).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma bs_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] /\ rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)].
Proof.
  intros m R. split; (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
Definition BSAVED (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition BSH00 : list cell :=
  [C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00;
   C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].
Lemma shadow32_c1sB : forall (m : amem) s,
  rw_cells bsegs m s [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells bsegs m s BSH00.
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Definition BSH0 : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B04; C1 BF2; C1 BF8; C1 BF2;
   C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8; C1 BF8;
   C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 B00; C1 B00; C1 B00; C1 B00].

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SPV lo : Z).
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPT : SPV + 16 < KEND.
  Hypothesis LOS : lo <= SPV - 208 - 4096.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition BSPA : Z := (SPV - 192) - (SPV - 192) mod 32.
  Lemma bspa_props : SPV - 208 <= BSPA <= SPV - 192 /\ BSPA mod 32 = 0 /\ (SPV + -192) - (SPV + -192) mod 2^5 = BSPA.
  Proof. unfold BSPA. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma bs_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SPV -> mem_inv bsegs m ->
    rt_shbase m -> rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] -> rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)] ->
    rw_cells bsegs m 0xcfd00 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA jB,
        ms' = MS (mkR (Z_to_bv 64 0x88d74) (Z_to_bv 64 BSPA) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 BSPA)
                     (Z_to_bv 64 224) (Z_to_bv 64 0xcfcf8) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     s2 a2 s4 a3 t5 s7 a5 a6 (Z_to_bv 64 SHB) t4 t3 t4 t5 t6)   (* [comment removed for export] *)
                 FR (Z_to_bv 64 0x3f190) fc None m' (seg_rom bsegs)
        /\ munch [(SPV - 208, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPV + -104) (BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ rw_cells bsegs m' BSPA [CB 16 jA; C8 a7; C8 t3; C8 a0; C8 t6; C8 a4; C8 a1; CB 24 jB]   (* [comment removed for export] *)
        /\ stk bsegs m' lo BSPA /\ stk bsegs m' (BSPA + 88) (SPV + -104))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0x88cd8) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI SHBm GOT1 GOT2 SUA.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof bspa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SPV - 208, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
    release_frame FR1 ST (SPV + -104).
    destruct (stk_split bsegs _ lo (BSPA + 88) (SPV + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (BSPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88 in STL, FRA. replace (BSPA + 88 - 88) with BSPA in STL, FRA by lia.
    apply (rw_cells_split_CB bsegs _ _ [] 88 _ [] [16; 8; 8; 8; 8; 8; 8; 24]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT1 GOT2.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  (* [comment removed for export] *)
  Lemma bs_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs11 : word) m (FF FLG : Z)
      (j0 j1 j2 c16 c24 c32 c40 c48 c56 : word) (junk jA jB : list byte),
    rw_cells bsegs m BSPA [CB 16 jA; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; CB 24 jB] -> stk bsegs m lo BSPA ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    mem_inv bsegs m ->
    ablk FF (FF + 256) -> FF + 256 <= ATOP -> FF mod 256 = 0 -> rng RNG FF 256 -> rng RNG (shad FF) 32 ->
    evtF bsegs RNG (fun ms' => exists m' jB' j3 j4,
        ms' = MS (mkR (Z_to_bv 64 0x88d74) (Z_to_bv 64 BSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 BSPA)
                     (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 0x88cd8)
                     (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 4) x16 x17
                     (Z_to_bv 64 FF) xs3 (Z_to_bv 64 FF) xs5 xs6 (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) xs8 xs9 (Z_to_bv 64 SHB) xs11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x88e68) fc None m' (seg_rom bsegs)
        /\ munch [(BSPA + 80, BSPA + 88); (FF, FF + 24); (FF + 32, FF + 36); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)] m m'
        /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' BSPA [CB 16 jA; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; CB 16 jB'; C8 (Z_to_bv 64 FF)] /\ stk bsegs m' lo BSPA
        /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a046); C8 (Z_to_bv 64 0x88cd8); CB 8 j3; C4 xs5; CB 212 j4; C8 (Z_to_bv 64 FLG)]
        /\ rw_cells bsegs m' (Z.shiftr FF 3 + SHB) BSH0)
      (MS (mkR (Z_to_bv 64 0x88d74) (Z_to_bv 64 BSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 BSPA)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 SHB) xs11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x88d74) fc None m (seg_rom bsegs)).
  Proof.
    intros until jB. intros FRA STL FFC SHF MI FH FC F256 RF RSF.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof bspa_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    apply shadow32_c1sB in SHF. unfold BSH00 in SHF. replace (shad FF) with (Z.shiftr FF 3 + SHB) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : SHB <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(BSPA + 80, BSPA + 88); (FF, FF + 24); (FF + 32, FF + 36); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 7 zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
    do 4 zstep.                              (* [comment removed for export] *)
    zstep.                                   (* [comment removed for export] *)
    do 8 zstep.                              (* [comment removed for export] *)
    do 6 zstep.                              (* [comment removed for export] *)
    do 6 zstep.                              (* [comment removed for export] *)
    zstep.                                   (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _, _. split; [reflexivity|]. split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [eassumption|].
    split; [exact FRA|]. split; [exact STL|]. split; [exact FFC| unfold BSH0; exact SHF].
  Qed.
End S.
End CANSEC1.
