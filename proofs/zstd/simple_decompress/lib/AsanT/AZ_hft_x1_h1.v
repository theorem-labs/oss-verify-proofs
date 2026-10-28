(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_seg AZ_hft_x1_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.
Section X1B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT WK wksz FF r : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + 16388).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : art m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Variable POST : machine_state -> Prop.
  (* [comment removed for export] *)
  Local Ltac kx_lia_bf :=
    lazymatch goal with
    | |- context [_ + _ <= _ \/ _] => first [ kx_sep_unhide5 DT WK SPA lo FF; lia | lia | kx_bv_ranges; lia ]
    | |- _ => first [ lia | kx_bv_ranges; lia ]
    end.
  Local Ltac kx_lia ::= kx_lia_bf.
  Local Ltac kxl_lia ::= kx_lia_bf.
  Local Ltac kxa_unpZ ::=
    lazymatch goal with
    | |- unpZ ?mm ?lo1 ?hi1 =>
        first [ kxa_hyp
              | let X := kxk_sbase5 DT WK SPA lo FF lo1 in
                lazymatch goal with
                | U : unpoisoned mm X ?hi0 |- _ => apply (unpoisoned_unpZ mm X hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | match goal with
                | U : unpoisoned mm ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ mm lo0 hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | kxa_unp_hook ]
    end.
  Local Ltac kxl_rng ::=
    first [ kxl_hyp
          | lazymatch goal with
            | |- rng ?RG ?A ?N =>
                let X := kxk_sbase5 DT WK SPA lo FF A in
                lazymatch goal with H : rng RG X ?N0 |- _ => apply (rng_sub' RG X N0 A N H); solve [kx_lia] end
            end
          | lazymatch goal with
            | |- rng ?RG ?A ?N => match goal with H : rng RG ?A0 ?N0 |- _ => apply (rng_sub' RG A0 N0 A N H); solve [kxl_lia_small] end
            end
          | kx_rng ].
  Local Ltac kxa_rng0 ::=
    kxa_norm;
    lazymatch goal with
    | |- rng ?RG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
        first [ let X := kxk_sbase5 DT WK SPA lo FF A in
                lazymatch goal with
                | H : rng RG (shad X) ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n (shad X) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                end
              | match goal with
                | H : rng RG (shad ?A0) ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n (shad A0) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                | H : rng RG ?A0 ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n A0 N0 H);
                    [ rewrite shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                end
              | lazymatch RG with
                | (fun _ _ => True) => split; [unfold KXSHLO; kx_lia | split; [unfold KXSHLO, shspanZ; Z.div_mod_to_equations; lia | intros; exact I]]
                end
              | kxa_rng_hook ]
    end.
  (* [comment removed for export] *)
  Local Ltac x1_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    try match goal with H : art ?mx |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    lazymatch goal with
    | MU : munch _ m5 ?m2 |- _ =>
        pose proof (x1_unp_dtM _ _ _ _ _ _ _ _ _ HY UDT m2 MU) as UDT1;
        pose proof (x1_unp_wkM _ _ _ _ _ _ _ _ _ HY UW m2 MU) as UW1;
        try lazymatch goal with WM : wmono _ m5 m2 |- _ => pose proof (x1_artM _ _ _ _ _ _ _ _ _ HY ART0 m2 MU WM) as ART1 end
    | |- _ => idtac
    end.
  Local Ltac x1_open :=
    open_hx HY; unfold KHIGH in *;
    pose proof (x1_bands _ _ _ _ _ _ _ _ HY) as (BDT & BWK & BSP & BSP2 & B5 & B6 & B7 & BFF);
    assert (RSTA : rng RNG SPA 312) by (lazymatch goal with H : rng RNG lo (SPV - lo) |- _ => eapply rng_sub'; [exact H| lia] end);
    lazymatch goal with H1 : DT + 16388 <= lo \/ SPV <= DT, H2 : WK + wksz <= lo \/ SPV <= WK, H3 : lo <= SPV - 5936, H4 : SPV - 448 <= SPA <= SPV - 416 |- _ =>
      assert (SDSA : DT + 16388 <= SPA \/ SPA + 312 <= DT) by (clear - H1 H3 H4; lia);
      assert (SWSA : WK + wksz <= SPA \/ SPA + 312 <= WK) by (clear - H2 H3 H4; lia) end;
    hide_all_disj; x1_reunp.
  (* [comment removed for export] *)
  Notation KZB := [KZRange SPA (0x10007fff8000 + 5488) (2^47 - 432); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16);
     KZRange DT 0x625000 (2^47 - 16388); KZRange WK 0x625000 (2^47 - 1492); KZRange wksz 1492 (2^32); KZRange (WK + wksz) 0 (2^47);
     KZRange FF 4096 (2^47); KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4; KZDisj DT 16388 SPA 312; KZDisj WK wksz SPA 312; KZDisj DT 16388 WK wksz] (only parsing).
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 0x7fff8000)
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Variables (n SRC : Z) (flags : word).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation FRA0 jA jC jD jB jE := ([CB 80 jA; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); CB 16 jC;
                                    C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 WK); CB 64 jD; CB 80 jB; CB 24 jE; C8 (Z_to_bv 64 FF)]).
  (* [comment removed for export] *)
  Notation ST3 pc mm dtd tl' nbs x5 x6 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST pc mm (Z_to_bv 64 0x962bc) x5 x6 (Z_to_bv 64 WK) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 dtd) (Z_to_bv 64 tl') (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 nbs) (Z_to_bv 64 13) (Z_to_bv 64 (0x7fff8000 + DT / 8)) (Z_to_bv 64 nbs) (Z_to_bv 64 (FF + 48))
        x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma x1_h1A : forall (hw rank dt : list Z) (nbs tl : Z) (fl : Z) (jA jC jD jB jE j3 j5 j6 : list byte)
      (x5 x6 x7 xa2 xa3 xa4 xa5 xa6 xa7 x19 x28 x29 x30 x31 : word),
    mem_inv bsegs m5 ->
    rw_cells bsegs m5 SPA (FRA0 jA jC jD jB jE) ->
    rw_cells bsegs m5 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
    u8arr bsegs m5 DT (map (Z_to_bv 8) dt) -> zlen dt = 16388 -> Forall isbyte dt -> Znth 0 dt = 12 ->
    1 <= tl <= 12 -> 2 <= nbs <= 256 ->
    (11 <= tl -> forall ya0 ya1 : word,
       evtF bsegs RNG POST (ST3 0x96440 m5 (12 + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt) tl nbs x5 x6 ya0 ya1 (Z_to_bv 64 tl) xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31)) ->
    (tl <= 10 -> forall ya1 : word,
       evtF bsegs RNG POST (ST3 0x96324 m5 (12 + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt) 11 nbs x5 x6 (Z_to_bv 64 12) ya1 (Z_to_bv 64 tl) xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (ST 0x962cc m5 (Z_to_bv 64 0x962bc) x5 x6 x7 (Z_to_bv 64 r) (Z_to_bv 64 18446744073709551496) xa2 xa3 xa4 xa5 xa6 xa7
                           (Z_to_bv 64 FF) x19 (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 n)
                           (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31).
  Proof.
    intros until x31; intros MI FR FFC DTC DTLEN DTBY DT0 TLR NBSR K11 KR. x1_open.
    assert (LDT : zlen (map (Z_to_bv 8) dt) = 16388) by (rewrite length_map; exact DTLEN).
    unfold X1FFHDR in FFC.
    kx_autoFLAc (FR, FFC) [KAUnp DT 4] [0x96440; 0x96324; 0x970d8] 40%nat
      (KZB ++ [KZRange tl 1 12; KZRange nbs 2 256])
      [(DT, 16388); (SPA, 312); (FF, 64)] [(DT, 16388); (SPA, 312); (FF, 64)].
    (* [comment removed for export] *)
    all: kx_the_read RD.
    all: rewrite (rdval_u32Zb bsegs m5 DT dt 0 (DT + 0) DTC eq_refl ltac:(lia) ltac:(lia) DTBY) in RD.
    all: change (0 + 1) with 1 in RD; change (0 + 2) with 2 in RD; change (0 + 3) with 3 in RD.
    all: rewrite DT0 in RD; rewrite RD, Z_to_bv_unsigned in *.
    all: pose proof (Forall_Znth _ dt 1 DTBY ltac:(lia)) as B1; pose proof (Forall_Znth _ dt 2 DTBY ltac:(lia)) as B2;
         pose proof (Forall_Znth _ dt 3 DTBY ltac:(lia)) as B3; cbv beta in B1, B2, B3.
    all: assert (L12 : Z.land (bv_wrap 64 (12 + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt)) 255 = 12)
      by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with 18446744073709551616; rewrite Z.mod_small by lia;
          change 255 with (Z.ones 8); rewrite Z.land_ones by lia; change (2^8) with 256; clear - B1 B2 B3; Z.div_mod_to_equations; lia).
    all: rewrite L12 in *.
    all: try (exfalso; clear - KXBR KXBR0 KXBR1 TLR; lia). all: try (exfalso; clear - KXBR KXBR0 TLR; lia). all: try (exfalso; clear - KXBR TLR; lia).
    all: kx_setreg 25 (0x7fff8000 + DT / 8); change (12 + 1) with 13; try (assert (E11 : tl = 11) by lia; subst tl); try (assert (E12 : tl = 12) by lia; subst tl).   (* [comment removed for export] *)
    all: clear RD L12 KXMI; kx_tidy_run.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96440) _ _ _ _) => eapply K11; lia
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96324) _ _ _ _) => eapply KR; lia
         end.
  Qed.
End X1B.
End CANSEC1.
