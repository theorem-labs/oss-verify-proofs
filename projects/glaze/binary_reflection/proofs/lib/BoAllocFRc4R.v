(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoAllocFRun.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3.
Export OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RUN12.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S p ra0 tp tsdp P top bot : word) (T tctx n q32 : Z) (D : nat).
  Variables (iab : byte) (pim : list byte) (h1 h2 h3 : byte) (hv : word) (bf0 bf1 : list byte).
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis HR10 : getr R 10 = p.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp : (AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584 /\ U p mod 16 = 0)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GpT : (U p + 8 <= T \/ T + 4096 <= U p - 16)%Z.      (* [comment removed for export] *)
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx) /\ (tctx + 4096 <= U p - 16 \/ U p + 8 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 40)%Z.
  Hypothesis Gq32 : (U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis C_iaflag : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 1 = Some [iab].
  Hypothesis C_iab : U iab <> 0%Z.
  Hypothesis C_pim : rdn BSEGS mem (Z_to_bv 64 (0x10f3c8 + 8 * q32)) 8 = Some pim.
  Hypothesis C_pim0 : bytes_le_to_Z pim = 0%Z.
  Hypothesis C_mcs : rdn BSEGS mem (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS mem (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn BSEGS mem (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_unw : rdn BSEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_unw_ok : store_ok BSEGS mem (at_ thr 3168) 1 = true.
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P : rdn BSEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn BSEGS mem (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS mem (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_sw : rdn BSEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn BSEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn BSEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_hook : rdn BSEGS mem (Z_to_bv 64 0x19fc88) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_h1 : h1 = Z_to_bv 8 0x11 \/ h1 = Z_to_bv 8 0x91.
  Hypothesis C_hdr : rdn BSEGS mem (at_ p (-16)) 4 = Some [Z_to_bv 8 2; h1; h2; h3].
  Hypothesis C_hv : bytes_le_to_Z [Z_to_bv 8 2; h1; h2; h3] = U hv.
  Hypothesis C_hdr_ok : store_ok BSEGS mem (at_ p (-16)) 4 = true.
  Hypothesis C_p_ok : store_ok BSEGS mem p 8 = true.
  Hypothesis C_nhi : rdn BSEGS mem (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS mem (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_f0 : rdn BSEGS mem (Z_to_bv 64 (T + 2824)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn BSEGS mem (Z_to_bv 64 (T + 2832)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_stat_ok : store_ok BSEGS mem (Z_to_bv 64 (T + 2824)) 16 = true.
  Hypothesis C_T0 : rdn BSEGS mem (Z_to_bv 64 T) 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn BSEGS mem (Z_to_bv 64 (tctx + 8)) 4 = Some (LE4 0).
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.

  #[local] Abbreviation M3 := (fr_P1 mem S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)).

  Theorem run_p12 :
    exists r MU (sz : Z) (bsz : list byte),
      msteps BSEGS (mkst R (0x6ed6c : word) mem rom) (mkst r (0x8f4f0 : word) (fr_P2 MU S p (getr R 22) T n h1 h2 h3 bf0 bf1) rom)
      /\ getr r 1 = Z_to_bv 64 0x50838 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = at_ p (-16) /\ getr r 9 = at_ S (-2128)
      /\ getr r 10 = at_ S (-2112) /\ getr r 11 = Z_to_bv 64 (bytes_le_to_Z bsz) /\ getr r 18 = Z_to_bv 64 0x10ab58
      /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = thr /\ getr r 21 = at_ S (-81) /\ getr r 22 = getr R 22
      /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 23 = getr R 23 /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27
      /\ (1 <= sz <= 30)%Z /\ (sz <= 2 + Z.of_nat D)%Z
      /\ (forall x : word, MU x <> M3 x ->
            (U S - 2272 <= U x < U S - 2128)%Z \/ (U S - 2120 <= U x < U S - 1872)%Z \/ (U S - 72 <= U x < U S - 64)%Z \/ U x = (T + 3168)%Z)
      /\ mem_grows M3 MU
      /\ rdn BSEGS MU (at_ S (-2120)) 4 = Some (LE4 sz) /\ rdn BSEGS MU (at_ S (-2112)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))
      /\ rdn BSEGS MU (at_ thr 3168) 1 = Some [Z_to_bv 8 0]
      /\ rdn BSEGS MU (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat
      /\ rdn BSEGS MU (at_ S (-2116)) 4 = Some (LE4 0).                                  (* [comment removed for export] *)
  Proof using Hfpc C_tid C_T0 C_stat_ok L_f1 C_f1 L_f0 C_f0 C_nlo C_nhi C_p_ok C_hdr_ok C_hv C_hdr C_h1 C_hook C_bot C_top C_sw C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_unw_ok C_unw C_inited C_fum C_gcf C_mcs C_pim0 C_pim C_iab C_iaflag Hstk Gq32 Gn Gbot Gtop GP Gtsdp Gtp Gctx GpT GT Gp GS HR10 HR4 HR2 HR1 hv pim iab q32 tctx bot top P tsdp.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    pose proof GS as (GS1 & GS2 & GS3). pose proof Gp as (Gp1 & Gp2 & Gp3). pose proof Gq32 as (Q1 & Q2 & Q3).
    (* [comment removed for export] *)
    destruct (icpt_pro mem rom S ra0 p R HR1 HR2 HR10 ltac:(lia)) as (r1 & RUN1 & A1 & A2 & A8 & A9 & A18 & A4 & A3 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    { eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (M1 := fr_icpt mem S ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) in RUN1.
    assert (OUT1 : forall x : word, (U x < U S - 56 \/ U S <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1, fr_icpt in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GR1 : mem_grows mem M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1, fr_icpt in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    Ltac x1 OUT H := eapply rd_same; [intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H].
    (* [comment removed for export] *)
    destruct (p1_blkA M1 rom S ra0 p (getr R 19) r1 iab pim A1 A2 A8 A9 A18 A19 ltac:(lia) GS2) with (q32 := q32)
      as (r2 & RUN2 & B2 & B8 & B9 & B18 & B4 & B3 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
    { eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { x1 OUT1 C_iaflag. }
    { exact C_iab. }
    { exact Q1. } { exact Q2. } { exact Q3. }
    { x1 OUT1 C_pim. }
    { exact C_pim0. }
    (* [comment removed for export] *)
    assert (B4' : getr r2 4 = getr R 4) by (rewrite B4; exact A4).
    assert (B3' : getr r2 3 = getr R 3) by (rewrite B3; exact A3).
    assert (B20' : getr r2 20 = getr R 20) by (rewrite B20; exact A20).
    assert (B21' : getr r2 21 = getr R 21) by (rewrite B21; exact A21).
    assert (B22' : getr r2 22 = getr R 22) by (rewrite B22; exact A22).
    assert (B23' : getr r2 23 = getr R 23) by (rewrite B23; exact A23).
    assert (B24' : getr r2 24 = getr R 24) by (rewrite B24; exact A24).
    assert (B25' : getr r2 25 = getr R 25) by (rewrite B25; exact A25).
    assert (B26' : getr r2 26 = getr R 26) by (rewrite B26; exact A26).
    assert (B27' : getr r2 27 = getr R 27) by (rewrite B27; exact A27).
    destruct (run_from_6ee44 mem rom R S p ra0 tp tsdp P top bot T tctx n q32 D h1 h2 h3 hv bf0 bf1 r2)
      as (r & MU & sz & bsz & RUNT & REST).
    all: try assumption.
    all: let k := numgoals in guard k = 1.
    exists r, MU, sz, bsz. split; [| exact REST].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [| exact RUNT]. subst M1. exact RUN2.
  Qed.
End RUN12.


End FPGen.
End BoAllocFRun.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFMem.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 BoAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.BoAllocFRun3.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Lemma wbytes_diff_w : forall (m : word -> option byte) (a x : word) bs,
  wbytes m a bs x <> m x -> U a + Z.of_nat (length bs) <= 2 ^ 64 -> U a <= U x < U a + Z.of_nat (length bs).
Proof.
  intros m a x bs NE Hb. destruct (Z_lt_dec (U x) (U a)) as [L|L].
  - exfalso. apply NE. apply wbytes_outside; [exact Hb | left; exact L].
  - destruct (Z_lt_dec (U x) (U a + Z.of_nat (length bs))) as [L2|L2]; [lia|].
    exfalso. apply NE. apply wbytes_outside; [exact Hb | right; lia].
Qed.

(* [comment removed for export] *)
Ltac lside := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
(* [comment removed for export] *)
Ltac peel1 NE fin :=
  lazymatch type of NE with
  | wbytes ?m ?a ?bs ?x <> _ =>
      destruct (decide (wbytes m a bs x = m x)) as [EQ__|NEQ__];
      [ rewrite EQ__ in NE; clear EQ__
      | clear NE; apply wbytes_diff_w in NEQ__; [ revert NEQ__; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length;
          (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; intros NEQ__; fin | lside ] ]
  end.
(* [comment removed for export] *)
Ltac rd_layers := (lazymatch goal with |- ?G => let G' := eval unfold fr_P3, fr_PS, fr_P2, fr_P1, fr_c2, fr_c1, fr_b5a, fr_b4b, fr_b4a, fr_b3, fr_b2, fr_b1, fr_p1, fr_ia, fr_icpt, ps_frame in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); repeat (wd_rdstep rd8_side).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P1MEM.
  Variables (mem : word -> option byte) (S p ra0 s0 s1 s2 s3 s4 s5 : word).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  #[local] Abbreviation M3 := (fr_P1 mem S p ra0 s0 s1 s2 s3 s4 s5).

  Lemma fr_P1_out : forall x : word, (U x < U S - 2176 \/ U S <= U x) -> M3 x = mem x.
  Proof using GS.
    intros x Hx. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma fr_P1_foot : forall x : word, M3 x <> mem x -> U S - 2176 <= U x < U S.
  Proof using GS.
    intros x NE. destruct (Z_lt_dec (U x) (U S - 2176)); [exfalso; apply NE; apply fr_P1_out; lia|].
    destruct (Z_lt_dec (U x) (U S)); [lia|]. exfalso; apply NE; apply fr_P1_out; lia.
  Qed.
  Lemma fr_P1_grows' : mem_grows mem M3.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Lemma fr_P1_i0 : rdn BSEGS M3 (at_ S (-8)) 8 = Some (LE8 ra0).   Proof using GS. pose proof (u64_range S). rd_layers. Qed.
  Lemma fr_P1_i1 : rdn BSEGS M3 (at_ S (-16)) 8 = Some (LE8 s0).   Proof using GS. pose proof (u64_range S). first [clear - GS | idtac]; (rd_layers). Qed.
  Lemma fr_P1_i2 : rdn BSEGS M3 (at_ S (-24)) 8 = Some (LE8 s1).   Proof using GS. pose proof (u64_range S). rd_layers. Qed.
  Lemma fr_P1_i3 : rdn BSEGS M3 (at_ S (-32)) 8 = Some (LE8 s2).   Proof using GS. pose proof (u64_range S). rd_layers. Qed.
  Lemma fr_P1_i4 : rdn BSEGS M3 (at_ S (-40)) 8 = Some (LE8 s3).   Proof using GS. pose proof (u64_range S). rd_layers. Qed.
  Lemma fr_P1_i5 : rdn BSEGS M3 (at_ S (-48)) 8 = Some (LE8 s4).   Proof using GS. pose proof (u64_range S). rd_layers. Qed.
  Lemma fr_P1_i6 : rdn BSEGS M3 (at_ S (-56)) 8 = Some (LE8 s5).   Proof using GS. pose proof (u64_range S). rd_layers. Qed.
End P1MEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P2MEM.
  Variables (MU : word -> option byte) (S p x22 : word) (T n : Z) (h1 h2 h3 : byte) (bf0 bf1 : list byte).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gp : AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis GpT : U p + 8 <= T \/ T + 4096 <= U p - 16.
  Lemma TSB_P2MEM : hideW ((T + 4096 <= 0x7fff8000)%Z \/ (0x10007fff8000 <= T)%Z).
  Proof using GT S. pose proof GT as X. unfold hideW in X |- *. lia. Qed.
  #[local] Abbreviation M11 := (fr_P2 MU S p x22 T n h1 h2 h3 bf0 bf1).

  Lemma fr_P2_outside : forall a : word,
    (U a < U S - 2216 \/ U S - 2128 <= U a) -> (U a < U p - 16 \/ U p - 12 <= U a) -> (U a < U p \/ U p + 8 <= U a) ->
    (U a < T + 2824 \/ T + 2840 <= U a) -> M11 a = MU a.
  Proof using GT Gp GS. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1.
    intros a A1 A2 A3 A4. pose proof (u64_range S). pose proof (u64_range p). (lazymatch goal with |- ?G => let G' := eval unfold fr_P2, fr_b5a, fr_b4b, fr_b4a, fr_b3, fr_b2, fr_b1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; unorm; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma fr_P2_foot : forall a : word, M11 a <> MU a ->
    (U S - 2216 <= U a < U S - 2128) \/ (U p - 16 <= U a < U p - 12) \/ (U p <= U a < U p + 8) \/ (T + 2824 <= U a < T + 2840).
  Proof using GS GT Gp GpT. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1.
    intros a NE.
    destruct (decide (U S - 2216 <= U a < U S - 2128)) as [wcY|?]; [clear - wcY; tauto|].
    destruct (decide (U p - 16 <= U a < U p - 12)) as [wcY|?]; [clear - wcY; tauto|].
    destruct (decide (U p <= U a < U p + 8)) as [wcY|?]; [clear - wcY; tauto|].
    destruct (decide (T + 2824 <= U a < T + 2840)) as [wcY|?]; [clear - wcY; tauto|].
    exfalso. apply NE. apply fr_P2_outside; lia.
  Qed.
  Lemma fr_P2_grows : mem_grows MU M11.
  Proof using GT. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1. (lazymatch goal with |- ?G => let G' := eval unfold fr_P2, fr_b5a, fr_b4b, fr_b4a, fr_b3, fr_b2, fr_b1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Lemma fr_P2_hdr : M11 (at_ p (-16)) = Some (Z_to_bv 8 3) /\ M11 (at_ p (-15)) = Some h1
                    /\ M11 (at_ p (-14)) = Some h2 /\ M11 (at_ p (-13)) = Some h3.
  Proof using GpT GT Gp GS. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1.
    pose proof (u64_range S). pose proof (u64_range p). (lazymatch goal with |- ?G => let G' := eval unfold fr_P2, fr_b5a, fr_b4b, fr_b4a, fr_b3, fr_b2, fr_b1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    Ltac hdr_byte K := rewrite !wbytes_outside by lside; rewrite wbytes_inside by lside;
                       match goal with |- Some (nth (Z.to_nat ?e) _ _) = _ => replace e with K by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia) end; reflexivity.
    split; [hdr_byte 0|]. split; [hdr_byte 1|]. first [clear - GpT GT Gp GS | idtac]; (split; [hdr_byte 2 | hdr_byte 3]).
  Qed.

  (* [comment removed for export] *)
  Lemma fr_P2_q0 : rdn BSEGS M11 (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).  Proof using GT GS. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.
  Lemma fr_P2_q1 : rdn BSEGS M11 (at_ S (-2144)) 8 = Some (LE8 S).                    Proof using GT GS. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.
  Lemma fr_P2_q2 : rdn BSEGS M11 (at_ S (-2152)) 8 = Some (LE8 p).                    Proof using GT GS. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.
  Lemma fr_P2_q3 : rdn BSEGS M11 (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)).  Proof using GT GS. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.
  Lemma fr_P2_q4 : rdn BSEGS M11 (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).        Proof using GT GS. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.
  Lemma fr_P2_q5 : rdn BSEGS M11 (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).       Proof using GT GS. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.

  (* [comment removed for export] *)
  Lemma fr_P2_rdn_out : forall (a : word) (k : nat),
    U a + Z.of_nat k <= 2 ^ 64 ->
    (U a + Z.of_nat k <= U S - 2216 \/ U S - 2128 <= U a) -> (U a + Z.of_nat k <= U p - 16 \/ U p + 8 <= U a) ->
    (U a + Z.of_nat k <= T + 2824 \/ T + 2840 <= U a) ->
    rdn BSEGS M11 a k = rdn BSEGS MU a k.
  Proof using GpT GT Gp GS. pose proof TSB_P2MEM as TSB1; unfold hideW in TSB1.
    intros a k Hk A1 A2 A3. apply rdn_ext; [exact Hk|]. intros x Hx. apply fr_P2_outside; lia.
  Qed.
End P2MEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P3MEM.
  Variables (memD : word -> option byte) (S p x22 : word) (T n n8 id last cnt bsz qb : Z).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gp : AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis Gn8 : 8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40.
  Hypothesis Glast : 0x10007fff8000 <= last /\ last + 8192 <= U S - 3584.
  Hypothesis GlastT : last + 8192 <= T \/ T + 4096 <= last.
  Hypothesis Glastp : last + 8192 <= U p - 16 \/ U p + n8 <= last.
  Hypothesis GpT : U p + n8 <= T \/ T + 4096 <= U p - 16.
  Hypothesis Gcnt : 0 <= cnt < 1021.
  Lemma TSB_P3MEM : hideW ((T + 4096 <= 0x7fff8000)%Z \/ (0x10007fff8000 <= T)%Z).
  Proof using GT n8 p S. pose proof GT as X. unfold hideW in X |- *. lia. Qed.
  Lemma PSB_P3MEM : hideW ((U p + n8 <= 0x7fff7000)%Z \/ (0x10007fff8000 + 16 <= U p)%Z).
  Proof using Gp S. pose proof Gp as X. unfold hideW in X |- *. lia. Qed.
  #[local] Abbreviation M13 := (fr_P3 memD S p x22 T n n8 id last cnt bsz qb).

  Lemma shlen8 : shlen (Z_to_bv 64 n8) = n8 / 8.
  Proof using Gn8 GT Gp T p S. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. reflexivity. Qed.


  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pd8 : 8 * (U p / 8) = U p /\ 8 * (n8 / 8) = n8 /\ AIMGHI / 8 <= U p / 8 /\ U p / 8 + n8 / 8 <= 2 ^ 44.
  Proof using Gcnt GpT Glastp GlastT Glast Gn8 GT Gp GS cnt last T x22 S memD. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). Z.div_mod_to_equations. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Ltac lside3 := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length, ?shlen8; rewrite ?Z2Nat.id by lia;
                 (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold shad, at_ in G in change_no_check G' end); wd_ulia.

  Lemma fr_P3_outside : forall a : word,
    (U a < U S - 2264 \/ U S - 2128 <= U a) -> (U a < U p \/ U p + 8 <= U a) ->
    (U a < SB + U p / 8 \/ SB + U p / 8 + n8 / 8 <= U a) ->
    (U a < last + 8 \/ last + 24 <= U a) -> (U a < last + 24 + 8 * cnt \/ last + 32 + 8 * cnt <= U a) ->
    (U a < T + 104 \/ T + 112 <= U a) -> M13 a = memD a.
  Proof using Gcnt GpT Glastp GlastT Glast Gn8 GT Gp GS. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1.
    intros a A1 A2 A3 A4 A5 A6. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8. unfold SB in *.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3, fr_PS, fr_c2, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside by (first [clear - GT GS A6 Gcnt Glast A5 A4 A1 H1 Gn8 Gp A3 A2 | idtac]; lside3). reflexivity.
  Qed.
  Lemma fr_P3_foot : forall a : word, M13 a <> memD a ->
    (U S - 2264 <= U a < U S - 2128) \/ (U p <= U a < U p + 8) \/ (SB + U p / 8 <= U a < SB + U p / 8 + n8 / 8)
    \/ (last + 8 <= U a < last + 24) \/ (last + 24 + 8 * cnt <= U a < last + 32 + 8 * cnt) \/ (T + 104 <= U a < T + 112).
  Proof using GS GT Gcnt Glast GlastT Glastp Gn8 Gp GpT. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1.
    intros a NE.
    destruct (decide (U S - 2264 <= U a < U S - 2128)) as [wcY|?]; [clear - wcY; tauto|].
    destruct (decide (U p <= U a < U p + 8)) as [wcY|?]; [clear - wcY; tauto|].
    destruct (decide (SB + U p / 8 <= U a < SB + U p / 8 + n8 / 8)) as [wcY|?]; [clear - wcY; tauto|].
    destruct (decide (last + 8 <= U a < last + 24)) as [wcY|?]; [clear - wcY; tauto|].
    destruct (decide (last + 24 + 8 * cnt <= U a < last + 32 + 8 * cnt)) as [wcY|?]; [clear - wcY; tauto|].
    destruct (decide (T + 104 <= U a < T + 112)) as [wcY|?]; [clear - wcY; tauto|].
    exfalso. apply NE. apply fr_P3_outside; lia.
  Qed.
  Lemma fr_P3_grows : mem_grows memD M13.
  Proof using GT Gp. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold fr_P3, fr_PS, fr_c2, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Lemma fr_P3_bsz : rdn BSEGS M13 (Z_to_bv 64 (last + 8)) 8 = Some (LE8 (Z_to_bv 64 (bsz + n))).
  Proof using Gcnt GpT Glastp GlastT Glast Gn8 GT Gp GS. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.
  Lemma fr_P3_cnt : rdn BSEGS M13 (Z_to_bv 64 (last + 16)) 8 = Some (LE8 (Z_to_bv 64 (cnt + 1))).
  Proof using Gcnt GpT Glastp GlastT Glast Gn8 GT Gp GS. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.
  Lemma fr_P3_slot : rdn BSEGS M13 (Z_to_bv 64 (last + 24 + 8 * cnt)) 8 = Some (LE8 (at_ p (-16))).
  Proof using Gcnt GpT Glastp GlastT Glast Gn8 GT Gp GS. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.
  Lemma fr_P3_qb : rdn BSEGS M13 (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (qb + n))).
  Proof using Gn8 GT Gp GS. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). rd_layers. Qed.

  (* [comment removed for export] *)
  Lemma fr_P3_shadow : forall i, 0 <= i < n8 / 8 -> M13 (Z_to_bv 64 (SB + U p / 8 + i)) = Some (Z_to_bv 8 0xfd).
  Proof using Gcnt GpT Glastp GlastT Glast Gn8 GT Gp GS. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1.
    intros i Hi. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8. unfold SB in *.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3, fr_PS, fr_c2 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside by (first [clear - GT GS H1 Hi TSB1 Gcnt Glast Gp Gn8 | idtac]; lside3).
    rewrite wbytes_inside by lside3.
    f_equal. rewrite nth_repeat_lt; [(lazymatch goal with |- ?G => let G' := eval unfold cbyte in G in change_no_check G' end); unorm; reflexivity|].
    rewrite shlen8. (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). unorm. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_P3_hdr16 : M13 (at_ p (-16)) = memD (at_ p (-16)).
  Proof using Gcnt GpT Glastp GlastT Glast Gn8 GT Gp GS. pose proof TSB_P3MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3MEM as PSB1; unfold hideW in PSB1.
    pose proof (u64_range S). pose proof (u64_range p). pose proof pd8.
    apply fr_P3_outside; (lazymatch goal with |- ?G => let G' := eval unfold SB, at_ in G in change_no_check G' end); wd_ulia.
  Qed.
End P3MEM.
End BoAllocFMem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_81fbc_82b14.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc4a.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_81fbc_82b14.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Ltac famoA F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_amoadd_d with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
      | rd_addr Hr | exact Hv | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Definition fr_dlf (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2408)) (LE8 ra0))
    (at_ S (-2416)) (LE8 s0v))
    (at_ S (-2424)) (LE8 s1v))
    (at_ S (-2432)) (LE8 s2v))
    (at_ S (-2440)) (LE8 s3v))
    (at_ S (-2448)) (LE8 s4v).
#[local] Hint Unfold fr_dlf : asfr.

(* [comment removed for export] *)
Definition fr_drn (mem : word -> option byte) (S : word) (pcz cnt' : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2456)) (LE8 (Z_to_bv 64 0x4ee58)))
    (at_ S (-2472)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2464)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2504)) (LE8 (Z_to_bv 64 0x10ab58)))
    (at_ S (-2496)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2488)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2480)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 pcz) (LE4 cnt').
#[local] Hint Unfold fr_drn : asfr.

Section DLFHEAD.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T c pz mx : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2400).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (T + 208).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 0x10ab58.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 pz.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hmx : (2 <= mx <= 16)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2512)) 112 = true.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Rmx : rdn BSEGS mem (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis Rcnt : rdn BSEGS mem (Z_to_bv 64 pc_) 4 = Some (LE4 mx).          (* [comment removed for export] *)

  #[local] Abbreviation n := (mx / 2)%Z.
  #[local] Abbreviation M1 := (fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2)).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma dlf_facts : (1 <= mx / 2 <= 8 /\ mx - mx / 2 >= 1 /\ mx * 2 ^ 32 / 2 ^ 32 = mx)%Z.
  Proof using Hmx HT T s4v S rom. split; [lia|]. split; [lia|]. rewrite Z.div_mul by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma dlf_drn_head :
    exists r, msteps BSEGS (mkst regs (0x4eca8 : word) mem rom) (mkst r (0x4f1e0 : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x4f0a0 /\ getr r 2 = at_ S (-2512) /\ getr r 10 = Z_to_bv 64 0x10ab58 /\ getr r 11 = at_ S (-2504)
      /\ getr r 13 = Z_to_bv 64 c /\ getr r 14 = Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2)) /\ getr r 15 = Z_to_bv 64 (mx / 2)
      /\ getr r 8 = Z_to_bv 64 pc_ /\ getr r 9 = Z_to_bv 64 (T + 208) /\ getr r 18 = Z_to_bv 64 0x10ab58 /\ getr r 19 = Z_to_bv 64 c /\ getr r 20 = Z_to_bv 64 pz
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rcnt Rmx HokT Hstk Hmx Hc HT HS H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct dlf_facts as (Hn & Hcn & Hdm).
    assert (Vmx : bytes_le_to_Z (LE4 mx) = bv_unsigned (Z_to_bv 64 mx)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - an F_4eca8 D_4eca8.                              (* [comment removed for export] *)
      fsd F_4ecac D_4ecac (at_ S (-2408)).
      fsd F_4ecb0 D_4ecb0 (at_ S (-2416)).
      fsd F_4ecb4 D_4ecb4 (at_ S (-2424)).
      fsd F_4ecb8 D_4ecb8 (at_ S (-2432)).
      fsd F_4ecbc D_4ecbc (at_ S (-2440)).
      fsd F_4ecc0 D_4ecc0 (at_ S (-2448)).
      ab_ft F_4ecc4 D_4ecc4 ltac:(condz).              (* [comment removed for export] *)
      an F_4ecc8 D_4ecc8.                              (* [comment removed for export] *)
      ab_ft F_4eccc D_4eccc ltac:(condz).              (* [comment removed for export] *)
      an F_4ecd0 D_4ecd0.                              (* [comment removed for export] *)
      av F_4ecd4 D_4ecd4 (Z_to_bv 64 (80 * c)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_4ecd8 D_4ecd8 (Z_to_bv 64 pc_) ltac:(valz).  (* [comment removed for export] *)
      clw F_4ecdc D_4ecdc (LE4 mx) (Z_to_bv 64 mx) Rmx Vmx.       (* [comment removed for export] *)
      rewrite (v_lw_small mx) by lia.
      ab_ft F_4ece0 D_4ece0 ltac:(condz).              (* [comment removed for export] *)
      clw F_4ece4 D_4ece4 (LE4 mx) (Z_to_bv 64 mx) Rcnt Vmx.      (* [comment removed for export] *)
      rewrite (v_lw_small mx) by lia.
      ab_tk F_4ece8 D_4ece8 ltac:(condz).              (* [comment removed for export] *)
      an F_4ee38 D_4ee38.                              (* [comment removed for export] *)
      an F_4ee3c D_4ee3c.                              (* [comment removed for export] *)
      an F_4ee40 D_4ee40.                              (* [comment removed for export] *)
      an F_4ee44 D_4ee44.                              (* [comment removed for export] *)
      an F_4ee48 D_4ee48.                              (* [comment removed for export] *)
      an F_4ee4c D_4ee4c.                              (* [comment removed for export] *)
      an F_4ee50 D_4ee50.                              (* [comment removed for export] *)
      an F_4ee54 D_4ee54.                              (* [comment removed for export] *)
      an F_4f03c D_4f03c.                              (* [comment removed for export] *)
      fsd F_4f040 D_4f040 (at_ S (-2456)).             (* [comment removed for export] *)
      fsd F_4f044 D_4f044 (at_ S (-2472)).             (* [comment removed for export] *)
      fsd F_4f048 D_4f048 (at_ S (-2464)).             (* [comment removed for export] *)
      clw F_4f04c D_4f04c (LE4 mx) (Z_to_bv 64 mx) Rcnt Vmx.      (* [comment removed for export] *)
      rewrite (v_lw_small mx) by lia.
      clwu F_4f050 D_4f050 (LE4 mx) (Z_to_bv 64 mx) Rmx Vmx.      (* [comment removed for export] *)
      fsd F_4f054 D_4f054 (at_ S (-2504)).             (* [comment removed for export] *)
      fsd F_4f058 D_4f058 (at_ S (-2496)).
      fsd F_4f05c D_4f05c (at_ S (-2488)).
      fsd F_4f060 D_4f060 (at_ S (-2480)).
      av F_4f064 D_4f064 (Z_to_bv 64 (mx / 2)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1)%Z with 2%Z; unorm; reflexivity).   (* [comment removed for export] *)
      av F_4f068 D_4f068 (Z_to_bv 64 (mx * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      av F_4f06c D_4f06c (Z_to_bv 64 mx) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite Hdm; unorm; reflexivity).   (* [comment removed for export] *)
      ab_ft F_4f070 D_4f070 ltac:(condz).              (* [comment removed for export] *)
      av F_4f074 D_4f074 (Z_to_bv 64 (mx - mx / 2)) ltac:(valz).   (* [comment removed for export] *)
      an F_4f078 D_4f078.                              (* [comment removed for export] *)
      fsw F_4f07c D_4f07c (Z_to_bv 64 pc_).            (* [comment removed for export] *)
      an F_4f080 D_4f080.                              (* [comment removed for export] *)
      av F_4f084 D_4f084 (Z_to_bv 64 (4 * (mx - mx / 2))) ltac:(valz).   (* [comment removed for export] *)
      av F_4f088 D_4f088 (Z_to_bv 64 (pc_ + 4 * (mx - mx / 2))) ltac:(valz).   (* [comment removed for export] *)
      av F_4f08c D_4f08c (Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2))) ltac:(valz).   (* [comment removed for export] *)
      an F_4f090 D_4f090.                              (* [comment removed for export] *)
      an F_4f094 D_4f094.                              (* [comment removed for export] *)
      an F_4f098 D_4f098.                              (* [comment removed for export] *)
      an F_4f09c D_4f09c.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with M1. wd_refl.
    - post.
  Qed.
End DLFHEAD.

(* [comment removed for export] *)
Definition fr_dtl (mem : word -> option byte) (S : word) (T c cnt' e : Z) (stw : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2520)) (LE8 (Z_to_bv 64 0x4f0b0)))
    (at_ S (-2528)) (LE8 (Z_to_bv 64 (T + 208 + 80 * c))))
    (at_ S (-2536)) (LE8 (Z_to_bv 64 (T + 208))))
    (at_ S (-2544)) (LE8 (Z_to_bv 64 0x10ab58)))
    (Z_to_bv 64 (T + 208 + 80 * c)) (LE4 (cnt' + 1)))
    (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * cnt')) (LE4 (e / 16)))
    (Z_to_bv 64 (T + 2784)) (LE8 stw).
#[local] Hint Unfold fr_dtl : asfr.

Section DLFTAIL.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T spb c e cnt' : Z) (bst bcs : list byte).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  Hypothesis H2 : getr regs 2 = at_ S (-2512).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 pc_.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (T + 208).
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 0x10ab58.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 c.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 (spb + c * 2 ^ 32 + e).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis He : (0 <= e < 2 ^ 32)%Z.
  Hypothesis Hcnt : (0 <= cnt' < 16)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Lbst : length bst = 8%nat.
  Hypothesis Lbcs : length bcs = 8%nat.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2560)) 48 = true.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Rb0 : rdn BSEGS mem (at_ S (-2480)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rb1 : rdn BSEGS mem (at_ S (-2472)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rdra : rdn BSEGS mem (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ee58)).
  Hypothesis Cra : rdn BSEGS mem (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn BSEGS mem (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn BSEGS mem (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn BSEGS mem (at_ S (-2432)) 8 = Some (LE8 s2v).
  Hypothesis Cs3 : rdn BSEGS mem (at_ S (-2440)) 8 = Some (LE8 s3v).
  Hypothesis Cs4 : rdn BSEGS mem (at_ S (-2448)) 8 = Some (LE8 s4v).
  Hypothesis Rcnt : rdn BSEGS mem (Z_to_bv 64 pc_) 4 = Some (LE4 cnt').
  Hypothesis Rcs : rdn BSEGS mem (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis Rst : rdn BSEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).

  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma dtl_facts : (cnt' * 2 ^ 32 / 2 ^ 30 = 4 * cnt' /\ (T + 2784) mod 8 = 0)%Z.
  Proof using Lbcs Lbst Hcnt He HT bcs bst e s4v S rom. destruct HT as (_ & _ & T16). split; [| lia]. replace (cnt' * 2 ^ 32)%Z with (4 * cnt' * 2 ^ 30)%Z by lia. rewrite Z.div_mul by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma drn_dlf_tail :
    exists r, msteps BSEGS (mkst regs (0x4f0a0 : word) mem rom) (mkst r ra0 (fr_dtl mem S T c cnt' e stw) rom)
      /\ getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rspb Rst Rcs Rcnt Cs4 Cs3 Cs2 Cs1 Cs0 Cra Rdra Rb1 Rb0 HokT Hstk Lbcs Lbst Hret Hcnt He Hc Hspb HT HS H20 H19 H18 H9 H8 H2 spb.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct dtl_facts as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (LE4 cnt') = bv_unsigned (Z_to_bv 64 cnt')) by (apply bytes4_small; lia).
    wd_eexists. split.
    - cld8 F_4f0a0 D_4f0a0 (Z_to_bv 64 0) Rb0.         (* [comment removed for export] *)
      cld8 F_4f0a4 D_4f0a4 (Z_to_bv 64 0) Rb1.         (* [comment removed for export] *)
      an F_4f0a8 D_4f0a8.                              (* [comment removed for export] *)
      an F_4f0ac D_4f0ac.                              (* [comment removed for export] *)
      an F_829f8 D_829f8.                              (* [comment removed for export] *)
      fsd F_829fc D_829fc (at_ S (-2520)).             (* [comment removed for export] *)
      fsd F_82a00 D_82a00 (at_ S (-2528)).             (* [comment removed for export] *)
      fsd F_82a04 D_82a04 (at_ S (-2536)).             (* [comment removed for export] *)
      fsd F_82a08 D_82a08 (at_ S (-2544)).             (* [comment removed for export] *)
      ab_tk F_82a0c D_82a0c ltac:(condz).              (* [comment removed for export] *)
      fld F_82a48 D_82a48 (Z_to_bv 64 0x4f0b0).        (* [comment removed for export] *)
      fld F_82a4c D_82a4c (Z_to_bv 64 pc_).            (* [comment removed for export] *)
      fld F_82a50 D_82a50 (Z_to_bv 64 (T + 208)).      (* [comment removed for export] *)
      fld F_82a54 D_82a54 (Z_to_bv 64 0x10ab58).       (* [comment removed for export] *)
      an F_82a58 D_82a58.                              (* [comment removed for export] *)
      aret F_82a5c D_82a5c (Z_to_bv 64 0x4f0b0).       (* [comment removed for export] *)
      cld8 F_4f0b0 D_4f0b0 (Z_to_bv 64 0x4ee58) Rdra.  (* [comment removed for export] *)
      an F_4f0b4 D_4f0b4.                              (* [comment removed for export] *)
      aret F_4f0b8 D_4f0b8 (Z_to_bv 64 0x4ee58).       (* [comment removed for export] *)
      an F_4ee58 D_4ee58.                              (* [comment removed for export] *)
      an F_4ee5c D_4ee5c.                              (* [comment removed for export] *)
      an F_4ee60 D_4ee60.                              (* [comment removed for export] *)
      an F_4ee64 D_4ee64.                              (* [comment removed for export] *)
      clw F_4ee68 D_4ee68 (LE4 cnt') (Z_to_bv 64 cnt') Rcnt Vcnt.   (* [comment removed for export] *)
      rewrite (v_lw_small cnt') by lia.
      an F_4ee6c D_4ee6c.                              (* [comment removed for export] *)
      cld8 F_4ecec D_4ecec (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      av F_4ecf0 D_4ecf0 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(apply cls_shl32; lia).   (* [comment removed for export] *)
      av F_4ecf4 D_4ecf4 (Z_to_bv 64 (spb + e)) ltac:(valz).      (* [comment removed for export] *)
      av F_4ecf8 D_4ecf8 (Z_to_bv 64 (cnt' * 2 ^ 32)) ltac:(valz). (* [comment removed for export] *)
      av F_4ecfc D_4ecfc (Z_to_bv 64 (cnt' + 1)) ltac:(valz).      (* [comment removed for export] *)
      av F_4ed00 D_4ed00 (Z_to_bv 64 e) ltac:(valz).   (* [comment removed for export] *)
      cld F_4ed04 D_4ed04 bcs (Z_to_bv 64 (bytes_le_to_Z bcs)) Rcs Vcs.   (* [comment removed for export] *)
      an F_4ed08 D_4ed08.                              (* [comment removed for export] *)
      av F_4ed0c D_4ed0c (Z_to_bv 64 (4 * cnt')) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite <- Hc4; unorm; reflexivity).   (* [comment removed for export] *)
      av F_4ed10 D_4ed10 (Z_to_bv 64 (T + 2784)) ltac:(valz).     (* [comment removed for export] *)
      av F_4ed14 D_4ed14 (Z_to_bv 64 (pc_ + 4 * cnt')) ltac:(valz).   (* [comment removed for export] *)
      av F_4ed18 D_4ed18 (Z_to_bv 64 (e / 16)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).   (* [comment removed for export] *)
      fsw F_4ed1c D_4ed1c (Z_to_bv 64 pc_).            (* [comment removed for export] *)
      fsw F_4ed20 D_4ed20 (Z_to_bv 64 (pc_ + 16 + 4 * cnt')).   (* [comment removed for export] *)
      an F_4ed24 D_4ed24.                              (* [comment removed for export] *)
      famoA F_4ed28 D_4ed28 bst (Z_to_bv 64 (bytes_le_to_Z bst)) Rst Vst.   (* [comment removed for export] *)
      cld8 F_4ed2c D_4ed2c ra0 Cra. cld8 F_4ed30 D_4ed30 s0v Cs0. cld8 F_4ed34 D_4ed34 s1v Cs1. cld8 F_4ed38 D_4ed38 s2v Cs2.
      cld8 F_4ed3c D_4ed3c s3v Cs3. cld8 F_4ed40 D_4ed40 s4v Cs4.
      an F_4ed44 D_4ed44.                              (* [comment removed for export] *)
      aret F_4ed48 D_4ed48 ra0.                        (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_dtl mem S T c cnt' e stw). wd_refl.
    - post.
  Qed.
End DLFTAIL.
End FPGen.
End BoAllocFRc4a.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc4U.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac BoAllocFMem BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Ltac lsideC := wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
Ltac rdC := repeat (wd_rdstep rd8_side).

Section STK.
  Variables (mem : word -> option byte) (S : word).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.

  Lemma fr_dlf_outside : forall ra0 s0v s1v s2v s3v s4v (a : word), (U a < U S - 2448 \/ U S - 2400 <= U a) -> fr_dlf mem S ra0 s0v s1v s2v s3v s4v a = mem a.
  Proof using HS. intros ra0 s0v s1v s2v s3v s4v a Ha. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dlf in G in change_no_check G' end). rewrite !wbytes_outside by lsideC. reflexivity. Qed.
  Lemma fr_dlf_grows : forall ra0 s0v s1v s2v s3v s4v, mem_grows mem (fr_dlf mem S ra0 s0v s1v s2v s3v s4v).
  Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold fr_dlf in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Lemma fr_dlf_ra : forall ra0 s0v s1v s2v s3v s4v, rdn BSEGS (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) (at_ S (-2408)) 8 = Some (LE8 ra0).
  Proof using HS. intros. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dlf in G in change_no_check G' end). rdC. Qed.
  Lemma fr_dlf_s0 : forall ra0 s0v s1v s2v s3v s4v, rdn BSEGS (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) (at_ S (-2416)) 8 = Some (LE8 s0v).
  Proof using HS. intros. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dlf in G in change_no_check G' end). rdC. Qed.
  Lemma fr_dlf_s1 : forall ra0 s0v s1v s2v s3v s4v, rdn BSEGS (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) (at_ S (-2424)) 8 = Some (LE8 s1v).
  Proof using HS. intros. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dlf in G in change_no_check G' end). rdC. Qed.
  Lemma fr_dlf_s2 : forall ra0 s0v s1v s2v s3v s4v, rdn BSEGS (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) (at_ S (-2432)) 8 = Some (LE8 s2v).
  Proof using HS. intros. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dlf in G in change_no_check G' end). rdC. Qed.
  Lemma fr_dlf_s3 : forall ra0 s0v s1v s2v s3v s4v, rdn BSEGS (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) (at_ S (-2440)) 8 = Some (LE8 s3v).
  Proof using HS. intros. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dlf in G in change_no_check G' end). rdC. Qed.
  Lemma fr_dlf_s4 : forall ra0 s0v s1v s2v s3v s4v, rdn BSEGS (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) (at_ S (-2448)) 8 = Some (LE8 s4v).
  Proof using HS. intros. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dlf in G in change_no_check G' end). rdC. Qed.

  Lemma fr_mro_outside : forall ra0 s0v s1v s2v s3v s4v s5v s6v s7v (a : word), (U a < U S - 2720 \/ U S - 2640 <= U a) ->
    fr_mro mem S ra0 s0v s1v s2v s3v s4v s5v s6v s7v a = mem a.
  Proof using HS. intros ra0 s0v s1v s2v s3v s4v s5v s6v s7v a Ha. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_mro in G in change_no_check G' end). rewrite !wbytes_outside by lsideC. reflexivity. Qed.
  Lemma fr_mro_grows : forall ra0 s0v s1v s2v s3v s4v s5v s6v s7v, mem_grows mem (fr_mro mem S ra0 s0v s1v s2v s3v s4v s5v s6v s7v).
  Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold fr_mro in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Section DRN.
    Variables (pcz cnt' : Z).
    Hypothesis Hpc : 0 <= pcz /\ pcz + 4 <= U S - 3584.
    Lemma fr_drn_outside : forall a : word, (U a < U S - 2512 \/ U S - 2448 <= U a) -> (U a < pcz \/ pcz + 4 <= U a) -> fr_drn mem S pcz cnt' a = mem a.
    Proof using Hpc HS. intros a A1 A2. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_drn in G in change_no_check G' end). rewrite !wbytes_outside by lsideC. reflexivity. Qed.
    Lemma fr_drn_grows : mem_grows mem (fr_drn mem S pcz cnt').
    Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_drn in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
    Lemma fr_drn_cnt : rdn BSEGS (fr_drn mem S pcz cnt') (Z_to_bv 64 pcz) 4 = Some (LE4 cnt').
    Proof using Hpc HS. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_drn in G in change_no_check G' end). pose proof (rdn_wbytes_hit BSEGS (LE4 cnt')) as X. rewrite length_N_to_le_bytes in X. apply X. unorm. lia. Qed.
    Lemma fr_drn_b0 : rdn BSEGS (fr_drn mem S pcz cnt') (at_ S (-2480)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Proof using Hpc HS. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_drn in G in change_no_check G' end). rewrite rdn_wbytes_out by lsideC. rdC. Qed.
    Lemma fr_drn_b1 : rdn BSEGS (fr_drn mem S pcz cnt') (at_ S (-2472)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Proof using Hpc HS. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_drn in G in change_no_check G' end). rewrite rdn_wbytes_out by lsideC. rdC. Qed.
    Lemma fr_drn_ra : rdn BSEGS (fr_drn mem S pcz cnt') (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ee58)).
    Proof using Hpc HS. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_drn in G in change_no_check G' end). rewrite rdn_wbytes_out by lsideC. rdC. Qed.
  End DRN.

  Section RTA0.
    Variables (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (RIz : Z).
    Hypothesis HRI : 0 <= RIz /\ RIz + 128 <= U S - 3584.
    #[local] Abbreviation M0 := (fr_rta0 mem S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v RIz).
    Lemma fr_rta0_outside : forall a : word, (U a < U S - 2640 \/ U S - 2512 <= U a) -> (U a < RIz \/ RIz + 8 <= U a) -> M0 a = mem a.
    Proof using HRI HS. intros a A1 A2. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_rta0 in G in change_no_check G' end). rewrite !wbytes_outside by lsideC. reflexivity. Qed.
    Lemma fr_rta0_grows : mem_grows mem M0.
    Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_rta0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
    Lemma fr_rta0_mu : rdn BSEGS M0 (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
    Proof using HRI HS. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_rta0 in G in change_no_check G' end). apply rdn_wbytes_hit8. unorm. lia. Qed.
    Ltac rdR0 := pose proof (u64_range S); (lazymatch goal with |- ?G => let G' := eval unfold fr_rta0 in G in change_no_check G' end); rewrite rdn_wbytes_out by lsideC; rdC.
    Lemma fr_rta0_ra : rdn BSEGS M0 (at_ S (-2520)) 8 = Some (LE8 ra0).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s0 : rdn BSEGS M0 (at_ S (-2528)) 8 = Some (LE8 s0v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s1 : rdn BSEGS M0 (at_ S (-2536)) 8 = Some (LE8 s1v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s2 : rdn BSEGS M0 (at_ S (-2544)) 8 = Some (LE8 s2v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s3 : rdn BSEGS M0 (at_ S (-2552)) 8 = Some (LE8 s3v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s4 : rdn BSEGS M0 (at_ S (-2560)) 8 = Some (LE8 s4v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s5 : rdn BSEGS M0 (at_ S (-2568)) 8 = Some (LE8 s5v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s6 : rdn BSEGS M0 (at_ S (-2576)) 8 = Some (LE8 s6v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s7 : rdn BSEGS M0 (at_ S (-2584)) 8 = Some (LE8 s7v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s8 : rdn BSEGS M0 (at_ S (-2592)) 8 = Some (LE8 s8v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s9 : rdn BSEGS M0 (at_ S (-2600)) 8 = Some (LE8 s9v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s10 : rdn BSEGS M0 (at_ S (-2608)) 8 = Some (LE8 s10v).  Proof using HRI HS. rdR0. Qed.
    Lemma fr_rta0_s11 : rdn BSEGS M0 (at_ S (-2616)) 8 = Some (LE8 s11v).  Proof using HRI HS. rdR0. Qed.
  End RTA0.

  Section DTL.
    Variables (T c cnt' e : Z) (stw : word).
    Hypothesis HT : 4096 <= T /\ T + 4096 <= U S - 3584.
    Hypothesis Hc : 1 <= c <= 30.
    Hypothesis Hcnt : 0 <= cnt' < 16.
    #[local] Abbreviation pc_ := (T + 208 + 80 * c).
    #[local] Abbreviation M9 := (fr_dtl mem S T c cnt' e stw).
    Lemma fr_dtl_outside : forall a : word, (U a < U S - 2560 \/ U S - 2512 <= U a) -> (U a < pc_ \/ pc_ + 4 <= U a) ->
      (U a < pc_ + 16 + 4 * cnt' \/ pc_ + 16 + 4 * cnt' + 4 <= U a) -> (U a < T + 2784 \/ T + 2792 <= U a) -> M9 a = mem a.
    Proof using Hcnt Hc HT HS. intros a A1 A2 A3 A4. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dtl in G in change_no_check G' end). rewrite !wbytes_outside by lsideC. reflexivity. Qed.
    Lemma fr_dtl_grows : mem_grows mem M9.
    Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_dtl in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
    Lemma fr_dtl_cnt : rdn BSEGS M9 (Z_to_bv 64 pc_) 4 = Some (LE4 (cnt' + 1)).
    Proof using Hcnt Hc HT HS.
      pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dtl in G in change_no_check G' end). do 2 rewrite rdn_wbytes_out by lsideC.
      pose proof (rdn_wbytes_hit BSEGS (LE4 (cnt' + 1))) as X. rewrite length_N_to_le_bytes in X. apply X. unorm. lia.
    Qed.
    Lemma fr_dtl_slot : rdn BSEGS M9 (Z_to_bv 64 (pc_ + 16 + 4 * cnt')) 4 = Some (LE4 (e / 16)).
    Proof using Hcnt Hc HT HS.
      pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_dtl in G in change_no_check G' end). rewrite rdn_wbytes_out by lsideC.
      pose proof (rdn_wbytes_hit BSEGS (LE4 (e / 16))) as X. rewrite length_N_to_le_bytes in X. apply X. unorm. lia.
    Qed.
  End DTL.
End STK.

(* [comment removed for export] *)
Lemma fa_fill_outside : forall ks (m : word -> option byte) dst (a : word), 0 <= dst -> dst + 4 * Z.of_nat (length ks) < 2 ^ 63 ->
  (U a < dst \/ dst + 4 * Z.of_nat (length ks) <= U a) -> fa_fill m dst ks a = m a.
Proof using.
  induction ks as [|k ks IH]; intros m dst a H0 H1 Ha; [reflexivity|]. cbn [fa_fill length] in *.
  rewrite IH by lia. apply wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; wd_ulia.
Qed.
Lemma fa_fill_grows : forall ks (m : word -> option byte) dst, mem_grows m (fa_fill m dst ks).
Proof using. induction ks as [|k ks IH]; intros m dst; [apply mem_grows_refl|]. (lazymatch goal with |- ?G => let G' := eval cbn [fa_fill] in G in change_no_check G' end). eapply mem_grows_trans; [apply wbytes_grows | apply IH]. Qed.
Lemma fa_fill_cell : forall ks (m : word -> option byte) dst i k, 0 <= dst -> dst + 4 * Z.of_nat (length ks) < 2 ^ 63 -> nth_error ks i = Some k ->
  rdn BSEGS (fa_fill m dst ks) (Z_to_bv 64 (dst + 4 * Z.of_nat i)) 4 = Some (LE4 k).
Proof using.
  induction ks as [|k0 ks IH]; intros m dst i k H0 H1 Hi; [destruct i; discriminate Hi|]. cbn [fa_fill length] in *.
  destruct i as [|i].
  - cbn in Hi. injection Hi as <-. replace (dst + 4 * Z.of_nat 0) with dst by lia.
    eapply rd_same; [intros x Hx; apply fa_fill_outside; [lia | lia | revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia] | wd_ulia_c |].
    pose proof (rdn_wbytes_hit BSEGS (LE4 k0)) as X. rewrite length_N_to_le_bytes in X. apply X. unorm. lia.
  - cbn [nth_error] in Hi. replace (dst + 4 * Z.of_nat (Datatypes.S i)) with (dst + 4 + 4 * Z.of_nat i) by lia. apply IH; [lia | lia | exact Hi].
Qed.

Section RTAC.
  Variables (mem : word -> option byte) (RIz nfn : Z) (w80 : word).
  Hypothesis HRI : 0 <= RIz /\ RIz + 128 < 2 ^ 63.
  Lemma fr_rtac_outside : forall a : word, (U a < RIz + 16 \/ RIz + 24 <= U a) -> (U a < RIz + 80 \/ RIz + 88 <= U a) -> fr_rtac mem RIz nfn w80 a = mem a.
  Proof using HRI. intros a A1 A2. (lazymatch goal with |- ?G => let G' := eval unfold fr_rtac in G in change_no_check G' end). rewrite !wbytes_outside by lsideC. reflexivity. Qed.
  Lemma fr_rtac_grows : mem_grows mem (fr_rtac mem RIz nfn w80).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_rtac in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma fr_rtac_nf : rdn BSEGS (fr_rtac mem RIz nfn w80) (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nfn)).
  Proof using HRI. (lazymatch goal with |- ?G => let G' := eval unfold fr_rtac in G in change_no_check G' end). rewrite rdn_wbytes_out by lsideC. apply rdn_wbytes_hit8. unorm. lia. Qed.
  Lemma fr_rtac_w80 : rdn BSEGS (fr_rtac mem RIz nfn w80) (Z_to_bv 64 (RIz + 80)) 8 = Some (LE8 w80).
  Proof using HRI. (lazymatch goal with |- ?G => let G' := eval unfold fr_rtac in G in change_no_check G' end). apply rdn_wbytes_hit8. unorm. lia. Qed.
End RTAC.
End FPGen.
End BoAllocFRc4U.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac BoAllocFMem BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma efs_m0_outside : forall (mem : word -> option byte) (sp ra s0v s1v s2v s3v a : word), 48 <= U sp ->
  (U a < U sp - 48 \/ U sp <= U a) -> efs_m0 mem sp ra s0v s1v s2v s3v a = mem a.
Proof using.
  intros mem sp ra s0v s1v s2v s3v a Hsp Ha. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold efs_m0 in G in change_no_check G' end).
  rewrite !wbytes_outside by (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). reflexivity.
Qed.
Lemma efs_m0_grows : forall (mem : word -> option byte) (sp ra s0v s1v s2v s3v : word), mem_grows mem (efs_m0 mem sp ra s0v s1v s2v s3v).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold efs_m0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

Definition fr_full (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (T spb c e mx nf : Z)
           (ks : list Z) (b80 : list byte) (w9 w22 stw : word) : word -> option byte :=
  let pcz := T + 208 + 80 * c in let RIz := spb + 2 ^ 37 + 128 * c in let fa := spb + c * 2 ^ 32 + 0xE0000000 in
  let M1 := fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pcz (mx - mx / 2) in
  let M2 := fr_rta0 M1 S (Z_to_bv 64 0x4f0a0) (Z_to_bv 64 pcz) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 0x10ab58) (Z_to_bv 64 c)
                    (Z_to_bv 64 (spb + c * 2 ^ 32 + e)) x21 x22 x23 x24 x25 x26 x27 RIz in
  let M3 := efs_m0 M2 (at_ S (-2640)) (Z_to_bv 64 0x4f344) (Z_to_bv 64 RIz) (Z_to_bv 64 nf) (Z_to_bv 64 c) (at_ S (-2504)) in
  let M4 := fa_fill M3 (fa + 4 * nf) ks in
  let M5 := fr_rtac M4 RIz (nf + mx / 2) (v_add (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (mx / 2))) in
  let M6 := fr_mro M5 S (Z_to_bv 64 0x4f394) (Z_to_bv 64 RIz) w9 (Z_to_bv 64 c) (at_ S (-2504)) (Z_to_bv 64 0x10ab58)
                   (Z_to_bv 64 (mx / 2)) w22 (Z_to_bv 64 (nf + mx / 2)) in
  let M7 := wbytes M6 (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0)) in
  fr_dtl M7 S T c (mx - mx / 2) e stw.

Section RUNFULL.
  Variables (mem rom : word -> option byte) (r0 : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (T spb c e mx nf mfa pgp : Z) (ks : list Z).
  Variables (b80 b88 b470 bst bcs : list byte).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c).
  #[local] Abbreviation RIz := (spb + 2 ^ 37 + 128 * c).
  #[local] Abbreviation fa := (spb + c * 2 ^ 32 + 0xE0000000).
  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).
  Hypothesis H1 : getr r0 1 = ra0.
  Hypothesis H2 : getr r0 2 = at_ S (-2400).
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 (T + 208).
  Hypothesis H11 : getr r0 11 = Z_to_bv 64 0x10ab58.
  Hypothesis H12 : getr r0 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr r0 13 = Z_to_bv 64 (spb + c * 2 ^ 32 + e).
  Hypothesis H8 : getr r0 8 = s0v.   Hypothesis H9 : getr r0 9 = s1v.   Hypothesis H18 : getr r0 18 = s2v.
  Hypothesis H19 : getr r0 19 = s3v. Hypothesis H20 : getr r0 20 = s4v.
  Hypothesis H21 : getr r0 21 = x21. Hypothesis H22 : getr r0 22 = x22. Hypothesis H23 : getr r0 23 = x23. Hypothesis H24 : getr r0 24 = x24.
  Hypothesis H25 : getr r0 25 = x25. Hypothesis H26 : getr r0 26 = x26. Hypothesis H27 : getr r0 27 = x27.
  (* [comment removed for export] *)
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0.
  Hypothesis Gspb : 0x10007fff8000 <= spb /\ spb + 2 ^ 37 + 4096 <= U S - 3584 /\ spb mod 8 = 0.
  Hypothesis GTsp : hideW (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T).
  Hypothesis Gce : 1 <= c <= 30 /\ 0 <= e < 2 ^ 32.
  Hypothesis Gmx : 2 <= mx <= 16.
  Hypothesis Gnf : 0 <= nf /\ 4 * (nf + mx / 2) <= mfa.
  Hypothesis Gmfa : 0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0.
  Hypothesis Gks : Z.of_nat (length ks) = mx / 2.
  Hypothesis Fks : Forall (fun k => 0 <= k < 2 ^ 31) ks.
  Hypothesis Gpgp : AIMGLO <= pgp /\ pgp + 8 <= AIMGHI.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis L80 : length b80 = 8%nat.  Hypothesis L88 : length b88 = 8%nat.  Hypothesis L470 : length b470 = 8%nat.
  Hypothesis Lst : length bst = 8%nat.  Hypothesis Lcs : length bcs = 8%nat.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2720)) 320 = true.
  Hypothesis OkT : store_ok BSEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis OkRI : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis Okfa : store_ok BSEGS mem (Z_to_bv 64 (fa + 4 * nf)) (4 * length ks) = true.
  (* [comment removed for export] *)
  Hypothesis C_mx : rdn BSEGS mem (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis C_cnt : rdn BSEGS mem (Z_to_bv 64 pc_) 4 = Some (LE4 mx).
  Hypothesis C_cs : rdn BSEGS mem (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis C_st : rdn BSEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis C_src : forall i k, nth_error ks i = Some k -> rdn BSEGS mem (Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i)) 4 = Some (LE4 k).
  Hypothesis C_spb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_rib : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 (spb + 2 ^ 37))).
  Hypothesis C_int : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff).
  Hypothesis C_gpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 pgp)).
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 pgp) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_470 : rdn BSEGS mem (Z_to_bv 64 0x10468) 8 = Some b470.
  Hypothesis C_mu : rdn BSEGS mem (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_nf : rdn BSEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis C_mfa : rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_80 : rdn BSEGS mem (Z_to_bv 64 (RIz + 80)) 8 = Some b80.
  Hypothesis C_88 : rdn BSEGS mem (Z_to_bv 64 (RIz + 88)) 8 = Some b88.

  Definition full_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr r0 3 /\ getr r 4 = getr r0 4
      /\ getr r 21 = x21 /\ getr r 22 = x22 /\ getr r 23 = x23 /\ getr r 24 = x24 /\ getr r 25 = x25 /\ getr r 26 = x26 /\ getr r 27 = x27.

  Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Ltac xq Q H :=
    eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
  Ltac rch := repeat (first [ reflexivity | assumption
                            | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).

  Theorem run_dfull :
    exists r w9 w22, msteps BSEGS (mkst r0 (0x4eca8%bv : word) mem rom)
        (mkst r ra0 (fr_full mem S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx nf ks b80 w9 w22 stw) rom)
      /\ full_regs r.
  Proof using C_88 C_80 C_mfa C_nf C_mu C_470 C_pg C_gpg C_int C_rib C_spb C_src C_st C_cs C_cnt C_mx Okfa OkRI OkT Hstk Lcs Lst L470 L88 L80 Hret Gpgp Fks Gks Gmfa Gnf Gmx Gce GTsp Gspb GT GS H27 H26 H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1 b470 b88 pgp mfa.
    (lazymatch goal with |- ?G => let G' := eval unfold full_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    destruct GS as (GS1 & GS2). destruct Gspb as (Gs1 & Gs2 & Gs8). destruct Gce as (Hc & He). destruct GT as (GT1 & (GTS & GT2) & GT16).
    destruct Gnf as (Gnf0 & Gnf1). destruct Gmfa as (Gm0 & Gm18).
    assert (DF : 1 <= mx / 2 <= 8 /\ mx - mx / 2 >= 1) by (clear - Gmx; Z.div_mod_to_equations; lia). destruct DF as (DF1 & DF2).
    assert (GTU : (T + 4096 <= AIMGLO \/ AIMGHI <= T) /\ (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T)).
    { unfold hideW in GTS, GTsp. split; [exact (proj1 GTS) | exact GTsp]. }
    hidehypW GTU.
    assert (GSs : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by lia.
    assert (GTk : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0) by (split; [exact GT1 | split; [split; [exact GTS | exact GT2] | exact GT16]]).
    assert (FAB : fa + 4 * nf + 4 * (mx / 2) <= spb + 2 ^ 37 /\ spb + 2 ^ 32 <= fa).
    { assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (replace (2 ^ 37) with (32 * 2 ^ 32) by reflexivity; nia). assert (2 ^ 32 <= c * 2 ^ 32) by nia. lia. }
    destruct FAB as (FAB1 & FAB2).
    assert (RIB : spb + 2 ^ 37 <= RIz /\ RIz + 128 <= spb + 2 ^ 37 + 4096 /\ RIz mod 8 = 0).
    { split; [lia|]. split; [lia|]. clear - Gs8. Z.div_mod_to_equations. lia. }
    destruct RIB as (RIB1 & RIB2 & RIB8).
    (* [comment removed for export] *)
    destruct (dlf_drn_head mem rom S ra0 s0v s1v s2v s3v s4v T c (spb + c * 2 ^ 32 + e) mx r0 H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 GSs GTk Hc Gmx
                ltac:(eapply (store_ok_sub BSEGS mem (at_ S (-2720)) _ 320); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia])
                OkT C_mx C_cnt)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A13 & A14 & A15 & A8 & A9 & A18 & A19 & A20 & A3 & A4 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    assert (GR1 : mem_grows mem (fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2))).
    { eapply mem_grows_trans; [apply fr_dlf_grows | apply fr_drn_grows]. }
    assert (Q1 : forall x : word, (U x < U S - 2512 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) ->
                 fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2) x = mem x).
    { intros x X1 X2. rewrite (fr_drn_outside _ S GSs pc_ (mx - mx / 2) ltac:(lia) x ltac:(lia) X2). apply (fr_dlf_outside mem S GSs). lia. }
    pose proof (fr_drn_cnt (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S GSs pc_ (mx - mx / 2) ltac:(lia)) as K1cnt.
    pose proof (fr_drn_b0 (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S GSs pc_ (mx - mx / 2) ltac:(lia)) as K1b0.
    pose proof (fr_drn_b1 (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S GSs pc_ (mx - mx / 2) ltac:(lia)) as K1b1.
    pose proof (fr_drn_ra (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S GSs pc_ (mx - mx / 2) ltac:(lia)) as K1ra.
    assert (K1f : forall k v, (k = -2408 \/ k = -2416 \/ k = -2424 \/ k = -2432 \/ k = -2440 \/ k = -2448) ->
               rdn BSEGS (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) (at_ S k) 8 = Some (LE8 v) ->
               rdn BSEGS (fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2)) (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hk Hv. eapply rd_same; [| | exact Hv].
      - intros x Hx. apply (fr_drn_outside _ S GSs pc_ (mx - mx / 2) ltac:(lia)); revert Hx; rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia.
      - rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    pose proof (K1f (-2408) _ ltac:(lia) (fr_dlf_ra mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c0.
    pose proof (K1f (-2416) _ ltac:(lia) (fr_dlf_s0 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c1.
    pose proof (K1f (-2424) _ ltac:(lia) (fr_dlf_s1 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c2.
    pose proof (K1f (-2432) _ ltac:(lia) (fr_dlf_s2 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c3.
    pose proof (K1f (-2440) _ ltac:(lia) (fr_dlf_s3 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c4.
    pose proof (K1f (-2448) _ ltac:(lia) (fr_dlf_s4 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c5.
    clear K1f.
    remember (fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2)) as M1 eqn:EM1 in RUN1, GR1, Q1, K1cnt, K1b0, K1b1, K1ra, K1c0, K1c1, K1c2, K1c3, K1c4, K1c5.
    idtac "PROGRESS 4R: stage 1".
    Ltac sokstk M GR := eapply (store_ok_sub BSEGS M (at_ S (-2720)) _ 320); [rewrite at_u; lia | eapply store_ok_mono; [exact GR | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    Ltac xqh TS Q H := unfold hideW in TS; xq Q H.
    (* [comment removed for export] *)
    assert (HribP : AIMGHI <= spb + 2 ^ 37 /\ spb + 2 ^ 37 + 4096 <= U S - 3584 /\ (spb + 2 ^ 37) mod 8 = 0).
    { split; [lia|]. split; [lia|]. clear - Gs8. Z.div_mod_to_equations. lia. }
    destruct (rta_lock M1 rom S (Z_to_bv 64 0x4f0a0) (Z_to_bv 64 pc_) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 0x10ab58) (Z_to_bv 64 c)
                (Z_to_bv 64 (spb + c * 2 ^ 32 + e)) x21 x22 x23 x24 x25 x26 x27 (at_ S (-2504)) spb (spb + 2 ^ 37) c
                (pc_ + 16 + 4 * (mx - mx / 2)) (mx / 2) nf r1
                A1 A2 A10 A11 A13 A14 A15 A8 A9 A18 A19 A20
                ltac:(rewrite A21; exact H21) ltac:(rewrite A22; exact H22) ltac:(rewrite A23; exact H23) ltac:(rewrite A24; exact H24)
                ltac:(rewrite A25; exact H25) ltac:(rewrite A26; exact H26) ltac:(rewrite A27; exact H27)
                GSs Hc ltac:(lia) HribP ltac:(lia) ltac:(lia)
                ltac:(sokstk M1 GR1)
                ltac:(eapply (store_ok_sub BSEGS M1 (Z_to_bv 64 RIz) _ 128); [wd_ulia | eapply store_ok_mono; [exact GR1 | exact OkRI] | wd_ulia | wd_ulia_c])
                ltac:(xqh GTU Q1 C_spb) ltac:(xqh GTU Q1 C_rib) ltac:(xqh GTU Q1 C_mu) ltac:(xqh GTU Q1 C_nf))
      as (r2 & RUN2 & RR & B1 & B10 & B11 & B12 & B13 & B9 & B23).
    destruct RR as (B2 & B8 & B18 & B19 & B20 & B21 & B22 & B24 & B25 & B3 & B4).
    match type of RUN2 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M2 eqn:EM2 end.
    assert (GR2 : mem_grows mem M2) by (rewrite EM2; eapply mem_grows_trans; [exact GR1 | apply fr_rta0_grows]).
    assert (QC2 : forall x : word, (U x < U S - 2640 \/ U S - 2512 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M2 x = M1 x).
    { intros x X1 X2. rewrite EM2. apply fr_rta0_outside; [exact GSs | lia | exact X1 | exact X2]. }
    assert (QM2 : forall x : word, (U x < U S - 2640 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M2 x = mem x).
    { intros x X1 X2 X3. rewrite QC2 by lia. apply Q1; lia. }
    assert (K2mu : rdn BSEGS M2 (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60)))) by (rewrite EM2; apply fr_rta0_mu; [exact GSs | lia]).
    assert (K2ra : rdn BSEGS M2 (at_ S (-2520)) 8 = Some (LE8 (Z_to_bv 64 0x4f0a0))) by (rewrite EM2; apply fr_rta0_ra; [exact GSs | lia]).
    assert (K2s0 : rdn BSEGS M2 (at_ S (-2528)) 8 = Some (LE8 (Z_to_bv 64 pc_))) by (rewrite EM2; apply fr_rta0_s0; [exact GSs | lia]).
    assert (K2s1 : rdn BSEGS M2 (at_ S (-2536)) 8 = Some (LE8 (Z_to_bv 64 (T + 208)))) by (rewrite EM2; apply fr_rta0_s1; [exact GSs | lia]).
    assert (K2s2 : rdn BSEGS M2 (at_ S (-2544)) 8 = Some (LE8 (Z_to_bv 64 0x10ab58))) by (rewrite EM2; apply fr_rta0_s2; [exact GSs | lia]).
    assert (K2s3 : rdn BSEGS M2 (at_ S (-2552)) 8 = Some (LE8 (Z_to_bv 64 c))) by (rewrite EM2; apply fr_rta0_s3; [exact GSs | lia]).
    assert (K2s4 : rdn BSEGS M2 (at_ S (-2560)) 8 = Some (LE8 (Z_to_bv 64 (spb + c * 2 ^ 32 + e)))) by (rewrite EM2; apply fr_rta0_s4; [exact GSs | lia]).
    assert (K2s5 : rdn BSEGS M2 (at_ S (-2568)) 8 = Some (LE8 x21)) by (rewrite EM2; apply fr_rta0_s5; [exact GSs | lia]).
    assert (K2s6 : rdn BSEGS M2 (at_ S (-2576)) 8 = Some (LE8 x22)) by (rewrite EM2; apply fr_rta0_s6; [exact GSs | lia]).
    assert (K2s7 : rdn BSEGS M2 (at_ S (-2584)) 8 = Some (LE8 x23)) by (rewrite EM2; apply fr_rta0_s7; [exact GSs | lia]).
    assert (K2s8 : rdn BSEGS M2 (at_ S (-2592)) 8 = Some (LE8 x24)) by (rewrite EM2; apply fr_rta0_s8; [exact GSs | lia]).
    assert (K2s9 : rdn BSEGS M2 (at_ S (-2600)) 8 = Some (LE8 x25)) by (rewrite EM2; apply fr_rta0_s9; [exact GSs | lia]).
    assert (K2s10 : rdn BSEGS M2 (at_ S (-2608)) 8 = Some (LE8 x26)) by (rewrite EM2; apply fr_rta0_s10; [exact GSs | lia]).
    assert (K2s11 : rdn BSEGS M2 (at_ S (-2616)) 8 = Some (LE8 x27)) by (rewrite EM2; apply fr_rta0_s11; [exact GSs | lia]).
    idtac "PROGRESS 4R: stage 2".
    (* [comment removed for export] *)
    assert (SPU : U (at_ S (-2640)) = U S - 2640) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    destruct (efs_enough M2 rom (at_ S (-2640)) (Z_to_bv 64 0x4f344) (Z_to_bv 64 RIz) (Z_to_bv 64 nf) (Z_to_bv 64 c) (at_ S (-2504)) RIz (nf + mx / 2) mfa r2
                B1 B2 B11 B13 B8 B9 B18 B19 ltac:(rewrite SPU; lia) ltac:(apply ret_ok_lit; [lia | reflexivity]) ltac:(lia) ltac:(split; [lia | exact Gm18]) ltac:(rewrite SPU; lia)
                ltac:(rewrite at_at; sokstk M2 GR2)
                ltac:(xqh GTU QM2 C_mfa) ltac:(lia))
      as (r3 & RUN3 & E10 & E2 & E1 & E8 & E9 & E18 & E19 & AGE).
    match type of RUN3 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M3 eqn:EM3 end.
    assert (GR3 : mem_grows mem M3) by (rewrite EM3; eapply mem_grows_trans; [exact GR2 | apply efs_m0_grows]).
    assert (QB3 : forall x : word, (U x < U S - 2688 \/ U S - 2640 <= U x) -> M3 x = M2 x).
    { intros x X1. rewrite EM3. apply efs_m0_outside; rewrite SPU; lia. }
    assert (QM3 : forall x : word, (U x < U S - 2688 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M3 x = mem x).
    { intros x X1 X2 X3. rewrite QB3 by lia. apply QM2; lia. }
    assert (E20 : getr r3 20 = Z_to_bv 64 0x10ab58) by (rewrite (AGE (20%bv : reg) ltac:(notin)); exact B20).
    assert (E21 : getr r3 21 = Z_to_bv 64 (mx / 2)) by (rewrite (AGE (21%bv : reg) ltac:(notin)); exact B21).
    assert (E22 : getr r3 22 = Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2))) by (rewrite (AGE (22%bv : reg) ltac:(notin)); exact B22).
    assert (E23 : getr r3 23 = Z_to_bv 64 (nf + mx / 2)) by (rewrite (AGE (23%bv : reg) ltac:(notin)); exact B23).
    assert (E24 : getr r3 24 = Z_to_bv 64 (2 ^ 61)) by (rewrite (AGE (24%bv : reg) ltac:(notin)); exact B24).
    assert (E25 : getr r3 25 = Z_to_bv 64 fa) by (rewrite (AGE (25%bv : reg) ltac:(notin)); exact B25).
    assert (E3 : getr r3 3 = getr r0 3) by (rewrite (AGE (3%bv : reg) ltac:(notin)), B3; exact A3).
    assert (E4 : getr r3 4 = getr r0 4) by (rewrite (AGE (4%bv : reg) ltac:(notin)), B4; exact A4).
    idtac "PROGRESS 4R: stage 3".
    (* [comment removed for export] *)
    destruct (rta_to_copy M3 rom S (at_ S (-2504)) RIz c (pc_ + 16 + 4 * (mx - mx / 2)) (mx / 2) nf fa r3 E2 E8 E9 E18 E19 E20 E21 E22 E23 E25
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E10)
      as (r4 & RUN4 & D22 & D25 & D10 & D1 & D2 & D3 & D4 & D8 & D18 & D19 & D20 & D21 & D23 & D24 & D26 & D27).
    assert (KSNE : ks <> []) by (intros E; rewrite E in Gks; cbn in Gks; lia).
    destruct (rta_copy_loop ks r4 M3 rom (pc_ + 16 + 4 * (mx - mx / 2)) (fa + 4 * nf) KSNE D22 D25 ltac:(rewrite Gks; exact D10)
                ltac:(rewrite Gks; lia) ltac:(rewrite Gks; lia) ltac:(rewrite Gks; unfold hideW in GTU; lia) Fks
                ltac:(intros i k Hik; assert (Z.of_nat i < mx / 2) by (rewrite <- Gks; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate);
                      xqh GTU QM3 (C_src i k Hik))
                ltac:(eapply store_ok_mono; [exact GR3 | exact Okfa]))
      as (r5 & RUN5 & KP).
    destruct KP as (P1 & P2 & P3 & P4 & P8 & P9 & P10 & P18 & P19 & P20 & P21 & P23 & P24 & P26 & P27).
    match type of RUN5 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M4 eqn:EM4 end.
    assert (GR4 : mem_grows mem M4) by (rewrite EM4; eapply mem_grows_trans; [exact GR3 | apply fa_fill_grows]).
    assert (QB4 : forall x : word, (U x < U S - 2688 \/ U S - 2640 <= U x) -> (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> M4 x = M2 x).
    { intros x X1 X2. rewrite EM4. rewrite fa_fill_outside by (rewrite ?Gks; lia). apply QB3; exact X1. }
    assert (QM4 : forall x : word, (U x < U S - 2688 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> M4 x = mem x).
    { intros x X1 X2 X3 X4. rewrite QB4 by lia. apply QM2; lia. }
    idtac "PROGRESS 4R: stage 5".
    (* [comment removed for export] *)
    destruct (rta_counters M4 rom S (at_ S (-2504)) RIz c (mx / 2) nf b80 r5
                ltac:(rewrite P2, D2; exact E2) ltac:(rewrite P8, D8; exact E8) ltac:(rewrite P18, D18; exact E18) ltac:(rewrite P19, D19; exact E19)
                ltac:(rewrite P20, D20; exact E20) ltac:(rewrite P21, D21; exact E21) ltac:(rewrite P23, D23; exact E23)
                GSs ltac:(lia) L80 ltac:(xqh GTU QM4 C_80) ltac:(eapply store_ok_mono; [exact GR4 | exact OkRI]))
      as (r6 & RUN6 & F1 & F10 & F11 & F12 & F13 & F2 & F3 & F4 & F8 & F18 & F19 & F20 & F21 & F23 & F24 & F26 & F27).
    match type of RUN6 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M5 eqn:EM5 end.
    assert (GR5 : mem_grows mem M5) by (rewrite EM5; eapply mem_grows_trans; [exact GR4 | apply fr_rtac_grows]).
    assert (QB5 : forall x : word, (U x < U S - 2688 \/ U S - 2640 <= U x) -> (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) ->
                  (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 80 \/ RIz + 88 <= U x) -> M5 x = M2 x).
    { intros x X1 X2 X3 X4. rewrite EM5. rewrite fr_rtac_outside by lia. apply QB4; assumption. }
    assert (QM5 : forall x : word, (U x < U S - 2688 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 80 \/ RIz + 88 <= U x) -> M5 x = mem x).
    { intros x X1 X2 X3 X4 X5 X6. rewrite QB5 by lia. apply QM2; lia. }
    assert (K5nf : rdn BSEGS M5 (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 (nf + mx / 2)))) by (rewrite EM5; apply fr_rtac_nf; lia).
    assert (K5w80 : rdn BSEGS M5 (Z_to_bv 64 (RIz + 80)) 8 = Some (LE8 (v_add (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (mx / 2))))) by (rewrite EM5; apply fr_rtac_w80; lia).
    idtac "PROGRESS 4R: stage 6".
    (* [comment removed for export] *)
    destruct (mro_run M5 rom S (Z_to_bv 64 0x4f394) (Z_to_bv 64 RIz) (getr r6 9) (Z_to_bv 64 c) (at_ S (-2504)) (Z_to_bv 64 0x10ab58)
                (Z_to_bv 64 (mx / 2)) (getr r6 22) (Z_to_bv 64 (nf + mx / 2)) (at_ S (-2504)) (spb + 2 ^ 37) c (nf + mx / 2) pgp
                (LE8 (v_add (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (mx / 2)))) b88 r6
                F1 ltac:(rewrite F2, P2, D2; exact E2) F10 F11 F12 F13 ltac:(rewrite F8, P8, D8; exact E8) eq_refl
                ltac:(rewrite F18, P18, D18; exact E18) ltac:(rewrite F19, P19, D19; exact E19) ltac:(rewrite F20, P20, D20; exact E20)
                ltac:(rewrite F21, P21, D21; exact E21) eq_refl ltac:(rewrite F23, P23, D23; exact E23)
                GSs Hc ltac:(lia) ltac:(lia) (length_N_to_le_bytes 8 _) L88 Gpgp ltac:(apply ret_ok_lit; [lia | reflexivity])
                ltac:(sokstk M5 GR5)
                ltac:(xqh GTU QM5 C_rib) ltac:(xqh GTU QM5 C_gpg) ltac:(xqh GTU QM5 C_pg) K5nf K5w80 ltac:(xqh GTU QM5 C_88) ltac:(xqh GTU QM5 C_int))
      as (r7 & RUN7 & MP).
    destruct MP as (J2 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J3 & J4 & J24 & J25 & J26 & J27).
    match type of RUN7 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M6 eqn:EM6 end.
    assert (GR6 : mem_grows mem M6) by (rewrite EM6; eapply mem_grows_trans; [exact GR5 | apply fr_mro_grows]).
    assert (QB6 : forall x : word, (U x < U S - 2720 \/ U S - 2640 <= U x) -> (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) ->
                  (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 80 \/ RIz + 88 <= U x) -> M6 x = M2 x).
    { intros x X1 X2 X3 X4. rewrite EM6. rewrite (fr_mro_outside M5 S GSs) by lia. apply QB5; [lia | assumption | assumption | assumption]. }
    assert (QM6 : forall x : word, (U x < U S - 2720 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 80 \/ RIz + 88 <= U x) -> M6 x = mem x).
    { intros x X1 X2 X3 X4 X5 X6. rewrite QB6 by lia. apply QM2; lia. }
    idtac "PROGRESS 4R: stage 7".
    (* [comment removed for export] *)
    destruct (rta_unlock M6 rom S (Z_to_bv 64 0x4f0a0) (Z_to_bv 64 pc_) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 0x10ab58) (Z_to_bv 64 c)
                (Z_to_bv 64 (spb + c * 2 ^ 32 + e)) x21 x22 x23 x24 x25 x26 x27 RIz b470 r7
                J2 J8 ltac:(rewrite J24, F24, P24, D24; exact E24) GSs ltac:(lia) ltac:(apply ret_ok_lit; [lia | reflexivity]) L470
                ltac:(eapply (store_ok_sub BSEGS M6 (Z_to_bv 64 RIz) _ 128); [wd_ulia | eapply store_ok_mono; [exact GR6 | exact OkRI] | wd_ulia | wd_ulia_c])
                ltac:(xq QB6 K2mu) ltac:(xqh GTU QM6 C_470)
                ltac:(xq QB6 K2ra) ltac:(xq QB6 K2s0) ltac:(xq QB6 K2s1) ltac:(xq QB6 K2s2) ltac:(xq QB6 K2s3) ltac:(xq QB6 K2s4) ltac:(xq QB6 K2s5)
                ltac:(xq QB6 K2s6) ltac:(xq QB6 K2s7) ltac:(xq QB6 K2s8) ltac:(xq QB6 K2s9) ltac:(xq QB6 K2s10) ltac:(xq QB6 K2s11))
      as (r8 & RUN8 & L2 & L8 & L9 & L18 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27 & L3 & L4).
    match type of RUN8 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M7 eqn:EM7 end.
    assert (GR7 : mem_grows mem M7) by (rewrite EM7; eapply mem_grows_trans; [exact GR6 | apply wbytes_grows]).
    assert (QC7 : forall x : word, (U x < U S - 2720 \/ U S - 2512 <= U x) -> (U x < RIz \/ RIz + 128 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> M7 x = M1 x).
    { intros x X1 X2 X3. rewrite EM7. rewrite wbytes_outside by (rewrite length_N_to_le_bytes; wd_ulia). rewrite QB6 by lia. apply QC2; lia. }
    assert (QM7 : forall x : word, (U x < U S - 2720 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 128 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> M7 x = mem x).
    { intros x X1 X2 X3 X4. rewrite QC7 by lia. apply Q1; lia. }
    idtac "PROGRESS 4R: stage 8".
    (* [comment removed for export] *)
    destruct (drn_dlf_tail M7 rom S ra0 s0v s1v s2v s3v s4v T spb c e (mx - mx / 2) bst bcs r8 L2 L8 L9 L18 L19 L20 GSs GTk ltac:(lia) Hc He ltac:(lia) Hret Lst Lcs
                ltac:(sokstk M7 GR7) ltac:(eapply store_ok_mono; [exact GR7 | exact OkT])
                ltac:(xq QC7 K1b0) ltac:(xq QC7 K1b1) ltac:(xq QC7 K1ra)
                ltac:(xq QC7 K1c0) ltac:(xq QC7 K1c1) ltac:(xq QC7 K1c2) ltac:(xq QC7 K1c3) ltac:(xq QC7 K1c4) ltac:(xq QC7 K1c5)
                ltac:(xqh GTU QC7 K1cnt) ltac:(xqh GTU QM7 C_cs) ltac:(xqh GTU QM7 C_st) ltac:(xqh GTU QM7 C_spb))
      as (r9 & RUN9 & N2 & N8 & N9 & N18 & N19 & N20 & N3 & N4 & N21 & N22 & N23 & N24 & N25 & N26 & N27).
    idtac "PROGRESS 4R: stage 9".
    (* [comment removed for export] *)
    exists r9, (getr r6 9), (getr r6 22). split.
    { replace (Z_to_bv 64 0x4f344 : word) with (0x4f344%bv : word) in RUN3 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x4f394 : word) with (0x4f394%bv : word) in RUN7 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x4f0a0 : word) with (0x4f0a0%bv : word) in RUN8 by (apply bv_eq; reflexivity).
      subst M7 M6 M5 M4 M3 M2 M1. (lazymatch goal with |- ?G => let G' := eval unfold fr_full in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8 | exact RUN9]. }
    repeat match goal with |- _ /\ _ => split end; try assumption; rch.
  Qed.
End RUNFULL.
End FPGen.
