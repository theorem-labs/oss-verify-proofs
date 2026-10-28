(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_dx1 AZ_huf_bitinit AZ_huf_dx2 AZ_huf_dx2b AZ_huf_dx2l AZ_huf_dx2l4.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
#[local] Ltac kx_path_hyp E zs nz KXA BR ::= kx_rr_dedup; kx_path_hyp_fast E zs nz KXA BR.
Ltac kxa_norm ::= unfold shspan in *.


Section CANSEC1. Context {rc : runConstT}.
Section DX2E.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis ACTX : x1_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2352 [] m0 huf_noQ).
  Notation W0 := [(DST, DST + dcap); (SPV - 2352, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation DINV2 := (dinv2 ra s0 s1 s2 s3 s4 s5 m0 SPV DST dcap SRC DT lo src dtb).
  Notation PINV := (pinv2 SRC n).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in let g := fresh "g" in
    destruct DI as (OUT & FR & [g GAP] & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold dinv2; repeat (split; [first [eassumption | eexists; eassumption]|]); eassumption.
  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333497648 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333495296 <= SPV - 2352) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  (* [comment removed for export] *)
  Ltac afacts MU0 UDT RDTS RSTK DSTA R3 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (eapply unp_carryS; [exact UDT | exact MU0 | clear - R3; lia | clear - R3; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 64) 64) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
  Ltac dfacts MU0 UDST RDST RDSTS DSTA R1 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let D := fresh "DPOS" in
    assert (D : 0 < dcap) by lia;
    assert (UDSTc : unpoisoned mm DST (DST + dcap))
      by (eapply unp_carryS; [exact (UDST D) | exact MU0 | clear - R1; lia | clear - R1; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (RDST D) as RDSTc; pose proof (RDSTS D) as RDSTSc;
    assert (DSTAc : DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST) by (clear - D DSTA; lia);
    pose proof (rng_shspanZ _ _ _ RDSTSc) as RDSTz;
    pose proof (unpoisoned_unpZ _ _ _ DST (DST + dcap) UDSTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R1; lia)) as UDSTz;
    clear D.
  Ltac sfacts MU0 USRC RSRC RSRCS DSTA R1 R2 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let N := fresh "NPOS" in
    assert (N : 0 < n) by lia;
    assert (USRCc : unpoisoned mm SRC (SRC + n))
      by (eapply unp_carryS; [exact (USRC N) | exact MU0 | clear - R2; lia | clear - R2; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (RSRC N) as RSRCc; pose proof (RSRCS N) as RSRCSc;
    pose proof (rng_shspanZ _ _ _ RSRCSc) as RSRCz;
    pose proof (unpoisoned_unpZ _ _ _ SRC (SRC + n) USRCc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R2 N; lia)) as USRCz;
    clear N.
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS2 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 64 \/ SPV - 64 + 64 <= DST) /\ (SPV - 64 + 64 <= DT \/ DT + 16388 <= SPV - 64) /\
                 (SPV - 64 + 64 <= SRC \/ SRC + n <= SPV - 64))
      by (clear - OS1 OS2 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3).
  Ltac kclean :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : DT mod 4 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < _ -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < _ -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : nth_error dtb _ = _ |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac len_range :=
    match goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + (_ + bv_unsigned (ev ?E ?k)))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        let H := fresh "LENR" in kx_erange H (EVar k); cbn [edenot] in H
    | |- _ => idtac
    end.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  (* [comment removed for export] *)
  Ltac x2_open DI :=
    let CTX' := fresh "CTX'" in let ACTX' := fresh "ACTX'" in let DI' := fresh "DI'" in
    pose proof CTX as CTX'; x1_ctx_open CTX'; pose proof ACTX as ACTX'; x1_actx_open ACTX';
    pose proof DI as DI'; dinv_open DI';
    lazymatch goal with
    | R1 : 4096 <= DST /\ _, R2 : 4096 <= SRC /\ _, R3 : 4096 <= DT /\ _, TL : 1 <= tl <= 12, RSV : 0 <= rsv <= 255,
      LO : 4096 <= lo /\ _, SPB : SPV < 2^47, KLO : 0x10007fff8000 <= lo, UDT : unpoisoned m0 DT _, RDTS : rng RNG (shad DT) _,
      RSTK : rng RNG lo _, DSTA : dcap <= 0 \/ _, OS1 : DST + dcap <= lo \/ _, OS2 : SRC + n <= lo \/ _, OS3 : DT + 16388 <= lo \/ _,
      MU : munch _ m0 _ |- _ =>
        facts R1 R2 R3 TL RSV LO SPB KLO; afacts MU UDT RDTS RSTK DSTA R3 LO KLO; ffacts OS1 OS2 OS3 LO
    end.
  Ltac x2_dst :=
    lazymatch goal with UDST : 0 < dcap -> unpoisoned m0 DST _, RDST : 0 < dcap -> rng RNG DST _, RDSTS : 0 < dcap -> rng RNG (shad DST) _,
                        DSTA : dcap <= 0 \/ _, MU : munch _ m0 _, R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ _, LO : 4096 <= lo /\ _,
                        KLO : 0x10007fff8000 <= lo |- _ =>
      dfacts MU UDST RDST RDSTS DSTA R1 LO KLO end.     (* [comment removed for export] *)
  Ltac x2_src :=
    lazymatch goal with USRC : 0 < n -> unpoisoned m0 SRC _, RSRC : 0 < n -> rng RNG SRC _, RSRCS : 0 < n -> rng RNG (shad SRC) _,
                        DSTA : dcap <= 0 \/ _, MU : munch _ m0 _, R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ _, R2 : 4096 <= SRC /\ 0 <= n < 2^32 /\ _,
                        LO : 4096 <= lo /\ _, KLO : 0x10007fff8000 <= lo |- _ =>
      sfacts MU USRC RSRC RSRCS DSTA R1 R2 LO KLO end.

  (* [comment removed for export] *)
  Notation ST pc mm x1 x7 x8 x9 x10 x13 x14 x15 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp (Z_to_bv 64 (tl + 256 * rsv)) (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10
             (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) x13 x14 x15 (Z_to_bv 64 (DT + 4)) SB
             x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation ST0 pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation x2_ret := (AZ_huf_dx2.x2_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x2_fcc := (AZ_huf_dx2b.x2_fcc RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x2_loop5 := (AZ_huf_dx2l.x2_loop5 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x2_loop4 := (AZ_huf_dx2l4.x2_loop4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).

  (* [comment removed for export] *)
  Notation STh pc mm x1 x5 x6 x7 x8 x9 x10 x13 x14 x15 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 x8 x9 x10
             (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) x13 x14 x15 (Z_to_bv 64 (DT + 4)) SB
             x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma x2_small : forall mm bc pt pe dl (x1 x7 x8 x9 x13 x15 x18 x19 x20 x21 x30 x31 : word),
    DINV2 mm -> 1 <= n -> 1 <= bc <= 64 -> PINV (SRC + pt) -> dcap < 8 ->
    pe = DST + dcap -> dl = tl + 256 * rsv ->
    evtF bsegs RNG POST (STh 0x9a2b0 mm x1 (Z_to_bv 64 dl) (Z_to_bv 64 pe) x7 x8 x9 (Z_to_bv 64 DST) x13 (Z_to_bv 64 8) x15
                             x18 x19 x20 x21 (Z_to_bv 64 pt) (Z_to_bv 64 bc) x30 x31).
  Proof using All.
    intros mm bc pt pe dl x1 x7 x8 x9 x13 x15 x18 x19 x20 x21 x30 x31 DI HN HBC HP HD8 Hpe Hdl. subst pe dl.
    x2_open DI. x2_src.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - HBC; lia).
    destruct QR as (q & r & -> & HQ & HR).
    assert (RJ : 0 <= dcap <= 7 /\ 1 <= 8 * q + r <= 64 /\ 1 <= n <= 4294967296) by (clear - HD8 R1 R2 HBC HN; lia).
    destruct RJ as (RJ1 & RJ3 & RJ4).
    unfold pinv2 in HP. destruct HP as [HP0 | (O1 & O2)].
    - assert (PT0 : pt = 0) by (clear - HP0; lia). subst pt. kclean.
      kx_autoFLA tt [KAApp (SPV - 64) 64] [0x9a824] 40%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange n 1 4294967296; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 7; KZRange DT 4096 140737488338940]
        (@nil (Z * Z)) (@nil (Z * Z)).
      all: aside.
      all: try kx_mem.
      all: kx_abs.
      all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
      all: eapply x2_fcc; [dinv_close | exact HN | lia | lia | intros; unfold pinv2; lia].
    - kclean.
      assert (RO : 1 <= pt <= 4294967296 /\ 8 <= n - pt <= 4294967296 /\ 9 <= n <= 4294967296 /\ 4097 <= SRC + pt <= 140737488355320)
        by (clear - O1 O2 R2; lia).
      destruct RO as (RO1 & RO2 & RO3 & RO4).
      destruct (Z_lt_le_dec pt 8) as [C8|C8]; [destruct (Z_lt_le_dec pt q) as [CQ|CQ]|].
      1: assert (RC : 1 <= pt <= 7 /\ 1 <= q - pt <= 8) by (clear - RO1 C8 CQ HQ; lia); destruct RC as (RC1 & RC2).
      2: assert (RC : 1 <= pt <= 7 /\ 0 <= pt - q <= 7) by (clear - RO1 C8 CQ HQ; lia); destruct RC as (RC1 & RC2).
      3: assert (RC : 8 <= pt <= 4294967296 /\ 0 <= pt - q <= 4294967296) by (clear - RO1 C8 HQ; lia); destruct RC as (RC1 & RC2).
      3: kx_autoFLA tt [KAUnp SRC n; KAApp (SPV - 64) 64] [0x9a824] 120%nat
        [KZRange (n - pt) 8 4294967296; KZRange pt 8 4294967296; KZRange (pt - q) 0 4294967296; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange n 9 4294967296;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange (SRC + pt) 4097 140737488355320;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 7; KZRange DT 4096 140737488338940]
        [(SRC, n)] [(SRC, n)].
      2: kx_autoFLA tt [KAUnp SRC n; KAApp (SPV - 64) 64] [0x9a824] 120%nat
        [KZRange (n - pt) 8 4294967296; KZRange pt 1 7; KZRange (pt - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange n 9 4294967296;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange (SRC + pt) 4097 140737488355320;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 7; KZRange DT 4096 140737488338940]
        [(SRC, n)] [(SRC, n)].
      1: kx_autoFLA tt [KAUnp SRC n; KAApp (SPV - 64) 64] [0x9a824] 120%nat
        [KZRange (n - pt) 8 4294967296; KZRange pt 1 7; KZRange (q - pt) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange n 9 4294967296;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange (SRC + pt) 4097 140737488355320;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 7; KZRange DT 4096 140737488338940]
        [(SRC, n)] [(SRC, n)].
      all: aside.
      all: kx_mem.
      all: kx_abs.
      all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
      all: eapply x2_fcc; [dinv_close | exact HN | lia | lia | intros; unfold pinv2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_hdr : forall mm bc pt pe dl b01 hv (x1 x7 x8 x9 x15 x18 x19 x20 x21 x30 x31 : word),
    DINV2 mm -> 1 <= n -> 1 <= bc <= 64 -> PINV (SRC + pt) -> 8 <= dcap ->
    pe = DST + dcap -> dl = tl + 256 * rsv -> 0 <= b01 < 65536 -> hv = b01 + 65536 * (tl + 256 * rsv) ->
    evtF bsegs RNG POST (STh 0x99d98 mm x1 (Z_to_bv 64 dl) (Z_to_bv 64 pe) x7 x8 x9 (Z_to_bv 64 DST) (Z_to_bv 64 hv) (Z_to_bv 64 8) x15
                             x18 x19 x20 x21 (Z_to_bv 64 pt) (Z_to_bv 64 bc) x30 x31).
  Proof using All.
    intros mm bc pt pe dl b01 hv x1 x7 x8 x9 x15 x18 x19 x20 x21 x30 x31 DI HN HBC HP HD8 Hpe Hdl HB01 Hhv. subst pe dl hv.
    x2_open DI. kclean.
    assert (RJ : 8 <= dcap <= 4294967296 /\ 1 <= bc <= 64 /\ 0 <= b01 <= 65535 /\ 4104 <= DST + dcap <= 140737488355328) by (clear - HD8 R1 HBC HB01; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4).
    lazymatch goal with TL : 1 <= tl <= 12 |- _ => destruct (Z.eq_dec tl 12) as [T12|T12];
      [ assert (RT : 12 <= tl <= 12) by (clear - T12; lia) | assert (RT : 1 <= tl <= 11) by (clear - T12 TL; lia) ] end.
    all: kx_autoFLA tt [KAApp (SPV - 64) 64] [0x99dbc; 0x9a374] 30%nat
      [KZRange dcap 8 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + dcap) 4104 140737488355328; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
       KZRange bc 1 64; KZRange DT 4096 140737488338940; ltac:(lazymatch goal with RT : 12 <= tl <= 12 |- _ => exact (KZRange tl 12 12) | |- _ => exact (KZRange tl 1 11) end);
       KZRange rsv 0 255; KZRange b01 0 65535; KZRange SPV 17594333497648 140737488355328]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: try kx_mem.
    all: kit_sh_fix.
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x99dbc) _ _ _ _) =>
             eapply (x2_loop5 (Z.to_nat dcap)); first [exact HN | exact HP | reflexivity | lia | dinv_close]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9a374) _ _ _ _) =>
             eapply (x2_loop4 (Z.to_nat dcap)); first [exact HN | exact HP | reflexivity | lia | dinv_close]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_read : forall b0 b1, nth_error dtb 0 = Some b0 -> nth_error dtb 1 = Some b1 ->
    extz false 4 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat 0) dtb))) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * tl + 16777216 * rsv.
  Proof using All.
    intros b0 b1 DT0 DT1. pose proof CTX as CTX'. x1_ctx_open CTX'.
    assert (E : firstn 4 (skipn (Z.to_nat 0) dtb) = [b0; b1; Z_to_bv 8 tl; Z_to_bv 8 rsv]).
    { change (Z.to_nat 0) with 0%nat.
      destruct dtb as [|y0 [|y1 [|y2 [|y3 r]]]]; cbn in DT0, DT1, DT2, DT3; try discriminate.
      injection DT0 as ->. injection DT1 as ->. injection DT2 as ->. injection DT3 as ->. reflexivity. }
    rewrite E. unfold extz. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
    rewrite !(Z_to_bv_unsigned 8), !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). lia.
  Qed.

  Ltac x2_rd4 RD :=
    lazymatch goal with
    | KXA : atoms_ok ?zs _ |- _ =>
        let nz := kx_len zs in
        let rec go k := first [ (let j := eval vm_compute in (nz + k)%nat in kx_read_eq j RD;
                                 lazymatch type of RD with _ = rdval _ _ _ 4 false => idtac end)
                              | lazymatch k with 8%nat => fail | _ => go (S k) end ] in
        go 0%nat
    end.
  (* [comment removed for export] *)
  Lemma x2_post : forall mm bc pt (x1 x5 x6 x7 x8 x9 x13 x15 x16 x18 x19 x20 x21 x30 x31 : word),
    DINV2 mm -> 1 <= n -> 1 <= bc <= 64 -> PINV (SRC + pt) ->
    evtF bsegs RNG POST (ST0 0x99d64 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) x13 (Z_to_bv 64 DT) x15 x16 SB
                             x18 x19 x20 x21 (Z_to_bv 64 pt) (Z_to_bv 64 bc) x30 x31).
  Proof using All.
    intros mm bc pt x1 x5 x6 x7 x8 x9 x13 x15 x16 x18 x19 x20 x21 x30 x31 DI HN HB1 HP.
    x2_open DI.
    lazymatch goal with DL : zlen dtb = 16388 |- _ =>
      destruct (nth_error dtb 0) as [b0|] eqn:DT0; [| apply nth_error_None in DT0; exfalso; clear - DT0 DL; lia];
      destruct (nth_error dtb 1) as [b1|] eqn:DT1; [| apply nth_error_None in DT1; exfalso; clear - DT1 DL; lia] end.
    assert (B01 : 0 <= bv_unsigned b0 + 256 * bv_unsigned b1 < 65536)
      by (pose proof (bv_unsigned_in_range 8 b0); pose proof (bv_unsigned_in_range 8 b1); unfold bv_modulus in *; change (2 ^ Z.of_N 8) with 256 in *; lia).
    pose proof (conj DT0 DT1) as DT01. clear DT0 DT1.      (* [comment removed for export] *)
    assert (RJ : 1 <= n <= 4294967296 /\ 1 <= bc <= 64) by (clear - HN R2 HB1; lia). destruct RJ as (RJ1 & RJ2).
    kclean.
    assert (DTA4 : DT mod 4 = 0) by (generalize CTX; clear; intros C2; x1_ctx_open C2; exact DTA).
    destruct (Z.eq_dec dcap 0) as [DC0|DC1];
      [ assert (RD0 : 0 <= dcap <= 0) by (clear - DC0; lia) | assert (RD0 : 1 <= dcap <= 4294967296 /\ 4097 <= DST + dcap <= 140737488355328) by (clear - DC1 R1; lia); destruct RD0 as (RD0 & RD1) ].
    (* [comment removed for export] *)
    2: kx_autoFLA tt [KAUnp DT 16388; KAApp (SPV - 64) 64] [0x9a2b0; 0x99d98] 30%nat
        [KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 1 4294967296; KZRange (DST + dcap) 4097 140737488355328; KZRange n 1 4294967296;
         KZRange DT 4096 140737488338940; KZAlign DT 4; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328]
        [(DT, 16388)] [(DT, 16388)].
    1: kx_autoFLA tt [KAUnp DT 16388; KAApp (SPV - 64) 64] [0x9a2b0; 0x99d98] 30%nat
        [KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 0; KZRange n 1 4294967296;
         KZRange DT 4096 140737488338940; KZAlign DT 4; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328]
        [(DT, 16388)] [(DT, 16388)].
    all: aside.
    all: destruct DT01 as (DT0 & DT1).
    all: x2_rd4 RD;
         rewrite (rdval_bytes_at bsegs _ DT dtb 0 4 false DTB ltac:(lia) ltac:(change (Z.to_nat 0) with 0%nat; lia)), (hdr_read b0 b1 DT0 DT1) in RD;
         lazymatch type of RD with ev ?E ?j = _ =>
           assert (HX : bv_unsigned (ev E j) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * tl + 16777216 * rsv)
             by (rewrite RD, Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia) end;
         rewrite HX; rewrite RD.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9a2b0) _ _ _ _) =>
             eapply x2_small; [dinv_close | exact HN | lia | exact HP | lia | lia
                             | symmetry; apply Z.div_unique with (r := bv_unsigned b0 + 256 * bv_unsigned b1); lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x99d98) _ _ _ _) =>
             eapply x2_hdr with (b01 := bv_unsigned b0 + 256 * bv_unsigned b1);
             [dinv_close | exact HN | lia | exact HP | lia | lia
             | symmetry; apply Z.div_unique with (r := bv_unsigned b0 + 256 * bv_unsigned b1); lia | lia | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Ltac x2_err :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        let w := eval vm_compute in (v mod 2^64) in      (* [comment removed for export] *)
        replace (Z_to_bv 64 v) with (Z_to_bv 64 w) by (apply Z_to_bv_eqm; reflexivity);
        eapply x2_ret; [dinv_close | right; reflexivity | lia]
    end.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac x2_bc_enum :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?w _ _) _ _ _ _ _ _) =>
        let BCE := fresh "BCE" in
        kx_read_ranges;
        lazymatch w with
        | Z_to_bv 64 ?t =>
            first
              [ lazymatch t with context [edenot ?E ?e] => lazymatch e with context [EVar ?j] =>
                  let g := eval pattern (bv_unsigned (edenot E e)) in t in
                  lazymatch g with ?f _ =>
                    kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (f v) mod 2^64) && ((f v) mod 2^64 <=? 64))%bool end end end
              | lazymatch t with context [ev ?E ?j] =>
                  let g := eval pattern (bv_unsigned (ev E j)) in t in
                  lazymatch g with ?f _ =>
                    kx_enum BCE E (EVar j) j 1 255%nat (fun v => (1 <=? (f v) mod 2^64) && ((f v) mod 2^64 <=? 64))%bool;
                    change (edenot E (EVar j)) with (ev E j) in BCE end end ];
            cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2;
            replace w with (Z_to_bv 64 (t mod 2^64)) by (rewrite KXS.Z_to_bv64_mod; reflexivity)
        | edenot ?E ?e =>
            lazymatch e with context [EVar ?j] =>
              kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool end;
            cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2;
            replace w with (Z_to_bv 64 (bv_unsigned (edenot E e) mod 2^64)) by (rewrite KXS.Z_to_bv64_mod, Z_to_bv_bv_unsigned; reflexivity)
        | ev ?E ?j =>
            kx_enum BCE E (EVar j) j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool;
            change (edenot E (EVar j)) with (ev E j) in BCE;
            cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2;
            replace w with (Z_to_bv 64 (bv_unsigned (ev E j) mod 2^64)) by (rewrite KXS.Z_to_bv64_mod, Z_to_bv_bv_unsigned; reflexivity)
        end
    end.

  (* [comment removed for export] *)
  Lemma x2_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv bsegs m0 -> stk bsegs m0 lo SPV -> stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 SRC src -> bytes_at bsegs m0 DT dtb ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99a40) fc None m0 (seg_rom bsegs)).
  Proof using All.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof ART as ART'. destruct ART' as (GOT & RIC & SHB & INI & LAY & REAL).
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (MU : munch W0 m0 m0) by apply munch_refl.
    assert (WM : wmono bsegs m0 m0) by apply wmono_refl.
    carve_frame 56%nat STK.
    destruct (stk_open bsegs m0 lo (SPV + -56) (SPV + -64) 8 STK ltac:(lia) ltac:(lia)) as (g & GAP & STK1 & STK2).
    change (Z.of_nat 8) with 8 in STK2. clear STK STK2. rename STK1 into STK.
    assert (RFR : rng RNG (SPV - 64) 64) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    ffacts OS1 OS2 OS3 LO.
    destruct (Z.eq_dec n 0) as [N0|N1].
    - kx_autoFLA (GOT, SHB) [KAApp (SPV - 64) 64] [0x9abbc] 30%nat
        [KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange SRC 4096 140737488355328; KZRange n 0 0;
         KZRange DT 4096 140737488338940; KZRange (SRC + n) 4096 140737488355328;
         KZWr (SPV + -56) 56; KZDisj (SPV + -56) 56 DT 16388; KZDisj (SPV + -56) 56 SRC n; KZDisj DST dcap (SPV - 64) 64]
        (@nil (Z * Z)) [(SPV - 64, 64)].
      all: aside.
      all: kx_mem.
      all: x2_err.
    - x2_src.
      assert (CASES : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ 8 <= n) by lia.
      destruct CASES as [Nc | [Nc | [Nc | [Nc | [Nc | [Nc | [Nc | Nc]]]]]]].
      all: try (lazymatch goal with Nc : n = ?k |- _ => replace (Z_to_bv 64 n) with (Z_to_bv 64 k) by (rewrite Nc; reflexivity) end).
      all: kx_autoFLA (GOT, SHB) [KAUnp SRC n; KAApp (SPV - 64) 64] [0x9abbc; 0x99d64] 200%nat
           [KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange SRC 4096 140737488355328;
            ltac:(lazymatch goal with Nc : n = ?k |- _ => exact (KZRange n k k) | |- _ => exact (KZRange n 8 4294967296) end);
            KZRange DT 4096 140737488338940; KZRange (SRC + n) 4096 140737488355328;
            KZWr (SPV + -56) 56; KZDisj (SPV + -56) 56 DT 16388; KZDisj (SPV + -56) 56 SRC n; KZDisj DST dcap (SPV - 64) 64; KZImg 0x22308 0x22320]
           [(SRC, n)] [(SRC, n); (SPV - 64, 64)].
      all: aside.
      all: kx_mem.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9abbc) _ _ _ _) => x2_err
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x99d64) _ _ _ _) =>
               x2_bc_enum; eapply x2_post; [dinv_close | lia | lia | unfold pinv2; lia]
           end.
  Qed.
End DX2E.

(* [comment removed for export] *)
Theorem huf_1x2_proofB : bit_init_stmtA -> huf_1x2_stmtA.
Proof.
  intros BITINIT.
  unfold huf_1x2_stmtA, huf_int_stmtA_at, APHUF_1X2.
  intros until dtb.
  intros (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & ARD & ARS & ART & AST & AZS & ARC & SPA)
         (DTB & DL & T0 & T1 & OS3 & DJ2 & ARODT & DTA) DT2 TL X2 _.
  unfold HUF_DTABLE_BYTES in *.
  destruct AST as (KLO & RSTK & RI).
  destruct ARODT as (UDT & RDT & RDTS).
  destruct (nth_error dtb 3) as [b3|] eqn:DT3; [| apply nth_error_None in DT3; exfalso; lia].
  pose proof atop_range as ATR.
  assert (DSTA : dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)).
  { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd]; [| left; lia]. right.
    destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS, KHIGH in ABD |- *. lia. }
  assert (CTX : x1_ctx SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb).
  { pose proof (bv_unsigned_in_range 8 b3) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
    assert (EB : Z_to_bv 8 (bv_unsigned b3) = b3)
      by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    unfold x1_ctx. rewrite EB. unfold KHIGH in KLO. repeat split; try assumption; lia. }
  assert (ACTX : x1_actx RNG m SPV DST dcap SRC n DT lo).
  { unfold x1_actx.
    split; [| split; [exact UDT|]; split; [| split; [| split; [| split; [exact RDT|]; split; [exact RDTS|]; split; [| split; [| split; [exact RSTK | split; [exact RI | split; [exact AZS | exact ART]]]]]]]]].
    - intros Hn. destruct (ARS Hn) as (_ & U & _). exact U.
    - intros Hd. destruct (ARD Hd) as (_ & U & _). exact U.
    - intros Hn. destruct (ARS Hn) as (_ & _ & R & _). exact R.
    - intros Hn. destruct (ARS Hn) as (_ & _ & _ & R). exact R.
    - intros Hd. destruct (ARD Hd) as (_ & _ & R & _). exact R.
    - intros Hd. destruct (ARD Hd) as (_ & _ & _ & R). exact R. }
  exact (x2_entry RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
                  CTX (X2 eq_refl) ACTX t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB).
Qed.

Theorem huf_1x2_proofA : huf_1x2_stmtA.
Proof. exact (huf_1x2_proofB bit_init_proofA). Qed.
End CANSEC1.
