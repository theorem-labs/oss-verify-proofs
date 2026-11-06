(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_dx1 AZ_huf_bitinit AZ_huf_dx1e AZ_huf_dx2 AZ_huf_dx2b AZ_huf_dx2l AZ_huf_dx2l4.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  Notation DINV2 := (dinv2 ra s0 s1 s2 s3 s4 s5 s6 m0 SPV DST dcap SRC DT lo src dtb).
  Notation BDC2 := (bdc2 SPV SRC).
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
    assert (RFR : rng RNG (SPV - 112) 112) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
    assert (FF : (DST + dcap <= SPV - 112 \/ SPV - 112 + 112 <= DST) /\ (SPV + -104 + 40 <= DT \/ DT + 16388 <= SPV + -104) /\
                 (SPV + -104 + 40 <= SRC \/ SRC + n <= SPV + -104) /\ (SPV - 112 + 112 <= DT \/ DT + 16388 <= SPV - 112) /\
                 (DST + dcap <= SPV + -104 \/ SPV + -104 + 40 <= DST))
      by (clear - OS1 OS2 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4 & DJF5).
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
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + (_ + bv_unsigned (ev ?E ?k)))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        let H := fresh "LENR" in kx_erange H (EVar k); cbn [edenot] in H
    | |- _ => idtac
    end.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  Ltac trap_close := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8b0) _ _ _ _) => kx_trap_fast | _ => idtac end.
  (* [comment removed for export] *)
  Ltac x2_open DI BD :=
    let CTX' := fresh "CTX'" in let ACTX' := fresh "ACTX'" in let DI' := fresh "DI'" in
    pose proof CTX as CTX'; x1_ctx_open CTX'; pose proof ACTX as ACTX'; x1_actx_open ACTX';
    pose proof DI as DI'; dinv_open DI'; try unfold bdc2 in BD;
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
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (tl + 256 * rsv)) x17
             x18 SB x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation ST0 pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation x2_ret := (AZ_huf_dx2.x2_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x2_fcc := (AZ_huf_dx2b.x2_fcc RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x2_loop5 := (AZ_huf_dx2l.x2_loop5 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x2_loop4 := (AZ_huf_dx2l4.x2_loop4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).

  (* [comment removed for export] *)
  Notation STh pc mm x1 x5 x6 x7 x9 x10 x11 x12 x14 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12
             (Z_to_bv 64 (DT + 4)) x14 (Z_to_bv 64 2305843009213693952) x16 x17
             x18 SB x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma x2_small : forall mm bc P pe dl (cont : word) pad (x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    DINV2 mm -> BDC2 mm cont (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 1 <= bc <= 64 -> PINV P -> dcap < 8 ->
    pe = DST + dcap -> dl = tl + 256 * rsv ->
    evtF bsegs RNG POST (STh 0x9abe4 mm x1 x5 x6 x7 (Z_to_bv 64 DST) x10 x11 x12 (Z_to_bv 64 pe) (Z_to_bv 64 dl) x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    intros mm bc P pe dl cont pad x1 x5 x6 x7 x10 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 DI BD HN HBC HP HD8 Hpe Hdl. subst pe dl.
    x2_open DI BD. x2_src.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - HBC; lia).
    destruct QR as (q & r & -> & HQ & HR).
    assert (RJ : 0 <= dcap <= 7 /\ 1 <= 8 * q + r <= 64 /\ 1 <= n <= 4294967296) by (clear - HD8 R1 R2 HBC HN; lia).
    destruct RJ as (RJ1 & RJ3 & RJ4).
    destruct HP as [-> | (O1 & O2)].
    - kclean.
      kx_autoFLA BD [KAApp (SPV - 112) 112] [0x9b334] 40%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange n 1 4294967296; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 7; KZRange DT 4096 140737488338940;
         KZWr (SPV + -104) 40; KZDisj (SPV + -104) 40 SRC n; KZDisj (SPV + -104) 40 DT 16388; KZDisj DST dcap (SPV + -104) 40]
        [(SRC, n); (SPV + -104, 40)] [(SRC, n); (SPV - 112, 112)].
      all: aside.
      all: trap_close.
      all: kx_mem.
      all: kx_abs.
      all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
      all: eapply x2_fcc; [dinv_close | unfold bdc2; eassumption | exact HN | lia | lia | intros; unfold pinv2; lia].
    - assert (O : exists off, P = SRC + off) by (exists (P - SRC); lia). destruct O as (off & ->).
      kclean.
      assert (RO : 1 <= off <= 4294967296 /\ 8 <= n - off <= 4294967296 /\ 9 <= n <= 4294967296 /\ 4097 <= SRC + off <= 140737488355320)
        by (clear - O1 O2 R2; lia).
      destruct RO as (RO1 & RO2 & RO3 & RO4).
      destruct (Z_lt_le_dec off 8) as [C8|C8]; [destruct (Z_lt_le_dec off q) as [CQ|CQ]|].
      1: assert (RC : 1 <= off <= 7 /\ 1 <= q - off <= 8) by (clear - RO1 C8 CQ HQ; lia); destruct RC as (RC1 & RC2).
      2: assert (RC : 1 <= off <= 7 /\ 0 <= off - q <= 7) by (clear - RO1 C8 CQ HQ; lia); destruct RC as (RC1 & RC2).
      3: assert (RC : 8 <= off <= 4294967296 /\ 0 <= off - q <= 4294967296) by (clear - RO1 C8 HQ; lia); destruct RC as (RC1 & RC2).
      3: kx_autoFLA BD [KAUnp SRC n; KAApp (SPV - 112) 112] [0x9b334] 120%nat
        [KZRange (n - off) 8 4294967296; KZRange off 8 4294967296; KZRange (off - q) 0 4294967296; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange n 9 4294967296;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange (SRC + off) 4097 140737488355320;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 7; KZRange DT 4096 140737488338940;
         KZWr (SPV + -104) 40; KZDisj (SPV + -104) 40 SRC n; KZDisj (SPV + -104) 40 DT 16388; KZDisj DST dcap (SPV + -104) 40]
        [(SRC, n); (SPV + -104, 40)] [(SRC, n); (SPV - 112, 112)].
      2: kx_autoFLA BD [KAUnp SRC n; KAApp (SPV - 112) 112] [0x9b334] 120%nat
        [KZRange (n - off) 8 4294967296; KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange n 9 4294967296;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange (SRC + off) 4097 140737488355320;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 7; KZRange DT 4096 140737488338940;
         KZWr (SPV + -104) 40; KZDisj (SPV + -104) 40 SRC n; KZDisj (SPV + -104) 40 DT 16388; KZDisj DST dcap (SPV + -104) 40]
        [(SRC, n); (SPV + -104, 40)] [(SRC, n); (SPV - 112, 112)].
      1: kx_autoFLA BD [KAUnp SRC n; KAApp (SPV - 112) 112] [0x9b334] 120%nat
        [KZRange (n - off) 8 4294967296; KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange n 9 4294967296;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange (SRC + off) 4097 140737488355320;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 7; KZRange DT 4096 140737488338940;
         KZWr (SPV + -104) 40; KZDisj (SPV + -104) 40 SRC n; KZDisj (SPV + -104) 40 DT 16388; KZDisj DST dcap (SPV + -104) 40]
        [(SRC, n); (SPV + -104, 40)] [(SRC, n); (SPV - 112, 112)].
      all: aside.
      all: trap_close.
      all: kx_mem.
      all: kx_abs.
      all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
      all: eapply x2_fcc; [dinv_close | unfold bdc2; eassumption | exact HN | lia | lia | intros; unfold pinv2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_hdr : forall mm bc P pe dl b01 hv (cont : word) pad (x1 x5 x6 x7 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    DINV2 mm -> BDC2 mm cont (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 1 <= bc <= 64 -> PINV P -> 8 <= dcap ->
    pe = DST + dcap -> dl = tl + 256 * rsv -> 0 <= b01 < 65536 -> hv = b01 + 65536 * (tl + 256 * rsv) ->
    evtF bsegs RNG POST (STh 0x9a4a8 mm x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 hv) x11 x12 (Z_to_bv 64 pe) (Z_to_bv 64 dl) x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    intros mm bc P pe dl b01 hv cont pad x1 x5 x6 x7 x11 x12 x17 x18 x20 x21 x22 x28 x29 x30 x31 DI BD HN HBC HP HD8 Hpe Hdl HB01 Hhv. subst pe dl hv.
    x2_open DI BD. kclean.
    assert (RJ : 8 <= dcap <= 4294967296 /\ 1 <= bc <= 64 /\ 0 <= b01 <= 65535 /\ 4104 <= DST + dcap <= 140737488355328) by (clear - HD8 R1 HBC HB01; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4).
    lazymatch goal with TL : 1 <= tl <= 12 |- _ => destruct (Z.eq_dec tl 12) as [T12|T12];
      [ assert (RT : 12 <= tl <= 12) by (clear - T12; lia) | assert (RT : 1 <= tl <= 11) by (clear - T12 TL; lia) ] end.
    all: kx_autoFLA BD [KAApp (SPV - 112) 112] [0x9a4f4; 0x9acc0; 0x9b334] 60%nat
      [KZRange dcap 8 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + dcap) 4104 140737488355328; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
       KZRange bc 1 64; KZRange DT 4096 140737488338940; ltac:(lazymatch goal with RT : 12 <= tl <= 12 |- _ => exact (KZRange tl 12 12) | |- _ => exact (KZRange tl 1 11) end);
       KZRange rsv 0 255; KZRange b01 0 65535; KZRange SPV 17594333497648 140737488355328;
       KZWr (SPV + -104) 40; KZDisj (SPV + -104) 40 SRC n; KZDisj (SPV + -104) 40 DT 16388; KZDisj DST dcap (SPV + -104) 40]
      [(SPV + -104, 40)] [(SPV - 112, 112)].
    all: aside.
    all: trap_close.
    all: kx_mem.
    all: kit_sh_fix.
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9a4f4) _ _ _ _) =>
             eapply (x2_loop5 (Z.to_nat dcap)); [dinv_close | unfold bdc2; eassumption | exact HN | lia | lia | lia | reflexivity | lia | lia | exact HP]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9acc0) _ _ _ _) =>
             eapply (x2_loop4 (Z.to_nat dcap)); [dinv_close | unfold bdc2; eassumption | exact HN | lia | lia | lia | reflexivity | lia | lia | exact HP]
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

  (* [comment removed for export] *)
  Lemma x2_post : forall mm bc cont pad (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    DINV2 mm -> BDC2 mm cont (Z_to_bv 64 bc) pad (Z_to_bv 64 (bitd_ptr SRC n)) -> 1 <= n -> 1 <= bc <= 64 -> (8 <= n -> bc <= 8) ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 0x9a42c) (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 DT) SB s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9a42c) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros mm bc cont pad x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 DI BD HN HB1 HB2.
    x2_open DI BD.
    assert (PI : PINV (bitd_ptr SRC n)) by (unfold pinv2, bitd_ptr; destruct (8 <=? n) eqn:E8; [apply Z.leb_le in E8 | apply Z.leb_gt in E8]; lia).
    lazymatch goal with DL : zlen dtb = 16388 |- _ =>
      destruct (nth_error dtb 0) as [b0|] eqn:DT0; [| apply nth_error_None in DT0; exfalso; clear - DT0 DL; lia];
      destruct (nth_error dtb 1) as [b1|] eqn:DT1; [| apply nth_error_None in DT1; exfalso; clear - DT1 DL; lia] end.
    assert (B01 : 0 <= bv_unsigned b0 + 256 * bv_unsigned b1 < 65536)
      by (pose proof (bv_unsigned_in_range 8 b0); pose proof (bv_unsigned_in_range 8 b1); unfold bv_modulus in *; change (2 ^ Z.of_N 8) with 256 in *; lia).
    pose proof (conj BD PI) as BDh. clear BD PI.      (* [comment removed for export] *)
    pose proof (conj DT0 DT1) as DT01. clear DT0 DT1.
    assert (RJ : 1 <= n <= 4294967296 /\ 1 <= bc <= 64) by (clear - HN R2 HB1; lia). destruct RJ as (RJ1 & RJ2).
    kclean.
    assert (DTA4 : DT mod 4 = 0) by (generalize CTX; clear; intros C2; x1_ctx_open C2; exact DTA).
    destruct (Z.eq_dec dcap 0) as [DC0|DC1];
      [ assert (RD0 : 0 <= dcap <= 0) by (clear - DC0; lia) | assert (RD0 : 1 <= dcap <= 4294967296 /\ 4097 <= DST + dcap <= 140737488355328) by (clear - DC1 R1; lia); destruct RD0 as (RD0 & RD1) ].
    (* [comment removed for export] *)
    2: kx_autoFLA tt [KAUnp DT 16388; KAApp (SPV - 112) 112] [0x9abe4; 0x9a4a8; 0x9b888] 60%nat
        [KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 1 4294967296; KZRange (DST + dcap) 4097 140737488355328; KZRange n 1 4294967296;
         KZRange DT 4096 140737488338940; KZAlign DT 4; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328]
        [(DT, 16388)] [(DT, 16388); (SPV - 112, 112)].
    1: kx_autoFLA tt [KAUnp DT 16388; KAApp (SPV - 112) 112] [0x9abe4; 0x9a4a8; 0x9b888] 60%nat
        [KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 0; KZRange n 1 4294967296;
         KZRange DT 4096 140737488338940; KZAlign DT 4; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328]
        [(DT, 16388)] [(DT, 16388); (SPV - 112, 112)].
    all: aside.
    all: trap_close.
    all: destruct BDh as (BD & PI); destruct DT01 as (DT0 & DT1).
    all: kx_read_eq 31%nat RD;
         rewrite (rdval_bytes_at bsegs _ DT dtb 0 4 false DTB ltac:(lia) ltac:(change (Z.to_nat 0) with 0%nat; lia)), (hdr_read b0 b1 DT0 DT1) in RD;
         assert (HX : bv_unsigned (ev KXE 31) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * tl + 16777216 * rsv)
           by (rewrite RD, Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia);
         rewrite HX; rewrite RD.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9abe4) _ _ _ _) =>
             eapply x2_small; [dinv_close | unfold bdc2; exact BD | exact HN | lia | exact PI | lia | lia
                             | symmetry; apply Z.div_unique with (r := bv_unsigned b0 + 256 * bv_unsigned b1); lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9a4a8) _ _ _ _) =>
             eapply x2_hdr with (b01 := bv_unsigned b0 + 256 * bv_unsigned b1);
             [dinv_close | unfold bdc2; exact BD | exact HN | lia | exact PI | lia | lia
             | symmetry; apply Z.div_unique with (r := bv_unsigned b0 + 256 * bv_unsigned b1); lia | lia | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_post_e : forall mm r csB (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    DINV2 mm -> rw_cells bsegs mm (SPV + -104) csB -> cells_size csB = 40%nat -> zd_is_error r = true -> r < 2^64 ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 0x9a42c) (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 DT) SB s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9a42c) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros mm r csB x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 DI BD SZ HE HR.
    pose proof CTX as CTX'. x1_ctx_open CTX'.
    assert (HE' : 2^64 - 120 < r) by (unfold zd_is_error, ZE_maxCode in HE; apply Z.ltb_lt in HE; exact HE).
    assert (RR : 18446744073709551497 <= r <= 18446744073709551615) by (clear - HE' HR; lia).
    pose proof (conj BD SZ) as BDh. clear BD SZ.      (* [comment removed for export] *)
    kx_autoFLA tt (@nil kza) [0x9b888] 10%nat [KZRange r 18446744073709551497 18446744073709551615] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    destruct BDh as (BD & SZ).
    eapply x2_ret; [exact DI | exact BD | exact SZ | right; exact HE | lia].
  Qed.

  Hypothesis BITINIT : bit_init_stmtA.
  (* [comment removed for export] *)
  Hypothesis DHI : 0 < dcap -> 0x629000 <= DST.

  (* [comment removed for export] *)
  Ltac x2_call m1 jb :=
    lazymatch goal with
    | MU : munch _ m0 m1, WM : wmono _ m0 m1, MI1 : mem_inv _ m1, BD0 : rw_cells _ m1 (SPV + -104) [CB 40 jb], STK1 : stk _ m1 lo (SPV + -112),
      SRCB : bytes_at _ m1 SRC src,
      LO : 4096 <= lo <= SPV - 2352, KLO : 0x10007fff8000 <= lo, SPB : SPV < 2^47, SPA : SPV mod 16 = 0, SL : Z.of_nat (length src) = n,
      R1 : 4096 <= DST /\ _, R2 : 4096 <= SRC /\ _, OS2 : SRC + n <= lo \/ SPV <= SRC, DSTA : dcap <= 0 \/ _,
      AZS : azstk RNG m0 lo SPV, ART : art m0, RSTK : rng RNG lo (SPV - lo), RI : rng_aimg RNG,
      USRC : 0 < n -> unpoisoned m0 SRC (SRC + n), RSRC : 0 < n -> rng RNG SRC n, RSRCS : 0 < n -> rng RNG (shad SRC) (shspan SRC n) |- _ =>
      let AW0 := fresh "AW0" in let AZmm := fresh "AZmm" in let ARTmm := fresh "ARTmm" in let RBD := fresh "RBD" in
      let AROB := fresh "AROB" in let AHB := fresh "AHB" in let APB := fresh "APB" in let ASTK' := fresh "ASTK'" in let BDA := fresh "BDA" in
      assert (AW0 : aappW [(SPV - 2352, SPV)]) by (apply Forall_cons; [cbn [fst snd]; unfold KHIGH; clear - LO KLO; lia | apply Forall_nil]);
      assert (AZmm : azstk RNG m1 lo SPV)
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply azstk_transport; [exact AZS | exact MU | exact WM | apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; clear - DSTA Hd; lia | exact AW0] | clear - LO; lia]
            | eapply azstk_transport; [exact AZS | eapply munch_drop_empty; replace (DST + dcap) with DST in MU by (clear - Hd R1; lia); exact MU
                                      | exact WM | exact AW0 | clear - LO; lia] ]);
      assert (ARTmm : art m1)
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply (art_transportW _ m0 m1 ART MU WM); constructor; [cbn [fst]; pose proof (DHI Hd); lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]]
            | eapply (art_transportW [(SPV - 2352, SPV)] m0 m1 ART); [| exact WM |];
              [ eapply munch_drop_empty; replace (DST + dcap) with DST in MU by (clear - Hd R1; lia); exact MU
              | constructor; [cbn [fst]; clear - LO KLO; lia | constructor] ] ]);
      assert (RBD : rng RNG (SPV + -104) 40) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]);
      assert (AROB : aro RNG m1 (SPV + -104) 40) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | lia | lia | exact RBD]);
      assert (AHB : ahull RNG m1 (SPV + -104) 40) by (eapply azstk_ahull; [exact AZmm | clear - LO; lia | lia | lia]);
      assert (APB : app_blk (SPV + -104) (SPV + -104 + 40)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | lia | lia]);
      assert (ASTK' : astk RNG lo (SPV + -112))
        by (split; [unfold KHIGH; clear - KLO; lia | split; [eapply rng_sub; [exact RSTK | lia | clear - LO; lia] | exact RI]]);
      assert (BDA : (SPV + -104) mod 8 = 0) by (clear - SPA SPB LO; lia);
      let NUMS := fresh "NUMS" in
      assert (NUMS : (4096 <= SPV + -104) /\ (SPV + -104 + 40 < 2^47) /\ (SPV + -104 + 40 <= SRC \/ SRC + n <= SPV + -104) /\
                     (lo <= SPV + -112 - 2224) /\ (SPV + -112 < 2^47) /\ (SPV + -104 + 40 <= lo \/ SPV + -112 <= SPV + -104) /\
                     (SRC + n <= lo \/ SPV + -112 <= SRC) /\ (SRC + n < 2^47) /\ (n < 2^32) /\ (4096 <= SRC))
        by (clear - LO SPB R2 OS2; lia);
      let P1 := fresh "P" in let P2 := fresh "P" in let P3 := fresh "P" in let P4 := fresh "P" in let P5 := fresh "P" in
      let P6 := fresh "P" in let P7 := fresh "P" in let P8 := fresh "P" in let P9 := fresh "P" in let P10 := fresh "P" in
      destruct NUMS as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10);
      let AROS := fresh "AROS" in
      assert (AROS : 0 < n -> aro RNG m1 SRC n)
        by (intros Hn; split; [| split; [exact (RSRC Hn) | exact (RSRCS Hn)]];
            eapply unp_carryS; [exact (USRC Hn) | exact MU | clear - R2; lia | clear - R2; lia | clear - DSTA; lia | clear - LO KLO; lia]);
      clear AW0 AZmm RBD;
      eapply evtF_cut;
        [ eapply (bit_init_g BITINIT RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -112) (SPV + -104) SRC n lo src jb);
          [ exact MI1 | exact BD0 | exact BDA | exact SRCB | exact SL | exact P1 | exact P2 | exact P10 | exact P8 | exact P9 | exact P3
          | exact STK1 | exact P4 | exact P5 | exact P6 | exact P7 | exact APB | exact AROB | exact AHB | exact AROS | exact ARTmm | exact ASTK' ]
        | clear BD0 STK1 ARTmm AROB AHB APB ASTK' AROS BDA P1 P2 P3 P4 P5 P6 P7 P8 P9 P10;
          unfold bit_init_postA; post_call bsegs m1 ]
    end.
  Ltac x2_after_call :=
    lazymatch goal with
    | POST : (_ /\ _) \/ (_ /\ _) |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
        destruct POST as [(HR & HN1 & cont & bc & pad & HB1 & HB2 & BDC1) | (HER & HRB & bs & BDC1)];
        [ first [ exfalso; clear - HN1; lia
                | lazymatch type of HR with ?rr = n => subst rr end; unfold bitd_cells in BDC1;
                  eapply (x2_post m2 bc cont pad); [dinv_close | unfold bdc2; exact BDC1 | exact HN1 | exact HB1 | exact HB2] ]
        | eapply (x2_post_e m2 _ [CB 40 bs]); [dinv_close | exact BDC1 | reflexivity | exact HER | exact HRB] ]
    end.

  (* [comment removed for export] *)
  Lemma x2_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv bsegs m0 -> stk bsegs m0 lo SPV -> stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 SRC src -> bytes_at bsegs m0 DT dtb ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a3e0) fc None m0 (seg_rom bsegs)).
  Proof using All.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof ART as ART'. destruct ART' as (GOT & RIC & SHB & INI & LAY & REAL).
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (MU : munch W0 m0 m0) by apply munch_refl.
    assert (WM : wmono bsegs m0 m0) by apply wmono_refl.
    carve_frame 64%nat STK.
    destruct (stk_open bsegs m0 lo (SPV + -64) (SPV + -104) 40 STK ltac:(lia) ltac:(lia)) as (jb & BD0 & STK1 & STK2).
    change (Z.of_nat 40) with 40 in STK2. clear STK STK2.
    destruct (stk_open bsegs m0 lo (SPV + -104) (SPV + -112) 8 STK1 ltac:(lia) ltac:(lia)) as (g & GAP & STK & STK3).
    change (Z.of_nat 8) with 8 in STK3. clear STK1 STK3. rename STK into STK1.
    assert (RFR : rng RNG (SPV - 112) 112) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    ffacts OS1 OS2 OS3 LO.
    kx_autoFLA (GOT, SHB) [KAApp (SPV - 112) 112] [0xa55d8] 30%nat
      [KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange SRC 4096 140737488355328; KZRange n 0 4294967296;
       KZRange DT 4096 140737488338940; KZRange (SRC + n) 4096 140737488355328;
       KZWr (SPV + -64) 64; KZDisj (SPV + -64) 64 DT 16388; KZDisj (SPV + -64) 64 SRC n; KZDisj DST dcap (SPV - 112) 112]
      (@nil (Z * Z)) [(SPV - 112, 112)].
    all: aside.
    all: trap_close.
    kx_mem.
    clear KXK KXA KXRD.
    lazymatch goal with K : mem_inv _ ?mq |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1; rename K into MI1 end.
    clear GF1 GF2 GF3 GF4 GF5 GF6 GF7 GF8 GF9 GF10 GF11 GF12 GF13 DJF1 DJF2 DJF3 DJF4 DJF5 RFR.
    x2_call m1 jb.
    all: x2_after_call.
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
  assert (DHI : 0 < dcap -> 0x629000 <= DST).
  { intros Hd. destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS in ABD. lia. }
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
                  CTX (X2 eq_refl) ACTX BITINIT DHI t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB).
Qed.

Theorem huf_1x2_proofA : huf_1x2_stmtA.
Proof. exact (huf_1x2_proofB bit_init_proofA). Qed.
End CANSEC1.
