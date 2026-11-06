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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_kx AZ_hufkit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x1_ctx (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte) : Prop :=
  (4096 <= lo /\ lo <= SPV - 2352) /\ SPV < 2^47 /\ SPV mod 16 = 0 /\ 0x10007fff8000 <= lo /\
  zlen src = n /\ zlen dtb = 16388 /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255 /\
  (4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47) /\ (4096 <= SRC /\ 0 <= n < 2^32 /\ SRC + n < 2^47) /\
  (4096 <= DT /\ DT + 16388 < 2^47) /\ DT mod 4 = 0 /\
  (DST + dcap <= lo \/ SPV <= DST) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (DT + 16388 <= lo \/ SPV <= DT) /\
  (DST + dcap <= SRC \/ SRC + n <= DST) /\ (DST + dcap <= DT \/ DT + 16388 <= DST) /\
  nth_error dtb 2 = Some (Z_to_bv 8 tl) /\ nth_error dtb 3 = Some (Z_to_bv 8 rsv) /\
  (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)).
Ltac x1_ctx_open CTX :=
  destruct CTX as (LO & SPB & SPA & KLO & SL & DL & TL & RSV & R1 & R2 & R3 & DTA & OS1 & OS2 & OS3 & DJ1 & DJ2 & DT2 & DT3 & DSTA).

Definition x1_actx (RNG : footprint) (m0 : amem) (SPV DST dcap SRC n DT lo : Z) : Prop :=
  (0 < n -> unpoisoned m0 SRC (SRC + n)) /\ unpoisoned m0 DT (DT + 16388) /\ (0 < dcap -> unpoisoned m0 DST (DST + dcap)) /\
  (0 < n -> rng RNG SRC n) /\ (0 < n -> rng RNG (shad SRC) (shspan SRC n)) /\ rng RNG DT 16388 /\ rng RNG (shad DT) (shspan DT 16388) /\
  (0 < dcap -> rng RNG DST dcap) /\ (0 < dcap -> rng RNG (shad DST) (shspan DST dcap)) /\
  rng RNG lo (SPV - lo) /\ rng_aimg RNG /\ azstk RNG m0 lo SPV /\ art m0.
Ltac x1_actx_open ACTX :=
  destruct ACTX as (USRC & UDT & UDST & RSRC & RSRCS & RDT & RDTS & RDST & RDSTS & RSTK & RI & AZS & ART).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma munch_drop_empty : forall (m mm : amem) A W, munch ((A, A) :: W) m mm -> munch W m mm.
Proof.
  intros m mm A W MU. eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside]. split; [lia | exact Hx].
Qed.

Section DX1.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x1_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2352 [] m0 huf_noQ).
  Notation W0 := [(DST, DST + dcap); (SPV - 2352, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).

  (* [comment removed for export] *)
  Definition DINV (mm : amem) : Prop :=
    stk bsegs mm DST (DST + dcap) /\
    rw_cells bsegs mm (SPV + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk bsegs mm lo (SPV + -128) /\
    bytes_at bsegs mm SRC src /\ bytes_at bsegs mm DT dtb /\
    munch W0 m0 mm /\ wmono bsegs m0 mm /\ mem_inv bsegs mm.

  Definition BDC (mm : amem) (cw bcw : word) (pad : list byte) (pw : word) : Prop :=
    rw_cells bsegs mm (SPV + -128) [C8 cw; C4 bcw; CB 4 pad; C8 pw; C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 (SRC + 8))].

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold DINV; repeat (split; [eassumption|]); eassumption.

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
    assert (RFR : rng RNG (SPV - 128) 128) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
    assert (FF : (DST + dcap <= SPV - 128 \/ SPV - 128 + 128 <= DST) /\ (SPV - 128 + 40 <= DT \/ DT + 16388 <= SPV - 128) /\
                 (SPV - 128 + 40 <= SRC \/ SRC + n <= SPV - 128) /\ (SPV - 128 + 128 <= DT \/ DT + 16388 <= SPV - 128))
      by (clear - OS1 OS2 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4).
  (* [comment removed for export] *)
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
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  Ltac trap_close := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9c4dc) _ _ _ _) => kx_trap_fast | _ => idtac end.

  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12 x13 x14 x15 x16 x17
             SB (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * rsv)) x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma x1_ret : forall mm r csB (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    DINV mm -> rw_cells bsegs mm (SPV + -128) csB -> cells_size csB = 40%nat ->
    (r = dcap \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
    evtF bsegs RNG POST (ST 0x9c4a8 mm x1 x5 x6 x7 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros mm r csB x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 DI BD SZ HR HR2.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    dinv_open DI. facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 128) 128) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    pose proof (stk_of_rw_cells bsegs mm _ _ BD) as HB. rewrite SZ in HB. change (Z.of_nat 40) with 40 in HB.
    replace (SPV + -128 + 40) with (SPV + -88) in HB by lia.
    assert (STK2 : stk bsegs mm lo (SPV + -88)) by (eapply stk_merge; [exact STK | exact HB | lia]).
    clear STK HB BD. kclean.
    kx_autoFLAx [KAApp (SPV - 128) 128] [] 30%nat [KZRange SPV 17594333497648 (2^47)] [(SPV - 88, 88)] [(SPV - 128, 128)].
    all: aside.
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK2 SPV.
    all: apply evtF_done; unfold huf_dec_postA; repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK2|]);
         (split; [exact OUT|]); (split; [exact HR|]); split; [exact HR2 | exact I].
  Qed.


  (* [comment removed for export] *)
  Lemma x1_end : forall mm cw bcw pad pw (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    DINV mm -> BDC mm cw bcw pad pw ->
    evtF bsegs RNG POST (ST 0x9c488 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros mm cw bcw pad pw x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 DI BD.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof DI as DI'. dinv_open DI'. unfold BDC in BD. facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 128) 128) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    kclean.
    kx_autoFLAx (@nil kza) [0x9c4a8] 30%nat [KZRange SPV 17594333497648 (2^47); KZRange dcap 0 (2^32); KZRange SRC 4096 (2^47)]
      [(SPV - 128, 40)] [(SPV - 128, 128)].
    all: aside.
    all: kx_mem.
    all: first [ eapply x1_ret; [exact DI | exact BD | reflexivity | left; reflexivity | clear - GF2; lia]
               | eapply x1_ret; [exact DI | exact BD | reflexivity | right; vm_compute; reflexivity | lia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_tail : forall (k : nat) mm j sh nd cw bcw pad pw (x1 x5 x6 x7 x11 x12 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    DINV mm -> BDC mm cw bcw pad pw -> 0 <= j < dcap -> dcap - j <= Z.of_nat k -> 52 <= sh <= 63 -> nd = -1 * DT + -5 ->
    evtF bsegs RNG POST (ST 0x9c3c8 mm x1 x5 x6 x7 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + j)) x11 x12 (Z_to_bv 64 nd) (Z_to_bv 64 (dcap - j))
                           (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 sh) (Z_to_bv 64 2) x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros mm j sh nd cw bcw pad pw x1 x5 x6 x7 x11 x12 x22 x23 x24 x25 x28 x29 x30 x31 DI BD HJ HK HSH HND;
      [exfalso; lia|].
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof DI as DI'. dinv_open DI'. unfold BDC in BD. facts R1 R2 R3 TL RSV LO SPB KLO.
    afacts MU UDT RDTS RSTK DSTA R3 LO KLO. dfacts MU UDST RDST RDSTS DSTA R1 LO KLO. ffacts OS1 OS2 OS3 LO.
    subst nd. kclean.
    Time kx_autoFLAx [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 128) 128] [0x9c3c8; 0x9c488] 60%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange (DST + j) 4096 (2^47 - 1); KZRange SPV 17594333497648 (2^47);
       KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange sh 52 63; KZRange DT 4096 (2^47 - 16388);
       KZWr DST dcap; KZWr (SPV - 128) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 128) 128; KZDisj (SPV - 128) 40 DT 16388;
       KZDisj DST dcap SRC n; KZDisj (SPV - 128) 40 SRC n]
      [(DT, 16388); (SPV - 128, 40)] [(DT, 16388); (DST, dcap); (SPV - 128, 128)].
    all: aside.
    all: trap_close.
    Time all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9c488) _ _ _ _) => eapply x1_end; [dinv_close | unfold BDC; eassumption]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9c3c8) _ _ _ _) =>
             replace (DST + j + 1) with (DST + (j + 1)) by lia; replace (dcap + -1 * j + -1) with (dcap - (j + 1)) by lia;
             eapply IH; [dinv_close | unfold BDC; eassumption | lia | lia | exact HSH | reflexivity]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_tset : forall mm j cw bcw pad pw (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    DINV mm -> BDC mm cw bcw pad pw -> 0 <= j < dcap ->
    evtF bsegs RNG POST (ST 0x9c3a8 mm x1 x5 x6 x7 (Z_to_bv 64 (DST + j)) x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros mm j cw bcw pad pw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 DI BD HJ.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    facts R1 R2 R3 TL RSV LO SPB KLO. kclean.
    kx_autoFLAx (@nil kza) [0x9c3c8] 12%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange (tl + 256 * rsv) 1 65535; KZRange DT 4096 (2^47 - 16388)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    kit_sh_fix.
    replace (dcap + -1 * j) with (dcap - j) by lia.
    eapply (x1_tail (Z.to_nat (dcap - j))); [exact DI | exact BD | lia | lia | lia | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_594 : forall mm j cw bcw pad pw (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    DINV mm -> BDC mm cw bcw pad pw -> 0 <= j <= dcap ->
    evtF bsegs RNG POST (ST 0x9c3a4 mm x1 x5 x6 x7 (Z_to_bv 64 (DST + j)) x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros mm j cw bcw pad pw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 DI BD HJ.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    facts R1 R2 R3 TL RSV LO SPB KLO. kclean.
    kx_autoFLAx (@nil kza) [0x9c3a8; 0x9c488] 6%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9c488) _ _ _ _) => eapply x1_end; [exact DI | exact BD]
         | |- _ => eapply x1_tset; [exact DI | exact BD | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_4d8 : forall mm j cw bcw pad pw (x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    DINV mm -> BDC mm cw bcw pad pw -> 0 <= j <= dcap ->
    evtF bsegs RNG POST (ST 0x9c2e8 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 (Z_to_bv 64 (DST + j)) x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros mm j cw bcw pad pw x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 DI BD HJ.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    facts R1 R2 R3 TL RSV LO SPB KLO. kclean.
    kx_autoFLAx (@nil kza) [0x9c3a8; 0x9c488] 6%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9c488) _ _ _ _) => eapply x1_end; [exact DI | exact BD]
         | |- _ => eapply x1_tset; [exact DI | exact BD | lia]
         end.
  Qed.

End DX1.
End CANSEC1.
