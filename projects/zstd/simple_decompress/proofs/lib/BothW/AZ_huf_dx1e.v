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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_libc_iface AZ_libc AZ_huf_iface AZ_kx AZ_hufkit AZ_huf_bitinit AZ_huf_dx1 AZ_huf_dx1l.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Lemma dl_read_g : forall (dtb : list byte) tl rsv, nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) ->
  0 <= tl <= 255 -> 0 <= rsv <= 255 ->
  extz false 2 (bytes_le_to_Z (firstn 2 (skipn (Z.to_nat 2) dtb))) = tl + 256 * rsv.
Proof.
  intros dtb tl rsv DT2 DT3 TL RSV.
  assert (E : firstn 2 (skipn (Z.to_nat 2) dtb) = [Z_to_bv 8 tl; Z_to_bv 8 rsv]).
  { change (Z.to_nat 2) with 2%nat.
    destruct dtb as [|x0 [|x1 [|x2 [|x3 r]]]]; cbn in DT2, DT3; try discriminate.
    injection DT2 as ->. injection DT3 as ->. reflexivity. }
  rewrite E. unfold extz. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
  rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma disjoint_from_aboveK : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  intros W A n K HW LE. induction HW as [|[x y] W Hx HW IH]; cbn [disjoint_from]; [exact I|].
  cbn [fst] in Hx. split; [lia | exact IH].
Qed.
Lemma art_transportW : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd5d40 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply disjoint_from_aboveK; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply disjoint_from_aboveK; [exact HW| cbn; lia]] ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bit_init0 : forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV BD SRC lo : Z) (junk : list byte),
  mem_inv bsegs m -> rw_cells bsegs m BD [CB 40 junk] -> BD mod 8 = 0 -> 4096 <= BD -> BD + 40 < 2^47 ->
  stk bsegs m lo SPV -> lo <= SPV - 2224 -> SPV < 2^47 -> (BD + 40 <= lo \/ SPV <= BD) ->
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> ahull RNG m BD 40 -> art m -> astk RNG lo SPV ->
  evtF bsegs RNG (bit_init_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD SRC 0 lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APHUF_BITINIT) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI BDC BDA B0 B1 STK LOS SPB OSB APB AROB AHB ART AST. unfold APHUF_BITINIT.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct AROB as (UB & RB & RBS).
  pose proof atop_range as ATR.
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (MU : munch [(BD, BD + 40); (SPV - 2224, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  pose proof STK as STK0.
  carve_frame 16%nat STK.
  destruct AHB as (RLO & RHI & AH1 & AH2 & AH3 & AH4 & AH5 & AH6 & AHW & AHR).
  kx_autoFLAx [KAApp (SPV - 16) 16] (@nil Z) 20%nat
    [KZRange SPV 4096 (2^47); KZWr (SPV - 16) 16] [(SPV - 16, 16)] [(SPV - 16, 16)].
  all: try kx_cell_lit; try kx_z; try kx_acc RI.
  kx_mem.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (unp_carryS m mc BD 40 SPV 2224 BD (BD + 40) UB MU ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as UBc
  end.
  call (zd_memsetZ_proofA RNG BD 40 0 (SPV - 16)).
  (* [comment removed for export] *)
  all: try exact STK.
  all: try exact BDC.
  all: try (split; [exact UBc | split; [exact RB | exact RBS]]).
  all: try (exists RLO, RHI; repeat (split; [first [assumption | lia]|]); exact AHR).
  all: try (split; [| split; [| split; [| split; [| split]]]]; assumption).
  all: try (eapply astk_sub; [split; [unfold KHIGH; lia|]; split; [exact RSTK | exact RI] | lia]).
  all: try assumption. all: try reflexivity. all: try lia.
  (* [comment removed for export] *)
  kx_autoFLAx [KAApp (SPV - 16) 16] (@nil Z) 10%nat [KZRange SPV 4096 (2^47)] [(SPV - 16, 16)] [(SPV - 16, 16)].
  all: try kx_cell_lit; try kx_z; try kx_acc RI.
  kx_mem. zstep.
  lazymatch goal with ST' : stk _ ?mc lo (SPV - 16) |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    replace (SPV - 16) with (SPV + -16) in ST' by lia; release_frame FR ST' SPV end.
  apply evtF_done; unfold bit_init_postA; repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  right. split; [vm_compute; reflexivity|]. split; [reflexivity|].
  lazymatch goal with |- exists bs, rw_cells _ ?mc BD _ => lazymatch goal with H : rw_cells _ mc BD [CB _ ?l] |- _ => exists l; exact H end end.
Qed.

(* [comment removed for export] *)
Lemma bit_init_g : bit_init_stmtA ->
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV BD SRC n lo : Z) (src junk : list byte),
  mem_inv bsegs m ->
  rw_cells bsegs m BD [CB 40 junk] -> BD mod 8 = 0 ->
  bytes_at bsegs m SRC src -> zlen src = n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
  (BD + 40 <= SRC \/ SRC + n <= BD) ->
  stk bsegs m lo SPV -> lo <= SPV - BITINIT_STACK_A -> SPV < 2^47 ->
  (BD + 40 <= lo \/ SPV <= BD) -> (SRC + n <= lo \/ SPV <= SRC) ->
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> ahull RNG m BD 40 -> (0 < n -> aro RNG m SRC n) ->
  art m -> astk RNG lo SPV ->
  evtF bsegs RNG (bit_init_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD SRC n lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APHUF_BITINIT) fc None m (seg_rom bsegs)).
Proof.
  intros BI. intros until junk. intros MI BDC BDA SRCB SL B0 B1 S0 S1 N32 DJ STK LOS SPB OSB OSS APB AROB AHB AROS ART AST.
  destruct (Z.eq_dec n 0) as [E|N1].
  - rewrite E in *. eapply bit_init0; eassumption.
  - eapply BI; try eassumption. apply AROS. lia.
Qed.

(* [comment removed for export] *)
Section DX1E.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x1_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2352 [] m0 huf_noQ).
  Notation W0 := [(DST, DST + dcap); (SPV - 2352, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation DINV := (AZ_huf_dx1.DINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m0 SPV DST dcap SRC DT lo src dtb).
  Notation BDC := (AZ_huf_dx1.BDC SPV SRC).
  Notation LINV := (AZ_huf_dx1l.LINV SRC n).
  Notation x1_ret := (AZ_huf_dx1.x1_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x1_594 := (AZ_huf_dx1.x1_594 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x1_loop := (AZ_huf_dx1l.x1_loop RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold AZ_huf_dx1.DINV; repeat (split; [eassumption|]); eassumption.
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333497648 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333495296 <= SPV - 2352) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  Ltac afacts MU0 UDT RDTS RSTK DSTA R3 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (eapply unp_carryS; [exact UDT | exact MU0 | clear - R3; lia | clear - R3; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 128) 128) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
  Ltac ffacts OS1 OS2 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 128 \/ SPV - 128 + 128 <= DST) /\ (SPV - 128 + 40 <= DT \/ DT + 16388 <= SPV - 128) /\
                 (SPV - 128 + 40 <= SRC \/ SRC + n <= SPV - 128) /\ (SPV - 128 + 128 <= DT \/ DT + 16388 <= SPV - 128))
      by (clear - OS1 OS2 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4).
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

  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12 x13 x14 x15 x16 x17
             SB (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * rsv)) x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma x1_post : forall mm bc cont pad d0 pe (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    DINV mm -> BDC mm cont (Z_to_bv 64 bc) pad (Z_to_bv 64 (bitd_ptr SRC n)) -> 1 <= n -> 1 <= bc <= 64 -> (8 <= n -> bc <= 8) ->
    d0 = dcap -> pe = DST + dcap ->       (* [comment removed for export] *)
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 0x9bd6c) (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 (Z_to_bv 64 d0) (Z_to_bv 64 DST) (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
               SB (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 pe) (Z_to_bv 64 (tl + 256 * rsv)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9bd6c) fc None mm (seg_rom bsegs)).
  Proof.
    intros mm bc cont pad d0 pe x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 DI BD HN HB1 HB2 Hd0 Hpe. subst d0 pe.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof DI as DI'. dinv_open DI'. unfold AZ_huf_dx1.BDC, bitd_ptr in BD. facts R1 R2 R3 TL RSV LO SPB KLO.
    afacts MU UDT RDTS RSTK DSTA R3 LO KLO. sfacts MU USRC RSRC RSRCS DSTA R1 R2 LO KLO. ffacts OS1 OS2 OS3 LO.
    destruct (Z_lt_le_dec dcap 4) as [D4|D4].
    - (* [comment removed for export] *)
      assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - HB1; lia).
      destruct QR as (q & r & -> & HQ & HR).
      destruct (Z_lt_le_dec n 8) as [N8|N8];
        [ replace (8 <=? n) with false in BD by (symmetry; apply Z.leb_gt; lia)
        | replace (8 <=? n) with true in BD by (symmetry; apply Z.leb_le; lia);
          replace (SRC + n - 8) with (SRC + (n - 8)) in BD by lia;
          assert (HB8 : 8 * q + r <= 8) by (apply HB2; lia) ].
      2: destruct (Z_lt_le_dec n 16) as [N16|N16]; [destruct (Z.eq_dec n 8) as [E8|E8]|].
      all: kclean.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      4: kx_autoFLAx [KAUnp SRC n; KAApp (SPV - 128) 128] [0x9c3a4] 120%nat
           [KZRange n 16 (2^32); KZRange (n - 8) 8 (2^32); KZRange (n - 8 - q) 7 (2^32); KZRange q 0 1; KZRange r 0 7; KZRange (8 * q + r) 1 8; KZRange dcap 0 3;
            KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + (n - 8)) 4104 (2^47 - 8);
            KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388);
            KZWr (SPV - 128) 40; KZDisj (SPV - 128) 40 SRC n; KZDisj (SPV - 128) 40 DT 16388; KZDisj DST dcap (SPV - 128) 128]
           [(SRC, n); (SPV - 128, 40)] [(SRC, n); (SPV - 128, 128)].
      (* [comment removed for export] *)
      3: kx_autoFLAx [KAUnp SRC n; KAApp (SPV - 128) 128] [0x9c3a4] 120%nat
           [KZRange n 9 15; KZRange (n - 8) 1 7; KZRange (n - 8 - q) 0 7; KZRange q 0 1; KZRange r 0 7; KZRange (8 * q + r) 1 8; KZRange dcap 0 3;
            KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + (n - 8)) 4097 (2^47 - 8);
            KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388);
            KZWr (SPV - 128) 40; KZDisj (SPV - 128) 40 SRC n; KZDisj (SPV - 128) 40 DT 16388; KZDisj DST dcap (SPV - 128) 128]
           [(SRC, n); (SPV - 128, 40)] [(SRC, n); (SPV - 128, 128)].
      (* [comment removed for export] *)
      2: kx_autoFLAx [KAApp (SPV - 128) 128] [0x9c3a4] 40%nat
           [KZRange n 8 8; KZRange (n - 8) 0 0; KZRange q 0 1; KZRange r 0 7; KZRange (8 * q + r) 1 8; KZRange dcap 0 3; KZRange DST 4096 (2^47);
            KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388)]
           [(SPV - 128, 40)] [(SRC, n); (SPV - 128, 128)].
      (* [comment removed for export] *)
      1: kx_autoFLAx [KAApp (SPV - 128) 128] [0x9c3a4] 40%nat
           [KZRange n 1 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange dcap 0 3; KZRange DST 4096 (2^47);
            KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388)]
           [(SPV - 128, 40)] [(SRC, n); (SPV - 128, 128)].
      all: aside.
      all: trap_close.
      all: kx_mem.
      all: kx_abs.
      all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
      all: eapply x1_594; [dinv_close | unfold AZ_huf_dx1.BDC; eassumption | lia].
    - (* [comment removed for export] *)
      kclean.
      kx_autoFLAx [KAApp (SPV - 128) 128] [0x9bdc8] 40%nat
        [KZRange n 1 (2^32); KZRange bc 1 64; KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4100 (2^47);
         KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388);
         KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535]
        [(SPV - 128, 40)] [(SRC, n); (SPV - 128, 128)].
      all: aside.
      all: trap_close.
      all: kx_mem.
      all: kit_sh_fix.
      all: eapply (x1_loop (Z.to_nat dcap));
        [ dinv_close | unfold AZ_huf_dx1.BDC; eassumption | exact HN | lia | lia | lia | lia | reflexivity
        | unfold AZ_huf_dx1l.LINV; destruct (Z.leb_spec 8 n); lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_post_e : forall mm r csB d0 pe (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    DINV mm -> rw_cells bsegs mm (SPV + -128) csB -> cells_size csB = 40%nat -> zd_is_error r = true -> r < 2^64 ->
    d0 = dcap -> pe = DST + dcap ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 0x9bd6c) (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 (Z_to_bv 64 d0) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               SB (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 pe) (Z_to_bv 64 (tl + 256 * rsv)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9bd6c) fc None mm (seg_rom bsegs)).
  Proof.
    intros mm r csB d0 pe x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 DI BD SZ HE HR Hd0 Hpe. subst d0 pe.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    facts R1 R2 R3 TL RSV LO SPB KLO. kclean.
    assert (HE' : 2^64 - 120 < r) by (unfold zd_is_error, ZE_maxCode in HE; apply Z.ltb_lt in HE; exact HE).
    pose proof (conj BD SZ) as BDh. clear BD SZ.      (* [comment removed for export] *)
    kx_autoFLAx (@nil kza) [0x9c4a8] 10%nat [KZRange r 18446744073709551497 18446744073709551615] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    destruct BDh as (BD & SZ).
    eapply x1_ret; [exact DI | exact BD | exact SZ | right; exact HE | lia].
  Qed.
  Hypothesis BITINIT : bit_init_stmtA.
  (* [comment removed for export] *)
  Hypothesis DHI : 0 < dcap -> 0x629000 <= DST.

  (* [comment removed for export] *)
  Ltac x1_call m1 jb :=
    lazymatch goal with
    | MU : munch _ m0 m1, WM : wmono _ m0 m1, MI1 : mem_inv _ m1, BD0 : rw_cells _ m1 (SPV + -128) [CB 40 jb], STK1 : stk _ m1 lo (SPV + -128),
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
      assert (RBD : rng RNG (SPV + -128) 40) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]);
      assert (AROB : aro RNG m1 (SPV + -128) 40) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | lia | lia | exact RBD]);
      assert (AHB : ahull RNG m1 (SPV + -128) 40) by (eapply azstk_ahull; [exact AZmm | clear - LO; lia | lia | lia]);
      assert (APB : app_blk (SPV + -128) (SPV + -128 + 40)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | lia | lia]);
      assert (ASTK' : astk RNG lo (SPV + -128))
        by (split; [unfold KHIGH; clear - KLO; lia | split; [eapply rng_sub; [exact RSTK | lia | clear - LO; lia] | exact RI]]);
      assert (BDA : (SPV + -128) mod 8 = 0) by (clear - SPA SPB LO; lia);
      let NUMS := fresh "NUMS" in
      assert (NUMS : (4096 <= SPV + -128) /\ (SPV + -128 + 40 < 2^47) /\ (SPV + -128 + 40 <= SRC \/ SRC + n <= SPV + -128) /\
                     (lo <= SPV + -128 - 2224) /\ (SPV + -128 < 2^47) /\ (SPV + -128 + 40 <= lo \/ SPV + -128 <= SPV + -128) /\
                     (SRC + n <= lo \/ SPV + -128 <= SRC) /\ (SRC + n < 2^47) /\ (n < 2^32) /\ (4096 <= SRC))
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
        [ eapply (bit_init_g BITINIT RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -128) (SPV + -128) SRC n lo src jb);
          [ exact MI1 | exact BD0 | exact BDA | exact SRCB | exact SL | exact P1 | exact P2 | exact P10 | exact P8 | exact P9 | exact P3
          | exact STK1 | exact P4 | exact P5 | exact P6 | exact P7 | exact APB | exact AROB | exact AHB | exact AROS | exact ARTmm | exact ASTK' ]
        | clear BD0 STK1 ARTmm AROB AHB APB ASTK' AROS BDA P1 P2 P3 P4 P5 P6 P7 P8 P9 P10;
          unfold bit_init_postA; post_call bsegs m1 ]
    end.
  Ltac x1_after_call :=
    lazymatch goal with
    | POST : (_ /\ _) \/ (_ /\ _) |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
        destruct POST as [(HR & HN1 & cont & bc & pad & HB1 & HB2 & BDC1) | (HER & HRB & bs & BDC1)];
        [ first [ exfalso; clear - HN1; lia
                | lazymatch type of HR with ?rr = n => subst rr end; unfold bitd_cells in BDC1;
                  eapply (x1_post m2 bc cont pad); [dinv_close | unfold AZ_huf_dx1.BDC; exact BDC1 | exact HN1 | exact HB1 | exact HB2 | lia | lia] ]
        | eapply (x1_post_e m2 _ [CB 40 bs]); [dinv_close | exact BDC1 | reflexivity | exact HER | exact HRB | lia | lia] ]
    end.

  (* [comment removed for export] *)
  Lemma x1_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv bsegs m0 -> stk bsegs m0 lo SPV -> stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 SRC src -> bytes_at bsegs m0 DT dtb ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9bcd8) fc None m0 (seg_rom bsegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof ART as ART'. destruct ART' as (GOT & RIC & SHB & INI & LAY & REAL).
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (MU : munch W0 m0 m0) by apply munch_refl.
    assert (WM : wmono bsegs m0 m0) by apply wmono_refl.
    carve_frame 88%nat STK.
    destruct (stk_open bsegs m0 lo (SPV + -88) (SPV + -128) 40 STK ltac:(lia) ltac:(lia)) as (jb & BD0 & STK1 & STK2).
    change (Z.of_nat 40) with 40 in STK2. clear STK STK2.
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz.
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDT ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz.
    assert (RFR : rng RNG (SPV - 128) 128) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    ffacts OS1 OS2 OS3 LO.
    destruct (Z.eq_dec dcap 0) as [DC0|DC1].
    - kx_autoFLAx [KAUnp DT 16388; KAApp (SPV - 128) 128] [0xa55d8] 60%nat
        [KZRange SPV 17594333497648 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 0; KZRange SRC 4096 (2^47); KZRange n 0 (2^32);
         KZRange DT 4096 (2^47 - 16388); KZAlign DT 4; KZWr (SPV - 88) 88; KZDisj (SPV - 88) 88 DT 16388; KZDisj (SPV - 88) 88 SRC n;
         KZDisj DST dcap (SPV - 128) 128]
        [(DT, 16388)] [(DT, 16388); (SPV - 128, 128)].
      all: aside.
      all: trap_close.
      kx_read_eq 32%nat RD.
      rewrite (rdval_bytes_at bsegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)),
              (dl_read_g dtb tl rsv DT2 DT3 ltac:(lia) ltac:(lia)) in RD.
      rewrite RD. kx_mem.
      clear KXK KXA KXRD RD.
      lazymatch goal with K : mem_inv _ ?mq |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1; rename K into MI1 end.
      clear GF1 GF2 GF3 GF4 GF5 GF6 GF7 GF8 GF9 GF10 GF11 GF12 GF13 DJF1 DJF2 DJF3 DJF4 RDTz UDTz RFR.
      x1_call m1 jb.
      all: x1_after_call.
    - kx_autoFLAx [KAUnp DT 16388; KAApp (SPV - 128) 128] [0xa55d8] 60%nat
        [KZRange SPV 17594333497648 (2^47); KZRange DST 4096 (2^47); KZRange dcap 1 (2^32 - 1); KZRange (DST + dcap) 4097 (2^47);
         KZRange SRC 4096 (2^47); KZRange n 0 (2^32);
         KZRange DT 4096 (2^47 - 16388); KZAlign DT 4; KZWr (SPV - 88) 88; KZDisj (SPV - 88) 88 DT 16388; KZDisj (SPV - 88) 88 SRC n;
         KZDisj DST dcap (SPV - 128) 128]
        [(DT, 16388)] [(DT, 16388); (SPV - 128, 128)].
      all: aside.
      all: trap_close.
      kx_read_eq 32%nat RD.
      rewrite (rdval_bytes_at bsegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)),
              (dl_read_g dtb tl rsv DT2 DT3 ltac:(lia) ltac:(lia)) in RD.
      rewrite RD. kx_mem.
      clear KXK KXA KXRD RD.
      lazymatch goal with K : mem_inv _ ?mq |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1; rename K into MI1 end.
      clear GF1 GF2 GF3 GF4 GF5 GF6 GF7 GF8 GF9 GF10 GF11 GF12 GF13 DJF1 DJF2 DJF3 DJF4 RDTz UDTz RFR.
      x1_call m1 jb.
      all: x1_after_call.
  Qed.

End DX1E.

(* [comment removed for export] *)
Theorem huf_1x1_proofB : bit_init_stmtA -> huf_1x1_stmtA.
Proof.
  intros BITINIT.
  unfold huf_1x1_stmtA, huf_int_stmtA_at, APHUF_1X1.
  intros until dtb.
  intros (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & ARD & ARS & ART & AST & AZS & ARC & SPA)
         (DTB & DL & T0 & T1 & OS3 & DJ2 & ARODT & DTA) DT2 TL _ _.
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
  exact (x1_entry RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
                  CTX ACTX BITINIT DHI t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB).
Qed.

Theorem huf_1x1_proofA : huf_1x1_stmtA.
Proof. exact (huf_1x1_proofB bit_init_proofA). Qed.
End CANSEC1.
