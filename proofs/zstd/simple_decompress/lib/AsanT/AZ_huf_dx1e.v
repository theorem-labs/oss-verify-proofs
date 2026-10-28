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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_libc_iface AZ_libc AZ_huf_iface AZ_kx AZ_hufkit AZ_huf_bitinit AZ_huf_dx1 AZ_huf_dx1l.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
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
  Notation DINV := (AZ_huf_dx1.DINV ra s0 s1 s2 s3 s4 s5 s6 m0 SPV DST dcap SRC DT lo src dtb).
  Notation LINV := (AZ_huf_dx1l.LINV n).
  Notation x1_ret := (AZ_huf_dx1.x1_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x1_594 := (AZ_huf_dx1.x1_594 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x1_tset := (AZ_huf_dx1.x1_tset RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x1_4d8 := (AZ_huf_dx1.x1_4d8 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x1_end := (AZ_huf_dx1.x1_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
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
    assert (RFR : rng RNG (SPV - 64) 64) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
    assert (FF : (DST + dcap <= SPV - 64 \/ SPV <= DST) /\ (SPV <= DT \/ DT + 16388 <= SPV - 64) /\
                 (SPV <= SRC \/ SRC + n <= SPV - 64))
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
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.

  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Ltac x1_bc_enum :=
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
                    kx_enum BCE E e j 1 255%nat (fun v => (0 <=? (f v) mod 2^64) && ((f v) mod 2^64 <=? 64))%bool end end end
              | lazymatch t with context [ev ?E ?j] =>
                  let g := eval pattern (bv_unsigned (ev E j)) in t in
                  lazymatch g with ?f _ =>
                    kx_enum BCE E (EVar j) j 1 255%nat (fun v => (0 <=? (f v) mod 2^64) && ((f v) mod 2^64 <=? 64))%bool;
                    change (edenot E (EVar j)) with (ev E j) in BCE end end ];
            cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2;
            replace w with (Z_to_bv 64 (t mod 2^64)) by (rewrite KXS.Z_to_bv64_mod; reflexivity)
        | edenot ?E ?e =>
            lazymatch e with context [EVar ?j] =>
              kx_enum BCE E e j 1 255%nat (fun v => (0 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool end;
            cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2;
            replace w with (Z_to_bv 64 (bv_unsigned (edenot E e) mod 2^64)) by (rewrite KXS.Z_to_bv64_mod, Z_to_bv_bv_unsigned; reflexivity)
        | ev ?E ?j =>
            kx_enum BCE E (EVar j) j 1 255%nat (fun v => (0 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool;
            change (edenot E (EVar j)) with (ev E j) in BCE;
            cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2;
            replace w with (Z_to_bv 64 (bv_unsigned (ev E j) mod 2^64)) by (rewrite KXS.Z_to_bv64_mod, Z_to_bv_bv_unsigned; reflexivity)
        end
    end.

  Ltac x1_e_ret :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        first
          [ eapply x1_ret; [first [eassumption | dinv_close] | left; lia | lia]
          | let w := eval vm_compute in (v mod 2^64) in
            replace (Z_to_bv 64 v) with (Z_to_bv 64 w) by (apply Z_to_bv_eqm; reflexivity);
            eapply x1_ret; [first [eassumption | dinv_close] | right; reflexivity | lia] ]
    end.

  (* [comment removed for export] *)
  Lemma x1_post : forall mm d0 pe (x1 x7 x8 x9 x13 x14 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    DINV mm -> 8 <= n ->
    d0 = dcap -> pe = DST + dcap ->       (* [comment removed for export] *)
    evtF bsegs RNG POST
      (ST 0x9b0f0 mm x1 (Z_to_bv 64 pe) (Z_to_bv 64 (DT + 4)) x7 x8 x9 (Z_to_bv 64 DST) (Z_to_bv 64 d0) (Z_to_bv 64 SRC) x13 x14
          (Z_to_bv 64 n) (Z_to_bv 64 (tl + 256 * rsv)) SB x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof using All.
    intros mm d0 pe x1 x7 x8 x9 x13 x14 x18 x19 x20 x21 x22 x28 x29 x30 x31 DI HN Hd0 Hpe. subst d0 pe.
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
    lazymatch goal with USRC : 0 < n -> unpoisoned m0 SRC _, RSRC : 0 < n -> rng RNG SRC _, RSRCS : 0 < n -> rng RNG (shad SRC) _,
                        DSTA : dcap <= 0 \/ _, MU : munch _ m0 _, R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ _, R2 : 4096 <= SRC /\ 0 <= n < 2^32 /\ _,
                        LO : 4096 <= lo /\ _, KLO : 0x10007fff8000 <= lo |- _ =>
      sfacts MU USRC RSRC RSRCS DSTA R1 R2 LO KLO end.
    assert (RJ1 : 8 <= n <= 4294967296) by (clear - HN R2; lia).
    kclean.
    destruct (Z_lt_le_dec dcap 4) as [D4|D4].
    (* [comment removed for export] *)
    1: kx_autoFLAx [KAUnp SRC n] [0x9b21c; 0x9b484; 0x9b8e4] 200%nat
         [KZRange n 8 (2^32); KZRange dcap 0 3; KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
          KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388);
          KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535; KZImg 0x22320 0x22338]
         [(SRC, n)] [(SRC, n)].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: lazymatch goal with
         | D : (4 <= dcap)%Z |- _ =>
             kx_autoFLAx [KAUnp SRC n] [0x9b920; 0x9b970; 0x9b984; 0x9b21c; 0x9b46c; 0x9b484; 0x9b8e4] 200%nat
               [KZRange n 8 (2^32); KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
                KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388);
                KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535; KZImg 0x22320 0x22338]
               [(SRC, n)] [(SRC, n)];
             aside; kx_mem; kit_sh_fix
         | |- _ => idtac
         end.
    all: aside.
    all: kx_mem.
    all: kit_sh_fix.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b21c) _ _ _ _) =>
             x1_bc_enum;
             lazymatch goal with
             | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?b) _ _) _ _ _ _ _ _) =>
                 set (bb := b) in *; clearbody bb
             end;
             kx_autoFLAx [KAUnp SRC n] [0x9b818; 0x9b81c; 0x9b8c8; 0x9b8e4] 200%nat
               [KZRange n 8 (2^32); KZRange dcap 0 3; KZRange bb 0 64; KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
                KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388);
                KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535; KZImg 0x22320 0x22338]
               [(SRC, n)] [(SRC, n)];
             aside; kx_mem; kit_sh_fix
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b46c) _ _ _ _) =>
             x1_bc_enum;
             lazymatch goal with
             | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?b) _ _) _ _ _ _ _ _) =>
                 set (bb := b) in *; clearbody bb
             end;
             kx_autoFLAx [KAUnp SRC n] [0x9b484] 20%nat
               [KZRange n 8 (2^32); KZRange dcap 4 (2^32); KZRange bb 0 64; KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
                KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388);
                KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535; KZImg 0x22320 0x22338]
               [(SRC, n)] [(SRC, n)];
             aside; kx_mem; kit_sh_fix
         | |- _ => idtac
         end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8e4) _ _ _ _) => x1_e_ret
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b484) _ _ _ _) =>
             try replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
             eapply (x1_loop (S (Z.to_nat dcap)) _ 0);
               [first [eassumption | dinv_close] | lia | lia | lia | unfold AZ_huf_dx1l.LINV; lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8c8) _ _ _ _) => eapply x1_end; first [eassumption | dinv_close]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b818) _ _ _ _) =>
             try replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
             eapply x1_594; [first [eassumption | dinv_close] | lia]
         | |- _ =>
             try replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
             eapply x1_tset; [first [eassumption | dinv_close] | lia]
         end.
  Qed.

  Ltac x1_small_walk k dlo dhi :=
    kx_autoFLAx [KAUnp SRC n] [0x9b484; 0x9b81c; 0x9b8c8; 0x9b8e4] 200%nat
      [KZRange n k k; KZRange dcap dlo dhi; KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
       KZRange SRC 4096 (2^47); KZRange SPV 17594333497648 (2^47); KZRange DT 4096 (2^47 - 16388);
       KZRange tl 1 12; KZRange rsv 0 255; KZRange (tl + 256 * rsv) 1 65535; KZImg 0x22320 0x22338]
      [(SRC, n)] [(SRC, n)].

  Ltac x1_e_tset :=
    try replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
    eapply x1_tset; [first [eassumption | dinv_close] | lia].

  Ltac x1_e_head :=
    try x1_bc_enum;
    try replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
    eapply (x1_loop (S (Z.to_nat dcap)) _ 0);
      [first [eassumption | dinv_close] | lia | lia | lia | unfold AZ_huf_dx1l.LINV; split; [lia | left; lia]].

  (* [comment removed for export] *)
  Lemma x1_post_e : forall mm d0 pe (x1 x7 x8 x9 x13 x14 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    DINV mm -> 1 <= n <= 7 ->
    d0 = dcap -> pe = DST + dcap ->
    evtF bsegs RNG POST
      (ST 0x9b2cc mm x1 (Z_to_bv 64 pe) (Z_to_bv 64 (DT + 4)) x7 x8 x9 (Z_to_bv 64 DST) (Z_to_bv 64 d0) (Z_to_bv 64 SRC) x13 x14
          (Z_to_bv 64 n) (Z_to_bv 64 (tl + 256 * rsv)) SB x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros mm d0 pe x1 x7 x8 x9 x13 x14 x18 x19 x20 x21 x22 x28 x29 x30 x31 DI HN Hd0 Hpe. subst d0 pe.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof DI as DI'. dinv_open DI'. facts R1 R2 R3 TL RSV LO SPB KLO.
    afacts MU UDT RDTS RSTK DSTA R3 LO KLO. sfacts MU USRC RSRC RSRCS DSTA R1 R2 LO KLO. ffacts OS1 OS2 OS3 LO. kclean.
    assert (NC : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7) by lia.      (* [comment removed for export] *)
    destruct NC as [NE|[NE|[NE|[NE|[NE|[NE|NE]]]]]]; rewrite NE; destruct (Z_lt_le_dec dcap 4) as [D4|D4].
    all: lazymatch goal with
         | NE : n = ?k, D4 : dcap < 4 |- _ => x1_small_walk k 0 3
         | NE : n = ?k, D4 : 4 <= dcap |- _ => x1_small_walk k 4 (2^32)
         end.
    all: aside.
    all: kx_mem.
    all: kit_sh_fix.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8e4) _ _ _ _) => x1_e_ret
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b484) _ _ _ _) => x1_e_head
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8c8) _ _ _ _) => eapply x1_end; first [eassumption | dinv_close]
         | |- _ => x1_e_tset
         end.
  Qed.
  (* [comment removed for export] *)
  Hypothesis DHI : 0 < dcap -> 0x625000 <= DST.

  (* [comment removed for export] *)
  Ltac x1_ent_walk CH dlo dhi nlo nhi :=
    kx_autoFLA CH [KAUnp DT 16388; KAApp (SPV - 64) 64] [0x9b0f0; 0x9b2cc; 0x9b8e4] 60%nat
      [KZRange SPV 17594333497648 (2^47); KZRange DST 4096 (2^47); KZRange dcap dlo dhi; KZRange (DST + dcap) 4096 (2^47);
       KZRange SRC 4096 (2^47); KZRange n nlo nhi;
       KZRange DT 4096 (2^47 - 16388); KZAlign DT 4; KZWr (SPV - 64) 64; KZDisj (SPV - 64) 64 DT 16388; KZDisj (SPV - 64) 64 SRC n;
       KZDisj DST dcap (SPV - 64) 64]
      [(DT, 16388)] [(DT, 16388); (SPV - 64, 64)].
  Ltac dl_fix j DTB DT2 DT3 :=
    let RD := fresh "RD" in kx_read_eq j RD;
    rewrite (rdval_bytes_at bsegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)),
            (dl_read_g dtb tl rsv DT2 DT3 ltac:(lia) ltac:(lia)) in RD;
    rewrite RD; clear RD.

  (* [comment removed for export] *)
  Lemma x1_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv bsegs m0 -> stk bsegs m0 lo SPV -> stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 SRC src -> bytes_at bsegs m0 DT dtb ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9b088) fc None m0 (seg_rom bsegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof ART as ART'. destruct ART' as (GOT & RIC & SHB & INI & LAY & REAL).
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (MU : munch W0 m0 m0) by apply munch_refl.
    assert (WM : wmono bsegs m0 m0) by apply wmono_refl.
    carve_frame 64%nat STK.
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz.
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDT ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz.
    assert (RFR : rng RNG (SPV - 64) 64) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    ffacts OS1 OS2 OS3 LO.
    destruct (Z.eq_dec dcap 0) as [DC0|DC1]; (destruct (Z.eq_dec n 0) as [N0|N1]; [| destruct (Z_lt_le_dec n 8) as [N8|N8]]).
    all: let dl := lazymatch goal with _ : dcap = 0 |- _ => constr:(0) | _ => constr:(1) end in
         let dh := lazymatch goal with _ : dcap = 0 |- _ => constr:(0) | _ => constr:(2^32 - 1) end in
         let nl := lazymatch goal with _ : n = 0 |- _ => constr:(0) | _ : n < 8 |- _ => constr:(1) | _ => constr:(8) end in
         let nh := lazymatch goal with _ : n = 0 |- _ => constr:(0) | _ : n < 8 |- _ => constr:(7) | _ => constr:(2^32 - 1) end in
         x1_ent_walk (GOT, SHB) dl dh nl nh.
    all: aside.
    all: first [ dl_fix 30%nat DTB DT2 DT3 | dl_fix 31%nat DTB DT2 DT3 | dl_fix 32%nat DTB DT2 DT3 | dl_fix 33%nat DTB DT2 DT3
               | dl_fix 34%nat DTB DT2 DT3 | dl_fix 35%nat DTB DT2 DT3 | dl_fix 36%nat DTB DT2 DT3 | idtac ].
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8e4) _ _ _ _) => eapply x1_ret; [dinv_close | right; vm_compute; reflexivity | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b0f0) _ _ _ _) => eapply x1_post; [dinv_close | lia | lia | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b2cc) _ _ _ _) => eapply x1_post_e; [dinv_close | lia | lia | lia]
         end.
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
  assert (DHI : 0 < dcap -> 0x625000 <= DST).
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
                  CTX ACTX DHI t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB).
Qed.

Theorem huf_1x1_proofA : huf_1x1_stmtA.
Proof. exact (huf_1x1_proofB bit_init_proofA). Qed.
End CANSEC1.
