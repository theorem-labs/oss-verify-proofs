(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_dx1.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
#[local] Ltac kx_path_hyp E zs nz KXA BR ::= kx_rr_dedup; kx_path_hyp_fast E zs nz KXA BR.
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dinv2 (ra s0 s1 s2 s3 s4 s5 : word) (m0 : amem) (SPV DST dcap SRC DT lo : Z) (src dtb : list byte) (mm : amem) : Prop :=
  stk bsegs mm DST (DST + dcap) /\
  rw_cells bsegs mm (SPV + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  (exists g, rw_cells bsegs mm (SPV + -64) [CB 8 g]) /\
  stk bsegs mm lo (SPV + -64) /\
  bytes_at bsegs mm SRC src /\ bytes_at bsegs mm DT dtb /\
  munch [(DST, DST + dcap); (SPV - 2352, SPV)] m0 mm /\ wmono bsegs m0 mm /\ mem_inv bsegs mm.
(* [comment removed for export] *)
Definition pinv2 (SRC n P : Z) : Prop := P = SRC \/ (SRC + 1 <= P /\ P + 8 <= SRC + n).

Section CANSEC1. Context {rc : runConstT}.
Section DX2A.
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

  (* [comment removed for export] *)
  Lemma x2_tbl : forall mm sh, bytes_at bsegs mm DT dtb -> sh = 64 - tl -> tbl_in_log bsegs mm DT sh 4 7 1 2.
  Proof using All.
    intros mm sh DTB ->. pose proof CTX as CTX'. x1_ctx_open CTX'.
    apply (tbl_in_log_bytes_at bsegs mm DT dtb (64 - tl) 4 7 1 2 DTB); [lia | lia |].
    intros i Hi. replace (64 - (64 - tl)) with tl in Hi by lia. exact (X2OK i Hi).
  Qed.

  (* [comment removed for export] *)
  Lemma x2_ret : forall mm r (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV2 mm ->
    (r = dcap \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
    evtF bsegs RNG POST (ST0 0x9abbc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 r) x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof using All.
    intros mm r x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HR HR2.
    x2_open DI.
    pose proof (stk_of_rw_cells bsegs mm _ _ GAP) as HG. change (Z.of_nat (cells_size [CB 8 g])) with 8 in HG.
    replace (SPV + -64 + 8) with (SPV + -56) in HG by lia.
    assert (STK2 : stk bsegs mm lo (SPV + -56)) by (eapply stk_merge; [exact STK | exact HG | lia]).
    clear STK HG GAP. kclean.
    kx_autoFLA FR [KAApp (SPV - 64) 64] [] 30%nat [KZRange SPV 17594333497648 140737488355328] [(SPV + -56, 56)] [(SPV - 64, 64)].
    all: [> aside ..].
    all: [> kx_mem ..].
    all: zstep.
    all: release_frame FR STK2 SPV.
    all: apply evtF_done; unfold huf_dec_postA; repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK2|]);
         (split; [exact OUT|]); (split; [exact HR|]); split; [exact HR2 | exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_end : forall mm (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV2 mm ->
    evtF bsegs RNG POST (ST0 0x9aba4 mm x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 dcap) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof using All.
    intros mm x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI.
    x2_open DI. kclean.
    kx_autoFLA tt (@nil kza) [0x9abbc] 30%nat [KZRange SPV 17594333497648 140737488355328; KZRange dcap 0 4294967296]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: [> aside ..].
    all: first [ eapply x2_ret; [exact DI | left; reflexivity | clear - GF2; lia]
               | eapply x2_ret; [exact DI | right; vm_compute; reflexivity | lia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_last : forall mm j (x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV2 mm -> 0 <= j < dcap ->
    evtF bsegs RNG POST (ST 0x9aa20 mm x1 x7 x8 x9 (Z_to_bv 64 (DST + j)) x13 x14 x15 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof using All.
    intros mm j x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x28 x29 x30 x31 DI HJ.
    x2_open DI. x2_dst. kclean.
    lazymatch goal with TL : 1 <= tl <= 12 |- _ =>
      assert (TLC : tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by (clear - TL; lia) end.
    assert (RJ : 1 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355327) by (clear - HJ R1; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3).
    repeat (destruct TLC as [TLC|TLC]).
    (* [comment removed for export] *)
    Time all: [> rewrite TLC;
      kx_autoFLA tt [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 64) 64] [0x9aba4] 60%nat
        [KZRange (dcap - j) 1 4294967296; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355327;
         KZRange DT 4096 140737488338940; KZRange rsv 0 255; KZRange SPV 17594333497648 140737488355328; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
         KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 64) 64;
         KZDisj DST dcap SRC n]
        [(DT, 16388)] [(DT, 16388); (DST, dcap); (SPV - 64, 64)] ..].
    all: [> aside ..].
    Time all: [> kx_mem ..].
    all: eapply x2_end; dinv_close.
  Qed.
  (* [comment removed for export] *)
  Lemma x2_874 : forall mm j (x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV2 mm -> 0 <= j <= dcap ->
    evtF bsegs RNG POST (ST 0x9aa1c mm x1 x7 x8 x9 (Z_to_bv 64 (DST + j)) x13 x14 x15 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof using All.
    intros mm j x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x28 x29 x30 x31 DI HJ.
    x2_open DI. kclean.
    assert (RJ : 0 <= j <= 4294967296) by (clear - HJ GF2; lia).
    kx_autoFLA tt (@nil kza) [0x9aa20; 0x9aba4] 6%nat [KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9aba4) _ _ _ _) => eapply x2_end; exact DI
         | |- _ => eapply x2_last; [exact DI | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_tail : forall (k : nat) mm j sh pm2 (x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x29 x30 : word),
    DINV2 mm -> 0 <= j -> j + 2 <= dcap -> dcap - j <= Z.of_nat k ->
    sh = 64 - tl -> pm2 = DST + dcap - 2 ->
    evtF bsegs RNG POST (ST 0x9aa9c mm x1 x7 x8 x9 (Z_to_bv 64 (DST + j)) x13 x14 x15 x18 x19 x20 x21
                           (Z_to_bv 64 pm2) x29 x30 (Z_to_bv 64 sh)).
  Proof using All.
    induction k as [|k IH]; intros mm j sh pm2 x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x29 x30
      DI HJ0 HJ HK HSH HPM; [exfalso; lia|].
    x2_open DI. x2_dst. kclean.
    lazymatch goal with DTB : bytes_at bsegs mm DT dtb |- _ =>
      assert (TBL : tbl_in_log bsegs mm DT sh 4 7 1 2) by (apply (x2_tbl mm sh DTB HSH)) end.
    assert (RJ : 2 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355326 /\ 52 <= sh <= 63)
      by (clear - HJ0 HJ R1 HSH GF8; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4).
    subst pm2.
    Time kx_autoFLA tt [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 64) 64] [0x9aa9c; 0x9aa1c] 60%nat
      [KZRange (dcap - j) 2 4294967296; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355326;
       KZRange DT 4096 140737488338940; KZRange sh 52 63; KZRange SPV 17594333497648 140737488355328; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 64) 64;
       KZDisj DST dcap SRC n; KZTblLog DT sh 4 7 1 2]
      [(DT, 16388)] [(DT, 16388); (DST, dcap); (SPV - 64, 64)].
    all: aside.
    all: len_range.
    (* [comment removed for export] *)
    all: kx_gen_regsF [8%nat; 9%nat; 13%nat; 14%nat; 15%nat; 29%nat]; intros.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9aa9c) _ _ _ _) =>
             eapply IH; [dinv_close | lia | lia | lia | exact HSH | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9aa1c) _ _ _ _) =>
             eapply x2_874; [dinv_close | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_870 : forall mm j sh pm2 (x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x29 x30 : word),
    DINV2 mm -> 0 <= j <= dcap -> sh = 64 - tl -> pm2 = DST + dcap - 2 ->
    evtF bsegs RNG POST (ST 0x9aa14 mm x1 x7 x8 x9 (Z_to_bv 64 (DST + j)) x13 x14 x15 x18 x19 x20 x21
                           (Z_to_bv 64 pm2) x29 x30 (Z_to_bv 64 sh)).
  Proof using All.
    intros mm j sh pm2 x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x29 x30 DI HJ HSH HPM.
    x2_open DI. kclean. subst pm2.
    assert (RJ : 0 <= j <= 4294967296) by (clear - HJ GF2; lia).
    kx_autoFLA tt (@nil kza) [0x9aa9c; 0x9aa1c] 6%nat [KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9aa9c) _ _ _ _) =>
             eapply (x2_tail (Z.to_nat (dcap - j))); [exact DI | lia | lia | lia | exact HSH | lia]
         | |- _ => eapply x2_874; [exact DI | lia]
         end.
  Qed.

End DX2A.
End CANSEC1.
