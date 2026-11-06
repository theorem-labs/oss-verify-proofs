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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x41a_ctx (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte) : Prop :=
  (4096 <= lo /\ lo <= SPV - 2720) /\ SPV < 2^47 /\ SPV mod 16 = 0 /\ 0x10007fff8000 <= lo /\
  zlen src = n /\ zlen dtb = 16388 /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255 /\
  (4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47) /\ (4096 <= SRC /\ 0 <= n < 2^32 /\ SRC + n < 2^47) /\
  (4096 <= DT /\ DT + 16388 < 2^47) /\
  (DST + dcap <= lo \/ SPV <= DST) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (DT + 16388 <= lo \/ SPV <= DT) /\
  (DST + dcap <= SRC \/ SRC + n <= DST) /\ (DST + dcap <= DT \/ DT + 16388 <= DST) /\
  nth_error dtb 2 = Some (Z_to_bv 8 tl) /\ nth_error dtb 3 = Some (Z_to_bv 8 rsv) /\
  (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)) /\
  DT mod 4 = 0.                                   (* [comment removed for export] *)
Ltac x41a_ctx_open CTX :=
  destruct CTX as (LO & SPB & SPA & KLO & SL & DL & TL & RSV & R1 & R2 & R3 & OS1 & OS2 & OS3 & DJ1 & DJ2 & DT2 & DT3 & DSTA & DTA).

Definition x41a_actx (RNG : footprint) (m0 : amem) (SPV DST dcap SRC n DT lo : Z) : Prop :=
  unpoisoned m0 SRC (SRC + n) /\ unpoisoned m0 DT (DT + 16388) /\ (0 < dcap -> unpoisoned m0 DST (DST + dcap)) /\
  rng RNG SRC n /\ rng RNG (shad SRC) (shspan SRC n) /\ rng RNG DT 16388 /\ rng RNG (shad DT) (shspan DT 16388) /\
  (0 < dcap -> rng RNG DST dcap) /\ (0 < dcap -> rng RNG (shad DST) (shspan DST dcap)) /\
  rng RNG lo (SPV - lo) /\ rng_aimg RNG /\ azstk RNG m0 lo SPV /\ aro_client RNG m0 /\ art m0.
Ltac x41a_actx_open ACTX :=
  destruct ACTX as (USRC & UDT & UDST & RSRC & RSRCS & RDT & RDTS & RDST & RDSTS & RSTK & RI & AZS & ARC & ART).

(* [comment removed for export] *)
Lemma land7 : forall x, 0 <= x -> Z.land x 7 = x - 8 * (x / 8).
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. pose proof (Z.div_mod x 8 ltac:(lia)). lia. Qed.
Ltac land7_lin :=
  repeat match goal with |- context [Z.land ?x 7] => rewrite (land7 x) by lia end;
  repeat match goal with H : context [Z.land ?x 7] |- _ => rewrite (land7 x) in H by lia end.

(* [comment removed for export] *)
Definition SINVA (off len bc : Z) : Prop := off = 0 \/ (1 <= off /\ off + 8 <= len /\ bc <= 64).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unp_carryW : forall (m mm : amem) W lo0 hi0,
  unpoisoned m lo0 hi0 -> munch W m mm -> aappW W -> 4096 <= lo0 -> lo0 < hi0 -> hi0 <= 2^47 -> unpoisoned mm lo0 hi0.
Proof.
  intros m mm W lo0 hi0 U MU HW L0 LT H0.
  eapply unpoisoned_munch; [exact U | exact MU |].
  apply aappW_shadow_disjoint; [exact HW | | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition aunp (mm : amem) (DST dcap SRC n DT : Z) : Prop :=
  (0 < n -> unpoisoned mm SRC (SRC + n)) /\ unpoisoned mm DT (DT + 16388) /\ (0 < dcap -> unpoisoned mm DST (DST + dcap)).

Lemma aunp_carry : forall (m mm : amem) W DST dcap SRC n DT,
  aunp m DST dcap SRC n DT -> munch W m mm -> aappW W ->
  4096 <= DST -> DST + dcap < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> 4096 <= DT -> DT + 16388 < 2^47 ->
  aunp mm DST dcap SRC n DT.
Proof.
  intros m mm W DST dcap SRC n DT (US & UD & UO) MU HW A1 A2 B1 B2 C1 C2. split; [| split].
  - intros Hn. eapply unp_carryW; [exact (US Hn) | exact MU | exact HW | lia | lia | lia].
  - eapply unp_carryW; [exact UD | exact MU | exact HW | lia | lia | lia].
  - intros Hd. eapply unp_carryW; [exact (UO Hd) | exact MU | exact HW | lia | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma aappW_D : forall DST dcap, (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)) -> 0 < dcap ->
  aappW [(DST, DST + dcap)].
Proof. intros DST dcap DA HD. constructor; [cbn [fst snd]; unfold KLOW, KHIGH; lia | constructor]. Qed.
Lemma aappW_cons_hi : forall A B W, 0x10007fff8000 <= A -> aappW W -> aappW ((A, B) :: W).
Proof. intros A B W HA HW. constructor; [cbn [fst snd]; unfold KHIGH; lia | exact HW]. Qed.
Lemma aappW_cons_D : forall DST dcap W, (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)) -> 0 < dcap ->
  aappW W -> aappW ((DST, DST + dcap) :: W).
Proof. intros DST dcap W DA HD HW. constructor; [cbn [fst snd]; unfold KLOW, KHIGH; lia | exact HW]. Qed.
Lemma aappW_nil : aappW [].
Proof. constructor. Qed.

(* [comment removed for export] *)
Lemma munch_drop_empty : forall (m mm : amem) A W, munch ((A, A) :: W) m mm -> munch W m mm.
Proof.
  intros m mm A W MU. eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside]. split; [lia | exact Hx].
Qed.

Lemma aunp_carryD : forall (m mm : amem) W DST dcap SRC n DT,
  aunp m DST dcap SRC n DT -> munch ((DST, DST + dcap) :: W) m mm -> aappW W ->
  (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)) -> 0 <= dcap ->
  4096 <= DST -> DST + dcap < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> 4096 <= DT -> DT + 16388 < 2^47 ->
  aunp mm DST dcap SRC n DT.
Proof.
  intros m mm W DST dcap SRC n DT AU MU HW DA D0 A1 A2 B1 B2 C1 C2.
  destruct (Z_lt_le_dec 0 dcap) as [HD|HD].
  - eapply aunp_carry; [exact AU | exact MU | apply aappW_cons_D; [exact DA | exact HD | exact HW] | lia..].
  - replace (DST + dcap) with DST in MU by lia.
    eapply aunp_carry; [exact AU | exact (munch_drop_empty _ _ _ _ MU) | exact HW | lia..].
Qed.

(* [comment removed for export] *)
Lemma rng_shspanZ_sub : forall RNG A n S len, rng RNG (shad A) (shspan A n) -> A <= S -> 0 <= len -> S + len <= A + n -> 0 <= A ->
  rng RNG (KXSHLO + S / 8) (shspanZ S len).
Proof.
  intros RNG A n S len H H1 H2 H3 H4. apply (shad_shspan_rng RNG S len (shad A) (shspan A n) H).
  - rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - unfold shspanZ, shspan. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - lia.
Qed.

(* [comment removed for export] *)
Section DX41A.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x41a_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x41a_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).

  (* [comment removed for export] *)
  Definition EINVA (mm : amem) : Prop :=
    stk bsegs mm DST (DST + dcap) /\
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk bsegs mm lo (SPV + -104) /\
    munch [(DST, DST + dcap); (SPV - 2720, SPV)] m0 mm /\ wmono bsegs m0 mm /\ mem_inv bsegs mm.

  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 :=
    (rw_cells bsegs mm (SPV + -480) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12]).
  (* [comment removed for export] *)
  Definition x41a_bd (mm : amem) (A : Z) (c b : word) (pad : list byte) (p st lm : word) : Prop :=
    rw_cells bsegs mm (SPV + A) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm].

  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\ (4096 <= SRC <= 140737488355328) /\
                 (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\ (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\
                 (0 <= rsv <= 255) /\ (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11).
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.

  (* [comment removed for export] *)
  Lemma x41_ret : forall mm r (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINVA mm -> (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evtF bsegs RNG POST (ST 0xa3c30 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                            x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mm r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI HR.
    destruct EI as (OUT & FR & STK & MU & WM & MI). facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RSTKf : rng RNG (SPV - 104) 104) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    kx_autoFLA FR [KAApp (SPV - 104) 104] [] 30%nat [KZRange SPV 17594333495296 140737488355328] [(SPV - 104, 104)] [(SPV - 104, 104)].
    all: aside.
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK SPV.
    all: apply evtF_done; unfold huf_dec_postA; repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
         (split; [exact OUT|]); (split; [|split; [|exact I]]).
    - destruct HR as [HR|[HR _]]; [left; exact HR | right; exact HR].
    - destruct HR as [->|[HR1 HR2]]; [clear - R1; lia|]. unfold zd_is_error, ZE_maxCode in HR1. apply Z.ltb_lt in HR1. clear - HR1 HR2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_end : forall mm (c1 b1 p1 st1 lm1 c2 b2 p2 st2 lm2 c3 b3 p3 st3 lm3 c4 b4 p4 st4 lm4 : word) pad1 pad2 pad3 pad4
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w10 w11 w12 : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINVA mm -> FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 (Z_to_bv 64 dcap) w10 w11 w12 ->
    x41a_bd mm (-376) c1 b1 pad1 p1 st1 lm1 -> x41a_bd mm (-144) c2 b2 pad2 p2 st2 lm2 ->
    x41a_bd mm (-184) c3 b3 pad3 p3 st3 lm3 -> x41a_bd mm (-224) c4 b4 pad4 p4 st4 lm4 ->
    evtF bsegs RNG POST (ST 0xa3b94 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                            x28 x29 x30 x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros until x31. intros EI FR B1 B2 B3 B4. unfold x41a_bd in B1, B2, B3, B4. facts R1 R2 R3 TL RSV LO SPB KLO.
    kx_autoFLA (FR, B1, B2, B3, B4) (@nil kza) [0xa3c30] 60%nat [KZRange SPV 17594333495296 140737488355328; KZRange dcap 0 4294967296]
      [(SPV - 480, 104); (SPV - 376, 40); (SPV - 144, 40); (SPV - 184, 40); (SPV - 224, 40)] [(SPV - 480, 480)].
    all: aside.
    all: try clear KXBR; try clear KXBR0; try clear KXBR1; try clear KXBR2; try clear KXBR3.
    all: try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv64_eqm_k; reflexivity)).
    all: first [ eapply x41_ret; [exact EI | left; reflexivity]
               | eapply x41_ret; [exact EI | right; split; [vm_compute; reflexivity | lia]] ].
  Qed.
End DX41A.
End CANSEC1.
