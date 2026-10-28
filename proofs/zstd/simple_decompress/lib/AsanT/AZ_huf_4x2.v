(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit42.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma aappW_frameN : forall SPV W, KHIGH <= SPV - W -> aappW [(SPV - W, SPV)].
Proof. intros SPV W H. constructor; [cbn [fst snd]; right; exact H | constructor]. Qed.

Lemma unpoisoned_frameN : forall m m' SPV W A B, unpoisoned m A B -> munch [(SPV - W, SPV)] m m' -> KHIGH <= SPV - W ->
  0 <= A -> B <= KEND -> unpoisoned m' A B.
Proof.
  intros m m' SPV W A B U MU K HA HB.
  eapply unpoisoned_munch; [exact U | exact MU |]. cbn [disjoint_from fst snd]. split; [|exact I].
  rewrite !shad_div. unfold ASHOFF, KHIGH, KEND in *. left. Z.div_mod_to_equations. lia.
Qed.

Lemma areg_frameN : forall RNG m m' SPV W A n, areg RNG m A n -> munch [(SPV - W, SPV)] m m' -> KHIGH <= SPV - W -> areg RNG m' A n.
Proof.
  intros RNG m m' SPV W A n H MU K Hn. destruct (H Hn) as (AB & U & R & RS).
  split; [exact AB | split; [| split; [exact R | exact RS]]].
  pose proof (ablk_lin _ _ AB) as (? & ? & ? & ?).
  eapply unpoisoned_frameN; [exact U | exact MU | exact K | lia | unfold KEND; lia].
Qed.

Lemma aro_frameN : forall RNG m m' SPV W A n, aro RNG m A n -> munch [(SPV - W, SPV)] m m' -> KHIGH <= SPV - W ->
  0 <= A -> A + n <= KEND -> aro RNG m' A n.
Proof.
  intros RNG m m' SPV W A n (U & R & RS) MU K HA HB. split; [| split; [exact R | exact RS]].
  eapply unpoisoned_frameN; eassumption.
Qed.

Lemma art_frameN : forall m m' SPV W, art m -> munch [(SPV - W, SPV)] m m' -> wmono bsegs m m' -> KHIGH <= SPV - W -> art m'.
Proof.
  intros m m' SPV W ART MU WM K. eapply art_transportW42; [exact ART | exact MU | exact WM |].
  constructor; [cbn [fst]; unfold KHIGH in K; lia | constructor].
Qed.

Ltac and_spine := lazymatch goal with |- _ /\ _ => split; [| and_spine] | _ => idtac end.

(* [comment removed for export] *)
Lemma huf_dec_preA_call : forall RNG m m' SPV W W' lo fr DST dcap SRC n src,
  huf_dec_preA RNG m SPV lo fr DST dcap SRC n src -> 0 < W <= fr -> W mod 16 = 0 -> W <= W' <= fr ->
  munch [(SPV - W', SPV)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
  stk bsegs m' lo (SPV + - W) ->
  huf_dec_preA RNG m' (SPV + - W) lo (fr - W) DST dcap SRC n src.
Proof.
  intros RNG m m' SPV W W' lo fr DST dcap SRC n src
    (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SRCL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & AD & AS & ART & ASTK & AZ & ARO & SPA)
    HW W16 HW' MU WM MI' STK'.
  pose proof ASTK as (KLO & RSTK & RI).
  assert (K : KHIGH <= SPV - W') by lia.
  unfold huf_dec_preA. and_spine.
  all: first [ eassumption
             | eapply stk_transport_disjoint; [exact OUT | exact MU | exact WM | cbn [disjoint_from fst snd]; lia]
             | eapply bytes_at_transport; [exact SRCB | exact MU | cbn [disjoint_from fst snd]; lia]
             | eapply areg_frameN; [eassumption | exact MU | exact K]
             | eapply art_frameN; [exact ART | exact MU | exact WM | exact K]
             | split; [exact KLO | split; [eapply rng_sub; [exact RSTK | lia | lia] | exact RI]]
             | eapply azstk_sub; [eapply azstk_transport; [exact AZ | exact MU | exact WM | apply aappW_frameN; exact K | lia] | apply Z.le_refl | lia | lia]
             | eapply aro_client_transport; [exact ARO | exact MU | exact WM | apply aappW_frameN; exact K]
             | Z.div_mod_to_equations; lia
             | lia ].
Qed.

Lemma huf_dt_preA_call : forall RNG m m' SPV W W' lo DST dcap DT dtb,
  huf_dt_preA RNG m SPV lo DST dcap DT dtb -> KHIGH <= lo -> lo <= SPV - W' -> 0 <= W <= W' ->
  munch [(SPV - W', SPV)] m m' -> huf_dt_preA RNG m' (SPV + - W) lo DST dcap DT dtb.
Proof.
  intros RNG m m' SPV W W' lo DST dcap DT dtb (DTB & DL & T0 & T1 & OS3 & DJ2 & ARO & DTA) K LO HW MU.
  unfold huf_dt_preA, HUF_DTABLE_BYTES in *. and_spine.
  all: first [ eassumption
             | eapply bytes_at_transport; [exact DTB | exact MU | cbn [disjoint_from fst snd]; lia]
             | eapply aro_frameN; [exact ARO | exact MU | lia | lia | unfold KEND; lia]
             | lia ].
Qed.

(* [comment removed for export] *)
Definition x42e_fast_stmt : Prop :=
  forall (RNG : footprint) (ra gp tp t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m1 : amem) (SPV DST dcap SRC n DT tl lo : Z) (src dtb junk : list byte),
  huf_dec_preA RNG m SPV lo 3136 DST dcap SRC n src ->
  huf_dt_preA RNG m SPV lo DST dcap DT dtb ->
  nth_error dtb 2 = Some (Z_to_bv 8 tl) -> 1 <= tl <= 12 -> huf_x2_ok dtb tl -> huf_nb_ok true dtb tl ->
  munch [(SPV - 576, SPV)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
  rw_cells bsegs m1 (SPV + -576) [CB 472 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk bsegs m1 lo (SPV + -576) ->
  evtF bsegs RNG (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m huf_noQ)
      (MS (mkR (Z_to_bv 64 n) (Z_to_bv 64 (SPV + -576)) gp tp (Z_to_bv 64 dcap) (Z_to_bv 64 DT) t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 0)
               (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 DST) s9 s10
               (Z_to_bv 64 0x7fff8000) t3 t4 t5 (Z_to_bv 64 SRC))
          F (Z_to_bv 64 0x9bb64) fc None m1 (seg_rom bsegs)).

Definition x42d_seg_stmt : Prop :=
  forall (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 : word)
         (m m1 : amem) (SPV DST dcap SRC n DT tl lo : Z) (src dtb junk : list byte),
  huf_dec_preA RNG m SPV lo 3136 DST dcap SRC n src ->
  huf_dt_preA RNG m SPV lo DST dcap DT dtb ->
  nth_error dtb 2 = Some (Z_to_bv 8 tl) -> 1 <= tl <= 12 -> huf_x2_ok dtb tl -> huf_nb_ok true dtb tl ->
  munch [(SPV - 624, SPV)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
  rw_cells bsegs m1 (SPV + -576) [CB 472 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk bsegs m1 lo (SPV + -576) ->
  evtF bsegs RNG (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m huf_noQ)
      (MS (mkR (Z_to_bv 64 n) (Z_to_bv 64 (SPV + -576)) gp tp (Z_to_bv 64 dcap) (Z_to_bv 64 DT) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 (Z_to_bv 64 DST) x25 x26 (Z_to_bv 64 0x7fff8000) x28 x29 x30 (Z_to_bv 64 SRC))
          F (Z_to_bv 64 0x9dc38) fc None m1 (seg_rom bsegs)).

Lemma x42a_epi : forall (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m mm : amem) (SPV DST dcap lo r : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk bsegs mm lo (SPV + -104) -> stk bsegs mm DST (DST + dcap) ->
  munch [(DST, DST + dcap); (SPV - 3136, SPV)] m mm -> wmono bsegs m mm -> mem_inv bsegs mm ->
  astk RNG lo SPV -> lo <= SPV - 3136 -> SPV < 2^47 ->
  (r = dcap \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
  evtF bsegs RNG (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m huf_noQ)
      (MS (mkR x1 (Z_to_bv 64 (SPV + -576)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9fd64) fc None mm (seg_rom bsegs)).
Proof.
  intros RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mm SPV DST dcap lo r
         x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         FR STK OUT MU WM MI ASTK LO SPB HR R0.
  pose proof ASTK as (KLO & RSTK & RI). unfold KHIGH in KLO.
  assert (RSTKf : rng RNG (SPV - 104) 104) by (eapply rng_sub; [exact RSTK | lia | lia]).
  kx_autoFLA FR [KAApp (SPV - 104) 104] (@nil Z) 30%nat [KZRange SPV (0x10007fff8000 + 3136) (2^47)] [(SPV - 104, 104)] [(SPV - 104, 104)].
  all: try kx_z.
  all: kx_mem.
  all: zstep.
  all: release_frame FR STK SPV.
  all: apply evtF_done; unfold huf_dec_postA; repeat (lazymatch goal with |- ex _ => eexists end).
  all: (split; [reflexivity|]); (split; [cbn [app]; exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
       (split; [exact OUT|]); (split; [exact HR|]); split; [exact R0|exact I].
Qed.

(* [comment removed for export] *)
Lemma x42e_body_call : x42d_seg_stmt ->
  forall (RNG : footprint) (ra gp tp t2 s0 s1 a1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m1 : amem) (SPV DST dcap SRC n DT tl lo : Z) (src dtb junk : list byte),
  huf_dec_preA RNG m SPV lo 3136 DST dcap SRC n src ->
  huf_dt_preA RNG m SPV lo DST dcap DT dtb ->
  nth_error dtb 2 = Some (Z_to_bv 8 tl) -> 1 <= tl <= 12 -> huf_x2_ok dtb tl -> huf_nb_ok true dtb tl ->
  munch [(SPV - 576, SPV)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
  rw_cells bsegs m1 (SPV + -576) [CB 472 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk bsegs m1 lo (SPV + -576) ->
  evtF bsegs RNG (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m huf_noQ)
      (MS (mkR (Z_to_bv 64 n) (Z_to_bv 64 (SPV + -576)) gp tp (Z_to_bv 64 dcap) (Z_to_bv 64 DT) t2 s0 s1 (Z_to_bv 64 DST) a1
               (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 DST) s9 s10
               (Z_to_bv 64 0x7fff8000) t3 t4 t5 (Z_to_bv 64 SRC))
          F (Z_to_bv 64 0x9dc38) fc None m1 (seg_rom bsegs)).
Proof.
  intros X42D RNG ra gp tp t2 s0 s1 a1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 F fc m m1 SPV DST dcap SRC n DT tl lo src dtb junk
         PRE DTP TLB TLR X2 NB MU0 WM0 MI1 FR STK2.
  (* [comment removed for export] *)
  assert (MU1 : munch [(SPV - 624, SPV)] m m1)
    by (eapply munch_weaken; [| exact MU0]; unfold sub_fp; cbn [outside fst snd app]; intros; lia).
  (* [comment removed for export] *)
  eapply X42D; eassumption.
Qed.

Theorem huf_4x2_proofA : x42d_seg_stmt -> x42e_fast_stmt -> huf_4x2_stmtA.
Proof.
  intros X42D XFAST. unfold huf_4x2_stmtA, huf_int_stmtA_at, APHUF_4X2.
  intros RNG ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DST dcap SRC n DT tl lo src dtb PRE DTP TLB TLR X2 NB.
  pose proof PRE as PRE'.
  destruct PRE' as (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & AD & AS & ART & ASTK & AZ & ARO & SP16).
  pose proof ASTK as (KLO & RSTK & RI). unfold KHIGH in KLO.
  pose proof ART as (GOT & RIC & SHB & INI & LAY & REAL).
  (* [comment removed for export] *)
  pose proof STK as STK2. carve_frame 576%nat STK2.
  assert (RSTKf : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | lia | lia]).
  assert (MU0 : munch [(SPV - 576, SPV)] m m) by apply munch_refl.
  assert (WM0 : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLA (GOT, SHB) (@nil kza) [0x9bb64; 0x9dc38] 40%nat
    [KZRange SPV (0x10007fff8000 + 3136) (2^47); KZAlign SPV 16; KZWr (SPV - 576) 576]
    (@nil (Z * Z)) [(SPV - 576, 576)].
  all: try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  all: kx_mem.
  - (* [comment removed for export] *)
    rewrite (Z.mod_small (bv_unsigned flags) (2^64)) by (pose proof (bv_unsigned_in_range 64 flags) as HB; unfold bv_modulus in HB; change (2 ^ Z.of_N 64) with (2^64) in HB; lia).
    rewrite KXBR.
    lazymatch goal with FR : rw_cells bsegs ?m1 (SPV + -576) _ |- _ =>
      eapply (XFAST RNG ra gp tp t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 F fc m m1) end.
    all: first [exact PRE | exact DTP | exact TLB | exact TLR | exact (X2 eq_refl) | exact NB | eassumption].
  - (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells bsegs ?m1 (SPV + -576) _ |- _ =>
      eapply (x42e_body_call X42D RNG ra gp tp t2 s0 s1 _ flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 F fc m m1) end.
    all: first [exact PRE | exact DTP | exact TLB | exact TLR | exact (X2 eq_refl) | exact NB | eassumption].
Qed.

End CANSEC1.
