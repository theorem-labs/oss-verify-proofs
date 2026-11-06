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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit42.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m1 : amem) (SPV DST dcap SRC n DT tl lo : Z) (src dtb junk : list byte),
  huf_dec_preA RNG m SPV lo 3136 DST dcap SRC n src ->
  huf_dt_preA RNG m SPV lo DST dcap DT dtb ->
  nth_error dtb 2 = Some (Z_to_bv 8 tl) -> 1 <= tl <= 12 -> huf_x2_ok dtb tl -> huf_nb_ok true dtb tl ->
  munch [(SPV - 528, SPV)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
  rw_cells bsegs m1 (SPV + -528) [CB 424 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk bsegs m1 lo (SPV + -528) ->
  evtF bsegs RNG (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m huf_noQ)
      (MS (mkR ra (Z_to_bv 64 (SPV + -528)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 0) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9c664) fc None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma x42e_body_call : huf_int_stmtA_at 0xa5d3c 2608 true ->
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m1 : amem) (SPV DST dcap SRC n DT tl lo : Z) (src dtb junk : list byte),
  huf_dec_preA RNG m SPV lo 3136 DST dcap SRC n src ->
  huf_dt_preA RNG m SPV lo DST dcap DT dtb ->
  nth_error dtb 2 = Some (Z_to_bv 8 tl) -> 1 <= tl <= 12 -> huf_x2_ok dtb tl -> huf_nb_ok true dtb tl ->
  munch [(SPV - 576, SPV)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
  rw_cells bsegs m1 (SPV + -528) [CB 424 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk bsegs m1 lo (SPV + -528) ->
  evtF bsegs RNG (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m huf_noQ)
      (MS (mkR ra (Z_to_bv 64 (SPV + -528)) gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ed30) fc None m1 (seg_rom bsegs)).
Proof.
  intros X42B RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1 SPV DST dcap SRC n DT tl lo src dtb junk
         PRE DTP TLB TLR X2 NB MU0 WM0 MI1 FR STK2.
  pose proof PRE as PRE'.
  destruct PRE' as (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & AD & AS & ART & ASTK & AZ & ARO & SP16).
  pose proof ASTK as (KLO & RSTK & RI). unfold KHIGH in KLO.
  zstep. zstep. zstep.
  eapply evtF_cut;
  [ eapply (X42B RNG (Z_to_bv 64 0x9ed3c) gp tp);
    [ eapply (huf_dec_preA_call RNG m m1 SPV 528 576 lo 3136); [exact PRE | lia | reflexivity | lia | exact MU0 | exact WM0 | exact MI1 | exact STK2]
    | eapply (huf_dt_preA_call RNG m m1 SPV 528 576 lo); [exact DTP | unfold KHIGH; lia | lia | lia | exact MU0]
    | exact TLB | exact TLR | intros _; exact X2 | exact NB ]
  | ].
  cbv beta. intros ms' P. unfold huf_dec_postA in P.
  destruct P as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & r & -> & MU2 & WM2 & MI2 & STK3 & OUT2 & RR & RB & _).
  replace (ret_pc (Z_to_bv 64 0x9ed3c)) with (Z_to_bv 64 0x9ed3c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* [comment removed for export] *)
  pose proof (rw_cells_transport _ _ _ _ _ _ FR MU2 WM2) as FR2.
  cbn [disjoint_from fst snd app cells_size csize Nat.add length] in FR2. specialize (FR2 ltac:(clear - OS1 LO; lia)).
  (* [comment removed for export] *)
  kx_autoFLA FR2 [KAApp (SPV - 528) 528] (@nil Z) 30%nat [KZRange SPV 0x10007fff8000 (2^47)] [(SPV - 528, 528)] [(SPV - 528, 528)].
  all: try kx_z.
  all: kx_mem.
  all: zstep.
  release_frame FR2 STK3 SPV.
  apply evtF_done; unfold huf_dec_postA; repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|].
  split; [ eapply munch_trans; [ eapply munch_weaken; [| exact MU0]; unfold sub_fp; cbn [outside fst snd app]; intros; lia
                               | eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside fst snd app]; intros; lia ] |].
  split; [ eapply wmono_trans; [exact WM0 | exact WM2] |].
  split; [assumption|]. split; [assumption|]. split; [exact OUT2|]. split; [exact RR|]. split; [exact RB| exact I].
Qed.

Theorem huf_4x2_proofA : huf_int_stmtA_at 0xa5d3c 2608 true -> x42e_fast_stmt -> huf_4x2_stmtA.
Proof.
  intros X42B XFAST. unfold huf_4x2_stmtA, huf_int_stmtA_at, APHUF_4X2.
  intros RNG ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DST dcap SRC n DT tl lo src dtb PRE DTP TLB TLR X2 NB.
  pose proof PRE as PRE'.
  destruct PRE' as (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & AD & AS & ART & ASTK & AZ & ARO & SP16).
  pose proof ASTK as (KLO & RSTK & RI). unfold KHIGH in KLO.
  (* [comment removed for export] *)
  pose proof STK as STK2. carve_frame 528%nat STK2.
  assert (RSTKf : rng RNG (SPV - 528) 528) by (eapply rng_sub; [exact RSTK | lia | lia]).
  assert (MU0 : munch [(SPV - 528, SPV)] m m) by apply munch_refl.
  assert (WM0 : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLA tt (@nil kza) [0x9c664; 0x9ed30] 40%nat
    [KZRange SPV (0x10007fff8000 + 3136) (2^47); KZAlign SPV 16; KZWr (SPV - 528) 528]
    (@nil (Z * Z)) [(SPV - 528, 528)].
  all: try kx_z.
  all: kx_mem.
  - (* [comment removed for export] *)
    rewrite (Z.mod_small (bv_unsigned flags) (2^64)) by (pose proof (bv_unsigned_in_range 64 flags) as HB; unfold bv_modulus in HB; change (2 ^ Z.of_N 64) with (2^64) in HB; lia).
    rewrite KXBR.
    lazymatch goal with FR : rw_cells bsegs ?m1 (SPV + -528) _ |- _ =>
      eapply (XFAST RNG ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1) end.
    all: first [exact PRE | exact DTP | exact TLB | exact TLR | exact (X2 eq_refl) | exact NB | eassumption].
  - (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells bsegs ?m1 (SPV + -528) _, MU1 : munch _ m ?m1 |- _ =>
      assert (MU1' : munch [(SPV - 576, SPV)] m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside fst snd app]; intros; lia);
      eapply (x42e_body_call X42B RNG ra gp tp _ _ _ s0 s1 _ _ flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m m1) end.
    all: first [exact PRE | exact DTP | exact TLB | exact TLR | exact (X2 eq_refl) | exact NB | eassumption].
Qed.

End CANSEC1.
