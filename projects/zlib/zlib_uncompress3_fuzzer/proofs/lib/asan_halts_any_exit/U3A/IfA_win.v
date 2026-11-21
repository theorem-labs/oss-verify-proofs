(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj IfA_base IfAKit IfA_lit IfA_lenb IfA_distb.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_f8 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation GST := (gms SP Zs S D n OB osz lb la da gp tp FR fc).
  Notation DST := (dst FR fc gp tp SP Zs S D n OB osz lb la da bo).
  Notation DINV m v0 fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880))
                              (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) sd id ni ai no ao msg mode hw bw fo).

  Definition wst (x1 x6 x10 x11 x15 x16 x21 : word) (len dist op ci co hold bits pc : Z) (m : amem) : machine_state :=
    GST x1 x6 (Z_to_bv 64 (Zs + 8)) (Z_to_bv 64 len) x10 x11 (Z_to_bv 64 op) x15 x16 (Z_to_bv 64 dist) x21
        (Z_to_bv 64 (Zs + 32)) (Z_to_bv 64 (Zs + 24)) (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880)) ci co hold bits pc m.

  Definition wentry_post (m : amem) (len dist ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (x1 x6 x10 x11 x15 x16 x21 : word) (op : Z),
      op = dist - (co - bo) /\
      ((ms' = wst x1 x6 x10 x11 x15 x16 x21 len dist op ci co hold bits 0x97980 m /\ whave < op)
       \/ (ms' = wst x1 x6 x10 (Z_to_bv 64 wnext) x15 x16 x21 len dist op ci co hold bits 0x97380 m /\ op <= whave /\ wnext = 0)
       \/ (ms' = wst (Z_to_bv 64 (Zs + 8)) x6 x10 (Z_to_bv 64 wnext) x15 x16 x21 len dist op ci co hold bits 0x97420 m /\ op <= whave /\ op <= wnext)
       \/ (ms' = wst (Z_to_bv 64 (Zs + 8)) x6 x10 (Z_to_bv 64 wnext) x15 x16 x21 len dist op ci co hold bits 0x97130 m /\ op <= whave /\ 0 < wnext < op)).

  Lemma if_wentry : forall (m : amem) (v0 : word) (fo : Z -> Z) (x1 x6 x10 x13 x16 x21 : word) (len dist ci co hold bits : Z),
    DINV m v0 fo ->
    3 <= len <= 258 -> 1 <= dist <= 32768 -> co - bo < dist -> bo <= co -> co + 258 <= osz ->
    evtF asegs RNG (wentry_post m len dist ci co hold bits) (DST x1 x6 (Z_to_bv 64 (co - bo)) x13 x16 x21 len dist ci co hold bits 0x970f4 m).
  Proof using All.
    intros until bits. intros INV0 LEN DIST DCO BCO CO258.
    pose proof CX as CX0. open_fctx CX. open_finv INV0. unfold dst, gms, wentry_post.
    clear ZOD TOKL TOKD FWR DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD WIN
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ RZ RSZ SHO DJO ROB RSOB.
    assert (SANEC : rw_cells asegs m (S + 7160) [C4 (Z_to_bv 64 1)]).
    { eapply rw_cells_transport; [exact SANE| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; try exact I; lia. }
    assert (WB : whave <= 32768 /\ wnext <= 32768) by lia.
    clear ZSD SOD WSZ WNX.
    zs. zs.
    setreg 13 (Z_to_bv 64 (dist - (co - bo))) ltac:(replace (dist - (OB + co - (OB + bo))) with (dist - (co - bo)) by lia; rewrite swrap32_small by lia; reflexivity).
    remember (dist - (co - bo)) as op eqn:EOP.
    zs. zs. zbr0 K.
    -
      zs. zs. zbr0 K1.
      +
        apply evtF_done. do 3 eexists. exists (Z_to_bv 64 0). do 3 eexists. exists op. split; [reflexivity|]. right. left.
        split; [unfold wst, gms; reflexivity| lia].
      + zs. zs. zbr0 K2.
        *
          apply evtF_done. exists (Z_to_bv 64 0). do 2 eexists. exists (Z_to_bv 64 0). do 3 eexists. exists op. split; [reflexivity|]. right. right. left.
          split; [unfold wst, gms; reflexivity| lia].
        *
          apply evtF_done. exists (Z_to_bv 64 0). do 2 eexists. exists (Z_to_bv 64 0). do 3 eexists. exists op. split; [reflexivity|]. right. right. right.
          split; [unfold wst, gms; reflexivity| lia].
    -
      zrunb [0x97980].
      apply evtF_done. do 7 eexists. exists op. split; [reflexivity|]. left.
      split; [unfold wst, gms; reflexivity| lia].
  Qed.
End P.
End CANSEC1.
