(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs Lept_iface Lept_env LeptC_kit LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_statics Fh_selkit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition hm_sels_upto (i : nat) (sels : list (Z * selv * list byte)) : Prop :=
  length sels = i
  /\ forall j, (j < i)%nat ->
       let e := nth j sels (0, mkSelv 0 0 0 0 0 0 [], []) in let d := nth j HM_DIMS (0, 0, 0, 0) in
       s_sy (snd (fst e)) = fst (fst (fst d)) /\ s_sx (snd (fst e)) = snd (fst (fst d)) /\ snd e = hm_name j.

(* [comment removed for export] *)
Definition HM_CHUNKS : list Z := [6; 5; 5; 6; 6; 16; 7; 7; 7; 7].
Definition hm_count (i : nat) : Z := 2 + fold_right Z.add 0 (firstn i HM_CHUNKS).

Lemma hm_sels_upto_10 : forall sels, hm_sels_upto 10 sels -> hm_sels_ok sels.
Proof. intros sels H. exact H. Qed.

Lemma hm_sels_upto_snoc : forall i sels sel v nm (sy sx : Z),
  hm_sels_upto i sels -> s_sy v = sy -> s_sx v = sx -> nm = hm_name i ->
  fst (fst (nth i HM_DIMS (0, 0, 0, 0))) = (sy, sx) ->
  hm_sels_upto (S i) (sels ++ [(sel, v, nm)]).
Proof.
  intros i sels sel v nm sy sx (HL & HJ) ESY ESX ENM ED. split; [rewrite length_app; cbn [length]; lia|].
  intros j Hj. destruct (Nat.eq_dec j i) as [->|NE].
  - rewrite app_nth2 by lia. rewrite HL, Nat.sub_diag. cbn [nth fst snd]. cbv zeta.
    destruct (nth i HM_DIMS (0, 0, 0, 0)) as [[[d1 d2] d3] d4]. cbn [fst snd] in *. injection ED as -> ->. repeat split; assumption.
  - rewrite app_nth1 by lia. apply HJ. lia.
Qed.

Section HmDefs.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition hm_inv (Σ : rts RT) (m : mem) (usp lo : Z) (fj : list byte) (es1 es0 era : word) (sela arr : Z)
    (i : nat) (Σk : rts RT) (mc : mem) (sels : list (Z * selv * list byte)) : Prop :=
  ART RT Σk mc /\ mem_inv asegs mc /\ stk asegs mc lo (usp + -32) /\ LIBH mc /\ io_ssp mc
  /\ agree_on (aclient (rt_live RT Σ) (rt_frames RT Σ) usp) m mc /\ wmono asegs m mc
  /\ rw_cells asegs mc (usp + -32) [CB 8 fj; C8 es1; C8 es0; C8 era]
  /\ sela_obj (rt_live RT Σk) mc sela arr sels /\ hm_sels_upto i sels
  /\ rt_live RT Σk = sela_live sela arr sels ++ rt_live RT Σ
  /\ Z.of_nat (length (rt_live RT Σk)) = Z.of_nat (length (rt_live RT Σ)) + hm_count i
  /\ (forall p n, In (p, n) (rt_live RT Σk) -> 0 < n)
  /\ rt_frames RT Σk = rt_frames RT Σ /\ rt_sp0 RT Σk = rt_sp0 RT Σ /\ rt_credit RT Σk = rt_credit RT Σ.

(* [comment removed for export] *)
Definition hm_state (pc : Z) (usp sela : Z) (gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (mc : mem) : machine_state :=
  MS (mkR ra' (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 sela) s1' a0' a1' a2' a3' a4' a5' a6' a7'
          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 pc) fc' None mc (seg_rom asegs).

(* [comment removed for export] *)
Definition hm_cont (PMc : Model -> Prop) (Q : config -> Prop) (Σ : rts RT) (m : mem) (usp lo : Z) (fj : list byte) (es1 es0 era : word) (sela arr : Z)
    (gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (pc : Z) (i : nat) : Prop :=
  forall (Σk : rts RT) (mc : mem) (sels : list (Z * selv * list byte))
         (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
    hm_inv Σ m usp lo fj es1 es0 era sela arr i Σk mc sels ->
    cps asegs (ASTA RT Σk PMc (eq (hm_state pc usp sela gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                     ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' mc))) Q.

(* [comment removed for export] *)
Definition hm_ctx (Σ : rts RT) (m : mem) (sp : word) (lo : Z) (sela arr : Z) : Prop :=
  lenv RT Σ m sp lo (LSTK 4) /\ lres RT Σ 0 74 0
  /\ (forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a -> (a < sela \/ sela + 16 <= a) /\ (a < arr \/ arr + 400 <= a)).

End HmDefs.
