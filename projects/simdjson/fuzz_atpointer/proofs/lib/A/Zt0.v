(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks D_defs D_kit D_clx Zpm Zpl Zq2 Sj_rtf
  Zqc Zqd Zsl Zqa Zq7 Zt5 Zt3 Ztb Ztc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section LMC.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f Y : Z) (ybs : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 256 - d)%Z.
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x669000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x669000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.
  Hypothesis YR : (0 <= Y /\ Y + 40 <= 0x669000 /\ Y mod 8 = 0)%Z.
  Hypothesis YL : length ybs = 40%nat.
  Hypothesis SHPY : forall m', munch (lm_WL X spq f) m0 m' -> wmono asegs m0 m' -> shz m' Y 40.
  Variable Q : machine_state -> Prop.
  Notation LMINV := (lm_inv X spq f Y ybs m0).

  Variable idx0 : Z.
  Hypothesis KHEAD : lm_head_k sp gp tp F fc X spq f Y ybs m0 Q idx0.
  Hypothesis KEXIT : lm_exit_k sp gp tp F fc X spq f m0 Q.
  Hypothesis KCPY2 : lm_cpy2_k sp gp tp F fc X spq f Y ybs m0 Q idx0.
  Hypothesis KMSET : lm_mset_k sp gp tp F fc X spq f Y ybs m0 Q idx0.
  Collection LMH := SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YR YL SHPY.

  Notation LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 S) xs4 xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac lm_env :=
    destruct SPQ as [Hd Hspq]; unfold LMA_STACK, RT_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    let F8 := fresh "F8" in pose proof (f64_8 f F64) as F8.

  Ltac shl48_facts :=
    repeat match goal with
    | H : context [Z.shiftl ?e 48] |- _ =>
        lazymatch goal with
        | _ : (Z.shiftl e 48 mod 18446744073709551616 = 0 <-> e = 0)%Z |- _ => fail
        | _ => pose proof (shl48_zero e ltac:(lia))
        end
    end.
  Ltac lm_exit_cut := first [ unfold lm_exit_k in KEXIT; eapply KEXIT; lm_xclose ].

  Lemma lm_norml : forall (fuel : nat) (k zlen : Z) xra xt0 xt1 xt2 xa0 xa2 xa3 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt5 xt6 ziw zsh (mm : mem),
    LMINV ziw zsh mm k zlen -> (1 <= k)%Z -> (k <= Z.of_nat fuel)%Z ->
    evt asegs Q (LMS 0xc9ca8 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 k) xa2 xa3 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa6 xa7
                     xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 (Z_to_bv 64 X) xt5 xt6 mm).
  Proof using LMH KEXIT.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros INV Hk Hf; [exfalso; lia|].
    lm_open INV. lm_env.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc9ca8%Z => first [ shl48_facts; eapply evt_eq; [| eapply (IH (k - 1)%Z zlen); [lm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xca5bc%Z => first [ lm_exit_cut | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_norm : forall (xlen zlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt5 xt6 ziw zsh (mm : mem),
    LMINV ziw zsh mm xlen zlen ->
    evt asegs Q (LMS 0xc9c84 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 (Z_to_bv 64 X) xt5 xt6 mm).
  Proof using LMH KEXIT.
    intros until mm. intros INV. pose proof INV as INV0. lm_open INV. lm_env.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc9ca8%Z => first [ eapply evt_eq; [| eapply (lm_norml (Z.to_nat xlen) xlen zlen); [exact INV0 | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xca5bc%Z => first [ lm_exit_cut | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_f2 : forall (xlen zlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 ziw zsh (mm : mem),
    LMINV ziw zsh mm xlen zlen ->
    evt asegs Q (LMS 0xca4b8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT.
    intros until mm. intros INV. lm_open INV. lm_env.
    astep. astep.
    num_cur_mem ltac:(fun m1 => eapply (lm_run4 f m1 ltac:(lia) Q); [exact ZSH | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI ZSH; intros j' mm' ZSH MI MU' WM'; transport_after_call asegs m1 mm' MU' WM'; clear MU' WM').
    lm_exit_cut.
  Qed.

  Lemma lm_bot50 : forall (idx xlen zlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 ziw zsh (mm : mem),
    LMINV ziw zsh mm xlen zlen -> (1 <= idx < 5 /\ idx0 <= idx + 1)%Z ->
    evt asegs Q (LMS 0xc9d8c (Z_to_bv 64 xlen) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 Y) (Z_to_bv 64 (1 - idx))
                     (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) (Z_to_bv 64 5) (Z_to_bv 64 (-8)) xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 608)) mm).
  Proof using LMH KEXIT KHEAD.
    intros until mm. intros INV Hidx. lm_open INV. lm_env.
    num_cur_mem ltac:(fun m1 => eapply (lm_run3 f m1 ltac:(lia) Q); [exact ZSH | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI ZSH; intros j' mm' ZSH MI MU' WM'; transport_after_call asegs m1 mm' MU' WM'; clear MU' WM').
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc9c84%Z => first [ eapply evt_eq; [| eapply (lm_norm xlen zlen); lm_close]; num_st_eq | fail 100 "cut" pc ]
      | 0xc9e9c%Z => first [ unfold lm_head_k in KHEAD; eapply evt_eq; [| eapply (KHEAD (idx + 1)%Z xlen zlen); [lm_close | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_bot4c : forall (idx xlen zlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xt3 ziw zsh (mm : mem),
    LMINV ziw zsh mm xlen zlen -> (1 <= idx < 5 /\ idx0 <= idx + 1)%Z ->
    evt asegs Q (LMS 0xc9d88 (Z_to_bv 64 xlen) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 Y) (Z_to_bv 64 (1 - idx))
                     (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) xs9 (Z_to_bv 64 (-8)) xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 608)) mm).
  Proof using LMH KEXIT KHEAD.
    intros until mm. intros INV Hidx. pose proof INV as INV0. lm_open INV. lm_env.
    astep.
    eapply evt_eq; [| eapply (lm_bot50 idx xlen zlen); [exact INV0 | exact Hidx]]. num_st_eq.
  Qed.

  Lemma lm_bot48 : forall (idx xlen zlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs9 xt3 ziw zsh (mm : mem),
    LMINV ziw zsh mm xlen zlen -> (1 <= idx < 5 /\ idx0 <= idx + 1)%Z ->
    evt asegs Q (LMS 0xc9d84 (Z_to_bv 64 xlen) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (X + 8 * idx)) xs5 (Z_to_bv 64 (1 - idx))
                     (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) xs9 (Z_to_bv 64 (-8)) xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 608)) mm).
  Proof using LMH KEXIT KHEAD.
    intros until mm. intros INV Hidx. pose proof INV as INV0. lm_open INV. lm_env.
    astep.
    eapply evt_eq; [| eapply (lm_bot4c idx xlen zlen); [exact INV0 | exact Hidx]]. num_st_eq.
  Qed.
End LMC.
