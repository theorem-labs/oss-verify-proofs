(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_lm_defs Sj_num_lm_runs Sj_num_lm_runs2 Sj_num_lm_c1.
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
  Hypothesis FLO : (0x66b000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x66b000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.
  Hypothesis YR : (0 <= Y /\ Y + 40 <= 0x66b000 /\ Y mod 8 = 0)%Z.
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

  Notation c1_bot50 := (lm_bot50 sp gp tp F fc X lo d spq f Y ybs m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YR YL SHPY Q idx0 KHEAD KEXIT).
  Notation c1_bot4c := (lm_bot4c sp gp tp F fc X lo d spq f Y ybs m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YR YL SHPY Q idx0 KHEAD KEXIT).
  Notation c1_bot48 := (lm_bot48 sp gp tp F fc X lo d spq f Y ybs m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YR YL SHPY Q idx0 KHEAD KEXIT).
  Notation c1_f2 := (lm_f2 sp gp tp F fc X lo d spq f Y ybs m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YR YL SHPY Q KEXIT).

  Lemma lm_addl : forall (fuel : nat) (j k base xlen zlen : Z) xra xt0 xt1 xt2 xa2 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 ziw (mm : mem),
    LMINV ziw (repeat (Z_to_bv 8 0) 63) mm xlen zlen -> (0 <= j < k)%Z -> (0 <= base)%Z -> (base + k <= 62)%Z -> (k - j <= Z.of_nat fuel)%Z ->
    (forall xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa6' xa7' xt3' (mm' : mem), LMINV ziw (repeat (Z_to_bv 8 0) 63) mm' xlen zlen ->
       evt asegs Q (LMS 0xcc024 xra xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' (Z_to_bv 64 0) xa6' xa7' xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3' xt4 xt5 xt6 mm')) ->
    evt asegs Q (LMS 0xcbfb0 xra xt0 xt1 xt2 (Z_to_bv 64 (X + 8 * (base + j))) (Z_to_bv 64 (f + 608 + 8 * j)) xa2 (Z_to_bv 64 (X + 8 * (base + j)))
                     (Z_to_bv 64 (f + 608 + 8 * j)) (Z_to_bv 64 (k - j)) xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using LMH.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros INV Hj Hb Hbk Hf HK; [exfalso; lia|].
    lm_open INV. lm_env.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xcbfb0%Z => first [ eapply evt_eq; [| eapply (IH (j + 1)%Z k base xlen zlen); [lm_close | lia | lia | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0xcc024%Z => first [ eapply evt_eq; [| eapply HK; lm_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_car : forall (fuel : nat) (p idx xlen zlen : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 ziw (mm : mem),
    LMINV ziw (repeat (Z_to_bv 8 0) 63) mm xlen zlen -> (1 <= idx < 5 /\ idx0 <= idx + 1)%Z -> (0 <= p <= xlen)%Z -> (xlen - p <= Z.of_nat fuel)%Z ->
    evt asegs Q (LMS 0xcc054 (Z_to_bv 64 xlen) xt0 xt1 xt2 (Z_to_bv 64 (X + 8 * p)) (Z_to_bv 64 (xlen - p + 1)) (Z_to_bv 64 (X + 8 * p)) xa3 xa4 xa5 xa6 xa7 xs2
                     (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 Y) (Z_to_bv 64 (1 - idx))
                     (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) (Z_to_bv 64 5) (Z_to_bv 64 (-8)) xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 608)) mm).
  Proof using LMH KEXIT KHEAD.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros INV Hidx Hp Hf.
    all: lm_open INV; lm_env.
    all: astep.
    all: awalk ltac:(fun pc => lazymatch pc with
      | 0xcc054%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z idx xlen zlen); [lm_close | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xcbc1c%Z => first [ eapply evt_eq; [| eapply (c1_bot50 idx); [lm_close | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xcc348%Z => first [ eapply evt_eq; [| eapply c1_f2; lm_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_2c8 : forall (idx k xlen zlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 ziw (mm : mem),
    LMINV ziw (repeat (Z_to_bv 8 0) 63) mm xlen zlen -> (1 <= idx < 5 /\ idx0 <= idx + 1)%Z -> (0 <= k <= 62)%Z -> (idx + k <= xlen)%Z ->
    evt asegs Q (LMS 0xcbf94 (Z_to_bv 64 xlen) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 (Z.shiftl k 48)) (Z_to_bv 64 (1 - idx))
                     (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) (Z_to_bv 64 k) (Z_to_bv 64 (-8)) xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 608)) mm).
  Proof using LMH KEXIT KHEAD.
    intros until mm. intros INV Hidx Hk Hik. pose proof INV as INV0. lm_open INV. lm_env.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xcbc14%Z => first [ eapply evt_eq; [| eapply (c1_bot48 idx); [exact INV0 | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xcbfb0%Z => first [ shl48_facts; eapply evt_eq; [| eapply (lm_addl (Z.to_nat k) 0%Z k idx xlen zlen); [exact INV0 | lia | lia | lia | lia |]]; [num_st_eq|] | fail 100 "cut" pc ]
      end).
    clear INV0. lm_forget. intros xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa6' xa7' xt3' mm' INV. pose proof INV as INV0. lm_open INV.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xcbc18%Z => first [ eapply evt_eq; [| eapply (c1_bot4c idx); [exact INV0 | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xcc054%Z => first [ eapply evt_eq; [| eapply (lm_car (Z.to_nat (xlen - (idx + k))) (idx + k)%Z idx xlen zlen); [exact INV0 | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_2a4 : forall (idx k nl xlen zlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 ziw (mm : mem),
    LMINV ziw (repeat (Z_to_bv 8 0) 63) mm xlen zlen -> (1 <= idx < 5 /\ idx0 <= idx + 1)%Z -> (0 <= k <= 62)%Z -> (nl = idx + k)%Z -> (nl <= 62)%Z ->
    evt asegs Q (LMS 0xcbf70 (Z_to_bv 64 0xcbf70) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 nl) (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 (Z.shiftl k 48)) (Z_to_bv 64 (1 - idx))
                     (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) (Z_to_bv 64 k) (Z_to_bv 64 (-8)) xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT KHEAD.
    intros until mm. intros INV Hidx Hk Hnl Hn62. lm_open INV. lm_env.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xcbf94%Z => first [ eapply evt_eq; [| eapply (lm_2c8 idx k nl zlen); [lm_close | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End LMC.
