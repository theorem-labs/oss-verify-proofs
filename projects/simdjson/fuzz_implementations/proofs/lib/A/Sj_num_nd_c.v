(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_nd_defs Sj_num_nd_runs Sj_num_nd_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section NDB.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 160 - d)%Z.
  Hypothesis ROOM : (lo + NDCA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6d2000 <= f /\ f + 1016 <= lo)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6d2000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 1024 <= X) /\ (X + 504 <= S \/ S + 128 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 1024 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 128 <= X / 8 + 2147450880))%Z.
  Variable Q : machine_state -> Prop.
  Collection NDH := SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP.
  Notation NDINV := (nd_inv X spq f m0).

  Notation NDS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac nd_env :=
    destruct SPQ as [Hd Hspq]; unfold NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    let F8 := fresh "F8" in pose proof (f64_8 f F64) as F8;
    let F32 := fresh "F32" in assert (F32 : ((f + 32) / 8 = f / 8 + 4)%Z) by (replace (f + 32)%Z with (f + 8 * 4)%Z by lia; apply f64_div; exact F64).

  Notation b_314 := (nd_314 sp gp tp F fc X lo d spq f m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP Q).

  Definition nd_p5_k (e : Z) : Prop :=
    forall (xlen : Z) xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs9 xt3 xt4 xt5 xt6 c16 (mm : mem),
      NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen 1 ->
      evt asegs Q (NDS 0xee2a0 (Z_to_bv 64 0xedd28) xt0 xt1 xt2 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 e) xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 X) xs6 (Z_to_bv 64 (f + 32)) xs8 xs9 xt3 xt4 xt5 xt6 mm).

  Definition nd_mvt_k : Prop :=
    forall (k n xlen : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 c16 (mm : mem),
      NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen n -> (0 <= k)%Z -> (1 <= n)%Z -> (k + n <= 62)%Z ->
      evt asegs Q (NDS 0x84c48 (Z_to_bv 64 0xede04) xt0 xt1 xt2 (Z_to_bv 64 (f + 32 + 8 * k)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (8 * n)) xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 X) (Z_to_bv 64 (8 * k))
                       (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).

  Definition nd_mst_k : Prop :=
    forall (k n xlen : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xt3 xt4 xt5 xt6 c16 (mm : mem),
      NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen n -> (0 <= k)%Z -> (1 <= n)%Z -> (k + n <= 62)%Z ->
      evt asegs Q (NDS 0x84a08 (Z_to_bv 64 0xede18) xt0 xt1 xt2 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 0) (Z_to_bv 64 (8 * k)) xa3 xa4 xa5 xa6 xa7 xs3 xs5 (Z_to_bv 64 X)
                       (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).

  Definition nd_mvx_k : Prop :=
    forall (k n tlen : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 (mm : mem),
      NDINV (repeat (Z_to_bv 8 0) 63) (Z_to_bv 64 (8 * k)) mm n tlen -> (0 <= k)%Z -> (1 <= n)%Z -> (k + n <= 62)%Z ->
      evt asegs Q (NDS 0x84c48 (Z_to_bv 64 0xedf28) xt0 xt1 xt2 (Z_to_bv 64 (X + 8 * k)) (Z_to_bv 64 X) (Z_to_bv 64 (8 * n)) xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 X)
                       (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).

  Definition nd_msx_k : Prop :=
    forall (k n tlen : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 (mm : mem),
      NDINV (repeat (Z_to_bv 8 0) 63) (Z_to_bv 64 (8 * k)) mm n tlen -> (0 <= k)%Z -> (1 <= n)%Z -> (k + n <= 62)%Z ->
      evt asegs Q (NDS 0x84a08 (Z_to_bv 64 0xedf38) xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 0) (Z_to_bv 64 (8 * k)) xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 X)
                       (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Hypothesis K564 : nd_564_k sp gp tp F fc X spq f m0 Q.
  Hypothesis KMVT : nd_mvt_k.
  Hypothesis KMVX : nd_mvx_k.

  Lemma nd_shlt : forall (fuel : nat) (i n xlen : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa7 xs3 xs5 xs6 xs8 xs9 xt3 xt4 xt5 xt6 c16 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen n -> (0 <= i < n)%Z -> (n - i <= Z.of_nat fuel)%Z ->
    (forall yt0 yt1 ya0 ya4 ya5 ya7 (mm' : mem), NDINV (repeat (Z_to_bv 8 0) 63) c16 mm' xlen n ->
       evt asegs Q (NDS 0xedd98 xra yt0 yt1 xt2 ya0 xa1 xa2 xa3 ya4 ya5 (Z_to_bv 64 0) ya7 xs3 xs5 xs6 (Z_to_bv 64 (f + 32)) xs8 xs9 xt3 xt4 xt5 xt6 mm')) ->
    evt asegs Q (NDS 0xedd64 xra xt0 xt1 xt2 (Z_to_bv 64 (f + 32 + 8 * i)) xa1 xa2 xa3 (Z_to_bv 64 (2147450880 + (f + 32) / 8 + i)) (Z_to_bv 64 (f + 32 + 8 * i)) (Z_to_bv 64 (n - i)) xa7
                     xs3 xs5 xs6 (Z_to_bv 64 (f + 32)) xs8 xs9 xt3 xt4 xt5 xt6 mm).
  Proof using NDH.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros INV Hi Hf HK; [exfalso; lia|].
    nd_open INV. nd_env.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xedd64%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z n xlen); [nd_close | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0xedd98%Z => first [ eapply evt_eq; [| eapply HK; nd_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_shlx : forall (fuel : nat) (i n tlen : Z) xra xt1 xt2 xa1 xa2 xa3 xa4 xa5 xs3 xs5 xs9 xt3 xt4 xt5 xt6 c16 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) c16 mm n tlen -> (0 <= i < n)%Z -> (n - i <= Z.of_nat fuel)%Z ->
    (forall yt1 yt2 ya0 ya6 ya7 yt3 (mm' : mem), NDINV (repeat (Z_to_bv 8 0) 63) c16 mm' n tlen ->
       evt asegs Q (NDS 0xedea4 xra (Z_to_bv 64 0) yt1 yt2 ya0 xa1 xa2 xa3 xa4 xa5 ya6 ya7 xs3 xs5 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) xs9 yt3 xt4 xt5 xt6 mm')) ->
    evt asegs Q (NDS 0xede70 xra (Z_to_bv 64 (n - i)) xt1 xt2 (Z_to_bv 64 (X + 8 * i)) xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (2147450880 + X / 8 + i)) (Z_to_bv 64 (X + 8 * i))
                     xs3 xs5 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) xs9 xt3 xt4 xt5 xt6 mm).
  Proof using NDH.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros INV Hi Hf HK; [exfalso; lia|].
    nd_open INV. nd_env.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xede70%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z n tlen); [nd_close | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0xedea4%Z => first [ eapply evt_eq; [| eapply HK; nd_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac nd_cut_314 := first [ eapply evt_eq; [| eapply (b_314 K564); nd_close]; num_st_eq ].

  Lemma nd_1f8 : forall (xlen tlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs9 xt3 xt4 xt5 xt6 c16 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen tlen ->
    evt asegs Q (NDS 0xede30 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) xs9 xt3 xt4 xt5 xt6 mm).
  Proof using NDH K564 KMVX.
    intros until mm. intros INV. pose proof INV as INV0. nd_open INV0. nd_env.
    assert (DM3 : IsData xs3) by exact I.
    pose proof (shr6_range (bv_unsigned xa1) ltac:(pose proof (bv_unsigned_in_range 64 xa1) as R; unfold bv_modulus in R; cbn in R; lia)) as HK6.
    assert (K2A8 : forall xlen' yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 ys5 yt3 yt4 yt5 yt6 (mm' : mem), NDINV (repeat (Z_to_bv 8 0) 63) c16 mm' xlen' tlen ->
              evt asegs Q (NDS 0xedee0 yra yt0 yt1 yt2 ya0 xa1 ya2 ya3 ya4 ya5 ya6 ya7 xs3 ys5 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) xs9 yt3 yt4 yt5 yt6 mm')).
    { clear INV. nd_forget. intros until mm'. intros INV. nd_open INV.
      awalk ltac:(fun pc => lazymatch pc with
        | 0xedf4c%Z => first [ nd_cut_314 | fail 100 "cut" pc ]
        | 0x84c48%Z => first [ unfold nd_mvx_k in KMVX; eapply evt_eq; [| eapply (KMVX (Z.shiftr (bv_unsigned xa1) 6) xlen' tlen); [nd_close | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
        end). }
    awalk ltac:(fun pc => lazymatch pc with
      | 0xede70%Z => first [ eapply evt_eq; [| eapply (nd_shlx (Z.to_nat xlen) 0%Z xlen tlen); [exact INV | lia | lia |]]; [num_st_eq|] | fail 100 "cut" pc ]
      | 0xedee0%Z => first [ eapply evt_eq; [| eapply (K2A8 xlen); exact INV]; num_st_eq | fail 100 "cut" pc ]
      | 0xedf4c%Z => first [ nd_cut_314 | fail 100 "cut" pc ]
      end).
    clear INV. nd_forget. intros yt1 yt2 ya0 ya6 ya7 yt3 mm' INV. pose proof INV as INV0. nd_open INV0.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xedee0%Z => first [ eapply evt_eq; [| eapply K2A8; nd_close]; num_st_eq | fail 100 "cut" pc ]
      | 0xedf4c%Z => first [ nd_cut_314 | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_0f0 : forall (xlen tlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs9 xt3 xt4 xt5 xt6 c16 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen tlen ->
    evt asegs Q (NDS 0xedd28 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 X) xs6 (Z_to_bv 64 (f + 32)) xs8 xs9 xt3 xt4 xt5 xt6 mm).
  Proof using NDH K564 KMVX KMVT.
    intros until mm. intros INV. pose proof INV as INV0. nd_open INV0. nd_env.
    assert (DM3 : IsData xs3) by exact I.
    pose proof (shr6_range (bv_unsigned xs9) ltac:(pose proof (bv_unsigned_in_range 64 xs9) as R; unfold bv_modulus in R; cbn in R; lia)) as HK6.
    assert (K194 : forall tlen' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 (mm' : mem), NDINV (repeat (Z_to_bv 8 0) 63) c16 mm' xlen tlen' ->
              evt asegs Q (NDS 0xeddcc yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs3 (Z_to_bv 64 X) (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) xs9 yt3 yt4 yt5 yt6 mm')).
    { clear INV. nd_forget. intros until mm'. intros INV. nd_open INV.
      awalk ltac:(fun pc => lazymatch pc with
        | 0xedf4c%Z => first [ nd_cut_314 | fail 100 "cut" pc ]
        | 0x84c48%Z => first [ unfold nd_mvt_k in KMVT; eapply evt_eq; [| eapply (KMVT (Z.shiftr (bv_unsigned xs9) 6) tlen' xlen); [nd_close | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
        end). }
    awalk ltac:(fun pc => lazymatch pc with
      | 0xedd64%Z => first [ eapply evt_eq; [| eapply (nd_shlt (Z.to_nat tlen) 0%Z tlen xlen); [exact INV | lia | lia |]]; [num_st_eq|] | fail 100 "cut" pc ]
      | 0xeddcc%Z => first [ eapply evt_eq; [| eapply (K194 tlen); exact INV]; num_st_eq | fail 100 "cut" pc ]
      | 0xede30%Z => first [ eapply evt_eq; [| eapply (nd_1f8 xlen tlen); exact INV]; num_st_eq | fail 100 "cut" pc ]
      | 0xedf4c%Z => first [ nd_cut_314 | fail 100 "cut" pc ]
      end).
    clear INV. nd_forget. intros yt0 yt1 ya0 ya4 ya5 ya7 mm' INV. pose proof INV as INV0. nd_open INV0.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xeddcc%Z => first [ eapply evt_eq; [| eapply K194; nd_close]; num_st_eq | fail 100 "cut" pc ]
      | 0xedf4c%Z => first [ nd_cut_314 | fail 100 "cut" pc ]
      end).
  Qed.

End NDB.
