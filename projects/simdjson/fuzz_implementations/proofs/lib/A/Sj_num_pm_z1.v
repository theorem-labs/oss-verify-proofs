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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_pm_kit Sj_num_pm_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PMA.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X N DG A IP IL FPT FL lo : Z) (txt : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation TL := (Z.of_nat (length txt)).
  Hypothesis ROOM : (lo + PMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6d2000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis NR : (N mod 8 = 0 /\ 0x6d2000 <= N /\ N + 64 <= lo)%Z.
  Hypothesis DGR : (DG mod 8 = 0 /\ SP <= DG /\ DG + 8 <= USTACK_TOP)%Z.
  Hypothesis TXR : (0 < A /\ A + TL <= lo /\ TL < 2147483648)%Z.
  Hypothesis SPANS : pm_spans_ok A txt IP IL FPT FL.

  Hypothesis XSEP : ((X + 504 <= N \/ N + 64 <= X) /\ (X + 504 <= A \/ A + TL <= X)
                     /\ (X / 8 + 2147450880 + 63 <= N \/ N + 64 <= X / 8 + 2147450880) /\ (X / 8 + 2147450880 + 63 <= A \/ A + TL <= X / 8 + 2147450880))%Z.
  Notation W := [(SP - 160, SP); (X, X + 504); (DG, DG + 8)]%Z.

  Hypothesis SHPT : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' (8 * (A / 8)) (A + TL - 8 * (A / 8)).
  Hypothesis SHPN : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' N 64.
  Hypothesis SHPD : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' DG 8.
  Hypothesis SHPL : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2fb60 160.
  Variable Q : machine_state -> Prop.
  Collection PMH := ROOM TOP X8 XR XSH XS0 NR DGR TXR SPANS XSEP SHPT SHPN SHPD SHPL.
  Notation PMINV := (pm_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X N DG A IP IL FPT FL txt lo m0).

  Notation PMS pc xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -160)) gp tp (Z_to_bv 64 (DG / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 DG) xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Hypothesis KEXIT : forall xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 w8 w16 w24 w32 w40 (mm : mem) len dg,
    PMINV w8 w16 w24 w32 w40 mm len dg ->
    evt asegs Q (PMS 0xecf70 xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Ltac fam L := constr:(L sp F fc X N DG A IP IL FPT FL lo txt m0 ROOM TOP X8 XR XSH XS0 NR DGR TXR SPANS XSEP SHPT SHPN SHPD SHPL Q).

  Notation PMD D := (D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X N DG A IP IL FPT FL lo txt m0 Q) (only parsing).
  Notation PML L := (L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X N DG A IP IL FPT FL lo txt m0
                       ROOM TOP X8 XR XSH XS0 NR DGR TXR SPANS XSEP SHPT SHPN SHPD SHPL Q) (only parsing).

  Ltac pm_fam_clear m1 := repeat match goal with
    | H : u8arr asegs m1 _ _ |- _ => clear H
    | H : bytes_at asegs m1 (_ / 8 + 2147450880)%Z _ |- _ => clear H
    | H : mem_inv asegs m1 |- _ => clear H
    | H : munch _ _ m1 |- _ => clear H
    | H : wmono asegs _ m1 |- _ => clear H end.
  Ltac pm_fam_intro m1 :=
    pm_fam_clear m1; repeat lazymatch goal with |- u8arr _ _ _ _ -> _ => fail | |- forall _, _ => intro end;
    let XA := fresh "XA" in let XL := fresh "XL" in let ZR := fresh "ZR" in let MI := fresh "MI" in
    let MU := fresh "MU" in let WM := fresh "WM" in let MUX := fresh "MUX" in let WMX := fresh "WMX" in
    intros XA XL ZR MI MU WM MUX WMX;
    lazymatch type of MUX with munch _ _ ?mm2 => transport_after_call asegs m1 mm2 MUX WMX end; clear MUX WMX.

  Ltac pm_len k := lazymatch goal with XN : rw_cells asegs _ (_ + 496)%Z [C2 (Z_to_bv 64 ?l)] |- _ => k l end.
  Ltac pm_mul_cut L KW :=
    pm_len ltac:(fun l => num_cur_mem ltac:(fun m1 =>
      eapply evt_eq; [| eapply (L 62%nat 0%Z l)];
      [ num_st_eq | eassumption | lia | eassumption | eassumption | eassumption | eassumption | apply munch_refl | apply wmono_refl | lia | lia | lia
      | pm_fam_intro m1; KW ])).
  Ltac pm_car_cut L KW :=
    pm_len ltac:(fun l => num_cur_mem ltac:(fun m1 =>
      eapply evt_eq; [| eapply (L 62%nat 1%Z l)];
      [ num_st_eq | eassumption | lia | eassumption | eassumption | eassumption | eassumption | apply munch_refl | apply wmono_refl | lia | lia | lia | lia
      | pm_fam_intro m1; KW | pm_fam_intro m1; KW ])).

  Ltac pm_env :=
    unfold PMA_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    let SO := fresh "SO" in pose proof SPANS as SO; unfold pm_spans_ok in SO.

  Lemma pm_z1a : forall (fuel : nat) (Pv Ev : Z) xra xsp xgp xtp xt0 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 (mm : mem),
    bytes_at asegs mm A txt -> munch W m0 mm -> wmono asegs m0 mm ->
    (A <= Pv < Ev)%Z -> (Ev <= A + TL)%Z -> (Ev - Pv <= Z.of_nat fuel)%Z ->
    (forall Pv' yt2, (Pv <= Pv' < Ev)%Z ->
       evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) yt2 xs0 xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (Pv')) (Z_to_bv 64 (Pv')) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 Ev) xt5 xt6)
                    F (Z_to_bv 64 0xeb9e0) fc None mm (seg_rom asegs))) ->
    (forall yt2,
       evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) yt2 xs0 xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (Ev)) (Z_to_bv 64 (Ev)) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 Ev) xt5 xt6)
                    F (Z_to_bv 64 0xeb9c8) fc None mm (seg_rom asegs))) ->
    evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 Pv) (Z_to_bv 64 Pv) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 Ev) xt5 xt6)
                    F (Z_to_bv 64 0xeb9a4) fc None mm (seg_rom asegs)).
  Proof using PMH.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros TXT MU WM HP HE Hf K1 K2; [exfalso; lia|].
    pm_env.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xeb9a4%Z => first [ eapply evt_eq; [| eapply (IH (Pv + 1)%Z Ev); [exact TXT | exact MU | exact WM | lia | lia | lia | intros; eapply K1; lia | exact K2]]; num_st_eq | fail 100 "cut" pc ]
      | 0xeb9e0%Z => first [ eapply evt_eq; [| eapply (K1 Pv); lia]; num_st_eq | fail 100 "cut" pc ]
      | 0xeb9c8%Z => first [ eapply evt_eq; [| eapply K2]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_z1b : forall (fuel : nat) (Pv Ev : Z) xra xsp xgp xtp xt0 xt2 xs0 xs1 xa0 xa2 xa3 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (mm : mem),
    bytes_at asegs mm A txt -> munch W m0 mm -> wmono asegs m0 mm ->
    (A <= Pv < Ev)%Z -> (Ev <= A + TL)%Z -> (Ev - Pv <= Z.of_nat fuel)%Z ->
    (forall Pv' yt2, (Pv <= Pv' < Ev)%Z ->
       evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) yt2 xs0 xs1 xa0 (Z_to_bv 64 (Pv')) xa2 xa3 (Z_to_bv 64 (Pv')) xa5 xa6 (Z_to_bv 64 Ev) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0xebf88) fc None mm (seg_rom asegs))) ->
    (forall yt2,
       evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) yt2 xs0 xs1 xa0 (Z_to_bv 64 (Ev)) xa2 xa3 (Z_to_bv 64 (Ev)) xa5 xa6 (Z_to_bv 64 Ev) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0xec820) fc None mm (seg_rom asegs))) ->
    evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 Pv) xa2 xa3 (Z_to_bv 64 Pv) xa5 xa6 (Z_to_bv 64 Ev) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0xec7fc) fc None mm (seg_rom asegs)).
  Proof using PMH.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros TXT MU WM HP HE Hf K1 K2; [exfalso; lia|].
    pm_env.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xec7fc%Z => first [ eapply evt_eq; [| eapply (IH (Pv + 1)%Z Ev); [exact TXT | exact MU | exact WM | lia | lia | lia | intros; eapply K1; lia | exact K2]]; num_st_eq | fail 100 "cut" pc ]
      | 0xebf88%Z => first [ eapply evt_eq; [| eapply (K1 Pv); lia]; num_st_eq | fail 100 "cut" pc ]
      | 0xec820%Z => first [ eapply evt_eq; [| eapply K2]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_z1c : forall (fuel : nat) (Pv Ev : Z) xra xsp xgp xtp xt0 xt2 xs0 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 (mm : mem),
    bytes_at asegs mm A txt -> munch W m0 mm -> wmono asegs m0 mm ->
    (A <= Pv < Ev)%Z -> (Ev <= A + TL)%Z -> (Ev - Pv <= Z.of_nat fuel)%Z ->
    (forall Pv' ya5, (Pv <= Pv' < Ev)%Z ->
       evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (Pv')) xa2 xa3 xa4 ya5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (Pv')) (Z_to_bv 64 Ev) xt5 xt6)
                    F (Z_to_bv 64 0xecb40) fc None mm (seg_rom asegs))) ->
    (forall ya5,
       evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (Ev)) xa2 xa3 xa4 ya5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (Ev)) (Z_to_bv 64 Ev) xt5 xt6)
                    F (Z_to_bv 64 0xecb28) fc None mm (seg_rom asegs))) ->
    evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 Pv) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 Pv) (Z_to_bv 64 Ev) xt5 xt6)
                    F (Z_to_bv 64 0xecb04) fc None mm (seg_rom asegs)).
  Proof using PMH.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros TXT MU WM HP HE Hf K1 K2; [exfalso; lia|].
    pm_env.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xecb04%Z => first [ eapply evt_eq; [| eapply (IH (Pv + 1)%Z Ev); [exact TXT | exact MU | exact WM | lia | lia | lia | intros; eapply K1; lia | exact K2]]; num_st_eq | fail 100 "cut" pc ]
      | 0xecb40%Z => first [ eapply evt_eq; [| eapply (K1 Pv); lia]; num_st_eq | fail 100 "cut" pc ]
      | 0xecb28%Z => first [ eapply evt_eq; [| eapply K2]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_z1d : forall (fuel : nat) (Pv Ev : Z) xra xsp xgp xtp xt0 xt2 xs0 xs1 xa0 xa1 xa3 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (mm : mem),
    bytes_at asegs mm A txt -> munch W m0 mm -> wmono asegs m0 mm ->
    (A <= Pv < Ev)%Z -> (Ev <= A + TL)%Z -> (Ev - Pv <= Z.of_nat fuel)%Z ->
    (forall Pv' yt2, (Pv <= Pv' < Ev)%Z ->
       evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) yt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 (Pv')) xa3 (Z_to_bv 64 (Pv')) xa5 xa6 (Z_to_bv 64 Ev) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0xecdfc) fc None mm (seg_rom asegs))) ->
    (forall yt2,
       evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) yt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 (Ev)) xa3 (Z_to_bv 64 (Ev)) xa5 xa6 (Z_to_bv 64 Ev) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0xecde8) fc None mm (seg_rom asegs))) ->
    evt asegs Q (MS (mkR xra xsp xgp xtp xt0 (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 Pv) xa3 (Z_to_bv 64 Pv) xa5 xa6 (Z_to_bv 64 Ev) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0xecdc4) fc None mm (seg_rom asegs)).
  Proof using PMH.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros TXT MU WM HP HE Hf K1 K2; [exfalso; lia|].
    pm_env.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xecdc4%Z => first [ eapply evt_eq; [| eapply (IH (Pv + 1)%Z Ev); [exact TXT | exact MU | exact WM | lia | lia | lia | intros; eapply K1; lia | exact K2]]; num_st_eq | fail 100 "cut" pc ]
      | 0xecdfc%Z => first [ eapply evt_eq; [| eapply (K1 Pv); lia]; num_st_eq | fail 100 "cut" pc ]
      | 0xecde8%Z => first [ eapply evt_eq; [| eapply K2]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End PMA.
