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
  Zqc Zqd Zsl Zqa Zq7 Zt5 Zuj Zu5 Zuk Zu4.
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
  Hypothesis XR : (0x669000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis NR : (N mod 8 = 0 /\ 0x669000 <= N /\ N + 64 <= lo)%Z.
  Hypothesis DGR : (DG mod 8 = 0 /\ SP <= DG /\ DG + 8 <= USTACK_TOP)%Z.
  Hypothesis TXR : (0 < A /\ A + TL <= lo /\ TL < 2147483648)%Z.
  Hypothesis SPANS : pm_spans_ok A txt IP IL FPT FL.

  Hypothesis XSEP : ((X + 504 <= N \/ N + 64 <= X) /\ (X + 504 <= A \/ A + TL <= X)
                     /\ (X / 8 + 2147450880 + 63 <= N \/ N + 64 <= X / 8 + 2147450880) /\ (X / 8 + 2147450880 + 63 <= A \/ A + TL <= X / 8 + 2147450880))%Z.
  Notation W := [(SP - 160, SP); (X, X + 504); (DG, DG + 8)]%Z.

  Hypothesis SHPT : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' (8 * (A / 8)) (A + TL - 8 * (A / 8)).
  Hypothesis SHPN : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' N 64.
  Hypothesis SHPD : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' DG 8.
  Hypothesis SHPL : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2ae60 160.
  Variable Q : machine_state -> Prop.
  Collection PMH := ROOM TOP X8 XR XSH XS0 NR DGR TXR SPANS XSEP SHPT SHPN SHPD SHPL.
  Notation PMINV := (pm_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X N DG A IP IL FPT FL txt lo m0).

  Notation PMS pc xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -160)) gp tp (Z_to_bv 64 (DG / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 DG) xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Hypothesis KEXIT : forall xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 w8 w16 w24 w32 w40 (mm : mem) len dg,
    PMINV w8 w16 w24 w32 w40 mm len dg ->
    evt asegs Q (PMS 0xc8174 xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).

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

  Variables w8 w24 w32 w40 : word.
  Notation PMINV2 := (PMINV w8 (Z_to_bv 64 761) w24 w32 w40).
  Notation PE := (IP + IL)%Z.

  Notation PMI pc xra xt2 p xa6 xa7 xs3 xs5 xs7 xs9 xs11 xt5 xt6 mm :=
    (PMS pc xra xt2 (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 X) (Z_to_bv 64 N) (Z_to_bv 64 769) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 p) xa6 xa7
         (Z_to_bv 64 10) xs3 (Z_to_bv 64 1) xs5 (Z_to_bv 64 (2147450880 + X / 8)) xs7 (Z_to_bv 64 1095216660735) xs9 (Z_to_bv 64 17) xs11
         (Z_to_bv 64 175712) (Z_to_bv 64 PE) xt5 xt6 mm).

  Definition ibot_k (p0 : Z) : Prop :=
    forall (p' len' dg' : Z) xra xt2 xa6 xa7 xs3 xs5 xs7 xs9 xs11 xt5 xt6 (mm' : mem),
      PMINV2 mm' len' dg' -> (p0 < p' <= PE)%Z -> (0 <= dg' < 769)%Z ->
      evt asegs Q (PMI 0xc6c68 xra xt2 p' xa6 xa7 xs3 xs5 xs7 xs9 xs11 xt5 xt6 mm').

  Definition iti_k : Prop :=
    forall (p' len' cnt' : Z) xra xt2 xa6 xs3 xs9 xs11 xt5 xt6 (mm' : mem),
      PMINV2 mm' len' 769 -> (IP <= p' <= PE)%Z -> (0 <= cnt' <= 19)%Z ->
      evt asegs Q (PMI 0xc76b0 xra xt2 p' xa6 (Z_to_bv 64 cnt') xs3 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 len') xs9 xs11 xt5 xt6 mm').

  Lemma pm_i_push : forall (p0 p len dg : Z) xt2 xa6 xa7 xs3 xs7 xs9 xs11 xt5 xt6 (mm : mem),
    ibot_k p0 -> PMINV2 mm len dg -> (len <= 61)%Z -> (p0 < p <= PE)%Z -> (0 <= dg < 769)%Z ->
    evt asegs Q (PMI 0xc7094 (Z_to_bv 64 len) xt2 p xa6 xa7 xs3 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs7 xs9 xs11 xt5 xt6 mm).
  Proof using PMH.
    intros until mm. intros HBOT INV Hl Hp Hd. pm_open INV. pm_env.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc6c68%Z => first [ eapply evt_eq; [| eapply (HBOT p); [pm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_i_b0 : forall (p0 p len dg : Z) xra xt2 xa6 xa7 xs3 xs7 xs9 xs11 xt5 xt6 (mm : mem),
    ibot_k p0 -> PMINV2 mm len dg -> (p0 < p <= PE)%Z -> (0 <= dg < 769)%Z ->
    evt asegs Q (PMI 0xc6fec xra xt2 p xa6 xa7 xs3 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs7 xs9 xs11 xt5 xt6 mm).
  Proof using PMH.
    intros until mm. intros HBOT INV Hp Hd. pm_open INV. pm_env.
    assert (DMv : IsData xs11) by exact I.
    let L := fam constr:(pm_cara) in
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc6c68%Z => first [ eapply evt_eq; [| eapply (HBOT p); [pm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xc7094%Z => first [ eapply evt_eq; [| eapply (pm_i_push p0 p _ dg); [exact HBOT | pm_close | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xc7040%Z => first [ num_cur_mem ltac:(fun m1 =>
            eapply evt_eq; [| eapply (L 62%nat 1%Z len); [eassumption | lia | eassumption | eassumption | eassumption | eassumption | apply munch_refl | apply wmono_refl | lia | lia | lia | lia | |]];
            [ num_st_eq | pm_fam_intro m1 | pm_fam_intro m1 ]) | fail 100 "cut" pc ]
      end).
    all: awalk ltac:(fun pc => lazymatch pc with
      | 0xc6c68%Z => first [ eapply evt_eq; [| eapply (HBOT p); [pm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xc7094%Z => first [ eapply evt_eq; [| eapply (pm_i_push p0 p _ dg); [exact HBOT | pm_close | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Definition idbc_k (p0 : Z) : Prop :=
    forall (p' dg' cnt' len : Z) xra xt2 xa6 xs3 xs5 xs7 xs9 xs11 xt5 xt6 (mm' : mem),
      PMINV2 mm' len dg' -> (p0 <= p' <= PE)%Z -> (0 <= cnt' <= 19)%Z -> (0 <= dg' <= 769)%Z -> (dg' = 769 \/ p0 < p')%Z ->
      evt asegs Q (PMI 0xc6f20 xra xt2 p' xa6 (Z_to_bv 64 cnt') xs3 xs5 xs7 xs9 xs11 xt5 xt6 mm').

  Lemma pm_i_dbc : forall p0, (IP <= p0)%Z -> ibot_k p0 -> iti_k -> idbc_k p0.
  Proof using PMH.
    intros p0 Hp0 HBOT HTI. unfold idbc_k. intros until mm'. intros INV Hp Hc Hd Hprog.
    pm_open INV. pm_env.
    assert (DMv : IsData xs11) by exact I.
    let L := fam constr:(pm_mula) in
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc76b0%Z => first [ assert (E769 : dg' = 769%Z) by lia; subst dg'; eapply evt_eq; [| eapply (HTI p' len cnt'); [pm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xc6fec%Z => first [ eapply evt_eq; [| eapply (pm_i_b0 p0 p' _ dg'); [exact HBOT | pm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xc6f74%Z => first [ num_cur_mem ltac:(fun m1 =>
            eapply evt_eq; [| eapply (L 62%nat 0%Z len); [eassumption | lia | eassumption | eassumption | eassumption | eassumption | apply munch_refl | apply wmono_refl | lia | lia | lia |]];
            [ num_st_eq | pm_fam_intro m1 ]) | fail 100 "cut" pc ]
      end).
    all: awalk ltac:(fun pc => lazymatch pc with
      | 0xc6fec%Z => first [ eapply evt_eq; [| eapply (pm_i_b0 p0 p' _ dg'); [exact HBOT | pm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End PMA.
