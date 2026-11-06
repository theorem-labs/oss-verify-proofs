(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YChi YCi1 YCie YCph YCrr YCrd YCrc YCr3 YCr7.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0t YG0r YG0q YC00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition kG (c : Z) : Z := EV_RGBNEWGIF + (17 - c) * EV_RRFC + (16 - c) * (EV_RGBADD + 1).
Definition KH : Z := EV_RGBNEWGIF + 16 * (EV_RRFC + EV_RGBADD + 1).
Lemma kG_16 : EV_RGBNEWGIF + EV_RRFC = kG 16. Proof. reflexivity. Qed.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac kg_num := unfold kG, KH; replace EV_RRFC with 2 by reflexivity; replace EV_RGBADD with 1247 by reflexivity; replace EV_RGBNEWGIF with 14 by reflexivity.
Lemma kG_step : forall c, kG c + EV_RGBADD + 1 + EV_RRFC = kG (c - 1).
Proof. intros c. kg_num. lia. Qed.
Lemma kG_KH : forall c, 1 <= c <= 16 -> kG c + EV_RGBADD + 1 <= KH.
Proof. intros c Hc. kg_num. lia. Qed.
Lemma kG_le_KH : forall c, 1 <= c <= 16 -> kG c <= KH.
Proof. intros c Hc. kg_num. lia. Qed.
Lemma KH_RLIB : KH + EV_RGBCLOSE = EV_RLIB. Proof. reflexivity. Qed.

Lemma KH_newgif : EV_RGBNEWGIF + EV_RRFC <= KH. Proof. vm_compute. discriminate. Qed.
Definition rt_CS_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition rt_CS_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition rt_G_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31; 23; 24]%nat.
Definition rt_G_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31; 23; 24]%bv.
Definition rt_fconfig_region : YQ0b.region :=
{| r_base := Some 75%nat; r_lo := 112; r_hi := 136; r_wlo := 112; r_whi := 136;
r_chunks := [{| c_off := 112; YQ0b.c_val := CVal 8 (SOff 1002 0) |}; {| c_off := 120; YQ0b.c_val := CVal 4 (SOff 1003 0) |}] |}.
Definition rt_cur_region (n : nat) : YQ0b.region :=
{| r_base := Some 70%nat; r_lo := 48; r_hi := 56; r_wlo := 48; r_whi := 56; r_chunks := [{| c_off := 48; YQ0b.c_val := CVal 8 (SOff n 0) |}] |}.
Definition rt_locals48 : YQ0b.region :=
{| r_base := Some 70%nat; r_lo := 0; r_hi := 48; r_wlo := 0; r_whi := 48;
r_chunks := [{| c_off := 40; YQ0b.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 32; YQ0b.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 24; YQ0b.c_val := CVal 8 (SOff 75 0) |}] |}.
Definition rt_frame_hi : YQ0b.region :=
{| r_base := Some 75%nat; r_lo := 136; r_hi := 256; r_wlo := 136; r_whi := 256; r_chunks := [{| c_off := 248; YQ0b.c_val := CVal 8 (SOff 87 0) |}] |}.
Definition rt_frame_lo : YQ0b.region := {| r_base := Some 75%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |}.
Definition rt_shadow_region : YQ0b.region :=
{| r_base := Some 88%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 0; r_chunks :=
[{| c_off := 16; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 14; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 8; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 7; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 19; YQ0b.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 18; YQ0b.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 17; YQ0b.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 23; YQ0b.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 22; YQ0b.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 21; YQ0b.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 20; YQ0b.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 13; YQ0b.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 12; YQ0b.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 11; YQ0b.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 10; YQ0b.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 9; YQ0b.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 3; YQ0b.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 2; YQ0b.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YQ0b.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YQ0b.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 24; YQ0b.c_val := CVal 8 (SLit 0) |}] |}.
Definition rt_stack_region : YQ0b.region :=
{| r_base := Some 2%nat; r_lo := -104; r_hi := 0; r_wlo := -104; r_whi := 0; r_chunks :=
[{| c_off := -104; YQ0b.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YQ0b.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YQ0b.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YQ0b.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YQ0b.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YQ0b.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YQ0b.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YQ0b.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YQ0b.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YQ0b.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YQ0b.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YQ0b.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YQ0b.c_val := CVal 8 (SOff 1 0) |}] |}.
Definition rt_consts : smem :=
[{| r_base := None; r_lo := 668240; r_hi := 668248; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 668240; YQ0b.c_val := CVal 8 (SLit 701048) |}] |};
{| r_base := None; r_lo := 701048; r_hi := 701056; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 701048; YQ0b.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := None; r_lo := 668328; r_hi := 668336; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 668328; YQ0b.c_val := CVal 8 (SLit 701056) |}] |};
{| r_base := None; r_lo := 701056; r_hi := 701060; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 701056; YQ0b.c_val := CVal 4 (SLit 1) |}] |}].
Definition rt_imgok (img fmt : Z) : Prop := ((fmt = 3 \/ fmt = 4) /\ img <> 0) \/ (fmt = 0 /\ img = 0).
Definition rt_objI (B : asyms) (cx : rtcx) (ly3 : alayout) (S3 : astate) (W3 : world trbsegs) (ms3 : machine_state) (r N img fmt : Z) : Prop :=
exists g s wfn ctx path attr gen loops Wd Hd bef beffmt cur,
obj_at trbsegs (mrestrict (w_H W3) (ms_mem ms3)) r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; Wd; Hd; bef; beffmt; cur] /\
tcgif_at (mrestrict (w_H W3) (ms_mem ms3)) g s /\ cgif_wf s N /\ cg_W s = Wd /\ cg_H s = Hd /\
(bef = 0 \/ beffmt = 3 \/ beffmt = 4) /\
Permutation (ablocks B ly3 S3) (trgb_own r g s N bef beffmt ++ timg_block img fmt N ++ ablocks B (c_ly cx) (c_S cx)) /\
(forall b, In b (trgb_own r g s N bef beffmt ++ timg_block img fmt N) -> aftok [] (ablocks B (c_ly cx) (c_S cx)) b).
Definition INV_GX (B : asyms) (kb Fc c : Z) : rtcx -> env -> Z -> alayout -> astate -> world trbsegs -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => rbv (c_S cx) S3 (16 + 3 * (16 - c)) Fc /\ k <= kb /\ 1 <= c <= 16 /\ ew E 1000 = Z_to_bv 64 c /\ 2 <= c_n cx /\
exists r N cur img fmt,
ew E rt_RGB = Z_to_bv 64 r /\ ew E 542 = Z_to_bv 64 N /\ N <= RGB_NMAX /\
ew E 1001 = Z_to_bv 64 cur /\ 0 <= cur <= c_n cx /\
ew E 1002 = Z_to_bv 64 img /\ ew E 1003 = Z_to_bv 64 fmt /\ 0 <= img < 2 ^ 64 /\ 0 <= fmt < 2 ^ 32 /\ rt_imgok img fmt /\
rt_objI B cx ly3 S3 W3 ms3 r N img fmt.
Definition INV_G (B : asyms) (c : Z) := INV_GX B (kG c) (16 - c) c.
Definition INV_G2 (B : asyms) (c : Z) := INV_GX B (kG c + EV_RGBADD) (17 - c) c.
Definition INV_G3 (B : asyms) (c : Z) : rtcx -> env -> Z -> alayout -> astate -> world trbsegs -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => rbv (c_S cx) S3 (17 + 3 * (16 - c)) (17 - c) /\ k <= kG c + EV_RGBADD + 1 /\ 1 <= c <= 16 /\ ew E 1000 = Z_to_bv 64 c /\ 2 <= c_n cx /\
exists r N cur, ew E rt_RGB = Z_to_bv 64 r /\ ew E 542 = Z_to_bv 64 N /\ N <= RGB_NMAX /\
ew E 1001 = Z_to_bv 64 cur /\ 0 <= cur <= c_n cx /\ rt_obj B cx ly3 S3 W3 ms3 r N.
Definition INV_H (B : asyms) : rtcx -> env -> Z -> alayout -> astate -> world trbsegs -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => rbv (c_S cx) S3 62 16 /\ k <= KH /\ exists r N, ew E rt_RGB = Z_to_bv 64 r /\ rt_obj B cx ly3 S3 W3 ms3 r N.
Definition ss_G_0 : sstate :=
(mkSS 0x814bc
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0;
SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 75 0; SOff 547 0; SOff 542 0; SOff 75 112; SOff 1000 0; SOff 23 0; SOff 24 0; SOff 88 0; SOff 75 0; SLit 18446744073709551608;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
([rt_fconfig_region; rt_cur_region 1001; rt_frame_lo; rt_shadow_region; rt_frame_hi; rt_locals48; rt_stack_region] ++ rt_consts)
None
{|
f_atoms :=
[(88%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (87%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (75%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(70%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (11%nat, {| af_lo := 0; af_hi := 67108863; af_al2 := 0 |});
(32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)]
|}).
Definition ss_G : sstate := Eval vm_compute in ss_havoc_regs ss_G_0 1010 rt_G_deads.
Definition ss_G2 : sstate := Eval vm_compute in ss_havoc_regs (ss_set_pc ss_G 0x814c8) 1028 rt_CS_deads.
Definition ss_G3 : sstate := Eval vm_compute in ss_havoc_regs (ss_set_pc ss_G 0x814d0) 1044 rt_CS_deads.
Definition ss_H_0 : sstate :=
(mkSS 0x814ec
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0;
SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 75 0; SOff 547 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 88 0; SOff 75 0; SLit 18446744073709551608;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[rt_frame_lo; rt_shadow_region; rt_frame_hi; rt_stack_region]
None
{|
f_atoms :=
[(88%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (87%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (75%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(70%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (11%nat, {| af_lo := 0; af_hi := 67108863; af_al2 := 0 |});
(32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)]
|}).
Definition rt_H_deads : list nat := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 28; 29; 30; 31]%nat.
Definition rt_H_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 28; 29; 30; 31]%bv.
Definition ss_H : sstate := Eval vm_compute in ss_havoc_regs ss_H_0 1300 rt_H_deads.
End a.
