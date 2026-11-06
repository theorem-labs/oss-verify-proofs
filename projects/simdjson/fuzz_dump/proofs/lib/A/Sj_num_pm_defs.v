(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface D_defs D_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition pm_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition pm_spill (j0 : list byte) (w8 w16 w24 w32 w40 : word) (X : Z) : list cell :=
  [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 (Z_to_bv 64 (X / 8))].

Definition pm_inv (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (X N DG A IP IL FPT FL : Z) (txt : list byte) (lo : Z) (m0 : mem)
    (w8 w16 w24 w32 w40 : word) (mm : mem) (len dg : Z) : Prop :=
  (exists j0, rw_cells asegs mm (bv_unsigned sp + -160) (pm_spill j0 w8 w16 w24 w32 w40 X ++ pm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) /\
  (exists bs, u8arr asegs mm X bs /\ length bs = 496%nat) /\
  rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ 0 <= len <= 62 /\
  bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  rw_cells asegs mm DG [C8 (Z_to_bv 64 dg)] /\ 0 <= dg <= 770 /\
  rw_cells asegs mm (N + 32) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)] /\
  bytes_at asegs mm A txt /\
  (exists tb, bytes_at asegs mm 0x2b320 tb /\ length tb = 160%nat) /\
  mem_inv asegs mm /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (X, X + 504); (DG, DG + 8)] m0 mm /\ wmono asegs m0 mm /\ stk asegs mm lo (bv_unsigned sp + -160).

Ltac pm_open H :=
  let j0 := fresh "j0" in let bs := fresh "bs" in let tb := fresh "tb" in
  destruct H as ((j0 & FR) & (bs & XA & XL) & XN & ?LEN & ZR & DGC & ?DGB & NUMC & TXT & (tb & TB & TBL) & MI & MU & WM & ST);
  unfold pm_spill, pm_saved in FR; cbn [app] in FR.
Ltac pm_forget := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
  | H : length _ = 496%nat |- _ => clear H | H : length _ = 160%nat |- _ => clear H | H : length _ = length _ |- _ => clear H end.
Ltac pm_close :=
  unfold pm_inv, pm_spill, pm_saved; cbn [app];
  split; [eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|];
  split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|];
  split; [eexists; split; [eassumption| lia]|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.
