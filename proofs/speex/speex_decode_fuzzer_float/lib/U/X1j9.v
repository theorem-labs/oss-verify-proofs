(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii X1it.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition reset_serialno_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A Bd L Gv : Z) (hdr : list byte) (m : mem) (r : Z) (os' : stream_st bptr) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + 408)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' A (stream_cells Bd L Gv hdr os') /\ stream_fields_ok os'.

Lemma recell_zero8' : forall m X pre post,
rw_cells rsegs m X (pre ++ C8 (Z_to_bv 64 0) :: post) -> rw_cells rsegs m X (pre ++ C4 (wz 0) :: C4 (wz 0) :: post).
Proof.
intros m X pre post H. eapply rw_cells_recell; [exact H| | |].
- apply cells_wf_app. pose proof (proj1 (proj1 H)) as WF. apply cells_wf_app in WF. destruct WF as [W1 W2].
split; [exact W1|]. cbn in W2 |- *. tauto.
- rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite le8_zero_split. rewrite <- app_assoc. reflexivity.
- rewrite !cells_size_app. reflexivity.
Qed.

Lemma ogg_stream_reset_serialno_spec : forall (A Bd L Gv : Z) (hdr : list byte) (os : stream_st bptr) (serialno : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) r (os' : stream_st bptr),
length hdr = 284%nat -> stream_fields_ok os -> 0 < A -> 0 <= Bd < 2^63 -> -2^31 <= serialno < 2^31 ->
(os_body_data os = None <-> Bd = 0) ->
mem_inv rsegs m -> rw_cells rsegs m A (stream_cells Bd L Gv hdr os) ->
ogg_stream_reset_serialno os serialno = (r, os') ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 serialno ->
evt rsegs (reset_serialno_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A Bd L Gv hdr m r os')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_reset_serialno) fc None m (seg_rom rsegs)).
Proof.
intros until os'. intros HL FOK HA HBd Hser HBD MI OS RES -> ->. unfold A_ogg_stream_reset_serialno.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as AB. cbn [cells_size csize Nat.add] in AB.
unfold ogg_stream_reset_serialno, ogg_stream_check in RES.

zstep. zstep. zstep. if_cases C0_; zify_cond C0_; rewrite ?unsigned_lit in C0_ by lia; [exfalso; lia|].
zstep. zstep. if_cases CB0; zify_cond CB0; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CB0 by lia.
-
destruct (os_body_data os) as [bd|]; [exfalso; pose proof (proj2 HBD CB0); discriminate|].
injection RES as <- <-. zstep. finish.
- destruct (os_body_data os) as [bd|]; [| exfalso; pose proof (proj1 HBD eq_refl); lia].
injection RES as <- <-.

zstep. lstep. lstep. lstep. lstep. lstep. zstep. lstep.

match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with OSx : rw_cells rsegs mx A ?cs |- _ =>
pose proof (rw_cells_merge rsegs mx A (firstn 12 cs) [nth 12 cs (CB 0 []); nth 13 cs (CB 0 [])] (skipn 14 cs) ltac:(exact OSx)) as OS2;
clear OSx; cbn [firstn skipn nth cells_size csize cells_bytes cbytes app Nat.add] in OS2 end end.
lstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with OSx : rw_cells rsegs mx A ?cs |- _ =>
pose proof (recell_zero8' mx A (firstn 12 cs) (skipn 13 cs) ltac:(exact OSx)) as OS3;
clear OSx; cbn [firstn skipn app] in OS3; unfold wz in OS3 end end.

zstep. lstep. lstep. lstep. zstep.
lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ =>
replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) in OSx by (apply bv_eq; reflexivity) end.
finish.
unfold stream_fields_ok, ogg_stream_reset, int31 in *; cbn. lia.
Qed.
