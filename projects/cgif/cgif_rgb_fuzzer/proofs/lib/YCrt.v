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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCe9 YCi1 YChi YCrr YCrn.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Record rfcx := mkRFCX {
x_STK : Z; x_sp0 : Z; x_FP : list (Z * Z); x_ly : alayout; x_S : astate; x_W0 : world trbsegs; x_mem0 : word -> option byte; x_md0 : Model;
x_own : list (Z * Z); x_lyc : alayout; x_Sc : astate; x_W : world trbsegs; x_memc : word -> option byte; x_mdc : Model; x_k : Z;
x_regs : bvmap 5 word; x_Bb : list (Z * Z); x_st : Z; x_dst : Z; x_N : Z; x_pdata : Z; x_nb : Z; x_cur : Z; x_cid : Z; x_pos : Z;
x_ch : list (Z * Z * Z); x_fpos : Z; x_sp1 : Z; x_E0 : env }.
Definition rf_base (B : asyms) (cx : rfcx) : Prop :=
ajournal trbsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx) /\
(forall b, In b (ablocks B (x_ly cx) (x_S cx)) -> In b (x_Bb cx)) /\ Permutation (ablocks B (x_lyc cx) (x_Sc cx)) (x_Bb cx) /\ In (x_pdata cx, x_nb cx) (x_Bb cx) /\
YK0s.ret_ok (getr (x_regs cx) 1) /\ 4096 <= raZ (x_regs cx) /\
getr (x_regs cx) 3 = w64 (as_gp B) /\ getr (x_regs cx) 4 = w64 (as_tp B) /\
getr (x_regs cx) 10 = w64 (x_st cx) /\ getr (x_regs cx) 11 = w64 (x_dst cx) /\ getr (x_regs cx) 12 = w64 (x_N cx) /\
achain (x_lyc cx) (aview trbsegs (w_H (x_W cx)) (x_memc cx)) (x_st cx + 24) (s0Z (x_regs cx)) (x_ch cx) /\
In (raZ (x_regs cx) :: spine (x_ch cx)) CTX_read_frameconfig /\ count_cid 0 (frames (x_Sc cx)) < fs_frames 0 /\
spZ (x_regs cx) mod 16 = 0 /\ x_sp0 cx - x_STK cx <= spZ (x_regs cx) - TRRFC_STK /\ spZ (x_regs cx) <= x_sp0 cx /\
In (x_cid cx, x_pos cx) (x_own cx) /\ 0 <= x_cid cx /\ frame_addr (x_lyc cx) (x_cid cx) (x_pos cx) mod 8 = 0 /\
frame_addr (x_lyc cx) (x_cid cx) (x_pos cx) <= x_dst cx /\ x_dst cx + RGBFC_SIZE <= frame_addr (x_lyc cx) (x_cid cx) (x_pos cx) + fs_frame_bytes (x_cid cx) /\ x_dst cx mod 8 = 0 /\
spZ (x_regs cx) <= x_st cx /\ x_st cx + 24 <= x_sp0 cx /\ x_st cx mod 8 = 0 /\
range_addressable (aview trbsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF (x_st cx) 24 /\
range_addressable (aview trbsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF (x_dst cx) RGBFC_SIZE /\
1 <= x_N cx <= RGB_NMAX /\ 0 <= x_cur cx <= x_nb cx /\ 0 < x_nb cx /\
val_mem trbsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (x_st cx) 8 (x_pdata cx) /\
val_mem trbsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (x_st cx + 8) 8 (x_nb cx) /\
val_mem trbsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (x_st cx + 16) 8 (x_cur cx) /\
vev (x_Sc cx) + EV_RRFC <= VEV_MAX   /\ blocks_bytes (x_Sc cx) + LIVE_RRFC <= LIVE_MAX /\
x_sp1 cx = 32 * ((spZ (x_regs cx) + -160) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (x_E0 cx) n = getr (x_regs cx) r) /\
ew (x_E0 cx) 32 = Z_to_bv 64 SB /\ ew (x_E0 cx) 33 = Z_to_bv 64 (x_pdata cx) /\ ew (x_E0 cx) 34 = Z_to_bv 64 (x_nb cx) /\
ew (x_E0 cx) 35 = Z_to_bv 64 (x_cur cx) /\ ew (x_E0 cx) 36 = Z_to_bv 64 (x_pdata cx + x_cur cx).
Definition rf_F (cx : rfcx) : Z := frame_addr (x_lyc cx) 0 (x_fpos cx).
Definition rf_FL (cx : rfcx) : Z := flag_addr (x_lyc cx) 0 (x_fpos cx).
Definition rf_E (cx : rfcx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (x_E0 cx) n) /\
ew E 32 = Z_to_bv 64 SB /\ ew E 33 = Z_to_bv 64 (x_pdata cx) /\ ew E 34 = Z_to_bv 64 (x_nb cx) /\
ew E 70 = Z_to_bv 64 (x_sp1 cx) /\ ew E 75 = Z_to_bv 64 (rf_F cx) /\ ew E 87 = Z_to_bv 64 (rf_FL cx) /\ ew E 88 = Z_to_bv 64 (SB + rf_F cx / 8).
Lemma rf_E_havoc : forall cx E N vs, (89 <= N)%nat -> rf_E cx E -> rf_E cx (havoc E N vs).
Proof. intros cx E N vs HN (AG & H32 & H33 & H34 & H70 & H75 & H87 & H88). unfold rf_E. rewrite !ew_havoc_old by lia. repeat split; try assumption. intros n Hn. rewrite ew_havoc_old by lia. apply AG. exact Hn. Qed.
Lemma rf_E_ewset : forall cx E n w, (89 <= n)%nat -> rf_E cx E -> rf_E cx (ewset E n w).
Proof. intros cx E n w HN (AG & H32 & H33 & H34 & H70 & H75 & H87 & H88). unfold rf_E. rewrite !ew_ewset_other by lia. repeat split; try assumption. intros m Hm. rewrite ew_ewset_other by lia. apply AG. exact Hm. Qed.
Definition rf_result (B : asyms) (cx : rfcx) (ly2 : alayout) (S2 : astate) (W2 : world trbsegs) (mem2 : word -> option byte) (res : Z) : Prop :=
(res = 2 ^ 64 - 1 /\ Permutation (ablocks B ly2 S2) (x_Bb cx) /\
exists fattr fgen delay, obj_at trbsegs (mrestrict (w_H W2) mem2) (x_dst cx) LAY_RgbFrameConfig [0; 0; fattr; fgen; delay]) \/
(res = 0 /\ Permutation (ablocks B ly2 S2) (x_Bb cx)) \/
(res = 1 /\ exists img fmt fattr fgen delay, (fmt = 3 \/ fmt = 4) /\
obj_at trbsegs (mrestrict (w_H W2) mem2) (x_dst cx) LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] /\
Permutation (ablocks B ly2 S2) ((img, fmt * x_N cx) :: x_Bb cx) /\
aftok (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (img, fmt * x_N cx) /\
forall blc i, In (img, fmt * x_N cx) blc -> 0 <= i < req_size (fmt * x_N cx) ->
awr_byte (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) blc ly2 (x_own cx) (img + i)).
Definition rf_post (B : asyms) (cx : rfcx) : world trbsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res cur2 : Z),
c2 = mkCfg (mkst regs2 (getr (x_regs cx) 1) mem2 (seg_rom trbsegs)) md2 /\
ajournal trbsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx + EV_RRFC) /\
aregs_preserved (x_regs cx) regs2 /\ frames S2 = frames (x_Sc cx) /\
jbud (x_Sc cx) S2 EV_RRFC /\
getr regs2 10 = w64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ (x_regs cx) - TRRFC_STK <= a < spZ (x_regs cx)) -> ~ (x_dst cx <= a < x_dst cx + RGBFC_SIZE) -> ~ (x_st cx + 16 <= a < x_st cx + 24) ->
aview trbsegs (w_H W2) mem2 a = aview trbsegs (w_H (x_W cx)) (x_memc cx) a) /\
(forall b m i, In (b, m) (x_Bb cx) -> 0 <= i < req_size m -> aview trbsegs (w_H W2) mem2 (b + i) = aview trbsegs (w_H (x_W cx)) (x_memc cx) (b + i)) /\
(forall c p a, In (c, p) (frames (x_Sc cx)) ->
(in_zr a (frame_rng (x_lyc cx) (c, p)) \/ in_zr a (shadow_addr (frame_addr (x_lyc cx) c p), fs_frame_bytes c / 8)) ->
~ (x_dst cx <= a < x_dst cx + RGBFC_SIZE) -> ~ (x_st cx + 16 <= a < x_st cx + 24) ->
aview trbsegs (w_H W2) mem2 a = aview trbsegs (w_H (x_W cx)) (x_memc cx) a) /\
val_mem trbsegs (mrestrict (w_H W2) mem2) (x_st cx) 8 (x_pdata cx) /\ val_mem trbsegs (mrestrict (w_H W2) mem2) (x_st cx + 8) 8 (x_nb cx) /\
val_mem trbsegs (mrestrict (w_H W2) mem2) (x_st cx + 16) 8 cur2 /\ x_cur cx <= cur2 <= x_nb cx /\
rf_result B cx ly2 S2 W2 mem2 res.
Definition rf_inv_t : Type := rfcx -> env -> Z -> alayout -> astate -> world trbsegs -> machine_state -> Model -> Prop.
Definition rf_Er (cx : rfcx) : Z -> Prop :=
fun a => in_zr a (frame_rng (x_lyc cx) (0, x_fpos cx)) \/ in_zr a (shadow_addr (rf_F cx), fs_frame_bytes 0 / 8).
Definition rf_fsep (cx : rfcx) : Prop :=
(forall b m i, In (b, m) (x_Bb cx) -> 0 <= i < req_size m -> ~ rf_Er cx (b + i)) /\
(forall c p a, In (c, p) (frames (x_Sc cx)) ->
(in_zr a (frame_rng (x_lyc cx) (c, p)) \/ in_zr a (shadow_addr (frame_addr (x_lyc cx) c p), fs_frame_bytes c / 8)) -> ~ rf_Er cx a).
Definition rf_from (B : asyms) (ss : sstate) (INV : rf_inv_t) : Prop :=
forall (cx : rfcx) (E : env) (kk : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rf_base B cx -> rf_E cx E ->
ajournal trbsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) ((0, x_fpos cx) :: x_own cx) ly3 S3 W3 (ms_mem ms3) md3 kk ->
jbud (x_Sc cx) S3 (kk - x_k cx) ->
frames S3 = (0, x_fpos cx) :: frames (x_Sc cx) -> ~ In (0, x_fpos cx) (frames (x_Sc cx)) -> rf_fsep cx ->
rfc_kept (x_W cx) (x_memc cx) W3 (ms_mem ms3) (spZ (x_regs cx)) (x_Bb cx) (x_lyc cx) (x_Sc cx) (x_st cx) (x_dst cx) ->
range_addressable (aview trbsegs (w_H W3) (ms_mem ms3)) SHADOW_OFF (x_st cx) 24 ->
range_addressable (aview trbsegs (w_H W3) (ms_mem ms3)) SHADOW_OFF (x_dst cx) 24 ->
INV cx E kk ly3 S3 W3 ms3 md3 ->
st_ok trbsegs E ss (restrict (w_H W3) ms3) ->
SRr trbsegs W3 (mkCfg ms3 md3) (rf_post B cx).
Definition rf_fromX (B : asyms) (ss : sstate) (INV : rf_inv_t) : Prop :=
forall (cx : rfcx) (E : env) (kk : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rf_base B cx -> rf_E cx E ->
ajournal trbsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) ly3 S3 W3 (ms_mem ms3) md3 kk ->
frames S3 = frames (x_Sc cx) ->
rfc_kept (x_W cx) (x_memc cx) W3 (ms_mem ms3) (spZ (x_regs cx)) (x_Bb cx) (x_lyc cx) (x_Sc cx) (x_st cx) (x_dst cx) ->
INV cx E kk ly3 S3 W3 ms3 md3 ->
st_ok trbsegs E ss (restrict (w_H W3) ms3) ->
SRr trbsegs W3 (mkCfg ms3 md3) (rf_post B cx).
Definition INV_R0 (B : asyms) : rf_inv_t :=
fun cx E kk ly3 S3 W3 ms3 md3 => kk = x_k cx /\ ablocks B ly3 S3 = ablocks B (x_lyc cx) (x_Sc cx).
Definition INV_R (B : asyms) (c : nat) : rf_inv_t :=
fun cx E kk ly3 S3 W3 ms3 md3 => kk = x_k cx /\ ablocks B ly3 S3 = ablocks B (x_lyc cx) (x_Sc cx) /\
exists curi, ew E c = Z_to_bv 64 curi /\ x_cur cx <= curi <= x_nb cx.
End d.
