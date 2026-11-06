(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X0gi X02b X0j0 X0hn X0h2 X0h3 X0j4.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X173 X0ta X19k X188 X17n X17o X19n.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA.X1e9.
Import ListNotations.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
lazymatch type of t with
| (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
| ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
end.
Local Ltac zhide :=
repeat match goal with
| H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
end;
repeat match goal with
| H : (?x mod ?k = ?r)%Z |- _ =>
let q := fresh "zq" in let Hq := fresh "Hzq" in
destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
| H : context [(?x mod ?k = ?r)%Z] |- _ =>
lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
(try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
end;
repeat match goal with
| H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
end
end.

Local Ltac zidle_na H A a := tryif constr_eq A a then idtac else zidle1 H.
Local Ltac zidle_begin_at a n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(a, a + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_na H A a
| H : ro_cells segs m ?A _ |- _ => zidle_na H A a
| H : u8arr segs m ?A _ |- _ => zidle_na H A a
| H : u32arr segs m ?A _ |- _ => zidle_na H A a
| H : u64arr segs m ?A _ |- _ => zidle_na H A a
| H : bytes_at segs m ?A _ |- _ => zidle_na H A a
| H : u8ro segs m ?A _ |- _ => zidle_na H A a
end
end.
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma fs_stk_window : forall (m : mem) lo hi a n, stk bsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n ->
stk bsegs m lo a /\ (exists junk, rw_cells bsegs m a [CB (Z.to_nat n) junk]) /\ stk bsegs m (a + n) hi.
Proof.
intros m lo hi a n ST H1 H2 H3.
destruct (stk_split bsegs m lo a hi ST ltac:(lia)) as [S1 S23].
destruct (stk_split bsegs m a (a + n) hi S23 ltac:(lia)) as [S2 S3].
split; [exact S1|]. split; [| exact S3].
destruct (stk_carve bsegs m a (a + n) (Z.to_nat n) S2 ltac:(lia)) as [_ (junk & FR)].
exists junk. replace (a + n - Z.of_nat (Z.to_nat n)) with a in FR by lia. exact FR.
Qed.

Lemma land63 : forall x, 0 <= x -> Z.land x 63 = x mod 64.
Proof. intros x Hx. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma fs8_scan : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
fs_flags FSB 8 m fl -> Z.of_nat (length fl) = 64 -> flags_ok 8 fl ->
0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 8 + 64 <= 2 ^ 47 ->
scan_from fl 64 h 64 = Some j ->
(forall t0 a0, evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 8 + (h + Z.of_nat j) mod 64))
(Z_to_bv 64 (fl_base FSB 8)) (Z_to_bv 64 63) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 64))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x51d40) fc None m (seg_rom bsegs))) ->
mem_inv bsegs m ->
forall (k : nat), (k <= j)%nat -> forall t0 a3 a7,
evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (64 - Z.of_nat (j - k))) a1 (Z_to_bv 64 (h + Z.of_nat (j - k)))
a3 (Z_to_bv 64 (fl_base FSB 8)) (Z_to_bv 64 63) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51cf4) fc None m (seg_rom bsegs)).
Proof.
intros until fc. intros FL LEN OK HH HF HB SC K MI.
destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
induction k as [|k IH]; intros Hk t0 a3 a7.
- rewrite Nat.sub_0_r.
assert (E1 : Z.land (h + Z.of_nat j) 63 = (h + Z.of_nat j) mod 64) by (apply land63; lia).
zhide.
do 2 zstep. rewrite E1.
set (pos := (h + Z.of_nat j) mod 64) in *.
assert (Hpos : 0 <= pos < 64) by (apply Z.mod_pos_bound; lia).
pose proof (u8arr_read bsegs m (fl_base FSB 8) (map b8 fl) pos (b8 0) (Z_to_bv 64 (fl_base FSB 8 + pos)) FL) as RD.
rewrite nth_error_map_b8, Hfree in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 0)) with (Z_to_bv 64 0).
zstep. ifT.
exact (K _ _).
- set (i := (j - S k)%nat) in *.
assert (Hi : (i < j)%nat) by (unfold i; lia).
assert (E1 : Z.land (h + Z.of_nat i) 63 = (h + Z.of_nat i) mod 64) by (apply land63; lia).
do 2 zstep. rewrite E1.
set (pos := (h + Z.of_nat i) mod 64) in *.
assert (Hpos : 0 <= pos < 64) by (apply Z.mod_pos_bound; lia).
assert (Hb1 : nth (Z.to_nat pos) fl 1 = 1).
{ destruct (flags_ok_nth 8 fl (Z.to_nat pos) OK ltac:(lia)) as [H0|H0]; [|exact H0].
exfalso. exact (Hbusy i Hi H0). }
pose proof (u8arr_read bsegs m (fl_base FSB 8) (map b8 fl) pos (b8 1) (Z_to_bv 64 (fl_base FSB 8 + pos)) FL) as RD.
rewrite nth_error_map_b8, Hb1 in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 1)) with (Z_to_bv 64 1).
zstep. ifF.
do 2 zstep.
replace (bv_swrap 32 (64 - Z.of_nat i + -1)) with (64 - Z.of_nat (j - k)).
2:{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. unfold i in *. lia. }
replace (h + Z.of_nat i + 1) with (h + Z.of_nat (j - k)) by (unfold i in *; lia).
zstep. ifT.
apply IH. lia.
Qed.

Corollary fs8_scan0 : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
fs_flags FSB 8 m fl -> Z.of_nat (length fl) = 64 -> flags_ok 8 fl ->
0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 8 + 64 <= 2 ^ 47 ->
scan_from fl 64 h 64 = Some j ->
(forall t0 a0, evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 8 + (h + Z.of_nat j) mod 64))
(Z_to_bv 64 (fl_base FSB 8)) (Z_to_bv 64 63) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 64))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x51d40) fc None m (seg_rom bsegs))) ->
mem_inv bsegs m ->
forall t0 a3 a7,
evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 64) a1 (Z_to_bv 64 h)
a3 (Z_to_bv 64 (fl_base FSB 8)) (Z_to_bv 64 63) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51cf4) fc None m (seg_rom bsegs)).
Proof.
intros. pose proof (fs8_scan Q m FSB h fl j ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
H H0 H1 H2 H3 H4 H5 H6 H7 j ltac:(lia) t0 a3 a7) as X.
rewrite Nat.sub_diag in X. cbn [Z.of_nat] in X. rewrite Z.sub_0_r, Z.add_0_r in X. exact X.
Qed.

Definition sm8_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(FSB h size : Z) (fl : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (j : nat) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 (Z_to_bv 64 (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)))
a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch (sm_W 8 FSB ((h + Z.of_nat j) mod 64) (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ (j < 64)%nat /\ nth (Z.to_nat ((h + Z.of_nat j) mod 64)) fl 1 = 0
/\ fs_hint FSB 8 m' (h + Z.of_nat j + 1) /\ fs_const FSB m'
/\ fs_flags FSB 8 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 64)) 1)
/\ stk bsegs m' (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)) (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 24)
/\ rw_cells bsegs m' (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 24) [C8 sp]
/\ stk bsegs m' (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 32) (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 16376)
/\ rw_cells bsegs m' (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 16376) [C8 (Z_to_bv 64 (fl_base FSB 8 + (h + Z.of_nat j) mod 64))]
/\ rw_cells bsegs m' (shad (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)))
[CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (size / 8)))]
/\ stk bsegs m' (shad (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)) + size / 8) (shad (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)) + 2048)
/\ fs_free_frames FSB 8 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 64)) 1).

Definition sm8_entry : Z := 0x51c58.

Lemma stack_malloc_8_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (FSB h size : Z) (fl : list Z) (DTV dtvbeg TCX T lo : Z) (tb te : word),
a0 = Z_to_bv 64 size -> size mod 8 = 0 -> 0 < size <= 16384 -> ps_cells m ->
fs_const FSB m -> fs_hint FSB 8 m h -> fs_flags FSB 8 m fl -> flags_ok 8 fl -> (nbusy fl < 64)%nat -> 0 <= h < 2 ^ 61 ->
fs_free_frames FSB 8 m fl -> rw_cells bsegs m tpA [C8 (Z_to_bv 64 FSB)] ->
tga_cells DTV dtvbeg m -> thread_cells TCX T m -> ttls_cells T m tb te -> m2s_cells m ->
FSB_ok2 FSB -> 0x10007fff8008 <= lo -> FSB + kFakeStackSize <= lo ->
0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 -> 0 < TCX -> TCX + 0xa0 <= lo -> 0 < T -> T + 4096 <= lo ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 224 -> bv_unsigned sp <= 2 ^ 47 ->
mem_inv bsegs m ->
evt bsegs (sm8_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB h size fl lo m)
(MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 sm8_entry) fc None m (seg_rom bsegs)).
Proof.
intros until te. intros -> SZ8 SZR PS FC HI FL OK NB HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL HB HX HXL HT HTL ST LO SPH MI.
pose proof OK as (LEN & _). change (NF 8) with 64 in LEN.
destruct (scan_target_exists fl 64 h LEN ltac:(lia)) as (j & SC).
destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
set (pos := (h + Z.of_nat j) mod 64) in *.
assert (Hpos : 0 <= pos < 64) by (apply Z.mod_pos_bound; lia).
destruct (FF pos ltac:(change (NF 8) with 64; lia) Hfree) as [[junkF FRm] [junkS SHm]].
pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
rewrite shad_frame in SHm by lia. change (fsz 8) with 16384 in SHm. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in SHm.
pose proof (stk_of_rw_cells bsegs _ _ _ FRm) as FRS. clear FRm.
change (Z.of_nat (cells_size [CB (Z.to_nat (fsz 8)) junkF])) with 16384 in FRS.
unfold frame_addr, fsz in FRS, SHm.
change (8 * 2 ^ 20) with 8388608 in FRS. change (64 * 2 ^ 8) with 16384 in FRS.
change (8 * 2 ^ 17) with 1048576 in SHm. change (16384 / 8) with 2048 in SHm. change (Z.to_nat 2048) with 2048%nat in SHm.
replace (FSB + 36864 + 8388608 + pos * 16384) with (FSB + 8425472 + pos * 16384) in FRS by lia.
destruct (fs_stk_window _ _ _ (FSB + 8425472 + pos * 16384 + 24) 8 FRS ltac:(lia) ltac:(lia) ltac:(lia)) as (FRA & (jB & FRB) & FRC0). clear FRS.
destruct (fs_stk_window _ _ _ (FSB + 8425472 + pos * 16384 + 16376) 8 FRC0 ltac:(lia) ltac:(lia) ltac:(lia)) as (FRC & (jD & FRD) & _). clear FRC0.
change (Z.to_nat 8) with 8%nat in FRB, FRD.
replace (FSB + 8425472 + pos * 16384 + 24 + 8) with (FSB + 8425472 + pos * 16384 + 32) in FRC by lia.
set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
clearbody F8.
replace (SHB + F8 + 4608 + 1048576 + pos * 2048) with (F8 + pos * 2048 + 2148504064) in SHm by (unfold SHB; lia).
unfold fs_flags, fl_base, flags_off in FL. change (32768 - 2 ^ (15 - 8)) with 32640 in FL.
replace (FSB + 4096 + 32640) with (FSB + 36736) in FL by lia.
assert (LENM : Z.of_nat (length (map b8 fl)) = 64) by (rewrite length_map; exact LEN).
destruct M2S as (M2a & M2b & M2c).
destruct TGA as (AI & RL & DP & D1 & DC). destruct TC as (TS & TX). destruct TS as (KI & K & TS & T0).
destruct DC as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
unfold fs_const, fs_hint, ttls_cells, tpA, g_real_tls_get_addr, musl_tls_get_addr_entry, g_tls_index, g_dtv_ptr, g_dtv, g_dtv1,
dtv1_val, g_got_common_flags, g_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity,
g_got_dtls_off, g_tls_dtls, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, sm8_entry in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl (sm_W 8 FSB pos (bv_unsigned sp)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold sm_W in MU. rewrite shad_frame in MU by lia. unfold frame_addr, fsz, fl_base, flags_off in MU.
change (8 * 2 ^ 20) with 8388608 in MU. change (64 * 2 ^ 8) with 16384 in MU. change (8 * 2 ^ 17) with 1048576 in MU.
change (16384 / 8) with 2048 in MU. change (32768 - 2 ^ (15 - 8)) with 32640 in MU. unfold SHB in MU.
replace (FSB + 36864 + 8388608 + pos * 16384) with (FSB + 8425472 + pos * 16384) in MU by lia.
replace (FSB + 4096 + 32640) with (FSB + 36736) in MU by lia.
replace (2147450880 + FSB / 8 + 4608 + 1048576 + pos * 2048) with (F8 + pos * 2048 + 2148504064) in MU
by (rewrite EF8, (Z.mul_comm 8 F8), Z.div_mul by lia; lia).
replace (FSB + 8 * 8) with (FSB + 64) in MU, HI by lia.
carve_frame 48%nat ST.
zidle_begin sp 48%Z MUz WMz.
zhide.
zhide. do 11 zstep.
zidle_end MUz WMz.
sp_facts.
call (tls_get_addr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ DTV dtvbeg TCX T lo tb te).
1: exact (conj AI (conj RL (conj DP (conj D1 (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 G8))))))))))).
1: exact (conj (conj KI (conj K (conj TS T0))) TX).
1: exact TT.
all: rewrite ?Esp; try lia; try assumption.
rewrite Esp in POST. rename POST into ST.
clear AI RL DP D1 G1 G2 G3 G4 G5 G6 G7 G8 KI K TS T0 TX TT.
unfold tpA. zstep. zstep. ifF.
do 3 zstep. ifT.
do 5 zstep. ifF.
zhide. do 15 zstep.
replace (Z_to_bv 64 (FSB + 36736)) with (Z_to_bv 64 (fl_base FSB 8)) by (unfold fl_base, flags_off; f_equal; cbn; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (fs8_scan0 _ mm FSB h fl j) end.
1:{ unfold fs_flags, fl_base, flags_off. change (32768 - 2 ^ (15 - 8)) with 32640.
replace (FSB + 4096 + 32640) with (FSB + 36736) by lia. exact FL. }
all: try assumption; try lia.
1:{ unfold fl_base, flags_off. cbn. lia. }
intros t0' a0'.
change ((h + Z.of_nat j) mod 64) with pos.
replace (fl_base FSB 8) with (FSB + 36736) by (unfold fl_base, flags_off; cbn; lia).
do 4 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (u8arr_store_ok bsegs mm (FSB + 36736) (map b8 fl) pos (wa (FSB + 36736 + pos)) FL ltac:(lia) ltac:(f_equal; lia)) as SOK;
pose proof (u8arr_write bsegs mm (FSB + 36736) (map b8 fl) pos (b8 1) FL ltac:(lia)) as FL2 end.
zstep. change (le1 (Z_to_bv 64 1)) with [b8 1]. clear FL. store_done.
do 8 zstep.
assert (SH8 : pos ≪ 14 = pos * 16384) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity). rewrite SH8.
replace (FSB + 36864 + (8388608 + pos * 16384)) with (FSB + 8425472 + pos * 16384) by lia.
do 3 zstep.
zstep. zstep.
call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 8425472 + pos * 16384)).
1: reflexivity.
1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
1: exact (conj M2a (conj M2b M2c)).
1: assumption.
assert (ESH : shad (FSB + 8425472 + pos * 16384) = F8 + pos * 2048 + 2148504064).
{ unfold shad, SHB. rewrite EF8. replace (8 * F8 + 8425472 + pos * 16384) with ((F8 + 1053184 + pos * 2048) * 8) by lia.
rewrite Z.div_mul by lia. lia. }
clear TLS.

pose proof (stk_of_rw_cells bsegs _ _ _ SHm) as SHS. cbn [cells_size csize Nat.add] in SHS. change (Z.of_nat 2048) with 2048 in SHS.
assert (SZD : 0 < size / 8 <= 2048 /\ 8 * (size / 8) = size) by (Z.div_mod_to_equations; lia).
destruct (fs_stk_window _ _ _ (F8 + pos * 2048 + 2148504064) (size / 8) SHS ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (shj & SHA) & SHB2). clear SHS SHm.
do 4 zstep.
rewrite <- ESH in SHA.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (ps_cells_framed m mm _ PS MU WM ltac:(unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia)) as PSm end.
call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 8425472 + pos * 16384) size 0 lo shj).
all: rewrite ?Esp; unfold kHighShadowEnd in *; try lia; try eassumption.
1:{ unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [split; [| split; lia]|].
- rewrite EF8. replace (8 * F8 + 8425472 + pos * 16384) with (8 * (F8 + 1053184 + pos * 2048)) by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia.
- destruct FS1 as [FS1|FS1]; [left| right]; lia. }
lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite Esp in H; rename H into ST end.
rewrite ESH in *.
do 7 zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
assert (EFR : FSB + 8425472 + pos * 16384 = frame_addr FSB 8 pos) by (unfold frame_addr, fsz; cbn; lia).
rewrite EFR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE end.
apply evt_done. unfold sm8_post. change ((h + Z.of_nat j) mod 64) with pos.
do 15 eexists. exists mE.
split; [reflexivity|]. change ((h + Z.of_nat j) mod 64) with pos.
assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
assert (MU' : munch (sm_W 8 FSB pos (bv_unsigned sp)) m mE).
{ replace (sm_W 8 FSB pos (bv_unsigned sp)) with
[(FSB + 64, FSB + 64 + 8); (FSB + 36736 + pos, FSB + 36736 + pos + 1);
(FSB + 8425472 + pos * 16384, FSB + 8425472 + pos * 16384 + 16384);
(F8 + pos * 2048 + 2148504064, F8 + pos * 2048 + 2148504064 + 2048);
(bv_unsigned sp - 224, bv_unsigned sp)]; [exact MU|].
unfold sm_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
change (8 * 2 ^ 20) with 8388608. change (64 * 2 ^ 8) with 16384. change (8 * 2 ^ 17) with 1048576.
change (16384 / 8) with 2048. change (32768 - 2 ^ (15 - 8)) with 32640.
repeat (f_equal; try lia). }
split; [exact MU'|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [change (Z.to_nat 64) with 64%nat in Hj; exact Hj|]. split; [exact Hfree|].
split; [exact HI|]. split; [exact FC|].
split.
{ unfold fs_flags. rewrite map_b8_upd. replace (fl_base FSB 8) with (FSB + 36736) by (unfold fl_base, flags_off; cbn; lia).
exact FL2. }
split; [rewrite <- EFR; eassumption|]. split; [rewrite <- EFR; eassumption|]. split; [rewrite <- EFR; eassumption|].
split.
{ rewrite <- EFR. replace (fl_base FSB 8 + pos) with (FSB + 36736 + pos) by (unfold fl_base, flags_off; cbn; lia). eassumption. }
split.
{ rewrite <- EFR, ESH. eassumption. }
split.
{ rewrite <- EFR, ESH. eassumption. }
apply (fs_free_frames_transport FSB 8 m mE _ _ (fs_free_frames_take FSB 8 m fl (Z.to_nat pos) FF) MU' WM).
intros p Hp Hf. pose proof (nth_upd_free_other _ _ _ Hf) as Hne. change (NF 8) with 64 in Hp.
assert (Hne' : p <> pos) by (intro E; apply Hne; rewrite E; reflexivity).
unfold sm_W. rewrite !shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
change (8 * 2 ^ 20) with 8388608. change (64 * 2 ^ 8) with 16384. change (8 * 2 ^ 17) with 1048576.
change (16384 / 8) with 2048. change (32768 - 2 ^ (15 - 8)) with 32640.
cbn [disjoint_from]. split; repeat split; lia.
Qed.
End B_TWIN.

Import ListNotations.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
lazymatch type of t with
| (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
| ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
end.
Local Ltac zhide :=
repeat match goal with
| H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
end;
repeat match goal with
| H : (?x mod ?k = ?r)%Z |- _ =>
let q := fresh "zq" in let Hq := fresh "Hzq" in
destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
| H : context [(?x mod ?k = ?r)%Z] |- _ =>
lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
(try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
end;
repeat match goal with
| H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
end
end.

Local Ltac zidle_na H A a := tryif constr_eq A a then idtac else zidle1 H.
Local Ltac zidle_begin_at a n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(a, a + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_na H A a
| H : ro_cells segs m ?A _ |- _ => zidle_na H A a
| H : u8arr segs m ?A _ |- _ => zidle_na H A a
| H : u32arr segs m ?A _ |- _ => zidle_na H A a
| H : u64arr segs m ?A _ |- _ => zidle_na H A a
| H : bytes_at segs m ?A _ |- _ => zidle_na H A a
| H : u8ro segs m ?A _ |- _ => zidle_na H A a
end
end.
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma fs_stk_window : forall (m : mem) lo hi a n, stk asegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n ->
stk asegs m lo a /\ (exists junk, rw_cells asegs m a [CB (Z.to_nat n) junk]) /\ stk asegs m (a + n) hi.
Proof.
intros m lo hi a n ST H1 H2 H3.
destruct (stk_split asegs m lo a hi ST ltac:(lia)) as [S1 S23].
destruct (stk_split asegs m a (a + n) hi S23 ltac:(lia)) as [S2 S3].
split; [exact S1|]. split; [| exact S3].
destruct (stk_carve asegs m a (a + n) (Z.to_nat n) S2 ltac:(lia)) as [_ (junk & FR)].
exists junk. replace (a + n - Z.of_nat (Z.to_nat n)) with a in FR by lia. exact FR.
Qed.

Lemma land63 : forall x, 0 <= x -> Z.land x 63 = x mod 64.
Proof. intros x Hx. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma fs8_scan : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
fs_flags FSB 8 m fl -> Z.of_nat (length fl) = 64 -> flags_ok 8 fl ->
0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 8 + 64 <= 2 ^ 47 ->
scan_from fl 64 h 64 = Some j ->
(forall t0 a0, evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 8 + (h + Z.of_nat j) mod 64))
(Z_to_bv 64 (fl_base FSB 8)) (Z_to_bv 64 63) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 64))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x51c54) fc None m (seg_rom asegs))) ->
mem_inv asegs m ->
forall (k : nat), (k <= j)%nat -> forall t0 a3 a7,
evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (64 - Z.of_nat (j - k))) a1 (Z_to_bv 64 (h + Z.of_nat (j - k)))
a3 (Z_to_bv 64 (fl_base FSB 8)) (Z_to_bv 64 63) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51c08) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros FL LEN OK HH HF HB SC K MI.
destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
induction k as [|k IH]; intros Hk t0 a3 a7.
- rewrite Nat.sub_0_r.
assert (E1 : Z.land (h + Z.of_nat j) 63 = (h + Z.of_nat j) mod 64) by (apply land63; lia).
zhide.
do 2 zstep. rewrite E1.
set (pos := (h + Z.of_nat j) mod 64) in *.
assert (Hpos : 0 <= pos < 64) by (apply Z.mod_pos_bound; lia).
pose proof (u8arr_read asegs m (fl_base FSB 8) (map b8 fl) pos (b8 0) (Z_to_bv 64 (fl_base FSB 8 + pos)) FL) as RD.
rewrite nth_error_map_b8, Hfree in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 0)) with (Z_to_bv 64 0).
zstep. ifT.
exact (K _ _).
- set (i := (j - S k)%nat) in *.
assert (Hi : (i < j)%nat) by (unfold i; lia).
assert (E1 : Z.land (h + Z.of_nat i) 63 = (h + Z.of_nat i) mod 64) by (apply land63; lia).
do 2 zstep. rewrite E1.
set (pos := (h + Z.of_nat i) mod 64) in *.
assert (Hpos : 0 <= pos < 64) by (apply Z.mod_pos_bound; lia).
assert (Hb1 : nth (Z.to_nat pos) fl 1 = 1).
{ destruct (flags_ok_nth 8 fl (Z.to_nat pos) OK ltac:(lia)) as [H0|H0]; [|exact H0].
exfalso. exact (Hbusy i Hi H0). }
pose proof (u8arr_read asegs m (fl_base FSB 8) (map b8 fl) pos (b8 1) (Z_to_bv 64 (fl_base FSB 8 + pos)) FL) as RD.
rewrite nth_error_map_b8, Hb1 in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 1)) with (Z_to_bv 64 1).
zstep. ifF.
do 2 zstep.
replace (bv_swrap 32 (64 - Z.of_nat i + -1)) with (64 - Z.of_nat (j - k)).
2:{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. unfold i in *. lia. }
replace (h + Z.of_nat i + 1) with (h + Z.of_nat (j - k)) by (unfold i in *; lia).
zstep. ifT.
apply IH. lia.
Qed.

Corollary fs8_scan0 : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
fs_flags FSB 8 m fl -> Z.of_nat (length fl) = 64 -> flags_ok 8 fl ->
0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 8 + 64 <= 2 ^ 47 ->
scan_from fl 64 h 64 = Some j ->
(forall t0 a0, evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 8 + (h + Z.of_nat j) mod 64))
(Z_to_bv 64 (fl_base FSB 8)) (Z_to_bv 64 63) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 64))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x51c54) fc None m (seg_rom asegs))) ->
mem_inv asegs m ->
forall t0 a3 a7,
evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 64) a1 (Z_to_bv 64 h)
a3 (Z_to_bv 64 (fl_base FSB 8)) (Z_to_bv 64 63) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51c08) fc None m (seg_rom asegs)).
Proof.
intros. pose proof (fs8_scan Q m FSB h fl j ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
H H0 H1 H2 H3 H4 H5 H6 H7 j ltac:(lia) t0 a3 a7) as X.
rewrite Nat.sub_diag in X. cbn [Z.of_nat] in X. rewrite Z.sub_0_r, Z.add_0_r in X. exact X.
Qed.

Definition sm8_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(FSB h size : Z) (fl : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (j : nat) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 (Z_to_bv 64 (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)))
a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (sm_W 8 FSB ((h + Z.of_nat j) mod 64) (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ (j < 64)%nat /\ nth (Z.to_nat ((h + Z.of_nat j) mod 64)) fl 1 = 0
/\ fs_hint FSB 8 m' (h + Z.of_nat j + 1) /\ fs_const FSB m'
/\ fs_flags FSB 8 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 64)) 1)
/\ stk asegs m' (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)) (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 24)
/\ rw_cells asegs m' (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 24) [C8 sp]
/\ stk asegs m' (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 32) (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 16376)
/\ rw_cells asegs m' (frame_addr FSB 8 ((h + Z.of_nat j) mod 64) + 16376) [C8 (Z_to_bv 64 (fl_base FSB 8 + (h + Z.of_nat j) mod 64))]
/\ rw_cells asegs m' (shad (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)))
[CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (size / 8)))]
/\ stk asegs m' (shad (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)) + size / 8) (shad (frame_addr FSB 8 ((h + Z.of_nat j) mod 64)) + 2048)
/\ fs_free_frames FSB 8 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 64)) 1).

Definition sm8_entry : Z := 0x51b6c.

Lemma stack_malloc_8_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (FSB h size : Z) (fl : list Z) (DTV dtvbeg TCX T lo : Z) (tb te : word),
a0 = Z_to_bv 64 size -> size mod 8 = 0 -> 0 < size <= 16384 -> ps_cells m ->
fs_const FSB m -> fs_hint FSB 8 m h -> fs_flags FSB 8 m fl -> flags_ok 8 fl -> (nbusy fl < 64)%nat -> 0 <= h < 2 ^ 61 ->
fs_free_frames FSB 8 m fl -> rw_cells asegs m tpA [C8 (Z_to_bv 64 FSB)] ->
tga_cells DTV dtvbeg m -> thread_cells TCX T m -> ttls_cells T m tb te -> m2s_cells m ->
FSB_ok2 FSB -> 0x10007fff8008 <= lo -> FSB + kFakeStackSize <= lo ->
0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 -> 0 < TCX -> TCX + 0xa0 <= lo -> 0 < T -> T + 4096 <= lo ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 224 -> bv_unsigned sp <= 2 ^ 47 ->
mem_inv asegs m ->
evt asegs (sm8_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB h size fl lo m)
(MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 sm8_entry) fc None m (seg_rom asegs)).
Proof.
intros until te. intros -> SZ8 SZR PS FC HI FL OK NB HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL HB HX HXL HT HTL ST LO SPH MI.
pose proof OK as (LEN & _). change (NF 8) with 64 in LEN.
destruct (scan_target_exists fl 64 h LEN ltac:(lia)) as (j & SC).
destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
set (pos := (h + Z.of_nat j) mod 64) in *.
assert (Hpos : 0 <= pos < 64) by (apply Z.mod_pos_bound; lia).
destruct (FF pos ltac:(change (NF 8) with 64; lia) Hfree) as [[junkF FRm] [junkS SHm]].
pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
rewrite shad_frame in SHm by lia. change (fsz 8) with 16384 in SHm. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in SHm.
pose proof (stk_of_rw_cells asegs _ _ _ FRm) as FRS. clear FRm.
change (Z.of_nat (cells_size [CB (Z.to_nat (fsz 8)) junkF])) with 16384 in FRS.
unfold frame_addr, fsz in FRS, SHm.
change (8 * 2 ^ 20) with 8388608 in FRS. change (64 * 2 ^ 8) with 16384 in FRS.
change (8 * 2 ^ 17) with 1048576 in SHm. change (16384 / 8) with 2048 in SHm. change (Z.to_nat 2048) with 2048%nat in SHm.
replace (FSB + 36864 + 8388608 + pos * 16384) with (FSB + 8425472 + pos * 16384) in FRS by lia.
destruct (fs_stk_window _ _ _ (FSB + 8425472 + pos * 16384 + 24) 8 FRS ltac:(lia) ltac:(lia) ltac:(lia)) as (FRA & (jB & FRB) & FRC0). clear FRS.
destruct (fs_stk_window _ _ _ (FSB + 8425472 + pos * 16384 + 16376) 8 FRC0 ltac:(lia) ltac:(lia) ltac:(lia)) as (FRC & (jD & FRD) & _). clear FRC0.
change (Z.to_nat 8) with 8%nat in FRB, FRD.
replace (FSB + 8425472 + pos * 16384 + 24 + 8) with (FSB + 8425472 + pos * 16384 + 32) in FRC by lia.
set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
clearbody F8.
replace (SHB + F8 + 4608 + 1048576 + pos * 2048) with (F8 + pos * 2048 + 2148504064) in SHm by (unfold SHB; lia).
unfold fs_flags, fl_base, flags_off in FL. change (32768 - 2 ^ (15 - 8)) with 32640 in FL.
replace (FSB + 4096 + 32640) with (FSB + 36736) in FL by lia.
assert (LENM : Z.of_nat (length (map b8 fl)) = 64) by (rewrite length_map; exact LEN).
destruct M2S as (M2a & M2b & M2c).
destruct TGA as (AI & RL & DP & D1 & DC). destruct TC as (TS & TX). destruct TS as (KI & K & TS & T0).
destruct DC as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
unfold fs_const, fs_hint, ttls_cells, tpA, g_real_tls_get_addr, musl_tls_get_addr_entry, g_tls_index, g_dtv_ptr, g_dtv, g_dtv1,
dtv1_val, g_got_common_flags, g_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity,
g_got_dtls_off, g_tls_dtls, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, sm8_entry in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl (sm_W 8 FSB pos (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold sm_W in MU. rewrite shad_frame in MU by lia. unfold frame_addr, fsz, fl_base, flags_off in MU.
change (8 * 2 ^ 20) with 8388608 in MU. change (64 * 2 ^ 8) with 16384 in MU. change (8 * 2 ^ 17) with 1048576 in MU.
change (16384 / 8) with 2048 in MU. change (32768 - 2 ^ (15 - 8)) with 32640 in MU. unfold SHB in MU.
replace (FSB + 36864 + 8388608 + pos * 16384) with (FSB + 8425472 + pos * 16384) in MU by lia.
replace (FSB + 4096 + 32640) with (FSB + 36736) in MU by lia.
replace (2147450880 + FSB / 8 + 4608 + 1048576 + pos * 2048) with (F8 + pos * 2048 + 2148504064) in MU
by (rewrite EF8, (Z.mul_comm 8 F8), Z.div_mul by lia; lia).
replace (FSB + 8 * 8) with (FSB + 64) in MU, HI by lia.
carve_frame 48%nat ST.
zidle_begin sp 48%Z MUz WMz.
zhide.
zhide. do 11 zstep.
zidle_end MUz WMz.
sp_facts.
call (tls_get_addr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ DTV dtvbeg TCX T lo tb te).
1: exact (conj AI (conj RL (conj DP (conj D1 (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 G8))))))))))).
1: exact (conj (conj KI (conj K (conj TS T0))) TX).
1: exact TT.
all: rewrite ?Esp; try lia; try assumption.
rewrite Esp in POST. rename POST into ST.
clear AI RL DP D1 G1 G2 G3 G4 G5 G6 G7 G8 KI K TS T0 TX TT.
unfold tpA. zstep. zstep. ifF.
do 3 zstep. ifT.
do 5 zstep. ifF.
zhide. do 15 zstep.
replace (Z_to_bv 64 (FSB + 36736)) with (Z_to_bv 64 (fl_base FSB 8)) by (unfold fl_base, flags_off; f_equal; cbn; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (fs8_scan0 _ mm FSB h fl j) end.
1:{ unfold fs_flags, fl_base, flags_off. change (32768 - 2 ^ (15 - 8)) with 32640.
replace (FSB + 4096 + 32640) with (FSB + 36736) by lia. exact FL. }
all: try assumption; try lia.
1:{ unfold fl_base, flags_off. cbn. lia. }
intros t0' a0'.
change ((h + Z.of_nat j) mod 64) with pos.
replace (fl_base FSB 8) with (FSB + 36736) by (unfold fl_base, flags_off; cbn; lia).
do 4 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (u8arr_store_ok asegs mm (FSB + 36736) (map b8 fl) pos (wa (FSB + 36736 + pos)) FL ltac:(lia) ltac:(f_equal; lia)) as SOK;
pose proof (u8arr_write asegs mm (FSB + 36736) (map b8 fl) pos (b8 1) FL ltac:(lia)) as FL2 end.
zstep. change (le1 (Z_to_bv 64 1)) with [b8 1]. clear FL. store_done.
do 8 zstep.
assert (SH8 : pos ≪ 14 = pos * 16384) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity). rewrite SH8.
replace (FSB + 36864 + (8388608 + pos * 16384)) with (FSB + 8425472 + pos * 16384) by lia.
do 3 zstep.
zstep. zstep.
call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 8425472 + pos * 16384)).
1: reflexivity.
1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
1: exact (conj M2a (conj M2b M2c)).
1: assumption.
assert (ESH : shad (FSB + 8425472 + pos * 16384) = F8 + pos * 2048 + 2148504064).
{ unfold shad, SHB. rewrite EF8. replace (8 * F8 + 8425472 + pos * 16384) with ((F8 + 1053184 + pos * 2048) * 8) by lia.
rewrite Z.div_mul by lia. lia. }
clear TLS.

pose proof (stk_of_rw_cells asegs _ _ _ SHm) as SHS. cbn [cells_size csize Nat.add] in SHS. change (Z.of_nat 2048) with 2048 in SHS.
assert (SZD : 0 < size / 8 <= 2048 /\ 8 * (size / 8) = size) by (Z.div_mod_to_equations; lia).
destruct (fs_stk_window _ _ _ (F8 + pos * 2048 + 2148504064) (size / 8) SHS ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (shj & SHA) & SHB2). clear SHS SHm.
do 4 zstep.
rewrite <- ESH in SHA.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (ps_cells_framed m mm _ PS MU WM ltac:(unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia)) as PSm end.
call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 8425472 + pos * 16384) size 0 lo shj).
all: rewrite ?Esp; unfold kHighShadowEnd in *; try lia; try eassumption.
1:{ unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [split; [| split; lia]|].
- rewrite EF8. replace (8 * F8 + 8425472 + pos * 16384) with (8 * (F8 + 1053184 + pos * 2048)) by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia.
- destruct FS1 as [FS1|FS1]; [left| right]; lia. }
lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite Esp in H; rename H into ST end.
rewrite ESH in *.
do 7 zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
assert (EFR : FSB + 8425472 + pos * 16384 = frame_addr FSB 8 pos) by (unfold frame_addr, fsz; cbn; lia).
rewrite EFR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE end.
apply evt_done. unfold sm8_post. change ((h + Z.of_nat j) mod 64) with pos.
do 15 eexists. exists mE.
split; [reflexivity|]. change ((h + Z.of_nat j) mod 64) with pos.
assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
assert (MU' : munch (sm_W 8 FSB pos (bv_unsigned sp)) m mE).
{ replace (sm_W 8 FSB pos (bv_unsigned sp)) with
[(FSB + 64, FSB + 64 + 8); (FSB + 36736 + pos, FSB + 36736 + pos + 1);
(FSB + 8425472 + pos * 16384, FSB + 8425472 + pos * 16384 + 16384);
(F8 + pos * 2048 + 2148504064, F8 + pos * 2048 + 2148504064 + 2048);
(bv_unsigned sp - 224, bv_unsigned sp)]; [exact MU|].
unfold sm_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
change (8 * 2 ^ 20) with 8388608. change (64 * 2 ^ 8) with 16384. change (8 * 2 ^ 17) with 1048576.
change (16384 / 8) with 2048. change (32768 - 2 ^ (15 - 8)) with 32640.
repeat (f_equal; try lia). }
split; [exact MU'|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [change (Z.to_nat 64) with 64%nat in Hj; exact Hj|]. split; [exact Hfree|].
split; [exact HI|]. split; [exact FC|].
split.
{ unfold fs_flags. rewrite map_b8_upd. replace (fl_base FSB 8) with (FSB + 36736) by (unfold fl_base, flags_off; cbn; lia).
exact FL2. }
split; [rewrite <- EFR; eassumption|]. split; [rewrite <- EFR; eassumption|]. split; [rewrite <- EFR; eassumption|].
split.
{ rewrite <- EFR. replace (fl_base FSB 8 + pos) with (FSB + 36736 + pos) by (unfold fl_base, flags_off; cbn; lia). eassumption. }
split.
{ rewrite <- EFR, ESH. eassumption. }
split.
{ rewrite <- EFR, ESH. eassumption. }
apply (fs_free_frames_transport FSB 8 m mE _ _ (fs_free_frames_take FSB 8 m fl (Z.to_nat pos) FF) MU' WM).
intros p Hp Hf. pose proof (nth_upd_free_other _ _ _ Hf) as Hne. change (NF 8) with 64 in Hp.
assert (Hne' : p <> pos) by (intro E; apply Hne; rewrite E; reflexivity).
unfold sm_W. rewrite !shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
change (8 * 2 ^ 20) with 8388608. change (64 * 2 ^ 8) with 16384. change (8 * 2 ^ 17) with 1048576.
change (16384 / 8) with 2048. change (32768 - 2 ^ (15 - 8)) with 32640.
cbn [disjoint_from]. split; repeat split; lia.
Qed.
