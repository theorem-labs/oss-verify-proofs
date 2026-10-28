(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bk X1bs X1c2 X1bn X1cc X1c6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1rl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qv X0pw X0qx X0qy.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1fd X1nm.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Import X1bs.Exc.

Notation rsegs := X1ff.rsegs.

Definition rmemsetZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A n c : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Lemma rmemset_specZ : forall (A n c : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
mem_inv rsegs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
(0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
evt rsegs (rmemsetZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3a1dc) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros DST MI -> -> -> Hc Hn Hl.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
eapply evt_mono. { eapply memset_spec; [|exact MI]. rewrite EA, En. exact DST. }
intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed.

Definition rmemcpyZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' A [CB (Z.to_nat n) src]
/\ bytes_at rsegs m' S src.

Lemma rmemcpy_specZ : forall (A S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at rsegs m S src ->
length src = Z.to_nat n ->
rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
(S + n <= A \/ A + n <= S)%Z ->
mem_inv rsegs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
(0 <= n < 2^64)%Z -> (A < 2^64)%Z -> (S < 2^64)%Z ->
evt rsegs (rmemcpyZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A S n src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x39c5c) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros SRC LEN DST SEP MI -> -> -> Hn HA HS.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply memcpy_spec; [| | | | exact MI]; rewrite ?EA, ?ES, ?En; [exact SRC | exact LEN | exact DST | lia]. }
intros ms' PO. unfold memcpy_post in PO. rewrite EA, ES, En in PO. exact PO.
Qed.

Notation RGOT_SSP := 0x3c0d0%Z (only parsing).
Notation RGUARD := 0x6d6b8%Z (only parsing).

Definition rtd_cells (self prev next sysinfo : word) (tid errno detach : word) (robust locale canary dtvp dtv0 : word) : list cell :=
[C8 self; C8 prev; C8 next; C8 sysinfo; C4 tid; C4 errno; C4 detach; CB 76 (repeat (Z_to_bv 8 0) 76);
C8 robust; CB 24 (repeat (Z_to_bv 8 0) 24); C8 locale; CB 24 (repeat (Z_to_bv 8 0) 24); C8 canary;
C8 dtvp; CB 16 (repeat (Z_to_bv 8 0) 16); C8 dtv0; CB 112 (repeat (Z_to_bv 8 0) 112)].

Definition rinit_ssp_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo R : Z) (cw x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x6d6c0); (0x4d440, 0x4d448)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' RGUARD [C8 (canary_of cw)]
/\ rw_cells rsegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
/\ rw_cells rsegs m' RTD (rtd_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 (canary_of cw) x10 x11)
/\ bytes_at rsegs m' R (le8 cw).

Lemma rinit_ssp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo R : Z) (cw x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 : word) (junk : list byte),
stk rsegs m lo (bv_unsigned sp) ->
bytes_at rsegs m R (le8 cw) ->
rw_cells rsegs m RGUARD [CB 8 junk] ->
rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
rw_cells rsegs m RTD (td_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11) ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 R ->
(lo <= bv_unsigned sp - 16)%Z -> (0x6e000 <= lo)%Z -> (bv_unsigned sp <= R)%Z ->
evt rsegs (rinit_ssp_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo R cw x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x316dc) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros ST RND GU GG TDC MI -> -> LO LOLO SPR.
unfold td_cells in TDC.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x6d6c0); (0x4d440, 0x4d448)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
carve_frame 16%nat ST.
lstep. lstep. lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
do 4 lstep.
lstep. call (rmemcpy_specZ RGUARD R 8); [exact RND | reflexivity | exact GU | lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
rename PC into GU. clear RND. rename POST into RND. change (Z.to_nat 8) with 8%nat in GU. try rename MI0 into MI.

lstep. lstep. lstep. lstep.

apply (rw_cells_recast rsegs _ _ _ [C8 (canary_of cw)]) in GU;
[| cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; rewrite le8_canary_of; reflexivity | reflexivity].
lstep. lstep. lstep.
do 2 lstep. release_frame FR ST (bv_unsigned sp). lstep.
unfold rinit_ssp_post, rtd_cells. sys_finish.
Qed.

Definition rauxv20 (U HW rnd : word) : list word :=
[Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 10;
Z_to_bv 64 16; HW; Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; U; Z_to_bv 64 12; U; Z_to_bv 64 23; z64;
Z_to_bv 64 25; rnd; z64; z64].

Notation RENVIRON := 0x4d380%Z (only parsing).
Notation RPROGNAME := 0x6d6c8%Z (only parsing).
Notation RHWCAP := 0x6d740%Z (only parsing).
Notation RGOT3 := 0x3c0a8%Z (only parsing).

Lemma renvp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
bytes_at rsegs m A (u64s ws ++ le8 z64 ++ rest) ->
evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x30df8) fc None m (seg_rom rsegs)) ->
evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x30dec) fc None m (seg_rom rsegs)).
Proof.
induction ws as [|w ws IH]; intros until rest; intros NZ B HQ.
- cbn [u64s app] in B.
pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite app_length, length_le8 in BB.
pose proof (rd_u64 rsegs m A z64 rest (Z_to_bv 64 A) B eq_refl) as RD.
zstep. clear RD. zstep. zstep.
cbn [length Z.of_nat] in HQ. exact_evt HQ.
- cbn [u64s app] in B. rewrite <- app_assoc in B.
pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite !app_length, !length_le8 in BB.
apply Forall_cons_iff in NZ. destruct NZ as [NZw NZ].
pose proof (rd_u64 rsegs m A w _ (Z_to_bv 64 A) B eq_refl) as RD.
zstep. clear RD. zstep. zstep. if_true.
apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
eapply (IH Q); [exact NZ | exact B |].
cbn [length] in HQ. exact_evt HQ.
Qed.

Lemma rd_u64s_g : forall segs mm A ws (i : nat) w a,
bytes_at segs mm A (u64s ws) -> nth_error ws i = Some w -> a = wa (A + 8 * Z.of_nat i) ->
ov_read_bytes segs mm a 8 = Some (le8 w).
Proof.
intros segs mm A ws i w a B Hn ->.
first [ pose proof (u64s_split _ _ _ Hn) as sfP_; sf_destruct 6%nat sfP_ as pre post E1 Hlen Eu Hlu | sf_fb; destruct (u64s_split _ _ _ Hn) as (pre & post & E1 & Hlen & Eu & Hlu) ].
rewrite Eu in B. apply bytes_at_app in B. destruct B as [_ B]. rewrite Hlu in B.
eapply rd_u64; [exact B|]. unfold wa. f_equal. lia.
Qed.

Ltac ldaux AUXB i :=
let a := cur_mem_addr in
let RD := fresh "RD" in
pose proof (rd_u64s_g _ _ _ _ i _ a AUXB eq_refl ltac:(addr_tac)) as RD;
zstep; clear RD.

Ltac join2 H1 H2 :=
lazymatch type of H2 with rw_cells ?segs ?mm ?A2 ?cs2 =>
lazymatch type of H1 with rw_cells _ _ ?A ?cs1 =>
let H := fresh "J" in
assert (H : rw_cells segs mm A (cs1 ++ cs2))
by (apply (proj2 (rw_cells_app segs mm A cs1 cs2)); split;
[ exact H1
| replace (A + Z.of_nat (cells_size cs1))%Z with A2 by (simpl; lia); exact H2 ]);
clear H1 H2; cbn [app] in H; rename H into H1
end end.

Ltac hyp_by_addr :=
lazymatch goal with
| |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
| |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
| |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
| |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
end.

Section RInitLibc.
Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
(E : Z) (eps : list word) (U HW : word) (R : Z) (cw : word) (P : Z) (s : list byte)
(pn0 pnf0 hw0 env0 : word) (gjunk : list byte).
Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x4d388); (0x4d388, 0x4d4d8); (0x6d460, 0x6d490);
(RGUARD, 0x6d6c0); (RPROGNAME, 0x6d6d8); (RLIBC, 0x6d748)]%Z.
Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

Definition rinit_libc_post : Z -> machine_state -> Prop :=
fun t ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pg m',
ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' RTD (rtd_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) z64 (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
(Z_to_bv 64 0x4d400) (Z_to_bv 64 0x6d710) (canary_of cw) (Z_to_bv 64 0x4d460) z64)
/\ rw_cells rsegs m' RLIBC (libc_cells (Z_to_bv 8 1) (Z_to_bv 64 AUXV) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 4096))
/\ rw_cells rsegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
/\ rw_cells rsegs m' RSYSINFO [C8 z64]
/\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
/\ rw_cells rsegs m' RHWCAP [C8 HW]
/\ rw_cells rsegs m' RENVIRON [C8 (Z_to_bv 64 E)]
/\ rw_cells rsegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
/\ rw_cells rsegs m' RGUARD [C8 (canary_of cw)]
/\ rw_cells rsegs m' RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x6d6d0); C8 (Z_to_bv 64 RPROGNAME)]
/\ rw_cells rsegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
/\ rw_cells rsegs m' RGOT_DYNAMIC [C8 z64]
/\ bytes_at rsegs m' E (u64s eps ++ le8 z64 ++ u64s (rauxv20 U HW (Z_to_bv 64 R)))
/\ bytes_at rsegs m' P (s ++ [Z_to_bv 8 0])
/\ bytes_at rsegs m' R (le8 cw)
/\ (0 < t < 4194304)%Z.

Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
Hypothesis LOLO : (0x6e000 <= lo)%Z.
Hypothesis SPE : (bv_unsigned sp <= E)%Z.
Hypothesis SPP : (bv_unsigned sp <= P)%Z.
Hypothesis SPR : (bv_unsigned sp <= R)%Z.

Definition rpn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
fun ms' => exists pg m',
ms' = MS (mkR (Z_to_bv 64 0x30de0) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11   x5 x6 x7
(Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 47) z64 x14 x15 x16 x17
(Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30ebc) fc None m' (seg_rom rsegs)
/\ munch [(RPROGNAME, 0x6d6d0)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)].

#[using="lo NONUL LO LOLO SPP"] Lemma rpn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
(Z.of_nat k = Z.of_nat (length s) + 1 - j)%Z -> (1 <= j)%Z ->
munch [(RPROGNAME, 0x6d6d0)]%Z m0 mm -> wmono rsegs m0 mm -> mem_inv rsegs mm ->
bytes_at rsegs mm P (s ++ [Z_to_bv 8 0]) ->
rw_cells rsegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
evt rsegs (rpn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
(MS (mkR (Z_to_bv 64 0x30de0) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
(Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
(Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30eb0) fc None mm (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg Hk Hj MU WM MI STR G2.
- pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some (Z_to_bv 8 0)).
{ rewrite nth_error_app2 by lia. replace (Z.to_nat (j - 1) - length s)%nat with 0%nat by lia. reflexivity. }
pose proof (u8ro_read rsegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD. zstep. if_false. zstep. if_false.
replace (Z_to_bv 64 (P + j)) with (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) by (f_equal; lia).
unfold rpn_post. finish2. all: eassumption.
- pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
destruct (nth_error s (Z.to_nat (j - 1))) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some b) by (rewrite nth_error_app1 by lia; exact Hb).
pose proof (proj1 (Forall_forall _ _) NONUL b (nth_error_In _ _ Hb)) as NZb. cbn in NZb.
pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
pose proof (u8ro_read rsegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD. zstep. if_cases K.
+   lstep. zstep.
replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
eapply (IH (j + 1)%Z); try eassumption; lia.
+ zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. zstep.
replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
eapply (IH (j + 1)%Z); try eassumption; lia.
Qed.

Ltac rscan_it AUXB vi ki :=
lstep; if_false; ldaux AUXB vi; lstep; lstep;
(try lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?spv + -336 + ?c)] =>
let off := eval vm_compute in (-336 + c)%Z in
replace (Z_to_bv 64 (bv_unsigned spv + -336 + c)) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
end);
(try lazymatch goal with |- context [Z_to_bv 64 (?c + (bv_unsigned ?spv + -336))] =>
let off := eval vm_compute in (c + -336)%Z in
replace (Z_to_bv 64 (c + (bv_unsigned spv + -336))) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
end);
lstep; lstep; ldaux AUXB ki; lstep; astep.

#[using="EPS NONUL LO LOLO SPE SPP SPR"] Lemma rinit_libc_spec : forall tp a0 a1,
stk rsegs m lo (bv_unsigned sp) ->
bytes_at rsegs m E (u64s eps ++ le8 z64 ++ u64s (rauxv20 U HW (Z_to_bv 64 R))) ->
bytes_at rsegs m P (s ++ [Z_to_bv 8 0]) ->
bytes_at rsegs m R (le8 cw) ->
rw_cells rsegs m RPROGNAME [C8 pn0; C8 pnf0] ->
rw_cells rsegs m RHWCAP [C8 hw0] ->
rw_cells rsegs m RENVIRON [C8 env0] ->
rw_cells rsegs m RSYSINFO [C8 z64] ->
rw_cells rsegs m RLIBC (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) ->
rw_cells rsegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
rw_cells rsegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
rw_cells rsegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
rw_cells rsegs m RGUARD [CB 8 gjunk] ->
rw_cells rsegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x6d6d0); C8 (Z_to_bv 64 RPROGNAME)] ->
rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
mem_inv rsegs m ->
a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost rinit_libc_post)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x30db4) fc None m (seg_rom rsegs)).
Proof.
intros tp a0 a1 ST ENV STR RND G2 HWC ENVC SI LC TDC MT DS GU GOT3 GG GD MI -> ->.
unfold td_cells, libc_cells in *.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8 in EB. cbn [length rauxv20] in EB.
pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
iprefix.
carve_frame 384%nat ST.
do 10 lstep.

apply (rw_cells_split_CB rsegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
lstep. call (rmemset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
apply (rw_cells_recast rsegs _ _ _ (repeat (C8 z64) 38)) in AUX;
[| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.

lstep. lstep. lstep.
eapply (renvp_count_loop eps); [exact EPS | exact ENV |].

lstep. lstep. lstep.
pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.

rscan_it AUXB 1%nat 2%nat. rscan_it AUXB 3%nat 4%nat. rscan_it AUXB 5%nat 6%nat. rscan_it AUXB 7%nat 8%nat.
rscan_it AUXB 9%nat 10%nat. rscan_it AUXB 11%nat 12%nat. rscan_it AUXB 13%nat 14%nat. rscan_it AUXB 15%nat 16%nat.
rscan_it AUXB 17%nat 18%nat.

steps_to 0x30e70%Z.
astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.

steps_to 0x30eb0%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
call (rpn_loop (length s) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
rename POST into G2. try rename MI0 into MI.

apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUXa AUX].
apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUX3 AUXb].
cbn [cells_size csize Nat.add] in AUX3, AUXb. change (Z.of_nat 24) with 24%Z in *.
replace (bv_unsigned sp + -336 + 24)%Z with (bv_unsigned sp + -312)%Z in AUX3 by lia.
replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
lstep. lstep.
name_sp sp (-384)%Z. name_sp sp (-336)%Z.
icallk (rinit_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
all: lazymatch goal with
| |- forall _, _ => ipost rsegs; unname_sp; unname_sp
| |- _ => unname_sp; unname_sp;
first [ hyp_by_addr | reflexivity | lia
| lazymatch goal with |- rw_cells _ _ (?b + -336 + 24)%Z _ =>
replace (b + -336 + 24)%Z with (b + -312)%Z by lia; hyp_by_addr end ]
end.
rename PC into ST. unfold td_cells, libc_cells in *.

lstep. lstep.
call_sp (rinit_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R cw).
all: lazymatch goal with
| |- evt _ _ _ => idtac
| |- ?g => first [ hyp_by_addr | reflexivity | lia ]
end.
match goal with H : stk _ _ _ _ |- _ => rename H into ST end.

do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
do 5 lstep.
join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
release_frame FRlo ST (bv_unsigned sp).
lstep.
unfold rinit_libc_post, td_cells, rtd_cells, libc_cells in *. sys_finish; try lia.
all: hyp_by_addr.
Qed.
End RInitLibc.

