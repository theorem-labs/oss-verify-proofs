(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X03z X04v X02a X02b X00b
X04g X04e.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X0ux X0vt X0t9 X0ta X0ra X0ve X0vc.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ve OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition cmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(b1 b2 : list byte) (K lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - K, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
/\ (bv_unsigned v = 0 <-> b1 = b2).

Definition cmp_pre (sp : word) (p1 p2 : Z) (b1 b2 : list byte) (K lo : Z) (m : mem) : Prop :=
length b1 = length b2 /\ 0 < Z.of_nat (length b1)
/\ stk bsegs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - K /\ kHighShadowEnd + 8 <= lo /\ bv_unsigned sp < 2^63
/\ 0 < p1 /\ 0 < p2 /\ p1 + Z.of_nat (length b1) <= 2^47 /\ p2 + Z.of_nat (length b1) <= 2^47
/\ (p1 + Z.of_nat (length b1) <= lo \/ bv_unsigned sp <= p1) /\ (p2 + Z.of_nat (length b1) <= lo \/ bv_unsigned sp <= p2)
/\ bytes_at bsegs m p1 b1 /\ bytes_at bsegs m p2 b2
/\ chk_ok m p1 (Z.of_nat (length b1)) /\ chk_ok m p2 (Z.of_nat (length b1))
/\ m2s_cells m /\ icells m /\ icells_cmp m /\ mem_inv bsegs m.

Definition cmpfn_stmt (fn K : Z) : Prop :=
forall (p1 p2 : Z) (b1 b2 : list byte) (lo : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 (Z.of_nat (length b1)) ->
cmp_pre sp p1 p2 b1 b2 K lo m ->
evt bsegs (cmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc b1 b2 K lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 fn) fc None m (seg_rom bsegs)).

Definition commonfn_stmt (fn K : Z) : Prop :=
forall (p1 p2 : Z) (b1 b2 : list byte) (lo : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
a1 = Z_to_bv 64 fn -> a2 = Z_to_bv 64 p1 -> a3 = Z_to_bv 64 p2 -> a4 = Z_to_bv 64 (Z.of_nat (length b1)) ->
cmp_pre sp p1 p2 b1 b2 K lo m ->
evt bsegs (cmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc b1 b2 K lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x57aa0) fc None m (seg_rom bsegs)).

Lemma cells_off_stack : forall (W : list (Z * Z)) (m m' : mem), munch W m m' -> wmono bsegs m m' ->
(forall x, x < 0x65b000 -> outside W x) ->
(m2s_cells m -> m2s_cells m') /\ (icells m -> icells m') /\ (icells_cmp m -> icells_cmp m').
Proof.
intros W m m' MU WM OFF.
assert (RO : forall a cs, ro_cells bsegs m a cs -> a + Z.of_nat (cells_size cs) <= 0x65b000 -> ro_cells bsegs m' a cs).
{ intros a cs H B. apply (ro_cells_agree bsegs m m' a cs H). apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply OFF. lia. }
assert (RW : forall a cs, rw_cells bsegs m a cs -> a + Z.of_nat (cells_size cs) <= 0x65b000 -> rw_cells bsegs m' a cs).
{ intros a cs H B. apply (rw_cells_agree bsegs m m' a cs H); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply OFF. lia. }
split; [| split].
- intros (M1 & M2 & M3). split; [| split]; apply RW; try assumption; cbn; lia.
- intros (G2 & G1 & RM & SHC & RI). split; [| split; [| split; [| split]]]; apply RO; try assumption; cbn; lia.
- intros (GCF & GRE & AI & FL). split; [| split; [| split]]; [apply RO | apply RO | apply RW | apply RO]; try assumption; cbn; lia.
Qed.

Local Ltac common_tail :=
let ST4 := fresh "ST4" in
lazymatch goal with H : stk bsegs _ _ (bv_unsigned (Z_to_bv 64 (?u + -2192))) |- _ =>
rewrite (unsigned_lit (u + -2192)) in H by lia; rename H into ST4 end;
do 25 lstep;
lazymatch goal with FR : rw_cells bsegs _ (?u + -2192) [CB 2088 _], FRs : rw_cells bsegs _ (?u + -104) _ |- _ =>
release_frame FR ST4 (u + -104); release_frame FRs ST4 u end;
lstep;
unfold cmp_post; sys_finish;
[ lazymatch goal with MU : munch _ _ _ |- munch _ _ _ => rewrite (unsigned_lit _) by lia; eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia end
| rewrite (unsigned_lit _) by lia; assumption ].

Section Common.
Hypothesis RIP : rip_stmt.
Variables (fn K : Z).
Hypothesis FN : fn = 0xf16c4 \/ fn = 0xf15f4.
Hypothesis K0 : 0 <= K.
Hypothesis REAL : cmpfn_stmt fn K.

Theorem memcmpc_spec : commonfn_stmt fn (K + MEMCMPC_DEPTH).
Proof using RIP FN K0 REAL.
unfold commonfn_stmt. intros until m.
intros -> -> -> -> (LEN & NPOS & ST & LO & LOLO & SPH & P1 & P2 & H1 & H2 & SEP1 & SEP2 & BY1 & BY2 & CS1 & CS2 & M2S & IC & ICC & MI).
unfold kHighShadowEnd in *.
set (n := Z.of_nat (length b1)) in *.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
pose proof (munch_refl [(usp - (K + 2272), usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (BY10 : keep (bytes_at bsegs m p1 b1)) by exact BY1. clear BY1.
assert (BY20 : keep (bytes_at bsegs m p2 b2)) by exact BY2. clear BY2.

assert (OFF : forall m', munch [(usp - (K + 2272), usp)] m m' -> wmono bsegs m m' ->
chk_ok m' p1 n /\ chk_ok m' p2 n /\ m2s_cells m' /\ icells m' /\ icells_cmp m' /\ bytes_at bsegs m' p1 b1 /\ bytes_at bsegs m' p2 b2).
{ intros m' MU' WM'.
destruct (cells_off_stack _ m m' MU' WM' ltac:(intros x Hx; cbn [outside]; split; [lia| exact I])) as (T1 & T2 & T3).
split; [apply (chk_ok_agree m m' p1 n CS1 ltac:(lia) H1); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [apply (chk_ok_agree m m' p2 n CS2 ltac:(lia) H2); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [exact (T1 M2S)|]. split; [exact (T2 IC)|]. split; [exact (T3 ICC)|].
split; [unfold keep in BY10; apply (bytes_at_agree bsegs m m' _ _ BY10) | unfold keep in BY20; apply (bytes_at_agree bsegs m m' _ _ BY20)];
apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; rewrite <- ?LEN in Hx; fold n in Hx; (split; [lia| exact I]). }
call (memcmpc_prologue usp p1 p2 n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact ICC| exact MI|].
rename PC into FRs. rename PC0 into FR. rename POST into ST1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MU WM) as (C1 & C2 & M2S1 & IC1 & ICC1 & _ & _) end.
call (memcmpc_r1 RIP usp p1 p2 n); [exact ST1| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
| exact C1| exact M2S1| exact IC1| assumption|].
lazymatch goal with H : stk bsegs _ lo (usp + -2192) |- _ => rename H into ST2 end.
clear C1 C2 M2S1 IC1 ICC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MU WM) as (C1 & C2 & M2S1 & IC1 & ICC1 & _ & _) end.
call (memcmpc_r2 RIP usp p1 p2 n); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
| exact C2| exact M2S1| exact IC1| assumption|].
lazymatch goal with H : stk bsegs _ lo (usp + -2192) |- _ => rename H into ST3 end.
clear C1 C2 M2S1 IC1 ICC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MU WM) as (C1 & C2 & M2S1 & IC1 & ICC1 & BY1 & BY2) end.
assert (EU2192 : bv_unsigned (Z_to_bv 64 (usp + -2192)) = usp + -2192) by (apply unsigned_lit; lia).
do 3 lstep.
assert (PRE : forall mm, munch [(usp - (K + 2272), usp)] m mm -> wmono bsegs m mm -> mem_inv bsegs mm -> stk bsegs mm lo (usp + -2192) ->
cmp_pre (Z_to_bv 64 (usp + -2192)) p1 p2 b1 b2 K lo mm).
{ intros mm MUm WMm MIm STm. destruct (OFF mm MUm WMm) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
unfold cmp_pre. rewrite EU2192. fold n.
split; [exact LEN|]. split; [exact NPOS|]. split; [exact STm|]. split; [lia|]. split; [unfold kHighShadowEnd; lia|]. split; [lia|].
split; [exact P1|]. split; [exact P2|]. split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact D6|]. split; [exact D7|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5| exact MIm]. }
pose proof REAL as REAL'.
destruct FN as [EF|EF]; rewrite EF in REAL' |- *; clear EF.
- lstep.
call (REAL' p1 p2 b1 b2 lo); [reflexivity | reflexivity | reflexivity | apply PRE; assumption |].
common_tail.
- lstep.
call (REAL' p1 p2 b1 b2 lo); [reflexivity | reflexivity | reflexivity | apply PRE; assumption |].
common_tail.
Qed.
End Common.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition cmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(b1 b2 : list byte) (K lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - K, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ (bv_unsigned v = 0 <-> b1 = b2).

Definition cmp_pre (sp : word) (p1 p2 : Z) (b1 b2 : list byte) (K lo : Z) (m : mem) : Prop :=
length b1 = length b2 /\ 0 < Z.of_nat (length b1)
/\ stk asegs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - K /\ kHighShadowEnd + 8 <= lo /\ bv_unsigned sp < 2^63
/\ 0 < p1 /\ 0 < p2 /\ p1 + Z.of_nat (length b1) <= 2^47 /\ p2 + Z.of_nat (length b1) <= 2^47
/\ (p1 + Z.of_nat (length b1) <= lo \/ bv_unsigned sp <= p1) /\ (p2 + Z.of_nat (length b1) <= lo \/ bv_unsigned sp <= p2)
/\ bytes_at asegs m p1 b1 /\ bytes_at asegs m p2 b2
/\ chk_ok m p1 (Z.of_nat (length b1)) /\ chk_ok m p2 (Z.of_nat (length b1))
/\ m2s_cells m /\ icells m /\ icells_cmp m /\ mem_inv asegs m.

Definition cmpfn_stmt (fn K : Z) : Prop :=
forall (p1 p2 : Z) (b1 b2 : list byte) (lo : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 (Z.of_nat (length b1)) ->
cmp_pre sp p1 p2 b1 b2 K lo m ->
evt asegs (cmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc b1 b2 K lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 fn) fc None m (seg_rom asegs)).

Definition commonfn_stmt (fn K : Z) : Prop :=
forall (p1 p2 : Z) (b1 b2 : list byte) (lo : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
a1 = Z_to_bv 64 fn -> a2 = Z_to_bv 64 p1 -> a3 = Z_to_bv 64 p2 -> a4 = Z_to_bv 64 (Z.of_nat (length b1)) ->
cmp_pre sp p1 p2 b1 b2 K lo m ->
evt asegs (cmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc b1 b2 K lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x579b4) fc None m (seg_rom asegs)).

Lemma cells_off_stack : forall (W : list (Z * Z)) (m m' : mem), munch W m m' -> wmono asegs m m' ->
(forall x, x < 0x652000 -> outside W x) ->
(m2s_cells m -> m2s_cells m') /\ (icells m -> icells m') /\ (icells_cmp m -> icells_cmp m').
Proof.
intros W m m' MU WM OFF.
assert (RO : forall a cs, ro_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= 0x652000 -> ro_cells asegs m' a cs).
{ intros a cs H B. apply (ro_cells_agree asegs m m' a cs H). apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply OFF. lia. }
assert (RW : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= 0x652000 -> rw_cells asegs m' a cs).
{ intros a cs H B. apply (rw_cells_agree asegs m m' a cs H); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply OFF. lia. }
split; [| split].
- intros (M1 & M2 & M3). split; [| split]; apply RW; try assumption; cbn; lia.
- intros (G2 & G1 & RM & SHC & RI). split; [| split; [| split; [| split]]]; apply RO; try assumption; cbn; lia.
- intros (GCF & GRE & AI & FL). split; [| split; [| split]]; [apply RO | apply RO | apply RW | apply RO]; try assumption; cbn; lia.
Qed.

Local Ltac common_tail :=
let ST4 := fresh "ST4" in
lazymatch goal with H : stk asegs _ _ (bv_unsigned (Z_to_bv 64 (?u + -2192))) |- _ =>
rewrite (unsigned_lit (u + -2192)) in H by lia; rename H into ST4 end;
do 25 lstep;
lazymatch goal with FR : rw_cells asegs _ (?u + -2192) [CB 2088 _], FRs : rw_cells asegs _ (?u + -104) _ |- _ =>
release_frame FR ST4 (u + -104); release_frame FRs ST4 u end;
lstep;
unfold cmp_post; sys_finish;
[ lazymatch goal with MU : munch _ _ _ |- munch _ _ _ => rewrite (unsigned_lit _) by lia; eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia end
| rewrite (unsigned_lit _) by lia; assumption ].

Section Common.
Hypothesis RIP : rip_stmt.
Variables (fn K : Z).
Hypothesis FN : fn = 0xe8e50 \/ fn = 0xe8d80.
Hypothesis K0 : 0 <= K.
Hypothesis REAL : cmpfn_stmt fn K.

Theorem memcmpc_spec : commonfn_stmt fn (K + MEMCMPC_DEPTH).
Proof using RIP FN K0 REAL.
unfold commonfn_stmt. intros until m.
intros -> -> -> -> (LEN & NPOS & ST & LO & LOLO & SPH & P1 & P2 & H1 & H2 & SEP1 & SEP2 & BY1 & BY2 & CS1 & CS2 & M2S & IC & ICC & MI).
unfold kHighShadowEnd in *.
set (n := Z.of_nat (length b1)) in *.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
pose proof (munch_refl [(usp - (K + 2272), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (BY10 : keep (bytes_at asegs m p1 b1)) by exact BY1. clear BY1.
assert (BY20 : keep (bytes_at asegs m p2 b2)) by exact BY2. clear BY2.

assert (OFF : forall m', munch [(usp - (K + 2272), usp)] m m' -> wmono asegs m m' ->
chk_ok m' p1 n /\ chk_ok m' p2 n /\ m2s_cells m' /\ icells m' /\ icells_cmp m' /\ bytes_at asegs m' p1 b1 /\ bytes_at asegs m' p2 b2).
{ intros m' MU' WM'.
destruct (cells_off_stack _ m m' MU' WM' ltac:(intros x Hx; cbn [outside]; split; [lia| exact I])) as (T1 & T2 & T3).
split; [apply (chk_ok_agree m m' p1 n CS1 ltac:(lia) H1); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [apply (chk_ok_agree m m' p2 n CS2 ltac:(lia) H2); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [exact (T1 M2S)|]. split; [exact (T2 IC)|]. split; [exact (T3 ICC)|].
split; [unfold keep in BY10; apply (bytes_at_agree asegs m m' _ _ BY10) | unfold keep in BY20; apply (bytes_at_agree asegs m m' _ _ BY20)];
apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; rewrite <- ?LEN in Hx; fold n in Hx; (split; [lia| exact I]). }
call (memcmpc_prologue usp p1 p2 n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact ICC| exact MI|].
rename PC into FRs. rename PC0 into FR. rename POST into ST1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MU WM) as (C1 & C2 & M2S1 & IC1 & ICC1 & _ & _) end.
call (memcmpc_r1 RIP usp p1 p2 n); [exact ST1| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
| exact C1| exact M2S1| exact IC1| assumption|].
lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST2 end.
clear C1 C2 M2S1 IC1 ICC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MU WM) as (C1 & C2 & M2S1 & IC1 & ICC1 & _ & _) end.
call (memcmpc_r2 RIP usp p1 p2 n); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
| exact C2| exact M2S1| exact IC1| assumption|].
lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST3 end.
clear C1 C2 M2S1 IC1 ICC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MU WM) as (C1 & C2 & M2S1 & IC1 & ICC1 & BY1 & BY2) end.
assert (EU2192 : bv_unsigned (Z_to_bv 64 (usp + -2192)) = usp + -2192) by (apply unsigned_lit; lia).
do 3 lstep.
assert (PRE : forall mm, munch [(usp - (K + 2272), usp)] m mm -> wmono asegs m mm -> mem_inv asegs mm -> stk asegs mm lo (usp + -2192) ->
cmp_pre (Z_to_bv 64 (usp + -2192)) p1 p2 b1 b2 K lo mm).
{ intros mm MUm WMm MIm STm. destruct (OFF mm MUm WMm) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
unfold cmp_pre. rewrite EU2192. fold n.
split; [exact LEN|]. split; [exact NPOS|]. split; [exact STm|]. split; [lia|]. split; [unfold kHighShadowEnd; lia|]. split; [lia|].
split; [exact P1|]. split; [exact P2|]. split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact D6|]. split; [exact D7|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5| exact MIm]. }
pose proof REAL as REAL'.
destruct FN as [EF|EF]; rewrite EF in REAL' |- *; clear EF.
- lstep.
call (REAL' p1 p2 b1 b2 lo); [reflexivity | reflexivity | reflexivity | apply PRE; assumption |].
common_tail.
- lstep.
call (REAL' p1 p2 b1 b2 lo); [reflexivity | reflexivity | reflexivity | apply PRE; assumption |].
common_tail.
Qed.
End Common.
