(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cq X1d0 X1cl X1dh X1cs X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X04b.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X03z X04v X0ec X001 X00b X000 X058
X04g X04k X04c X053 X04w X048 X03w X03v X04j X04i X04e X04d X03y.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0v9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X0ux X0vt X14x X0r0 X0ra X0qz X0ve X0vi X0va X0w1 X0vu X0v6 X0uu X0ut X0vh X0vg X0vc X0vb X0uw.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X058.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ve OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vi OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0va OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ut OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section LiftSpx.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem asan_memmove_lift : memmove_icontract RT e_asan_memmove.
Proof using AF RIP AF_IC AF_SHW.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo
FDO MST -> -> -> D0 S0 NB BS CSRC CDST ART0 MI0 CALL.
intros T c Hc Hk.
set (n := Z.of_nat (length bs)) in *.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (AF_IC Σ m ART0) as (IC & _ & _ & _ & M2S).
destruct CSRC as (CS & SEPS). destruct CDST as (CD & DCL & DWR).
assert (CHS : chk_ok m s n) by (apply (chk_ok_of RT AF_SHW Σ m s n ART0); [lia| exact CS]).
assert (CHD : chk_ok m d n) by (apply (chk_ok_of RT AF_SHW Σ m d n ART0); [lia| exact CD]).
destruct (wr_at_rw_CB m d n DWR ltac:(lia)) as (junk & DST).
unfold n in DST. rewrite Nat2Z.id in DST.
assert (SEPD : n = 0 \/ d + n <= lo \/ usp <= d).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right].
destruct (range_side d n lo usp); [| ul| lia| right; lia| left; lia].
intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
assert (RS : n = 0 \/ s + n <= 2^47).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (RD : n = 0 \/ d + n <= 2^47).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (W1 : evt bsegs (amemmove_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d bs lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memmove m)).
{ unfold entry_st, e_asan_memmove. rewrite ESP.
apply (amemmove_spec RIP) with (s := s) (junk := junk); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul;
try assumption. }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
unfold amemmove_post in PO.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
rewrite (unsigned_lit usp) in MU, ST' by ul.
destruct (icpt_after RT AF Σ m m' usp lo _ d n ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
{ intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
{ intros i Hi. apply DCL. exact Hi. }
exists m'. split; [rewrite ESP; do 14 eexists; reflexivity|].
split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
split; [exact PRES|].
destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

Theorem memmove_lift : memmove_icontract RT e_memmove.
Proof using AF RIP AF_IC AF_SHW.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo
FDO MST -> -> -> D0 S0 NB BS CSRC CDST ART0 MI0 CALL.
intros T c Hc Hk.
set (n := Z.of_nat (length bs)) in *.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (AF_IC Σ m ART0) as (IC & _ & _ & _ & M2S).
destruct CSRC as (CS & SEPS). destruct CDST as (CD & DCL & DWR).
assert (CHS : chk_ok m s n) by (apply (chk_ok_of RT AF_SHW Σ m s n ART0); [lia| exact CS]).
assert (CHD : chk_ok m d n) by (apply (chk_ok_of RT AF_SHW Σ m d n ART0); [lia| exact CD]).
destruct (wr_at_rw_CB m d n DWR ltac:(lia)) as (junk & DST).
unfold n in DST. rewrite Nat2Z.id in DST.
assert (SEPD : n = 0 \/ d + n <= lo \/ usp <= d).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right].
destruct (range_side d n lo usp); [| ul| lia| right; lia| left; lia].
intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
assert (RS : n = 0 \/ s + n <= 2^47).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (RD : n = 0 \/ d + n <= 2^47).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (W1 : evt bsegs (memmove_ipost ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d bs lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memmove m)).
{ unfold entry_st, e_memmove. rewrite ESP.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
lstep.
apply (memmove_ispec RIP) with (s := s) (junk := junk); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul;
try assumption. }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
unfold memmove_ipost in PO.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
rewrite (unsigned_lit usp) in MU, ST' by ul.
destruct (icpt_after RT AF Σ m m' usp lo _ d n ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
{ intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
{ intros i Hi. apply DCL. exact Hi. }
exists m'. split; [rewrite ESP; do 14 eexists; reflexivity|].
split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
split; [exact PRES|].
destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

Hypothesis AF_CMP : forall Σ m, ART RT Σ m -> icells_cmp m.

Theorem bcmp_lift : bcmp_icontract RT.
Proof using AF RIP AF_IC AF_SHW AF_CMP.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 b1 b2 lo
FDO MST -> -> -> LEN NB P1 P2 BY1 BY2 CSRC1 CSRC2 ART0 MI0 CALL.
intros T c Hc Hk.
set (n := Z.of_nat (length b1)) in *.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (AF_IC Σ m ART0) as (IC & _ & _ & _ & M2S).
pose proof (AF_CMP Σ m ART0) as ICC.
destruct CSRC1 as (CS1 & SEP1). destruct CSRC2 as (CS2 & SEP2).
assert (CH1 : chk_ok m p1 n) by (apply (chk_ok_of RT AF_SHW Σ m p1 n ART0); [lia| exact CS1]).
assert (CH2 : chk_ok m p2 n) by (apply (chk_ok_of RT AF_SHW Σ m p2 n ART0); [lia| exact CS2]).
assert (R1 : p1 + n <= 2^47).
{ destruct CH1 as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (R2 : p2 + n <= 2^47).
{ destruct CH2 as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (W1 : evt bsegs (cmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc b1 b2 BCMP_DEPTH lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bcmp m)).
{ unfold entry_st, e_bcmp. rewrite ESP.
apply (bcmp_entry_spec RIP p1 p2 b1 b2 lo); try reflexivity.
unfold cmp_pre. rewrite (unsigned_lit usp) by ul. fold n.
split; [exact LEN|]. split; [lia|]. split; [exact ST|]. split; [ul|]. split; [ul|]. split; [ul|].
split; [lia|]. split; [lia|]. split; [exact R1|]. split; [exact R2|]. split; [exact SEP1|]. split; [exact SEP2|].
split; [exact BY1|]. split; [exact BY2|]. split; [exact CH1|]. split; [exact CH2|]. split; [exact M2S|]. split; [exact IC|]. split; [exact ICC| exact MI0]. }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1.
destruct (ASTA_unpack RT Σ PMc _ c1 Hc1) as (ms1 & PO & Hc2).
unfold cmp_post in PO.
destruct PO as (u0 & u1 & u2 & v & b1' & b2' & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & IFF).
rewrite (unsigned_lit usp) in MU, ST' by ul.
apply Hk. exists v. split; [exact IFF|].
unfold icpt_postF. eapply ASTA_conseq; [exact Hc2|]. intros ms <-.
destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
{ intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
{ intros i Hi. lia. }
exists m'. split; [rewrite ESP; do 14 eexists; reflexivity|].
split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
split; [exact PRES| exact I].
Qed.

End LiftSpx.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section LiftSpx.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem asan_memmove_lift : memmove_icontract RT e_asan_memmove.
Proof using AF RIP AF_IC AF_SHW.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo
FDO MST -> -> -> D0 S0 NB BS CSRC CDST ART0 MI0 CALL.
intros T c Hc Hk.
set (n := Z.of_nat (length bs)) in *.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (AF_IC Σ m ART0) as (IC & _ & _ & _ & M2S).
destruct CSRC as (CS & SEPS). destruct CDST as (CD & DCL & DWR).
assert (CHS : chk_ok m s n) by (apply (chk_ok_of RT AF_SHW Σ m s n ART0); [lia| exact CS]).
assert (CHD : chk_ok m d n) by (apply (chk_ok_of RT AF_SHW Σ m d n ART0); [lia| exact CD]).
destruct (wr_at_rw_CB m d n DWR ltac:(lia)) as (junk & DST).
unfold n in DST. rewrite Nat2Z.id in DST.
assert (SEPD : n = 0 \/ d + n <= lo \/ usp <= d).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right].
destruct (range_side d n lo usp); [| ul| lia| right; lia| left; lia].
intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
assert (RS : n = 0 \/ s + n <= 2^47).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (RD : n = 0 \/ d + n <= 2^47).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (W1 : evt asegs (amemmove_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d bs lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memmove m)).
{ unfold entry_st, e_asan_memmove. rewrite ESP.
apply (amemmove_spec RIP) with (s := s) (junk := junk); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul;
try assumption. }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
unfold amemmove_post in PO.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
rewrite (unsigned_lit usp) in MU, ST' by ul.
destruct (icpt_after RT AF Σ m m' usp lo _ d n ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
{ intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
{ intros i Hi. apply DCL. exact Hi. }
exists m'. split; [rewrite ESP; do 14 eexists; reflexivity|].
split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
split; [exact PRES|].
destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

Theorem memmove_lift : memmove_icontract RT e_memmove.
Proof using AF RIP AF_IC AF_SHW.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo
FDO MST -> -> -> D0 S0 NB BS CSRC CDST ART0 MI0 CALL.
intros T c Hc Hk.
set (n := Z.of_nat (length bs)) in *.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (AF_IC Σ m ART0) as (IC & _ & _ & _ & M2S).
destruct CSRC as (CS & SEPS). destruct CDST as (CD & DCL & DWR).
assert (CHS : chk_ok m s n) by (apply (chk_ok_of RT AF_SHW Σ m s n ART0); [lia| exact CS]).
assert (CHD : chk_ok m d n) by (apply (chk_ok_of RT AF_SHW Σ m d n ART0); [lia| exact CD]).
destruct (wr_at_rw_CB m d n DWR ltac:(lia)) as (junk & DST).
unfold n in DST. rewrite Nat2Z.id in DST.
assert (SEPD : n = 0 \/ d + n <= lo \/ usp <= d).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right].
destruct (range_side d n lo usp); [| ul| lia| right; lia| left; lia].
intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
assert (RS : n = 0 \/ s + n <= 2^47).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (RD : n = 0 \/ d + n <= 2^47).
{ destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CHD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (W1 : evt asegs (memmove_ipost ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d bs lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memmove m)).
{ unfold entry_st, e_memmove. rewrite ESP.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
lstep.
apply (memmove_ispec RIP) with (s := s) (junk := junk); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; try ul;
try assumption. }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
unfold icpt_postF. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
unfold memmove_ipost in PO.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
rewrite (unsigned_lit usp) in MU, ST' by ul.
destruct (icpt_after RT AF Σ m m' usp lo _ d n ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
{ intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
{ intros i Hi. apply DCL. exact Hi. }
exists m'. split; [rewrite ESP; do 14 eexists; reflexivity|].
split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
split; [exact PRES|].
destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

Hypothesis AF_CMP : forall Σ m, ART RT Σ m -> icells_cmp m.

Theorem bcmp_lift : bcmp_icontract RT.
Proof using AF RIP AF_IC AF_SHW AF_CMP.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 b1 b2 lo
FDO MST -> -> -> LEN NB P1 P2 BY1 BY2 CSRC1 CSRC2 ART0 MI0 CALL.
intros T c Hc Hk.
set (n := Z.of_nat (length b1)) in *.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (AF_IC Σ m ART0) as (IC & _ & _ & _ & M2S).
pose proof (AF_CMP Σ m ART0) as ICC.
destruct CSRC1 as (CS1 & SEP1). destruct CSRC2 as (CS2 & SEP2).
assert (CH1 : chk_ok m p1 n) by (apply (chk_ok_of RT AF_SHW Σ m p1 n ART0); [lia| exact CS1]).
assert (CH2 : chk_ok m p2 n) by (apply (chk_ok_of RT AF_SHW Σ m p2 n ART0); [lia| exact CS2]).
assert (R1 : p1 + n <= 2^47).
{ destruct CH1 as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (R2 : p2 + n <= 2^47).
{ destruct CH2 as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
assert (W1 : evt asegs (cmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc b1 b2 BCMP_DEPTH lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bcmp m)).
{ unfold entry_st, e_bcmp. rewrite ESP.
apply (bcmp_entry_spec RIP p1 p2 b1 b2 lo); try reflexivity.
unfold cmp_pre. rewrite (unsigned_lit usp) by ul. fold n.
split; [exact LEN|]. split; [lia|]. split; [exact ST|]. split; [ul|]. split; [ul|]. split; [ul|].
split; [lia|]. split; [lia|]. split; [exact R1|]. split; [exact R2|]. split; [exact SEP1|]. split; [exact SEP2|].
split; [exact BY1|]. split; [exact BY2|]. split; [exact CH1|]. split; [exact CH2|]. split; [exact M2S|]. split; [exact IC|]. split; [exact ICC| exact MI0]. }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1.
destruct (ASTA_unpack RT Σ PMc _ c1 Hc1) as (ms1 & PO & Hc2).
unfold cmp_post in PO.
destruct PO as (u0 & u1 & u2 & v & b1' & b2' & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & IFF).
rewrite (unsigned_lit usp) in MU, ST' by ul.
apply Hk. exists v. split; [exact IFF|].
unfold icpt_postF. eapply ASTA_conseq; [exact Hc2|]. intros ms <-.
destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
{ intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
{ intros i Hi. lia. }
exists m'. split; [rewrite ESP; do 14 eexists; reflexivity|].
split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
split; [exact PRES| exact I].
Qed.

End LiftSpx.
