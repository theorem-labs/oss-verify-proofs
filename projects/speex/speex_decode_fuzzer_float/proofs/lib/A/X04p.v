(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X03z X04v X0jg X00b.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X04r X04t X04l X04u X04q X04m X04n X04o.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X0ux X0vt X19x X0ra.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0vp X0vr X0vj X0vs X0vo X0vk X0vl X0vm.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vs OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition L_NOTIFY1 : list Z := [110; 111; 116; 105; 102; 105; 99; 97; 116; 105; 111; 110; 58; 32].
Definition L_WARN1 : list Z := [119; 97; 114; 110; 105; 110; 103; 58; 32].
Definition F_NOTIFY : list Z := L_NOTIFY1 ++ [37; 115; 10].
Definition F_WARN : list Z := L_WARN1 ++ [37; 115; 10].
Definition NOTIFY_FMTS : list Z := [0x23580; 0x23860; 0x23ee0; 0x272c0].

Lemma cstr_f_notify : forall A, In A NOTIFY_FMTS -> forall m, mem_inv bsegs m -> cstr_at m A (zb8 F_NOTIFY).
Proof. intros A HA. unfold NOTIFY_FMTS in HA. destruct HA as [<-|[<-|[<-|[<-|[]]]]]; cstr_tac. Qed.
Lemma cstr_f_warn : forall m, mem_inv bsegs m -> cstr_at m 0x235c0 (zb8 F_WARN). Proof. cstr_tac. Qed.

Definition F_WARNINT : list Z := L_WARN1 ++ [37; 115; 32; 37; 100; 10].
Definition WARNINT_FMTS : list Z := [0x23640; 0x23e60; 0x26de0; 0x272a0].
Lemma cstr_f_warnint : forall A, In A WARNINT_FMTS -> forall m, mem_inv bsegs m -> cstr_at m A (zb8 F_WARNINT).
Proof. intros A HA. unfold WARNINT_FMTS in HA. destruct HA as [<-|[<-|[<-|[<-|[]]]]]; cstr_tac. Qed.

Lemma bytes_at_sub' : forall m A (bs : list byte) i k, bytes_at bsegs m A bs -> (i + k <= length bs)%nat ->
bytes_at bsegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
intros m A bs i k H Hik. rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H. destruct H as [_ H].
rewrite firstn_length, Nat.min_l in H by lia.
rewrite <- (firstn_skipn k (skipn i bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma fmt_sd_pieces : forall m A l1, cstr_at m A (zb8 (l1 ++ [37; 115; 32; 37; 100; 10])) ->
bytes_at bsegs m A (zb8 l1) /\ bytes_at bsegs m (A + Z.of_nat (length l1)) (zb8 [37; 115; 32])
/\ bytes_at bsegs m (A + Z.of_nat (length l1) + 2) (zb8 [32]) /\ bytes_at bsegs m (A + Z.of_nat (length l1) + 3) (zb8 [37; 100; 10])
/\ bytes_at bsegs m (A + Z.of_nat (length l1) + 5) (zb8 [10]) /\ bytes_at bsegs m (A + Z.of_nat (length l1) + 6) [z8].
Proof.
intros m A l1 (BY & _). rewrite zb8_app in BY. rewrite <- app_assoc in BY.
apply (proj1 (bytes_at_app bsegs m A _ _)) in BY. destruct BY as [B1 BY]. rewrite length_zb8 in BY.
split; [exact B1|]. cbn [zb8 map app] in BY |- *.
pose proof (bytes_at_sub' m _ _ 0 3 BY ltac:(cbn; lia)) as P2. pose proof (bytes_at_sub' m _ _ 2 1 BY ltac:(cbn; lia)) as P3.
pose proof (bytes_at_sub' m _ _ 3 3 BY ltac:(cbn; lia)) as P4. pose proof (bytes_at_sub' m _ _ 5 1 BY ltac:(cbn; lia)) as P5.
pose proof (bytes_at_sub' m _ _ 6 1 BY ltac:(cbn; lia)) as P6.
cbn [firstn skipn] in P2, P3, P4, P5, P6. change (Z.of_nat 0) with 0 in P2. change (Z.of_nat 2) with 2 in P3. change (Z.of_nat 3) with 3 in P4.
change (Z.of_nat 5) with 5 in P5. change (Z.of_nat 6) with 6 in P6. rewrite Z.add_0_r in P2.
split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5 | exact P6].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Ltac fstr_inst_spx A l1 CSTR :=
intros until lo; intros E1 E2 SLOT QAP APH CSS S0 SSEP SH CHKS ST LO LOLO SPH S16 CHK PCX MI;
eapply (pcom_fstr_spec RIP A l1 10 []);
[ exact E1 | exact E2 | reflexivity | reflexivity | apply CSTR; exact MI
| unfold kHighShadowEnd in LOLO; cbn [length Z.of_nat L_NOTIFY1 L_WARN1]; lia
| exact SLOT | exact QAP | exact APH | exact CSS | exact S0 | exact SSEP | exact SH | exact CHKS
| exact ST | exact LO | exact LOLO | exact SPH | exact S16 | exact CHK | exact PCX | exact MI ].

Lemma pcom_notify_spec : forall A, In A NOTIFY_FMTS ->
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (ap S : Z) (str : list byte) (lo : Z),
a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
ro_cells bsegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 8 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
bv_unsigned sp mod 16 = 0 -> chk_ok m A 18 -> pctx m -> mem_inv bsegs m ->
evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x59658) fc None m (seg_rom bsegs)).
Proof using RIP.
intros A HA. assert (HR : 0 <= A < 2^20) by (unfold NOTIFY_FMTS in HA; destruct HA as [<-|[<-|[<-|[<-|[]]]]]; lia).
fstr_inst_spx A L_NOTIFY1 (cstr_f_notify A HA).
Qed.

Lemma pcom_warn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (ap S : Z) (str : list byte) (lo : Z),
a1 = Z_to_bv 64 0x235c0 -> a2 = Z_to_bv 64 ap ->
ro_cells bsegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 8 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
bv_unsigned sp mod 16 = 0 -> chk_ok m 0x235c0 13 -> pctx m -> mem_inv bsegs m ->
evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x59658) fc None m (seg_rom bsegs)).
Proof using RIP. fstr_inst_spx 0x235c0 L_WARN1 cstr_f_warn. Qed.

Local Ltac tr_below B MU := apply (bytes_at_agree bsegs _ _ _ _ B); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
cbn [outside]; rewrite ?length_zb8, ?length_app in Hx; cbn [length zb8 map] in Hx; lia.
Local Ltac str_facts m MU SLOT CSS CHKS PCX SLOT1 CS1 CHK1 PCX1 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (SLOT1 : ro_cells bsegs mm _ _) by
(apply (ro_cells_agree bsegs m mm _ _ SLOT); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside cells_size csize Nat.add] in *; lia);
assert (CS1 : cstr_at mm _ _) by
(apply (cstr_agree m mm _ _ CSS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia);
assert (CHK1 : chk_ok mm _ _) by
(eapply chk_ok_agree; [exact CHKS | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
assert (PCX1 : pctx mm) by
(apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.

Lemma pcom_fstrint_spec : forall (A : Z) (l1 : list Z) (ap S : Z) (str : list byte) (lo : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap -> txt_ok l1 = true ->
cstr_at m A (zb8 (l1 ++ [37; 115; 32; 37; 100; 10])) -> A + Z.of_nat (length l1) + 8 <= lo ->
ro_cells bsegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 16 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
bv_unsigned sp mod 16 = 0 ->
chk_ok m A (Z.of_nat (length l1) + 7) -> pctx m -> mem_inv bsegs m ->
evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x59658) fc None m (seg_rom bsegs)).
Proof using RIP.
intros until m. intros -> -> OK1 CS AB SLOT QAP APH CSS S0 SSEP SH CHKS ST LO LOLO SPH S16 CHK PCX MI.
set (q := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
unfold kHighShadowEnd in LOLO.
pose proof (cstr_bound _ _ _ CS) as (A0 & _).
pose proof (fmt_sd_pieces m A l1 CS) as PP.
pose proof (conj SLOT I) as SLOTb. clear SLOT.
pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (LF : Z.of_nat (length (zb8 (l1 ++ [37; 115; 32; 37; 100; 10]))) = Z.of_nat (length l1) + 6).
{ rewrite length_zb8, !length_app. cbn [length]. lia. }
call (pcom_head_spec RIP q A ap (zb8 (l1 ++ [37; 115; 32; 37; 100; 10])) lo);
[ reflexivity | reflexivity | reflexivity | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | exact S16
| exact CS | rewrite length_zb8, !length_app; cbn [length]; lia | rewrite LF; lia | rewrite LF; replace (Z.of_nat (length l1) + 6 + 1) with (Z.of_nat (length l1) + 7) by lia; exact CHK
| exact PCX | exact MI | ].
destruct PC1 as (jb & FRb). destruct PC2 as (jd & DIR). destruct POST as (ja & FRa). rename PC into ST, PC0 into FRh.
call (pcom_setup_spec q jd); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR | exact S16 | lia | assumption | ].
eapply evt_cut; [eapply (pcom_scan_spec l1 A); [reflexivity | reflexivity | exact OK1 | tr_below (proj1 PP) MU | assumption] |].
intros msa (xa0 & ->).
str_facts m MU (proj1 SLOTb) CSS CHKS PCX SLOT1 CS1 CHK1 PCX1.
call (pcom_dstr_spec RIP q (A + Z.of_nat (length l1)) ap 32 S str lo);
[ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | lia | tr_below (proj1 (proj2 PP)) MU | assumption | exact SLOT1 | lia | lia
| exact CS1 | exact S0 | lia | exact SH | exact CHK1 | exact PCX1 | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | lia
| assumption | ].
lazymatch goal with H : exists junk, rw_cells bsegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd2 & DIR2) end.
call (pcom_setup_spec q jd2); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR2 | exact S16 | lia | assumption | ].
eapply evt_cut; [eapply (pcom_scan_spec [32] (A + Z.of_nat (length l1) + 2)); [reflexivity | reflexivity | reflexivity
| tr_below (proj1 (proj2 (proj2 PP))) MU | assumption] |].
intros msb (xb0 & ->). replace (A + Z.of_nat (length l1) + 2 + Z.of_nat (length [32])) with (A + Z.of_nat (length l1) + 3) by (cbn; lia).
call (pcom_dint_spec q (A + Z.of_nat (length l1) + 3) (ap + 8) 100 10 lo);
[ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | left; reflexivity | lia | tr_below (proj1 (proj2 (proj2 (proj2 PP)))) MU | assumption | assumption | lia | lia | lia | lia | assumption | ].
lazymatch goal with H : exists junk, rw_cells bsegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd3 & DIR3) end.
call (pcom_setup_spec q jd3); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR3 | exact S16 | lia | assumption | ].
eapply evt_cut; [eapply (pcom_scan_spec [10] (A + Z.of_nat (length l1) + 3 + 2)); [reflexivity | reflexivity | reflexivity
| replace (A + Z.of_nat (length l1) + 3 + 2) with (A + Z.of_nat (length l1) + 5) by lia; tr_below (proj1 (proj2 (proj2 (proj2 (proj2 PP))))) MU | assumption] |].
intros msc (xc0 & ->).
lazymatch goal with H : rw_cells bsegs _ (q + -2216) DIR0 |- _ => rename H into DIR4 end.
call (pcom_end_spec q (A + Z.of_nat (length l1) + 3 + 2 + Z.of_nat (length [10])) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
[ reflexivity | reflexivity | reflexivity | reflexivity
| replace (A + Z.of_nat (length l1) + 3 + 2 + Z.of_nat (length [10])) with (A + Z.of_nat (length l1) + 6) by (cbn; lia); tr_below (proj2 (proj2 (proj2 (proj2 (proj2 PP))))) MU
| eapply (cells_byte _ _ _ 36%nat z8); [exact DIR4 | reflexivity | lia] | exact FRh | lia | assumption | ].
release_frame FRa PC (q + -2216). unfold DIR0 in DIR4. release_frame DIR4 PC (q + -2176). release_frame FRb PC (q + -104).
unfold pcom_saved in FRh. release_frame FRh PC q.
apply evt_done. unfold pcom_post. rewrite (unsigned_lit q) by lia. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact PC].
Qed.

End WithRIP.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition L_NOTIFY1 : list Z := [110; 111; 116; 105; 102; 105; 99; 97; 116; 105; 111; 110; 58; 32].
Definition L_WARN1 : list Z := [119; 97; 114; 110; 105; 110; 103; 58; 32].
Definition F_NOTIFY : list Z := L_NOTIFY1 ++ [37; 115; 10].
Definition F_WARN : list Z := L_WARN1 ++ [37; 115; 10].
Definition NOTIFY_FMTS : list Z := [0x23540; 0x23820; 0x23ec0; 0x272c0].

Lemma cstr_f_notify : forall A, In A NOTIFY_FMTS -> forall m, mem_inv asegs m -> cstr_at m A (zb8 F_NOTIFY).
Proof. intros A HA. unfold NOTIFY_FMTS in HA. destruct HA as [<-|[<-|[<-|[<-|[]]]]]; cstr_tac. Qed.
Lemma cstr_f_warn : forall m, mem_inv asegs m -> cstr_at m 0x23580 (zb8 F_WARN). Proof. cstr_tac. Qed.

Definition F_WARNINT : list Z := L_WARN1 ++ [37; 115; 32; 37; 100; 10].
Definition WARNINT_FMTS : list Z := [0x23600; 0x23e40; 0x26de0; 0x272a0].
Lemma cstr_f_warnint : forall A, In A WARNINT_FMTS -> forall m, mem_inv asegs m -> cstr_at m A (zb8 F_WARNINT).
Proof. intros A HA. unfold WARNINT_FMTS in HA. destruct HA as [<-|[<-|[<-|[<-|[]]]]]; cstr_tac. Qed.

Lemma bytes_at_sub' : forall m A (bs : list byte) i k, bytes_at asegs m A bs -> (i + k <= length bs)%nat ->
bytes_at asegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
intros m A bs i k H Hik. rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H. destruct H as [_ H].
rewrite firstn_length, Nat.min_l in H by lia.
rewrite <- (firstn_skipn k (skipn i bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma fmt_sd_pieces : forall m A l1, cstr_at m A (zb8 (l1 ++ [37; 115; 32; 37; 100; 10])) ->
bytes_at asegs m A (zb8 l1) /\ bytes_at asegs m (A + Z.of_nat (length l1)) (zb8 [37; 115; 32])
/\ bytes_at asegs m (A + Z.of_nat (length l1) + 2) (zb8 [32]) /\ bytes_at asegs m (A + Z.of_nat (length l1) + 3) (zb8 [37; 100; 10])
/\ bytes_at asegs m (A + Z.of_nat (length l1) + 5) (zb8 [10]) /\ bytes_at asegs m (A + Z.of_nat (length l1) + 6) [z8].
Proof.
intros m A l1 (BY & _). rewrite zb8_app in BY. rewrite <- app_assoc in BY.
apply (proj1 (bytes_at_app asegs m A _ _)) in BY. destruct BY as [B1 BY]. rewrite length_zb8 in BY.
split; [exact B1|]. cbn [zb8 map app] in BY |- *.
pose proof (bytes_at_sub' m _ _ 0 3 BY ltac:(cbn; lia)) as P2. pose proof (bytes_at_sub' m _ _ 2 1 BY ltac:(cbn; lia)) as P3.
pose proof (bytes_at_sub' m _ _ 3 3 BY ltac:(cbn; lia)) as P4. pose proof (bytes_at_sub' m _ _ 5 1 BY ltac:(cbn; lia)) as P5.
pose proof (bytes_at_sub' m _ _ 6 1 BY ltac:(cbn; lia)) as P6.
cbn [firstn skipn] in P2, P3, P4, P5, P6. change (Z.of_nat 0) with 0 in P2. change (Z.of_nat 2) with 2 in P3. change (Z.of_nat 3) with 3 in P4.
change (Z.of_nat 5) with 5 in P5. change (Z.of_nat 6) with 6 in P6. rewrite Z.add_0_r in P2.
split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5 | exact P6].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Ltac fstr_inst_spx A l1 CSTR :=
intros until lo; intros E1 E2 SLOT QAP APH CSS S0 SSEP SH CHKS ST LO LOLO SPH S16 CHK PCX MI;
eapply (pcom_fstr_spec RIP A l1 10 []);
[ exact E1 | exact E2 | reflexivity | reflexivity | apply CSTR; exact MI
| unfold kHighShadowEnd in LOLO; cbn [length Z.of_nat L_NOTIFY1 L_WARN1]; lia
| exact SLOT | exact QAP | exact APH | exact CSS | exact S0 | exact SSEP | exact SH | exact CHKS
| exact ST | exact LO | exact LOLO | exact SPH | exact S16 | exact CHK | exact PCX | exact MI ].

Lemma pcom_notify_spec : forall A, In A NOTIFY_FMTS ->
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (ap S : Z) (str : list byte) (lo : Z),
a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
ro_cells asegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 8 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
bv_unsigned sp mod 16 = 0 -> chk_ok m A 18 -> pctx m -> mem_inv asegs m ->
evt asegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5956c) fc None m (seg_rom asegs)).
Proof using RIP.
intros A HA. assert (HR : 0 <= A < 2^20) by (unfold NOTIFY_FMTS in HA; destruct HA as [<-|[<-|[<-|[<-|[]]]]]; lia).
fstr_inst_spx A L_NOTIFY1 (cstr_f_notify A HA).
Qed.

Lemma pcom_warn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (ap S : Z) (str : list byte) (lo : Z),
a1 = Z_to_bv 64 0x23580 -> a2 = Z_to_bv 64 ap ->
ro_cells asegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 8 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
bv_unsigned sp mod 16 = 0 -> chk_ok m 0x23580 13 -> pctx m -> mem_inv asegs m ->
evt asegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5956c) fc None m (seg_rom asegs)).
Proof using RIP. fstr_inst_spx 0x23580 L_WARN1 cstr_f_warn. Qed.

Local Ltac tr_below B MU := apply (bytes_at_agree asegs _ _ _ _ B); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
cbn [outside]; rewrite ?length_zb8, ?length_app in Hx; cbn [length zb8 map] in Hx; lia.
Local Ltac str_facts m MU SLOT CSS CHKS PCX SLOT1 CS1 CHK1 PCX1 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (SLOT1 : ro_cells asegs mm _ _) by
(apply (ro_cells_agree asegs m mm _ _ SLOT); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside cells_size csize Nat.add] in *; lia);
assert (CS1 : cstr_at mm _ _) by
(apply (cstr_agree m mm _ _ CSS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia);
assert (CHK1 : chk_ok mm _ _) by
(eapply chk_ok_agree; [exact CHKS | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
assert (PCX1 : pctx mm) by
(apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.

Lemma pcom_fstrint_spec : forall (A : Z) (l1 : list Z) (ap S : Z) (str : list byte) (lo : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap -> txt_ok l1 = true ->
cstr_at m A (zb8 (l1 ++ [37; 115; 32; 37; 100; 10])) -> A + Z.of_nat (length l1) + 8 <= lo ->
ro_cells asegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 16 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
bv_unsigned sp mod 16 = 0 ->
chk_ok m A (Z.of_nat (length l1) + 7) -> pctx m -> mem_inv asegs m ->
evt asegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5956c) fc None m (seg_rom asegs)).
Proof using RIP.
intros until m. intros -> -> OK1 CS AB SLOT QAP APH CSS S0 SSEP SH CHKS ST LO LOLO SPH S16 CHK PCX MI.
set (q := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
unfold kHighShadowEnd in LOLO.
pose proof (cstr_bound _ _ _ CS) as (A0 & _).
pose proof (fmt_sd_pieces m A l1 CS) as PP.
pose proof (conj SLOT I) as SLOTb. clear SLOT.
pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (LF : Z.of_nat (length (zb8 (l1 ++ [37; 115; 32; 37; 100; 10]))) = Z.of_nat (length l1) + 6).
{ rewrite length_zb8, !length_app. cbn [length]. lia. }
call (pcom_head_spec RIP q A ap (zb8 (l1 ++ [37; 115; 32; 37; 100; 10])) lo);
[ reflexivity | reflexivity | reflexivity | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | exact S16
| exact CS | rewrite length_zb8, !length_app; cbn [length]; lia | rewrite LF; lia | rewrite LF; replace (Z.of_nat (length l1) + 6 + 1) with (Z.of_nat (length l1) + 7) by lia; exact CHK
| exact PCX | exact MI | ].
destruct PC1 as (jb & FRb). destruct PC2 as (jd & DIR). destruct POST as (ja & FRa). rename PC into ST, PC0 into FRh.
call (pcom_setup_spec q jd); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR | exact S16 | lia | assumption | ].
eapply evt_cut; [eapply (pcom_scan_spec l1 A); [reflexivity | reflexivity | exact OK1 | tr_below (proj1 PP) MU | assumption] |].
intros msa (xa0 & ->).
str_facts m MU (proj1 SLOTb) CSS CHKS PCX SLOT1 CS1 CHK1 PCX1.
call (pcom_dstr_spec RIP q (A + Z.of_nat (length l1)) ap 32 S str lo);
[ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | lia | tr_below (proj1 (proj2 PP)) MU | assumption | exact SLOT1 | lia | lia
| exact CS1 | exact S0 | lia | exact SH | exact CHK1 | exact PCX1 | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | lia
| assumption | ].
lazymatch goal with H : exists junk, rw_cells asegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd2 & DIR2) end.
call (pcom_setup_spec q jd2); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR2 | exact S16 | lia | assumption | ].
eapply evt_cut; [eapply (pcom_scan_spec [32] (A + Z.of_nat (length l1) + 2)); [reflexivity | reflexivity | reflexivity
| tr_below (proj1 (proj2 (proj2 PP))) MU | assumption] |].
intros msb (xb0 & ->). replace (A + Z.of_nat (length l1) + 2 + Z.of_nat (length [32])) with (A + Z.of_nat (length l1) + 3) by (cbn; lia).
call (pcom_dint_spec q (A + Z.of_nat (length l1) + 3) (ap + 8) 100 10 lo);
[ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | left; reflexivity | lia | tr_below (proj1 (proj2 (proj2 (proj2 PP)))) MU | assumption | assumption | lia | lia | lia | lia | assumption | ].
lazymatch goal with H : exists junk, rw_cells asegs _ (q + -2216) [CB 40 junk] |- _ => destruct H as (jd3 & DIR3) end.
call (pcom_setup_spec q jd3); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR3 | exact S16 | lia | assumption | ].
eapply evt_cut; [eapply (pcom_scan_spec [10] (A + Z.of_nat (length l1) + 3 + 2)); [reflexivity | reflexivity | reflexivity
| replace (A + Z.of_nat (length l1) + 3 + 2) with (A + Z.of_nat (length l1) + 5) by lia; tr_below (proj1 (proj2 (proj2 (proj2 (proj2 PP))))) MU | assumption] |].
intros msc (xc0 & ->).
lazymatch goal with H : rw_cells asegs _ (q + -2216) DIR0 |- _ => rename H into DIR4 end.
call (pcom_end_spec q (A + Z.of_nat (length l1) + 3 + 2 + Z.of_nat (length [10])) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
[ reflexivity | reflexivity | reflexivity | reflexivity
| replace (A + Z.of_nat (length l1) + 3 + 2 + Z.of_nat (length [10])) with (A + Z.of_nat (length l1) + 6) by (cbn; lia); tr_below (proj2 (proj2 (proj2 (proj2 (proj2 PP))))) MU
| eapply (cells_byte _ _ _ 36%nat z8); [exact DIR4 | reflexivity | lia] | exact FRh | lia | assumption | ].
release_frame FRa PC (q + -2216). unfold DIR0 in DIR4. release_frame DIR4 PC (q + -2176). release_frame FRb PC (q + -104).
unfold pcom_saved in FRh. release_frame FRh PC q.
apply evt_done. unfold pcom_post. rewrite (unsigned_lit q) by lia. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact PC].
Qed.

End WithRIP.
