(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cq X1d0 X1cl X1dh X1cs X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rv X1s9 X1rn X1s6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X00b X000
X01v X01x X03f X03d X0jh X0ji X047 X022 X044 X0jg X0jw X0jt X0jn X0jm.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0ra X0qz X0su X0sw X0ue X0uc X0v5 X0t1 X0v2 X19x X1ab X1a8 X1a2 X1a1.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0su OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sw OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ue OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1ab OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.

Definition so_id (so : stdout_st) : stdout_st := so.
Definition so_set (so : stdout_st) (_ : stdout_st) : stdout_st := so.

Lemma TT_exit_flush : forall (so : stdout_st) (T : TSet),
(so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 -> T [] ->
t_eq (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => T)) (t_emit (evw 1 (so_buf so)) T).
Proof.
intros so T H Hl HT. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
unfold so_id at 1.
destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
- destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
rewrite TT_ebind. cbn [TT]. unfold so_id. unfold stdio_writev.
assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
rewrite (iov_start_cons (so_buf so) [] NE).
eapply t_eq_trans.
{ apply (TT_wv_loop (WV_FUEL [so_buf so; []]) 1 [so_buf so; []] so (fun _ => T)); [cbn; lia| | | exact HT];
unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia. }
cbn [concat]. rewrite app_nil_r. rewrite <- evw_to_bytes. apply t_eq_refl.
- assert (E : so_buf so = []) by (destruct (so_buf so); [reflexivity| cbn in Ge; unfold zlength in Ge; cbn in Ge; lia]).
rewrite E. cbn [TT evw map]. apply t_eq_sym, t_emit_nil_eq. exact HT.
Qed.

Lemma tok_exit_flush : forall (so : stdout_st),
(so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 ->
tok [1] ((stdout_exit_flush so_id so_set : @M stdout_st unit) so).
Proof.
intros so H Hl. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
unfold so_id at 1.
destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
- destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
apply tok_ebind; [| intros x; exact I].
unfold so_id. unfold stdio_writev.
assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
rewrite (iov_start_cons (so_buf so) [] NE).
apply tok_wv_loop; [left; reflexivity| cbn; lia| |]; unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia.
- cbn. exact I.
Qed.

Section XExit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_XIT : forall Σ m, ART RT Σ m -> xit_rt m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma exit_ok_ph : forall (ph : bool) (XEP : mem -> Prop),
(forall m, XEP m -> XENVC m /\ atxA ph m /\ atexit_ph ph m) ->
exit_contract RT XEP OUT_repA ERR_repA.
Proof using AF AF_XIT.
intros ph XEP HXE.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo
Ha0 Hcode Htp Hso HFD OUT ERR XE ART0 MI0 CALL SSP.
intros T c Hc Hk.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite ESP in Hc.
destruct (AF_XIT Σ m ART0) as (FA & GF & GCX & (dso & DSO) & GX & UG1 & UG2 & RG & MUX & SHC & AI & CP & THR & RMS & COV
& SC1 & SC2 & SC3).
destruct (HXE m XE) as (XC & ((p1 & p2 & ATX) & _) & PH).
destruct XC as ((tid & HT & TID) & ATA & EXL & (cdt & thr & sec & tm1 & LIBC) & OFL & SEU & SOU & SIN & SINU
& GDS & (flag & FLGNZ & FLG) & CPL & (os & ODRC)).
pose proof (stk_of_rw_cells bsegs m _ _ ODRC) as ODRS. change (ODR_LO + Z.of_nat (cells_size [CB ODR_N os])) with ODR_HI in ODRS.
destruct SSP as (g & G1 & G2).
assert (LO0 : 0x7fff7f800000 <= lo) by ul.
assert (SOK : (so_first so = false \/ so_buf so = []) /\ zlength (so_buf so) <= 2^26).
{ destruct Hso as [->|(k & Hk5 & ->)].
- split; [right; reflexivity| unfold zlength; cbn; lia].
- split; [left; reflexivity|]. cbn [so_lines so_buf]. rewrite zlength_zeros_out. lia. }

set (Qfin := fun (x : unit * stdout_st) (ms' : machine_state) =>
ms_svc_pending ms' = Some (Z_to_bv 64 94) /\ areg ms' 10 = Z_to_bv 64 code).
assert (IMPL : impl bsegs (at_node bsegs) ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (epost Qfin)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_exit m)).
{ assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
eapply impl_evt.
{ exact (exit_prefix_spec ph ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m lo code tid (Z_to_bv 8 0) p1 p2 cdt thr sec tm1 flag dso Ha0 Htp ltac:(lia) ltac:(rewrite EU; exact ST)
ltac:(rewrite EU; ul) ltac:(lia) TID HT ATX PH ATA EXL LIBC COV FA GF GCX DSO GX CPL FLG FLGNZ (conj UG1 UG2) RG MUX SHC AI CP
THR RMS SC1 SC2 SC3 GDS ODRS MI0). }
intros ms1 PO. unfold exit_prefix_post in PO.
destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1).
rewrite EU in MU1, ST1.
assert (AG1 : agree_on (fun x => (0x658f28 <= x < 0x658f30) \/ (0x659390 <= x < 0x659be8) \/ (0x1007b0 <= x < 0x100aa8)
\/ (0xfce58 <= x < 0xfce60) \/ (0x658cd8 <= x < 0x658ce0)) m m1).
{ apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. ul. }
Local Ltac tr AG1 WM1 H := apply (rw_cells_agree bsegs _ _ _ _ H); [apply (agree_sub _ _ _ _ AG1); intros xa Hxa; cbn in Hxa; lia| exact WM1].
assert (LIBC1 : rw_cells bsegs m1 0x658f28 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]) by tr AG1 WM1 LIBC.
assert (OFL1 : rw_cells bsegs m1 0x659390 [C8 (Z_to_bv 64 0)]) by tr AG1 WM1 OFL.
assert (SINU1 : rw_cells bsegs m1 0x100a78 [C8 (Z_to_bv 64 0x100990)]) by tr AG1 WM1 SINU.
assert (SOU1 : rw_cells bsegs m1 0x100988 [C8 (Z_to_bv 64 0x1008a0)]) by tr AG1 WM1 SOU.
assert (SEU1 : rw_cells bsegs m1 0x100898 [C8 (Z_to_bv 64 0x1007b0)]) by tr AG1 WM1 SEU.
assert (SIN1 : stdin_file m1).
{ destruct SIN as (j0 & j1 & j2 & j3 & j4 & C). exists j0, j1, j2, j3, j4. tr AG1 WM1 C. }
assert (OUT1 : stdout_file m1 so).
{ apply (stdout_file_agree so m m1); [| exact WM1| exact OUT]. apply (agree_sub _ _ _ _ AG1). intros xa Hxa. lia. }
assert (ERR1 : stderr_file m1).
{ apply stderr_wfile0_file. apply (stderr_wfile0_agree m m1); [| exact WM1| exact ERR]. apply (agree_sub _ _ _ _ AG1). intros xa Hxa. lia. }
assert (G11 : ro_cells bsegs m1 0xfce58 [C8 (Z_to_bv 64 0x658cd8)]).
{ apply (ro_cells_agree bsegs m m1 _ _ G1). apply (agree_sub _ _ _ _ AG1). intros xa Hxa. cbn in Hxa. lia. }
assert (G21 : ro_cells bsegs m1 0x658cd8 [C8 g]).
{ apply (ro_cells_agree bsegs m m1 _ _ G2). apply (agree_sub _ _ _ _ AG1). intros xa Hxa. cbn in Hxa. lia. }
assert (EU16 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).
pose proof (stdio_exit_proof so_id so_set (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ => eq_refl)) as SE.
unfold stdio_exit_spec_stmt in SE.
pose proof (SE (Z_to_bv 64 0xe6e4c) (Z_to_bv 64 (usp + -16)) gp tp u0 u1 u2 (Z_to_bv 64 code) s1 b0 b1 b2 b3 b4 b5 b6 b7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 lo so g cdt thr sec tm1
ltac:(rewrite EU16; exact ST1) LIBC1 OFL1 SINU1 SIN1 SOU1 SEU1 OUT1 ERR1 G11 G21 MI1 Htp
ltac:(rewrite EU16; ul) ltac:(ul)) as IM.
clear SE. unfold implM in IM.
rewrite EU.
eapply impl_post_evt''; [exact IM|].
intros [|[xr so']] ms2 H2; [apply evt_done; exact I|].
cbn [epost fst snd] in H2 |- *. unfold stdio_exit_post in H2.
destruct H2 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & so'' & m2 & -> & _ & _ & MI2 & _).
rewrite (ret_pc_even 0xe6e4c) by lia.
eapply evt_mono; [exact (exit_tail_spec (usp + -16) code gp tp v0 v1 v2 s1 c0 c1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
v3 v4 v5 v6 F fc m2 ltac:(lia) ltac:(assumption))|].
intros ms3 (ra3 & ->). split; reflexivity. }

assert (RZ : realizes bsegs c (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => t_emit [] T))).
{ apply (impl_realizes bsegs SEGTOP_A asegs_wx asegs_below [1] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo) Qfin
(fun _ => t_emit [] T)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_exit m) c
(ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact (tok_exit_flush so (proj1 SOK) (proj2 SOK))| exact Hc| exact IMPL|].
- intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
- intros x ms' c' (HS & HA0) Hc'.
assert (R : realizes bsegs c' T).
{ apply Hk.
exists (rt_allow RT Σ), (eq ms'), (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo). split; [exact Hc'|]. split.
+ intros ms <-. split; [right; exact HS| exact HA0].
+ intros mo (_ & _ & HFS). exact HFS. }
eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty bsegs _ _ R). }
eapply rz_conseq; [exact RZ|].
eapply t_eq_trans; [apply TT_exit_flush; [exact (proj1 SOK)| exact (proj2 SOK)| apply t_emit_has_nil]|].
eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.

Theorem exit_ok : exit_contract RT XENVA OUT_repA ERR_repA.
Proof using AF AF_XIT.
apply (exit_ok_ph false). intros m (XC & XA). split; [exact XC|]. split; [exact XA| exact I].
Qed.

Theorem exit_ok1 : exit_contract RT XENVA1x OUT_repA ERR_repA.
Proof using AF AF_XIT.
apply (exit_ok_ph true). intros m ((XC & XA) & FL). split; [exact XC|]. split; [exact XA|].
destruct XA as (_ & PF & PA). exact (conj PF (conj PA FL)).
Qed.

End XExit.

End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.

Definition so_id (so : stdout_st) : stdout_st := so.
Definition so_set (so : stdout_st) (_ : stdout_st) : stdout_st := so.

Lemma TT_exit_flush : forall (so : stdout_st) (T : TSet),
(so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 -> T [] ->
t_eq (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => T)) (t_emit (evw 1 (so_buf so)) T).
Proof.
intros so T H Hl HT. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
unfold so_id at 1.
destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
- destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
rewrite TT_ebind. cbn [TT]. unfold so_id. unfold stdio_writev.
assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
rewrite (iov_start_cons (so_buf so) [] NE).
eapply t_eq_trans.
{ apply (TT_wv_loop (WV_FUEL [so_buf so; []]) 1 [so_buf so; []] so (fun _ => T)); [cbn; lia| | | exact HT];
unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia. }
cbn [concat]. rewrite app_nil_r. rewrite <- evw_to_bytes. apply t_eq_refl.
- assert (E : so_buf so = []) by (destruct (so_buf so); [reflexivity| cbn in Ge; unfold zlength in Ge; cbn in Ge; lia]).
rewrite E. cbn [TT evw map]. apply t_eq_sym, t_emit_nil_eq. exact HT.
Qed.

Lemma tok_exit_flush : forall (so : stdout_st),
(so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 ->
tok [1] ((stdout_exit_flush so_id so_set : @M stdout_st unit) so).
Proof.
intros so H Hl. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
unfold so_id at 1.
destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
- destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
apply tok_ebind; [| intros x; exact I].
unfold so_id. unfold stdio_writev.
assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
rewrite (iov_start_cons (so_buf so) [] NE).
apply tok_wv_loop; [left; reflexivity| cbn; lia| |]; unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia.
- cbn. exact I.
Qed.

Section XExit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_XIT : forall Σ m, ART RT Σ m -> xit_rt m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma exit_ok_ph : forall (ph : bool) (XEP : mem -> Prop),
(forall m, XEP m -> XENVC m /\ atxA ph m /\ atexit_ph ph m) ->
exit_contract RT XEP OUT_repA ERR_repA.
Proof using AF AF_XIT.
intros ph XEP HXE.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo
Ha0 Hcode Htp Hso HFD OUT ERR XE ART0 MI0 CALL SSP.
intros T c Hc Hk.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite ESP in Hc.
destruct (AF_XIT Σ m ART0) as (FA & GF & GCX & (dso & DSO) & GX & UG1 & UG2 & RG & MUX & SHC & AI & CP & THR & RMS & COV
& SC1 & SC2 & SC3).
destruct (HXE m XE) as (XC & ((p1 & p2 & ATX) & _) & PH).
destruct XC as ((tid & HT & TID) & ATA & EXL & (cdt & thr & sec & tm1 & LIBC) & OFL & SEU & SOU & SIN & SINU
& GDS & (flag & FLGNZ & FLG) & CPL & (os & ODRC)).
pose proof (stk_of_rw_cells asegs m _ _ ODRC) as ODRS. change (ODR_LO + Z.of_nat (cells_size [CB ODR_N os])) with ODR_HI in ODRS.
destruct SSP as (g & G1 & G2).
assert (LO0 : 0x7fff7f800000 <= lo) by ul.
assert (SOK : (so_first so = false \/ so_buf so = []) /\ zlength (so_buf so) <= 2^26).
{ destruct Hso as [->|(k & Hk5 & ->)].
- split; [right; reflexivity| unfold zlength; cbn; lia].
- split; [left; reflexivity|]. cbn [so_lines so_buf]. rewrite zlength_zeros_out. lia. }

set (Qfin := fun (x : unit * stdout_st) (ms' : machine_state) =>
ms_svc_pending ms' = Some (Z_to_bv 64 94) /\ areg ms' 10 = Z_to_bv 64 code).
assert (IMPL : impl asegs (at_node asegs) ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (epost Qfin)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_exit m)).
{ assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
eapply impl_evt.
{ exact (exit_prefix_spec ph ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m lo code tid (Z_to_bv 8 0) p1 p2 cdt thr sec tm1 flag dso Ha0 Htp ltac:(lia) ltac:(rewrite EU; exact ST)
ltac:(rewrite EU; ul) ltac:(lia) TID HT ATX PH ATA EXL LIBC COV FA GF GCX DSO GX CPL FLG FLGNZ (conj UG1 UG2) RG MUX SHC AI CP
THR RMS SC1 SC2 SC3 GDS ODRS MI0). }
intros ms1 PO. unfold exit_prefix_post in PO.
destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1).
rewrite EU in MU1, ST1.
assert (AG1 : agree_on (fun x => (0x6506e8 <= x < 0x6506f0) \/ (0x650b50 <= x < 0x6513a8) \/ (0xf7f30 <= x < 0xf8228)
\/ (0xf45d8 <= x < 0xf45e0) \/ (0x650498 <= x < 0x6504a0)) m m1).
{ apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. ul. }
Local Ltac tr AG1 WM1 H := apply (rw_cells_agree asegs _ _ _ _ H); [apply (agree_sub _ _ _ _ AG1); intros xa Hxa; cbn in Hxa; lia| exact WM1].
assert (LIBC1 : rw_cells asegs m1 0x6506e8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]) by tr AG1 WM1 LIBC.
assert (OFL1 : rw_cells asegs m1 0x650b50 [C8 (Z_to_bv 64 0)]) by tr AG1 WM1 OFL.
assert (SINU1 : rw_cells asegs m1 0xf81f8 [C8 (Z_to_bv 64 0xf8110)]) by tr AG1 WM1 SINU.
assert (SOU1 : rw_cells asegs m1 0xf8108 [C8 (Z_to_bv 64 0xf8020)]) by tr AG1 WM1 SOU.
assert (SEU1 : rw_cells asegs m1 0xf8018 [C8 (Z_to_bv 64 0xf7f30)]) by tr AG1 WM1 SEU.
assert (SIN1 : stdin_file m1).
{ destruct SIN as (j0 & j1 & j2 & j3 & j4 & C). exists j0, j1, j2, j3, j4. tr AG1 WM1 C. }
assert (OUT1 : stdout_file m1 so).
{ apply (stdout_file_agree so m m1); [| exact WM1| exact OUT]. apply (agree_sub _ _ _ _ AG1). intros xa Hxa. lia. }
assert (ERR1 : stderr_file m1).
{ apply stderr_wfile0_file. apply (stderr_wfile0_agree m m1); [| exact WM1| exact ERR]. apply (agree_sub _ _ _ _ AG1). intros xa Hxa. lia. }
assert (G11 : ro_cells asegs m1 0xf45d8 [C8 (Z_to_bv 64 0x650498)]).
{ apply (ro_cells_agree asegs m m1 _ _ G1). apply (agree_sub _ _ _ _ AG1). intros xa Hxa. cbn in Hxa. lia. }
assert (G21 : ro_cells asegs m1 0x650498 [C8 g]).
{ apply (ro_cells_agree asegs m m1 _ _ G2). apply (agree_sub _ _ _ _ AG1). intros xa Hxa. cbn in Hxa. lia. }
assert (EU16 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).
pose proof (stdio_exit_proof so_id so_set (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ => eq_refl)) as SE.
unfold stdio_exit_spec_stmt in SE.
pose proof (SE (Z_to_bv 64 0xde71c) (Z_to_bv 64 (usp + -16)) gp tp u0 u1 u2 (Z_to_bv 64 code) s1 b0 b1 b2 b3 b4 b5 b6 b7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 lo so g cdt thr sec tm1
ltac:(rewrite EU16; exact ST1) LIBC1 OFL1 SINU1 SIN1 SOU1 SEU1 OUT1 ERR1 G11 G21 MI1 Htp
ltac:(rewrite EU16; ul) ltac:(ul)) as IM.
clear SE. unfold implM in IM.
rewrite EU.
eapply impl_post_evt''; [exact IM|].
intros [|[xr so']] ms2 H2; [apply evt_done; exact I|].
cbn [epost fst snd] in H2 |- *. unfold stdio_exit_post in H2.
destruct H2 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & so'' & m2 & -> & _ & _ & MI2 & _).
rewrite (ret_pc_even 0xde71c) by lia.
eapply evt_mono; [exact (exit_tail_spec (usp + -16) code gp tp v0 v1 v2 s1 c0 c1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
v3 v4 v5 v6 F fc m2 ltac:(lia) ltac:(assumption))|].
intros ms3 (ra3 & ->). split; reflexivity. }

assert (RZ : realizes asegs c (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => t_emit [] T))).
{ apply (impl_realizes asegs SEGTOP_A asegs_wx asegs_below [1] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo) Qfin
(fun _ => t_emit [] T)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_exit m) c
(ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact (tok_exit_flush so (proj1 SOK) (proj2 SOK))| exact Hc| exact IMPL|].
- intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
- intros x ms' c' (HS & HA0) Hc'.
assert (R : realizes asegs c' T).
{ apply Hk.
exists (rt_allow RT Σ), (eq ms'), (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo). split; [exact Hc'|]. split.
+ intros ms <-. split; [right; exact HS| exact HA0].
+ intros mo (_ & _ & HFS). exact HFS. }
eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty asegs _ _ R). }
eapply rz_conseq; [exact RZ|].
eapply t_eq_trans; [apply TT_exit_flush; [exact (proj1 SOK)| exact (proj2 SOK)| apply t_emit_has_nil]|].
eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.

Theorem exit_ok : exit_contract RT XENVA OUT_repA ERR_repA.
Proof using AF AF_XIT.
apply (exit_ok_ph false). intros m (XC & XA). split; [exact XC|]. split; [exact XA| exact I].
Qed.

Theorem exit_ok1 : exit_contract RT XENVA1x OUT_repA ERR_repA.
Proof using AF AF_XIT.
apply (exit_ok_ph true). intros m ((XC & XA) & FL). split; [exact XC|]. split; [exact XA|].
destruct XA as (_ & PF & PA). exact (conj PF (conj PA FL)).
Qed.

End XExit.

