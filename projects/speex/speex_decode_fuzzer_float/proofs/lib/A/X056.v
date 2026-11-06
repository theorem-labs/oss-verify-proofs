(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cq X1d0 X1cl X1dh X1cs X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rv X1s9 X1rn X1ry.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e0 X1dx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X03z X04v X0ec X00a X001 X00b X000
X0jh X0ji X047 X048 X01z X03c X0bs X03g X027 X03j
X04l X04q X04o X057 X054 X022 X01y X02e X02d X0jo X04w.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0e7 X055.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X01t X01u.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require X1cn.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X0ux X0vt X14x X0r9 X0r0 X0ra X0qz X0v5 X0v6 X0sy X0ub X12d X0uf X0t6 X0ui X0vj X0vo X0vm X0w5 X0w2 X0t1 X0sx X0td X0tc X1a3 X0vu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X14s X0w3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0ss X0st.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sy OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ub OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ui OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0td OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0tc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vu.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.

Lemma frm0_decR : forall fc : bv 32, {X1cn.frm0 fc} + {~ X1cn.frm0 fc}.
Proof. intros fc. unfold X1cn.frm0. apply Z.eq_dec. Qed.

Section XVprintfR.
Variable RT : rt_sig.

Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_PF : forall Σ m, ART RT Σ m -> pf_consts m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Lemma rng_class_sub : forall Σ p n p' n', rng_class RT Σ p n -> p <= p' -> p' + n' <= p + n -> rng_class RT Σ p' n'.
Proof.
intros Σ p n p' n' H H1 H2. unfold rng_class in *.
destruct H as [(q & k & IN & A1 & A2) | [(f & k & IN & A1 & A2) | [(A1 & A2) | (A1 & A2)]]].
- left. exists q, k. split; [exact IN| lia].
- right; left. exists f, k. split; [exact IN| lia].
- right; right; left. lia.
- right; right; right. lia.
Qed.

Lemma chkr_of : forall Σ m p n, ART RT Σ m -> 0 < n <= 2^40 -> acc bsegs m p n -> rng_class RT Σ p n -> chkr m p n.
Proof using AF_SHW.
intros Σ m p n ART0 Hn AC RC. split; [exact AC|]. split.
- intros i Hi. destruct (AF_SHW Σ m (p + i) 1 ART0 ltac:(lia) (rng_class_sub Σ p n (p + i) 1 RC ltac:(lia) ltac:(lia))) as (QW & _).
destruct (QW ltac:(lia)) as (w1 & w2 & W1 & _). exists w1. exact W1.
- destruct (AF_SHW Σ m p n ART0 ltac:(lia) RC) as (_ & RIM). split; [exact RIM| lia].
Qed.

Theorem vprintf_okR : vprintf_emit0_icontractR RT OUT_repA ERR_repA IO_FPA.
Proof using AF RIP AF_SHW AF_PF.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so ap lo
Ha0 Ha1 VA APS SO HFD OUT0 IOS ART0 MI0 CALL POIS.
destruct (frm0_decR fc) as [FRM|NFRM].
2: {
eapply cpsE_conseq; [exact (vprintf_ok RT AF RIP AF_SHW AF_PF Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc m so ap lo Ha0 Ha1 VA APS SO HFD OUT0 IOS ART0 MI0 CALL POIS)| intros c0 Hc0; exact Hc0|].
intros c0 Hc0. eapply ASTA_conseq; [exact Hc0|]. intros ms (v & m' & RS & REST). exists v, m'. split; [| exact REST].
destruct RS as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F' & fc' & ->).
do 16 eexists. split; [reflexivity| intros H; exfalso; exact (NFRM H)]. }
destruct IOS as (g & SG1 & SG2).
subst a0 a1. intros T c Hc Hk.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite ESP in Hc.
destruct (AF_PF Σ m ART0) as (PFC & IC & ACCF & ACCP & ACCX & ACCN & _).
assert (LO0 : 0x7fff7f800000 <= lo) by ul.
assert (CHKF : chk_ok m 0x1529e 4).
{ apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia|]. intros _. split; [exact ACCF|]. right; right; right. ul. }
assert (PCX : pctx m).
{ destruct IC as ((G2 & G1 & RM & SHC & RI) & _ & _ & M2S). split; [exact M2S| split; assumption]. }

set (Qfin := fun (x : unit * stdout_st) (ms' : machine_state) => exists (m3 : mem),
(exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m3 (seg_rom bsegs) /\ (X1cn.frm0 fc -> X1cn.frm0 fc'))
/\ munch [(lo, usp); (0x1008a0, 0x1008a0 + 232); (0x6593a8, 0x6593a8 + 1024)] m m3 /\ wmono bsegs m m3
/\ mem_inv bsegs m3 /\ stk bsegs m3 lo usp /\ stdout_file m3 (snd x)).
assert (IMPL : impl bsegs (at_node bsegs) (emit_prog so) (epost Qfin)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m)).
assert (L1 : lo <= usp - 2416) by ul.
assert (L2 : kHighShadowEnd + 8 <= lo) by ul.
assert (L3 : usp <= 2^47) by ul.
pose proof (rw_cells_bound bsegs m ap _ VA) as APB. cbn [cells_size csize Nat.add] in APB.
assert (L4 : 0 <= ap < 2^63) by ul.
{ eapply impl_evt;
[exact (vprintf_walkA RIP usp ap lo ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m ST L1 L2 L3 SPA L4 CHKF PCX PFC MI0)|].
intros ms1 (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & -> & MU1 & WM1 & MI1 & ST1 & FRf & FRv).
assert (AG1 : agree_on (fun x => x < usp - 2416 \/ usp <= x) m m1).
{ apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia| exact I]. }
assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ul).

assert (SF1 : stdout_file m1 (vso_get so)).
{ apply (stdout_file_agree so m m1); [| exact WM1| exact OUT0]. apply (agree_sub _ _ _ _ AG1). intros x Hx. ul. }
assert (BY1 : bytes_at bsegs m1 0x1529e (zb [37; 100; 10; 0])) by (apply img_bytes; [exact MI1 | lia | cbn; lia | vm_compute; reflexivity]).
assert (VA1 : va_area m1 ap [Z_to_bv 64 0]).
{ pose proof (rw_cells_agree bsegs m m1 _ _ VA ltac:(apply (agree_sub _ _ _ _ AG1); intros x Hx; cbn [cells_size csize Nat.add] in Hx; ul) WM1) as V.
exact (proj2 (proj1 V)). }
assert (SSP1 : ssp_cells m1 g).
{ split.
- apply (ro_cells_agree bsegs m m1 _ _ SG1). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul.
- apply (ro_cells_agree bsegs m m1 _ _ SG2). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul. }
assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MU1 WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; ul).
assert (CHM : forall p n, chkr m p n -> chkr m1 p n).
{ intros p n H. apply (chkr_munch _ m m1 p n H MU1). intros x Hx. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hx. ul. }
pose proof (stk_split bsegs m1 lo (lo + 64) (usp + -96) ST1 ltac:(ul)) as (ST1a & ST1b).
assert (STKC : forall p n, lo + 64 <= p -> p + n <= usp + -96 -> chkr m1 p n).
{ intros p n H1 H2. apply CHM. destruct (Z_lt_le_dec 0 n) as [NP|NN].
- apply (chkr_of Σ m p n ART0); [ul| | ].
+ apply (af_acc_stack RT AF Σ m p n ART0); [ul | ul | apply (pois_apart_above _ _ _ _ POIS); ul].
+ right; right; left. ul.
- split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul. }
assert (FMTC : chkr m1 0x1529e 4) by (apply CHM; apply (chkr_of Σ m _ _ ART0); [lia| exact ACCF| right; right; right; ul]).
assert (ROD : rod_chk m1).
{ split; [| split]; apply CHM; (apply (chkr_of Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]). }
assert (CHBUF : chkr m1 RSTDOUT_BUF 1024).
{ apply CHM. apply (chkr_of Σ m _ _ ART0); [lia| | right; right; right; ul].
apply (af_acc_static RT AF Σ m _ _ ART0); [lia|]. intros i Hi.
split; [apply client_static_intro; lia| lia]. }
pose proof (X0st.vfprintf_stdout_proof vso_get vso_set vso_GS vso_SS
(fwritex_stdout_proof RIP (fun St get set GS SS => stdout_writefn_proof get set GS SS)) RIP) as VF.
unfold X0st.vfprintf_stdout_stmt in VF. cbv zeta in VF.
pose proof (VF (Z_to_bv 64 0x5a190) (Z_to_bv 64 (usp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 86686) (Z_to_bv 64 1050784)
(Z_to_bv 64 1050784) (Z_to_bv 64 86686) (Z_to_bv 64 ap) a3' a4' a5' a6' a7' (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m1 so 0x1529e ap [37; 100; 10; 0] [Z_to_bv 64 0] [PA_i 0] pieces_emit_0 2 (lo + 64) g) as IM.
clear VF. unfold X1rv.implM in IM.
eapply impl_post_evt''.
{ apply IM; clear IM; rewrite ?EU96.
- reflexivity.
- reflexivity.
- reflexivity.
- exact SF1.
- exact BY1.
- repeat constructor; lia.
- vm_compute; reflexivity.
- exact VA1.
- cbn [X0ss.args_ok X0ss.arg_ok]. split; [| exact I]. split; [lia| reflexivity].
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- exact ST1b.
- unfold X0ss.VF_DEPTH; ul.
- unfold GLOBALS_TOP; ul.
- ul.
- exact SSP1.
- exact MI1.
- exact FRM.
- lia.
- unfold zlength, STATIC_SPLIT; cbn; lia.
- lia.
- unfold zlength; cbn; lia.
- ul.
- exact IC1.
- exact STKC.
- exact FMTC.
- exact ROD.
- exact CHBUF. }
intros [|[xr st']] ms2 H2; [apply evt_done; exact I|].
cbn [epost fst snd] in H2 |- *.
destruct H2 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc2 & m2 & -> & MU2 & WM2 & MI2
& FRM2 & _ & ST2 & SF2 & SSP2).
rewrite EU96 in MU2, ST2.
rewrite (ret_pc_even 0x5a190) by lia.
assert (AG2 : agree_on (fun x => usp + -96 <= x) m1 m2).
{ apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. split; [lia|]. split; [ul| split; [ul| exact I]]. }
pose proof (rw_cells_agree bsegs m1 m2 _ _ FRf ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRf2.
pose proof (rw_cells_agree bsegs m1 m2 _ _ FRv ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRv2.
eapply evt_mono.
{ apply (vprintf_walkB usp ap (lo + 64) junk (Z_to_bv 64 0x5a190) ra gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 86686) (Z_to_bv 64 1050784)
b0 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 Ft fc2 m2
ST2 ltac:(lia) L3 FRf2 FRv2 MI2). }
intros ms3 ((w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & RS3) & ST3).
exists m2. split.
{ rewrite RS3. do 17 eexists. split; [reflexivity| intros _; exact FRM2]. }
split.
{ apply (munch_merge [(usp - 2416, usp)] [(lo + 64, usp + -96); (0x1008a0, 0x1008a0 + 232); (0x6593a8, 0x6593a8 + 1024)] _ m m1 m2 MU1 MU2).
intros x Hx. cbn in Hx |- *. intuition lia. }
split; [exact (wmono_trans bsegs m m1 m2 WM1 WM2)|]. split; [exact MI2|].
split; [| exact SF2]. apply (stk_merge bsegs m2 lo (lo + 64) usp); [| exact ST3| ul].
exact (stk_transport_disjoint bsegs _ _ _ _ _ ST1a MU2 WM2 ltac:(cbn [disjoint_from]; ul)). }
assert (IMPL2 : impl bsegs (at_node bsegs) (emit_prog so) (epost (fun x ms' => Qfin x ms' /\ snd x = emit0_next so))
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m)).
{ eapply impl_mono; [eapply impl_tforall; [exact (leaves_emit so SO)| exact IMPL]|].
intros [|x] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I| split; assumption]. }

assert (RZ : realizes bsegs c (TT (emit_prog so) (fun _ => t_emit [] T))).
{ apply (impl_realizes bsegs SEGTOP_A asegs_wx asegs_below [1] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
(fun x ms' => Qfin x ms' /\ snd x = emit0_next so) (fun _ => t_emit [] T)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m) c
(ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact (tok_emit so SO)| exact Hc| exact IMPL2|].
- intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
- intros x ms' c' (HQ & HX) Hc'.
assert (R : realizes bsegs c' T).
{ apply Hk. eapply ASTA_conseq; [exact Hc'|]. intros ms <-.
destruct HQ as (m3 & (v & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & -> & FRM3)
& MU3 & WM3 & MI3 & ST3 & SF3).
exists v, m3. split.
{ rewrite ESP. do 16 eexists. split; [reflexivity| exact FRM3]. }
split; [split; [| split; [exact MI3| split; [exact WM3| exact ST3]]]|].
- apply (af_frame RT AF Σ m m3 lo ART0); [ul| | exact WM3].
intros a Ha. apply MU3. cbn. split; [intros Hin; apply Ha; left; ul|].
split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|].
split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia| exact I].
- split; [| split].
+ intros a Ha Hout. apply MU3. cbn in Hout |- *. destruct Hout as (O1 & O2 & O3 & _). split; [| split; [lia| split; [lia| exact I]]].
destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
+ rewrite <- HX. exact SF3.
+ intros ERR0. apply (stderr_wfile0_agree m m3); [| exact WM3| exact ERR0].
apply (agree_of_munch _ _ _ _ MU3). intros y Hy. cbn. split; [ul| split; [lia| split; [lia| exact I]]]. }
eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty bsegs _ _ R). }
eapply rz_conseq; [exact RZ|].
eapply t_eq_trans; [apply (TT_emit so (fun _ => t_emit [] T) SO (t_emit_has_nil [] T))|].
eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.
End XVprintfR.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.

Lemma frm0_decR : forall fc : bv 32, {X1cn.frm0 fc} + {~ X1cn.frm0 fc}.
Proof. intros fc. unfold X1cn.frm0. apply Z.eq_dec. Qed.

Section XVprintfR.
Variable RT : rt_sig.

Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_PF : forall Σ m, ART RT Σ m -> pf_consts m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Lemma rng_class_sub : forall Σ p n p' n', rng_class RT Σ p n -> p <= p' -> p' + n' <= p + n -> rng_class RT Σ p' n'.
Proof.
intros Σ p n p' n' H H1 H2. unfold rng_class in *.
destruct H as [(q & k & IN & A1 & A2) | [(f & k & IN & A1 & A2) | [(A1 & A2) | (A1 & A2)]]].
- left. exists q, k. split; [exact IN| lia].
- right; left. exists f, k. split; [exact IN| lia].
- right; right; left. lia.
- right; right; right. lia.
Qed.

Lemma chkr_of : forall Σ m p n, ART RT Σ m -> 0 < n <= 2^40 -> acc asegs m p n -> rng_class RT Σ p n -> chkr m p n.
Proof using AF_SHW.
intros Σ m p n ART0 Hn AC RC. split; [exact AC|]. split.
- intros i Hi. destruct (AF_SHW Σ m (p + i) 1 ART0 ltac:(lia) (rng_class_sub Σ p n (p + i) 1 RC ltac:(lia) ltac:(lia))) as (QW & _).
destruct (QW ltac:(lia)) as (w1 & w2 & W1 & _). exists w1. exact W1.
- destruct (AF_SHW Σ m p n ART0 ltac:(lia) RC) as (_ & RIM). split; [exact RIM| lia].
Qed.

Theorem vprintf_okR : vprintf_emit0_icontractR RT OUT_repA ERR_repA IO_FPA.
Proof using AF RIP AF_SHW AF_PF.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so ap lo
Ha0 Ha1 VA APS SO HFD OUT0 IOS ART0 MI0 CALL POIS.
destruct (frm0_decR fc) as [FRM|NFRM].
2: {
eapply cpsE_conseq; [exact (vprintf_ok RT AF RIP AF_SHW AF_PF Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc m so ap lo Ha0 Ha1 VA APS SO HFD OUT0 IOS ART0 MI0 CALL POIS)| intros c0 Hc0; exact Hc0|].
intros c0 Hc0. eapply ASTA_conseq; [exact Hc0|]. intros ms (v & m' & RS & REST). exists v, m'. split; [| exact REST].
destruct RS as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F' & fc' & ->).
do 16 eexists. split; [reflexivity| intros H; exfalso; exact (NFRM H)]. }
destruct IOS as (g & SG1 & SG2).
subst a0 a1. intros T c Hc Hk.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite ESP in Hc.
destruct (AF_PF Σ m ART0) as (PFC & IC & ACCF & ACCP & ACCX & ACCN & _).
assert (LO0 : 0x7fff7f800000 <= lo) by ul.
assert (CHKF : chk_ok m 0x151ae 4).
{ apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia|]. intros _. split; [exact ACCF|]. right; right; right. ul. }
assert (PCX : pctx m).
{ destruct IC as ((G2 & G1 & RM & SHC & RI) & _ & _ & M2S). split; [exact M2S| split; assumption]. }

set (Qfin := fun (x : unit * stdout_st) (ms' : machine_state) => exists (m3 : mem),
(exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m3 (seg_rom asegs) /\ (X1cn.frm0 fc -> X1cn.frm0 fc'))
/\ munch [(lo, usp); (0xf8020, 0xf8020 + 232); (0x650b68, 0x650b68 + 1024)] m m3 /\ wmono asegs m m3
/\ mem_inv asegs m3 /\ stk asegs m3 lo usp /\ stdout_file m3 (snd x)).
assert (IMPL : impl asegs (at_node asegs) (emit_prog so) (epost Qfin)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m)).
assert (L1 : lo <= usp - 2416) by ul.
assert (L2 : kHighShadowEnd + 8 <= lo) by ul.
assert (L3 : usp <= 2^47) by ul.
pose proof (rw_cells_bound asegs m ap _ VA) as APB. cbn [cells_size csize Nat.add] in APB.
assert (L4 : 0 <= ap < 2^63) by ul.
{ eapply impl_evt;
[exact (vprintf_walkA RIP usp ap lo ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m ST L1 L2 L3 SPA L4 CHKF PCX PFC MI0)|].
intros ms1 (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & -> & MU1 & WM1 & MI1 & ST1 & FRf & FRv).
assert (AG1 : agree_on (fun x => x < usp - 2416 \/ usp <= x) m m1).
{ apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia| exact I]. }
assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ul).

assert (SF1 : stdout_file m1 (vso_get so)).
{ apply (stdout_file_agree so m m1); [| exact WM1| exact OUT0]. apply (agree_sub _ _ _ _ AG1). intros x Hx. ul. }
assert (BY1 : bytes_at asegs m1 0x151ae (zb [37; 100; 10; 0])) by (apply img_bytes; [exact MI1 | lia | cbn; lia | vm_compute; reflexivity]).
assert (VA1 : va_area m1 ap [Z_to_bv 64 0]).
{ pose proof (rw_cells_agree asegs m m1 _ _ VA ltac:(apply (agree_sub _ _ _ _ AG1); intros x Hx; cbn [cells_size csize Nat.add] in Hx; ul) WM1) as V.
exact (proj2 (proj1 V)). }
assert (SSP1 : ssp_cells m1 g).
{ split.
- apply (ro_cells_agree asegs m m1 _ _ SG1). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul.
- apply (ro_cells_agree asegs m m1 _ _ SG2). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul. }
assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MU1 WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; ul).
assert (CHM : forall p n, chkr m p n -> chkr m1 p n).
{ intros p n H. apply (chkr_munch _ m m1 p n H MU1). intros x Hx. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hx. ul. }
pose proof (stk_split asegs m1 lo (lo + 64) (usp + -96) ST1 ltac:(ul)) as (ST1a & ST1b).
assert (STKC : forall p n, lo + 64 <= p -> p + n <= usp + -96 -> chkr m1 p n).
{ intros p n H1 H2. apply CHM. destruct (Z_lt_le_dec 0 n) as [NP|NN].
- apply (chkr_of Σ m p n ART0); [ul| | ].
+ apply (af_acc_stack RT AF Σ m p n ART0); [ul | ul | apply (pois_apart_above _ _ _ _ POIS); ul].
+ right; right; left. ul.
- split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul. }
assert (FMTC : chkr m1 0x151ae 4) by (apply CHM; apply (chkr_of Σ m _ _ ART0); [lia| exact ACCF| right; right; right; ul]).
assert (ROD : rod_chk m1).
{ split; [| split]; apply CHM; (apply (chkr_of Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]). }
assert (CHBUF : chkr m1 RSTDOUT_BUF 1024).
{ apply CHM. apply (chkr_of Σ m _ _ ART0); [lia| | right; right; right; ul].
apply (af_acc_static RT AF Σ m _ _ ART0); [lia|]. intros i Hi.
split; [apply client_static_intro; lia| lia]. }
pose proof (X01u.vfprintf_stdout_proof vso_get vso_set vso_GS vso_SS
(fwritex_stdout_proof RIP (fun St get set GS SS => stdout_writefn_proof get set GS SS)) RIP) as VF.
unfold X01u.vfprintf_stdout_stmt in VF. cbv zeta in VF.
pose proof (VF (Z_to_bv 64 0x5a0a4) (Z_to_bv 64 (usp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 86446) (Z_to_bv 64 1015840)
(Z_to_bv 64 1015840) (Z_to_bv 64 86446) (Z_to_bv 64 ap) a3' a4' a5' a6' a7' (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m1 so 0x151ae ap [37; 100; 10; 0] [Z_to_bv 64 0] [PA_i 0] pieces_emit_0 2 (lo + 64) g) as IM.
clear VF. unfold X1rv.implM in IM.
eapply impl_post_evt''.
{ apply IM; clear IM; rewrite ?EU96.
- reflexivity.
- reflexivity.
- reflexivity.
- exact SF1.
- exact BY1.
- repeat constructor; lia.
- vm_compute; reflexivity.
- exact VA1.
- cbn [X01t.args_ok X01t.arg_ok]. split; [| exact I]. split; [lia| reflexivity].
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- exact ST1b.
- unfold X01t.VF_DEPTH; ul.
- unfold GLOBALS_TOP; ul.
- ul.
- exact SSP1.
- exact MI1.
- exact FRM.
- lia.
- unfold zlength, STATIC_SPLIT; cbn; lia.
- lia.
- unfold zlength; cbn; lia.
- ul.
- exact IC1.
- exact STKC.
- exact FMTC.
- exact ROD.
- exact CHBUF. }
intros [|[xr st']] ms2 H2; [apply evt_done; exact I|].
cbn [epost fst snd] in H2 |- *.
destruct H2 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc2 & m2 & -> & MU2 & WM2 & MI2
& FRM2 & _ & ST2 & SF2 & SSP2).
rewrite EU96 in MU2, ST2.
rewrite (ret_pc_even 0x5a0a4) by lia.
assert (AG2 : agree_on (fun x => usp + -96 <= x) m1 m2).
{ apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. split; [lia|]. split; [ul| split; [ul| exact I]]. }
pose proof (rw_cells_agree asegs m1 m2 _ _ FRf ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRf2.
pose proof (rw_cells_agree asegs m1 m2 _ _ FRv ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRv2.
eapply evt_mono.
{ apply (vprintf_walkB usp ap (lo + 64) junk (Z_to_bv 64 0x5a0a4) ra gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 86446) (Z_to_bv 64 1015840)
b0 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 Ft fc2 m2
ST2 ltac:(lia) L3 FRf2 FRv2 MI2). }
intros ms3 ((w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & RS3) & ST3).
exists m2. split.
{ rewrite RS3. do 17 eexists. split; [reflexivity| intros _; exact FRM2]. }
split.
{ apply (munch_merge [(usp - 2416, usp)] [(lo + 64, usp + -96); (0xf8020, 0xf8020 + 232); (0x650b68, 0x650b68 + 1024)] _ m m1 m2 MU1 MU2).
intros x Hx. cbn in Hx |- *. intuition lia. }
split; [exact (wmono_trans asegs m m1 m2 WM1 WM2)|]. split; [exact MI2|].
split; [| exact SF2]. apply (stk_merge asegs m2 lo (lo + 64) usp); [| exact ST3| ul].
exact (stk_transport_disjoint asegs _ _ _ _ _ ST1a MU2 WM2 ltac:(cbn [disjoint_from]; ul)). }
assert (IMPL2 : impl asegs (at_node asegs) (emit_prog so) (epost (fun x ms' => Qfin x ms' /\ snd x = emit0_next so))
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m)).
{ eapply impl_mono; [eapply impl_tforall; [exact (leaves_emit so SO)| exact IMPL]|].
intros [|x] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I| split; assumption]. }

assert (RZ : realizes asegs c (TT (emit_prog so) (fun _ => t_emit [] T))).
{ apply (impl_realizes asegs SEGTOP_A asegs_wx asegs_below [1] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
(fun x ms' => Qfin x ms' /\ snd x = emit0_next so) (fun _ => t_emit [] T)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m) c
(ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact (tok_emit so SO)| exact Hc| exact IMPL2|].
- intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
- intros x ms' c' (HQ & HX) Hc'.
assert (R : realizes asegs c' T).
{ apply Hk. eapply ASTA_conseq; [exact Hc'|]. intros ms <-.
destruct HQ as (m3 & (v & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & -> & FRM3)
& MU3 & WM3 & MI3 & ST3 & SF3).
exists v, m3. split.
{ rewrite ESP. do 16 eexists. split; [reflexivity| exact FRM3]. }
split; [split; [| split; [exact MI3| split; [exact WM3| exact ST3]]]|].
- apply (af_frame RT AF Σ m m3 lo ART0); [ul| | exact WM3].
intros a Ha. apply MU3. cbn. split; [intros Hin; apply Ha; left; ul|].
split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|].
split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia| exact I].
- split; [| split].
+ intros a Ha Hout. apply MU3. cbn in Hout |- *. destruct Hout as (O1 & O2 & O3 & _). split; [| split; [lia| split; [lia| exact I]]].
destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
+ rewrite <- HX. exact SF3.
+ intros ERR0. apply (stderr_wfile0_agree m m3); [| exact WM3| exact ERR0].
apply (agree_of_munch _ _ _ _ MU3). intros y Hy. cbn. split; [ul| split; [lia| split; [lia| exact I]]]. }
eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty asegs _ _ R). }
eapply rz_conseq; [exact RZ|].
eapply t_eq_trans; [apply (TT_emit so (fun _ => t_emit [] T) SO (t_emit_has_nil [] T))|].
eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.
End XVprintfR.
