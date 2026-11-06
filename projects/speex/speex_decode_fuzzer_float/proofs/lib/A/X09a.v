(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck X1cu X1cv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05q X05s X05u X05t
X081 X05l X05m X09f X06d X069 X082 X09e X08y X091 X08x X08u X094.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X09c X097 X096 X099.

From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require X1cr X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X12b X0z5 X0wl X0wn X0wm X0ys X0x2 X0yt X0zq X0zp X0zl X0zu X101 X0zw X0zy.
Module B_TWIN.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0mx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0k2.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1di OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cs OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1da OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1df OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1ck OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cv OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dh.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1r2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1nt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1rh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1re.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X06d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X091.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X101 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zw OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zy.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NbEB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MST : memset_icontract RT e_asan_memset.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MSTa : mat_stable PMc.
Variable X : @nbinvA bptr.
Hypothesis NXOK : nbx_ok X.
Hypothesis TP : x_tp X = Z_to_bv 64 0x638c98.
Variables (Σ0 : rts RT) (fr0 : list (Z * nat)) (PD ND fh : Z) (kh : nat).
Hypothesis NSIG : nbsig RT Σ0 X fr0 PD ND fh kh.
Variables (mE : mem) (r : smrec) (mo olp : Z).

Hypothesis LTP : forall k, sm_ltp_unquant (smr_sm r) = Some k -> @ltp_unquant_cps RT bptr k.
Hypothesis INN : forall ki, sm_innovation_unquant (smr_sm r) = Some ki -> @innov_unquant_cps RT bptr ki.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation FF := (x_ff X). Local Notation SF := (x_sf X). Local Notation STEREO := (x_stereo X).
Local Notation lo := (x_lo X). Local Notation usp := (x_usp X). Local Notation nout := (x_nout X).

Local Notation R_J := (X0zy.R_J X).
Local Notation slots_J := (X0zy.slots_J X).
Local Notation at_Jc := (X0zy.at_Jc RT PMc X Σ0 mE r mo olp).
Local Notation nbE_bJ := (X0zy.nbE_bJ r).
Local Notation nbE_tabs_acc_art := (X0zy.nbE_tabs_acc_art RT AF).
Local Notation nbE_live_apart := (X0zy.nbE_live_apart RT AF).
Local Notation nbE_live_checked_dst := (X0zy.nbE_live_checked_dst RT AF).
Local Notation nbE_frame_checked_dst := (X0zy.nbE_frame_checked_dst RT).
Local Notation nbG_acc_pres2 := (X0zy.nbG_acc_pres2 RT AF).
Local Ltac simpl_sizes ::=
rewrite ?nbE_sz_shadow, ?nbE_sz_slots, ?nbE_sz_saves, ?nbE_sz_hdr, ?nbE_sz_cfg, ?nbE_sz_tail, ?nbE_sz_ucb, ?nbE_sz_ltpargs;
rewrite ?length_app, ?cells_size_app, ?cells_size_f32, ?length_f32, ?repeat_length;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app, ?cells_size_f32, ?length_f32, ?repeat_length; cbn [length].

Ltac nbe_base t := lazymatch t with ?x + _ => nbe_base x | _ => t end.
Ltac nbe_lia := first [ llia | cllia ].
Ltac nbe_cls :=
lazymatch goal with
| Hx : ?a <= ?x < _ |- aclient ?L ?Fr ?spv ?x =>
let bs := nbe_base a in
lazymatch bs with
| x_st _ => right; right; left; exists (x_st X), 2968; split; [assumption | nbe_lia]
| x_ff _ => right; right; right; left; exists (x_ff X), NBD_FCLASS; split; [assumption | fs_lit; nbe_lia]
| x_sf _ => right; right; right; right; exists (x_ff X), NBD_FCLASS; split; [assumption | fs_lit;
match goal with E1 : shad (x_ff X) = x_sf X, E2 : shad (x_ff X + 2048) = x_sf X + 256 |- _ => rewrite E1, E2 end; nbe_lia]
| x_out _ => right; right; right; left; exists fh, kh; split; [assumption | nbe_lia]
| x_A _ => right; right; right; left; exists fh, kh; split; [assumption | nbe_lia]
| x_stereo _ => right; right; right; left; exists fh, kh; split; [assumption | nbe_lia]
| x_D _ => right; right; left; exists PD, ND; split; [assumption | nbe_lia]
| x_usp _ => left; unfold USTACK_TOP; nbe_lia
end
end.
Ltac nbe_out1 :=
first [ llia
| lazymatch goal with Hx : ?a <= ?x < _ |- ~ (?d <= ?x < _) =>
let ba := nbe_base a in let bd := nbe_base d in
match goal with H : hid ?P |- _ => match P with context [ba] => match P with context [bd] =>
let U := fresh "U" in pose proof (H : P) as U; nbe_lia end end end
end
| cllia ].
Ltac nbe_trp PRES :=
lazymatch type of PRES with
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
lazymatch goal with WM : wmono bsegs m m' |- _ =>
repeat match goal with
| H : rw_cells bsegs m ?Aa ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells bsegs m' Aa cs)
by (apply (rw_cells_agree bsegs m m' Aa cs H);
[ apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [nbe_cls | try unfold BITS_SIZEOF, NBSTATE_SIZEOF; nbe_out1] | exact WM ]);
clear H; rename H' into H
| idtac "note: nbe_trp dropping" H; clear H ]
end end
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch goal with WM : wmono bsegs m m' |- _ =>
repeat match goal with
| H : rw_cells bsegs m ?Aa ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells bsegs m' Aa cs)
by (apply (rw_cells_agree bsegs m m' Aa cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ?x ?Hx; cps_sizes Hx;
split; [nbe_cls | cbn [outside]; try unfold BITS_SIZEOF, NBSTATE_SIZEOF; repeat lazymatch goal with |- _ /\ _ => split end; first [exact I | nbe_out1]] | exact WM ]);
clear H; rename H' into H
| idtac "note: nbe_trp dropping" H; clear H ]
end end
end.

Tactic Notation "nbe_unpack" hyp(Hc) "as" simple_intropattern(P) :=
try unfold icpt_postF in Hc;
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
lazymatch type of H with bv_unsigned (Z_to_bv 64 _) = _ => fail | _ => idtac end;
rewrite (unsigned_lit z) in H by ulc
end
end.

Ltac nbe_dj1 :=
first [ llia
| lazymatch goal with |- ?a + _ <= ?l \/ _ =>
let ba := nbe_base a in let bl := nbe_base l in
match goal with H : hid ?P |- _ => match P with context [ba] => match P with context [bl] =>
let U := fresh "U" in pose proof (H : P) as U; nbe_lia end end end
end
| cllia ].
Ltac nbe_dj := cbn [disjoint_from]; simpl_sizes; repeat (split; [nbe_dj1|]); first [exact I | nbe_dj1].
Ltac nbe_seg_tr m m' MU WM :=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at bsegs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport bsegs W m m' A2 bs2) in H; [ | exact MU | nbe_dj ]
| idtac "note: nbe_seg_tr dropping" H; clear H ]
| H : rw_cells bsegs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport bsegs W m m' A2 cs2) in H; [ | exact MU | exact WM | nbe_dj ]
| idtac "note: nbe_seg_tr dropping" H; clear H ]
| H : ro_cells bsegs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport bsegs W m m' A2 cs2) in H; [ | exact MU | nbe_dj ]
| idtac "note: nbe_seg_tr dropping" H; clear H ]
| H : stk bsegs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint bsegs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; repeat (split; [nbe_dj1|]); first [exact I | nbe_dj1] ]
| idtac "note: nbe_seg_tr dropping" H; clear H ]
end.

Ltac nbe_pf_fp PRES :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_of_pres_fp L0 F0 U0 W0 live frames sp W m m' PRES);
[ cps_incl | cps_incl | ulc
| let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho |- *; decompose [and] Ho; clear Ho Hx;
repeat (split; [ let Hin := fresh "Hin" in intro Hin; try unfold BITS_SIZEOF, NBSTATE_SIZEOF in Hin;
match goal with H : ~ (_ <= x < _) |- False => apply H;
first [clear - Hin; cps_unf; lia | match goal with S : 0 <= ?v < 4 |- _ => clear - Hin S; cps_unf; lia end | nbe_lia] end | ]);
exact I ]);
clear PF; rename PF' into PF
end
end.

Lemma nbE_h2z2 : forall (usp ST FF EXW iv : Z) (gp tp xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
iv = 0 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (F' : bvmap 5 word) (a0' a1' a2' a3' a4' a5' : word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5' a6 a7
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 iv) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F' (Z_to_bv 64 NBE_PC_H3) fc None m (seg_rom bsegs))
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 iv) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa3418) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros E0 MI. subst iv.
unfold NBE_PC_H3 in *.
astep.
apply evt_done. do 7 eexists. reflexivity.
Qed.

Definition R_H3 (isv sub : Z) (xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) (x_gp X) (x_tp X) (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) s3 (Z_to_bv 64 (160 * sub)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6.
Definition at_H3c (bp' sub : Z) (st : nb_state bptr) (bJ : bits_st bptr) : config -> Prop :=
fun c => exists (Σ : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word)
(j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff) (bp : Z),
ASTA RT Σ PMc (eq (MS (R_H3 (nb_isave_ptr OUT st) sub xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6) Fx (Z_to_bv 64 NBE_PC_H3) fc None m (seg_rom bsegs))) c
/\ frm0 fc /\ nbctx X m st bJ j ows sws (slots_J bp' sub s) ff SC_E /\ slots_EL ST OUT A FF SF olp bp sub s
/\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp' <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4
/\ nbEH_mem RT X Σ0 mE Σ m /\ nbEH_sig RT Σ0 Σ (rt_credit RT Σ0).

Lemma nbE_B1 : forall (bp' sub : Z) (st : nb_state bptr) (bJ : bits_st bptr),
cps bsegs (at_Jc bp' sub st bJ) (at_H3c bp' sub st bJ).
Proof.
intros bp' sub st bJ T c Hc Hk.
destruct Hc as (Σ & Fx & fc & m & xra & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & bp
& Hc0 & FRM & CTX & SLE & SAT & EMO & BP' & OLP & SUB & MEM & SIG).
destruct MEM as (ART0 & NACC & WM0 & PF).
destruct SIG as (LV & FRS & SP0 & CR & POI).
destruct CTX as (MI0 & STK0 & NBP & JOK & CBOK & NINV & BREP & BOK & BSZ & OW & LOW & SW & LSW & (SL & SV) & FFA & FFOK & (rest & SH) & CC & LC & JEXC & JISV).
unfold slots_J in SL.
pose proof NXOK as (U32 & SPH & LOS & LOU & F0 & F64 & ESF & FLO & FTOP & FSH & SF0 & SF1 & SFLO & S8 & SPOS & SLO & SSH & SIMG & O4 & OTOP & OLO & NOUT & OSH
& A8 & ATOP & ALO & ASH & D0 & DLO & DSZ & STE4 & STETOP & STELO & STESH & ISVX & SOA & SAA & SDA & SSTA & SFA & SSFA & OAA & ODA & OSTA & OFA & OSFA
& ADA & ASTEA & AFFA & ASFA & DSTA & DFA & DSFA & STEFA & STESFA & FSFA).
pose proof NSIG as (NFR & NLS & NLD & PD1 & PD2 & PDS & NFH & FHO1 & FHO2 & FHA1 & FHA2 & FHS1 & FHS2 & NPOIS & NLOW & NROOM & NTOP).
destruct NBP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
destruct FFA as (FF0 & FFp & FFg & FFl & FFq & FFk & FFi & FFe & FFj & FFiq).
assert (INL : In (ST, NBSTATE_SIZEOF) (rt_live RT Σ)) by (rewrite LV; exact NLS).
assert (INF : In (FF, NBD_FCLASS) (rt_frames RT Σ)) by (rewrite FRS, NFR; left; reflexivity).
assert (INFH : In (fh, kh) (rt_frames RT Σ)) by (rewrite FRS, NFR; right; exact NFH).
assert (INPD : In (PD, ND) (rt_live RT Σ)) by (rewrite LV; exact NLD).
assert (ESF8 : FF / 8 + SHB = SF) by (rewrite ESF, Z.shiftr_div_pow2 by lia; reflexivity).
assert (SHD1 : shad FF = SF) by (unfold shad; exact ESF8).
assert (SHD2 : shad (FF + 2048) = SF + 256) by (unfold shad; rewrite <- ESF8; clear - F64; Z.div_mod_to_equations; lia).
destruct (af_acc_live RT AF Σ m ST NBSTATE_SIZEOF ART0 INL) as (WRS & ACS).
pose proof (af_live_small RT AF Σ m ST NBSTATE_SIZEOF ART0 INL ltac:(unfold NBSTATE_SIZEOF; lia)) as STTOP.
assert (LOWS : rt_sp0 RT Σ - STACK_WIN <= lo) by (rewrite SP0; exact NLOW).
assert (POA : pois_above (rt_pois RT Σ) (usp + -576)) by (rewrite POI; replace (usp + -576) with (usp - NBD_FRAME) by (unfold NBD_FRAME; lia); exact NPOIS).
change hidp with hid in *.
unfold NBSTATE_SIZEOF, NBD_FRAME, NBD_CALLEE_STACK, RT_STACK, BITS_SIZEOF in *.
assert (OBS : aobj bsegs m ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS]).

assert (ISK : (nb_innov_save st = None /\ nb_isave_ptr OUT st = 0)
\/ (exists kis, nb_innov_save st = Some kis /\ nb_isave_ptr OUT st = OUT + 4 * kis /\ 160 <= kis /\ kis + 160 <= Z.of_nat nout)).
{ unfold nb_isave_ptr. pose proof NINV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NI12). rewrite JISV in NI12 |- *.
destruct (nb_innov_save (x_st0 X)) as [kis|]; [right; exists kis; split; [reflexivity|]; split; [reflexivity|]; split; [exact NI12| exact ISVX]| left; split; reflexivity]. }
assert (ISB : 0 <= nb_isave_ptr OUT st < 2^63).
{ destruct ISK as [(_ & ->) | (kis & _ & -> & K1 & K2)]; [lia|]. clear - K1 K2 OLO LOU SPH O4 OTOP. unfold IMG_TOP_B in *. lia. }
rewrite JEXC in P3.

pose proof (PF : nbE_keep (rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE m)) as PFE. clear PF.
pose proof (WM0 : nbE_keep (wmono bsegs mE m)) as WME. clear WM0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -576, usp)] m) as PF.
pose proof (fun a0 => aclient_split RT AF Σ m (usp + -576) a0 ART0) as SPL.

destruct BREP as ((rj & Lrj & BOBJ) & (bs & BDAT & Hbs) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bs)) in BDAT.
clear LC CC.
pose proof JOK as (JL1 & JL2 & JL3 & JL4 & JL5 & JL6 & JL7 & JL8 & JL9 & JL10 & (JL11a & JL11b) & JL12 & JL13).
pose proof FFOK as (FL1 & FL2 & FL3 & FL4 & FL5 & FL6 & FL7 & FL8).
assert (LBS : Z.of_nat (length bs) = sb_buf_size bJ)
by (pose proof BOK as BOK'; unfold bits_ok in BOK'; rewrite Hbs, zlength_map_unsigned in BOK'; clear - BOK'; lia).
assert (DLOb : D + Z.of_nat (length bs) <= lo) by (rewrite LBS, BSZ, <- DSZ; exact DLO).
assert (DPD : D + Z.of_nat (length bs) <= PD + ND) by (rewrite LBS, BSZ, <- DSZ; exact PD2).
assert (DSZb : Z.of_nat (length bs) = x_dsz X) by (rewrite LBS, BSZ, <- DSZ; reflexivity).
pose proof SLE as (E0s & E24s & E32s & E40s & E48s & E56s & E64s & E72s & E80s & E88s & E96s & E104s & E120s & E128s & E136s & E144s & E152s & E160s & E168s & E176s
& E184s & E192s & E200s & E208s & E216s & E232s & E240s & E256s & E264s & E272s & E280s & E288s & E296s & E304s & E312s & E320s & E328s & E336s & E344s & E368s).
pose proof NINV as (NCL & _ & _ & _ & NVO & _).
cps_norm. unfold IMG_TOP_B in *. cps_hide.

destruct (nbe_f32_win m (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 P2 ltac:(clear - JL1 SUB; lia)) as (EX1 & EX2 & EX3). clear P2.
replace (ST + 32 + 4 * Z.of_nat (Z.to_nat (334 + 40 * sub))) with (ST + 1368 + 160 * sub) in EX2, EX3 by (clear - SUB; lia).
change (4 * Z.of_nat 40) with 160 in EX3.
remember (firstn (Z.to_nat (334 + 40 * sub)) (j_excbuf j)) as ex1 eqn:EEX1.
remember (firstn 40 (skipn (Z.to_nat (334 + 40 * sub)) (j_excbuf j))) as exw eqn:EEXW.
remember (skipn (Z.to_nat (334 + 40 * sub) + 40) (j_excbuf j)) as ex3 eqn:EEX3.
assert (LEX1 : Z.of_nat (length ex1) = 334 + 40 * sub) by (subst ex1; rewrite length_firstn; clear - JL1 SUB; lia).
assert (LEXW : length exw = 40%nat) by (subst exw; rewrite length_firstn, length_skipn; clear - JL1 SUB; lia).
assert (LEX3 : Z.of_nat (length ex3) = 126 - 40 * sub) by (subst ex3; rewrite length_skipn; clear - JL1 SUB; lia).
clear EEX1 EEXW EEX3.
assert (OBX : aobj bsegs m (ST + 1368 + 160 * sub) 160)
by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub bsegs m ST 2968 (ST + 1368 + 160 * sub) 160 ACS ltac:(clear - SUB; lia) ltac:(clear - SUB; lia))]).
assert (XSH : ST + 1368 + 160 * sub + 160 <= 2147450880 \/ 17594333495296 <= ST + 1368 + 160 * sub) by (pose proof (SSH : _ \/ _) as U; clear - U SUB; lia).
assert (XFA : ST + 1368 + 160 * sub + 160 <= FF \/ FF + 2048 <= ST + 1368 + 160 * sub) by (pose proof (SFA : _ \/ _) as U; clear - U SUB; lia).
assert (ISV2 : nb_isave_ptr OUT st = 0 \/ 0 < nb_isave_ptr OUT st /\ nb_isave_ptr OUT st + 160 * sub < 2^63).
{ destruct ISK as [(_ & ->) | (kis & _ & -> & K1 & K2)]; [left; reflexivity| right]. clear - K1 K2 OLO LOU SPH O4 OTOP SUB. unfold IMG_TOP_B in *. lia. }
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
cps_seg (nbe_h1 usp lo ST FF SF (nb_isave_ptr OUT st) sub (ST + 1368 + 160 * sub) exw (f_exc32 ff) (f_innov ff)
(x_gp X) (x_tp X) xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6
(sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s))) Fx fc m
SL ltac:(cbn; exact E264s) ltac:(cbn; reflexivity) ltac:(cbn; exact E232s)
eq_refl SUB EX2 LEXW OBX S8 SPOS XSH ltac:(unfold IMG_TOP_B in *; lia)
FFe FL6 FFi FL5 F0 F64 FLO FTOP FSH XFA ltac:(clear - SLO SUB; lia) STK0 ltac:(clear - LOU; lia) SPH LOS CC0 MI0 FRM).
destruct POST as (m1 & F1 & fc1 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xw1 & -> & FRM1 & MU1 & WM1 & MI1 & EXW1 & LXW1).
clear EX2 OBX CC0 FRM.
assert (ART1 : ART RT Σ m1).
{ apply (af_frame RT AF Σ m m1 lo ART0 LOWS); [| exact WM1]. intros a Ha; apply MU1; cbn [outside].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin SUB; lia]| exact I]. }
cps_pf_seg m m1 MU1.
clear ART0. nbe_seg_tr m m1 MU1 WM1. try match goal with MI : mem_inv bsegs m |- _ => clear MI end.

pose proof (af_client_consts RT AF Σ m1 ART1) as CC1.
destruct ISK as [(ISN & ISP0) | (kis & ISS & ISP & K1 & K2)].
-
cps_seg (nbE_h2z2 usp ST FF (ST + 1368 + 160 * sub) (isv_cur (nb_isave_ptr OUT st) sub) (x_gp X) (x_tp X) xra t2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s3
(Z_to_bv 64 (160 * sub)) t3 t4 t5 t6 F1 fc1 m1 ltac:(rewrite ISP0; reflexivity) MI1).
destruct POST as (F2 & xb0 & xb1 & xb2 & xb3 & xb4 & xb5 & ->).
clear CC1.
pose (ows2 := ows). assert (OW2 : rw_cells bsegs m1 OUT (f32 ows2)) by exact OW. assert (LOW2 : length ows2 = nout) by exact LOW. clear OW.
remember m1 as m2 eqn:EM2. rename ART1 into ART2. rename MI1 into MI2.

apply Hk.
assert (EXB2 : rw_cells bsegs m2 (ST + 32) (f32 (ex1 ++ xw1 ++ ex3))).
{ apply nbe_f32_join_win; [exact EX1| rewrite LEX1; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by (clear; lia); exact EXW1|].
rewrite LEX1, LXW1. replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 160) by (clear; lia). exact EX3. }
pose proof (nbG_acc_pres2 Σ m2 m m2 (usp + -576) _ fh kh A 48 ART2 INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACA2.
pose proof (nbG_acc_pres2 Σ m2 m m2 (usp + -576) _ fh kh OUT (4 * Z.of_nat nout) ART2 INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACO2.
pose proof (nbG_acc_pres2 Σ m2 m m2 (usp + -576) _ fh kh STEREO 8 ART2 INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACT2.
assert (WM2E : wmono bsegs mE m2) by (apply (wmono_trans bsegs mE m m2); [exact WME| cps_wmono]).
assert (PF2E : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE m2).
{ apply (pres_fp_trans _ _ _ _ mE m m2); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_H3c.
exists Σ, F2, fc1, m2, xra, t2, xb0, xb1, xb2, xb3, xb4, xb5, xa6, xa7, s3, t3, t4, t5, t6,
(NBJ (j_last_ol_gain j) (ex1 ++ xw1 ++ ex3) (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)),
ows2, sws, s, ff, bp.
split; [eassumption|]. split; [exact FRM1|].
split.
{ unfold nbctx. split; [exact MI2|]. split; [exact STK0|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXB2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split.
{ unfold nb_junk_ok. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [rewrite !length_app; clear - LXW1 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact JL12| exact JL13]. }
split; [exact CBOK|]. split; [exact NINV|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB m2 D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OW2|]. split; [exact LOW2|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SL SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ m2 ART2)|]. split; [exact (AF_LIB Σ m2 ART2)|]. split; [reflexivity| exact JISV]. }
split; [exact SLE|]. split; [exact SAT|]. split; [exact EMO|]. split; [exact BP'|].
split; [exact OLP|]. split; [exact SUB|].
split; [exact (conj ART2 (conj (conj ACO2 (conj ACA2 ACT2)) (conj WM2E PF2E)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
-
assert (ISNZ : nb_isave_ptr OUT st <> 0) by (rewrite ISP; clear - OTOP K1; unfold IMG_TOP_B in *; lia).
destruct (nbe_f32_win m1 OUT ows (Z.to_nat (kis + 40 * sub)) 40 OW ltac:(clear - LOW K1 K2 SUB; lia)) as (OW1 & OWW & OW3). clear OW.
replace (OUT + 4 * Z.of_nat (Z.to_nat (kis + 40 * sub))) with (nb_isave_ptr OUT st + 160 * sub) in OWW, OW3 by (rewrite ISP; clear - K1 SUB; lia).
change (4 * Z.of_nat 40) with 160 in OW3.
remember (firstn (Z.to_nat (kis + 40 * sub)) ows) as ow1 eqn:EOW1.
remember (firstn 40 (skipn (Z.to_nat (kis + 40 * sub)) ows)) as yw eqn:EYW.
remember (skipn (Z.to_nat (kis + 40 * sub) + 40) ows) as ow3 eqn:EOW3.
assert (LOW1 : Z.of_nat (length ow1) = kis + 40 * sub) by (subst ow1; rewrite length_firstn; clear - LOW K1 K2 SUB; lia).
assert (LYW : length yw = 40%nat) by (subst yw; rewrite length_firstn, length_skipn; clear - LOW K1 K2 SUB; lia).
assert (LOW3 : Z.of_nat (length ow3) = Z.of_nat nout - kis - 40 * sub - 40) by (subst ow3; rewrite length_skipn; clear - LOW K1 K2 SUB; lia).
clear EOW1 EYW EOW3.
assert (OFFO : forall i, 0 <= i < 4 * Z.of_nat nout -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -576, usp)] (shad (OUT + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 Σ m1 m m1 (usp + -576) _ fh kh OUT (4 * Z.of_nat nout) ART1 INFH FHO1 FHO2 PF OFFO (proj1 NACC)) as ACO1.
assert (HYW : nb_isave_ptr OUT st <> 0 ->
rw_cells bsegs m1 (nb_isave_ptr OUT st + 160 * sub) (f32 yw) /\ length yw = 40%nat /\ aobj bsegs m1 (nb_isave_ptr OUT st + 160 * sub) 160
/\ (nb_isave_ptr OUT st + 160 * sub) mod 4 = 0
/\ (nb_isave_ptr OUT st + 160 * sub + 160 <= SH_LO \/ SH_HI <= nb_isave_ptr OUT st + 160 * sub) /\ IMG_TOP_B <= nb_isave_ptr OUT st + 160 * sub
/\ (nb_isave_ptr OUT st + 160 * sub + 160 <= FF \/ FF + 2048 <= nb_isave_ptr OUT st + 160 * sub) /\ nb_isave_ptr OUT st + 160 * sub + 160 <= lo).
{ intros _. rewrite ISP in *. split; [exact OWW|]. split; [exact LYW|].
split; [split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub bsegs m1 OUT (4 * Z.of_nat nout) (OUT + 4 * kis + 160 * sub) 160 ACO1 ltac:(clear - K1 SUB; lia) ltac:(clear - K1 K2 SUB; lia))]|].
split; [clear - O4; Z.div_mod_to_equations; lia|].
split; [pose proof (OSH : _ \/ _) as U; clear - U K1 K2 SUB; unfold SH_LO, SH_HI; lia|]. split; [clear - OTOP K1 SUB; unfold IMG_TOP_B in *; lia|].
split; [pose proof (OFA : _ \/ _) as U; clear - U K1 K2 SUB; lia| clear - OLO K1 K2 SUB; lia]. }
cps_seg (nbe_h2 usp lo ST FF SF (nb_isave_ptr OUT st) sub (ST + 1368 + 160 * sub) yw (f_innov ff)
(x_gp X) (x_tp X) xra t2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s3 (Z_to_bv 64 (160 * sub)) t3 t4 t5 t6 F1 fc1 m1
ISV2 SUB HYW FFi FL5 F0 F64 FLO FTOP FSH ltac:(clear - LOU; lia) SPH LOS MI1).
destruct POST as (m2 & F2 & xb0 & xb1 & xb2 & xb3 & xb4 & xb5 & -> & MU2 & WM2 & MI2 & YW2).
destruct (YW2 ISNZ) as (yw2 & OWW2 & LYW2). clear YW2 HYW OWW CC1 ACO1 OFFO.
rewrite ISP in MU2, OWW2, OW3.
assert (ART2 : ART RT Σ m2).
{ apply (af_frame RT AF Σ m1 m2 lo ART1 LOWS); [| exact WM2]. intros a Ha; apply MU2; cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists fh, kh; split; [exact INFH| clear - Hin FHO1 FHO2 K1 K2 SUB; lia]| exact I]. }
cps_pf_seg m1 m2 MU2.
clear ART1. nbe_seg_tr m1 m2 MU2 WM2. try match goal with MI : mem_inv bsegs m1 |- _ => clear MI end.
pose (ows2 := ow1 ++ yw2 ++ ow3).
assert (OW2 : rw_cells bsegs m2 OUT (f32 ows2)).
{ apply nbe_f32_join_win; [exact OW1| rewrite LOW1; replace (OUT + 4 * (kis + 40 * sub)) with (OUT + 4 * kis + 160 * sub) by (clear; lia); exact OWW2|].
rewrite LOW1, LYW2. replace (OUT + 4 * (kis + 40 * sub) + 4 * Z.of_nat 40) with (OUT + 4 * kis + 160 * sub + 160) by (clear; lia). exact OW3. }
assert (LOW2 : length ows2 = nout) by (unfold ows2; rewrite !length_app; clear - LOW1 LYW2 LOW3; lia).
clear OW1 OWW2 OW3.

apply Hk.
assert (EXB2 : rw_cells bsegs m2 (ST + 32) (f32 (ex1 ++ xw1 ++ ex3))).
{ apply nbe_f32_join_win; [exact EX1| rewrite LEX1; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by (clear; lia); exact EXW1|].
rewrite LEX1, LXW1. replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 160) by (clear; lia). exact EX3. }
pose proof (nbG_acc_pres2 Σ m2 m m2 (usp + -576) _ fh kh A 48 ART2 INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACA2.
pose proof (nbG_acc_pres2 Σ m2 m m2 (usp + -576) _ fh kh OUT (4 * Z.of_nat nout) ART2 INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACO2.
pose proof (nbG_acc_pres2 Σ m2 m m2 (usp + -576) _ fh kh STEREO 8 ART2 INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACT2.
assert (WM2E : wmono bsegs mE m2) by (apply (wmono_trans bsegs mE m m2); [exact WME| cps_wmono]).
assert (PF2E : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE m2).
{ apply (pres_fp_trans _ _ _ _ mE m m2); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_H3c.
exists Σ, F2, fc1, m2, xra, t2, xb0, xb1, xb2, xb3, xb4, xb5, xa6, xa7, s3, t3, t4, t5, t6,
(NBJ (j_last_ol_gain j) (ex1 ++ xw1 ++ ex3) (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)),
ows2, sws, s, ff, bp.
split; [eassumption|]. split; [exact FRM1|].
split.
{ unfold nbctx. split; [exact MI2|]. split; [exact STK0|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXB2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split.
{ unfold nb_junk_ok. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [rewrite !length_app; clear - LXW1 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact JL12| exact JL13]. }
split; [exact CBOK|]. split; [exact NINV|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB m2 D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OW2|]. split; [exact LOW2|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SL SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ m2 ART2)|]. split; [exact (AF_LIB Σ m2 ART2)|]. split; [reflexivity| exact JISV]. }
split; [exact SLE|]. split; [exact SAT|]. split; [exact EMO|]. split; [exact BP'|].
split; [exact OLP|]. split; [exact SUB|].
split; [exact (conj ART2 (conj (conj ACO2 (conj ACA2 ACT2)) (conj WM2E PF2E)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
Qed.

Lemma nbE_B2 : forall (bp' sub : Z) (st : nb_state bptr) (bJ : bits_st bptr) (st1 : nb_state bptr),
(if nb_submodeID st =? 1 then exists v, voc_loop VOC_FUEL (nb_voc_offset st) olp = Some v /\ st1 = set_nb_voc_offset st (v - NB_SUBFRAME_SIZE) else st1 = st) ->
cps bsegs (at_H3c bp' sub st bJ)
(fun c => (sub < 3 /\ at_ELc RT PMc X Σ0 mE r mo olp bp' (sub + 1) st1 bJ c) \/ (sub = 3 /\ at_EXc RT PMc X Σ0 mE r mo olp bp' st1 bJ c)).
Proof.
intros bp' sub st bJ st1 EST1 T c Hc Hk.
destruct Hc as (Σ & Fx & fc & m & xra & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & bp
& Hc0 & FRM & CTX & SLE & SAT & EMO & BP' & OLP & SUB & MEM & SIG).
destruct MEM as (ART0 & NACC & WM0 & PF).
destruct SIG as (LV & FRS & SP0 & CR & POI).
destruct CTX as (MI0 & STK0 & NBP & JOK & CBOK & NINV & BREP & BOK & BSZ & OW & LOW & SW & LSW & (SL & SV) & FFA & FFOK & (rest & SH) & CC & LC & JEXC & JISV).
unfold slots_J in SL.
pose proof NXOK as (U32 & SPH & LOS & LOU & F0 & F64 & ESF & FLO & FTOP & FSH & SF0 & SF1 & SFLO & S8 & SPOS & SLO & SSH & SIMG & O4 & OTOP & OLO & NOUT & OSH
& A8 & ATOP & ALO & ASH & D0 & DLO & DSZ & STE4 & STETOP & STELO & STESH & ISVX & SOA & SAA & SDA & SSTA & SFA & SSFA & OAA & ODA & OSTA & OFA & OSFA
& ADA & ASTEA & AFFA & ASFA & DSTA & DFA & DSFA & STEFA & STESFA & FSFA).
pose proof NSIG as (NFR & NLS & NLD & PD1 & PD2 & PDS & NFH & FHO1 & FHO2 & FHA1 & FHA2 & FHS1 & FHS2 & NPOIS & NLOW & NROOM & NTOP).
destruct NBP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
destruct FFA as (FF0 & FFp & FFg & FFl & FFq & FFk & FFi & FFe & FFj & FFiq).
assert (INL : In (ST, NBSTATE_SIZEOF) (rt_live RT Σ)) by (rewrite LV; exact NLS).
assert (INF : In (FF, NBD_FCLASS) (rt_frames RT Σ)) by (rewrite FRS, NFR; left; reflexivity).
assert (INFH : In (fh, kh) (rt_frames RT Σ)) by (rewrite FRS, NFR; right; exact NFH).
assert (INPD : In (PD, ND) (rt_live RT Σ)) by (rewrite LV; exact NLD).
assert (ESF8 : FF / 8 + SHB = SF) by (rewrite ESF, Z.shiftr_div_pow2 by lia; reflexivity).
assert (SHD1 : shad FF = SF) by (unfold shad; exact ESF8).
assert (SHD2 : shad (FF + 2048) = SF + 256) by (unfold shad; rewrite <- ESF8; clear - F64; Z.div_mod_to_equations; lia).
destruct (af_acc_live RT AF Σ m ST NBSTATE_SIZEOF ART0 INL) as (WRS & ACS).
pose proof (af_live_small RT AF Σ m ST NBSTATE_SIZEOF ART0 INL ltac:(unfold NBSTATE_SIZEOF; lia)) as STTOP.
assert (LOWS : rt_sp0 RT Σ - STACK_WIN <= lo) by (rewrite SP0; exact NLOW).
assert (POA : pois_above (rt_pois RT Σ) (usp + -576)) by (rewrite POI; replace (usp + -576) with (usp - NBD_FRAME) by (unfold NBD_FRAME; lia); exact NPOIS).
change hidp with hid in *.
unfold NBSTATE_SIZEOF, NBD_FRAME, NBD_CALLEE_STACK, RT_STACK, BITS_SIZEOF in *.
assert (OBS : aobj bsegs m ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS]).

assert (ISK : (nb_innov_save st = None /\ nb_isave_ptr OUT st = 0)
\/ (exists kis, nb_innov_save st = Some kis /\ nb_isave_ptr OUT st = OUT + 4 * kis /\ 160 <= kis /\ kis + 160 <= Z.of_nat nout)).
{ unfold nb_isave_ptr. pose proof NINV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NI12). rewrite JISV in NI12 |- *.
destruct (nb_innov_save (x_st0 X)) as [kis|]; [right; exists kis; split; [reflexivity|]; split; [reflexivity|]; split; [exact NI12| exact ISVX]| left; split; reflexivity]. }
assert (ISB : 0 <= nb_isave_ptr OUT st < 2^63).
{ destruct ISK as [(_ & ->) | (kis & _ & -> & K1 & K2)]; [lia|]. clear - K1 K2 OLO LOU SPH O4 OTOP. unfold IMG_TOP_B in *. lia. }
rewrite JEXC in P3.

pose proof (PF : nbE_keep (rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE m)) as PFE. clear PF.
pose proof (WM0 : nbE_keep (wmono bsegs mE m)) as WME. clear WM0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -576, usp)] m) as PF.
pose proof (fun a0 => aclient_split RT AF Σ m (usp + -576) a0 ART0) as SPL.

destruct BREP as ((rj & Lrj & BOBJ) & (bs & BDAT & Hbs) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bs)) in BDAT.
clear LC CC.
pose proof JOK as (JL1 & JL2 & JL3 & JL4 & JL5 & JL6 & JL7 & JL8 & JL9 & JL10 & (JL11a & JL11b) & JL12 & JL13).
pose proof FFOK as (FL1 & FL2 & FL3 & FL4 & FL5 & FL6 & FL7 & FL8).
assert (LBS : Z.of_nat (length bs) = sb_buf_size bJ)
by (pose proof BOK as BOK'; unfold bits_ok in BOK'; rewrite Hbs, zlength_map_unsigned in BOK'; clear - BOK'; lia).
assert (DLOb : D + Z.of_nat (length bs) <= lo) by (rewrite LBS, BSZ, <- DSZ; exact DLO).
assert (DPD : D + Z.of_nat (length bs) <= PD + ND) by (rewrite LBS, BSZ, <- DSZ; exact PD2).
assert (DSZb : Z.of_nat (length bs) = x_dsz X) by (rewrite LBS, BSZ, <- DSZ; reflexivity).
pose proof SLE as (E0s & E24s & E32s & E40s & E48s & E56s & E64s & E72s & E80s & E88s & E96s & E104s & E120s & E128s & E136s & E144s & E152s & E160s & E168s & E176s
& E184s & E192s & E200s & E208s & E216s & E232s & E240s & E256s & E264s & E272s & E280s & E288s & E296s & E304s & E312s & E320s & E328s & E336s & E344s & E368s).
pose proof NINV as (NCL & _ & _ & _ & NVO & _).
cps_norm. unfold IMG_TOP_B in *. cps_hide.

pose proof (smrec_facts mo r SAT) as (_ & MO18 & _).
cps_seg (nbe_h3 usp lo ST FF SF (nb_isave_ptr OUT st) sub (ST + 1368 + 160 * sub) mo st (j_pad1 j) (x_gp X) (x_tp X) xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (160 * sub)) t3 t4 t5 t6
(sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s))) Fx fc m
SL ltac:(cbn; exact E344s) ltac:(cbn; reflexivity) ltac:(cbn; exact E264s) ltac:(cbn; exact E168s) ltac:(cbn; exact E176s)
P15 EMO ltac:(clear - MO18; lia) SUB OBS S8 SPOS SLO SSH STK0 ltac:(clear - LOU; lia) SPH LOS MI0).
destruct POST as (m1 & xra1 & rt0 & rt1 & rt2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & rt3 & rt4 & rt5 & rt6 & MU1 & WM1 & MI1 & ST1 & CASES).
clear SL STK0 OBS.
assert (ART1 : ART RT Σ m1).
{ apply (af_frame RT AF Σ m m1 lo ART0 LOWS); [| exact WM1]. intros a Ha; apply MU1; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m m1 MU1.
clear ART0. nbe_seg_tr m m1 MU1 WM1. try match goal with MI : mem_inv bsegs m |- _ => clear MI end.
destruct CASES as [(MO1 & SL1 & [(SUB3 & ->) | (SUB3 & ->)]) | (MO1 & SL1 & ->)].
-
assert (ST1E : st1 = st) by (rewrite EMO in EST1; destruct (Z.eqb_spec mo 1) as [E|_]; [exfalso; exact (MO1 E)| exact EST1]).
subst st1. rename m1 into mF. rename ART1 into ARTF. rename MI1 into MIF. rename ST1 into STF. rename SL1 into SLF. rename P2 into EXBF.
set (jF := j). set (owsF := ows). set (ffF := ff).
set (sF := sset 264 (Z_to_bv 64 (40 * (sub + 1))) (sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s)))) in SLF.
assert (JOKF : nb_junk_ok jF) by exact JOK. assert (NINVF : nb_inv st) by exact NINV.
assert (OWF : rw_cells bsegs mF OUT (f32 owsF)) by exact OW. assert (LOWF : length owsF = nout) by exact LOW.
assert (JEXCF : j_exc jF = ST + 1368) by exact JEXC. assert (JISVF : nb_innov_save st = nb_innov_save (x_st0 X)) by exact JISV.
assert (EMOF : nb_submodeID st = mo) by exact EMO.

apply Hk. left. split; [clear - SUB3; lia|].
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh A 48 ARTF INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACAF.
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh OUT (4 * Z.of_nat nout) ARTF INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACOF.
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh STEREO 8 ARTF INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACTF.
assert (WMFE : wmono bsegs mE mF) by (apply (wmono_trans bsegs mE m mF); [exact WME| cps_wmono]).
assert (PFFE : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE mF).
{ apply (pres_fp_trans _ _ _ _ mE m mF); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_ELc. exists Σ. split; [| exact (conj LV (conj FRS (conj SP0 (conj CR POI))))].
eapply ASTA_conseq; [eassumption|]. intros ms <-. split.
2:{ cbn [ms_mem]. exact (conj ARTF (conj (conj ACOF (conj ACAF ACTF)) (conj WMFE PFFE))). }
unfold at_EL. do 21 eexists. exists jF, owsF, sws, sF, ffF.
split; [reflexivity|]. split; [exact FRM|].
split.
{ unfold nbctx. split; [exact MIF|]. split; [exact STF|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXBF|]. split; [rewrite JEXCF; exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split; [exact JOKF|].
split; [exact CBOK|]. split; [exact NINVF|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB mF D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OWF|]. split; [exact LOWF|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SLF SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ mF ARTF)|]. split; [exact (AF_LIB Σ mF ARTF)|]. split; [exact JEXCF| exact JISVF]. }
split; [unfold slots_EL; cbn; repeat split; first [assumption | reflexivity]|].
split; [exact SAT|]. split; [exact EMOF|]. split; [exact BP'|]. split; [exact OLP| clear - SUB SUB3; lia].
-
assert (ST1E : st1 = st) by (rewrite EMO in EST1; destruct (Z.eqb_spec mo 1) as [E|_]; [exfalso; exact (MO1 E)| exact EST1]).
subst st1. rename m1 into mF. rename ART1 into ARTF. rename MI1 into MIF. rename ST1 into STF. rename SL1 into SLF. rename P2 into EXBF.
set (jF := j). set (owsF := ows). set (ffF := ff).
set (sF := sset 264 (Z_to_bv 64 (40 * (sub + 1))) (sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s)))) in SLF.
assert (JOKF : nb_junk_ok jF) by exact JOK. assert (NINVF : nb_inv st) by exact NINV.
assert (OWF : rw_cells bsegs mF OUT (f32 owsF)) by exact OW. assert (LOWF : length owsF = nout) by exact LOW.
assert (JEXCF : j_exc jF = ST + 1368) by exact JEXC. assert (JISVF : nb_innov_save st = nb_innov_save (x_st0 X)) by exact JISV.
assert (EMOF : nb_submodeID st = mo) by exact EMO.

apply Hk. right. split; [exact SUB3|].
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh A 48 ARTF INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACAF.
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh OUT (4 * Z.of_nat nout) ARTF INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACOF.
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh STEREO 8 ARTF INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACTF.
assert (WMFE : wmono bsegs mE mF) by (apply (wmono_trans bsegs mE m mF); [exact WME| cps_wmono]).
assert (PFFE : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE mF).
{ apply (pres_fp_trans _ _ _ _ mE m mF); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_EXc. do 22 eexists. exists jF, owsF, sws, sF, ffF.
split; [eassumption|]. split; [exact FRM|].
split.
{ unfold nbctx. split; [exact MIF|]. split; [exact STF|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXBF|]. split; [rewrite JEXCF; exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split; [exact JOKF|].
split; [exact CBOK|]. split; [exact NINVF|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB mF D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OWF|]. split; [exact LOWF|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SLF SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ mF ARTF)|]. split; [exact (AF_LIB Σ mF ARTF)|]. split; [exact JEXCF| exact JISVF]. }
split; [unfold slots_EL; cbn; repeat split; first [assumption | reflexivity | rewrite SUB3; reflexivity]|].
split; [cbn; reflexivity|].
split; [exact SAT|]. split; [exact EMOF|]. split; [exact BP'|].
split; [exact (conj ARTF (conj (conj ACOF (conj ACAF ACTF)) (conj WMFE PFFE)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
-
assert (LB0 : sm_lbr_pitch (smr_sm r) = 0) by (rewrite MO1 in SAT; cbn in SAT; injection SAT as E; rewrite <- E; reflexivity).
assert (OLP1 : 17 <= olp <= 144) by (destruct OLP as [(HL & _)|(_ & HO)]; [rewrite LB0 in HL; discriminate HL| exact HO]).
destruct (nbe_f32_win m1 (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 P2 ltac:(clear - JL1 SUB; lia)) as (EX1 & EX2 & EX3). clear P2.
replace (ST + 32 + 4 * Z.of_nat (Z.to_nat (334 + 40 * sub))) with (ST + 1368 + 160 * sub) in EX2, EX3 by (clear - SUB; lia).
change (4 * Z.of_nat 40) with 160 in EX3.
remember (firstn (Z.to_nat (334 + 40 * sub)) (j_excbuf j)) as ex1 eqn:EEX1.
remember (firstn 40 (skipn (Z.to_nat (334 + 40 * sub)) (j_excbuf j))) as exw eqn:EEXW.
remember (skipn (Z.to_nat (334 + 40 * sub) + 40) (j_excbuf j)) as ex3 eqn:EEX3.
assert (LEX1 : Z.of_nat (length ex1) = 334 + 40 * sub) by (subst ex1; rewrite length_firstn; clear - JL1 SUB; lia).
assert (LEXW : length exw = 40%nat) by (subst exw; rewrite length_firstn, length_skipn; clear - JL1 SUB; lia).
assert (LEX3 : Z.of_nat (length ex3) = 126 - 40 * sub) by (subst ex3; rewrite length_skipn; clear - JL1 SUB; lia).
clear EEX1 EEXW EEX3.
pose proof (proj2 EX2) as WRX. rewrite cells_size_f32, LEXW in WRX. change (Z.of_nat (4 * 40)) with 160 in WRX. clear EX2.
destruct (af_acc_live RT AF Σ m1 ST 2968 ART1 INL) as (_ & ACS1).
assert (CD4 : checked_dst RT Σ m1 (Z_to_bv 64 (usp + -576)) (ST + 1368 + 160 * sub) 160).
{ split; [intros _; split| split; [| exact WRX]].
- exact (acc_sub bsegs m1 ST 2968 (ST + 1368 + 160 * sub) 160 ACS1 ltac:(clear - SUB; lia) ltac:(clear - SUB; lia)).
- left. exists ST, 2968. split; [exact INL| clear - SUB; lia].
- intros i Hi. right; right; left. exists ST, 2968. split; [exact INL| clear - SUB Hi; lia]. }
cps_rt (MST Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (ST + 1368 + 160 * sub) 160 (Z_to_bv 8 0) lo).
{ clear - SPOS SLO LOU NTOP SUB. lia. }
{ cps_callok. }
intros c2 Hc2.
clear CD4 ACS1.
nbe_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
nbe_trp PRES2.
cps_pf_pres PRES2.
clear ART1 MI1 ST1 PRES2.
assert (EXZ : rw_cells bsegs m2 (ST + 1368 + 160 * sub) (f32 (repeat (Z_to_bv 64 0) 40))).
{ split; [split; [apply cells_wf_f32 | replace (cells_bytes (f32 (repeat (Z_to_bv 64 0) 40))) with (repeat (Z_to_bv 8 0) (Z.to_nat 160)) by (vm_compute; reflexivity); exact BY2]|].
rewrite cells_size_f32, repeat_length. exact (wr_at_transport bsegs m1 m2 _ _ WRX WM2). }
clear BY2 WRX.

destruct (af_acc_live RT AF Σ m2 ST 2968 ART2 INL) as (_ & ACS2).
assert (OBS2 : aobj bsegs m2 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS2]).
assert (OBX2 : aobj bsegs m2 (ST + 1368 + 160 * sub) 160)
by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub bsegs m2 ST 2968 (ST + 1368 + 160 * sub) 160 ACS2 ltac:(clear - SUB; lia) ltac:(clear - SUB; lia))]).
clear ACS2.
cps_seg (nbe_i1 usp lo ST FF SF olp (nb_isave_ptr OUT st) sub (ST + 1368 + 160 * sub) st (j_pad2 j) (repeat (Z_to_bv 64 0) 40) (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s))) _ _ m2
SL1 ltac:(cbn; exact E72s) ltac:(cbn; exact E208s) ltac:(cbn; exact E320s) ltac:(cbn; exact E312s) ltac:(cbn; reflexivity) eq_refl SUB
P19 NVO OLP1 OBS2 S8 SPOS SLO SSH EXZ (repeat_length _ _) OBX2 ST2 ltac:(clear - LOU; lia) SPH LOS MI2).
destruct POST as (m3 & qt0 & qa0 & qa3 & qa4 & qa5 & qa6 & qa7 & qt3 & qt4 & qt5 & qt6 & vfin & xw3 & -> & MU3 & WM3 & MI3 & VOCL & TAIL3 & EXW3 & LXW3).
clear OBS2 OBX2 EXZ P19.
assert (ART3 : ART RT Σ m3).
{ apply (af_frame RT AF Σ m2 m3 lo ART2 LOWS); [| exact WM3]. intros a Ha; apply MU3; cbn [outside].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin SUB; lia]|].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin; lia]| exact I]. }
cps_pf_seg m2 m3 MU3.
clear ART2. nbe_seg_tr m2 m3 MU3 WM3. try match goal with MI : mem_inv bsegs m2 |- _ => clear MI end.

clear Hc. rename Hc1 into Hc.
destruct xw3 as [|x3 rest3]; [cbn in LXW3; discriminate LXW3|].
pose proof P18 as P18'. destruct (j_voc j) as [|v1 [|v2 [|v3 [|]]]] eqn:EV; cbn [length] in JL12; try discriminate JL12. clear P18'.
destruct (af_acc_live RT AF Σ m3 ST 2968 ART3 INL) as (_ & ACS3).
assert (OBS3 : aobj bsegs m3 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS3]).
assert (OBX3 : aobj bsegs m3 (ST + 1368 + 160 * sub) 160)
by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub bsegs m3 ST 2968 (ST + 1368 + 160 * sub) 160 ACS3 ltac:(clear - SUB; lia) ltac:(clear - SUB; lia))]).
clear ACS3.
pose proof (af_client_consts RT AF Σ m3 ART3) as CC3.
assert (XSH3 : ST + 1368 + 160 * sub + 160 <= SH_LO \/ SH_HI <= ST + 1368 + 160 * sub) by (pose proof (SSH : _ \/ _) as U; clear - U SUB; unfold SH_LO, SH_HI; lia).
assert (XFA3 : ST + 1368 + 160 * sub + 160 <= FF \/ FF + 2048 <= ST + 1368 + 160 * sub) by (pose proof (SFA : _ \/ _) as U; clear - U SUB; lia).
replace (ST + 1368 + 160 * sub) with (ST + 1368 + 160 * sub + 0) in EXW3 by lia.
cps_seg (voc_loop_walk ST (ST + 1368 + 160 * sub) FF lo usp (f_innov ff) m3
(Z_to_bv 64 RA_nbe_mset4) (Z_to_bv 64 (usp + -576)) (x_gp X) (x_tp X) (Z_to_bv 64 (ST + 2248)) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) (Z_to_bv 64 1) s3
(Z_to_bv 64 (isv_cur (nb_isave_ptr OUT st) sub)) (Z_to_bv 64 (ST + 1368 + 160 * sub)) qt3 qt4 qt5 qt6
OBX3 ltac:(clear - S8; Z.div_mod_to_equations; lia) ltac:(clear - SPOS SUB; lia) XSH3 ltac:(unfold IMG_TOP_B in *; lia) OBS3 S8 SPOS SSH ltac:(clear - SUB; lia) ltac:(clear - SUB; lia)
FL5 FTOP FSH XFA3 SFA SLO FLO ltac:(clear - LOU; lia) SPH LOS
rest3 [] x3 v1 v2 v3 0 qt0 qa0 qa3 qa4 qa5 qa6 qa7 _ _ m3
ltac:(cbn [length] in LXW3 |- *; lia) eq_refl FRM (munch_refl _ m3)
ltac:(cbn; unfold SH_LO, SH_HI in *; pose proof (SSH : _ \/ _) as U; clear - U SUB; lia) (wmono_refl bsegs m3) MI3
(rw_cells_nil bsegs m3 (ST + 1368 + 160 * sub) ltac:(clear - SPOS SLO LOU NTOP SUB; lia)) EXW3 P18 FFi).
destruct POST as (m4 & F4 & fc4 & pt0 & pa0 & pa1 & pa2 & pa3 & pa4 & pa5 & pa6 & pa7 & xw4 & vs4 & -> & FRM4 & MU4 & WM4 & MI4 & EXW4 & LXW4 & VS4 & LVS4).
clear OBS3 OBX3 CC3 XSH3 EXW3 P18 FRM.
assert (ART4 : ART RT Σ m4).
{ apply (af_frame RT AF Σ m3 m4 lo ART3 LOWS); [| exact WM4]. intros a Ha; apply MU4; cbn [outside].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin SUB; lia]|].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin; lia]| exact I]. }
cps_pf_seg m3 m4 MU4.
clear ART3. nbe_seg_tr m3 m4 MU4 WM4. try match goal with MI : mem_inv bsegs m3 |- _ => clear MI end.

cps_seg (nbe_bk usp lo ST FF sub (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s))) _ _ m4
SL1 ltac:(cbn; reflexivity) ltac:(cbn; exact E264s) ltac:(cbn; exact E168s) ltac:(cbn; exact E176s) SUB ST2 ltac:(clear - LOU; lia) SPH LOS MI4).
destruct POST as (m5 & pb2 & pb0 & MU5 & WM5 & MI5 & ST5 & SL5 & BK).
clear SL1 ST2.
assert (ART5 : ART RT Σ m5).
{ apply (af_frame RT AF Σ m4 m5 lo ART4 LOWS); [| exact WM5]. intros a Ha; apply MU5; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m4 m5 MU5.
clear ART4. nbe_seg_tr m4 m5 MU5 WM5. try match goal with MI : mem_inv bsegs m4 |- _ => clear MI end.

rewrite EMO, MO1 in EST1. cbn [Z.eqb Pos.eqb] in EST1. destruct EST1 as (v & VOC1 & ->). rewrite VOCL in VOC1. injection VOC1 as <-.
destruct (voc_loop_inv (nb_voc_offset st) olp NVO OLP1) as (v' & VOCv & VB). rewrite VOCL in VOCv. injection VOCv as <-.

assert (EXBF : rw_cells bsegs m5 (ST + 32) (f32 (ex1 ++ xw4 ++ ex3))).
{ apply nbe_f32_join_win; [exact EX1| rewrite LEX1; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by (clear; lia); exact EXW4|].
rewrite LEX1, LXW4. replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 160) by (clear; lia). exact EX3. }
clear EX1 EXW4 EX3.
rename m5 into mF. rename ART5 into ARTF. rename MI5 into MIF. rename ST5 into STF. rename SL5 into SLF. rename FRM4 into FRM.
rename VS4 into P18. rename TAIL3 into P19.
set (jF := NBJ (j_last_ol_gain j) (ex1 ++ xw4 ++ ex3) (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) vs4 (j_pad2 j)).
set (owsF := ows). set (ffF := ff).
set (sF := sset 264 (Z_to_bv 64 (40 * (sub + 1))) (sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s)))) in SLF.
assert (JOKF : nb_junk_ok jF).
{ unfold nb_junk_ok, jF. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [rewrite !length_app; clear - LXW4 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact LVS4| exact JL13]. }
assert (NINVF : nb_inv (set_nb_voc_offset st (vfin - NB_SUBFRAME_SIZE))).
{ pose proof NINV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold nb_inv. cbn.
exact (conj I1 (conj I2 (conj I3 (conj I4 (conj VB (conj I6 (conj I7 (conj I8 (conj I9 (conj I10 (conj I11 I12))))))))))). }
assert (OWF : rw_cells bsegs mF OUT (f32 owsF)) by exact OW. assert (LOWF : length owsF = nout) by exact LOW.
assert (JEXCF : j_exc jF = ST + 1368) by reflexivity.
assert (JISVF : nb_innov_save (set_nb_voc_offset st (vfin - NB_SUBFRAME_SIZE)) = nb_innov_save (x_st0 X)) by exact JISV.
assert (EMOF : nb_submodeID (set_nb_voc_offset st (vfin - NB_SUBFRAME_SIZE)) = mo) by exact EMO.
destruct BK as [(SUB3 & ->) | (SUB3 & ->)].
+ idtac.

apply Hk. left. split; [clear - SUB3; lia|].
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh A 48 ARTF INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACAF.
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh OUT (4 * Z.of_nat nout) ARTF INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACOF.
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh STEREO 8 ARTF INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACTF.
assert (WMFE : wmono bsegs mE mF) by (apply (wmono_trans bsegs mE m mF); [exact WME| cps_wmono]).
assert (PFFE : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE mF).
{ apply (pres_fp_trans _ _ _ _ mE m mF); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_ELc. exists Σ. split; [| exact (conj LV (conj FRS (conj SP0 (conj CR POI))))].
eapply ASTA_conseq; [eassumption|]. intros ms <-. split.
2:{ cbn [ms_mem]. exact (conj ARTF (conj (conj ACOF (conj ACAF ACTF)) (conj WMFE PFFE))). }
unfold at_EL. do 21 eexists. exists jF, owsF, sws, sF, ffF.
split; [reflexivity|]. split; [exact FRM|].
split.
{ unfold nbctx. split; [exact MIF|]. split; [exact STF|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXBF|]. split; [rewrite JEXCF; exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split; [exact JOKF|].
split; [exact CBOK|]. split; [exact NINVF|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB mF D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OWF|]. split; [exact LOWF|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SLF SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ mF ARTF)|]. split; [exact (AF_LIB Σ mF ARTF)|]. split; [exact JEXCF| exact JISVF]. }
split; [unfold slots_EL; cbn; repeat split; first [assumption | reflexivity]|].
split; [exact SAT|]. split; [exact EMOF|]. split; [exact BP'|]. split; [exact OLP| clear - SUB SUB3; lia].
+ idtac.

apply Hk. right. split; [exact SUB3|].
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh A 48 ARTF INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACAF.
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh OUT (4 * Z.of_nat nout) ARTF INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACOF.
pose proof (nbG_acc_pres2 Σ mF m mF (usp + -576) _ fh kh STEREO 8 ARTF INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACTF.
assert (WMFE : wmono bsegs mE mF) by (apply (wmono_trans bsegs mE m mF); [exact WME| cps_wmono]).
assert (PFFE : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE mF).
{ apply (pres_fp_trans _ _ _ _ mE m mF); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_EXc. do 22 eexists. exists jF, owsF, sws, sF, ffF.
split; [eassumption|]. split; [exact FRM|].
split.
{ unfold nbctx. split; [exact MIF|]. split; [exact STF|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXBF|]. split; [rewrite JEXCF; exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split; [exact JOKF|].
split; [exact CBOK|]. split; [exact NINVF|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB mF D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OWF|]. split; [exact LOWF|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SLF SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ mF ARTF)|]. split; [exact (AF_LIB Σ mF ARTF)|]. split; [exact JEXCF| exact JISVF]. }
split; [unfold slots_EL; cbn; repeat split; first [assumption | reflexivity | rewrite SUB3; reflexivity]|].
split; [cbn; reflexivity|].
split; [exact SAT|]. split; [exact EMOF|]. split; [exact BP'|].
split; [exact (conj ARTF (conj (conj ACOF (conj ACAF ACTF)) (conj WMFE PFFE)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
Qed.

Lemma nbE_iter : forall (bp sub : Z) (st : nb_state bptr) (b : bits_st bptr) (st1 : nb_state bptr) (b1 : bits_st bptr),
0 <= sub < 4 -> subframe_pure (smr_sm r) olp sub st b = Some (st1, b1) ->
cps bsegs (at_ELc RT PMc X Σ0 mE r mo olp bp sub st b)
(fun c => exists bp', 17 <= bp' <= 144 /\ ((sub < 3 /\ at_ELc RT PMc X Σ0 mE r mo olp bp' (sub + 1) st1 b1 c)
\/ (sub = 3 /\ at_EXc RT PMc X Σ0 mE r mo olp bp' st1 b1 c))).
Proof.
intros bp sub st b st1 b1 SUB SFP.
unfold subframe_pure in SFP.
assert (LTKx : exists k, sm_ltp_unquant (smr_sm r) = Some k)
by (destruct (sm_ltp_unquant (smr_sm r)); [eexists; reflexivity| discriminate SFP]).
destruct LTKx as (k & LTK). rewrite LTK in SFP.
assert (INKx : exists ki, sm_innovation_unquant (smr_sm r) = Some ki)
by (destruct (sm_innovation_unquant (smr_sm r)); [eexists; reflexivity| discriminate SFP]).
destruct INKx as (ki & INK). rewrite INK in SFP.
cbv zeta in SFP.
assert (EB : (if nb_submodeID st =? 1 then exists v, voc_loop VOC_FUEL (nb_voc_offset st) olp = Some v /\ st1 = set_nb_voc_offset st (v - NB_SUBFRAME_SIZE) else st1 = st)
/\ b1 = nbE_bJ k ki b).
{ destruct (nb_submodeID st =? 1).
- destruct (voc_loop VOC_FUEL (nb_voc_offset st) olp) as [v|]; [| discriminate SFP]. injection SFP as <- <-. split; [exists v; split; reflexivity| reflexivity].
- injection SFP as <- <-. split; reflexivity. }
destruct EB as (EST1 & ->).
intros T c Hc Hk.
apply (X0zy.nbE_A RT AF MST AF_LIB PMc FDO MSTa X NXOK TP Σ0 fr0 PD ND fh kh NSIG mE r mo olp LTP INN bp sub st b k ki SUB LTK INK T c Hc). intros c' (bp' & HJ).
assert (BP' : 17 <= bp' <= 144)
by (destruct HJ as (Σ' & Fx & fc & m & xra & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & bpx
& _ & _ & _ & _ & _ & _ & B & _); exact B).
apply (nbE_B1 bp' sub st (nbE_bJ k ki b) T c' HJ). intros c'' H3.
apply (nbE_B2 bp' sub st (nbE_bJ k ki b) st1 EST1 T c'' H3). intros c3 H3'.
apply Hk. exists bp'. split; [exact BP'| exact H3'].
Qed.

Lemma nbE_loop : forall (n : nat) (bp sub : Z) (st : nb_state bptr) (b : bits_st bptr) (st' : nb_state bptr) (b' : bits_st bptr),
(1 <= n)%nat -> Z.of_nat n + sub = 4 -> 0 <= sub -> subframes_pure n sub (smr_sm r) olp st b = Some (st', b') ->
cps bsegs (at_ELc RT PMc X Σ0 mE r mo olp bp sub st b) (fun c => exists bp', 17 <= bp' <= 144 /\ at_EXc RT PMc X Σ0 mE r mo olp bp' st' b' c).
Proof.
induction n as [|n IH]; intros bp sub st b st' b' N1 HN H0 SFS; [lia|].
cbn [subframes_pure] in SFS.
destruct (subframe_pure (smr_sm r) olp sub st b) as [[st1 b1]|] eqn:SF1; [| discriminate SFS].
intros T c Hc Hk.
apply (nbE_iter bp sub st b st1 b1 ltac:(lia) SF1 T c Hc). intros c' (bp' & BP' & [(S3 & H1) | (S3 & H1)]).
- destruct n as [|n]; [lia|].
apply (IH bp' (sub + 1) st1 b1 st' b' ltac:(lia) ltac:(lia) ltac:(lia) SFS T c' H1 Hk).
- destruct n as [|n]; [| lia]. cbn [subframes_pure] in SFS. injection SFS as <- <-.
apply Hk. exists bp'. split; [exact BP'| exact H1].
Qed.
End NbEB.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NbEB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MST : memset_icontract RT e_asan_memset.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MSTa : mat_stable PMc.
Variable X : @nbinvA bptr.
Hypothesis NXOK : nbx_ok X.
Hypothesis TP : x_tp X = Z_to_bv 64 0x630458.
Variables (Σ0 : rts RT) (fr0 : list (Z * nat)) (PD ND fh : Z) (kh : nat).
Hypothesis NSIG : nbsig RT Σ0 X fr0 PD ND fh kh.
Variables (mE : mem) (r : smrec) (mo olp : Z).

Hypothesis LTP : forall k, sm_ltp_unquant (smr_sm r) = Some k -> @ltp_unquant_cps RT bptr k.
Hypothesis INN : forall ki, sm_innovation_unquant (smr_sm r) = Some ki -> @innov_unquant_cps RT bptr ki.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation FF := (x_ff X). Local Notation SF := (x_sf X). Local Notation STEREO := (x_stereo X).
Local Notation lo := (x_lo X). Local Notation usp := (x_usp X). Local Notation nout := (x_nout X).

Local Notation R_J := (X099.R_J X olp).
Local Notation slots_J := (X099.slots_J X).
Local Notation at_Jc := (X099.at_Jc RT PMc X Σ0 mE r mo olp).
Local Notation nbE_bJ := (X099.nbE_bJ r).
Local Ltac simpl_sizes ::=
rewrite ?nbE_sz_shadow, ?nbE_sz_slots, ?nbE_sz_saves, ?nbE_sz_hdr, ?nbE_sz_cfg, ?nbE_sz_tail, ?nbE_sz_ucb, ?nbE_sz_ltpargs;
rewrite ?length_app, ?cells_size_app, ?cells_size_f32, ?length_f32, ?repeat_length;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app, ?cells_size_f32, ?length_f32, ?repeat_length; cbn [length].

Ltac nbe_base t := lazymatch t with ?x + _ => nbe_base x | _ => t end.
Ltac nbe_lia := first [ llia | cllia ].
Ltac nbe_cls :=
lazymatch goal with
| Hx : ?a <= ?x < _ |- aclient ?L ?Fr ?spv ?x =>
let bs := nbe_base a in
lazymatch bs with
| x_st _ => right; right; left; exists (x_st X), 2968; split; [assumption | nbe_lia]
| x_ff _ => right; right; right; left; exists (x_ff X), NBD_FCLASS; split; [assumption | fs_lit; nbe_lia]
| x_sf _ => right; right; right; right; exists (x_ff X), NBD_FCLASS; split; [assumption | fs_lit;
match goal with E1 : shad (x_ff X) = x_sf X, E2 : shad (x_ff X + 2048) = x_sf X + 256 |- _ => rewrite E1, E2 end; nbe_lia]
| x_out _ => right; right; right; left; exists fh, kh; split; [assumption | nbe_lia]
| x_A _ => right; right; right; left; exists fh, kh; split; [assumption | nbe_lia]
| x_stereo _ => right; right; right; left; exists fh, kh; split; [assumption | nbe_lia]
| x_D _ => right; right; left; exists PD, ND; split; [assumption | nbe_lia]
| x_usp _ => left; unfold USTACK_TOP; nbe_lia
end
end.
Ltac nbe_out1 :=
first [ llia
| lazymatch goal with Hx : ?a <= ?x < _ |- ~ (?d <= ?x < _) =>
let ba := nbe_base a in let bd := nbe_base d in
match goal with H : hid ?P |- _ => match P with context [ba] => match P with context [bd] =>
let U := fresh "U" in pose proof (H : P) as U; nbe_lia end end end
end
| cllia ].
Ltac nbe_trp PRES :=
lazymatch type of PRES with
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
lazymatch goal with WM : wmono asegs m m' |- _ =>
repeat match goal with
| H : rw_cells asegs m ?Aa ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells asegs m' Aa cs)
by (apply (rw_cells_agree asegs m m' Aa cs H);
[ apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [nbe_cls | try unfold BITS_SIZEOF, NBSTATE_SIZEOF; nbe_out1] | exact WM ]);
clear H; rename H' into H
| idtac "note: nbe_trp dropping" H; clear H ]
end end
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch goal with WM : wmono asegs m m' |- _ =>
repeat match goal with
| H : rw_cells asegs m ?Aa ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells asegs m' Aa cs)
by (apply (rw_cells_agree asegs m m' Aa cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ?x ?Hx; cps_sizes Hx;
split; [nbe_cls | cbn [outside]; try unfold BITS_SIZEOF, NBSTATE_SIZEOF; repeat lazymatch goal with |- _ /\ _ => split end; first [exact I | nbe_out1]] | exact WM ]);
clear H; rename H' into H
| idtac "note: nbe_trp dropping" H; clear H ]
end end
end.

Tactic Notation "nbe_unpack" hyp(Hc) "as" simple_intropattern(P) :=
try unfold icpt_postF in Hc;
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
lazymatch type of H with bv_unsigned (Z_to_bv 64 _) = _ => fail | _ => idtac end;
rewrite (unsigned_lit z) in H by ulc
end
end.

Ltac nbe_dj1 :=
first [ llia
| lazymatch goal with |- ?a + _ <= ?l \/ _ =>
let ba := nbe_base a in let bl := nbe_base l in
match goal with H : hid ?P |- _ => match P with context [ba] => match P with context [bl] =>
let U := fresh "U" in pose proof (H : P) as U; nbe_lia end end end
end
| cllia ].
Ltac nbe_dj := cbn [disjoint_from]; simpl_sizes; repeat (split; [nbe_dj1|]); first [exact I | nbe_dj1].
Ltac nbe_seg_tr m m' MU WM :=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at asegs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport asegs W m m' A2 bs2) in H; [ | exact MU | nbe_dj ]
| idtac "note: nbe_seg_tr dropping" H; clear H ]
| H : rw_cells asegs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport asegs W m m' A2 cs2) in H; [ | exact MU | exact WM | nbe_dj ]
| idtac "note: nbe_seg_tr dropping" H; clear H ]
| H : ro_cells asegs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport asegs W m m' A2 cs2) in H; [ | exact MU | nbe_dj ]
| idtac "note: nbe_seg_tr dropping" H; clear H ]
| H : stk asegs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint asegs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; repeat (split; [nbe_dj1|]); first [exact I | nbe_dj1] ]
| idtac "note: nbe_seg_tr dropping" H; clear H ]
end.

Ltac nbe_pf_fp PRES :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_of_pres_fp L0 F0 U0 W0 live frames sp W m m' PRES);
[ cps_incl | cps_incl | ulc
| let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho |- *; decompose [and] Ho; clear Ho Hx;
repeat (split; [ let Hin := fresh "Hin" in intro Hin; try unfold BITS_SIZEOF, NBSTATE_SIZEOF in Hin;
match goal with H : ~ (_ <= x < _) |- False => apply H;
first [clear - Hin; cps_unf; lia | match goal with S : 0 <= ?v < 4 |- _ => clear - Hin S; cps_unf; lia end | nbe_lia] end | ]);
exact I ]);
clear PF; rename PF' into PF
end
end.

Local Notation nbE_tabs_acc_art := (X099.nbE_tabs_acc_art RT AF).
Local Notation nbE_live_apart := (X099.nbE_live_apart RT AF).
Local Notation nbE_live_checked_dst := (X099.nbE_live_checked_dst RT AF).
Local Notation nbE_frame_checked_dst := (X099.nbE_frame_checked_dst RT).

Definition R_H3 (sub : Z) (xra s3 t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) (x_gp X) (x_tp X) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (ST + 1368 + 160 * sub)) a7
(Z_to_bv 64 SF) s3 (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6.
Definition at_H3c (bp' sub : Z) (st : nb_state bptr) (bJ : bits_st bptr) : config -> Prop :=
fun c => exists (Σ : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra s3 t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6 : word)
(j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff) (bp : Z),
ASTA RT Σ PMc (eq (MS (R_H3 sub xra s3 t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6) Fx (Z_to_bv 64 NBE_PC_H3) fc None m (seg_rom asegs))) c
/\ frm0 fc /\ nbctx X m st bJ j ows sws (slots_J bp' sub st s) ff SC_E /\ slots_EL ST OUT A FF bp sub s
/\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp' <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4
/\ nbEH_mem RT X Σ0 mE Σ m /\ nbEH_sig RT Σ0 Σ (rt_credit RT Σ0).

Lemma nbE_B1 : forall (bp' sub : Z) (st : nb_state bptr) (bJ : bits_st bptr),
cps asegs (at_Jc bp' sub st bJ) (at_H3c bp' sub st bJ).
Proof.
intros bp' sub st bJ T c Hc Hk.
destruct Hc as (Σ & Fx & fc & m & xra & s3 & s11 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & bp
& Hc0 & FRM & CTX & SLE & SAT & EMO & BP' & OLP & SUB & MEM & SIG).
destruct MEM as (ART0 & NACC & WM0 & PF).
destruct SIG as (LV & FRS & SP0 & CR & POI).
destruct CTX as (MI0 & STK0 & NBP & JOK & CBOK & NINV & BREP & BOK & BSZ & OW & LOW & SW & LSW & (SL & SV) & FFA & FFOK & (rest & SH) & CC & LC & JEXC & JISV).
unfold slots_J in SL.
pose proof NXOK as (U32 & SPH & LOS & LOU & F0 & F64 & ESF & FLO & FTOP & FSH & SF0 & SF1 & SFLO & S8 & SPOS & SLO & SSH & SIMG & O4 & OTOP & OLO & NOUT & OSH
& A8 & ATOP & ALO & ASH & D0 & DLO & DSZ & STE4 & STETOP & STELO & STESH & ISVX & SOA & SAA & SDA & SSTA & SFA & SSFA & OAA & ODA & OSTA & OFA & OSFA
& ADA & ASTEA & AFFA & ASFA & DSTA & DFA & DSFA & STEFA & STESFA & FSFA).
pose proof NSIG as (NFR & NLS & NLD & PD1 & PD2 & PDS & NFH & FHO1 & FHO2 & FHA1 & FHA2 & FHS1 & FHS2 & NPOIS & NLOW & NROOM & NTOP).
destruct NBP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
destruct FFA as (FF0 & FFp & FFg & FFl & FFq & FFk & FFi & FFe & FFj & FFiq).
assert (INL : In (ST, NBSTATE_SIZEOF) (rt_live RT Σ)) by (rewrite LV; exact NLS).
assert (INF : In (FF, NBD_FCLASS) (rt_frames RT Σ)) by (rewrite FRS, NFR; left; reflexivity).
assert (INFH : In (fh, kh) (rt_frames RT Σ)) by (rewrite FRS, NFR; right; exact NFH).
assert (INPD : In (PD, ND) (rt_live RT Σ)) by (rewrite LV; exact NLD).
assert (ESF8 : FF / 8 + SHB = SF) by (rewrite ESF, Z.shiftr_div_pow2 by lia; reflexivity).
assert (SHD1 : shad FF = SF) by (unfold shad; exact ESF8).
assert (SHD2 : shad (FF + 2048) = SF + 256) by (unfold shad; rewrite <- ESF8; clear - F64; Z.div_mod_to_equations; lia).
destruct (af_acc_live RT AF Σ m ST NBSTATE_SIZEOF ART0 INL) as (WRS & ACS).
pose proof (af_live_small RT AF Σ m ST NBSTATE_SIZEOF ART0 INL ltac:(unfold NBSTATE_SIZEOF; lia)) as STTOP.
assert (LOWS : rt_sp0 RT Σ - STACK_WIN <= lo) by (rewrite SP0; exact NLOW).
assert (POA : pois_above (rt_pois RT Σ) (usp + -544)) by (rewrite POI; replace (usp + -544) with (usp - NBD_FRAME) by (unfold NBD_FRAME; lia); exact NPOIS).
change hidp with hid in *.
unfold NBSTATE_SIZEOF, NBD_FRAME, NBD_CALLEE_STACK, RT_STACK, BITS_SIZEOF in *.
assert (OBS : aobj asegs m ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS]).

assert (ISK : (nb_innov_save st = None /\ nb_isave_ptr OUT st = 0)
\/ (exists kis, nb_innov_save st = Some kis /\ nb_isave_ptr OUT st = OUT + 4 * kis /\ 160 <= kis /\ kis + 160 <= Z.of_nat nout)).
{ unfold nb_isave_ptr. pose proof NINV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NI12). rewrite JISV in NI12 |- *.
destruct (nb_innov_save (x_st0 X)) as [kis|]; [right; exists kis; split; [reflexivity|]; split; [reflexivity|]; split; [exact NI12| exact ISVX]| left; split; reflexivity]. }
assert (ISB : 0 <= nb_isave_ptr OUT st < 2^63).
{ destruct ISK as [(_ & ->) | (kis & _ & -> & K1 & K2)]; [lia|]. clear - K1 K2 OLO LOU SPH O4 OTOP. unfold IMG_TOP in *. lia. }
rewrite JEXC in P3.

pose proof (PF : nbE_keep (rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE m)) as PFE. clear PF.
pose proof (WM0 : nbE_keep (wmono asegs mE m)) as WME. clear WM0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) (usp + -544)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -544, usp)] m) as PF.
pose proof (fun a0 => aclient_split RT AF Σ m (usp + -544) a0 ART0) as SPL.

destruct BREP as ((rj & Lrj & BOBJ) & (bs & BDAT & Hbs) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bs)) in BDAT.
clear LC CC.
pose proof JOK as (JL1 & JL2 & JL3 & JL4 & JL5 & JL6 & JL7 & JL8 & JL9 & JL10 & (JL11a & JL11b) & JL12 & JL13).
pose proof FFOK as (FL1 & FL2 & FL3 & FL4 & FL5 & FL6 & FL7 & FL8).
assert (LBS : Z.of_nat (length bs) = sb_buf_size bJ)
by (pose proof BOK as BOK'; unfold bits_ok in BOK'; rewrite Hbs, zlength_map_unsigned in BOK'; clear - BOK'; lia).
assert (DLOb : D + Z.of_nat (length bs) <= lo) by (rewrite LBS, BSZ, <- DSZ; exact DLO).
assert (DPD : D + Z.of_nat (length bs) <= PD + ND) by (rewrite LBS, BSZ, <- DSZ; exact PD2).
assert (DSZb : Z.of_nat (length bs) = x_dsz X) by (rewrite LBS, BSZ, <- DSZ; reflexivity).
pose proof SLE as (E0s & E8s & E16s & E24s & E32s & E40s & E48s & E56s & E64s & E80s & E88s & E96s & E104s & E112s & E120s & E128s & E136s & E144s & E152s
& E160s & E168s & E176s & E184s & E192s & E224s & E240s & E248s & E256s & E272s & E280s & E288s & E296s & E304s & E312s & E336s).
pose proof NINV as (NCL & _ & _ & _ & NVO & _).
cps_norm. cps_hide.

destruct (nbe_f32_win m (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 P2 ltac:(clear - JL1 SUB; lia)) as (EX1 & EX2 & EX3). clear P2.
replace (ST + 32 + 4 * Z.of_nat (Z.to_nat (334 + 40 * sub))) with (ST + 1368 + 160 * sub) in EX2, EX3 by (clear - SUB; lia).
change (4 * Z.of_nat 40) with 160 in EX3.
remember (firstn (Z.to_nat (334 + 40 * sub)) (j_excbuf j)) as ex1 eqn:EEX1.
remember (firstn 40 (skipn (Z.to_nat (334 + 40 * sub)) (j_excbuf j))) as exw eqn:EEXW.
remember (skipn (Z.to_nat (334 + 40 * sub) + 40) (j_excbuf j)) as ex3 eqn:EEX3.
assert (LEX1 : Z.of_nat (length ex1) = 334 + 40 * sub) by (subst ex1; rewrite length_firstn; clear - JL1 SUB; lia).
assert (LEXW : length exw = 40%nat) by (subst exw; rewrite length_firstn, length_skipn; clear - JL1 SUB; lia).
assert (LEX3 : Z.of_nat (length ex3) = 126 - 40 * sub) by (subst ex3; rewrite length_skipn; clear - JL1 SUB; lia).
clear EEX1 EEXW EEX3.
assert (OBX : aobj asegs m (ST + 1368 + 160 * sub) 160)
by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub asegs m ST 2968 (ST + 1368 + 160 * sub) 160 ACS ltac:(clear - SUB; lia) ltac:(clear - SUB; lia))]).
assert (XSH : ST + 1368 + 160 * sub + 160 <= 2147450880 \/ 17594333495296 <= ST + 1368 + 160 * sub) by (pose proof (SSH : _ \/ _) as U; clear - U SUB; lia).
assert (XFA : ST + 1368 + 160 * sub + 160 <= FF \/ FF + 2048 <= ST + 1368 + 160 * sub) by (pose proof (SFA : _ \/ _) as U; clear - U SUB; lia).
assert (ISV2 : nb_isave_ptr OUT st = 0 \/ 0 < nb_isave_ptr OUT st /\ nb_isave_ptr OUT st + 160 * sub < 2^63).
{ destruct ISK as [(_ & ->) | (kis & _ & -> & K1 & K2)]; [left; reflexivity| right]. clear - K1 K2 OLO LOU SPH O4 OTOP SUB. unfold IMG_TOP in *. lia. }
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
cps_seg (nbe_h1 usp lo ST FF SF olp sub (nb_isave_ptr OUT st) (ST + 1368 + 160 * sub) exw (f_exc32 ff) (f_innov ff)
(x_gp X) (x_tp X) xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) Fx fc m
SL ltac:(cbn; reflexivity) ltac:(cbn; reflexivity) ltac:(cbn; exact E272s) ltac:(cbn; reflexivity) ltac:(cbn; exact E224s) ltac:(cbn; exact E280s)
ltac:(cbn; exact E136s) eq_refl ISV2 SUB EX2 LEXW OBX S8 XSH ltac:(unfold IMG_TOP; lia)
FFe FL6 FFi FL5 F0 F64 FLO FTOP FSH XFA ltac:(clear - SLO SUB; lia) STK0 ltac:(clear - LOU; lia) SPH LOS CC0 MI0 FRM).
destruct POST as (m1 & F1 & fc1 & xa0 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xw1 & -> & FRM1 & MU1 & WM1 & MI1 & EXW1 & LXW1).
clear EX2 OBX CC0 FRM.
assert (ART1 : ART RT Σ m1).
{ apply (af_frame RT AF Σ m m1 lo ART0 LOWS); [| exact WM1]. intros a Ha; apply MU1; cbn [outside].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin SUB; lia]| exact I]. }
cps_pf_seg m m1 MU1.
clear ART0. nbe_seg_tr m m1 MU1 WM1. try match goal with MI : mem_inv asegs m |- _ => clear MI end.

pose proof (af_client_consts RT AF Σ m1 ART1) as CC1.
destruct ISK as [(ISN & ISP0) | (kis & ISS & ISP & K1 & K2)].
-
rewrite ISP0 in Hc. cbn [Z.eqb] in Hc.
cps_seg (nbE_h2z usp lo ST FF SF olp sub (ST + 1368 + 160 * sub) (f_innov ff)
(x_gp X) (x_tp X) xra t0 t1 t2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 s3 t3 t4 t5 t6
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) F1 fc1 m1
SL ltac:(cbn; reflexivity) ltac:(cbn; exact E280s) SUB FFi FL5 F0 F64 FLO FTOP FSH STK0 ltac:(clear - LOU; lia) SPH LOS CC1 MI1 FRM1).
destruct POST as (F2 & xb0 & xb1 & xb2 & xb3 & xb4 & xb5 & ->).
clear CC1.
pose (ows2 := ows). assert (OW2 : rw_cells asegs m1 OUT (f32 ows2)) by exact OW. assert (LOW2 : length ows2 = nout) by exact LOW. clear OW.
remember m1 as m2 eqn:EM2. rename ART1 into ART2. rename MI1 into MI2.

apply Hk.
assert (EXB2 : rw_cells asegs m2 (ST + 32) (f32 (ex1 ++ xw1 ++ ex3))).
{ apply nbe_f32_join_win; [exact EX1| rewrite LEX1; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by (clear; lia); exact EXW1|].
rewrite LEX1, LXW1. replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 160) by (clear; lia). exact EX3. }
pose proof (nbG_acc_pres2 RT AF Σ m2 m m2 (usp + -544) _ fh kh A 48 ART2 INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACA2.
pose proof (nbG_acc_pres2 RT AF Σ m2 m m2 (usp + -544) _ fh kh OUT (4 * Z.of_nat nout) ART2 INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACO2.
pose proof (nbG_acc_pres2 RT AF Σ m2 m m2 (usp + -544) _ fh kh STEREO 8 ART2 INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACT2.
assert (WM2E : wmono asegs mE m2) by (apply (wmono_trans asegs mE m m2); [exact WME| cps_wmono]).
assert (PF2E : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE m2).
{ apply (pres_fp_trans _ _ _ _ mE m m2); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_H3c.
exists Σ, F2, fc1, m2, xra, s3, t0, t1, t2, xb0, xb1, xb2, xb3, xb4, xb5, xa7, t3, t4, t5, t6,
(NBJ (j_last_ol_gain j) (ex1 ++ xw1 ++ ex3) (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)),
ows2, sws, s, ff, bp.
split; [eassumption|]. split; [exact FRM1|].
split.
{ unfold nbctx. split; [exact MI2|]. split; [exact STK0|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXB2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split.
{ unfold nb_junk_ok. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [rewrite !length_app; clear - LXW1 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact JL12| exact JL13]. }
split; [exact CBOK|]. split; [exact NINV|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB m2 D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OW2|]. split; [exact LOW2|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SL SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ m2 ART2)|]. split; [exact (AF_LIB Σ m2 ART2)|]. split; [reflexivity| exact JISV]. }
split; [exact SLE|]. split; [exact SAT|]. split; [exact EMO|]. split; [exact BP'|].
split; [exact OLP|]. split; [exact SUB|].
split; [exact (conj ART2 (conj (conj ACO2 (conj ACA2 ACT2)) (conj WM2E PF2E)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
-
assert (ISNZ : nb_isave_ptr OUT st <> 0) by (rewrite ISP; clear - OTOP K1; unfold IMG_TOP in *; lia).
destruct (nbe_f32_win m1 OUT ows (Z.to_nat (kis + 40 * sub)) 40 OW ltac:(clear - LOW K1 K2 SUB; lia)) as (OW1 & OWW & OW3). clear OW.
replace (OUT + 4 * Z.of_nat (Z.to_nat (kis + 40 * sub))) with (nb_isave_ptr OUT st + 160 * sub) in OWW, OW3 by (rewrite ISP; clear - K1 SUB; lia).
change (4 * Z.of_nat 40) with 160 in OW3.
remember (firstn (Z.to_nat (kis + 40 * sub)) ows) as ow1 eqn:EOW1.
remember (firstn 40 (skipn (Z.to_nat (kis + 40 * sub)) ows)) as yw eqn:EYW.
remember (skipn (Z.to_nat (kis + 40 * sub) + 40) ows) as ow3 eqn:EOW3.
assert (LOW1 : Z.of_nat (length ow1) = kis + 40 * sub) by (subst ow1; rewrite length_firstn; clear - LOW K1 K2 SUB; lia).
assert (LYW : length yw = 40%nat) by (subst yw; rewrite length_firstn, length_skipn; clear - LOW K1 K2 SUB; lia).
assert (LOW3 : Z.of_nat (length ow3) = Z.of_nat nout - kis - 40 * sub - 40) by (subst ow3; rewrite length_skipn; clear - LOW K1 K2 SUB; lia).
clear EOW1 EYW EOW3.
assert (OFFO : forall i, 0 <= i < 4 * Z.of_nat nout -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -544, usp)] (shad (OUT + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 RT AF Σ m1 m m1 (usp + -544) _ fh kh OUT (4 * Z.of_nat nout) ART1 INFH FHO1 FHO2 PF OFFO (proj1 NACC)) as ACO1.
assert (HYW : nb_isave_ptr OUT st <> 0 ->
rw_cells asegs m1 (nb_isave_ptr OUT st + 160 * sub) (f32 yw) /\ length yw = 40%nat /\ aobj asegs m1 (nb_isave_ptr OUT st + 160 * sub) 160
/\ (nb_isave_ptr OUT st + 160 * sub) mod 4 = 0
/\ (nb_isave_ptr OUT st + 160 * sub + 160 <= SH_LO \/ SH_HI <= nb_isave_ptr OUT st + 160 * sub) /\ IMG_TOP <= nb_isave_ptr OUT st + 160 * sub
/\ (nb_isave_ptr OUT st + 160 * sub + 160 <= FF \/ FF + 2048 <= nb_isave_ptr OUT st + 160 * sub) /\ nb_isave_ptr OUT st + 160 * sub + 160 <= lo).
{ intros _. rewrite ISP in *. split; [exact OWW|]. split; [exact LYW|].
split; [split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub asegs m1 OUT (4 * Z.of_nat nout) (OUT + 4 * kis + 160 * sub) 160 ACO1 ltac:(clear - K1 SUB; lia) ltac:(clear - K1 K2 SUB; lia))]|].
split; [clear - O4; Z.div_mod_to_equations; lia|].
split; [pose proof (OSH : _ \/ _) as U; clear - U K1 K2 SUB; unfold SH_LO, SH_HI; lia|]. split; [clear - OTOP K1 SUB; unfold IMG_TOP in *; lia|].
split; [pose proof (OFA : _ \/ _) as U; clear - U K1 K2 SUB; lia| clear - OLO K1 K2 SUB; lia]. }
cps_seg (nbe_h2 usp lo ST FF SF olp sub (nb_isave_ptr OUT st) (ST + 1368 + 160 * sub) yw (f_innov ff)
(x_gp X) (x_tp X) xra t0 t1 t2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 s3 t3 t4 t5 t6
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) F1 fc1 m1
SL ltac:(cbn; reflexivity) ltac:(cbn; exact E280s) ISV2 SUB HYW FFi FL5 F0 F64 FLO FTOP FSH STK0 ltac:(clear - LOU; lia) SPH LOS CC1 MI1 FRM1).
destruct POST as (m2 & F2 & xb0 & xb1 & xb2 & xb3 & xb4 & xb5 & -> & MU2 & WM2 & MI2 & YW2).
destruct (YW2 ISNZ) as (yw2 & OWW2 & LYW2). clear YW2 HYW OWW CC1 ACO1 OFFO.
rewrite ISP in MU2, OWW2, OW3.
assert (ART2 : ART RT Σ m2).
{ apply (af_frame RT AF Σ m1 m2 lo ART1 LOWS); [| exact WM2]. intros a Ha; apply MU2; cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists fh, kh; split; [exact INFH| clear - Hin FHO1 FHO2 K1 K2 SUB; lia]| exact I]. }
cps_pf_seg m1 m2 MU2.
clear ART1. nbe_seg_tr m1 m2 MU2 WM2. try match goal with MI : mem_inv asegs m1 |- _ => clear MI end.
pose (ows2 := ow1 ++ yw2 ++ ow3).
assert (OW2 : rw_cells asegs m2 OUT (f32 ows2)).
{ apply nbe_f32_join_win; [exact OW1| rewrite LOW1; replace (OUT + 4 * (kis + 40 * sub)) with (OUT + 4 * kis + 160 * sub) by (clear; lia); exact OWW2|].
rewrite LOW1, LYW2. replace (OUT + 4 * (kis + 40 * sub) + 4 * Z.of_nat 40) with (OUT + 4 * kis + 160 * sub + 160) by (clear; lia). exact OW3. }
assert (LOW2 : length ows2 = nout) by (unfold ows2; rewrite !length_app; clear - LOW1 LYW2 LOW3; lia).
clear OW1 OWW2 OW3.

apply Hk.
assert (EXB2 : rw_cells asegs m2 (ST + 32) (f32 (ex1 ++ xw1 ++ ex3))).
{ apply nbe_f32_join_win; [exact EX1| rewrite LEX1; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by (clear; lia); exact EXW1|].
rewrite LEX1, LXW1. replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 160) by (clear; lia). exact EX3. }
pose proof (nbG_acc_pres2 RT AF Σ m2 m m2 (usp + -544) _ fh kh A 48 ART2 INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACA2.
pose proof (nbG_acc_pres2 RT AF Σ m2 m m2 (usp + -544) _ fh kh OUT (4 * Z.of_nat nout) ART2 INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACO2.
pose proof (nbG_acc_pres2 RT AF Σ m2 m m2 (usp + -544) _ fh kh STEREO 8 ART2 INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACT2.
assert (WM2E : wmono asegs mE m2) by (apply (wmono_trans asegs mE m m2); [exact WME| cps_wmono]).
assert (PF2E : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE m2).
{ apply (pres_fp_trans _ _ _ _ mE m m2); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_H3c.
exists Σ, F2, fc1, m2, xra, s3, t0, t1, t2, xb0, xb1, xb2, xb3, xb4, xb5, xa7, t3, t4, t5, t6,
(NBJ (j_last_ol_gain j) (ex1 ++ xw1 ++ ex3) (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)),
ows2, sws, s, ff, bp.
split; [eassumption|]. split; [exact FRM1|].
split.
{ unfold nbctx. split; [exact MI2|]. split; [exact STK0|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXB2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split.
{ unfold nb_junk_ok. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [rewrite !length_app; clear - LXW1 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact JL12| exact JL13]. }
split; [exact CBOK|]. split; [exact NINV|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB m2 D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OW2|]. split; [exact LOW2|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SL SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ m2 ART2)|]. split; [exact (AF_LIB Σ m2 ART2)|]. split; [reflexivity| exact JISV]. }
split; [exact SLE|]. split; [exact SAT|]. split; [exact EMO|]. split; [exact BP'|].
split; [exact OLP|]. split; [exact SUB|].
split; [exact (conj ART2 (conj (conj ACO2 (conj ACA2 ACT2)) (conj WM2E PF2E)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
Qed.

Lemma nbE_B2 : forall (bp' sub : Z) (st : nb_state bptr) (bJ : bits_st bptr) (st1 : nb_state bptr),
(if nb_submodeID st =? 1 then exists v, voc_loop VOC_FUEL (nb_voc_offset st) olp = Some v /\ st1 = set_nb_voc_offset st (v - NB_SUBFRAME_SIZE) else st1 = st) ->
cps asegs (at_H3c bp' sub st bJ)
(fun c => (sub < 3 /\ at_ELc RT PMc X Σ0 mE r mo olp bp' (sub + 1) st1 bJ c) \/ (sub = 3 /\ at_EXc RT PMc X Σ0 mE r mo olp bp' st1 bJ c)).
Proof.
intros bp' sub st bJ st1 EST1 T c Hc Hk.
destruct Hc as (Σ & Fx & fc & m & xra & s3 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a7 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & bp
& Hc0 & FRM & CTX & SLE & SAT & EMO & BP' & OLP & SUB & MEM & SIG).
destruct MEM as (ART0 & NACC & WM0 & PF).
destruct SIG as (LV & FRS & SP0 & CR & POI).
destruct CTX as (MI0 & STK0 & NBP & JOK & CBOK & NINV & BREP & BOK & BSZ & OW & LOW & SW & LSW & (SL & SV) & FFA & FFOK & (rest & SH) & CC & LC & JEXC & JISV).
unfold slots_J in SL.
pose proof NXOK as (U32 & SPH & LOS & LOU & F0 & F64 & ESF & FLO & FTOP & FSH & SF0 & SF1 & SFLO & S8 & SPOS & SLO & SSH & SIMG & O4 & OTOP & OLO & NOUT & OSH
& A8 & ATOP & ALO & ASH & D0 & DLO & DSZ & STE4 & STETOP & STELO & STESH & ISVX & SOA & SAA & SDA & SSTA & SFA & SSFA & OAA & ODA & OSTA & OFA & OSFA
& ADA & ASTEA & AFFA & ASFA & DSTA & DFA & DSFA & STEFA & STESFA & FSFA).
pose proof NSIG as (NFR & NLS & NLD & PD1 & PD2 & PDS & NFH & FHO1 & FHO2 & FHA1 & FHA2 & FHS1 & FHS2 & NPOIS & NLOW & NROOM & NTOP).
destruct NBP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
destruct FFA as (FF0 & FFp & FFg & FFl & FFq & FFk & FFi & FFe & FFj & FFiq).
assert (INL : In (ST, NBSTATE_SIZEOF) (rt_live RT Σ)) by (rewrite LV; exact NLS).
assert (INF : In (FF, NBD_FCLASS) (rt_frames RT Σ)) by (rewrite FRS, NFR; left; reflexivity).
assert (INFH : In (fh, kh) (rt_frames RT Σ)) by (rewrite FRS, NFR; right; exact NFH).
assert (INPD : In (PD, ND) (rt_live RT Σ)) by (rewrite LV; exact NLD).
assert (ESF8 : FF / 8 + SHB = SF) by (rewrite ESF, Z.shiftr_div_pow2 by lia; reflexivity).
assert (SHD1 : shad FF = SF) by (unfold shad; exact ESF8).
assert (SHD2 : shad (FF + 2048) = SF + 256) by (unfold shad; rewrite <- ESF8; clear - F64; Z.div_mod_to_equations; lia).
destruct (af_acc_live RT AF Σ m ST NBSTATE_SIZEOF ART0 INL) as (WRS & ACS).
pose proof (af_live_small RT AF Σ m ST NBSTATE_SIZEOF ART0 INL ltac:(unfold NBSTATE_SIZEOF; lia)) as STTOP.
assert (LOWS : rt_sp0 RT Σ - STACK_WIN <= lo) by (rewrite SP0; exact NLOW).
assert (POA : pois_above (rt_pois RT Σ) (usp + -544)) by (rewrite POI; replace (usp + -544) with (usp - NBD_FRAME) by (unfold NBD_FRAME; lia); exact NPOIS).
change hidp with hid in *.
unfold NBSTATE_SIZEOF, NBD_FRAME, NBD_CALLEE_STACK, RT_STACK, BITS_SIZEOF in *.
assert (OBS : aobj asegs m ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS]).

assert (ISK : (nb_innov_save st = None /\ nb_isave_ptr OUT st = 0)
\/ (exists kis, nb_innov_save st = Some kis /\ nb_isave_ptr OUT st = OUT + 4 * kis /\ 160 <= kis /\ kis + 160 <= Z.of_nat nout)).
{ unfold nb_isave_ptr. pose proof NINV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NI12). rewrite JISV in NI12 |- *.
destruct (nb_innov_save (x_st0 X)) as [kis|]; [right; exists kis; split; [reflexivity|]; split; [reflexivity|]; split; [exact NI12| exact ISVX]| left; split; reflexivity]. }
assert (ISB : 0 <= nb_isave_ptr OUT st < 2^63).
{ destruct ISK as [(_ & ->) | (kis & _ & -> & K1 & K2)]; [lia|]. clear - K1 K2 OLO LOU SPH O4 OTOP. unfold IMG_TOP in *. lia. }
rewrite JEXC in P3.

pose proof (PF : nbE_keep (rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE m)) as PFE. clear PF.
pose proof (WM0 : nbE_keep (wmono asegs mE m)) as WME. clear WM0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) (usp + -544)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -544, usp)] m) as PF.
pose proof (fun a0 => aclient_split RT AF Σ m (usp + -544) a0 ART0) as SPL.

destruct BREP as ((rj & Lrj & BOBJ) & (bs & BDAT & Hbs) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bs)) in BDAT.
clear LC CC.
pose proof JOK as (JL1 & JL2 & JL3 & JL4 & JL5 & JL6 & JL7 & JL8 & JL9 & JL10 & (JL11a & JL11b) & JL12 & JL13).
pose proof FFOK as (FL1 & FL2 & FL3 & FL4 & FL5 & FL6 & FL7 & FL8).
assert (LBS : Z.of_nat (length bs) = sb_buf_size bJ)
by (pose proof BOK as BOK'; unfold bits_ok in BOK'; rewrite Hbs, zlength_map_unsigned in BOK'; clear - BOK'; lia).
assert (DLOb : D + Z.of_nat (length bs) <= lo) by (rewrite LBS, BSZ, <- DSZ; exact DLO).
assert (DPD : D + Z.of_nat (length bs) <= PD + ND) by (rewrite LBS, BSZ, <- DSZ; exact PD2).
assert (DSZb : Z.of_nat (length bs) = x_dsz X) by (rewrite LBS, BSZ, <- DSZ; reflexivity).
pose proof SLE as (E0s & E8s & E16s & E24s & E32s & E40s & E48s & E56s & E64s & E80s & E88s & E96s & E104s & E112s & E120s & E128s & E136s & E144s & E152s
& E160s & E168s & E176s & E184s & E192s & E224s & E240s & E248s & E256s & E272s & E280s & E288s & E296s & E304s & E312s & E336s).
pose proof NINV as (NCL & _ & _ & _ & NVO & _).
cps_norm. cps_hide.

pose proof (smrec_facts mo r SAT) as (_ & MO18 & _).
cps_seg (nbe_h3 usp lo ST FF SF olp sub mo st (j_pad1 j) (x_gp X) (x_tp X) xra t0 t1 t2 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (ST + 1368 + 160 * sub)) a7 s3 t3 t4 t5 t6
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) Fx fc m
SL ltac:(cbn; exact E312s) ltac:(cbn; exact E288s) ltac:(cbn; exact E240s) ltac:(cbn; reflexivity) ltac:(cbn; exact E272s)
P15 EMO ltac:(clear - MO18; lia) SUB OBS S8 SPOS SLO SSH STK0 ltac:(clear - LOU; lia) SPH LOS MI0).
destruct POST as (m1 & xra1 & rt0 & rt1 & rt2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & rt3 & rt4 & rt5 & rt6 & MU1 & WM1 & MI1 & ST1 & CASES).
clear SL STK0 OBS.
assert (ART1 : ART RT Σ m1).
{ apply (af_frame RT AF Σ m m1 lo ART0 LOWS); [| exact WM1]. intros a Ha; apply MU1; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m m1 MU1.
clear ART0. nbe_seg_tr m m1 MU1 WM1. try match goal with MI : mem_inv asegs m |- _ => clear MI end.
destruct CASES as [(MO1 & SL1 & [(SUB3 & ->) | (SUB3 & ->)]) | (MO1 & SL1 & ->)].
-
assert (ST1E : st1 = st) by (rewrite EMO in EST1; destruct (Z.eqb_spec mo 1) as [E|_]; [exfalso; exact (MO1 E)| exact EST1]).
subst st1. rename m1 into mF. rename ART1 into ARTF. rename MI1 into MIF. rename ST1 into STF. rename SL1 into SLF. rename P2 into EXBF.
set (jF := j). set (owsF := ows). set (ffF := ff).
set (sF := sset 272 (Z_to_bv 64 (160 * (sub + 1))) (sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s)))) in SLF.
assert (JOKF : nb_junk_ok jF) by exact JOK. assert (NINVF : nb_inv st) by exact NINV.
assert (OWF : rw_cells asegs mF OUT (f32 owsF)) by exact OW. assert (LOWF : length owsF = nout) by exact LOW.
assert (JEXCF : j_exc jF = ST + 1368) by exact JEXC. assert (JISVF : nb_innov_save st = nb_innov_save (x_st0 X)) by exact JISV.
assert (EMOF : nb_submodeID st = mo) by exact EMO.

apply Hk. left. split; [clear - SUB3; lia|].
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh A 48 ARTF INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACAF.
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh OUT (4 * Z.of_nat nout) ARTF INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACOF.
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh STEREO 8 ARTF INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACTF.
assert (WMFE : wmono asegs mE mF) by (apply (wmono_trans asegs mE m mF); [exact WME| cps_wmono]).
assert (PFFE : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE mF).
{ apply (pres_fp_trans _ _ _ _ mE m mF); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_ELc. exists Σ. split; [| exact (conj LV (conj FRS (conj SP0 (conj CR POI))))].
eapply ASTA_conseq; [eassumption|]. intros ms <-. split.
2:{ cbn [ms_mem]. exact (conj ARTF (conj (conj ACOF (conj ACAF ACTF)) (conj WMFE PFFE))). }
unfold at_EL. do 18 eexists. exists jF, owsF, sws, sF, ffF.
split; [reflexivity|]. split; [exact FRM|].
split.
{ unfold nbctx. split; [exact MIF|]. split; [exact STF|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXBF|]. split; [rewrite JEXCF; exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split; [exact JOKF|].
split; [exact CBOK|]. split; [exact NINVF|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB mF D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OWF|]. split; [exact LOWF|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SLF SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ mF ARTF)|]. split; [exact (AF_LIB Σ mF ARTF)|]. split; [exact JEXCF| exact JISVF]. }
split; [unfold slots_EL; cbn; repeat split; first [assumption | reflexivity]|].
split; [exact SAT|]. split; [exact EMOF|]. split; [exact BP'|]. split; [exact OLP| clear - SUB SUB3; lia].
-
assert (ST1E : st1 = st) by (rewrite EMO in EST1; destruct (Z.eqb_spec mo 1) as [E|_]; [exfalso; exact (MO1 E)| exact EST1]).
subst st1. rename m1 into mF. rename ART1 into ARTF. rename MI1 into MIF. rename ST1 into STF. rename SL1 into SLF. rename P2 into EXBF.
set (jF := j). set (owsF := ows). set (ffF := ff).
set (sF := sset 272 (Z_to_bv 64 (160 * (sub + 1))) (sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s)))) in SLF.
assert (JOKF : nb_junk_ok jF) by exact JOK. assert (NINVF : nb_inv st) by exact NINV.
assert (OWF : rw_cells asegs mF OUT (f32 owsF)) by exact OW. assert (LOWF : length owsF = nout) by exact LOW.
assert (JEXCF : j_exc jF = ST + 1368) by exact JEXC. assert (JISVF : nb_innov_save st = nb_innov_save (x_st0 X)) by exact JISV.
assert (EMOF : nb_submodeID st = mo) by exact EMO.

apply Hk. right. split; [exact SUB3|].
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh A 48 ARTF INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACAF.
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh OUT (4 * Z.of_nat nout) ARTF INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACOF.
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh STEREO 8 ARTF INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACTF.
assert (WMFE : wmono asegs mE mF) by (apply (wmono_trans asegs mE m mF); [exact WME| cps_wmono]).
assert (PFFE : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE mF).
{ apply (pres_fp_trans _ _ _ _ mE m mF); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_EXc. do 20 eexists. exists jF, owsF, sws, sF, ffF.
split; [eassumption|]. split; [exact FRM|].
split.
{ unfold nbctx. split; [exact MIF|]. split; [exact STF|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXBF|]. split; [rewrite JEXCF; exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split; [exact JOKF|].
split; [exact CBOK|]. split; [exact NINVF|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB mF D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OWF|]. split; [exact LOWF|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SLF SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ mF ARTF)|]. split; [exact (AF_LIB Σ mF ARTF)|]. split; [exact JEXCF| exact JISVF]. }
split; [unfold slots_EL; cbn; repeat split; first [assumption | reflexivity | rewrite SUB3; reflexivity]|].
split; [cbn; reflexivity|].
split; [exact SAT|]. split; [exact EMOF|]. split; [exact BP'|].
split; [exact (conj ARTF (conj (conj ACOF (conj ACAF ACTF)) (conj WMFE PFFE)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
-
assert (LB0 : sm_lbr_pitch (smr_sm r) = 0) by (rewrite MO1 in SAT; cbn in SAT; injection SAT as E; rewrite <- E; reflexivity).
assert (OLP1 : 17 <= olp <= 144) by (destruct OLP as [(HL & _)|(_ & HO)]; [rewrite LB0 in HL; discriminate HL| exact HO]).
destruct (nbe_f32_win m1 (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 P2 ltac:(clear - JL1 SUB; lia)) as (EX1 & EX2 & EX3). clear P2.
replace (ST + 32 + 4 * Z.of_nat (Z.to_nat (334 + 40 * sub))) with (ST + 1368 + 160 * sub) in EX2, EX3 by (clear - SUB; lia).
change (4 * Z.of_nat 40) with 160 in EX3.
remember (firstn (Z.to_nat (334 + 40 * sub)) (j_excbuf j)) as ex1 eqn:EEX1.
remember (firstn 40 (skipn (Z.to_nat (334 + 40 * sub)) (j_excbuf j))) as exw eqn:EEXW.
remember (skipn (Z.to_nat (334 + 40 * sub) + 40) (j_excbuf j)) as ex3 eqn:EEX3.
assert (LEX1 : Z.of_nat (length ex1) = 334 + 40 * sub) by (subst ex1; rewrite length_firstn; clear - JL1 SUB; lia).
assert (LEXW : length exw = 40%nat) by (subst exw; rewrite length_firstn, length_skipn; clear - JL1 SUB; lia).
assert (LEX3 : Z.of_nat (length ex3) = 126 - 40 * sub) by (subst ex3; rewrite length_skipn; clear - JL1 SUB; lia).
clear EEX1 EEXW EEX3.
pose proof (proj2 EX2) as WRX. rewrite cells_size_f32, LEXW in WRX. change (Z.of_nat (4 * 40)) with 160 in WRX. clear EX2.
destruct (af_acc_live RT AF Σ m1 ST 2968 ART1 INL) as (_ & ACS1).
assert (CD4 : checked_dst RT Σ m1 (Z_to_bv 64 (usp + -544)) (ST + 1368 + 160 * sub) 160).
{ split; [intros _; split| split; [| exact WRX]].
- exact (acc_sub asegs m1 ST 2968 (ST + 1368 + 160 * sub) 160 ACS1 ltac:(clear - SUB; lia) ltac:(clear - SUB; lia)).
- left. exists ST, 2968. split; [exact INL| clear - SUB; lia].
- intros i Hi. right; right; left. exists ST, 2968. split; [exact INL| clear - SUB Hi; lia]. }
cps_rt (MST Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (ST + 1368 + 160 * sub) 160 (Z_to_bv 8 0) lo).
{ clear - SPOS SLO LOU NTOP SUB. lia. }
{ cps_callok. }
intros c2 Hc2.
clear CD4 ACS1.
nbe_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
nbe_trp PRES2.
cps_pf_pres PRES2.
clear ART1 MI1 ST1 PRES2.
assert (EXZ : rw_cells asegs m2 (ST + 1368 + 160 * sub) (f32 (repeat (Z_to_bv 64 0) 40))).
{ split; [split; [apply cells_wf_f32 | replace (cells_bytes (f32 (repeat (Z_to_bv 64 0) 40))) with (repeat (Z_to_bv 8 0) (Z.to_nat 160)) by (vm_compute; reflexivity); exact BY2]|].
rewrite cells_size_f32, repeat_length. exact (wr_at_transport asegs m1 m2 _ _ WRX WM2). }
clear BY2 WRX.

destruct (af_acc_live RT AF Σ m2 ST 2968 ART2 INL) as (_ & ACS2).
assert (OBS2 : aobj asegs m2 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS2]).
assert (OBX2 : aobj asegs m2 (ST + 1368 + 160 * sub) 160)
by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub asegs m2 ST 2968 (ST + 1368 + 160 * sub) 160 ACS2 ltac:(clear - SUB; lia) ltac:(clear - SUB; lia))]).
clear ACS2.
cps_seg (nbe_i1 usp lo ST FF SF olp sub (ST + 1368 + 160 * sub) st (j_pad2 j) (repeat (Z_to_bv 64 0) 40) (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) _ _ m2
SL1 ltac:(cbn; exact E56s) ltac:(cbn; reflexivity) ltac:(cbn; exact E272s) ltac:(cbn; reflexivity) ltac:(cbn; exact E280s) eq_refl SUB
P19 NVO OLP1 OBS2 S8 SPOS SLO SSH EXZ (repeat_length _ _) OBX2 ST2 ltac:(clear - LOU; lia) SPH LOS MI2).
destruct POST as (m3 & qt0 & qt1 & qt2 & qa4 & qa6 & qa7 & qt3 & qt4 & qt5 & qt6 & vfin & xw3 & -> & MU3 & WM3 & MI3 & VOCL & TAIL3 & EXW3 & LXW3).
clear OBS2 OBX2 EXZ P19.
assert (ART3 : ART RT Σ m3).
{ apply (af_frame RT AF Σ m2 m3 lo ART2 LOWS); [| exact WM3]. intros a Ha; apply MU3; cbn [outside].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin SUB; lia]|].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin; lia]| exact I]. }
cps_pf_seg m2 m3 MU3.
clear ART2. nbe_seg_tr m2 m3 MU3 WM3. try match goal with MI : mem_inv asegs m2 |- _ => clear MI end.

clear Hc. rename Hc1 into Hc.
destruct xw3 as [|x3 rest3]; [cbn in LXW3; discriminate LXW3|].
pose proof P18 as P18'. destruct (j_voc j) as [|v1 [|v2 [|v3 [|]]]] eqn:EV; cbn [length] in JL12; try discriminate JL12. clear P18'.
destruct (af_acc_live RT AF Σ m3 ST 2968 ART3 INL) as (_ & ACS3).
assert (OBS3 : aobj asegs m3 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS3]).
assert (OBX3 : aobj asegs m3 (ST + 1368 + 160 * sub) 160)
by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub asegs m3 ST 2968 (ST + 1368 + 160 * sub) 160 ACS3 ltac:(clear - SUB; lia) ltac:(clear - SUB; lia))]).
clear ACS3.
pose proof (af_client_consts RT AF Σ m3 ART3) as CC3.
assert (XSH3 : ST + 1368 + 160 * sub + 160 <= SH_LO \/ SH_HI <= ST + 1368 + 160 * sub) by (pose proof (SSH : _ \/ _) as U; clear - U SUB; unfold SH_LO, SH_HI; lia).
assert (XFA3 : ST + 1368 + 160 * sub + 160 <= FF \/ FF + 2048 <= ST + 1368 + 160 * sub) by (pose proof (SFA : _ \/ _) as U; clear - U SUB; lia).
replace (Z_to_bv 64 (ST + 1368 + 160 * sub)) with (Z_to_bv 64 (ST + 1368 + 160 * sub + 0)) in Hc by (f_equal; lia).
replace (Z_to_bv 64 (FF + 320)) with (Z_to_bv 64 (FF + 320 + 0)) in Hc by (f_equal; lia).
replace (ST + 1368 + 160 * sub) with (ST + 1368 + 160 * sub + 0) in EXW3 by lia.
cps_seg (voc_loop_walk ST (ST + 1368 + 160 * sub) FF lo usp (f_innov ff) m3
(Z_to_bv 64 RA_nbe_mset4) (Z_to_bv 64 (usp + -544)) (x_gp X) (x_tp X) qt1 qt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) (Z_to_bv 64 SF) (Z_to_bv 64 0)
(Z_to_bv 64 (FF + 928)) (Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2032)) qt3 qt4 qt5 qt6
OBX3 ltac:(clear - S8; Z.div_mod_to_equations; lia) XSH3 ltac:(unfold IMG_TOP in *; lia) OBS3 S8 SPOS SSH ltac:(clear - SUB; lia) ltac:(clear - SUB; lia)
FL5 FTOP FSH XFA3 SFA SLO FLO ltac:(clear - LOU; lia) SPH LOS
rest3 [] x3 v1 v2 v3 40 0 qt0 qa4 (Z_to_bv 64 (ST + 2948)) qa6 qa7 _ _ m3
ltac:(cbn [length] in LXW3 |- *; lia) ltac:(cbn [length] in LXW3 |- *; lia) eq_refl FRM (munch_refl _ m3)
ltac:(cbn; unfold SH_LO, SH_HI in *; pose proof (SSH : _ \/ _) as U; clear - U SUB; lia) (wmono_refl asegs m3) MI3 CC3
(rw_cells_nil asegs m3 (ST + 1368 + 160 * sub) ltac:(clear - SPOS SLO LOU NTOP SUB; lia)) EXW3 P18 FFi).
destruct POST as (m4 & F4 & fc4 & pt0 & pa0 & pa1 & pa2 & pa3 & pa4 & pa5 & pa6 & pa7 & xw4 & vs4 & -> & FRM4 & MU4 & WM4 & MI4 & EXW4 & LXW4 & VS4 & LVS4).
clear OBS3 OBX3 CC3 XSH3 EXW3 P18 FRM.
assert (ART4 : ART RT Σ m4).
{ apply (af_frame RT AF Σ m3 m4 lo ART3 LOWS); [| exact WM4]. intros a Ha; apply MU4; cbn [outside].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin SUB; lia]|].
split; [intros Hin; apply Ha; right; right; left; exists ST, 2968; split; [exact INL| clear - Hin; lia]| exact I]. }
cps_pf_seg m3 m4 MU4.
clear ART3. nbe_seg_tr m3 m4 MU4 WM4. try match goal with MI : mem_inv asegs m3 |- _ => clear MI end.

cps_seg (nbe_bk usp lo ST FF SF olp sub (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) _ _ m4
SL1 ltac:(cbn; reflexivity) ltac:(cbn; exact E272s) SUB ST2 ltac:(clear - LOU; lia) SPH LOS MI4).
destruct POST as (m5 & pb0 & pb7 & MU5 & WM5 & MI5 & ST5 & SL5 & BK).
clear SL1 ST2.
assert (ART5 : ART RT Σ m5).
{ apply (af_frame RT AF Σ m4 m5 lo ART4 LOWS); [| exact WM5]. intros a Ha; apply MU5; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m4 m5 MU5.
clear ART4. nbe_seg_tr m4 m5 MU5 WM5. try match goal with MI : mem_inv asegs m4 |- _ => clear MI end.

rewrite EMO, MO1 in EST1. cbn [Z.eqb Pos.eqb] in EST1. destruct EST1 as (v & VOC1 & ->). rewrite VOCL in VOC1. injection VOC1 as <-.
destruct (voc_loop_inv (nb_voc_offset st) olp NVO OLP1) as (v' & VOCv & VB). rewrite VOCL in VOCv. injection VOCv as <-.

assert (EXBF : rw_cells asegs m5 (ST + 32) (f32 (ex1 ++ xw4 ++ ex3))).
{ apply nbe_f32_join_win; [exact EX1| rewrite LEX1; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by (clear; lia); exact EXW4|].
rewrite LEX1, LXW4. replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 160) by (clear; lia). exact EX3. }
clear EX1 EXW4 EX3.
rename m5 into mF. rename ART5 into ARTF. rename MI5 into MIF. rename ST5 into STF. rename SL5 into SLF. rename FRM4 into FRM.
rename VS4 into P18. rename TAIL3 into P19.
set (jF := NBJ (j_last_ol_gain j) (ex1 ++ xw4 ++ ex3) (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) vs4 (j_pad2 j)).
set (owsF := ows). set (ffF := ff).
set (sF := sset 272 (Z_to_bv 64 (160 * (sub + 1))) (sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s)))) in SLF.
assert (JOKF : nb_junk_ok jF).
{ unfold nb_junk_ok, jF. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [rewrite !length_app; clear - LXW4 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact LVS4| exact JL13]. }
assert (NINVF : nb_inv (set_nb_voc_offset st (vfin - NB_SUBFRAME_SIZE))).
{ pose proof NINV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold nb_inv. cbn.
exact (conj I1 (conj I2 (conj I3 (conj I4 (conj VB (conj I6 (conj I7 (conj I8 (conj I9 (conj I10 (conj I11 I12))))))))))). }
assert (OWF : rw_cells asegs mF OUT (f32 owsF)) by exact OW. assert (LOWF : length owsF = nout) by exact LOW.
assert (JEXCF : j_exc jF = ST + 1368) by reflexivity.
assert (JISVF : nb_innov_save (set_nb_voc_offset st (vfin - NB_SUBFRAME_SIZE)) = nb_innov_save (x_st0 X)) by exact JISV.
assert (EMOF : nb_submodeID (set_nb_voc_offset st (vfin - NB_SUBFRAME_SIZE)) = mo) by exact EMO.
destruct BK as [(SUB3 & ->) | (SUB3 & ->)].
+ idtac.

apply Hk. left. split; [clear - SUB3; lia|].
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh A 48 ARTF INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACAF.
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh OUT (4 * Z.of_nat nout) ARTF INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACOF.
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh STEREO 8 ARTF INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACTF.
assert (WMFE : wmono asegs mE mF) by (apply (wmono_trans asegs mE m mF); [exact WME| cps_wmono]).
assert (PFFE : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE mF).
{ apply (pres_fp_trans _ _ _ _ mE m mF); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_ELc. exists Σ. split; [| exact (conj LV (conj FRS (conj SP0 (conj CR POI))))].
eapply ASTA_conseq; [eassumption|]. intros ms <-. split.
2:{ cbn [ms_mem]. exact (conj ARTF (conj (conj ACOF (conj ACAF ACTF)) (conj WMFE PFFE))). }
unfold at_EL. do 18 eexists. exists jF, owsF, sws, sF, ffF.
split; [reflexivity|]. split; [exact FRM|].
split.
{ unfold nbctx. split; [exact MIF|]. split; [exact STF|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXBF|]. split; [rewrite JEXCF; exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split; [exact JOKF|].
split; [exact CBOK|]. split; [exact NINVF|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB mF D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OWF|]. split; [exact LOWF|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SLF SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ mF ARTF)|]. split; [exact (AF_LIB Σ mF ARTF)|]. split; [exact JEXCF| exact JISVF]. }
split; [unfold slots_EL; cbn; repeat split; first [assumption | reflexivity]|].
split; [exact SAT|]. split; [exact EMOF|]. split; [exact BP'|]. split; [exact OLP| clear - SUB SUB3; lia].
+ idtac.

apply Hk. right. split; [exact SUB3|].
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh A 48 ARTF INFH FHA1 FHA2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 (proj2 NACC))) as ACAF.
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh OUT (4 * Z.of_nat nout) ARTF INFH FHO1 FHO2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj1 NACC)) as ACOF.
pose proof (nbG_acc_pres2 RT AF Σ mF m mF (usp + -544) _ fh kh STEREO 8 ARTF INFH FHS1 FHS2 PF
(fun i Hi => nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)) (proj2 (proj2 NACC))) as ACTF.
assert (WMFE : wmono asegs mE mF) by (apply (wmono_trans asegs mE m mF); [exact WME| cps_wmono]).
assert (PFFE : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE mF).
{ apply (pres_fp_trans _ _ _ _ mE m mF); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_EXc. do 20 eexists. exists jF, owsF, sws, sF, ffF.
split; [eassumption|]. split; [exact FRM|].
split.
{ unfold nbctx. split; [exact MIF|]. split; [exact STF|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [exact P1|]. split; [exact EXBF|]. split; [rewrite JEXCF; exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split; [exact JOKF|].
split; [exact CBOK|]. split; [exact NINVF|].
split; [exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB mF D bs) BDAT) Hbs)) BSIDE))|].
split; [exact BOK|]. split; [exact BSZ|].
split; [exact OWF|]. split; [exact LOWF|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SLF SV)|].
split; [exact (conj FF0 (conj FFp (conj FFg (conj FFl (conj FFq (conj FFk (conj FFi (conj FFe (conj FFj FFiq)))))))))|].
split; [exact FFOK|].
split; [exists rest; exact SH|].
split; [exact (af_client_consts RT AF Σ mF ARTF)|]. split; [exact (AF_LIB Σ mF ARTF)|]. split; [exact JEXCF| exact JISVF]. }
split; [unfold slots_EL; cbn; repeat split; first [assumption | reflexivity | rewrite SUB3; reflexivity]|].
split; [cbn; reflexivity|].
split; [exact SAT|]. split; [exact EMOF|]. split; [exact BP'|].
split; [exact (conj ARTF (conj (conj ACOF (conj ACAF ACTF)) (conj WMFE PFFE)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
Qed.

Lemma nbE_iter : forall (bp sub : Z) (st : nb_state bptr) (b : bits_st bptr) (st1 : nb_state bptr) (b1 : bits_st bptr),
0 <= sub < 4 -> subframe_pure (smr_sm r) olp sub st b = Some (st1, b1) ->
cps asegs (at_ELc RT PMc X Σ0 mE r mo olp bp sub st b)
(fun c => exists bp', 17 <= bp' <= 144 /\ ((sub < 3 /\ at_ELc RT PMc X Σ0 mE r mo olp bp' (sub + 1) st1 b1 c)
\/ (sub = 3 /\ at_EXc RT PMc X Σ0 mE r mo olp bp' st1 b1 c))).
Proof.
intros bp sub st b st1 b1 SUB SFP.
unfold subframe_pure in SFP.
assert (LTKx : exists k, sm_ltp_unquant (smr_sm r) = Some k)
by (destruct (sm_ltp_unquant (smr_sm r)); [eexists; reflexivity| discriminate SFP]).
destruct LTKx as (k & LTK). rewrite LTK in SFP.
assert (INKx : exists ki, sm_innovation_unquant (smr_sm r) = Some ki)
by (destruct (sm_innovation_unquant (smr_sm r)); [eexists; reflexivity| discriminate SFP]).
destruct INKx as (ki & INK). rewrite INK in SFP.
cbv zeta in SFP.
assert (EB : (if nb_submodeID st =? 1 then exists v, voc_loop VOC_FUEL (nb_voc_offset st) olp = Some v /\ st1 = set_nb_voc_offset st (v - NB_SUBFRAME_SIZE) else st1 = st)
/\ b1 = nbE_bJ k ki b).
{ destruct (nb_submodeID st =? 1).
- destruct (voc_loop VOC_FUEL (nb_voc_offset st) olp) as [v|]; [| discriminate SFP]. injection SFP as <- <-. split; [exists v; split; reflexivity| reflexivity].
- injection SFP as <- <-. split; reflexivity. }
destruct EB as (EST1 & ->).
intros T c Hc Hk.
apply (X099.nbE_A RT AF MST AF_LIB PMc FDO MSTa X NXOK TP Σ0 fr0 PD ND fh kh NSIG mE r mo olp LTP INN bp sub st b k ki SUB LTK INK T c Hc). intros c' (bp' & HJ).
assert (BP' : 17 <= bp' <= 144)
by (destruct HJ as (Σ' & Fx & fc & m & xra & s3 & s11 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & bpx
& _ & _ & _ & _ & _ & _ & B & _); exact B).
apply (nbE_B1 bp' sub st (nbE_bJ k ki b) T c' HJ). intros c'' H3.
apply (nbE_B2 bp' sub st (nbE_bJ k ki b) st1 EST1 T c'' H3). intros c3 H3'.
apply Hk. exists bp'. split; [exact BP'| exact H3'].
Qed.

Lemma nbE_loop : forall (n : nat) (bp sub : Z) (st : nb_state bptr) (b : bits_st bptr) (st' : nb_state bptr) (b' : bits_st bptr),
(1 <= n)%nat -> Z.of_nat n + sub = 4 -> 0 <= sub -> subframes_pure n sub (smr_sm r) olp st b = Some (st', b') ->
cps asegs (at_ELc RT PMc X Σ0 mE r mo olp bp sub st b) (fun c => exists bp', 17 <= bp' <= 144 /\ at_EXc RT PMc X Σ0 mE r mo olp bp' st' b' c).
Proof.
induction n as [|n IH]; intros bp sub st b st' b' N1 HN H0 SFS; [lia|].
cbn [subframes_pure] in SFS.
destruct (subframe_pure (smr_sm r) olp sub st b) as [[st1 b1]|] eqn:SF1; [| discriminate SFS].
intros T c Hc Hk.
apply (nbE_iter bp sub st b st1 b1 ltac:(lia) SF1 T c Hc). intros c' (bp' & BP' & [(S3 & H1) | (S3 & H1)]).
- destruct n as [|n]; [lia|].
apply (IH bp' (sub + 1) st1 b1 st' b' ltac:(lia) ltac:(lia) ltac:(lia) SFS T c' H1 Hk).
- destruct n as [|n]; [| lia]. cbn [subframes_pure] in SFS. injection SFS as <- <-.
apply Hk. exists bp'. split; [exact BP'| exact H1].
Qed.
End NbEB.
