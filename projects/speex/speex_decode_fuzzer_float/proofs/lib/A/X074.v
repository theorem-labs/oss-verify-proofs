(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1qy X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X000 X04b X00c X07z X05o X05p X05s X05t
X0ae X09j X09u X0af X09x X09p X0ab X09l X0a4 X0a5
X05l X05e X05c X05j X05i X06c X05m X09f X08y X09e X06d X069 X068 X07m
X071 X06v X06y X06u X073 X07j X072 X079 X07h
X077 X076 X07f X07e X07b X07a X07c X06o X07d.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X106 X10j X10c X10x X108 X10q X10r X0wb X0w9 X0wg X0wf X0x5 X0zq X0x2 X0x1 X0xn X0xq X0xm X0xu X0ya X0xt X0y0 X0y8 X0y6 X0y5 X0y2 X0y1 X0y3 X0xg X0y4.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Loops.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_drv : forall y, in_ranges IO_FP y -> ~ drv_cell y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis DEC : forall d, dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Hypothesis ISAVE : forall (d d' : dec_state bptr) b q ret b' q',
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
isave_ok d -> isave_ok d'.
Hypothesis RF : speex_bits_read_from_cps RT OUT_rep ERR_rep IO_FP.
Hypothesis BCMP : bcmp_icontract RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Hypothesis FD2 : fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Hypothesis HDR : h_hdr_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Hypothesis HCH : h_chunk_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Hypothesis HPN : h_pnext_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Hypothesis HPX : h_pexit_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Hypothesis HPB : h_page_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.

Definition KPOST (o : outcome unit) (nbr brem0 : Z) : config -> Prop :=
fun c => (o = Returned /\ at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c) \/ (exists h1, o = Cont h1 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 nbr brem0 c).

Lemma cpsE_with : forall P e Q (phi : Prop), (forall c, P c -> phi) -> (phi -> cpsE bsegs P e Q) -> cpsE bsegs P e Q.
Proof. intros P e Q phi H1 H2 T c Hc Hk. exact (H2 (H1 c Hc) T c Hc Hk). Qed.
Lemma rz_emit_nil : forall c T, realizes bsegs c T -> realizes bsegs c (t_emit [] T).
Proof. intros c T R. eapply rz_conseq; [exact R|]. apply t_eq_sym. apply t_emit_nil_eq. eapply realizes_nonempty. exact R. Qed.
Lemma rz_emit_app : forall c e1 e2 T, realizes bsegs c (t_emit e1 (t_emit e2 T)) -> realizes bsegs c (t_emit (e1 ++ e2) T).
Proof. intros c e1 e2 T R. eapply rz_conseq; [exact R| apply t_eq_sym, t_emit_app]. Qed.
Lemma bs_nil : forall (q : pst) bs, p_err q = p_err q ++ bs -> bs = [].
Proof. intros q bs E. apply (app_inv_head (p_err q)). rewrite app_nil_r. symmetry. exact E. Qed.
Lemma bs_split : forall (q q1 q' : pst) bs bs1 bs2, p_err q' = p_err q ++ bs -> p_err q1 = p_err q ++ bs1 -> p_err q' = p_err q1 ++ bs2 -> bs = bs1 ++ bs2.
Proof. intros q q1 q' bs bs1 bs2 H H0 H1. rewrite H1, H0, <- app_assoc in H. exact (eq_sym (app_inv_head _ _ _ H)). Qed.
Lemma evw_nil : Spec.X1nu.evw 2 [] = [].
Proof. reflexivity. Qed.

Lemma at_KH_facts : forall h pno nbr brem0 c, at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0 c ->
h_eos h = 0 /\ (h_packet_count h = 0 -> h_st h = None).
Proof.
intros h pno nbr brem0 c Hc. split.
- destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E0' & _). exact E0'.
- intros P0. destruct Hc as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HR & _). destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STPC & _).
destruct (h_st h); [exfalso; exact (STPC P0)| reflexivity].
Qed.

Definition h_chunk0_cps : Prop := hinv_ok OUT_rep IO_FP X -> x_size X = 0 -> x_d X <= x_lo X ->
cps bsegs (at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 (h_init X))
(h_after_pageout RT OUT_rep ERR_rep IO_FP X F0 fs0 (ch_h1 X (h_init X)) (ch_nbr (h_init X)) (h_bytes_remaining (h_init X))).
Hypothesis HCH0 : h_chunk0_cps.

Lemma h_ss_step : hinv_ok OUT_rep IO_FP X -> forall fuel,
(forall h pno nbr brem0 q o q' bs, prun (hP_packet_loop fuel h pno) q = Some (o, q') -> p_err q' = p_err q ++ bs ->
cpsE bsegs (at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0) (Spec.X1nu.evw 2 bs) (KPOST o nbr brem0)) ->
forall (h1 : hstate unit) (op : packet) (pno nbr brem0 : Z) (q : pst) (o : outcome unit) (q' : pst) bs,
pkt_cases fuel h1 (h_os h1) op pno q o q' -> p_err q' = p_err q ++ bs ->
cpsE bsegs (at_SS RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 op pno nbr brem0) (Spec.X1nu.evw 2 bs) (KPOST o nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF FD2 HDR.
intros HX fuel IH h1 op pno nbr brem0 q o q' bs CASES EB.
pose proof (h_ssw_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV X F0 fs0 HX h1 op pno nbr brem0) as SSW.
unfold pkt_cases in CASES.
destruct CASES as [(SC & EO & EQ) | (SN & SE & [(P0 & ph & q1 & EPH & PHC) | [(PN & PLE & RUN) | (PN & PGT & d & b & q1 & st' & b' & q2 & ESt & ERF & EDL & RUN)]])].
-
subst q'. rewrite (bs_nil q bs EB), evw_nil. apply cpsE_nil. eapply cps_conseq; [exact SSW| intros c Hc; exact Hc|].
intros c [(_ & HPNc) | [(SN' & SE' & _) | [(SN' & SE' & _) | (SN' & SE' & _)]]];
[| exfalso; destruct SC as [SC|SC]; [exact (SN' SC)| exact (SC SE')] ..].
right. exists (set_serialno h1 (pk_sser h1 (h_os h1) op)). split; [exact EO| exact HPNc].
-
destruct (app_process_header _ _ _ q ph q1 EPH) as (bsH & EBH).
pose proof (HDR HX (set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 q q1 ph bsH EPH EBH) as HDRE.
destruct ph as [h3|].
+ destruct (app_packet_loop _ _ _ q1 o q' PHC) as (bsR & EBR).
rewrite (bs_split q q1 q' bs bsH bsR EB EBH EBR), Spec.X1nu.evw_app.
eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & _ & HHP) | [(_ & _ & PN' & _) | (_ & _ & PN' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| | exfalso; exact (PN' P0) ..].
apply rz_emit_app. refine (HDRE _ c HHP _). intros c' HKH. exact (IH _ pno nbr brem0 q1 o q' bsR PHC EBR T c' HKH Hk).
+ destruct PHC as (EO & ->).
assert (EBS : bs = bsH) by (rewrite EBH in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & _ & HHP) | [(_ & _ & PN' & _) | (_ & _ & PN' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| | exfalso; exact (PN' P0) ..].
refine (HDRE T c HHP _). intros c' HXT. apply Hk. left. split; [exact EO| exact HXT].
-
eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & P0' & _) | [(_ & _ & _ & _ & HKT) | (_ & _ & _ & PGT' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| exfalso; exact (PN P0')| | exfalso; lia].
refine (h_kt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X F0 fs0 HX _ pno nbr brem0 _ c HKT _).
intros c' [(E0' & HKH) | (E1 & HPNc)].
+ exact (IH _ pno nbr brem0 q o q' bs RUN EB T c' HKH Hk).
+ destruct (pkt_eos1 fuel (incr_packet_count (set_serialno h1 (pk_sser h1 (h_os h1) op))) pno q o q'
ltac:(cbn [incr_packet_count h_eos]; lia) RUN) as (EO & ->).
rewrite (bs_nil q bs EB), evw_nil. apply rz_emit_nil. apply Hk. right. eexists. split; [exact EO| exact HPNc].
-
destruct (read_from_appends _ _ _ q b q1 ERF) as (bs1 & EB1).
destruct (app_decode_loop _ _ _ q1 (st', b') q2 EDL) as (bs2 & EB2).
destruct (app_packet_loop _ _ _ q2 o q' RUN) as (bsR & EBR).
assert (EBD : p_err q2 = p_err q ++ (bs1 ++ bs2)) by (rewrite EB2, EB1, app_assoc; reflexivity).
rewrite (bs_split q q2 q' bs (bs1 ++ bs2) bsR EB EBD EBR), Spec.X1nu.evw_app.
eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & P0' & _) | [(_ & _ & _ & PLE' & _) | (_ & _ & _ & _ & HRF)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| exfalso; exact (PN P0')| exfalso; lia|].
apply rz_emit_app.
refine (h_data_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF X F0 fs0 FD2 HX
(set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 q q1 q2 b d st' b' (bs1 ++ bs2) ESt ERF EDL EBD _ c HRF _).
intros c' HKT.
refine (h_kt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X F0 fs0 HX _ (pno + 1) nbr brem0 _ c' HKT _).
intros c'' [(E0' & HKH) | (E1 & HPNc)].
+ exact (IH _ (pno + 1) nbr brem0 q2 o q' bsR RUN EBR T c'' HKH Hk).
+ destruct (pkt_eos1 fuel (incr_packet_count (set_bits_st (set_serialno h1 (pk_sser h1 (h_os h1) op)) b' (Some st') (if pk_e_o_s op =? 0 then 0 else 1)))
(pno + 1) q2 o q' ltac:(cbn [incr_packet_count h_eos]; lia) RUN) as (EO & ->).
rewrite (bs_nil q2 bsR EBR), evw_nil. apply rz_emit_nil. apply Hk. right. eexists. split; [exact EO| exact HPNc].
Qed.

Theorem h_kloop_ok : hinv_ok OUT_rep IO_FP X -> forall fuel (h : hstate unit) (pno nbr brem0 : Z) (q : pst) (o : outcome unit) (q' : pst) bs,
prun (hP_packet_loop fuel h pno) q = Some (o, q') -> p_err q' = p_err q ++ bs ->
cpsE bsegs (at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0) (Spec.X1nu.evw 2 bs) (KPOST o nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP FD2 HDR.
intros HX fuel. induction fuel as [|fuel IH]; intros h pno nbr brem0 q o q' bs RUN EB.
{ unfold hP_packet_loop in RUN. cbn [packet_loop] in RUN. rewrite prun_munr in RUN. discriminate RUN. }
apply (cpsE_with _ _ _ _ (at_KH_facts h pno nbr brem0)). intros (E0 & PC0).
pose proof (h_kss_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV BCMP X F0 fs0 HX h pno nbr brem0) as KSS.
destruct (pkt_step fuel h pno q o q' E0 PC0 RUN) as (r & opo & os & EPO & [(RN & EO & EQ) | (R1 & op & EOP & CASES)]).
- subst q'. rewrite (bs_nil q bs EB), evw_nil. apply cpsE_nil.
eapply cps_conseq; [exact (KSS r opo os EPO)| intros c Hc; exact Hc|].
intros c [(_ & HPNc) | (R1 & _)]; [| exfalso; exact (RN R1)].
right. exists (set_ogg h (h_oy h) os). split; [exact EO| exact HPNc].
- eapply cps_cpsE; [exact (KSS r opo os EPO)|].
intros T c [(RN & _) | (_ & op' & EOP' & HSS)] Hk; [exfalso; exact (RN R1)|].
rewrite EOP in EOP'. injection EOP' as <-.
exact (h_ss_step HX fuel IH _ op pno nbr brem0 q o q' bs CASES EB T c HSS Hk).
Qed.

Lemma ploop_step : forall fuel (h : hstate unit) q o q', prun (hP_page_loop (S fuel) h) q = Some (o, q') ->
exists r oog oy, ogg_sync_pageout (h_oy h) = Some ((r, oog), oy) /\
( (r <> 1 /\ o = Cont (set_ogg h oy (h_os h)) /\ q' = q)
\/ (r = 1 /\ exists og h3 q3, oog = Some og /\ prun (pb_pre (set_ogg h oy (h_os h)) og) q = Some (h3, q3) /\
match granule_step h3 (page_header oy og) with
| None => exists q4, prun (hP_cleanup h3) q3 = Some (tt, q4) /\ o = Returned /\ q' = q4
| Some skip => exists o1 q4,
prun (hP_packet_loop (packet_fuel (h_os (set_granule h3 (ogg_page_granulepos (page_header oy og)) skip)))
(set_granule h3 (ogg_page_granulepos (page_header oy og)) skip) 0) q3 = Some (o1, q4) /\
match o1 with Returned => o = Returned /\ q' = q4 | Cont h5 => prun (hP_page_loop fuel h5) q4 = Some (o, q') end
end)).
Proof.
intros fuel h q o q' H. unfold hP_page_loop in H. cbn [page_loop] in H.
destruct (ogg_sync_pageout (h_oy h)) as [[[r oog] oy]|] eqn:EPO; [| rewrite prun_munr in H; discriminate H].
exists r, oog, oy. split; [reflexivity|].
destruct (Z.eqb_spec r 1) as [R1|RN].
2:{ left. cbn [negb] in H. rewrite prun_ret in H. injection H as <- <-. split; [exact RN| split; reflexivity]. }
right. split; [exact R1|]. cbn [negb] in H.
destruct oog as [og|]; [| rewrite prun_munr in H; discriminate H].
rewrite prun_bind in H.
lazymatch type of H with
| match prun ?C q with _ => _ end = _ => destruct (prun C q) as [[h2 q2]|] eqn:E1; [| discriminate H]
end.
rewrite prun_bind in H.
lazymatch type of H with
| match prun ?C q2 with _ => _ end = _ => destruct (prun C q2) as [[[r2 os2] q3]|] eqn:E2; [| discriminate H]
end.
cbn beta iota in H.
set (hR := if negb (ogg_page_serialno (page_header oy og) =? os_serialno (h_os h2))
then let '(_, os) := ogg_stream_reset_serialno (h_os h2) (ogg_page_serialno (page_header oy og)) in set_ogg h2 (h_oy h2) os else h2) in *.
exists og, (set_ogg hR (h_oy hR) os2), q3. split; [reflexivity|]. split.
{ unfold pb_pre. change (h_oy (set_ogg h oy (h_os h))) with oy. rewrite prun_bind.
assert (E1' : prun (if h_stream_init (set_ogg h oy (h_os h)) =? 0
then X1qy.mbind (ogg_stream_init p_malloc p_free (ogg_page_serialno (page_header oy og)))
(fun ro => X1qy.mret (set_stream_init (set_ogg h oy (h_os h)) (snd ro)))
else X1qy.mret (set_ogg h oy (h_os h))) q = Some (h2, q2)).
{ destruct (h_stream_init (set_ogg h oy (h_os h)) =? 0); [| exact E1].
rewrite prun_bind in E1 |- *. destruct (prun (ogg_stream_init p_malloc p_free (ogg_page_serialno (page_header oy og))) q) as [[[ri osi] qi]|];
[cbn beta iota in E1 |- *; exact E1| discriminate E1]. }
rewrite E1'. cbn beta iota. fold hR. rewrite prun_bind, E2. cbn beta iota. rewrite prun_ret. reflexivity. }
destruct (granule_step (set_ogg hR (h_oy hR) os2) (page_header oy og)) as [skip|] eqn:EG.
- rewrite prun_bind in H.
lazymatch type of H with
| match prun ?C q3 with _ => _ end = _ => destruct (prun C q3) as [[o1 q4]|] eqn:E3; [| discriminate H]
end.
exists o1, q4. split; [exact E3|]. destruct o1 as [h5|]; [exact H| rewrite prun_ret in H; injection H as <- <-; split; reflexivity].
- rewrite prun_bind in H.
lazymatch type of H with
| match prun ?C q3 with _ => _ end = _ => destruct (prun C q3) as [[u q4]|] eqn:E3; [| discriminate H]
end.
cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. exists q4. destruct u. split; [exact E3| split; reflexivity].
Qed.

Definition PLPOST (o : outcome unit) (nbr brem0 : Z) : config -> Prop :=
fun c => (o = Returned /\ at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c) \/ (exists h1, o = Cont h1 /\ at_PX RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 nbr brem0 c).

Theorem h_ploop_ok : hinv_ok OUT_rep IO_FP X -> forall fuel (h : hstate unit) (nbr brem0 : Z) (q : pst) (o : outcome unit) (q' : pst) bs,
prun (hP_page_loop fuel h) q = Some (o, q') -> p_err q' = p_err q ++ bs ->
cpsE bsegs (h_after_pageout RT OUT_rep ERR_rep IO_FP X F0 fs0 h nbr brem0) (Spec.X1nu.evw 2 bs) (PLPOST o nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP FD2 HDR HPN HPB.
intros HX fuel. induction fuel as [|fuel IH]; intros h nbr brem0 q o q' bs RUN EB.
{ unfold hP_page_loop in RUN. cbn [page_loop] in RUN. rewrite prun_munr in RUN. discriminate RUN. }
destruct (ploop_step fuel h q o q' RUN) as (r & oog & oy & EPO & [(RN & EO & EQ) | (R1 & og & h3 & q3 & EOG & EPB & GR)]).
-
subst q'. rewrite (bs_nil q bs EB), evw_nil. apply cpsE_nil.
intros T c (r' & oog' & oy2 & EPO' & [(R1' & og' & EOG' & HPB') | (RN' & HPX')]) Hk;
rewrite EPO in EPO'; injection EPO' as <- <- <-; [exfalso; exact (RN R1')|].
apply Hk. right. exists (set_ogg h oy (h_os h)). split; [exact EO| exact HPX'].
-
subst oog.
intros T c (r' & oog' & oy2 & EPO' & [(R1' & og' & EOG' & HPB') | (RN' & HPX')]) Hk;
rewrite EPO in EPO'; injection EPO' as <- <- <-; [| exfalso; exact (RN' R1)].
injection EOG' as <-.
refine (HPB HX (set_ogg h oy (h_os h)) og nbr brem0 q q3 h3 EPB (t_emit (Spec.X1nu.evw 2 bs) T) c HPB' _).
intros c1 (-> & GPOST). change (h_oy (set_ogg h oy (h_os h))) with oy in GPOST.
destruct (granule_step h3 (page_header oy og)) as [skip|] eqn:EG.
+
destruct GR as (o1 & q4 & RUNK & GR).
destruct (app_packet_loop _ _ _ q o1 q4 RUNK) as (bsK & EBK).
set (h4 := set_granule h3 (ogg_page_granulepos (page_header oy og)) skip) in *.
destruct o1 as [h5|].
*
destruct (app_page_loop _ _ q4 o q' GR) as (bsR & EBR).
rewrite (bs_split q q4 q' bs bsK bsR EB EBK EBR), Spec.X1nu.evw_app. apply rz_emit_app.
destruct GPOST as [(E40 & HKH) | (E4N & HPN4)].
-- refine (h_kloop_ok HX _ h4 0 nbr brem0 q (Cont h5) q4 bsK RUNK EBK _ c1 HKH _).
intros c2 [(ER & _) | (h6 & EC & HPN6)]; [discriminate ER|]. injection EC as <-.
refine (HPN HX h5 nbr brem0 _ c2 HPN6 _). intros c3 HAP.
exact (IH h5 nbr brem0 q4 o q' bsR GR EBR T c3 HAP Hk).
-- destruct (pkt_eos1 _ h4 0 q (Cont h5) q4 E4N RUNK) as (EC & ->). injection EC as EC'. subst h5.
rewrite (bs_nil q bsK EBK), evw_nil. apply rz_emit_nil.
refine (HPN HX h4 nbr brem0 _ c1 HPN4 _). intros c3 HAP.
exact (IH h4 nbr brem0 q o q' bsR GR EBR T c3 HAP Hk).
*
destruct GR as (EO & ->).
assert (EBS : bs = bsK) by (rewrite EBK in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
destruct GPOST as [(E40 & HKH) | (E4N & HPN4)].
-- refine (h_kloop_ok HX _ h4 0 nbr brem0 q Returned q4 bsK RUNK EBK T c1 HKH _).
intros c2 [(_ & HXT) | (h6 & EC & _)]; [| discriminate EC]. apply Hk. left. split; [exact EO| exact HXT].
-- destruct (pkt_eos1 _ h4 0 q Returned q4 E4N RUNK) as (EC & _). discriminate EC.
+
destruct GR as (q4 & ECL & EO & ->). rewrite prun_cleanup in ECL. injection ECL as <-.
rewrite (bs_nil q bs EB), evw_nil. apply rz_emit_nil. apply Hk. left. split; [exact EO| exact GPOST].
Qed.

Lemma cloop_step : forall fuel (h : hstate unit) q o q', prun (hP_chunk_loop (S fuel) (x_payload X) h) q = Some (o, q') ->
0 <= sy_storage (h_oy h) -> 0 <= ch_nbr h -> ch_nbr h + (sy_fill (h_oy h) - sy_returned (h_oy h)) + 4096 < 2^31 ->
0 <= sy_fill (h_oy h) - sy_returned (h_oy h) ->
exists o1 q1, prun (hP_page_loop (page_fuel (h_oy (ch_h1 X h))) (ch_h1 X h)) q = Some (o1, q1) /\
match o1 with
| Returned => o = Returned /\ q' = q1
| Cont h2 => if h_bytes_remaining h2 <=? 0 then o = Cont h2 /\ q' = q1 else prun (hP_chunk_loop fuel (x_payload X) h2) q1 = Some (o, q')
end.
Proof.
intros fuel h q o q' H S0 N0 NB PF0. unfold hP_chunk_loop in H. cbn [chunk_loop] in H.
change (if CHUNK <? h_bytes_remaining h then CHUNK else h_bytes_remaining h) with (ch_nbr h) in H.
rewrite prun_bind in H.
destruct (prun (ogg_sync_buffer p_malloc p_realloc p_free (h_oy h) (ch_nbr h)) q) as [[[data oy] q1]|] eqn:ESB; [| discriminate H].
destruct (sync_buffer_prun (h_oy h) (ch_nbr h) q (data, oy) q1 ESB S0 N0 NB PF0) as (ER & ->).
cbn beta iota in H.
assert (HD : (match data with Some _ => true | None => negb (0 <? ch_nbr h) end) = true).
{ destruct data; [reflexivity|]. destruct (0 <? ch_nbr h); [rewrite prun_munr in H; discriminate H| reflexivity]. }
destruct (ogg_sync_wrote (match data with Some (_, off) => sync_write oy off (ztake (ch_nbr h) (x_payload X)) | None => oy end) (ch_nbr h))
as [rw oyw] eqn:EW.
assert (ECH : ch_h1 X h = set_bytes_remaining (set_ogg h oy (h_os h)) oyw (h_bytes_remaining (set_ogg h oy (h_os h)) - ch_nbr h)).
{ unfold ch_h1. rewrite <- ER. cbn beta iota zeta. unfold bptr. rewrite EW. reflexivity. }
rewrite ECH.
assert (H' : prun (X1qy.mbind (hP_page_loop (page_fuel (h_oy (set_bytes_remaining (set_ogg h oy (h_os h)) oyw (h_bytes_remaining (set_ogg h oy (h_os h)) - ch_nbr h))))
(set_bytes_remaining (set_ogg h oy (h_os h)) oyw (h_bytes_remaining (set_ogg h oy (h_os h)) - ch_nbr h)))
(fun o => match o with Cont h => if h_bytes_remaining h <=? 0 then X1qy.mret (Cont h) else hP_chunk_loop fuel (x_payload X) h
| Returned => X1qy.mret Returned end)) q = Some (o, q')).
{ destruct data as [[p off]|]; [exact H|]. destruct (0 <? ch_nbr h); [discriminate HD| exact H]. }
clear H HD. rewrite prun_bind in H'.
lazymatch type of H' with
| match prun ?C q with _ => _ end = _ => destruct (prun C q) as [[o1 q2]|] eqn:EPL; [| discriminate H']
end.
exists o1, q2. split; [first [exact EPL| reflexivity]|].
destruct o1 as [h2|]; [| rewrite prun_ret in H'; injection H' as <- <-; split; reflexivity].
destruct (h_bytes_remaining h2 <=? 0); [rewrite prun_ret in H'; injection H' as <- <-; split; reflexivity| exact H'].
Qed.

Definition CLPOST (o : outcome unit) : config -> Prop :=
fun c => (o = Returned /\ at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c) \/ (exists h1, o = Cont h1 /\ at_CL RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 c).

Lemma at_CH_hpure : forall h c, at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 h c -> hpure X h.
Proof. intros h c Hc. destruct Hc as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HR & _). destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP). exact HP. Qed.

Theorem h_cloop_ok : hinv_ok OUT_rep IO_FP X -> forall fuel (h : hstate unit) (q : pst) (o : outcome unit) (q' : pst) bs,
(0 < h_bytes_remaining h \/ (h = h_init X /\ x_size X = 0 /\ x_d X <= x_lo X)) ->
prun (hP_chunk_loop fuel (x_payload X) h) q = Some (o, q') -> p_err q' = p_err q ++ bs ->
cpsE bsegs (at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 h) (Spec.X1nu.evw 2 bs) (CLPOST o).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP FD2 HDR HCH HCH0 HPN HPX HPB.
intros HX fuel. induction fuel as [|fuel IH]; intros h q o q' bs BR RUN EB.
{ unfold hP_chunk_loop in RUN. cbn [chunk_loop] in RUN. rewrite prun_munr in RUN. discriminate RUN. }
apply (cpsE_with _ _ _ _ (at_CH_hpure h)). intros HP.
assert (BR0 : 0 <= h_bytes_remaining h) by (destruct BR as [BR|(-> & XS0 & _)]; [lia| unfold h_init, x_size in *; cbn [h_bytes_remaining]; lia]).
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP as (_ & _ & (S0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BRM & _ & PND & CNS & _).
assert (NB : 0 <= ch_nbr h <= 200) by (unfold ch_nbr, CHUNK; destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia).
destruct (cloop_step fuel h q o q' RUN S0 (proj1 NB) ltac:(unfold h_consumed, h_pend in *; lia) ltac:(unfold h_pend in PND; lia))
as (o1 & q1 & RUNP & REST).
destruct (app_page_loop _ _ q o1 q1 RUNP) as (bsP & EBP).
assert (CHS : cps bsegs (at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 h) (h_after_pageout RT OUT_rep ERR_rep IO_FP X F0 fs0 (ch_h1 X h) (ch_nbr h) (h_bytes_remaining h))).
{ destruct BR as [BR|(-> & XS0 & XD0)]; [exact (HCH HX h BR)| exact (HCH0 HX XS0 XD0)]. }
eapply cps_cpsE; [exact CHS|].
destruct o1 as [h2|].
- destruct (Z.leb_spec (h_bytes_remaining h2) 0) as [BL|BG].
+
destruct REST as (EO & ->).
assert (EBS : bs = bsP) by (rewrite EBP in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
intros T c HAP Hk.
refine (h_ploop_ok HX _ (ch_h1 X h) (ch_nbr h) (h_bytes_remaining h) q (Cont h2) q1 bsP RUNP EBP _ c HAP _).
intros c1 [(ER & _) | (h3 & EC & HPX3)]; [discriminate ER|]. injection EC as EC'. subst h3.
refine (HPX HX h2 (ch_nbr h) (h_bytes_remaining h) T c1 HPX3 _).
intros c2 [(BG' & _) | (_ & HCL)]; [lia|]. apply Hk. right. exists h2. split; [exact EO| exact HCL].
+
destruct (app_chunk_loop _ _ _ q1 o q' REST) as (bsR & EBR).
rewrite (bs_split q q1 q' bs bsP bsR EB EBP EBR), Spec.X1nu.evw_app.
intros T c HAP Hk. apply rz_emit_app.
refine (h_ploop_ok HX _ (ch_h1 X h) (ch_nbr h) (h_bytes_remaining h) q (Cont h2) q1 bsP RUNP EBP _ c HAP _).
intros c1 [(ER & _) | (h3 & EC & HPX3)]; [discriminate ER|]. injection EC as EC'. subst h3.
refine (HPX HX h2 (ch_nbr h) (h_bytes_remaining h) _ c1 HPX3 _).
intros c2 [(_ & HCH2) | (BL' & _)]; [| lia].
exact (IH h2 q1 o q' bsR (or_introl BG) REST EBR T c2 HCH2 Hk).
-
destruct REST as (EO & ->).
assert (EBS : bs = bsP) by (rewrite EBP in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
intros T c HAP Hk.
refine (h_ploop_ok HX _ (ch_h1 X h) (ch_nbr h) (h_bytes_remaining h) q Returned q1 bsP RUNP EBP T c HAP _).
intros c1 [(_ & HXT) | (h3 & EC & _)]; [| discriminate EC]. apply Hk. left. split; [exact EO| exact HXT].
Qed.
End Loops.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Loops.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_drv : forall y, in_ranges IO_FP y -> ~ drv_cell y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis DEC : forall d, dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Hypothesis ISAVE : forall (d d' : dec_state bptr) b q ret b' q',
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
isave_ok d -> isave_ok d'.
Hypothesis RF : speex_bits_read_from_cps RT OUT_rep ERR_rep IO_FP.
Hypothesis BCMP : bcmp_icontract RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Hypothesis FD2 : fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Hypothesis HDR : h_hdr_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Hypothesis HCH : h_chunk_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Hypothesis HPN : h_pnext_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Hypothesis HPX : h_pexit_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Hypothesis HPB : h_page_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.

Definition KPOST (o : outcome unit) (nbr brem0 : Z) : config -> Prop :=
fun c => (o = Returned /\ at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c) \/ (exists h1, o = Cont h1 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 nbr brem0 c).

Lemma cpsE_with : forall P e Q (phi : Prop), (forall c, P c -> phi) -> (phi -> cpsE asegs P e Q) -> cpsE asegs P e Q.
Proof. intros P e Q phi H1 H2 T c Hc Hk. exact (H2 (H1 c Hc) T c Hc Hk). Qed.
Lemma rz_emit_nil : forall c T, realizes asegs c T -> realizes asegs c (t_emit [] T).
Proof. intros c T R. eapply rz_conseq; [exact R|]. apply t_eq_sym. apply t_emit_nil_eq. eapply realizes_nonempty. exact R. Qed.
Lemma rz_emit_app : forall c e1 e2 T, realizes asegs c (t_emit e1 (t_emit e2 T)) -> realizes asegs c (t_emit (e1 ++ e2) T).
Proof. intros c e1 e2 T R. eapply rz_conseq; [exact R| apply t_eq_sym, t_emit_app]. Qed.
Lemma bs_nil : forall (q : pst) bs, p_err q = p_err q ++ bs -> bs = [].
Proof. intros q bs E. apply (app_inv_head (p_err q)). rewrite app_nil_r. symmetry. exact E. Qed.
Lemma bs_split : forall (q q1 q' : pst) bs bs1 bs2, p_err q' = p_err q ++ bs -> p_err q1 = p_err q ++ bs1 -> p_err q' = p_err q1 ++ bs2 -> bs = bs1 ++ bs2.
Proof. intros q q1 q' bs bs1 bs2 H H0 H1. rewrite H1, H0, <- app_assoc in H. exact (eq_sym (app_inv_head _ _ _ H)). Qed.
Lemma evw_nil : Spec.X1nu.evw 2 [] = [].
Proof. reflexivity. Qed.

Lemma at_KH_facts : forall h pno nbr brem0 c, at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0 c ->
h_eos h = 0 /\ (h_packet_count h = 0 -> h_st h = None).
Proof.
intros h pno nbr brem0 c Hc. split.
- destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E0' & _). exact E0'.
- intros P0. destruct Hc as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HR & _). destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STPC & _).
destruct (h_st h); [exfalso; exact (STPC P0)| reflexivity].
Qed.

Definition h_chunk0_cps : Prop := hinv_ok OUT_rep IO_FP X -> x_size X = 0 -> x_d X <= x_lo X ->
cps asegs (at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 (h_init X))
(h_after_pageout RT OUT_rep ERR_rep IO_FP X F0 fs0 (ch_h1 X (h_init X)) (ch_nbr (h_init X)) (h_bytes_remaining (h_init X))).
Hypothesis HCH0 : h_chunk0_cps.

Lemma h_ss_step : hinv_ok OUT_rep IO_FP X -> forall fuel,
(forall h pno nbr brem0 q o q' bs, prun (hP_packet_loop fuel h pno) q = Some (o, q') -> p_err q' = p_err q ++ bs ->
cpsE asegs (at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0) (Spec.X1nu.evw 2 bs) (KPOST o nbr brem0)) ->
forall (h1 : hstate unit) (op : packet) (pno nbr brem0 : Z) (q : pst) (o : outcome unit) (q' : pst) bs,
pkt_cases fuel h1 (h_os h1) op pno q o q' -> p_err q' = p_err q ++ bs ->
cpsE asegs (at_SS RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 op pno nbr brem0) (Spec.X1nu.evw 2 bs) (KPOST o nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF FD2 HDR.
intros HX fuel IH h1 op pno nbr brem0 q o q' bs CASES EB.
pose proof (h_ssw_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV X F0 fs0 HX h1 op pno nbr brem0) as SSW.
unfold pkt_cases in CASES.
destruct CASES as [(SC & EO & EQ) | (SN & SE & [(P0 & ph & q1 & EPH & PHC) | [(PN & PLE & RUN) | (PN & PGT & d & b & q1 & st' & b' & q2 & ESt & ERF & EDL & RUN)]])].
-
subst q'. rewrite (bs_nil q bs EB), evw_nil. apply cpsE_nil. eapply cps_conseq; [exact SSW| intros c Hc; exact Hc|].
intros c [(_ & HPNc) | [(SN' & SE' & _) | [(SN' & SE' & _) | (SN' & SE' & _)]]];
[| exfalso; destruct SC as [SC|SC]; [exact (SN' SC)| exact (SC SE')] ..].
right. exists (set_serialno h1 (pk_sser h1 (h_os h1) op)). split; [exact EO| exact HPNc].
-
destruct (app_process_header _ _ _ q ph q1 EPH) as (bsH & EBH).
pose proof (HDR HX (set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 q q1 ph bsH EPH EBH) as HDRE.
destruct ph as [h3|].
+ destruct (app_packet_loop _ _ _ q1 o q' PHC) as (bsR & EBR).
rewrite (bs_split q q1 q' bs bsH bsR EB EBH EBR), Spec.X1nu.evw_app.
eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & _ & HHP) | [(_ & _ & PN' & _) | (_ & _ & PN' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| | exfalso; exact (PN' P0) ..].
apply rz_emit_app. refine (HDRE _ c HHP _). intros c' HKH. exact (IH _ pno nbr brem0 q1 o q' bsR PHC EBR T c' HKH Hk).
+ destruct PHC as (EO & ->).
assert (EBS : bs = bsH) by (rewrite EBH in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & _ & HHP) | [(_ & _ & PN' & _) | (_ & _ & PN' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| | exfalso; exact (PN' P0) ..].
refine (HDRE T c HHP _). intros c' HXT. apply Hk. left. split; [exact EO| exact HXT].
-
eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & P0' & _) | [(_ & _ & _ & _ & HKT) | (_ & _ & _ & PGT' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| exfalso; exact (PN P0')| | exfalso; lia].
refine (h_kt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X F0 fs0 HX _ pno nbr brem0 _ c HKT _).
intros c' [(E0' & HKH) | (E1 & HPNc)].
+ exact (IH _ pno nbr brem0 q o q' bs RUN EB T c' HKH Hk).
+ destruct (pkt_eos1 fuel (incr_packet_count (set_serialno h1 (pk_sser h1 (h_os h1) op))) pno q o q'
ltac:(cbn [incr_packet_count h_eos]; lia) RUN) as (EO & ->).
rewrite (bs_nil q bs EB), evw_nil. apply rz_emit_nil. apply Hk. right. eexists. split; [exact EO| exact HPNc].
-
destruct (read_from_appends _ _ _ q b q1 ERF) as (bs1 & EB1).
destruct (app_decode_loop _ _ _ q1 (st', b') q2 EDL) as (bs2 & EB2).
destruct (app_packet_loop _ _ _ q2 o q' RUN) as (bsR & EBR).
assert (EBD : p_err q2 = p_err q ++ (bs1 ++ bs2)) by (rewrite EB2, EB1, app_assoc; reflexivity).
rewrite (bs_split q q2 q' bs (bs1 ++ bs2) bsR EB EBD EBR), Spec.X1nu.evw_app.
eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & P0' & _) | [(_ & _ & _ & PLE' & _) | (_ & _ & _ & _ & HRF)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| exfalso; exact (PN P0')| exfalso; lia|].
apply rz_emit_app.
refine (h_data_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF X F0 fs0 FD2 HX
(set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 q q1 q2 b d st' b' (bs1 ++ bs2) ESt ERF EDL EBD _ c HRF _).
intros c' HKT.
refine (h_kt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X F0 fs0 HX _ (pno + 1) nbr brem0 _ c' HKT _).
intros c'' [(E0' & HKH) | (E1 & HPNc)].
+ exact (IH _ (pno + 1) nbr brem0 q2 o q' bsR RUN EBR T c'' HKH Hk).
+ destruct (pkt_eos1 fuel (incr_packet_count (set_bits_st (set_serialno h1 (pk_sser h1 (h_os h1) op)) b' (Some st') (if pk_e_o_s op =? 0 then 0 else 1)))
(pno + 1) q2 o q' ltac:(cbn [incr_packet_count h_eos]; lia) RUN) as (EO & ->).
rewrite (bs_nil q2 bsR EBR), evw_nil. apply rz_emit_nil. apply Hk. right. eexists. split; [exact EO| exact HPNc].
Qed.

Theorem h_kloop_ok : hinv_ok OUT_rep IO_FP X -> forall fuel (h : hstate unit) (pno nbr brem0 : Z) (q : pst) (o : outcome unit) (q' : pst) bs,
prun (hP_packet_loop fuel h pno) q = Some (o, q') -> p_err q' = p_err q ++ bs ->
cpsE asegs (at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0) (Spec.X1nu.evw 2 bs) (KPOST o nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP FD2 HDR.
intros HX fuel. induction fuel as [|fuel IH]; intros h pno nbr brem0 q o q' bs RUN EB.
{ unfold hP_packet_loop in RUN. cbn [packet_loop] in RUN. rewrite prun_munr in RUN. discriminate RUN. }
apply (cpsE_with _ _ _ _ (at_KH_facts h pno nbr brem0)). intros (E0 & PC0).
pose proof (h_kss_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV BCMP X F0 fs0 HX h pno nbr brem0) as KSS.
destruct (pkt_step fuel h pno q o q' E0 PC0 RUN) as (r & opo & os & EPO & [(RN & EO & EQ) | (R1 & op & EOP & CASES)]).
- subst q'. rewrite (bs_nil q bs EB), evw_nil. apply cpsE_nil.
eapply cps_conseq; [exact (KSS r opo os EPO)| intros c Hc; exact Hc|].
intros c [(_ & HPNc) | (R1 & _)]; [| exfalso; exact (RN R1)].
right. exists (set_ogg h (h_oy h) os). split; [exact EO| exact HPNc].
- eapply cps_cpsE; [exact (KSS r opo os EPO)|].
intros T c [(RN & _) | (_ & op' & EOP' & HSS)] Hk; [exfalso; exact (RN R1)|].
rewrite EOP in EOP'. injection EOP' as <-.
exact (h_ss_step HX fuel IH _ op pno nbr brem0 q o q' bs CASES EB T c HSS Hk).
Qed.

Lemma ploop_step : forall fuel (h : hstate unit) q o q', prun (hP_page_loop (S fuel) h) q = Some (o, q') ->
exists r oog oy, ogg_sync_pageout (h_oy h) = Some ((r, oog), oy) /\
( (r <> 1 /\ o = Cont (set_ogg h oy (h_os h)) /\ q' = q)
\/ (r = 1 /\ exists og h3 q3, oog = Some og /\ prun (pb_pre (set_ogg h oy (h_os h)) og) q = Some (h3, q3) /\
match granule_step h3 (page_header oy og) with
| None => exists q4, prun (hP_cleanup h3) q3 = Some (tt, q4) /\ o = Returned /\ q' = q4
| Some skip => exists o1 q4,
prun (hP_packet_loop (packet_fuel (h_os (set_granule h3 (ogg_page_granulepos (page_header oy og)) skip)))
(set_granule h3 (ogg_page_granulepos (page_header oy og)) skip) 0) q3 = Some (o1, q4) /\
match o1 with Returned => o = Returned /\ q' = q4 | Cont h5 => prun (hP_page_loop fuel h5) q4 = Some (o, q') end
end)).
Proof.
intros fuel h q o q' H. unfold hP_page_loop in H. cbn [page_loop] in H.
destruct (ogg_sync_pageout (h_oy h)) as [[[r oog] oy]|] eqn:EPO; [| rewrite prun_munr in H; discriminate H].
exists r, oog, oy. split; [reflexivity|].
destruct (Z.eqb_spec r 1) as [R1|RN].
2:{ left. cbn [negb] in H. rewrite prun_ret in H. injection H as <- <-. split; [exact RN| split; reflexivity]. }
right. split; [exact R1|]. cbn [negb] in H.
destruct oog as [og|]; [| rewrite prun_munr in H; discriminate H].
rewrite prun_bind in H.
lazymatch type of H with
| match prun ?C q with _ => _ end = _ => destruct (prun C q) as [[h2 q2]|] eqn:E1; [| discriminate H]
end.
rewrite prun_bind in H.
lazymatch type of H with
| match prun ?C q2 with _ => _ end = _ => destruct (prun C q2) as [[[r2 os2] q3]|] eqn:E2; [| discriminate H]
end.
cbn beta iota in H.
set (hR := if negb (ogg_page_serialno (page_header oy og) =? os_serialno (h_os h2))
then let '(_, os) := ogg_stream_reset_serialno (h_os h2) (ogg_page_serialno (page_header oy og)) in set_ogg h2 (h_oy h2) os else h2) in *.
exists og, (set_ogg hR (h_oy hR) os2), q3. split; [reflexivity|]. split.
{ unfold pb_pre. change (h_oy (set_ogg h oy (h_os h))) with oy. rewrite prun_bind.
assert (E1' : prun (if h_stream_init (set_ogg h oy (h_os h)) =? 0
then X1qy.mbind (ogg_stream_init p_malloc p_free (ogg_page_serialno (page_header oy og)))
(fun ro => X1qy.mret (set_stream_init (set_ogg h oy (h_os h)) (snd ro)))
else X1qy.mret (set_ogg h oy (h_os h))) q = Some (h2, q2)).
{ destruct (h_stream_init (set_ogg h oy (h_os h)) =? 0); [| exact E1].
rewrite prun_bind in E1 |- *. destruct (prun (ogg_stream_init p_malloc p_free (ogg_page_serialno (page_header oy og))) q) as [[[ri osi] qi]|];
[cbn beta iota in E1 |- *; exact E1| discriminate E1]. }
rewrite E1'. cbn beta iota. fold hR. rewrite prun_bind, E2. cbn beta iota. rewrite prun_ret. reflexivity. }
destruct (granule_step (set_ogg hR (h_oy hR) os2) (page_header oy og)) as [skip|] eqn:EG.
- rewrite prun_bind in H.
lazymatch type of H with
| match prun ?C q3 with _ => _ end = _ => destruct (prun C q3) as [[o1 q4]|] eqn:E3; [| discriminate H]
end.
exists o1, q4. split; [exact E3|]. destruct o1 as [h5|]; [exact H| rewrite prun_ret in H; injection H as <- <-; split; reflexivity].
- rewrite prun_bind in H.
lazymatch type of H with
| match prun ?C q3 with _ => _ end = _ => destruct (prun C q3) as [[u q4]|] eqn:E3; [| discriminate H]
end.
cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. exists q4. destruct u. split; [exact E3| split; reflexivity].
Qed.

Definition PLPOST (o : outcome unit) (nbr brem0 : Z) : config -> Prop :=
fun c => (o = Returned /\ at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c) \/ (exists h1, o = Cont h1 /\ at_PX RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 nbr brem0 c).

Theorem h_ploop_ok : hinv_ok OUT_rep IO_FP X -> forall fuel (h : hstate unit) (nbr brem0 : Z) (q : pst) (o : outcome unit) (q' : pst) bs,
prun (hP_page_loop fuel h) q = Some (o, q') -> p_err q' = p_err q ++ bs ->
cpsE asegs (h_after_pageout RT OUT_rep ERR_rep IO_FP X F0 fs0 h nbr brem0) (Spec.X1nu.evw 2 bs) (PLPOST o nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP FD2 HDR HPN HPB.
intros HX fuel. induction fuel as [|fuel IH]; intros h nbr brem0 q o q' bs RUN EB.
{ unfold hP_page_loop in RUN. cbn [page_loop] in RUN. rewrite prun_munr in RUN. discriminate RUN. }
destruct (ploop_step fuel h q o q' RUN) as (r & oog & oy & EPO & [(RN & EO & EQ) | (R1 & og & h3 & q3 & EOG & EPB & GR)]).
-
subst q'. rewrite (bs_nil q bs EB), evw_nil. apply cpsE_nil.
intros T c (r' & oog' & oy2 & EPO' & [(R1' & og' & EOG' & HPB') | (RN' & HPX')]) Hk;
rewrite EPO in EPO'; injection EPO' as <- <- <-; [exfalso; exact (RN R1')|].
apply Hk. right. exists (set_ogg h oy (h_os h)). split; [exact EO| exact HPX'].
-
subst oog.
intros T c (r' & oog' & oy2 & EPO' & [(R1' & og' & EOG' & HPB') | (RN' & HPX')]) Hk;
rewrite EPO in EPO'; injection EPO' as <- <- <-; [| exfalso; exact (RN' R1)].
injection EOG' as <-.
refine (HPB HX (set_ogg h oy (h_os h)) og nbr brem0 q q3 h3 EPB (t_emit (Spec.X1nu.evw 2 bs) T) c HPB' _).
intros c1 (-> & GPOST). change (h_oy (set_ogg h oy (h_os h))) with oy in GPOST.
destruct (granule_step h3 (page_header oy og)) as [skip|] eqn:EG.
+
destruct GR as (o1 & q4 & RUNK & GR).
destruct (app_packet_loop _ _ _ q o1 q4 RUNK) as (bsK & EBK).
set (h4 := set_granule h3 (ogg_page_granulepos (page_header oy og)) skip) in *.
destruct o1 as [h5|].
*
destruct (app_page_loop _ _ q4 o q' GR) as (bsR & EBR).
rewrite (bs_split q q4 q' bs bsK bsR EB EBK EBR), Spec.X1nu.evw_app. apply rz_emit_app.
destruct GPOST as [(E40 & HKH) | (E4N & HPN4)].
-- refine (h_kloop_ok HX _ h4 0 nbr brem0 q (Cont h5) q4 bsK RUNK EBK _ c1 HKH _).
intros c2 [(ER & _) | (h6 & EC & HPN6)]; [discriminate ER|]. injection EC as <-.
refine (HPN HX h5 nbr brem0 _ c2 HPN6 _). intros c3 HAP.
exact (IH h5 nbr brem0 q4 o q' bsR GR EBR T c3 HAP Hk).
-- destruct (pkt_eos1 _ h4 0 q (Cont h5) q4 E4N RUNK) as (EC & ->). injection EC as EC'. subst h5.
rewrite (bs_nil q bsK EBK), evw_nil. apply rz_emit_nil.
refine (HPN HX h4 nbr brem0 _ c1 HPN4 _). intros c3 HAP.
exact (IH h4 nbr brem0 q o q' bsR GR EBR T c3 HAP Hk).
*
destruct GR as (EO & ->).
assert (EBS : bs = bsK) by (rewrite EBK in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
destruct GPOST as [(E40 & HKH) | (E4N & HPN4)].
-- refine (h_kloop_ok HX _ h4 0 nbr brem0 q Returned q4 bsK RUNK EBK T c1 HKH _).
intros c2 [(_ & HXT) | (h6 & EC & _)]; [| discriminate EC]. apply Hk. left. split; [exact EO| exact HXT].
-- destruct (pkt_eos1 _ h4 0 q Returned q4 E4N RUNK) as (EC & _). discriminate EC.
+
destruct GR as (q4 & ECL & EO & ->). rewrite prun_cleanup in ECL. injection ECL as <-.
rewrite (bs_nil q bs EB), evw_nil. apply rz_emit_nil. apply Hk. left. split; [exact EO| exact GPOST].
Qed.

Lemma cloop_step : forall fuel (h : hstate unit) q o q', prun (hP_chunk_loop (S fuel) (x_payload X) h) q = Some (o, q') ->
0 <= sy_storage (h_oy h) -> 0 <= ch_nbr h -> ch_nbr h + (sy_fill (h_oy h) - sy_returned (h_oy h)) + 4096 < 2^31 ->
0 <= sy_fill (h_oy h) - sy_returned (h_oy h) ->
exists o1 q1, prun (hP_page_loop (page_fuel (h_oy (ch_h1 X h))) (ch_h1 X h)) q = Some (o1, q1) /\
match o1 with
| Returned => o = Returned /\ q' = q1
| Cont h2 => if h_bytes_remaining h2 <=? 0 then o = Cont h2 /\ q' = q1 else prun (hP_chunk_loop fuel (x_payload X) h2) q1 = Some (o, q')
end.
Proof.
intros fuel h q o q' H S0 N0 NB PF0. unfold hP_chunk_loop in H. cbn [chunk_loop] in H.
change (if CHUNK <? h_bytes_remaining h then CHUNK else h_bytes_remaining h) with (ch_nbr h) in H.
rewrite prun_bind in H.
destruct (prun (ogg_sync_buffer p_malloc p_realloc p_free (h_oy h) (ch_nbr h)) q) as [[[data oy] q1]|] eqn:ESB; [| discriminate H].
destruct (sync_buffer_prun (h_oy h) (ch_nbr h) q (data, oy) q1 ESB S0 N0 NB PF0) as (ER & ->).
cbn beta iota in H.
assert (HD : (match data with Some _ => true | None => negb (0 <? ch_nbr h) end) = true).
{ destruct data; [reflexivity|]. destruct (0 <? ch_nbr h); [rewrite prun_munr in H; discriminate H| reflexivity]. }
destruct (ogg_sync_wrote (match data with Some (_, off) => sync_write oy off (ztake (ch_nbr h) (x_payload X)) | None => oy end) (ch_nbr h))
as [rw oyw] eqn:EW.
assert (ECH : ch_h1 X h = set_bytes_remaining (set_ogg h oy (h_os h)) oyw (h_bytes_remaining (set_ogg h oy (h_os h)) - ch_nbr h)).
{ unfold ch_h1. rewrite <- ER. cbn beta iota zeta. unfold bptr. rewrite EW. reflexivity. }
rewrite ECH.
assert (H' : prun (X1qy.mbind (hP_page_loop (page_fuel (h_oy (set_bytes_remaining (set_ogg h oy (h_os h)) oyw (h_bytes_remaining (set_ogg h oy (h_os h)) - ch_nbr h))))
(set_bytes_remaining (set_ogg h oy (h_os h)) oyw (h_bytes_remaining (set_ogg h oy (h_os h)) - ch_nbr h)))
(fun o => match o with Cont h => if h_bytes_remaining h <=? 0 then X1qy.mret (Cont h) else hP_chunk_loop fuel (x_payload X) h
| Returned => X1qy.mret Returned end)) q = Some (o, q')).
{ destruct data as [[p off]|]; [exact H|]. destruct (0 <? ch_nbr h); [discriminate HD| exact H]. }
clear H HD. rewrite prun_bind in H'.
lazymatch type of H' with
| match prun ?C q with _ => _ end = _ => destruct (prun C q) as [[o1 q2]|] eqn:EPL; [| discriminate H']
end.
exists o1, q2. split; [first [exact EPL| reflexivity]|].
destruct o1 as [h2|]; [| rewrite prun_ret in H'; injection H' as <- <-; split; reflexivity].
destruct (h_bytes_remaining h2 <=? 0); [rewrite prun_ret in H'; injection H' as <- <-; split; reflexivity| exact H'].
Qed.

Definition CLPOST (o : outcome unit) : config -> Prop :=
fun c => (o = Returned /\ at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c) \/ (exists h1, o = Cont h1 /\ at_CL RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 c).

Lemma at_CH_hpure : forall h c, at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 h c -> hpure X h.
Proof. intros h c Hc. destruct Hc as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HR & _). destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP). exact HP. Qed.

Theorem h_cloop_ok : hinv_ok OUT_rep IO_FP X -> forall fuel (h : hstate unit) (q : pst) (o : outcome unit) (q' : pst) bs,
(0 < h_bytes_remaining h \/ (h = h_init X /\ x_size X = 0 /\ x_d X <= x_lo X)) ->
prun (hP_chunk_loop fuel (x_payload X) h) q = Some (o, q') -> p_err q' = p_err q ++ bs ->
cpsE asegs (at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 h) (Spec.X1nu.evw 2 bs) (CLPOST o).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP FD2 HDR HCH HCH0 HPN HPX HPB.
intros HX fuel. induction fuel as [|fuel IH]; intros h q o q' bs BR RUN EB.
{ unfold hP_chunk_loop in RUN. cbn [chunk_loop] in RUN. rewrite prun_munr in RUN. discriminate RUN. }
apply (cpsE_with _ _ _ _ (at_CH_hpure h)). intros HP.
assert (BR0 : 0 <= h_bytes_remaining h) by (destruct BR as [BR|(-> & XS0 & _)]; [lia| unfold h_init, x_size in *; cbn [h_bytes_remaining]; lia]).
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP as (_ & _ & (S0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BRM & _ & PND & CNS & _).
assert (NB : 0 <= ch_nbr h <= 200) by (unfold ch_nbr, CHUNK; destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia).
destruct (cloop_step fuel h q o q' RUN S0 (proj1 NB) ltac:(unfold h_consumed, h_pend in *; lia) ltac:(unfold h_pend in PND; lia))
as (o1 & q1 & RUNP & REST).
destruct (app_page_loop _ _ q o1 q1 RUNP) as (bsP & EBP).
assert (CHS : cps asegs (at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 h) (h_after_pageout RT OUT_rep ERR_rep IO_FP X F0 fs0 (ch_h1 X h) (ch_nbr h) (h_bytes_remaining h))).
{ destruct BR as [BR|(-> & XS0 & XD0)]; [exact (HCH HX h BR)| exact (HCH0 HX XS0 XD0)]. }
eapply cps_cpsE; [exact CHS|].
destruct o1 as [h2|].
- destruct (Z.leb_spec (h_bytes_remaining h2) 0) as [BL|BG].
+
destruct REST as (EO & ->).
assert (EBS : bs = bsP) by (rewrite EBP in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
intros T c HAP Hk.
refine (h_ploop_ok HX _ (ch_h1 X h) (ch_nbr h) (h_bytes_remaining h) q (Cont h2) q1 bsP RUNP EBP _ c HAP _).
intros c1 [(ER & _) | (h3 & EC & HPX3)]; [discriminate ER|]. injection EC as EC'. subst h3.
refine (HPX HX h2 (ch_nbr h) (h_bytes_remaining h) T c1 HPX3 _).
intros c2 [(BG' & _) | (_ & HCL)]; [lia|]. apply Hk. right. exists h2. split; [exact EO| exact HCL].
+
destruct (app_chunk_loop _ _ _ q1 o q' REST) as (bsR & EBR).
rewrite (bs_split q q1 q' bs bsP bsR EB EBP EBR), Spec.X1nu.evw_app.
intros T c HAP Hk. apply rz_emit_app.
refine (h_ploop_ok HX _ (ch_h1 X h) (ch_nbr h) (h_bytes_remaining h) q (Cont h2) q1 bsP RUNP EBP _ c HAP _).
intros c1 [(ER & _) | (h3 & EC & HPX3)]; [discriminate ER|]. injection EC as EC'. subst h3.
refine (HPX HX h2 (ch_nbr h) (h_bytes_remaining h) _ c1 HPX3 _).
intros c2 [(_ & HCH2) | (BL' & _)]; [| lia].
exact (IH h2 q1 o q' bsR (or_introl BG) REST EBR T c2 HCH2 Hk).
-
destruct REST as (EO & ->).
assert (EBS : bs = bsP) by (rewrite EBP in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
intros T c HAP Hk.
refine (h_ploop_ok HX _ (ch_h1 X h) (ch_nbr h) (h_bytes_remaining h) q Returned q1 bsP RUNP EBP T c HAP _).
intros c1 [(_ & HXT) | (h3 & EC & _)]; [| discriminate EC]. apply Hk. left. split; [exact EO| exact HXT].
Qed.
End Loops.
