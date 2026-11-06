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
X077 X076 X07f X07e X07b X07a X07c X06o.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X106 X10j X10c X10x X108 X10q X10r X0wb X0w9 X0wg X0wf X0x5 X0zq X0x2 X0x1 X0xn X0xq X0xm X0xu X0ya X0xt X0y0 X0y8 X0y6 X0y5 X0y2 X0y1 X0y3 X0xg.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Pkt2.
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

Definition SPEEX5 : list byte := map (Z_to_bv 8) [83; 112; 101; 101; 120].

Lemma speex5_ro : forall m, mem_inv bsegs m -> bytes_at bsegs m A_SPEEX_LIT SPEEX5.
Proof.
intros m MI.
pose proof (ro_cells_image bsegs m A_SPEEX_LIT SPEEX5 MI ltac:(vm_compute; reflexivity) ltac:(unfold A_SPEEX_LIT; lia)
ltac:(vm_compute; intros XX; discriminate XX)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma speex_acc : forall (Σ : rts RT) m, ART RT Σ m -> acc bsegs m A_SPEEX_LIT 5.
Proof.
intros Σ m ART0. pose proof (af_acc_lits RT AF Σ m ART0) as FA. rewrite Forall_forall in FA.
pose proof (FA (0x232e0, 6) (or_intror (or_introl eq_refl))) as A6. cbn [fst snd] in A6.
apply (acc_sub bsegs m _ _ _ _ A6); unfold A_SPEEX_LIT; lia.
Qed.

Lemma speex_checked : forall (Σ : rts RT) m sp lo, ART RT Σ m -> A_SPEEX_LIT + 5 <= lo -> checked_src RT Σ m sp lo A_SPEEX_LIT 5.
Proof.
intros Σ m sp lo ART0 LO. split; [intros _; split; [exact (speex_acc Σ m ART0)| right; right; right; unfold A_SPEEX_LIT, SEGTOP_A; lia]| left; exact LO].
Qed.

Lemma map_bv_inj : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate H; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1| exact (IH l2 H2)].
Qed.

Lemma speex_eq : forall (pb : list byte), firstn 5 pb = SPEEX5 <-> list_eqb (ztake 5 (map bv_unsigned pb)) SPEEX_STR = true.
Proof.
intros pb. rewrite list_eqb_eq. unfold ztake. change (Z.to_nat 5) with 5%nat. rewrite firstn_map. split.
- intros ->. vm_compute. reflexivity.
- intros E. apply map_bv_inj. rewrite E. vm_compute. reflexivity.
Qed.

Lemma hrep_bcmp : hinv_ok OUT_rep IO_FP X -> forall (Σ1 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
rt_after RT Σ1 (x_S1 X) (x_lo X) m m' -> rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) (x_S1 X) 0 0 m m' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m' a h spill ogc opc.
Proof.
intros HX Σ1 m m' a h spill ogc opc HS HR SPS OGS OPS (ART' & MI' & WM' & ST') PRX.
pose proof HS as (EL & ND & PERM & EF & _).
rewrite EF in PRX.
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (PR : rt_pres_fp (rt_live RT Σ1) [(x_F X, 8%nat)] (x_S1 X) [(x_F X + 8688, x_F X + 8688 + 408)] m m')
by (apply (pres_fp_of_ex _ _ _ 0 0 _ m m' PRX); intros x Hx; exfalso; lia).
assert (PR0 : rt_pres_fp (rt_live RT Σ1) [(x_F X, 8%nat)] (x_S1 X) [] m m')
by (apply (pres_fp_of_ex _ _ _ 0 0 _ m m' PRX); intros x Hx; exfalso; lia).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INF : In (x_F X, 8%nat) [(x_F X, 8%nat)]) by (left; reflexivity).
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _ & _ & _ & _ & HP).
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR0 X a h OSR).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| apply rng_out_nil]. }
exact (hrep_os_step RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ1 m m' a a h h spill ogc opc (rt_live RT Σ1) HS HR SPS OGS OPS ART' MI' ST'
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) ltac:(intros p q Hin _; exact (INL _ Hin)) PR OSR'
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HP).
Qed.

Lemma hrep_set_serialno : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc ser,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> -2^31 <= ser < 2^31 ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a (set_serialno h ser) spill ogc opc.
Proof.
intros Σ1 m a h spill ogc opc ser HR SER.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & HP).
unfold hrep. cbn [set_serialno h_frame_size h_bits h_oy h_rate].
do 16 (split; [assumption|]).
split; [unfold h_os_rep in *; cbn [set_serialno h_stream_init h_os]; exact A17|].
do 3 (split; [assumption|]).
split; [unfold h_dec_rep in *; cbn [set_serialno h_st]; exact A21|].
unfold hpure, h_consumed, h_pend in *.
cbn [set_serialno h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & REST).
do 13 (split; [assumption|]). split; [exact (conj SER (proj2 B14))| exact REST].
Qed.

Lemma hsig_set_serialno : forall (Σ1 : rts RT) a (h : hstate unit) ser, hsig RT X Σ1 a h -> hsig RT X Σ1 a (set_serialno h ser).
Proof. intros Σ1 a h ser HS. exact HS. Qed.

Definition at_SS (h : hstate unit) (op : packet) (pno nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r10 t3 t4 t5 t6 : word)
(v48 v56 v88 j224 j232 gw : word) (ogc kc : list cell),
ASTA RT Σ1 (PMfd F0 fs0) (eq (MS (h_regs X h ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z64 (x_F X + 8608)) (Z64 (pk_sser h (h_os h) op)) (Z64 (x_F X + 8688))
(Z64 pno) (Z64 (pk_bytes op)) r10 t3 t4 t5 t6) Fx (Z64 A_SS) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1 /\ h_eos h = 0 /\ 0 <= pno <= h_packet_count h
/\ h_skip_word v48 h
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ogc (op_cells (a_Bd a) (Some op) gw kc)
/\ og_junk ogc /\ cells_size kc = 48%nat
/\ 0 <= pk_off op /\ 0 <= pk_bytes op /\ pk_off op + pk_bytes op <= os_body_fill (h_os h) /\ 0 <= pk_e_o_s op < 1024
/\ (h_packet_count h = 0 -> pk_off op = 0)
/\ h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * h_consumed X h.

Lemma packetout_none : forall (os os' : stream_st unit) r opo, ogg_stream_packetout os = Some ((r, opo), os') -> r <> 1 -> opo = None.
Proof.
intros os os' r opo H NR. unfold ogg_stream_packetout, packetout in H.
destruct (ogg_stream_check os); [injection H as _ <- _; reflexivity|].
destruct (_ <=? _); [injection H as _ <- _; reflexivity|].
destruct (negb _); [injection H as _ <- _; reflexivity|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [injection H as <- _ _; exfalso; exact (NR eq_refl)| discriminate H].
Qed.

Lemma packetout_off : forall (os os' : stream_st unit) r op, ogg_stream_packetout os = Some ((r, Some op), os') -> pk_off op = os_body_returned os.
Proof.
intros os os' r op H. unfold ogg_stream_packetout, packetout in H.
destruct (ogg_stream_check os); [injection H as _ E _; discriminate E|].
destruct (_ <=? _); [injection H as _ E _; discriminate E|].
destruct (negb _); [injection H as _ E _; discriminate E|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [injection H as _ E _; subst op; reflexivity| discriminate H].
Qed.

Theorem h_kss_ok : hinv_ok OUT_rep IO_FP X -> forall (h : hstate unit) (pno nbr brem0 r : Z) opo (os : stream_st unit),
ogg_stream_packetout (h_os h) = Some ((r, opo), os) ->
cps bsegs (at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0)
(fun c => (r <> 1 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_ogg h (h_oy h) os) nbr brem0 c)
\/ (r = 1 /\ exists op, opo = Some op /\ at_SS (set_ogg h (h_oy h) os) op pno nbr brem0 c)).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV BCMP.
intros HX h pno nbr brem0 r opo os EPO T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r2 & r5 & r10 & t3 & t4 & t5 & t6
& v48 & v56 & v88 & j224 & j232 & ogc & opc & Hc & FRM & HS & HIT & SI1 & E0 & PNR & SKW & PC0B & HR & OGJ & OPJ).
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h _ ogc _ HR) as OPOS.
pose proof HR as HR'. destruct HR' as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC
& OSR & (stb & STB) & RATE & (wl & LOOK & LKR) & DEC0 & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (SIN : h_stream_init h <> 0) by (rewrite SI1; discriminate).
pose proof OSR as OSR0.
unfold h_os_rep in OSR0. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0'|_]; [exfalso; exact (SIN E0')|].
destruct OSR0 as (OS & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
pose proof (own_in_os a h SIN) as (IBD & ILD & IGD).
destruct HSP as (HSP1 & HSP2 & HSP3).
pose proof (HSP1 _ _ IBD) as (B0 & B1 & B2 & _). pose proof (HSP1 _ _ ILD) as (L0 & L1 & L2 & _). pose proof (HSP1 _ _ IGD) as (G0 & G1 & G2 & _).
destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->).

unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS in Hc.
pose proof SP as SP0. unfold h_spill, HO_OS, HO_OP in SP0.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply kh_w0; [exact S1R| exact SP0| exact MI]. }
intros ms1 c1 -> Hc1. clear Hc SP0.

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c1 (PMfd_mat_stable F0 fs0) Hc1 _ _).
{ eapply (ogg_stream_packetout_spec (x_F X + 8688) (a_Bd a) (a_L a) (a_G a) (x_F X + 8608) (a_shdr a) (h_os h) (a_lws a) (a_gws a) k0 k1 k2 k3 k4 k5).
{ exact LH. } { exact FOK. } { exact (stream_inv_lacing_inv _ SINV). } { exact LOK. } { exact WP. } { exact LL. } { exact LG. } { exact GL. }
{ lia. } { lia. } { lia. }
{ rewrite LL. unfold bptr in *. lia. } { rewrite LG. unfold bptr in *. lia. }
{ right. lia. } { unfold bptr in *. lia. } { unfold bptr in *. lia. } { unfold bptr in *. lia. } { unfold bptr in *. lia. }
{ exact MI. } { unfold HO_OS in OS. exact OS. } { exact UL. } { exact UG. } { unfold HO_OP in OPC. exact OPC. }
{ split; [intros E; exfalso; exact (BD E)| intros E; lia]. }
{ exact EPO. } { reflexivity. } { reflexivity. } }
intros ms2 c2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & gw & -> & MU1 & WM1 & MI1 & OS1 & FOK1 & OP1) Hc2.
clear Hc1.
destruct (hrep_packetout RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h _ ogc _ r opo os gw HS HR
ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(reflexivity) SIN EPO MU1 WM1 MI1 OS1 FOK1 OP1)
as (HS1 & HR1 & LR1 & R1 & PK).
pose proof (packetout_r_eos _ _ _ _ EPO) as (RR & EOS).
pose proof HR1 as HR1'. destruct HR1' as (ART1 & MI1' & ST1 & PF1 & ERR1 & OUTR1 & SSP1 & SP1 & _).

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc2 _ _).
{ eapply (kh_w1 (x_S1 X)); [reflexivity| exact RR| exact S1R| unfold h_spill in SP1; exact SP1| exact MI1]. }
intros ms3 c3 [(RN & ->) | (R1' & ->)] Hc3; clear Hc2.
-
pose proof (packetout_none _ _ _ _ EPO RN) as ENone. subst opo.
apply Hk. left. split; [exact RN|].
exists Σ1, a, Fx, fc, m1, (Z64 0x96f20), t0', t1', t2', (Z64 r), (Z64 1), a2', a3', a4', a5', a6', a7', (Z64 (x_F X + 8608)), (Z64 (h_speex_serialno h)),
(Z64 pno), t3', t4', t5', t6', v48, v56, v88, j224, j232, ogc, [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_ogg h_packet_count h_channels h_eos]; rewrite E0; exact Hc3|].
split; [exact FRM|]. split; [exact HS1|]. split; [exact HIT|]. split; [exact SI1|].
split; [exact HR1|]. split; [exact OGJ| do 6 eexists; reflexivity].
-
subst r. destruct (R1 eq_refl) as (NOP & LRL).
destruct opo as [op|]; [| exfalso; exact (NOP eq_refl)].
cbn beta iota in PK, EOS. destruct PK as (PK0 & PK1 & PK2 & PK3).
pose proof (packetout_off _ _ _ _ EPO) as POFF.
destruct (packetout_same (h_os h) os 1 (Some op) EPO) as (_ & _ & EBO & _ & _ & _ & EBS & _ & EBF & ELF & ESER).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BRM & _ & PND & CNS & _ & BF & _ & _ & _ & PCL).
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
assert (BYT : pk_bytes op <= 4096) by (unfold h_consumed, h_pend in *; lia).
pose proof HR1 as HR1'. destruct HR1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OPC1 & OSR1 & _).
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c3 (PMfd_mat_stable F0 fs0) Hc3 _ _).
{ eapply (kh_w2 (x_S1 X) (x_F X) (a_Bd a) op gw [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5]);
[exact S1R| lia| unfold HO_OP in OPC1; exact OPC1| exact MI1]. }
intros ms4 c4 [(LT5 & ->) | (GE5 & ->)] Hc4; clear Hc3.
+
apply Hk. right. split; [reflexivity|]. exists op. split; [reflexivity|].
exists Σ1, a, Fx, fc, m1, (Z64 0x96f20), t0', t1', t2', (Z64 5), (Z64 1), a2', a3', a4', a5', a6', a7', r10, t3', t4', t5', t6', v48, v56, v88, j224, j232, gw, ogc,
[CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split.
{ unfold pk_sser. replace (5 <=? pk_bytes op) with false by (symmetry; apply Z.leb_gt; lia).
unfold h_regs. cbn [andb set_ogg h_packet_count h_extra_headers h_speex_serialno h_os h_channels]. exact Hc4. }
split; [exact FRM|]. split; [exact HS1|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact E0|]. split; [cbn [set_ogg h_packet_count]; lia|].
split; [exact SKW|].
split; [exact HR1|]. split; [exact OGJ|]. split; [reflexivity|].
split; [exact PK0|]. split; [exact PK1|]. split; [cbn [set_ogg h_os]; unfold bptr in *; lia|]. split; [exact EOS|].
split; [cbn [set_ogg h_packet_count]; intros PC0; rewrite POFF; exact (PC0B PC0)|].
unfold h_consumed, h_pend in *. cbn [set_ogg h_os h_oy h_packet_count h_bytes_remaining]. unfold bptr in *. lia.
+
unfold h_os_rep in OSR1. cbn [set_ogg h_stream_init h_os] in OSR1. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0'|_]; [exfalso; exact (SIN E0')|].
destruct OSR1 as (OS1' & _ & (UB1 & LB1 & BP1 & _) & FOK1' & _ & BINV1 & _).
destruct (pk_window m1 (a_Bd a) (a_body a) os op UB1 BP1 (proj1 BINV1) PK0 PK1 ltac:(unfold bptr in *; lia)) as (U8 & EPD & LPB).
set (pb := firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) (a_body a))) in *.
assert (P5 : bytes_at bsegs m1 (a_Bd a + pk_off op) (firstn 5 pb)).
{ unfold u8ro in U8. rewrite <- (firstn_skipn 5 pb) in U8. apply bytes_at_app in U8 as [U8 _]. exact U8. }
assert (L5 : length (firstn 5 pb) = 5%nat) by (rewrite length_firstn; lia).
assert (LOR : SEGTOP_A <= x_lo X).
{ pose proof (af_sp0_range RT AF Σ1 m ART) as SR0. rewrite ESP in SR0. pose proof (hi_lo _ _ _ HX) as (LW0 & _). lia. }
assert (INB1 : In (a_Bd a, os_body_storage os) (rt_live RT Σ1)).
{ destruct HS1 as (EL1 & _ & PERM1 & _). rewrite EL1. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PERM1)).
exact (proj1 (own_in_os a (set_ogg h (h_oy h) os) SIN)). }
Time cps_rt (BCMP Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1
(a_Bd a + pk_off op) A_SPEEX_LIT (firstn 5 pb) SPEEX5 (x_lo X)).
{ apply PMfd_fdfs_only. } { apply PMfd_mat_stable. } { rewrite L5. reflexivity. }
{ pose proof (proj1 BINV1) as ZL. destruct BP1 as (_ & BPL). unfold zlength in ZL. unfold bptr in *. unfold USTACK_TOP, RT_STACK, H_STACK in *. lia. }
{ unfold A_SPEEX_LIT. lia. }
{ exact (speex5_ro m1 MI1). }
{ rewrite L5. change (Z.of_nat 5) with 5.
pose proof (proj1 BINV1) as ZL. destruct BP1 as (_ & BPL). unfold zlength in ZL. unfold bptr in *.
apply (live_checked_src RT AF Σ1 m1 _ (x_lo X) (a_Bd a) (os_body_storage os) _ _ ART1 INB1); lia. }
{ rewrite L5. change (Z.of_nat 5) with 5. apply (speex_checked Σ1 m1 _ _ ART1). unfold A_SPEEX_LIT, SEGTOP_A in *. lia. }
{ unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST1|]. split; [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); exact LW0|].
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|]. clear - S32. Z.div_mod_to_equations. lia. }
intros c5 (v & EV & Hc5). clear Hc4. unfold icpt_postF in Hc5.
Time cps_unpack_lib Hc5 as (m3 & RS3 & RA3 & PRX3 & _).
cps_ret RS3.
pose proof (hrep_bcmp HX Σ1 m1 m3 a (set_ogg h (h_oy h) os) _ ogc _ HS1 HR1 eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl
RA3 PRX3) as HR3.
pose proof HR3 as HR3'. destruct HR3' as (ART3 & MI3 & ST3 & _ & _ & _ & _ & SP3 & _ & _ & _ & _ & _ & _ & _ & _ & OSR3 & _).
unfold h_os_rep in OSR3. cbn [set_ogg h_stream_init h_os] in OSR3.
destruct (Z.eqb_spec (h_stream_init h) 0) as [E0''|_]; [exfalso; exact (SIN E0'')|].
destruct OSR3 as (OS3 & _).
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c5 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (kh_w3 (x_S1 X) (x_F X) (a_Bd a) (a_L a) (a_G a) (a_shdr a) os);
[reflexivity| exact S1R| lia| exact FOK1'| unfold HO_OS in OS3; exact OS3| exact MI3]. }
intros ms6 c6 (s5'' & CASEV & ->) Hc6. clear Hc.
assert (EA1 : s5'' = Z64 (pk_sser (set_ogg h (h_oy h) os) (h_os (set_ogg h (h_oy h) os)) op)).
{ unfold pk_sser. cbn [set_ogg h_os h_speex_serialno]. replace (5 <=? pk_bytes op) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
rewrite <- EPD. destruct CASEV as [(VN & ->) | (V0 & ->)].
- replace (list_eqb (ztake 5 (map bv_unsigned pb)) SPEEX_STR) with false; [reflexivity|].
symmetry. apply not_true_is_false. intros EQ. apply VN. apply EV. apply speex_eq. exact EQ.
- replace (list_eqb (ztake 5 (map bv_unsigned pb)) SPEEX_STR) with true; [reflexivity|].
symmetry. apply speex_eq. apply EV. exact V0. }
subst s5''.
apply Hk. right. split; [reflexivity|]. exists op. split; [reflexivity|].
exists Σ1, a. do 2 eexists. exists m3. do 17 eexists. exists v48, v56, v88, j224, j232, gw, ogc, [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs; cbn [set_ogg h_packet_count h_extra_headers h_os h_channels]; exact Hc6|].
split; [exact FRM|]. split; [exact HS1|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact E0|]. split; [cbn [set_ogg h_packet_count]; lia|].
split; [exact SKW|].
split; [exact HR3|]. split; [exact OGJ|]. split; [reflexivity|].
split; [exact PK0|]. split; [exact PK1|]. split; [cbn [set_ogg h_os]; unfold bptr in *; lia|]. split; [exact EOS|].
split; [cbn [set_ogg h_packet_count]; intros PC0; rewrite POFF; exact (PC0B PC0)|].
unfold h_consumed, h_pend in *. cbn [set_ogg h_os h_oy h_packet_count h_bytes_remaining]. unfold bptr in *. lia.
Qed.

Theorem h_ssw_ok : hinv_ok OUT_rep IO_FP X -> forall (h1 : hstate unit) (op : packet) (pno nbr brem0 : Z),
cps bsegs (at_SS h1 op pno nbr brem0)
(fun c => ((pk_sser h1 (h_os h1) op = -1 \/ os_serialno (h_os h1) <> pk_sser h1 (h_os h1) op)
/\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_serialno h1 (pk_sser h1 (h_os h1) op)) nbr brem0 c)
\/ (pk_sser h1 (h_os h1) op <> -1 /\ os_serialno (h_os h1) = pk_sser h1 (h_os h1) op /\ h_packet_count h1 = 0
/\ at_HP RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 c)
\/ (pk_sser h1 (h_os h1) op <> -1 /\ os_serialno (h_os h1) = pk_sser h1 (h_os h1) op /\ h_packet_count h1 <> 0
/\ h_packet_count h1 <= 1 + h_extra_headers h1
/\ at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_serialno h1 (pk_sser h1 (h_os h1) op)) pno nbr brem0 c)
\/ (pk_sser h1 (h_os h1) op <> -1 /\ os_serialno (h_os h1) = pk_sser h1 (h_os h1) op /\ h_packet_count h1 <> 0
/\ 1 + h_extra_headers h1 < h_packet_count h1
/\ at_RF RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 c)).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV.
intros HX h1 op pno nbr brem0 T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r10 & t3 & t4 & t5 & t6 & v48 & v56 & v88 & j224 & j232 & gw & ogc & kc
& Hc & FRM & HS & HIT & SI1 & E0 & PNR & SKW & HR & OGJ & KCS & PK0 & PK1 & PK2 & EOS & POFF0 & PCR).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC
& OSR & (stb & STB) & RATE & (wl & LOOK & LKR) & DEC0 & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (SIN : h_stream_init h1 <> 0) by (rewrite SI1; discriminate).
pose proof OSR as OSR0.
unfold h_os_rep in OSR0. destruct (Z.eqb_spec (h_stream_init h1) 0) as [E0'|_]; [exfalso; exact (SIN E0')|].
destruct OSR0 as (OS & LH & _ & FOK & _).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EXR & (SNR & _) & PCR0 & _ & _ & _ & BRM & STPC & PND & CNS & _ & BF & _).
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
assert (BYT : pk_bytes op <= 4096) by (unfold h_consumed, h_pend in *; lia).
assert (SSR : -2^31 <= pk_sser h1 (h_os h1) op < 2^31).
{ unfold pk_sser. destruct (_ && _); [pose proof FOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SN & _); exact SN| exact SNR]. }
unfold h_regs in Hc.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (kh_w4 (x_S1 X) (x_F X) (a_Bd a) (a_L a) (a_G a) (pk_sser h1 (h_os h1) op) (h_packet_count h1) (h_extra_headers h1) pno (a_shdr a) (h_os h1) op gw kc).
{ exact S1R. } { exact FP0. } { lia. } { exact FOK. } { exact SSR. } { lia. } { lia. } { lia. } { lia. } { lia. }
{ unfold HO_OS in OS. exact OS. } { unfold HO_OP in OPC. exact OPC. } { unfold h_spill, HO_OG, HO_OP, HO_BITS in SP. exact SP. } { exact MI. } }
intros ms1 c1 (m1 & MU1 & WM1 & MI1 & [(B1 & SP1 & ->) | [(B2 & B2' & SP1 & ->) | [(B3 & B3' & B3'' & SP1 & ->) | [(B4 & B4' & B4'' & B4''' & SP1 & ->) | (B5 & B5' & B5'' & B5''' & SP1 & ->)]]]]) Hc1;
clear Hc.
-
assert (SPn : rw_cells bsegs m1 (x_S1 X) (h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_nframes h_speex_serialno h_last_granule h_bytes_remaining]. rewrite B1. unfold HO_OG, HO_OP, HO_BITS. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
destruct (hrep_op_junk RT OUT_rep ERR_rep IO_FP X Σ1 m1 a _ _ ogc (a_Bd a) op gw kc HR2) as (opc & OPJ & HR3).
apply Hk. left. split; [left; exact B1|].
exists Σ1, a, Fx, fc, m1. do 19 eexists. exists v48, v56, v88, j224, j232, ogc, opc.
split; [unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_serialno h_packet_count h_eos h_channels]; rewrite E0; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_serialno Σ1 a h1 _ HS)|]. split; [exact HIT|]. split; [exact SI1|].
split; [exact HR3|]. split; [exact OGJ| exact OPJ].
-
assert (SPn : rw_cells bsegs m1 (x_S1 X) (h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_nframes h_speex_serialno h_last_granule h_bytes_remaining]. unfold HO_OG, HO_OP, HO_BITS. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
destruct (hrep_op_junk RT OUT_rep ERR_rep IO_FP X Σ1 m1 a _ _ ogc (a_Bd a) op gw kc HR2) as (opc & OPJ & HR3).
apply Hk. left. split; [right; exact B2'|].
exists Σ1, a, Fx, fc, m1. do 19 eexists. exists v48, v56, v88, j224, j232, ogc, opc.
split; [unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_serialno h_packet_count h_eos h_channels]; rewrite E0; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_serialno Σ1 a h1 _ HS)|]. split; [exact HIT|]. split; [exact SI1|].
split; [exact HR3|]. split; [exact OGJ| exact OPJ].
-
assert (SPn : rw_cells bsegs m1 (x_S1 X) (h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_nframes h_speex_serialno h_last_granule h_bytes_remaining]. unfold HO_OG, HO_OP, HO_BITS. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
apply Hk. right. left. split; [exact B3|]. split; [exact B3'|]. split; [exact B3''|].
exists Σ1, a, Fx, fc, m1. do 16 eexists. exists v48, v56, v88, j224, j232, gw, ogc, kc.
split; [unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_serialno h_packet_count h_speex_serialno h_extra_headers h_channels]; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_serialno Σ1 a h1 _ HS)|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact E0|].
split; [exact B3''|]. split; [cbn [set_serialno h_packet_count]; lia|]. split; [exact SKW|]. split; [exact HR2|]. split; [exact OGJ|]. split; [exact KCS|].
split; [exact (POFF0 B3'')|]. split; [exact PK1|]. split; [exact PK2| exact PCR].
-
assert (SPn : rw_cells bsegs m1 (x_S1 X) (h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_nframes h_speex_serialno h_last_granule h_bytes_remaining]. unfold HO_OG, HO_OP, HO_BITS. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
destruct (hrep_op_junk RT OUT_rep ERR_rep IO_FP X Σ1 m1 a _ _ ogc (a_Bd a) op gw kc HR2) as (opc & OPJ & HR3).
apply Hk. right. right. left. split; [exact B4|]. split; [exact B4'|]. split; [exact B4''|]. split; [lia|].
exists Σ1, a, Fx, fc, m1. do 20 eexists. exists v48, v56, v88, j224, j232, ogc, opc.
split; [unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_serialno h_packet_count h_eos h_extra_headers h_channels]; rewrite E0; exact Hc1|].
split; [exact FRM|].
split; [apply (hsig_k_weaken RT X Σ1 a _ 0); [unfold H_DEC_CREDIT; lia| exact (hsig_k_of RT X Σ1 a _ (hsig_set_serialno Σ1 a h1 _ HS))]|].
split; [exact HIT|]. split; [exact SI1|]. split; [left; exact E0|]. split; [cbn [set_serialno h_packet_count]; lia|]. split; [exact SKW|].
split; [exact HR3|]. split; [exact OGJ|]. split; [exact OPJ|].
split; [exact PCR|]. cbn [set_serialno h_st]. destruct (h_st h1); [discriminate| exfalso; exact (B4'' STPC)].
-
assert (SPn : rw_cells bsegs m1 (x_S1 X) (h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_nframes h_speex_serialno h_last_granule h_bytes_remaining]. unfold HO_OG, HO_OP, HO_BITS. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 (h_bytes_remaining h1)) v48 v56 v88 j224 j232 a (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
apply Hk. right. right. right. split; [exact B5|]. split; [exact B5'|]. split; [exact B5''|]. split; [lia|].
exists Σ1, a, Fx, fc, m1. do 13 eexists. exists v48, v56, v88, j224, j232, gw, ogc, kc.
split; [unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_serialno h_packet_count h_extra_headers h_channels]; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_serialno Σ1 a h1 _ HS)|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact E0|].
split; [cbn [set_serialno h_packet_count]; lia|].
assert (STN1 : h_st h1 <> None) by (destruct (h_st h1); [discriminate| exfalso; exact (B5'' STPC)]).
split; [exact STN1|]. split; [exact SKW|]. split; [exact HR2|]. split; [exact OGJ|]. split; [exact KCS|].
split; [exact PK0|]. split; [exact PK1|]. split; [exact PK2|]. split; [lia|].
split; [exact PCR| exact STN1].
Qed.

Lemma read_from_appends : forall (b : bits_st unit) pkt len q r q',
prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning b pkt len) q = Some (r, q') -> exists bs, p_err q' = p_err q ++ bs.
Proof.
intros b pkt len q r q' H. unfold speex_bits_read_from in H. rewrite prun_bind in H.
destruct (sb_buf_size b <? len).
- rewrite prun_bind, prun_notify in H. cbn beta iota in H.
destruct (negb (sb_owner b =? 0)).
+ rewrite prun_bind in H. unfold p_realloc at 1 in H. rewrite prun_ret in H. cbn beta iota in H.
destruct (p_overflows len).
* rewrite prun_bind, prun_warning, prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as _ <-.
exists (notify_bytes MSG_PACKET_LARGER ++ warning_bytes MSG_COULD_NOT_RESIZE). cbn [p_app p_err]. rewrite app_assoc. reflexivity.
* rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as _ <-. exists (notify_bytes MSG_PACKET_LARGER). reflexivity.
+ rewrite prun_bind, prun_warning, prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as _ <-.
exists (notify_bytes MSG_PACKET_LARGER ++ warning_bytes MSG_NOT_OWNER). cbn [p_app p_err]. rewrite app_assoc. reflexivity.
- rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as _ <-. exists []. rewrite app_nil_r. reflexivity.
Qed.

Lemma pkt_eos1 : forall fuel (h : hstate unit) pno q o q', h_eos h <> 0 -> prun (hP_packet_loop fuel h pno) q = Some (o, q') -> o = Cont h /\ q' = q.
Proof.
intros [|fuel] h pno q o q' E H; unfold hP_packet_loop in H; cbn [packet_loop] in H; [rewrite prun_munr in H; discriminate H|].
replace (negb (h_eos h =? 0)) with true in H by (symmetry; apply negb_true_iff, Z.eqb_neq; exact E). rewrite prun_ret in H.
injection H as <- <-. split; reflexivity.
Qed.

Definition pk_post (fuel : nat) (q : pst) (bs : list Z) (o : outcome unit) (q' : pst) (nbr brem0 : Z) : config -> Prop :=
fun c => exists q1, p_err q1 = p_err q ++ bs /\
( (o = Returned /\ q1 = q' /\ at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c)
\/ (exists h1, o = Cont h1 /\ q1 = q' /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 nbr brem0 c)
\/ (exists h1 pno1, h_eos h1 = 0 /\ prun (hP_packet_loop fuel h1 pno1) q1 = Some (o, q') /\ at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 pno1 nbr brem0 c)).

Lemma kt_post : forall fuel q bs (h : hstate unit) pno nbr brem0 q1 o q' c, p_err q1 = p_err q ++ bs ->
prun (hP_packet_loop fuel (incr_packet_count h) pno) q1 = Some (o, q') ->
(h_eos h = 0 /\ at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h) pno nbr brem0 c)
\/ (h_eos h = 1 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h) nbr brem0 c) ->
pk_post fuel q bs o q' nbr brem0 c.
Proof.
intros fuel q bs h pno nbr brem0 q1 o q' c EB RUN [(E0 & HK) | (E1 & HP)].
- exists q1. split; [exact EB|]. right. right. exists (incr_packet_count h), pno. split; [exact E0|]. split; [exact RUN| exact HK].
- destruct (pkt_eos1 fuel (incr_packet_count h) pno q1 o q' ltac:(cbn [incr_packet_count h_eos]; lia) RUN) as (-> & ->).
exists q1. split; [exact EB|]. right. left. exists (incr_packet_count h). split; [reflexivity|]. split; [reflexivity| exact HP].
Qed.

Theorem h_ss_ok : hinv_ok OUT_rep IO_FP X -> forall fuel (h1 : hstate unit) (op : packet) (pno nbr brem0 : Z) (q : pst) (o : outcome unit) (q' : pst),
pkt_cases fuel h1 (h_os h1) op pno q o q' ->
exists bs, cpsE bsegs (at_SS h1 op pno nbr brem0) (Spec.X1nu.evw 2 bs) (pk_post fuel q bs o q' nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF FD2 HDR.
intros HX fuel h1 op pno nbr brem0 q o q' CASES.
pose proof (h_ssw_ok HX h1 op pno nbr brem0) as SSW.
unfold pkt_cases in CASES.
destruct CASES as [(SC & EO & EQ) | (SN & SE & [(P0 & ph & q1 & EPH & PHC) | [(PN & PLE & RUN) | (PN & PGT & d & b & q1 & st' & b' & q2 & ESt & ERF & EDL & RUN)]])].
-
exists []. apply cpsE_nil. eapply cps_conseq; [exact SSW| intros c Hc; exact Hc|].
intros c [(_ & HPN) | [(SN' & SE' & _) | [(SN' & SE' & _) | (SN' & SE' & _)]]];
[| exfalso; destruct SC as [SC|SC]; [exact (SN' SC)| exact (SC SE')] ..].
exists q. split; [rewrite app_nil_r; reflexivity|]. right. left. exists (set_serialno h1 (pk_sser h1 (h_os h1) op)).
split; [exact EO|]. split; [symmetry; exact EQ| exact HPN].
-
destruct (app_process_header _ _ _ q ph q1 EPH) as (bs & EB').
pose proof (HDR HX (set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 q q1 ph bs EPH EB') as HDRE.
exists bs. eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & _ & HHP) | [(_ & _ & PN' & _) | (_ & _ & PN' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| | exfalso; exact (PN' P0) ..].
refine (HDRE T c HHP _). intros c' POST. apply Hk.
exists q1. split; [exact EB'|]. destruct ph as [h3|].
+ right. right. exists (incr_packet_count h3), pno.
assert (E3 : h_eos (incr_packet_count h3) = 0) by (destruct POST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3' & _); exact E3').
split; [exact E3|]. split; [exact PHC| exact POST].
+ left. destruct PHC as (-> & ->). split; [reflexivity|]. split; [reflexivity| exact POST].
-
exists []. apply cpsE_nil. eapply cps_seq; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & P0' & _) | [(_ & _ & _ & _ & HKT) | (_ & _ & _ & PGT' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| exfalso; exact (PN P0')| | exfalso; lia].
refine (h_kt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X F0 fs0 HX _ pno nbr brem0 T c HKT _).
intros c' POST. apply Hk. exact (kt_post fuel q [] _ pno nbr brem0 q o q' c' ltac:(rewrite app_nil_r; reflexivity) RUN POST).
-
destruct (read_from_appends _ _ _ q b q1 ERF) as (bs1 & EB1).
pose proof EDL as EDL'. unfold hP_decode_loop in EDL'. destruct (dloop_appends _ d b q1 _ q2 EDL') as (bs2 & EB2). clear EDL'.
exists (bs1 ++ bs2). eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & P0' & _) | [(_ & _ & _ & PLE' & _) | (_ & _ & _ & _ & HRF)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| exfalso; exact (PN P0')| exfalso; lia|].
assert (EB : p_err q2 = p_err q ++ (bs1 ++ bs2)) by (rewrite EB2, EB1, app_assoc; reflexivity).
refine (h_data_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF X F0 fs0 FD2 HX
(set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 q q1 q2 b d st' b' (bs1 ++ bs2) ESt ERF EDL EB T c HRF _).
intros c' HKT.
refine (h_kt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X F0 fs0 HX _ (pno + 1) nbr brem0 T c' HKT _).
intros c'' POST. apply Hk. exact (kt_post fuel q (bs1 ++ bs2) _ (pno + 1) nbr brem0 q2 o q' c'' EB RUN POST).
Qed.

Theorem h_pkt_ok : h_pkt_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP FD2 HDR.
intros HX fuel h pno nbr brem0 q q' o RUN.
destruct (Z.eq_dec (h_eos h) 0) as [E0|EN].
2:{ exists []. intros T c Hc _. exfalso. destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E0' & _). exact (EN E0'). }
assert (PCD : (h_packet_count h = 0 -> h_st h = None) \/ (h_packet_count h = 0 /\ h_st h <> None)).
{ destruct (Z.eq_dec (h_packet_count h) 0) as [P0|PN]; [| left; intros P0; exfalso; exact (PN P0)].
destruct (h_st h) as [d|]; [right; split; [exact P0| discriminate]| left; intros _; reflexivity]. }
destruct PCD as [PC0 | (P0 & STN)].
2:{ exists []. intros T c Hc _. exfalso. destruct Hc as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HR & _).
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STPC & _).
destruct (h_st h); [exact (STPC P0)| exact (STN eq_refl)]. }
destruct (pkt_step fuel h pno q o q' E0 PC0 RUN) as (r & opo & os & EPO & [(RN & EO & EQ) | (R1 & op & EOP & CASES)]).
-
exists []. apply cpsE_nil. eapply cps_conseq; [exact (h_kss_ok HX h pno nbr brem0 r opo os EPO)| intros c Hc; exact Hc|].
intros c [(_ & HPN) | (R1 & _)]; [| exfalso; exact (RN R1)].
exists q. split; [rewrite app_nil_r; reflexivity|]. right. left. exists (set_ogg h (h_oy h) os).
split; [exact EO|]. split; [symmetry; exact EQ| exact HPN].
-
destruct (h_ss_ok HX fuel (set_ogg h (h_oy h) os) op pno nbr brem0 q o q' CASES) as (bs & SSE).
exists bs. eapply cps_cpsE; [exact (h_kss_ok HX h pno nbr brem0 r opo os EPO)|].
intros T c [(RN & _) | (_ & op' & EOP' & HSS)] Hk; [exfalso; exact (RN R1)|].
rewrite EOP in EOP'. injection EOP' as <-. exact (SSE T c HSS Hk).
Qed.
End Pkt2.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Pkt2.
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

Definition SPEEX5 : list byte := map (Z_to_bv 8) [83; 112; 101; 101; 120].

Lemma speex5_ro : forall m, mem_inv asegs m -> bytes_at asegs m A_SPEEX_LIT SPEEX5.
Proof.
intros m MI.
pose proof (ro_cells_image asegs m A_SPEEX_LIT SPEEX5 MI ltac:(vm_compute; reflexivity) ltac:(unfold A_SPEEX_LIT; lia)
ltac:(vm_compute; intros XX; discriminate XX)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma speex_acc : forall (Σ : rts RT) m, ART RT Σ m -> acc asegs m A_SPEEX_LIT 5.
Proof.
intros Σ m ART0. pose proof (af_acc_lits RT AF Σ m ART0) as FA. rewrite Forall_forall in FA.
pose proof (FA (0x232a0, 6) (or_intror (or_introl eq_refl))) as A6. cbn [fst snd] in A6.
apply (acc_sub asegs m _ _ _ _ A6); unfold A_SPEEX_LIT; lia.
Qed.

Lemma speex_checked : forall (Σ : rts RT) m sp lo, ART RT Σ m -> A_SPEEX_LIT + 5 <= lo -> checked_src RT Σ m sp lo A_SPEEX_LIT 5.
Proof.
intros Σ m sp lo ART0 LO. split; [intros _; split; [exact (speex_acc Σ m ART0)| right; right; right; unfold A_SPEEX_LIT, SEGTOP_A; lia]| left; exact LO].
Qed.

Lemma map_bv_inj : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate H; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1| exact (IH l2 H2)].
Qed.

Lemma speex_eq : forall (pb : list byte), firstn 5 pb = SPEEX5 <-> list_eqb (ztake 5 (map bv_unsigned pb)) SPEEX_STR = true.
Proof.
intros pb. rewrite list_eqb_eq. unfold ztake. change (Z.to_nat 5) with 5%nat. rewrite firstn_map. split.
- intros ->. vm_compute. reflexivity.
- intros E. apply map_bv_inj. rewrite E. vm_compute. reflexivity.
Qed.

Lemma hrep_bcmp : hinv_ok OUT_rep IO_FP X -> forall (Σ1 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
rt_after RT Σ1 (x_S1 X) (x_lo X) m m' -> rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) (x_S1 X) 0 0 m m' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m' a h spill ogc opc.
Proof.
intros HX Σ1 m m' a h spill ogc opc HS HR SPS OGS OPS (ART' & MI' & WM' & ST') PRX.
pose proof HS as (EL & ND & PERM & EF & _).
rewrite EF in PRX.
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (PR : rt_pres_fp (rt_live RT Σ1) [(x_F X, 8%nat)] (x_S1 X) [(x_F X + 8688, x_F X + 8688 + 408)] m m')
by (apply (pres_fp_of_ex _ _ _ 0 0 _ m m' PRX); intros x Hx; exfalso; lia).
assert (PR0 : rt_pres_fp (rt_live RT Σ1) [(x_F X, 8%nat)] (x_S1 X) [] m m')
by (apply (pres_fp_of_ex _ _ _ 0 0 _ m m' PRX); intros x Hx; exfalso; lia).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INF : In (x_F X, 8%nat) [(x_F X, 8%nat)]) by (left; reflexivity).
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _ & _ & _ & _ & HP).
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR0 X a h OSR).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| apply rng_out_nil]. }
exact (hrep_os_step RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ1 m m' a a h h spill ogc opc (rt_live RT Σ1) HS HR SPS OGS OPS ART' MI' ST'
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) ltac:(intros p q Hin _; exact (INL _ Hin)) PR OSR'
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HP).
Qed.

Lemma hrep_set_serialno : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc ser,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> -2^31 <= ser < 2^31 ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a (set_serialno h ser) spill ogc opc.
Proof.
intros Σ1 m a h spill ogc opc ser HR SER.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & HP).
unfold hrep. cbn [set_serialno h_frame_size h_bits h_oy h_rate].
do 16 (split; [assumption|]).
split; [unfold h_os_rep in *; cbn [set_serialno h_stream_init h_os]; exact A17|].
do 3 (split; [assumption|]).
split; [unfold h_dec_rep in *; cbn [set_serialno h_st]; exact A21|].
unfold hpure, h_consumed, h_pend in *.
cbn [set_serialno h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & REST).
do 13 (split; [assumption|]). split; [exact SER| exact REST].
Qed.

Lemma hsig_set_serialno : forall (Σ1 : rts RT) a (h : hstate unit) ser, hsig RT X Σ1 a h -> hsig RT X Σ1 a (set_serialno h ser).
Proof. intros Σ1 a h ser HS. exact HS. Qed.

Definition at_SS (h : hstate unit) (op : packet) (pno nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j0 j192 j200 gw : word) (ogc kc : list cell),
ASTA RT Σ1 (PMfd F0 fs0) (eq (MS (mkR ra (Z64 (x_S1 X)) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 (x_usp X)) (Z64 (x_S1 X)) a0 (Z64 (pk_sser h (h_os h) op))
a2 a3 a4 a5 a6 a7 (Z64 (x_F X + 8608)) (Z64 (x_sf X)) (Z64 (x_F X + 128)) (Z64 (x_F X + 8544))
(Z64 (h_packet_count h)) (Z64 (x_F X + 8688)) (Z64 (1 + h_extra_headers h)) (Z64 (a_S a)) (Z64 (pk_bytes op))
(Z64 (x_F X + 8400)) t3 t4 t5 t6) Fx (Z64 A_SS) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1 /\ h_eos h = 0 /\ 0 <= pno
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h)
ogc (op_cells (a_Bd a) (Some op) gw kc)
/\ og_junk ogc /\ cells_size kc = 48%nat
/\ 0 <= pk_off op /\ 0 <= pk_bytes op /\ pk_off op + pk_bytes op <= os_body_fill (h_os h) /\ 0 <= pk_e_o_s op < 1024
/\ h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * h_consumed X h.

Lemma packetout_none : forall (os os' : stream_st unit) r opo, ogg_stream_packetout os = Some ((r, opo), os') -> r <> 1 -> opo = None.
Proof.
intros os os' r opo H NR. unfold ogg_stream_packetout, packetout in H.
destruct (ogg_stream_check os); [injection H as _ <- _; reflexivity|].
destruct (_ <=? _); [injection H as _ <- _; reflexivity|].
destruct (negb _); [injection H as _ <- _; reflexivity|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [injection H as <- _ _; exfalso; exact (NR eq_refl)| discriminate H].
Qed.

Theorem h_kss_ok : hinv_ok OUT_rep IO_FP X -> forall (h : hstate unit) (pno nbr brem0 r : Z) opo (os : stream_st unit),
ogg_stream_packetout (h_os h) = Some ((r, opo), os) ->
cps asegs (at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0)
(fun c => (r <> 1 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_ogg h (h_oy h) os) nbr brem0 c)
\/ (r = 1 /\ exists op, opo = Some op /\ at_SS (set_ogg h (h_oy h) os) op pno nbr brem0 c)).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV BCMP.
intros HX h pno nbr brem0 r opo os EPO T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r5 & r7 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & ogc & opc
& Hc & FRM & HS & HIT & SI1 & E0 & PN0 & HR & OGJ & OPJ).
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h _ ogc _ HR) as OPOS.
pose proof HR as HR'. destruct HR' as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC
& OSR & (stb & STB) & RATE & (wl & LOOK) & DEC0 & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (SIN : h_stream_init h <> 0) by (rewrite SI1; discriminate).
pose proof OSR as OSR0.
unfold h_os_rep in OSR0. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0'|_]; [exfalso; exact (SIN E0')|].
destruct OSR0 as (OS & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
pose proof (own_in_os a h SIN) as (IBD & ILD & IGD).
destruct HSP as (HSP1 & HSP2 & HSP3).
pose proof (HSP1 _ _ IBD) as (B0 & B1 & B2 & _). pose proof (HSP1 _ _ ILD) as (L0 & L1 & L2 & _). pose proof (HSP1 _ _ IGD) as (G0 & G1 & G2 & _).
destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->).

unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS in Hc.
pose proof SP as SP0. unfold h_spill, HO_OS in SP0.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply kh_w0; [exact S1R| exact SP0| exact MI]. }
intros ms1 c1 -> Hc1. clear Hc SP0.

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c1 (PMfd_mat_stable F0 fs0) Hc1 _ _).
{ eapply (ogg_stream_packetout_spec (x_F X + 8688) (a_Bd a) (a_L a) (a_G a) (x_F X + 8608) (a_shdr a) (h_os h) (a_lws a) (a_gws a) k0 k1 k2 k3 k4 k5).
{ exact LH. } { exact FOK. } { exact (stream_inv_lacing_inv _ SINV). } { exact LOK. } { exact WP. } { exact LL. } { exact LG. } { exact GL. }
{ lia. } { lia. } { lia. }
{ rewrite LL. unfold bptr in *. lia. } { rewrite LG. unfold bptr in *. lia. }
{ right. lia. } { unfold bptr in *. lia. } { unfold bptr in *. lia. } { unfold bptr in *. lia. } { unfold bptr in *. lia. }
{ exact MI. } { unfold HO_OS in OS. exact OS. } { exact UL. } { exact UG. } { unfold HO_OP in OPC. exact OPC. }
{ split; [intros E; exfalso; exact (BD E)| intros E; lia]. }
{ exact EPO. } { reflexivity. } { reflexivity. } }
intros ms2 c2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & gw & -> & MU1 & WM1 & MI1 & OS1 & FOK1 & OP1) Hc2.
clear Hc1.
destruct (hrep_packetout RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h _ ogc _ r opo os gw HS HR
ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(reflexivity) SIN EPO MU1 WM1 MI1 OS1 FOK1 OP1)
as (HS1 & HR1 & LR1 & R1 & PK).
pose proof (packetout_r_eos _ _ _ _ EPO) as (RR & EOS).
pose proof HR1 as HR1'. destruct HR1' as (ART1 & MI1' & ST1 & PF1 & ERR1 & OUTR1 & SSP1 & SP1 & _).

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc2 _ _).
{ eapply (kh_w1 (x_S1 X) (x_F X)); [reflexivity| exact RR| exact S1R| unfold h_spill in SP1; exact SP1| exact MI1]. }
intros ms3 c3 (m2 & MU2 & WM2 & MI2 & [(RN & SP2 & ->) | (R1' & -> & ->)]) Hc3; clear Hc2.
-
pose proof (packetout_none _ _ _ _ EPO RN) as ENone. subst opo.
assert (SP2' : rw_cells asegs m2 (x_S1 X) (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200
(set_ogg h (h_oy h) os))).
{ unfold h_spill. cbn [set_ogg h_granule_frame_size h_extra_headers h_eos h_nframes h_channels]. rewrite E0. exact SP2. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m1 m2 a _ _
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 (set_ogg h (h_oy h) os)) ogc _ HS1 HR1 eq_refl eq_refl
ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU2 WM2 MI2 SP2') as HR2.
apply Hk. left. split; [exact RN|].
exists Σ1, a, Fx, fc, m2, (Z64 617840), t0', t1', t2', (Z64 r), (Z64 1), a2', a3', a4', a5', a6', a7', r5, (Z64 (1 + h_extra_headers h)),
t3', t4', t5', t6', j0, j192, j200, ogc, [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_ogg h_packet_count]; exact Hc3|].
split; [exact FRM|]. split; [exact HS1|]. split; [exact HIT|]. split; [exact SI1|].
split; [exact HR2|]. split; [exact OGJ| do 6 eexists; reflexivity].
-
subst r. destruct (R1 eq_refl) as (NOP & LRL).
destruct opo as [op|]; [| exfalso; exact (NOP eq_refl)].
cbn beta iota in PK, EOS. destruct PK as (PK0 & PK1 & PK2 & PK3).
destruct (packetout_same (h_os h) os 1 (Some op) EPO) as (_ & _ & EBO & _ & _ & _ & EBS & _ & EBF & ELF & ESER).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BRM & _ & PND & CNS & _ & BF & _ & _ & _ & PCL).
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
assert (BYT : pk_bytes op <= 4096) by (unfold h_consumed, h_pend in *; lia).
pose proof HR1 as HR1'. destruct HR1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OPC1 & OSR1 & _).
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c3 (PMfd_mat_stable F0 fs0) Hc3 _ _).
{ eapply (kh_w2 (x_S1 X) (x_F X) (a_Bd a) op gw [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5]);
[exact S1R| lia| unfold HO_OP in OPC1; exact OPC1| unfold h_spill in SP1; exact SP1| exact MI1]. }
intros ms4 c4 [(LT5 & ->) | (GE5 & ->)] Hc4; clear Hc3.
+
apply Hk. right. split; [reflexivity|]. exists op. split; [reflexivity|].
exists Σ1, a, Fx, fc, m1, (Z64 617840), t0', t1', t2', (Z64 5), a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', j0, j192, j200, gw, ogc,
[CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split.
{ unfold pk_sser. replace (5 <=? pk_bytes op) with false by (symmetry; apply Z.leb_gt; lia).
cbn [andb set_ogg h_packet_count h_extra_headers h_speex_serialno h_os]. exact Hc4. }
split; [exact FRM|]. split; [exact HS1|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact E0|]. split; [exact PN0|].
split; [exact HR1|]. split; [exact OGJ|]. split; [reflexivity|].
split; [exact PK0|]. split; [exact PK1|]. split; [cbn [set_ogg h_os]; unfold bptr in *; lia|]. split; [exact EOS|].
unfold h_consumed, h_pend in *. cbn [set_ogg h_os h_oy h_packet_count h_bytes_remaining]. unfold bptr in *. lia.
+
unfold h_os_rep in OSR1. cbn [set_ogg h_stream_init h_os] in OSR1. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0'|_]; [exfalso; exact (SIN E0')|].
destruct OSR1 as (OS1' & _ & (UB1 & LB1 & BP1 & _) & FOK1' & _ & BINV1 & _).
destruct (pk_window m1 (a_Bd a) (a_body a) os op UB1 BP1 (proj1 BINV1) PK0 PK1 ltac:(unfold bptr in *; lia)) as (U8 & EPD & LPB).
set (pb := firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) (a_body a))) in *.
assert (P5 : bytes_at asegs m1 (a_Bd a + pk_off op) (firstn 5 pb)).
{ unfold u8ro in U8. rewrite <- (firstn_skipn 5 pb) in U8. apply bytes_at_app in U8 as [U8 _]. exact U8. }
assert (L5 : length (firstn 5 pb) = 5%nat) by (rewrite length_firstn; lia).
assert (LOR : SEGTOP_A <= x_lo X).
{ pose proof (af_sp0_range RT AF Σ1 m ART) as SR0. rewrite ESP in SR0. pose proof (hi_lo _ _ _ HX) as (LW0 & _). lia. }
assert (INB1 : In (a_Bd a, os_body_storage os) (rt_live RT Σ1)).
{ destruct HS1 as (EL1 & _ & PERM1 & _). rewrite EL1. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PERM1)).
exact (proj1 (own_in_os a (set_ogg h (h_oy h) os) SIN)). }
Time cps_rt (BCMP Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1
(a_Bd a + pk_off op) A_SPEEX_LIT (firstn 5 pb) SPEEX5 (x_lo X)).
{ apply PMfd_fdfs_only. } { apply PMfd_mat_stable. } { rewrite L5. reflexivity. }
{ pose proof (proj1 BINV1) as ZL. destruct BP1 as (_ & BPL). unfold zlength in ZL. unfold bptr in *. unfold USTACK_TOP, RT_STACK, H_STACK in *. lia. }
{ unfold A_SPEEX_LIT. lia. }
{ exact (speex5_ro m1 MI1). }
{ rewrite L5. change (Z.of_nat 5) with 5.
pose proof (proj1 BINV1) as ZL. destruct BP1 as (_ & BPL). unfold zlength in ZL. unfold bptr in *.
apply (live_checked_src RT AF Σ1 m1 _ (x_lo X) (a_Bd a) (os_body_storage os) _ _ ART1 INB1); lia. }
{ rewrite L5. change (Z.of_nat 5) with 5. apply (speex_checked Σ1 m1 _ _ ART1). unfold A_SPEEX_LIT, SEGTOP_A in *. lia. }
{ unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST1|]. split; [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); exact LW0|].
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|]. clear - S32. Z.div_mod_to_equations. lia. }
intros c5 (v & EV & Hc5). clear Hc4. unfold icpt_postF in Hc5.
Time cps_unpack_lib Hc5 as (m3 & RS3 & RA3 & PRX3 & _).
cps_ret RS3.
pose proof (hrep_bcmp HX Σ1 m1 m3 a (set_ogg h (h_oy h) os) _ ogc _ HS1 HR1 eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl
RA3 PRX3) as HR3.
pose proof HR3 as HR3'. destruct HR3' as (ART3 & MI3 & ST3 & _ & _ & _ & _ & SP3 & _ & _ & _ & _ & _ & _ & _ & _ & OSR3 & _).
unfold h_os_rep in OSR3. cbn [set_ogg h_stream_init h_os] in OSR3.
destruct (Z.eqb_spec (h_stream_init h) 0) as [E0''|_]; [exfalso; exact (SIN E0'')|].
destruct OSR3 as (OS3 & _).
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c5 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (kh_w3 (x_S1 X) (x_F X) (a_Bd a) (a_L a) (a_G a) (a_shdr a) os);
[reflexivity| exact S1R| lia| exact FOK1'| unfold HO_OS in OS3; exact OS3| unfold h_spill in SP3; exact SP3| exact MI3]. }
intros ms6 c6 (a1'' & CASEV & ->) Hc6. clear Hc.
assert (EA1 : a1'' = Z64 (pk_sser (set_ogg h (h_oy h) os) (h_os (set_ogg h (h_oy h) os)) op)).
{ unfold pk_sser. cbn [set_ogg h_os h_speex_serialno]. replace (5 <=? pk_bytes op) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
rewrite <- EPD. destruct CASEV as [(VN & ->) | (V0 & ->)].
- replace (list_eqb (ztake 5 (map bv_unsigned pb)) SPEEX_STR) with false; [reflexivity|].
symmetry. apply not_true_is_false. intros EQ. apply VN. apply EV. apply speex_eq. exact EQ.
- replace (list_eqb (ztake 5 (map bv_unsigned pb)) SPEEX_STR) with true; [reflexivity|].
symmetry. apply speex_eq. apply EV. exact V0. }
subst a1''.
apply Hk. right. split; [reflexivity|]. exists op. split; [reflexivity|].
exists Σ1, a, Fx, fc, m3, (Z64 617884), r, r0, r1, v, r3, r4, r6, r8, r9, r10, r11, r12, r13, r14, j0, j192, j200, gw, ogc,
[CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [cbn [set_ogg h_packet_count h_extra_headers h_os]; exact Hc6|].
split; [exact FRM|]. split; [exact HS1|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact E0|]. split; [exact PN0|].
split; [exact HR3|]. split; [exact OGJ|]. split; [reflexivity|].
split; [exact PK0|]. split; [exact PK1|]. split; [cbn [set_ogg h_os]; unfold bptr in *; lia|]. split; [exact EOS|].
unfold h_consumed, h_pend in *. cbn [set_ogg h_os h_oy h_packet_count h_bytes_remaining]. unfold bptr in *. lia.
Qed.

Theorem h_ssw_ok : hinv_ok OUT_rep IO_FP X -> forall (h1 : hstate unit) (op : packet) (pno nbr brem0 : Z),
cps asegs (at_SS h1 op pno nbr brem0)
(fun c => ((pk_sser h1 (h_os h1) op = -1 \/ os_serialno (h_os h1) <> pk_sser h1 (h_os h1) op)
/\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_serialno h1 (pk_sser h1 (h_os h1) op)) nbr brem0 c)
\/ (pk_sser h1 (h_os h1) op <> -1 /\ os_serialno (h_os h1) = pk_sser h1 (h_os h1) op /\ h_packet_count h1 = 0
/\ at_HP RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 c)
\/ (pk_sser h1 (h_os h1) op <> -1 /\ os_serialno (h_os h1) = pk_sser h1 (h_os h1) op /\ h_packet_count h1 <> 0
/\ h_packet_count h1 <= 1 + h_extra_headers h1
/\ at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_serialno h1 (pk_sser h1 (h_os h1) op)) pno nbr brem0 c)
\/ (pk_sser h1 (h_os h1) op <> -1 /\ os_serialno (h_os h1) = pk_sser h1 (h_os h1) op /\ h_packet_count h1 <> 0
/\ 1 + h_extra_headers h1 < h_packet_count h1
/\ at_RF RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 c)).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV.
intros HX h1 op pno nbr brem0 T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & gw & ogc & kc
& Hc & FRM & HS & HIT & SI1 & E0 & PN0 & HR & OGJ & KCS & PK0 & PK1 & PK2 & EOS & PCR).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC
& OSR & (stb & STB) & RATE & (wl & LOOK) & DEC0 & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (SIN : h_stream_init h1 <> 0) by (rewrite SI1; discriminate).
pose proof OSR as OSR0.
unfold h_os_rep in OSR0. destruct (Z.eqb_spec (h_stream_init h1) 0) as [E0'|_]; [exfalso; exact (SIN E0')|].
destruct OSR0 as (OS & LH & _ & FOK & _).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EXR & SNR & PCR0 & _ & _ & _ & BRM & STPC & PND & CNS & _ & BF & _).
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
assert (BYT : pk_bytes op <= 4096) by (unfold h_consumed, h_pend in *; lia).
assert (SSR : -2^31 <= pk_sser h1 (h_os h1) op < 2^31).
{ unfold pk_sser. destruct (_ && _); [pose proof FOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SN & _); exact SN| exact SNR]. }
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (kh_w4 (x_S1 X) (x_F X) (a_Bd a) (a_L a) (a_G a) (pk_sser h1 (h_os h1) op) (h_packet_count h1) (1 + h_extra_headers h1) (a_shdr a) (h_os h1) op gw kc).
{ exact S1R. } { exact FP0. } { lia. } { exact FOK. } { exact SSR. } { lia. } { lia. } { lia. } { lia. }
{ unfold HO_OS in OS. exact OS. } { unfold HO_OP in OPC. exact OPC. } { unfold h_spill in SP. exact SP. } { exact MI. } }
intros ms1 c1 (m1 & MU1 & WM1 & MI1 & [(B1 & SP1 & ->) | [(B2 & B2' & SP1 & ->) | [(B3 & B3' & B3'' & SP1 & ->) | [(B4 & B4' & B4'' & B4''' & SP1 & ->) | (B5 & B5' & B5'' & B5''' & SP1 & ->)]]]]) Hc1;
clear Hc.
-
assert (SPn : rw_cells asegs m1 (x_S1 X) (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200
(set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_eos h_nframes h_channels]. rewrite E0, B1. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200 (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
destruct (hrep_op_junk RT OUT_rep ERR_rep IO_FP X Σ1 m1 a _ _ ogc (a_Bd a) op gw kc HR2) as (opc & OPJ & HR3).
apply Hk. left. split; [left; exact B1|].
exists Σ1, a, Fx, fc, m1, ra, t0, t1, t2, (Z64 (-1)), (Z64 (-1)), a2, a3, a4, a5, a6, a7, (Z64 (x_F X + 8544)), (Z64 (1 + h_extra_headers h1)),
t3, t4, t5, t6, j0, j192, j200, ogc, opc.
split; [unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_serialno h_packet_count]; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_serialno Σ1 a h1 _ HS)|]. split; [exact HIT|]. split; [exact SI1|].
split; [exact HR3|]. split; [exact OGJ| exact OPJ].
-
assert (SPn : rw_cells asegs m1 (x_S1 X) (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200
(set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_eos h_nframes h_channels]. rewrite E0. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200 (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
destruct (hrep_op_junk RT OUT_rep ERR_rep IO_FP X Σ1 m1 a _ _ ogc (a_Bd a) op gw kc HR2) as (opc & OPJ & HR3).
apply Hk. left. split; [right; exact B2'|].
exists Σ1, a, Fx, fc, m1, ra, t0, t1, t2, (Z64 (os_serialno (h_os h1))), (Z64 (pk_sser h1 (h_os h1) op)), a2, a3, a4, a5, a6, a7, (Z64 (x_F X + 8544)), (Z64 (1 + h_extra_headers h1)),
t3, t4, t5, t6, j0, j192, j200, ogc, opc.
split; [unfold h_regs, HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_serialno h_packet_count]; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_serialno Σ1 a h1 _ HS)|]. split; [exact HIT|]. split; [exact SI1|].
split; [exact HR3|]. split; [exact OGJ| exact OPJ].
-
assert (SPn : rw_cells asegs m1 (x_S1 X) (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200
(set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_eos h_nframes h_channels]. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200 (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
apply Hk. right. left. split; [exact B3|]. split; [exact B3'|]. split; [exact B3''|].
exists Σ1, a, Fx, fc, m1, ra, t0, t1, t2, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, j0, j192, j200, gw, ogc, kc.
split; [unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_serialno h_packet_count h_speex_serialno h_extra_headers]; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_serialno Σ1 a h1 _ HS)|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact E0|].
split; [exact B3''|]. split; [exact PN0|]. split; [exact HR2|]. split; [exact OGJ|]. split; [exact KCS|].
split; [exact PK0|]. split; [exact PK1|]. split; [exact PK2| exact PCR].
-
assert (SPn : rw_cells asegs m1 (x_S1 X) (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200
(set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_eos h_nframes h_channels]. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200 (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
destruct (hrep_op_junk RT OUT_rep ERR_rep IO_FP X Σ1 m1 a _ _ ogc (a_Bd a) op gw kc HR2) as (opc & OPJ & HR3).
assert (ESPL : h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule (set_serialno h1 (pk_sser h1 (h_os h1) op))))
(Z64 (h_speex_serialno (set_serialno h1 (pk_sser h1 (h_os h1) op)))) j0 j192 j200 (h_eos0 (set_serialno h1 (pk_sser h1 (h_os h1) op)))
= h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200 (set_serialno h1 (pk_sser h1 (h_os h1) op))).
{ unfold h_spill, h_eos0. cbn [set_serialno set_bits_st h_granule_frame_size h_extra_headers h_eos h_nframes h_channels h_last_granule h_speex_serialno].
rewrite E0. reflexivity. }
apply Hk. right. right. left. split; [exact B4|]. split; [exact B4'|]. split; [exact B4''|]. split; [lia|].
exists Σ1, a, Fx, fc, m1, ra, t0, t1, t2, (Z64 (pk_sser h1 (h_os h1) op)), (Z64 (pk_sser h1 (h_os h1) op)), a2, a3, a4, a5, a6, a7, (Z64 (pk_bytes op)),
t3, t4, t5, t6, j0, j192, j200, ogc, opc.
split; [unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; cbn [set_serialno h_packet_count h_eos h_extra_headers]; rewrite E0; exact Hc1|].
split; [exact FRM|].
split; [apply (hsig_k_weaken RT X Σ1 a _ 0); [unfold H_DEC_CREDIT; lia| exact (hsig_k_of RT X Σ1 a _ (hsig_set_serialno Σ1 a h1 _ HS))]|].
split; [exact HIT|]. split; [exact SI1|]. split; [left; exact E0|]. split; [exact PN0|].
split; [rewrite ESPL; exact HR3|]. split; [exact OGJ|]. split; [exact OPJ|].
split; [exact PCR|]. cbn [set_serialno h_st]. destruct (h_st h1); [discriminate| exfalso; exact (B4'' STPC)].
-
assert (SPn : rw_cells asegs m1 (x_S1 X) (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200
(set_serialno h1 (pk_sser h1 (h_os h1) op)))).
{ unfold h_spill. cbn [set_serialno h_granule_frame_size h_extra_headers h_eos h_nframes h_channels]. exact SP1. }
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h1)) (Z64 (pk_sser h1 (h_os h1) op)) j0 j192 j200 (set_serialno h1 (pk_sser h1 (h_os h1) op)))
ogc _ HS HR eq_refl eq_refl ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) eq_refl MU1 WM1 MI1 SPn) as HR1.
pose proof (hrep_set_serialno Σ1 m1 a h1 _ ogc _ (pk_sser h1 (h_os h1) op) HR1 SSR) as HR2.
apply Hk. right. right. right. split; [exact B5|]. split; [exact B5'|]. split; [exact B5''|]. split; [lia|].
exists Σ1, a, Fx, fc, m1, t0, t1, t2, a3, a4, a5, a6, a7, t3, t4, t5, t6, j0, j192, j200, gw, ogc, kc.
split; [cbn [set_serialno h_packet_count h_extra_headers]; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_serialno Σ1 a h1 _ HS)|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact E0|].
split; [exact PN0|].
assert (STN1 : h_st h1 <> None) by (destruct (h_st h1); [discriminate| exfalso; exact (B5'' STPC)]).
split; [exact STN1|]. split; [exact HR2|]. split; [exact OGJ|]. split; [exact KCS|].
split; [exact PK0|]. split; [exact PK1|]. split; [exact PK2|]. split; [lia|].
split; [exact PCR| exact STN1].
Qed.

Lemma read_from_appends : forall (b : bits_st unit) pkt len q r q',
prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning b pkt len) q = Some (r, q') -> exists bs, p_err q' = p_err q ++ bs.
Proof.
intros b pkt len q r q' H. unfold speex_bits_read_from in H. rewrite prun_bind in H.
destruct (sb_buf_size b <? len).
- rewrite prun_bind, prun_notify in H. cbn beta iota in H.
destruct (negb (sb_owner b =? 0)).
+ rewrite prun_bind in H. unfold p_realloc at 1 in H. rewrite prun_ret in H. cbn beta iota in H.
destruct (p_overflows len).
* rewrite prun_bind, prun_warning, prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as _ <-.
exists (notify_bytes MSG_PACKET_LARGER ++ warning_bytes MSG_COULD_NOT_RESIZE). cbn [p_app p_err]. rewrite app_assoc. reflexivity.
* rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as _ <-. exists (notify_bytes MSG_PACKET_LARGER). reflexivity.
+ rewrite prun_bind, prun_warning, prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as _ <-.
exists (notify_bytes MSG_PACKET_LARGER ++ warning_bytes MSG_NOT_OWNER). cbn [p_app p_err]. rewrite app_assoc. reflexivity.
- rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as _ <-. exists []. rewrite app_nil_r. reflexivity.
Qed.

Lemma pkt_eos1 : forall fuel (h : hstate unit) pno q o q', h_eos h <> 0 -> prun (hP_packet_loop fuel h pno) q = Some (o, q') -> o = Cont h /\ q' = q.
Proof.
intros [|fuel] h pno q o q' E H; unfold hP_packet_loop in H; cbn [packet_loop] in H; [rewrite prun_munr in H; discriminate H|].
replace (negb (h_eos h =? 0)) with true in H by (symmetry; apply negb_true_iff, Z.eqb_neq; exact E). rewrite prun_ret in H.
injection H as <- <-. split; reflexivity.
Qed.

Definition pk_post (fuel : nat) (q : pst) (bs : list Z) (o : outcome unit) (q' : pst) (nbr brem0 : Z) : config -> Prop :=
fun c => exists q1, p_err q1 = p_err q ++ bs /\
( (o = Returned /\ q1 = q' /\ at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c)
\/ (exists h1, o = Cont h1 /\ q1 = q' /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 nbr brem0 c)
\/ (exists h1 pno1, h_eos h1 = 0 /\ prun (hP_packet_loop fuel h1 pno1) q1 = Some (o, q') /\ at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 pno1 nbr brem0 c)).

Lemma kt_post : forall fuel q bs (h : hstate unit) pno nbr brem0 q1 o q' c, p_err q1 = p_err q ++ bs ->
prun (hP_packet_loop fuel (incr_packet_count h) pno) q1 = Some (o, q') ->
(h_eos h = 0 /\ at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h) pno nbr brem0 c)
\/ (h_eos h = 1 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h) nbr brem0 c) ->
pk_post fuel q bs o q' nbr brem0 c.
Proof.
intros fuel q bs h pno nbr brem0 q1 o q' c EB RUN [(E0 & HK) | (E1 & HP)].
- exists q1. split; [exact EB|]. right. right. exists (incr_packet_count h), pno. split; [exact E0|]. split; [exact RUN| exact HK].
- destruct (pkt_eos1 fuel (incr_packet_count h) pno q1 o q' ltac:(cbn [incr_packet_count h_eos]; lia) RUN) as (-> & ->).
exists q1. split; [exact EB|]. right. left. exists (incr_packet_count h). split; [reflexivity|]. split; [reflexivity| exact HP].
Qed.

Theorem h_ss_ok : hinv_ok OUT_rep IO_FP X -> forall fuel (h1 : hstate unit) (op : packet) (pno nbr brem0 : Z) (q : pst) (o : outcome unit) (q' : pst),
pkt_cases fuel h1 (h_os h1) op pno q o q' ->
exists bs, cpsE asegs (at_SS h1 op pno nbr brem0) (Spec.X1nu.evw 2 bs) (pk_post fuel q bs o q' nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF FD2 HDR.
intros HX fuel h1 op pno nbr brem0 q o q' CASES.
pose proof (h_ssw_ok HX h1 op pno nbr brem0) as SSW.
unfold pkt_cases in CASES.
destruct CASES as [(SC & EO & EQ) | (SN & SE & [(P0 & ph & q1 & EPH & PHC) | [(PN & PLE & RUN) | (PN & PGT & d & b & q1 & st' & b' & q2 & ESt & ERF & EDL & RUN)]])].
-
exists []. apply cpsE_nil. eapply cps_conseq; [exact SSW| intros c Hc; exact Hc|].
intros c [(_ & HPN) | [(SN' & SE' & _) | [(SN' & SE' & _) | (SN' & SE' & _)]]];
[| exfalso; destruct SC as [SC|SC]; [exact (SN' SC)| exact (SC SE')] ..].
exists q. split; [rewrite app_nil_r; reflexivity|]. right. left. exists (set_serialno h1 (pk_sser h1 (h_os h1) op)).
split; [exact EO|]. split; [symmetry; exact EQ| exact HPN].
-
destruct (app_process_header _ _ _ q ph q1 EPH) as (bs & EB').
pose proof (HDR HX (set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 q q1 ph bs EPH EB') as HDRE.
exists bs. eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & _ & HHP) | [(_ & _ & PN' & _) | (_ & _ & PN' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| | exfalso; exact (PN' P0) ..].
refine (HDRE T c HHP _). intros c' POST. apply Hk.
exists q1. split; [exact EB'|]. destruct ph as [h3|].
+ right. right. exists (incr_packet_count h3), pno.
assert (E3 : h_eos (incr_packet_count h3) = 0) by (destruct POST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3' & _); exact E3').
split; [exact E3|]. split; [exact PHC| exact POST].
+ left. destruct PHC as (-> & ->). split; [reflexivity|]. split; [reflexivity| exact POST].
-
exists []. apply cpsE_nil. eapply cps_seq; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & P0' & _) | [(_ & _ & _ & _ & HKT) | (_ & _ & _ & PGT' & _)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| exfalso; exact (PN P0')| | exfalso; lia].
refine (h_kt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X F0 fs0 HX _ pno nbr brem0 T c HKT _).
intros c' POST. apply Hk. exact (kt_post fuel q [] _ pno nbr brem0 q o q' c' ltac:(rewrite app_nil_r; reflexivity) RUN POST).
-
destruct (read_from_appends _ _ _ q b q1 ERF) as (bs1 & EB1).
pose proof EDL as EDL'. unfold hP_decode_loop in EDL'. destruct (dloop_appends _ d b q1 _ q2 EDL') as (bs2 & EB2). clear EDL'.
exists (bs1 ++ bs2). eapply cps_cpsE; [exact SSW|].
intros T c [(SC & _) | [(_ & _ & P0' & _) | [(_ & _ & _ & PLE' & _) | (_ & _ & _ & _ & HRF)]]] Hk;
[exfalso; destruct SC as [SC|SC]; [exact (SN SC)| exact (SC SE)]| exfalso; exact (PN P0')| exfalso; lia|].
assert (EB : p_err q2 = p_err q ++ (bs1 ++ bs2)) by (rewrite EB2, EB1, app_assoc; reflexivity).
refine (h_data_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF X F0 fs0 FD2 HX
(set_serialno h1 (pk_sser h1 (h_os h1) op)) op pno nbr brem0 q q1 q2 b d st' b' (bs1 ++ bs2) ESt ERF EDL EB T c HRF _).
intros c' HKT.
refine (h_kt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X F0 fs0 HX _ (pno + 1) nbr brem0 T c' HKT _).
intros c'' POST. apply Hk. exact (kt_post fuel q (bs1 ++ bs2) _ (pno + 1) nbr brem0 q2 o q' c'' EB RUN POST).
Qed.

Theorem h_pkt_ok : h_pkt_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP FD2 HDR.
intros HX fuel h pno nbr brem0 q q' o RUN.
destruct (Z.eq_dec (h_eos h) 0) as [E0|EN].
2:{ exists []. intros T c Hc _. exfalso. destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E0' & _). exact (EN E0'). }
assert (PCD : (h_packet_count h = 0 -> h_st h = None) \/ (h_packet_count h = 0 /\ h_st h <> None)).
{ destruct (Z.eq_dec (h_packet_count h) 0) as [P0|PN]; [| left; intros P0; exfalso; exact (PN P0)].
destruct (h_st h) as [d|]; [right; split; [exact P0| discriminate]| left; intros _; reflexivity]. }
destruct PCD as [PC0 | (P0 & STN)].
2:{ exists []. intros T c Hc _. exfalso. destruct Hc as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & HR & _).
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STPC & _).
destruct (h_st h); [exact (STPC P0)| exact (STN eq_refl)]. }
destruct (pkt_step fuel h pno q o q' E0 PC0 RUN) as (r & opo & os & EPO & [(RN & EO & EQ) | (R1 & op & EOP & CASES)]).
-
exists []. apply cpsE_nil. eapply cps_conseq; [exact (h_kss_ok HX h pno nbr brem0 r opo os EPO)| intros c Hc; exact Hc|].
intros c [(_ & HPN) | (R1 & _)]; [| exfalso; exact (RN R1)].
exists q. split; [rewrite app_nil_r; reflexivity|]. right. left. exists (set_ogg h (h_oy h) os).
split; [exact EO|]. split; [symmetry; exact EQ| exact HPN].
-
destruct (h_ss_ok HX fuel (set_ogg h (h_oy h) os) op pno nbr brem0 q o q' CASES) as (bs & SSE).
exists bs. eapply cps_cpsE; [exact (h_kss_ok HX h pno nbr brem0 r opo os EPO)|].
intros T c [(RN & _) | (_ & op' & EOP' & HSS)] Hk; [exfalso; exact (RN R1)|].
rewrite EOP in EOP'. injection EOP' as <-. exact (SSE T c HSS Hk).
Qed.
End Pkt2.
