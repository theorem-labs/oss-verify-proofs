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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X09c X097 X096.

From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require X1cr X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X12b X0z5 X0wl X0wn X0wm X0ys X0x2 X0yt X0zq X0zp X0zl X0zu X101 X0zw.
Module B_TWIN.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0mx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0k2.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1di OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cs OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1da OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1df OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1ck OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cv OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dh.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1r2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1nt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1rh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1re.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X06d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X091.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X101 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NbE.
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

Definition nbE_keep (P : Prop) : Prop := P.

Lemma nbE_tabs_acc_art : forall (Σ : rts RT) (m : mem), ART RT Σ m -> nb_tabs_acc m.
Proof using AF.
intros Σ m A0.
assert (K : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj bsegs m a n) by (intros a n; exact (aobj_lit RT AF Σ m a n A0)).
split.
- apply K; [unfold ACC_LITS, A_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_nb_mode; lia | unfold A_nb_mode, APP_TOP; lia].
- unfold nb_smrecs, nb_smrec1, nb_smrec2, nb_smrec3, nb_smrec4, nb_smrec5, nb_smrec6, nb_smrec7, nb_smrec8.
repeat (apply Forall_cons; [cbv beta; cbn [smr_ptr];
unfold A_nb_submode1, A_nb_submode2, A_nb_submode3, A_nb_submode4, A_nb_submode5, A_nb_submode6, A_nb_submode7, A_nb_submode8;
apply K; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia | unfold APP_TOP; lia]|]). apply Forall_nil.
Qed.

Lemma nbE_sz_shadow : forall sc rest, cells_size (nbd_shadow sc rest) = 256%nat.
Proof. intros [[] [] [] [] []] rest; reflexivity. Qed.
Lemma nbE_sz_slots : forall s, cells_size (slot_cells s) = 376%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_saves : cells_size (@fr_saves bptr X) = 200%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_hdr : forall z (st : nb_state bptr) w, cells_size (nb_hdr_cells z st w) = 32%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_cfg : forall z (st : nb_state bptr) pad, cells_size (nb_cfg_cells z st pad) = 24%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_tail : forall (st : nb_state bptr) pad, cells_size (nb_tail_cells st pad) = 20%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_ucb : forall z ju, cells_size (nb_ucb_cells z ju) = 40%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_ltpargs : forall a w o, cells_size (ltp_args_cells a w o) = 40%nat. Proof. reflexivity. Qed.
Local Ltac simpl_sizes ::=
rewrite ?nbE_sz_shadow, ?nbE_sz_slots, ?nbE_sz_saves, ?nbE_sz_hdr, ?nbE_sz_cfg, ?nbE_sz_tail, ?nbE_sz_ucb, ?nbE_sz_ltpargs;
rewrite ?length_app, ?cells_size_app, ?cells_size_f32, ?length_f32, ?repeat_length;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app, ?cells_size_f32, ?length_f32, ?repeat_length; cbn [length].

Lemma nbE_live_checked_dst : forall (Σ : rts RT) (m : mem) sp p k d n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= d -> d + n <= p + k -> wr_at bsegs m d n -> checked_dst RT Σ m sp d n.
Proof using AF.
intros Σ m sp p k d n ART0 INL H1 H2 WR. split; [intros _; split| split; [| exact WR]].
- apply (acc_sub bsegs m p k d n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
- intros i Hi. right; right; left. exists p, k. split; [exact INL| lia].
Qed.

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

Definition R_J (isv sub : Z) (xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) (x_gp X) (x_tp X) (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6.

Definition slots_J (bp' sub : Z) (s : nbslots) : nbslots :=
sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s)).

Definition at_Jc (bp' sub : Z) (st : nb_state bptr) (bJ : bits_st bptr) : config -> Prop :=
fun c => exists (Σ : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word)
(j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff) (bp : Z),
ASTA RT Σ PMc (eq (MS (R_J (nb_isave_ptr OUT st) sub xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6) Fx (Z_to_bv 64 NBE_PC_J) fc None m (seg_rom bsegs))) c
/\ frm0 fc /\ nbctx X m st bJ j ows sws (slots_J bp' sub s) ff SC_E /\ slots_EL ST OUT A FF SF olp bp sub s
/\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp' <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4
/\ nbEH_mem RT X Σ0 mE Σ m /\ nbEH_sig RT Σ0 Σ (rt_credit RT Σ0).

Definition nbE_bJ (k : ltp_kind) (ki : innov_kind) (b : bits_st bptr) : bits_st bptr :=
let b3 := innov_bits ki (hsg_bits (smr_sm r) (ltp_bits k b)) in
if negb (sm_double_codebook (smr_sm r) =? 0) then innov_bits ki b3 else b3.

Lemma nbG_acc_pres2 : forall (Σ : rts RT) (m0 m m' : mem) sp W fp kp P n,
ART RT Σ m0 -> In (fp, kp) (rt_frames RT Σ) -> fp <= P -> P + n <= fp + fs_size kp - 8 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp W m m' -> (forall i, 0 <= i < n -> outside W (shad (P + i))) ->
acc bsegs m P n -> acc bsegs m' P n.
Proof using AF.
intros Σ m0 m m' sp W fp kp P n ART0 INF F1 F2 PRES OFF ACC i Hi. destruct (ACC i Hi) as (b & B & OK). exists b. split; [| exact OK].
pose proof (frame_facts RT AF Σ m0 fp kp ART0 INF) as (FP0 & FP64 & _ & _ & _ & _ & SA & S1 & S2 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (R : shad fp <= shad (P + i) < shad (fp + fs_size kp)).
{ unfold shad. split; [assert (fp / 8 <= (P + i) / 8) by (apply Z.div_le_mono; lia); lia|].
assert ((P + i) / 8 < (fp + fs_size kp) / 8); [| lia].
assert (E8 : (fp + fs_size kp) mod 8 = 0).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. clear - FP64. set (q := 2 ^ Z.of_nat kp). assert (fp mod 8 = 0) by (Z.div_mod_to_equations; lia).
rewrite Z.add_mod, H by lia. change 64 with (8 * 8). rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia. reflexivity. }
clear - E8 F2 Hi. Z.div_mod_to_equations. lia. }
apply (bytes_at_agree bsegs m m' _ _ B). intros a Ha. cbn [length] in Ha.
apply PRES; [right; right; right; right; exists fp, kp; split; [exact INF| lia]|].
replace (bv_unsigned a) with (shad (P + i)) by lia. apply OFF. exact Hi.
Qed.

Lemma nbEH_off_shadow : forall (ST OUT A FF SF usp lo nout P n i : Z),
SF = FF / 8 + SHB -> FF mod 64 = 0 -> 0 <= P -> P + n <= 2^47 -> (P + n <= FF \/ FF + 2048 <= P) -> 0 <= i < n ->
(ST + 2968 <= SH_LO \/ SH_HI <= ST) -> (OUT + nout <= SH_LO \/ SH_HI <= OUT) -> (A + 48 <= SH_LO \/ SH_HI <= A) -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
SH_HI <= lo -> lo <= usp - 576 ->
outside [(ST, ST + 2968); (OUT, OUT + nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] (shad (P + i)).
Proof.
intros ST OUT A FF SF usp lo nout P n i ESF F64 P0 P1 PFA Hi SSH OSH ASH FSH LOS LOU.
assert (SW : SH_LO <= shad (P + i) < SH_HI) by (apply shad_window; unfold APP_TOP; Lia.lia).
assert (SHS : shad (P + i) < SF \/ SF + 256 <= shad (P + i)) by (unfold shad; rewrite ESF; clear - PFA Hi F64; Z.div_mod_to_equations; Lia.lia).
cbn [outside]. split; [clear - SW SSH; Lia.lia|]. split; [clear - SW OSH; Lia.lia|]. split; [clear - SW ASH; Lia.lia|]. split; [clear - SW FSH; Lia.lia|].
split; [clear - SHS; Lia.lia|]. split; [clear - SW LOS LOU; Lia.lia| exact I].
Qed.

Lemma nbE_mo_cases : forall mo0 (r0 : smrec), smrec_at mo0 = Some r0 ->
(mo0 = 1 /\ r0 = nb_smrec1) \/ (mo0 = 2 /\ r0 = nb_smrec2) \/ (mo0 = 3 /\ r0 = nb_smrec3) \/ (mo0 = 4 /\ r0 = nb_smrec4)
\/ (mo0 = 5 /\ r0 = nb_smrec5) \/ (mo0 = 6 /\ r0 = nb_smrec6) \/ (mo0 = 7 /\ r0 = nb_smrec7) \/ (mo0 = 8 /\ r0 = nb_smrec8).
Proof.
intros mo0 r0 H. pose proof (smrec_facts mo0 r0 H) as (_ & MO & _).
assert (C : mo0 = 1 \/ mo0 = 2 \/ mo0 = 3 \/ mo0 = 4 \/ mo0 = 5 \/ mo0 = 6 \/ mo0 = 7 \/ mo0 = 8) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn in H; injection H as <-; tauto.
Qed.
Lemma nbE_ltp_row : forall mo0 (r0 : smrec) k (m : mem) olp0, smrec_at mo0 = Some r0 -> sm_ltp_unquant (smr_sm r0) = Some k -> lib_consts m ->
(sm_lbr_pitch (smr_sm r0) = -1 /\ olp0 = 0 \/ sm_lbr_pitch (smr_sm r0) <> -1 /\ 17 <= olp0 <= 144) ->
17 <= nbe_pmin (sm_lbr_pitch (smr_sm r0)) olp0 /\ nbe_pmin (sm_lbr_pitch (smr_sm r0)) olp0 + ltp_pitch_span k <= 144
/\ nbe_pmin (sm_lbr_pitch (smr_sm r0)) olp0 <= nbe_pmax (sm_lbr_pitch (smr_sm r0)) olp0 <= 144
/\ match k with LtpPitchUnquant3tap p => ro_cells bsegs m (smr_ltp_par r0) (ltp_par_cellsA (gain_cdbk_addrA (ltp_gain_cdbk p)) (ltp_gain_bits p) (ltp_pitch_bits p))
/\ smr_ltp_par r0 mod 8 = 0 /\ 0x10000 <= smr_ltp_par r0 /\ smr_ltp_par r0 + 16 <= X07z.IMG_TOP /\ In (smr_ltp_par r0, 16) ACC_LITS
| LtpForcedPitchUnquant => True end.
Proof.
intros mo0 r0 k m olp0 SAT LTK LC HOLP. destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in LTK; injection LTK as <-; cbn in HOLP |- *;
(destruct HOLP as [(HL & HO)|(HL & HO)]; [try discriminate HL | try (exfalso; apply HL; reflexivity)]);
repeat split; try lia;
first [ apply (lib_const m); [exact LC | lc_in]
| unfold A_ltp_params_vlbr, A_ltp_params_lbr, A_ltp_params_med, A_ltp_params_nb, X07z.IMG_TOP; lia
| repeat (first [left; reflexivity | right]) ].
Qed.

Lemma nbE_shadow_acc_u : forall (m : mem) (f sf : Z) (cs : list cell) (pre rest : list byte) (n : Z),
rw_cells bsegs m sf cs -> cells_bytes cs = pre ++ ushadow n ++ rest -> sf = Z.shiftr f 3 + SHB -> f mod 64 = 0 -> 0 <= f -> 0 <= n ->
acc bsegs m (f + 8 * Z.of_nat (length pre)) n.
Proof.
intros m f sf cs pre rest n [[_ B] _] E Esf F64 F0 N0. rewrite E in B.
apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [B _].
apply (acc_ushadow bsegs); [clear - F64; Z.div_mod_to_equations; lia | lia | lia |].
replace (shad (f + 8 * Z.of_nat (length pre))) with (sf + Z.of_nat (length pre)); [exact B|].
rewrite Esf, shad_shiftr. unfold shad. clear - F64. Z.div_mod_to_equations. lia.
Qed.

Lemma nbsh_acc_E : forall (m : mem) (F0 S0 : Z) rest, rw_cells bsegs m S0 (nbd_shadow SC_E rest) -> S0 = Z.shiftr F0 3 + SHB -> F0 mod 64 = 0 -> 0 <= F0 ->
acc bsegs m (F0 + 32) 4 /\ acc bsegs m (F0 + 48) 12 /\ acc bsegs m (F0 + 320) 160 /\ acc bsegs m (F0 + 544) 160.
Proof.
intros m F0 S0 rest SH ESF F64 FPOS. split; [| split; [| split]].
- pose proof (nbE_shadow_acc_u m F0 S0 _ (firstn 4 (nbd_shadow_bytes SC_E)) (skipn 5 (nbd_shadow_bytes SC_E) ++ rest ++ []) 4 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS| lia].
- pose proof (nbE_shadow_acc_u m F0 S0 _ (firstn 6 (nbd_shadow_bytes SC_E)) (skipn 8 (nbd_shadow_bytes SC_E) ++ rest ++ []) 12 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS| lia].
- pose proof (shadow_acc m F0 S0 _ (firstn 40 (nbd_shadow_bytes SC_E)) (skipn 60 (nbd_shadow_bytes SC_E) ++ rest ++ []) 20 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
- pose proof (shadow_acc m F0 S0 _ (firstn 68 (nbd_shadow_bytes SC_E)) (skipn 88 (nbd_shadow_bytes SC_E) ++ rest ++ []) 20 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
Qed.
Lemma nbsh_acc_E2 : forall (m : mem) (F0 S0 : Z) rest, rw_cells bsegs m S0 (nbd_shadow SC_E2 rest) -> S0 = Z.shiftr F0 3 + SHB -> F0 mod 64 = 0 -> 0 <= F0 ->
acc bsegs m (F0 + 320) 160 /\ acc bsegs m (F0 + 768) 160.
Proof.
intros m F0 S0 rest SH ESF F64 FPOS. split.
- pose proof (shadow_acc m F0 S0 _ (firstn 40 (nbd_shadow_bytes SC_E2)) (skipn 60 (nbd_shadow_bytes SC_E2) ++ rest ++ []) 20 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
- pose proof (shadow_acc m F0 S0 _ (firstn 96 (nbd_shadow_bytes SC_E2)) (skipn 116 (nbd_shadow_bytes SC_E2) ++ rest ++ []) 20 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
Qed.

Lemma nbE_live_apart : forall (Σ : rts RT) (m : mem) p1 n1 p2 n2, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> p1 <> p2 ->
p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
intros Σ m p1 n1 p2 n2 ART0 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 ART0 E). rewrite E in H2. apply in_app_iff in H2. apply in_app_iff.
destruct H2 as [H2|[H2|H2]]; [left; exact H2| exfalso; apply NE; congruence| right; exact H2].
Qed.

Lemma nbE_frame_checked_dst : forall (Σ : rts RT) (m : mem) sp f k d n,
In (f, k) (rt_frames RT Σ) -> f <= d -> d + n <= f + fs_size k - 8 -> acc bsegs m d n -> wr_at bsegs m d n -> checked_dst RT Σ m sp d n.
Proof.
intros Σ m sp f k d n INF H1 H2 ACC WR. split; [intros _; split| split; [| exact WR]].
- exact ACC.
- right; left. exists f, k. split; [exact INF| lia].
- intros i Hi. right; right; right; left. exists f, k. split; [exact INF| lia].
Qed.

Lemma nbE_ltp_bits_size : forall k (b : bits_st bptr), sb_buf_size (ltp_bits k b) = sb_buf_size b.
Proof. intros [|p] b; cbn [ltp_bits]; [reflexivity|]. unfold ltp3_bits. rewrite !ub_size. reflexivity. Qed.
Lemma nbE_ltp_pitch : forall mo0 (r0 : smrec) k (b : bits_st bptr) start, smrec_at mo0 = Some r0 -> sm_ltp_unquant (smr_sm r0) = Some k -> bits_ok b ->
start <= ltp_pitch k start b <= start + ltp_pitch_span k.
Proof.
intros mo0 r0 k b start SAT LTK OK. destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in LTK; injection LTK as <-; cbn [ltp_pitch ltp_pitch_span]; try lia;
unfold ltp3_pitch; cbn [ltp_pitch_bits ltp_params_vlbr ltp_params_lbr ltp_params_med ltp_params_nb];
match goal with |- context [uv b ?n] => pose proof (ub_ok b n OK ltac:(lia)) as (_ & _ & U) end; lia.
Qed.

Lemma nbE_innov_row : forall mo0 (r0 : smrec) ki (m : mem), smrec_at mo0 = Some r0 -> sm_innovation_unquant (smr_sm r0) = Some ki -> lib_consts m ->
match ki with InnovSplitCbShapeSignUnquant p => ro_cells bsegs m (smr_innov_par r0) (scb_par_cellsA p) /\ smr_innov_par r0 mod 8 = 0 /\ 0x10000 <= smr_innov_par r0
/\ smr_innov_par r0 + 24 <= X07z.IMG_TOP /\ In (smr_innov_par r0, 24) ACC_LITS
| InnovNoiseCodebookUnquant => True end.
Proof.
intros mo0 r0 ki m SAT INK LC. destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in INK; injection INK as <-; cbn; repeat split;
first [ apply (lib_const m); [exact LC | lc_in]
| unfold A_split_cb_nb_vlbr, A_split_cb_nb_lbr, A_split_cb_nb_med, A_split_cb_nb, A_split_cb_sb, A_split_cb_nb_ulbr, X07z.IMG_TOP; lia
| repeat (first [left; reflexivity | right]) ].
Qed.
Lemma nbE_scb_bits_ok : forall n hs sbits (bb : bits_st bptr), bits_ok bb -> 0 <= sbits -> bits_ok (scb_bits n hs sbits bb) /\ sb_buf_size (scb_bits n hs sbits bb) = sb_buf_size bb.
Proof.
induction n as [|n IH]; intros hs sbits bb OKb Hs; cbn [scb_bits]; [split; [exact OKb| reflexivity]|].
destruct (negb (hs =? 0)).
- destruct (ub_ok bb 1 OKb ltac:(lia)) as (OK1 & SZ1 & _). destruct (ub_ok (ub bb 1) sbits OK1 Hs) as (OK3 & SZ3 & _).
destruct (IH hs sbits _ OK3 Hs) as (OK4 & SZ4). split; [exact OK4| rewrite SZ4, SZ3, SZ1; reflexivity].
- destruct (ub_ok bb sbits OKb Hs) as (OK3 & SZ3 & _). destruct (IH hs sbits _ OK3 Hs) as (OK4 & SZ4). split; [exact OK4| rewrite SZ4, SZ3; reflexivity].
Qed.
Lemma nbE_innov_bits_ok : forall mo0 (r0 : smrec) ki (b : bits_st bptr), smrec_at mo0 = Some r0 -> sm_innovation_unquant (smr_sm r0) = Some ki -> bits_ok b ->
bits_ok (innov_bits ki b) /\ sb_buf_size (innov_bits ki b) = sb_buf_size b.
Proof.
intros mo0 r0 ki b SAT INK OK. destruct ki as [|p]; cbn [innov_bits]; [split; [exact OK| reflexivity]|].
destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in INK; try discriminate INK; injection INK as <-; (apply nbE_scb_bits_ok; [exact OK| cbn; lia]).
Qed.
Lemma nbE_hsg_ok : forall sm (b : bits_st bptr), bits_ok b -> bits_ok (hsg_bits sm b) /\ sb_buf_size (hsg_bits sm b) = sb_buf_size b.
Proof.
intros sm b OK. unfold hsg_bits. destruct (sm_have_subframe_gain sm =? 3); [destruct (ub_ok b 3 OK ltac:(lia)) as (O & S & _); split; assumption|].
destruct (sm_have_subframe_gain sm =? 1); [destruct (ub_ok b 1 OK ltac:(lia)) as (O & S & _); split; assumption| split; [exact OK| reflexivity]].
Qed.
Lemma nbE_ltp_bits_ok : forall mo0 (r0 : smrec) k (b : bits_st bptr), smrec_at mo0 = Some r0 -> sm_ltp_unquant (smr_sm r0) = Some k -> bits_ok b -> bits_ok (ltp_bits k b).
Proof.
intros mo0 r0 k b SAT LTK OK. destruct k as [|p]; cbn [ltp_bits]; [exact OK|]. unfold ltp3_bits.
destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in LTK; try discriminate LTK; injection LTK as <-; cbn [ltp_pitch_bits ltp_gain_bits ltp_params_vlbr ltp_params_lbr ltp_params_med ltp_params_nb];
match goal with |- bits_ok (ub (ub b ?n1) ?n2) => exact (proj1 (ub_ok (ub b n1) n2 (proj1 (ub_ok b n1 OK ltac:(lia))) ltac:(lia))) end.
Qed.

Lemma nbE_h2z : forall (usp ST FF EXW : Z) (gp tp xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
mem_inv bsegs m ->
evt bsegs (fun ms => exists (F' : bvmap 5 word) (a0' a1' a2' a3' a4' a5' : word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5' a6 a7
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 0) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F' (Z_to_bv 64 NBE_PC_H3) fc None m (seg_rom bsegs))
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 0) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa3418) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros MI.
unfold NBE_PC_H3 in *.
astep.
apply evt_done. do 7 eexists. reflexivity.
Qed.

Lemma nbE_A : forall (bp sub : Z) (st : nb_state bptr) (b : bits_st bptr) (k : ltp_kind) (ki : innov_kind),
0 <= sub < 4 -> sm_ltp_unquant (smr_sm r) = Some k -> sm_innovation_unquant (smr_sm r) = Some ki ->
cps bsegs (at_ELc RT PMc X Σ0 mE r mo olp bp sub st b) (fun c => exists bp', at_Jc bp' sub st (nbE_bJ k ki b) c).
Proof.
intros bp sub st b k ki SUB LTK INK T c Hc Hk.
destruct Hc as (Σ & Hc & SIG).
destruct (ASTA_unpack RT Σ PMc _ c Hc) as (ms & (ATEL & MEM) & Hc0); clear Hc.
destruct ATEL as (Fx & fc & m & xra & t0 & t1 & a0 & a1 & a2 & a3 & a4 & a5 & s2 & s3 & s4 & s7 & s9 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff
& -> & FRM & CTX & SLE & SAT & EMO & BP & OLP & SUB').
cbn [ms_mem] in MEM. destruct MEM as (ART0 & NACC & WM0 & PF).
destruct SIG as (LV & FRS & SP0 & CR & POI).
destruct CTX as (MI0 & STK0 & NBP & JOK & CBOK & NINV & BREP & BOK & BSZ & OW & LOW & SW & LSW & (SL & SV) & FFA & FFOK & (rest & SH) & CC & LC & JEXC & JISV).
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
assert (LBS : Z.of_nat (length bs) = sb_buf_size b)
by (pose proof BOK as BOK'; unfold bits_ok in BOK'; rewrite Hbs, zlength_map_unsigned in BOK'; clear - BOK'; lia).
assert (DLOb : D + Z.of_nat (length bs) <= lo) by (rewrite LBS, BSZ, <- DSZ; exact DLO).
assert (DPD : D + Z.of_nat (length bs) <= PD + ND) by (rewrite LBS, BSZ, <- DSZ; exact PD2).
assert (DSZb : Z.of_nat (length bs) = x_dsz X) by (rewrite LBS, BSZ, <- DSZ; reflexivity).

cps_norm. unfold IMG_TOP_B in *. cps_hide.
cps_seg (nbe_a usp lo ST OUT A FF SF olp bp sub (nb_isave_ptr OUT st) (x_gp X) (x_tp X) xra t0 t1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s7 s9 t3 t4 t5 t6 s Fx fc m
SL SLE P3 P9 OBS S8 SPOS SLO SSH ISB SUB STK0 ltac:(clear - LOU; lia) LOS SPH MI0).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & SL1). clear SL.
clear STK0 OBS ACS WRS.
assert (ART1 : ART RT Σ m1).
{ apply (af_frame RT AF Σ m m1 lo ART0 LOWS); [| exact WM1]. intros a Ha; apply MU1; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m m1 MU1.
clear ART0. nbe_seg_tr m m1 MU1 WM1. try match goal with MI : mem_inv bsegs m |- _ => clear MI end.

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
assert (CD1 : checked_dst RT Σ m1 (Z_to_bv 64 (usp + -576)) (ST + 1368 + 160 * sub) 160).
{ split; [intros _; split| split; [| exact WRX]].
- exact (acc_sub bsegs m1 ST 2968 (ST + 1368 + 160 * sub) 160 ACS1 ltac:(clear - SUB; lia) ltac:(clear - SUB; lia)).
- left. exists ST, 2968. split; [exact INL| clear - SUB; lia].
- intros i Hi. right; right; left. exists ST, 2968. split; [exact INL| clear - SUB Hi; lia]. }
cps_rt (MST Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (ST + 1368 + 160 * sub) 160 (Z_to_bv 8 0) lo).
{ clear - SPOS SLO LOU NTOP SUB. lia. }
{ cps_callok. }
intros c2 Hc2.
clear CD1 ACS1.
nbe_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
nbe_trp PRES2.
cps_pf_pres PRES2.
clear ART1 MI1 ST1.

assert (EXZ : rw_cells bsegs m2 (ST + 1368 + 160 * sub) (f32 (repeat (Z_to_bv 64 0) 40))).
{ split; [split; [apply cells_wf_f32 | replace (cells_bytes (f32 (repeat (Z_to_bv 64 0) 40))) with (repeat (Z_to_bv 8 0) (Z.to_nat 160)) by (vm_compute; reflexivity); exact BY2]|].
rewrite cells_size_f32, repeat_length. exact (wr_at_transport bsegs m1 m2 _ _ WRX WM2). }
clear BY2 WRX.

unfold nb_hdr_cells in P1. chunk_uncons P1 as P1a. chunk_uncons P1 as P1b. chunk_uncons P1 as P1c.
replace (ST + 8 + 4) with (ST + 12) in P1c by lia. replace (ST + 8 + 4 + 4) with (ST + 16) in P1 by lia.
pose proof NINV as (NCL & _). rewrite NCL in P1c.
destruct (af_acc_live RT AF Σ m2 ST 2968 ART2 INL) as (_ & ACS2).
assert (OBS2 : aobj bsegs m2 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS2]). clear ACS2.
pose proof (AF_LIB Σ m2 ART2) as LC2. pose proof (nbE_tabs_acc_art Σ m2 ART2) as NTA2. pose proof (af_client_consts RT AF Σ m2 ART2) as CC2.
cps_seg (nbe_b usp lo ST OUT A FF SF olp bp sub (nb_isave_ptr OUT st) mo r k st (j_pad1 j) (j_last_pitch_gain j) (j_last_pitch j)
(x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s Fx fc m2
SL1 SLE P15 EMO SAT LTK P1c P11 OBS2 S8 SPOS SLO SSH LC2 NTA2 CC2 OLP SUB F0 F64 FLO ST2 ltac:(clear - NROOM; lia) LOS SPH U32 MI2).
destruct POST as (m3 & F3 & xt0 & xt2 & jk & -> & MU3 & WM3 & MI3 & ST3 & SL3 & SA3). clear SL1 ST2 OBS2 LC2 NTA2 CC2.
assert (ART3 : ART RT Σ m3).
{ apply (af_frame RT AF Σ m2 m3 lo ART2 LOWS); [| exact WM3]. intros a Ha; apply MU3; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m2 m3 MU3.
clear ART2. nbe_seg_tr m2 m3 MU3 WM3. try match goal with MI : mem_inv bsegs m2 |- _ => clear MI end.

pose proof (AF_LIB Σ m3 ART3) as LC3.
destruct (nbE_ltp_row mo r k m3 olp SAT LTK LC3 OLP) as (LS1 & LS2 & LS3 & LPAR). clear LC3.
pose proof (nbsh_acc_E m3 FF SF rest SH ESF F64 ltac:(lia)) as (ACP3 & ACG3 & ACI3 & ACE3).
assert (OFFA : forall i, 0 <= i < 48 -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -576, usp)] (shad (A + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 Σ m3 m m3 (usp + -576) _ fh kh A 48 ART3 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA3.
pose proof (nbE_live_apart Σ m3 PD ND ST 2968 ART3 INPD INL PDS) as PDST.
assert (BREP3 : bits_rep bsegs m3 A D b)
by exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB m3 D bs) BDAT) Hbs)) BSIDE)).
apply rw_cells_app in SA3. destruct SA3 as (SA3a & SA3b). rewrite nbE_sz_ltpargs in SA3b. change (Z.of_nat 40) with 40 in SA3b.
assert (EXB3 : rw_cells bsegs m3 (ST + 32) (f32 (ex1 ++ repeat (Z_to_bv 64 0) 40 ++ ex3))).
{ apply nbe_f32_join_win; [exact EX1| rewrite LEX1; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by (clear; lia); exact EXZ|].
rewrite LEX1, repeat_length. replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 160) by (clear; lia). exact EX3. }
clear EX1 EXZ EX3.
cps_rt (LTP k LTK Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc m3 A D b (ST + 32) (334 + 40 * sub) (FF + 544) (FF + 32) (FF + 48)
(nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) (nbe_pmax (sm_lbr_pitch (smr_sm r)) olp) (smr_ltp_par r) (40 * sub) lo ST 2968 PD ND FF fh NBD_FCLASS kh
(ex1 ++ repeat (Z_to_bv 64 0) 40 ++ ex3) (f_exc32 ff) (f_pg ff) (f_pitch ff) (Z_to_bv 64 0)).
{ f_equal. clear. lia. }
{ rewrite !length_app, repeat_length. clear - LEX1 LEX3 SUB. lia. }
{ rewrite !length_app, repeat_length. clear - LEX1 LEX3 SUB. lia. }
{ unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACE3| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACP3| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACG3| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold hidp. right. lia. }
{ unfold hidp. right. lia. }
{ unfold hidp. left. lia. }
{ unfold in_frame_obj, BITS_SIZEOF. split; [exact FHA1|]. split; [exact FHA2|]. split; [exact ACA3| clear - A8; Z.div_mod_to_equations; lia]. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact SA3a. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact ST3. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold RT_STACK, LTP_STACK. clear - NROOM. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold USTACK_TOP. clear - NTOP. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). clear - U32. Z.div_mod_to_equations. lia. }
intros c4 (Σ4 & Hc4 & LV4 & FRS4 & SP4 & CR4 & PO4).
cps_unpack_lib Hc4 as (v4 & m4 & eb4 & e324 & pg4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & EB4 & LEB4 & E324 & LE324 & PV4 & PG4 & LPG4 & BREP4 & BOK4 & SA4 & ACE4 & ACP4 & ACG4 & ACA4).
clear EXB3 FFe FFp FFg BOBJ BDAT SA3a ACE3 ACP3 ACG3 ACA3 ACI3 BREP3.
nbe_trp PRES4.
nbe_pf_fp PRES4.
clear ART3 MI3 ST3 PRES4. try clear Hc. try clear Hc1.

rewrite <- LV4 in INL, INPD, LV, PF, SPL. rewrite <- FRS4 in INF, INFH, FRS, PF, SPL. rewrite <- SP4 in LOWS, SP0, SPL. rewrite <- CR4 in CR. rewrite <- PO4 in POA, POI.
clear LV4 FRS4 SP4 CR4 PO4.

rewrite !length_app, repeat_length in LEB4.
destruct BREP4 as ((rj4 & Lrj4 & BOBJ4) & (bs4 & BDAT4 & Hbs4) & BSIDE4). unfold bits_cells in BOBJ4. apply (proj1 (u8arr_rw_CB m4 D bs4)) in BDAT4.
assert (LBS4 : Z.of_nat (length bs4) = sb_buf_size b)
by (pose proof BOK4 as BOK'; unfold bits_ok in BOK'; rewrite Hbs4, zlength_map_unsigned, nbE_ltp_bits_size in BOK'; clear - BOK'; lia).
assert (DSZb4 : Z.of_nat (length bs4) = x_dsz X) by (rewrite LBS4, BSZ, <- DSZ; reflexivity).
assert (DLOb4 : D + Z.of_nat (length bs4) <= lo) by (rewrite DSZb4; exact DLO).
assert (DPD4 : D + Z.of_nat (length bs4) <= PD + ND) by (rewrite DSZb4; exact PD2).
clear LBS DSZb DLOb DPD Hbs BSIDE Lrj.

clear FRM. rename RS4 into FRM.
pose proof SLE as (E0s & E24s & E32s & E40s & E48s & E56s & E64s & E72s & E80s & E88s & E96s & E104s & E120s & E128s & E136s & E144s & E152s & E160s & E168s & E176s
& E184s & E192s & E200s & E208s & E216s & E232s & E240s & E256s & E264s & E272s & E280s & E288s & E296s & E304s & E312s & E320s & E328s & E336s & E344s & E368s).
pose proof (nbE_ltp_pitch mo r k b (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) SAT LTK BOK) as PPR.
assert (PP : 17 <= ltp_pitch k (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) b <= 144) by (clear - PPR LS1 LS2; lia).
assert (SA34 : rw_cells bsegs m4 (usp + -624) (ltp_args_cells A (Z_to_bv 64 0) (40 * sub) ++ [CB 8 jk]))
by (apply rw_cells_app; split; [exact SA4| rewrite nbE_sz_ltpargs; exact SA3b]).
clear SA4 SA3b.
assert (OBE4 : aobj bsegs m4 (FF + 544) 160) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACE4]).
pose proof (af_client_consts RT AF Σ4 m4 ART4) as CC4.
cps_seg (nbe_c usp lo ST OUT A FF SF olp bp sub (nb_isave_ptr OUT st) (ltp_pitch k (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) b) (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(slots_Eb ST (slots_Ea (ST + 1368) sub s)) jk e324 pg4 _ _ m4
SL3 ltac:(cbn; exact E256s) ltac:(cbn; exact E96s) ltac:(cbn; exact E296s)
SA34 E324 LE324 OBE4 PG4 LPG4 PV4 BP PP SUB F0 F64 FLO FTOP FSH ST4 ltac:(clear - NROOM; lia) LOS SPH U32 MI4 CC4 FRM).
destruct POST as (m5 & F5 & fc5 & yt0 & yt1 & yt2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & bp' & e325
& -> & FRM5 & MU5 & WM5 & MI5 & ST5 & SL5 & BPE & E325 & LE325).
clear SL3 SA34 E324 ST4 OBE4 CC4 FRM ACE4 ACP4 ACG4.
assert (ART5 : ART RT Σ4 m5).
{ apply (af_frame RT AF Σ4 m4 m5 lo ART4 LOWS); [| exact WM5]. intros a Ha; apply MU5; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m4 m5 MU5.
clear ART4. nbe_seg_tr m4 m5 MU5 WM5. try match goal with MI : mem_inv bsegs m4 |- _ => clear MI end.

pose proof (nbsh_acc_E m5 FF SF rest SH ESF F64 ltac:(lia)) as (_ & _ & ACI5 & _).
pose proof (proj2 FFi) as WRI. rewrite cells_size_f32, FL5 in WRI. change (Z.of_nat (4 * 40)) with 160 in WRI.
assert (CD2 : checked_dst RT Σ4 m5 (Z_to_bv 64 (usp + -576)) (FF + 320) 160)
by (apply (nbE_frame_checked_dst Σ4 m5 _ FF NBD_FCLASS); [exact INF| lia| fs_lit; lia| exact ACI5| exact WRI]).
cps_rt (MST Σ4 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (FF + 320) 160 (Z_to_bv 8 0) lo).
{ clear - F0 FLO LOU NTOP. lia. }
{ cps_callok. }
intros c6 Hc6.
clear CD2 ACI5 FFi.
nbe_unpack Hc6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & BY6).
nbe_trp PRES6.
cps_pf_pres PRES6.
clear ART5 MI5 ST5 PRES6.
assert (FFi6 : rw_cells bsegs m6 (FF + 320) (f32 (repeat (Z_to_bv 64 0) 40))).
{ split; [split; [apply cells_wf_f32 | replace (cells_bytes (f32 (repeat (Z_to_bv 64 0) 40))) with (repeat (Z_to_bv 8 0) (Z.to_nat 160)) by (vm_compute; reflexivity); exact BY6]|].
rewrite cells_size_f32, repeat_length. exact (wr_at_transport bsegs m5 m6 _ _ WRI WM6). }
clear BY6 WRI.

destruct (af_acc_live RT AF Σ4 m6 ST 2968 ART6 INL) as (_ & ACS6).
assert (OBS6 : aobj bsegs m6 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS6]). clear ACS6.
pose proof (AF_LIB Σ4 m6 ART6) as LC6. pose proof (nbE_tabs_acc_art Σ4 m6 ART6) as NTA6. pose proof (af_client_consts RT AF Σ4 m6 ART6) as CC6.
assert (BREP6 : bits_rep bsegs m6 A D (ltp_bits k b))
by exact (conj (ex_intro _ rj4 (conj Lrj4 BOBJ4)) (conj (ex_intro _ bs4 (conj (proj2 (u8arr_rw_CB m6 D bs4) BDAT4) Hbs4)) BSIDE4)).
pose proof (nbG_acc_pres2 Σ4 m6 m m6 (usp + -576) _ fh kh A 48 ART6 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA6.
assert (OBA6 : aobj bsegs m6 A 48) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACA6]).
destruct (af_acc_live RT AF Σ4 m6 PD ND ART6 INPD) as (_ & ACD6).
assert (OBD6 : aobj bsegs m6 D (sb_buf_size (ltp_bits k b))).
{ rewrite nbE_ltp_bits_size, BSZ, <- DSZ. split; [lia|]. split; [unfold APP_TOP, USTACK_TOP in *; lia|].
exact (acc_sub bsegs m6 PD ND D (x_dsz X) ACD6 PD1 PD2). }
assert (K3 : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj bsegs m6 a n) by (intros a n; exact (aobj_lit RT AF Σ4 m6 a n ART6)).
assert (OS3 : aobj bsegs m6 A_scal3 32) by (apply K3; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_scal3; lia | unfold A_scal3, APP_TOP; lia]).
assert (OS1 : aobj bsegs m6 A_scal1 8) by (apply K3; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_scal1; lia | unfold A_scal1, APP_TOP; lia]).
clear K3 ACD6.
cps_seg (nbe_d1 usp lo ST OUT A D FF SF (nb_isave_ptr OUT st) sub mo r st (j_pad1 j) (ltp_bits k b) (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s))) _ _ m6
SL5 ltac:(cbn; exact E328s) ltac:(cbn; exact E344s) ltac:(cbn; exact E336s) ltac:(cbn; exact E312s) ltac:(cbn; exact E288s)
P15 EMO SAT OBS6 S8 SPOS SLO SSH LC6 NTA6 CC6 BREP6 BOK4 OBA6 OBD6 ASH ALO ltac:(rewrite nbE_ltp_bits_size, BSZ, <- DSZ; exact DLO)
OS3 OS1 ST6 ltac:(clear - NROOM; lia) LOS SPH MI6 FRM5).
destruct POST as (m7 & F7 & fc7 & xra7 & zt0 & zt1 & zt2 & za0 & za1 & za2 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & -> & FRM7 & MU7 & WM7 & MI7 & ST7 & BREP7).
clear BOBJ4 BDAT4 BREP6 OBS6 LC6 NTA6 CC6 ACA6 OBA6 OBD6 OS3 OS1 ST6 FRM5.
unfold BITS_SIZEOF in MU7.
assert (ART7 : ART RT Σ4 m7).
{ apply (af_frame RT AF Σ4 m6 m7 lo ART6 LOWS); [| exact WM7]. intros a Ha; apply MU7; cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists fh, kh; split; [exact INFH| clear - Hin FHA1 FHA2; lia]|].
split; [intros Hin; apply Ha; left; unfold USTACK_TOP; clear - Hin LOU NROOM NTOP; lia| exact I]. }
cps_pf_seg m6 m7 MU7.
clear ART6. nbe_seg_tr m6 m7 MU7 WM7. try match goal with MI : mem_inv bsegs m6 |- _ => clear MI end.
destruct (af_acc_live RT AF Σ4 m7 ST 2968 ART7 INL) as (_ & ACS7).
assert (OBS7 : aobj bsegs m7 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS7]). clear ACS7.
pose proof (AF_LIB Σ4 m7 ART7) as LC7. pose proof (nbE_tabs_acc_art Σ4 m7 ART7) as NTA7. pose proof (af_client_consts RT AF Σ4 m7 ART7) as CC7.
cps_seg (nbe_d2 usp lo ST OUT A FF SF (nb_isave_ptr OUT st) sub mo r ki st (j_pad1 j) (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s))) _ _ m7
SL5 ltac:(cbn; exact E328s) ltac:(cbn; exact E344s) ltac:(cbn; exact E336s) ltac:(cbn; exact E288s) ltac:(cbn; exact E304s) ltac:(cbn; exact E216s)
P15 EMO SAT INK OBS7 S8 SPOS SLO SSH LC7 NTA7 CC7 ST7 ltac:(clear - NROOM; lia) LOS SPH MI7).
destruct POST as (zt0' & zt2' & za7' & ->). clear OBS7 LC7 NTA7 CC7.

pose proof (AF_LIB Σ4 m7 ART7) as LC7.
pose proof (nbE_innov_row mo r ki m7 SAT INK LC7) as IPAR. clear LC7.
pose proof (nbE_ltp_bits_ok mo r k b SAT LTK BOK) as BOKl.
destruct (nbE_hsg_ok (smr_sm r) (ltp_bits k b) BOKl) as (BOKh & BSZh).
pose proof (nbsh_acc_E m7 FF SF rest SH ESF F64 ltac:(lia)) as (_ & _ & ACI7 & _).
pose proof (nbG_acc_pres2 Σ4 m7 m m7 (usp + -576) _ fh kh A 48 ART7 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA7.
cps_rt (INN ki INK Σ4 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 A D (hsg_bits (smr_sm r) (ltp_bits k b))
(FF + 320) (ST + 2228) (smr_innov_par r) lo ST 2968 PD ND fh kh (repeat (Z_to_bv 64 0) 40) (j_seed j) (Z_to_bv 64 0)).
{ left. exists FF, NBD_FCLASS. split; [exact INF|]. unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACI7| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold in_frame_obj, BITS_SIZEOF. split; [exact FHA1|]. split; [exact FHA2|]. split; [exact ACA7| clear - A8; Z.div_mod_to_equations; lia]. }
{ rewrite BSZh, nbE_ltp_bits_size, BSZ, <- DSZ. exact PD2. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact ST7. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold RT_STACK, INNOV_STACK. clear - NROOM. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold USTACK_TOP. clear - NTOP. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). clear - U32. Z.div_mod_to_equations. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact POA. }
intros c8 (Σ8 & Hc8 & LV8 & FRS8 & SP8 & CR8 & PO8).
cps_unpack_lib Hc8 as (v8 & m8 & is8 & seed8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & FFi8 & LFi8 & SEED8 & BREP8 & BOK8 & ACI8 & ACA8).
clear FFi6 P14 ACI7 ACA7.
clear BREP7.
nbe_trp PRES8.
nbe_pf_fp PRES8.
clear ART7 MI7 ST7 PRES8. try clear Hc0.
rewrite <- LV8 in INL, INPD, LV, PF, SPL. rewrite <- FRS8 in INF, INFH, FRS, PF, SPL. rewrite <- SP8 in LOWS, SP0, SPL. rewrite <- CR8 in CR. rewrite <- PO8 in POA, POI.
clear LV8 FRS8 SP8 CR8 PO8.
clear FRM7. rename RS8 into FRM.

destruct (nbE_innov_bits_ok mo r ki _ SAT INK BOKh) as (_ & BSZi).
destruct BREP8 as ((rj8 & Lrj8 & BOBJ8) & (bs8 & BDAT8 & Hbs8) & BSIDE8). unfold bits_cells in BOBJ8. apply (proj1 (u8arr_rw_CB m8 D bs8)) in BDAT8.
assert (LBS8 : Z.of_nat (length bs8) = sb_buf_size b)
by (pose proof BOK8 as BOK'; unfold bits_ok in BOK'; rewrite Hbs8, zlength_map_unsigned, BSZi, BSZh, nbE_ltp_bits_size in BOK'; clear - BOK'; lia).
assert (DSZb8 : Z.of_nat (length bs8) = x_dsz X) by (rewrite LBS8, BSZ, <- DSZ; reflexivity).
assert (DLOb8 : D + Z.of_nat (length bs8) <= lo) by (rewrite DSZb8; exact DLO).
assert (DPD8 : D + Z.of_nat (length bs8) <= PD + ND) by (rewrite DSZb8; exact PD2).
clear LBS4 DSZb4 DLOb4 DPD4 Hbs4 BSIDE4 Lrj4 BOK4.

destruct (af_acc_live RT AF Σ8 m8 ST 2968 ART8 INL) as (_ & ACS8).
assert (OBS8 : aobj bsegs m8 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS8]). clear ACS8.
pose proof (AF_LIB Σ8 m8 ART8) as LC8. pose proof (nbE_tabs_acc_art Σ8 m8 ART8) as NTA8. pose proof (af_client_consts RT AF Σ8 m8 ART8) as CC8.
assert (OBI8 : aobj bsegs m8 (FF + 320) 160) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACI8]).
cps_seg (nbe_e usp lo ST OUT A FF SF (nb_isave_ptr OUT st) sub mo r st (j_pad1 j) rest is8 (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s))) _ _ m8
SL5 ltac:(cbn; exact E328s) ltac:(cbn; exact E344s) ltac:(cbn; exact E336s) ltac:(cbn; exact E312s) ltac:(cbn; exact E184s) ltac:(cbn; exact E200s)
P15 EMO SAT OBS8 S8 SPOS SLO SSH SFA LC8 NTA8 CC8 FFi8 LFi8 OBI8 SH ESF SF0 SF1 F0 F64 FLO FTOP FSH ST8 ltac:(clear - NROOM; lia) LOS NTOP MI8 FRM).
destruct POST as (m9 & F9 & fc9 & wt2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & wt4 & wt5 & wt6 & is9
& FRM9 & MU9 & WM9 & MI9 & ST9 & FFi9 & LFi9 & DCB).
clear OBS8 LC8 NTA8 CC8 OBI8 FFi8 ST8 FRM ACI8.
assert (SH9 : rw_cells bsegs m9 SF (nbd_shadow (if sm_double_codebook (smr_sm r) =? 0 then SC_E else SC_E2) rest))
by (destruct DCB as [(E & _ & SHx)|(E & _ & SHx)]; rewrite E; exact SHx).
clear SH.
assert (ART9 : ART RT Σ8 m9).
{ apply (af_frame RT AF Σ8 m8 m9 lo ART8 LOWS); [| exact WM9]. intros a Ha; apply MU9; cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; clear - Hin; lia]|].
split; [intros Hin; apply Ha; right; right; right; right; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; rewrite SHD1, SHD2; clear - Hin; lia]|].
split; [intros Hin; apply Ha; left; unfold USTACK_TOP; clear - Hin LOU NROOM NTOP; lia| exact I]. }
cps_pf_seg m8 m9 MU9.
clear ART8. nbe_seg_tr m8 m9 MU9 WM9. try match goal with MI : mem_inv bsegs m8 |- _ => clear MI end.
clear Hc.
destruct DCB as [(DCB0 & -> & _) | (DCB1 & -> & _)].
-
rewrite DCB0 in SH9. cbn [Z.eqb] in SH9.
apply Hk. exists bp'.
pose proof (nbG_acc_pres2 Σ8 m9 m m9 (usp + -576) _ fh kh A 48 ART9 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA9.
assert (OFFO : forall i, 0 <= i < 4 * Z.of_nat nout -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -576, usp)] (shad (OUT + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 Σ8 m9 m m9 (usp + -576) _ fh kh OUT (4 * Z.of_nat nout) ART9 INFH FHO1 FHO2 PF OFFO (proj1 NACC)) as ACO9.
assert (OFFT : forall i, 0 <= i < 8 -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -576, usp)] (shad (STEREO + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 Σ8 m9 m m9 (usp + -576) _ fh kh STEREO 8 ART9 INFH FHS1 FHS2 PF OFFT (proj2 (proj2 NACC))) as ACT9.
assert (WM9E : wmono bsegs mE m9) by (apply (wmono_trans bsegs mE m m9); [exact WME| cps_wmono]).
assert (PF9E : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE m9).
{ apply (pres_fp_trans _ _ _ _ mE m m9); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_Jc.
exists Σ8, F9, fc9, m9, (Z_to_bv 64 RA_nbe_smul1), wt2, wa0, wa1, wa2, wa3, wa4, wa5, wa6, wa7,
(Z_to_bv 64 (Z.shiftr (1016736 + mo * 8) 3 + SHB)), (Z_to_bv 64 (1016736 + mo * 8)), wt3, wt4, wt5, wt6,
(NBJ (j_last_ol_gain j) eb4 (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed8 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)),
ows, sws, s, (NBF (Z_to_bv 64 (ltp_pitch k (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) b)) pg4 (f_lpc ff) (f_qlsp ff) (f_ak ff) is9 e325 (f_innov2 ff) (f_iq ff)), bp.
split; [eassumption|]. split; [exact FRM9|].
split.
{ unfold nbctx. split; [exact MI9|]. split; [exact ST9|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split.
{ unfold nb_hdr_cells. rewrite NCL.
change [C8 (Z_to_bv 64 A_speex_nb_mode); C4 (Z_to_bv 64 (nb_first st)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 (j_last_ol_gain j); C8 (Z_to_bv 64 0)]
with ([C8 (Z_to_bv 64 A_speex_nb_mode)] ++ [C4 (Z_to_bv 64 (nb_first st))] ++ [C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 (j_last_ol_gain j); C8 (Z_to_bv 64 0)]).
apply rw_cells_app. split; [exact P1a|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 8) by (cbn; lia) end.
apply rw_cells_app. split; [exact P1b|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 12) by (cbn; lia) end.
apply rw_cells_app. split; [exact P1c|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 16) by (cbn; lia) end. exact P1. }
split; [exact EB4|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact SEED8|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split.
{ unfold nb_junk_ok. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [clear - LEB4 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact JL12| exact JL13]. }
split; [exact CBOK|]. split; [exact NINV|].
split; [unfold nbE_bJ; rewrite DCB0; cbn [negb Z.eqb];
exact (conj (ex_intro _ rj8 (conj Lrj8 BOBJ8)) (conj (ex_intro _ bs8 (conj (proj2 (u8arr_rw_CB m9 D bs8) BDAT8) Hbs8)) BSIDE8))|].
split; [unfold nbE_bJ; rewrite DCB0; cbn [negb Z.eqb]; exact BOK8|].
split; [unfold nbE_bJ; rewrite DCB0; cbn [negb Z.eqb]; rewrite BSZi, BSZh, nbE_ltp_bits_size; exact BSZ|].
split; [exact OW|]. split; [exact LOW|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SL5 SV)|].
split; [exact (conj FF0 (conj PV4 (conj PG4 (conj FFl (conj FFq (conj FFk (conj FFi9 (conj E325 (conj FFj FFiq)))))))))|].
split; [exact (conj LPG4 (conj FL2 (conj FL3 (conj FL4 (conj LFi9 (conj LE325 (conj FL7 FL8)))))))|].
split; [exists rest; exact SH9|].
split; [exact (af_client_consts RT AF Σ8 m9 ART9)|]. split; [exact (AF_LIB Σ8 m9 ART9)|]. split; [reflexivity| exact JISV]. }
split; [exact SLE|]. split; [exact SAT|]. split; [exact EMO|]. split; [destruct BPE as [-> | ->]; [exact BP| exact PP]|].
split; [exact OLP|]. split; [exact SUB|].
split; [exact (conj ART9 (conj (conj ACO9 (conj ACA9 ACT9)) (conj WM9E PF9E)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
-
rewrite DCB1 in SH9. cbn [Z.eqb] in SH9.
pose proof (nbsh_acc_E2 m9 FF SF rest SH9 ESF F64 ltac:(lia)) as (_ & ACJ9).
pose proof (proj2 FFj) as WRJ. rewrite cells_size_f32, FL7 in WRJ. change (Z.of_nat (4 * 40)) with 160 in WRJ.
assert (CD3 : checked_dst RT Σ8 m9 (Z_to_bv 64 (usp + -576)) (FF + 768) 160)
by (apply (nbE_frame_checked_dst Σ8 m9 _ FF NBD_FCLASS); [exact INF| lia| fs_lit; lia| exact ACJ9| exact WRJ]).
cps_rt (MST Σ8 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 (FF + 768) 160 (Z_to_bv 8 0) lo).
{ clear - F0 FLO LOU NTOP. lia. }
{ cps_callok. }
intros c10 Hc10.
clear CD3 ACJ9 FFj.
nbe_unpack Hc10 as (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & BY10).
nbe_trp PRES10.
cps_pf_pres PRES10.
clear ART9 MI9 ST9 PRES10.
assert (FFj10 : rw_cells bsegs m10 (FF + 768) (f32 (repeat (Z_to_bv 64 0) 40))).
{ split; [split; [apply cells_wf_f32 | replace (cells_bytes (f32 (repeat (Z_to_bv 64 0) 40))) with (repeat (Z_to_bv 8 0) (Z.to_nat 160)) by (vm_compute; reflexivity); exact BY10]|].
rewrite cells_size_f32, repeat_length. exact (wr_at_transport bsegs m9 m10 _ _ WRJ WM10). }
clear BY10 WRJ.
pose proof (AF_LIB Σ8 m10 ART10) as LC10. pose proof (nbE_tabs_acc_art Σ8 m10 ART10) as NTA10.
cps_seg (@nbe_f bptr usp lo ST OUT A FF SF (nb_isave_ptr OUT st) sub mo r ki (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s))) _ _ m10
SL5 ltac:(cbn; exact E304s) ltac:(cbn; exact E288s) ltac:(cbn; exact E184s) ltac:(cbn; exact E216s) SAT INK LC10 NTA10 ST10 ltac:(clear - NROOM; lia) LOS SPH MI10).
destruct POST as (ut0 & ut2 & ua7 & ->). clear LC10 NTA10.

pose proof (AF_LIB Σ8 m10 ART10) as LC10.
pose proof (nbE_innov_row mo r ki m10 SAT INK LC10) as IPAR2. clear LC10.
destruct (nbE_innov_bits_ok mo r ki _ SAT INK BOKh) as (BOKi & _).
pose proof (nbsh_acc_E2 m10 FF SF rest SH9 ESF F64 ltac:(lia)) as (_ & ACJ10).
pose proof (nbG_acc_pres2 Σ8 m10 m m10 (usp + -576) _ fh kh A 48 ART10 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA10.
assert (BREP10 : bits_rep bsegs m10 A D (innov_bits ki (hsg_bits (smr_sm r) (ltp_bits k b))))
by exact (conj (ex_intro _ rj8 (conj Lrj8 BOBJ8)) (conj (ex_intro _ bs8 (conj (proj2 (u8arr_rw_CB m10 D bs8) BDAT8) Hbs8)) BSIDE8)).
cps_rt (INN ki INK Σ8 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 A D (innov_bits ki (hsg_bits (smr_sm r) (ltp_bits k b)))
(FF + 768) (ST + 2228) (smr_innov_par r) lo ST 2968 PD ND fh kh (repeat (Z_to_bv 64 0) 40) seed8 (Z_to_bv 64 0)).
{ left. exists FF, NBD_FCLASS. split; [exact INF|]. unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACJ10| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold in_frame_obj, BITS_SIZEOF. split; [exact FHA1|]. split; [exact FHA2|]. split; [exact ACA10| clear - A8; Z.div_mod_to_equations; lia]. }
{ rewrite BSZi, BSZh, nbE_ltp_bits_size, BSZ, <- DSZ. exact PD2. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact ST10. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold RT_STACK, INNOV_STACK. clear - NROOM. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold USTACK_TOP. clear - NTOP. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). clear - U32. Z.div_mod_to_equations. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact POA. }
intros c12 (Σ11 & Hc11 & LV11 & FRS11 & SP11 & CR11 & PO11).
cps_unpack_lib Hc11 as (v11 & m11 & is11 & seed11 & RS11 & (ART11 & MI11 & WM11 & ST11) & PRES11 & FFj11 & LFj11 & SEED11 & BREP11 & BOK11 & ACJ11 & ACA11).
clear FFj10 SEED8 BREP10 ACJ10 ACA10 BOBJ8 BDAT8.
nbe_trp PRES11.
nbe_pf_fp PRES11.
clear ART10 MI10 ST10 PRES11. try clear Hc0.
rewrite <- LV11 in INL, INPD, LV, PF, SPL. rewrite <- FRS11 in INF, INFH, FRS, PF, SPL. rewrite <- SP11 in LOWS, SP0, SPL. rewrite <- CR11 in CR. rewrite <- PO11 in POA, POI.
clear LV11 FRS11 SP11 CR11 PO11.
clear FRM9. rename RS11 into FRM.
destruct (nbE_innov_bits_ok mo r ki _ SAT INK BOKi) as (_ & BSZi2).
destruct BREP11 as ((rj11 & Lrj11 & BOBJ11) & (bs11 & BDAT11 & Hbs11) & BSIDE11). unfold bits_cells in BOBJ11. apply (proj1 (u8arr_rw_CB m11 D bs11)) in BDAT11.
assert (LBS11 : Z.of_nat (length bs11) = sb_buf_size b)
by (pose proof BOK11 as BOK'; unfold bits_ok in BOK'; rewrite Hbs11, zlength_map_unsigned, BSZi2, BSZi, BSZh, nbE_ltp_bits_size in BOK'; clear - BOK'; lia).
assert (DSZb11 : Z.of_nat (length bs11) = x_dsz X) by (rewrite LBS11, BSZ, <- DSZ; reflexivity).
assert (DLOb11 : D + Z.of_nat (length bs11) <= lo) by (rewrite DSZb11; exact DLO).
assert (DPD11 : D + Z.of_nat (length bs11) <= PD + ND) by (rewrite DSZb11; exact PD2).
clear LBS8 DSZb8 DLOb8 DPD8 Hbs8 BSIDE8 Lrj8.

pose proof (af_client_consts RT AF Σ11 m11 ART11) as CC11.
assert (OBJ11 : aobj bsegs m11 (FF + 768) 160) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACJ11]).
cps_seg (nbe_g usp lo ST FF SF (nb_isave_ptr OUT st) sub mo rest is9 is11 (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 296 (Z_to_bv 64 bp') (slots_Eb ST (slots_Ea (ST + 1368) sub s))) _ _ m11
SL5 ltac:(cbn; exact E80s) ltac:(cbn; exact E200s) ltac:(cbn; exact E312s) FFi9 LFi9 FFj11 LFj11 OBJ11 SH9 ESF SF0 SF1 F0 F64 FLO FTOP FSH CC11 ST11 ltac:(clear - NROOM; lia) LOS SPH MI11 FRM).
destruct POST as (m12 & F12 & fc12 & xra12 & vt2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & vt3 & vt4 & vt5 & vt6 & is12 & i212
& -> & FRM12 & MU12 & WM12 & MI12 & ST12 & FFi12 & LFi12 & FFj12 & LFj12 & SH12).
clear CC11 OBJ11 FFi9 FFj11 SH9 ST11 FRM ACJ11 ACA11.
assert (ART12 : ART RT Σ11 m12).
{ apply (af_frame RT AF Σ11 m11 m12 lo ART11 LOWS); [| exact WM12]. intros a Ha; apply MU12; cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; clear - Hin; lia]|].
split; [intros Hin; apply Ha; right; right; right; left; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; clear - Hin; lia]|].
split; [intros Hin; apply Ha; right; right; right; right; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; rewrite SHD1, SHD2; clear - Hin; lia]|].
split; [intros Hin; apply Ha; left; unfold USTACK_TOP; clear - Hin LOU NROOM NTOP; lia| exact I]. }
cps_pf_seg m11 m12 MU12.
clear ART11. nbe_seg_tr m11 m12 MU12 WM12. try match goal with MI : mem_inv bsegs m11 |- _ => clear MI end.
clear Hc1.
apply Hk. exists bp'.
pose proof (nbG_acc_pres2 Σ11 m12 m m12 (usp + -576) _ fh kh A 48 ART12 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA12.
assert (OFFO : forall i, 0 <= i < 4 * Z.of_nat nout -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -576, usp)] (shad (OUT + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 Σ11 m12 m m12 (usp + -576) _ fh kh OUT (4 * Z.of_nat nout) ART12 INFH FHO1 FHO2 PF OFFO (proj1 NACC)) as ACO12.
assert (OFFT : forall i, 0 <= i < 8 -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -576, usp)] (shad (STEREO + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 Σ11 m12 m m12 (usp + -576) _ fh kh STEREO 8 ART12 INFH FHS1 FHS2 PF OFFT (proj2 (proj2 NACC))) as ACT12.
assert (WM12E : wmono bsegs mE m12) by (apply (wmono_trans bsegs mE m m12); [exact WME| cps_wmono]).
assert (PF12E : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 576) (nbW_EH X) mE m12).
{ apply (pres_fp_trans _ _ _ _ mE m m12); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_Jc.
exists Σ11, F12, fc12, m12, xra12, vt2, va0, va1, va2, va3, va4, va5, va6, va7, (Z_to_bv 64 (FF + 928)), (Z_to_bv 64 (1016736 + mo * 8)), vt3, vt4, vt5, vt6,
(NBJ (j_last_ol_gain j) eb4 (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed11 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)),
ows, sws, s, (NBF (Z_to_bv 64 (ltp_pitch k (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) b)) pg4 (f_lpc ff) (f_qlsp ff) (f_ak ff) is12 e325 i212 (f_iq ff)), bp.
split; [eassumption|]. split; [exact FRM12|].
split.
{ unfold nbctx. split; [exact MI12|]. split; [exact ST12|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split.
{ unfold nb_hdr_cells. rewrite NCL.
change [C8 (Z_to_bv 64 A_speex_nb_mode); C4 (Z_to_bv 64 (nb_first st)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 (j_last_ol_gain j); C8 (Z_to_bv 64 0)]
with ([C8 (Z_to_bv 64 A_speex_nb_mode)] ++ [C4 (Z_to_bv 64 (nb_first st))] ++ [C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 (j_last_ol_gain j); C8 (Z_to_bv 64 0)]).
apply rw_cells_app. split; [exact P1a|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 8) by (cbn; lia) end.
apply rw_cells_app. split; [exact P1b|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 12) by (cbn; lia) end.
apply rw_cells_app. split; [exact P1c|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 16) by (cbn; lia) end. exact P1. }
split; [exact EB4|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact SEED11|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split.
{ unfold nb_junk_ok. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [clear - LEB4 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact JL12| exact JL13]. }
split; [exact CBOK|]. split; [exact NINV|].
split; [unfold nbE_bJ; rewrite DCB1; cbn [negb Z.eqb];
exact (conj (ex_intro _ rj11 (conj Lrj11 BOBJ11)) (conj (ex_intro _ bs11 (conj (proj2 (u8arr_rw_CB m12 D bs11) BDAT11) Hbs11)) BSIDE11))|].
split; [unfold nbE_bJ; rewrite DCB1; cbn [negb Z.eqb]; exact BOK11|].
split; [unfold nbE_bJ; rewrite DCB1; cbn [negb Z.eqb]; rewrite BSZi2, BSZi, BSZh, nbE_ltp_bits_size; exact BSZ|].
split; [exact OW|]. split; [exact LOW|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SL5 SV)|].
split; [exact (conj FF0 (conj PV4 (conj PG4 (conj FFl (conj FFq (conj FFk (conj FFi12 (conj E325 (conj FFj12 FFiq)))))))))|].
split; [exact (conj LPG4 (conj FL2 (conj FL3 (conj FL4 (conj LFi12 (conj LE325 (conj LFj12 FL8)))))))|].
split; [exists rest; exact SH12|].
split; [exact (af_client_consts RT AF Σ11 m12 ART12)|]. split; [exact (AF_LIB Σ11 m12 ART12)|]. split; [reflexivity| exact JISV]. }
split; [exact SLE|]. split; [exact SAT|]. split; [exact EMO|]. split; [destruct BPE as [-> | ->]; [exact BP| exact PP]|].
split; [exact OLP|]. split; [exact SUB|].
split; [exact (conj ART12 (conj (conj ACO12 (conj ACA12 ACT12)) (conj WM12E PF12E)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
Unshelve. all: exact bptr.
Qed.

End NbE.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NbE.
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

Definition nbE_keep (P : Prop) : Prop := P.

Lemma nbE_tabs_acc_art : forall (Σ : rts RT) (m : mem), ART RT Σ m -> nb_tabs_acc m.
Proof using AF.
intros Σ m A0.
assert (K : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj asegs m a n) by (intros a n; exact (aobj_lit RT AF Σ m a n A0)).
split.
- apply K; [unfold ACC_LITS, A_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_nb_mode; lia | unfold A_nb_mode, APP_TOP; lia].
- unfold nb_smrecs, nb_smrec1, nb_smrec2, nb_smrec3, nb_smrec4, nb_smrec5, nb_smrec6, nb_smrec7, nb_smrec8.
repeat (apply Forall_cons; [cbv beta; cbn [smr_ptr];
unfold A_nb_submode1, A_nb_submode2, A_nb_submode3, A_nb_submode4, A_nb_submode5, A_nb_submode6, A_nb_submode7, A_nb_submode8;
apply K; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia | unfold APP_TOP; lia]|]). apply Forall_nil.
Qed.

Lemma nbE_sz_shadow : forall sc rest, cells_size (nbd_shadow sc rest) = 256%nat.
Proof. intros [[] [] [] [] []] rest; reflexivity. Qed.
Lemma nbE_sz_slots : forall s, cells_size (slot_cells s) = 344%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_saves : cells_size (@fr_saves bptr X) = 200%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_hdr : forall z (st : nb_state bptr) w, cells_size (nb_hdr_cells z st w) = 32%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_cfg : forall z (st : nb_state bptr) pad, cells_size (nb_cfg_cells z st pad) = 24%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_tail : forall (st : nb_state bptr) pad, cells_size (nb_tail_cells st pad) = 20%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_ucb : forall z ju, cells_size (nb_ucb_cells z ju) = 40%nat. Proof. reflexivity. Qed.
Lemma nbE_sz_ltpargs : forall a w o, cells_size (ltp_args_cells a w o) = 40%nat. Proof. reflexivity. Qed.
Local Ltac simpl_sizes ::=
rewrite ?nbE_sz_shadow, ?nbE_sz_slots, ?nbE_sz_saves, ?nbE_sz_hdr, ?nbE_sz_cfg, ?nbE_sz_tail, ?nbE_sz_ucb, ?nbE_sz_ltpargs;
rewrite ?length_app, ?cells_size_app, ?cells_size_f32, ?length_f32, ?repeat_length;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app, ?cells_size_f32, ?length_f32, ?repeat_length; cbn [length].

Lemma nbE_live_checked_dst : forall (Σ : rts RT) (m : mem) sp p k d n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= d -> d + n <= p + k -> wr_at asegs m d n -> checked_dst RT Σ m sp d n.
Proof using AF.
intros Σ m sp p k d n ART0 INL H1 H2 WR. split; [intros _; split| split; [| exact WR]].
- apply (acc_sub asegs m p k d n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
- intros i Hi. right; right; left. exists p, k. split; [exact INL| lia].
Qed.

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

Definition R_J (xra s3 s11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) (x_gp X) (x_tp X) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) s3 (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) s11 t3 t4 t5 t6.

Definition slots_J (bp' sub : Z) (st : nb_state bptr) (s : nbslots) : nbslots :=
sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s)).

Definition at_Jc (bp' sub : Z) (st : nb_state bptr) (bJ : bits_st bptr) : config -> Prop :=
fun c => exists (Σ : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra s3 s11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff) (bp : Z),
ASTA RT Σ PMc (eq (MS (R_J xra s3 s11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) Fx (Z_to_bv 64 NBE_PC_J) fc None m (seg_rom asegs))) c
/\ frm0 fc /\ nbctx X m st bJ j ows sws (slots_J bp' sub st s) ff SC_E /\ slots_EL ST OUT A FF bp sub s
/\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp' <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4
/\ nbEH_mem RT X Σ0 mE Σ m /\ nbEH_sig RT Σ0 Σ (rt_credit RT Σ0).

Definition nbE_bJ (k : ltp_kind) (ki : innov_kind) (b : bits_st bptr) : bits_st bptr :=
let b3 := innov_bits ki (hsg_bits (smr_sm r) (ltp_bits k b)) in
if negb (sm_double_codebook (smr_sm r) =? 0) then innov_bits ki b3 else b3.

Lemma nbE_mo_cases : forall mo0 (r0 : smrec), smrec_at mo0 = Some r0 ->
(mo0 = 1 /\ r0 = nb_smrec1) \/ (mo0 = 2 /\ r0 = nb_smrec2) \/ (mo0 = 3 /\ r0 = nb_smrec3) \/ (mo0 = 4 /\ r0 = nb_smrec4)
\/ (mo0 = 5 /\ r0 = nb_smrec5) \/ (mo0 = 6 /\ r0 = nb_smrec6) \/ (mo0 = 7 /\ r0 = nb_smrec7) \/ (mo0 = 8 /\ r0 = nb_smrec8).
Proof.
intros mo0 r0 H. pose proof (smrec_facts mo0 r0 H) as (_ & MO & _).
assert (C : mo0 = 1 \/ mo0 = 2 \/ mo0 = 3 \/ mo0 = 4 \/ mo0 = 5 \/ mo0 = 6 \/ mo0 = 7 \/ mo0 = 8) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn in H; injection H as <-; tauto.
Qed.
Lemma nbE_ltp_row : forall mo0 (r0 : smrec) k (m : mem) olp0, smrec_at mo0 = Some r0 -> sm_ltp_unquant (smr_sm r0) = Some k -> lib_consts m ->
(sm_lbr_pitch (smr_sm r0) = -1 /\ olp0 = 0 \/ sm_lbr_pitch (smr_sm r0) <> -1 /\ 17 <= olp0 <= 144) ->
17 <= nbe_pmin (sm_lbr_pitch (smr_sm r0)) olp0 /\ nbe_pmin (sm_lbr_pitch (smr_sm r0)) olp0 + ltp_pitch_span k <= 144
/\ nbe_pmin (sm_lbr_pitch (smr_sm r0)) olp0 <= nbe_pmax (sm_lbr_pitch (smr_sm r0)) olp0 <= 144
/\ match k with LtpPitchUnquant3tap p => ro_cells asegs m (smr_ltp_par r0) (ltp_par_cellsA (gain_cdbk_addrA (ltp_gain_cdbk p)) (ltp_gain_bits p) (ltp_pitch_bits p))
/\ smr_ltp_par r0 mod 8 = 0 /\ 0x10000 <= smr_ltp_par r0 /\ smr_ltp_par r0 + 16 <= IMG_TOP /\ In (smr_ltp_par r0, 16) ACC_LITS
| LtpForcedPitchUnquant => True end.
Proof.
intros mo0 r0 k m olp0 SAT LTK LC HOLP. destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in LTK; injection LTK as <-; cbn in HOLP |- *;
(destruct HOLP as [(HL & HO)|(HL & HO)]; [try discriminate HL | try (exfalso; apply HL; reflexivity)]);
repeat split; try lia;
first [ apply (lib_const m); [exact LC | lc_in]
| unfold A_ltp_params_vlbr, A_ltp_params_lbr, A_ltp_params_med, A_ltp_params_nb, IMG_TOP; lia
| repeat (first [left; reflexivity | right]) ].
Qed.

Lemma nbE_shadow_acc_u : forall (m : mem) (f sf : Z) (cs : list cell) (pre rest : list byte) (n : Z),
rw_cells asegs m sf cs -> cells_bytes cs = pre ++ ushadow n ++ rest -> sf = Z.shiftr f 3 + SHB -> f mod 64 = 0 -> 0 <= f -> 0 <= n ->
acc asegs m (f + 8 * Z.of_nat (length pre)) n.
Proof.
intros m f sf cs pre rest n [[_ B] _] E Esf F64 F0 N0. rewrite E in B.
apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [B _].
apply (acc_ushadow asegs); [clear - F64; Z.div_mod_to_equations; lia | lia | lia |].
replace (shad (f + 8 * Z.of_nat (length pre))) with (sf + Z.of_nat (length pre)); [exact B|].
rewrite Esf, shad_shiftr. unfold shad. clear - F64. Z.div_mod_to_equations. lia.
Qed.

Lemma nbsh_acc_E : forall (m : mem) (F0 S0 : Z) rest, rw_cells asegs m S0 (nbd_shadow SC_E rest) -> S0 = Z.shiftr F0 3 + SHB -> F0 mod 64 = 0 -> 0 <= F0 ->
acc asegs m (F0 + 32) 4 /\ acc asegs m (F0 + 48) 12 /\ acc asegs m (F0 + 320) 160 /\ acc asegs m (F0 + 544) 160.
Proof.
intros m F0 S0 rest SH ESF F64 FPOS. split; [| split; [| split]].
- pose proof (nbE_shadow_acc_u m F0 S0 _ (firstn 4 (nbd_shadow_bytes SC_E)) (skipn 5 (nbd_shadow_bytes SC_E) ++ rest ++ []) 4 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS| lia].
- pose proof (nbE_shadow_acc_u m F0 S0 _ (firstn 6 (nbd_shadow_bytes SC_E)) (skipn 8 (nbd_shadow_bytes SC_E) ++ rest ++ []) 12 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS| lia].
- pose proof (shadow_acc m F0 S0 _ (firstn 40 (nbd_shadow_bytes SC_E)) (skipn 60 (nbd_shadow_bytes SC_E) ++ rest ++ []) 20 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
- pose proof (shadow_acc m F0 S0 _ (firstn 68 (nbd_shadow_bytes SC_E)) (skipn 88 (nbd_shadow_bytes SC_E) ++ rest ++ []) 20 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
Qed.
Lemma nbsh_acc_E2 : forall (m : mem) (F0 S0 : Z) rest, rw_cells asegs m S0 (nbd_shadow SC_E2 rest) -> S0 = Z.shiftr F0 3 + SHB -> F0 mod 64 = 0 -> 0 <= F0 ->
acc asegs m (F0 + 320) 160 /\ acc asegs m (F0 + 768) 160.
Proof.
intros m F0 S0 rest SH ESF F64 FPOS. split.
- pose proof (shadow_acc m F0 S0 _ (firstn 40 (nbd_shadow_bytes SC_E2)) (skipn 60 (nbd_shadow_bytes SC_E2) ++ rest ++ []) 20 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
- pose proof (shadow_acc m F0 S0 _ (firstn 96 (nbd_shadow_bytes SC_E2)) (skipn 116 (nbd_shadow_bytes SC_E2) ++ rest ++ []) 20 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
Qed.

Lemma nbE_live_apart : forall (Σ : rts RT) (m : mem) p1 n1 p2 n2, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> p1 <> p2 ->
p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
intros Σ m p1 n1 p2 n2 ART0 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 ART0 E). rewrite E in H2. apply in_app_iff in H2. apply in_app_iff.
destruct H2 as [H2|[H2|H2]]; [left; exact H2| exfalso; apply NE; congruence| right; exact H2].
Qed.

Lemma nbE_frame_checked_dst : forall (Σ : rts RT) (m : mem) sp f k d n,
In (f, k) (rt_frames RT Σ) -> f <= d -> d + n <= f + fs_size k - 8 -> acc asegs m d n -> wr_at asegs m d n -> checked_dst RT Σ m sp d n.
Proof.
intros Σ m sp f k d n INF H1 H2 ACC WR. split; [intros _; split| split; [| exact WR]].
- exact ACC.
- right; left. exists f, k. split; [exact INF| lia].
- intros i Hi. right; right; right; left. exists f, k. split; [exact INF| lia].
Qed.

Lemma nbE_ltp_bits_size : forall k (b : bits_st bptr), sb_buf_size (ltp_bits k b) = sb_buf_size b.
Proof. intros [|p] b; cbn [ltp_bits]; [reflexivity|]. unfold ltp3_bits. rewrite !ub_size. reflexivity. Qed.
Lemma nbE_ltp_pitch : forall mo0 (r0 : smrec) k (b : bits_st bptr) start, smrec_at mo0 = Some r0 -> sm_ltp_unquant (smr_sm r0) = Some k -> bits_ok b ->
start <= ltp_pitch k start b <= start + ltp_pitch_span k.
Proof.
intros mo0 r0 k b start SAT LTK OK. destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in LTK; injection LTK as <-; cbn [ltp_pitch ltp_pitch_span]; try lia;
unfold ltp3_pitch; cbn [ltp_pitch_bits ltp_params_vlbr ltp_params_lbr ltp_params_med ltp_params_nb];
match goal with |- context [uv b ?n] => pose proof (ub_ok b n OK ltac:(lia)) as (_ & _ & U) end; lia.
Qed.

Lemma nbE_innov_row : forall mo0 (r0 : smrec) ki (m : mem), smrec_at mo0 = Some r0 -> sm_innovation_unquant (smr_sm r0) = Some ki -> lib_consts m ->
match ki with InnovSplitCbShapeSignUnquant p => ro_cells asegs m (smr_innov_par r0) (scb_par_cellsA p) /\ smr_innov_par r0 mod 8 = 0 /\ 0x10000 <= smr_innov_par r0
/\ smr_innov_par r0 + 24 <= IMG_TOP /\ In (smr_innov_par r0, 24) ACC_LITS
| InnovNoiseCodebookUnquant => True end.
Proof.
intros mo0 r0 ki m SAT INK LC. destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in INK; injection INK as <-; cbn; repeat split;
first [ apply (lib_const m); [exact LC | lc_in]
| unfold A_split_cb_nb_vlbr, A_split_cb_nb_lbr, A_split_cb_nb_med, A_split_cb_nb, A_split_cb_sb, A_split_cb_nb_ulbr, IMG_TOP; lia
| repeat (first [left; reflexivity | right]) ].
Qed.
Lemma nbE_scb_bits_ok : forall n hs sbits (bb : bits_st bptr), bits_ok bb -> 0 <= sbits -> bits_ok (scb_bits n hs sbits bb) /\ sb_buf_size (scb_bits n hs sbits bb) = sb_buf_size bb.
Proof.
induction n as [|n IH]; intros hs sbits bb OKb Hs; cbn [scb_bits]; [split; [exact OKb| reflexivity]|].
destruct (negb (hs =? 0)).
- destruct (ub_ok bb 1 OKb ltac:(lia)) as (OK1 & SZ1 & _). destruct (ub_ok (ub bb 1) sbits OK1 Hs) as (OK3 & SZ3 & _).
destruct (IH hs sbits _ OK3 Hs) as (OK4 & SZ4). split; [exact OK4| rewrite SZ4, SZ3, SZ1; reflexivity].
- destruct (ub_ok bb sbits OKb Hs) as (OK3 & SZ3 & _). destruct (IH hs sbits _ OK3 Hs) as (OK4 & SZ4). split; [exact OK4| rewrite SZ4, SZ3; reflexivity].
Qed.
Lemma nbE_innov_bits_ok : forall mo0 (r0 : smrec) ki (b : bits_st bptr), smrec_at mo0 = Some r0 -> sm_innovation_unquant (smr_sm r0) = Some ki -> bits_ok b ->
bits_ok (innov_bits ki b) /\ sb_buf_size (innov_bits ki b) = sb_buf_size b.
Proof.
intros mo0 r0 ki b SAT INK OK. destruct ki as [|p]; cbn [innov_bits]; [split; [exact OK| reflexivity]|].
destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in INK; try discriminate INK; injection INK as <-; (apply nbE_scb_bits_ok; [exact OK| cbn; lia]).
Qed.
Lemma nbE_hsg_ok : forall sm (b : bits_st bptr), bits_ok b -> bits_ok (hsg_bits sm b) /\ sb_buf_size (hsg_bits sm b) = sb_buf_size b.
Proof.
intros sm b OK. unfold hsg_bits. destruct (sm_have_subframe_gain sm =? 3); [destruct (ub_ok b 3 OK ltac:(lia)) as (O & S & _); split; assumption|].
destruct (sm_have_subframe_gain sm =? 1); [destruct (ub_ok b 1 OK ltac:(lia)) as (O & S & _); split; assumption| split; [exact OK| reflexivity]].
Qed.
Lemma nbE_ltp_bits_ok : forall mo0 (r0 : smrec) k (b : bits_st bptr), smrec_at mo0 = Some r0 -> sm_ltp_unquant (smr_sm r0) = Some k -> bits_ok b -> bits_ok (ltp_bits k b).
Proof.
intros mo0 r0 k b SAT LTK OK. destruct k as [|p]; cbn [ltp_bits]; [exact OK|]. unfold ltp3_bits.
destruct (nbE_mo_cases mo0 r0 SAT) as [(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]]]]];
cbn in LTK; try discriminate LTK; injection LTK as <-; cbn [ltp_pitch_bits ltp_gain_bits ltp_params_vlbr ltp_params_lbr ltp_params_med ltp_params_nb];
match goal with |- bits_ok (ub (ub b ?n1) ?n2) => exact (proj1 (ub_ok (ub b n1) n2 (proj1 (ub_ok b n1 OK ltac:(lia))) ltac:(lia))) end.
Qed.

Lemma nbE_h2z : forall (usp lo ST FF SF olp sub EXW : Z) (inn : list word)
(gp tp xra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> v264 s = Z_to_bv 64 EXW -> v280 s = Z_to_bv 64 (FF + 320) -> 0 <= sub < 4 ->
rw_cells asegs m (FF + 320) (f32 inn) -> length inn = 40%nat ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> usp < 2^63 -> SH_HI <= lo ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (F' : bvmap 5 word) (a0' a1' a2' a3' a4' a5' : word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' a3' a4' a5' (Z_to_bv 64 EXW) a7
(Z_to_bv 64 SF) s3 (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F' (Z_to_bv 64 NBE_PC_H3) fc None m (seg_rom asegs))
(MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0
(Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) s3 (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa0c84) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E264 E280 SUB INNV LINN F0 F64 FLO FTOP FSH ST0 LO SPH LOS CC MI FRM.
unfold NBE_PC_H3 in *. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v264 v280] in E264, E280. subst w264 w280.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
ato 0xa0c88. astep.
apply evt_done. do 7 eexists. reflexivity.
Qed.

Lemma nbE_A : forall (bp sub : Z) (st : nb_state bptr) (b : bits_st bptr) (k : ltp_kind) (ki : innov_kind),
0 <= sub < 4 -> sm_ltp_unquant (smr_sm r) = Some k -> sm_innovation_unquant (smr_sm r) = Some ki ->
cps asegs (at_ELc RT PMc X Σ0 mE r mo olp bp sub st b) (fun c => exists bp', at_Jc bp' sub st (nbE_bJ k ki b) c).
Proof.
intros bp sub st b k ki SUB LTK INK T c Hc Hk.
destruct Hc as (Σ & Hc & SIG).
destruct (ASTA_unpack RT Σ PMc _ c Hc) as (ms & (ATEL & MEM) & Hc0); clear Hc.
destruct ATEL as (Fx & fc & m & xra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff
& -> & FRM & CTX & SLE & SAT & EMO & BP & OLP & SUB').
cbn [ms_mem] in MEM. destruct MEM as (ART0 & NACC & WM0 & PF).
destruct SIG as (LV & FRS & SP0 & CR & POI).
destruct CTX as (MI0 & STK0 & NBP & JOK & CBOK & NINV & BREP & BOK & BSZ & OW & LOW & SW & LSW & (SL & SV) & FFA & FFOK & (rest & SH) & CC & LC & JEXC & JISV).
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
assert (LBS : Z.of_nat (length bs) = sb_buf_size b)
by (pose proof BOK as BOK'; unfold bits_ok in BOK'; rewrite Hbs, zlength_map_unsigned in BOK'; clear - BOK'; lia).
assert (DLOb : D + Z.of_nat (length bs) <= lo) by (rewrite LBS, BSZ, <- DSZ; exact DLO).
assert (DPD : D + Z.of_nat (length bs) <= PD + ND) by (rewrite LBS, BSZ, <- DSZ; exact PD2).
assert (DSZb : Z.of_nat (length bs) = x_dsz X) by (rewrite LBS, BSZ, <- DSZ; reflexivity).

cps_norm. cps_hide.
cps_seg (nbe_a usp lo ST OUT A FF SF olp bp sub (nb_isave_ptr OUT st) (x_gp X) (x_tp X) xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 s Fx fc m
SL SLE P3 P9 OBS S8 SPOS SLO SSH ISB SUB STK0 ltac:(clear - LOU; lia) LOS SPH MI0).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & SL1). clear SL.
clear STK0 OBS ACS WRS.
assert (ART1 : ART RT Σ m1).
{ apply (af_frame RT AF Σ m m1 lo ART0 LOWS); [| exact WM1]. intros a Ha; apply MU1; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m m1 MU1.
clear ART0. nbe_seg_tr m m1 MU1 WM1. try match goal with MI : mem_inv asegs m |- _ => clear MI end.

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
assert (CD1 : checked_dst RT Σ m1 (Z_to_bv 64 (usp + -544)) (ST + 1368 + 160 * sub) 160).
{ split; [intros _; split| split; [| exact WRX]].
- exact (acc_sub asegs m1 ST 2968 (ST + 1368 + 160 * sub) 160 ACS1 ltac:(clear - SUB; lia) ltac:(clear - SUB; lia)).
- left. exists ST, 2968. split; [exact INL| clear - SUB; lia].
- intros i Hi. right; right; left. exists ST, 2968. split; [exact INL| clear - SUB Hi; lia]. }
cps_rt (MST Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (ST + 1368 + 160 * sub) 160 (Z_to_bv 8 0) lo).
{ clear - SPOS SLO LOU NTOP SUB. lia. }
{ cps_callok. }
intros c2 Hc2.
clear CD1 ACS1.
nbe_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
Time nbe_trp PRES2.
Time cps_pf_pres PRES2.
clear ART1 MI1 ST1.

assert (EXZ : rw_cells asegs m2 (ST + 1368 + 160 * sub) (f32 (repeat (Z_to_bv 64 0) 40))).
{ split; [split; [apply cells_wf_f32 | replace (cells_bytes (f32 (repeat (Z_to_bv 64 0) 40))) with (repeat (Z_to_bv 8 0) (Z.to_nat 160)) by (vm_compute; reflexivity); exact BY2]|].
rewrite cells_size_f32, repeat_length. exact (wr_at_transport asegs m1 m2 _ _ WRX WM2). }
clear BY2 WRX.

unfold nb_hdr_cells in P1. chunk_uncons P1 as P1a. chunk_uncons P1 as P1b. chunk_uncons P1 as P1c.
replace (ST + 8 + 4) with (ST + 12) in P1c by lia. replace (ST + 8 + 4 + 4) with (ST + 16) in P1 by lia.
pose proof NINV as (NCL & _). rewrite NCL in P1c.
destruct (af_acc_live RT AF Σ m2 ST 2968 ART2 INL) as (_ & ACS2).
assert (OBS2 : aobj asegs m2 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS2]). clear ACS2.
pose proof (AF_LIB Σ m2 ART2) as LC2. pose proof (nbE_tabs_acc_art Σ m2 ART2) as NTA2. pose proof (af_client_consts RT AF Σ m2 ART2) as CC2.
cps_seg (nbe_b usp lo ST OUT A FF SF olp bp sub (nb_isave_ptr OUT st) mo r k st (j_pad1 j) (j_last_pitch_gain j) (j_last_pitch j)
(x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s Fx fc m2
SL1 SLE P15 EMO SAT LTK P1c P11 OBS2 S8 SPOS SLO SSH LC2 NTA2 CC2 OLP SUB ST2 ltac:(clear - NROOM; lia) LOS SPH U32 MI2).
destruct POST as (m3 & F3 & xt0 & xt2 & jk & -> & MU3 & WM3 & MI3 & ST3 & SL3 & SA3). clear SL1 ST2 OBS2 LC2 NTA2 CC2.
assert (ART3 : ART RT Σ m3).
{ apply (af_frame RT AF Σ m2 m3 lo ART2 LOWS); [| exact WM3]. intros a Ha; apply MU3; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m2 m3 MU3.
clear ART2. nbe_seg_tr m2 m3 MU3 WM3. try match goal with MI : mem_inv asegs m2 |- _ => clear MI end.

pose proof (AF_LIB Σ m3 ART3) as LC3.
destruct (nbE_ltp_row mo r k m3 olp SAT LTK LC3 OLP) as (LS1 & LS2 & LS3 & LPAR). clear LC3.
pose proof (nbsh_acc_E m3 FF SF rest SH ESF F64 ltac:(lia)) as (ACP3 & ACG3 & ACI3 & ACE3).
assert (OFFA : forall i, 0 <= i < 48 -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -544, usp)] (shad (A + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) A 48 i (eq_sym ESF8) F64 ltac:(clear - ATOP; lia) ltac:(clear - ALO LOU NTOP; lia)
AFFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 RT AF Σ m3 m m3 (usp + -544) _ fh kh A 48 ART3 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA3.
pose proof (nbE_live_apart Σ m3 PD ND ST 2968 ART3 INPD INL PDS) as PDST.
assert (BREP3 : bits_rep asegs m3 A D b)
by exact (conj (ex_intro _ rj (conj Lrj BOBJ)) (conj (ex_intro _ bs (conj (proj2 (u8arr_rw_CB m3 D bs) BDAT) Hbs)) BSIDE)).
apply rw_cells_app in SA3. destruct SA3 as (SA3a & SA3b). rewrite nbE_sz_ltpargs in SA3b. change (Z.of_nat 40) with 40 in SA3b.
assert (EXB3 : rw_cells asegs m3 (ST + 32) (f32 (ex1 ++ repeat (Z_to_bv 64 0) 40 ++ ex3))).
{ apply nbe_f32_join_win; [exact EX1| rewrite LEX1; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by (clear; lia); exact EXZ|].
rewrite LEX1, repeat_length. replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 160) by (clear; lia). exact EX3. }
clear EX1 EXZ EX3.
cps_rt (LTP k LTK Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc m3 A D b (ST + 32) (334 + 40 * sub) (FF + 544) (FF + 32) (FF + 48)
(nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) (nbe_pmax (sm_lbr_pitch (smr_sm r)) olp) (smr_ltp_par r) (40 * sub) lo ST 2968 PD ND FF fh NBD_FCLASS kh
(ex1 ++ repeat (Z_to_bv 64 0) 40 ++ ex3) (f_exc32 ff) (f_pg ff) (f_pitch ff) (Z_to_bv 64 0)).
{ f_equal. clear. lia. }
{ rewrite !length_app, repeat_length. clear - LEX1 LEX3 SUB. lia. }
{ rewrite !length_app, repeat_length. clear - LEX1 LEX3 SUB. lia. }
{ unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACE3| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACP3| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACG3| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold hidp. right. lia. }
{ unfold hidp. right. lia. }
{ unfold hidp. left. lia. }
{ unfold in_frame_obj, BITS_SIZEOF. split; [exact FHA1|]. split; [exact FHA2|]. split; [exact ACA3| clear - A8; Z.div_mod_to_equations; lia]. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact SA3a. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact ST3. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold RT_STACK, LTP_STACK. clear - NROOM. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold USTACK_TOP. clear - NTOP. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). clear - U32. Z.div_mod_to_equations. lia. }
intros c4 (Σ4 & Hc4 & LV4 & FRS4 & SP4 & CR4 & PO4).
cps_unpack_lib Hc4 as (v4 & m4 & eb4 & e324 & pg4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & EB4 & LEB4 & E324 & LE324 & PV4 & PG4 & LPG4 & BREP4 & BOK4 & SA4 & ACE4 & ACP4 & ACG4 & ACA4).
clear EXB3 FFe FFp FFg BOBJ BDAT SA3a ACE3 ACP3 ACG3 ACA3 ACI3 BREP3.
nbe_trp PRES4.
nbe_pf_fp PRES4.
clear ART3 MI3 ST3 PRES4. try clear Hc. try clear Hc1.

rewrite <- LV4 in INL, INPD, LV, PF, SPL. rewrite <- FRS4 in INF, INFH, FRS, PF, SPL. rewrite <- SP4 in LOWS, SP0, SPL. rewrite <- CR4 in CR. rewrite <- PO4 in POA, POI.
clear LV4 FRS4 SP4 CR4 PO4.

rewrite !length_app, repeat_length in LEB4.
destruct BREP4 as ((rj4 & Lrj4 & BOBJ4) & (bs4 & BDAT4 & Hbs4) & BSIDE4). unfold bits_cells in BOBJ4. apply (proj1 (u8arr_rw_CB m4 D bs4)) in BDAT4.
assert (LBS4 : Z.of_nat (length bs4) = sb_buf_size b)
by (pose proof BOK4 as BOK'; unfold bits_ok in BOK'; rewrite Hbs4, zlength_map_unsigned, nbE_ltp_bits_size in BOK'; clear - BOK'; lia).
assert (DSZb4 : Z.of_nat (length bs4) = x_dsz X) by (rewrite LBS4, BSZ, <- DSZ; reflexivity).
assert (DLOb4 : D + Z.of_nat (length bs4) <= lo) by (rewrite DSZb4; exact DLO).
assert (DPD4 : D + Z.of_nat (length bs4) <= PD + ND) by (rewrite DSZb4; exact PD2).
clear LBS DSZb DLOb DPD Hbs BSIDE Lrj.

clear FRM. rename RS4 into FRM.
pose proof SLE as (E0s & E8s & E16s & E24s & E32s & E40s & E48s & E56s & E64s & E80s & E88s & E96s & E104s & E112s & E120s & E128s & E136s & E144s & E152s
& E160s & E168s & E176s & E184s & E192s & E224s & E240s & E248s & E256s & E272s & E280s & E288s & E296s & E304s & E312s & E336s).
pose proof (nbE_ltp_pitch mo r k b (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) SAT LTK BOK) as PPR.
assert (PP : 17 <= ltp_pitch k (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) b <= 144) by (clear - PPR LS1 LS2; lia).
assert (SA34 : rw_cells asegs m4 (usp + -592) (ltp_args_cells A (Z_to_bv 64 0) (40 * sub) ++ [CB 8 jk]))
by (apply rw_cells_app; split; [exact SA4| rewrite nbE_sz_ltpargs; exact SA3b]).
clear SA4 SA3b.
assert (OBE4 : aobj asegs m4 (FF + 544) 160) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACE4]).
pose proof (af_client_consts RT AF Σ4 m4 ART4) as CC4.
cps_seg (nbe_c usp lo ST OUT A FF SF olp bp sub (ltp_pitch k (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) b) (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s)) jk e324 pg4 _ _ m4
SL3 ltac:(cbn; exact E248s) ltac:(cbn; exact E64s) ltac:(cbn; exact E192s) ltac:(cbn; exact E256s) ltac:(cbn; exact E280s)
SA34 E324 LE324 OBE4 PG4 LPG4 PV4 BP PP SUB F0 F64 FLO FTOP FSH ST4 ltac:(clear - NROOM; lia) LOS SPH U32 MI4 CC4 FRM).
destruct POST as (m5 & F5 & fc5 & yt0 & yt1 & yt2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & bp' & e325
& -> & FRM5 & MU5 & WM5 & MI5 & ST5 & SL5 & BPE & E325 & LE325).
clear SL3 SA34 E324 ST4 OBE4 CC4 FRM ACE4 ACP4 ACG4.
assert (ART5 : ART RT Σ4 m5).
{ apply (af_frame RT AF Σ4 m4 m5 lo ART4 LOWS); [| exact WM5]. intros a Ha; apply MU5; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
cps_pf_seg m4 m5 MU5.
clear ART4. nbe_seg_tr m4 m5 MU5 WM5. try match goal with MI : mem_inv asegs m4 |- _ => clear MI end.

pose proof (nbsh_acc_E m5 FF SF rest SH ESF F64 ltac:(lia)) as (_ & _ & ACI5 & _).
pose proof (proj2 FFi) as WRI. rewrite cells_size_f32, FL5 in WRI. change (Z.of_nat (4 * 40)) with 160 in WRI.
assert (CD2 : checked_dst RT Σ4 m5 (Z_to_bv 64 (usp + -544)) (FF + 320) 160)
by (apply (nbE_frame_checked_dst Σ4 m5 _ FF NBD_FCLASS); [exact INF| lia| fs_lit; lia| exact ACI5| exact WRI]).
cps_rt (MST Σ4 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (FF + 320) 160 (Z_to_bv 8 0) lo).
{ clear - F0 FLO LOU NTOP. lia. }
{ cps_callok. }
intros c6 Hc6.
clear CD2 ACI5 FFi.
nbe_unpack Hc6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & BY6).
nbe_trp PRES6.
cps_pf_pres PRES6.
clear ART5 MI5 ST5 PRES6.
assert (FFi6 : rw_cells asegs m6 (FF + 320) (f32 (repeat (Z_to_bv 64 0) 40))).
{ split; [split; [apply cells_wf_f32 | replace (cells_bytes (f32 (repeat (Z_to_bv 64 0) 40))) with (repeat (Z_to_bv 8 0) (Z.to_nat 160)) by (vm_compute; reflexivity); exact BY6]|].
rewrite cells_size_f32, repeat_length. exact (wr_at_transport asegs m5 m6 _ _ WRI WM6). }
clear BY6 WRI.

destruct (af_acc_live RT AF Σ4 m6 ST 2968 ART6 INL) as (_ & ACS6).
assert (OBS6 : aobj asegs m6 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS6]). clear ACS6.
pose proof (AF_LIB Σ4 m6 ART6) as LC6. pose proof (nbE_tabs_acc_art Σ4 m6 ART6) as NTA6. pose proof (af_client_consts RT AF Σ4 m6 ART6) as CC6.
assert (BREP6 : bits_rep asegs m6 A D (ltp_bits k b))
by exact (conj (ex_intro _ rj4 (conj Lrj4 BOBJ4)) (conj (ex_intro _ bs4 (conj (proj2 (u8arr_rw_CB m6 D bs4) BDAT4) Hbs4)) BSIDE4)).
pose proof (nbG_acc_pres2 RT AF Σ4 m6 m m6 (usp + -544) _ fh kh A 48 ART6 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA6.
assert (OBA6 : aobj asegs m6 A 48) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACA6]).
destruct (af_acc_live RT AF Σ4 m6 PD ND ART6 INPD) as (_ & ACD6).
assert (OBD6 : aobj asegs m6 D (sb_buf_size (ltp_bits k b))).
{ rewrite nbE_ltp_bits_size, BSZ, <- DSZ. split; [lia|]. split; [unfold APP_TOP, USTACK_TOP in *; lia|].
exact (acc_sub asegs m6 PD ND D (x_dsz X) ACD6 PD1 PD2). }
assert (K3 : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj asegs m6 a n) by (intros a n; exact (aobj_lit RT AF Σ4 m6 a n ART6)).
assert (OS3 : aobj asegs m6 A_scal3 32) by (apply K3; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_scal3; lia | unfold A_scal3, APP_TOP; lia]).
assert (OS1 : aobj asegs m6 A_scal1 8) by (apply K3; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_scal1; lia | unfold A_scal1, APP_TOP; lia]).
clear K3 ACD6.
cps_seg (nbe_d1 usp lo ST OUT A D FF SF olp mo r st (j_pad1 j) (ltp_bits k b) (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) _ _ m6
SL5 ltac:(cbn; exact E296s) ltac:(cbn; exact E312s) ltac:(cbn; exact E304s) ltac:(cbn; exact E288s)
P15 EMO SAT OBS6 S8 SPOS SLO SSH LC6 NTA6 CC6 BREP6 BOK4 OBA6 OBD6 ASH ALO ltac:(rewrite nbE_ltp_bits_size, BSZ, <- DSZ; exact DLO)
OS3 OS1 ST6 ltac:(clear - NROOM; lia) LOS SPH MI6 FRM5).
destruct POST as (m7 & F7 & fc7 & xra7 & zt0 & zt1 & zt2 & za0 & za1 & za2 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & -> & FRM7 & MU7 & WM7 & MI7 & ST7 & BREP7).
clear BOBJ4 BDAT4 BREP6 OBS6 LC6 NTA6 CC6 ACA6 OBA6 OBD6 OS3 OS1 ST6 FRM5.
unfold BITS_SIZEOF in MU7.
assert (ART7 : ART RT Σ4 m7).
{ apply (af_frame RT AF Σ4 m6 m7 lo ART6 LOWS); [| exact WM7]. intros a Ha; apply MU7; cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists fh, kh; split; [exact INFH| clear - Hin FHA1 FHA2; lia]|].
split; [intros Hin; apply Ha; left; unfold USTACK_TOP; clear - Hin LOU NROOM NTOP; lia| exact I]. }
cps_pf_seg m6 m7 MU7.
clear ART6. nbe_seg_tr m6 m7 MU7 WM7. try match goal with MI : mem_inv asegs m6 |- _ => clear MI end.
destruct (af_acc_live RT AF Σ4 m7 ST 2968 ART7 INL) as (_ & ACS7).
assert (OBS7 : aobj asegs m7 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS7]). clear ACS7.
pose proof (AF_LIB Σ4 m7 ART7) as LC7. pose proof (nbE_tabs_acc_art Σ4 m7 ART7) as NTA7. pose proof (af_client_consts RT AF Σ4 m7 ART7) as CC7.
cps_seg (nbe_d2 usp lo ST OUT A FF SF olp mo r ki st (j_pad1 j) (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) _ _ m7
SL5 ltac:(cbn; exact E296s) ltac:(cbn; exact E312s) ltac:(cbn; exact E304s) ltac:(cbn; exact E288s) ltac:(cbn; exact E280s) ltac:(cbn; exact E184s)
P15 EMO SAT INK OBS7 S8 SPOS SLO SSH LC7 NTA7 CC7 ST7 ltac:(clear - NROOM; lia) LOS SPH MI7).
destruct POST as (zt0' & zt2' & za7' & ->). clear OBS7 LC7 NTA7 CC7.

pose proof (AF_LIB Σ4 m7 ART7) as LC7.
pose proof (nbE_innov_row mo r ki m7 SAT INK LC7) as IPAR. clear LC7.
pose proof (nbE_ltp_bits_ok mo r k b SAT LTK BOK) as BOKl.
destruct (nbE_hsg_ok (smr_sm r) (ltp_bits k b) BOKl) as (BOKh & BSZh).
pose proof (nbsh_acc_E m7 FF SF rest SH ESF F64 ltac:(lia)) as (_ & _ & ACI7 & _).
pose proof (nbG_acc_pres2 RT AF Σ4 m7 m m7 (usp + -544) _ fh kh A 48 ART7 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA7.
cps_rt (INN ki INK Σ4 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 A D (hsg_bits (smr_sm r) (ltp_bits k b))
(FF + 320) (ST + 2228) (smr_innov_par r) lo ST 2968 PD ND fh kh (repeat (Z_to_bv 64 0) 40) (j_seed j) (Z_to_bv 64 0)).
{ left. exists FF, NBD_FCLASS. split; [exact INF|]. unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACI7| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold in_frame_obj, BITS_SIZEOF. split; [exact FHA1|]. split; [exact FHA2|]. split; [exact ACA7| clear - A8; Z.div_mod_to_equations; lia]. }
{ rewrite BSZh, nbE_ltp_bits_size, BSZ, <- DSZ. exact PD2. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact ST7. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold RT_STACK, INNOV_STACK. clear - NROOM. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold USTACK_TOP. clear - NTOP. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). clear - U32. Z.div_mod_to_equations. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact POA. }
intros c8 (Σ8 & Hc8 & LV8 & FRS8 & SP8 & CR8 & PO8).
cps_unpack_lib Hc8 as (v8 & m8 & is8 & seed8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & FFi8 & LFi8 & SEED8 & BREP8 & BOK8 & ACI8 & ACA8).
clear FFi6 P14 ACI7 ACA7.
clear BREP7.
nbe_trp PRES8.
nbe_pf_fp PRES8.
clear ART7 MI7 ST7 PRES8. try clear Hc0.
rewrite <- LV8 in INL, INPD, LV, PF, SPL. rewrite <- FRS8 in INF, INFH, FRS, PF, SPL. rewrite <- SP8 in LOWS, SP0, SPL. rewrite <- CR8 in CR. rewrite <- PO8 in POA, POI.
clear LV8 FRS8 SP8 CR8 PO8.
clear FRM7. rename RS8 into FRM.

destruct (nbE_innov_bits_ok mo r ki _ SAT INK BOKh) as (_ & BSZi).
destruct BREP8 as ((rj8 & Lrj8 & BOBJ8) & (bs8 & BDAT8 & Hbs8) & BSIDE8). unfold bits_cells in BOBJ8. apply (proj1 (u8arr_rw_CB m8 D bs8)) in BDAT8.
assert (LBS8 : Z.of_nat (length bs8) = sb_buf_size b)
by (pose proof BOK8 as BOK'; unfold bits_ok in BOK'; rewrite Hbs8, zlength_map_unsigned, BSZi, BSZh, nbE_ltp_bits_size in BOK'; clear - BOK'; lia).
assert (DSZb8 : Z.of_nat (length bs8) = x_dsz X) by (rewrite LBS8, BSZ, <- DSZ; reflexivity).
assert (DLOb8 : D + Z.of_nat (length bs8) <= lo) by (rewrite DSZb8; exact DLO).
assert (DPD8 : D + Z.of_nat (length bs8) <= PD + ND) by (rewrite DSZb8; exact PD2).
clear LBS4 DSZb4 DLOb4 DPD4 Hbs4 BSIDE4 Lrj4 BOK4.

destruct (af_acc_live RT AF Σ8 m8 ST 2968 ART8 INL) as (_ & ACS8).
assert (OBS8 : aobj asegs m8 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS8]). clear ACS8.
pose proof (AF_LIB Σ8 m8 ART8) as LC8. pose proof (nbE_tabs_acc_art Σ8 m8 ART8) as NTA8. pose proof (af_client_consts RT AF Σ8 m8 ART8) as CC8.
assert (OBI8 : aobj asegs m8 (FF + 320) 160) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACI8]).
cps_seg (nbe_e usp lo ST OUT A FF SF olp mo r st (j_pad1 j) rest is8 (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) _ _ m8
SL5 ltac:(cbn; exact E296s) ltac:(cbn; exact E312s) ltac:(cbn; exact E304s) ltac:(cbn; exact E288s) ltac:(cbn; exact E176s)
P15 EMO SAT OBS8 S8 SPOS SLO SSH SFA LC8 NTA8 CC8 FFi8 LFi8 OBI8 SH ESF SF0 SF1 F0 F64 FLO FTOP FSH ST8 ltac:(clear - NROOM; lia) LOS NTOP MI8 FRM).
destruct POST as (m9 & F9 & fc9 & wt0 & wt1 & wt2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & wt4 & wt5 & wt6 & is9
& FRM9 & MU9 & WM9 & MI9 & ST9 & FFi9 & LFi9 & DCB).
clear OBS8 LC8 NTA8 CC8 OBI8 FFi8 ST8 FRM ACI8.
assert (SH9 : rw_cells asegs m9 SF (nbd_shadow (if sm_double_codebook (smr_sm r) =? 0 then SC_E else SC_E2) rest))
by (destruct DCB as [(E & _ & SHx)|(E & _ & SHx)]; rewrite E; exact SHx).
clear SH.
assert (ART9 : ART RT Σ8 m9).
{ apply (af_frame RT AF Σ8 m8 m9 lo ART8 LOWS); [| exact WM9]. intros a Ha; apply MU9; cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; clear - Hin; lia]|].
split; [intros Hin; apply Ha; right; right; right; right; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; rewrite SHD1, SHD2; clear - Hin; lia]|].
split; [intros Hin; apply Ha; left; unfold USTACK_TOP; clear - Hin LOU NROOM NTOP; lia| exact I]. }
cps_pf_seg m8 m9 MU9.
clear ART8. nbe_seg_tr m8 m9 MU9 WM9. try match goal with MI : mem_inv asegs m8 |- _ => clear MI end.
clear Hc.
destruct DCB as [(DCB0 & -> & _) | (DCB1 & -> & _)].
-
rewrite DCB0 in SH9. cbn [Z.eqb] in SH9.
apply Hk. exists bp'.
pose proof (nbG_acc_pres2 RT AF Σ8 m9 m m9 (usp + -544) _ fh kh A 48 ART9 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA9.
assert (OFFO : forall i, 0 <= i < 4 * Z.of_nat nout -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -544, usp)] (shad (OUT + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 RT AF Σ8 m9 m m9 (usp + -544) _ fh kh OUT (4 * Z.of_nat nout) ART9 INFH FHO1 FHO2 PF OFFO (proj1 NACC)) as ACO9.
assert (OFFT : forall i, 0 <= i < 8 -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -544, usp)] (shad (STEREO + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 RT AF Σ8 m9 m m9 (usp + -544) _ fh kh STEREO 8 ART9 INFH FHS1 FHS2 PF OFFT (proj2 (proj2 NACC))) as ACT9.
assert (WM9E : wmono asegs mE m9) by (apply (wmono_trans asegs mE m m9); [exact WME| cps_wmono]).
assert (PF9E : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE m9).
{ apply (pres_fp_trans _ _ _ _ mE m m9); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_Jc.
exists Σ8, F9, fc9, m9, (Z_to_bv 64 RA_nbe_smul1), (Z_to_bv 64 (Z.shiftr (981792 + mo * 8) 3 + SHB)), (Z_to_bv 64 (981792 + mo * 8)),
wt0, wt1, wt2, wa0, wa1, wa2, wa3, wa4, wa5, wa6, wa7, wt3, wt4, wt5, wt6,
(NBJ (j_last_ol_gain j) eb4 (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed8 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)),
ows, sws, s, (NBF (Z_to_bv 64 (ltp_pitch k (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) b)) pg4 (f_lpc ff) (f_qlsp ff) (f_ak ff) is9 e325 (f_innov2 ff) (f_iq ff)), bp.
split; [exact Hc0|]. split; [exact FRM9|].
split.
{ unfold nbctx. split; [exact MI9|]. split; [exact ST9|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split.
{ unfold nb_hdr_cells. rewrite NCL.
change [C8 (Z_to_bv 64 A_speex_nb_mode); C4 (Z_to_bv 64 (nb_first st)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 (j_last_ol_gain j); C8 (Z_to_bv 64 0)]
with ([C8 (Z_to_bv 64 A_speex_nb_mode)] ++ [C4 (Z_to_bv 64 (nb_first st))] ++ [C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 (j_last_ol_gain j); C8 (Z_to_bv 64 0)]).
apply rw_cells_app. split; [exact P1a|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 8) by (cbn; lia) end.
apply rw_cells_app. split; [exact P1b|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 12) by (cbn; lia) end.
apply rw_cells_app. split; [exact P1c|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 16) by (cbn; lia) end. exact P1. }
split; [exact EB4|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact SEED8|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split.
{ unfold nb_junk_ok. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [clear - LEB4 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact JL12| exact JL13]. }
split; [exact CBOK|]. split; [exact NINV|].
split; [unfold nbE_bJ; rewrite DCB0; cbn [negb Z.eqb];
exact (conj (ex_intro _ rj8 (conj Lrj8 BOBJ8)) (conj (ex_intro _ bs8 (conj (proj2 (u8arr_rw_CB m9 D bs8) BDAT8) Hbs8)) BSIDE8))|].
split; [unfold nbE_bJ; rewrite DCB0; cbn [negb Z.eqb]; exact BOK8|].
split; [unfold nbE_bJ; rewrite DCB0; cbn [negb Z.eqb]; rewrite BSZi, BSZh, nbE_ltp_bits_size; exact BSZ|].
split; [exact OW|]. split; [exact LOW|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SL5 SV)|].
split; [exact (conj FF0 (conj PV4 (conj PG4 (conj FFl (conj FFq (conj FFk (conj FFi9 (conj E325 (conj FFj FFiq)))))))))|].
split; [exact (conj LPG4 (conj FL2 (conj FL3 (conj FL4 (conj LFi9 (conj LE325 (conj FL7 FL8)))))))|].
split; [exists rest; exact SH9|].
split; [exact (af_client_consts RT AF Σ8 m9 ART9)|]. split; [exact (AF_LIB Σ8 m9 ART9)|]. split; [reflexivity| exact JISV]. }
split; [exact SLE|]. split; [exact SAT|]. split; [exact EMO|]. split; [destruct BPE as [-> | ->]; [exact BP| exact PP]|].
split; [exact OLP|]. split; [exact SUB|].
split; [exact (conj ART9 (conj (conj ACO9 (conj ACA9 ACT9)) (conj WM9E PF9E)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
-
rewrite DCB1 in SH9. cbn [Z.eqb] in SH9.
pose proof (nbsh_acc_E2 m9 FF SF rest SH9 ESF F64 ltac:(lia)) as (_ & ACJ9).
pose proof (proj2 FFj) as WRJ. rewrite cells_size_f32, FL7 in WRJ. change (Z.of_nat (4 * 40)) with 160 in WRJ.
assert (CD3 : checked_dst RT Σ8 m9 (Z_to_bv 64 (usp + -544)) (FF + 768) 160)
by (apply (nbE_frame_checked_dst Σ8 m9 _ FF NBD_FCLASS); [exact INF| lia| fs_lit; lia| exact ACJ9| exact WRJ]).
cps_rt (MST Σ8 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 (FF + 768) 160 (Z_to_bv 8 0) lo).
{ clear - F0 FLO LOU NTOP. lia. }
{ cps_callok. }
intros c10 Hc10.
clear CD3 ACJ9 FFj.
nbe_unpack Hc10 as (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & BY10).
nbe_trp PRES10.
cps_pf_pres PRES10.
clear ART9 MI9 ST9 PRES10.
assert (FFj10 : rw_cells asegs m10 (FF + 768) (f32 (repeat (Z_to_bv 64 0) 40))).
{ split; [split; [apply cells_wf_f32 | replace (cells_bytes (f32 (repeat (Z_to_bv 64 0) 40))) with (repeat (Z_to_bv 8 0) (Z.to_nat 160)) by (vm_compute; reflexivity); exact BY10]|].
rewrite cells_size_f32, repeat_length. exact (wr_at_transport asegs m9 m10 _ _ WRJ WM10). }
clear BY10 WRJ.
pose proof (AF_LIB Σ8 m10 ART10) as LC10. pose proof (nbE_tabs_acc_art Σ8 m10 ART10) as NTA10.
cps_seg (nbe_f usp lo ST OUT A FF SF olp mo r ki (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) _ _ m10
SL5 ltac:(cbn; exact E240s) ltac:(cbn; exact E256s) ltac:(cbn; exact E176s) ltac:(cbn; exact E184s) SAT INK LC10 NTA10 ST10 ltac:(clear - NROOM; lia) LOS SPH MI10).
destruct POST as (ut0 & ut2 & ua7 & ->). clear LC10 NTA10.

pose proof (AF_LIB Σ8 m10 ART10) as LC10.
pose proof (nbE_innov_row mo r ki m10 SAT INK LC10) as IPAR2. clear LC10.
destruct (nbE_innov_bits_ok mo r ki _ SAT INK BOKh) as (BOKi & _).
pose proof (nbsh_acc_E2 m10 FF SF rest SH9 ESF F64 ltac:(lia)) as (_ & ACJ10).
pose proof (nbG_acc_pres2 RT AF Σ8 m10 m m10 (usp + -544) _ fh kh A 48 ART10 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA10.
assert (BREP10 : bits_rep asegs m10 A D (innov_bits ki (hsg_bits (smr_sm r) (ltp_bits k b))))
by exact (conj (ex_intro _ rj8 (conj Lrj8 BOBJ8)) (conj (ex_intro _ bs8 (conj (proj2 (u8arr_rw_CB m10 D bs8) BDAT8) Hbs8)) BSIDE8)).
cps_rt (INN ki INK Σ8 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 A D (innov_bits ki (hsg_bits (smr_sm r) (ltp_bits k b)))
(FF + 768) (ST + 2228) (smr_innov_par r) lo ST 2968 PD ND fh kh (repeat (Z_to_bv 64 0) 40) seed8 (Z_to_bv 64 0)).
{ left. exists FF, NBD_FCLASS. split; [exact INF|]. unfold in_frame_obj. fs_lit. split; [lia|]. split; [lia|]. split; [exact ACJ10| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold in_frame_obj, BITS_SIZEOF. split; [exact FHA1|]. split; [exact FHA2|]. split; [exact ACA10| clear - A8; Z.div_mod_to_equations; lia]. }
{ rewrite BSZi, BSZh, nbE_ltp_bits_size, BSZ, <- DSZ. exact PD2. }
{ unfold hidp, BITS_SIZEOF. pose proof (AFFA : _ \/ _) as U. clear - U. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact ST10. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold RT_STACK, INNOV_STACK. clear - NROOM. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). unfold USTACK_TOP. clear - NTOP. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). clear - U32. Z.div_mod_to_equations. lia. }
{ rewrite unsigned_lit by (clear - LOU NROOM NTOP LOS; lia). exact POA. }
intros c12 (Σ11 & Hc11 & LV11 & FRS11 & SP11 & CR11 & PO11).
cps_unpack_lib Hc11 as (v11 & m11 & is11 & seed11 & RS11 & (ART11 & MI11 & WM11 & ST11) & PRES11 & FFj11 & LFj11 & SEED11 & BREP11 & BOK11 & ACJ11 & ACA11).
clear FFj10 SEED8 BREP10 ACJ10 ACA10 BOBJ8 BDAT8.
nbe_trp PRES11.
nbe_pf_fp PRES11.
clear ART10 MI10 ST10 PRES11. try clear Hc0.
rewrite <- LV11 in INL, INPD, LV, PF, SPL. rewrite <- FRS11 in INF, INFH, FRS, PF, SPL. rewrite <- SP11 in LOWS, SP0, SPL. rewrite <- CR11 in CR. rewrite <- PO11 in POA, POI.
clear LV11 FRS11 SP11 CR11 PO11.
clear FRM9. rename RS11 into FRM.
destruct (nbE_innov_bits_ok mo r ki _ SAT INK BOKi) as (_ & BSZi2).
destruct BREP11 as ((rj11 & Lrj11 & BOBJ11) & (bs11 & BDAT11 & Hbs11) & BSIDE11). unfold bits_cells in BOBJ11. apply (proj1 (u8arr_rw_CB m11 D bs11)) in BDAT11.
assert (LBS11 : Z.of_nat (length bs11) = sb_buf_size b)
by (pose proof BOK11 as BOK'; unfold bits_ok in BOK'; rewrite Hbs11, zlength_map_unsigned, BSZi2, BSZi, BSZh, nbE_ltp_bits_size in BOK'; clear - BOK'; lia).
assert (DSZb11 : Z.of_nat (length bs11) = x_dsz X) by (rewrite LBS11, BSZ, <- DSZ; reflexivity).
assert (DLOb11 : D + Z.of_nat (length bs11) <= lo) by (rewrite DSZb11; exact DLO).
assert (DPD11 : D + Z.of_nat (length bs11) <= PD + ND) by (rewrite DSZb11; exact PD2).
clear LBS8 DSZb8 DLOb8 DPD8 Hbs8 BSIDE8 Lrj8.

pose proof (af_client_consts RT AF Σ11 m11 ART11) as CC11.
assert (OBJ11 : aobj asegs m11 (FF + 768) 160) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACJ11]).
cps_seg (nbe_g usp lo ST FF SF olp mo rest is9 is11 (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(sset 192 (Z_to_bv 64 bp') (slots_Eb ST sub (slots_Ea (nb_isave_ptr OUT st) (ST + 1368) sub s))) _ _ m11
SL5 ltac:(cbn; exact E280s) FFi9 LFi9 FFj11 LFj11 OBJ11 SH9 ESF SF0 SF1 F0 F64 FLO FTOP FSH CC11 ST11 ltac:(clear - NROOM; lia) LOS SPH MI11 FRM).
destruct POST as (m12 & F12 & fc12 & xra12 & vt0 & vt1 & vt2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & vt3 & vt4 & vt5 & vt6 & is12 & i212
& -> & FRM12 & MU12 & WM12 & MI12 & ST12 & FFi12 & LFi12 & FFj12 & LFj12 & SH12).
clear CC11 OBJ11 FFi9 FFj11 SH9 ST11 FRM ACJ11 ACA11.
assert (ART12 : ART RT Σ11 m12).
{ apply (af_frame RT AF Σ11 m11 m12 lo ART11 LOWS); [| exact WM12]. intros a Ha; apply MU12; cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; clear - Hin; lia]|].
split; [intros Hin; apply Ha; right; right; right; left; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; clear - Hin; lia]|].
split; [intros Hin; apply Ha; right; right; right; right; exists FF, NBD_FCLASS; split; [exact INF| fs_lit; rewrite SHD1, SHD2; clear - Hin; lia]|].
split; [intros Hin; apply Ha; left; unfold USTACK_TOP; clear - Hin LOU NROOM NTOP; lia| exact I]. }
cps_pf_seg m11 m12 MU12.
clear ART11. nbe_seg_tr m11 m12 MU12 WM12. try match goal with MI : mem_inv asegs m11 |- _ => clear MI end.
clear Hc1.
apply Hk. exists bp'.
pose proof (nbG_acc_pres2 RT AF Σ11 m12 m m12 (usp + -544) _ fh kh A 48 ART12 INFH FHA1 FHA2 PF OFFA (proj1 (proj2 NACC))) as ACA12.
assert (OFFO : forall i, 0 <= i < 4 * Z.of_nat nout -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -544, usp)] (shad (OUT + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) OUT (4 * Z.of_nat nout) i (eq_sym ESF8) F64 ltac:(clear - OTOP; lia) ltac:(clear - OLO LOU NTOP; lia)
OFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 RT AF Σ11 m12 m m12 (usp + -544) _ fh kh OUT (4 * Z.of_nat nout) ART12 INFH FHO1 FHO2 PF OFFO (proj1 NACC)) as ACO12.
assert (OFFT : forall i, 0 <= i < 8 -> outside [(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp + -544, usp)] (shad (STEREO + i))).
{ intros i Hi. exact (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat nout) STEREO 8 i (eq_sym ESF8) F64 ltac:(clear - STETOP; lia) ltac:(clear - STELO LOU NTOP; lia)
STEFA Hi SSH OSH ASH FSH LOS ltac:(clear - LOU; lia)). }
pose proof (nbG_acc_pres2 RT AF Σ11 m12 m m12 (usp + -544) _ fh kh STEREO 8 ART12 INFH FHS1 FHS2 PF OFFT (proj2 (proj2 NACC))) as ACT12.
assert (WM12E : wmono asegs mE m12) by (apply (wmono_trans asegs mE m m12); [exact WME| cps_wmono]).
assert (PF12E : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 544) (nbW_EH X) mE m12).
{ apply (pres_fp_trans _ _ _ _ mE m m12); [exact PFE|]. rewrite <- LV, <- FRS. unfold nbW_EH, NBSTATE_SIZEOF, BITS_SIZEOF, NBD_FRAME. exact PF. }
unfold at_Jc.
exists Σ11, F12, fc12, m12, xra12, (Z_to_bv 64 (FF + 928)), (Z_to_bv 64 (981792 + mo * 8)),
vt0, vt1, vt2, va0, va1, va2, va3, va4, va5, va6, va7, vt3, vt4, vt5, vt6,
(NBJ (j_last_ol_gain j) eb4 (ST + 1368) (j_old_qlsp j) (j_interp_qlpc j) (j_mem_sp j) (j_mem_hp j) (j_pi_gain j) (j_levels j) (j_last_pitch j)
(j_last_pitch_gain j) (j_pitch_gain_buf j) seed11 (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)),
ows, sws, s, (NBF (Z_to_bv 64 (ltp_pitch k (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp) b)) pg4 (f_lpc ff) (f_qlsp ff) (f_ak ff) is12 e325 i212 (f_iq ff)), bp.
split; [exact Hc0|]. split; [exact FRM12|].
split.
{ unfold nbctx. split; [exact MI12|]. split; [exact ST12|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split.
{ unfold nb_hdr_cells. rewrite NCL.
change [C8 (Z_to_bv 64 A_speex_nb_mode); C4 (Z_to_bv 64 (nb_first st)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 (j_last_ol_gain j); C8 (Z_to_bv 64 0)]
with ([C8 (Z_to_bv 64 A_speex_nb_mode)] ++ [C4 (Z_to_bv 64 (nb_first st))] ++ [C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 (j_last_ol_gain j); C8 (Z_to_bv 64 0)]).
apply rw_cells_app. split; [exact P1a|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 8) by (cbn; lia) end.
apply rw_cells_app. split; [exact P1b|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 12) by (cbn; lia) end.
apply rw_cells_app. split; [exact P1c|]. match goal with |- rw_cells _ _ ?a _ => replace a with (ST + 16) by (cbn; lia) end. exact P1. }
split; [exact EB4|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|]. split; [exact SEED11|]. split; [exact P15|]. split; [exact P16|].
split; [exact P17|]. split; [exact P18| exact P19]. }
split.
{ unfold nb_junk_ok. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split; [clear - LEB4 LEX1 LEX3; lia|]. split; [exact JL2|]. split; [exact JL3|]. split; [exact JL4|]. split; [exact JL5|]. split; [exact JL6|]. split; [exact JL7|].
split; [exact JL8|]. split; [exact JL9|]. split; [exact JL10|]. split; [exact (conj JL11a JL11b)|]. split; [exact JL12| exact JL13]. }
split; [exact CBOK|]. split; [exact NINV|].
split; [unfold nbE_bJ; rewrite DCB1; cbn [negb Z.eqb];
exact (conj (ex_intro _ rj11 (conj Lrj11 BOBJ11)) (conj (ex_intro _ bs11 (conj (proj2 (u8arr_rw_CB m12 D bs11) BDAT11) Hbs11)) BSIDE11))|].
split; [unfold nbE_bJ; rewrite DCB1; cbn [negb Z.eqb]; exact BOK11|].
split; [unfold nbE_bJ; rewrite DCB1; cbn [negb Z.eqb]; rewrite BSZi2, BSZi, BSZh, nbE_ltp_bits_size; exact BSZ|].
split; [exact OW|]. split; [exact LOW|]. split; [exact SW|]. split; [exact LSW|].
split; [exact (conj SL5 SV)|].
split; [exact (conj FF0 (conj PV4 (conj PG4 (conj FFl (conj FFq (conj FFk (conj FFi12 (conj E325 (conj FFj12 FFiq)))))))))|].
split; [exact (conj LPG4 (conj FL2 (conj FL3 (conj FL4 (conj LFi12 (conj LE325 (conj LFj12 FL8)))))))|].
split; [exists rest; exact SH12|].
split; [exact (af_client_consts RT AF Σ11 m12 ART12)|]. split; [exact (AF_LIB Σ11 m12 ART12)|]. split; [reflexivity| exact JISV]. }
split; [exact SLE|]. split; [exact SAT|]. split; [exact EMO|]. split; [destruct BPE as [-> | ->]; [exact BP| exact PP]|].
split; [exact OLP|]. split; [exact SUB|].
split; [exact (conj ART12 (conj (conj ACO12 (conj ACA12 ACT12)) (conj WM12E PF12E)))|].
exact (conj LV (conj FRS (conj SP0 (conj CR POI)))).
Unshelve. all: exact bptr.
Qed.

End NbE.
