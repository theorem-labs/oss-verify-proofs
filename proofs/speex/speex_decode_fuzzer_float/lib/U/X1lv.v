(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qw X0pv X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1nl X1m8 X1fr X1no X1np X1h7 X1kc X1ka X1kd X1k9. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1m7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1o8 X1rm X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.
Ltac ua := change X1ff.rsegs with X1gj.rsegs in *; change U.X1fd.rsegs with X1gj.rsegs in *.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma implM_enter : forall {A} (c : M PState A) s (Q : A -> PState -> machine_state -> Prop) ms,
evt rsegs (fun ms' => implM rsegs c s Q ms') ms -> implM rsegs c s Q ms.
Proof. intros A c s Q ms H. unfold implM in *. apply impl_evt with (P := fun ms' => impl rsegs (at_node rsegs) (c s) (epost (fun p => Q (fst p) (snd p))) ms'); [exact H| intros ms' X; exact X]. Qed.

Lemma pres_except_of_heap : forall LB SP m m', rheap_pres LB SP m m' -> pres_except rsegs (rclient_addr LB SP) [] m m'.
Proof. intros LB SP m m' H a Ha Hc _. exact (H a Ha Hc). Qed.

Lemma rdrv_pres_refl : forall LB SP m, rdrv_pres LB SP m m.
Proof. intros. apply pres_except_refl. Qed.
Lemma rdrv_pres_trans : forall LB SP m1 m2 m3, rdrv_pres LB SP m1 m2 -> rdrv_pres LB SP m2 m3 -> rdrv_pres LB SP m1 m3.
Proof. intros. eapply pres_except_trans; eauto. Qed.

Lemma rdrv_pres_of_heap : forall LB LB' SP SP' m m',
rheap_pres LB' SP' m m' -> SP' <= SP -> (forall b, In b LB -> In b LB') -> rdrv_pres LB SP m m'.
Proof.
intros LB LB' SP SP' m m' H HS HL. eapply pres_except_weaken; [apply pres_except_of_heap; exact H| |intros a X; destruct X].
intros a [X|[X|(b & Hb & Hr)]]; [left; lia| right; left; exact X| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
Qed.

Lemma rdrv_pres_of_harness : forall LB LB' SP SP' m m',
pres_except rsegs (rclient_addr LB' SP') rharness_X m m' -> SP' <= SP -> (forall b, In b LB -> In b LB') -> rdrv_pres LB SP m m'.
Proof.
intros LB LB' SP SP' m m' H HS HL. eapply pres_except_weaken; [exact H| |].
- intros a [X|[X|(b & Hb & Hr)]]; [left; lia| right; left; exact X| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
- unfold rharness_X, rdrv_X. cbn. intros a X. tauto.
Qed.

Lemma rdrv_pres_of_munch {RCEIL : RunCeiling} : forall LB SP m m' W,
munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => (snd iv <= SP /\ alloc_ceiling <= fst iv) \/ In iv rdrv_X
\/ (snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x6e000 <= fst iv)
/\ forall b, In b LB -> blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b)) W ->
(forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)) -> alloc_ceiling <= SP ->
rdrv_pres LB SP m m'.
Proof.
intros LB SP m m' W MU WM HW HB HSP. eapply pres_except_of_munch; [exact MU| exact WM|].
intros a Ha Hc Hx. clear MU WM. induction HW as [|[lo1 hi1] W H1 H2 IH]; cbn; [exact I|].
split; [| exact IH]. cbn [fst snd] in H1. intros IN.
destruct H1 as [H1|[H1|(H1 & H1' & H1'')]].
- destruct Hc as [C|[C|(b & Hb & Hr)]]; [lia| unfold alloc_ceiling in *; lia|].
pose proof (HB b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. lia.
- apply Hx. unfold rdrv_X in *. cbn in H1 |- *.
destruct H1 as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; inversion E; subst; tauto.
- destruct Hc as [C|[C|(b & Hb & Hr)]].
+ lia.
+ lia.
+ destruct (H1'' b Hb); lia.
Qed.

Lemma heap_pres_agree : forall LB SP m m', rheap_pres LB SP m m' -> agree_on rsegs (fun a => rclient_addr LB SP a) m m'.
Proof. intros LB SP m m' H a Ha Hc. exact (H a Ha Hc). Qed.

Lemma mod32_of_lit : forall rc, -2^31 <= rc < 2^31 -> bv_unsigned (Z_to_bv 64 rc) mod 2^32 = rc mod 2^32.
Proof.
intros rc Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
Z.div_mod_to_equations. nia.
Qed.

Definition RLOOP : Z := 0x1c010.

Fixpoint rall {Nd R : Type} (P : R -> Prop) (t : X1bt.itree Nd R) : Prop :=
match t with
| Ret r => P r
| Vis _ k => forall rsp, rall P (k rsp)
end.

Lemma rall_bind : forall {Nd A B : Type} (t : X1bt.itree Nd A) (f : A -> X1bt.itree Nd B) (P : B -> Prop),
(forall a, rall P (f a)) -> rall P (X1bt.bind Nd t f).
Proof. intros Nd A B t f P H. induction t as [r|n k IH]; cbn; [apply H| intros rsp; apply IH]. Qed.

Lemma rall_impl : forall {R} (t : X1bt.itree node R) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
impl rsegs (at_node rsegs) t Q ms -> rall P t -> impl rsegs (at_node rsegs) t (fun r ms' => Q r ms' /\ P r) ms.
Proof.
intros R t P Q. induction t as [r|n k IH]; intros ms H HP; cbn in *.
- eapply evt_mono; [exact H|]. intros ms' Hq. split; [exact Hq| exact HP].
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply Hk| apply HP].
Qed.

Definition mall {A} (P : A -> Prop) (c : M PState A) : Prop :=
forall s, rall (fun x => match x with Unr => True | Ok p => P (fst p) end) (c s).

Lemma mall_ret : forall {A} (P : A -> Prop) (a : A), P a -> mall P (mret a).
Proof. intros A P a H s. exact H. Qed.

Lemma mall_unr : forall {A} (P : A -> Prop), mall P (munr (A:=A)).
Proof. intros A P s. exact I. Qed.

Lemma mall_bind : forall {A B} (m : M PState A) (f : A -> M PState B) (P : B -> Prop),
(forall a, mall P (f a)) -> mall P (X1qx.mbind m f).
Proof.
intros A B m f P H s. unfold X1qx.mbind, ebind. apply rall_bind.
intros [|[a s']]; cbn; [exact I| apply H].
Qed.

Lemma implM_mall : forall {A} (c : M PState A) (P : A -> Prop) s Q ms,
mall P c -> implM rsegs c s Q ms -> implM rsegs c s (fun a s' ms' => Q a s' ms' /\ P a) ms.
Proof.
intros A c P s Q ms HP H. unfold implM in *.
eapply impl_mono; [exact (rall_impl _ _ _ _ H (HP s))|].
intros [|[a s']] ms' [H1 H2]; cbn in *; [exact I| split; assumption].
Qed.

Lemma fuzz_one_ret0 : forall pl, mall (fun r => r = 0) (fuzz_one pl).
Proof.
intros pl. unfold fuzz_one, X1od.LLVMFuzzerTestOneInput. cbv zeta.
lazymatch goal with |- mall _ (if ?c then _ else _) => destruct c end; [apply mall_ret; reflexivity|].
apply mall_bind. intros [bits|]; [| apply mall_unr].
apply mall_bind. intros o. destruct o;
first [ apply mall_ret; reflexivity | apply mall_bind; intros _; apply mall_ret; reflexivity ].
Qed.

Lemma AXSTAT_agree : forall (k : bool) (P : Z -> Prop) m m', agree_on rsegs P m m' -> (forall a, axstat_addr a -> P a) -> AXSTAT k m -> AXSTAT k m'.
Proof.
intros k P m m' AG HP. rewrite !AXSTAT_cells. intros (X1 & X2 & X3).
unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0, ax_cells in *. cbn [Z.add] in *.
split; [|split]; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HP; cbn in Ha; lia]).
Qed.

Lemma AXSTAT_heap_pres : forall k LBx SPx m m', rheap_pres LBx SPx m m' -> AXSTAT k m -> AXSTAT k m'.
Proof.
intros k LBx SPx m m' HP. apply (AXSTAT_agree k _ _ _ (heap_pres_agree _ _ _ _ HP)). intros a Ha. right; left.
unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.

Lemma AXSTAT_munch : forall k W m m', munch W m m' -> wmono rsegs m m' -> (forall a, axstat_addr a -> outside W a) -> AXSTAT k m -> AXSTAT k m'.
Proof. intros k W m m' MU WM HW. apply (AXSTAT_agree k _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

Lemma ax_cell_harness : forall LBx SPx m m' a cs, pres_except rsegs (rclient_addr LBx SPx) rharness_X m m' ->
rw_cells rsegs m a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> axstat_addr x) ->
rw_cells rsegs m' a cs.
Proof.
intros LBx SPx m m' a cs PE RW HA. eapply rw_cells_agree; [exact (pres_except_agree _ _ _ _ _ PE)| exact RW|].
intros x Hx. specialize (HA x Hx). unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0 in HA.
split; [lia|]. split.
- right; left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia.
- unfold rharness_X. cbn. lia.
Qed.

Section RUN.
Context {RCEIL : RunCeiling}.

Hypothesis RMALLOC : rmalloc_stmt.
Hypothesis RFREE : rfree_stmt.
Hypothesis EMIT : emit_printf_stmt ps_so set_so_ps.
Hypothesis FWXO : fwritex_stdout_stmt.
Hypothesis FUZZ : harness_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Hypothesis RBR : rheap_block_range_stmt.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem)
(LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (AB lo : Z).
Hypothesis INLB : In (p, A, cap) LB.
Hypothesis FC : Forall (fun c => 0 <= c < 256) content.
Hypothesis LC : zlength content <= cap.
Hypothesis CAP : cap <= 2^26.
Hypothesis L0 : 0 <= L.
Hypothesis L6 : 6 + L <= zlength content.
Hypothesis SPAB : bv_unsigned sp <= AB.
Hypothesis ABB : AB < 2^62.
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RTARGET_RUN_STACK.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.

Notation usp := (bv_unsigned sp).
Notation tpv := (Z_to_bv 64 RATP).
Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).

Definition plen : Z := zlength content - 6 - L.
Definition PAY : Z := A + 6 + L.
Definition payload : list Z := skipn (Z.to_nat (6 + L)) content.
Definition cfg : Z := if 0 <? L then znth content 2 else 0.
Definition calls : Z := 1 + Z.land cfg 3.

Definition LBT (ow : option (bptr * Z)) : list block :=
match ow with None => LB | Some (pb, P) => (pb, P, plen) :: LB end.
Definition oreg (ow : option (bptr * Z)) : Z := match ow with None => 0 | Some (_, P) => P end.
Definition optr (ow : option (bptr * Z)) : Z := match ow with None => REMPTY | Some (_, P) => P end.
Definition obptr (ow : option (bptr * Z)) : option bptr := match ow with None => None | Some (pb, _) => Some pb end.

Definition FRAME (j0 : list byte) (m : mem) : Prop :=
rw_cells rsegs m (usp + -80) [CB 8 j0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition INV0 (st : PState) (m : mem) : Prop :=
(exists x0, FRAME x0 m) /\ rtables_pristine m /\ stderr_wfile m /\ stdout_file m (ps_so st)
/\ (exists errv : word, rw_cells rsegs m RERRNO [C4 errv])
/\ rauxv_ok m AB /\ mem_inv rsegs m /\ stk rsegs m lo (usp + -80) /\ rdrv_pres LB usp m0 m.
Definition INV (ow : option (bptr * Z)) (st : PState) (m : mem) : Prop :=
RHEAP st (LBT ow) m /\ bytes_at rsegs m (optr ow) (to_bytes payload) /\ INV0 st m.

Notation DST ow pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 q3 k t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 (optr ow)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (oreg ow)) q3 (Z_to_bv 64 RINITIALIZED) (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Definition RUNST (ow : option (bptr * Z)) (pc : Z) (k : Z) (q3 : word) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
ms = DST ow pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 q3 k t3 t4 t5 t6 F fc m
/\ frm0 fc /\ INV ow st m /\ AXSTAT true m.

Notation POST := (rtarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

#[using="RCEIL sp cap FC LC CAP L0 L6"] Lemma facts : 0 <= plen /\ plen + 1 <= 2^26 /\ zlength payload = plen /\ 0 <= cfg < 256 /\ 1 <= calls <= 4 /\ PAY = A + 6 + L
/\ Forall (fun c => 0 <= c < 256) payload.
Proof.
unfold calls, plen, payload, cfg, PAY. unfold zlength in *. rewrite length_skipn.
split; [lia|]. split; [lia|]. split; [lia|].
assert (CR : 0 <= (if 0 <? L then znth content 2 else 0) < 256).
{ destruct (0 <? L); [|lia]. unfold znth. destruct (Z.ltb_spec 2 0); [lia|].
assert (LT : (Z.to_nat 2 < length content)%nat) by lia.
pose proof (proj1 (Forall_forall _ _) FC _ (nth_In content 0 LT)) as X. cbn beta in X. lia. }
split; [exact CR|]. split.
{ remember (if 0 <? L then znth content 2 else 0) as c. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. Z.div_mod_to_equations. lia. }
split; [reflexivity|].
apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) FC).
rewrite <- (firstn_skipn (Z.to_nat (6 + L)) content). apply in_app_iff. right. exact Hx.
Qed.

#[using="RCEIL LO"] Lemma LO' : lo <= usp - 80 - RFUZZ_STACK.
Proof. unfold RTARGET_RUN_STACK in LO. lia. Qed.

#[using="RBR"] Lemma blocks_LB : forall st ow m, RHEAP st (LBT ow) m -> forall b, In b LB -> rblock_range (blk_addr b) (blk_size b).
Proof. intros st ow m HP b Hb. eapply RBR; [exact HP|]. destruct ow as [[pb P]|]; [right|]; exact Hb. Qed.

#[using="CEIL LO"] Lemma run_exit : forall (sX st : PState) (r : Z) (x1 t0 t1 t2 q8 q9 a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q21 q22 q23 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
0 <= r <= 2 -> frm0 fc -> RHEAP st LB m -> INV0 st m -> AXSTAT true m ->
evt rsegs (POST sX LB AB lo m0 r st)
(MS (mkR x1 SPF gp tpv t0 t1 t2 q8 q9 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q21 q22 q23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c05c) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros Hr FRM HP sfH_ AX; first [ sf_destruct 9%nat sfH_ as [x0 FR] TP SEW SOF [errv ERR] AUX MI ST DPR | sf_fb; destruct sfH_ as ([x0 FR] & TP & SEW & SOF & [errv ERR] & AUX & MI & ST & DPR) ].
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO' as L'. unfold RFUZZ_STACK in L'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
unfold FRAME in FR.
do 10 zstep.
release_frame FR ST (bv_unsigned sp). zstep.
apply evt_done. unfold rtarget_run_post. cbv beta. sf_eexists 16%nat. exists m, errv.
split; [reflexivity|]. split; [exact Hr|]. split; [exact FRM|]. split; [exact MI|]. split; [exact ST|].
split; [unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR|]. split; [exact AUX|]. split; [exact DPR|].
split; [exact HP|]. split; [exact SOF|]. split; [exact SEW| exact AX].
Qed.

#[using="Type"] Lemma INV0_after_heap : forall st st' LX m m' (errv' : word),
INV0 st m ->
rheap_pres LX (usp + -80) m m' -> (forall b, In b LB -> In b LX) ->
ps_so st' = ps_so st ->
rw_cells rsegs m' RERRNO [C4 errv'] -> mem_inv rsegs m' -> stk rsegs m' lo (usp + -80) -> rauxv_ok m' AB ->
INV0 st' m'.
Proof.
intros st st' LX m m' errv' sfH_; first [ sf_destruct 9%nat sfH_ as [x0 FR] TP SEW SOF _ _ _ _ DP0 | sf_fb; destruct sfH_ as ([x0 FR] & TP & SEW & SOF & _ & _ & _ & _ & DP0) ]; intros HP HL ESO ERR' MI' ST' AUX'.
pose proof (heap_pres_agree _ _ _ _ HP) as AG.
split. { exists x0. unfold FRAME in *. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. left. cbn in Ha. lia. }
split; [eapply rtables_pristine_heap_pres; [exact HP| exact TP]|].
split; [eapply stderr_wfile_heap_pres; [exact HP| exact SEW]|].
split; [rewrite ESO; eapply stdout_file_heap_pres; [exact HP| exact SOF]|].
split; [exists errv'; exact ERR'|]. split; [exact AUX'|]. split; [exact MI'|]. split; [exact ST'|].
eapply rdrv_pres_trans; [exact DP0|]. eapply rdrv_pres_of_heap; [exact HP| lia| exact HL].
Qed.

#[using="RFREE RND RBR A cap FC LC CAP L0 L6 SPAB CEIL LO"] Lemma run_free : forall (sX st : PState) ow (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 q19 q20 q21 q23 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
frm0 fc -> INV ow st m -> AXSTAT true m ->
implM rsegs (X1qx.mbind (match obptr ow with Some q => raw_free q | None => mret tt end) (fun _ => mret 0)) st
(POST sX LB AB lo m0)
(MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 (optr ow)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (oreg ow)) q19 q20 q21 (Z_to_bv 64 0) q23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c048) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros FRM (HP & PAYL & IV) AX.
pose proof IV as sfP_; first [ sf_destruct 9%nat sfP_ as [x0 FR] TP SEW SOF [errv ERR] AUX MI ST DPR | sf_fb; destruct sfP_ as ([x0 FR] & TP & SEW & SOF & [errv ERR] & AUX & MI & ST & DPR) ].
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO' as L'. unfold RFUZZ_STACK in L'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof facts as sfP_; first [ sf_destruct 7%nat sfP_ as PL0 PL1 PLEN CR CALLS EP PF | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & CR & CALLS & EP & PF) ].
destruct ow as [[pb P]|]; cbn [obptr oreg optr LBT] in *.
-
pose proof (RBR _ _ _ (pb, P, plen) HP ltac:(left; reflexivity)) as sfP_; first [ sf_destruct 5%nat sfP_ as B1 B2 B3 B4 B5 | sf_fb; destruct sfP_ as (B1 & B2 & B3 & B4 & B5) ]. cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5.
unfold alloc_ceiling in B4.
eapply implM_bind.
{ unfold implM. iprefix. zstep. zstep.
apply evt_done. unfold rfree_stmt in RFREE.
eapply RFREE with (s := st) (LB := (pb, P, plen) :: LB) (p := pb) (A := P) (n := plen) (lo := lo) (B := AB);
try solve [ exact HP | left; reflexivity | exact AUX | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; exact ST | exact CEIL | unfold RFREE_STACK; rewrite unsigned_lit by lia; lia
| exact MI | reflexivity ].
all: try (unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR).
all: match goal with |- ?g => idtac "RFREE-SIDE:" g end. all: fail. }
cbv beta. intros [] st1 ms1 PO.
first [ sf_destruct 25%nat PO as y0 y1 y2 ra2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 m1 -> MI1 ST1 ERR1 AUX1 HP1 EFA ESO H1 | sf_fb; destruct PO as (y0 & y1 & y2 & ra2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m1 & -> & MI1 & ST1 & ERR1 & AUX1 & HP1 & EFA & ESO & H1) ].
rewrite ?unsigned_lit in ST1 by lia. rewrite ?unsigned_lit in HP1 by lia. unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia.
change (RATP + -164) with RERRNO in ERR1 || replace (0x4d450 + -164) with RERRNO in ERR1 by reflexivity.
rewrite (lb_remove_head (pb, P, plen)) in HP1, H1 by (eapply RND; exact HP).
assert (IV1 : INV0 st1 m1).
{ eapply (INV0_after_heap st st1 LB); [exact IV| exact HP1| intros b Hb; exact Hb| exact ESO| exact ERR1| exact MI1| exact ST1| exact AUX1]. }
assert (AX1 : AXSTAT true m1) by (eapply AXSTAT_heap_pres; [exact HP1| exact AX]).
apply implM_ret. replace (ret_pc (Z_to_bv 64 0x1c050)) with (Z_to_bv 64 0x1c050) by (symmetry; rpc).
zstep. zstep. zstep.
eapply (run_exit _ _ 0); [lia| exact FRM| exact H1| exact IV1| exact AX1].
-
apply implM_retb. apply implM_ret.
zstep. zstep.
eapply evt_cut; [eapply rfree_null_spec; reflexivity|]. cbv beta. intros ms' ->.
replace (ret_pc (Z_to_bv 64 0x1c050)) with (Z_to_bv 64 0x1c050) by (symmetry; rpc).
zstep. zstep. zstep.
eapply (run_exit _ _ 0); [lia| exact FRM| exact HP| exact IV| exact AX].
Qed.

Definition OWOK (ow : option (bptr * Z)) : Prop :=
match ow with None => plen = 0 | Some (pb, P) => 0 < plen end.

#[using="RBR sp A cap FC LC CAP L0 L6"] Lemma optr_facts : forall ow st m, OWOK ow -> RHEAP st (LBT ow) m ->
0 < optr ow /\ optr ow mod 16 = 0 /\
((payload <> [] /\ In (fst (match ow with Some x => x | None => (p, 0) end), optr ow, zlength payload) (LBT ow)) \/ (payload = [] /\ optr ow = REMPTY)) /\
match ow with None => True | Some (pb, P) => rblock_range P plen end.
Proof.
intros ow st m OK HP. pose proof facts as sfP_; first [ sf_destruct 4%nat sfP_ as PL0 PL1 PLEN _ | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & _) ].
destruct ow as [[pb P]|]; cbn [optr OWOK LBT fst] in *.
- pose proof (RBR _ _ _ (pb, P, plen) HP ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as B1 B2 B3 B4 B5 | sf_fb; destruct sfP_ as (B1 & B2 & B3 & B4 & B5) ].
split; [exact B1|]. split; [exact B2|]. split; [| exact BR]. left. split.
+ intros E. rewrite E in PLEN. unfold zlength in PLEN. cbn [length Z.of_nat] in PLEN. lia.
+ rewrite PLEN. left. reflexivity.
- split; [unfold REMPTY; lia|]. split; [reflexivity|]. split; [| exact I]. right. split; [| reflexivity].
destruct payload; [reflexivity|]. exfalso. unfold zlength in PLEN. cbn [length] in PLEN. lia.
Qed.

#[using="RBR p A cap FC LC CAP L0 L6 SPAB ABB CEIL LO"] Lemma INV_after_harness : forall ow st st' m m' (errv' : word),
OWOK ow -> INV ow st m ->
pres_except rsegs (rclient_addr (LBT ow) (usp + -80)) rharness_X m m' ->
RHEAP st' (LBT ow) m' -> stderr_wfile m' -> ps_so st' = ps_so st ->
rw_cells rsegs m' RERRNO [C4 errv'] -> mem_inv rsegs m' -> stk rsegs m' lo (usp + -80) -> rauxv_ok m' AB ->
INV ow st' m'.
Proof.
intros ow st st' m m' errv' OK (HP & PAYL & ([x0 FR] & TP & SEW & SOF & _ & _ & _ & _ & DP0)) PE HP' SEW' ESO ERR' MI' ST' AUX'.
pose proof (pres_except_agree _ _ _ _ _ PE) as AG.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO' as L'. unfold RFUZZ_STACK in L'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (optr_facts ow st m OK HP) as sfP_; first [ sf_destruct 4%nat sfP_ as O1 O2 O3 O4 | sf_fb; destruct sfP_ as (O1 & O2 & O3 & O4) ].
pose proof facts as sfP_; first [ sf_destruct 4%nat sfP_ as PL0 PL1 PLEN _ | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & _) ].
split; [exact HP'|]. split.
{ destruct ow as [[pb P]|]; cbn [optr OWOK LBT] in *.
- first [ sf_destruct 5%nat O4 as B1 B2 B3 B4 B5 | sf_fb; destruct O4 as (B1 & B2 & B3 & B4 & B5) ]. unfold alloc_ceiling in B4.
eapply bytes_at_agree; [exact AG| exact PAYL|]. intros a Ha. unfold to_bytes in Ha. rewrite length_map in Ha. unfold zlength in PLEN.
split; [lia|]. split.
+ right; right. exists (pb, P, plen). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
+ unfold rharness_X. cbn. lia.
- assert (E : payload = []) by (destruct payload; [reflexivity| unfold zlength in PLEN; cbn [length] in PLEN; lia]).
rewrite E. split; [unfold REMPTY; lia|]. split; [cbn; unfold REMPTY; lia|]. intros i Hi. cbn in Hi. lia. }
split. { exists x0. unfold FRAME in *. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. cbn in Ha. split; [lia|]. split; [left; lia|]. unfold rharness_X. cbn. lia. }
split. { eapply rtables_pristine_pres_except; [exact PE| | exact TP]. unfold rharness_X, RTABLES_LO, RTABLES_HI. cbn. lia. }
split; [exact SEW'|].
split. { rewrite ESO. eapply stdout_file_pres_except; [exact PE| | exact SOF]. unfold rharness_X, stdout_addr. cbn. lia. }
split; [exists errv'; exact ERR'|]. split; [exact AUX'|]. split; [exact MI'|]. split; [exact ST'|].
eapply rdrv_pres_trans; [exact DP0|]. eapply rdrv_pres_of_harness; [exact PE| lia|]. intros b Hb. destruct ow as [[pb P]|]; [right|]; exact Hb.
Qed.

Definition WEMIT : list (Z * Z) := [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)].

#[using="RHF RBR p A cap FC LC CAP L0 L6 SPAB CEIL LO"] Lemma INV_after_emit : forall ow st st' m m',
OWOK ow -> INV ow st m ->
munch WEMIT m m' -> wmono rsegs m m' ->
ps_m st' = ps_m st -> ps_brk st' = ps_brk st -> ps_hdr st' = ps_hdr st ->
stdout_file m' (ps_so st') -> mem_inv rsegs m' -> stk rsegs m' lo (usp + -80) ->
INV ow st' m'.
Proof.
intros ow st st' m m' OK (HP & PAYL & ([x0 FR] & TP & SEW & SOF & [errv ERR] & AUX & MI & ST & DP0)) MU WM E1 E2 E3 SOF' MI' ST'.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO' as L'. unfold RFUZZ_STACK in L'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof facts as sfP_; first [ sf_destruct 4%nat sfP_ as PL0 PL1 PLEN _ | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & _) ].
pose proof (optr_facts ow st m OK HP) as sfP_; first [ sf_destruct 4%nat sfP_ as O1 O2 O3 O4 | sf_fb; destruct sfP_ as (O1 & O2 & O3 & O4) ].
unfold WEMIT in MU.
split.
{ eapply RHEAP_ext; [| exact E1| exact E2| exact E3]. eapply RHF; [exact HP| exact MU| exact WM|].
unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
split.
{ destruct ow as [[pb P]|]; cbn [optr OWOK LBT] in *.
- first [ sf_destruct 5%nat O4 as B1 B2 B3 B4 B5 | sf_fb; destruct O4 as (B1 & B2 & B3 & B4 & B5) ]. unfold alloc_ceiling in B4.
eapply bytes_at_transport; [exact PAYL| exact MU|]. unfold to_bytes. rewrite length_map. unfold zlength in PLEN. cbn [disjoint_from fst snd]. lia.
- assert (E : payload = []) by (destruct payload; [reflexivity| unfold zlength in PLEN; cbn [length] in PLEN; lia]).
rewrite E. split; [unfold REMPTY; lia|]. split; [cbn; unfold REMPTY; lia|]. intros i Hi. cbn in Hi. lia. }
split. { exists x0. unfold FRAME in *. eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. lia. }
split. { eapply rtables_pristine_munch; [exact MU| exact WM| | exact TP]. unfold RTABLES_LO, RTABLES_HI. cbn. lia. }
split. { eapply stderr_wfile_munch; [exact MU| exact WM| | exact SEW]. unfold stderr_addr. cbn. lia. }
split; [exact SOF'|].
split. { exists errv. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. unfold RERRNO. cbn [cells_size csize Nat.add disjoint_from fst snd]. lia. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
split; [exact MI'|]. split; [exact ST'|].
eapply rdrv_pres_trans; [exact DP0|]. eapply rdrv_pres_of_munch; [exact MU| exact WM| | exact (blocks_LB _ _ _ HP)| lia].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [left; lia| right; left; cbn; tauto| right; left; cbn; tauto].
Qed.

#[using="RHF RBR p A cap FC LC CAP L0 L6 SPAB CEIL LO"] Lemma INV_after_incb : forall ow st m m',
OWOK ow -> INV ow st m -> munch [(RAEF_INCB, RAEF_INCB + 1)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
INV ow st m'.
Proof.
intros ow st m m' OK (HP & PAYL & ([x0 FR] & TP & SEW & SOF & [errv ERR] & AUX & MI & ST & DP0)) MU WM MI'.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO' as L'. unfold RFUZZ_STACK in L'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof facts as sfP_; first [ sf_destruct 4%nat sfP_ as PL0 PL1 PLEN _ | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & _) ].
pose proof (optr_facts ow st m OK HP) as sfP_; first [ sf_destruct 4%nat sfP_ as O1 O2 O3 O4 | sf_fb; destruct sfP_ as (O1 & O2 & O3 & O4) ].
unfold RAEF_INCB in MU.
split.
{ eapply RHF; [exact HP| exact MU| exact WM|]. unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED, alloc_ceiling.
constructor; [cbn [fst snd]; lia| constructor]. }
split.
{ destruct ow as [[pb P]|]; cbn [optr OWOK LBT] in *.
- first [ sf_destruct 5%nat O4 as B1 B2 B3 B4 B5 | sf_fb; destruct O4 as (B1 & B2 & B3 & B4 & B5) ]. unfold alloc_ceiling in B4.
eapply bytes_at_transport; [exact PAYL| exact MU|]. unfold to_bytes. rewrite length_map. unfold zlength in PLEN. cbn [disjoint_from fst snd]. lia.
- assert (E : payload = []) by (destruct payload; [reflexivity| unfold zlength in PLEN; cbn [length] in PLEN; lia]).
rewrite E. split; [unfold REMPTY; lia|]. split; [cbn; unfold REMPTY; lia|]. intros i Hi. cbn in Hi. lia. }
split. { exists x0. unfold FRAME in *. eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. lia. }
split. { eapply rtables_pristine_munch; [exact MU| exact WM| | exact TP]. unfold RTABLES_LO, RTABLES_HI. cbn. lia. }
split. { eapply stderr_wfile_munch; [exact MU| exact WM| | exact SEW]. unfold stderr_addr. cbn. lia. }
split. { eapply stdout_file_munch; [exact MU| exact WM| | exact SOF]. unfold stdout_addr. cbn. lia. }
split. { exists errv. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. unfold RERRNO. cbn [cells_size csize Nat.add disjoint_from fst snd]. lia. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
split; [exact MI'|].
split. { eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn [disjoint_from fst snd]. lia. }
eapply rdrv_pres_trans; [exact DP0|]. eapply rdrv_pres_of_munch; [exact MU| exact WM| | exact (blocks_LB _ _ _ HP)| lia].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; left. unfold rdrv_X, RAEF_INCB. cbn. tauto.
Qed.

#[using="RFREE EMIT FWXO FUZZ RHF RND RBR p A cap FC LC CAP L0 L6 SPAB ABB CEIL LO SP16"] Lemma run_loop : forall (n : nat) sX ow (rc0 : Z) (q3 : word) st ms,
Z.of_nat n <= 4 -> (0 < n)%nat -> OWOK ow ->
RUNST ow RLOOP (Z.of_nat n) q3 st ms ->
implM rsegs (X1qx.mbind (run_calls io_emit fuzz_one n payload rc0)
(fun rc => X1qx.mbind (match obptr ow with Some q => raw_free q | None => mret tt end) (fun _ => mret (if rc =? 0 then 0 else 1))))
st (POST sX LB AB lo m0) ms.
Proof.
induction n as [|n IH]; intros sX ow rc0 q3 st ms Hn Hpos OK RS; [lia|].
first [ sf_destruct 23%nat RS as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m -> FRM IV AX | sf_fb; destruct RS as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & IV & AX) ].
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO' as L'. unfold RFUZZ_STACK in L'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof facts as sfP_; first [ sf_destruct 7%nat sfP_ as PL0 PL1 PLEN CR CALLS EP PF | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & CR & CALLS & EP & PF) ].
pose proof IV as (HP & PAYL & IV0).
pose proof (optr_facts ow st m OK HP) as sfP_; first [ sf_destruct 4%nat sfP_ as O1 O2 O3 O4 | sf_fb; destruct sfP_ as (O1 & O2 & O3 & O4) ].
pose proof IV0 as sfP_; first [ sf_destruct 9%nat sfP_ as _ _ _ _ _ _ MI _ _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & MI & _ & _) ].
destruct AX as [INC [AXR AX0]]. unfold RAEF_INCB, RATEXIT, RATEXIT_A0, RAEF_GUARD, RATEXIT_CALL, ax_cells in INC, AXR, AX0. cbn [Z.add] in AXR. ua.
pose proof (munch_refl [(RAEF_INCB, RAEF_INCB + 1)] m) as MU. pose proof (wmono_refl rsegs m) as WM. unfold RAEF_INCB in MU.
cbn [run_calls]. apply implM_bind_assoc.
unfold RINITIALIZED. unfold implM. iprefix.
zstep. zstep. rewrite (le1_small 1) by lia. mem_after_store.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (IVB : INV ow st mx) by (eapply INV_after_incb; [exact OK| exact IV| exact MU| exact WM| exact MI]) end.
clear MU WM.
pose proof IVB as (HPB & PAYLB & ([xB FRB] & TPB & SEWB & SOFB & [errvB ERRB] & AUXB & MIB & STB & DPRB)).
zstep. zstep. zstep.
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st (POST sX LB AB lo m0) msx) end.
eapply implM_bind.
{ eapply (implM_mall _ (fun r => r = 0)); [apply fuzz_one_ret0|].
unfold harness_stmt in FUZZ.
eapply FUZZ with (LB := LBT ow) (pb := fst (match ow with Some x => x | None => (p, 0) end)) (P := optr ow) (B := AB) (lo := lo) (errv := errvB);
rewrite ?(unsigned_lit (usp + -80)) by lia.
all: first [ exact HPB | exact PAYLB | exact PF | exact O1 | exact O2 | exact O3 | exact TPB | exact SEWB | exact AUXB | exact STB | exact CEIL
| exact MIB | exact FRM | reflexivity | rewrite PLEN; reflexivity
| unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERRB
| unfold RFUZZ_STACK; lia | lia
| clear -SP16 SPR; Z.div_mod_to_equations; lia ].
all: match goal with |- ?g => idtac "FUZZ-SIDE:" g end. all: fail. }
cbv beta. intros r st1 ms1 [PO R0]. subst r.
first [ sf_destruct 29%nat PO as u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 m2 errv1 -> Hr FRM1 MI1 ST1 ERR1 AUX1 PE HP1 SEW1 ESO | sf_fb; destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & errv1 & -> & Hr & FRM1 & MI1 & ST1 & ERR1 & AUX1 & PE & HP1 & SEW1 & ESO) ].
rewrite ?(unsigned_lit (usp + -80)) in ST1 by lia. rewrite ?(unsigned_lit (usp + -80)) in PE by lia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia. change (0x4d450 + -164) with RERRNO in ERR1.
assert (IV2 : INV ow st1 m2).
{ eapply INV_after_harness; [exact OK| exact IVB| exact PE| exact HP1| exact SEW1| exact ESO| exact ERR1| exact MI1| exact ST1| exact AUX1]. }
pose proof (ax_cell_harness _ _ _ _ _ _ PE INC ltac:(intros x Hx; cbn in Hx; unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0; lia)) as INC2.
pose proof (ax_cell_harness _ _ _ _ _ _ PE AXR ltac:(intros x Hx; cbn in Hx; unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0; lia)) as AXR2.
pose proof (ax_cell_harness _ _ _ _ _ _ PE AX0 ltac:(intros x Hx; cbn in Hx; unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0; lia)) as AX02.
clear INC AXR AX0. rename INC2 into INC. rename AXR2 into AXR. rename AX02 into AX0.
replace (ret_pc (Z_to_bv 64 0x1c024)) with (Z_to_bv 64 0x1c024) by (symmetry; rpc).
apply implM_bind_assoc.
pose proof (munch_refl [(RAEF_INCB, RAEF_INCB + 1)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM. unfold RAEF_INCB in MU.
unfold implM. iprefix.
zstep. zstep. try rewrite (le1_small 0) by lia. mem_after_store.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (IV3 : INV ow st1 mx) by (eapply INV_after_incb; [exact OK| exact IV2| exact MU| exact WM| exact MI1]);
assert (AX3 : AXSTAT true mx) by (unfold AXSTAT, RAEF_INCB, RATEXIT, RATEXIT_A0, RAEF_GUARD, RATEXIT_CALL, ax_cells; cbn [Z.add]; split; [exact INC| split; [exact AXR| exact AX0]]) end.
clear MU WM.
zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st1 (POST sX LB AB lo m0) msx) end.
pose proof IV3 as (HPa & PAYLa & ([x0a FRa] & TPa & SEWa & SOFa & [errva ERRa] & AUXa & MIa & STa & DPRa)).
eapply implM_bind.
{ apply (implM_keepsf rsegs (fun s => set_so_ps stdout_init s)); [| apply io_emit_keeps].
unfold io_emit. unfold emit_printf_stmt in EMIT.
eapply EMIT with (lo := lo) (canary := run_canary); rewrite ?(unsigned_lit (usp + -80)) by lia.
all: first [ intros; reflexivity | exact FWXO | exact SOFa | exact Hr | apply mod32_of_lit; exact Hr | exact STa
| apply (RHEAP_ssp _ _ _ HPa) | exact MIa | exact FRM1
| unfold EMIT_DEPTH; lia | unfold GLOBALS_TOP; lia | lia ].
all: match goal with |- ?g => idtac "EMIT-SIDE:" g end. all: fail. }
cbv beta. intros [] st2 ms2 [PO KE].
first [ sf_destruct 27%nat PO as v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 Ft fc2 m4 -> MU WM MI2 FRM2 FOK ST2 SOF2 SSP2 | sf_fb; destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & Ft & fc2 & m4 & -> & MU & WM & MI2 & FRM2 & FOK & ST2 & SOF2 & SSP2) ].
rewrite ?(unsigned_lit (usp + -80)) in MU by lia. rewrite ?(unsigned_lit (usp + -80)) in ST2 by lia.
pose proof (set_so_ps_eq _ _ _ KE) as sfP_; first [ sf_destruct 4%nat sfP_ as Em Ebrk Efa Ehdr | sf_fb; destruct sfP_ as (Em & Ebrk & Efa & Ehdr) ].
assert (IV4 : INV ow st2 m4).
{ eapply INV_after_emit; [exact OK| exact IV3| exact MU| exact WM| exact Em| exact Ebrk| exact Ehdr| exact SOF2| exact MI2| exact ST2]. }
assert (AX4 : AXSTAT true m4).
{ eapply AXSTAT_munch; [exact MU| exact WM| | exact AX3]. intros a Ha. unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0 in Ha. cbn. lia. }
replace (ret_pc (Z_to_bv 64 0x1c034)) with (Z_to_bv 64 0x1c034) by (symmetry; rpc).

unfold implM. iprefix.
zstep. zstep. if_true.
zstep.
rewrite swrap32_small by lia. replace (Z.of_nat (S n) + -1) with (Z.of_nat n) by lia.
zstep. if_cases K; zify_cond K.
all: first
[
assert (n = 0%nat) by (rewrite ?unsigned_lit in K by lia; lia); subst n; cbn [run_calls];
apply evt_done;
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st2 (POST sX LB AB lo m0) msx) end;
apply implM_retb;
eapply run_free; [exact FRM2| exact IV4| exact AX4]
|
assert (0 < n)%nat by (rewrite ?unsigned_lit in K by lia; lia);
apply evt_done;
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st2 (POST sX LB AB lo m0) msx) end;
eapply (IH sX ow 0 _ st2); [lia| assumption| exact OK|];
unfold RUNST; sf_eexists 16%nat; first [ unshelve sf_eexists 3%nat; [ exact (Ft) | exact (fc2) | exact (m4) | ] | sf_fb; exists Ft, fc2, m4 ]; split; [reflexivity|]; split; [exact FRM2|]; split; [exact IV4| exact AX4] ].
Qed.

#[using="RCEIL sp"] Lemma got_fuzzinit_of_pristine : forall m, rtables_pristine m -> rw_cells rsegs m RGOT_FUZZINIT [C8 (Z_to_bv 64 0)].
Proof.
intros m TP. unfold RGOT_FUZZINIT.
apply (X0pw.rw_cells_recast rsegs m 0x3c028 [CB 8%nat (cells_bytes [C8 (Z_to_bv 64 0)])] [C8 (Z_to_bv 64 0)]).
- apply (X0pw.rw_cells_image0 rsegs m 0x3c028 (cells_bytes [C8 (Z_to_bv 64 0)])).
+ intros a Ha. replace (Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 0)]))) with 8 in Ha by reflexivity. apply TP. unfold RTABLES_LO, RTABLES_HI. lia.
+ vm_compute. reflexivity.
+ lia.
+ replace (Z.of_nat (length (cells_bytes [C8 (Z_to_bv 64 0)]))) with 8 by reflexivity. lia.
- cbn. repeat split; exact I.
- vm_compute. reflexivity.
- reflexivity.
Qed.

#[using="RCEIL sp L0 L6"] Lemma payload_bytes : forall m, bytes_at rsegs m A (zbytes content) -> bytes_at rsegs m PAY (zbytes payload).
Proof.
intros m CT. unfold PAY, payload, zbytes in *. rewrite <- skipn_map.
rewrite <- (firstn_skipn (Z.to_nat (6 + L)) (map (Z_to_bv 8) content)) in CT.
apply bytes_at_app in CT. destruct CT as [_ X]. rewrite length_firstn, length_map in X.
unfold zlength in L6. replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length content))) with (A + 6 + L) in X by lia. exact X.
Qed.

Definition TPFX : M PState (option (option bptr)) :=
let payload_len := zlength payload in
if payload_len =? 0 then mret (Some None)
else p <- raw_malloc payload_len ;; mret (match p with Some q => Some (Some q) | None => None end).

Definition PPOST (sX : PState) (o : option (option bptr)) (st : PState) (ms : machine_state) : Prop :=
match o with
| None => evt rsegs (POST sX LB AB lo m0 2 st) ms
| Some ob => exists ow q3, obptr ow = ob /\ OWOK ow /\ RUNST ow RLOOP calls q3 st ms
end.

#[using="A cap FC LC CAP L0 L6 CEIL LO"] Lemma run_from_empty_prefix : forall (sX st : PState) (x1 t0 t1 t2 q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q22 q23 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
plen = 0 -> frm0 fc -> RHEAP st LB m -> INV0 st m -> AXSTAT true m ->
implM rsegs TPFX st (PPOST sX)
(MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 (Z_to_bv 64 RINITIALIZED) (Z_to_bv 64 calls) q22 q23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c000) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros PZ FRM HP IV0 AX.
pose proof facts as sfP_; first [ sf_destruct 7%nat sfP_ as PL0 PL1 PLEN CR CALLS EP PF | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & CR & CALLS & EP & PF) ].
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO' as L'. unfold RFUZZ_STACK in L'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
unfold TPFX. rewrite PLEN. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; exact PZ).
apply implM_ret. cbv beta iota delta [PPOST].
zstep. zstep. zstep. zstep. apply evt_done. cbv beta.
exists None, q19. split; [reflexivity|]. split; [exact PZ|].
unfold RUNST. sf_eexists 16%nat. first [ unshelve sf_eexists 3%nat; [ exact (F) | exact (fc) | exact (m) | ] | sf_fb; exists F, fc, m ]. cbn [optr oreg LBT].
split; [unfold REMPTY, RINITIALIZED, RLOOP; reflexivity|].
split; [exact FRM|]. split; [| exact AX]. split; [exact HP|]. split; [| exact IV0].
assert (E : payload = []) by (destruct payload; [reflexivity| unfold zlength in PLEN; cbn [length] in PLEN; lia]).
rewrite E. cbn [optr to_bytes map]. unfold REMPTY. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

#[using="RMALLOC RHF RND RBD RBR p cap INLB FC LC CAP L0 L6 SPAB CEIL LO"] Lemma run_from_malloc_prefix : forall (sX st : PState) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q22 q23 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
0 < plen -> frm0 fc -> RHEAP st LB m -> bytes_at rsegs m A (zbytes content) -> INV0 st m -> AXSTAT true m ->
implM rsegs TPFX st (PPOST sX)
(MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 PAY) a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 (Z_to_bv 64 RINITIALIZED) (Z_to_bv 64 calls) q22 q23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1bfb4) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros PP FRM HP CT IV0 AX.
pose proof IV0 as sfP_; first [ sf_destruct 9%nat sfP_ as [x0 FR] TP SEW SOF [errv ERR] AUX MI ST DPR | sf_fb; destruct sfP_ as ([x0 FR] & TP & SEW & SOF & [errv ERR] & AUX & MI & ST & DPR) ].
pose proof facts as sfP_; first [ sf_destruct 7%nat sfP_ as PL0 PL1 PLEN CR CALLS EP PF | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & CR & CALLS & EP & PF) ].
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO' as L'. unfold RFUZZ_STACK in L'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (RBR _ _ _ (p, A, cap) HP INLB) as sfP_; first [ sf_destruct 5%nat sfP_ as BA1 BA2 BA3 BA4 BA5 | sf_fb; destruct sfP_ as (BA1 & BA2 & BA3 & BA4 & BA5) ]. cbn [blk_addr blk_size fst snd] in BA1, BA2, BA3, BA4, BA5. unfold alloc_ceiling in BA4.
unfold TPFX. rewrite PLEN. replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
unfold implM. iprefix. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st (PPOST sX) msx) end.
eapply implM_bind.
{ unfold rmalloc_stmt in RMALLOC.
eapply RMALLOC with (lo := lo) (B := AB); try reflexivity; unfold RATP, RERRNO in *; rewrite ?(unsigned_lit 316496) by lia; rewrite ?(unsigned_lit (usp + -80)) by lia;
first [ exact HP | exact AUX | exact ST | exact ERR | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
cbv beta. intros r st1 ms1 PO.
first [ sf_destruct 26%nat PO as u0 u1 u2 ra0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 errv1 -> MI1 ST1 ERR1 AUX1 HPR FAE SOE RR | sf_fb; destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR) ].
unfold RATP in ERR1. rewrite ?(unsigned_lit 316496) in ERR1 by lia. change (316496 + -164) with RERRNO in ERR1.
rewrite ?(unsigned_lit (usp + -80)) in ST1 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR by lia.
replace (ret_pc (Z_to_bv 64 0x1bfbc)) with (Z_to_bv 64 0x1bfbc) by (symmetry; rpc).
assert (CT1 : bytes_at rsegs m1 A (zbytes content)).
{ eapply rheap_pres_bytes_at; [exact HPR| exact CT|]. right; right. exists (p, A, cap). split; [exact INLB|]. cbn [blk_addr blk_size fst snd]. rewrite zbytes_length. unfold zlength in *. lia. }
destruct r as [pb|].
2:{
destruct RR as [-> HEAP1].
assert (IV1 : INV0 st1 m1) by (eapply (INV0_after_heap st st1 LB); [exact IV0| exact HPR| intros b Hb; exact Hb| exact SOE| exact ERR1| exact MI1| exact ST1| exact AUX1]).
assert (AX1 : AXSTAT true m1) by (eapply AXSTAT_heap_pres; [exact HPR| exact AX]).
apply implM_ret. apply evt_done. cbn [PPOST].
zstep. if_true. zstep. zstep.
eapply run_exit; [lia| exact FRM| exact HEAP1| exact IV1| exact AX1]. }

first [ sf_destruct 8%nat RR as A' junk -> BR' HEAP1 NBLK HEXP _ | sf_fb; destruct RR as (A' & junk & -> & BR' & HEAP1 & NBLK & HEXP & _) ].
pose proof BR' as sfP_; first [ sf_destruct 5%nat sfP_ as BQ1 BQ2 BQ3 BQ4 BQ5 | sf_fb; destruct sfP_ as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5) ]. unfold alloc_ceiling in BQ4.
assert (DISJ : A' + plen <= A \/ A + cap <= A').
{ pose proof (RBD _ _ _ (pb, A', plen) (p, A, cap) HEAP1 ltac:(left; reflexivity) ltac:(right; exact INLB)) as D.
cbn [blk_id blk_addr blk_size fst snd] in D. apply D.
pose proof (RND _ _ _ HEAP1) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite E.
apply in_map_iff. exists (p, A, cap). split; [reflexivity| exact INLB]. }
assert (IV1 : INV0 st1 m1) by (eapply (INV0_after_heap st st1 LB); [exact IV0| exact HPR| intros b Hb; exact Hb| exact SOE| exact ERR1| exact MI1| exact ST1| exact AUX1]).
assert (AX1 : AXSTAT true m1) by (eapply AXSTAT_heap_pres; [exact HPR| exact AX]).
pose proof IV1 as sfP_; first [ sf_destruct 9%nat sfP_ as [x0' FR1] TP1 SEW1 SOF1 [errv1' ERR1'] AUX1' _ _ DPR1 | sf_fb; destruct sfP_ as ([x0' FR1] & TP1 & SEW1 & SOF1 & [errv1' ERR1'] & AUX1' & _ & _ & DPR1) ].
apply implM_ret. cbv beta iota delta [PPOST].
zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
zstep. zstep. zstep. zstep.

pose proof (payload_bytes m1 CT1) as SRC.
eapply evt_cut.
{ eapply memcpy_callv with (src := zbytes payload) (junk := junk);
[exact SRC| rewrite zbytes_length; unfold zlength in PLEN; lia| lia| lia| unfold PAY, plen in *; unfold zlength in *; lia| exact NBLK| unfold PAY, plen in *; unfold zlength in *; lia| exact MI1]. }
cbv beta. intros ms' PO.
first [ sf_destruct 21%nat PO as v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 m2 -> MUc WMc MI2 NB _ | sf_fb; destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB & _) ].
ua.
replace (ret_pc (Z_to_bv 64 0x1bfd0)) with (Z_to_bv 64 0x1bfd0) by (symmetry; rpc).
assert (IV2 : INV (Some (pb, A')) st1 m2).
{ split.
{ eapply RHF; [exact HEAP1| exact MUc| exact WMc|]. constructor; [| constructor]. right; right. exists (pb, A', plen). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia. }
split.
{ cbn [optr]. apply rw_cells_bytes_at in NB. cbn [cells_bytes cbytes app] in NB. rewrite app_nil_r in NB. exact NB. }
split. { exists x0'. unfold FRAME in *. eapply rw_cells_transport; [exact FR1| exact MUc| exact WMc|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. lia. }
split. { eapply rtables_pristine_munch; [exact MUc| exact WMc| | exact TP1]. unfold RTABLES_LO, RTABLES_HI. cbn. lia. }
split. { eapply stderr_wfile_munch; [exact MUc| exact WMc| | exact SEW1]. unfold stderr_addr. cbn. lia. }
split. { eapply stdout_file_munch; [exact MUc| exact WMc| | exact SOF1]. unfold stdout_addr. cbn. lia. }
split. { exists errv1'. eapply rw_cells_transport; [exact ERR1'| exact MUc| exact WMc|]. unfold RERRNO. cbn [cells_size csize Nat.add disjoint_from fst snd]. lia. }
split. { eapply rauxv_ok_frame; [exact AUX1'| exact MUc| exact WMc|]. unfold RAUXV_CELL. constructor; [cbn [fst snd]; lia| constructor]. }
split; [exact MI2|].
split. { eapply stk_transport_disjoint; [exact ST1| exact MUc| exact WMc|]. cbn [disjoint_from fst snd]. lia. }
eapply rdrv_pres_trans; [exact DPR1|]. eapply rdrv_pres_of_munch; [exact MUc| exact WMc| | exact (blocks_LB _ (Some (pb, A')) _ HEAP1)| lia].
constructor; [| constructor]. right; right. cbn [fst snd]. split; [unfold alloc_ceiling; lia|]. split; [lia|].
intros b Hb. pose proof (RBD _ _ _ (pb, A', plen) b HEAP1 ltac:(left; reflexivity) ltac:(right; exact Hb)) as D.
cbn [blk_id blk_addr blk_size fst snd] in D.
assert (NE : pb <> blk_id b).
{ pose proof (RND _ _ _ HEAP1) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite E. apply in_map. exact Hb. }
destruct (D NE); lia. }
assert (AX2 : AXSTAT true m2).
{ eapply AXSTAT_munch; [exact MUc| exact WMc| | exact AX1]. intros a Ha. unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0 in Ha. cbn. lia. }

zstep. zstep. zstep. zstep. apply evt_done. cbv beta.
exists (Some (pb, A')), q19. split; [reflexivity|]. split; [exact PP|].
unfold RUNST. sf_eexists 16%nat. first [ unshelve sf_eexists 3%nat; [ exact (F) | exact (fc) | exact (m2) | ] | sf_fb; exists F, fc, m2 ]. cbn [optr oreg LBT].
split; [unfold RLOOP; reflexivity|].
split; [exact FRM|]. split; [exact IV2| exact AX2].
Qed.

#[using="RMALLOC RHF RND RBD RBR p cap INLB FC LC CAP L0 L6 SPAB CEIL LO"] Lemma run_entry_prefix : forall (sX : PState) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (st : PState) (errv : word),
RHEAP st LB m0 -> bytes_at rsegs m0 A (zbytes content) ->
rauxv_ok m0 AB -> stk rsegs m0 lo usp -> rw_cells rsegs m0 RERRNO [C4 errv] -> mem_inv rsegs m0 -> frm0 fc ->
stdout_file m0 (ps_so st) -> stderr_wfile m0 -> rw_cells rsegs m0 RINITIALIZED [C1 (Z_to_bv 8 0)] -> rtables_pristine m0 ->
AXSTAT false m0 ->
a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 (A + 6 + L) -> a3 = Z_to_bv 64 (zlength content - 6 - L) ->
implM rsegs TPFX st (PPOST sX)
(MS (mkR ra sp gp tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RTARGET_RUN) fc None m0 (seg_rom rsegs)).
Proof.
intros until errv. intros HP CT AUX ST ERR MI FRM SOF SEW INI TP AXF -> -> -> ->.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO' as L'. unfold RFUZZ_STACK in L'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof facts as sfP_; first [ sf_destruct 7%nat sfP_ as PL0 PL1 PLEN CR CALLS EP PF | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & CR & CALLS & EP & PF) ].
pose proof (RBR _ _ _ (p, A, cap) HP INLB) as sfP_; first [ sf_destruct 5%nat sfP_ as BA1 BA2 BA3 BA4 BA5 | sf_fb; destruct sfP_ as (BA1 & BA2 & BA3 & BA4 & BA5) ]. cbn [blk_addr blk_size fst snd] in BA1, BA2, BA3, BA4, BA5. unfold alloc_ceiling in BA4.
unfold RINITIALIZED in INI. unfold RERRNO in ERR.
pose proof (munch_refl [(usp - 80, usp); (RINITIALIZED, RINITIALIZED + 1)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold RINITIALIZED in MU.
change (id (bytes_at rsegs m0 A (zbytes content))) in CT.
change (id (AXSTAT false m0)) in AXF.
apply implM_enter.
unfold RTARGET_RUN.
zstep. carve_frame 80%nat ST.
do 9 zstep.

do 8 zstep. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; cbn in K0; lia]. clear K0.

zstep. zstep. rewrite (le1_small 1) by lia. mem_after_store.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mA := mx) in * end.
assert (HP1 : RHEAP st LB mA).
{ eapply RHF; [exact HP| exact MU| exact WM|]. unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED, alloc_ceiling.
constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (CT1 : bytes_at rsegs mA A (zbytes content)).
{ unfold id in CT. eapply bytes_at_transport; [exact CT| exact MU|]. rewrite zbytes_length. unfold zlength in *. cbn [disjoint_from fst snd]. lia. }
assert (IV1 : INV0 st mA).
{ split; [eexists; exact FR|].
split. { eapply rtables_pristine_munch; [exact MU| exact WM| | exact TP]. unfold RTABLES_LO, RTABLES_HI. cbn. lia. }
split. { eapply stderr_wfile_munch; [exact MU| exact WM| | exact SEW]. unfold stderr_addr. cbn. lia. }
split. { eapply stdout_file_munch; [exact MU| exact WM| | exact SOF]. unfold stdout_addr. cbn. lia. }
split. { exists errv. first [exact ERR | eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]; unfold RERRNO; cbn [cells_size csize Nat.add disjoint_from fst snd]; lia]. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
split; [assumption|]. split; [exact ST|].
eapply rdrv_pres_of_munch; [exact MU| exact WM| | exact (blocks_LB _ None _ HP)| lia].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [left; lia| right; left; unfold RINITIALIZED; cbn; tauto]. }
assert (AXA : AXSTAT false mA).
{ unfold id in AXF. eapply AXSTAT_munch; [exact MU| exact WM| | exact AXF]. intros a Ha. unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0 in Ha. cbn. lia. }
replace (zlength content - 6 - L) with plen by reflexivity. replace (A + 6 + L) with PAY by reflexivity.
clearbody mA. clear MU WM.
destruct (RHEAP_libc_head _ _ _ HP1) as (cdt & thr & sec & tm1 & LCH).
pose proof IV1 as sfP_; first [ sf_destruct 9%nat sfP_ as [x0A FRA] TPA SEWA SOFA [errvA ERRA] AUXA MIA STA DPRA | sf_fb; destruct sfP_ as ([x0A FRA] & TPA & SEWA & SOFA & [errvA ERRA] & AUXA & MIA & STA & DPRA) ].

zstep. zstep. zstep.
eapply evt_cut.
{ eapply atexit_guard_spec with (lo := lo) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1);
rewrite ?(unsigned_lit (usp + -80)) by lia;
first [ exact STA | exact LCH | exact AXA | exact MIA | reflexivity | lia ]. }
cbv beta. intros ms' PO. unfold atexit_guard_post in PO.
first [ sf_destruct 21%nat PO as z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 mX -> MU1 WM1 MI1 ST1 AX1 | sf_fb; destruct PO as (z0 & z1 & z2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & mX & -> & MU1 & WM1 & MI1 & ST1 & AX1) ].
rewrite ?(unsigned_lit (usp + -80)) in MU1, ST1 by lia. unfold RATEXIT, RATEXIT_A0 in MU1.
assert (HP2 : RHEAP st LB mX).
{ eapply RHF; [exact HP1| exact MU1| exact WM1|]. unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED, alloc_ceiling.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
assert (CT2 : bytes_at rsegs mX A (zbytes content)).
{ eapply bytes_at_transport; [exact CT1| exact MU1|]. rewrite zbytes_length. unfold zlength in *. cbn [disjoint_from fst snd]. lia. }
assert (IV2 : INV0 st mX).
{ split. { exists x0A. unfold FRAME in *. eapply rw_cells_transport; [exact FRA| exact MU1| exact WM1|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. lia. }
split. { eapply rtables_pristine_munch; [exact MU1| exact WM1| | exact TPA]. unfold RTABLES_LO, RTABLES_HI. cbn. lia. }
split. { eapply stderr_wfile_munch; [exact MU1| exact WM1| | exact SEWA]. unfold stderr_addr. cbn. lia. }
split. { eapply stdout_file_munch; [exact MU1| exact WM1| | exact SOFA]. unfold stdout_addr. cbn. lia. }
split. { exists errvA. eapply rw_cells_transport; [exact ERRA| exact MU1| exact WM1|]. unfold RERRNO. cbn [cells_size csize Nat.add disjoint_from fst snd]. lia. }
split. { eapply rauxv_ok_frame; [exact AUXA| exact MU1| exact WM1|]. unfold RAUXV_CELL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
split; [exact MI1|]. split; [exact ST1|].
eapply rdrv_pres_trans; [exact DPRA|]. eapply rdrv_pres_of_munch; [exact MU1| exact WM1| | exact (blocks_LB _ None _ HP1)| lia].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [left; lia| right; left; unfold rdrv_X, RATEXIT; cbn; tauto| right; left; unfold rdrv_X, RATEXIT_A0; cbn; tauto]. }
clear MU1 WM1.
replace (ret_pc (Z_to_bv 64 0x1bfec)) with (Z_to_bv 64 0x1bfec) by (symmetry; rpc).
zstep. if_true.
pose proof IV2 as sfP_; first [ sf_destruct 9%nat sfP_ as _ TP2 _ _ _ _ _ _ _ | sf_fb; destruct sfP_ as (_ & TP2 & _ & _ & _ & _ & _ & _ & _) ].
pose proof (got_fuzzinit_of_pristine mX TP2) as GOTF. unfold RGOT_FUZZINIT in GOTF.
zstep. zstep. zstep. if_true.

zstep. if_cases KL; zify_cond KL.
-
assert (EC : calls = 1) by (unfold calls, cfg; destruct (Z.ltb_spec 0 L); [lia| reflexivity]).
pose proof (run_from_malloc_prefix sX st) as RM. rewrite EC in RM. pose proof (run_from_empty_prefix sX st) as RE. rewrite EC in RE.
zstep. zstep. if_cases KP; zify_cond KP.
+ apply evt_done. eapply RM; [lia| exact FRM| exact HP2| exact CT2| exact IV2| exact AX1].
+ apply evt_done. eapply RE; [lia| exact FRM| exact HP2| exact IV2| exact AX1].
-
assert (NTH : nth_error (zbytes content) (Z.to_nat 2) = Some (Z_to_bv 8 (znth content 2))).
{ unfold zbytes, znth. rewrite nth_error_map. destruct (Z.ltb_spec 2 0); [lia|].
destruct (nth_error content (Z.to_nat 2)) as [c|] eqn:E; cbn [option_map].
- f_equal. f_equal. symmetry. apply nth_error_nth. exact E.
- exfalso. apply nth_error_None in E. unfold zlength in *. lia. }
pose proof (u8ro_read rsegs mX _ _ 2 _ (wa (A + 2)) CT2 NTH ltac:(lia) eq_refl) as RD.
zstep. clear RD. zstep. zstep.
assert (EC : Z.land (bv_unsigned (Z_to_bv 8 (znth content 2))) 3 + 1 = calls).
{ unfold calls, cfg in *. destruct (Z.ltb_spec 0 L); [| lia]. rewrite X0pt.unsigned_lit8 by lia. lia. }
rewrite EC.
zstep. if_cases KP; zify_cond KP.
+ apply evt_done. eapply (run_from_empty_prefix sX st); [lia| exact FRM| exact HP2| exact IV2| exact AX1].
+ apply evt_done. eapply (run_from_malloc_prefix sX st); [lia| exact FRM| exact HP2| exact CT2| exact IV2| exact AX1].
Qed.

#[using="RMALLOC RFREE EMIT FWXO FUZZ RHF RND RBD RBR p cap INLB FC LC CAP L0 L6 SPAB ABB CEIL LO SP16"] Lemma run_entry : forall (sX : PState) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (st : PState) (errv : word),
RHEAP st LB m0 -> bytes_at rsegs m0 A (zbytes content) ->
rauxv_ok m0 AB -> stk rsegs m0 lo usp -> rw_cells rsegs m0 RERRNO [C4 errv] -> mem_inv rsegs m0 -> frm0 fc ->
stdout_file m0 (ps_so st) -> stderr_wfile m0 -> rw_cells rsegs m0 RINITIALIZED [C1 (Z_to_bv 8 0)] -> rtables_pristine m0 -> AXSTAT false m0 ->
a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 (A + 6 + L) -> a3 = Z_to_bv 64 (zlength content - 6 - L) ->
implM rsegs (run cfg payload) st (POST sX LB AB lo m0)
(MS (mkR ra sp gp tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RTARGET_RUN) fc None m0 (seg_rom rsegs)).
Proof.
intros until errv. intros HP CT AUX ST ERR MI FRM SOF SEW INI TP AXF E0 E1 E2 E3.
pose proof facts as sfP_; first [ sf_destruct 7%nat sfP_ as PL0 PL1 PLEN CR CALLS EP PF | sf_fb; destruct sfP_ as (PL0 & PL1 & PLEN & CR & CALLS & EP & PF) ].
unfold run, target_run.
eapply implM_bind; [exact (run_entry_prefix sX t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc st errv HP CT AUX ST ERR MI FRM SOF SEW INI TP AXF E0 E1 E2 E3)|].
cbv beta. intros [ob|] stX msX H; cbn [PPOST] in H.
- first [ sf_destruct 5%nat H as ow q3 Ho OK RS | sf_fb; destruct H as (ow & q3 & Ho & OK & RS) ]. rewrite <- Ho.
replace (1 + Z.land cfg 3) with calls by reflexivity. rewrite <- (Z2Nat.id calls) in RS by lia.
exact (run_loop (Z.to_nat calls) sX ow 0 q3 stX msX ltac:(lia) ltac:(lia) OK RS).
- apply implM_ret. exact H.
Qed.
End RUN.

Definition rtarget_run_prefix_stmt {RCEIL : RunCeiling} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (AB lo : Z) (errv : word),
RHEAP s LB m -> In (p, A, cap) LB ->
bytes_at rsegs m A (zbytes content) -> Forall (fun c => 0 <= c < 256) content ->
zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
rauxv_ok m AB -> bv_unsigned sp <= AB -> AB < 2^62 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RTARGET_RUN_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc ->
stdout_file m (ps_so s) -> stderr_wfile m ->
rw_cells rsegs m RINITIALIZED [C1 (Z_to_bv 8 0)] -> rtables_pristine m -> AXSTAT false m ->
tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 (A + 6 + L) -> a3 = Z_to_bv 64 (zlength content - 6 - L) ->
implM rsegs (let payload_len := zlength (skipn (Z.to_nat (6 + L)) content) in
if payload_len =? 0 then mret (Some None)
else p' <- raw_malloc payload_len ;; mret (match p' with Some q => Some (Some q) | None => None end)) s
(PPOST ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m LB L content AB lo s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RTARGET_RUN) fc None m (seg_rom rsegs)).

Theorem rtarget_run_prefix_proof {RCEIL : RunCeiling} :
rmalloc_stmt -> rheap_frame_stmt -> rheap_blocks_nodup_stmt -> rheap_blocks_disjoint_stmt -> rheap_block_range_stmt ->
rtarget_run_prefix_stmt.
Proof.
intros RMALLOC RHF RND RBD RBR.
unfold rtarget_run_prefix_stmt. intros until errv. intros HP INLB CT FC LC CAP L0 L6 AUX SPAB ABB ST CEIL LO ERR MI FRM SOF SEW INI TP AXF -> SP16 -> -> -> ->.
unfold RATP in ERR. rewrite unsigned_lit in ERR by lia. change (0x4d450 + -164) with RERRNO in ERR.
eapply (run_entry_prefix RMALLOC RHF RND RBD RBR); try eassumption; try reflexivity.
Qed.

Theorem rtarget_run_proof {RCEIL : RunCeiling} :
rmalloc_stmt -> rfree_stmt -> emit_printf_stmt ps_so set_so_ps -> fwritex_stdout_stmt -> harness_stmt ->
rheap_frame_stmt -> rheap_blocks_nodup_stmt -> rheap_blocks_disjoint_stmt -> rheap_block_range_stmt ->
rtarget_run_stmt.
Proof.
intros RMALLOC RFREE EMIT FWXO FUZZ RHF RND RBD RBR.
unfold rtarget_run_stmt. intros until errv. intros HP INLB CT FC LC CAP L0 L6 AUX SPAB ABB ST CEIL LO ERR MI FRM SOF SEW INI TP AXF -> SP16 -> -> -> ->.
unfold RATP in ERR. rewrite unsigned_lit in ERR by lia. change (0x4d450 + -164) with RERRNO in ERR.
eapply (run_entry RMALLOC RFREE EMIT FWXO FUZZ RHF RND RBD RBR); try eassumption; try reflexivity.
Qed.
