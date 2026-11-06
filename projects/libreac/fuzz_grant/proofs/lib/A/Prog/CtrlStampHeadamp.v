(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* reac_ctrl_stamp_headamp (0x82a14) on fuzz_grant's ASan build.

   It takes a class-0 frame on the side stack for frames, writes the three
   argument bytes into it, refuses a head-amp parameter/value pair the console
   cannot carry (legalb), and otherwise lays the control block over the caller's
   frame bytes [p+16, p+50): the type word 0xcd 0xea at [p+16, p+18), then
   ctrl_lay_block for [p+18, p+50) and ctrl_finish for the two checksums. The
   result is Pau's GAz ch pm v (lib/Prog/GrantSweepModel.v:38-40), by her
   stamp_bytes (:172-183) over ly_lay/fin.

   It writes the caller's bytes, so the contract is in the caller-journal form
   (cgif lib/YC20.v:311-365); tcj_kept, twr_ok and tsrc_ok come from
   CtrlFinish.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase
YC4b YC81 YC88 YCbw YCkd YC1g YC1h YC45 YC85 GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
CtrlLayBlockSpec CtrlStampHeadampSpec CtrlFinish.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1i ACj1 ACbf GrantACja GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel RcFin FinishLink.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* Drop the low part of the first region of a symbolic memory: the machine-stack
   region shrinks to the saved registers once the frame slot at sp1 gets a
   region of its own. *)
Definition trim_lo (r : YP09.region) (lo : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo (YP09.r_hi r) (Z.max lo (YP09.r_wlo r)) (YP09.r_whi r)
(filter (fun c => lo <=? YP09.c_off c) (YP09.r_chunks r)).
Definition trim_stack (rs : smem) (lo : Z) : smem :=
match rs with [] => [] | r :: t => trim_lo r lo :: t end.
(* `mv s1,sp` right after `andi sp,sp,-32` leaves s1 as the same value with a
   zero displacement. *)
Lemma denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv.
assert (Hq : 0 <= 32 * ((v + c) / 32) < 2 ^ 64).
{ split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia. }
rewrite denot_lit_U. f_equal.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia.
rewrite (zcanon_id (32 * ((v + c) / 32))) by (unfold M64; lia).
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r.
apply zcanon_id. unfold M64. lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* TSTAMP_STK and EV_STAMP are CtrlStampHeadampSpec.v's, with the contract. *)
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
(* the two program functions it calls, each at the address the image gives it *)
Hypothesis TLAY : tctrl_lay_block_spec B (BASE + AF_ctrl_lay_block) pa_relro_lo pa_relro_hi.
Hypothesis TCF : tctrl_finish_spec B (BASE + AF_ctrl_finish) pa_relro_lo pa_relro_hi.
(* The three bytes of the static control-frame row that ctrl_finish reads
   (rec_off 16, rec_len 6, cksum 2 at A_OBJ 18 + 18..20), and the row's place
   in a range the memory-checking runtime leaves marked usable: facts of the
   image alone, of the same form as CtrlLayBlock.v's HROW_* and HZS_ROW, which
   the composition discharges from GrantImg.v and the runtime's own symbols. *)
Hypothesis HROW_ck : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_ROW) + 18) [16; 6; 2].
Hypothesis HZS_ROW : in_zs B (VAL (A_OBJ A_ROW)) ROW_BYTES.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
(* ---- the contract: CtrlStampHeadampSpec.v -------------------------------- *)
(* ---- the 34 bytes, at the level of Pau's address-free model --------------
   ctrl_lay_block leaves lay_z ch pm v at p + 18; ctrl_finish replaces that by
   RcFin.fin 2 16 6 of it; with the type word 0xcd 0xea at p + 16 the result is
   GAz ch pm v (lib/Prog/GrantSweepModel.v:38-40). This is her stamp_bytes
   (:172-183) read through map bv_unsigned, which her map_unsigned_bl (:166)
   undoes on both sides. *)
Lemma ga_r_rng : forall ch pm v, 0 <= ga_r ch pm v < 128.
Proof. intros ch pm v. unfold ga_r. apply Z.mod_pos_bound. lia. Qed.
Lemma ga_c_rng : forall ch pm v, 0 <= ga_c ch pm v < 256.
Proof. intros ch pm v. unfold ga_c. apply Z.mod_pos_bound. lia. Qed.
Lemma GAz_bytes : forall ch pm v, 0 <= ch < 256 -> 0 <= pm < 256 -> 0 <= v < 256 ->
Forall (fun z => 0 <= z < 256) (GAz ch pm v).
Proof.
intros ch pm v Hc Hp Hv.
pose proof (ga_r_rng ch pm v) as Hr. pose proof (ga_c_rng ch pm v) as Hcc.
unfold GAz. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
Qed.
Lemma lay_bl_len : forall ch pm v, length (bl (lay_z ch pm v)) = 32%nat.
Proof. intros ch pm v. reflexivity. Qed.
Lemma stamp_bytes_z : forall ch pm v, 0 <= ch < 256 -> 0 <= pm < 256 -> 0 <= v < 256 ->
GAz ch pm v = [0xcd; 0xea] ++ map bv_unsigned (RcFin.fin 2 16 6 (bl (lay_z ch pm v))).
Proof.
intros ch pm v Hc Hp Hv.
rewrite (fin_eq (bl (lay_z ch pm v)) (lay_bl_len ch pm v)).
pose proof (stamp_bytes ch pm v Hc Hp Hv) as HS.
apply (f_equal (map bv_unsigned)) in HS. rewrite map_app in HS.
rewrite (map_unsigned_bl [0xcd; 0xea] ltac:(repeat constructor; lia)) in HS.
unfold GA in HS. rewrite (map_unsigned_bl (GAz ch pm v) (GAz_bytes ch pm v Hc Hp Hv)) in HS.
symmetry. exact HS.
Qed.
(* ---- what the call keeps, step by step ------------------------------------
   tcj_kept (CtrlFinish.v) relates the state at this call's entry to a later
   state. It starts as tcj_refl and each step of the walk extends it: a run of
   the symbolic engine changes only the windows of its regions (tcj_run), the
   memory-checking runtime's stack_malloc keeps what acall_kept says
   (tcj_of_acall), and a callee in the caller-journal form keeps what its own
   tcj_kept says (tcj_compose). The bytes of this call's own frame on the side
   stack for frames, of its shadow and of its flag are outside everything the
   entry state's tcj_kept protects (own_ok, own_frame_ok). *)
Definition own_ok (lyc : alayout) (Sc : astate) (Q : Z -> Prop) : Prop :=
forall a, Q a -> a < alloc_ceiling /\ ~ in_img SEGS a /\
(forall b n i, In (b, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> b + i <> a) /\
(forall cid pos, In (cid, pos) (frames Sc) ->
 ~ in_zr a (frame_rng lyc (cid, pos)) /\ ~ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).
Lemma tcj_refl : forall STK lyc Sc W memc sp (E : Z -> Prop),
(forall a, sp - STK <= a < sp -> apresent (w_H W) memc a) ->
tcj_kept B STK lyc Sc W memc W memc sp E.
Proof.
intros STK lyc Sc W memc sp E Hp. unfold tcj_kept.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros a _ _ H; exact H | exact Hp].
Qed.
Lemma tcj_mono_E : forall STK lyc Sc W memc W2 mem2 sp (E E' : Z -> Prop),
tcj_kept B STK lyc Sc W memc W2 mem2 sp E -> (forall a, E a -> E' a) ->
tcj_kept B STK lyc Sc W memc W2 mem2 sp E'.
Proof.
intros STK lyc Sc W memc W2 mem2 sp E E' (K1 & K2 & K3 & K4 & K5 & K6) HE.
split; [intros a Ha Hw He; apply K1; [exact Ha | exact Hw | intros H; exact (He (HE a H))]|].
split; [intros b m i Hb Hi He; apply (K2 b m i Hb Hi); intros H; exact (He (HE _ H))|].
split; [exact K3|].
split; [intros cid pos a Hf Hz He; apply (K4 cid pos a Hf Hz); intros H; exact (He (HE _ H))|].
split; [exact K5 | exact K6].
Qed.
Lemma tcj_of_acall : forall lyc Sc W m W2 m2 slo shi (E : Z -> Prop),
acall_kept SEGS B lyc Sc W m W2 m2 slo shi E -> tcj_kept B (shi - slo) lyc Sc W m W2 m2 shi E.
Proof.
intros lyc Sc W m W2 m2 slo shi E (K1 & K2 & K3 & K4 & K5 & K6). unfold tcj_kept.
replace (shi - (shi - slo)) with slo by lia.
split; [intros a Ha Hw _; exact (K1 a Ha Hw)|]. split; [exact K2|]. split; [exact K3|].
split; [exact K4|]. split; [exact K5 | exact K6].
Qed.
Lemma tcj_compose : forall STK STK' lyc Sc lyc' Sc' W memc W1 m1 W2 m2 sp sp' (E E' : Z -> Prop),
tcj_kept B STK lyc Sc W memc W1 m1 sp E ->
tcj_kept B STK' lyc' Sc' W1 m1 W2 m2 sp' E' ->
sp - STK <= sp' - STK' -> sp' <= sp -> alloc_ceiling <= sp - STK -> sp <= 2 ^ 64 ->
(forall a, E' a -> E a) ->
(forall b, In b (ablocks B lyc Sc) -> In b (ablocks B lyc' Sc')) ->
(forall f, In f (frames Sc) -> In f (frames Sc')) ->
(forall c q, frame_addr lyc' c q = frame_addr lyc c q) ->
tcj_kept B STK lyc Sc W memc W2 m2 sp E.
Proof.
intros STK STK' lyc Sc lyc' Sc' W memc W1 m1 W2 m2 sp sp' E E'
(T1 & T2 & T3 & T4 & T5 & T6) (U1 & U2 & U3 & U4 & U5 & U6) H1 H2 H3 H4 HE Hb Hf Hfa.
split.
{ intros a Ha Hw He. rewrite (U1 a Ha); [exact (T1 a Ha Hw He) | lia | intros H; exact (He (HE a H))]. }
split.
{ intros b m i Hin Hi He. rewrite (U2 b m i (Hb _ Hin) Hi); [exact (T2 b m i Hin Hi He) | intros H; exact (He (HE _ H))]. }
split.
{ intros a Hi Ho Her. rewrite (U3 a Hi Ho Her). exact (T3 a Hi Ho Her). }
split.
{ intros cid pos a Hin Hz He. rewrite (U4 cid pos a (Hf _ Hin)).
  - exact (T4 cid pos a Hin Hz He).
  - unfold frame_rng in *. cbn [fst snd] in *. rewrite !Hfa. exact Hz.
  - intros H. exact (He (HE a H)). }
split.
{ intros a Ha Hw Hp. apply (U5 a Ha); [lia | exact (T5 a Ha Hw Hp)]. }
intros a Ha. destruct (Z_le_gt_dec (sp' - STK') a) as [Hl|Hl]; [destruct (Z_lt_ge_dec a sp') as [Hh|Hh]|].
- exact (U6 a (conj Hl Hh)).
- apply (U5 a); [lia | lia | exact (T6 a Ha)].
- apply (U5 a); [lia | lia | exact (T6 a Ha)].
Qed.
Lemma tcj_step : forall STK lyc Sc W memc mdc W1 m1 W2 m2 sp (E Q : Z -> Prop),
AR SEGS B lyc Sc W memc mdc ->
tcj_kept B STK lyc Sc W memc W1 m1 sp E ->
alloc_ceiling <= sp - STK -> sp <= 2 ^ 64 -> (forall a, E a -> ~ in_img SEGS a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> ~ E a -> ~ Q a ->
 aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
own_ok lyc Sc Q ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) ->
(forall a, sp - STK <= a < sp -> apresent (w_H W2) m2 a) ->
tcj_kept B STK lyc Sc W memc W2 m2 sp E.
Proof.
intros STK lyc Sc W memc mdc W1 m1 W2 m2 sp E Q HAR (T1 & T2 & T3 & T4 & T5 & T6) Hce H64 HEi Hst HQ Hp Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
split.
{ intros a Ha Hn He. rewrite (Hst a ltac:(lia) Hn He); [exact (T1 a Ha Hn He)|].
  intros Hq. destruct (HQ a Hq) as (Hl & _). lia. }
split.
{ intros b m i Hb Hi He. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4 & Hc & _).
  rewrite (Hst (b + i)); [exact (T2 b m i Hb Hi He) | lia | lia | exact He |].
  intros Hq. destruct (HQ _ Hq) as (_ & _ & Hbl & _). exact (Hbl b m i Hb Hi eq_refl). }
split.
{ intros a Hi Ho Her. pose proof (Hsegs a Hi) as Hlo.
  rewrite (Hst a); [exact (T3 a Hi Ho Her) | lia | lia | intros He; exact (HEi a He Hi) |].
  intros Hq. destruct (HQ a Hq) as (_ & Hni & _). exact (Hni Hi). }
split.
{ intros cid pos a Hf Hz He. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (F4 & Fc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (Z.mul_div_le (frame_addr lyc cid pos) 8 ltac:(lia)) as D1.
  pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as D3.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
  assert (Hr : 0 <= a < alloc_ceiling).
  { unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Hz. cbn [fst snd] in Hz. lia. }
  rewrite (Hst a); [exact (T4 cid pos a Hf Hz He) | lia | lia | exact He |].
  intros Hq. destruct (HQ a Hq) as (_ & _ & _ & Hfr). destruct (Hfr cid pos Hf) as [N1 N2].
  destruct Hz as [Hz|Hz]; [exact (N1 Hz) | exact (N2 Hz)]. }
split.
{ intros a Ha Hn Hp0. apply Hp; [exact Ha | exact Hn | exact (T5 a Ha Hn Hp0)]. }
exact Hw.
Qed.
Lemma tcj_run : forall STK lyc Sc W memc mdc W1 m1 m2 Ev rs sp (E Q : Z -> Prop),
AR SEGS B lyc Sc W memc mdc -> tcj_kept B STK lyc Sc W memc W1 m1 sp E ->
alloc_ceiling <= sp - STK -> sp <= 2 ^ 64 -> (forall a, E a -> ~ in_img SEGS a) ->
frame_of Ev rs (mrestrict (w_H W1) m1) (mrestrict (w_H W1) m2) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) m2) ->
(forall a, 0 <= a < 2 ^ 64 -> in_wrange Ev rs a -> (sp - STK <= a < sp) \/ E a \/ Q a) ->
own_ok lyc Sc Q -> (forall a, sp - STK <= a < sp -> apresent (w_H W1) m2 a) ->
tcj_kept B STK lyc Sc W memc W1 m2 sp E.
Proof.
intros STK lyc Sc W memc mdc W1 m1 m2 Ev rs sp E Q HAR HT Hce H64 HEi HF HG Hwin HQ Hw.
apply (tcj_step STK lyc Sc W memc mdc W1 m1 W1 m2 sp E Q HAR HT Hce H64 HEi); [| exact HQ | | exact Hw].
- intros a Ha Hn He Hq. apply (aview_kept_out Ev rs (w_H W1) m1 m2 HF a Ha).
  intros Hin. destruct (Hwin a Ha Hin) as [H|[H|H]]; contradiction.
- intros a _ _ Hp. eapply apresent_grows; [exact HG | exact Hp].
Qed.
(* The frame this call takes, its eight shadow bytes and its flag byte. *)
Definition own_bytes (F FL : Z) (a : Z) : Prop :=
F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/ a = FL.
Lemma own_frame_ok : forall lyc Sc S2 W m2 md2 fpos,
AR SEGS B lyc S2 W m2 md2 -> frames S2 = (0, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
own_ok lyc Sc (own_bytes (frame_addr lyc 0 fpos) (flag_addr lyc 0 fpos)).
Proof.
intros lyc Sc S2 W m2 md2 fpos HAR Hfrs Eab.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR Hfin) as (F4 & Fc & Fapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR Hfin) as (F64 & _ & _).
destruct (FFL lyc S2 W m2 md2 0 fpos HAR Hfin) as (_ & FLown & (_ & FLimg) & (_ & _ & FLc)).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
assert (HF8 : F / 8 = 8 * (F / 64)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite F64, Z.add_0_r in D. rewrite D at 1.
  replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
pose proof (Z.div_mod F 64 ltac:(lia)) as DF0. rewrite F64, Z.add_0_r in DF0.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp.
intros a Ha. unfold own_bytes, SB in Ha.
split; [destruct Ha as [Ha|[Ha|Ha]]; [lia | lia | subst a; exact FLc]|].
split.
{ destruct Ha as [Ha|[Ha|Ha]].
  - exact (frm_img SEGS B LAWS _ _ _ _ _ 0 fpos a HAR Hfin ltac:(change (fs_frame_bytes 0) with 64; fold F; lia)).
  - intros Hi. pose proof (Hsegs a Hi). lia.
  - subst a. exact FLimg. }
split.
{ intros b n i Hb Hi Heq. rewrite <- Eab in Hb.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & B4 & Bc & Bapp & Bpres & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp.
  destruct Ha as [Ha|[Ha|Ha]].
  - pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b n 0 fpos HAR Hb Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd. lia.
  - lia.
  - subst a. apply (proj2 (Bpres (b + i) ltac:(lia))). rewrite Heq. exact FLown. }
intros cid pos Hf.
assert (Hf2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hf).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf2) as (G4 & Gc & Gapp).
destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR Hf2) as (G64 & Gb64 & Gb).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hf2) as (_ & _ & Gpres & GSpres).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Gapp.
set (G := frame_addr lyc cid pos) in *. set (gs := fs_frame_bytes cid) in *.
assert (HG8 : G / 8 = 8 * (G / 64)).
{ pose proof (Z.div_mod G 64 ltac:(lia)) as D. rewrite G64, Z.add_0_r in D. rewrite D at 1.
  replace (64 * (G / 64)) with (8 * (G / 64) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
assert (Hg8 : gs / 8 = 8 * (gs / 64)).
{ pose proof (Z.div_mod gs 64 ltac:(lia)) as D. rewrite Gb64, Z.add_0_r in D. rewrite D at 1.
  replace (64 * (gs / 64)) with (8 * (gs / 64) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
pose proof (Z.div_mod G 64 ltac:(lia)) as DG. rewrite G64, Z.add_0_r in DG.
pose proof (Z.div_mod gs 64 ltac:(lia)) as Dg. rewrite Gb64, Z.add_0_r in Dg.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite F64, Z.add_0_r in DF.
assert (Hd : F + 64 <= G \/ G + gs <= F).
{ destruct (in_split _ _ Hf) as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (0, fpos) (cid, pos) [] l2 l3 HAR
    ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F G gs in Hd. lia. }
unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. fold G gs.
destruct Ha as [Ha|[Ha|Ha]].
- split; [lia|]. lia.
- split; [lia|]. lia.
- subst a. split.
  + intros Hz. apply (proj2 (Gpres FL ltac:(fold G gs; lia))). exact FLown.
  + intros Hz. assert (Hi : 0 <= FL - shadow_addr G < gs / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
    apply (proj2 (GSpres (FL - shadow_addr G) Hi)). replace (shadow_addr G + (FL - shadow_addr G)) with FL by lia. exact FLown.
Qed.
(* A byte of the caller's machine stack inside its window: AR's zero-shadow
   range for the whole machine stack marks it usable and its shadow readable
   in every state the caller's journal reaches. *)
Lemma stack_buf_ok : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k a n,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
sp0 - STK <= a -> a + n <= sp0 -> 0 < n ->
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W2) mem2) a n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k a n HJ Ha Hn Hn0.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & _) & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR2))) as (_ & _ & _ & _ & Hpal & Hpah & _).
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2) HAR2 ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz. rewrite Elo, Ehi in Hz. rewrite Elo in Hpal. rewrite Ehi in Hpah. unfold page_aligned in Hpal, Hpah.
set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as Dl. rewrite Hpal, Z.add_0_r in Dl.
pose proof (Z.div_mod hi 4096 ltac:(lia)) as Dh. rewrite Hpah, Z.add_0_r in Dh.
assert (Hl8 : lo mod 8 = 0) by (rewrite Dl; replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia; apply Z_mod_mult).
assert (Hn8 : (hi - lo) mod 8 = 0) by (rewrite Dl, Dh; replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096 - lo / 4096)) * 8) by lia; apply Z_mod_mult).
split.
- eapply range_addressable_sub; [apply zero_shadow_range; [exact Hl8 | exact Hn8 | exact Hz] | lia | lia].
- intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  assert (Elo8 : lo / 8 = 512 * (lo / 4096)) by (rewrite Dl at 1; replace (4096 * (lo / 4096)) with (512 * (lo / 4096) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (Ehi8 : hi / 8 = 512 * (hi / 4096)) by (rewrite Dh at 1; replace (4096 * (hi / 4096)) with (512 * (hi / 4096) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (Elen8 : (hi - lo) / 8 = 512 * (hi / 4096) - 512 * (lo / 4096)).
  { rewrite Dl at 1. rewrite Dh at 1. replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (A1 : lo / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (A2 : (a + n - 1) / 8 < hi / 8) by (apply Z.div_lt_upper_bound; [lia|]; rewrite Ehi8; lia).
  pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (2147450880 + a / 8) 8 ltac:(lia)) as M2. pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)) as M3.
  pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)) as M4.
  assert (Hi : 0 <= s - shadow_of_addr SHADOW_OFF lo < (hi - lo) / 8).
  { unfold shadow_of_addr, SHADOW_OFF. rewrite Elen8. lia. }
  rewrite <- (Z.add_0_r s). replace (s + 0) with (shadow_of_addr SHADOW_OFF lo + (s - shadow_of_addr SHADOW_OFF lo)) by lia.
  rewrite (Hz _ Hi). discriminate.
Qed.
(* The bytes of the read-only image this call relies on stay as they were. *)
Lemma arodata_tcj : forall STK lyc Sc W memc W2 mem2 sp (E : Z -> Prop),
tcj_kept B STK lyc Sc W memc W2 mem2 sp E ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros STK lyc Sc W memc W2 mem2 sp E (_ & _ & K3 & _) HR a Hro Ho He.
rewrite (K3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (pa_relro_img a Hgot).
Qed.
Lemma legalb_iff : forall pm v, legalb pm v = true <-> (pm < 2 /\ v <= 1) \/ (pm = 2 /\ v <= 55).
Proof.
intros pm v. unfold legalb. rewrite Bool.orb_true_iff, !Bool.andb_true_iff, Z.ltb_lt, !Z.leb_le, Z.eqb_eq. tauto.
Qed.
Lemma own_ok_False : forall lyc Sc, own_ok lyc Sc (fun _ => False).
Proof. intros lyc Sc a []. Qed.
(* tcj_run with the arguments in the order a walk has them at hand. *)
Lemma tcj_run' : forall STK lyc Sc W memc mdc W1 m1 m2 Ev rs sp (E Q : Z -> Prop),
AR SEGS B lyc Sc W memc mdc -> tcj_kept B STK lyc Sc W memc W1 m1 sp E -> own_ok lyc Sc Q ->
alloc_ceiling <= sp - STK -> sp <= 2 ^ 64 -> (forall a, E a -> ~ in_img SEGS a) ->
frame_of Ev rs (mrestrict (w_H W1) m1) (mrestrict (w_H W1) m2) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) m2) ->
(forall a, sp - STK <= a < sp -> apresent (w_H W1) m2 a) ->
(forall a, 0 <= a < 2 ^ 64 -> in_wrange Ev rs a -> (sp - STK <= a < sp) \/ E a \/ Q a) ->
tcj_kept B STK lyc Sc W memc W1 m2 sp E.
Proof.
intros STK lyc Sc W memc mdc W1 m1 m2 Ev rs sp E Q HAR HT HQ Hce H64 HEi HF HG Hw Hwin.
exact (tcj_run STK lyc Sc W memc mdc W1 m1 m2 Ev rs sp E Q HAR HT Hce H64 HEi HF HG Hwin HQ Hw).
Qed.
Lemma aj_pres : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W2) mem2 a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.
Lemma region_kept_gen : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma garr8_aview : forall H H2 (m m2 : word -> option byte) base l,
garr8 SEGS (mrestrict H m) base l ->
(forall a, base <= a < base + Z.of_nat (length l) -> aview SEGS H2 m2 a = aview SEGS H m a) ->
garr8 SEGS (mrestrict H2 m2) base l.
Proof.
intros H H2 m m2 base l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H2 m m2 (base + Z.of_nat j) (base + Z.of_nat j) 1 _); [|exact Hv].
intros k Hk1. apply Hk. lia.
Qed.
(* The caller's buffer [q, q + n) in its machine-stack window: the right to
   write it, in every state the caller's journal reaches. *)
Lemma twr_stack : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp q n,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= q -> q + n <= sp0 -> sp <= q ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp q n HJ H1 H2 H3 a Ha.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (_ & _ & Hceil & Hslo & _) & _).
split; [left; lia|]. split; [apply Hpres; lia|].
split; [intros Ho; pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR Ho); lia | lia].
Qed.
Lemma frame_addr_le : forall n ly ly', layout_le n ly ly' -> forall c q, frame_addr ly' c q = frame_addr ly c q.
Proof. intros n ly ly' Hl c q. pose proof Hl as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity. Qed.
Lemma flag_addr_le : forall n ly ly', layout_le n ly ly' -> forall c q, flag_addr ly' c q = flag_addr ly c q.
Proof. intros n ly ly' Hl c q. pose proof Hl as (_ & _ & _ & _ & _ & EF & _). unfold flag_addr. rewrite EF. reflexivity. Qed.

(* ---- the symbolic state at the function's first slot ---------------------
   Atom 32 is the shadow base (the value the memory-checking runtime keeps in
   the shadow-base cell, object 32, reached through the GOT word object 1);
   atom 274 = A_OBJ 33 is the use-after-return flag cell, reached through the
   GOT word object 0, and it holds 1 in every state, so the `beqz` at 0x82a7c
   is never taken and the stack-probe loop at 0x82aa8 is not reached. *)
Definition st_extra : list word := [Z_to_bv 64 SB].
Definition Bx_ST : sv := SOff 32 0.
Definition Bspan_ST : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition st_regions : smem :=
[ stack_region 96; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 33); uar_cell_regionP (A_OBJ 33) ].
Definition st_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 0);
(11%nat, mkAF 0 255 0); (12%nat, mkAF 0 255 0); (13%nat, mkAF 0 255 0);
(32%nat, mkAF SB SB 0); (A_OBJ 33, mkAF 4096 (2 ^ 47) 2) ] [] [].
Definition ss_st : sstate := mkSS AF_reac_ctrl_stamp_headamp sr_atoms st_regions None st_facts.
Definition EST (regs : bvmap 5 word) : env := Eimg (Ereg regs st_extra).
Lemma st_entry : forall lyc Sc (W : world SEGS) (regs : bvmap 5 word) memc mdc (p ch pm v : Z),
AR SEGS B lyc Sc W memc mdc ->
(forall a, spZ regs - 128 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
getr regs 10 = w64 p -> getr regs 11 = w64 ch -> getr regs 12 = w64 pm -> getr regs 13 = w64 v ->
4096 <= p -> p < 2 ^ 47 -> 0 <= ch < 256 -> 0 <= pm < 256 -> 0 <= v < 256 ->
st_ok_pi SEGS VAL (EST regs) ss_st
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_stamp_headamp)) memc (seg_rom SEGS))).
Proof.
intros lyc Sc W regs memc mdc p ch pm v HAR Hpres Hsp Hsp16 H10 H11 H12 H13 Hp0 Hp47 Hch Hpm Hv.
pose proof pa_B_ok as HBASE.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite (palf_got_uar B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kguar, Kuar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 32 ltac:(lia)) as Hob32. pose proof (pa_obj_img 33 ltac:(lia)) as Hob33.
pose proof (pal_got_cell B TL) as Hgc. pose proof (palf_uar_al B TLF) as Huar4.
rewrite restrict_mkst_fx. unfold ss_st.
set (E := EST regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs st_extra) n)
by (intros n Hn; unfold E, EST; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 ch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 pm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO : forall i, (i < 34)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; unfold E, EST; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (EO 0%nat ltac:(lia)) as E241. pose proof (EO 1%nat ltac:(lia)) as E242.
pose proof (EO 32%nat ltac:(lia)) as E273. pose proof (EO 33%nat ltac:(lia)) as E274.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
pose proof (pa_val_range (A_OBJ 0)) as R241. pose proof (pa_val_range (A_OBJ 1)) as R242.
pose proof (pa_val_range (A_OBJ 32)) as R273. pose proof (pa_val_range (A_OBJ 33)) as R274.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold st_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
    [cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 33) 0) (VAL (A_OBJ 33)));
    [cbn [sv_denot]; rewrite E274, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
  + rewrite (VB (A_OBJ 33) (VAL (A_OBJ 33)) E274) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 33)) 0 4 (SLit 1) 1);
    [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold st_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241), (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242),
  (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273), (VB (A_OBJ 33) (VAL (A_OBJ 33)) E274) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof (palf_sep B TLF) as Hsep4.
  cbn [zseps zseps_from fst snd] in Hsep4. rewrite (pal_uar_cell B TL) in Hsep4.
  revert Hgc Hsep4 Hob0 Hob1 Hob32 Hob33 Huar4 R241 R242 R273 R274 Hsp. clear.
  unfold A_OBJ, Nat.add. intros. repeat split; first [exact I | lia].
- assert (Huar4' : VAL (A_OBJ 33) mod 4 = 0) by (rewrite <- (pal_uar_cell B TL); exact Huar4).
  split; [|split; [exact I | exact I]].
  cbn [st_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, E11, E12, E13, E32, E274, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hsp Hsp16 Hp0 Hp47 Hch Hpm Hv Hob33 R274 Huar4'. clear.
  unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Ltac awr_ro_rec := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]; awr_ro_rec ].
(* The write rights of this walk's own regions: the machine-stack slots (atoms
   2 and 60, inside the caller's window) and the frame and its shadow (atoms
   516 and 529, the class-0 frame this call owns). *)
Ltac awr_st_hd U2 U60 U516 U529 sp0v spv sp1v fposv Fv :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0v));
  [reflexivity | rewrite U2; lia | cbn; unfold TSTAMP_STK, TLAY_STK, ESTACK in *; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1v - sp0v));
  [reflexivity | rewrite U60; lia | cbn; unfold TSTAMP_STK, TLAY_STK, ESTACK in *; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat);
  [reflexivity | exact U516
  | cbn [YP09.r_wlo YP09.r_whi]; let aq := fresh "aq" in let Haq := fresh "Haq" in intros aq Haq;
    right; right; right; exists 0, fposv; split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold Fv; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat);
  [reflexivity | exact U529
  | cbn [YP09.r_wlo YP09.r_whi]; let aq := fresh "aq" in let Haq := fresh "Haq" in intros aq Haq;
    right; right; right; exists 0, fposv; split; [left; reflexivity|]; right;
    unfold in_zr, shadow_addr, SHADOW_OFF; cbn [fst snd];
    change (fs_frame_bytes 0 / 8) with 8; fold Fv; unfold SB in *; lia |]
end.
(* A run's write windows, region by region: each lies in this call's stack
   window, in the bytes E it may change, or in own_bytes (its own frame on the
   side stack for frames, the frame's shadow, the frame's flag). `norm` turns
   the region's base into a number. *)
Ltac wr_tac_with norm :=
let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a Ha (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; cbv beta; try unfold own_bytes; try unfold SB;
    revert Hr; norm; intros Hr;
    first [lia | let t := type of Hr in lazymatch goal with |- ?g => idtac "WRFAIL" t "GOAL" g end; fail] |]);
destruct Hin.
(* GrantACja's evalE, with this file's SB (CtrlFinish.SB) unfolded before the
   bases are turned into numbers. *)
Ltac evalS AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
try unfold SB; rewrite ?unsigned_lit_small by lia.
Ltac wr_tac AG := wr_tac_with ltac:(evalS AG).
(* After a run: extend what the call keeps (TK) to the run's last memory. *)
Ltac tk_upd HAR TK HQ HJx AG HEi :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
let TK2 := fresh "TK" in
pose proof (tcj_run' _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR TK HQ ltac:(lia) ltac:(lia) HEi HFr HG
  ltac:(intros ? ?; apply (aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx); lia) ltac:(wr_tac AG)) as TK2;
clear TK; rename TK2 into TK end; clear_frames.
(* Run and resolve branches until every leaf is at the slot that accepts the
   head-amp pair (0x82b44) or at the slot the refusing paths jump to
   (0x82ba8); after each run, tktac extends what the call keeps. *)
Ltac st_loop fuel RUNPx RUNCx BRx awrtac tktac :=
lazymatch fuel with
| O => idtac "FUEL-OUT"
| S ?f =>
  lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx _ |- _ =>
    let pc := eval vm_compute in (ss_pc ssx) in
    lazymatch pc with
    | 9376 => idtac   (* 0x82b50: the shadow check of the first caller byte *)
    | 9528 => idtac   (* 0x82be8: the flag store that releases the frame *)
    | _ => first [ psrr_branch_pi RUNPx BRx HSx
                 | lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
                     paj_run_shc RUNPx RUNCx HSx HJx; [ awrtac | tktac HJx ] end
                 | idtac "STUCK" pc ];
           st_loop f RUNPx RUNCx BRx awrtac tktac
    end
  end
end.
(* The conditions the walk took to reach a leaf, as facts about pm and v
   (U12 : U E (SOff 12 0) = pm, U13 : U E (SOff 13 0) = v). *)
Ltac leaf_conds HSx U12 U13 :=
lazymatch type of HSx with st_ok_pi _ _ ?Ev ?ssx _ =>
let cs := eval vm_compute in (f_conds (ss_facts ssx)) in
let rec go l := lazymatch l with
| nil => idtac
| cons ?c ?l' =>
  let Hc := fresh "Hcd" in
  assert (Hc : acond_ok Ev c)
    by (apply (st_ok_pi_cond_In Ev ssx _ c HSx); vm_compute; repeat (first [left; reflexivity | right]));
  unfold acond_ok in Hc; cbn [ac_c ac_a ac_b] in Hc;
  rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc;
  rewrite ?U12, ?U13 in Hc; rewrite ?U_lit in Hc by lia;
  repeat match type of Hc with negb _ = true => apply Bool.negb_true_iff in Hc end;
  first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc | idtac];
  go l'
end in go cs end.
(* The flag byte of this call's frame gets a region of its own (ACbf.v's
   add_flag_region, with this file's SB). *)
Ltac add_flag_region' HS AG E528 Hp HFLown :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite ?ew_ewset_other by lia; rewrite E528, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
  intros o Ho; apply (apresent_writable _); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalS AG;
  repeat split; first [flag_disj_cheap HFLown | zone_lia
    | match goal with |- ?g => idtac "DISJFAIL" g end; fail ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* RUNF's write rights: every window is this call's stack window, its own
   frame or frame shadow (the frame is the head of the journal's own list), or
   the frame's flag byte. normF names the frame's address F and flag FL. *)
Ltac wr_flag AG normF :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalS AG; intros Hr; normF;
    first [ exfalso; lia
          | right; lia
          | left; left; lia
          | left; right; right; right; eexists 0, _; split; [left; reflexivity|];
            first [ left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; normF; lia
                  | right; unfold in_zr, shadow_addr, SHADOW_OFF; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; normF; lia ]
          | let t := type of Hr in lazymatch goal with |- ?g => idtac "WRFLAGFAIL" t g end; fail ] |]);
destruct Hin.
(* The flag byte is 0 after the store (ACbf.v's flag0, without its rewrite). *)
Ltac flag0' E528 normF :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in let V0 := fresh "V0" in
intros msr HSr; normF;
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
  ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E528; apply unsigned_lit_small; lia)
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.
(* From the flag store at 0x82be8 to the `ret`: the flag byte gets its region,
   RUNF releases the frame (the runtime's frame_flag_law and astack_free_law),
   TK follows the run, and RETx returns to the caller. *)
Ltac stamp_flag HSx RUNFx RETx FFLx tktac HJx AG E528 HFLown Hfin normF hnorm :=
let HFLp := fresh "HFLp" in
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyX ?SX ?Wx ?mX ?mdX _ =>
destruct (FFLx lyX SX Wx mX mdX 0 _ (proj1 HJx) Hfin) as (HFLp & _) end;
hnorm HFLp;
add_flag_region' HSx AG E528 HFLp HFLown;
paj_run_flag_sh RUNFx HSx HJx; [lia | wr_flag AG normF | flag0' E528 normF | ];
tktac HJx;
lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RETx Wx _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'.
(* The post's common part: the configuration, the journal, the callee-saved
   registers, the frames and blocks, the side-stack-frame field. *)
Ltac post_common HSx LAWSx HJx AG EE E1 Hra Hfrs Eab SFtac res :=
let R1 := fresh "R1" in
prreg HSx (1%bv : bv 5) R1;
unfold tstamp_post; cbv beta;
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyX ?SX _ _ _ _ =>
lazymatch goal with |- exists ly2 S2 regs2 mem2 md2 res, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
  exists lyX, SX, rg, mm, mdx, res end end;
split; [rewrite R1, (AG 1%nat), E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
split; [eapply (ajournal_mono_k _ _); [apply (ajournal_materialize _ _ LAWSx pa_segs_low); exact HJx | unfold EV_STAMP, EV_LAY; try unfold EV_CF; lia]|];
split; [apply aregs_preserved_eqs; creg HSx AG EE|];
split; [let Hfx := fresh "Hfx" in pose proof HJx as (_ & _ & _ & _ & _ & Hfx & _); rewrite Hfx, Hfrs; reflexivity|];
split; [unfold ablocks; rewrite blocks_stack_free_state; unfold ablocks in Eab; exact Eab|];
split; [SFtac|].
(* A refusing leaf, at 0x82be8: the pair is not legal, the call returns -1 and
   leaves [p + 16, p + 50) as it was. *)
Ltac refuse_leaf HSx RUNFx RETx FFLx LAWSx HAR TK HQ HJx AG E528 HFLown Hfin normF HEi U12 U13 EE E1 Hra Eab Hfrs ES2 :=
leaf_conds HSx U12 U13;
let Hleg := fresh "Hleg" in
lazymatch type of U12 with _ = ?pmv => lazymatch type of U13 with _ = ?vv =>
assert (Hleg : legalb pmv vv = false)
  by (let Eq := fresh "Eq" in destruct (legalb pmv vv) eqn:Eq; [apply legalb_iff in Eq; lia | reflexivity]) end end;
stamp_flag HSx RUNFx RETx FFLx ltac:(fun HJy => tk_upd HAR TK HQ HJy AG HEi) HJx AG E528 HFLown Hfin normF ltac:(fun H => idtac);
post_common HSx LAWSx HJx AG EE E1 Hra Hfrs Eab ltac:(rewrite ES2; eexists; reflexivity) (-1);
let R10 := fresh "R10" in prreg HSx (10%bv : bv 5) R10;
split; [rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|];
split; [apply (tcj_mono_E _ _ _ _ _ _ _ _ (fun _ => False)); [exact TK | intros ? []]|];
rewrite Hleg; split; [reflexivity|];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
let K1 := fresh "K1" in destruct TK as (K1 & _); apply K1; [lia | lia | intros []].
(* Close the write window of the region based at atom n (GrantACja's fs_roF,
   for any base): the token runner's cells_safe_b wants no open window over
   the shadow band, and this call's frame and its shadow lie in it. *)
Ltac close_win HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* Write rights on the accepting path: the caller's two type-word bytes
   [p + 16, p + 18) (atom 10) lie in the caller's machine-stack window. *)
Ltac awr_acc_hd U2 U60 U516 U529 U10 sp0v spv sp1v fposv Fv :=
first [ lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
          let aq := fresh "aq" in let Haq := fresh "Haq" in
          eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat);
          [reflexivity | exact U10 | cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq; left; lia |] end
      | awr_st_hd U2 U60 U516 U529 sp0v spv sp1v fposv Fv ].
(* Write rights for this call's frame and frame shadow, whatever layout the
   journal has reached (normF names frame_addr _ 0 fpos as F). *)
Ltac awr_frame_hd U516 U529 fposv normF :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
  let aq := fresh "aq" in let Haq := fresh "Haq" in
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat);
  [reflexivity | exact U516 | cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq;
   right; right; right; exists 0, fposv; split; [left; reflexivity|]; left;
   unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; normF; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
  let aq := fresh "aq" in let Haq := fresh "Haq" in
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat);
  [reflexivity | exact U529 | cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq;
   right; right; right; exists 0, fposv; split; [left; reflexivity|]; right;
   unfold in_zr, shadow_addr, SHADOW_OFF; cbn [fst snd];
   change (fs_frame_bytes 0 / 8) with 8; normF; unfold SB in *; lia |]
end.
(* After a callee in the caller-journal form: each region of the call's state
   is kept, from the callee's tcj_kept TKc (CtrlFinish.v): this call's frame
   and frame shadow (closed windows) by its fourth clause, the machine-stack
   regions (the saved registers, the slot at sp1, the caller's two type-word
   bytes) by its first, since they lie above the callee's stack window and
   outside what it writes; the image's cells by AR's constant cells (keptFL). *)
Ltac kept_call TKc HJx AG Hfin Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 normF :=
first [
  lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
    lazymatch n with 516%nat => idtac | 529%nat => idtac | _ => fail end;
    let a := fresh "a" in let Ha := fresh "Ha" in
    eapply region_kept_gen;
    [ evalS AG; reflexivity
    | intros a Ha; apply (proj1 (proj2 (proj2 (proj2 TKc))) 0 _ a Hfin);
      [ first [ left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; normF; lia
              | right; unfold in_zr, shadow_addr, SHADOW_OFF; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; normF; lia ]
      | cbv beta; lia ]
    | intros a Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
    lazymatch n with 2%nat => idtac | 60%nat => idtac | 10%nat => idtac | _ => fail end;
    let a := fresh "a" in let Ha := fresh "Ha" in
    eapply region_kept_gen;
    [ evalS AG; reflexivity
    | intros a Ha; apply (proj1 TKc); [lia | lia | cbv beta; lia]
    | intros a Ha; apply (aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx); lia ] end
| keptFL_with ltac:(idtac; fail) TKc HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ltac:(idtac; fail) ltac:(idtac; fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ].
(* No window of a run's regions meets the caller's [p + 18, p + 50), whose
   bytes the callees laid down. *)
Ltac nwr_tac AG :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalS AG; intros Hr; lia |]);
destruct Hin.
(* Carry a garr8 fact over [p + 18, p + 18 + len) across a run (Llen : the
   list's length is 32). *)
Ltac ga_upd HGA AG Llen :=
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
let HGA2 := fresh "HGA" in
pose proof (garr8_aview _ _ _ _ _ _ HGA ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; rewrite Llen in Ha;
   apply (aview_kept_out Ef rs _ _ _ HFr a ltac:(lia)); nwr_tac AG)) as HGA2;
clear HGA; rename HGA2 into HGA end.
(* Reopen the write window [0, hi) of the region based at atom n; ptac proves
   the window's bytes writable. *)
Ltac open_win HS n hi ptac :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 hi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; ptac))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Theorem pb_reac_ctrl_stamp_headamp : tctrl_stamp_headamp_spec B (BASE + AF_reac_ctrl_stamp_headamp) pa_relro_lo pa_relro_hi.
Proof.
unfold tctrl_stamp_headamp_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p ch pm v cl
HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 Hch Hpm Hv Hchain Hsp16 Hbud Hsple Hfrl
Hp0 Hp47 Hmr Hnimg Hpsp Hpsp0 HLEG.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : TSTAMP_STK = 4384) by reflexivity.
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk &
F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hsp016 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
assert (Hsprng : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof (st_entry lyc Sc W regs memc mdc p ch pm v HARc
ltac:(intros a Ha; apply Hpres; lia) Hsprng Hsp16 H10 H11 H12 H13 ltac:(lia) ltac:(lia) Hch Hpm Hv) as HS.
assert (HEI : img_env VAL A_LIM (EST regs)) by apply Eimg_env.
assert (SHOK : sh_ok SEGS Bx_ST (@nil shent) (EST regs) (mrestrict (w_H W) memc)) by constructor.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (EST regs) n = ew (Ereg regs st_extra) n)
by (intros n Hn; unfold EST; apply Eimg_low; exact Hn).
assert (E1 : ew (EST regs) 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew (EST regs) 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew (EST regs) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E32 : ew (EST regs) 32 = Z_to_bv 64 SB)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs st_extra) (EST regs))
by (split; [intros n Hn; unfold EST; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at. change (w64 (BASE + AF_reac_ctrl_stamp_headamp)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_stamp_headamp)).
paj_run_tok RUN HS HJ SHOK Bspan_ST.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite Usp; lia | cbn; unfold TSTAMP_STK, TLAY_STK, ESTACK; lia | cbn; lia |].
  awr_ro_rec. }
(* 0x82a80: the class-0 frame on the side stack for frames.  sp1 is the stack
   pointer after `andi sp,sp,-32` at 0x82a4c. *)
assert (E3 : ew (EST regs) 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew (EST regs) 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
set (sp1 := 32 * ((spZ regs + -96) / 32)).
destruct (sp1_facts (spZ regs + -96) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by lia. clear Hsp1r.
lazymatch type of HS with st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
  let e := eval vm_compute in (sr_get (ss_regs ssx) (2%bv : bv 5)) in
  assert (R2 : getr (ms_regs msx) (2%bv : bv 5) = Z_to_bv 64 sp1) by
    (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx (2%bv : bv 5) HS) _);
     change (sv_denot Ex e = Z_to_bv 64 sp1);
     exact (denot_and_m32 Ex 2 (spZ regs) (-96)
       ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)));
  let e3 := eval vm_compute in (sr_get (ss_regs ssx) (3%bv : bv 5)) in
  assert (R3 : getr (ms_regs msx) (3%bv : bv 5) = w64 (as_gp B)) by
    (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx (3%bv : bv 5) HS) _);
     change (sv_denot Ex e3 = w64 (as_gp B)); cbn [sv_denot]; rewrite E3, Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp);
  let e4 := eval vm_compute in (sr_get (ss_regs ssx) (4%bv : bv 5)) in
  assert (R4 : getr (ms_regs msx) (4%bv : bv 5) = w64 (as_tp B)) by
    (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx (4%bv : bv 5) HS) _);
     change (sv_denot Ex e4 = w64 (as_tp B)); cbn [sv_denot]; rewrite E4, Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp);
  let e1 := eval vm_compute in (sr_get (ss_regs ssx) (1%bv : bv 5)) in
  assert (R1 : getr (ms_regs msx) (1%bv : bv 5) = Z_to_bv 64 (BASE + 9176)) by
    (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx (1%bv : bv 5) HS) _);
     change (sv_denot Ex e1 = Z_to_bv 64 (BASE + 9176)); apply codeptr_val; exact HEI)
end.
assert (Hfs0 : 8 < fs_frames 0) by (let vv := eval vm_compute in (fs_frames 0) in change (fs_frames 0) with vv; lia).
pose proof (count_cid_le_length 0 (frames Sc)) as Hcnt0.
pmkst HS. rewrite (palf_sm0 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msX)
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Hsp016.
    rewrite <- (Z.mod_small (sp1 mod 16) 16) by (apply Z.mod_pos_bound; lia).
    rewrite Hsp1al16. reflexivity.
  - lia.
  - unfold ESTACK, TSTAMP_STK, TLAY_STK, ESTACK in *; lia.
  - exact R3. - exact R4. - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin &
Hnev2 & Hbb2 & Hz & Hflag & HK & HJM & (fS2 & ES2)).
pose proof HJ2 as (HAR2x & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstatic2 & _ & _).
(* what the call keeps, from its entry to the return of stack_malloc_0 *)
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (EST regs) n = getr regs r)
by (intros n r Hn; unfold EST; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Hwce : alloc_ceiling <= spZ regs - TSTAMP_STK) by lia.
assert (HEiF : forall a, (fun _ : Z => False) a -> ~ in_img SEGS a) by (intros a []).
replace (sp0 + (sp1 - sp0)) with sp1 in HK by lia.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?m1), HG : mem_grows _ _ |- _ =>
pose proof (tcj_run' TSTAMP_STK lyc Sc W memc mdc W memc m1 _ _ (spZ regs) (fun _ => False) (fun _ => False)
  HARc (tcj_refl TSTAMP_STK lyc Sc W memc (spZ regs) (fun _ => False) ltac:(intros a Ha; apply Hpres; lia))
  (own_ok_False lyc Sc) Hwce ltac:(lia) HEiF HFr HG
  ltac:(intros a Ha; apply (aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia)
  ltac:(wr_tac_with ltac:(rewrite ?Usp))) as TK end.
pose proof (tcj_compose _ _ lyc Sc lyc Sc W memc W _ W mem2 (spZ regs) sp1 (fun _ => False) (fun _ => False)
  TK (tcj_of_acall lyc Sc W _ W mem2 (sp1 - ESTACK) sp1 (fun _ => False) HK)
  ltac:(lia) ltac:(lia) Hwce ltac:(lia) (fun a H => H) (fun b H => H) (fun f H => H) (fun c q => eq_refl)) as TK1.
clear TK; rename TK1 into TK. clear_frames.
(* the symbolic state at the return point 0x82a88 *)
assert (AG : forall n, (n < 33)%nat -> ew (EST regs) n = ew (EST regs) n) by (intros; reflexivity).
aconstsF HJ Kgot1 Kcell1 Kguar1 Kuar1.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
reseat HS HJ2 HP2 [0;1;2;3;4]%nat AG
ltac:(idtac; first [ kept_malloc HK HJ2 AG Usp
| keptFL HK HJ2 AG Kgot1 Kgot2 Kcell1 Kcell2 Kguar1 Kguar2 Kuar1 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
(* the frame the memory-checking runtime gave us, and the stack slot at sp1 *)
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal64 & _ & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFimg.
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
destruct (FFL lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
pose proof (own_frame_ok lyc Sc S2 W mem2 md2 fpos HAR2 Hfrs2 Eab) as HQ. fold F FL in HQ.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite HFq at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
(* name sp1 as atom 60 and keep only the saved registers in the machine-stack region *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (trim_stack (ss_mem ssx) (-88)) in
  pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
  remember Enew as E1v eqn:HEv in HS;
  repeat match goal with Hh : img_env _ _ Enew |- _ => rewrite <- HEv in Hh end end.
assert (AG2 : forall n, (n < 33)%nat -> ew E1v n = ew (EST regs) n)
by (intros nn Hnn; rewrite HEv; rewrite !ew_havoc_old by lia; apply AG; exact Hnn).
clear AG. rename AG2 into AG.
assert (E60 : ew E1v 60 = Z_to_bv 64 sp1)
by (rewrite HEv; rewrite ew_havoc_old by lia;
    exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E528 : ew E1v 528 = Z_to_bv 64 FL)
by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E529 : ew E1v 529 = Z_to_bv 64 (SB + F / 8))
by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HEv.
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
assert (E2v : ew E1v 2 = Z_to_bv 64 (spZ regs))
by (rewrite (AG 2%nat) by lia; rewrite E2; symmetry; apply Z_to_bv_bv_unsigned).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hh ?msx) =>
  let e2 := eval vm_compute in (sr_get (ss_regs ssx) (2%bv : bv 5)) in
  assert (R2' : getr (ms_regs msx) (2%bv : bv 5) = Z_to_bv 64 sp1) by
    (refine (eq_trans (st_ok_pi_restrict_reg Hh Ev ssx msx (2%bv : bv 5) HS) _);
     change (sv_denot Ev e2 = Z_to_bv 64 sp1);
     exact (denot_and_m32 Ev 2 (spZ regs) (-96) E2v ltac:(lia) ltac:(lia) ltac:(lia)));
  let e9 := eval vm_compute in (sr_get (ss_regs ssx) (9%bv : bv 5)) in
  assert (R9' : getr (ms_regs msx) (9%bv : bv 5) = Z_to_bv 64 sp1) by
    (refine (eq_trans (st_ok_pi_restrict_reg Hh Ev ssx msx (9%bv : bv 5) HS) _);
     change (sv_denot Ev e9 = Z_to_bv 64 sp1);
     exact (denot_and_m32_add0 Ev 2 (spZ regs) (-96) E2v ltac:(lia) ltac:(lia) ltac:(lia)))
end.
cbn [ms_regs restrict mkst] in R2', R9'.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2';
        rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R9';
        rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia;
        change (2 ^ 5) with 32; lia)) as HS3;
  clear HS; rename HS3 into HS end.
lazymatch goal with Himg : img_env _ _ E1v |- _ => pose proof Himg as HEIv end.
assert (E241v : ew E1v 241 = Z_to_bv 64 (VAL (A_OBJ 0)))
by (exact (img_env_atomP E1v 241%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia))).
assert (E242v : ew E1v 242 = Z_to_bv 64 (VAL (A_OBJ 1)))
by (exact (img_env_atomP E1v 242%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia))).
assert (E273v : ew E1v 273 = Z_to_bv 64 (VAL (A_OBJ 32)))
by (exact (img_env_atomP E1v 273%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia))).
assert (E274v : ew E1v 274 = Z_to_bv 64 (VAL (A_OBJ 33)))
by (exact (img_env_atomP E1v 274%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia))).
pose proof (pa_val_range (A_OBJ 0)) as Rv241. pose proof (pa_val_range (A_OBJ 1)) as Rv242.
pose proof (pa_val_range (A_OBJ 32)) as Rv273. pose proof (pa_val_range (A_OBJ 33)) as Rv274.
pose proof (pa_obj_img 0 ltac:(lia)) as Io241. pose proof (pa_obj_img 1 ltac:(lia)) as Io242.
pose proof (pa_obj_img 32 ltac:(lia)) as Io273. pose proof (pa_obj_img 33 ltac:(lia)) as Io274.
assert (Bv60 : base_val E1v (Some 60%nat) = sp1)
by (cbn [base_val]; rewrite E60; apply unsigned_lit_small; lia).
assert (Bv2 : base_val E1v (Some 2%nat) = spZ regs)
by (cbn [base_val]; rewrite (AG 2%nat) by lia; exact Usp).
assert (Bv241 : base_val E1v (Some 241%nat) = VAL (A_OBJ 0))
by (cbn [base_val]; rewrite E241v; apply unsigned_lit_small; lia).
assert (Bv242 : base_val E1v (Some 242%nat) = VAL (A_OBJ 1))
by (cbn [base_val]; rewrite E242v; apply unsigned_lit_small; lia).
assert (Bv273 : base_val E1v (Some 273%nat) = VAL (A_OBJ 32))
by (cbn [base_val]; rewrite E273v; apply unsigned_lit_small; lia).
assert (Bv274 : base_val E1v (Some 274%nat) = VAL (A_OBJ 33))
by (cbn [base_val]; rewrite E274v; apply unsigned_lit_small; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 8 0 8 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst];
        rewrite Bv60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply Hpres2; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
        rewrite Bv60, Bv2, Bv241, Bv242, Bv273, Bv274;
        repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
(* the frame itself (its flag pointer at F + 56) and its eight shadow bytes *)
assert (E32' : ew E1v 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32).
assert (Bv516 : base_val E1v (Some 516%nat) = F)
by (cbn [base_val]; rewrite RF; apply unsigned_lit_small; lia).
assert (Bv529 : base_val E1v (Some 529%nat) = SB + F / 8)
by (cbn [base_val]; rewrite E529; apply unsigned_lit_small; unfold SB; lia).
assert (ZS8 : val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8) 8 0).
{ apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  apply Hz. change (64 / 8) with 8. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 516%nat (HPTR 6) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia;
        change (2 ^ 6) with 64; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 528%nat (HPTR 0) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia;
        rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 529%nat (mkAF (SB + 512) (SB + 17592186044416) 3) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
        change (2 ^ 3) with 8; unfold SB; split; [lia|]; split;
        [rewrite HF8; replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia; apply Z_mod_mult | lia]))
  as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 516 528 0 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst app];
        change (fs_frame_bytes 0) with 64; rewrite Bv516; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
        | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 56 8 _ FL);
          [cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
          | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
        change (fs_frame_bytes 0) with 64;
        rewrite Bv516, Bv60, Bv2, Bv241, Bv242, Bv273, Bv274;
        repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 529 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst app];
        change (fs_frame_bytes 0 / 8) with 8; rewrite Bv529; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
        [ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
          apply (proj1 (HFSpres o ltac:(change (64 / 8) with 8; lia)))
        | apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; exact ZS8] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fshadow_region, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
        change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64;
        rewrite Bv529, Bv516, Bv60, Bv2, Bv241, Bv242, Bv273, Bv274;
        unfold SB; repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
assert (Usp2 : bv_unsigned (ew E1v 2) = spZ regs) by exact Bv2.
assert (Usp60 : bv_unsigned (ew E1v 60) = sp1) by exact Bv60.
assert (EFA0 : forall c p0, frame_addr lyc c p0 = frame_addr lyc c p0) by reflexivity.
assert (U516 : bv_unsigned (ew E1v 516) = F) by exact Bv516.
assert (U529 : bv_unsigned (ew E1v 529) = SB + F / 8) by exact Bv529.
(* 0x82a88-0x82b40: the frame's magic, description and pc, its shadow bytes
   f1 f1 f1 f1 03 f3 f3 f3, the three argument bytes at F + 32, and the
   head-amp legality test.  The shadow of the frame is a region of the
   symbolic state here, so the walk runs without the shadow tokens. *)
paj_run_shc RUNP RUNC HS HJ2.
{ awrFL_with ltac:(idtac; awr_st_hd Usp2 Usp60 U516 U529 sp0 (spZ regs) sp1 fpos F) AG fpos F EFA0. }
tk_upd HARc TK HQ HJ2 AG HEiF.
st_loop 14%nat RUNP RUNC BR ltac:(idtac; awrFL_with ltac:(idtac; awr_st_hd Usp2 Usp60 U516 U529 sp0 (spZ regs) sp1 fpos F) AG fpos F EFA0)
  ltac:(fun HJx => tk_upd HARc TK HQ HJx AG HEiF).
(* Five leaves: three refusing paths at the flag store 0x82be8 (pc 9528) and
   two accepting paths at the shadow check of p + 16, 0x82b50 (pc 9376). *)
all: assert (U12 : U E1v (SOff 12 0) = pm)
  by (apply U_atom; [rewrite (AG 12%nat), (EE 12%nat 12%bv eq_refl) by lia; exact H12 | lia]).
all: assert (U13 : U E1v (SOff 13 0) = v)
  by (apply U_atom; [rewrite (AG 13%nat), (EE 13%nat 13%bv eq_refl) by lia; exact H13 | lia]).
all: assert (HnoF : forall a, F <= a < F + 64 -> ~ aowned B lyc S2 a) by (intros a Ha; exact (proj2 (HFpres a Ha))).
all: assert (HnoS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 8 -> ~ aowned B lyc S2 a)
  by (intros a Ha; unfold shadow_addr, SHADOW_OFF in HFSpres;
      replace a with (2147450880 + F / 8 + (a - (2147450880 + F / 8))) by lia;
      apply (proj2 (HFSpres (a - (2147450880 + F / 8)) ltac:(change (64 / 8) with 8; lia)))).
all: lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx _ |- _ =>
  let pc := eval vm_compute in (ss_pc ssx) in lazymatch pc with
  | 9528 => refuse_leaf HS RUNF RET FFL LAWS HARc TK HQ HJ2 AG E528 HFLown Hfin2 ltac:(fold F FL) HEiF U12 U13 EE E1 Hra Eab Hfrs ES2
  | 9376 => idtac end end.
(* ---- the two accepting leaves, at the shadow check of p + 16 (0x82b50) ----
   Both have the same symbolic state up to their branch conditions, so each
   step below runs on both. The pair is legal; from here the call may write
   the caller's [p + 16, p + 50), which TK now allows. *)
all: leaf_conds HS U12 U13.
all: assert (Hleg : legalb pm v = true) by (apply legalb_iff; lia).
all: assert (HEi10 : forall a, (fun a => p + 16 <= a < p + 50) a -> ~ in_img SEGS a) by exact Hnimg.
all: pose proof (tcj_mono_E _ _ _ _ _ _ _ _ _ (fun a => p + 16 <= a < p + 50) TK (fun a (H : False) => match H with end)) as TK1.
all: clear TK; rename TK1 into TK.
all: assert (E10e : ew (EST regs) 10 = Z_to_bv 64 p) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
all: assert (U10 : bv_unsigned (ew E1v 10) = p) by (rewrite (AG 10%nat), E10e by lia; apply unsigned_lit_small; lia).
(* The token runner wants no write window over the shadow band: close the
   frame's and the frame shadow's (nothing on this path writes them before
   ctrl_finish returns), name the buffer [p + 16, p + 18) as a region of its
   own, and bound atom 10 so that its shadow lies in the band. *)
all: close_win HS 516%nat.
all: close_win HS 529%nat.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 10%nat (mkAF 4096 (2 ^ 47 - 58) 0) HS
   ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U10; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
  clear HS; rename HS3 into HS end.
all: norm_ss HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 10%nat) 16 18 16 18 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst base_val];
        rewrite U10; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply (aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        evalS AG; repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end.
all: norm_ss HS.
(* The two shadow loads read the shadow of [p + 16, p + 18): the stack's
   zero-shadow range marks [p + 16, p + 50) usable (stack_buf_ok). *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict (w_H ?Wx) ?msx) =>
  assert (SHOK2 : sh_ok SEGS Bx_ST [mkSHE 10 16 50] Ev (mrestrict (w_H Wx) (ms_mem msx)))
  by (unfold sh_ok; apply Forall_cons; [| apply Forall_nil];
      eapply shent_ok_of_range;
      [ exact (proj1 (stack_buf_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (p + 16) 34 HJ2 ltac:(lia) ltac:(lia) ltac:(lia)))
      | unfold Bx_ST; apply U_atom; [exact E32' | unfold SHADOW_OFF; lia]
      | apply U_atom; [rewrite (AG 10%nat), E10e by lia; reflexivity | lia]
      | lia | lia
      | intros x Hx; unfold SHADOW_OFF; lia ]) end.
all: paj_run_tok RUN HS HJ2 SHOK2 Bspan_ST;
  [ awrFL_with ltac:(idtac; awr_acc_hd Usp2 Usp60 U516 U529 U10 sp0 (spZ regs) sp1 fpos F) AG fpos F EFA0 | ].
all: tk_upd HARc TK HQ HJ2 AG HEi10.
(* 0x82b94: the call of ctrl_lay_block, by its contract TLAY. First its
   registers, then the three argument bytes at F + 32 and their shadow byte
   03 at SB + F / 8 + 4, read off the frame's regions. *)
all: rregU HS (1%bv : bv 5) (BASE + 9448)
  ltac:(rewrite (U_atom_off E1v 240%nat (VAL A_TEXT) 9448 (img_env_atomP E1v 240%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia)))
        by lia; reflexivity) Rc1.
all: rregU HS (2%bv : bv 5) sp1 ltac:(apply U_atom; [exact E60 | lia]) Rc2.
all: prreg HS (3%bv : bv 5) Rc3.
all: prreg HS (4%bv : bv 5) Rc4.
all: rregU HS (10%bv : bv 5) p ltac:(apply U_atom; [rewrite (AG 10%nat), E10e by lia; reflexivity | lia]) Rc10.
all: rregU HS (11%bv : bv 5) (VAL (A_OBJ A_ROW))
  ltac:(apply U_atom; [exact (img_env_atomP E1v 259%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia)) | pose proof (pa_val_range (A_OBJ A_ROW)); lia]) Rc11.
all: rregU HS (12%bv : bv 5) 0 ltac:(apply U_lit; lia) Rc12.
all: rregU HS (13%bv : bv 5) (F + 32) ltac:(rewrite (U_atom_off E1v 516%nat F 32 RF) by lia; reflexivity) Rc13.
all: lazymatch type of Rc2 with getr ?rg _ = _ =>
  assert (Esp : spZ rg = sp1) by (unfold spZ; rewrite Rc2; apply unsigned_lit_small; lia) end.
all: lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_regionP) in
  let j := idx_of_base rs 529%nat in let j := eval vm_compute in j in
  let r2 := eval vm_compute in (nth j rs got_regionP) in
  pose proof (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR516;
  pose proof (st_ok_region_nth Ex ssx msx j r2 HS ltac:(vm_compute; reflexivity)) as HR529 end.
all: cbn [ms_mem restrict] in HR516, HR529.
all: pose proof (field_of_region _ _ 516%nat F _ _ _ _ _ 32 1%N (SOff 11 0) ch HR516 U516
  ltac:(repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (AG 11%nat), (EE 11%nat 11%bv eq_refl) by lia; exact H11)
  ltac:(cbn; lia) ltac:(cbn; lia)) as V32.
all: pose proof (field_of_region _ _ 516%nat F _ _ _ _ _ 33 1%N (SOff 12 0) pm HR516 U516
  ltac:(repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (AG 12%nat), (EE 12%nat 12%bv eq_refl) by lia; exact H12)
  ltac:(cbn; lia) ltac:(cbn; lia)) as V33.
all: pose proof (field_of_region _ _ 516%nat F _ _ _ _ _ 34 1%N (SOff 13 0) v HR516 U516
  ltac:(repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (AG 13%nat), (EE 13%nat 13%bv eq_refl) by lia; exact H13)
  ltac:(cbn; lia) ltac:(cbn; lia)) as V34.
all: pose proof (field_of_region _ _ 529%nat (SB + F / 8) _ _ _ _ _ 4 1%N (SLit 3) 3 HR529 U529
  ltac:(repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VS.
all: cbn [N.to_nat Pos.to_nat] in V32, V33, V34, VS.
all: assert (HF8m : F mod 8 = 0) by (rewrite HFq; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z_mod_mult).
all: assert (D32 : (F + 32) / 8 = F / 8 + 4)
  by (rewrite HF8; replace (F + 32) with ((8 * (F / 64) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia).
all: lazymatch type of VS with val_mem _ (mrestrict ?Hh ?mm) _ _ _ =>
  pose proof (aview_of_val_mem1 _ _ _ _ _ VS ltac:(lia)) as AVs;
  assert (GA : garr8 SEGS (mrestrict Hh mm) (F + 32) [ch; pm; v])
  by (intros j Hj; cbn [length] in Hj;
      destruct j as [|[|[|j]]]; [ | | | lia ]; cbn [nth];
      [ replace (F + 32 + Z.of_nat 0) with (F + 32) by lia; split; [exact V32 | lia]
      | replace (F + 32 + Z.of_nat 1) with (F + 33) by lia; split; [exact V33 | lia]
      | replace (F + 32 + Z.of_nat 2) with (F + 34) by lia; split; [exact V34 | lia] ]);
  pose proof (range_addressable_partial (aview SEGS Hh mm) SHADOW_OFF (F + 32) 3
    ltac:(unfold shadow_of_addr; rewrite D32; replace (SHADOW_OFF + (F / 8 + 4)) with (SB + F / 8 + 4) by (unfold SB, SHADOW_OFF; lia); exact AVs)
    ltac:(replace (F + 32) with ((8 * (F / 64) + 4) * 8) by lia; apply Z_mod_mult) ltac:(lia)) as RA end.
all: lazymatch type of RA with range_addressable (aview _ (w_H ?Wx) ?mm) _ _ _ =>
  assert (TS : tsrc_ok Wx mm sp1 (F + 32) 3)
  by (split; [ intros a Ha; split;
               [ assert (Hc3 : a = F + 32 \/ a = F + 33 \/ a = F + 34) by lia;
                 destruct Hc3 as [-> | [-> | ->]];
                 [ rewrite (aview_of_val_mem1 _ _ _ _ _ V32 ltac:(lia))
                 | rewrite (aview_of_val_mem1 _ _ _ _ _ V33 ltac:(lia))
                 | rewrite (aview_of_val_mem1 _ _ _ _ _ V34 ltac:(lia)) ]; discriminate
               | lia ] |];
      split; [exact RA|];
      split; [ eapply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ 0 fpos);
               [exact (proj1 HJ2) | exact Hfin2 | fold F; lia | change (fs_frame_bytes 0) with 64; fold F; lia | lia] |];
      split; [ eapply amem_range_sub_app; [exact HFapp | exact HFceil | lia | lia | lia] |];
      lia);
  assert (AF : afobj SEGS B lyc S2 Wx mm (F + 32) 3)
  by (split; [ exists 0, fpos; split; [exact Hfin2|]; split; [lia|]; fold F; split; [exact HF8m|];
               change (fs_frame_bytes 0) with 64; lia |];
      split; [replace (F + 32) with ((8 * (F / 64) + 4) * 8) by lia; apply Z_mod_mult | exact RA]) end.
all: pmkst HS.
all: rewrite pa_sigma_ctrl_lay_block.
all: eapply SRr_bind; [ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
       pose proof (TLAY STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W mm _ k rg p (F + 32) ch pm v HJ2) as CALL end;
     unfold cfg_at in CALL; change (w64 (BASE + AF_ctrl_lay_block)) with (Z_to_bv 64 (BASE + AF_ctrl_lay_block)) in CALL;
     apply CALL; clear CALL;
     [ exact (arodata_tcj _ _ _ _ _ _ _ _ _ TK HROD)
     | rewrite Rc1; apply ret_ok_codeptr_v; [lia | reflexivity]
     | unfold raZ; rewrite Rc1, unsigned_lit_small by lia; lia
     | rewrite Rc3, (AG 3%nat), (EE 3%nat 3%bv eq_refl) by lia; exact Hgp
     | rewrite Rc4, (AG 4%nat), (EE 4%nat 4%bv eq_refl) by lia; exact Htp
     | rewrite Rc10; reflexivity
     | rewrite Rc11; reflexivity
     | rewrite Rc12; reflexivity
     | rewrite Rc13; reflexivity
     | rewrite Esp; exact Hsp1al16
     | rewrite Esp; unfold TLAY_STK in *; lia
     | rewrite Esp; lia
     | rewrite Hfrs2; cbn [length]; lia
     | lia | lia
     | unfold amem_range in *; lia
     | intros x Hx; apply Hnimg; lia
     | rewrite Esp; apply (twr_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia
     | rewrite Esp; lia
     | lia | lia
     | rewrite Esp; exact TS
     | exact GA
     | exact AF
     | right; lia ] | ].
all: cbv beta.
all: intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & Eab3 & (f3 & ES3) & HLAY & TK3).
all: rewrite Esp in TK3.
(* the symbolic state at the return point 0x82b98: every region is kept *)
all: aconstsF HJ2 KgA KcA KguA KuA.
all: aconstsF HJ3 KgB KcB KguB KuB.
all: lazymatch type of HS with st_ok _ _ ?ssx _ => let idxs := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
  reseat HS HJ3 HP3 idxs AG ltac:(kept_call TK3 HJ3 AG Hfin2 KgA KgB KcA KcB KguA KguB KuA KuB ltac:(fold F FL)) end.
all: pose proof (tcj_compose _ _ lyc Sc lyc S2 W memc W _ W3 mem3 (spZ regs) sp1 _ _ TK TK3
    ltac:(unfold TLAY_STK in *; lia) ltac:(lia) Hwce ltac:(lia) ltac:(intros a Ha; cbv beta in *; lia)
    ltac:(intros b Hb; rewrite Eab; exact Hb) ltac:(intros f Hf; rewrite Hfrs2; right; exact Hf)
    ltac:(intros c q; reflexivity)) as TK1.
all: clear TK TK3; rename TK1 into TK.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  clear U516 U529 U10 Usp2 Usp60;
  assert (U516 : bv_unsigned (ew Ev 516) = F) by (rewrite RF; apply unsigned_lit_small; lia);
  assert (U529 : bv_unsigned (ew Ev 529) = SB + F / 8) by (rewrite E529; apply unsigned_lit_small; unfold SB; lia);
  assert (U10 : bv_unsigned (ew Ev 10) = p) by (rewrite (AG 10%nat), E10e by lia; apply unsigned_lit_small; lia);
  assert (Usp2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
  assert (Usp60 : bv_unsigned (ew Ev 60) = sp1) by (rewrite E60; apply unsigned_lit_small; lia) end.
(* 0x82b98-0x82ba0: a0 = p, a1 = the row, and the call of ctrl_finish *)
all: rewrite Rc1.
all: assert (Llay : length (lay_z ch pm v) = 32%nat) by reflexivity.
all: paj_run_shc RUNP RUNC HS HJ3;
  [ awrFL_with ltac:(idtac; awr_acc_hd Usp2 Usp60 U516 U529 U10 sp0 (spZ regs) sp1 fpos F) AG fpos F EFA0 | ].
all: ga_upd HLAY AG Llay.
all: tk_upd HARc TK HQ HJ3 AG HEi10.
all: lazymatch type of HS with st_ok _ ?Ex _ _ => let H := rnHEI Ex in
  rregU HS (1%bv : bv 5) (BASE + 9460)
    ltac:(rewrite (U_atom_off Ex 240%nat (VAL A_TEXT) 9460 (img_env_atomP Ex 240%nat H ltac:(unfold A_TEXT, A_LIM; lia))) by lia;
          reflexivity) Rd1 end.
all: rregU HS (2%bv : bv 5) sp1 ltac:(apply U_atom; [exact E60 | lia]) Rd2.
all: prreg HS (3%bv : bv 5) Rd3.
all: prreg HS (4%bv : bv 5) Rd4.
all: rregU HS (10%bv : bv 5) p ltac:(apply U_atom; [rewrite (AG 10%nat), E10e by lia; reflexivity | lia]) Rd10.
all: lazymatch type of HS with st_ok _ ?Ex _ _ => let H := rnHEI Ex in
  rregU HS (11%bv : bv 5) (VAL (A_OBJ A_ROW))
    ltac:(apply U_atom; [exact (img_env_atomP Ex 259%nat H ltac:(unfold A_TEXT, A_LIM; lia)) | pose proof (pa_val_range (A_OBJ A_ROW)); lia]) Rd11 end.
all: lazymatch type of Rd2 with getr ?rg _ = _ =>
  assert (Esp' : spZ rg = sp1) by (unfold spZ; rewrite Rd2; apply unsigned_lit_small; lia) end.
all: pmkst HS.
all: rewrite pa_sigma_ctrl_finish.
all: assert (Lfin : length (map bv_unsigned (RcFin.fin 2 16 6 (bl (lay_z ch pm v)))) = 32%nat)
  by (pose proof (stamp_bytes_z ch pm v Hch Hpm Hv) as HG; apply (f_equal (@length Z)) in HG;
      rewrite length_app in HG; change (length (GAz ch pm v)) with 34%nat in HG;
      change (length [0xcd; 0xea]) with 2%nat in HG; lia).
all: assert (Fz : Forall (fun z => 0 <= z < 256) (lay_z ch pm v))
  by (unfold lay_z, T32z; cbn [firstn skipn app]; repeat constructor; lia).
all: eapply SRr_bind; [ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
       pose proof (TCF STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) ly3 S3 W3 mm _ _ rg p (bl (lay_z ch pm v)) HJ3) as CALL end;
     unfold cfg_at in CALL; change (w64 (BASE + AF_ctrl_finish)) with (Z_to_bv 64 (BASE + AF_ctrl_finish)) in CALL;
     apply CALL; clear CALL;
     [ exact (arodata_tcj _ _ _ _ _ _ _ _ _ TK HROD)
     | rewrite Rd1; apply ret_ok_codeptr_v; [lia | reflexivity]
     | unfold raZ; rewrite Rd1, unsigned_lit_small by lia; lia
     | rewrite Rd3, (AG 3%nat), (EE 3%nat 3%bv eq_refl) by lia; exact Hgp
     | rewrite Rd4, (AG 4%nat), (EE 4%nat 4%bv eq_refl) by lia; exact Htp
     | rewrite Rd10; reflexivity
     | rewrite Rd11; reflexivity
     | rewrite Esp'; exact Hsp1al16
     | rewrite Esp'; unfold TCF_STK in *; lia
     | rewrite Esp'; lia
     | exact (HROW_ck _ _ (arodata_tcj _ _ _ _ _ _ _ _ _ TK HROD))
     | eapply range_addressable_sub; [exact (ro_usable SEGS B LAWS _ _ _ _ _ _ _ (proj1 HJ3) HZS_ROW) | lia | unfold ROW_BYTES; lia]
     | reflexivity
     | rewrite (map_unsigned_bl _ Fz); exact HLAY
     | lia | lia
     | unfold amem_range in *; lia
     | intros x Hx; apply Hnimg; lia
     | rewrite Esp'; apply (twr_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3); lia
     | left; rewrite Esp'; lia
     | exact (proj1 (stack_buf_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (p + 18) 32 HJ3 ltac:(lia) ltac:(lia) ltac:(lia)))
     | exact (proj2 (stack_buf_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (p + 18) 32 HJ3 ltac:(lia) ltac:(lia) ltac:(lia))) ] | ].
all: cbv beta.
all: intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HFIN & TK4).
all: rewrite Esp' in TK4.
all: assert (EFA3 : forall c q, frame_addr ly3 c q = frame_addr lyc c q)
  by (intros c q; pose proof HJ4 as (_ & Hl3 & _); rewrite (frame_addr_le _ _ _ Hl3), (frame_addr_le _ _ _ Hly); reflexivity).
all: assert (EFL3 : forall c q, flag_addr ly3 c q = flag_addr lyc c q)
  by (intros c q; pose proof HJ4 as (_ & Hl3 & _); rewrite (flag_addr_le _ _ _ Hl3), (flag_addr_le _ _ _ Hly); reflexivity).
all: assert (Hfin3 : In (0, fpos) (frames S3)) by (rewrite Hfrs3; exact Hfin2).
all: aconstsF HJ3 KgC KcC KguC KuC.
all: aconstsF HJ4 KgD KcD KguD KuD.
all: lazymatch type of HS with st_ok _ _ ?ssx _ => let idxs := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
  reseat HS HJ4 HP4 idxs AG ltac:(kept_call TK4 HJ4 AG Hfin3 KgC KgD KcC KcD KguC KguD KuC KuD ltac:(rewrite ?EFA3; fold F FL)) end.
all: pose proof (tcj_compose _ _ lyc Sc ly3 S3 W memc W3 _ W3 mem4 (spZ regs) sp1 _ _ TK TK4
    ltac:(unfold TCF_STK in *; lia) ltac:(lia) Hwce ltac:(lia) ltac:(intros a Ha; cbv beta in *; lia)
    ltac:(intros b Hb; rewrite Eab3, Eab; exact Hb) ltac:(intros f Hf; rewrite Hfrs3, Hfrs2; right; exact Hf)
    EFA3) as TK1.
all: clear TK TK4; rename TK1 into TK.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  clear U516 U529 U10 Usp2 Usp60;
  assert (U516 : bv_unsigned (ew Ev 516) = F) by (rewrite RF; apply unsigned_lit_small; lia);
  assert (U529 : bv_unsigned (ew Ev 529) = SB + F / 8) by (rewrite E529; apply unsigned_lit_small; unfold SB; lia);
  assert (U10 : bv_unsigned (ew Ev 10) = p) by (rewrite (AG 10%nat), E10e by lia; apply unsigned_lit_small; lia);
  assert (Usp2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
  assert (Usp60 : bv_unsigned (ew Ev 60) = sp1) by (rewrite E60; apply unsigned_lit_small; lia) end.
(* 0x82ba4-0x82be4: res = 0, the frame marked unusable (0xf5) and its magic
   rewritten: reopen the frame's and the frame shadow's windows *)
all: rewrite Rd1.
all: pose proof (proj1 HJ4) as HAR4.
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR4 Hfin3) as (_ & _ & HFpres4 & HFSpres4).
all: rewrite EFA3 in HFpres4, HFSpres4. 
all: fold F in HFpres4, HFSpres4.
all: change (fs_frame_bytes 0) with 64 in HFpres4, HFSpres4.
all: open_win HS 516%nat 64
  ltac:(rewrite U516; intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HFpres4 (F + o) ltac:(lia)))).
all: open_win HS 529%nat 8
  ltac:(rewrite U529; intros o Ho; apply (apresent_writable SEGS);
        replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, SHADOW_OFF, SB; lia);
        exact (proj1 (HFSpres4 o ltac:(change (64 / 8) with 8; lia)))).
all: st_loop 6%nat RUNP RUNC BR
  ltac:(idtac; awrFL_with ltac:(idtac; first [ awr_frame_hd U516 U529 fpos ltac:(rewrite ?EFA3; fold F)
                                             | awr_acc_hd Usp2 Usp60 U516 U529 U10 sp0 (spZ regs) sp1 fpos F ]) AG fpos F EFA0)
  ltac:(fun HJx => ga_upd HFIN AG Lfin; tk_upd HARc TK HQ HJx AG HEi10).
(* 0x82be8 to the `ret`, then the post with res = 0 *)
all: stamp_flag HS RUNF RET FFL ltac:(fun HJy => ga_upd HFIN AG Lfin; tk_upd HARc TK HQ HJy AG HEi10) HJ4 AG E528 HFLown Hfin3
  ltac:(rewrite ?EFA3, ?EFL3; fold F FL) ltac:(fun H => rewrite EFL3 in H).
all: assert (EabA : ablocks B ly3 S3 = ablocks B lyc Sc) by (rewrite Eab3; exact Eab).
all: post_common HS LAWS HJ4 AG EE E1 Hra Hfrs EabA ltac:(rewrite ES3, ES2; eexists; reflexivity) 0.
all: let R10 := fresh "R10" in prreg HS (10%bv : bv 5) R10; split; [rewrite R10; reflexivity|].
all: split; [exact TK|].
all: rewrite Hleg; split; [reflexivity|].
all: rewrite (stamp_bytes_z ch pm v Hch Hpm Hv); apply garr8_app; split;
  [ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let rs := eval vm_compute in (ss_mem ssx) in
      let i := idx_of_base rs 10%nat in let i := eval vm_compute in i in
      let r := eval vm_compute in (nth i rs got_regionP) in
      pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR10 end;
    cbn [ms_mem restrict] in HR10;
    pose proof (field_of_region_any _ _ 10%nat p _ _ _ _ _ 16 1%N _ HR10 U10 ltac:(repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as W16;
    pose proof (field_of_region_any _ _ 10%nat p _ _ _ _ _ 17 1%N _ HR10 U10 ltac:(repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as W17;
    lazymatch type of W16 with val_mem _ _ _ _ ?vv => replace vv with 205 in W16 by (vm_compute; reflexivity) end;
    lazymatch type of W17 with val_mem _ _ _ _ ?vv => replace vv with 234 in W17 by (vm_compute; reflexivity) end;
    cbn [N.to_nat Pos.to_nat] in W16, W17;
    let j := fresh "j" in let Hj := fresh "Hj" in
    intros j Hj; cbn [length] in Hj; destruct j as [|[|j]]; [ | | lia]; cbn [nth];
    [ replace (p + 16 + Z.of_nat 0) with (p + 16) by lia; split; [exact W16 | lia]
    | replace (p + 16 + Z.of_nat 1) with (p + 17) by lia; split; [exact W17 | lia] ]
  | replace (p + 16 + Z.of_nat (length [205; 234])) with (p + 18) by (cbn; lia); exact HFIN ].
Qed.
End e.
End d.
End b.
