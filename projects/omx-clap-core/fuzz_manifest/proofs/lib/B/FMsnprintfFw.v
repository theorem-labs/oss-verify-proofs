(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfFw.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: new contract of musl __fwritex on musl vsnprintf's FILE (sn_write sink) at
   fm.asan addresses; the frame invariant FWI, fw_phase and the window lemmas follow A/YE3h.v's VI_run / vf_phase /
   vf_windows_sound with the stderr FILE replaced by the snprintf sink. The kit (Section g) is generic in the call's
   band top sp0 + T, so FMsnprintfFl.v reuses it for vfprintf's flush. *)
(* __fwritex (s, l, f) on the snprintf FILE, called from printf_core's out(): the bytes go to vfprintf's 80-byte
   internal buffer, or, when they do not fit, sn_write copies the buffer and the bytes to the destination behind the
   cookie and writes a NUL after them. Stated over the sink invariant SNK (FMsnprintfI.v); no truncation. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YE3e YE3f YE3g YE6g YE39 YE2p YE3i YE3h YF0m YE22 YF0x YE20 YE2y YE7f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMsnprintfI FMsnprintfK FMsnprintfFw0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition w1_s : sstate := Eval vm_compute in (fw0).
Definition w1_e : sstate := Eval vm_compute in fst (RUN w1_s).
Lemma r_w1 : RUN w1_s = (w1_e, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 33 (-80))) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition wA1_s : sstate := Eval vm_compute in (AC w1_e BC_GEU FW_ROOM (SOff 11 0)).
Definition wA1_e : sstate := Eval vm_compute in fst (RUN wA1_s).
Lemma r_wA1 : RUN wA1_s = (wA1_e, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition wA2_s : sstate := Eval vm_compute in (kafter 40 wA1_e 0x8ee0c (-976) (-352) (-272)).
Definition wA2_e : sstate := Eval vm_compute in fst (RUN wA2_s).
Lemma r_wA2 : RUN wA2_s = (wA2_e, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition wB1_s : sstate := Eval vm_compute in (AC w1_e BC_LTU FW_ROOM (SOff 11 0)).
Definition wB1_e : sstate := Eval vm_compute in fst (RUN wB1_s).
Lemma r_wB1 : RUN wB1_s = (wB1_e, RS_stopped (SR_branch BC_LTU (SOff 35 0) (SOff 33 0))). Proof. vm_compute. reflexivity. Qed.
Definition wB2_s : sstate := Eval vm_compute in (AC wB1_e BC_GEU (SOff 35 0) (SOff 33 0)).
Definition wB2_e : sstate := Eval vm_compute in fst (RUN wB2_s).
Lemma r_wB2 : RUN wB2_s = (wB2_e, RS_stopped (SR_branch BC_EQ (SOff 33 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition wZ1_s : sstate := Eval vm_compute in (AC wB2_e BC_EQ (SOff 33 0) (SLit 0)).
Definition wZ1_e : sstate := Eval vm_compute in fst (RUN wZ1_s).
Lemma r_wZ1 : RUN wZ1_s = (wZ1_e, RS_stopped (SR_branch BC_LTU (SOff 35 0) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition wZ2_s : sstate := Eval vm_compute in (AC wZ1_e BC_GEU (SOff 35 0) (SOff 11 0)).
Definition wZ2_e : sstate := Eval vm_compute in fst (RUN wZ2_s).
Lemma r_wZ2 : RUN wZ2_s = (wZ2_e, RS_stopped (SR_branch BC_EQ (SOff 11 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition wN1_s : sstate := Eval vm_compute in (AC wB2_e BC_NE (SOff 33 0) (SLit 0)).
Definition wN1_e : sstate := Eval vm_compute in fst (RUN wN1_s).
Lemma r_wN1 : RUN wN1_s = (wN1_e, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition wN2_s : sstate := Eval vm_compute in (kafter 56 wN1_e 0x9231c (-976) 0 0).
Definition wN2_e : sstate := Eval vm_compute in fst (RUN wN2_s).
Lemma r_wN2 : RUN wN2_s = (wN2_e, RS_stopped (SR_branch BC_LTU (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SOff 35 0)) (SOff 11 0))). Proof. vm_compute. reflexivity. Qed.
Definition wN3_s : sstate := Eval vm_compute in (AC wN2_e BC_GEU (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SOff 35 0)) (SOff 11 0)).
Definition wN3_e : sstate := Eval vm_compute in fst (RUN wN3_s).
Lemma r_wN3 : RUN wN3_s = (wN3_e, RS_stopped (SR_branch BC_EQ (SOff 11 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition wZ3_s : sstate := Eval vm_compute in (AC wZ2_e BC_NE (SOff 11 0) (SLit 0)).
Definition wZ3_e : sstate := Eval vm_compute in fst (RUN wZ3_s).
Lemma r_wZ3 : RUN wZ3_s = (wZ3_e, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition wN4_s : sstate := Eval vm_compute in (AC wN3_e BC_NE (SOff 11 0) (SLit 0)).
Definition wN4_e : sstate := Eval vm_compute in fst (RUN wN4_s).
Lemma r_wN4 : RUN wN4_s = (wN4_e, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition wZ4_s : sstate := Eval vm_compute in (kafter 40 wZ3_e 0x9234c (-976) 0 0).
Definition wZ4_e : sstate := Eval vm_compute in fst (RUN wZ4_s).
Lemma r_wZ4 : RUN wZ4_s = (wZ4_e, RS_stopped (SR_addr (SAlu ALU_ADD (SOff 11 0) (SOff 34 0)))). Proof. vm_compute. reflexivity. Qed.
Definition wN5_s : sstate := Eval vm_compute in (kafter 72 wN4_e 0x9234c (-976) 0 0).
Definition wN5_e : sstate := Eval vm_compute in fst (RUN wN5_s).
Lemma r_wN5 : RUN wN5_s = (wN5_e, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 33 0)) (SOff 34 0)))). Proof. vm_compute. reflexivity. Qed.
Definition wZ5_s : sstate := Eval vm_compute in (set_regs_pc wZ4_e [] 0x92368).
Definition wZ5_e : sstate := Eval vm_compute in fst (RUN wZ5_s).
Lemma r_wZ5 : RUN wZ5_s = (wZ5_e, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition wN6_s : sstate := Eval vm_compute in (set_regs_pc wN5_e [] 0x92368).
Definition wN6_e : sstate := Eval vm_compute in fst (RUN wN6_s).
Lemma r_wN6 : RUN wN6_s = (wN6_e, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
End r.
(* ---- value and branch arithmetic over the engine's U (YP0e.v) ---- *)
Lemma zc_add : forall a b, zcanon (zcanon a + zcanon b) = zcanon (a + b).
Proof. intros a b. unfold zcanon. rewrite <- Zplus_mod. reflexivity. Qed.
Lemma zc_sub : forall a b, zcanon (zcanon a - zcanon b) = zcanon (a - b).
Proof. intros a b. unfold zcanon. rewrite <- Zminus_mod. reflexivity. Qed.
Lemma zc_mul : forall a b, zcanon (zcanon a * zcanon b) = zcanon (a * b).
Proof. intros a b. unfold zcanon. rewrite <- Zmult_mod. reflexivity. Qed.
Lemma zc_shift : forall z k, zcanon (z + k * M64) = zcanon z.
Proof. intros z k. unfold zcanon. apply Z_mod_plus_full. Qed.
(* U of a symbolic value as one zcanon of an integer expression over the atoms *)
Ltac zc_free t := lazymatch t with context [zcanon _] => fail | _ => idtac end.
Ltac zc1 :=
  match goal with
  | |- context [zcanon (zcanon ?a + zcanon ?b)] => zc_free a; zc_free b; rewrite (zc_add a b)
  | |- context [zcanon (zcanon ?a - zcanon ?b)] => zc_free a; zc_free b; rewrite (zc_sub a b)
  | |- context [zcanon (zcanon ?a * zcanon ?b)] => zc_free a; zc_free b; rewrite (zc_mul a b)
  end.
Ltac uz := rewrite ?U_SAlu, ?U_SMd, ?U_SOff, ?U_SLit; cbn [zalu_raw zmd_raw]; repeat zc1.
Lemma bt_ltu : forall E a b, branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = (YP0e.U E a <? YP0e.U E b).
Proof. reflexivity. Qed.
Lemma bt_geu : forall E a b, branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = negb (YP0e.U E a <? YP0e.U E b).
Proof. reflexivity. Qed.
Lemma bt_eq : forall E a b, branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (YP0e.U E a =? YP0e.U E b).
Proof.
intros E a b. cbn [branch_taken]. unfold YP0e.U.
destruct (bv_eqb (sv_denot E a) (sv_denot E b)) eqn:Ee.
- apply bv_eqb_eq in Ee. rewrite Ee. symmetry. apply Z.eqb_refl.
- symmetry. apply Z.eqb_neq. intros Hu. apply bv_eq in Hu. rewrite (proj2 (bv_eqb_eq _ _) Hu) in Ee. discriminate.
Qed.
Lemma bt_ne : forall E a b, branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (YP0e.U E a =? YP0e.U E b).
Proof. intros E a b. change (branch_taken BC_NE (sv_denot E a) (sv_denot E b)) with (negb (branch_taken BC_EQ (sv_denot E a) (sv_denot E b))). rewrite bt_eq. reflexivity. Qed.
Lemma denot_U : forall E e v, YP0e.U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite denot_lit_U, H. reflexivity. Qed.
(* ---- chunk values by offset ---- *)
Fixpoint cv_at (off : Z) (cs : list YP09.chunk) : option cval :=
match cs with
| [] => None
| c :: t => if Z.eqb (YP09.c_off c) off then Some (YP09.c_val c) else cv_at off t
end.
Lemma cv_at_in : forall off cs v, cv_at off cs = Some v -> In (YP09.mkChunk off v) cs.
Proof.
intros off cs v. induction cs as [|[o v'] t IH]; cbn [cv_at]; [discriminate|].
cbn [YP09.c_off YP09.c_val]. destruct (Z.eqb_spec o off) as [->|_].
- intros H. injection H as <-. left. reflexivity.
- intros H. right. exact (IH H).
Qed.
Definition ss_cv (ss : sstate) (ri : nat) (off : Z) : option cval :=
match nth_error (ss_mem ss) ri with
| Some r => match YP09.r_base r with Some 2%nat => cv_at off (YP09.r_chunks r) | _ => None end
| None => None
end.
Definition cv_eqb (c : option cval) (n : BinNums.N) (e : sv) : bool :=
match c with Some (CVal n' e') => N.eqb n' n && sv_eqb e' e | _ => false end.
Lemma cv_eqb_eq : forall c n e, cv_eqb c n e = true -> c = Some (CVal n e).
Proof.
intros [[n' e'| | |]|] n e H; cbn in H; try discriminate.
apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply sv_eqb_eq in H2. subst. reflexivity.
Qed.
(* the FILE fields a sink call does not move, as chunks of the state's FILE region (region 1) *)
Definition fw_fixed (ss : sstate) : bool :=
cv_eqb (ss_cv ss 1 FO) 4 (SLit 0) && cv_eqb (ss_cv ss 1 (FO + 32)) 8 (SOff 2 (IBO + 80)) &&
cv_eqb (ss_cv ss 1 (FO + 56)) 8 (SOff 2 IBO) && cv_eqb (ss_cv ss 1 (FO + 72)) 8 (SLit A_SNW) &&
cv_eqb (ss_cv ss 1 (FO + 88)) 8 (SOff 2 IBO) && cv_eqb (ss_cv ss 1 (FO + 144)) 4 (SLit 0xffffffff) &&
cv_eqb (ss_cv ss 1 (FO + 152)) 8 (SOff 2 CKO).
(* the state's regions all hang off atom 2 inside [-SNK_STK, 0x200) *)
Definition regs_hi (ss : sstate) : bool :=
forallb (fun r => match YP09.r_base r with
| Some 2%nat => (- SNK_STK <=? YP09.r_lo r) && (YP09.r_hi r <=? 0x200) | _ => false end) (ss_mem ss).
Lemma regs_hi_in : forall E ss r a sp0, regs_hi ss = true -> bv_unsigned (ew E 2) = sp0 -> In r (ss_mem ss) ->
base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
sp0 - SNK_STK <= a < sp0 + 0x200.
Proof.
intros E ss r a sp0 Hb Hsp Hin Ha. unfold regs_hi in Hb. rewrite forallb_forall in Hb. specialize (Hb r Hin).
destruct (YP09.r_base r) as [[|[|[|nn]]]|] eqn:Eb; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
try rewrite Eb in Ha. cbn [base_val] in Ha. rewrite Hsp in Ha. lia.
Qed.
Definition cs_list : list Z := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma cs_cases : forall r, acallee_saved r -> r = 2 \/ In r cs_list.
Proof.
intros r Hr. unfold acallee_saved in Hr. unfold cs_list.
destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [left; reflexivity | right; cbn; auto 20 .. |].
right. assert (X : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct X as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; cbn; auto 20.
Qed.
(* ---- the generic sink-call kit: frame base sp0, sink cells, destination [D, D + M), the call's band top
   sp0 + T (T = OSP_FW for __fwritex from printf_core's out(), T = OSP_PC for vfprintf's flush) ---- *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (B : asyms) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
(mem : word -> option byte) (md : Model) (sp0 D M T : Z).
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizesU B OCpy W_MEMCPY.
Hypothesis HB : snk_base B ly S U W mem md sp0.
Hypothesis HDst : snk_dest B ly S W mem D M.
Hypothesis HT : OSP_FW <= T <= OSP_PC.
Lemma st_ok_cv : forall (H : word -> bool) E ss ms ri off (n : BinNums.N) e v,
st_ok tfibsegs E ss (restrict H ms) -> ss_cv ss ri off = Some (CVal n e) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 2) + off) (N.to_nat n) v.
Proof.
intros H E ss ms ri off n e v HS Hc He Hv Hn. unfold ss_cv in Hc.
destruct (nth_error (ss_mem ss) ri) as [r|] eqn:Er; [|discriminate].
destruct (YP09.r_base r) as [[|[|[|nn]]]|] eqn:Eb; try discriminate.
pose proof (cv_at_in _ _ _ Hc) as Hin.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Er)) as (_ & _ & _ & Hcs).
pose proof (val_of_chunk_ok tfibsegs E _ _ off n e v (proj1 (Forall_forall _ _) Hcs _ Hin) He Hv Hn) as X.
rewrite Eb in X. exact X.
Qed.
Lemma st_ok_cv2 : forall (H : word -> bool) E ss ms ri off (n : BinNums.N) e v sp,
st_ok tfibsegs E ss (restrict H ms) -> bv_unsigned (ew E 2) = sp -> ss_cv ss ri off = Some (CVal n e) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (sp + off) (N.to_nat n) v.
Proof. intros H E ss ms ri off n e v sp HS Hsp Hc He Hv Hn. rewrite <- Hsp. exact (st_ok_cv H E ss ms ri off n e v HS Hc He Hv Hn). Qed.
Lemma writable_keep : forall (H : word -> bool) (m m' : word -> option byte) a,
writable_at tfibsegs (mrestrict H m) a -> (apresent H m a -> apresent H m' a) -> writable_at tfibsegs (mrestrict H m') a.
Proof.
intros H m m' a Hw Hp. unfold writable_at, wview, mrestrict in *. unfold apresent in Hp.
revert Hw Hp. destruct (H (Z_to_bv 64 a)); intros Hw Hp; [exact Hw|].
revert Hw Hp. destruct (m (Z_to_bv 64 a)) as [bb|]; intros Hw Hp.
- destruct (Hp (conj eq_refl (ex_intro _ bb eq_refl))) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma ra_keep : forall (rd rd' : reader) p n, (forall s, kLowMemEnd <= s < kHighShadowEnd -> rd' s = rd s) ->
0 <= p -> p + n <= kHighMemEnd -> range_addressable rd SHADOW_OFF p n -> range_addressable rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n Hk Hp Hn H. apply (range_addressable_agree rd rd'); [|exact H].
intros y Hy. apply Hk. pose proof (YE2y.shadow_addr_bounds y ltac:(lia)) as Hb.
unfold shadow_of_addr. unfold shadow_addr in Hb. lia.
Qed.
Lemma hull_keep : forall (rd rd' : reader) p n, (forall s, kLowMemEnd <= s < kHighShadowEnd -> rd' s = rd s) ->
0 <= p -> 0 < n -> p + n <= kHighMemEnd -> shadow_hull_vis rd p n -> shadow_hull_vis rd' p n.
Proof.
intros rd rd' p n Hk Hp Hn Hpn H s Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite Hk; [apply H; exact Hs|].
pose proof (YE2y.shadow_addr_bounds p ltac:(lia)) as B1. pose proof (YE2y.shadow_addr_bounds (p + n - 1) ltac:(lia)) as B2.
pose proof (Z.div_mod (shadow_addr p) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr p) 8 ltac:(lia)).
pose proof (Z.div_mod (shadow_addr (p + n - 1)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr (p + n - 1)) 8 ltac:(lia)).
rewrite C2 in *. rewrite C5 in *. lia.
Qed.
Lemma hull_sub : forall (rd : reader) a len p n, shadow_hull_vis rd a len -> a <= p -> p + n <= a + len -> 0 < n ->
shadow_hull_vis rd p n.
Proof.
intros rd a len p n H H1 H2 Hn s Hs. apply H. unfold shadow_addr in *.
assert (A1 : (SHADOW_OFF + a / 8) / 8 * 8 <= (SHADOW_OFF + p / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (A2 : (SHADOW_OFF + (p + n - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (a + len - 1) / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.
Local Ltac gf :=
  pose proof HB as (HAR & Hac & Hsp44 & Hsp16 & Hstk & Htop & Hsp47 & Hhigh & Hpres & Hzsh);
  pose proof HDst as (HD0 & HDac & HM & Hcan & HDw & HDam & HDra & HDhu);
  assert (HVF : SNK_STK = 9104) by reflexivity; unfold snk_band in Hpres;
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  unfold OSP_FW, OSP_PC in HT.
(* What the sink calls may change, and what they keep. *)
Definition fw_band (a : Z) : Prop := sp0 - SNK_STK <= a < sp0 + T.
Definition fw_fc (a : Z) : Prop := (sp0 + FO + 40 <= a < sp0 + FO + 64) \/ (sp0 + CKO <= a < sp0 + CKO + 16).
Definition FWI (m : word -> option byte) (md1 : Model) : Prop :=
ARU tfibsegs B ly S U W m md1 /\ same_but_materialized md md1 /\
(forall a, sp0 - SNK_STK <= a < sp0 + 0x200 -> apresent (w_H W) m a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ fw_band a -> ~ fw_xw sp0 D M a -> aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) m a).
Lemma FWI_init : FWI mem md.
Proof using All.
gf. split; [exact HAR|]. split; [apply same_but_materialized_refl|]. split; [exact Hpres|].
split; [intros; reflexivity | intros a Ha; exact Ha].
Qed.
Lemma stk_in : forall a, sp0 - SNK_STK <= a < sp0 + 0x200 -> ly_stk_lo ly <= a < ly_stk_hi ly.
Proof using All. intros a Ha. gf. lia. Qed.
Lemma FWI_run : forall m md1 mB mat, FWI m md1 ->
(forall z : word, ~ (sp0 - SNK_STK <= bv_unsigned z < sp0 + 0x200) -> mB z = m z) ->
(forall z : word, ~ fw_band (bv_unsigned z) -> ~ fw_xw sp0 D M (bv_unsigned z) -> mB z = m z) ->
(forall a, sp0 - SNK_STK <= a < sp0 + 0x200 -> apresent (w_H W) mB a) ->
FWI mB (with_vm_backing (m_vm_lazy md1) mat md1).
Proof using All.
intros m md1 mB mat (HA & Hsb & Hp & Hfr & Hpm) HF1 HF2 HpB. gf.
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < sp0 + 0x200) -> aview tfibsegs (w_H W) mB a = aview tfibsegs (w_H W) m a).
{ intros a Hr Ha. apply aview_same. apply HF1. rewrite unsigned_lit_small by lia. exact Ha. }
pose proof (same_but_materialized_frame md1 _ (with_vm_backing_same md1 mat)) as MF.
split; [|split; [|split; [exact HpB|split]]].
- apply (ARU_frame tfibsegs B LAWS ly S U W m md1 mB _ HA).
+ intros a Hr Hown. apply AVB; [exact Hr|]. intros Hs. exact (ARU_stack tfibsegs B LAWS ly S U W m md1 a HA (stk_in a Hs) Hown).
+ intros a Hv. rewrite (aview_mod tfibsegs (w_H W) mB a). rewrite (aview_mod tfibsegs (w_H W) m a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 - SNK_STK)) as [L1|L1]; [rewrite AVB by lia; exact Hv|].
destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 + 0x200)) as [L2|L2]; [| rewrite AVB by lia; exact Hv].
apply aview_some_of_apresent. apply HpB. lia.
+ apply MF. + apply MF. + apply MF.
+ intros a Ha Hh. unfold YG0d.w64 in Hh |- *.
assert (Har : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
destruct (Z_lt_le_dec a (sp0 - SNK_STK)) as [L1|L1];
[apply HF1; rewrite unsigned_lit_small by lia; lia|].
destruct (Z_lt_le_dec a (sp0 + 0x200)) as [L2|L2];
[exfalso; destruct (HpB a ltac:(lia)) as [Hf _]; rewrite Hf in Hh; discriminate Hh|].
apply HF1. rewrite unsigned_lit_small by lia. lia.
- eapply same_but_materialized_trans; [exact Hsb | apply with_vm_backing_same].
- intros a Hr Hb Hx. rewrite <- (Hfr a Hr Hb Hx). apply aview_same. apply HF2; rewrite unsigned_lit_small by lia; assumption.
- intros a Hpa. pose proof (Hpm a Hpa) as Hpa'.
assert (CASE : sp0 - SNK_STK <= a mod 2 ^ 64 < sp0 + 0x200 \/ ~ (sp0 - SNK_STK <= a mod 2 ^ 64 < sp0 + 0x200)) by lia.
rewrite (apresent_mod _ mB a). rewrite (apresent_mod _ m a) in Hpa'.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
destruct CASE as [Hin|Hout]; [apply HpB; exact Hin|].
apply (apresent_same (w_H W) m mB _); [apply HF1; rewrite unsigned_lit_small by lia; exact Hout | exact Hpa'].
Qed.
Lemma FWI_wvb : forall m md1 mat, FWI m md1 -> FWI m (with_vm_backing (m_vm_lazy md1) mat md1).
Proof using All.
intros m md1 mat HI. pose proof HI as (_ & _ & Hp & _ & _).
apply (FWI_run m md1 m mat HI); [intros; reflexivity | intros; reflexivity | exact Hp].
Qed.
Lemma FWI_writable : forall m md1 a, FWI m md1 -> D <= a < D + M -> writable_at tfibsegs (mrestrict (w_H W) m) a.
Proof using All.
intros m md1 a (_ & _ & _ & _ & Hpm) Ha. gf. apply (writable_keep (w_H W) mem m a); [apply (HDw a Ha) | apply Hpm].
Qed.
Lemma FWI_band : forall m md1 a, FWI m md1 -> sp0 - SNK_STK <= a < sp0 + 0x200 ->
writable_at tfibsegs (mrestrict (w_H W) m) a /\ ~ aowned B ly S a.
Proof using All.
intros m md1 a (HA & _ & Hp & _ & _) Ha. split; [apply apresent_writable; apply Hp; exact Ha|].
exact (ARU_stack tfibsegs B LAWS ly S U W m md1 a HA (stk_in a Ha)).
Qed.
(* the shadow (below the band, above the low application memory) is never written *)
Lemma FWI_shadow : forall m md1 s, FWI m md1 -> kLowMemEnd <= s < kHighShadowEnd ->
aview tfibsegs (w_H W) m s = aview tfibsegs (w_H W) mem s.
Proof using All.
intros m md1 s (_ & _ & _ & Hfr & _) Hs. gf.
apply Hfr; [lia | unfold fw_band; lia | ].
unfold fw_xw, CKO, IBO, FO. unfold amem_range in HDam. intros [X|[X|[X|X]]]; lia.
Qed.
Lemma FWI_ra : forall m md1 p n, FWI m md1 -> 0 <= p -> p + n <= kHighMemEnd ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n -> range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF p n.
Proof using All.
intros m md1 p n HI H1 H2 H. apply (ra_keep (aview tfibsegs (w_H W) mem)); [|exact H1 | exact H2 | exact H].
intros s Hs. exact (FWI_shadow m md1 s HI Hs).
Qed.
Lemma FWI_hull : forall m md1 p n, FWI m md1 -> 0 <= p -> 0 < n -> p + n <= kHighMemEnd ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) p n -> shadow_hull_vis (aview tfibsegs (w_H W) m) p n.
Proof using All.
intros m md1 p n HI H1 H2 H3 H. apply (hull_keep (aview tfibsegs (w_H W) mem)); [|exact H1 | exact H2 | exact H3 | exact H].
intros s Hs. exact (FWI_shadow m md1 s HI Hs).
Qed.
Lemma band_ra : forall m md1 p n, FWI m md1 -> sp0 - SNK_STK <= p -> p + n <= sp0 + 0x200 ->
range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF p n.
Proof using All.
intros m md1 p n HI H1 H2. gf.
apply (FWI_ra m md1 p n HI); [lia | lia |].
apply (range_addressable_sub _ _ (sp0 - SNK_STK) (SNK_STK + 0x200)); [| lia | lia].
apply zero_shadow_range; [|rewrite HVF; reflexivity | exact Hzsh].
pose proof (Z.div_mod sp0 16 ltac:(lia)) as X. rewrite Hsp16, Z.add_0_r in X.
rewrite X, HVF. replace (16 * (sp0 / 16) - 9104) with ((2 * (sp0 / 16) - 1138) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma band_hull : forall m md1 p n, FWI m md1 -> sp0 - SNK_STK + 64 <= p -> p + n <= sp0 + 0x200 - 64 -> 0 < n ->
shadow_hull_vis (aview tfibsegs (w_H W) m) p n.
Proof using All.
intros m md1 p n HI H1 H2 Hn. gf.
apply (FWI_hull m md1 p n HI); [lia | lia | lia |].
intros s Hs.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as X. rewrite Hsp16, Z.add_0_r in X.
assert (Hz : forall i, 0 <= i < (SNK_STK + 0x200) / 8 ->
aview tfibsegs (w_H W) mem (shadow_of_addr SHADOW_OFF (sp0 - SNK_STK) + i) = Some 0) by exact Hzsh.
replace s with (shadow_of_addr SHADOW_OFF (sp0 - SNK_STK) + (s - shadow_of_addr SHADOW_OFF (sp0 - SNK_STK))) by lia.
rewrite Hz; [discriminate|].
rewrite HVF in *. change ((9104 + 0x200) / 8) with 1202.
unfold shadow_of_addr, shadow_addr in *.
replace (sp0 - 9104) with ((2 * (sp0 / 16) - 1138) * 8) by lia. rewrite Z.div_mul by lia.
pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)).
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma band_amem : forall p n, sp0 - SNK_STK <= p -> p + n <= sp0 -> amem_range p n.
Proof using All. intros p n H1 H2. gf. unfold amem_range. right. lia. Qed.
Lemma dest_ra : forall m md1 p n, FWI m md1 -> D <= p -> p + n <= D + M ->
range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF p n.
Proof using All.
intros m md1 p n HI H1 H2. gf. unfold amem_range in HDam.
apply (FWI_ra m md1 p n HI); [lia | lia |].
exact (range_addressable_sub _ _ D M p n HDra H1 H2).
Qed.
Lemma dest_hull : forall m md1 p n, FWI m md1 -> D <= p -> p + n <= D + M -> 0 < n ->
shadow_hull_vis (aview tfibsegs (w_H W) m) p n.
Proof using All.
intros m md1 p n HI H1 H2 Hn. gf. unfold amem_range in HDam.
apply (FWI_hull m md1 p n HI); [lia | lia | lia |].
exact (hull_sub _ D M p n HDhu H1 H2 Hn).
Qed.
Lemma dest_amem : forall p n, D <= p -> p + n <= D + M -> amem_range p n.
Proof using All. intros p n H1 H2. gf. unfold amem_range in *. lia. Qed.
Definition fw_winb (t : option nat * Z * Z) : bool :=
match t with
| (Some 2%nat, lo, hi) =>
((- SNK_STK <=? lo) && (hi <=? T)) || ((lo =? FO + 40) && (hi =? FO + 64)) || ((lo =? CKO) && (hi =? CKO + 16))
| _ => false
end || (snd t <=? snd (fst t)).
Definition fw_windows_ok (ss : sstate) : bool := forallb fw_winb (windows (ss_mem ss)).
Lemma fw_windows_sound : forall E ss a, fw_windows_ok ss = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> fw_band a \/ fw_fc a.
Proof.
intros E ss a Hb Hsp Hin. unfold fw_band, fw_fc.
destruct (in_wrange_windows E _ a Hin) as (bb & lo & hi & Ht & Hr).
unfold fw_windows_ok in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht). unfold fw_winb in Hb.
apply orb_prop in Hb as [Hb|Hb].
- destruct bb as [[|[|[|nn]]]|]; try discriminate Hb. cbn [base_val] in Hr. rewrite Hsp in Hr.
repeat (apply orb_prop in Hb as [Hb|Hb]); repeat (apply andb_prop in Hb as [? Hb]);
repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end;
unfold CKO, FO in *; lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Definition in_wrangeb (E : env) (rs : smem) (a : Z) : bool :=
existsb (fun r => (base_val E (YP09.r_base r) + YP09.r_wlo r <=? a) && (a <? base_val E (YP09.r_base r) + YP09.r_whi r))%bool rs.
Lemma in_wrangeb_false : forall E rs a, in_wrangeb E rs a = false -> ~ in_wrange E rs a.
Proof.
intros E rs a H (r & Hin & Ha). unfold in_wrangeb in H.
assert (X : existsb (fun r => (base_val E (YP09.r_base r) + YP09.r_wlo r <=? a) && (a <? base_val E (YP09.r_base r) + YP09.r_whi r))%bool rs = true).
{ apply existsb_exists. exists r. split; [exact Hin|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite X in H. discriminate H.
Qed.
Lemma in_wrangeb_true : forall E rs a, in_wrangeb E rs a = true -> in_wrange E rs a.
Proof.
intros E rs a H. unfold in_wrangeb in H. apply existsb_exists in H as (r & Hin & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists r. split; [exact Hin | lia].
Qed.
Lemma win_writable : forall E ss ms a, st_ok tfibsegs E ss ms -> in_wrange E (ss_mem ss) a -> writable_at tfibsegs (ms_mem ms) a.
Proof.
intros E ss ms a HS (r & Hin & Ha).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _).
pose proof (proj1 (Forall_forall _ _) Hok r Hin) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.
Lemma in_wrange_windows_eq : forall E rs rs' a, windows rs' = windows rs -> in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs rs' a Hw Hin. destruct (in_wrange_windows E rs a Hin) as (bb & lo & hi & Ht & Hr).
rewrite <- Hw in Ht. unfold windows in Ht. apply in_map_iff in Ht as (r & Er & Hr').
injection Er as E1 E2 E3. exists r. split; [exact Hr'|]. rewrite E1, E2, E3. exact Hr.
Qed.
(* A symbolic run: st_ok kept, FWI kept, every byte outside the band and the FILE / cookie windows kept. *)
Lemma fw_phase : forall E ss ss' st ms md1,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tfibmusl_tbl FUEL ss = (ss', st) -> st <> RS_ecall ->
fw_windows_ok ss = true -> windows (ss_mem ss') = windows (ss_mem ss) -> bv_unsigned (ew E 2) = sp0 ->
FWI (ms_mem ms) md1 ->
SRr tfibsegs W (mkCfg ms md1)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md1) mat1 md1) /\
st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\ FWI (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat1 md1) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ fw_band a -> ~ fw_fc a ->
aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) (ms_mem ms) a)).
Proof using All.
intros E ss ss' st ms md1 HS Hrun Hst Hwok Hweq Hsp HI. gf.
eapply SRr_mono; [apply (vf_phase W E ss ss' st ms md1 HS Hrun)|].
cbv beta. intros W' c' _ (-> & ms1 & mat1 & -> & HS1 & HF & HFr).
assert (HS1' : st_ok tfibsegs E ss' (restrict (w_H W) ms1)) by (destruct st; [exact HS1 | contradiction | exact HS1]).
split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1'|].
split.
- apply (FWI_run (ms_mem ms) md1 (ms_mem ms1) mat1 HI).
+ intros z Hz. apply HF. intros Hin. destruct (fw_windows_sound E ss _ Hwok Hsp Hin) as [Hw|[Hw|Hw]];
unfold fw_band, CKO, FO in *; lia.
+ intros z Hb Hx. apply HF. intros Hin. destruct (fw_windows_sound E ss _ Hwok Hsp Hin) as [Hw|[Hw|Hw]];
[apply Hb; exact Hw | apply Hx; right; left; exact Hw | apply Hx; right; right; left; exact Hw].
+ intros a Ha. destruct (in_wrangeb E (ss_mem ss) a) eqn:Ew.
* apply in_wrangeb_true in Ew. apply (in_wrange_windows_eq E _ (ss_mem ss') a Hweq) in Ew.
pose proof (win_writable E ss' (restrict (w_H W) ms1) a HS1' Ew) as Hwr. cbn [restrict ms_mem] in Hwr.
apply (apresent_of_writable (w_H W) (ms_mem ms1) a); [lia | apply high_not_img; lia | exact Hwr].
* apply in_wrangeb_false in Ew. destruct HI as (_ & _ & Hp & _).
pose proof (Hp a Ha) as [Hh [bb Hbb]]. split; [exact Hh|]. exists bb.
rewrite (HF (Z_to_bv 64 a)); [exact Hbb|]. rewrite unsigned_lit_small by lia. exact Ew.
- intros a Hr Hb Hf. apply aview_same. apply HF. rewrite unsigned_lit_small by lia. intros Hin.
destruct (fw_windows_sound E ss _ Hwok Hsp Hin) as [Hw|Hw]; [exact (Hb Hw) | exact (Hf Hw)].
Qed.
Lemma unp_high : forall (m : word -> option byte) md1 a, ARU tfibsegs B ly S U W m md1 -> kHighMemBeg <= a < 2 ^ 64 ->
unpoison U m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros m md1 a HA Ha. apply unpoison_out. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [|reflexivity].
exfalso. pose proof (ush_facts tfibsegs B ly S U W m md1 _ HA Ei) as (_ & _ & L2).
assert (Ha0 : 0 <= a) by (unfold kHighMemBeg in Ha; lia).
rewrite unsigned_lit_small in L2 by lia. lia.
Qed.
(* A memcpy interceptor call met by the walk (pc = memcpy's wrapper), handled by the ARU memcpy contract. *)
Lemma fw_mcpy : forall E ss ms md1 r0 rest k ra osp xlo xhi (dsv xsv nsv : sv) (d xs n : Z),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = W_MEMCPY -> ss_resv ss = None -> bv_unsigned (ew E 2) = sp0 ->
ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - SNK_STK -> YP09.r_hi r0 = 0 ->
- SNK_STK <= YP09.r_wlo r0 -> YP09.r_whi r0 <= 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp ->
sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = dsv -> sv_denot E dsv = w64 d -> sr_get (ss_regs ss) 11 = xsv -> sv_denot E xsv = w64 xs ->
sr_get (ss_regs ss) 12 = nsv -> sv_denot E nsv = w64 n ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (kafter k ss ra osp xlo xhi)) = true ->
no_cdata (ss_mem (kafter k ss ra osp xlo xhi)) = true ->
mem_atoms_lt k (ss_mem (kafter k ss ra osp xlo xhi)) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - SNK_STK <= osp -> osp <= T -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
(forall a, d <= a < d + n -> fw_xw sp0 D M a) ->
(forall a, d <= a < d + n -> sp0 - SNK_STK <= a < sp0 -> sp0 + xlo <= a < sp0 + xhi) ->
(forall a, d <= a < d + n -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) a /\ ~ aowned B ly S a /\
~ (sp0 + osp - ESTACK <= a < sp0 + osp)) ->
amem_range d n -> range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) d n) ->
0 <= xs -> xs + n <= 2 ^ 63 ->
(forall a, xs <= a < xs + n -> aview tfibsegs (w_H W) (ms_mem ms) a <> None /\ ~ (sp0 + osp - ESTACK <= a < sp0 + osp)) ->
(d + n <= xs \/ xs + n <= d) -> amem_range xs n ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF xs n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) xs n) ->
(forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
0 <= a < 2 ^ 64 /\ ~ (sp0 + osp - ESTACK <= a < sp0 + osp) /\ ~ (d <= a < d + n)) ->
(forall r a, In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> apresent (w_H W) (ms_mem ms) a) ->
FWI (ms_mem ms) md1 ->
SRr tfibsegs W (mkCfg ms md1)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md1) mat2 md1) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (kafter k ss ra osp xlo xhi) (restrict (w_H W) ms2) /\
FWI (ms_mem ms2) (with_vm_backing (m_vm_lazy md1) mat2 md1) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) (ms_mem ms2) (d + i) = aview tfibsegs (w_H W) (ms_mem ms) (xs + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (d <= a < d + n) ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a)).
Proof using All.
intros E ss ms md1 r0 rest k ra osp xlo xhi dsv xsv nsv d xs n HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 Hd S11 Hx S12 Hn Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hra Hra2 Hn32 Hd0 Hdn Hdxw Hdwin Hdok Hdam Hdra Hdhu
Kx0 Kxn Kxok Hdisj Kxam Kxra Kxhu Hrest HrestW HI.
gf. assert (HES : ESTACK = 4096) by reflexivity.
pose proof HI as (HA & Hsb & Hps & Hfr & Hpm).
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (R10 : getr regsT 10 = w64 d) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10; exact Hd).
assert (R11 : getr regsT 11 = w64 xs) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS), S11; exact Hx).
assert (R12 : getr regsT 12 = w64 n) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS), S12; exact Hn).
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
eapply SRr_mono.
{ apply (kcall W E ss ms md1 sp0 SNK_STK r0 rest k ra osp xlo xhi ESTACK (fun a => d <= a < d + n)
(fun regs2 mem2 md2 => ARU tfibsegs B ly S U W mem2 md2 /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem2 (d + i) = aview tfibsegs (w_H W) (ms_mem ms) (xs + i)))
HS Hrv Usp Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0 S1 S2 Hat Hwf2 Hnc2 Hma2 Hci0); try lia.
- intros a Ha Hs. exact (Hdwin a Ha Hs).
- intros r a Hr Ha. destruct (Hrest r a Hr Ha) as (Hr64 & Hb & Hx'). split; [exact Hr64|]. split; [exact Hb | exact Hx'].
- exact HrestW.
- intros a Ha. apply Hps. lia.
- rewrite Hpc. pose proof AMEMCPY as AM. unfold aintrin_realizesU in AM.
eapply SRr_mono.
{ apply (AM ly S U W regsT (ms_mem ms) md1 d xs n).
- split; [|split; [exact (ARU_ok tfibsegs B ly S U W _ md1 HA) | exact (ARU_poisoned tfibsegs B ly S U W _ md1 HA)]].
split; [exact (ARU_AR tfibsegs B ly S U W _ md1 HA)|].
split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; exact Hra2 |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|].
split; [intros a Ha; destruct (Hps a ltac:(lia)) as [Hh [bb Hbb]]; split; [exact Hh|]; exists bb;
rewrite (unp_high (ms_mem ms) md1 a HA) by lia; exact Hbb|].
split; [exact R3 | exact R4].
- exact R10. - exact R11. - exact R12.
- lia. - lia. - lia.
- intros a Ha. rewrite HspT. exact (Hdok a Ha).
- exact Hdam. - exact Hdra. - exact Hdhu.
- split; [lia|]. split; [lia|]. split.
+ intros a Ha. rewrite HspT. exact (Kxok a Ha).
+ split; [exact Hdisj|]. split; [exact Kxam|]. split; [exact Kxra | exact Kxhu]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite R1; f_equal; f_equal; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
split; [exact HP|]. split; [exact Hsbm|].
split; [intros a Hr Hb Hx'; rewrite HspT in Hfr2; apply Hfr2; assumption|].
split; [exact Hpres2|]. split; [exact HAR2 | exact Heff]. }
cbv beta. intros W' c' _ (-> & ms2 & mat2 & -> & HS2 & HP2 & Hfr2 & Hpm2 & HAR2 & Heff2).
split; [reflexivity|]. exists ms2, mat2. split; [reflexivity|]. split; [exact HS2|].
split; [|split; [exact HP2 | split; [exact Heff2 | exact Hfr2]]].
split; [exact HAR2|].
split; [eapply same_but_materialized_trans; [exact Hsb | apply with_vm_backing_same]|].
split; [intros a Ha; apply Hpm2; apply Hps; exact Ha|].
split; [|intros a Hpa; apply Hpm2; apply Hpm; exact Hpa].
intros a Hr Hb Hx'. rewrite Hfr2; [apply Hfr; assumption | exact Hr | unfold fw_band in *; lia |].
intros Hd'. apply Hx'. apply Hdxw. exact Hd'.
Qed.
(* The byte store `sb zero, 0(a0)` of sn_write's `*c->s = 0` (0x92364), at a in the destination: FWI kept. *)
Lemma FWI_store : forall m md1 m' mat a, FWI m md1 -> D <= a < D + M ->
writable_at tfibsegs (mrestrict (w_H W) m) a ->
(forall z : word, m' z = if bv_eqb z (Z_to_bv 64 a) then Some (Z_to_bv 8 0) else m z) ->
FWI m' (with_vm_backing (m_vm_lazy md1) mat md1).
Proof using All.
intros m md1 m' mat a (HA & Hsb & Hp & Hfr & Hpm) Ha Hw Hm. gf.
assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
pose proof (writable_unhidden W m a Ha64 Hw) as Hh.
assert (OUT : forall y, 0 <= y < 2 ^ 64 -> y <> a -> m' (Z_to_bv 64 y) = m (Z_to_bv 64 y)).
{ intros y Hy Hya. rewrite Hm. destruct (bv_eqb (Z_to_bv 64 y) (Z_to_bv 64 a)) eqn:Ee; [|reflexivity].
apply bv_eqb_eq in Ee. exfalso. apply Hya. apply (f_equal bv_unsigned) in Ee. rewrite !unsigned_lit_small in Ee by lia. exact Ee. }
assert (AT : m' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) by (rewrite Hm, (proj2 (bv_eqb_eq _ _) eq_refl); reflexivity).
pose proof (same_but_materialized_frame md1 _ (with_vm_backing_same md1 mat)) as MF.
split; [|split; [|split; [|split]]].
- apply (ARU_frame tfibsegs B LAWS ly S U W m md1 m' _ HA).
+ intros y Hy Hown. apply aview_same. apply OUT; [exact Hy|]. intros ->. exact (proj1 (proj2 (HDw a Ha)) Hown).
+ intros y Hv. rewrite (aview_mod tfibsegs (w_H W) m' y). rewrite (aview_mod tfibsegs (w_H W) m y) in Hv.
destruct (Z.eq_dec (y mod 2 ^ 64) a) as [Ey|Hne].
* rewrite Ey. unfold aview, mbyte, mrestrict. rewrite Hh, AT. simpl. discriminate.
* rewrite (aview_same _ m m'); [exact Hv|]. apply OUT; [apply Z.mod_pos_bound; lia | exact Hne].
+ apply MF. + apply MF. + apply MF.
+ intros y Hy Hhy. unfold YG0d.w64 in *.
assert (Hy64 : 0 <= y < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hy; lia).
apply OUT; [exact Hy64|]. intros ->. rewrite Hh in Hhy. discriminate.
- eapply same_but_materialized_trans; [exact Hsb | apply with_vm_backing_same].
- intros y Hy. apply (apresent_same (w_H W) m m'); [apply OUT; lia | exact (Hp y Hy)].
- intros y Hy Hb Hx. rewrite <- (Hfr y Hy Hb Hx). apply aview_same. apply OUT; [exact Hy|].
intros ->. apply Hx. right; right; right. exact Ha.
- intros y Hpy. pose proof (Hpm y Hpy) as Hpy'. rewrite (apresent_mod _ m' y). rewrite (apresent_mod _ m y) in Hpy'.
destruct (Z.eq_dec (y mod 2 ^ 64) a) as [Ey|Hne].
+ rewrite Ey. split; [exact Hh | exists (Z_to_bv 8 0); exact AT].
+ apply (apresent_same (w_H W) m m'); [apply OUT; [apply Z.mod_pos_bound; lia | exact Hne] | exact Hpy'].
Qed.
(* The engine stops at that store (an address outside every region): kstore0 steps it. *)
Lemma fw_nul : forall E ss ms md1 a,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = 0x92364 -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> regs_hi ss = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 a -> D <= a < D + M -> FWI (ms_mem ms) md1 ->
SRr tfibsegs W (mkCfg ms md1)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md1) mat1 md1) /\
st_ok tfibsegs E (set_regs_pc ss [] 0x92368) (restrict (w_H W) ms1) /\
FWI (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat1 md1) /\
aview tfibsegs (w_H W) (ms_mem ms1) a = Some 0 /\
(forall y, 0 <= y < 2 ^ 64 -> y <> a -> aview tfibsegs (w_H W) (ms_mem ms1) y = aview tfibsegs (w_H W) (ms_mem ms) y)).
Proof using All.
intros E ss ms md1 a HS Hpc Hrv Hsp Hhi R10 Ha HI. gf.
assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
pose proof (FWI_writable _ _ a HI Ha) as Hw.
eapply SRr_mono.
{ apply (kstore0 tfibmusl_tbl W E ss ms md1 0x92364 327715 10%bv a tfibmusl_tbl_ok HS Hpc Hrv);
[lia | lia | vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv | exact R10 | exact Ha64 | exact Hw |].
intros r y Hr Hy Heq. pose proof (regs_hi_in E ss r y sp0 Hhi Hsp Hr Hy) as Hy'.
apply (f_equal bv_unsigned) in Heq. rewrite !unsigned_lit_small in Heq by lia. lia. }
cbv beta. intros W' c' _ (-> & ms1 & mat1 & -> & HS1 & HR1 & HM1).
split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|].
split; [exact (FWI_store _ _ _ mat1 a HI Ha Hw HM1)|].
split.
- unfold aview, mbyte, mrestrict. rewrite (writable_unhidden W (ms_mem ms) a Ha64 Hw), HM1, (proj2 (bv_eqb_eq _ _) eq_refl).
reflexivity.
- intros y Hy Hya. apply aview_same. rewrite HM1. destruct (bv_eqb (Z_to_bv 64 y) (Z_to_bv 64 a)) eqn:Ee; [|reflexivity].
apply bv_eqb_eq in Ee. apply (f_equal bv_unsigned) in Ee. rewrite !unsigned_lit_small in Ee by lia. contradiction.
Qed.
(* The `ret` of the sink call: back at ra with the snk_post. *)
Definition fw_cs_ok (ss : sstate) : bool :=
sv_eqb (sr_get (ss_regs ss) 1) (SOff 1 0) && sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 2)) (SOff 2 T) &&
forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) cs_list.
Lemma fw_ret : forall regs E ss ms md1 v sv10 (Q : (word -> option byte) -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
clookup tfibmusl_tbl (ss_pc ss) = Some RET_WORD_r -> bv_unsigned (ew E 2) = sp0 ->
(forall i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
fw_cs_ok ss = true -> YK0s.ret_ok (getr regs 1) -> getr regs 2 = w64 (sp0 + T) ->
sr_get (ss_regs ss) 10 = sv10 -> sv_denot E sv10 = w64 v ->
FWI (ms_mem ms) md1 -> Q (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md1) (snk_post B ly S U W regs mem md sp0 (sp0 + T) (fw_xw sp0 D M) v Q).
Proof using All.
intros regs E ss ms md1 v sv10 Q HS Hrv Hpc Hsp HE Hcs Hra G2 S10 H10 HI HQ.
unfold fw_cs_ok in Hcs. apply andb_prop in Hcs as [Hcs HL]. apply andb_prop in Hcs as [H1 H2].
apply sv_eqb_eq in H1. apply sv_eqb_eq in H2. rewrite forallb_forall in HL.
eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx_tfa W E ss ms md1 _ HS Hrv Hpc).
intros mat'.
assert (R1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), H1. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply HE; [discriminate | reflexivity]. }
unfold snk_post. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md1) mat' md1).
split.
{ unfold cfg_at. rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. unfold raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact (FWI_wvb _ _ mat' HI)|].
split.
{ intros r Hr. destruct (cs_cases r Hr) as [->|Hin].
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ (Z_to_bv 5 2) HS), H2. cbn [sv_denot]. rewrite Hsp.
transitivity (w64 (sp0 + T)); [reflexivity|]. rewrite <- G2. f_equal. all: try (apply bv_eq; reflexivity).
- assert (Hr32 : 3 <= r <= 27) by (unfold cs_list in Hin; cbn in Hin; lia).
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ (Z_to_bv 5 r) HS).
pose proof (HL r Hin) as Hc. apply sv_eqb_eq in Hc. rewrite Hc.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply HE; [lia|].
rewrite Z_to_bv_unsigned, Z2Nat.id by lia. unfold bv_wrap. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 5) with 32. lia. }
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10. exact H10. }
exact HQ.
Qed.
(* The fixed FILE fields of a state, as val_mem facts in SNK's form. *)
Lemma fw_fixed_ok : forall E ss ms, st_ok tfibsegs E ss (restrict (w_H W) ms) -> bv_unsigned (ew E 2) = sp0 ->
fw_fixed ss = true ->
val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + FO) 4 0 /\
val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + FO + 32) 8 (sp0 + IBO + 80) /\
val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + FO + 56) 8 (sp0 + IBO) /\
val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + FO + 72) 8 A_SNW /\
val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + FO + 88) 8 (sp0 + IBO) /\
val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + FO + 144) 4 0xffffffff /\
val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + FO + 152) 8 (sp0 + CKO).
Proof using All.
intros E ss ms HS Hsp Hf. gf. unfold fw_fixed in Hf.
apply andb_prop in Hf as [Hf F152]. apply andb_prop in Hf as [Hf F144]. apply andb_prop in Hf as [Hf F88].
apply andb_prop in Hf as [Hf F72]. apply andb_prop in Hf as [Hf F56]. apply andb_prop in Hf as [F0 F32].
apply cv_eqb_eq in F0, F32, F56, F72, F88, F144, F152.
rewrite <- !Z.add_assoc.
split; [apply (st_ok_cv2 _ E ss ms 1 FO 4 (SLit 0) 0 sp0 HS Hsp F0); [reflexivity | zside | zside]|].
split; [apply (st_ok_cv2 _ E ss ms 1 (FO + 32) 8 (SOff 2 (IBO + 80)) _ sp0 HS Hsp F32);
[cbn [sv_denot]; rewrite Hsp; reflexivity | unfold IBO; zside | zside]|].
split; [apply (st_ok_cv2 _ E ss ms 1 (FO + 56) 8 (SOff 2 IBO) _ sp0 HS Hsp F56);
[cbn [sv_denot]; rewrite Hsp; reflexivity | unfold IBO; zside | zside]|].
split; [apply (st_ok_cv2 _ E ss ms 1 (FO + 72) 8 (SLit A_SNW) _ sp0 HS Hsp F72);
[reflexivity | unfold A_SNW; zside | zside]|].
split; [apply (st_ok_cv2 _ E ss ms 1 (FO + 88) 8 (SOff 2 IBO) _ sp0 HS Hsp F88);
[cbn [sv_denot]; rewrite Hsp; reflexivity | unfold IBO; zside | zside]|].
split; [apply (st_ok_cv2 _ E ss ms 1 (FO + 144) 4 (SLit 0xffffffff) _ sp0 HS Hsp F144);
[reflexivity | zside | zside]|].
apply (st_ok_cv2 _ E ss ms 1 (FO + 152) 8 (SOff 2 CKO) _ sp0 HS Hsp F152);
[cbn [sv_denot]; rewrite Hsp; reflexivity | unfold CKO, FO; zside | zside].
Qed.
(* SNK of a state's memory: the FILE fields from the state's chunks, the buffer / destination bytes as given. *)
Lemma snk_intro : forall E ss ms N' out' b' w' ewp ecs ecn,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> bv_unsigned (ew E 2) = sp0 -> fw_fixed ss = true ->
w' = Z.of_nat (length out') - b' ->
ss_cv ss 1 (FO + 40) = Some (CVal 8 ewp) -> sv_denot E ewp = Z_to_bv 64 (sp0 + IBO + b') ->
ss_cv ss 2 CKO = Some (CVal 8 ecs) -> sv_denot E ecs = Z_to_bv 64 (D + w') ->
ss_cv ss 2 (CKO + 8) = Some (CVal 8 ecn) -> sv_denot E ecn = Z_to_bv 64 (N' - 1 - w') ->
(forall i, 0 <= i < b' -> aview tfibsegs (w_H W) (ms_mem ms) (sp0 + IBO + i) = Some (nth (Z.to_nat (w' + i)) out' 0)) ->
(forall i, 0 <= i < w' -> aview tfibsegs (w_H W) (ms_mem ms) (D + i) = Some (nth (Z.to_nat i) out' 0)) ->
aview tfibsegs (w_H W) (ms_mem ms) (D + w') = Some 0 ->
0 <= b' <= 80 -> b' <= Z.of_nat (length out') -> Z.of_nat (length out') <= N' - 1 -> N' <= 2 ^ 30 ->
Forall (fun z => 0 <= z < 256) out' ->
SNK W (ms_mem ms) sp0 D N' out' b'.
Proof using All.
intros E ss ms N' out' b' w' ewp ecs ecn HS Hsp Hf Hw' Cwp Dwp Ccs Dcs Ccn Dcn HIB HDB HDN Hb1 Hb2 Hb3 HN' HF.
gf. pose proof (fw_fixed_ok E ss ms HS Hsp Hf) as (F0 & F32 & F56 & F72 & F88 & F144 & F152).
unfold SNK. cbv zeta. rewrite <- Hw'.
split; [exact F0|]. split; [exact F32|].
split; [replace (sp0 + FO + 40) with (sp0 + (FO + 40)) by lia;
apply (st_ok_cv2 _ E ss ms 1 (FO + 40) 8 ewp _ sp0 HS Hsp Cwp Dwp); [unfold IBO; zside | zside]|].
split; [exact F56|]. split; [exact F72|]. split; [exact F88|]. split; [exact F144|]. split; [exact F152|].
split; [apply (st_ok_cv2 _ E ss ms 2 CKO 8 ecs _ sp0 HS Hsp Ccs Dcs); [zside | zside]|].
split; [replace (sp0 + CKO + 8) with (sp0 + (CKO + 8)) by lia;
apply (st_ok_cv2 _ E ss ms 2 (CKO + 8) 8 ecn _ sp0 HS Hsp Ccn Dcn); [zside | zside]|].
split; [exact HIB|]. split; [exact HDB|]. split; [exact HDN|].
repeat split; try lia. exact HF.
Qed.
End g.
Lemma T_FW : OSP_FW <= OSP_FW <= OSP_PC.
Proof. unfold OSP_FW, OSP_PC. lia. Qed.
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AMEMCPY : aintrin_realizesU B OCpy W_MEMCPY.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (sp0 D N M : Z) (out : list Z) (b x : Z) (bs : list Z).
Let l := Z.of_nat (length bs).
Let w := Z.of_nat (length out) - b.
(* snk_base *)
Hypothesis HAR : ARU tfibsegs B ly S U W mem md.
Hypothesis Hac : alloc_ceiling <= ly_stk_lo ly.
Hypothesis Hsp44 : 2 ^ 44 <= sp0.
Hypothesis Hsp16 : sp0 mod 16 = 0.
Hypothesis Hstk : ly_stk_lo ly + SNK_STK <= sp0.
Hypothesis Htop : sp0 + 0x200 <= ly_stk_hi ly.
Hypothesis Hsp47 : sp0 + 0x200 <= 2 ^ 47.
Hypothesis Hhigh : kHighMemBeg <= sp0 - SNK_STK.
Hypothesis Hpres : forall a, sp0 - SNK_STK <= a < sp0 + 0x200 -> apresent (w_H W) mem a.
Hypothesis Hzsh : zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (sp0 - SNK_STK) (SNK_STK + 0x200).
(* snk_regs and the arguments *)
Hypothesis G1 : YK0s.ret_ok (getr regs 1).
Hypothesis G2 : getr regs 2 = w64 (sp0 + OSP_FW).
Hypothesis G3 : getr regs 3 = w64 (as_gp B).
Hypothesis G4 : getr regs 4 = w64 (as_tp B).
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 l.
Hypothesis G12 : getr regs 12 = w64 (sp0 + FO).
Hypothesis HSNK : SNK W mem sp0 D N out b.
(* snk_dest D M *)
Hypothesis HD0 : 0 < D.
Hypothesis HDac : D + M <= alloc_ceiling.
Hypothesis HM : 1 <= M <= 2 ^ 30.
Hypothesis Hcan : D + M <= FM_canary \/ FM_canary + 8 <= D.
Hypothesis HDw : forall a, D <= a < D + M ->
writable_at tfibsegs (mrestrict (w_H W) mem) a /\ ~ aowned B ly S a /\ ~ in_rom tfibsegs a.
Hypothesis HDam : amem_range D M.
Hypothesis HDra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF D M.
Hypothesis HDhu : shadow_hull_vis (aview tfibsegs (w_H W) mem) D M.
(* fw_src D M x bs *)
Hypothesis Hx0 : 0 < x.
Hypothesis Hxac : x + l <= alloc_ceiling.
Hypothesis HxD : x + l <= D \/ D + M <= x.
Hypothesis Hbs : forall i, 0 <= i < l -> aview tfibsegs (w_H W) mem (x + i) = Some (nth (Z.to_nat i) bs 0).
Hypothesis Hbsr : Forall (fun z => 0 <= z < 256) bs.
Hypothesis Hxam : amem_range x l.
Hypothesis Hxra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x l.
Hypothesis Hxhu : 0 < l -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x l.
(* room *)
Hypothesis Hroom : Z.of_nat (length out) + l + 1 <= M <= N.
Hypothesis HN : N <= 2 ^ 30.
Definition fw_extra : list word := [Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 (D + w); Z_to_bv 64 (N - 1 - w)].
Definition E0 : env := kenv regs sp0 fw_extra.
Lemma E0_reg : forall i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r.
Proof. intros i r Hi Hr. apply kenv_reg; assumption. Qed.
Lemma E0_2 : bv_unsigned (ew E0 2) = sp0.
Proof. unfold E0. rewrite kenv_2. rewrite unsigned_lit_small; [reflexivity|]. lia. Qed.
Lemma fw_basic : 0 <= b <= 80 /\ 0 <= w /\ 0 <= l /\ w + b + l <= N - 1 /\ 0 <= N.
Proof.
pose proof HSNK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & Hbo & Ho & _).
unfold w, l. lia.
Qed.
Lemma fw_regs_ok : regs_ok E0 fw_sr regs.
Proof.
pose proof E0_2 as E2.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- getr _ ?r = sv_denot _ (sr_get ?sr ?r) =>
let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ reflexivity
| (rewrite Z.add_0_r;
match goal with |- getr _ ?r = Z_to_bv 64 (bv_unsigned (ew E0 ?i)) =>
rewrite (E0_reg i r) by (cbv; first [discriminate | reflexivity]) end;
rewrite Z_to_bv_bv_unsigned; reflexivity)
| (rewrite E2; first [rewrite G2 | rewrite G12]; reflexivity) ] |]).
destruct Hr.
Qed.
Lemma E0_x : forall j, ew E0 (32 + j) = nth j fw_extra (Z_to_bv 64 0).
Proof. intros j. apply kenv_x. Qed.
Lemma fw_val_chunk : forall (e : sv) (off : Z) (n : BinNums.N) v,
sv_denot E0 e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 + off) (N.to_nat n) v ->
YP09.chunk_ok tfibsegs E0 (mrestrict (w_H W) mem) sp0 (YP09.mkChunk off (CVal n e)).
Proof.
intros e off n v He Hv Hn Hm.
exact (chunk_ok_val tfibsegs E0 _ sp0 off n e v He Hv Hn Hm).
Qed.
Lemma fw_entry_ok : st_ok tfibsegs E0 fw0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_FWX) mem (seg_rom tfibsegs))).
Proof.
pose proof E0_2 as E2. pose proof fw_basic as (Hb & Hw & Hl & Hsum & HN0).
pose proof HSNK as (S0 & S32 & S40 & S56 & S72 & S88 & S144 & S152 & SC0 & SC8 & SIB & SD & SDn & _ & _ & _ & _).
assert (HES : SNK_STK = 9104) by reflexivity.
assert (E33 : bv_unsigned (ew E0 33) = b) by (change (ew E0 33) with (ew E0 (32 + 1)); rewrite E0_x; cbn [nth fw_extra]; apply unsigned_lit_small; lia).
assert (E34 : ew E0 34 = Z_to_bv 64 (D + w)) by (change (ew E0 34) with (ew E0 (32 + 2)); rewrite E0_x; reflexivity).
assert (E35 : ew E0 35 = Z_to_bv 64 (N - 1 - w)) by (change (ew E0 35) with (ew E0 (32 + 3)); rewrite E0_x; reflexivity).
assert (E34' : bv_unsigned (ew E0 34) = D + w) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35' : bv_unsigned (ew E0 35) = N - 1 - w) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E10 : bv_unsigned (ew E0 10) = x) by (rewrite (E0_reg 10 10%bv) by (cbv; first [discriminate | reflexivity]); rewrite G10; apply unsigned_lit_small; lia).
assert (E11 : bv_unsigned (ew E0 11) = l) by (rewrite (E0_reg 11 11%bv) by (cbv; first [discriminate | reflexivity]); rewrite G11; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold fw0.
apply kentry.
- exact fw_regs_ok.
- vm_compute. reflexivity.
- unfold fw_regions. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply apresent_writable. apply Hpres. unfold OSP_FW in Ho. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite E2. unfold CKO, FO in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply apresent_writable. apply Hpres. lia. }
unfold fw_chunks. repeat apply Forall_cons; try apply Forall_nil;
(eapply fw_val_chunk; [ | | | first [eassumption | rewrite Z.add_assoc; eassumption]]);
first [ reflexivity | (unfold IBO, FO, CKO, A_SNW; zside)
| (cbn [sv_denot]; rewrite E2; f_equal; unfold IBO, CKO, FO; lia)
| (rewrite denot_lit_U, U_add_off_atom;
[ rewrite E2, E33; f_equal; lia | rewrite E2, E33; unfold M64, IBO; lia | rewrite E33; unfold M64; lia ]) ].
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite E2. unfold CKO, FO in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply apresent_writable. apply Hpres. lia. }
repeat apply Forall_cons; try apply Forall_nil;
(eapply fw_val_chunk; [ | | | first [eassumption | rewrite Z.add_assoc; eassumption]]);
first [ (unfold IBO, FO, CKO, A_SNW; zside)
| (cbn [sv_denot]; rewrite Z.add_0_r; first [rewrite E34' | rewrite E35']; reflexivity) ].
- apply pairwise_disjoint_of_extents. unfold fw_regions, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
unfold CKO, FO. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [fw_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E33, E34', E35', E11, E10. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; first [exact Hsp16 | apply Z.mod_1_r | lia].
Qed.
(* ---- the kit at OSP_FW ---- *)
Let HBp : snk_base B ly S U W mem md sp0 :=
conj HAR (conj Hac (conj Hsp44 (conj Hsp16 (conj Hstk (conj Htop (conj Hsp47 (conj Hhigh (conj Hpres Hzsh)))))))).
Let HDp : snk_dest B ly S W mem D M := conj HD0 (conj HDac (conj HM (conj Hcan (conj HDw (conj HDam (conj HDra HDhu)))))).
#[local] Abbreviation FWIp := (FWI B ly S U W mem md sp0 D M OSP_FW).
Let PH := fw_phase B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let MC := fw_mcpy B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let NUL := fw_nul B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let RET := fw_ret B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let SNKI := snk_intro B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let FINIT := FWI_init B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let FBAND := FWI_band B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let FWR := FWI_writable B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let BRA := band_ra B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let BHU := band_hull B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let BAM := band_amem B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let DRA := dest_ra B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let DHU := dest_hull B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let DAM := dest_amem B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let FRA := FWI_ra B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
Let FHU := FWI_hull B ly S U W mem md sp0 D M OSP_FW LAWS AMEMCPY HBp HDp T_FW.
(* environments after calls keep the entry atoms *)
Definition E0like (E : env) : Prop := forall i, (i < 40)%nat -> ew E i = ew E0 i.
Lemma E0like_E0 : E0like E0.
Proof. intros i _. reflexivity. Qed.
Lemma E0like_havoc : forall E k ws, E0like E -> (40 <= k)%nat -> E0like (havoc E k ws).
Proof. intros E k ws HE Hk i Hi. rewrite ew_havoc_old by lia. apply HE, Hi. Qed.
Lemma E0like_at : forall E, E0like E ->
bv_unsigned (ew E 2) = sp0 /\ ew E 3 = w64 (as_gp B) /\ ew E 4 = w64 (as_tp B) /\
bv_unsigned (ew E 10) = x /\ bv_unsigned (ew E 11) = l /\ bv_unsigned (ew E 33) = b /\
bv_unsigned (ew E 34) = D + w /\ bv_unsigned (ew E 35) = N - 1 - w /\
(forall i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs r).
Proof.
intros E HE. pose proof fw_basic as (Hb & Hw & Hl & Hsum & HN0). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite !HE by lia.
split; [exact E0_2|].
split; [rewrite (E0_reg 3 3%bv) by (cbv; first [discriminate | reflexivity]); exact G3|].
split; [rewrite (E0_reg 4 4%bv) by (cbv; first [discriminate | reflexivity]); exact G4|].
split; [rewrite (E0_reg 10 10%bv) by (cbv; first [discriminate | reflexivity]); rewrite G10; apply unsigned_lit_small; lia|].
split; [rewrite (E0_reg 11 11%bv) by (cbv; first [discriminate | reflexivity]); rewrite G11; apply unsigned_lit_small; lia|].
split; [change (ew E0 33) with (ew E0 (32 + 1)); rewrite E0_x; cbn [nth fw_extra]; apply unsigned_lit_small; lia|].
split; [change (ew E0 34) with (ew E0 (32 + 2)); rewrite E0_x; cbn [nth fw_extra]; apply unsigned_lit_small; lia|].
split; [change (ew E0 35) with (ew E0 (32 + 3)); rewrite E0_x; cbn [nth fw_extra]; apply unsigned_lit_small; lia|].
intros i r Hi Hr. pose proof (u5_range r). rewrite HE by lia. apply E0_reg; assumption.
Qed.
(* what a run keeps: every byte outside the band, the FILE / cookie windows and X *)
Definition KEEP (m : word -> option byte) (X : Z -> Prop) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ fw_band sp0 OSP_FW a -> ~ fw_fc sp0 a -> ~ X a ->
aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) mem a.
Lemma KEEP_step : forall m m' (X : Z -> Prop), KEEP m X ->
(forall a, 0 <= a < 2 ^ 64 -> ~ fw_band sp0 OSP_FW a -> ~ fw_fc sp0 a ->
aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) -> KEEP m' X.
Proof. intros m m' X HK H a H1 H2 H3 H4. rewrite (H a H1 H2 H3). exact (HK a H1 H2 H3 H4). Qed.
Definition FPOST := snk_post B ly S U W regs mem md sp0 (sp0 + OSP_FW) (fw_xw sp0 D M) l
(fun mem' => exists b', SNK W mem' sp0 D N (out ++ bs) b').
Lemma fw_snk0 : (forall i, 0 <= i < b -> aview tfibsegs (w_H W) mem (sp0 + IBO + i) = Some (nth (Z.to_nat (w + i)) out 0)) /\
(forall i, 0 <= i < w -> aview tfibsegs (w_H W) mem (D + i) = Some (nth (Z.to_nat i) out 0)) /\
aview tfibsegs (w_H W) mem (D + w) = Some 0 /\ Forall (fun z => 0 <= z < 256) out.
Proof.
pose proof HSNK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SIB & SD & SDn & _ & _ & _ & _ & SF).
split; [exact SIB|]. split; [exact SD|]. split; [exact SDn | exact SF].
Qed.
Lemma nth_out : forall i, 0 <= i < Z.of_nat (length out) -> nth (Z.to_nat i) (out ++ bs) 0 = nth (Z.to_nat i) out 0.
Proof. intros i Hi. apply app_nth1. lia. Qed.
Lemma nth_bs : forall i, Z.of_nat (length out) <= i ->
nth (Z.to_nat i) (out ++ bs) 0 = nth (Z.to_nat (i - Z.of_nat (length out))) bs 0.
Proof. intros i Hi. rewrite app_nth2 by lia. f_equal. lia. Qed.
Lemma len_app : Z.of_nat (length (out ++ bs)) = Z.of_nat (length out) + l.
Proof. rewrite length_app. unfold l. lia. Qed.
Lemma zc_eq : forall z v k, z = v + k * M64 -> 0 <= v < M64 -> zcanon z = v.
Proof. intros z v k -> Hv. rewrite zc_shift. apply zcanon_id. exact Hv. Qed.
Ltac vmr := vm_compute; reflexivity.
Ltac atoms := repeat match goal with H : bv_unsigned (ew ?E ?i) = _ |- context [bv_unsigned (ew ?E ?i)] => rewrite H end.
Ltac zfin := rewrite ?zcanon_id by (unfold M64; lia); unfold IBO, CKO, FO in *; lia.
Ltac dn := try unfold YG0d.w64; apply denot_U; uz; atoms; zfin.
Ltac bfin := repeat first [rewrite negb_true_iff | rewrite negb_false_iff];
  first [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.eqb_neq | apply Z.eqb_eq]; lia.
Ltac btf := first [rewrite bt_ltu | rewrite bt_geu | rewrite bt_eq | rewrite bt_ne]; uz; atoms;
  rewrite ?zcanon_id by (unfold M64; lia); bfin.
Ltac nbf := unfold fw_band, fw_fc, OSP_FW, CKO, IBO, FO in *; lia.
Ltac sc := first [lia | nbf | (cbv beta; tauto) | (cbv beta; unfold IBO, CKO, FO in *; lia)].
Ltac mc_auto :=
  lazymatch goal with
  | |- ss_pc _ = _ => vmr
  | |- ss_resv _ = _ => reflexivity
  | |- ss_mem _ = _ :: _ => reflexivity
  | |- YP09.r_base _ = _ => reflexivity
  | |- YP09.r_lo _ = _ => reflexivity
  | |- YP09.r_hi _ = _ => reflexivity
  | |- - SNK_STK <= YP09.r_wlo _ => cbn; lia
  | |- YP09.r_whi _ <= 0 => cbn; lia
  | |- sr_get _ _ = _ => vmr
  | |- ss_atoms_lt _ _ = true => vmr
  | |- regions_wf _ = true => vmr
  | |- no_cdata _ = true => vmr
  | |- mem_atoms_lt _ _ = true => vmr
  | |- forallb _ _ = true => vmr
  | |- sv_denot _ _ = _ => dn
  | |- bv_unsigned (ew _ 2) = _ => assumption
  | |- ew _ 3 = _ => assumption
  | |- ew _ 4 = _ => assumption
  | |- _ mod _ = _ => reflexivity
  | |- ESTACK - SNK_STK <= _ => unfold ESTACK, SNK_STK; lia
  | |- _ <= OSP_FW => unfold OSP_FW; lia
  end.
Ltac mc_rest HI A2 :=
  lazymatch goal with
  | |- forall a, _ -> fw_xw _ _ _ a => let a := fresh "a" in intros a ?; unfold fw_xw, CKO, IBO, FO in *; lia
  | |- forall a, _ -> _ -> _ <= a < _ => let a := fresh "a" in intros a ? ?; unfold IBO in *; lia
  | |- forall a, _ -> writable_at _ _ a /\ _ =>
      let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      first [ (destruct (FBAND _ _ a HI ltac:(unfold IBO in *; lia)) as [?Hw ?Ho];
               split; [assumption | split; [assumption | unfold ESTACK, IBO in *; lia]])
            | (split; [apply (FWR _ _ a HI); lia | split; [apply HDw; lia | unfold ESTACK; lia]]) ]
  | |- amem_range _ _ => first [ apply BAM; unfold IBO in *; lia | apply DAM; lia | exact Hxam ]
  | |- range_addressable _ _ _ _ =>
      first [ apply (BRA _ _ _ _ HI); unfold IBO in *; lia | apply (DRA _ _ _ _ HI); lia
            | apply (FRA _ _ _ _ HI); [lia | lia | exact Hxra] ]
  | |- 0 < _ -> shadow_hull_vis _ _ _ => intros ?;
      first [ apply (BHU _ _ _ _ HI); unfold IBO in *; lia | apply (DHU _ _ _ _ HI); lia
            | apply (FHU _ _ _ _ HI); [lia | lia | lia | apply Hxhu; lia] ]
  | |- forall r a, In r _ -> _ -> 0 <= a < _ /\ _ =>
      let r := fresh "r" in let a := fresh "a" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros r a Hr Ha; cbn in Hr; destruct Hr as [<-|[<-|[]]];
      cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; rewrite A2 in Ha; unfold ESTACK, IBO in *; repeat split; lia
  | |- forall r a, In r _ -> _ -> apresent _ _ a =>
      let r := fresh "r" in let a := fresh "a" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros r a Hr Ha; cbn in Hr; destruct Hr as [<-|[<-|[]]];
      cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite A2 in Ha; apply (proj1 (proj2 (proj2 HI))); lia
  end.
(* the source bytes of the memcpy calls *)
Lemma src_x : forall m (X : Z -> Prop), KEEP m X -> (forall a, x <= a < x + l -> ~ X a) ->
forall a, x <= a < x + l -> aview tfibsegs (w_H W) m a <> None /\ ~ (sp0 + -976 - ESTACK <= a < sp0 + -976).
Proof.
intros m X HK HX a Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof fw_basic as (Hb & Hw & Hl & Hsum & HN0).
assert (HVF : SNK_STK = 9104) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
split; [|lia].
rewrite (HK a) by first [sc | apply HX, Ha].
replace a with (x + (a - x)) by lia. rewrite (Hbs (a - x)) by lia. discriminate.
Qed.
Lemma src_buf : forall m (X : Z -> Prop), KEEP m X -> (forall a, sp0 + IBO <= a < sp0 + IBO + b -> ~ X a) ->
forall a, sp0 + IBO <= a < sp0 + IBO + b -> aview tfibsegs (w_H W) m a <> None /\ ~ (sp0 + -976 - ESTACK <= a < sp0 + -976).
Proof.
intros m X HK HX a Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof fw_basic as (Hb & Hw & Hl & Hsum & HN0).
pose proof fw_snk0 as (SIB & SD & SDn & SF).
assert (HVF : SNK_STK = 9104) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
split; [|unfold IBO in *; lia].
rewrite (HK a) by first [sc | apply HX, Ha].
replace a with (sp0 + IBO + (a - (sp0 + IBO))) by lia. rewrite (SIB (a - (sp0 + IBO))) by lia. discriminate.
Qed.
Ltac pfacts :=
  pose proof fw_basic as (Hb & Hw & Hl & Hsum & HN0); pose proof fw_snk0 as (SIB & SD & SDn & SF);
  pose proof (E0like_at E0 E0like_E0) as (A2 & A3 & A4 & A10 & A11 & A33 & A34 & A35 & AR);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  assert (HVF : SNK_STK = 9104) by reflexivity; assert (HES : ESTACK = 4096) by reflexivity.
(* l fits in the buffer: memcpy (wpos, x, l), wpos += l *)
Lemma path_fit : forall ms md1, l <= 80 - b ->
st_ok tfibsegs E0 wA1_s (restrict (w_H W) ms) -> FWIp (ms_mem ms) md1 -> KEEP (ms_mem ms) (fun _ => False) ->
SRr tfibsegs W (mkCfg ms md1) FPOST.
Proof using All.
intros ms md1 Hfit HS HI HK. pfacts.
eapply SRr_bind; [apply (PH E0 wA1_s wA1_e _ ms md1 HS r_wA1); [discriminate | vmr | vmr | exact A2 | exact HI] |].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HI2 & HK2).
assert (K2 : KEEP (ms_mem ms2) (fun _ => False)) by (apply (KEEP_step _ _ _ HK); intros; apply HK2; assumption).
eapply SRr_bind.
{ eapply (MC E0 wA1_e ms2 _ _ _ 40 0x8ee0c (-976) (-352) (-272)
    (SAlu ALU_ADD (SOff 2 (-352)) (SOff 33 0)) (SOff 10 0) (SOff 11 0) (sp0 + IBO + b) x l HS2).
  all: try mc_auto.
  all: try solve [unfold IBO in *; lia].
  all: try mc_rest HI2 A2.
  all: try exact HI2.
  apply (src_x _ _ K2). intros; tauto. }
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HI3 & HP3 & Heff3 & Hfr3).
pose proof (E0like_at _ (E0like_havoc E0 40 (map (getr (ms_regs ms3)) CLOB) E0like_E0 (le_n 40)))
  as (B2 & B3 & B4 & B10 & B11 & B33 & B34 & B35 & BR).
eapply SRr_bind; [apply (PH _ wA2_s wA2_e _ ms3 _ HS3 r_wA2); [discriminate | vmr | vmr | exact B2 | exact HI3] |].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HI4 & HK4).
assert (KF : KEEP (ms_mem ms4) (fun a => sp0 + IBO + b <= a < sp0 + IBO + b + l)).
{ intros a Ha Hb' Hf Hx. rewrite (HK4 a Ha Hb' Hf). rewrite (Hfr3 a Ha); [| unfold fw_band, OSP_FW in Hb'; lia | exact Hx].
  exact (K2 a Ha Hb' Hf (fun f => f)). }
assert (CP : forall i, 0 <= i < l -> aview tfibsegs (w_H W) (ms_mem ms4) (sp0 + IBO + b + i) = Some (nth (Z.to_nat i) bs 0)).
{ intros i Hi. rewrite (HK4 (sp0 + IBO + b + i)) by sc. rewrite (Heff3 i Hi).
  rewrite (K2 (x + i)) by sc. apply Hbs, Hi. }
unfold FPOST.
apply (RET regs _ wA2_e ms4 _ l (SOff 11 0) _ HS4);
[reflexivity | vmr | exact B2 | exact BR | vmr | exact G1 | exact G2 | vmr | dn | exact HI4 |].
exists (b + l).
apply (SNKI _ wA2_e ms4 N (out ++ bs) (b + l) w (SAlu ALU_ADD (SAlu ALU_ADD (SOff 2 (-352)) (SOff 11 0)) (SOff 33 0))
  (SOff 34 0) (SOff 35 0) HS4 B2);
[vmr | rewrite len_app; unfold w; lia | vmr | dn | vmr | dn | vmr | dn | | | | lia | rewrite len_app; lia
| rewrite len_app; lia | exact HN | apply Forall_app; split; assumption].
- intros i Hi. destruct (Z_lt_le_dec i b) as [Hib|Hib].
  + rewrite (KF (sp0 + IBO + i)) by sc. rewrite nth_out by (unfold w in *; lia). apply SIB. lia.
  + replace (sp0 + IBO + i) with (sp0 + IBO + b + (i - b)) by lia. rewrite CP by lia.
    rewrite nth_bs by (unfold w in *; lia). replace (w + i - Z.of_nat (length out)) with (i - b) by (unfold w; lia). reflexivity.
- intros i Hi. rewrite (KF (D + i)) by sc. rewrite nth_out by (unfold w in *; lia). apply SD, Hi.
- rewrite (KF (D + w)) by sc. exact SDn.
Qed.
(* no fit, b = 0: sn_write copies bs to the destination, a NUL after it, wpos = wbase = buf *)
Lemma path_z : forall ms md1, b = 0 -> 80 - b < l ->
st_ok tfibsegs E0 wZ1_s (restrict (w_H W) ms) -> FWIp (ms_mem ms) md1 -> KEEP (ms_mem ms) (fun _ => False) ->
SRr tfibsegs W (mkCfg ms md1) FPOST.
Proof using All.
intros ms md1 Hb0 Hnf HS HI HK. pfacts.
eapply SRr_bind; [apply (PH E0 wZ1_s wZ1_e _ ms md1 HS r_wZ1); [discriminate | vmr | vmr | exact A2 | exact HI] |].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HI2 & HK2).
pose proof (st_ok_add_cond_neg tfibsegs E0 _ _ BC_LTU (SOff 35 0) (SOff 11 0) HS2 ltac:(btf)) as HS2'.
eapply SRr_bind; [apply (PH E0 wZ2_s wZ2_e _ ms2 _ HS2' r_wZ2); [discriminate | vmr | vmr | exact A2 | exact HI2] |].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HI3 & HK3).
pose proof (st_ok_add_cond_neg tfibsegs E0 _ _ BC_EQ (SOff 11 0) (SLit 0) HS3 ltac:(btf)) as HS3'.
eapply SRr_bind; [apply (PH E0 wZ3_s wZ3_e _ ms3 _ HS3' r_wZ3); [discriminate | vmr | vmr | exact A2 | exact HI3] |].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HI4 & HK4).
assert (K4 : KEEP (ms_mem ms4) (fun _ => False)).
{ apply (KEEP_step _ _ _ (KEEP_step _ _ _ (KEEP_step _ _ _ HK HK2) HK3) HK4). }
eapply SRr_bind.
{ eapply (MC E0 wZ3_e ms4 _ _ _ 40 0x9234c (-976) 0 0 (SOff 34 0) (SOff 10 0) (SOff 11 0) (D + w) x l HS4).
  all: try mc_auto.
  all: try solve [unfold IBO in *; lia].
  all: try mc_rest HI4 A2.
  all: try exact HI4.
  apply (src_x _ _ K4). intros; tauto. }
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HI5 & HP5 & Heff5 & Hfr5).
pose proof (E0like_at _ (E0like_havoc E0 40 (map (getr (ms_regs ms5)) CLOB) E0like_E0 (le_n 40)))
  as (B2 & B3 & B4 & B10 & B11 & B33 & B34 & B35 & BR).
eapply SRr_bind; [apply (PH _ wZ4_s wZ4_e _ ms5 _ HS5 r_wZ4); [discriminate | vmr | vmr | exact B2 | exact HI5] |].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HI6 & HK6).
assert (R10 : getr (ms_regs ms6) 10 = Z_to_bv 64 (D + w + l)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) _ _ _ 10 HS6).
  replace (sr_get (ss_regs wZ4_e) 10) with (SAlu ALU_ADD (SOff 11 0) (SOff 34 0)) by vmr. dn. }
eapply SRr_bind; [apply (NUL _ wZ4_e ms6 _ (D + w + l) HS6); [vmr | reflexivity | exact B2 | vmr | exact R10 | lia | exact HI6] |].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HI7 & HN7 & HO7).
eapply SRr_bind; [apply (PH _ wZ5_s wZ5_e _ ms7 _ HS7 r_wZ5); [discriminate | vmr | vmr | exact B2 | exact HI7] |].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HI8 & HK8).
assert (KF : KEEP (ms_mem ms8) (fun a => D + w <= a <= D + w + l)).
{ intros a Ha Hb' Hf Hx. rewrite (HK8 a Ha Hb' Hf). rewrite (HO7 a Ha); [| cbv beta in Hx; lia].
  rewrite (HK6 a Ha Hb' Hf). rewrite (Hfr5 a Ha); [| unfold fw_band, OSP_FW in Hb'; lia | cbv beta in Hx; lia].
  exact (K4 a Ha Hb' Hf (fun f => f)). }
assert (CP : forall i, 0 <= i < l -> aview tfibsegs (w_H W) (ms_mem ms8) (D + w + i) = Some (nth (Z.to_nat i) bs 0)).
{ intros i Hi. rewrite (HK8 (D + w + i)) by sc. rewrite (HO7 (D + w + i)) by lia. rewrite (HK6 (D + w + i)) by sc.
  rewrite (Heff5 i Hi). rewrite (K4 (x + i)) by sc. apply Hbs, Hi. }
assert (NL : aview tfibsegs (w_H W) (ms_mem ms8) (D + w + l) = Some 0) by (rewrite (HK8 (D + w + l)) by sc; exact HN7).
unfold FPOST.
apply (RET regs _ wZ5_e ms8 _ l (SOff 11 0) _ HS8);
[reflexivity | vmr | exact B2 | exact BR | vmr | exact G1 | exact G2 | vmr | dn | exact HI8 |].
exists 0.
apply (SNKI _ wZ5_e ms8 N (out ++ bs) 0 (w + l) (SOff 2 (-352)) (SAlu ALU_ADD (SOff 11 0) (SOff 34 0))
  (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit (-1))) (SOff 35 0)) HS8 B2);
[vmr | rewrite len_app; unfold w; lia | vmr | dn | vmr | dn | vmr | dn | | | | lia | lia
| rewrite len_app; lia | exact HN | apply Forall_app; split; assumption].
- intros i Hi. lia.
- intros i Hi. destruct (Z_lt_le_dec i w) as [Hiw|Hiw].
  + rewrite (KF (D + i)) by sc. rewrite nth_out by (unfold w in *; lia). apply SD. lia.
  + replace (D + i) with (D + w + (i - w)) by lia. rewrite CP by lia.
    rewrite nth_bs by (unfold w in *; lia). replace (i - Z.of_nat (length out)) with (i - w) by (unfold w; lia). reflexivity.
- replace (D + (w + l)) with (D + w + l) by lia. exact NL.
Qed.
(* no fit, b <> 0: sn_write copies the buffer, then bs, then a NUL *)
Lemma path_n : forall ms md1, b <> 0 -> 80 - b < l ->
st_ok tfibsegs E0 wN1_s (restrict (w_H W) ms) -> FWIp (ms_mem ms) md1 -> KEEP (ms_mem ms) (fun _ => False) ->
SRr tfibsegs W (mkCfg ms md1) FPOST.
Proof using All.
intros ms md1 Hbn Hnf HS HI HK. pfacts.
eapply SRr_bind; [apply (PH E0 wN1_s wN1_e _ ms md1 HS r_wN1); [discriminate | vmr | vmr | exact A2 | exact HI] |].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HI2 & HK2).
assert (K2 : KEEP (ms_mem ms2) (fun _ => False)) by (apply (KEEP_step _ _ _ HK HK2)).
eapply SRr_bind.
{ eapply (MC E0 wN1_e ms2 _ _ _ 56 0x9231c (-976) 0 0 (SOff 34 0) (SOff 2 (-352)) (SOff 33 0) (D + w) (sp0 + IBO) b HS2).
  all: try mc_auto.
  all: try solve [unfold IBO in *; lia].
  all: try mc_rest HI2 A2.
  all: try exact HI2.
  apply (src_buf _ _ K2). intros; tauto. }
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HI3 & HP3 & Heff3 & Hfr3).
assert (EL1 : E0like (havoc E0 56 (map (getr (ms_regs ms3)) CLOB))) by (apply E0like_havoc; [exact E0like_E0 | lia]).
pose proof (E0like_at _ EL1) as (B2 & B3 & B4 & B10 & B11 & B33 & B34 & B35 & BR).
eapply SRr_bind; [apply (PH _ wN2_s wN2_e _ ms3 _ HS3 r_wN2); [discriminate | vmr | vmr | exact B2 | exact HI3] |].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HI4 & HK4).
pose proof (st_ok_add_cond_neg tfibsegs _ _ _ BC_LTU (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SOff 35 0)) (SOff 11 0)
  HS4 ltac:(btf)) as HS4'.
eapply SRr_bind; [apply (PH _ wN3_s wN3_e _ ms4 _ HS4' r_wN3); [discriminate | vmr | vmr | exact B2 | exact HI4] |].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HI5 & HK5).
pose proof (st_ok_add_cond_neg tfibsegs _ _ _ BC_EQ (SOff 11 0) (SLit 0) HS5 ltac:(btf)) as HS5'.
eapply SRr_bind; [apply (PH _ wN4_s wN4_e _ ms5 _ HS5' r_wN4); [discriminate | vmr | vmr | exact B2 | exact HI5] |].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HI6 & HK6).
assert (K6 : KEEP (ms_mem ms6) (fun a => D + w <= a < D + w + b)).
{ intros a Ha Hb' Hf Hx. rewrite (HK6 a Ha Hb' Hf), (HK5 a Ha Hb' Hf), (HK4 a Ha Hb' Hf).
  rewrite (Hfr3 a Ha); [| unfold fw_band, OSP_FW in Hb'; lia | exact Hx]. exact (K2 a Ha Hb' Hf (fun f => f)). }
eapply SRr_bind.
{ eapply (MC _ wN4_e ms6 _ _ _ 72 0x9234c (-976) 0 0 (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) (SOff 10 0) (SOff 11 0)
    (D + w + b) x l HS6).
  all: try mc_auto.
  all: try solve [unfold IBO in *; lia].
  all: try mc_rest HI6 B2.
  all: try exact HI6.
  apply (src_x _ _ K6). intros a Ha. cbv beta. lia. }
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HI7 & HP7 & Heff7 & Hfr7).
assert (EL2 : E0like (havoc (havoc E0 56 (map (getr (ms_regs ms3)) CLOB)) 72 (map (getr (ms_regs ms7)) CLOB)))
  by (apply E0like_havoc; [exact EL1 | lia]).
clear B2 B3 B4 B10 B11 B33 B34 B35 BR.
pose proof (E0like_at _ EL2) as (B2 & B3 & B4 & B10 & B11 & B33 & B34 & B35 & BR).
eapply SRr_bind; [apply (PH _ wN5_s wN5_e _ ms7 _ HS7 r_wN5); [discriminate | vmr | vmr | exact B2 | exact HI7] |].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HI8 & HK8).
assert (R10 : getr (ms_regs ms8) 10 = Z_to_bv 64 (D + w + b + l)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) _ _ _ 10 HS8).
  replace (sr_get (ss_regs wN5_e) 10) with (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 33 0)) (SOff 34 0)) by vmr. dn. }
eapply SRr_bind; [apply (NUL _ wN5_e ms8 _ (D + w + b + l) HS8); [vmr | reflexivity | exact B2 | vmr | exact R10 | lia | exact HI8] |].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HI9 & HN9 & HO9).
eapply SRr_bind; [apply (PH _ wN6_s wN6_e _ ms9 _ HS9 r_wN6); [discriminate | vmr | vmr | exact B2 | exact HI9] |].
cbv beta. intros W10 c10 _ (-> & ms10 & mat10 & -> & HS10 & HI10 & HK10).
assert (KF : KEEP (ms_mem ms10) (fun a => D + w <= a <= D + w + b + l)).
{ intros a Ha Hb' Hf Hx. rewrite (HK10 a Ha Hb' Hf). rewrite (HO9 a Ha); [| cbv beta in Hx; lia].
  rewrite (HK8 a Ha Hb' Hf). rewrite (Hfr7 a Ha); [| unfold fw_band, OSP_FW in Hb'; lia | cbv beta in Hx; lia].
  apply (K6 a Ha Hb' Hf). cbv beta in Hx |- *. lia. }
assert (CP1 : forall i, 0 <= i < b -> aview tfibsegs (w_H W) (ms_mem ms10) (D + w + i) = Some (nth (Z.to_nat (w + i)) out 0)).
{ intros i Hi. rewrite (HK10 (D + w + i)) by sc. rewrite (HO9 (D + w + i)) by lia. rewrite (HK8 (D + w + i)) by sc.
  rewrite (Hfr7 (D + w + i)) by (unfold ESTACK in *; lia). rewrite (HK6 (D + w + i)) by sc.
  rewrite (HK5 (D + w + i)) by sc. rewrite (HK4 (D + w + i)) by sc. rewrite (Heff3 i Hi).
  rewrite (K2 (sp0 + IBO + i)) by sc. apply SIB, Hi. }
assert (CP2 : forall i, 0 <= i < l -> aview tfibsegs (w_H W) (ms_mem ms10) (D + w + b + i) = Some (nth (Z.to_nat i) bs 0)).
{ intros i Hi. rewrite (HK10 (D + w + b + i)) by sc. rewrite (HO9 (D + w + b + i)) by lia. rewrite (HK8 (D + w + b + i)) by sc.
  rewrite (Heff7 i Hi). rewrite (K6 (x + i)) by sc. apply Hbs, Hi. }
assert (NL : aview tfibsegs (w_H W) (ms_mem ms10) (D + w + b + l) = Some 0) by (rewrite (HK10 (D + w + b + l)) by sc; exact HN9).
unfold FPOST.
apply (RET regs _ wN6_e ms10 _ l (SOff 11 0) _ HS10);
[reflexivity | vmr | exact B2 | exact BR | vmr | exact G1 | exact G2 | vmr | dn | exact HI10 |].
exists 0.
apply (SNKI _ wN6_e ms10 N (out ++ bs) 0 (w + b + l) (SOff 2 (-352))
  (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 33 0)) (SOff 34 0))
  (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit (-1))) (SMd M_MUL (SOff 33 0) (SLit 18446744073709551615))) (SOff 35 0))
  HS10 B2);
[vmr | rewrite len_app; unfold w; lia | vmr | dn | vmr | dn | vmr | | | | | lia | lia
| rewrite len_app; lia | exact HN | apply Forall_app; split; assumption].
- apply denot_U. uz. atoms. apply (zc_eq _ _ b); unfold M64; lia.
- intros i Hi. lia.
- intros i Hi. destruct (Z_lt_le_dec i w) as [Hiw|Hiw]; [|destruct (Z_lt_le_dec i (w + b)) as [Hiwb|Hiwb]].
  + rewrite (KF (D + i)) by sc. rewrite nth_out by (unfold w in *; lia). apply SD. lia.
  + replace (D + i) with (D + w + (i - w)) by lia. rewrite CP1 by lia. rewrite nth_out by (unfold w in *; lia).
    replace (w + (i - w)) with i by lia. reflexivity.
  + replace (D + i) with (D + w + b + (i - w - b)) by lia. rewrite CP2 by lia.
    rewrite nth_bs by (unfold w in *; lia). replace (i - Z.of_nat (length out)) with (i - w - b) by (unfold w; lia). reflexivity.
- replace (D + (w + b + l)) with (D + w + b + l) by lia. exact NL.
Qed.
(* no fit: c->n >= b, then b = 0 or not *)
Lemma path_nf : forall ms md1, 80 - b < l ->
st_ok tfibsegs E0 wB1_s (restrict (w_H W) ms) -> FWIp (ms_mem ms) md1 -> KEEP (ms_mem ms) (fun _ => False) ->
SRr tfibsegs W (mkCfg ms md1) FPOST.
Proof using All.
intros ms md1 Hnf HS HI HK. pfacts.
eapply SRr_bind; [apply (PH E0 wB1_s wB1_e _ ms md1 HS r_wB1); [discriminate | vmr | vmr | exact A2 | exact HI] |].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HI2 & HK2).
pose proof (st_ok_add_cond_neg tfibsegs E0 _ _ BC_LTU (SOff 35 0) (SOff 33 0) HS2 ltac:(btf)) as HS2'.
eapply SRr_bind; [apply (PH E0 wB2_s wB2_e _ ms2 _ HS2' r_wB2); [discriminate | vmr | vmr | exact A2 | exact HI2] |].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HI3 & HK3).
assert (K3 : KEEP (ms_mem ms3) (fun _ => False)) by (apply (KEEP_step _ _ _ (KEEP_step _ _ _ HK HK2) HK3)).
destruct (Z.eq_dec b 0) as [Hb0|Hbn].
- apply (path_z ms3 _ Hb0 Hnf); [| exact HI3 | exact K3].
  exact (st_ok_add_cond tfibsegs E0 _ _ BC_EQ (SOff 33 0) (SLit 0) HS3 ltac:(btf)).
- apply (path_n ms3 _ Hbn Hnf); [| exact HI3 | exact K3].
  exact (st_ok_add_cond_neg tfibsegs E0 _ _ BC_EQ (SOff 33 0) (SLit 0) HS3 ltac:(btf)).
Qed.
Lemma fw_main : SRr tfibsegs W (cfg_at tfibsegs A_FWX regs mem md) FPOST.
Proof using All.
pfacts.
pose proof fw_entry_ok as HS0.
unfold cfg_at. change (YG0d.w64 A_FWX) with (Z_to_bv 64 A_FWX).
eapply SRr_bind; [apply (PH E0 w1_s w1_e _ _ md HS0 r_w1); [discriminate | vmr | vmr | exact A2 | exact FINIT] |].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HI1 & HK1).
assert (K1 : KEEP (ms_mem ms1) (fun _ => False)) by (intros a Ha Hb' Hf _; exact (HK1 a Ha Hb' Hf)).
destruct (Z_le_gt_dec l (80 - b)) as [Hfit|Hnf].
- apply (path_fit ms1 _ Hfit); [| exact HI1 | exact K1].
  exact (st_ok_add_cond tfibsegs E0 _ _ BC_GEU FW_ROOM (SOff 11 0) HS1 ltac:(unfold FW_ROOM; btf)).
- apply (path_nf ms1 _ ltac:(lia)); [| exact HI1 | exact K1].
  exact (st_ok_add_cond_neg tfibsegs E0 _ _ BC_GEU FW_ROOM (SOff 11 0) HS1 ltac:(unfold FW_ROOM; btf)).
Qed.
End p.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem afwx_realizes : forall B, AR_laws tfibsegs B -> TfibSyms B -> aintrin_realizesU B OCpy W_MEMCPY -> afwx_realizesU B A_FWX.
Proof.
intros B LAWS TB AMEMCPY. unfold afwx_realizesU.
intros ly S U W regs mem md sp0 D N M out b x bs HB HR G10 G11 G12 HSNK HDst HFS HRM.
destruct HB as (HAR & Hac & Hsp44 & Hsp16 & Hstk & Htop & Hsp47 & Hhigh & Hpres & Hzsh).
destruct HR as (G1 & G2 & G3 & G4).
destruct HDst as (HD0 & HDac & HM & Hcan & HDw & HDam & HDra & HDhu).
destruct HFS as (Hx0 & Hxac & HxD & Hbs & Hbsr & Hxam & Hxra & Hxhu).
pose proof HSNK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HN & _).
exact (fw_main B LAWS TB AMEMCPY ly S U W regs mem md sp0 D N M out b x bs HAR Hac Hsp44 Hsp16 Hstk Htop Hsp47 Hhigh
  Hpres Hzsh G1 G2 G3 G4 G10 G11 G12 HSNK HD0 HDac HM Hcan HDw HDam HDra HDhu Hx0 Hxac HxD Hbs Hbsr Hxam Hxra Hxhu HRM HN).
Qed.
End t.
