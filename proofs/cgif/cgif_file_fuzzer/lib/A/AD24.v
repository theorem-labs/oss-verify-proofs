(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK14 YK15 YK18 YP0n YP01 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YL09 YK04 YA0i YA0n YA0o YA0p YK09 YA0e YG00 YG01 YG0f YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1v AD1y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Lemma tfib_const_val : forall ly S W mem md i a w v,
AR tfibsegs B ly S W mem md ->
nth_error Tfib_const_abs i = Some (ACell (ANum a) w (AV (ANum v))) ->
val_mem tfibsegs (mrestrict (w_H W) mem) a w v.
Proof.
intros ly S W mem md i a w v HAR Hi k Hk.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite (ts_const B HB) in HC.
assert (Hin : In (ACell (ANum a) w (AV (ANum v))) (Tfib_const ly)).
{ unfold Tfib_const. apply in_or_app. right. apply in_or_app. left. exact (nth_error_In _ _ Hi). }
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. unfold cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte v w k) with (YG0f.le_byte v w k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.
Lemma region_ok_const1 : forall E ly S W mem md,
AR tfibsegs B ly S W mem md -> region_ok tfibsegs E (mrestrict (w_H W) mem) R_inited.
Proof.
intros E ly S W mem md HAR.
pose proof (tfib_const_val ly S W mem md 51 0xa6cd8 1 1 HAR eq_refl) as V.
split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; intros; lia|].
constructor; [|constructor]. intros i Hi. cbn [c_off c_val R_inited base_val r_base] in *. cbn in Hi.
eexists. split; [reflexivity|].
specialize (V (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in V by lia. replace (0 + 683224 + i) with (683224 + i) by lia.
rewrite V. f_equal. apply bv_eq. unfold byte_of_word. cbn [sv_denot]. rewrite u64_lit by lia. assert (i = 0) as -> by lia. reflexivity.
Qed.
Lemma region_ok_const2 : forall E ly S W mem md,
AR tfibsegs B ly S W mem md -> region_ok tfibsegs E (mrestrict (w_H W) mem) R_realrd.
Proof.
intros E ly S W mem md HAR.
pose proof (tfib_const_val ly S W mem md 72 0x9fce8 8 0x9c998 HAR eq_refl) as V.
split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; intros; lia|].
constructor; [|constructor]. intros i Hi. cbn [c_off c_val R_realrd base_val r_base] in *. cbn in Hi.
eexists. split; [reflexivity|].
specialize (V (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in V by lia. replace (0 + 654568 + i) with (654568 + i) by lia.
rewrite V. f_equal. apply bv_eq. unfold byte_of_word. cbn [sv_denot]. rewrite u64_lit by lia.
rewrite (le_byte_small 0x9c998 8 (Z.to_nat i)) by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma region_ok_errno : forall E (m : word -> option byte), region_ok tfibsegs E m R_errno.
Proof.
intros E m. split; [cbn; lia|]. split; [cbn; lia|]. split; [| constructor].
cbn [r_wlo r_whi r_base base_val R_errno]. intros o Ho. unfold writable_at. apply tfib_rw_window. rewrite u64_lit by lia. lia.
Qed.
Definition LT42 (j : nat) : bool := (j <? 42)%nat.
Definition RD_srcs : list (bv 5) :=
([0; 0; 0; 0; 9; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 19; 21] ++ [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31])%bv.
Definition E_RD (EL : YP0m.env) (regs : bvmap 5 word) : YP0m.env := havoc EL K_M1 (map (getr regs) RD_srcs).
Lemma RD_fact_obls_eq : fact_obls LT42 RD_facts = [(A_LEN, fact_len); (A_CAP, fact_cap)].
Proof. vm_compute. reflexivity. Qed.
Lemma RD_mem_atoms : mem_atoms_lt K_M1 LH_mem = true. Proof. vm_compute. reflexivity. Qed.
Lemma RD_mem_wf : regions_wf LH_mem = true. Proof. vm_compute. reflexivity. Qed.
Lemma E_RD_old : forall EL regs n, (n < K_M1)%nat -> ew (E_RD EL regs) n = ew EL n.
Proof. intros EL regs n Hn. unfold E_RD. apply ew_havoc_old. exact Hn. Qed.
Lemma E_RD_new : forall EL regs i, (i < length RD_srcs)%nat -> ew (E_RD EL regs) (K_M1 + i) = getr regs (nth i RD_srcs 0%bv).
Proof.
intros EL regs i Hi. unfold E_RD. rewrite (ew_havoc_new EL K_M1 _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi).
apply map_nth.
Qed.
Lemma reabs_RD : forall (EL E : YP0m.env) ss ms (H : word -> bool),
(forall n, (n < K_M1)%nat -> ew E n = ew EL n) -> ed E = ed EL ->
st_ok tfibsegs E ss (restrict H ms) -> ss_pc ss = RDPC ->
reabs_check LT42 ss RD_regs RD_facts = true -> submem LH_mem (ss_mem ss) ->
(let regs := ms_regs ms in afact_ok (E_RD EL regs) A_LEN fact_len /\ afact_ok (E_RD EL regs) A_CAP fact_cap) ->
st_ok tfibsegs (E_RD EL (ms_regs ms)) S_RD (restrict H ms).
Proof.
intros EL E ss ms H HEE HED HS Hpc Hck Hsub (F1 & F2).
unfold S_RD. rewrite <- Hpc.
apply (st_ok_reabs tfibsegs LT42 E (E_RD EL (ms_regs ms)) ss (restrict H ms) RD_regs LH_mem RD_facts HS).
- split; [| intros d _; unfold E_RD, havoc; cbn [ed]; rewrite HED; reflexivity]. intros n Hn. unfold LT42 in Hn. apply Nat.ltb_lt in Hn.
rewrite E_RD_old by exact Hn. symmetry. exact (HEE n Hn).
- exact Hck.
- cbn [ms_regs restrict].
assert (X : forall i r, (i < 35)%nat -> nth i RD_srcs 0%bv = r -> ew (E_RD EL (ms_regs ms)) (K_M1 + i) = getr (ms_regs ms) r).
{ intros i r Hi <-. apply E_RD_new. cbn. exact Hi. }
apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
Ltac one X i := apply (X i); [cbn; lia | apply bv_eq; vm_compute; reflexivity].
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-;
first [ one X 4%nat | one X 16%nat | one X 17%nat | one X 18%nat | one X 19%nat | one X 20%nat | one X 21%nat | one X 22%nat
| one X 23%nat | one X 24%nat | one X 25%nat | one X 26%nat | one X 27%nat | one X 28%nat | one X 29%nat | one X 30%nat
| one X 31%nat | one X 32%nat | one X 33%nat | one X 34%nat ] |]).
destruct Hin.
- rewrite RD_fact_obls_eq. repeat (constructor; [cbn [fst snd]; assumption|]). constructor.
- cbn [ms_mem restrict]. pose proof (st_ok_mem_ok tfibsegs _ ss _ HS) as HM. cbn [ms_mem restrict] in HM.
apply (mem_ok_agree tfibsegs K_M1 E); [| exact RD_mem_atoms | exact (mem_ok_sub tfibsegs _ _ _ _ Hsub RD_mem_wf HM)].
split; [| unfold E_RD, havoc; cbn [ed]; symmetry; exact HED]. intros n Hn. rewrite E_RD_old by exact Hn. symmetry. exact (HEE n Hn).
Qed.
Lemma region_ok_transport_chunks : forall E (m m' : word -> option byte) r,
region_ok tfibsegs E m r ->
(forall c i, In c (r_chunks r) -> 0 <= i < c_len c ->
mbyte tfibsegs m' (base_val E (r_base r) + c_off c + i) = mbyte tfibsegs m (base_val E (r_base r) + c_off c + i)) ->
(forall o, r_wlo r <= o < r_whi r -> writable_at tfibsegs m' (base_val E (r_base r) + o)) ->
region_ok tfibsegs E m' r.
Proof.
intros E m m' r (B1 & B2 & Wr & C) Hc Hw. split; [exact B1|]. split; [exact B2|]. split; [exact Hw|].
apply Forall_forall. intros c Hin i Hi. pose proof (proj1 (Forall_forall _ _) C c Hin i Hi) as (b & Hb1 & Hb2).
exists b. split; [exact Hb1|]. rewrite (Hc c i Hin Hi). exact Hb2.
Qed.
Lemma reg_in_In : forall r l, reg_in r l = true <-> In r l.
Proof.
intros r l. induction l as [|x l IH]; cbn; [split; [discriminate | tauto]|].
rewrite Bool.orb_true_iff, IH. split.
- intros [H|H]; [left; symmetry; apply bv_eqb_eq; exact H | right; exact H].
- intros [<-|H]; [left; apply bv_eqb_refl | right; exact H].
Qed.
Lemma reg_in_perm : forall r l l', (forall x, In x l <-> In x l') -> reg_in r l = reg_in r l'.
Proof.
intros r l l' H. destruct (reg_in r l) eqn:E1, (reg_in r l') eqn:E2; try reflexivity.
- apply reg_in_In in E1. apply H in E1. apply (proj2 (reg_in_In r l')) in E1. congruence.
- apply reg_in_In in E2. apply H in E2. apply (proj2 (reg_in_In r l)) in E2. congruence.
Qed.
Lemma CLOB'_perm : forall x, In x (10%bv :: CLOB') <-> In x CLOB.
Proof. intros x. unfold CLOB', CLOB. cbn. tauto. Qed.
Lemma regs_kept_CLOB' : forall regs regs', aregs_preserved regs regs' ->
forall r, reg_in r (map fst [(10%bv : bv 5, SOff A_N 0)] ++ CLOB') = false -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. apply (regs_preserved_frame regs regs' (aregs_regs_preserved regs regs' HP)).
rewrite <- Hr. cbn [map fst app]. symmetry. apply reg_in_perm. exact CLOB'_perm.
Qed.
Lemma regs_kept_CHK : forall regs regs', chk_regs_post regs regs' ->
forall r, reg_in r (map fst [(10%bv : bv 5, SOff A_N 0)] ++ CLOB_CHK) = false -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP.
apply (YP01.reg_cases_lit (fun r => reg_in r (map fst [(10%bv : bv 5, SOff A_N 0)] ++ CLOB_CHK) = false -> getr regs' r = getr regs r)).
intros r Hin. cbv [YP01.all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin];
[ intros Hr; first [ discriminate Hr
| rewrite !getr_zero; reflexivity
| match goal with |- getr _ ?x = _ => let k := eval vm_compute in (bv_unsigned x) in
exact (HP k ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) end ] |]).
destruct Hin.
Qed.
End f.
End e.
