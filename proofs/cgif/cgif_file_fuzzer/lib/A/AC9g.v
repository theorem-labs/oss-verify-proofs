(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC93.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition PC_INIT : Z := 0x1650.
Definition lzw_MR (nP idl : Z) : Z := nP / (4094 - idl).
Definition lzw_tabs (ti lm lc li tm ld nP idl : Z) : list (Z * Z) :=
[(ld, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)].
Lemma tlzw_frame_of_region : forall E m (regs0 : bvmap 5 word) spe cs lo hi wlo whi,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spe ->
(forall od r, In (od, r) TSAVED -> exists e, In (YP09.mkChunk (- od) (CVal 8 e)) cs /\ sv_denot E e = getr regs0 r) ->
tlzw_frame m spe regs0.
Proof.
intros E m regs0 spe cs lo hi wlo whi (_ & _ & _ & Hcs) H2 Hsv. unfold tlzw_frame. apply Forall_forall. intros [od r] Hin.
cbn [fst snd]. destruct (Hsv od r Hin) as (e & Hc & He).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite H2 in Hck.
pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
replace (spe - od) with (spe + - od) by lia. change 8%nat with (N.to_nat 8).
exact (val_of_chunk_ok SEGS E m spe (- od) 8%N e (bv_unsigned (getr regs0 r)) Hck
ltac:(rewrite He; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma st_ok_region_nth : forall E ss ms i r,
st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma slot_of_region : forall E m spe cs lo hi wlo whi od e v,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spe -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem SEGS m (spe + od) 8 v.
Proof.
intros E m spe cs lo hi wlo whi od e v (_ & _ & _ & Hcs) H2 Hc He Hv.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite H2 in Hck.
change 8%nat with (N.to_nat 8). exact (val_of_chunk_ok SEGS E m spe od 8%N e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem SEGS m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok SEGS E m b od w e v Hck He Hv Hw).
Qed.
Lemma tnz_app : forall l1 l2, tnz (l1 ++ l2) = tnz l1 ++ tnz l2.
Proof. intros. unfold tnz. apply filter_app. Qed.
Lemma perm_tab_update : forall (bl bl' C l1 l2 : list (Z * Z)) (res n : Z) (P Q : Prop),
Permutation bl (tnz (l1 ++ (0, n) :: l2) ++ C) ->
(res = 0 /\ bl' = bl /\ P) \/ (4096 <= res /\ bl' = bl ++ [(res, n)] /\ Q) ->
Permutation bl' (tnz (l1 ++ (res, n) :: l2) ++ C).
Proof.
intros bl bl' C l1 l2 res n P Q HP [(-> & -> & _) | (Hr & -> & _)]; [exact HP|].
rewrite tnz_app in HP. rewrite tnz_cons0 in HP. rewrite tnz_app, tnz_cons_nz by lia.
eapply Permutation_trans; [apply Permutation_app_tail; exact HP|].
rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. rewrite app_assoc.
apply Permutation_sym. apply Permutation_cons_append.
Qed.
Lemma tnz_fst_nz : forall (b : Z * Z) l, In b (tnz l) -> fst b = 0 -> False.
Proof. intros b l Hb H0. unfold tnz in Hb. apply filter_In in Hb as [_ Hb]. rewrite H0 in Hb. discriminate Hb. Qed.
Lemma in_tnz_update : forall (l1 l2 : list (Z * Z)) (res n : Z) b,
In b (tnz (l1 ++ (res, n) :: l2)) -> b = (res, n) \/ In b (tnz (l1 ++ (0, n) :: l2)).
Proof.
intros l1 l2 res n b Hb. rewrite tnz_app in *. rewrite tnz_cons0. apply in_app_iff in Hb as [Hb | Hb].
- right. apply in_app_iff. left. exact Hb.
- unfold tnz in Hb. cbn [List.filter fst] in Hb. destruct (negb (res =? 0)).
+ destruct Hb as [<- | Hb]; [left; reflexivity | right; apply in_app_iff; right; exact Hb].
+ right. apply in_app_iff. right. exact Hb.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma awr_ok_cons_gen : forall E r rs STK sp0 FP bl0 blc ly own n b,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. apply Hw. exact Ha.
- apply H. exists r'. auto.
Qed.
Lemma aview_kept_frame : forall E rs H (m m' : word -> option byte) lo,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= lo ->
(forall a, lo <= a < 2 ^ 64 -> ~ in_wrange E rs a) ->
forall a, lo <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo HF Hlo Hno a Ha. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. apply Hno. exact Ha.
Qed.
Lemma blocks_bytes_after_malloc : forall ly1 S1 ly2 S2 (res n : Z) (P Q : Prop),
(res = 0 /\ ablocks B ly2 S2 = ablocks B ly1 S1 /\ P) \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B ly1 S1 ++ [(res, n)] /\ Q) ->
0 <= n -> blocks_bytes S2 <= blocks_bytes S1 + n.
Proof.
intros ly1 S1 ly2 S2 res n P Q Hres Hn. rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly1 S1).
destruct Hres as [(_ & -> & _) | (_ & -> & _)]; [lia|]. rewrite bsum_app. cbn. lia.
Qed.
Lemma mres_kept : forall lyc Sc W memT W2 mem2 ly2 S2 slo shi res n,
(res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ acall_kept SEGS B lyc Sc W memT W2 mem2 slo shi (fun _ => False))
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept SEGS B lyc Sc W memT W2 mem2 slo shi (fun a => res <= a < res + req_size n)) ->
acall_kept SEGS B lyc Sc W memT W2 mem2 slo shi (fun a => res <> 0 /\ res <= a < res + req_size n) /\
(forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) /\
(res <> 0 -> In (res, n) (ablocks B ly2 S2)).
Proof.
intros lyc Sc W memT W2 mem2 ly2 S2 slo shi res n [(Hz & Ebl & HK) | (Hnz & Ebl & HK)].
- split; [eapply acall_kept_mono_E; [exact HK | intros a []]|]. split; [intros b Hb; rewrite Ebl; exact Hb | intros H; lia].
- split; [eapply acall_kept_mono_E; [exact HK | intros a Ha; split; [lia | exact Ha]]|].
split; [intros b Hb; rewrite Ebl; apply in_app_iff; left; exact Hb | intros _; rewrite Ebl; apply in_app_iff; right; left; reflexivity].
Qed.
Lemma mres_range : forall ly2 S2 W2 mem2 md2 lyc Sc (res n : Z) (P Q : Prop),
AR SEGS B ly2 S2 W2 mem2 md2 ->
(res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ P) \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\ Q) ->
res = 0 \/ (4096 <= res /\ ((res + req_size n <= 65536 \/ 6270976 <= res) /\ (res + req_size n <= 2147446784 \/ 17594333495296 <= res))
/\ res + req_size n <= alloc_ceiling /\ res mod 16 = 0 /\ In (res, n) (ablocks B ly2 S2)).
Proof.
intros ly2 S2 W2 mem2 md2 lyc Sc res n P Q HAR [(-> & _ & _) | (Hr & Ebl & _)]; [left; reflexivity | right].
assert (Hin : In (res, n) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res n HAR Hin) as (H16 & _ & Hc & [Hh Happ] & _).
pose proof (blk_off_imgP _ _ _ _ _ _ res n HAR Hin) as Hh_img.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Hh_img; lia|]. split; [exact Hc|]. split; [exact H16 | exact Hin].
Qed.
Lemma region_kept_block_ajw : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi cs b m ly2 S2 md2,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er -> AR SEGS B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> 0 <= lo -> hi <= req_size m ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi lo hi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi cs b m ly2 S2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi HnE.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable SEGS). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.
Lemma writable_kept : forall H (m m2 : word -> option byte) a,
(apresent H m a -> apresent H m2 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma region_kept_aview : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- apply writable_kept. apply Hp.
Qed.
Lemma val_mem_zero8 : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 8 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 8 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
End h.
End f.
End d.
Definition shadow_word (a : Z) : Z := bv_unsigned (alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 3)) (Z_to_bv 64 SB)).
Ltac getB := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end.
Ltac getLAWS := lazymatch goal with L : AR_laws _ _ |- _ => L end.
Ltac getTL := lazymatch goal with T : PALib _ |- _ => T end.
Ltac getML := lazymatch goal with M : model_laws _ |- _ => M end.
Ltac getAM := lazymatch goal with A : amalloc_realizes _ _ |- _ => A end.
Ltac getAF := lazymatch goal with A : afree_realizes _ _ |- _ => A end.
Ltac getENV := lazymatch goal with H : api_env _ _ |- _ => H end.
Ltac reseat HS HJ2 HP2 keep AG kept_tac :=
let K := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => eval vm_compute in (run_K_lo 0 (SOff 32 0) [] ss) | st_ok _ _ ?ss _ => eval vm_compute in (run_K_lo 0 (SOff 32 0) [] ss)  end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep_pi HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG | st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG  end end.
Ltac kept_malloc HK HJ2 AG Usp :=
eapply (region_kept_stack_aj _ _);
[exact HK | exact HJ2 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
Ltac kept_ctx HK HJ2 Hc2 Hc1 Rctx AG Ebl :=
let L := getLAWS in eapply (region_kept_block_ajw _ L _ _ _ _ _ _ _ _ _ _ 37%nat 0 72 _ _ 72);
[ exact HK | exact (proj1 HJ2) | exact Hc2
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 37%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| exact Hc1 | lia | change (req_size 72) with 72; lia
| first [ intros a Ha Hn; exact Hn
| let l1 := fresh "l1" in let l2 := fresh "l2" in let El := fresh "El" in let Hd := fresh "Hd" in
intros a Ha Hra; destruct (in_split _ _ Hc1) as (l1 & l2 & El);
lazymatch type of Ebl with ablocks _ ?ly2 ?S2 = _ ++ [?nb] =>
pose proof (sep_blocks_pos _ _ L ly2 S2 _ _ _ (_, 72) nb l1 l2 [] (proj1 HJ2)
ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd end;
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd; change (req_size 72) with 72 in Hd; lia ] ].
Ltac kept_ctx_m HKw HJ2 Hc2 Hc1 Rctx AG Hres :=
let L := getLAWS in eapply (region_kept_block_ajw _ L _ _ _ _ _ _ _ _ _ _ 37%nat 0 72 _ _ 72);
[ exact HKw | exact (proj1 HJ2) | exact Hc2
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 37%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| exact Hc1 | lia | change (req_size 72) with 72; lia
| let l1 := fresh "l1" in let l2 := fresh "l2" in let El := fresh "El" in let Hd := fresh "Hd" in
let Hnz := fresh "Hnz" in let Hra := fresh "Hra" in let Ebl := fresh "Ebl" in
intros a Ha [Hnz Hra]; destruct Hres as [(? & _ & _) | (_ & Ebl & _)]; [lia|];
destruct (in_split _ _ Hc1) as (l1 & l2 & El);
lazymatch type of Ebl with ablocks _ ?ly2 ?S2 = _ ++ [?nb] =>
pose proof (sep_blocks_pos _ _ L ly2 S2 _ _ _ (_, 72) nb l1 l2 [] (proj1 HJ2)
ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd end;
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd; change (req_size 72) with 72 in Hd; lia ].
Ltac kept_intrin Hfr Hpres2 AG Usp :=
eapply region_kept_aview; [cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | intros a Ha; apply Hfr; unfold ESTACK; lia | exact Hpres2].
Ltac reshok_bx HS bx :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto SH (SOff bx 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) | st_ok _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto SH (SOff bx 0) Ex (mrestrict (w_H Wx) (ms_mem msx))  end.
Ltac reshok HS := reshok_bx HS 32%nat.
Ltac norm_ss HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS | st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS  end.
Ltac frame_tac HS idx AG EE :=
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (tlzw_frame_of_region E1);
[ eapply (st_ok_pi_region_nth E1 ss1 ms1 idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; rewrite (EE 2%nat 2%bv eq_refl); reflexivity
| let od := fresh "od" in let r := fresh "r" in let Hin := fresh "Hin" in
intros od r Hin; cbv [TSAVED In] in Hin;
repeat (destruct Hin as [Hin | Hin];
[ apply pair_equal_spec in Hin as [<- <-]; eexists; split;
[ cbv; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?AG by lia; apply EE; reflexivity ] | ]);
destruct Hin ] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (tlzw_frame_of_region E1);
[ eapply (st_ok_region_nth E1 ss1 ms1 idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; rewrite (EE 2%nat 2%bv eq_refl); reflexivity
| let od := fresh "od" in let r := fresh "r" in let Hin := fresh "Hin" in
intros od r Hin; cbv [TSAVED In] in Hin;
repeat (destruct Hin as [Hin | Hin];
[ apply pair_equal_spec in Hin as [<- <-]; eexists; split;
[ cbv; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?AG by lia; apply EE; reflexivity ] | ]);
destruct Hin ]  end.
Ltac malloc_site HS HJ nval a0tac AG Usp Rctx Hom HSZ :=
let Bv := getB in let L := getLAWS in let T := getTL in let M := getML in let AM := getAM in
let HUL := getHUL in let ENV := getENV in
let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in let Rs0 := fresh "Rs0" in
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp; prreg HS (8%bv : bv 5) Rs0;
pmkst HS; ppcs;
ppcs;
lazymatch type of Usp with _ = ?spv =>
lazymatch type of Rctx with _ = w64 ?ctxv =>
lazymatch type of HJ with ajournal _ _ ?STK ?sp0 ?FP ?ly ?S ?W0 ?mem0 ?md0 ?own ?lyc ?Sc ?Wc (ms_mem ?msX) ?mdc ?kk =>
lazymatch type of Rra with _ = Z_to_bv 64 ?ra =>
let Hnev := fresh "Hnev" in pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _);
eapply SRr_bind;
[ eapply (aj_malloc_at _ Bv L pa_segs_low ENV M AM Wc (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
lyc Sc mdc kk nval (spv - 320 - sp0) (Z_to_bv 64 ra) [] HJ);
[ first [ a0tac | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact (proj1 HSZ) | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact (proj2 HSZ) | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ unfold spZ; rewrite Rsp, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact Hom | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ lia | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ lia | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ rewrite Rgp, ?(AG 3%nat) by lia; lazymatch goal with H : ew _ 3%nat = Z_to_bv 64 (as_gp _) |- _ => rewrite H; reflexivity end | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ rewrite Rtp, ?(AG 4%nat) by lia; lazymatch goal with H : ew _ 4%nat = Z_to_bv 64 (as_tp _) |- _ => rewrite H; reflexivity end | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact Rra | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity] | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ match goal with H1 : st_nev ?Sb + LZW_EV <= EV_MAX, H2 : LZW_EV = 19 |- _ => clear - Hnev H1 H2; lia end | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ apply (achain_chain_pre lyc _ (spv - 320) ctxv [] _ (achain_low lyc _ (spv - 320) ctxv ltac:(lia)));
[ unfold spZ; rewrite Rsp, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite Rs0, Rctx; apply unsigned_lit_small; lia
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ] | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; try rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (pal_rt_below Bv T); lia);
hul_tac | match goal with |- ?g => idtac "MSFAIL" g end ] ]
| clear Rra Rsp Rgp Rtp Rs0 Hnev ] end end end end.
Ltac eatom AG Efact := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?AG by lia; exact Efact.
Ltac rregU HS r v Utac H :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = Z_to_bv 64 v)
by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
change (sv_denot Ex e = Z_to_bv 64 v); rewrite denot_lit_U; f_equal; Utac)
| st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = Z_to_bv 64 v)
by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _);
change (sv_denot Ex e = Z_to_bv 64 v); rewrite denot_lit_U; f_equal; Utac)
end.
Ltac obl_ctx HJ Hc AG Rctx E32 :=
let L := getLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?nc ?c)) ?len =>
first [ rewrite (U_atom_off Ex nc _ c) by (first [eatom AG Rctx | lia])
| rewrite (U_atom Ex nc _) by (first [eatom AG Rctx | lia]) ];
lazymatch type of Rctx with _ = w64 ?ctxv =>
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff bx 0) _ len ctxv 72 (proj1 HJ) Hc);
[ rewrite (U_atom Ex bx SB) by (first [eatom AG E32 | unfold SB; lia]); reflexivity
| lia | change (req_size 72) with 72; lia ] end end.
Ltac awr2 Actx Hc AG Rctx Usp :=
lazymatch type of Rctx with _ = w64 ?ctxv =>
lazymatch type of Usp with _ = ?spv =>
lazymatch goal with |- awr_ok _ _ ?STK ?sp0 _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ ctxv); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Rctx; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (ctxv + (a - ctxv)) by lia; apply Actx; [exact Hc | lia] |];
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; rewrite Usp; lia | cbn; lia | cbn; lia | awr_ok_tac] end end end.
Ltac obls HJ Hc AG Rctx E32 Actx Usp :=
lazymatch goal with
| |- range_addressable _ _ _ _ => obl_ctx HJ Hc AG Rctx E32
| |- awr_ok _ _ _ _ _ _ _ _ _ => awr2 Actx Hc AG Rctx Usp
| |- _ => idtac
end.
Ltac chunk_val AG Rctx :=
first [ rewrite denot_lit_U; f_equal; apply (U_tisz _ 13); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?AG by lia; assumption | assumption]
| rewrite denot_lit_U; f_equal; apply (U_idl2 _ 13); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?AG by lia; assumption | assumption]
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ reflexivity
| rewrite ?AG by lia; assumption
| rewrite ?AG by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity
|
unfold shadow_word; rewrite ?Z_to_bv_bv_unsigned; rewrite ?AG by lia; rewrite Rctx;
match goal with H : ew _ 32%nat = _ |- _ => rewrite ?(AG 32%nat) by lia; rewrite H end; rewrite ?unsigned_lit_small by lia; reflexivity
| match goal with |- ?g => idtac "CHUNKVAL" g end ] ].
Ltac ctx_field HS idx Rctx AG :=
lazymatch goal with |- val_mem _ _ (?ctxv + ?off) ?nn ?v =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let w := eval vm_compute in (N.of_nat nn) in
eapply (field_of_region Ex _ 37%nat ctxv _ _ _ _ _ off w _ v);
[ eapply (st_ok_pi_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite Rctx; apply unsigned_lit_small; lia
| cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [reflexivity | rewrite ?AG by lia; assumption | match goal with |- ?g => idtac "FIELDVAL" g end]
| cbn; lia | cbn; lia ] | st_ok _ ?Ex ?ssx ?msx =>
let w := eval vm_compute in (N.of_nat nn) in
eapply (field_of_region Ex _ 37%nat ctxv _ _ _ _ _ off w _ v);
[ eapply (st_ok_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite Rctx; apply unsigned_lit_small; lia
| cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [reflexivity | rewrite ?AG by lia; assumption | match goal with |- ?g => idtac "FIELDVAL" g end]
| cbn; lia | cbn; lia ]  end
| |- val_mem _ _ ?ctxv _ ?v =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
rewrite <- (Z.add_0_r ctxv) at 1;
eapply (field_of_region Ex _ 37%nat ctxv _ _ _ _ _ 0 8%N _ v);
[ eapply (st_ok_pi_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite Rctx; apply unsigned_lit_small; lia
| cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [reflexivity | rewrite ?AG by lia; assumption | match goal with |- ?g => idtac "FIELDVAL" g end]
| cbn; lia | cbn; lia ] | st_ok _ ?Ex ?ssx ?msx =>
rewrite <- (Z.add_0_r ctxv) at 1;
eapply (field_of_region Ex _ 37%nat ctxv _ _ _ _ _ 0 8%N _ v);
[ eapply (st_ok_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite Rctx; apply unsigned_lit_small; lia
| cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [reflexivity | rewrite ?AG by lia; assumption | match goal with |- ?g => idtac "FIELDVAL" g end]
| cbn; lia | cbn; lia ]  end end.
Ltac slot_tac HS idx Usp AG Rctx :=
lazymatch type of Usp with _ = ?spv =>
lazymatch goal with |- val_mem _ _ (_ - 320 + ?k) 8 ?v =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
replace (spZ _ - 320 + k) with (spv + (k - 320)) by (fold spv; lia);
eapply (slot_of_region Ex _ spv _ _ _ _ _ (k - 320) _ v);
[ eapply (st_ok_pi_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp
| cbn; repeat (first [left; reflexivity | right])
| chunk_val AG Rctx
| first [ lia
|
unfold shadow_word; lazymatch goal with |- 0 <= bv_unsigned ?x < _ =>
let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 x) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq end ] ] | st_ok _ ?Ex ?ssx ?msx =>
replace (spZ _ - 320 + k) with (spv + (k - 320)) by (fold spv; lia);
eapply (slot_of_region Ex _ spv _ _ _ _ _ (k - 320) _ v);
[ eapply (st_ok_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp
| cbn; repeat (first [left; reflexivity | right])
| chunk_val AG Rctx
| first [ lia
|
unfold shadow_word; lazymatch goal with |- 0 <= bv_unsigned ?x < _ =>
let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 x) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq end ] ]  end end end.
Ltac slot_tacS HS idx Usp AG Rctx E32 :=
lazymatch type of Usp with _ = ?spv =>
lazymatch goal with |- val_mem _ _ (_ - 320 + ?k) 8 (shadow_word ?a) =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
replace (spZ _ - 320 + k) with (spv + (k - 320)) by (fold spv; lia);
eapply (slot_of_region Ex _ spv _ _ _ _ _ (k - 320) _ (shadow_word a));
[ eapply (st_ok_pi_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp
| cbn; repeat (first [left; reflexivity | right])
| unfold shadow_word; rewrite Z_to_bv_bv_unsigned;
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
rewrite Rctx; rewrite ?(AG 32%nat) by lia; rewrite E32; rewrite ?unsigned_lit_small by lia;
first [reflexivity | match goal with |- ?g => idtac "SLOTS-VAL" g end]
| unfold shadow_word;
match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as Hw; change (bv_modulus 64) with (2 ^ 64) in Hw; exact Hw end ] | st_ok _ ?Ex ?ssx ?msx =>
replace (spZ _ - 320 + k) with (spv + (k - 320)) by (fold spv; lia);
eapply (slot_of_region Ex _ spv _ _ _ _ _ (k - 320) _ (shadow_word a));
[ eapply (st_ok_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp
| cbn; repeat (first [left; reflexivity | right])
| unfold shadow_word; rewrite Z_to_bv_bv_unsigned;
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
rewrite Rctx; rewrite ?(AG 32%nat) by lia; rewrite E32; rewrite ?unsigned_lit_small by lia;
first [reflexivity | match goal with |- ?g => idtac "SLOTS-VAL" g end]
| unfold shadow_word;
match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as Hw; change (bv_modulus 64) with (2 ^ 64) in Hw; exact Hw end ]  end end end.
Ltac to_clean HS HJ HB TOK AG EE Usp Rctx E32 pld pti plm plc pli ptm stkidx ctxidx :=
let Bv := getB in let L := getLAWS in let T := getTL in let M := getML in let AF := getAF in
let R2 := fresh "R2" in let R3 := fresh "R3" in let R4 := fresh "R4" in let R8 := fresh "R8" in let R9 := fresh "R9" in
let R18 := fresh "R18" in let R19 := fresh "R19" in let R20 := fresh "R20" in let R21 := fresh "R21" in
let R24 := fresh "R24" in let R26 := fresh "R26" in let R27 := fresh "R27" in
prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4; prreg HS (8%bv : bv 5) R8; prreg HS (22%bv : bv 5) R9;
prreg HS (20%bv : bv 5) R18; prreg HS (9%bv : bv 5) R19; prreg HS (27%bv : bv 5) R20; prreg HS (21%bv : bv 5) R21;
prreg HS (18%bv : bv 5) R24; prreg HS (1%bv : bv 5) R26; prreg HS (19%bv : bv 5) R27;
let HFR := fresh "HFR" in
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msx) =>
lazymatch type of Usp with _ = ?spv =>
lazymatch type of EE with forall n rr, _ -> _ = getr ?regs0 rr =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) spv regs0) by (frame_tac HS stkidx AG EE) end end | st_ok _ _ _ (restrict (w_H ?Wx) ?msx) =>
lazymatch type of Usp with _ = ?spv =>
lazymatch type of EE with forall n rr, _ -> _ = getr ?regs0 rr =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) spv regs0) by (frame_tac HS stkidx AG EE) end end  end;
pmkst HS; ppcs;
lazymatch type of HJ with ajournal _ _ ?STK ?sp0 ?FP ?ly ?S ?W0 ?mem0 ?md0 ?own ?lyc ?Sc ?Wc (ms_mem ?msX) ?mdc ?kk =>
lazymatch type of Rctx with _ = w64 ?ctxv =>
lazymatch type of HB with Permutation _ (tnz [(_, ?nld); (_, ?nti); (_, ?nlm); (_, ?nlc); (_, ?nli); (_, ?ntm)] ++ _ :: ?Cfin) =>
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdX) _ =>
lazymatch type of EE with forall n rr, _ -> _ = getr ?regs0 rr =>
let Hnev := fresh "Hnev" in pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _);
eapply SRr_mono;
[ eapply (tlzw_clean Bv T L M AF ltac:(pHUL) Wc (ms_regs msX) (ms_mem msX) mdX regs0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk
ctxv pti nti plm nlm plc nlc pli nli ptm ntm pld nld Cfin 2 HJ HB);
[ first [ intros b Hb; apply (TOK b Hb) | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "0" end ]
| first [ let b := fresh "b" in let Hb := fresh "Hb" in
intros b Hb; cbv [In] in Hb;
repeat (destruct Hb as [Hb | Hb]; [subst b; cbn [fst]; first [lia | ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia] |]); destruct Hb | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "1" end ]
| first [ ctx_field HS ctxidx Rctx AG | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "2" end ]
| first [ ctx_field HS ctxidx Rctx AG | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "3" end ]
| first [ ctx_field HS ctxidx Rctx AG | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "4" end ]
| first [ ctx_field HS ctxidx Rctx AG | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "5" end ]
| first [ ctx_field HS ctxidx Rctx AG | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "6" end ]
| first [ ctx_field HS ctxidx Rctx AG | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "7" end ]
| first [ first [assumption | match goal with |- ?g => idtac "ASSUM" g end] | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "8" end ]
| first [ first [assumption | match goal with |- ?g => idtac "ASSUM" g end] | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "9" end ]
| first [ first [assumption | match goal with |- ?g => idtac "ASSUM" g end] | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "10" end ]
| first [ first [assumption | match goal with |- ?g => idtac "ASSUM" g end] | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "11" end ]
| first [ lazymatch goal with H : ew _ 3%nat = Z_to_bv 64 (as_gp _) |- _ => rewrite <- (EE 3%nat 3%bv eq_refl); exact H end | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "12" end ]
| first [ lazymatch goal with H : ew _ 4%nat = Z_to_bv 64 (as_tp _) |- _ => rewrite <- (EE 4%nat 4%bv eq_refl); exact H end | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "13" end ]
| first [ lazymatch type of Usp with _ = ?spv => fold spv end; unfold spZ; rewrite R2, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "14" end ]
| first [ rewrite R3, ?(AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl) | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "15" end ]
| first [ rewrite R4, ?(AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl) | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "16" end ]
| first [ rewrite R8; exact Rctx | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "17" end ]
| first [ rewrite R20, ?(AG 32%nat) by lia; exact E32 | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "18" end ]
| first [ exact R21 | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "19" end ]
| first [ lia | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "20" end ]
| first [ rewrite R9, Rctx, ?(AG 32%nat) by lia; rewrite E32; reflexivity | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "21" end ]
| first [ rewrite R18, Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "22" end ]
| first [ rewrite R27, Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "23" end ]
| first [ rewrite R24, Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "24" end ]
| first [ rewrite R19, Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "25" end ]
| first [ rewrite R26, Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "26" end ]
| first [ exact HFR | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "27" end ]
| first [ match goal with H1 : st_nev ?Sb + LZW_EV <= EV_MAX, H2 : LZW_EV = 19 |- _ => clear - Hnev H1 H2; lia end | match goal with |- ?g => idtac "TCFAIL" g; idtac "BR" "28" end ] ]
| ];
[ ..
|
let W9 := fresh "W" in let c9 := fresh "c" in let ly9 := fresh "ly" in let S9 := fresh "S" in let regs9 := fresh "regs" in
let mem9 := fresh "mem" in let md9 := fresh "md" in let HJ9 := fresh "HJ" in let HP9 := fresh "HP" in let Ha9 := fresh "Ha" in
let Hfrs9 := fresh "Hfrs" in let HPerm9 := fresh "HPerm" in
cbv beta; intros W9 c9 _ (ly9 & S9 & regs9 & mem9 & md9 & -> & HJ9 & HP9 & Ha9 & Hfrs9 & HPerm9 & _);
left; exists ly9, S9, regs9, mem9, md9; split; [reflexivity|];
split; [eapply ajournal_mono_k; [exact HJ9 | match goal with H2 : LZW_EV = 19 |- _ => rewrite H2; lia end]|];
split; [exact HP9|]; split; [exact Ha9|];
split; [rewrite Hfrs9; repeat match goal with H : frames ?x = frames _ |- frames ?x = _ => rewrite H end; reflexivity | exact HPerm9] ]
end end end end end.
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section q.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section s.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Definition tpro_ok (STK sp0 : Z) (FP : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS)
(memc : word -> option byte) (mdc : Model) (own : list (Z * Z))
(regs : bvmap 5 word) (pR nP img idl icl : Z) : world SEGS -> config -> Prop :=
fun W6 c6 => exists ly6 S6 regs6 mem6 md6 (ctx ti lm lc li tm ld : Z),
let m6 := mrestrict (w_H W6) mem6 in let sp := spZ regs - 320 in
let tabs := lzw_tabs ti lm lc li tm ld nP idl in
c6 = mkCfg (mkst regs6 (Z_to_bv 64 (BASE + PC_INIT)) mem6 (seg_rom SEGS)) md6 /\
ajournal SEGS B STK sp0 FP lyc Sc W memc mdc own ly6 S6 W6 mem6 md6 7 /\
spZ regs6 = sp /\ getr regs6 3 = getr regs 3 /\ getr regs6 4 = getr regs 4 /\
getr regs6 8 = w64 ctx /\ getr regs6 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 ctx) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regs6 20 = w64 (ctx + 8) /\ getr regs6 19 = w64 (ctx + 16) /\ getr regs6 18 = w64 (ctx + 24) /\ getr regs6 9 = w64 (ctx + 32) /\
getr regs6 27 = w64 SB /\ getr regs6 21 = w64 2 /\ getr regs6 25 = w64 idl /\
getr regs6 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regs6 1 = w64 (ctx + 40) /\ getr regs6 10 = w64 ld /\
tlzw_frame m6 (spZ regs) regs /\
val_mem SEGS m6 (sp + 208) 8 (ctx + 40) /\ val_mem SEGS m6 (sp + 200) 8 (shadow_word (ctx + 16)) /\ val_mem SEGS m6 (sp + 192) 8 (shadow_word (ctx + 24)) /\
val_mem SEGS m6 (sp + 184) 8 (2 * idl * idl) /\ val_mem SEGS m6 (sp + 176) 8 icl /\ val_mem SEGS m6 (sp + 168) 8 (2 * idl) /\
val_mem SEGS m6 (sp + 160) 8 (shadow_word (ctx + 32)) /\ val_mem SEGS m6 (sp + 152) 8 pR /\ val_mem SEGS m6 (sp + 144) 8 (ctx + 56) /\
val_mem SEGS m6 (sp + 136) 8 (shadow_word (ctx + 56)) /\ val_mem SEGS m6 (sp + 128) 8 (shadow_word (ctx + 40)) /\
val_mem SEGS m6 (sp + 120) 8 (ctx + 48) /\ val_mem SEGS m6 (sp + 112) 8 (shadow_word (ctx + 48)) /\
val_mem SEGS m6 ctx 8 ti /\ val_mem SEGS m6 (ctx + 8) 8 lm /\ val_mem SEGS m6 (ctx + 16) 8 lc /\
val_mem SEGS m6 (ctx + 24) 8 li /\ val_mem SEGS m6 (ctx + 32) 8 tm /\ val_mem SEGS m6 (ctx + 40) 8 ld /\
val_mem SEGS m6 (ctx + 48) 8 img /\ val_mem SEGS m6 (ctx + 56) 4 nP /\
Permutation (ablocks B ly6 S6) (tabs ++ (ctx, 72) :: ablocks B lyc Sc) /\
(forall b, In b ((ctx, 72) :: tabs) ->
4096 <= fst b /\ 0 <= snd b /\ aftok FP (ablocks B lyc Sc) b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (fst b + i)) /\
frames S6 = frames Sc.
Definition tpro_fail (STK sp0 : Z) (FP : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS)
(memc : word -> option byte) (mdc : Model) (own : list (Z * Z)) (regs : bvmap 5 word)
: world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP lyc Sc W memc mdc own ly2 S2 W2 mem2 md2 LZW_EV /\
aregs_preserved regs regs2 /\ getr regs2 10 = w64 2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc).
Definition lzw_facts : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0 (2^63 - 16) 3); (11%nat, mkAF 1 100000000 0);
(12%nat, PTR 0); (13%nat, mkAF 2 256 0); (14%nat, mkAF 0 12 0); (32%nat, mkAF SB SB 0) ].
Definition ss_lzw : sstate := mkSS A_LZW sr_atoms [stack_region 320; got_regionP; bcell_regionP 32] None (mkFacts lzw_facts [] []).
Definition ss_lzw_c : sstate := Eval vm_compute in ss_lzw.
Lemma tlzw_entry : forall W STK sp0 FP ly S W0 mem0 md0 own lyc Sc memc mdc k (regs : bvmap 5 word) (pR nP img idl icl bi Li : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 pR -> getr regs 11 = w64 nP -> getr regs 12 = w64 img -> getr regs 13 = w64 idl -> getr regs 14 = w64 icl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_TSTK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> 0 <= pR -> pR + 16 <= 2 ^ 63 ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (ablocks B lyc Sc) -> bi <= img -> img + nP <= bi + req_size Li ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 SB])) ss_lzw_c (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_LZW)) memc (seg_rom SEGS))).
Proof.
intros W STK sp0 FP ly S W0 mem0 md0 own lyc Sc memc mdc k regs pR nP img idl icl bi Li
HJ G10 G11 G12 G13 G14 Hal16 Hwlo Hwhi HpR8 HpR0 HpR63 HnP Hidl Hicl Hbi Hbi1 Hbi2.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HAR Hbi) as (Hbi16 & Hbi4096 & Hbiceil & Hbih_ia & _ & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bi Li HAR Hbi) as Hbih_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx. change ss_lzw_c with ss_lzw.
set (E := Eimg (Ereg regs [Z_to_bv 64 SB])).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 pR) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 nP) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact G11).
assert (E12 : ew E 12 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact G12).
assert (E13 : ew E 13 = Z_to_bv 64 idl) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact G13).
assert (E14 : ew E 14 = Z_to_bv 64 icl) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact G14).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold ss_lzw. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [base_val]. rewrite E241, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
+ cbn [base_val]. rewrite E253, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, E241, E253.
rewrite !unsigned_lit_small by (first [pose proof (pa_val_range (A_OBJ 0)); lia | pose proof (pa_val_range (A_OBJ 12)); lia]).
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hwlo Hwhi C1 C3 HTS Has Hstk0 HcellR HgcD HgotR. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok lzw_facts]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E12, E13, E14, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hwlo Hwhi Hal16 HpR8 HpR0 HpR63 HnP Hidl Hicl Hbi1 Hbi2 Hbi16 Hbi4096 Hbiceil Hbih Hbih_img C1 C3 HTS Has Hstk0. clear. unfold off_img.
ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. pose proof (req_size_pos' Li) as HrL. repeat match goal with |- _ /\ _ => split end; try lia.
all: match goal with |- ?g => idtac "ENTRYFACT" g end; fail.
Qed.
Definition tok_inv (STK sp0 : Z) (FP : list (Z * Z)) (bl0 : list (Z * Z)) (own : list (Z * Z)) (l : list (Z * Z)) : Prop :=
forall b, In b l -> 4096 <= fst b /\ 0 <= snd b /\ aftok FP bl0 b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP bl0 blc lyq own (fst b + i).
Definition ss_pro9 : sstate :=
(mkSS 0x154c
[SLit 0; SOff 113 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 114 0; SOff 115 0; SOff 116 0; SOff 37 0; SOff 37 32; SOff 117 0; SOff 118 0; SOff 119 0; SOff 120 0; SOff 121 0; SOff 122 0; SOff 123 0; SOff 124 0; SOff 37 24;
SOff 37 16; SOff 37 8; SLit 2; SAlu ALU_ADD (SAlu ALU_SRL (SOff 37 0) (SLit 3)) (SOff 32 0); SOff 12 0; SOff 11 0; SOff 13 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 37 8) (SLit 3)) (SOff 32 0); SOff 32 0; SOff 125 0; SOff 126 0;
SOff 127 0; SOff 128 0]
[{|
r_base := Some 37%nat;
r_lo := 0;
r_hi := 72;
r_wlo := 0;
r_whi := 72;
r_chunks :=
[{| c_off := 16; YP09.c_val := CVal 8 (SOff 101 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 85 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SOff 69 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 48; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -320;
r_hi := 0;
r_wlo := -320;
r_whi := 0;
r_chunks :=
[{| c_off := -120; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 37 16) (SLit 3)) (SOff 32 0)) |}; {| c_off := -112; YP09.c_val := CVal 8 (SOff 37 40) |}; {| c_off := -168; YP09.c_val := CVal 8 (SOff 10 0) |};
{| c_off := -136; YP09.c_val := CVal 8 (SMd M_MUL (SAlu ALU_SLL (SOff 13 0) (SLit 1)) (SOff 13 0)) |}; {| c_off := -152; YP09.c_val := CVal 8 (SAlu ALU_SLL (SOff 13 0) (SLit 1)) |};
{| c_off := -144; YP09.c_val := CVal 8 (SOff 14 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}]
None
{|
f_atoms :=
[(69%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (37%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |});
(10%nat, {| af_lo := 0; af_hi := 9223372036854775792; af_al2 := 3 |}); (11%nat, {| af_lo := 1; af_hi := 100000000; af_al2 := 0 |}); (12%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(13%nat, {| af_lo := 2; af_hi := 256; af_al2 := 0 |}); (14%nat, {| af_lo := 0; af_hi := 12; af_al2 := 0 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |})];
f_conds := [];
f_alias := []
|}).
Definition ss_pro9_c : sstate := Eval vm_compute in ss_pro9.
Lemma tlzw_pro9 : forall E W6 (regs6 : bvmap 5 word) mem6 md6 STK sp0 FP lyc Sc W memc mdc own ly6 S6
(regs : bvmap 5 word) (pR nP img idl icl bi Li ctx ti lm lc li : Z),
st_ok_pi SEGS VAL E ss_pro9_c (restrict (w_H W6) (mkst regs6 (Z_to_bv 64 (BASE + 0x154c)) mem6 (seg_rom SEGS))) -> img_env VAL A_LIM E ->
ajournal SEGS B STK sp0 FP lyc Sc W memc mdc own ly6 S6 W6 mem6 md6 5 ->
(forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
ew E 32%nat = w64 SB -> ew E 37%nat = w64 ctx -> ew E 69%nat = w64 ti -> ew E 85%nat = w64 lm -> ew E 101%nat = w64 lc -> ew E 117%nat = w64 li ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 pR -> getr regs 11 = w64 nP -> getr regs 12 = w64 img -> getr regs 13 = w64 idl -> getr regs 14 = w64 icl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_TSTK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> 0 <= pR -> pR + 16 <= 2 ^ 63 ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (ablocks B lyc Sc) -> bi <= img -> img + nP <= bi + req_size Li ->
st_nev Sc + LZW_EV <= EV_MAX -> blocks_bytes Sc + 2 ^ 29 <= LIVE_MAX ->
Permutation (ablocks B ly6 S6)
(tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (0, 4098 * idl)] ++ (ctx, 72) :: ablocks B lyc Sc) ->
tok_inv STK sp0 FP (ablocks B lyc Sc) own
((ctx, 72) :: tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (0, 4098 * idl)]) ->
4096 <= ti -> ti + req_size (2 * idl * idl) <= alloc_ceiling ->
(lm = 0 \/ 4096 <= lm < 2 ^ 64) -> (lc = 0 \/ 4096 <= lc < 2 ^ 64) -> (li = 0 \/ 4096 <= li < 2 ^ 64) ->
blocks_bytes S6 <= blocks_bytes Sc + (72 + 2 * idl * idl + 8192 + 4096 + 8192) -> frames S6 = frames Sc ->
SRr SEGS W6 (mkCfg (mkst regs6 (Z_to_bv 64 (BASE + 0x154c)) mem6 (seg_rom SEGS)) md6)
(fun W' c' => tpro_fail STK sp0 FP lyc Sc W memc mdc own regs W' c' \/
tpro_ok STK sp0 FP lyc Sc W memc mdc own regs pR nP img idl icl W' c').
Proof.
intros E W6 regs6 mem6 md6 STK sp0 FP lyc Sc W memc mdc own ly6 S6 regs pR nP img idl icl bi Li ctx ti lm lc li
HS HEI HJ6 EE E32 Rctx Rti Rlm Rlc Rli Hra0 Hgp Htp G10 G11 G12 G13 G14 Hal16 Hwlo Hwhi HpR8 HpR0 HpR63 HnP Hidl Hicl Hbi Hbi1 Hbi2 Hev Hlive
HB6 TOK6 Hti4096 Hticeil Hlm Hlc Hli HBB6 Hfrs6.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ6 as (HAR6 & Hly6 & _ & _ & _ & _ & Hnev6 & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof Hly6 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity.
assert (ASTACK = 16384) as Has by reflexivity. assert (HEV : LZW_EV = 19) by reflexivity.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
pose proof (req_size_pos' (2 * idl * idl) ltac:(lia)) as Hrq.
assert (Htisz : 8 <= 2 * idl * idl <= 131072) by (clear - Hidl; nia).
assert (Hin6 : forall b, In b (tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (0, 4098 * idl)] ++ (ctx, 72) :: ablocks B lyc Sc) ->
In b (ablocks B ly6 S6)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HB6 | exact Hb]).
assert (Hctx6 : In (ctx, 72) (ablocks B ly6 S6)) by (apply Hin6; apply in_app_iff; right; left; reflexivity).
assert (Hbi6 : In (bi, Li) (ablocks B ly6 S6)) by (apply Hin6; apply in_app_iff; right; right; exact Hbi).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HAR6 Hbi6) as (Hbi16 & Hbi4096 & Hbiceil & Hbih_ia & _ & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bi Li HAR6 Hbi6) as Hbih_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ ctx 72 HAR6 Hctx6) as (Hc16 & Hc4096 & Hcceil & Hchigh_ia & Hcpres & _). pose proof (proj1 Hchigh_ia) as Hchigh.
pose proof (blk_off_imgP _ _ _ _ _ _ ctx 72 HAR6 Hctx6) as Hchigh_img.
change (req_size 72) with 72 in Hcceil, Hcpres.
assert (Actx : forall blc lyq i, In (ctx, 72) blc -> 0 <= i < 72 -> awr_byte STK sp0 FP (ablocks B lyc Sc) blc lyq own (ctx + i)).
{ intros blc lyq i Hin Hi. apply (TOK6 (ctx, 72) ltac:(left; reflexivity)); [exact Hin | cbn [snd]; change (req_size 72) with 72; lia]. }
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
assert (E10 : ew E 10 = Z_to_bv 64 pR) by (rewrite (EE 10%nat 10%bv ltac:(lia) eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 nP) by (rewrite (EE 11%nat 11%bv ltac:(lia) eq_refl); exact G11).
assert (E12 : ew E 12 = Z_to_bv 64 img) by (rewrite (EE 12%nat 12%bv ltac:(lia) eq_refl); exact G12).
assert (E13 : ew E 13 = Z_to_bv 64 idl) by (rewrite (EE 13%nat 13%bv ltac:(lia) eq_refl); exact G13).
assert (E14 : ew E 14 = Z_to_bv 64 icl) by (rewrite (EE 14%nat 14%bv ltac:(lia) eq_refl); exact G14).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
set (sp := spZ regs) in *.
assert (Hom : (sp - 320 - sp0) mod 16 = 0).
{ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D0. pose proof (Z.div_mod sp 16 ltac:(lia)) as D1.
rewrite Hsp0al, Z.add_0_r in D0. rewrite Hal16, Z.add_0_r in D1.
replace (sp - 320 - sp0) with ((sp / 16 - 20 - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EE' : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. apply EE; [|exact Hn]. pose proof (bv_unsigned_in_range 5 rr) as Hr. change (bv_modulus 5) with 32 in Hr. lia. }
clear EE. rename EE' into EE.
reshok HS.
paj_run_tok RUN HS HJ6 SHOK Bspan; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |].
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{
paj_run_to_tok RUNTO HS HJ6 SHOK Bspan 0x2138; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |].
clear HF HFr HG.
to_clean HS HJ6 HB6 TOK6 AG EE Usp Rctx E32 0 ti lm lc li 0 1%nat 0%nat. }
rewrite branch_eq_U, (U_atom _ 85 lm), U_SLit in Hc by (first [eatom AG Rlm | lia]). change (zcanon 0) with 0 in Hc.
assert (Hlm1 : lm <> 0) by (destruct (Z.eqb_spec lm 0); [discriminate | assumption]). clear Hc.
paj_run_tok RUN HS HJ6 SHOK Bspan; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |]. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{
paj_run_to_tok RUNTO HS HJ6 SHOK Bspan 0x2138; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |].
clear HF HFr HG.
to_clean HS HJ6 HB6 TOK6 AG EE Usp Rctx E32 0 ti lm lc li 0 1%nat 0%nat. }
rewrite branch_eq_U, (U_atom _ 101 lc), U_SLit in Hc by (first [eatom AG Rlc | lia]). change (zcanon 0) with 0 in Hc.
assert (Hlc1 : lc <> 0) by (destruct (Z.eqb_spec lc 0); [discriminate | assumption]). clear Hc.
paj_run_tok RUN HS HJ6 SHOK Bspan; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |]. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{
paj_run_to_tok RUNTO HS HJ6 SHOK Bspan 0x2138; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |].
clear HF HFr HG.
to_clean HS HJ6 HB6 TOK6 AG EE Usp Rctx E32 0 ti lm lc li 0 1%nat 0%nat. }
rewrite branch_eq_U, (U_atom _ 117 li), U_SLit in Hc by (first [eatom AG Rli | lia]). change (zcanon 0) with 0 in Hc.
assert (Hli1 : li <> 0) by (destruct (Z.eqb_spec li 0); [discriminate | assumption]). clear Hc.
paj_run_tok RUN HS HJ6 SHOK Bspan; [obl_ctx HJ6 Hctx6 AG Rctx E32 .. | awr2 Actx Hctx6 AG Rctx Usp |]. clear HF HFr HG.
rregU HS (10%bv : bv 5) (4098 * idl) ltac:(apply (U_tmsz _ 13 idl); [eatom AG E13 | exact Hidl]) Ra0.
assert (HSZ6 : 0 <= 4098 * idl < MALLOC_MAX /\ blocks_bytes S6 + 4098 * idl <= LIVE_MAX) by (clear - HMM HBB6 Hlive Htisz Hidl; rewrite HMM; unfold LIVE_MAX in *; lia).
malloc_site HS HJ6 (4098 * idl) ltac:(exact Ra0) AG Usp Rctx Hom HSZ6. clear Ra0.
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & tm & -> & HJ7 & HP7 & Ha07 & Hfrs7 & Hres7).
assert (HBB7 : blocks_bytes S7 <= blocks_bytes Sc + (72 + 2 * idl * idl + 8192 + 4096 + 8192 + 4098 * idl)) by (pose proof (blocks_bytes_after_malloc B _ _ _ _ _ _ _ _ Hres7 ltac:(lia)); lia).
destruct (mres_kept B _ _ _ _ _ _ _ _ _ _ _ _ Hres7) as (HK7 & Hsub7 & Htm_in).
pose proof (mres_range B LAWS _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ7) Hres7) as Hrr7.
assert (Hctx7 : In (ctx, 72) (ablocks B ly7 S7)) by (apply Hsub7; exact Hctx6).
pose proof (perm_tab_update _ _ _ [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192)] _ tm _ _ _ HB6 Hres7) as HB7. cbn [app] in HB7.
assert (TOK7 : tok_inv STK sp0 FP (ablocks B lyc Sc) own
((ctx, 72) :: tnz [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)])).
{ intros b [<- | Hb]; [apply TOK6; left; reflexivity|].
destruct (in_tnz_update [(0, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192)] _ tm _ b Hb) as [-> | Hb']; [| apply TOK6; right; exact Hb'].
cbn [fst snd]. destruct Hres7 as [(Hz0 & _ & _) | (Hnz & Ebl & _)].
{ exfalso. subst tm. exact (tnz_fst_nz _ _ Hb eq_refl). }
split; [exact Hnz|]. split; [lia|]. split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tm _ HJ6 (proj1 HJ7) Ebl ltac:(lia))|].
intros blc lyq i Hin Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tm _ blc i lyq HJ6 (proj1 HJ7) Ebl ltac:(lia) Hin Hi). }
reseat HS HJ7 HP7 [0%nat; 1%nat] AG ltac:(first [kept_malloc HK7 HJ7 AG Usp | kept_ctx_m HK7 HJ7 Hctx7 Hctx6 Rctx AG Hres7]).
prreg HS (10%bv : bv 5) Rtm. rewrite Ha07 in Rtm. symmetry in Rtm.
destruct Hrr7 as [Htm0 | (Htm4096 & Htmh & Htmceil & Htm16 & Htm7)].
{
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha07, Htm0; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS. reshok HS. subst tm.
paj_run_to_tok RUNTO HS HJ7 SHOK Bspan 0x2138; [obl_ctx HJ7 Hctx7 AG Rctx E32 .. | awr2 Actx Hctx7 AG Rctx Usp |].
clear HF HFr HG.
to_clean HS HJ7 HB7 TOK7 AG EE Usp Rctx E32 0 ti lm lc li 0 1%nat 0%nat. }
pose proof (req_size_pos' (4098 * idl) ltac:(lia)) as Hrq7.
lazymatch type of Rtm with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (PTR 4) HS
ltac:(clear HS; idtac; unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite Rtm, unsigned_lit_small by lia;
change (2 ^ 4) with 16; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
paj_run_tok RUN HS HJ7 SHOK Bspan;
[obl_ctx HJ7 Hctx7 AG Rctx E32 .. | awr2 Actx Hctx7 AG Rctx Usp |].
clear HF HFr HG.
pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [HMR1 HMR2].
assert (HMRle : 0 <= lzw_MR nP idl <= nP) by (clear - HMR1 HMR2 Hidl HnP; unfold lzw_MR in *; nia).
rregU HS (10%bv : bv 5) (2 * (lzw_MR nP idl + nP + 2))
ltac:(unfold lzw_MR; apply (U_ldsz _ 13 11 idl nP); [eatom AG E13 | eatom AG E11 | exact Hidl | exact HnP]) Ra0.
assert (HMRb : 3838 * lzw_MR nP idl <= nP) by (clear - HMR1 HMR2 Hidl HnP; unfold lzw_MR in *; nia).
assert (HSZ7 : 0 <= 2 * (lzw_MR nP idl + nP + 2) < MALLOC_MAX /\ blocks_bytes S7 + 2 * (lzw_MR nP idl + nP + 2) <= LIVE_MAX) by (clear - HMM HBB7 Hlive Htisz Hidl HnP HMRb HMRle; rewrite HMM; unfold LIVE_MAX in *; lia).
malloc_site HS HJ7 (2 * (lzw_MR nP idl + nP + 2)) ltac:(exact Ra0) AG Usp Rctx Hom HSZ7. clear Ra0.
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & ld & -> & HJ8 & HP8 & Ha08 & Hfrs8 & Hres8).
destruct (mres_kept B _ _ _ _ _ _ _ _ _ _ _ _ Hres8) as (HK8 & Hsub8 & Hld_in).
pose proof (mres_range B LAWS _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ8) Hres8) as Hrr8.
assert (Hctx8 : In (ctx, 72) (ablocks B ly8 S8)) by (apply Hsub8; exact Hctx7).
pose proof (perm_tab_update _ _ _ [] _ ld _ _ _ HB7 Hres8) as HB8. cbn [app] in HB8.
assert (TOK8 : tok_inv STK sp0 FP (ablocks B lyc Sc) own
((ctx, 72) :: tnz [(ld, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)])).
{ intros b [<- | Hb]; [apply TOK7; left; reflexivity|].
destruct (in_tnz_update [] _ ld _ b Hb) as [-> | Hb']; [| apply TOK7; right; exact Hb'].
cbn [fst snd]. destruct Hres8 as [(Hz0 & _ & _) | (Hnz & Ebl & _)].
{ exfalso. subst ld. exact (tnz_fst_nz _ _ Hb eq_refl). }
split; [exact Hnz|]. split; [lia|]. split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ HJ7 (proj1 HJ8) Ebl ltac:(lia))|].
intros blc lyq i Hin Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ blc i lyq HJ7 (proj1 HJ8) Ebl ltac:(lia) Hin Hi). }
reseat HS HJ8 HP8 [0%nat; 1%nat] AG ltac:(first [kept_malloc HK8 HJ8 AG Usp | kept_ctx_m HK8 HJ8 Hctx8 Hctx7 Rctx AG Hres8]).
prreg HS (10%bv : bv 5) Rld. rewrite Ha08 in Rld. symmetry in Rld.
destruct Hrr8 as [Hld0 | (Hld4096 & Hldh & Hldceil & Hld16 & Hld8)].
{
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha08, Hld0; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS. reshok HS. subst ld.
paj_run_to_tok RUNTO HS HJ8 SHOK Bspan 0x2138; [obl_ctx HJ8 Hctx8 AG Rctx E32 .. | awr2 Actx Hctx8 AG Rctx Usp |].
clear HF HFr HG.
to_clean HS HJ8 HB8 TOK8 AG EE Usp Rctx E32 0 ti lm lc li tm 1%nat 0%nat. }
pose proof (req_size_pos' (2 * (lzw_MR nP idl + nP + 2)) ltac:(lia)) as Hrq8.
lazymatch type of Rld with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (PTR 4) HS
ltac:(clear HS; idtac; unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite Rld, unsigned_lit_small by lia;
change (2 ^ 4) with 16; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
paj_run_to_tok RUNTO HS HJ8 SHOK Bspan PC_INIT; [obl_ctx HJ8 Hctx8 AG Rctx E32 .. | awr2 Actx Hctx8 AG Rctx Usp |].
clear HF HFr HG.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
prreg HS (10%bv : bv 5) R10. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
prreg HS (22%bv : bv 5) R22. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27. prreg HS (1%bv : bv 5) R1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) sp regs) by (frame_tac HS 1%nat AG EE) | st_ok _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) sp regs) by (frame_tac HS 1%nat AG EE)  end.
assert (Htabs : tnz [(ld, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]
= lzw_tabs ti lm lc li tm ld nP idl).
{ unfold lzw_tabs. rewrite !tnz_cons_nz by lia. reflexivity. }
rewrite Htabs in HB8, TOK8.
pmkst HS.
apply SRr_ret. right.
lazymatch goal with |- tpro_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?rg _ ?m _) ?mdx) =>
exists ly8, S8, rg, m, mdx, ctx, ti, lm, lc, li, tm, ld end.
cbv beta zeta.
split; [reflexivity|]. split; [exact HJ8|].
split; [fold sp; unfold spZ; rewrite R2, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia|].
split; [rewrite R3, ?(AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl)|].
split; [rewrite R4, ?(AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl)|].
split; [rewrite R8; exact Rctx|].
split; [rewrite R22, Rctx, ?(AG 32%nat) by lia; rewrite E32; reflexivity|].
split; [rewrite R20, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R19, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R18, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R9, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R27, ?(AG 32%nat) by lia; exact E32|].
split; [exact R21|].
split; [rewrite R25, ?(AG 13%nat) by lia; exact E13|].
split; [rewrite R26, Rctx, ?(AG 32%nat) by lia; rewrite E32, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R1, Rctx, unsigned_lit_small by lia; reflexivity|].
split; [rewrite R10; exact Rld|].
split; [exact HFR|].
do 13 (split; [slot_tac HS 1%nat Usp AG Rctx|]).
do 8 (split; [ctx_field HS 0%nat Rctx AG|]).
split; [exact HB8|]. split; [exact TOK8|].
rewrite Hfrs8, Hfrs7. exact Hfrs6.
Qed.
End s.
End q.
End p.
