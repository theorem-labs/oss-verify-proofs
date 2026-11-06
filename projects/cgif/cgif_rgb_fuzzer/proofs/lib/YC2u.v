(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC0x YC3g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition PC_INIT : Z := 0x8952c.
Definition A_wrap_malloc : Z := 0x53104.
Definition A_asan_memset : Z := 0x5224c.
Definition lzw_MR (nP idl : Z) : Z := nP / (4094 - idl).
Definition lzw_tabs (ti lm lc li tm ld nP idl : Z) : list (Z * Z) :=
[(ld, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)].
Lemma st_ok_region_nth : forall E ss ms i r,
st_ok trasegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok trasegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok trasegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma slot_of_region : forall E m spe cs lo hi wlo whi od e v,
region_ok trasegs E m (YQ0b.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spe -> In (YQ0b.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem trasegs m (spe + od) 8 v.
Proof.
intros E m spe cs lo hi wlo whi od e v (_ & _ & _ & Hcs) H2 Hc He Hv.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YQ0b.r_base base_val] in Hck. rewrite H2 in Hck.
change 8%nat with (N.to_nat 8). exact (val_of_chunk_ok trasegs E m spe od 8%N e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok trasegs E m (YQ0b.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YQ0b.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem trasegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YQ0b.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok trasegs E m b od w e v Hck He Hv Hw).
Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Lemma awr_ok_cons_gen : forall E r rs STK sp0 FP bl0 blc ly own n b,
YQ0b.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YQ0b.r_wlo r <= a < b + YQ0b.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. apply Hw. exact Ha.
- apply H. exists r'. auto.
Qed.
Lemma aview_kept_frame : forall E rs H (m m' : word -> option byte) lo,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= lo ->
(forall a, lo <= a < 2 ^ 64 -> ~ in_wrange E rs a) ->
forall a, lo <= a < 2 ^ 64 -> aview trasegs H m' a = aview trasegs H m a.
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
(res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ acall_kept trasegs B lyc Sc W memT W2 mem2 slo shi (fun _ => False))
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept trasegs B lyc Sc W memT W2 mem2 slo shi (fun a => res <= a < res + req_size n)) ->
acall_kept trasegs B lyc Sc W memT W2 mem2 slo shi (fun a => res <> 0 /\ res <= a < res + req_size n) /\
(forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) /\
(res <> 0 -> In (res, n) (ablocks B ly2 S2)).
Proof.
intros lyc Sc W memT W2 mem2 ly2 S2 slo shi res n [(Hz & Ebl & HK) | (Hnz & Ebl & HK)].
- split; [eapply acall_kept_mono_E; [exact HK | intros a []]|]. split; [intros b Hb; rewrite Ebl; exact Hb | intros H; lia].
- split; [eapply acall_kept_mono_E; [exact HK | intros a Ha; split; [lia | exact Ha]]|].
split; [intros b Hb; rewrite Ebl; apply in_app_iff; left; exact Hb | intros _; rewrite Ebl; apply in_app_iff; right; left; reflexivity].
Qed.
Lemma mres_range : forall ly2 S2 W2 mem2 md2 lyc Sc (res n : Z) (P Q : Prop),
AR trasegs B ly2 S2 W2 mem2 md2 ->
(res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ P) \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\ Q) ->
res = 0 \/ (4096 <= res /\ ((res + req_size n <= 65536 \/ 6287360 <= res) /\ (res + req_size n <= 2147446784 \/ 17594333495296 <= res))
/\ res + req_size n <= alloc_ceiling /\ res mod 16 = 0 /\ In (res, n) (ablocks B ly2 S2)).
Proof.
intros ly2 S2 W2 mem2 md2 lyc Sc res n P Q HAR [(-> & _ & _) | (Hr & Ebl & _)]; [left; reflexivity | right].
assert (Hin : In (res, n) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res n HAR Hin) as (H16 & _ & Hc & [Hh Happ] & _).
pose proof (blk_off_img _ _ _ _ _ _ res n HAR Hin) as Hh_img.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Hh_img; lia|]. split; [exact Hc|]. split; [exact H16 | exact Hin].
Qed.
Lemma region_kept_block_ajw : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi cs b m ly2 S2 md2,
acall_kept trasegs B lyc Sc W memc W2 mem2 slo shi Er -> AR trasegs B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> 0 <= lo -> hi <= req_size m ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept trasegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi lo hi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi cs b m ly2 S2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi HnE.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trasegs). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable trasegs). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.
Lemma writable_kept : forall H (m m2 : word -> option byte) a,
(apresent H m a -> apresent H m2 a) -> writable_at trasegs (mrestrict H m) a -> writable_at trasegs (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma region_kept_aview : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview trasegs H m2 a = aview trasegs H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
region_kept trasegs E (mrestrict H m) (mrestrict H m2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trasegs). apply Hav. exact Ha.
- apply writable_kept. apply Hp.
Qed.
Lemma val_mem_zero8 : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 8 -> aview trasegs H m (a + i) = Some 0) -> val_mem trasegs (mrestrict H m) a 8 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte trasegs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YP0g.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by (vm_compute; discriminate)). lia.
Qed.
End d.
End c.
Ltac getB := lazymatch goal with L : AR_laws trasegs ?Bv |- _ => Bv end.
Ltac getLAWS := lazymatch goal with L : AR_laws trasegs _ |- _ => L end.
Ltac getTL := lazymatch goal with T : TraLib _ |- _ => T end.
Ltac getML := lazymatch goal with M : model_laws _ |- _ => M end.
Ltac getAM := lazymatch goal with A : amalloc_realizes _ _ |- _ => A end.
Ltac getAF := lazymatch goal with A : afree_realizes _ _ |- _ => A end.
Ltac getCODE := lazymatch goal with H : as_code _ = Tra_code |- _ => H end.
Ltac getENV := lazymatch goal with H : api_env _ _ |- _ => H end.
Ltac reseat HS HJ2 HP2 keep AG kept_tac :=
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 (SOff 32 0) [] ss) end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
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
clear HEv AG; rename AG2 into AG end end.
Ltac kept_malloc HK HJ2 AG Usp :=
eapply (region_kept_stack_aj trasegs _);
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
pose proof (sep_blocks_pos trasegs _ L ly2 S2 _ _ _ (_, 72) nb l1 l2 [] (proj1 HJ2)
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
pose proof (sep_blocks_pos trasegs _ L ly2 S2 _ _ _ (_, 72) nb l1 l2 [] (proj1 HJ2)
ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd end;
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd; change (req_size 72) with 72 in Hd; lia ].
Ltac kept_intrin Hfr Hpres2 AG Usp :=
eapply region_kept_aview; [cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | intros a Ha; apply Hfr; unfold ESTACK; lia | exact Hpres2].
Ltac reshok_bx HS bx :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto SH (SOff bx 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) end.
Ltac reshok HS := reshok_bx HS 32%nat.
Ltac norm_ss HS := lazymatch type of HS with st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac eatom AG Efact := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?AG by lia; exact Efact.
Ltac rregU HS r v Utac H :=
lazymatch type of HS with
| st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = Z_to_bv 64 v)
by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _);
change (sv_denot Ex e = Z_to_bv 64 v); rewrite denot_lit_U; f_equal; Utac)
end.
