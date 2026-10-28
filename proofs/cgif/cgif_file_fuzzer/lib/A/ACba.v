(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8j ACbc ACbf.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC7k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition xfacts (P : Prop) : Prop := P.
Lemma xfacts_i : forall P : Prop, P -> xfacts P. Proof. intros P H. exact H. Qed.
Section d. Context {rc : YM05.RunCeil}.
Lemma asink_fp_off_shadow : forall pf x, in_app pf 1264 -> inFP (asink_fp pf) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x.
Proof.
intros pf x Hia Hx. apply in_asink_fp in Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, ASAN_CEIL in Hia. rewrite C2. rewrite C3 in Hia. unfold kLowShadowBeg, FILE_BLOCK in *. lia.
Qed.
End d.
Lemma block_shadow_cells2 : forall (rd : Z -> option Z) SO p n,
p mod 8 = 0 -> 8 < n <= 16 ->
rd (shadow_of_addr SO p) = Some 0 -> rd (shadow_of_addr SO p + 1) = Some (if n =? 16 then 0 else n - 8) ->
block_shadow rd SO p n.
Proof.
intros rd SO p n Hp Hn H0 H1. split; [exact Hp|]. split; [lia|]. intros i Hi.
assert (Hq : (n + 7) / 8 = 2) by (destruct (Z.eq_dec n 16) as [->|]; [reflexivity|]; symmetry; apply Z.div_unique with (r := n + 7 - 16); lia).
rewrite Hq in Hi.
destruct (Z.eq_dec i 0) as [->|].
- rewrite Z.add_0_r. rewrite H0. f_equal. assert (Hd : 1 <= n / 8) by (apply Z.div_le_lower_bound; lia). destruct (Z.ltb_spec 0 (n / 8)); [reflexivity | lia].
- assert (i = 1) as -> by lia. rewrite H1. f_equal.
destruct (Z.eqb_spec n 16) as [->|Hne]; [reflexivity|].
assert (Hd : n / 8 = 1) by (symmetry; apply Z.div_unique with (r := n - 8); lia).
rewrite Hd. cbn. rewrite (Z.mod_eq n 8) by lia. rewrite Hd. lia.
Qed.
Lemma block_shadow_cells1 : forall (rd : Z -> option Z) SO p n,
p mod 8 = 0 -> 0 < n <= 8 ->
rd (shadow_of_addr SO p) = Some (if n =? 8 then 0 else n) ->
block_shadow rd SO p n.
Proof.
intros rd SO p n Hp Hn H0. split; [exact Hp|]. split; [lia|]. intros i Hi.
assert (Hq : (n + 7) / 8 = 1) by (symmetry; apply Z.div_unique with (r := n + 7 - 8); lia). rewrite Hq in Hi.
assert (i = 0) as -> by lia. rewrite Z.add_0_r, H0. f_equal.
destruct (Z.eqb_spec n 8) as [->|Hne]; [reflexivity|].
assert (Hd : n / 8 = 0) by (apply Z.div_small; lia). rewrite Hd. cbn. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma block_shadow_cells3 : forall (rd : Z -> option Z) SO p n,
p mod 8 = 0 -> 16 < n <= 24 ->
rd (shadow_of_addr SO p) = Some 0 -> rd (shadow_of_addr SO p + 1) = Some 0 -> rd (shadow_of_addr SO p + 2) = Some (if n =? 24 then 0 else n - 16) ->
block_shadow rd SO p n.
Proof.
intros rd SO p n Hp Hn H0 H1 H2. split; [exact Hp|]. split; [lia|]. intros i Hi.
assert (Hq : (n + 7) / 8 = 3) by (destruct (Z.eq_dec n 24) as [->|]; [reflexivity|]; symmetry; apply Z.div_unique with (r := n + 7 - 24); lia).
rewrite Hq in Hi. assert (H2d : 2 <= n / 8) by (apply Z.div_le_lower_bound; lia).
destruct (Z.eq_dec i 0) as [->|]; [rewrite Z.add_0_r, H0; f_equal; destruct (Z.ltb_spec 0 (n / 8)); [reflexivity | lia]|].
destruct (Z.eq_dec i 1) as [->|]; [rewrite H1; f_equal; destruct (Z.ltb_spec 1 (n / 8)); [reflexivity | lia]|].
assert (i = 2) as -> by lia. rewrite H2. f_equal.
destruct (Z.eqb_spec n 24) as [->|Hne]; [reflexivity|].
assert (Hd : n / 8 = 2) by (symmetry; apply Z.div_unique with (r := n - 16); lia).
rewrite Hd. cbn. rewrite (Z.mod_eq n 8) by lia. rewrite Hd. lia.
Qed.
Ltac evalE_in AG Hrr :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr; rewrite ?ew_ewset_other in Hrr by lia;
repeat match type of Hrr with context [ew ?Ex ?n] => match goal with H : ew Ex n = Z_to_bv 64 _ |- _ => rewrite H in Hrr end end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match type of Hrr with context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) in Hrr by lia end end end;
repeat match type of Hrr with context [ew ?Ex ?n] => match goal with H : ew Ex n = Z_to_bv 64 _ |- _ => rewrite H in Hrr end end;
repeat match type of Hrr with context [bv_unsigned (ew ?Ex 2)] => match goal with H : bv_unsigned (ew Ex 2) = _ |- _ => rewrite H in Hrr end end;
rewrite ?unsigned_lit_small in Hrr by (unfold SB; lia); unfold SB in Hrr.
Ltac xwinF Hrr Hpf :=
lazymatch type of Hrr with
| context [_ / 8] =>
lazymatch goal with Hia : xfacts (in_app ?pfv 1264) |- _ =>
lazymatch type of Hrr with _ <= ?a < _ + ?Fv / 8 + ?k =>
lazymatch goal with XF : xfacts (_ /\ _) |- _ =>
refine (fshadow_not_app Fv 32 pfv 1264 a _ _ Hia _ _);
[ clear - XF; unfold xfacts in XF; lia | clear - XF; unfold xfacts in XF; lia
| clear - Hrr; unfold SB in *; lia | clear - Hpf; lia ] end end end
| _ => first
[ lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Hrr Hpf; unfold xfacts in XF; lia end
|
lazymatch goal with Hno : forall x, _ <= x < _ + 1264 -> ~ aowned _ _ _ x |- _ =>
lazymatch goal with Hown : aowned _ _ _ ?fl |- _ =>
let av := lazymatch type of Hpf with _ <= ?a < _ => a end in
apply (Hno _ Hpf); replace fl with av in Hown by (clear - Hrr; lia); exact Hown end end ]
end.
Ltac xwinI Hrr Himg :=
first [ let Hr := fresh "Hr" in pose proof (pa_img_range _ Himg) as Hr;
lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Hrr Hr; unfold xfacts in XF; unfold SB in *; lia end
|
lazymatch goal with Hni : ~ in_img _ ?fl |- _ =>
let av := lazymatch type of Himg with in_img _ ?a => a end in
apply Hni; replace fl with av by (clear - Hrr; lia); exact Himg end ].
Ltac xwin_one AG Hrr :=
first [ exfalso; clear - Hrr; lia
| evalE_in AG Hrr; split; [ let Hpf := fresh "Hpf" in intros Hpf; xwinF Hrr Hpf | let Himg := fresh "Himg" in intros Himg; xwinI Hrr Himg ] ].
Ltac xwin_loop AG Hin Hrr :=
lazymatch type of Hin with
| False => destruct Hin
| _ \/ _ => let Hq := fresh "Hq" in let Hin2 := fresh "Hin" in
destruct Hin as [Hq | Hin2]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; xwin_one AG Hrr | xwin_loop AG Hin2 Hrr]
end.
Ltac xsink_stretch HFr HSINK :=
let made := match goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => constr:(false) | _ => constr:(true) end in
lazymatch type of HFr with frame_of ?Ef _ _ _ =>
lazymatch made with true => let AG0 := fresh "AG0" in assert (AG0 : forall n, (n < 33)%nat -> ew Ef n = ew Ef n) by (intros; reflexivity) | false => idtac end end;
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let AIL := lazymatch goal with H : asink_img_laws _ _ _ |- _ => H end in
lazymatch goal with |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
lazymatch type of HSINK with asink_at ?sg ?Kv (mrestrict (w_H ?Wv) ?mo) ?mdo ?pf ?SG =>
let UN := fresh "UN" in let H2 := fresh "HSINK" in
pose proof (kept_of_frame (segs:=sg) _ _ _ _ _ (fun a => ~ (pf <= a < pf + 1264) /\ ~ in_img sg a) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
intros b wlo whi a Hin Hrr; vm_compute in Hin; xwin_loop AG Hin Hrr)) as UN;
cbn beta in UN;
assert (H2 : asink_at sg Kv (mrestrict (w_H Wv) (ms_mem msn)) mdn pf SG);
[ apply (asink_at_model sg Kv _ mdo); [reflexivity | reflexivity |];
apply (asink_at_frame sg Kv (mrestrict (w_H Wv) mo)); [|exact HSINK];
let a := fresh "a" in let Ha := fresh "Ha" in let Hn1 := fresh "Hn" in let Hn2 := fresh "Hn" in
intros a Ha; apply (mbyte_of_aview sg); cbn [ms_mem]; apply UN;
[ destruct Ha as [Ha | Ha];
[ lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Ha; unfold xfacts in XF; unfold FILE_BLOCK in Ha; lia end
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))); lia ]
| intros [Hn1 Hn2]; destruct Ha as [Ha | Ha];
[ apply Hn1; unfold FILE_BLOCK in Ha; exact Ha | exact (Hn2 (proj1 (ail_env _ _ _ AIL a Ha))) ] ]
| clear UN HSINK; rename H2 into HSINK; lazymatch made with true => clear AG | false => idtac end ] end end.
Ltac xsink_sub HJt HSINK Hin Hin2 :=
let AIL := lazymatch goal with H : asink_img_laws _ _ _ |- _ => H end in
lazymatch type of HJt with ajournal ?sg ?Bv _ _ ?FP _ _ _ _ _ _ _ _ ?W2 ?mem2 ?md2 _ =>
lazymatch type of HSINK with asink_at _ ?Kv _ _ ?pf ?SG =>
let H2 := fresh "HSINK" in
assert (H2 : asink_at sg Kv (mrestrict (w_H W2) mem2) md2 pf SG);
[ eapply (asink_at_kept sg Bv Kv AIL); [exact HJt | | exact Hin | exact Hin2 | | exact HSINK];
[ first [exact sink_closed_nil | apply sink_closed_ablocks_fp; repeat (constructor; [cbn; lia|]); constructor]
| let i := fresh "i" in let Hi := fresh "Hi" in let HF := fresh "HF" in
intros i Hi HF; first [exact (inFP_nil _ HF)
| let p' := fresh "p'" in let n' := fresh "n'" in let Hpn := fresh "Hpn" in let Hpa := fresh "Hpa" in
destruct (inFP_ablocks_fp_inv _ _ HF) as (p' & n' & Hpn & Hpa); cbn in Hpn;
repeat (destruct Hpn as [Hpn | Hpn]; [injection Hpn as <- <-; rqs Hpa;
lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Hi Hpa; unfold xfacts in XF; unfold FILE_BLOCK in Hi; lia end |]);
destruct Hpn ] ]
| clear HSINK; rename H2 into HSINK ] end end.
Ltac xsink_intrin Hfr HSM HSINK :=
let AIL := lazymatch goal with H : asink_img_laws _ _ _ |- _ => H end in
lazymatch type of Hfr with forall a, _ -> _ -> _ -> aview ?sg (w_H ?W2) ?mem2 a = aview _ _ ?memT a =>
lazymatch type of HSM with same_but_materialized ?mdc ?md2 =>
lazymatch type of HSINK with asink_at _ ?Kv _ _ ?pf ?SG =>
let H2 := fresh "HSINK" in let Q := fresh "Q" in
pose proof (same_but_materialized_frame mdc md2 HSM) as Q;
assert (H2 : asink_at sg Kv (mrestrict (w_H W2) mem2) md2 pf SG);
[ apply (asink_at_model sg Kv _ mdc); [unfold m_fs; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 Q))))); reflexivity | unfold m_fds; rewrite (proj1 Q); reflexivity |];
apply (asink_at_frame sg Kv (mrestrict (w_H W2) memT)); [|exact HSINK];
let a := fresh "a" in let Ha := fresh "Ha" in let Hr := fresh "Hr" in
intros a Ha; apply (mbyte_of_aview sg);
(destruct Ha as [Ha | Ha]; [unfold FILE_BLOCK in Ha | pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr]);
(apply Hfr; unfold ESTACK, ASTACK; lazymatch goal with XF : xfacts (_ /\ _) |- _ => first [clear - XF Ha; unfold xfacts in XF; lia | clear - XF Ha Hr; unfold xfacts in XF; lia] end)
| clear Q HSINK; rename H2 into HSINK ] end end end.
Ltac xsepF Haa HFP :=
let Hpf := fresh "Hpf" in
repeat match type of Haa with context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v in Haa end;
repeat match type of Haa with context [Z.of_N ?n] => let v := eval cbv in (Z.of_N n) in change (Z.of_N n) with v in Haa end;
unfold FILE_BLOCK in HFP; destruct HFP as [Hpf | Hpf];
[ xwinF Haa Hpf
| lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Haa Hpf; unfold xfacts in XF; unfold SB in *; lia end ].
Ltac xFP :=
cbv beta;
lazymatch goal with
| |- forall x, inFP _ x -> x < kLowShadowBeg \/ kHighShadowEnd <= x =>
lazymatch goal with Hia : xfacts (in_app ?pfv 1264) |- _ => exact (fun x Hx => asink_fp_off_shadow pfv x Hia Hx) end
| |- forall a, _ -> ~ inFP _ a =>
let aa := fresh "aa" in let Haa := fresh "Haa" in let HFP := fresh "HFP" in
intros aa Haa HFP; apply in_asink_fp in HFP; xsepF Haa HFP
| |- forall a, _ -> inFP _ a -> False =>
let aa := fresh "aa" in let Haa := fresh "Haa" in let HFP := fresh "HFP" in
intros aa Haa HFP; apply in_asink_fp in HFP; xsepF Haa HFP
| |- inFP _ ?a -> False =>
let HFP := fresh "HFP" in intros HFP; apply in_asink_fp in HFP;
lazymatch goal with Haa : _ <= a < _ |- _ => xsepF Haa HFP end
| |- ~ inFP _ ?a =>
let HFP := fresh "HFP" in intros HFP; apply in_asink_fp in HFP;
lazymatch goal with Haa : _ <= a < _ |- _ => xsepF Haa HFP end
end.
Ltac oblFX HJx HE10 HE35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 10 ?c)) ?len =>
lazymatch type of HE10 with _ = Z_to_bv 64 ?cfgp =>
first [ rewrite (U_atom_off Ex 10 cfgp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia | lia]
| rewrite (U_atom Ex 10 cfgp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia] ];
eapply (obl_of_range _ _ _ Ex (SOff 35 0) _ len cfgp 40);
[ let L := rnLAWS in eapply (range_addressable_entry_frame _ _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| xFP | exact HAR | exact HRA]
| rewrite (U_atom Ex 35 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | lia ] end end.
Ltac exitRX RET RUNF HS HJx AG fpos F cfgp g E528 E529 Hfin HfinS HingX EE Hra HEV EFA EFL :=
let HFLpres' := fresh "HFLpres'" in let HFLown := fresh "HFLown'" in let HFLrng := fresh "HFLrng'" in
let HFpres' := fresh "HFpres'" in let HFSpres' := fresh "HFSpres'" in
let HCpres' := fresh "HCpres'" in let HGpres' := fresh "HGpres'" in
let HnoG := fresh "HnoG" in let HnoC := fresh "HnoC" in let HnoF := fresh "HnoF" in
let HFLni := fresh "HFLni" in let HnoP := fresh "HnoP" in let HPp := fresh "HPp" in
let FFL := rnFFL in let LAWS := rnLAWS in destruct (FFL _ _ _ _ _ 2 fpos (proj1 HJx) Hfin) as (HFLpres' & HFLown & HFLrng); rewrite ?EFL in HFLpres'; rewrite ?EFL in HFLown; rewrite ?EFL in HFLrng; fold F in HFLrng;
pose proof (proj2 (proj1 HFLrng)) as HFLni;
try (lazymatch goal with FLv := flag_addr _ 2 _ |- _ => fold FLv in HFLown; fold FLv in HFLni end);
lazymatch type of HFLown with aowned ?Bv ?lyx ?Sx _ =>
lazymatch goal with Hinf : In (?pfv, FILE_BLOCK) (ablocks Bv lyx Sx) |- _ =>
destruct (al_blocks _ _ LAWS _ _ _ _ _ pfv FILE_BLOCK (proj1 HJx) Hinf) as (_ & _ & _ & _ & HPp & _); change (req_size FILE_BLOCK) with 1264 in HPp;
assert (HnoP : forall x, pfv <= x < pfv + 1264 -> ~ aowned Bv lyx Sx x) by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; exact (proj2 (HPp x Hx))); clear HPp end end;
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJx) Hfin) as (_ & _ & HFpres' & HFSpres'); change (fs_frame_bytes 2) with 256 in HFpres', HFSpres';
change (256 / 8) with 32 in HFSpres'; rewrite ?EFA in HFpres'; rewrite ?EFA in HFSpres'; fold F in HFpres', HFSpres';
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJx) HfinS) as (_ & _ & HCpres' & _); rewrite ?EFA in HCpres';
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE (proj1 HJx) HingX) as (_ & _ & _ & _ & HGpres' & _); change (req_size CGIF_SIZE) with 96 in HGpres';
lazymatch type of HGpres' with forall a, _ -> _ /\ ~ aowned ?B ?lyx ?Sx a =>
assert (HnoG : forall a, g <= a < g + 96 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HGpres' a Ha)));
assert (HnoC : forall a, cfgp <= a < cfgp + 40 -> ~ aowned B lyx Sx a) by (intros a Ha; apply (fun H => proj2 (HCpres' a H)); lia);
assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HFpres' a Ha)));
try (match goal with Hin : In (?r, 48) (ablocks _ lyx Sx) |- _ =>
let HRp := fresh "HRp" in let HnoR := fresh "HnoR" in
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 48 (proj1 HJx) Hin) as (_ & _ & _ & _ & HRp & _); change (req_size 48) with 48 in HRp;
assert (HnoR : forall a, r <= a < r + 48 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HRp a Ha))); clear HRp end) end;
fs_rw HS E529 HFSpres';
add_flag_region HS AG E528 HFLpres' HFLrng HFLown HnoG HnoC HnoF;
paj_run_flag_sh RUNF HS HJx; [lia | wrangeR AG fpos F EFA EFL | flag0 E528 EFL |];
(let HFr := lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in xsink_stretch HFr HSINK);
let R1 := fresh "R1" in let R10 := fresh "R10" in
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; unfold rn_postX, rn_post, apost_base;
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k _ _); [apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx | rewrite HEV; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac rn_preludeX :=
let LAWS := rnLAWS in let B := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end in
intros RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 E W3 ly3 S3 ms3 md3 k fpos res Sg GCT
HPRE Hchne Hal32 HROD HCFG Hcfg HPerm Hev HE0 HE HNOW Hsg HSmax HGCT HS;
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TRAWNEW_STK = 16576) by reflexivity;
assert (HEV : EV_RAWNEW = 4) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
destruct HCFG as (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA);
destruct HE0 as (EE & E10 & E32 & Usp); destruct HE as ((AG & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & RF & E528 & E529 & Rres & E41 & E42 & E43 & HEI) & E44 & E45);
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hres4096 & Tres & Ares & HSINK & MLE);
pose proof (proj1 HJ3) as HAR3;
destruct (frames_bounds _ _ LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity);
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _); pose proof (proj1 Hgh_ia) as Hgh;
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img;
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh;
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (2, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfin);
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFapp_img;
destruct (frames_bounds _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
change (fs_frame_bytes 2) with 256 in *; change (256 / 8) with 32 in HFSpres3; rewrite !EFA3 in *;
set (F := frame_addr ly 2 fpos) in *; set (FL := flag_addr ly 2 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    ;
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (Hres_in : In (res, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Eab3|]; apply in_app_iff; right; left; reflexivity);
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Eab3|]; apply in_app_iff; left; exact Hing);
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 HAR3 Hres_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & Hrpres3 & _); pose proof (proj1 Hrh_ia) as Hrh;
pose proof (blk_off_imgP _ _ _ _ _ _ res 48 HAR3 Hres_in) as Hrh_img;
change (req_size 48) with 48 in Hrceil, Hrpres3;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ res 48 2 fpos HAR3 Hres_in Hfin3) as HdRF;
unfold zdisjoint in HdRF; cbn [fst snd] in HdRF; change (req_size 48) with 48 in HdRF; change (fs_frame_bytes 2) with 256 in HdRF; rewrite EFA3 in HdRF; fold F in HdRF;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ res 48 cid pos HAR3 Hres_in HfinS3) as HdRC;
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size 48) with 48 in HdRC; rewrite EFA3 in HdRC;
pose proof (sep_blocks _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE res 48 HAR3 Hing3 Hres_in ltac:(unfold CGIF_SIZE; intros X; injection X; lia)) as HdRG;
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size 48) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE 2 fpos HAR3 Hing3 Hfin3) as HdFG;
unfold zdisjoint in HdFG; cbn [fst snd] in HdFG; change (req_size CGIF_SIZE) with 96 in HdFG; change (fs_frame_bytes 2) with 256 in HdFG; rewrite EFA3 in HdFG; fold F in HdFG;
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos _ _ LAWS ly3 S3 _ _ _ (2, fpos) (cid, pos) [] fl1 fl2 HAR3 ltac:(rewrite Hfrs3, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC; change (fs_frame_bytes 2) with 256 in HdFC; rewrite !EFA3 in HdFC; fold F in HdFC;
let Kgot3 := fresh "Kgot3" in let Kcell3 := fresh "Kcell3" in let Kguar3 := fresh "Kguar3" in let Kuar3 := fresh "Kuar3" in let Vgr3 := fresh "Vgr3" in
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
let Hinf := fresh "Hinf" in let Hinf3 := fresh "Hinf3" in let Hp16 := fresh "Hp16" in let Hp4096 := fresh "Hp4096" in let Hpceil := fresh "Hpceil" in
let Hp_ia := fresh "Hp_ia" in let Hph := fresh "Hph_img" in let HdPC := fresh "HdPC" in let HdPF := fresh "HdPF" in let HdPR := fresh "HdPR" in
let XF := fresh "XF" in
assert (Hinf : In (pf, FILE_BLOCK) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity);
assert (Hinf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Eab3|]; apply in_app_iff; left; exact Hinf);
destruct (al_blocks _ _ LAWS ly S W mem md pf FILE_BLOCK HAR Hinf) as (Hp16 & Hp4096 & Hpceil & Hp_ia & _ & _);
pose proof (blk_off_imgP _ _ _ _ _ _ pf FILE_BLOCK HAR Hinf) as Hph; change (req_size FILE_BLOCK) with 1264 in Hpceil, Hph, Hp_ia; unfold off_img in Hph;
pose proof (sep_block_frame _ _ LAWS ly S W mem md pf FILE_BLOCK cid pos HAR Hinf Hfin) as HdPC;
unfold zdisjoint in HdPC; cbn [fst snd] in HdPC; change (req_size FILE_BLOCK) with 1264 in HdPC;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ pf FILE_BLOCK 2 fpos HAR3 Hinf3 Hfin3) as HdPF;
unfold zdisjoint in HdPF; cbn [fst snd] in HdPF; change (req_size FILE_BLOCK) with 1264 in HdPF; change (fs_frame_bytes 2) with 256 in HdPF; rewrite EFA3 in HdPF; fold F in HdPF;
pose proof (sep_blocks _ _ LAWS ly3 S3 _ _ _ pf FILE_BLOCK res 48 HAR3 Hinf3 Hres_in ltac:(unfold FILE_BLOCK; intros X; injection X; lia)) as HdPR;
unfold zdisjoint in HdPR; cbn [fst snd] in HdPR; change (req_size 48) with 48 in HdPR; change (req_size FILE_BLOCK) with 1264 in HdPR;
let HdPG := fresh "HdPG" in
pose proof (sep_blocks _ _ LAWS ly S _ _ _ pf FILE_BLOCK g CGIF_SIZE HAR Hinf Hing ltac:(unfold FILE_BLOCK, CGIF_SIZE; intros X; injection X; lia)) as HdPG;
unfold zdisjoint in HdPG; cbn [fst snd] in HdPG; change (req_size CGIF_SIZE) with 96 in HdPG; change (req_size FILE_BLOCK) with 1264 in HdPG;
assert (XF : xfacts (pf + 1264 <= alloc_ceiling /\ 4096 <= pf /\ alloc_ceiling + TRAWNEW_STK <= spZ regs /\ TRAWNEW_STK = 16576 /\
140735332483072 <= alloc_ceiling <= 140737479966720 /\ (pf + 1264 <= 65536 \/ 6270976 <= pf) /\
(pf + 1264 <= cfgp \/ cfgp + 40 <= pf) /\ 4096 <= cfgp /\
(pf + 1264 <= F \/ F + 256 <= pf) /\ 4096 <= F /\ F + 256 <= alloc_ceiling /\ (F + 256 <= 65536 \/ 6270976 <= F) /\ 512 <= F / 8 < 17592186044416 /\
(pf + 1264 <= res \/ res + 48 <= pf) /\ 4096 <= res /\ res + 48 <= alloc_ceiling /\ (res + 48 <= 65536 \/ 6270976 <= res) /\
(pf + 1264 <= g \/ g + 96 <= pf) /\ 4096 <= g /\ g + 96 <= alloc_ceiling))
by (apply xfacts_i; unfold off_img in HFhigh_img, Hrh_img; change (req_size 48) with 48 in Hrh_img; change (fs_frame_bytes 2) with 256 in HFhigh_img; clear - Hpceil Hp4096 Hceil Hslo FFS C1 Hph HdPC Hflo Hfhi Hf4096 HdPF HF4096 HFceil HFhigh_img HF8lo HF8hi HdPR Hr4096 Hrceil Hrh_img HdPG Hg4096 Hgceil; lia);
clear Hph HdPC HdPF HdPR HdPG; change (in_app pf 1264) with (xfacts (in_app pf 1264)) in Hp_ia;
img_facts E; img_hull_facts.
Ltac xidx_516_122 rs :=
lazymatch rs with
| YP09.mkRegion (Some 516%nat) 122 _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?rs' => let i := xidx_516_122 rs' in constr:(S i)
end.
Ltac xrechunk_pk HS valtac :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let E45 := lazymatch goal with H : ew _ 45 = Z_to_bv 64 (rn_pk _) |- _ => H end in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
lazymatch type of E45 with _ = Z_to_bv 64 (rn_pk ?sg) =>
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i := xidx_516_122 rsm in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
let HR := fresh "HRq" in let V := fresh "Vq" in let HV := fresh "HVq" in let HRO := fresh "HROq" in let HS3 := fresh "HS3" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i r HS ltac:(vm_compute; reflexivity)) as HR; cbn [ms_mem restrict] in HR;
lazymatch type of HR with region_ok _ _ ?m (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk 122 (CVal 1 ?e)] =>
pose proof (field_of_region_any Ev m 516 Fv cs lo hi wlo whi 122 1%N e HR ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
assert (HV : bv_unsigned (sv_denot Ev e) mod 2 ^ (8 * Z.of_N 1) = rn_pk sg) by valtac;
rewrite HV in V;
unfold region_ok in HR; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR; evalE_in AG HR;
assert (HRO : region_ok pa_segs Ev m (YP09.mkRegion (Some 516%nat) 122 125 122 125
[YP09.mkChunk 122 (CVal 1 (SOff 45 0)); YP09.mkChunk 123 (CVal 1 (SLit 0)); YP09.mkChunk 124 (CVal 1 (SLit 0))]));
[ let Q1 := fresh "Q" in let Q2 := fresh "Q" in let Q3 := fresh "Q" in let Qc := fresh "Qc" in
pose proof HR as (Q1 & Q2 & Q3 & Qc);
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; evalE AG;
split; [exact Q1|]; split; [exact Q2|]; split; [exact Q3|];
apply Forall_cons;
[ apply (chunk_ok_val pa_segs Ev m Fv 122 1 (SOff 45 0) (rn_pk sg));
[ cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (rn_pk_range sg ltac:(lia)); cbn [Z.of_N Z.mul]; lia | cbn; lia | exact V ]
| apply Forall_cons; [exact (proj1 (Forall_forall _ _) Qc (YP09.mkChunk 123 (CVal 1 (SLit 0))) ltac:(cbn; tauto)) |];
apply Forall_cons; [exact (proj1 (Forall_forall _ _) Qc (YP09.mkChunk 124 (CVal 1 (SLit 0))) ltac:(cbn; tauto)) | apply Forall_nil] ]
| pose proof (ast_ok_pi_set_region Ev ssx (restrict Hw msx) i r
(YP09.mkRegion (Some 516%nat) 122 125 122 125 [YP09.mkChunk 122 (CVal 1 (SOff 45 0)); YP09.mkChunk 123 (CVal 1 (SLit 0)); YP09.mkChunk 124 (CVal 1 (SLit 0))])
HS ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity) HRO) as HS3;
clear HS HR V HV HRO; rename HS3 into HS; norm_ss HS ] end end end end end.
Lemma denot_rn_flags : forall E ka K, ew E ka = Z_to_bv 64 K -> 0 <= K <= 8 ->
bv_unsigned (sv_denot E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_AND (SOff ka 0) (SLit 255)) (SAlu ALU_ADD (SAlu ALU_AND (SOff ka 0) (SLit 255)) (SLit (-1)))) (SLit (-1)))
(SAlu ALU_ADD (SAlu ALU_AND (SOff ka 0) (SLit 255)) (SLit (-1)))) (SLit 128))) mod 2 ^ (8 * Z.of_N 1)
= 128 + (Z.max K 1 - 1).
Proof.
intros E ka K HK Hr. cbn [sv_denot]. rewrite HK.
destruct (rn_pow_cases K Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma rn_pk_of_K : forall K sgct, 0 <= K <= 8 -> 0 < sgct -> sgct <= 2 ^ K -> 2 ^ K < 2 * sgct -> rn_pk sgct = 128 + (Z.max K 1 - 1).
Proof.
intros K sgct HK Hs H1 H2. unfold rn_pk. destruct (Z.eqb_spec sgct 0); [lia|].
rewrite (YI0j.pal_pow_class K sgct ltac:(lia)); [lia | intros ->; exact H1 | | exact H1].
intros HKp. assert (E : 2 ^ K = 2 * 2 ^ (K - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). lia.
Qed.
Ltac wcb_siteX rs HS HWX HGA HRA HHV HJ3 HAR3 Hfin3 HfinS3 Hing3 Hres_in Eab3 Hfrs3 EFA3 EFL3 HFpres3 HFSpres3 Hrpres3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let EE := lazymatch goal with H : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew _ n = getr _ r |- _ => H end in
let Usp := lazymatch goal with H : bv_unsigned (ew _ 2) = spZ _ |- _ => H end in
let E0v := lazymatch type of EE with forall n r, _ -> ew ?E0v n = _ => E0v end in
let E32 := lazymatch goal with H : ew E0v 32 = Z_to_bv 64 _ |- _ => H end in
let E41 := lazymatch goal with H : ew _ 41 = Z_to_bv 64 _ |- _ => H end in
let E42 := lazymatch goal with H : ew _ 42 = Z_to_bv 64 _ |- _ => H end in
let Hch := lazymatch goal with H : achain _ _ _ _ _ |- _ => H end in
let Hchne := lazymatch goal with H : _ <> @nil (Z * Z * Z) |- _ => H | H : ?c <> [] |- _ => H end in
let Hal32 := lazymatch goal with H : spZ _ mod 32 = 0 |- _ => H end in
let Hra4 := lazymatch goal with H : 4096 <= raZ _ |- _ => H end in
let Hgp := lazymatch goal with H : getr _ 3 = w64 (as_gp _) |- _ => H end in
let Htp := lazymatch goal with H : getr _ 4 = w64 (as_tp _) |- _ => H end in
let FFS := lazymatch goal with H : TRAWNEW_STK = _ |- _ => H end in
let HROD := lazymatch goal with H : arodata_okP _ _ _ _ _ |- _ => H end in
let WFN := lazymatch goal with H : twcbF_spec _ _ _ _ |- _ => H end in
let Rwfn := lazymatch type of WFN with twcbF_spec _ _ _ ?wf => lazymatch goal with H : 0 <= wf < 2 ^ 64 /\ wf mod 2 = 0 |- _ => H end end in
let E44 := lazymatch goal with H : ew _ 44 = Z_to_bv 64 _ |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ /\ _) |- _ => H end in
let LAWS := rnLAWS in let Bv := rnB in
lazymatch type of HJ3 with ajournal _ _ ?STK (spZ ?regs) _ ?ly ?S ?W ?mem ?md [(2, ?fpos)] ?ly3 ?S3 ?W3 _ _ ?k =>
lazymatch type of HfinS3 with In (?cid, ?pos) _ =>
lazymatch type of Hing3 with In (?g, CGIF_SIZE) _ =>
lazymatch type of Hres_in with In (?res, 48) _ =>
lazymatch type of Hch with achain _ _ _ _ ?ch =>
lazymatch type of WFN with twcbF_spec _ ?Kv _ ?wfn =>
lazymatch type of E42 with _ = Z_to_bv 64 ?hw =>
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
lazymatch type of HWX with ?n = Z.of_nat (length ?bs) /\ _ /\ _ /\ (?p + _ <= _ \/ _) /\ _ =>
let Hinf3 := lazymatch goal with H : In (pf, FILE_BLOCK) (ablocks _ ly3 S3) |- _ => H end in
lazymatch type of HFpres3 with forall a, ?F <= a < _ -> _ =>
let Hfin := lazymatch goal with H : In (cid, pos) (frames S) |- _ => H end in
let P2 := fresh "P2" in let Prs := fresh "Prs" in let P8 := fresh "P8" in let P10 := fresh "P10" in
let P1 := fresh "P1" in let P3 := fresh "P3" in let P4 := fresh "P4" in let P11 := fresh "P11" in let P12 := fresh "P12" in
let Qtop := fresh "Qtop" in let Qtop64 := fresh "Qtop64" in let Qceil := fresh "Qceil" in let Qal8 := fresh "Qal8" in
let Qra := fresh "Qra" in let Qs0 := fresh "Qs0" in let Vra := fresh "Vra" in let Vs0 := fresh "Vs0" in let HRr := fresh "HRr" in
let Hch1 := fresh "Hch1" in let Vhw := fresh "Vhw" in let Vctx := fresh "Vctx" in let Vpf := fresh "Vpf" in
let mat1 := fresh "mat" in let ms1 := fresh "msj" in let Ems1 := fresh "Emsj" in let HS1 := fresh "HSj" in let HS2 := fresh "HS2" in
let W4 := fresh "W" in let c4 := fresh "c" in let Hwle4 := fresh "Hwle" in let ly4 := fresh "ly" in let S4 := fresh "S" in
let regs4 := fresh "regs" in let mem4 := fresh "mem" in let md4 := fresh "md" in
let HJ4 := fresh "HJ4" in let HJc := fresh "HJc" in let HP4 := fresh "HP4" in let Ha04 := fresh "Ha0c" in let HPb4 := fresh "HPb" in
let HRK := fresh "HRK" in let HEv := fresh "HEv" in
prreg HS (2%bv : bv 5) P2; prreg HS rs Prs; prreg HS (8%bv : bv 5) P8;
assert (Qtop : spZ regs < ly_top ly - 16) by (destruct Hch as [[_ Hnil] | (Q1 & Q2 & _)]; [exfalso; exact (Hchne Hnil) | lia]);
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia;
assert (Qceil : alloc_ceiling <= spZ regs) by lia;
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult);
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rsm := eval vm_compute in (ss_mem ssx) in let i := idx_of_base rsm 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRr
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRr
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0;
clear HRr;
assert (Hch1 : achain ly3 (aview pa_segs (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
let Etop := fresh "Etop" in
pose proof HJ3 as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _) & _);
apply (achain_ly_top ly ly3); [exact Etop|];
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)
(rdword_of_val_mem _ _ _ _ _ Vra Qra) (rdword_of_val_mem _ _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop ltac:(lia))
| ] end;
let i := idx_of_base rsm 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict mkst] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SOff 42 0) hw HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vhw;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 40 0) (bv_unsigned (ew Ex 40)) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (ew Ex 40)) as Q; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Q; exact Q) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SOff 44 0) pf HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E44, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vpf end;
clear HRr;
let pcj := eval vm_compute in (ss_pc ssx) in
let wj := eval vm_compute in (match plookup asan3_1_tpi pcj with Some (PW x) => x | _ => 0 end) in
let HEIx := rnHEI Ex in
eapply (SRr_jalr_call_pi (PL:=PL_asan3_1) W3 Ex ssx _ _ _ wj (1%bv : bv 5) rs wfn HEIx HS eq_refl);
[ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | rewrite Prs; exact E41 | exact (proj1 Rwfn) | exact (proj2 Rwfn) |];
clear HS; intros mat1 ms1 Ems1 HS1;
prreg HS1 (1%bv : bv 5) P1; prreg HS1 (3%bv : bv 5) P3; prreg HS1 (4%bv : bv 5) P4; clear P8; prreg HS1 (8%bv : bv 5) P8; prreg HS1 (10%bv : bv 5) P10;
prreg HS1 (11%bv : bv 5) P11; prreg HS1 (12%bv : bv 5) P12;
clear P2; prreg HS1 (2%bv : bv 5) P2;
let HJm := fresh "HJm" in let Qsp := fresh "Qsp" in
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
assert (HJm : ajournal pa_segs Bv STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem msX) mdq k)
by (apply (ajournal_materialize _ Bv LAWS pa_segs_low); exact HJ3);
assert (Qsp : spZ (ms_regs msq) = spZ regs + -192)
by (unfold spZ at 1; rewrite P2; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia;
rewrite Z_to_bv_bv_unsigned || idtac; evalE AG);
rewrite Ems1 at 1; rewrite Ems1 in Qsp; cbn [ms_regs mkst] in Qsp;
rewrite Ems1 in P1, P3, P4, P8, P10, P11, P12; cbn [ms_regs mkst] in P1, P3, P4, P8, P10, P11, P12;
eapply SRr_bind;
[ eapply (cl_callS Bv LAWS W3 _ (ms_mem msX) _ STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)] ly3 S3 mdq k
WCBF_STK (asink_fp pf) 0 (-192) _ ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ getr regs2 10 = w64 0 /\ asink_at pa_segs Kv (mrestrict (w_H W2) mem2) md2 pf (SG ++ bs)) HJm Qsp);
[ reflexivity | lia | unfold WCBF_STK, YC20.WCB_STK, AFWRITE_STK; lia | rewrite FFS; unfold WCBF_STK, YC20.WCB_STK, AFWRITE_STK; lia
| rewrite P3; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite P4; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact P1 | apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| unfold s0Z; rewrite P8; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -192) with (spZ regs - 192) by lia; exact Hch1
| let HPRE1 := fresh "HPRE1" in let HC := fresh "HC" in
intros HPRE1; eapply SRr_mono;
[ pose proof (WFN W3 ly3 S3 _ _ _ ((spZ regs, raZ regs, s0Z regs) :: ch) g p n pf SG bs HPRE1) as HC; unfold cfg_at in HC;
lazymatch type of HS1 with st_ok _ _ ?sse _ => replace (w64 wfn) with (Z_to_bv 64 (ss_pc sse)) in HC by reflexivity end;
eapply HC;
[ rewrite P10; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32; reflexivity
| rewrite P11; first [ assumption | symmetry; assumption
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; evalE AG;
first [ reflexivity | assumption | symmetry; assumption | match goal with |- ?gl => idtac "wcb_siteX: a1 goal left:" gl; fail end ] ]
| rewrite P12; first [ assumption | symmetry; assumption
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; evalE AG;
first [ reflexivity | assumption | symmetry; assumption | match goal with |- ?gl => idtac "wcb_siteX: a2 goal left:" gl; fail end ] ]
| exact Hing3 | exact Vpf | exact Hinf3 | exact HSINK | exact HGA
| exact (proj1 HWX) | exact (proj1 (proj2 HWX))
| clear - HWX; rewrite ?app_nil_r in *; rewrite ?length_app in *; lia
| clear - HWX; unfold FILE_BLOCK in *; lia
| left; rewrite Qsp; clear - HWX XF; unfold xfacts in XF; unfold WCBF_STK, YC20.WCB_STK, AFWRITE_STK; lia
| clear - HWX; lia | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HWX))))))
| exact HRA | exact HHV ]
| cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in
intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJ1 & HP & Ha0 & HSINK2);
exists ly3, S3, regs2, mem2, md2; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | ]]];
split; [reflexivity | split; [reflexivity | split; [exact Ha0 | exact HSINK2]]] ]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; left; exact Ha ]
| ] end;
clear HJm Qsp;
clear P3 P4 P10 P11 P12 Vra Vs0 Vhw Vctx Vpf Hch1 Prs;
let Ely4 := fresh "Ely" in let ES4 := fresh "ES" in let HSINK4 := fresh "HSINK4" in
cbv beta; intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & (Ely4 & ES4 & Ha04 & HSINK4)); subst ly4 S4;
pose proof (Permutation_refl (ablocks Bv ly3 S3)) as HPb4;
(let HP4' := fresh "HP4'" in
lazymatch type of HS1 with st_ok _ _ _ (restrict ?Hw ?msy) =>
assert (HP4' : aregs_preserved (ms_regs (restrict Hw msy)) regs4) by (rewrite Ems1; cbn [ms_regs restrict mkst]; exact HP4); clear HP4; rename HP4' into HP4 end);
let K := run_K_hi HS1 in
lazymatch type of HS1 with st_ok _ _ ?ssy _ =>
let n := eval vm_compute in (length (ss_mem ssy)) in let idxs := eval vm_compute in (seq 0 n) in
jafter_call_keep_hi HS1 K regs4 (mrestrict (w_H W4) mem4) HP4 idxs HS2 end;
rewrite Ems1 in HS2; cbn [ms_mem ms_regs restrict mkst] in HS2, HJc;
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3; aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
let HAR4 := fresh "HAR4" in let HFpres4 := fresh "HFpres4" in let HFSpres4 := fresh "HFSpres4" in let Hrpres4 := fresh "Hrpres4" in
let Kgot4 := fresh "Kgot4" in let Kcell4 := fresh "Kcell4" in let Kguar4 := fresh "Kguar4" in let Kuar4 := fresh "Kuar4" in let Vgr4 := fresh "Vgr4" in
pose proof (proj1 HJ4) as HAR4;
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin3) as (_ & _ & HFpres4 & HFSpres4); change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4;
change (256 / 8) with 32 in HFSpres4; rewrite !EFA3 in HFpres4, HFSpres4; fold F in HFpres4, HFSpres4;
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 HAR4 Hres_in) as (_ & _ & _ & _ & Hrpres4 & _); change (req_size 48) with 48 in Hrpres4;
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4;
match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
[ repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 516%nat F lo hi wlo whi _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; lia
| xFP | intros aa Haa; apply (fun H => proj1 (HFpres4 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_fshadow_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8) lo hi wlo whi _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia
| rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; lia
| xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 534%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_subw (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 534%nat lo hi wlo whi _ res 48 HJc);
[ evalE AG | exact Hres_in | exact Hres_in | lia | change (req_size 48) with 48; lia
| xFP | intros aa Haa; apply (fun H => proj1 (Hrpres4 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub _ Bv); [exact HJc | exact HJ4 | evalE AG | lia | rewrite FFS; lia | lia | cbn; lia | cbn; lia]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat _ lo hi wlo whi _ cid pos HJc);
[ evalE AG | exact HfinS3 | rewrite EFA3; lia | rewrite EFA3; lia | xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_sub _ Bv); [exact HJc | evalE AG | exact Hing3 | exact Hing3 | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia
| xFP ]
| |- _ => keptI I I AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
end
| ];
specialize (HS2 HRK); clear HRK HS1; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
rebaseE HS AG HEv; clear HEv;
let HS0 := fresh "HS0" in
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msr) =>
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs mkst restrict]; exact Ha04) eq_refl) as HS0 end;
clear HS; rename HS0 into HS; norm_ss HS;
clear HJ3 HAR3 HFpres3 HFSpres3 Hrpres3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
clear HJc HP4 HPb4 Ha04 Hwle4 P1 P2 P8 Qtop Qtop64 Qceil Qal8 Qra Qs0 Ems1; clear HSINK;
rename HJ4 into HJ3; rename HAR4 into HAR3; rename HFpres4 into HFpres3; rename HFSpres4 into HFSpres3;
rename Hrpres4 into Hrpres3; rename Kgot4 into Kgot3; rename Kcell4 into Kcell3; rename Kguar4 into Kguar3; rename Kuar4 into Kuar3; rename Vgr4 into Vgr3;
rename HSINK4 into HSINK;
replace (k + 0) with k in HJ3 by lia; clear HWX HGA HRA HHV
end end end end end end end end end end end.
Lemma xb_lit : forall E v, 0 <= v < 256 -> bv_unsigned (sv_denot E (SLit v)) mod 2 ^ (8 * Z.of_N 1) = v.
Proof.
intros E v Hv. change (bv_unsigned (sv_denot E (SLit v))) with (U E (SLit v)). rewrite U_SLit. unfold zcanon, M64. change (2 ^ (8 * Z.of_N 1)) with 256.
rewrite (Z.mod_small v) by lia. apply Z.mod_small. lia.
Qed.
Lemma xb_litm : forall E v, 0 <= v < 2 ^ 64 -> bv_unsigned (sv_denot E (SLit v)) mod 2 ^ (8 * Z.of_N 1) = v mod 256.
Proof.
intros E v Hv. change (bv_unsigned (sv_denot E (SLit v))) with (U E (SLit v)). rewrite U_SLit. unfold zcanon, M64. change (2 ^ (8 * Z.of_N 1)) with 256.
rewrite (Z.mod_small v) by lia. reflexivity.
Qed.
Lemma xb_lo : forall E a W, ew E a = Z_to_bv 64 W -> 0 <= W < 2 ^ 64 -> bv_unsigned (sv_denot E (SOff a 0)) mod 2 ^ (8 * Z.of_N 1) = W mod 256.
Proof. intros E a W Ha HW. change (bv_unsigned (sv_denot E (SOff a 0))) with (U E (SOff a 0)). rewrite (U_atom E a W Ha HW). reflexivity. Qed.
Lemma xb_hi : forall E a W, ew E a = Z_to_bv 64 W -> 0 <= W < 65536 ->
bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff a 0) (SLit 8))) mod 2 ^ (8 * Z.of_N 1) = (W / 256) mod 256.
Proof.
intros E a W Ha HW. change (bv_unsigned (sv_denot E ?[e]) mod _ = _) with (U E (SAlu ALU_SRL (SOff a 0) (SLit 8)) mod 2 ^ (8 * Z.of_N 1) = (W / 256) mod 256).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E a W Ha ltac:(lia)), U_SLit.
unfold zcanon, M64. change (Z.land (8 mod 2 ^ 64) 63) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. change (2 ^ (8 * Z.of_N 1)) with 256.
rewrite (Z.mod_small (W / 256)); [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma xb_slo : forall E a W, ew E a = Z_to_bv 64 W -> 0 <= W < 65536 ->
bv_unsigned (sv_denot E (SExt true 16 (SOff a 0))) mod 2 ^ (8 * Z.of_N 1) = W mod 256.
Proof.
intros E a W Ha HW. change (bv_unsigned (sv_denot E ?[e]) mod _ = _) with (U E (SExt true 16 (SOff a 0)) mod 2 ^ (8 * Z.of_N 1) = W mod 256).
rewrite U_SExt. rewrite (U_atom E a W Ha ltac:(lia)).
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N two_power_nat]. change (2 ^ (8 * 1)) with 256.
change (2 ^ 16 / 2) with 32768. change (2 ^ 16) with 65536.
rewrite (Z.mod_small W 65536) by lia.
destruct (Z_lt_le_dec W 32768).
- rewrite (Z.mod_small (W + 32768) 65536) by lia. replace (W + 32768 - 32768) with W by lia. rewrite (Z.mod_small W (2^64)) by lia. reflexivity.
- rewrite <- (Z.mod_add _ (-1) 65536) by lia. rewrite (Z.mod_small (W + 32768 + -1 * 65536) 65536) by lia.
replace (W + 32768 + -1 * 65536 - 32768) with (W - 65536) by lia.
rewrite <- (Z.mod_add _ 1 (2^64)) by lia. rewrite (Z.mod_small _ (2^64)) by lia.
replace (W - 65536 + 1 * 2 ^ 64) with (W + (2^56 - 256) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma xb_shi : forall E a W, ew E a = Z_to_bv 64 W -> 0 <= W < 65536 ->
bv_unsigned (sv_denot E (SAlu ALU_SRL (SExt true 16 (SOff a 0)) (SLit 8))) mod 2 ^ (8 * Z.of_N 1) = (W / 256) mod 256.
Proof.
intros E a W Ha HW.
change (bv_unsigned (sv_denot E ?[e]) mod _ = _) with (U E (SAlu ALU_SRL (SExt true 16 (SOff a 0)) (SLit 8)) mod 2 ^ (8 * Z.of_N 1) = (W / 256) mod 256).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, U_SLit. rewrite (U_atom E a W Ha ltac:(lia)).
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N two_power_nat]. change (2 ^ (8 * 1)) with 256.
change (Z.land (8 mod 2 ^ 64) 63) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
change (2 ^ 16 / 2) with 32768. change (2 ^ 16) with 65536.
rewrite (Z.mod_small W 65536) by lia.
destruct (Z_lt_le_dec W 32768).
- rewrite (Z.mod_small (W + 32768) 65536) by lia. replace (W + 32768 - 32768) with W by lia. rewrite (Z.mod_small W (2^64)) by lia.
rewrite (Z.mod_small (W / 256) (2 ^ 64)); [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
- rewrite <- (Z.mod_add _ (-1) 65536) by lia. rewrite (Z.mod_small (W + 32768 + -1 * 65536) 65536) by lia.
replace (W + 32768 + -1 * 65536 - 32768) with (W - 65536) by lia.
rewrite <- (Z.mod_add (W - 65536) 1 (2^64)) by lia. rewrite (Z.mod_small (W - 65536 + 1 * 2 ^ 64) (2^64)) by lia.
replace (W - 65536 + 1 * 2 ^ 64) with (W + (2^56 - 256) * 256) by lia. rewrite Z.div_add by lia.
rewrite (Z.mod_small (W / 256 + (2 ^ 56 - 256)) (2 ^ 64)); [| split; [pose proof (Z.div_pos W 256); lia | pose proof (Z.div_lt_upper_bound W 256 256); lia]].
replace (W / 256 + (2 ^ 56 - 256)) with (W / 256 + (2 ^ 48 - 1) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Ltac xidx_reg rs b lo :=
lazymatch rs with
| YP09.mkRegion (Some b) lo _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?rs' => let i := xidx_reg rs' b lo in constr:(S i)
end.
Ltac xatom Ev a H :=
lazymatch goal with H0 : ew _ a = Z_to_bv 64 ?W |- _ =>
assert (H : ew Ev a = Z_to_bv 64 W) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact H0) end.
Ltac xbyte HR off V :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HR with region_ok _ ?Ev ?m (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk off (CVal 1 ?e)] =>
pose proof (field_of_region_any Ev m 516 Fv cs lo hi wlo whi off 1%N e HR ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
change (N.to_nat 1) with 1%nat in V;
lazymatch e with
| SLit ?v => first [ rewrite (xb_lit Ev v ltac:(lia)) in V
| rewrite (xb_litm Ev v ltac:(lia)) in V; let r := eval vm_compute in (v mod 256) in change (v mod 256) with r in V ]
| SOff ?a 0 => let Ha := fresh "Ha" in xatom Ev a Ha; rewrite (xb_lo Ev a _ Ha ltac:(lia)) in V; clear Ha; try rewrite (Z.mod_small _ 256) in V by lia
| SAlu ALU_SRL (SOff ?a 0) (SLit 8) => let Ha := fresh "Ha" in xatom Ev a Ha; rewrite (xb_hi Ev a _ Ha ltac:(lia)) in V; clear Ha
| SExt true 16 (SOff ?a 0) => let Ha := fresh "Ha" in xatom Ev a Ha; rewrite (xb_slo Ev a _ Ha ltac:(lia)) in V; clear Ha
| SAlu ALU_SRL (SExt true 16 (SOff ?a 0)) (SLit 8) => let Ha := fresh "Ha" in xatom Ev a Ha; rewrite (xb_shi Ev a _ Ha ltac:(lia)) in V; clear Ha
| _ => idtac "xbyte: unknown chunk shape" e
end end end end.
Ltac xgarr8 :=
lazymatch goal with
| |- garr8 _ _ _ [] => let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; cbn in Hj; exfalso; lia
| |- garr8 ?sg ?m ?p (?v :: _) =>
apply garr8_cons_x;
[ match goal with V : val_mem _ m ?p' 1%nat v |- _ => first [exact V | replace p with p' by (clear; lia); exact V] end
| first [clear; lia | apply Z.mod_pos_bound; clear; lia | match goal with H : 0 <= v < 256 |- _ => exact H end]
| xgarr8 ]
end.
Ltac xhdr13_facts HS :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let LAWS := rnLAWS in let Bv := rnB in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
let E45 := lazymatch goal with H : ew _ 45 = Z_to_bv 64 (rn_pk _) |- _ => H end in
let Hcfg := lazymatch goal with H : obj_at _ _ _ LAY_RawConfig _ |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ /\ _) |- _ => H end in
let HSmax := lazymatch goal with H : Z.of_nat (length _) + HDR_OUT <= SINK_MAX |- _ => H end in
let Hsg := lazymatch goal with H : ?s <= 256 |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of E45 with _ = Z_to_bv 64 (rn_pk ?sg) =>
lazymatch type of Hcfg with obj_at _ _ _ _ [_; _; _; _; ?Wd; ?Hd; _; _] =>
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
let Hc' := fresh "Hc'" in let R28 := fresh "R28" in let R30 := fresh "R30" in let R32 := fresh "R32'" in
pose proof Hcfg as Hc'; cbn [obj_at LAY_RawConfig] in Hc';
destruct Hc' as (_ & _ & _ & _ & [_ R28] & [_ R30] & [_ R32] & _); cbn [fst snd N.to_nat Z.of_N] in R28, R30, R32;
change (2 ^ (8 * 2)) with 65536 in R28, R30, R32;
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i0 := xidx_reg rsm 516%nat 0 in let i0 := eval vm_compute in i0 in let r0 := eval vm_compute in (nth i0 rsm got_regionP) in
let i1 := xidx_reg rsm 516%nat 122 in let i1 := eval vm_compute in i1 in let r1 := eval vm_compute in (nth i1 rsm got_regionP) in
let i2 := xidx_reg rsm 529%nat 0 in let i2 := eval vm_compute in i2 in let r2 := eval vm_compute in (nth i2 rsm got_regionP) in
let HR0 := fresh "HR0" in let HR1 := fresh "HR1" in let HR2 := fresh "HR2" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict] in HR0;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict] in HR1;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict] in HR2;
let Hpk := fresh "Hpk" in pose proof (rn_pk_range sg ltac:(lia)) as Hpk;
let V112 := fresh "V112" in let V113 := fresh "V113" in let V114 := fresh "V114" in let V115 := fresh "V115" in let V116 := fresh "V116" in let V117 := fresh "V117" in let V118 := fresh "V118" in let V119 := fresh "V119" in let V120 := fresh "V120" in let V121 := fresh "V121" in let V122 := fresh "V122" in let V123 := fresh "V123" in let V124 := fresh "V124" in
xbyte HR0 112 V112; xbyte HR0 113 V113; xbyte HR0 114 V114; xbyte HR0 115 V115; xbyte HR0 116 V116; xbyte HR0 117 V117;
xbyte HR0 118 V118; xbyte HR0 119 V119; xbyte HR0 120 V120; xbyte HR0 121 V121;
xbyte HR1 122 V122; xbyte HR1 123 V123; xbyte HR1 124 V124;
lazymatch type of HR0 with region_ok _ _ ?m _ =>
assert (HGA : garr8 pa_segs m (Fv + 112) (YI0j.hdr13 Wd Hd (rn_pk sg))) by (unfold YI0j.hdr13; xgarr8);
clear V112 V113 V114 V115 V116 V117 V118 V119 V120 V121 V122 V123 V124 HR0 HR1;
let V14 := fresh "V14" in let V15 := fresh "V15" in let Hsh14 := fresh "Hsh14" in let Hsh15 := fresh "Hsh15" in let Hsa := fresh "Hsa" in
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 14 1%N (SLit 0) 0 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V14;
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 15 1%N (SLit 5) 5 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V15 end;
clear HR2;
pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V14 ltac:(lia)) as Hsh14; pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V15 ltac:(lia)) as Hsh15;
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
assert (Hsa : shadow_of_addr SHADOW_OFF (Fv + 112) = SB + Fv / 8 + 14)
by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; rewrite HFq at 1; rewrite HF8;
replace (32 * (Fv / 32) + 112) with ((4 * (Fv / 32) + 14) * 8) by lia; rewrite Z.div_mul by lia; lia);
assert (HRAX : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF (Fv + 112) 13)
by (apply (block_shadow_range _ _ (Fv + 112) 13); [| lia | lia];
apply block_shadow_cells2; [rewrite HFq; replace (32 * (Fv / 32) + 112) with ((4 * (Fv / 32) + 14) * 8) by lia; apply Z_mod_mult | lia | rewrite Hsa; exact Hsh14 | rewrite Hsa; replace (SB + Fv / 8 + 14 + 1) with (SB + Fv / 8 + 15) by lia; exact Hsh15]);
clear V14 V15 Hsh14 Hsh15 Hsa;
let HJ3 := lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ (ms_mem msx) _ _ |- _ => H end in
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ _ _ _ =>
let Hfin3 := lazymatch goal with H : In (2, ?fp) (frames S3) |- _ => H end in
let EFA3 := lazymatch goal with H : forall c p, frame_addr ly3 c p = frame_addr _ c p |- _ => H end in
lazymatch type of Hfin3 with In (2, ?fpos) _ =>
assert (HHVX : shadow_hull_vis (aview pa_segs Hw (ms_mem msx)) (Fv + 112) 13)
by (eapply (shadow_hull_vis_of_frame pa_segs Bv LAWS ly3 S3 _ _ _ 2 fpos (Fv + 112) 13 (proj1 HJ3) Hfin3);
[rewrite EFA3; lia | rewrite EFA3; change (fs_frame_bytes 2) with 256; lia | lia]) end end;
let HFhigh := lazymatch goal with H : in_app Fv 256 |- _ => H end in
let HFceil := lazymatch goal with H : Fv + 256 <= alloc_ceiling |- _ => H end in
assert (HWX : 13 = Z.of_nat (length (YI0j.hdr13 Wd Hd (rn_pk sg))) /\ 1 <= 13 <= 2 ^ 30 /\ Z.of_nat (length SG) + 13 <= SINK_MAX /\
(Fv + 112 + 13 <= pf \/ pf + FILE_BLOCK <= Fv + 112) /\ 0 <= Fv + 112 /\ amem_range (Fv + 112) 13 /\ Fv + 112 + 13 <= alloc_ceiling)
by (split; [reflexivity|]; split; [lia|]; split; [clear - HSmax; rewrite ?app_nil_r; unfold HDR_OUT in HSmax; lia|];
split; [clear - XF; unfold xfacts in XF; unfold FILE_BLOCK; lia|]; split; [clear - XF; unfold xfacts in XF; lia|];
split; [apply (amem_range_sub_app _ _ _ _ HFhigh HFceil); clear; lia | clear - XF; unfold xfacts in XF; lia]);
clear R28 R30 R32 Hpk
end end end end end end.
Ltac xlist_eq :=
first [ reflexivity
| lazymatch goal with Hz : ?s = 0 |- context [?s =? 0] => rewrite (proj2 (Z.eqb_eq s 0) Hz); rewrite ?app_nil_r, <- ?app_assoc; reflexivity end
| lazymatch goal with Hz : ?s <> 0 |- context [?s =? 0] => rewrite (proj2 (Z.eqb_neq s 0) Hz); rewrite ?app_nil_r, <- ?app_assoc; reflexivity end
| match goal with |- ?g => idtac "xpre_sink: list goal left" g; fail end ].
Ltac xpre_sink :=
lazymatch goal with |- asink_at ?sg ?Kv ?m ?md ?f ?S1 =>
lazymatch goal with H : asink_at sg Kv m md f ?S2 |- _ =>
replace S1 with S2; [exact H | unfold PRE_C, PRE_D, PRE_G, PRE_X; rewrite ?app_nil_r, <- ?app_assoc; xlist_eq ] end end.
Ltac xsgct0 Hc Hsg0 :=
let E38 := lazymatch goal with H : ew _ 38 = Z_to_bv 64 ?s |- _ => H end in
let Hcfg := lazymatch goal with H : obj_at _ _ _ LAY_RawConfig _ |- _ => H end in
let Hc' := fresh "Hc'" in let R32 := fresh "R32q" in
pose proof Hcfg as Hc'; cbn [obj_at LAY_RawConfig] in Hc'; destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _); cbn [fst snd N.to_nat Z.of_N] in R32;
change (2 ^ (8 * 2)) with 65536 in R32;
unfold branch_taken in Hc; rewrite bv_eqb_unsigned in Hc; cbn [sv_denot] in Hc; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc;
rewrite ?ew_ewset_other in Hc by lia; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia; apply Z.eqb_eq in Hc; rename Hc into Hsg0; clear R32.
Lemma denot_mul3 : forall E n s, ew E n = Z_to_bv 64 s -> 0 <= s < 65536 -> sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = w64 (s * 3).
Proof.
intros E n s Hn Hs. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)))).
change (bv_unsigned (sv_denot E ?[e])) with (U E (SMd M_MUL (SOff n 0) (SLit 3))). rewrite U_SMd, U_SLit, (U_atom E n s Hn ltac:(lia)). cbv beta zeta iota delta [zmd_raw].
unfold zcanon, M64. rewrite (Z.mod_small 3) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac xgct_facts HS :=
let LAWS := rnLAWS in let Bv := rnB in
let HGCT := lazymatch goal with H : ?s <> 0 -> In _ _ /\ _ |- _ => H end in
let Hc := lazymatch type of HGCT with ?s <> 0 -> _ => lazymatch goal with H : s <> 0 |- _ => H end end in
let HPerm := lazymatch goal with H : Permutation (ablocks _ _ _) ((_, CGIF_SIZE) :: (_, FILE_BLOCK) :: _) |- _ => H end in
let Eab3 := lazymatch goal with H : Permutation (ablocks _ _ _) (ablocks _ _ _ ++ [(_, 48)]) |- _ => H end in
let HAR := lazymatch type of HPerm with Permutation (ablocks _ ?ly ?S) _ => lazymatch goal with H : AR _ _ ly S _ _ _ |- _ => H end end in
let XF := lazymatch goal with H : xfacts (_ /\ _) |- _ => H end in
let HSmax := lazymatch goal with H : Z.of_nat (length _) + HDR_OUT <= SINK_MAX |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let E38 := lazymatch goal with H : ew _ 38 = Z_to_bv 64 _ |- _ => H end in
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
lazymatch type of HGCT with ?sgct <> 0 -> In (?pga, ?Npg) ?rest /\ _ /\ _ /\ garr8 _ _ _ ?GCT /\ _ =>
lazymatch type of HPerm with Permutation _ ((?g, CGIF_SIZE) :: _ :: _) =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let HJ3 := lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ (ms_mem msx) _ _ |- _ => H end in
lazymatch type of HJ3 with ajournal _ _ _ _ _ ?ly ?S ?W ?mem ?md _ ?ly3 ?S3 _ _ _ _ =>
let HinR := fresh "HinR" in let HGeq := fresh "HGeq" in let H3N := fresh "H3N" in let HG0 := fresh "HG0" in let HGlen := fresh "HGlen" in
let HinA := fresh "HinA" in let HinA3 := fresh "HinA3" in let r1 := fresh "r1" in let r2 := fresh "r2" in let Er := fresh "Er" in
let HPq := fresh "HPq" in let HdPQ := fresh "HdPQ" in let HNq := fresh "HNq" in let HLn := fresh "HLn" in let HG1 := fresh "HG1" in
let Hq4096 := fresh "Hq4096" in let Hqceil := fresh "Hqceil" in
destruct (HGCT Hc) as (HinR & HGeq & H3N & HG0 & HGlen);
assert (HinA : In (pga, Npg) (ablocks Bv ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; right; exact HinR);
assert (HinA3 : In (pga, Npg) (ablocks Bv ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Eab3|]; apply in_app_iff; left; exact HinA);
destruct (in_split _ _ HinR) as (r1 & r2 & Er);
assert (HPq : Permutation (ablocks Bv ly S) ((pf, FILE_BLOCK) :: (pga, Npg) :: (g, CGIF_SIZE) :: r1 ++ r2));
[ eapply Permutation_trans; [exact HPerm|]; rewrite Er; eapply Permutation_trans; [apply perm_skip; apply perm_skip; apply Permutation_sym; apply Permutation_middle|];
eapply Permutation_trans; [apply perm_swap|]; apply perm_skip; apply perm_swap | ];
pose proof (sep_blocks_perm _ _ LAWS ly S W mem md _ _ _ HAR HPq) as HdPQ; unfold zdisjoint, block_rng in HdPQ; cbn [fst snd] in HdPQ; change (req_size FILE_BLOCK) with 1264 in HdPQ;
pose proof (proj2 (req_size_pos Npg ltac:(lia))) as HNq;
destruct (al_blocks _ _ LAWS _ _ _ _ _ pga Npg (proj1 HJ3) HinA3) as (_ & Hq4096 & Hqceil & _ & _ & _);
clear HPq Er;
assert (HLn : length (firstn (Z.to_nat (sgct * 3)) GCT) = Z.to_nat (sgct * 3)) by (rewrite length_firstn; apply Nat.min_l; apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia);
pose proof (garr8_sub_x pa_segs _ pga GCT 0 (Z.to_nat (sgct * 3)) HG0 ltac:(rewrite Nat.add_0_l; apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia)) as HG1;
rewrite skipn_O, Z.add_0_r in HG1;
let XF2 := fresh "XF" in
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ (pf + 1264 <= pga \/ pga + Npg <= pf) /\ 4096 <= pga /\ pga + Npg <= alloc_ceiling /\ 3 * sgct <= Npg /\ 0 < sgct <= 256))
by (apply xfacts_i; split; [exact XF | lazymatch goal with Hs : sgct <= 256, R : 0 <= sgct < _ |- _ => clear - HdPQ HNq Hq4096 Hqceil H3N Hc Hs R; lia end]);
clear XF; rename XF2 into XF end;
assert (HGA : garr8 pa_segs (mrestrict Hw (ms_mem msx)) pga (firstn (Z.to_nat (sgct * 3)) GCT));
[ eapply (garr8_journal_block_x pa_segs Bv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pga Npg pga _ HJ3 HinA HinA3 ltac:(lia));
[rewrite HLn, Z2Nat.id by lia; lia | rewrite HLn, Z2Nat.id by lia; xFP | exact HG1] | ];
clear HG1;
assert (HRAX : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF pga (sgct * 3))
by (apply (range_addressable_of_block _ Bv LAWS _ _ _ _ _ pga Npg pga (sgct * 3) (proj1 HJ3) HinA3); lia);
assert (HHVX : shadow_hull_vis (aview pa_segs Hw (ms_mem msx)) pga (sgct * 3))
by (apply (shadow_hull_vis_of_block _ Bv LAWS _ _ _ _ _ pga Npg pga (sgct * 3) (proj1 HJ3) HinA3); lia);
assert (HWX : sgct * 3 = Z.of_nat (length (firstn (Z.to_nat (sgct * 3)) GCT)) /\ 1 <= sgct * 3 <= 2 ^ 30 /\ Z.of_nat (length SG) + sgct * 3 <= SINK_MAX /\
(pga + sgct * 3 <= pf \/ pf + FILE_BLOCK <= pga) /\ 0 <= pga /\ amem_range pga (sgct * 3) /\ pga + sgct * 3 <= alloc_ceiling)
by (split; [rewrite HLn, Z2Nat.id by lia; reflexivity|]; split; [clear - XF; unfold xfacts in XF; lia|];
split; [clear - HSmax XF; unfold xfacts in XF; rewrite ?app_nil_r, ?length_app in *; unfold YI0j.hdr13 in *; cbn [length Nat.add] in *; unfold HDR_OUT in HSmax; lia|];
split; [clear - XF; unfold xfacts in XF; unfold FILE_BLOCK; lia|]; split; [clear - XF; unfold xfacts in XF; lia|];
split; [apply (amem_range_of_block _ Bv LAWS _ _ _ _ _ pga Npg pga (sgct * 3) (proj1 HJ3) HinA3); lia | clear - XF; unfold xfacts in XF; lia]);
let XA2 := fresh "XA2" in
lazymatch type of E38 with ew ?Eb 38 = _ =>
assert (XA2 : sv_denot Eb (SMd M_MUL (SOff 38 0) (SLit 3)) = w64 (sgct * 3)) by (apply (denot_mul3 Eb 38 sgct); [exact E38 | lia]);
cbn [sv_denot] in XA2; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in XA2 end;
clear HinR H3N HG0 HGlen HdPQ HNq HLn Hq4096 Hqceil r1 r2
end end end end end.
Lemma gct_pad_K : forall Kq sgct GCT, 0 <= Kq <= 8 -> 0 < sgct -> sgct <= 2 ^ Kq -> 2 ^ Kq < 2 * sgct ->
YI0j.gct_pad sgct GCT = firstn (Z.to_nat (sgct * 3)) GCT ++ repeat 0 (Z.to_nat (3 * (2 ^ Z.max Kq 1 - sgct))).
Proof.
intros Kq sgct GCT HK Hs H1 H2. unfold YI0j.gct_pad, YO07.zeros.
rewrite (YI0j.pal_pow_class Kq sgct ltac:(lia)); [| intros ->; exact H1 | | exact H1].
2:{ intros HKp. assert (E : 2 ^ Kq = 2 * 2 ^ (Kq - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). lia. }
rewrite Z.max_comm.
assert (Hp2 : sgct <= 2 ^ Z.max Kq 1 <= 256).
{ split; [apply (Z.le_trans _ (2 ^ Kq)); [lia | apply Z.pow_le_mono_r; lia]|]. change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia. }
rewrite Z.mod_small by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma np2_aux_ge : forall fuel n p, 0 <= p -> n <= 2 ^ (p + Z.of_nat fuel) -> n <= 2 ^ YO07.np2_aux fuel n p.
Proof.
induction fuel as [|fuel IH]; intros n p Hp Hn; cbn [YO07.np2_aux].
- rewrite Z.add_0_r in Hn. exact Hn.
- destruct (Z.ltb_spec (2 ^ p) n); [|lia]. apply IH; [lia|]. replace (p + 1 + Z.of_nat fuel) with (p + Z.of_nat (S fuel)) by lia. exact Hn.
Qed.
Lemma pal_pow_bounds : forall sgct, 1 <= sgct <= 256 -> sgct <= 2 ^ YO07.pal_pow sgct <= 256.
Proof.
intros sgct Hs. unfold YO07.pal_pow, YO07.calcNextPower2Ex.
pose proof (np2_aux_le8 17 sgct 0 ltac:(lia) ltac:(lia)) as Hle. pose proof (np2_aux_ge 17 sgct 0 ltac:(lia) ltac:(cbn; lia)) as Hge.
split.
- apply (Z.le_trans _ _ _ Hge). apply Z.pow_le_mono_r; lia.
- change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia.
Qed.
Lemma PRE_D_length : forall Wd Hd sgct GCT rattr loops, 0 <= sgct <= 256 -> Z.of_nat (length (PRE_D Wd Hd sgct GCT rattr loops)) <= 781.
Proof.
intros Wd Hd sgct GCT rattr loops Hs. unfold PRE_D, YI0j.hdr13, YI0j.gct_pad, YO07.zeros.
rewrite length_app. cbn [length]. destruct (Z.eqb_spec sgct 0) as [->|Hnz]; [cbn; lia|].
pose proof (pal_pow_bounds sgct ltac:(lia)) as [H1 H2].
rewrite length_app, length_firstn, repeat_length. rewrite Z.mod_small by lia.
pose proof (Nat.le_min_l (Z.to_nat (sgct * 3)) (length GCT)). lia.
Qed.
Ltac xnet19_facts HS :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let LAWS := rnLAWS in let Bv := rnB in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
let Hcfg := lazymatch goal with H : obj_at _ _ _ LAY_RawConfig _ |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ /\ _) |- _ => H end in
let HSmax := lazymatch goal with H : Z.of_nat (length _) + HDR_OUT <= SINK_MAX |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of Hcfg with obj_at _ _ _ _ [_; _; _; _; _; _; ?sg; ?loops] =>
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
let Hsg := lazymatch goal with H : sg <= 256 |- _ => H end in
let R32 := lazymatch goal with H : 0 <= sg < _ |- _ => H end in
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i0 := xidx_reg rsm 516%nat 0 in let i0 := eval vm_compute in i0 in let r0 := eval vm_compute in (nth i0 rsm got_regionP) in
let i2 := xidx_reg rsm 529%nat 0 in let i2 := eval vm_compute in i2 in let r2 := eval vm_compute in (nth i2 rsm got_regionP) in
let HR0 := fresh "HR0" in let HR2 := fresh "HR2" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict] in HR0;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict] in HR2;
let V48 := fresh "V48" in let V49 := fresh "V49" in let V50 := fresh "V50" in let V51 := fresh "V51" in let V52 := fresh "V52" in let V53 := fresh "V53" in let V54 := fresh "V54" in let V55 := fresh "V55" in let V56 := fresh "V56" in let V57 := fresh "V57" in let V58 := fresh "V58" in let V59 := fresh "V59" in let V60 := fresh "V60" in let V61 := fresh "V61" in let V62 := fresh "V62" in let V63 := fresh "V63" in let V64 := fresh "V64" in let V65 := fresh "V65" in let V66 := fresh "V66" in
xbyte HR0 48 V48; xbyte HR0 49 V49; xbyte HR0 50 V50; xbyte HR0 51 V51; xbyte HR0 52 V52; xbyte HR0 53 V53; xbyte HR0 54 V54; xbyte HR0 55 V55; xbyte HR0 56 V56; xbyte HR0 57 V57; xbyte HR0 58 V58; xbyte HR0 59 V59; xbyte HR0 60 V60; xbyte HR0 61 V61; xbyte HR0 62 V62; xbyte HR0 63 V63; xbyte HR0 64 V64; xbyte HR0 65 V65; xbyte HR0 66 V66;
lazymatch type of HR0 with region_ok _ _ ?m _ =>
assert (HGA : garr8 pa_segs m (Fv + 48) (YI0j.net19 loops)) by (unfold YI0j.net19; xgarr8);
clear V48 V49 V50 V51 V52 V53 V54 V55 V56 V57 V58 V59 V60 V61 V62 V63 V64 V65 V66 HR0;
let V6 := fresh "V6" in let V7 := fresh "V7" in let V8 := fresh "V8" in let Hsh6 := fresh "Hsh6" in let Hsh7 := fresh "Hsh7" in let Hsh8 := fresh "Hsh8" in let Hsa := fresh "Hsa" in
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 6 1%N (SLit 0) 0 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V6;
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 7 1%N (SLit 0) 0 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V7;
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 8 1%N (SLit 3) 3 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V8 end;
clear HR2;
pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V6 ltac:(lia)) as Hsh6; pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V7 ltac:(lia)) as Hsh7;
pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V8 ltac:(lia)) as Hsh8;
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
assert (Hsa : shadow_of_addr SHADOW_OFF (Fv + 48) = SB + Fv / 8 + 6)
by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; rewrite HFq at 1; rewrite HF8;
replace (32 * (Fv / 32) + 48) with ((4 * (Fv / 32) + 6) * 8) by lia; rewrite Z.div_mul by lia; lia);
assert (HRAX : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF (Fv + 48) 19)
by (apply (block_shadow_range _ _ (Fv + 48) 19); [| lia | lia];
apply block_shadow_cells3; [rewrite HFq; replace (32 * (Fv / 32) + 48) with ((4 * (Fv / 32) + 6) * 8) by lia; apply Z_mod_mult | lia
| rewrite Hsa; exact Hsh6 | rewrite Hsa; replace (SB + Fv / 8 + 6 + 1) with (SB + Fv / 8 + 7) by lia; exact Hsh7
| rewrite Hsa; replace (SB + Fv / 8 + 6 + 2) with (SB + Fv / 8 + 8) by lia; exact Hsh8]);
clear V6 V7 V8 Hsh6 Hsh7 Hsh8 Hsa;
let HJ3 := lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ (ms_mem msx) _ _ |- _ => H end in
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ _ _ _ =>
let Hfin3 := lazymatch goal with H : In (2, ?fp) (frames S3) |- _ => H end in
let EFA3 := lazymatch goal with H : forall c p, frame_addr ly3 c p = frame_addr _ c p |- _ => H end in
lazymatch type of Hfin3 with In (2, ?fpos) _ =>
assert (HHVX : shadow_hull_vis (aview pa_segs Hw (ms_mem msx)) (Fv + 48) 19)
by (eapply (shadow_hull_vis_of_frame pa_segs Bv LAWS ly3 S3 _ _ _ 2 fpos (Fv + 48) 19 (proj1 HJ3) Hfin3);
[rewrite EFA3; lia | rewrite EFA3; change (fs_frame_bytes 2) with 256; lia | lia]) end end;
let HFhigh := lazymatch goal with H : in_app Fv 256 |- _ => H end in
let HFceil := lazymatch goal with H : Fv + 256 <= alloc_ceiling |- _ => H end in
lazymatch SG with ?Sg ++ PRE_D ?Wd ?Hd _ ?GCT ?rattr _ =>
assert (HWX : 19 = Z.of_nat (length (YI0j.net19 loops)) /\ 1 <= 19 <= 2 ^ 30 /\ Z.of_nat (length SG) + 19 <= SINK_MAX /\
(Fv + 48 + 19 <= pf \/ pf + FILE_BLOCK <= Fv + 48) /\ 0 <= Fv + 48 /\ amem_range (Fv + 48) 19 /\ Fv + 48 + 19 <= alloc_ceiling)
by (split; [reflexivity|]; split; [lia|];
split; [let HL := fresh "HL" in pose proof (PRE_D_length Wd Hd sg GCT rattr loops ltac:(clear - Hsg R32; lia)) as HL; clear - HSmax HL; rewrite length_app; unfold HDR_OUT in HSmax; lia|];
split; [clear - XF; unfold xfacts in XF; unfold FILE_BLOCK; lia|]; split; [clear - XF; unfold xfacts in XF; lia|];
split; [apply (amem_range_sub_app _ _ _ _ HFhigh HFceil); clear; lia | clear - XF; unfold xfacts in XF; lia]) end
end end end end end.
