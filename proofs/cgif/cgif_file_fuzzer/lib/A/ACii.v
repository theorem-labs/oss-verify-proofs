(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1 ACj0 ACja.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj0 ACj6 ACiy ACj7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac xwinF_fl Hrr Hpf :=
lazymatch type of Hrr with
| context [_ / 8] =>
lazymatch goal with Hia : xfacts (in_app ?pfv 1264) |- _ =>
lazymatch type of Hrr with _ <= ?a < _ + ?Fv / 8 + ?k =>
lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ =>
refine (fshadow_not_app Fv 32 pfv 1264 a _ _ Hia _ _);
[ clear - XF; unfold xfacts in XF; lia | clear - XF; unfold xfacts in XF; lia
| clear - Hrr; unfold SB in *; lia | clear - Hpf; lia ] end end end
| _ => first
[ lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _), Hsp1 : _ - 400 <= _ <= _ - 384 |- _ =>
clear - XF Hrr Hpf Hsp1; unfold xfacts in XF; lia end
|
lazymatch goal with Hno : forall x, _ <= x < _ + 1264 -> ~ aowned _ _ _ x |- _ =>
lazymatch goal with Hown : aowned _ _ _ ?fl |- _ =>
let av := lazymatch type of Hpf with _ <= ?a < _ => a end in
apply (Hno _ Hpf); replace fl with av in Hown by (clear - Hrr; lia); exact Hown end end ]
end.
Ltac xwinI_fl Hrr Himg :=
let Hr := fresh "Hr" in pose proof (pa_img_range _ Himg) as Hr;
lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _), Hsp1 : _ - 400 <= _ <= _ - 384 |- _ =>
first [ clear - XF Hrr Hr Hsp1; unfold xfacts in XF; unfold SB in *; lia
| lazymatch type of Hrr with ?c + _ <= _ < _ => lazymatch goal with Hc : off_img c _ |- _ => clear - Hrr Hr Hc; unfold off_img in Hc; lia end end
|
lazymatch goal with Hni : ~ in_img _ ?fl |- _ =>
let av := lazymatch type of Himg with in_img _ ?a => a end in
apply Hni; replace fl with av by (clear - Hrr; lia); exact Himg end ] end.
Ltac xwin_one_fl AG Hrr :=
first [ exfalso; clear - Hrr; lia
| evalE_in AG Hrr; split; [ let Hpf := fresh "Hpf" in intros Hpf; xwinF_fl Hrr Hpf | let Himg := fresh "Himg" in intros Himg; xwinI_fl Hrr Himg ] ].
Ltac xwin_loop_fl AG Hin Hrr :=
lazymatch type of Hin with
| False => destruct Hin
| _ \/ _ => let Hq := fresh "Hq" in let Hin2 := fresh "Hin" in
destruct Hin as [Hq | Hin2]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; xwin_one_fl AG Hrr | xwin_loop_fl AG Hin2 Hrr]
end.
Ltac xsink_stretchF HFr HSINK :=
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
intros b wlo whi a Hin Hrr; vm_compute in Hin; xwin_loop_fl AG Hin Hrr)) as UN;
cbn beta in UN;
assert (H2 : asink_at sg Kv (mrestrict (w_H Wv) (ms_mem msn)) mdn pf SG);
[ apply (asink_at_model sg Kv _ mdo); [reflexivity | reflexivity |];
apply (asink_at_frame sg Kv (mrestrict (w_H Wv) mo)); [|exact HSINK];
let a := fresh "a" in let Ha := fresh "Ha" in let Hn1 := fresh "Hn" in let Hn2 := fresh "Hn" in
intros a Ha; apply (mbyte_of_aview sg); cbn [ms_mem]; apply UN;
[ destruct Ha as [Ha | Ha];
[ lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => clear - XF Ha; unfold xfacts in XF; unfold FILE_BLOCK in Ha; lia end
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))); lia ]
| intros [Hn1 Hn2]; destruct Ha as [Ha | Ha];
[ apply Hn1; unfold FILE_BLOCK in Ha; exact Ha | exact (Hn2 (proj1 (ail_env _ _ _ AIL a Ha))) ] ]
| clear UN HSINK; rename H2 into HSINK; lazymatch made with true => clear AG | false => idtac end ] end end.
Ltac xval_stretchF HV :=
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?Hh ?m0) (mrestrict _ (ms_mem ?msX)) |- _ =>
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
lazymatch type of HV with val_mem ?sg (mrestrict ?Hh0 ?m00) ?p ?n ?v =>
let HV2 := fresh "HV" in
assert (HV2 : val_mem sg (mrestrict Hh (ms_mem msX)) p n v);
[ apply (val_mem_aview_kept_x sg Hh0 Hh m00 (ms_mem msX) p n v); [| exact HV];
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; eapply (aview_kept_out Ef rs _ _ _ HFr); [lazymatch goal with Hr : 4096 <= ?r, Hc : ?r + 48 <= alloc_ceiling, C1 : _ <= alloc_ceiling <= _ |- _ => clear - Ha Hr Hc C1; lia end|];
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
first [ lazymatch goal with HdFR : _ + 48 <= ?Fv \/ ?Fv + 256 <= _, HdRC : _ + 48 <= _ \/ _ + 40 <= _, Hrceil : _ + 48 <= alloc_ceiling,
XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _), Hsp1 : _ - 400 <= _ <= _ - 384 |- _ =>
clear - Ha Hrg HdFR HdRC Hrceil XF Hsp1; unfold xfacts in XF; unfold SB in *; lia end
|
lazymatch type of Hrg with _ <= ?a0 < _ + ?Fv / 8 + _ =>
lazymatch goal with Hia : xfacts (in_app ?r 48), XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ =>
refine (fshadow_not_app Fv 32 r 48 a0 _ _ Hia _ _);
[ clear - XF; unfold xfacts in XF; lia | clear - XF; unfold xfacts in XF; lia | clear - Hrg; unfold SB in *; lia | clear - Ha; lia ] end end
|
lazymatch goal with Hno : forall x, ?r <= x < ?r + 48 -> ~ aowned _ _ _ x, Hown : aowned _ _ _ ?fl |- _ =>
apply (Hno fl); [clear - Ha Hrg; lia | exact Hown] end ] |]);
destruct Hin
| clear HV; rename HV2 into HV ] end end.
