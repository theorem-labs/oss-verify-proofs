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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8a ACjr ACj3 ACh9 ACk4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACk5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YC5d YC7z YC7x YC21 YC85 YC86 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI17 YE02 YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACk0 ACk2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac fptokS :=
lazymatch goal with
| |- forall x, inFP _ x -> x < kLowShadowBeg \/ kHighShadowEnd <= x =>
let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply inFP_token in Hx; left; unfold kLowShadowBeg; clear - Hx; lia
| |- forall x, inFP _ x -> False =>
let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply inFP_token in Hx; first [lia | unfold SB in *; lia]
| |- _ => fptok
end.
Ltac xgwinB p Hrr Hp :=
lazymatch type of Hrr with
| context [_ / 8] =>
lazymatch goal with Hia : xfacts (in_app p ?n) |- _ =>
lazymatch type of Hrr with _ <= ?a < _ + ?Fv / 8 + ?k =>
lazymatch goal with XF : xfacts (_ /\ _) |- _ =>
refine (fshadow_not_app Fv 32 p n a _ _ Hia _ _);
[ clear - XF; unfold xfacts in XF; lia | clear - XF; unfold xfacts in XF; lia
| clear - Hrr; unfold SB in *; lia | clear - XF Hp; unfold xfacts in XF; lia ] end end end
| _ => first
[ lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Hrr Hp; unfold xfacts in XF; lia end
|
lazymatch goal with Hno : forall x, p <= x < _ -> ~ aowned _ _ _ x |- _ =>
lazymatch goal with Hown : aowned _ _ _ ?fl |- _ =>
let av := lazymatch type of Hp with _ <= ?a < _ => a end in
refine (Hno av _ _); [ lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Hp; unfold xfacts in XF; lia end
| replace av with fl by (clear - Hrr; lia); exact Hown ] end end ]
end.
Ltac xgwin_loop AG Hin Hrr p :=
lazymatch type of Hin with
| False => destruct Hin
| _ \/ _ => let Hq := fresh "Hq" in let Hin2 := fresh "Hin" in
destruct Hin as [Hq | Hin2];
[ injection Hq as <- <- <-; cbn [base_val] in Hrr;
first [ exfalso; clear - Hrr; lia | evalE_in AG Hrr; let Hp := fresh "Hp" in intros Hp; xgwinB p Hrr Hp ]
| xgwin_loop AG Hin2 Hrr p ]
end.
Ltac xgarr_stretch HFr HG :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
lazymatch goal with |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
lazymatch type of HG with garr8 ?sg (mrestrict (w_H ?Wv) ?mo) ?p ?L =>
lazymatch goal with Hlen : Z.of_nat (length L) = ?bn |- _ =>
let UN := fresh "UN" in let H2 := fresh "HG" in
pose proof (kept_of_frame (segs:=sg) _ _ _ _ _ (fun a => ~ (p <= a < p + bn)) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
intros b wlo whi a Hin Hrr; vm_compute in Hin; xgwin_loop AG Hin Hrr p)) as UN;
cbn beta in UN;
assert (H2 : garr8 sg (mrestrict (w_H Wv) (ms_mem msn)) p L);
[ apply (garr8_aview_kept sg (w_H Wv) (w_H Wv) mo (ms_mem msn)); [|exact HG];
let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
intros a Ha; rewrite Hlen in Ha; cbn [ms_mem]; apply UN;
[ lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Ha; unfold xfacts in XF; lia end
| intros Hn; exact (Hn Ha) ]
| clear UN HG; rename H2 into HG ] end end end.
Ltac fpfile :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
intros a Ha Hn; apply in_asink_fp in Hn; destruct Hn as [Hn | Hn];
[ unfold FILE_BLOCK in Hn;
lazymatch type of Ha with
| context [_ / 8] =>
lazymatch goal with Hia : xfacts (in_app ?pfv 1264) |- _ =>
lazymatch type of Ha with _ <= _ < _ + ?Fv / 8 + ?k =>
lazymatch goal with XF : xfacts (_ /\ _) |- _ =>
refine (fshadow_not_app Fv 32 pfv 1264 a _ _ Hia _ Hn);
[ clear - XF; unfold xfacts in XF; lia | clear - XF; unfold xfacts in XF; lia | clear - Ha; unfold SB in *; lia ] end end end
| _ => lazymatch goal with XF : xfacts (_ /\ _) |- _ => clear - XF Ha Hn; unfold xfacts in XF; lia end
end
| first [lia | unfold SB in *; lia] ].
Ltac oblFX HJx HE10 HE35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 10 ?c)) ?len =>
lazymatch type of HE10 with _ = Z_to_bv 64 ?cfgp =>
first [ rewrite (U_atom_off Ex 10 cfgp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia | lia]
| rewrite (U_atom Ex 10 cfgp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia] ];
eapply (obl_of_range _ _ _ Ex (SOff 35 0) _ len cfgp 48);
[ let L := rnLAWS in eapply (range_addressable_entry_frame _ _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| fptokS | exact HAR | exact HRA]
| rewrite (U_atom Ex 35 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | lia ] end end.
