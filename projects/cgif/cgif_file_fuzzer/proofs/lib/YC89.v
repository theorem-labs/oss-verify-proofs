(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP09 YP0l YP03 YP0b YP0a YP0d YN3v YI04 YI08 YI00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YG0n YM05.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YC4a YC1f YC4b.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {L : ptable asym} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
#[local] Notation VAL := (@pa_val _ L PI).
Lemma st_ok_pi_region_nthX : forall E ss ms i r,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)). Qed.
End c.
End a.
Ltac xcarry GP HFr rng :=
lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m) (mrestrict _ ?m') =>
lazymatch type of GP with garr8 ?sg _ ?p ?L =>
let GPn := fresh "GPc" in
assert (GPn : garr8 sg (mrestrict H m') p L);
[ apply (garr8_aview_kept sg H H m m'); [|exact GP]; intros xa_ Hxa_;
apply (kept_of_frame (segs:=sg) _ _ _ _ _ (fun _ => False) HFr ltac:(intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_; destruct Hin_)); [rng xa_ Hxa_ | tauto]
| clear GP; rename GPn into GP ]
end end.
Ltac xcarryw GP HFr Zs ev :=
lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m) (mrestrict _ ?m') =>
lazymatch type of GP with garr8 ?sg _ ?p ?L =>
let GPn := fresh "GPc" in
assert (GPn : garr8 sg (mrestrict H m') p L);
[ apply (garr8_aview_kept sg H H m m'); [|exact GP]; intros xa_ Hxa_;
apply (kept_of_frame (segs:=sg) _ _ _ _ _ Zs HFr
ltac:(intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; lia|]); destruct Hin_)); lia
| clear GP; rename GPn into GP ]
end end.
Ltac xcarryv V HFr Zs ev :=
lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m) (mrestrict _ ?m') =>
lazymatch type of V with val_mem ?sg _ ?p ?n ?v =>
let Vn := fresh "Vc" in
assert (Vn : val_mem sg (mrestrict H m') p n v);
[ apply (val_mem_aview_kept_x sg H H m m'); [|exact V]; intros xa_ Hxa_;
apply (kept_of_frame (segs:=sg) _ _ _ _ _ Zs HFr
ltac:(intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; lia|]); destruct Hin_)); cbn in Hxa_; lia
| clear V; rename Vn into V ]
end end.
Ltac xregbyte V HS idx b v Hbu dv :=
lazymatch type of HS with
| st_ok_pi ?sg _ ?Ex ?ss (restrict ?H ?msx) =>
assert (V : val_mem sg (mrestrict H (ms_mem msx)) (b + 0) (N.to_nat 1) v);
[ eapply (@field_of_region sg Ex _ _ b _ 0 1 0 1 0 1%N _ v (st_ok_pi_region_nthX Ex ss (restrict H msx) idx _ HS eq_refl));
[ first [exact Hbu | rewrite ?ew_ewset_other by lia; exact Hbu] | left; reflexivity | dv | lia | cbn; lia ]
| ]
| st_ok ?sg ?Ex ?ss (restrict ?H ?msx) =>
assert (V : val_mem sg (mrestrict H (ms_mem msx)) (b + 0) (N.to_nat 1) v);
[ eapply (@field_of_region sg Ex _ _ b _ 0 1 0 1 0 1%N _ v (@st_ok_region_nth _ sg Ex ss (restrict H msx) idx _ HS eq_refl));
[ first [exact Hbu | rewrite ?ew_ewset_other by lia; exact Hbu] | left; reflexivity | dv | lia | cbn; lia ]
| ]
end.
