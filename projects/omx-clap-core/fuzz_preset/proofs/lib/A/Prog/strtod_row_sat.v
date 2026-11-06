(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the three non-call-row premises of lib/A/Prog/strtod_row.v's strtod_row_aj_A hold at image
   A's instance record lib/A/AD2l.v TfibB (by vm_compute), and strtod_row_aj_A at that record without them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK04 YK0o YA0i YA0n YG00 YG0a YG01 YG0d YG0f YG0n YG0p YG0v YI16 YM05 YI00 YI04 YCbq YCbqG FCiface YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import strtod_c strtod_row.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Open Scope Z_scope.

Lemma strtod_sat_not_in_zr_A : forall a l,
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r))%bool l = false -> ~ Exists (in_zr a) l.
Proof.
intros a l H HE. apply Exists_exists in HE as (r & Hr & Hin). unfold in_zr in Hin. destruct Hin as [H1 H2].
assert (T : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r))%bool l = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro.
  split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2]. }
rewrite H in T. discriminate.
Qed.

Theorem strtod_sat_tp_A : as_tp AD2l.TfibB = STRTOD_TP.
Proof. vm_compute. reflexivity. Qed.

Theorem strtod_sat_errno_A : as_errno AD2l.TfibB = STRTOD_ERRNO.
Proof. vm_compute. reflexivity. Qed.

Theorem strtod_sat_errno_free_b_A :
  forallb (fun k => negb (existsb
    (fun r => (fst r <=? as_errno AD2l.TfibB + k) && (as_errno AD2l.TfibB + k <? fst r + snd r))%bool
    (as_owned_static AD2l.TfibB))) [0; 1; 2; 3] = true.
Proof. vm_compute. reflexivity. Qed.

Theorem strtod_sat_owned_A : forall a, as_errno AD2l.TfibB <= a < as_errno AD2l.TfibB + 4 ->
  ~ Exists (in_zr a) (as_owned_static AD2l.TfibB).
Proof.
intros a Ha. apply strtod_sat_not_in_zr_A.
assert (Hk : In (a - as_errno AD2l.TfibB) [0; 1; 2; 3]) by (cbv [In]; lia).
pose proof (proj1 (forallb_forall _ _) strtod_sat_errno_free_b_A (a - as_errno AD2l.TfibB) Hk) as Hb.
cbv beta in Hb. replace (as_errno AD2l.TfibB + (a - as_errno AD2l.TfibB)) with a in Hb by lia.
apply negb_true_iff in Hb. exact Hb.
Qed.

Theorem strtod_row_aj_A_at_TfibB : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {HL : Z} (SK : YI16.sink_head)
  (PST : list (Z * Z)) (ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop),
  AR_laws_x rsegs AD2l.TfibB ARx HL ->
  forall STKS sm txt_ok, STRTOD_K <= STKS ->
  (forall txt, txt_ok txt -> Forall (fun c => FmtFp_facts3.is_numch c = true) txt /\ Z.of_nat (length txt) < 2 ^ 30) ->
  (forall txt bits c, txt_ok txt -> strtod_model txt = Some (bits, c) -> sm txt = Some (bits, c)) ->
  aj_strtod_row (SK := SK) rsegs AD2l.TfibB ARx strtod_img_A PST STRTOD STKS sm txt_ok.
Proof.
intros fx rc HL SK PST ARx LAWS STKS sm txt_ok HK HTX HSM.
exact (@strtod_row_aj_A fx rc HL SK AD2l.TfibB PST ARx LAWS strtod_sat_tp_A strtod_sat_errno_A strtod_sat_owned_A
  STKS sm txt_ok HK HTX HSM).
Qed.
