(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import FContract.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VParamsCheck VCert VItab VItab_both VContract VDriver
     VState2 VCert2 VContract2 VDriver2 VGamma2 VSound2 VSoundAll2 VSoundClosed2 FPA_both VGenv_both VTopAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VParamsCheckFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma fa_genv_ok_both : fa_genv_prop (genv_both true) FPA_both.
Proof.
  unfold fa_genv_prop. cbv zeta.
  change (ge2_P0 (genv_both true)) with P0_both. change (p1 P0_both) with P1_both.
  change (ge2_tp (genv_both true)) with A_tp. change (ge2_CI (genv_both true)) with CI_both.
  (* [comment removed for export] *)
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  (* [comment removed for export] *) split; [reflexivity|].
  (* [comment removed for export] *) split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|]. split; [vm_compute; reflexivity|].
  (* [comment removed for export] *) split; [intros r Hr; exists r; split; [exact Hr|clear; lia]|].
  (* [comment removed for export] *) split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  (* [comment removed for export] *) split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  (* [comment removed for export] *) split; [vm_compute; reflexivity|]. split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|].
  (* [comment removed for export] *) split; [vm_compute; reflexivity|]. split; [vm_compute; split; [discriminate|reflexivity]|].
  (* [comment removed for export] *) split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|].
  (* [comment removed for export] *) split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|].
  (* [comment removed for export] *) split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|].
  (* [comment removed for export] *) split.
  { intros c Hc. cbn in Hc. repeat (destruct Hc as [<-|Hc]; [vm_compute; repeat split; discriminate || reflexivity|]). destruct Hc. }
  (* [comment removed for export] *) split.
  { intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; repeat split; discriminate || reflexivity|]). destruct Hr. }
  (* [comment removed for export] *) split.
  { intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; split; discriminate|]). destruct Hr. }
  (* [comment removed for export] *) split; [cbn; repeat (first [left; reflexivity | right])|].
  split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|].
  (* [comment removed for export] *)
  split; [reflexivity|]. split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|].
  split. { intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; discriminate|]). destruct Hr. }
  split. { intros c Hc. cbn in Hc. repeat (destruct Hc as [<-|Hc]; [vm_compute; discriminate|]). destruct Hc. }
  split. { intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; discriminate|]). destruct Hr. }
  vm_compute. discriminate.
Qed.

Lemma segs_wr_readable_both : segs_wr_readable SEGSB = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma find_segment_none segs addr n bound :
  (forall seg, In seg segs -> Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= bound) ->
  bound <= addr -> 0 < n -> find_segment segs addr n = None.
Proof.
  induction segs as [|seg rest IH]; intros Hb Ha Hn; cbn [find_segment]; [reflexivity|].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) addr); cbn [andb].
  - destruct (Z.leb_spec (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))).
    + exfalso. specialize (Hb seg (or_introl eq_refl)). lia.
    + apply IH; auto. intros s Hs. apply Hb. right; exact Hs.
  - apply IH; auto. intros s Hs. apply Hb. right; exact Hs.
Qed.

Lemma segs_top_both : forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) (fa_imgend FPA_both)) SEGSB = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seghi_both (a : word) : fa_imgend FPA_both <= bv_unsigned a -> seg_rom SEGSB a = None.
Proof.
  intros Ha. unfold seg_rom, memory_read.
  rewrite (find_segment_none _ _ _ (fa_imgend FPA_both)); [reflexivity| |exact Ha|lia].
  intros seg Hs. pose proof segs_top_both as T. rewrite forallb_forall in T. specialize (T _ Hs). apply Z.leb_le in T. exact T.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac gnd := vm_compute; first [reflexivity | discriminate | (left; discriminate) | (right; discriminate) | (left; reflexivity) | (right; reflexivity)].

Lemma P0_both_ok : params_ok2 SEGSB P0_both.
Proof.
  unfold params_ok2.
  split; [apply VParamsCheckFast.params_check_soundF'; vm_cast_no_check (@eq_refl bool true) (* [comment removed for export] *)|].
  split; [gnd|]. split; [gnd|].
  split.
  { intros a w v Hin. cbn in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <- <-; split; [gnd|]; split; [gnd|]; split; [gnd|]; intros c [<-|[<-|[]]]; gnd|]).
    destruct Hin. }
  split.
  { intros c Hin f Hf. cbn in Hin. cbn in Hf.
    destruct Hf as [<-|[<-|[]]]; repeat (destruct Hin as [<-|Hin]; [gnd|]); destruct Hin. }
  split; [intros i lo hi []|].
  split; [intros _; split; [reflexivity|]; intros c [<-|[<-|[]]]; gnd|].
  split; [intros H; discriminate|].
  split; [vm_compute; reflexivity|].
  (* [comment removed for export] *)
  intros _. split; [split; vm_compute; discriminate|]. split.
  { intros c [<-|[<-|[]]]; gnd. }
  split.
  { intros a w v Hin. cbn in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <- <-; gnd|]). destruct Hin. }
  intros lo hi Hin. cbn in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; gnd|]). destruct Hin.
Qed.

Lemma genv_both_ok rom :
  ctab_ok2 SEGSB (genv_both true) rom -> genv_ok2 SEGSB (genv_both true) rom.
Proof.
  intros CT. split; [reflexivity|]. split; [exact itab_both_ok|]. split; [exact P0_both_ok|exact CT].
Qed.

(* [comment removed for export] *)
Theorem F_contract_asan_of_certs (CS : list vcert2) :
  (forall rom, ctab_ok2 SEGSB (genv_both true) rom) ->
  Forall (fun C => check_cert2 (genv_both true) C = R2Ok) CS ->
  roots_ok2 FPA_both (concat CS) = true ->
  F_contract_asan SEGSB FPA_both.
Proof.
  intros CT CHK ROK.
  apply (F_contract_asan_of_roots SEGSB (genv_both true) FPA_both fa_genv_ok_both segs_wr_readable_both seghi_both (concat CS)); [|exact ROK].
  intros rom U HU _. apply in_concat in HU as (C & HC & HU). rewrite Forall_forall in CHK.
  pose proof (check_cert2_sound_closed SEGSB (genv_both true) rom C (genv_both_ok rom (CT rom)) (CHK C HC)) as F.
  rewrite Forall_forall in F. exact (F U HU).
Qed.

(* [comment removed for export] *)
Theorem F_contract_asan_of_chunks (CSS : list (list (list vunit2))) :
  (forall rom, ctab_ok2 SEGSB (genv_both true) rom) ->
  Forall (fun chunks => check_chunks2 (genv_both true) [] chunks) CSS ->
  roots_ok2 FPA_both (concat (map (@concat vunit2) CSS)) = true ->
  F_contract_asan SEGSB FPA_both.
Proof.
  intros CT CHK ROK.
  apply (F_contract_asan_of_roots SEGSB (genv_both true) FPA_both fa_genv_ok_both segs_wr_readable_both seghi_both (concat (map (@concat vunit2) CSS))); [|exact ROK].
  intros rom U HU _. apply in_concat in HU as (C & HC & HU). apply in_map_iff in HC as (chunks & <- & Hch). rewrite Forall_forall in CHK.
  pose proof (check_chunks2_sound SEGSB (genv_both true) rom (genv_both_ok rom (CT rom)) chunks [] (Forall_nil _) (CHK chunks Hch)) as F.
  cbn [app] in F. rewrite Forall_forall in F. exact (F U HU).
Qed.

(* [comment removed for export] *)
Theorem F_contract_asan_of_chunksb (CSS : list (list (list vunit2))) :
  (forall rom, ctab_ok2 SEGSB (genv_both true) rom) ->
  Forall (fun chunks => check_chunks2b (genv_both true) [] chunks = true) CSS ->
  roots_ok2 FPA_both (concat (map (@concat vunit2) CSS)) = true ->
  F_contract_asan SEGSB FPA_both.
Proof.
  intros CT CHK ROK. apply (F_contract_asan_of_chunks CSS CT); [|exact ROK].
  apply Forall_impl with (2 := CHK). intros chunks H. exact (check_chunks2b_sound _ _ _ H).
Qed.
