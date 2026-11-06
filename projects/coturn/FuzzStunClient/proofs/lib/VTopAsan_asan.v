(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import FContract.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VParamsCheck VCert VItab VItab_asan VContract VDriver
     VState2 VCert2 VContract2 VDriver2 VGamma2 VSound2 VSoundAll2 VSoundClosed2 FPA_asan VGenv_asan VTopAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VParamsCheckFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma fa_genv_ok_asan : fa_genv_prop (genv_asan true) FPA_asan.
Proof.
  unfold fa_genv_prop. cbv zeta.
  change (ge2_P0 (genv_asan true)) with P0_asan. change (p1 P0_asan) with P1_asan.
  change (ge2_tp (genv_asan true)) with A_tp. change (ge2_CI (genv_asan true)) with CI_asan.
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

Lemma segs_wr_readable_asan : segs_wr_readable SEGSA = true.
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

Lemma segs_top_asan : forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) (fa_imgend FPA_asan)) SEGSA = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seghi_asan (a : word) : fa_imgend FPA_asan <= bv_unsigned a -> seg_rom SEGSA a = None.
Proof.
  intros Ha. unfold seg_rom, memory_read.
  rewrite (find_segment_none _ _ _ (fa_imgend FPA_asan)); [reflexivity| |exact Ha|lia].
  intros seg Hs. pose proof segs_top_asan as T. rewrite forallb_forall in T. specialize (T _ Hs). apply Z.leb_le in T. exact T.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac gnd := vm_compute; first [reflexivity | discriminate | (left; discriminate) | (right; discriminate) | (left; reflexivity) | (right; reflexivity)].

Lemma P0_asan_ok : params_ok2 SEGSA P0_asan.
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

Lemma genv_asan_ok rom :
  ctab_ok2 SEGSA (genv_asan true) rom -> genv_ok2 SEGSA (genv_asan true) rom.
Proof.
  intros CT. split; [reflexivity|]. split; [exact itab_asan_ok|]. split; [exact P0_asan_ok|exact CT].
Qed.

(* [comment removed for export] *)
Theorem F_contract_asan_of_certs (CS : list vcert2) :
  (forall rom, ctab_ok2 SEGSA (genv_asan true) rom) ->
  Forall (fun C => check_cert2 (genv_asan true) C = R2Ok) CS ->
  roots_ok2 FPA_asan (concat CS) = true ->
  F_contract_asan SEGSA FPA_asan.
Proof.
  intros CT CHK ROK.
  apply (F_contract_asan_of_roots SEGSA (genv_asan true) FPA_asan fa_genv_ok_asan segs_wr_readable_asan seghi_asan (concat CS)); [|exact ROK].
  intros rom U HU _. apply in_concat in HU as (C & HC & HU). rewrite Forall_forall in CHK.
  pose proof (check_cert2_sound_closed SEGSA (genv_asan true) rom C (genv_asan_ok rom (CT rom)) (CHK C HC)) as F.
  rewrite Forall_forall in F. exact (F U HU).
Qed.

(* [comment removed for export] *)
Theorem F_contract_asan_of_chunks (CSS : list (list (list vunit2))) :
  (forall rom, ctab_ok2 SEGSA (genv_asan true) rom) ->
  Forall (fun chunks => check_chunks2 (genv_asan true) [] chunks) CSS ->
  roots_ok2 FPA_asan (concat (map (@concat vunit2) CSS)) = true ->
  F_contract_asan SEGSA FPA_asan.
Proof.
  intros CT CHK ROK.
  apply (F_contract_asan_of_roots SEGSA (genv_asan true) FPA_asan fa_genv_ok_asan segs_wr_readable_asan seghi_asan (concat (map (@concat vunit2) CSS))); [|exact ROK].
  intros rom U HU _. apply in_concat in HU as (C & HC & HU). apply in_map_iff in HC as (chunks & <- & Hch). rewrite Forall_forall in CHK.
  pose proof (check_chunks2_sound SEGSA (genv_asan true) rom (genv_asan_ok rom (CT rom)) chunks [] (Forall_nil _) (CHK chunks Hch)) as F.
  cbn [app] in F. rewrite Forall_forall in F. exact (F U HU).
Qed.

(* [comment removed for export] *)
Theorem F_contract_asan_of_chunksb (CSS : list (list (list vunit2))) :
  (forall rom, ctab_ok2 SEGSA (genv_asan true) rom) ->
  Forall (fun chunks => check_chunks2b (genv_asan true) [] chunks = true) CSS ->
  roots_ok2 FPA_asan (concat (map (@concat vunit2) CSS)) = true ->
  F_contract_asan SEGSA FPA_asan.
Proof.
  intros CT CHK ROK. apply (F_contract_asan_of_chunks CSS CT); [|exact ROK].
  apply Forall_impl with (2 := CHK). intros chunks H. exact (check_chunks2b_sound _ _ _ H).
Qed.
