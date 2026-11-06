(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame DriverCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvData UDrvMain UDrvCall UbStdioDefs UbExitBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac bvlit := vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity).

(* [comment removed for export] *)
Definition untracked (c : tree bval) (o : Z) (n : nat) : bool :=
  forallb (fun j => match tget (okey (o + Z.of_nat j)) c with None => true | Some _ => false end) (seq 0 n).

Lemma untracked_spec : forall c o n, untracked c o n = true -> forall j, (j < n)%nat -> tget (okey (o + Z.of_nat j)) c = None.
Proof.
  intros c o n H j Hj. unfold untracked in H. rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)). destruct (tget (okey (o + Z.of_nat j)) c); [discriminate | reflexivity].
Qed.

Definition Z8 : list bval := repeat (BK 0) 8.
(* [comment removed for export] *)
Definition bks (v : Z) (n : nat) : list bval := map (fun j => BK (Z.land (Z.shiftr v (8 * Z.of_nat j)) 255)) (seq 0 n).

(* [comment removed for export] *)
Definition c5_clean (c5 : tree bval) : Prop :=
  get_bytes c5 40 8 = Some Z8 /\ get_bytes c5 56 8 = Some Z8 /\ get_bytes c5 8 8 = Some Z8 /\ get_bytes c5 16 8 = Some Z8 /\
  untracked c5 140 4 = true.

Section ExitGen.
Variable sp0 tid : word.
Hypothesis SL : 0x7fff80000000 <= bv_unsigned sp0.
Hypothesis SH : bv_unsigned sp0 <= 0x800000000000.
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.

#[using="SL SH Htid"] Theorem exit_pre_gen : forall E3 L ms3 model (csp : Z) (i0 i3 i5 i6 i7 i21 : nat) (o0 : Z) (c5 c7 : tree bval) (k7 : rkind),
  sden PSEGS E3 L ms3 -> lden E3 SP0 = sp0 -> lden E3 T = tid -> -65536 + 144 <= csp <= 0 ->
  exit_glob (ms_mem ms3) -> m_halted model = None -> m_vm_lazy model = [] ->
  rget (s_regs L) (rkey 2) = laddc SP0 csp -> rget (s_regs L) (rkey 4) = lconst 0x77990 ->
  rget (s_regs L) (rkey 10) = lconst 2 ->
  nth_error (s_rgs L) i3 = Some (RGz (lconst 0x65a18) 344 RO TEmpty) ->
  nth_error (s_rgs L) i5 = Some (RGz (lconst 0x66bd8) 232 RI c5) -> c5_clean c5 ->
  nth_error (s_rgs L) i6 = Some (RGz (lconst 0x66cc8) 232 RI TEmpty) ->
  nth_error (s_rgs L) i7 = Some (RGz (lconst 0x778e8) 8 k7 c7) -> get_bytes c7 0 4 = Some (bvs_of T 4) ->
  nth_error (s_rgs L) i21 = Some (RGz (lconst 0x979d8) 296 RI TEmpty) ->
  frame_in E3 L i0 o0 144 (bv_unsigned sp0 + csp - 144) ->
  exit_pre (ms_regs ms3) (ms_mem ms3) model (Z_to_bv 64 2) [].
Proof. LiaFast.lf_pins (fun (SL SH Htid : LiaFast.U) => LiaFast.u0).
  intros E3 L ms3 model csp i0 i3 i5 i6 i7 i21 o0 c5 c7 k7 Hd3 HSP HT Hcsp EG Hh Hl G2 G4 G10 N3 N5 C5 N6 N7 C7 N21 FRM.
  assert (Q2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (bv_unsigned sp0 + csp)).
  { rewrite (getr_leaf PSEGS E3 L ms3 2 (laddc SP0 csp) Hd3 G2). rewrite lden_laddc, HSP. reflexivity. }
  assert (Q4 : getr (ms_regs ms3) 4 = Z_to_bv 64 0x77990) by exact (getr_leaf_c PSEGS E3 L ms3 4 _ Hd3 G4).
  assert (Q10 : getr (ms_regs ms3) 10 = Z_to_bv 64 2) by exact (getr_leaf_c PSEGS E3 L ms3 10 _ Hd3 G10).
  destruct EG as (G1 & Gfa & Gc & Gn & Go & Gi & Gso & Gse).
  (* [comment removed for export] *)
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N3) as HR3.
  assert (GOT : forall o, 0 <= o -> o + 8 <= 344 ->
            rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x65a18 + o)) 8 = rdn PSEGS (fun _ => None) (Z_to_bv 64 (0x65a18 + o)) 8).
  { intros o Ho1 Ho2.
    pose proof (rg_rdn_img PSEGS E3 _ _ o 8 HR3 (or_introl eq_refl) Ho1 ltac:(rsz_simpl; lia)) as X.
    cbn [RGz rg_base] in X. rewrite u_lconst in X by lia. apply X. intros j Hj. apply tget_empty. }
  (* [comment removed for export] *)
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N21) as HR21.
  assert (ATX : forall o n, 0 <= o -> o + Z.of_nat n <= 296 ->
            rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x979d8 + o)) n = rdn PSEGS (fun _ => None) (Z_to_bv 64 (0x979d8 + o)) n).
  { intros o n Ho1 Ho2.
    pose proof (rg_rdn_img PSEGS E3 _ _ o n HR21 (or_intror eq_refl) Ho1 ltac:(rsz_simpl; lia)) as X.
    cbn [RGz rg_base] in X. rewrite u_lconst in X by lia. apply X. intros j Hj. apply tget_empty. }
  (* [comment removed for export] *)
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N5) as HR5.
  destruct C5 as (Z40 & Z56 & Z08 & Z16 & U140).
  assert (ZT5 : forall o, get_bytes c5 o 8 = Some Z8 -> 0 <= o ->
            rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + o)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
  { intros o Hg Ho. pose proof (rg_rdn_gb PSEGS E3 _ _ o 8 Z8 HR5 Ho Hg) as X. cbn [RGz rg_base] in X.
    rewrite u_lconst in X by lia. rewrite X. bvlit. }
  assert (LK5 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66bd8 + 140)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))).
  { pose proof (rg_rdn_img PSEGS E3 _ _ 140 4 HR5 (or_intror eq_refl) ltac:(lia) ltac:(rsz_simpl; lia)) as X.
    cbn [RGz rg_base] in X. rewrite u_lconst in X by lia. rewrite X; [bvlit|].
    intros j Hj. exact (untracked_spec _ _ _ U140 j Hj). }
  (* [comment removed for export] *)
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N6) as HR6.
  assert (ZT6 : forall o, 0 <= o -> o + 8 <= 232 ->
            rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66cc8 + o)) 8 = rdn PSEGS (fun _ => None) (Z_to_bv 64 (0x66cc8 + o)) 8).
  { intros o Ho1 Ho2.
    pose proof (rg_rdn_img PSEGS E3 _ _ o 8 HR6 (or_intror eq_refl) Ho1 ltac:(rsz_simpl; lia)) as X.
    cbn [RGz rg_base] in X. rewrite u_lconst in X by lia. apply X. intros j Hj. apply tget_empty. }
  assert (LK6 : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x66cc8 + 140)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))).
  { pose proof (rg_rdn_img PSEGS E3 _ _ 140 4 HR6 (or_intror eq_refl) ltac:(lia) ltac:(rsz_simpl; lia)) as X.
    cbn [RGz rg_base] in X. rewrite u_lconst in X by lia. rewrite X; [bvlit|]. intros j Hj. apply tget_empty. }
  (* [comment removed for export] *)
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N7) as HR7.
  assert (TD : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x778e8 + 0)) 4 = Some (word_to_le_bytes 4 tid)).
  { pose proof (rg_rdn_gb PSEGS E3 _ _ 0 4 (bvs_of T 4) HR7 ltac:(lia) C7) as X. cbn [RGz rg_base] in X.
    rewrite u_lconst in X by lia. rewrite X, bvs_of_den_lin, HT. reflexivity. }
  pose proof (frame_in_store_ok E3 L ms3 i0 o0 144 _ Hd3 FRM ltac:(lia)) as SOK.
  exists (Z_to_bv 64 (bv_unsigned sp0 + csp)), (Z_to_bv 64 0x77990), (bv_unsigned tid), (Z_to_bv 64 0), (Z_to_bv 64 0).
  split; [|split; [exact Hh|split; [exact Hl|]]].
  - constructor.
    + exact Q2.
    + exact Q4.
    + exact Q10.
    + rewrite u_small64 by (unfold two64; lia). lia.
    + rewrite u_small64 by (unfold two64; lia). lia.
    + rewrite u_small64 by (unfold two64; lia). exact SOK.
    + vm_compute. intros Hc; discriminate Hc.
    + vm_compute. intros Hc; discriminate Hc.
    + lia.
    + rewrite Z_to_bv_bv_unsigned. replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0x77990) - 168)) with (Z_to_bv 64 (0x778e8 + 0)) by reflexivity.
      exact TD.
    + exact G1.
    + replace (Z_to_bv 64 0x65b60) with (Z_to_bv 64 (0x65a18 + 328)) by reflexivity. rewrite GOT by lia. bvlit.
    + replace (Z_to_bv 64 0x65b68) with (Z_to_bv 64 (0x65a18 + 336)) by reflexivity. rewrite GOT by lia. bvlit.
    + exact Gfa.
    + exact Gc.
    + replace (Z_to_bv 64 0x65a48) with (Z_to_bv 64 (0x65a18 + 48)) by reflexivity. rewrite GOT by lia. bvlit.
    + replace (Z_to_bv 64 0x65a50) with (Z_to_bv 64 (0x65a18 + 56)) by reflexivity. rewrite GOT by lia. bvlit.
    + split; [exact Gn|split; [exact Go|split; [exact Gi|split; [exact Gso|exact Gse]]]].
    + split; [exact LK5|]. split; [exact (ZT5 40 Z40 ltac:(lia))|]. split; [exact (ZT5 56 Z56 ltac:(lia))|].
      split; [exact (ZT5 8 Z08 ltac:(lia))|exact (ZT5 16 Z16 ltac:(lia))].
    + (* [comment removed for export] *)
      replace (Z_to_bv 64 0x979dc) with (Z_to_bv 64 (0x979d8 + 4)) by reflexivity. rewrite (ATX 4 4%nat) by lia. bvlit.
    + (* [comment removed for export] *)
      left. unfold atx_idle.
      replace (Z_to_bv 64 0x979e8) with (Z_to_bv 64 (0x979d8 + 16)) by reflexivity. rewrite (ATX 16 8%nat) by lia. bvlit.
  - left. split; [reflexivity|]. exists (Z_to_bv 64 0), (Z_to_bv 64 0).
    split; [exact LK6|]. split; [rewrite ZT6 by lia; bvlit|]. split; [rewrite ZT6 by lia; bvlit|].
    split; [rewrite ZT6 by lia; bvlit|rewrite ZT6 by lia; bvlit].
Qed.
End ExitGen.

(* [comment removed for export] *)
Definition RDF : region := RGz lc0 0 RW TEmpty.
Definition rgn (L : sst) (i : nat) : region := nth i (s_rgs L) RDF.

Lemma rgn_eq : forall L i, (i < length (s_rgs L))%nat -> nth_error (s_rgs L) i = Some (rgn L i).
Proof. intros L i H. unfold rgn. apply nth_error_nth'. exact H. Qed.

Lemma rdn_trk_c : forall E L ms i c o n bvs, sden PSEGS E L ms -> (i < length (s_rgs L))%nat ->
  rg_base (rgn L i) = lconst c -> 0 <= c < 2 ^ 64 -> 0 <= o ->
  get_bytes (rg_cont (rgn L i)) o n = Some bvs ->
  rdn PSEGS (ms_mem ms) (Z_to_bv 64 (c + o)) n = Some (map (bden E) bvs).
Proof.
  intros E L ms i c o n bvs Hd Hi Hb Hc Ho Hg. pose proof (sden_rg _ _ _ _ _ _ Hd (rgn_eq L i Hi)) as HR.
  pose proof (rg_rdn_gb PSEGS E _ _ o n bvs HR Ho Hg) as X. rewrite Hb, u_lconst in X by lia. exact X.
Qed.

Lemma rdn_img_c : forall E L ms i c o n, sden PSEGS E L ms -> (i < length (s_rgs L))%nat ->
  rg_base (rgn L i) = lconst c -> 0 <= c < 2 ^ 64 -> (rg_kind (rgn L i) = RO \/ rg_kind (rgn L i) = RI) -> 0 <= o ->
  o + Z.of_nat n <= rsz E (rgn L i) -> untracked (rg_cont (rgn L i)) o n = true ->
  rdn PSEGS (ms_mem ms) (Z_to_bv 64 (c + o)) n = rdn PSEGS (fun _ => None) (Z_to_bv 64 (c + o)) n.
Proof.
  intros E L ms i c o n Hd Hi Hb Hc Hk Ho Hn Hu. pose proof (sden_rg _ _ _ _ _ _ Hd (rgn_eq L i Hi)) as HR.
  pose proof (rg_rdn_img PSEGS E _ _ o n HR Hk Ho Hn) as X. rewrite Hb, u_lconst in X by lia. apply X.
  intros j Hj. exact (untracked_spec _ _ _ Hu j Hj).
Qed.

Section SpRd.
Variable sp0 : word.
Hypothesis SL : 0x7fff80000000 <= bv_unsigned sp0.
Hypothesis SH : bv_unsigned sp0 <= 0x800000000000.

#[using="SL SH"] Lemma rdn_trk_sp : forall E L ms i c o n bvs, sden PSEGS E L ms -> (i < length (s_rgs L))%nat ->
  rg_base (rgn L i) = laddc SP0 c -> lden E SP0 = sp0 -> -65536 <= c <= 0 -> 0 <= o ->
  get_bytes (rg_cont (rgn L i)) o n = Some bvs ->
  rdn PSEGS (ms_mem ms) (Z_to_bv 64 (bv_unsigned sp0 + c + o)) n = Some (map (bden E) bvs).
Proof. LiaFast.lf_pins (fun (SL SH : LiaFast.U) => LiaFast.u0).
  intros E L ms i c o n bvs Hd Hi Hb HS Hc Ho Hg. pose proof (sden_rg _ _ _ _ _ _ Hd (rgn_eq L i Hi)) as HR.
  pose proof (rg_rdn_gb PSEGS E _ _ o n bvs HR Ho Hg) as X. rewrite Hb, lden_laddc, HS, u_small64 in X by (unfold two64; lia). exact X.
Qed.

#[using="SL SH"] Lemma frame_sp : forall E L i c o n a, (i < length (s_rgs L))%nat -> rg_base (rgn L i) = laddc SP0 c -> lden E SP0 = sp0 ->
  -65536 <= c <= 0 -> wkind (rg_kind (rgn L i)) = true -> 0 <= o -> o + n <= rsz E (rgn L i) -> bv_unsigned sp0 + c + o = a ->
  frame_in E L i o n a.
Proof. LiaFast.lf_pins (fun (SL SH : LiaFast.U) => LiaFast.u0).
  intros E L i c o n a Hi Hb HS Hc Hk Ho Hn Ha. exists (rgn L i). split; [exact (rgn_eq L i Hi)|].
  rewrite Hb, lden_laddc, HS, u_small64 by (unfold two64; lia). split; [exact Ha|]. split; [exact Hk|]. lia.
Qed.
End SpRd.
