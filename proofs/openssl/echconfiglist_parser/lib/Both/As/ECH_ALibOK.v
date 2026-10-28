(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainCells.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_Iface ECH_ATraces ECH_ALib
     AS_InstDefs AS_InstTR AS_InstanceKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma K_libx0 : forall iv, In iv (al_LIBX0 ECHL) -> img_check (fst iv) (snd iv) = true.
Proof.
  assert (E : forallb (fun iv : Z * Z => img_check (fst iv) (snd iv)) LIBX0 = true) by (vm_compute; reflexivity).
  intros iv Hin. cbn [al_LIBX0 ECHL] in Hin. rewrite forallb_forall in E. exact (E iv Hin).
Qed.

(* [comment removed for export] *)
Lemma LIBX_wf : Forall (fun iv : Z * Z => fst iv < snd iv) LIBXT.
Proof. unfold LIBXT, LIBXP, LIBX, LIBX0, LIBXW, A_next_key, A_key_lock. cbn [app]. repeat (constructor; [cbn; lia|]). constructor. Qed.

Definition in_win4_b (iv : Z * Z) : bool :=
  let '(lo, hi) := iv in
  ((0x5ed1a0 <=? lo) && (hi <=? 0x5edca8)) || ((0xbdcf70 <=? lo) && (hi <=? 0xbe1be8)) || ((0xbe1bf0 <=? lo) && (hi <=? 0xbe1c38))
  || ((0xc03040 <=? lo) && (hi <=? 0xc03570))
  || ((0xc02bf8 <=? lo) && (hi <=? 0xc03010)) || ((0x5edf88 <=? lo) && (hi <=? 0x5edf90)).
Lemma in_win4_all : forallb in_win4_b LIBXT = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma TRLEN : (length (trlist_of (all_demands ECHL LIB_TRACES)) <= TRCAP)%nat.
Proof. vm_compute. lia. Qed.
Lemma DOK : demands_okb (all_demands ECHL LIB_TRACES) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section OK.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma musl0_of_amusl0 : forall m, amusl0 m -> musl0 m.
  Proof.
    intros m HM. unfold amusl0, AMUSL0_CELLS in HM.
    apply Forall_cons_iff in HM as [H1 HM]. apply Forall_cons_iff in HM as [H2 HM]. apply Forall_cons_iff in HM as [H3 HM]. apply Forall_inv in HM.
    cbn [fst snd] in H1, H2, H3, HM. unfold musl0, A_keys, A_keys0_val, A_next_key, A_key_lock, A_td_tsd_used. exact (conj H1 (conj H2 (conj H3 HM))).
  Qed.

  Lemma alo_libx_proofT : forall a, rin_ivs LIBXT a -> alibx_ok a.
  Proof.
    intros a Ha. pose proof in_win4_all as W. rewrite forallb_forall in W.
    revert Ha W. generalize LIBXT. intros X. induction X as [|[lo hi] X IH]; intros Ha W; [destruct Ha|].
    destruct Ha as [Ha|Ha].
    - specialize (W (lo, hi) (or_introl eq_refl)). cbn [fst snd] in Ha. unfold in_win4_b in W.
      repeat rewrite Bool.orb_true_iff in W. repeat rewrite Bool.andb_true_iff in W. rewrite !Z.leb_le in W.
      unfold alibx_ok. destruct W as [[[[[W|W]|W]|W]|W]|W]; lia.
    - apply IH; [exact Ha|]. intros x Hx. apply W. right. exact Hx.
  Qed.
  (* [comment removed for export] *)
  Lemma alo_libx_proof : forall a, rin_ivs LIBX a -> alibx_ok a.
  Proof. intros a Ha. apply alo_libx_proofT. apply LIBX_sub_LIBXT. exact Ha. Qed.

  Lemma alo_cost_laws : forall H, asan_rt_hyps H -> cost_laws H.
  Proof. intros H HH. exact (ah_costs H HH). Qed.

  Theorem ECHL_ok : alib_ok ECHL.
  Proof.
    constructor; cbn [al_LIBST al_fresh al_is_fresh al_LIBX0 al_LIBX al_frames al_cost al_st ECHL].
    - (* [comment removed for export] *) intros m P M. apply LIBST_fresh_intro; [exact P| apply musl0_of_amusl0; exact M].
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) intros st LIB m HL E. exact (LIBST_nil st LIB m HL E).
    - (* [comment removed for export] *) intros st LIB m m' HL AG. eapply LIBST_frame; [exact HL|]. apply magree_of_amagreeT. exact AG.
    - (* [comment removed for export] *) intros a Ha. apply LIBX_sub_LIBXT. exact (LIBX0_sub_LIBX a Ha).
    - (* [comment removed for export] *) exact alo_libx_proofT.
    - (* [comment removed for export] *) exact LIBX_wf.
    - (* [comment removed for export] *) intros st LIB m HL. rewrite <- A_global_cleanup_eq. exact (LIBST_cleanup_byte st LIB m HL).
    - (* [comment removed for export] *) intros H n HH Hn. unfold acost. destruct (alo_cost_laws H HH) as (C1 & _ & C3 & _).
      pose proof (C1 ACOST_BYTES ltac:(unfold ACOST_BYTES; lia)). pose proof (C3 ACOST_BYTES ltac:(unfold ACOST_BYTES; lia)). lia.
    - (* [comment removed for export] *) intros H n n' HH Hn. unfold acost. lia.
    - (* [comment removed for export] *) unfold AL_FRAMES, AFS_MAXLIVE. lia.
  Qed.
End OK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma LT : forall (HC : HeapCeil) (H : asr), (forall pc0 t, In (pc0, t) LIB_TRACES -> trace_ok (as_TR H) pc0 t) -> al_tr_ok ECHL H.
Proof.
  intros HC H D. cbn [al_tr_ok ECHL]. unfold atr_ok. apply Forall_forall. intros [pc0 t] Hin. cbn [fst snd]. exact (D pc0 t Hin).
Qed.
Lemma LCOST : forall (HC : HeapCeil) (H : asr), as_Cm H = ICm -> as_Cf H = ICf -> al_cost ECHL H (2 ^ 26) <= ALIB_COST_MAX.
Proof.
  intros HC H E1 E2. cbn [al_cost ECHL]. unfold acost. rewrite E1, E2. unfold ICm, ICf, ACOST_BYTES, ALIB_COST_MAX.
  cbn [Z.leb]. vm_compute. discriminate.
Qed.

(* [comment removed for export] *)
