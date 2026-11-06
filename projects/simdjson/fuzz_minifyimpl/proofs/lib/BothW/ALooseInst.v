(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg AProto ABase ARep ALayout AHeapP ARepQ ARepQP ASec ASecFrame
     ADepot ADepot_iface F_adepot AFake_iface AFake_arep AInstance ALoose AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition remapL (L : alayout) (f : aptr -> option (list byte)) (g : Z -> option (list byte)) : alayout :=
  mkALayout (al_V L) (al_w L) (al_U L) f g.
Lemma set_pat_remapL : forall L f, set_pat L f = remapL L f (al_spat L). Proof. reflexivity. Qed.
Lemma set_spat_remapL : forall L g, set_spat L g = remapL L (al_pat L) g. Proof. reflexivity. Qed.
Lemma remapL_remapL : forall L f g f' g', remapL (remapL L f g) f' g' = remapL L f' g'. Proof. reflexivity. Qed.
Lemma remapL_self : forall L, remapL L (al_pat L) (al_spat L) = L. Proof. intros [V w U f g]. reflexivity. Qed.

Section Remap.
Variables (L : alayout) (f : aptr -> option (list byte)) (g : Z -> option (list byte)).
Local Notation L' := (remapL L f g).
(* [comment removed for export] *)
Lemma remapL_pat : al_pat L' = f. Proof. reflexivity. Qed.
Lemma remapL_spat : al_spat L' = g. Proof. reflexivity. Qed.
Lemma remapL_V : al_V L' = al_V L. Proof. reflexivity. Qed.
Lemma remapL_w : al_w L' = al_w L. Proof. reflexivity. Qed.
Lemma remapL_U : al_U L' = al_U L. Proof. reflexivity. Qed.
Lemma remapL_sp0 : al_sp0 L' = al_sp0 L. Proof. reflexivity. Qed.
Lemma remapL_top : al_top L' = al_top L. Proof. reflexivity. Qed.
Lemma remapL_bot : al_bot L' = al_bot L. Proof. reflexivity. Qed.
Lemma remapL_t : al_t L' = al_t L. Proof. reflexivity. Qed.
Lemma remapL_ctx : al_ctx L' = al_ctx L. Proof. reflexivity. Qed.
Lemma remapL_space_beg : al_space_beg L' = al_space_beg L. Proof. reflexivity. Qed.
Lemma remapL_ptr_array : al_ptr_array L' = al_ptr_array L. Proof. reflexivity. Qed.
Lemma remapL_nodes : al_nodes L' = al_nodes L. Proof. reflexivity. Qed.
Lemma remapL_store : al_store L' = al_store L. Proof. reflexivity. Qed.
Lemma remapL_fake : al_fake L' = al_fake L. Proof. reflexivity. Qed.
Lemma remapL_res : al_res L' = al_res L. Proof. reflexivity. Qed.
Lemma remapL_dtls : al_dtls L' = al_dtls L. Proof. reflexivity. Qed.
Lemma remapL_xr : al_xr L' = al_xr L. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma remapL_aregion : forall c, aregion L' c = aregion L c. Proof. reflexivity. Qed.
Lemma remapL_aslot_addr : forall c k, aslot_addr L' c k = aslot_addr L c k. Proof. reflexivity. Qed.
Lemma remapL_afreearr : forall c, afreearr L' c = afreearr L c. Proof. reflexivity. Qed.
Lemma remapL_aregion_info : forall c, aregion_info L' c = aregion_info L c. Proof. reflexivity. Qed.
Lemma remapL_acache_addr : forall c, acache_addr L' c = acache_addr L c. Proof. reflexivity. Qed.
Lemma remapL_xb_alloc : forall b, xb_alloc L' b = xb_alloc L b. Proof. reflexivity. Qed.
Lemma remapL_xb_user : forall b, xb_user L' b = xb_user L b. Proof. reflexivity. Qed.
Lemma remapL_xb_hdr : forall b, xb_hdr L' b = xb_hdr L b. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma remapL_ok : alayout_ok L' <-> alayout_ok L.
Proof. split; intros H; destruct H; constructor; assumption. Qed.
(* [comment removed for export] *)
Lemma remapL_awf : forall st X, awf L' st X = awf L st X. Proof. reflexivity. Qed.
Lemma remapL_arep_rt : forall m, arep_rt L' m = arep_rt L m. Proof. reflexivity. Qed.
Lemma remapL_ainstance : forall st m, ainstance L' st m = ainstance L st m. Proof. reflexivity. Qed.
Lemma remapL_athread : forall st X m, athread L' st X m = athread L st X m. Proof. reflexivity. Qed.
Lemma remapL_acache_cells : forall st X m c, acache_cells L' st X m c = acache_cells L st X m c. Proof. reflexivity. Qed.
Lemma remapL_aregion_cells : forall st m c, aregion_cells L' st m c = aregion_cells L st m c. Proof. reflexivity. Qed.
Lemma remapL_afreearray : forall st X m c, afreearray L' st X m c = afreearray L st X m c. Proof. reflexivity. Qed.
Lemma remapL_aslot_busy : forall m b, aslot_busy L' m b = aslot_busy L m b. Proof. reflexivity. Qed.
Lemma remapL_aslots : forall st X m c, aslots L' st X m c = aslots L st X m c. Proof. reflexivity. Qed.
Lemma remapL_ashadow_avail : forall st m c, ashadow_avail L' st m c = ashadow_avail L st m c. Proof. reflexivity. Qed.
Lemma remapL_arng : forall RNG st, arng L' RNG st = arng L RNG st. Proof. reflexivity. Qed.
Lemma remapL_ablocks : forall st X LB, ablocks L' st X LB = ablocks L st X LB. Proof. reflexivity. Qed.
Lemma remapL_sec_wf1 : forall ch, sec_wf1 L' ch = sec_wf1 L ch. Proof. reflexivity. Qed.
Lemma remapL_sec_clear : forall mb ms, sec_clear L' mb ms = sec_clear L mb ms. Proof. reflexivity. Qed.
Lemma remapL_ADEPOTi : forall m, ADEPOTi L' m = ADEPOTi L m. Proof. reflexivity. Qed.
Lemma remapL_AFAKE : forall LB m, AFAKE L' LB m = AFAKE L LB m. Proof. reflexivity. Qed.
Lemma remapL_quar_untouched : forall X W, quar_untouched L' X W = quar_untouched L X W. Proof. reflexivity. Qed.
Lemma remapL_sec_untouched : forall W, sec_untouched L' W = sec_untouched L W. Proof. reflexivity. Qed.
Lemma remapL_fake_untouched : forall W, fake_untouched L' W = fake_untouched L W. Proof. reflexivity. Qed.
Lemma remapL_aknown : forall a, aknown L' a = aknown L a. Proof. reflexivity. Qed.
Lemma remapL_astartup_hulls : astartup_hulls L' = astartup_hulls L. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma remapL_qhdrs : forall chs ks, qhdrs L' chs ks = qhdrs L chs ks.
Proof. induction chs as [|ch chs IH]; intros [|k ks]; cbn [qhdrs]; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma remapL_abatch_cells : forall m b q nx, abatch_cells L' m b q nx = abatch_cells L m b q nx.
Proof. intros. unfold abatch_cells. rewrite remapL_qhdrs. reflexivity. Qed.
Lemma remapL_abatches_to : forall m bs qs nxt, abatches_to L' m bs qs nxt = abatches_to L m bs qs nxt.
Proof.
  intros m bs. induction bs as [|b bs IH]; intros [|q qs] nxt; cbn [abatches_to]; try reflexivity.
  rewrite remapL_abatch_cells, IH. reflexivity.
Qed.
Lemma remapL_aqcache : forall m C bs qs bytes, aqcache L' m C bs qs bytes = aqcache L m C bs qs bytes.
Proof. intros. unfold aqcache, abatches. rewrite remapL_abatches_to. reflexivity. Qed.
Lemma remapL_AQUAR_at : forall st X Q m, AQUAR_at L' st X Q m = AQUAR_at L st X Q m.
Proof. intros. unfold AQUAR_at. rewrite !remapL_aqcache. reflexivity. Qed.
Lemma remapL_AQUAR : forall st X m, AQUAR L' st X m <-> AQUAR L st X m.
Proof. intros. unfold AQUAR. split; intros [Q HQ]; exists Q; [rewrite <- remapL_AQUAR_at| rewrite remapL_AQUAR_at]; exact HQ. Qed.
(* [comment removed for export] *)
Lemma remapL_asec_wf : forall st cs, asec_wf L' st cs <-> asec_wf L st cs.
Proof.
  intros st cs. unfold asec_wf. rewrite remapL_ok.
  change (Forall (sec_wf1 L') cs) with (Forall (sec_wf1 L) cs). change (al_ptr_array L') with (al_ptr_array L). tauto.
Qed.
End Remap.

(* [comment removed for export] *)
Lemma remapL_ASEC_of_prim : forall L f st X m, ASEC_of (remapL L f (al_spat L)) st X m <-> ASEC_of L st X m.
Proof.
  intros. unfold ASEC_of, ASECc. rewrite remapL_asec_wf.
  change (asec_arr (remapL L f (al_spat L)) st (sec_chunks_of st) m) with (asec_arr L st (sec_chunks_of st) m).
  change (asec_inst (remapL L f (al_spat L)) m) with (asec_inst L m).
  change (aprim0 (remapL L f (al_spat L)) m) with (aprim0 L m).
  change (ashz (remapL L f (al_spat L)) (sec_chunks_of st) m) with (ashz L (sec_chunks_of st) m). tauto.
Qed.
Lemma remapL_aslot_shadow_sec : forall L g st X m c, aslot_shadow (remapL L (al_pat L) g) st X m c = aslot_shadow L st X m c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AHL : aholes := mkAHoles AQUAR ASEC_of (ADEPOT adepot_iface_raw) AFAKE.

Theorem AHL_laws : ahole_laws AHL.
Proof.
  constructor; cbn [AHL ah_quar ah_sec ah_depot ah_fake].
  - exact AQUAR_frame.
  - exact asec_hs_frame.
  - exact (adi_frame adepot_iface_raw).
  - intros L LB m m' W HF MU WM UT. eapply afake_frame; [exact HF| exact MU| exact WM| exact UT].
  - intros L LB LB' m HF EQ. eapply afake_blocks; [exact HF| exact EQ].
Qed.

Lemma AHL_eq : AHL = AH adepot_iface_raw AQUAR ASEC_of.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition AHEAP_L : alayout -> footprint -> astate -> list ablock -> amem -> Prop := AHEAP_P AHL.
Lemma AHEAP_L_E : AHEAP_L = AHEAP_P (AH adepot_iface_raw AQUAR ASEC_of).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma AREP_I_iff : forall L st X m, AREP AHI L st X m <-> AREP AHL L st X m /\ al_tight L.
Proof.
  intros L st X m. split.
  - intros (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
    cbn [AHI ah_depot ADEPOT adepot_iface ADEPOTt] in HD. destruct HD as [HD TI].
    split; [| exact TI]. repeat (split; [eassumption|]). exact RT3.
  - intros [(WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3) TI].
    repeat (split; [eassumption|]). split; [| split; [| split; [| split; [exact AVL| exact RT3]]]]; try eassumption.
    cbn [AHI ah_depot ADEPOT adepot_iface ADEPOTt]. split; [exact HD| exact TI].
Qed.

Lemma AHEAP_I_iff : forall L RNG st LB m, AHEAP_P AHI L RNG st LB m <-> AHEAP_L L RNG st LB m /\ al_tight L.
Proof.
  intros L RNG st LB m. unfold AHEAP_L. split.
  - intros (ALO & ARNG & [X [AR BL]] & HF). apply AREP_I_iff in AR. destruct AR as [AR TI].
    split; [| exact TI]. split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR| exact BL]| exact HF].
  - intros [(ALO & ARNG & [X [AR BL]] & HF) TI].
    split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [apply AREP_I_iff; split; [exact AR| exact TI]| exact BL]| exact HF].
Qed.

Corollary AHEAP_I_L : forall L RNG st LB m, AHEAP_P AHI L RNG st LB m -> AHEAP_L L RNG st LB m.
Proof. intros L RNG st LB m H. apply AHEAP_I_iff in H. exact (proj1 H). Qed.
Corollary AHEAP_L_I : forall L RNG st LB m, AHEAP_L L RNG st LB m -> al_tight L -> AHEAP_P AHI L RNG st LB m.
Proof. intros L RNG st LB m H T. apply AHEAP_I_iff. split; assumption. Qed.
Corollary AHEAP_I_tight : forall L RNG st LB m, AHEAP_P AHI L RNG st LB m -> al_tight L.
Proof. intros L RNG st LB m H. apply AHEAP_I_iff in H. exact (proj2 H). Qed.
End CANSEC1.
