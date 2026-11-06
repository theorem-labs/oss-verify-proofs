(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ARep ARepFrame ALayout AHeapP AMalloc_iface AEmbRep AFrameD AEmbFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Definition axflag (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  rw_cells asegs m (aregion_info L c + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))].

Definition axflags (L : alayout) (st : astate) (m : amem) : Prop :=
  forall c, 1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> axflag L st m c.

Definition emb_clrK (L : alayout) (st : astate) : Prop :=
  let '(d, cap, _) := a_emb st in forall a, d <= a < d + cap ->
    AIMG_HI <= a /\ ~ aknown L a /\ ~ (KLS <= a < K_HIGH_MEM) /\ ~ (al_ptr_array L <= a < al_ptr_array L + 8388608).

Definition emb_clrS (st : astate) : Prop :=
  let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (flat_map sec_iv (achunks st)) = true.
Definition AEXH (L : alayout) (st : astate) (m : amem) : Prop :=
  exh_cells m /\ emb_cells st m /\ axflags L st m /\ emb_clrK L st /\ emb_clrS st.
Lemma emb_clrS_of : forall RESV st, emb_clr RESV st -> emb_clrS st.
Proof.
  intros RESV st EC. unfold emb_clrS, emb_clr in *. destruct (a_emb st) as [[d cap] sz]. destruct EC as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. rewrite forallb_app in AV. apply andb_prop in AV as [_ AV]. exact AV.
Qed.

Lemma flat_sec_filter : forall l : list achunk, flat_map sec_iv (List.filter is_sec l) = flat_map sec_iv l.
Proof. induction l as [|[c n|mb ms n] l IH]; cbn; [reflexivity| exact IH| rewrite IH; reflexivity]. Qed.
Lemma emb_clrS_same : forall st st', a_emb st' = a_emb st -> Permutation.Permutation (sec_chunks_of st') (sec_chunks_of st) -> emb_clrS st -> emb_clrS st'.
Proof.
  intros st st' EE PERM CS. unfold emb_clrS in *. rewrite EE. destruct (a_emb st) as [[d cap] sz]. destruct CS as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. rewrite <- flat_sec_filter in AV |- *. fold (sec_chunks_of st) in AV. fold (sec_chunks_of st').
  apply forallb_forall. intros iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin).
  apply (proj1 (forallb_forall _ _) AV). apply in_flat_map. exists ch. split; [eapply Permutation.Permutation_in; [exact PERM| exact Hch]| exact Hin].
Qed.

Lemma emb_clrS_sub : forall st st', a_emb st' = a_emb st -> (forall ch, In ch (sec_chunks_of st') -> In ch (sec_chunks_of st)) -> emb_clrS st -> emb_clrS st'.
Proof.
  intros st st' EE SUB CS. unfold emb_clrS in *. rewrite EE. destruct (a_emb st) as [[d cap] sz]. destruct CS as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. rewrite <- flat_sec_filter in AV |- *. fold (sec_chunks_of st) in AV. fold (sec_chunks_of st').
  apply forallb_forall. intros iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin).
  apply (proj1 (forallb_forall _ _) AV). apply in_flat_map. exists ch. split; [exact (SUB ch Hch)| exact Hin].
Qed.

Definition emb_clrC (cs : list achunk) (st : astate) : Prop :=
  let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (flat_map sec_iv cs) = true.
Definition AEXHc (cs : list achunk) (L : alayout) (st : astate) (m : amem) : Prop :=
  exh_cells m /\ emb_cells st m /\ axflags L st m /\ emb_clrK L st /\ emb_clrC cs st.
Lemma AEXHc_of : forall L st m, AEXH L st m <-> AEXHc (sec_chunks_of st) L st m.
Proof.
  intros L st m. unfold AEXH, AEXHc, emb_clrS, emb_clrC, sec_chunks_of. destruct (a_emb st) as [[d cap] sz]. rewrite flat_sec_filter. tauto.
Qed.
Lemma emb_clrC_sub : forall cs cs' st st', a_emb st' = a_emb st -> (forall ch, In ch cs' -> In ch cs) -> emb_clrC cs st -> emb_clrC cs' st'.
Proof.
  intros cs cs' st st' EE SUB CS. unfold emb_clrC in *. rewrite EE. destruct (a_emb st) as [[d cap] sz]. destruct CS as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. apply forallb_forall. intros iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin).
  apply (proj1 (forallb_forall _ _) AV). apply in_flat_map. exists ch. split; [exact (SUB ch Hch)| exact Hin].
Qed.
Lemma AEXHc_sub : forall cs cs' L st m, (forall ch, In ch cs' -> In ch cs) -> AEXHc cs L st m -> AEXHc cs' L st m.
Proof. intros cs cs' L st m SUB (A1 & A2 & A3 & A4 & A5). repeat (split; [assumption|]). exact (emb_clrC_sub cs cs' st st eq_refl SUB A5). Qed.

Lemma emb_clrC_cons : forall ch cs st, (let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (sec_iv ch) = true) -> emb_clrC cs st -> emb_clrC (ch :: cs) st.
Proof.
  intros ch cs st H CS. unfold emb_clrC in *. destruct (a_emb st) as [[d cap] sz]. destruct H as [Z0|AV1]; [left; exact Z0|]. destruct CS as [Z0|AV]; [left; exact Z0| right].
  cbn [flat_map]. unfold avoids_all in *. rewrite forallb_app, AV1, AV. reflexivity.
Qed.

Lemma emb_clrK_of : forall L RESV st m, alayout_ok L -> aresv_ok L RESV -> emb_cells st m -> emb_clr RESV st -> emb_clrK L st.
Proof.
  intros L RESV st m ALO ARV EC ECL. unfold emb_clrK, emb_cells, emb_clr in *. destruct (a_emb st) as [[d cap] sz]. intros a Ha.
  destruct (Z.eqb_spec cap 0) as [E0|NZ]; [lia|].
  destruct EC as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _). unfold EMB_INIT in P2.
  destruct ECL as [QQ|AV]; [exfalso; exact (NZ QQ)|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
  destruct ARV as (PCI & PCSH & PCR & PCP & PCT & PCC & PCN & PCST & PCF & PCD & _). fold (al_res L) in PCR. fold (al_dtls L) in PCD.
  assert (OUT : forall l h, pcov RESV l h -> l <= a < h -> False).
  { intros l h PC Hx. destruct (PC a Hx) as ([lo hi] & Hin & R). rewrite forallb_forall in AV. specialize (AV _ Hin). unfold iv_clear in AV. cbn [fst snd] in *.
    apply orb_prop in AV as [Q|Q]; apply Z.leb_le in Q; lia. }
  split; [lia|]. split; [| split; [intros K; apply (OUT _ _ PCSH); unfold KLS, K_HIGH_MEM in K; lia| intros K; apply (OUT _ _ PCP); lia]].
  intros KN.
  pose proof atop_range as ATR. pose proof (ao_fake L ALO) as (_ & OF0 & OF1 & _). pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_space L ALO) as RSP.
  pose proof (ao_res_hi L ALO) as ORH.
  assert (SHF : 0x7fff7000 <= shad (al_fake L) /\ shad (al_fake L) + 1446400 <= 0x10007fff8000
                /\ 0x7fff7000 <= shad (al_space_beg L) + 536870912 /\ shad (al_space_beg L) + 17179869696 <= 0x10007fff8000
                /\ 0x7fff7000 <= shad ATOP /\ shad AIMG_HI <= 0x10007fff8000 /\ 0x7fff7000 <= shad KLS)
    by (rewrite !shad_div; unfold ASHOFF, KLS, AIMG_HI; clear -OF0 OF1 ORS ORH RSP ATR; Z.div_mod_to_equations; lia).
  destruct SHF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  unfold aknown, KLS, AIMG_HI in *.
  destruct KN as [[[K _]|[K|K]]|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]].
  - lia.
  - exact (OUT _ _ PCSH ltac:(lia)).
  - exact (OUT _ _ PCSH ltac:(lia)).
  - exact (OUT _ _ PCSH ltac:(lia)).
  - exact (OUT _ _ PCSH ltac:(lia)).
  - exact (OUT _ _ PCSH ltac:(lia)).
  - lia.
  - exact (OUT _ _ PCT K).
  - exact (OUT _ _ PCC K).
  - exact (OUT _ _ PCR K).
  - exact (OUT _ _ PCN K).
  - exact (OUT _ _ PCST K).
  - exact (OUT _ _ PCF K).
  - exact (OUT _ _ PCD K).
Qed.

Definition AREPns (H : aholes) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     awf L st X
  /\ arep_rt L m
  /\ ainstance L st m
  /\ athread L st X m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L st m c /\ afreearray L st X m c /\ aslots L st X m c /\ aslot_shadow L st X m c)
  /\ ah_quar H L st X m /\ ah_depot H L m
  /\ arelro m
  /\ arep_rt2 m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L st m c)
  /\ arep_rt3 m.
Lemma AREP_split : forall H L st X m, AREP H L st X m <-> AREPns H L st X m /\ ah_sec H L st X m.
Proof.
  intros H L st X m. unfold AREP, AREPns. split.
  - intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). split; [| exact A7]. repeat (split; [assumption|]). assumption.
  - intros [(A1 & A2 & A3 & A4 & A5 & A6 & A8 & A9 & A10 & A11 & A12) A7]. repeat (split; [assumption|]). assumption.
Qed.
Definition sec_sameX (st st' : astate) : Prop :=
     a_nsec st' = a_nsec st /\ a_nres st' = a_nres st /\ a_ptr_array st' = a_ptr_array st
  /\ (forall p mb ms n, (a_live st') !! p = Some (CSec mb ms n) <-> (a_live st) !! p = Some (CSec mb ms n))
  /\ Permutation.Permutation (sec_chunks_of st') (sec_chunks_of st).
Lemma sec_same_X : forall st st', sec_same st st' -> sec_sameX st st'.
Proof. intros st st' (A1 & A2 & A3 & A4 & A5 & _). unfold sec_sameX. repeat (split; [assumption|]). assumption. Qed.
End CANSEC.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ARep.TwinB ARepFrame.TwinB ALayout.TwinB AHeapP.TwinB AMalloc_iface.TwinB AEmbRep.TwinB AFrameD.TwinB AEmbFrame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Definition axflag (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  rw_cells bsegs m (aregion_info L c + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))].

Definition axflags (L : alayout) (st : astate) (m : amem) : Prop :=
  forall c, 1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> axflag L st m c.

Definition emb_clrK (L : alayout) (st : astate) : Prop :=
  let '(d, cap, _) := a_emb st in forall a, d <= a < d + cap ->
    AIMG_HI <= a /\ ~ aknown L a /\ ~ (KLS <= a < K_HIGH_MEM) /\ ~ (al_ptr_array L <= a < al_ptr_array L + 8388608).

Definition emb_clrS (st : astate) : Prop :=
  let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (flat_map sec_iv (achunks st)) = true.
Definition AEXH (L : alayout) (st : astate) (m : amem) : Prop :=
  exh_cells m /\ emb_cells st m /\ axflags L st m /\ emb_clrK L st /\ emb_clrS st.
Lemma emb_clrS_of : forall RESV st, emb_clr RESV st -> emb_clrS st.
Proof.
  intros RESV st EC. unfold emb_clrS, emb_clr in *. destruct (a_emb st) as [[d cap] sz]. destruct EC as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. rewrite forallb_app in AV. apply andb_prop in AV as [_ AV]. exact AV.
Qed.

Lemma flat_sec_filter : forall l : list achunk, flat_map sec_iv (List.filter is_sec l) = flat_map sec_iv l.
Proof. induction l as [|[c n|mb ms n] l IH]; cbn; [reflexivity| exact IH| rewrite IH; reflexivity]. Qed.
Lemma emb_clrS_same : forall st st', a_emb st' = a_emb st -> Permutation.Permutation (sec_chunks_of st') (sec_chunks_of st) -> emb_clrS st -> emb_clrS st'.
Proof.
  intros st st' EE PERM CS. unfold emb_clrS in *. rewrite EE. destruct (a_emb st) as [[d cap] sz]. destruct CS as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. rewrite <- flat_sec_filter in AV |- *. fold (sec_chunks_of st) in AV. fold (sec_chunks_of st').
  apply forallb_forall. intros iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin).
  apply (proj1 (forallb_forall _ _) AV). apply in_flat_map. exists ch. split; [eapply Permutation.Permutation_in; [exact PERM| exact Hch]| exact Hin].
Qed.

Lemma emb_clrS_sub : forall st st', a_emb st' = a_emb st -> (forall ch, In ch (sec_chunks_of st') -> In ch (sec_chunks_of st)) -> emb_clrS st -> emb_clrS st'.
Proof.
  intros st st' EE SUB CS. unfold emb_clrS in *. rewrite EE. destruct (a_emb st) as [[d cap] sz]. destruct CS as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. rewrite <- flat_sec_filter in AV |- *. fold (sec_chunks_of st) in AV. fold (sec_chunks_of st').
  apply forallb_forall. intros iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin).
  apply (proj1 (forallb_forall _ _) AV). apply in_flat_map. exists ch. split; [exact (SUB ch Hch)| exact Hin].
Qed.

Definition emb_clrC (cs : list achunk) (st : astate) : Prop :=
  let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (flat_map sec_iv cs) = true.
Definition AEXHc (cs : list achunk) (L : alayout) (st : astate) (m : amem) : Prop :=
  exh_cells m /\ emb_cells st m /\ axflags L st m /\ emb_clrK L st /\ emb_clrC cs st.
Lemma AEXHc_of : forall L st m, AEXH L st m <-> AEXHc (sec_chunks_of st) L st m.
Proof.
  intros L st m. unfold AEXH, AEXHc, emb_clrS, emb_clrC, sec_chunks_of. destruct (a_emb st) as [[d cap] sz]. rewrite flat_sec_filter. tauto.
Qed.
Lemma emb_clrC_sub : forall cs cs' st st', a_emb st' = a_emb st -> (forall ch, In ch cs' -> In ch cs) -> emb_clrC cs st -> emb_clrC cs' st'.
Proof.
  intros cs cs' st st' EE SUB CS. unfold emb_clrC in *. rewrite EE. destruct (a_emb st) as [[d cap] sz]. destruct CS as [Z0|AV]; [left; exact Z0| right].
  unfold avoids_all in *. apply forallb_forall. intros iv Hiv. apply in_flat_map in Hiv as (ch & Hch & Hin).
  apply (proj1 (forallb_forall _ _) AV). apply in_flat_map. exists ch. split; [exact (SUB ch Hch)| exact Hin].
Qed.
Lemma AEXHc_sub : forall cs cs' L st m, (forall ch, In ch cs' -> In ch cs) -> AEXHc cs L st m -> AEXHc cs' L st m.
Proof. intros cs cs' L st m SUB (A1 & A2 & A3 & A4 & A5). repeat (split; [assumption|]). exact (emb_clrC_sub cs cs' st st eq_refl SUB A5). Qed.

Lemma emb_clrC_cons : forall ch cs st, (let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (sec_iv ch) = true) -> emb_clrC cs st -> emb_clrC (ch :: cs) st.
Proof.
  intros ch cs st H CS. unfold emb_clrC in *. destruct (a_emb st) as [[d cap] sz]. destruct H as [Z0|AV1]; [left; exact Z0|]. destruct CS as [Z0|AV]; [left; exact Z0| right].
  cbn [flat_map]. unfold avoids_all in *. rewrite forallb_app, AV1, AV. reflexivity.
Qed.

Lemma emb_clrK_of : forall L RESV st m, alayout_ok L -> aresv_ok L RESV -> emb_cells st m -> emb_clr RESV st -> emb_clrK L st.
Proof.
  intros L RESV st m ALO ARV EC ECL. unfold emb_clrK, emb_cells, emb_clr in *. destruct (a_emb st) as [[d cap] sz]. intros a Ha.
  destruct (Z.eqb_spec cap 0) as [E0|NZ]; [lia|].
  destruct EC as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _). unfold EMB_INIT in P2.
  destruct ECL as [QQ|AV]; [exfalso; exact (NZ QQ)|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
  destruct ARV as (PCI & PCSH & PCR & PCP & PCT & PCC & PCN & PCST & PCF & PCD & _). fold (al_res L) in PCR. fold (al_dtls L) in PCD.
  assert (OUT : forall l h, pcov RESV l h -> l <= a < h -> False).
  { intros l h PC Hx. destruct (PC a Hx) as ([lo hi] & Hin & R). rewrite forallb_forall in AV. specialize (AV _ Hin). unfold iv_clear in AV. cbn [fst snd] in *.
    apply orb_prop in AV as [Q|Q]; apply Z.leb_le in Q; lia. }
  split; [lia|]. split; [| split; [intros K; apply (OUT _ _ PCSH); unfold KLS, K_HIGH_MEM in K; lia| intros K; apply (OUT _ _ PCP); lia]].
  intros KN.
  pose proof atop_range as ATR. pose proof (ao_fake L ALO) as (_ & OF0 & OF1 & _). pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_space L ALO) as RSP.
  pose proof (ao_res_hi L ALO) as ORH.
  assert (SHF : 0x7fff7000 <= shad (al_fake L) /\ shad (al_fake L) + 1446400 <= 0x10007fff8000
                /\ 0x7fff7000 <= shad (al_space_beg L) + 536870912 /\ shad (al_space_beg L) + 17179869696 <= 0x10007fff8000
                /\ 0x7fff7000 <= shad ATOP /\ shad AIMG_HI <= 0x10007fff8000 /\ 0x7fff7000 <= shad KLS)
    by (rewrite !shad_div; unfold ASHOFF, KLS, AIMG_HI; clear -OF0 OF1 ORS ORH RSP ATR; Z.div_mod_to_equations; lia).
  destruct SHF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  unfold aknown, KLS, AIMG_HI in *.
  destruct KN as [[[K _]|[K|K]]|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]].
  - lia.
  - exact (OUT _ _ PCSH ltac:(lia)).
  - exact (OUT _ _ PCSH ltac:(lia)).
  - exact (OUT _ _ PCSH ltac:(lia)).
  - exact (OUT _ _ PCSH ltac:(lia)).
  - exact (OUT _ _ PCSH ltac:(lia)).
  - lia.
  - exact (OUT _ _ PCT K).
  - exact (OUT _ _ PCC K).
  - exact (OUT _ _ PCR K).
  - exact (OUT _ _ PCN K).
  - exact (OUT _ _ PCST K).
  - exact (OUT _ _ PCF K).
  - exact (OUT _ _ PCD K).
Qed.

Definition AREPns (H : aholes) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     awf L st X
  /\ arep_rt L m
  /\ ainstance L st m
  /\ athread L st X m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L st m c /\ afreearray L st X m c /\ aslots L st X m c /\ aslot_shadow L st X m c)
  /\ ah_quar H L st X m /\ ah_depot H L m
  /\ arelro m
  /\ arep_rt2 m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L st m c)
  /\ arep_rt3 m.
Lemma AREP_split : forall H L st X m, AREP H L st X m <-> AREPns H L st X m /\ ah_sec H L st X m.
Proof.
  intros H L st X m. unfold AREP, AREPns. split.
  - intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). split; [| exact A7]. repeat (split; [assumption|]). assumption.
  - intros [(A1 & A2 & A3 & A4 & A5 & A6 & A8 & A9 & A10 & A11 & A12) A7]. repeat (split; [assumption|]). assumption.
Qed.
Definition sec_sameX (st st' : astate) : Prop :=
     a_nsec st' = a_nsec st /\ a_nres st' = a_nres st /\ a_ptr_array st' = a_ptr_array st
  /\ (forall p mb ms n, (a_live st') !! p = Some (CSec mb ms n) <-> (a_live st) !! p = Some (CSec mb ms n))
  /\ Permutation.Permutation (sec_chunks_of st') (sec_chunks_of st).
Lemma sec_same_X : forall st st', sec_same st st' -> sec_sameX st st'.
Proof. intros st st' (A1 & A2 & A3 & A4 & A5 & _). unfold sec_sameX. repeat (split; [assumption|]). assumption. Qed.
End CANSEC.
End TwinB.
