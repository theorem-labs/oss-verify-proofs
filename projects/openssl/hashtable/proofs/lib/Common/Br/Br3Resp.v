(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRun FxRn FxHandoff.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 BackingAlgebra.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cx Require Import CxPlan CxPlanSound.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrTrans BrHole Br3X Br3RespDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Resp.
Variable segs : list Segment.
Variable E : AX2.env.

Definition row_ok (r : rrow) : Prop :=
  bv_unsigned (AX2.edenot E (rr_n r)) = bv_unsigned (AX2.edenot E (rr_b r)) + rr_k r.

Lemma resp_a_start RT a : Forall row_ok RT -> AX2S.estart E (resp_a RT a) = AX2S.estart E a.
Proof.
  intros HRT. unfold resp_a.
  destruct (List.find (fun r => AX2.expr_eqb (AX2.a_base a) (rr_b r)) RT) as [r|] eqn:Hf; [|reflexivity].
  apply find_some in Hf as [Hin Heq]. apply AX2S.expr_eqb_eq in Heq.
  pose proof (proj1 (Forall_forall _ _) HRT r Hin) as Hr. unfold row_ok in Hr.
  unfold AX2S.estart. cbn [AX2.a_base AX2.a_off]. rewrite Hr, Heq. lia.
Qed.

(* [comment removed for export] *)
Lemma adenot_of_start a a' n : AX2S.estart E a = AX2S.estart E a' -> AX2S.flat E a n -> AX2.adenot E a = AX2.adenot E a'.
Proof.
  intros He Hf. assert (Hf' : AX2S.flat E a' n) by (unfold AX2S.flat in *; rewrite <- He; exact Hf).
  apply bv_eq. rewrite (AX2S.flat_u _ _ _ Hf), (AX2S.flat_u _ _ _ Hf'). exact He.
Qed.

Lemma flat_of_start a a' n : AX2S.estart E a = AX2S.estart E a' -> AX2S.flat E a n -> AX2S.flat E a' n.
Proof. intros He Hf. unfold AX2S.flat in *. rewrite <- He. exact Hf. Qed.

Lemma kentry_resp_imp (M : word -> option byte) (f : AX2.saddr -> AX2.saddr) K K' :
  (forall a, AX2S.estart E (f a) = AX2S.estart E a) ->
  K' = match K with
       | AX2.KWord a w v => AX2.KWord (f a) w v
       | AX2.KZero a n => AX2.KZero (f a) n
       | AX2.KBlob a n k => AX2.KBlob (f a) n k
       | AX2.KWr a n => AX2.KWr (f a) n
       | AX2.KFill a n c => AX2.KFill (f a) n c
       | AX2.KUnk a n => AX2.KUnk (f a) n
       | _ => K
       end ->
  (AX2S.kentry_ok segs E M K <-> AX2S.kentry_ok segs E M K').
Proof.
  intros Hst ->.
  destruct K as [a w v | a n | a n k | lo hi | e mm | e lo hi | a n | a1 n1 a2 n2 | a n c | a n]; cbn [AX2S.kentry_ok]; try tauto.
  - (* [comment removed for export] *)
    split; intros (Hw & Hf & Hr).
    + split; [exact Hw|]. split; [exact (flat_of_start _ _ _ (eq_sym (Hst a)) Hf)|].
      rewrite <- (adenot_of_start a (f a) _ (eq_sym (Hst a)) Hf). exact Hr.
    + split; [exact Hw|]. split; [exact (flat_of_start _ _ _ (Hst a) Hf)|].
      rewrite <- (adenot_of_start (f a) a _ (Hst a) Hf). exact Hr.
  - (* [comment removed for export] *)
    split; intros (Hf & Hz).
    + split; [exact (flat_of_start _ _ _ (eq_sym (Hst a)) Hf)|]. intros i Hi. rewrite (Hst a). exact (Hz i Hi).
    + split; [exact (flat_of_start _ _ _ (Hst a) Hf)|]. intros i Hi. rewrite <- (Hst a). exact (Hz i Hi).
  - (* [comment removed for export] *)
    split; intros (Hf & Hl & Hz).
    + split; [exact (flat_of_start _ _ _ (eq_sym (Hst a)) Hf)|]. split; [exact Hl|]. intros i Hi. rewrite (Hst a). exact (Hz i Hi).
    + split; [exact (flat_of_start _ _ _ (Hst a) Hf)|]. split; [exact Hl|]. intros i Hi. rewrite <- (Hst a). exact (Hz i Hi).
  - (* [comment removed for export] *)
    split; intros (Hf & Hz).
    + split; [exact (flat_of_start _ _ _ (eq_sym (Hst a)) Hf)|]. intros dd mm H1 H2. rewrite (Hst a). exact (Hz dd mm H1 H2).
    + split; [exact (flat_of_start _ _ _ (Hst a) Hf)|]. intros dd mm H1 H2. rewrite <- (Hst a). exact (Hz dd mm H1 H2).
  - (* [comment removed for export] *)
    split; intros (Hf & Hz).
    + split; [exact (flat_of_start _ _ _ (eq_sym (Hst a)) Hf)|]. intros i Hi. rewrite (Hst a). exact (Hz i Hi).
    + split; [exact (flat_of_start _ _ _ (Hst a) Hf)|]. intros i Hi. rewrite <- (Hst a). exact (Hz i Hi).
  - (* [comment removed for export] *)
    split; intros (Hf & Hz).
    + split; [exact (flat_of_start _ _ _ (eq_sym (Hst a)) Hf)|]. intros i Hi. rewrite (Hst a). exact (Hz i Hi).
    + split; [exact (flat_of_start _ _ _ (Hst a) Hf)|]. intros i Hi. rewrite <- (Hst a). exact (Hz i Hi).
Qed.

Lemma resp_k_iff M RT K : Forall row_ok RT -> (AX2S.kentry_ok segs E M K <-> AX2S.kentry_ok segs E M (resp_k RT K)).
Proof.
  intros HRT. apply (kentry_resp_imp M (resp_a RT)); [intros a; exact (resp_a_start RT a HRT)|].
  destruct K; reflexivity.
Qed.

Lemma resp_know_iff M RT kn : Forall row_ok RT -> (AX2S.know_ok segs E M kn <-> AX2S.know_ok segs E M (map (resp_k RT) kn)).
Proof.
  intros HRT. unfold AX2S.know_ok. rewrite Forall_map. split; intros H; (eapply Forall_impl; [|exact H]); intros K HK;
    [exact (proj1 (resp_k_iff M RT K HRT) HK) | exact (proj2 (resp_k_iff M RT K HRT) HK)].
Qed.

(* [comment removed for export] *)
Variable kn : list AX2.kentry.
Variable base : word -> option byte.
Hypothesis Hkn : AX2S.know_ok segs E base kn.

Definition row_chk (r : rrow) : bool :=
  (0 <=? rr_k r)
  && lin_match (AX2.lin_of (rr_n r)) (AX2.lin_of (rr_b r)) (rr_k r)
  && (match AX2.base_range kn (rr_n r) with Some (lo, _) => (rr_k r <=? lo) | None => false end
      || match rr_par r with
         | Some bp => lin_sh_chk kn bp (rr_n r) && (rr_k r <=? to_Z shadow_K)
         | None => false
         end).

Lemma row_chk_sound r : row_chk r = true -> row_ok r.
Proof.
  unfold row_chk, row_ok. intros Hc. apply andb_prop in Hc as [Hc Hlo]. apply andb_prop in Hc as [Hk Hm]. apply Z.leb_le in Hk.
  pose proof (lin_match_sound E _ _ _ Hm) as Hq.
  pose proof (AX2S.lin_of_sound E (rr_n r)) as Hn. pose proof (AX2S.lin_of_sound E (rr_b r)) as Hb.
  pose proof (br_u64 (AX2.edenot E (rr_n r))) as Hun. pose proof (br_u64 (AX2.edenot E (rr_b r))) as Hub.
  assert (Hlow : rr_k r <= bv_unsigned (AX2.edenot E (rr_n r))).
  { apply orb_prop in Hlo as [Hlo|Hlo].
    - destruct (AX2.base_range kn (rr_n r)) as [[lo hi]|] eqn:Hr; [|discriminate]. apply Z.leb_le in Hlo.
      destruct (AX2S.base_range_sound segs E base kn _ lo hi Hkn Hr) as [H1 _]. lia.
    - destruct (rr_par r) as [bp|]; [|discriminate]. apply andb_prop in Hlo as [Hs Hle]. apply Z.leb_le in Hle.
      pose proof (lin_sh_sound segs E kn base Hkn _ _ Hs) as Es.
      pose proof (br_u64 (AX2.edenot E bp)) as Hup.
      assert (0 <= bv_unsigned (AX2.edenot E bp) / 8) by (apply Z.div_pos; lia). lia. }
  symmetry. replace (bv_unsigned (AX2.edenot E (rr_b r)) + rr_k r) with (bv_unsigned (AX2.edenot E (rr_n r)))
    ; [reflexivity|].
  assert (Eb : bv_unsigned (AX2.edenot E (rr_b r)) = bv_unsigned (AX2.edenot E (rr_n r)) - rr_k r).
  { apply br_eqm_small; [|exact Hub|lia].
    destruct Hq as [q1 Hq1]. destruct Hn as [q2 Hn2]. destruct Hb as [q3 Hb3]. unfold AX2S.uE in *.
    exists (q2 - q1 - q3). lia. }
  lia.
Qed.

Lemma rows_chk_sound RT : forallb row_chk RT = true -> Forall row_ok RT.
Proof. intros Hc. rewrite forallb_forall in Hc. apply Forall_forall. intros r Hr. exact (row_chk_sound r (Hc r Hr)). Qed.

End Resp.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RespCs.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

(* [comment removed for export] *)
Lemma cs_ok_set_kn E CS R FULL m kn' :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  AX2S.know_ok segs E (CXS.Mr A argH E CS m FULL) kn' ->
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E (CAP.set_kn CS kn') R FULL m.
Proof.
  intros HCS Hk.
  exact (cs_ok_transform segs A Lim SINV argH ISP FS0 SINV_frame E CS R FULL m
           (AX2.s_pc (CAP.a_ss CS)) (AX2.s_regs (CAP.a_ss CS)) kn' (AX2.s_next (CAP.a_ss CS)) R FULL m HCS
           (CXS.co_regs _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hk (lazy_frame_refl m)
           (CXS.co_minv _ _ _ _ _ _ _ _ _ _ _ _ HCS) (fun a _ => eq_refl)).
Qed.

Theorem cs_ok_resp RT E CS R FULL m :
  forallb (row_chk (CAP.kn CS)) RT = true ->
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E (resp_cs RT CS) R FULL m.
Proof.
  intros Hc HCS. unfold resp_cs. apply (cs_ok_set_kn E CS R FULL m _ HCS).
  pose proof (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hk.
  apply (proj1 (resp_know_iff segs E _ RT _ (rows_chk_sound segs E _ _ Hk RT Hc))). exact Hk.
Qed.

(* [comment removed for export] *)
Theorem cs_ok_unresp RT E CS R FULL m :
  forallb (row_chk (CAP.kn (resp_cs RT CS))) RT = true ->
  CAP.set_kn (resp_cs RT CS) (CAP.kn CS) = CS ->
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E (resp_cs RT CS) R FULL m ->
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Proof.
  intros Hc Heq HCS. rewrite <- Heq. apply (cs_ok_set_kn E _ R FULL m _ HCS).
  pose proof (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hk.
  pose proof (rows_chk_sound segs E _ _ Hk RT Hc) as HRT.
  apply (proj2 (resp_know_iff segs E _ RT _ HRT)). exact Hk.
Qed.

End RespCs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HoleResp.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Definition resp_chk (RTs RTe : list rrow) (START END : CAP.acs) : bool :=
  forallb (row_chk (CAP.kn START)) RTs && forallb (row_chk (CAP.kn (resp_cs RTe END))) RTe.

Theorem fx_hole_resp RTs RTe START END :
  resp_chk RTs RTe START END = true ->
  CAP.set_kn (resp_cs RTe END) (CAP.kn END) = END ->
  fx_hole cfg segs A Lim SINV argH ISP FS0 (resp_cs RTs START) (resp_cs RTe END) ->
  fx_hole cfg segs A Lim SINV argH ISP FS0 START END.
Proof.
  unfold resp_chk. intros Hc Heq Hh E R FULL m T HCS HK. apply andb_prop in Hc as [Hs He].
  pose proof (cs_ok_resp segs A Lim SINV argH ISP FS0 SINV_frame RTs E START R FULL m Hs HCS) as HCS'.
  apply (Hh E R FULL m T HCS').
  intros E1 R1 FULL1 m1 Hag HCS1 Hfs.
  apply (HK E1 R1 FULL1 m1); [exact Hag | | exact Hfs].
  exact (cs_ok_unresp segs A Lim SINV argH ISP FS0 SINV_frame RTe E1 END R1 FULL1 m1 He Heq HCS1).
Qed.

End HoleResp.
