(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD F_sec_A F_sec_B F_sec_C AQuar F_quar_Ep F_quar_E AQuarM AHeap AFoot AQuarR AQuarS AQuarP.
Import ListNotations.
Open Scope Z_scope.

Section DZ.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation THR := (at_thr (al_thread AL)).
Notation D := (al_depot AL).

Definition dreg (iv : Z * Z) : Prop :=
  (DN0 D <= fst iv /\ snd iv <= DN0 D + 2^20) \/ (SS0 D <= fst iv /\ snd iv <= SS0 D + 2^23).
Definition dzone (lo : Z) (iv : Z * Z) : Prop := lo <= fst iv \/ dstat iv \/ dreg iv.

#[using="Type"] Lemma dr_inv_frame_d : forall X H (m m' : mem) WB WC hrest lo W,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  dr_inv AL E X H m WB WC hrest -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall (dzone lo) W ->
  dr_inv AL E X H m' WB WC hrest.
Proof.
  intros X H m m' WB WC hrest lo W AO LOH CLO INV MU WM MI' FZ.
  destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1 & N2 & _). layout_facts AO 6%nat LSS. destruct LSS as (S1 & S2 & _).
  layout_apart_fact AO 0%nat 5%nat A05. layout_apart_fact AO 0%nat 6%nat A06. layout_apart_fact AO 1%nat 5%nat A15. layout_apart_fact AO 1%nat 6%nat A16.
  layout_apart_fact AO 2%nat 5%nat A25. layout_apart_fact AO 2%nat 6%nat A26. layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36.
  assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
  assert (SHL : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).

  assert (DJZ : forall A n, 0 <= n -> 6328320 <= A -> A + n <= alloc_ceiling ->
            (A + n <= DN0 D \/ DN0 D + 2^20 <= A) -> (A + n <= SS0 D \/ SS0 D + 2^23 <= A) -> disjoint_from W A n).
  { intros A n N0 HA HN HD1 HD2. apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; cbn [fst snd] in *; lia. }
  unfold dr_inv.
  split.
  { apply (RPRIM_frame AL AO (fst X) _ m m' RP MU WM). unfold prim_clear. eapply Forall_impl; [| exact FZ].
    intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; left; unfold prim_out; cbn [fst snd] in *.
    - clear - Z1 LOH CLO ACR T3 T4 SP2 SHS. repeat split; lia.
    - clear - Z1 Z2 SP1 SHL T3. repeat split; lia.
    - clear - Z1 Z2 A05 A35 N1 SHL SHS T3. repeat split; lia.
    - clear - Z1 Z2 A06 A36 S1 SHL SHS T3. repeat split; lia. }
  split; [exact POK|].
  split.
  { pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
    eapply (RSEC_frame_but_q AL (snd X) _ m m' RS MU (wmono_but_of_wmono _ _ _ WM)).
    + eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; unfold img_out_q, dstat; cbn [fst snd] in *.
      * right; left. clear - Z1 LOH. lia.
      * right; right; right. lia.
      * clear - Z1 Z2 N1. lia.
      * clear - Z1 Z2 S1. lia.
    + clear - P1. lia.
    + apply DJZ; [lia| clear - P1; lia| clear - P2; lia| clear - A15; lia| clear - A16; lia].
    + apply Forall_forall. intros d Hd. pose proof (sec_geo AL (snd X) SOK d Hd) as (D1 & D2 & D3 & _).
      pose proof (proj1 (Forall_forall _ _) COK d Hd) as (_ & _ & _ & _ & _ & _ & D7').
      unfold al_regions in D7'. do 5 (apply Forall_cons_iff in D7' as [_ D7']). apply Forall_cons_iff in D7' as [DDN D7']. apply Forall_cons_iff in D7' as [DSS _].
      cbn [fst snd] in DDN, DSS. unfold apart in DDN, DSS. apply DJZ; [lia| lia| lia| clear - DDN D2; lia| clear - DSS D2; lia]. }
  split; [exact MI'|].
  assert (IOQ : Forall img_out_q W).
  { eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; unfold img_out_q, dstat; cbn [fst snd] in *;
      [right; left; clear - Z1 LOH; lia| right; right; right; lia| clear - Z1 Z2 N1; lia| clear - Z1 Z2 S1; lia]. }
  split; [exact (poison_env_frame_q E _ m m' PE MU WM IOQ)|].
  split.
  { eapply (thread_env_frame_q L _ m m' TE MU WM). unfold thread_clear_q. eapply Forall_impl; [| exact FZ].
    intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; unfold img_out_q, dstat; cbn [fst snd] in *.
    - split; [right; left; clear - Z1 LOH; lia|]. clear - Z1 CLO T2 T4. lia.
    - split; [right; right; right; lia|]. clear - Z1 Z2 T1 T3. lia.
    - split; [clear - Z1 Z2 N1; lia|]. clear - Z1 Z2 A25 A35. lia.
    - split; [clear - Z1 Z2 S1; lia|]. clear - Z1 Z2 A26 A36. lia. }
  split; [eapply shvis_wmono; [exact SV| exact WM]|].
  split; [exact WFS|].
  assert (MU0 : munch (W ++ []) m m') by (rewrite app_nil_r; exact MU).
  assert (DJP : forall c v, held1 (fst X) (c, v) -> disjoint_from W (region AL c + 16 * v) (class_size c) /\ disjoint_from W (sh (region AL c + 16 * v)) (class_size c / 8)).
  { intros c v HE. pose proof (held_geo AL (fst X) AO WF0 c v HE) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & G5 & G6 & G7). rewrite G5 in G7.
    pose proof (region_range AL c Hc) as [RR1 RR2].
    split; apply dj_of_Forall; (eapply Forall_impl; [| exact FZ]); intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; cbn [fst snd] in *.
    - clear - Z1 G2 G3 RR2 SP2 CLO. lia.
    - clear - Z1 Z2 G1 RR1 SP1. lia.
    - clear - Z1 Z2 G1 G2 G3 RR1 RR2 A05. lia.
    - clear - Z1 Z2 G1 G2 G3 RR1 RR2 A06. lia.
    - clear - Z1 G7 LOH. lia.
    - clear - Z1 Z2 G6. lia.
    - clear - Z1 Z2 G6 G7 N1. lia.
    - clear - Z1 Z2 G6 G7 S1. lia. }
  split.
  { apply Forall_forall. intros ch' Hin. pose proof (proj1 (Forall_forall _ _) HKS ch' Hin) as HK'. pose proof (proj1 (Forall_forall _ _) WFS ch' Hin) as WF'.
    eapply (qchunk_rep_other_g AL X m m' lo lo W [] [] [] ch' AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) MU0 ltac:(constructor)); [| exact WF'| exact (proj1 (Forall_forall _ _) REPS ch' Hin)| exact HK'| intros cv _ []| intros sc _ []].
    intros A n HU. destruct ch' as [[c v|sc] rz n0]; unfold held_kind in HK'; cbn [qc_kind] in HK'; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind] in HU.
    - destruct (DJP c v HK') as [DB DS]. destruct HU as [[-> ->]|[[-> ->]|[]]]; assumption.
    - pose proof (sec_geo AL (snd X) SOK sc HK') as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
      pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
      pose proof (proj1 (Forall_forall _ _) COK sc HK') as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _ & _ & _ & _ & _ & D7').
      unfold al_regions in D7'. do 5 (apply Forall_cons_iff in D7' as [_ D7']). apply Forall_cons_iff in D7' as [DDN D7']. apply Forall_cons_iff in D7' as [DSS _].
      cbn [fst snd] in DDN, DSS. unfold apart in DDN, DSS.
      assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
      assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
      assert (DJSH : forall A0 n1, sh (sc_beg sc) <= A0 -> A0 + n1 <= sh (sc_beg sc) + sc_msize sc / 8 -> disjoint_from W A0 n1).
      { intros A0 n1 HA0 HN1. apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; cbn [fst snd] in *;
          [clear - Z1 HN1 D10 LOH; lia| clear - Z1 Z2 HA0 D9; lia| clear - Z1 Z2 HA0 HN1 D9 D10 N1; lia| clear - Z1 Z2 HA0 HN1 D9 D10 S1; lia]. }
      destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
      + apply DJZ; [lia| lia| lia| clear - DDN CM1; lia| clear - DSS CM1; lia].
      + rewrite SHB, DV. apply DJSH; lia.
      + apply DJZ; [lia| lia| lia| clear - DDN CM1; lia| clear - DSS CM1; lia].
      + apply DJSH; [lia| clear - CM1 CM2; Z.div_mod_to_equations; lia]. }
  split; [exact HKS|]. split; [exact HOK|]. split; [exact NDS|]. split; [exact BWF|].
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) BREP b Hb) as [nx RB]. exists nx.
  assert (HBb : held1 (fst X) (bpair b)) by (destruct HOK as [_ FH]; apply (proj1 (Forall_forall _ _) FH); apply in_or_app; left; apply in_map; exact Hb).
  destruct (DJP K_BCLASS (qb_v b) HBb) as [DB DS]. change (class_size K_BCLASS) with 8192 in DB, DS. change (8192 / 8) with 1024 in DS. fold (qb_addr AL b) in DB, DS.
  eapply (qbatch_rep_other_g AL X m m' lo lo W [] [] [] b nx AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) MU0 ltac:(constructor) DB DS RB HBb). intros [].
Qed.

#[using="Type"] Lemma dr_inv_blk : forall X H (m m' : mem) WB WC hrest ch lo q sa sb A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  dr_inv AL E X H m WB WC (prim_of ch ++ hrest) -> held_kind X ch -> qchunk_wf ch ->
  (forall sc, In sc (sec_of ch) -> ~ In sc (flat_map sec_of WC)) ->
  munch [(sa, sb); (A, A + n)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  lo <= sa -> sb <= q -> qc_blk AL ch <= A -> A + n <= qc_blk AL ch + qc_bsize ch ->
  dr_inv AL E X H m' WB WC (prim_of ch ++ hrest).
Proof.
  intros X H m m' WB WC hrest ch lo q sa sb A n AO LOH CLO INV HK WF NSC MU WM MI' LSA SBQ HA HN.
  destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
  layout_apart_fact AO 0%nat 1%nat A01. layout_apart_fact AO 0%nat 2%nat A02. layout_apart_fact AO 0%nat 3%nat A03.
  assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
  assert (SHL : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
  destruct (pchunk_geo AL X m ch AO RP RS HK) as (GB8 & GS8 & GS32 & GLO & GHI & GBAND).
  assert (TCH : Forall (held1 (fst X)) (prim_of ch)).
  { destruct ch as [[c v|sc] rz n0]; cbn [prim_of qc_kind]; [| constructor]. constructor; [exact HK| constructor]. }
  assert (TSI : incl (sec_of ch) (se_chunks (snd X))).
  { destruct ch as [[c v|sc] rz n0]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HK. }
  assert (FWa : Forall (atouch AL lo q (fst X) (snd X) (prim_of ch) (sec_of ch)) [(sa, sb); (A, A + n)]).
  { constructor; [left; unfold sub_iv; cbn [fst snd]; lia|]. constructor; [| constructor].
    destruct ch as [[c v|sc] rz n0]; unfold qc_blk, qc_bsize in HA, HN; cbn [qc_kind prim_of sec_of] in *.
    - right; right; right; right; left. exists (c, v). split; [left; reflexivity|]. left. unfold chunk_iv. cbn [fst snd]. lia.
    - right; right; right; right; right; left. exists sc. split; [left; reflexivity|]. left. unfold sub_iv. cbn [fst snd]. lia. }

  assert (BLK : (A + n <= at_ctx L \/ at_ctx L + 4096 <= A) /\ (A + n <= THR \/ THR + 4096 <= A) /\ (A + n <= al_parr AL \/ al_parr AL + 2^23 <= A)
                /\ Forall (fun d => A + n <= sc_beg d \/ sc_beg d + 32 <= A) (se_chunks (snd X))).
  { destruct ch as [[c v|sc] rz n0]; unfold held_kind in HK; unfold qc_blk, qc_bsize in HA, HN; cbn [qc_kind] in *.
    - pose proof (held_geo AL (fst X) AO WF0 c v HK) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & _). pose proof (region_range AL c Hc) as [RR1 RR2].
      split; [clear - HA HN G1 G2 G3 RR1 RR2 A02; lia|]. split; [clear - HA HN G1 G2 G3 RR1 RR2 A03; lia|]. split; [clear - HA HN G1 G2 G3 RR1 RR2 A01; lia|].
      apply Forall_forall. intros d Hd. pose proof (sec_geo AL (snd X) SOK d Hd) as (_ & D2 & _ & _ & D5 & _). clear - HA HN G1 G2 G3 RR1 RR2 D2 D5. lia.
    - pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & _).
      pose proof (proj1 (Forall_forall _ _) COK sc HK) as (_ & _ & _ & _ & _ & _ & D7').
      unfold al_regions in D7'. do 2 (apply Forall_cons_iff in D7' as [_ D7']). apply Forall_cons_iff in D7' as [DCTX _]. cbn [fst snd] in DCTX. unfold apart in DCTX.
      split; [clear - HA HN DCTX; lia|]. split; [clear - HA HN D7; lia|]. split; [clear - HA HN D6; lia|].
      apply Forall_forall. intros d Hd. pose proof (sec_geo AL (snd X) SOK d Hd) as (_ & E2 & _).
      destruct (chunks_sep_In2 _ SSEP sc d HK Hd) as [<-|[AP|AP]]; [right; clear - HA; lia| |]; unfold apart_chunks in AP; clear - HA HN AP E2 D2; lia. }
  destruct BLK as (BCTX & BTHR & BPARR & BHDR).
  destruct HOK as [ND FH].
  unfold dr_inv.
  split.
  { apply (RPRIM_frame AL AO (fst X) _ m m' RP MU WM). unfold prim_clear. constructor; [| constructor; [| constructor]].
    - left. unfold prim_out. cbn [fst snd]. clear - LSA LOH CLO ACR T3 T4 SP2 SHS. repeat split; lia.
    - destruct ch as [[c v|sc] rz n0]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_blk, qc_bsize in HA, HN; cbn [qc_kind] in HA, HN.
      + right. exists c, v. split; [exact HK|]. left. unfold chunk_iv. cbn [fst snd]. lia.
      + left. pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & _).
        unfold prim_out. cbn [fst snd]. clear - HA HN D1 D2 D4 D5 D7 SHL SHS T3. repeat split; lia. }
  split; [exact POK|].
  split.
  { eapply (RSEC_frame_but AL (snd X) _ m m' RS MU (wmono_but_of_wmono _ _ _ WM)).
    - constructor; [| constructor; [| constructor]]; cbn [fst snd]; [right; clear - LSA LOH; lia| right; clear - HA GLO; lia].
    - clear - P1. lia.
    - cbn [disjoint_from]. split; [clear - LSA P2 CLO; lia|]. split; [clear - BPARR; lia| exact I].
    - apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) BHDR d Hd) as BD. cbn beta in BD.
      pose proof (sec_geo AL (snd X) SOK d Hd) as (_ & E2 & E3 & _). cbn [disjoint_from].
      split; [clear - LSA E2 E3 CLO; lia|]. split; [clear - BD; lia| exact I]. }
  split; [exact MI'|].
  split. { eapply poison_env_frame; [exact PE| exact MU| exact WM|]. unfold above_img. constructor; [| constructor; [| constructor]]; cbn [fst snd]; [clear - LSA LOH; lia| clear - HA GLO; lia]. }
  split. { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor; [| constructor]]; cbn [fst snd].
           - clear - LSA LOH CLO ACR T1 T2 T3 T4 T5. repeat split; lia.
           - clear - HA GLO BCTX BTHR. repeat split; lia. }
  split; [eapply shvis_wmono; [exact SV| exact WM]|].
  split; [exact WFS|].
  split.
  { apply Forall_forall. intros ch' Hin.
    eapply (qchunk_rep_other AL X m m' lo q _ (prim_of ch) (sec_of ch) ch' AO LOH CLO RP RS TCH TSI MU FWa).
    - exact (proj1 (Forall_forall _ _) WFS ch' Hin).
    - exact (proj1 (Forall_forall _ _) REPS ch' Hin).
    - exact (proj1 (Forall_forall _ _) HKS ch' Hin).
    - intros cv Hcv Hc. apply NoDup_app_remove_l in ND. apply (NoDup_app_disj_s _ _ cv ND); [apply in_flat_map; exists ch'; split; assumption|].
      apply in_or_app. left. exact Hc.
    - intros sc Hsc Hc. apply (NSC sc Hc). apply in_flat_map. exists ch'. split; assumption. }
  split; [exact HKS|]. split; [exact (conj ND FH)|]. split; [exact NDS|]. split; [exact BWF|].
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) BREP b Hb) as [nx RB]. exists nx.
  eapply (qbatch_rep_other AL X m m' lo q _ (prim_of ch) (sec_of ch) b nx AO LOH CLO RP RS TCH TSI MU FWa RB).
  - apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb.
  - intros Hc. apply (NoDup_app_disj_s _ _ (bpair b) ND); [apply in_map; exact Hb|]. apply in_or_app. right. apply in_or_app. left. exact Hc.
Qed.

#[using="Type"] Lemma RDEPOT_frame_m : forall hs total W (m m' : mem),
  dl_ok D -> SWIN D <= 2^23 ->
  RDEPOT D hs total m -> munch W m m' ->
  disjoint_from W 1595336 4259888 -> disjoint_from W (DN0 D) (2^20) -> disjoint_from W (SS0 D) (2^23) ->
  RDEPOT D hs total m'.
Proof.
  intros hs total W m m' DLO SW (TAB & NI & M1 & NR & (fj & FS) & SA & SD & (sj & FF) & RGH & T0 & TS & NB) MU DS DN DSS.
  unfold dl_ok in DLO.
  assert (ST : forall A n, 1595336 <= A -> A + n <= 5855224 -> disjoint_from W A n) by (intros A n H1 H2; eapply disjoint_from_sub; [exact DS| lia| lia]).
  assert (SN : forall A n, DN0 D <= A -> A + n <= DN0 D + 2^20 -> disjoint_from W A n) by (intros A n H1 H2; eapply disjoint_from_sub; [exact DN| lia| lia]).
  assert (SS : forall A n, SS0 D <= A -> A + n <= SS0 D + 2^23 -> disjoint_from W A n) by (intros A n H1 H2; eapply disjoint_from_sub; [exact DSS| lia| lia]).
  unfold RDEPOT.
  split. { intros b Hb. eapply rw_cells_transport_m; [exact (TAB b Hb)| exact MU|]. cbn [cells_size csize Nat.add]. apply ST; lia. }
  split. { eapply rw_cells_transport_m; [exact NI| exact MU|]. cbn [cells_size csize Nat.add]. apply ST; lia. }
  split. { eapply rw_cells_transport_m; [exact M1| exact MU|]. cbn [cells_size csize Nat.add]. apply ST; lia. }
  split. { intros i Hi. destruct (NR i Hi) as [sid C]. exists sid. eapply rw_cells_transport_m; [exact C| exact MU|]. cbn [cells_size csize Nat.add]. apply SN; unfold zlen in *; lia. }
  split. { exists fj. eapply rw_cells_transport_m; [exact FS| exact MU|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply SN; unfold zlen in *; lia. }
  split. { eapply rw_cells_transport_m; [exact SA| exact MU|]. cbn [cells_size csize Nat.add]. apply ST; lia. }
  split. { eapply rw_cells_transport_m; [exact SD| exact MU|]. cbn [cells_size csize Nat.add]. apply ST; lia. }
  split. { exists sj. eapply rw_cells_transport_m; [exact FF| exact MU|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply SS; lia. }
  repeat split; assumption.
Qed.

#[using="Type"] Lemma atouch_dreg_dj : forall X (m : mem) lo q W tc tsc A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
  (DN0 D <= A /\ A + n <= DN0 D + 2^20) \/ (SS0 D <= A /\ A + n <= SS0 D + 2^23) -> disjoint_from W A n.
Proof.
  intros X m lo q W tc tsc A n AO LOH CLO RP RS TCH TSI FW HA.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1 & N2 & _). layout_facts AO 6%nat LSS. destruct LSS as (S1 & S2 & _).
  layout_apart_fact AO 0%nat 5%nat A05. layout_apart_fact AO 0%nat 6%nat A06. layout_apart_fact AO 1%nat 5%nat A15. layout_apart_fact AO 1%nat 6%nat A16.
  layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36.
  assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
  assert (SHR : forall x, 0 <= x <= 2^47 -> 2147450880 <= sh x <= 17594333495296) by (intros x Hx; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  assert (SECD : forall d, In d (se_chunks (snd X)) -> (sc_beg d + sc_msize d <= DN0 D \/ DN0 D + 2^20 <= sc_beg d) /\ (sc_beg d + sc_msize d <= SS0 D \/ SS0 D + 2^23 <= sc_beg d)).
  { intros d Hd. pose proof (proj1 (Forall_forall _ _) COK d Hd) as (_ & _ & _ & _ & _ & _ & D7').
    unfold al_regions in D7'. do 5 (apply Forall_cons_iff in D7' as [_ D7']). apply Forall_cons_iff in D7' as [DDN D7']. apply Forall_cons_iff in D7' as [DSS _].
    cbn [fst snd] in DDN, DSS. unfold apart in DDN, DSS. split; lia. }
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros iv AT. unfold atouch, sub_iv in AT.
  destruct AT as [AT|[AT|[AT|[AT|[AT|[AT|[AT|AT]]]]]]].
  - clear - AT HA N2 S2 CLO. lia.
  - clear - AT HA N1 S1. lia.
  - clear - AT HA A35 A36. lia.
  - destruct AT as (c0 & Hc0 & [AT|[AT|AT]]).
    + unfold ri_addr, RIB in AT. clear - AT HA A05 A06 Hc0. lia.
    + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & K2 & _). rewrite !RGE in *. clear - AT HA A05 A06 Hc0 K1 K2 Q2. lia.
    + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & K2 & _).
      pose proof (SHR (region AL c0 + p_au (get_cls (fst X) c0)) ltac:(rewrite RGE in *; clear - SP1 SP5 Hc0 K1 K2 Q2; lia)) as SH1.
      pose proof (SHR (region AL (c0 + 1)) ltac:(rewrite RGE in *; clear - SP1 SP5 Hc0 Q2; lia)) as SH2. clear - AT HA SH1 SH2 N1 S1. lia.
  - destruct AT as ([c1 v1] & Hin & AT). cbn [fst snd] in AT.
    pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo AL (fst X) AO WF0 c1 v1 HE1) as G'. cbv zeta in G'.
    destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7). pose proof (region_range AL c1 Hc1) as [Q1 Q2]. rewrite H5 in H7. rewrite RGE in *.
    unfold chunk_iv, chunk_sh_iv in AT. rewrite RGE in AT. destruct AT as [AT|AT]; [clear - AT HA H1 H2 H3 Q2 A05 A06 Hc1; lia| clear - AT HA H6 H7 N1 S1; lia].
  - destruct AT as (sc & Hin & AT). pose proof (sec_geo AL (snd X) SOK sc (TSI sc Hin)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
    destruct (SECD sc (TSI sc Hin)) as [E1 E2]. destruct AT as [AT|AT]; [clear - AT HA E1 E2; lia| clear - AT HA D9 D10 N1 S1; lia].
  - destruct AT as (d & Hin & AT). pose proof (sec_geo AL (snd X) SOK d Hin) as (D1 & D2 & _). destruct (SECD d Hin) as [E1 E2]. clear - AT HA D2 E1 E2. lia.
  - clear - AT HA A15 A16. lia.
Qed.

Definition thread_env2 (m : mem) : Prop :=
  rw_cells asegs m THR [C8 (wz (at_ctx L))] /\ exists tid : word, rw_cells asegs m (at_ctx L + 8) [C4 tid].

#[using="Type"] Lemma thread_env2_frame_m : forall W (m m' : mem), thread_env2 m -> munch W m m' ->
  disjoint_from W THR 8 -> disjoint_from W (at_ctx L + 8) 4 -> thread_env2 m'.
Proof.
  intros W m m' (C1 & tid & C2) MU D1 D2. split; [| exists tid].
  - eapply rw_cells_transport_m; [exact C1| exact MU| exact D1].
  - eapply rw_cells_transport_m; [exact C2| exact MU| exact D2].
Qed.

#[using="Type"] Lemma atouch_thr_dj : forall X (m : mem) lo q W tc tsc A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
  (THR <= A /\ A + n <= THR + TQ_OFF) \/ (at_ctx L <= A /\ A + n <= at_ctx L + 4096) -> disjoint_from W A n.
Proof.
  intros X m lo q W tc tsc A n AO LOH CLO RP RS TCH TSI FW HA.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_apart_fact AO 0%nat 2%nat A02. layout_apart_fact AO 0%nat 3%nat A03. layout_apart_fact AO 1%nat 2%nat A12. layout_apart_fact AO 1%nat 3%nat A13.
  assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
  assert (SHR : forall x, 0 <= x <= 2^47 -> 2147450880 <= sh x <= 17594333495296) by (intros x Hx; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  assert (SECD : forall d, In d (se_chunks (snd X)) -> (sc_beg d + sc_msize d <= at_ctx L \/ at_ctx L + 4096 <= sc_beg d) /\ (sc_beg d + sc_msize d <= THR \/ THR + 4096 <= sc_beg d)).
  { intros d Hd. pose proof (proj1 (Forall_forall _ _) COK d Hd) as (_ & _ & _ & _ & _ & _ & D7').
    unfold al_regions in D7'. do 2 (apply Forall_cons_iff in D7' as [_ D7']). apply Forall_cons_iff in D7' as [DCT D7']. apply Forall_cons_iff in D7' as [DTH _].
    cbn [fst snd] in DCT, DTH. unfold apart in DCT, DTH. split; lia. }
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros iv AT. unfold atouch, sub_iv in AT.
  destruct AT as [AT|[AT|[AT|[AT|[AT|[AT|[AT|AT]]]]]]].
  - clear - AT HA T2 T4 CLO. lia.
  - clear - AT HA T1 T3. lia.
  - clear - AT HA T5. lia.
  - destruct AT as (c0 & Hc0 & [AT|[AT|AT]]).
    + unfold ri_addr, RIB in AT. clear - AT HA A02 A03 Hc0. lia.
    + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & K2 & _). rewrite !RGE in *. clear - AT HA A02 A03 Hc0 K1 K2 Q2. lia.
    + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & K2 & _).
      pose proof (SHR (region AL c0 + p_au (get_cls (fst X) c0)) ltac:(rewrite RGE in *; clear - SP1 SP5 Hc0 K1 K2 Q2; lia)) as SH1.
      pose proof (SHR (region AL (c0 + 1)) ltac:(rewrite RGE in *; clear - SP1 SP5 Hc0 Q2; lia)) as SH2. clear - AT HA SH1 SH2 T1 T3. lia.
  - destruct AT as ([c1 v1] & Hin & AT). cbn [fst snd] in AT.
    pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo AL (fst X) AO WF0 c1 v1 HE1) as G'. cbv zeta in G'.
    destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7). pose proof (region_range AL c1 Hc1) as [Q1 Q2]. rewrite H5 in H7. rewrite RGE in *.
    unfold chunk_iv, chunk_sh_iv in AT. rewrite RGE in AT. destruct AT as [AT|AT]; [clear - AT HA H1 H2 H3 Q2 A02 A03 Hc1; lia| clear - AT HA H6 H7 T1 T3; lia].
  - destruct AT as (sc & Hin & AT). pose proof (sec_geo AL (snd X) SOK sc (TSI sc Hin)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
    destruct (SECD sc (TSI sc Hin)) as [E1 E2]. destruct AT as [AT|AT]; [clear - AT HA E1 E2; lia| clear - AT HA D9 D10 T1 T3; lia].
  - destruct AT as (d & Hin & AT). pose proof (sec_geo AL (snd X) SOK d Hin) as (D1 & D2 & _). destruct (SECD d Hin) as [E1 E2]. clear - AT HA D2 E1 E2. lia.
  - clear - AT HA A12 A13. lia.
Qed.

Ltac demodt H z :=
  unfold id in H;
  lazymatch type of H with
  | ?a mod ?b = 0 => apply (proj1 (Z.mod_divide a b ltac:(lia))) in H; unfold Z.divide in H; destruct H as [z H]
  end.

#[using="Type"] Lemma pchunk_rep_frame_m : forall W (m m' : mem) ch,
  pchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 -> munch W m m' ->
  disjoint_from W (qc_blk AL ch) (qc_bsize ch) -> disjoint_from W (sh (qc_blk AL ch)) (qc_bsize ch / 8) ->
  match qc_kind ch with
  | QPrim _ _ => True
  | QSec sc => disjoint_from W (sc_beg sc + 32) 4064 /\ disjoint_from W (sh (sc_beg sc)) 512
  end ->
  pchunk_rep AL m' ch.
Proof.
  intros W m m' ch R WF B8 S8 MU DA DS DK. unfold pchunk_rep in *. cbv zeta in *.
  destruct WF as (RZ16 & RZM & NR & RZN & _).
  set (B := qc_blk AL ch) in *. set (bs := qc_bsize ch) in *. set (rz := qc_rz ch) in *. set (n := qc_n ch) in *.
  assert (EH : qc_hdr AL ch = B + rz - 16) by reflexivity. rewrite EH in *. clear EH.
  assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
  demodt B8 kb. demodt S8 ks. demodt RZM kr. destruct N8 as [N8 N8m]. demodt N8m kn.
  assert (SHX : forall k, 0 <= k -> sh (B + 8 * k) = sh B + k) by (intros k Hk; unfold sh; rewrite B8; clear - Hk; Z.div_mod_to_equations; lia).
  assert (DV : rz / 8 = 2 * kr /\ rup8 n / 8 = kn /\ bs / 8 = ks /\ (bs - rz - rup8 n) / 8 = ks - 2 * kr - kn)
    by (rewrite RZM, N8m, S8; clear; Z.div_mod_to_equations; lia).
  destruct DV as (DV1 & DV2 & DV3 & DV4). rewrite DV3 in DS.
  assert (TRA : forall A cs, rw_cells asegs m A cs -> B <= A -> A + Z.of_nat (cells_size cs) <= B + bs -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DA| exact H1| exact H2]. }
  assert (TRS : forall A cs, rw_cells asegs m A cs -> sh B <= A -> A + Z.of_nat (cells_size cs) <= sh B + ks -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DS| exact H1| exact H2]. }
  destruct R as ((bits & actx & R1) & R2 & (j3 & R3) & R4 & (sj & R5) & R6 & R7).
  split. { exists bits, actx. apply TRA; [exact R1| clear - RZ16; lia| cbn [cells_size csize Nat.add]; clear - RZ16 RZN N8 NR; lia]. }
  split.
  { intros RZ32. destruct (R2 RZ32) as [R2a (j2 & R2b)]. split.
    - apply TRA; [exact R2a| clear; lia| cbn [cells_size csize Nat.add]; clear - RZ32 RZM RZN N8 NR; lia].
    - exists j2. apply TRA; [exact R2b| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ32 RZM; lia). clear - RZ32 RZM RZN N8 NR. lia. }
  split. { exists j3. apply TRA; [exact R3| clear - RZ16; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZN N8 NR; lia). clear. lia. }
  split. { apply TRS; [exact R4| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV1, Z2Nat.id by (clear - RZ16 RZM; lia). clear - RZN RZM N8m S8 N8 NR. lia. }
  split.
  { exists sj. replace (B + rz - 16 + 16) with (B + 8 * (2 * kr)) in * by (clear - RZM; lia). rewrite (SHX (2 * kr)) in * by (clear - RZ16 RZM; lia).
    apply TRS; [exact R5| clear - RZ16 RZM; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV2, Z2Nat.id by (clear - N8 NR N8m; lia). clear - RZN RZM N8m S8. lia. }
  split.
  { replace (B + rz - 16 + 16 + rup8 n) with (B + 8 * (2 * kr + kn)) in * by (clear - RZM N8m; lia).
    rewrite (SHX (2 * kr + kn)) in * by (clear - RZ16 RZM N8 NR N8m; lia).
    apply TRS; [exact R6| clear - RZ16 RZM N8 NR N8m; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV4, Z2Nat.id by (clear - RZN RZM N8m S8; lia). clear. lia. }
  destruct (qc_kind ch) as [c v| sc]; [exact I|]. destruct DK as [DK1 DK2]. destruct R7 as [(j7 & R7a) R7b]. split.
  - exists j7. eapply rw_cells_transport_m; [exact R7a| exact MU| cbn [cells_size csize Nat.add]; exact DK1].
  - eapply rw_cells_transport_m; [exact R7b| exact MU| cbn [cells_size csize Nat.add]; exact DK2].
Qed.

#[using="Type"] Lemma hull_dzone_dj : forall X (m : mem) lo W ch A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch -> Forall (dzone lo) W ->
  qc_hull AL ch A n -> disjoint_from W A n.
Proof.
  intros X m lo W ch A n AO LOH CLO RP RS HK' FZ HU.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1 & N2 & _). layout_facts AO 6%nat LSS. destruct LSS as (S1 & S2 & _).
  layout_apart_fact AO 0%nat 5%nat A05. layout_apart_fact AO 0%nat 6%nat A06.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  assert (DJZ : forall A n, 0 <= n -> 6328320 <= A -> A + n <= alloc_ceiling ->
            (A + n <= DN0 D \/ DN0 D + 2^20 <= A) -> (A + n <= SS0 D \/ SS0 D + 2^23 <= A) -> disjoint_from W A n).
  { intros A1 n1 N0 HA HN HD1 HD2. apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; cbn [fst snd] in *; lia. }
  destruct ch as [[c v|sc] rz n0]; unfold held_kind in HK'; cbn [qc_kind] in HK'; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind] in HU.
  - pose proof (held_geo AL (fst X) AO WF0 c v HK') as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & G5 & G6 & G7). rewrite G5 in G7.
    pose proof (region_range AL c Hc) as [RR1 RR2].
    destruct HU as [[-> ->]|[[-> ->]|[]]]; apply dj_of_Forall; (eapply Forall_impl; [| exact FZ]); intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; cbn [fst snd] in *.
    + clear - Z1 G2 G3 RR2 SP2 CLO. lia.
    + clear - Z1 Z2 G1 RR1 SP1. lia.
    + clear - Z1 Z2 G1 G2 G3 RR1 RR2 A05. lia.
    + clear - Z1 Z2 G1 G2 G3 RR1 RR2 A06. lia.
    + clear - Z1 G7 LOH. lia.
    + clear - Z1 Z2 G6. lia.
    + clear - Z1 Z2 G6 G7 N1. lia.
    + clear - Z1 Z2 G6 G7 S1. lia.
  - pose proof (sec_geo AL (snd X) SOK sc HK') as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
    pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
    pose proof (proj1 (Forall_forall _ _) COK sc HK') as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _ & _ & _ & _ & _ & D7').
    unfold al_regions in D7'. do 5 (apply Forall_cons_iff in D7' as [_ D7']). apply Forall_cons_iff in D7' as [DDN D7']. apply Forall_cons_iff in D7' as [DSS _].
    cbn [fst snd] in DDN, DSS. unfold apart in DDN, DSS.
    assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
    assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
    assert (DJSH : forall A0 n1, sh (sc_beg sc) <= A0 -> A0 + n1 <= sh (sc_beg sc) + sc_msize sc / 8 -> disjoint_from W A0 n1).
    { intros A0 n1 HA0 HN1. apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; cbn [fst snd] in *;
        [clear - Z1 HN1 D10 LOH; lia| clear - Z1 Z2 HA0 D9; lia| clear - Z1 Z2 HA0 HN1 D9 D10 N1; lia| clear - Z1 Z2 HA0 HN1 D9 D10 S1; lia]. }
    destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    + apply DJZ; [lia| lia| lia| clear - DDN CM1; lia| clear - DSS CM1; lia].
    + rewrite SHB, DV. apply DJSH; lia.
    + apply DJZ; [lia| lia| lia| clear - DDN CM1; lia| clear - DSS CM1; lia].
    + apply DJSH; [lia| clear - CM1 CM2; Z.div_mod_to_equations; lia].
Qed.

#[using="Type"] Lemma pchunk_rep_frame_d : forall X (m m' : mem) lo W ch,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch -> qchunk_wf ch -> Forall (dzone lo) W ->
  pchunk_rep AL m ch -> munch W m m' -> pchunk_rep AL m' ch.
Proof.
  intros X m m' lo W ch AO LOH CLO RP RS HK WF FZ R MU.
  destruct (pchunk_geo AL X m ch AO RP RS HK) as (GB8 & GS8 & _).
  assert (HU : forall A n, qc_hull AL ch A n -> disjoint_from W A n) by (intros A n HU; exact (hull_dzone_dj X m lo W ch A n AO LOH CLO RP RS HK FZ HU)).
  eapply pchunk_rep_frame_m; [exact R| exact WF| exact GB8| exact GS8| exact MU| | |].
  - apply HU. left. split; reflexivity.
  - apply HU. right; left. split; reflexivity.
  - destruct (qc_kind ch) as [c v|sc] eqn:EK; [exact I|]. split; apply HU; right; right; rewrite EK; [left| right]; split; reflexivity.
Qed.

#[using="Type"] Lemma pchunk_ctx_stored : forall W (m m' : mem) ch j',
  pchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 -> munch W m m' ->
  rw_cells asegs m' (qc_hdr AL ch + 16) [CB (Z.to_nat (qc_bsize ch - qc_rz ch)) j'] ->
  disjoint_from W (qc_blk AL ch) (qc_rz ch) -> disjoint_from W (sh (qc_blk AL ch)) (qc_bsize ch / 8) ->
  match qc_kind ch with
  | QPrim _ _ => True
  | QSec sc => disjoint_from W (sc_beg sc + 32) 4064 /\ disjoint_from W (sh (sc_beg sc)) 512
  end ->
  pchunk_rep AL m' ch.
Proof.
  intros W m m' ch j' R WF B8 S8 MU NEW DA DS DK. unfold pchunk_rep in *. cbv zeta in *.
  destruct WF as (RZ16 & RZM & NR & RZN & _).
  set (B := qc_blk AL ch) in *. set (bs := qc_bsize ch) in *. set (rz := qc_rz ch) in *. set (n := qc_n ch) in *.
  assert (EH : qc_hdr AL ch = B + rz - 16) by reflexivity. rewrite EH in *. clear EH.
  assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
  demodt B8 kb. demodt S8 ks. demodt RZM kr. destruct N8 as [N8 N8m]. demodt N8m kn.
  assert (SHX : forall k, 0 <= k -> sh (B + 8 * k) = sh B + k) by (intros k Hk; unfold sh; rewrite B8; clear - Hk; Z.div_mod_to_equations; lia).
  assert (DV : rz / 8 = 2 * kr /\ rup8 n / 8 = kn /\ bs / 8 = ks /\ (bs - rz - rup8 n) / 8 = ks - 2 * kr - kn)
    by (rewrite RZM, N8m, S8; clear; Z.div_mod_to_equations; lia).
  destruct DV as (DV1 & DV2 & DV3 & DV4). rewrite DV3 in DS.
  assert (TRA : forall A cs, rw_cells asegs m A cs -> B <= A -> A + Z.of_nat (cells_size cs) <= B + rz -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DA| exact H1| exact H2]. }
  assert (TRS : forall A cs, rw_cells asegs m A cs -> sh B <= A -> A + Z.of_nat (cells_size cs) <= sh B + ks -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DS| exact H1| exact H2]. }
  destruct R as ((bits & actx & R1) & R2 & (j3 & R3) & R4 & (sj & R5) & R6 & R7).
  split. { exists bits, actx. apply TRA; [exact R1| clear - RZ16; lia| cbn [cells_size csize Nat.add]; clear; lia]. }
  split.
  { intros RZ32. destruct (R2 RZ32) as [R2a (j2 & R2b)]. split.
    - apply TRA; [exact R2a| clear; lia| cbn [cells_size csize Nat.add]; clear - RZ32 RZM; lia].
    - exists j2. apply TRA; [exact R2b| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ32 RZM; lia). clear. lia. }
  split. { exists j'. exact NEW. }
  split. { apply TRS; [exact R4| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV1, Z2Nat.id by (clear - RZ16 RZM; lia). clear - RZN RZM N8m S8 N8 NR. lia. }
  split.
  { exists sj. replace (B + rz - 16 + 16) with (B + 8 * (2 * kr)) in * by (clear - RZM; lia). rewrite (SHX (2 * kr)) in * by (clear - RZ16 RZM; lia).
    apply TRS; [exact R5| clear - RZ16 RZM; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV2, Z2Nat.id by (clear - N8 NR N8m; lia). clear - RZN RZM N8m S8. lia. }
  split.
  { replace (B + rz - 16 + 16 + rup8 n) with (B + 8 * (2 * kr + kn)) in * by (clear - RZM N8m; lia).
    rewrite (SHX (2 * kr + kn)) in * by (clear - RZ16 RZM N8 NR N8m; lia).
    apply TRS; [exact R6| clear - RZ16 RZM N8 NR N8m; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV4, Z2Nat.id by (clear - RZN RZM N8m S8; lia). clear. lia. }
  destruct (qc_kind ch) as [c v| sc]; [exact I|]. destruct DK as [DK1 DK2]. destruct R7 as [(j7 & R7a) R7b]. split.
  - exists j7. eapply rw_cells_transport_m; [exact R7a| exact MU| cbn [cells_size csize Nat.add]; exact DK1].
  - eapply rw_cells_transport_m; [exact R7b| exact MU| cbn [cells_size csize Nat.add]; exact DK2].
Qed.

#[using="Type"] Lemma held_blk_geo : forall X (m : mem) ch lo q A n, alayout_ok AL -> RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  qc_blk AL ch <= A -> A + n <= qc_blk AL ch + qc_bsize ch ->
  atouch AL lo q (fst X) (snd X) (prim_of ch) (sec_of ch) (A, A + n).
Proof.
  intros X m ch lo q A n AO RP RS HK HA HN. destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  destruct ch as [[c v|sc] rz n0]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_blk, qc_bsize in HA, HN; cbn [qc_kind prim_of sec_of] in *.
  - right; right; right; right; left. exists (c, v). split; [left; reflexivity|]. left. unfold chunk_iv. cbn [fst snd]. lia.
  - right; right; right; right; right; left. exists sc. split; [left; reflexivity|]. left. unfold sub_iv. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. lia.
Qed.

Definition dtouch (lo q : Z) (iv : Z * Z) : Prop := sub_iv lo q iv \/ dstat iv \/ dreg iv.
#[using="Type"] Lemma dtouch_dzone : forall lo q iv, dtouch lo q iv -> dzone lo iv.
Proof. intros lo q iv [[A _]|[A|A]]; [left; exact A| right; left; exact A| right; right; exact A]. Qed.
#[using="Type"] Lemma dtouch_dj : forall lo q W A k, Forall (dtouch lo q) W ->
  (A + k <= lo \/ q <= A) -> (A + k <= 1595336 \/ 5855224 <= A) ->
  (A + k <= DN0 D \/ DN0 D + 2^20 <= A) -> (A + k <= SS0 D \/ SS0 D + 2^23 <= A) -> disjoint_from W A k.
Proof.
  intros lo q W A k FW H1 H2 H3 H4. apply dj_of_Forall. eapply Forall_impl; [| exact FW].
  intros [a b] [[Z1 Z2]|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]]; cbn [fst snd] in *; lia.
Qed.

#[using="Type"] Lemma held_dzone_dj : forall X (m : mem) lo W c v,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held1 (fst X) (c, v) -> Forall (dzone lo) W ->
  disjoint_from W (region AL c + 16 * v) (class_size c) /\ disjoint_from W (sh (region AL c + 16 * v)) (class_size c / 8).
Proof.
  intros X m lo W c v AO LOH CLO RP RS HE FZ.
  split; apply (hull_dzone_dj X m lo W (mkQC (QPrim c v) 16 1) _ _ AO LOH CLO RP RS HE FZ); unfold qc_hull, qc_blk, qc_bsize; cbn [qc_kind];
    [left| right; left]; split; reflexivity.
Qed.

#[using="Type"] Lemma qlist_rep_frame_dc : forall X (m m' : mem) (lo q : Z) Ws ch A n l nxt,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch -> Forall (dzone lo) Ws ->
  qc_blk AL ch <= A -> A + n <= qc_blk AL ch + qc_bsize ch ->
  munch (Ws ++ [(A, A + n)]) m m' ->
  qlist_rep AL m l nxt -> Forall (fun b => held1 (fst X) (bpair b) /\ ~ In (bpair b) (prim_of ch)) l ->
  qlist_rep AL m' l nxt.
Proof.
  intros X m m' lo q Ws ch A n l nxt AO LOH CLO RP RS HK FZ HA HN MU QL FB.
  assert (TCH : Forall (held1 (fst X)) (prim_of ch)).
  { destruct ch as [[c v|sc] rz0 n0]; cbn [prim_of qc_kind]; [| constructor]. constructor; [exact HK| constructor]. }
  assert (TSI : incl (sec_of ch) (se_chunks (snd X))).
  { destruct ch as [[c v|sc] rz0 n0]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HK. }
  eapply (qlist_rep_other_g AL X m m' lo q Ws [(A, A + n)] (prim_of ch) (sec_of ch) l nxt AO LOH CLO RP RS TCH TSI MU); [| exact QL|].
  - constructor; [| constructor]. exact (held_blk_geo X m ch lo q A n AO RP RS HK HA HN).
  - eapply Forall_impl; [| exact FB]. intros b [HB NB]. split; [exact HB|]. split; [exact NB|].
    destruct (held_dzone_dj X m lo Ws K_BCLASS (qb_v b) AO LOH CLO RP RS HB FZ) as [D1 D2].
    change (class_size K_BCLASS) with 8192 in D1, D2. change (8192 / 8) with 1024 in D2. split; assumption.
Qed.

#[using="Type"] Lemma dr_inv_tstats : forall X H (m m' : mem) WB WC hrest lo q sa sb,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= sa -> sa <= sb -> sb <= q ->
  dr_inv AL E X H m WB WC hrest -> munch [(sa, sb); (THR + 2800, THR + 3168)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  (exists ts', rw_cells asegs m' (THR + TSTATS_OFF) [CB 368 ts']) ->
  dr_inv AL E X H m' WB WC hrest.
Proof.
  intros X H m m' WB WC hrest lo q sa sb AO LOH CLO LSA SAB SBQ INV MU WM MI' TS'.
  destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
  assert (FW : Forall (atouch AL lo q (fst X) (snd X) [] []) [(sa, sb); (THR + 2800, THR + 3168)]).
  { constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LSA SBQ; lia|]. constructor; [| constructor].
    right; right; left. unfold sub_iv. cbn [fst snd]. clear. lia. }
  assert (TCH : Forall (held1 (fst X)) []) by constructor.
  assert (TSI : incl (@nil schunk) (se_chunks (snd X))) by (intros d []).
  unfold dr_inv.
  split.
  { apply (RPRIM_frame_ts AL AO (fst X) _ m m' RP MU); [| exact TS']. unfold prim_clear_ts.
    constructor; [left; unfold prim_out; cbn [fst snd]; clear - LSA SAB LOH CLO ACR T3 T4 SP2 SHS; repeat split; lia|].
    constructor; [right; right; cbn [fst snd]; clear; lia| constructor]. }
  split; [exact POK|].
  split.
  { eapply (RSEC_frame_pzone AL (snd X) _ m m' lo AO LOH CLO RS MU WM).
    constructor; [unfold pzone; cbn [fst snd]; right; right; right; exact LSA|]. constructor; [| constructor].
    unfold pzone. cbn [fst snd]. right; right; left. clear. lia. }
  split; [exact MI'|].
  split. { eapply poison_env_frame; [exact PE| exact MU| exact WM|]. clear - LSA SAB CLO ACR T3. env_clear. }
  split. { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. clear - LSA SAB CLO ACR T1 T2 T3 T4 T5. env_clear. }
  split; [eapply shvis_wmono; [exact SV| exact WM]|].
  split; [exact WFS|].
  split.
  { apply Forall_forall. intros ch' Hin.
    eapply (qchunk_rep_other AL X m m' lo q _ [] [] ch' AO LOH CLO RP RS TCH TSI MU FW).
    - exact (proj1 (Forall_forall _ _) WFS ch' Hin).
    - exact (proj1 (Forall_forall _ _) REPS ch' Hin).
    - exact (proj1 (Forall_forall _ _) HKS ch' Hin).
    - intros cv _ [].
    - intros sc _ []. }
  split; [exact HKS|]. split; [exact HOK|]. split; [exact NDS|]. split; [exact BWF|].
  apply Forall_forall. intros b' Hb. destruct (proj1 (Forall_forall _ _) BREP b' Hb) as [nx RB]. exists nx.
  eapply (qbatch_rep_other AL X m m' lo q _ [] [] b' nx AO LOH CLO RP RS TCH TSI MU FW RB).
  - destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb.
  - intros [].
Qed.

#[using="Type"] Lemma qlist_rep_frame_c0 : forall X (m m' : mem) (lo q : Z) W l nxt,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> munch W m m' -> Forall (atouch AL lo q (fst X) (snd X) [] []) W ->
  qlist_rep AL m l nxt -> Forall (fun b => held1 (fst X) (bpair b)) l -> qlist_rep AL m' l nxt.
Proof.
  intros X m m' lo q W l nxt AO LOH CLO RP RS MU FW QL FB.
  eapply (qlist_rep_other AL X m m' lo q W [] [] l nxt AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) MU FW QL).
  eapply Forall_impl; [| exact FB]. intros b HB. split; [exact HB| intros []].
Qed.

#[using="Type"] Lemma block_shadow_len : forall n, 0 <= n -> Z.of_nat (length (block_shadow n)) = rup8 n / 8.
Proof.
  intros n Hn. unfold block_shadow, rup8. rewrite length_app, repeat_length, Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia).
  destruct (n mod 8 =? 0) eqn:EQ8; cbn [length Z.of_nat]; [apply Z.eqb_eq in EQ8| apply Z.eqb_neq in EQ8]; Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma shadow_cells_CB : forall (m : mem) A ks, rw_cells asegs m A (shadow_cells ks) -> exists bs, rw_cells asegs m A [CB (length ks) bs].
Proof.
  intros m A ks R. pose proof (rw_cells_merge asegs m A [] (shadow_cells ks) [] ltac:(rewrite app_nil_r; exact R)) as C.
  cbn [app] in C. rewrite cells_size_shadow in C. eexists. exact C.
Qed.

#[using="Type"] Lemma lchunk_freed : forall W (m m' : mem) ch bits actx j',
  lchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 -> munch W m m' ->
  rw_cells asegs m' (qc_hdr AL ch) [CB 4 [Z_to_bv 8 3; bits; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (wz (qc_n ch)); C8 actx] ->
  rw_cells asegs m' (qc_hdr AL ch + 16) [CB (Z.to_nat (qc_bsize ch - qc_rz ch)) j'] ->
  disjoint_from W (qc_blk AL ch) (qc_rz ch - 16) -> disjoint_from W (sh (qc_blk AL ch)) (qc_bsize ch / 8) ->
  match qc_kind ch with
  | QPrim _ _ => True
  | QSec sc => disjoint_from W (sc_beg sc + 32) 4064 /\ disjoint_from W (sh (sc_beg sc)) 512
  end ->
  pchunk_rep AL m' ch.
Proof.
  intros W m m' ch bits actx j' R WF B8 S8 MU HDR NEW DA DS DK. unfold lchunk_rep in R. unfold pchunk_rep. cbv zeta in *.
  destruct WF as (RZ16 & RZM & NR & RZN & _).
  set (B := qc_blk AL ch) in *. set (bs := qc_bsize ch) in *. set (rz := qc_rz ch) in *. set (n := qc_n ch) in *.
  assert (EH : qc_hdr AL ch = B + rz - 16) by reflexivity. rewrite EH in *. clear EH.
  assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
  demodt B8 kb. demodt S8 ks. demodt RZM kr. destruct N8 as [N8 N8m]. demodt N8m kn.
  assert (SHX : forall k, 0 <= k -> sh (B + 8 * k) = sh B + k) by (intros k Hk; unfold sh; rewrite B8; clear - Hk; Z.div_mod_to_equations; lia).
  assert (DV : rz / 8 = 2 * kr /\ rup8 n / 8 = kn /\ bs / 8 = ks /\ (bs - rz - rup8 n) / 8 = ks - 2 * kr - kn)
    by (rewrite RZM, N8m, S8; clear; Z.div_mod_to_equations; lia).
  destruct DV as (DV1 & DV2 & DV3 & DV4). rewrite DV3 in DS.
  assert (TRA : forall A cs, rw_cells asegs m A cs -> B <= A -> A + Z.of_nat (cells_size cs) <= B + rz - 16 -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DA| exact H1| lia]. }
  assert (TRS : forall A cs, rw_cells asegs m A cs -> sh B <= A -> A + Z.of_nat (cells_size cs) <= sh B + ks -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DS| exact H1| exact H2]. }
  destruct R as (_ & R2 & _ & _ & R4 & R5 & R6 & R7).
  split. { exists bits, actx. exact HDR. }
  split.
  { intros RZ32. destruct (R2 RZ32) as [R2a (j2 & R2b)]. split.
    - apply TRA; [exact R2a| clear; lia| cbn [cells_size csize Nat.add]; clear - RZ32 RZM; lia].
    - exists j2. apply TRA; [exact R2b| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ32 RZM; lia). clear. lia. }
  split. { exists j'. exact NEW. }
  split. { apply TRS; [exact R4| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV1, Z2Nat.id by (clear - RZ16 RZM; lia). clear - RZN RZM N8m S8 N8 NR. lia. }
  split.
  { replace (B + rz - 16 + 16) with (B + 8 * (2 * kr)) in * by (clear - RZM; lia). rewrite (SHX (2 * kr)) in * by (clear - RZ16 RZM; lia).
    destruct (shadow_cells_CB m _ _ R5) as [sj R5']. pose proof (block_shadow_len n ltac:(clear - NR; lia)) as BL. rewrite DV2 in BL.
    exists sj. replace (Z.to_nat (rup8 n / 8)) with (length (block_shadow n)) by (rewrite DV2; clear - BL; lia).
    apply TRS; [exact R5'| clear - RZ16 RZM; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, BL. clear - RZN RZM N8m S8. lia. }
  split.
  { replace (B + rz - 16 + 16 + rup8 n) with (B + 8 * (2 * kr + kn)) in * by (clear - RZM N8m; lia).
    rewrite (SHX (2 * kr + kn)) in * by (clear - RZ16 RZM N8 NR N8m; lia).
    apply TRS; [exact R6| clear - RZ16 RZM N8 NR N8m; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV4, Z2Nat.id by (clear - RZN RZM N8m S8; lia). clear. lia. }
  destruct (qc_kind ch) as [c v| sc]; [exact I|]. destruct DK as [DK1 DK2]. destruct R7 as [(j7 & R7a) R7b]. split.
  - exists j7. eapply rw_cells_transport_m; [exact R7a| exact MU| cbn [cells_size csize Nat.add]; exact DK1].
  - eapply rw_cells_transport_m; [exact R7b| exact MU| cbn [cells_size csize Nat.add]; exact DK2].
Qed.

#[using="Type"] Lemma hull_atouch_dj : forall X (m : mem) (lo q : Z) W tc tsc ch A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  Forall (atouch AL lo q (fst X) (snd X) tc tsc) W -> held_kind X ch ->
  (forall cv, In cv (prim_of ch) -> ~ In cv tc) -> (forall sc, In sc (sec_of ch) -> ~ In sc tsc) ->
  qc_hull AL ch A n -> disjoint_from W A n.
Proof.
  intros X m lo q W tc tsc ch A n AO LOH CLO RP RS TCH TSI FW HK NP NS HU.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  destruct ch as [[c v|sc] rz n0]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind] in HU.
  - destruct (atouch_clear_prim AL lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK TSI W c v FW HK
                (NP (c, v) ltac:(cbn; left; reflexivity))) as [DA DS].
    destruct HU as [[-> ->]|[[-> ->]|[]]]; assumption.
  - destruct (atouch_clear_sec AL lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK SSEP TSI W sc FW HK
                (NS sc ltac:(cbn; left; reflexivity))) as [DA DS].
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2].
    destruct CK as (CK1 & _).
    assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
    assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
    destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    + eapply disjoint_from_sub; [exact DA| clear; lia| clear; lia].
    + rewrite SHB, DV. eapply disjoint_from_sub; [exact DS| clear; lia| clear; lia].
    + eapply disjoint_from_sub; [exact DA| clear; lia| clear - CM1; lia].
    + eapply disjoint_from_sub; [exact DS| clear; lia| clear - CM1 CM2; Z.div_mod_to_equations; lia].
Qed.

#[using="Type"] Lemma lchunk_rep_frame_m : forall W (m m' : mem) ch,
  lchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 -> munch W m m' ->
  disjoint_from W (qc_blk AL ch) (qc_bsize ch) -> disjoint_from W (sh (qc_blk AL ch)) (qc_bsize ch / 8) ->
  match qc_kind ch with
  | QPrim _ _ => True
  | QSec sc => disjoint_from W (sc_beg sc + 32) 4064 /\ disjoint_from W (sh (sc_beg sc)) 512
  end ->
  lchunk_rep AL m' ch.
Proof.
  intros W m m' ch R WF B8 S8 MU DA DS DK. unfold lchunk_rep in *. cbv zeta in *.
  destruct WF as (RZ16 & RZM & NR & RZN & _).
  set (B := qc_blk AL ch) in *. set (bs := qc_bsize ch) in *. set (rz := qc_rz ch) in *. set (n := qc_n ch) in *.
  assert (EH : qc_hdr AL ch = B + rz - 16) by reflexivity. rewrite EH in *. clear EH.
  assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
  demodt B8 kb. demodt S8 ks. demodt RZM kr. destruct N8 as [N8 N8m]. demodt N8m kn.
  assert (SHX : forall k, 0 <= k -> sh (B + 8 * k) = sh B + k) by (intros k Hk; unfold sh; rewrite B8; clear - Hk; Z.div_mod_to_equations; lia).
  assert (DV : rz / 8 = 2 * kr /\ rup8 n / 8 = kn /\ bs / 8 = ks /\ (bs - rz - rup8 n) / 8 = ks - 2 * kr - kn)
    by (rewrite RZM, N8m, S8; clear; Z.div_mod_to_equations; lia).
  destruct DV as (DV1 & DV2 & DV3 & DV4). rewrite DV3 in DS.
  assert (TRA : forall A cs, rw_cells asegs m A cs -> B <= A -> A + Z.of_nat (cells_size cs) <= B + bs -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DA| exact H1| exact H2]. }
  assert (TRS : forall A cs, rw_cells asegs m A cs -> sh B <= A -> A + Z.of_nat (cells_size cs) <= sh B + ks -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DS| exact H1| exact H2]. }
  destruct R as ((bits & actx & BITS & R1) & R2 & (ub & R3) & (j4 & R4) & R5 & R6 & R7 & R8).
  split. { exists bits, actx. split; [exact BITS|]. apply TRA; [exact R1| clear - RZ16; lia| cbn [cells_size csize Nat.add]; clear - RZ16 RZN N8 NR; lia]. }
  split.
  { intros RZ32. destruct (R2 RZ32) as [R2a (j2 & R2b)]. split.
    - apply TRA; [exact R2a| clear; lia| cbn [cells_size csize Nat.add]; clear - RZ32 RZM RZN N8 NR; lia].
    - exists j2. apply TRA; [exact R2b| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ32 RZM; lia). clear - RZ32 RZM RZN N8 NR. lia. }
  split. { exists ub. apply TRA; [exact R3| clear - RZ16; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - NR; lia). clear - RZN N8. lia. }
  split. { exists j4. apply TRA; [exact R4| clear - RZ16 NR; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZN N8 NR; lia). clear. lia. }
  split. { apply TRS; [exact R5| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV1, Z2Nat.id by (clear - RZ16 RZM; lia). clear - RZN RZM N8m S8 N8 NR. lia. }
  split.
  { replace (B + rz - 16 + 16) with (B + 8 * (2 * kr)) in * by (clear - RZM; lia). rewrite (SHX (2 * kr)) in * by (clear - RZ16 RZM; lia).
    pose proof (block_shadow_len n ltac:(clear - NR; lia)) as BL. rewrite DV2 in BL.
    apply TRS; [exact R6| clear - RZ16 RZM; lia|]. rewrite cells_size_shadow, BL. clear - RZN RZM N8m S8. lia. }
  split.
  { replace (B + rz - 16 + 16 + rup8 n) with (B + 8 * (2 * kr + kn)) in * by (clear - RZM N8m; lia).
    rewrite (SHX (2 * kr + kn)) in * by (clear - RZ16 RZM N8 NR N8m; lia).
    apply TRS; [exact R7| clear - RZ16 RZM N8 NR N8m; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV4, Z2Nat.id by (clear - RZN RZM N8m S8; lia). clear. lia. }
  destruct (qc_kind ch) as [c v| sc]; [exact I|]. destruct DK as [DK1 DK2]. destruct R8 as [(j7 & R7a) R7b]. split.
  - exists j7. eapply rw_cells_transport_m; [exact R7a| exact MU| cbn [cells_size csize Nat.add]; exact DK1].
  - eapply rw_cells_transport_m; [exact R7b| exact MU| cbn [cells_size csize Nat.add]; exact DK2].
Qed.

#[using="Type"] Lemma lchunk_rep_hull : forall X W (m m' : mem) ch, alayout_ok AL -> RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  lchunk_rep AL m ch -> qchunk_wf ch -> munch W m m' -> (forall A n, qc_hull AL ch A n -> disjoint_from W A n) -> lchunk_rep AL m' ch.
Proof.
  intros X W m m' ch AO RP RS HK R WF MU HU.
  destruct (pchunk_geo AL X m ch AO RP RS HK) as (GB8 & GS8 & _).
  eapply lchunk_rep_frame_m; [exact R| exact WF| exact GB8| exact GS8| exact MU| | |].
  - apply HU. left. split; reflexivity.
  - apply HU. right; left. split; reflexivity.
  - destruct (qc_kind ch) as [c v|sc] eqn:EK; [exact I|]. split; apply HU; right; right; rewrite EK; [left| right]; split; reflexivity.
Qed.

Definition izone (lo : Z) (iv : Z * Z) : Prop := lo <= fst iv \/ iastat iv \/ iv = (THR + 3168, THR + 3169).

#[using="Type"] Lemma dr_inv_frame_i : forall X H (m m' : mem) WB WC hrest lo W,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  dr_inv AL E X H m WB WC hrest -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> thread_env L m' -> Forall (izone lo) W ->
  dr_inv AL E X H m' WB WC hrest.
Proof.
  intros X H m m' WB WC hrest lo W AO LOH CLO INV MU WM MI' TE' FZ.
  destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
  layout_apart_fact AO 0%nat 3%nat A03. layout_apart_fact AO 1%nat 3%nat A13.
  assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
  assert (SHL : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).

  assert (DJZ : forall A n, 0 <= n -> 6328320 <= A -> A + n <= alloc_ceiling -> (A + n <= THR \/ THR + 4096 <= A) -> disjoint_from W A n).
  { intros A n N0 HA HN HT. apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[[Z1 Z2]|[Z1 Z2]]|ZE]]; cbn [fst snd] in *; [lia| lia| lia|].
    inversion ZE; subst a b. lia. }

  assert (DJS : forall A n, 0 <= n -> 2147450880 <= A -> A + n <= 17594333495296 -> disjoint_from W A n).
  { intros A n N0 HA HN. apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[[Z1 Z2]|[Z1 Z2]]|ZE]]; cbn [fst snd] in *; [clear - Z1 HN LOH; lia| lia| lia|].
    inversion ZE; subst a b. clear - HA HN T3 N0. lia. }
  assert (IOQ : Forall img_out_q W).
  { eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[IA|ZE]]; unfold img_out_q; cbn [fst snd] in *.
    - right; left. clear - Z1 LOH. lia.
    - right; right; right; right. exact IA.
    - inversion ZE; subst a b. clear - T3. lia. }
  unfold dr_inv.
  split.
  { apply (RPRIM_frame AL AO (fst X) _ m m' RP MU WM). unfold prim_clear. eapply Forall_impl; [| exact FZ].
    intros [a b] [Z1|[[[Z1 Z2]|[Z1 Z2]]|ZE]]; left; unfold prim_out; cbn [fst snd] in *.
    - clear - Z1 LOH CLO ACR T3 T4 SP2 SHS. repeat split; lia.
    - clear - Z1 Z2 SP1 SHL T3. repeat split; lia.
    - clear - Z1 Z2 SP1 SHL T3. repeat split; lia.
    - inversion ZE; subst a b. clear - SP1 SP2 SHL SHS T3 A03. repeat split; lia. }
  split; [exact POK|].
  split.
  { pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
    eapply (RSEC_frame_but_q AL (snd X) _ m m' RS MU (wmono_but_of_wmono _ _ _ WM) IOQ).
    + clear - P1. lia.
    + apply DJZ; [lia| clear - P1; lia| clear - P2; lia| clear - A13; lia].
    + apply Forall_forall. intros d Hd. pose proof (sec_geo AL (snd X) SOK d Hd) as (D1 & D2 & D3 & _).
      pose proof (proj1 (Forall_forall _ _) COK d Hd) as (_ & _ & _ & _ & _ & _ & D7').
      unfold al_regions in D7'. do 3 (apply Forall_cons_iff in D7' as [_ D7']). apply Forall_cons_iff in D7' as [DTH _].
      cbn [fst snd] in DTH. unfold apart in DTH. apply DJZ; [lia| lia| lia| clear - DTH D2; lia]. }
  split; [exact MI'|].
  split; [exact (poison_env_frame_q E _ m m' PE MU WM IOQ)|].
  split; [exact TE'|].
  split; [eapply shvis_wmono; [exact SV| exact WM]|].
  split; [exact WFS|].
  assert (MU0 : munch (W ++ []) m m') by (rewrite app_nil_r; exact MU).
  assert (DJP : forall c v, held1 (fst X) (c, v) -> disjoint_from W (region AL c + 16 * v) (class_size c) /\ disjoint_from W (sh (region AL c + 16 * v)) (class_size c / 8)).
  { intros c v HE. pose proof (held_geo AL (fst X) AO WF0 c v HE) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & G5 & G6 & G7). rewrite G5 in G7.
    pose proof (region_range AL c Hc) as [RR1 RR2].
    split.
    - apply DJZ; [clear - CS; lia| clear - G1 RR1 SP1; lia| clear - G2 G3 RR2 SP2; lia| clear - G1 G2 G3 RR1 RR2 A03; lia].
    - apply DJS; [apply Z.div_pos; [clear - CS; lia| lia]| exact G6| exact G7]. }
  split.
  { apply Forall_forall. intros ch' Hin. pose proof (proj1 (Forall_forall _ _) HKS ch' Hin) as HK'. pose proof (proj1 (Forall_forall _ _) WFS ch' Hin) as WF'.
    eapply (qchunk_rep_other_g AL X m m' lo lo W [] [] [] ch' AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) MU0 ltac:(constructor)); [| exact WF'| exact (proj1 (Forall_forall _ _) REPS ch' Hin)| exact HK'| intros cv _ []| intros sc _ []].
    intros A n HU. destruct ch' as [[c v|sc] rz n0]; unfold held_kind in HK'; cbn [qc_kind] in HK'; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind] in HU.
    - destruct (DJP c v HK') as [DB DS]. destruct HU as [[-> ->]|[[-> ->]|[]]]; assumption.
    - pose proof (sec_geo AL (snd X) SOK sc HK') as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
      pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
      pose proof (proj1 (Forall_forall _ _) COK sc HK') as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _ & _ & _ & _ & _ & D7').
      unfold al_regions in D7'. do 3 (apply Forall_cons_iff in D7' as [_ D7']). apply Forall_cons_iff in D7' as [DTH _].
      cbn [fst snd] in DTH. unfold apart in DTH.
      assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
      assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
      destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
      + apply DJZ; [lia| lia| lia| clear - DTH CM1; lia].
      + rewrite SHB, DV. apply DJS; [clear - CM1 CM2; Z.div_mod_to_equations; lia| lia| lia].
      + apply DJZ; [lia| lia| lia| clear - DTH CM1; lia].
      + apply DJS; [lia| lia| clear - D10 CM1 CM2; Z.div_mod_to_equations; lia]. }
  split; [exact HKS|]. split; [exact HOK|]. split; [exact NDS|]. split; [exact BWF|].
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) BREP b Hb) as [nx RB]. exists nx.
  assert (HBb : held1 (fst X) (bpair b)) by (destruct HOK as [_ FH]; apply (proj1 (Forall_forall _ _) FH); apply in_or_app; left; apply in_map; exact Hb).
  destruct (DJP K_BCLASS (qb_v b) HBb) as [DB DS]. change (class_size K_BCLASS) with 8192 in DB, DS. change (8192 / 8) with 1024 in DS. fold (qb_addr AL b) in DB, DS.
  eapply (qbatch_rep_other_g AL X m m' lo lo W [] [] [] b nx AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) MU0 ltac:(constructor) DB DS RB HBb). intros [].
Qed.
End DZ.
