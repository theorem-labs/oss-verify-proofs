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
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot AQuarR AQuarS AQuarP AFrameG AQuarG.
Import ListNotations.
Open Scope Z_scope.

Section INVS.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation PARR := (al_parr AL).

  #[using="Type"] Lemma salloc_dj_app : forall a msz b s A n,
    0 <= a -> 0 <= msz -> a + msz <= 2^47 ->
    (a + msz <= b \/ b + s <= a) -> (b + s <= 0x7fff8000 \/ 0x10007fff8000 <= b) -> b <= A -> A + n <= b + s ->
    disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] A n.
  Proof.
    intros a msz b s A n A0 M0 TOP AP BM BA AN. cbn [disjoint_from].
    assert (SR : 0x7fff8000 <= sh a /\ sh a + msz / 8 <= 0x10007fff8000) by (unfold sh, SHADOW_OFF; clear - A0 M0 TOP; Z.div_mod_to_equations; lia).
    clear - AP BM BA AN SR. split; [lia|]. split; [lia| exact I].
  Qed.

  #[using="Type"] Lemma salloc_dj_sh : forall a msz b s b' s',
    app_mem a msz -> a mod 8 = 0 -> 0 <= msz -> msz mod 8 = 0 ->
    (a + msz <= b \/ b + s <= a) -> 0 <= b -> b + s <= 2^47 -> b <= b' -> b' + s' <= b + s -> 0 <= s' -> b' mod 8 = 0 ->
    disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] (sh b') (s' / 8).
  Proof.
    intros a msz b s b' s' AM A8 M0 M8 AP B0 BT BB BS S0 B8. cbn [disjoint_from]. unfold app_mem in AM.
    assert (SR : 0x7fff8000 <= sh b' /\ sh b' + s' / 8 <= 0x10007fff8000) by (unfold sh, SHADOW_OFF; clear - B0 BT BB BS S0; Z.div_mod_to_equations; lia).
    split; [clear - AM SR M0; lia|]. split; [| exact I].
    unfold sh, SHADOW_OFF. clear - A8 M8 AP BB BS S0 B8 M0. Z.div_mod_to_equations. lia.
  Qed.

  #[using="Type"] Lemma dr_inv_salloc : forall (X : pstate) (H H1 : word -> bool) (m m1 : mem) WB WC hrest lo q a size avoid,
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q ->
    dr_inv AL E X H m WB WC hrest ->
    gmunch [(lo, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (THR + 2800, THR + 3168); (PARR, PARR + 2^23);
            (a, a + sec_msize size); (sh a, sh a + sec_msize size / 8)] m m1 ->
    wmono asegs m m1 -> mem_inv asegs m1 -> poison_env E m1 -> thread_env L m1 -> shvis H1 m1 ->
    RSEC AL (sec_alloc (snd X) a size) m1 -> (exists ts, rw_cells asegs m1 (THR + 2800) [CB 368 ts]) ->
    a mod 4096 = 0 -> 0x609000 <= a -> app_mem a (sec_msize size) -> 0 < size ->
    Forall (fun iv => a + sec_msize size <= fst iv \/ snd iv <= a) avoid ->
    Forall (fun rg : Z * Z => In (fst rg, fst rg + snd rg) avoid) (al_regions AL) ->
    Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks (snd X)) ->
    dr_inv AL E (fst X, sec_alloc (snd X) a size) H1 m1 WB WC hrest.
  Proof.
    intros X H H1 m m1 WB WC hrest lo q a size avoid AO LOH CLO LQ INV GM WM MI1 PE1 TE1 SV1 RSN TSN A4K ALO AM S0 AV AREG ACH.
    destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
    assert (MB : 8192 <= sec_msize size /\ sec_msize size mod 4096 = 0) by (unfold sec_msize, rup4k; clear - S0; Z.div_mod_to_equations; lia).
    remember (sec_msize size) as msz eqn:Emsz. destruct MB as (MB & MB4K).
    assert (ATOP : 0 <= a /\ a + msz <= 2^47 /\ a mod 8 = 0 /\ msz mod 8 = 0) by (unfold app_mem in AM; clear - AM ALO A4K MB4K; Z.div_mod_to_equations; lia).
    destruct ATOP as (A0 & ATOP & A8 & M8).

    assert (RAP : forall rg, In rg (al_regions AL) -> a + msz <= fst rg \/ fst rg + snd rg <= a).
    { intros rg Hrg. pose proof (proj1 (Forall_forall _ _) AV _ (proj1 (Forall_forall _ _) AREG rg Hrg)) as X0. cbn [fst snd] in X0. exact X0. }
    pose proof (RAP _ (or_introl eq_refl)) as APS. pose proof (RAP _ (or_intror (or_introl eq_refl))) as APP.
    pose proof (RAP _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as APT. cbn [fst snd] in APS, APP, APT.
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & SP7).
    layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
    assert (SRA : 0x7fff8000 <= sh a /\ sh a + msz / 8 <= 0x10007fff8000) by (unfold sh, SHADOW_OFF; clear - A0 MB ATOP; Z.div_mod_to_equations; lia).
    layout_apart_fact AO 0%nat 1%nat LP01. layout_apart_fact AO 1%nat 3%nat LP13.
    assert (SHSP : 0x7fff8000 <= sh (al_space AL) /\ sh (al_space AL + K_SPACE + 4096) <= 0x10007fff8000
                   /\ (a + msz <= al_space AL -> sh a + msz / 8 <= sh (al_space AL))
                   /\ (al_space AL + K_SPACE + 4096 <= a -> sh (al_space AL + K_SPACE + 4096) <= sh a)).
    { unfold sh, SHADOW_OFF. clear - SP1 SP5 A0 MB. repeat split; intros; Z.div_mod_to_equations; lia. }
    destruct SHSP as (SHS1 & SHS2 & SHS3 & SHS4).
    assert (RPN : RPRIM AL (fst X) m1).
    { apply (RPRIM_frame_ts_g AL AO (fst X) _ m m1 RP (conj GM WM)); [| exact TSN].
      unfold prim_clear_ts, prim_out. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd].
      - left. clear - LOH CLO SP2 T4 SHS2. lia.
      - left. clear - SP1 SHS1 T3. lia.
      - left. clear - SP1 SHS1 T3. lia.
      - right. right. clear. lia.
      - left. clear - P1 LP01 LP13 SHS1 SHS2 SP1. lia.
      - left. unfold app_mem in AM. clear - APS APT AM ALO SHS1 SHS2 SP1. lia.
      - left. clear - SRA SP1 APS SHS3 SHS4 T3. lia. }

    assert (PHULL : forall c v, held1 (fst X) (c, v) ->
              disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] (region AL c + 16 * v) (class_size c)
              /\ disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] (sh (region AL c + 16 * v)) (class_size c / 8)).
    { intros c v HK. pose proof (held_range AL (fst X) m c v RP HK) as (R1 & R2 & R3 & R4).
      pose proof HK as (Hc & V0 & _). cbn [fst snd] in Hc, V0. pose proof (class_size_pos c Hc) as CS. pose proof (REG_mod8 AL AO c) as RG8.
      split.
      - apply (salloc_dj_app a msz (al_space AL) (K_SPACE + 4096)); [exact A0| clear - MB; lia| exact ATOP| clear - APS; lia| right; exact SP1| clear - R3; lia| clear - R4; lia].
      - apply (salloc_dj_sh a msz (al_space AL) (K_SPACE + 4096)); [exact AM| exact A8| clear - MB; lia| exact M8| clear - APS; lia| clear - SP1; lia| clear - SP5; lia
                                                                    | clear - R3; lia| clear - R4; lia| clear - CS; lia| clear - RG8; Z.div_mod_to_equations; lia]. }
    assert (SHULL : forall sc, In sc (se_chunks (snd X)) -> forall b' s', sc_beg sc <= b' -> b' + s' <= sc_beg sc + sc_msize sc -> 0 <= s' -> b' mod 8 = 0 ->
              disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] b' s'
              /\ disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] (sh b') (s' / 8)).
    { intros sc Hsc b' s' B1 B2 S'0 B8.
      pose proof (proj1 (Forall_forall _ _) SOK sc Hsc) as CK. destruct CK as (_ & CK2 & _ & _ & CK5 & CK6 & _).
      pose proof (proj1 (Forall_forall _ _) AV _ (proj1 (Forall_forall _ _) ACH sc Hsc)) as APC. cbn [fst snd] in APC.
      split.
      - apply (salloc_dj_app a msz (sc_beg sc) (sc_msize sc)); [exact A0| clear - MB; lia| exact ATOP| exact APC| clear - CK5; lia| exact B1| exact B2].
      - apply (salloc_dj_sh a msz (sc_beg sc) (sc_msize sc)); [exact AM| exact A8| clear - MB; lia| exact M8| exact APC| clear - CK2; lia| clear - CK6 ACR; lia
                                                               | exact B1| exact B2| exact S'0| exact B8]. }
    assert (HULL : forall ch', qchunk_wf ch' -> held_kind X ch' -> forall A n, qc_hull AL ch' A n -> disjoint_from [(a, a + msz); (sh a, sh a + msz / 8)] A n).
    { intros ch' WF' HK' A n HU. destruct ch' as [[c v|sc] rz' n']; unfold held_kind in HK'; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind] in HK', HU.
      - destruct (PHULL c v HK') as (D1 & D2). destruct HU as [(-> & ->)|[(-> & ->)|[]]]; assumption.
      - pose proof (proj1 (Forall_forall _ _) SOK sc HK') as CK. pose proof (chunk_ok_msize AL sc CK) as (CM1 & CM2). destruct CK as (CK1 & _).
        destruct HU as [(-> & ->)|[(-> & ->)|[(-> & ->)|(-> & ->)]]].
        + apply (SHULL sc HK' (sc_beg sc + 4096) (sc_msize sc - 4096)); [clear; lia| clear; lia| clear - CM1; lia| clear - CK1; Z.div_mod_to_equations; lia].
        + apply (SHULL sc HK' (sc_beg sc + 4096) (sc_msize sc - 4096)); [clear; lia| clear; lia| clear - CM1; lia| clear - CK1; Z.div_mod_to_equations; lia].
        + apply (SHULL sc HK' (sc_beg sc + 32) 4064); [clear; lia| clear - CM1; lia| clear; lia| clear - CK1; Z.div_mod_to_equations; lia].
        + change 512 with (4096 / 8). apply (SHULL sc HK' (sc_beg sc) 4096); [clear; lia| clear - CM1; lia| clear; lia| clear - CK1; Z.div_mod_to_equations; lia]. }

    assert (GMW : gmw ([(a, a + msz); (sh a, sh a + msz / 8)]
                       ++ [(lo, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (THR + 2800, THR + 3168); (PARR, PARR + 2^23)]) m m1).
    { split; [| exact WM]. refine (gmunch_weaken _ _ _ _ _ GM). unfold sub_fp. cbn [app outside]. intros x0 Hx0. clear - Hx0. tauto. }
    assert (FW : Forall (atouch AL lo q (fst X) (snd X) [] []) [(lo, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (THR + 2800, THR + 3168); (PARR, PARR + 2^23)]).
    { repeat (apply Forall_cons || apply Forall_nil); unfold atouch, sub_iv; cbn [fst snd].
      - left. clear - LQ. lia.
      - right; left. clear. lia.
      - right; left. clear. lia.
      - right; right; left. clear. lia.
      - do 7 right. clear. lia. }
    destruct HOK as [ND FH].
    unfold dr_inv. cbn [fst snd].
    split; [exact RPN|]. split; [exact POK|]. split; [exact RSN|].
    split; [exact MI1|]. split; [exact PE1|]. split; [exact TE1|]. split; [exact SV1|]. split; [exact WFS|].
    split.
    { apply Forall_forall. intros ch' Hin.
      pose proof (proj1 (Forall_forall _ _) WFS ch' Hin) as WF'. pose proof (proj1 (Forall_forall _ _) HKS ch' Hin) as HK'.
      eapply (qchunk_rep_other_gg AL X m m1 lo q _ _ [] [] ch' AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) GMW FW (HULL ch' WF' HK') WF').
      - exact (proj1 (Forall_forall _ _) REPS ch' Hin).
      - exact HK'.
      - intros cv _ [].
      - intros sc _ []. }
    split.
    { apply Forall_forall. intros ch' Hin. pose proof (proj1 (Forall_forall _ _) HKS ch' Hin) as HK'.
      destruct ch' as [[c' v'|sc] rz' n']; unfold held_kind in *; cbn [qc_kind fst snd] in *; [exact HK'|].
      unfold sec_alloc. cbn [se_chunks]. apply in_or_app. left. exact HK'. }
    split; [split; [exact ND| exact FH]|].
    split; [exact NDS|]. split; [exact BWF|].
    apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) BREP b Hb) as [nx BR]. exists nx.
    assert (HB : held1 (fst X) (bpair b)) by (apply (proj1 (Forall_forall _ _) FH); apply in_or_app; left; apply in_map; exact Hb).
    destruct (PHULL _ _ HB) as (D1 & D2). unfold bpair in D1, D2. change (class_size K_BCLASS) with 8192 in D1, D2. change (8192 / 8) with 1024 in D2.
    eapply (qbatch_rep_other_gg AL X m m1 lo q _ _ [] [] b nx AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) GMW FW D1 D2 BR HB).
    intros [].
  Qed.
End INVS.

