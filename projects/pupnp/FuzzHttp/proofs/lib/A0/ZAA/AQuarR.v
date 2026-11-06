(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_sec_B F_sec_C F_quar_A F_quar_As ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section ARANY.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).
  Notation PARR := (al_parr AL).

  Definition held_kind (X : pstate) (ch : qchunk) : Prop :=
    match qc_kind ch with QPrim c v => held1 (fst X) (c, v) | QSec sc => In sc (se_chunks (snd X)) end.

  Definition arec_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (q lo : Z) (X : pstate) (ch : qchunk) (H : word -> bool) (m : mem) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W,
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_recycle1 AL X ch H
      /\ munch W m m' /\ Forall (atouch AL lo q (fst X) (snd X) (prim_of ch) (sec_of ch)) W
      /\ mem_inv asegs m' /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env L m' /\ shvis H' m'
      /\ RPRIM AL (fst (recycle1 X ch)) m' /\ prim_ok (fst (recycle1 X ch)) /\ RSEC AL (snd (recycle1 X ch)) m'.

  #[using="Type"] Theorem arec_any : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32)
         (m : mem) (H : word -> bool) (q lo CBA : Z) (X : pstate) (ch : qchunk) (stackw : word),
    alayout_ok AL -> mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env L m ->
    stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - AREC_STACK -> q <= 2^47 -> q mod 16 = 0 ->
    RPRIM AL (fst X) m -> prim_ok (fst X) -> RSEC AL (snd X) m ->
    qchunk_wf ch -> qchunk_rep AL m ch -> held_kind X ch ->
    rw_cells asegs m CBA [C8 (wz CACHE); C8 stackw] -> q <= CBA -> CBA + 16 <= 2^47 ->
    implA H (t_recycle1 AL X ch)
          (arec_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo X ch H m)
          (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz CBA) (wz (qc_hdr AL ch)) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F_ (wz arec_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo CBA [P S] [kind rz n] stackw
           AO MI MC SV PE TE ST LOH CLO LO QH Q16 RP POK RS CHW CHR HELD CBC CBQ CB47.
    cbn [fst snd] in RP, POK, RS. unfold held_kind in HELD. cbn [qc_kind fst snd] in HELD.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    destruct kind as [c v | sc].

    -
      cbn [t_recycle1 qc_kind fst snd].
      eapply implA_mono.
      { eapply (arec_prim AL E ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo c v rz n CBA P stackw); eassumption. }
      intros a H' ms' PO. unfold arec_prim_post in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & -> & MUd & WMd & MId & STd & PEd & TEd & SVd & RPd & POKd).
      unfold arec_post. exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', (arec_W AL lo q c v P).
      cbn [recycle1 qc_kind fst snd H_recycle1 prim_of sec_of].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact MUd|].
      destruct HELD as (Hc & V0 & VAU & VAL & VNI). cbn [fst snd] in Hc, V0, VAU, VAL, VNI.
      pose proof RP as (_ & _ & CLS & _). pose proof (CLS c Hc) as (WFk & _).
      pose proof RPd as (_ & _ & CLSd & _). pose proof (CLSd c Hc) as (WFd & _).
      destruct WFk as (K1 & _ & _ & K4 & K5 & _ & K7 & K8 & _). destruct WFd as (D1 & _ & _ & D4 & D5 & _ & D7 & D8 & _).
      pose proof (class_size_pos c Hc) as CS.

      split.
      {
        unfold arec_W. apply Forall_app. split.
        - apply atouch_prim_W; [exact Hc| | | | | | |]; try (clear - K1 K4 K5 K7 K8 D1 D4 D5 D7 D8; lia).

        - assert (TCH : forall iv, chunk_iv AL c v iv \/ chunk_sh_iv AL c v iv -> atouch AL lo q P S [(c, v)] [] iv).
          { intros iv X. right; right; right; right; left. exists (c, v). split; [left; reflexivity| exact X]. }
          apply Forall_cons; [apply TCH; left; unfold chunk_iv; cbn [fst snd]; clear; lia|].
          apply Forall_cons; [apply TCH; right; unfold chunk_sh_iv; cbn [fst snd]; clear; lia| apply Forall_nil]. }
      split; [exact MId|]. split; [exact STd|]. split; [exact PEd|]. split; [exact TEd|]. split; [exact SVd|]. split; [exact RPd|]. split; [exact POKd|].

      pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
      layout_facts AO 1%nat LPARR. layout_apart_fact AO 0%nat 1%nat LP01. layout_apart_fact AO 1%nat 3%nat LP13. layout_apart_fact AO 0%nat 3%nat LP03.
      destruct LPARR as (P1 & P2 & _ & _ & _ & _ & _).
      assert (SHB : forall x, 0 <= x <= 2^47 -> 2147450880 <= sh x <= 17594333495296) by (intros x Hx; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
      assert (RG : region AL c = al_space AL + c * K_REGION) by reflexivity.
      assert (RIA : ri_addr AL c = al_space AL + K_SPACE + 128 * c) by reflexivity.
      assert (FAB : fa_base AL c = al_space AL + c * K_REGION + FA_OFF) by reflexivity.

      set (ZONE := fun iv : Z * Z => (al_space AL <= fst iv /\ snd iv <= al_space AL + K_SPACE + 4096) \/ (2147450880 <= fst iv /\ snd iv <= 17594333495296)
                                     \/ (THR <= fst iv /\ snd iv <= THR + 4096) \/ lo <= fst iv).
      assert (ZW : Forall ZONE (arec_W AL lo q c v P)).
      { unfold arec_W, prim_W. cbn [app].
        set (k := get_cls P c) in *. set (k' := get_cls (cache_dealloc P c v) c) in *.
        pose proof (SHB (region AL c + p_mu k) ltac:(rewrite RG; clear - Hc K7 K8 SP1 SP5; lia)) as B1.
        pose proof (SHB (region AL c + p_mu k') ltac:(rewrite RG; clear - Hc D7 D8 SP1 SP5; lia)) as B2.
        pose proof (SHB (fa_base AL c + p_mfa k) ltac:(rewrite FAB; clear - Hc K5 SP1 SP5; lia)) as B3.
        pose proof (SHB (fa_base AL c + p_mfa k') ltac:(rewrite FAB; clear - Hc D5 SP1 SP5; lia)) as B4.
        pose proof (SHB (region AL c + 16 * v) ltac:(rewrite RG; clear - Hc V0 VAU K7 K8 CS SP1 SP5; lia)) as B5.
        assert (B6 : sh (region AL c + 16 * v) + class_size c / 8 <= 17594333495296).
        { pose proof (SHB (region AL c + 16 * v + class_size c) ltac:(rewrite RG; clear - Hc V0 VAU K7 K8 CS SP1 SP5; lia)) as B6.
          revert B6. unfold sh, SHADOW_OFF. clear - CS. intros B6. Z.div_mod_to_equations. lia. }
        unfold ZONE. rewrite RG, RIA, FAB in *.
        repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd].
        - right; right; right. clear; lia.
        - left. clear - Hc; lia.
        - left. clear - Hc K1 D1 D5; lia.
        - left. clear - Hc K7 D7 D8; lia.
        - right; left. clear - B1 B2; lia.
        - right; left. clear - B3 B4; lia.
        - right; right; left. clear; lia.
        - right; right; left. clear; lia.
        - left. clear - Hc V0 VAU K7 K8 CS; lia.
        - right; left. clear - B5 B6; lia. }

      eapply (RSEC_frame_but AL S _ m m' RS MUd (wmono_but_of_wmono _ _ _ WMd)).
      + eapply Forall_impl; [| exact ZW]. unfold ZONE. intros iv Z0. clear - Z0 SP1 T3 LOH. lia.
      + clear - P1. lia.
      + apply dj_of_Forall. eapply Forall_impl; [| exact ZW]. unfold ZONE. intros iv Z0. clear - Z0 P1 P2 LP01 LP13 CLO. lia.
      + apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) COK d Hd) as (_ & D2 & _ & _ & D5' & D6 & D7').
        pose proof (chunk_ok_msize AL d (proj1 (Forall_forall _ _) COK d Hd)) as [DM _].
        unfold al_regions in D7'. apply Forall_cons_iff in D7' as [DSP D7']. apply Forall_cons_iff in D7' as [_ D7'].
        apply Forall_cons_iff in D7' as [_ D7']. apply Forall_cons_iff in D7' as [DTH _]. cbn [fst snd] in DSP, DTH. unfold apart in DSP, DTH.
        apply dj_of_Forall. eapply Forall_impl; [| exact ZW]. unfold ZONE. intros iv Z0. clear - Z0 D2 D5' D6 DM DSP DTH CLO. lia.

    -
      cbn [t_recycle1 qc_kind fst snd].
      eapply implA_mono.
      { eapply (arec_sec AL E ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo rz n CBA P S sc stackw); try eassumption.
        unfold AREC_SEC_STACK. unfold AREC_STACK, CDEALLOC_STACK, MF_STACK in LO. clear - LO. lia. }
      intros a H' ms' PO. unfold arec_sec_post in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & -> & MUd & MId & STd & PEd & TEd & SVd & RPd & RSd).
      unfold arec_post. exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', (arec_sec_W AL lo q S sc).
      cbn [recycle1 qc_kind fst snd H_recycle1 prim_of sec_of].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact MUd|].
      split.
      { unfold arec_sec_W.
        assert (INL : In (sec_last S sc) (se_chunks S)).
        { unfold sec_last. apply nth_In. destruct (se_chunks S) as [|x l]; [destruct HELD| cbn [length]; clear; lia]. }
        repeat (apply Forall_cons || apply Forall_nil); unfold atouch, sub_iv; cbn [fst snd].
        - left. clear; lia.
        - right; left. clear; lia.
        - right; left. clear; lia.
        - right; right; left. clear; lia.
        - right; right; right; right; right; right; right. clear; lia.
        - right; right; right; right; right; left. exists sc. split; [left; reflexivity| left; clear; lia].
        - right; right; right; right; right; left. exists sc. split; [left; reflexivity| right; clear; lia].
        - right; right; right; right; right; right; left. exists (sec_last S sc). split; [exact INL| clear; lia]. }
      split; [exact MId|]. split; [exact STd|]. split; [exact PEd|]. split; [exact TEd|]. split; [exact SVd|]. split; [exact RPd|]. split; [exact POK| exact RSd].
  Qed.

  #[using="Type"] Lemma sh_add8 : forall A n, A mod 8 = 0 -> n mod 8 = 0 -> sh (A + n) = sh A + n / 8.
  Proof. intros A n HA Hn. unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.

  Section CLEAR.
    Variables (lo q : Z) (P0 : prim) (S0 : asec) (tc : list (Z * Z)) (tsc : list schunk).
    Hypothesis AO : alayout_ok AL.
    Hypothesis WF0 : forall c, 1 <= c <= 31 -> pclass_wf c (get_cls P0 c).
    Hypothesis LOH : 0x10007fff8000 <= lo.
    Hypothesis CLO : alloc_ceiling <= lo.
    Hypothesis TCH : Forall (held1 P0) tc.
    Hypothesis SOK : Forall (chunk_ok AL) (se_chunks S0).
    Hypothesis SSEP : chunks_sep (se_chunks S0).
    Hypothesis TSI : incl tsc (se_chunks S0).

    #[using="HC AO WF0"] Lemma held_geo : forall c v, held1 P0 (c, v) ->
      let B := region AL c + 16 * v in
      1 <= c <= 31 /\ region AL c <= B /\ B + class_size c <= region AL c + p_au (get_cls P0 c)
      /\ p_au (get_cls P0 c) <= FA_OFF /\ 32 <= class_size c <= 65536
      /\ sh (B + class_size c) = sh B + class_size c / 8 /\ 2147450880 <= sh B /\ sh (B + class_size c) <= 17594333495296.
    Proof.
      intros c v (Hc & V0 & VAU & VAL & _) B. cbn [fst snd] in *.
      pose proof (WF0 c Hc) as (_ & _ & _ & _ & _ & _ & K7 & K8 & _).
      pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CM.
      layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
      pose proof (region_range AL c Hc) as [R1 R2].
      assert (RG : region AL c = al_space AL + c * K_REGION) by reflexivity.
      split; [exact Hc|]. split; [unfold B; lia|]. split; [unfold B; lia|]. split; [lia|]. split; [exact CS|].
      split. { apply sh_add8; [unfold B; rewrite RG; clear - SPM; Z.div_mod_to_equations; lia| clear - CM; Z.div_mod_to_equations; lia]. }
      unfold B. unfold sh, SHADOW_OFF. clear - R1 R2 SP1 SP5 V0 VAU K7 K8 CS. split; Z.div_mod_to_equations; lia.
    Qed.

    #[using="SOK"] Lemma sec_geo : forall d, In d (se_chunks S0) ->
      6328320 <= sc_beg d /\ 8192 <= sc_msize d /\ sc_beg d + sc_msize d <= alloc_ceiling
      /\ (sc_beg d + sc_msize d < 2147450880 \/ 17594333495296 <= sc_beg d)
      /\ (sc_beg d + sc_msize d <= al_space AL \/ al_space AL + (K_SPACE + 4096) <= sc_beg d)
      /\ (sc_beg d + sc_msize d <= al_parr AL \/ al_parr AL + 2^23 <= sc_beg d)
      /\ (sc_beg d + sc_msize d <= THR \/ THR + 4096 <= sc_beg d)
      /\ sh (sc_beg d + sc_msize d) = sh (sc_beg d) + sc_msize d / 8
      /\ 2147450880 <= sh (sc_beg d) /\ sh (sc_beg d + sc_msize d) <= 17594333495296.
    Proof.
      intros d Hd. pose proof (proj1 (Forall_forall _ _) SOK d Hd) as CK.
      pose proof (chunk_ok_msize AL d CK) as [CM1 CM2]. destruct CK as (CK1 & CK2 & _ & _ & CK5 & CK6 & CK7).
      unfold al_regions in CK7. apply Forall_cons_iff in CK7 as [CSP CK7]. apply Forall_cons_iff in CK7 as [CPA CK7].
      apply Forall_cons_iff in CK7 as [_ CK7]. apply Forall_cons_iff in CK7 as [CTH _]. cbn [fst snd] in CSP, CPA, CTH. unfold apart in CSP, CPA, CTH.
      pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
      split; [exact CK2|]. split; [exact CM1|]. split; [exact CK6|]. split; [clear - CK5; lia|]. split; [exact CSP|]. split; [exact CPA|]. split; [exact CTH|].
      split. { apply sh_add8; [clear - CK1; Z.div_mod_to_equations; lia| clear - CM2; Z.div_mod_to_equations; lia]. }
      unfold sh, SHADOW_OFF. clear - CK2 CK6 ACR CM1. split; Z.div_mod_to_equations; lia.
    Qed.

    #[using="HC AO WF0 LOH CLO TCH SOK TSI"] Lemma atouch_clear_prim : forall W c v,
      Forall (atouch AL lo q P0 S0 tc tsc) W -> held1 P0 (c, v) -> ~ In (c, v) tc ->
      disjoint_from W (region AL c + 16 * v) (class_size c) /\ disjoint_from W (sh (region AL c + 16 * v)) (class_size c / 8).
    Proof.
      intros W c v FW HE NI. pose proof (held_geo c v HE) as G. cbv zeta in G.
      set (B := region AL c + 16 * v) in *. destruct G as (Hc & G1 & G2 & G3 & CS & G5 & G6 & G7).
      pose proof HE as (_ & V0 & VAU & VAL & _). cbn [fst snd] in V0, VAU, VAL.
      layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
      layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _). layout_apart_fact AO 0%nat 1%nat LP01. layout_apart_fact AO 0%nat 3%nat LP03.
      pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
      pose proof (region_range AL c Hc) as [R1 R2].
      assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
      pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
      assert (KEY : forall iv, atouch AL lo q P0 S0 tc tsc iv ->
                (B + class_size c <= fst iv \/ snd iv <= B) /\ (sh B + class_size c / 8 <= fst iv \/ snd iv <= sh B)).
      { intros iv A. rewrite <- G5. unfold atouch, sub_iv in A.
        destruct A as [A|[A|[A|[A|[A|[A|[A|A]]]]]]].
        - clear - A G2 G3 G7 R2 SP2 CLO LOH. lia.
        - clear - A G1 G6 R1 SP1. lia.
        - clear - A G1 G2 G3 G6 G7 R1 R2 LP03 T3 T4. lia.
        - destruct A as (c0 & Hc0 & [A|[A|A]]).
          + unfold ri_addr, RIB in A. clear - A G2 G3 G7 R2 SP1 Hc0. lia.
          + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. rewrite !RGE in *.
            pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K7 & _).
            assert (c0 = c \/ c0 < c \/ c < c0) as [->|[LT|GT]] by lia.
            * clear - A G1 G2 G7 SP1 Hc CS K7. lia.
            * clear - A G1 G2 G7 SP1 LT Hc Hc0 CS K7. lia.
            * clear - A G1 G2 G3 G7 SP1 GT Hc Hc0 CS K7. lia.
          + pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K7 & K8 & _).
            pose proof (region_range AL c0 Hc0) as [Q1 Q2].
            assert (SHI : sh (region AL (c0 + 1)) <= 17594333495296).
            { rewrite RGE in *. unfold sh, SHADOW_OFF. clear - Q2 SP5. Z.div_mod_to_equations. lia. }
            assert (c0 = c \/ c0 < c \/ c < c0) as [->|[LT|GT]] by lia.
            * pose proof (sh_le _ _ G2). clear - A H SHI G1 R1 SP1. lia.
            * pose proof (sh_le (region AL (c0 + 1)) B ltac:(rewrite !RGE in *; clear - G1 LT; lia)). clear - A H SHI G1 R1 SP1. lia.
            * pose proof (sh_le (B + class_size c) (region AL c0 + p_au (get_cls P0 c0)) ltac:(rewrite !RGE in *; clear - G2 G3 GT K7; lia)).
              clear - A H SHI G1 R1 SP1. lia.
        - destruct A as ([c1 v1] & Hin & A). cbn [fst snd] in A.
          pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo c1 v1 HE1) as G'. cbv zeta in G'.
          set (B1 := region AL c1 + 16 * v1) in *. destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7).
          pose proof HE1 as (_ & _ & _ & VAL1 & _). cbn [fst snd] in VAL1.
          pose proof (region_range AL c1 Hc1) as [Q1 Q2].
          assert (AP : B + class_size c <= B1 \/ B1 + class_size c1 <= B).
          { assert (c1 = c \/ c1 < c \/ c < c1) as [EC|[LT|GT]] by lia.
            - subst c1. assert (NV : v <> v1) by (intros ->; apply NI; exact Hin).
              pose proof (chunks_apart c v v1 Hc VAL VAL1 NV). unfold B, B1. clear - H. lia.
            - right. unfold B, B1 in *. rewrite !RGE in *. clear - H2 H3 G1 LT. lia.
            - left. unfold B, B1 in *. rewrite !RGE in *. clear - G2 G3 H1 GT. lia. }
          unfold chunk_iv, chunk_sh_iv in A. fold B1 in A. rewrite <- H5 in A.
          destruct AP as [AP|AP].
          + pose proof (sh_le _ _ AP). destruct A as [A|A]; [clear - A AP H7 G7 Q1 SP1 H1; lia| clear - A H H7 G1 R1 SP1; lia].
          + pose proof (sh_le _ _ AP). destruct A as [A|A]; [clear - A AP H7 G7 Q1 SP1 H1 G1 R1; lia| clear - A H H7 G1 R1 SP1; lia].
        - destruct A as (sc & Hin & A). pose proof (sec_geo sc (TSI sc Hin)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
          rewrite <- D8 in A.
          assert (AP : sc_beg sc + sc_msize sc <= B \/ B + class_size c <= sc_beg sc) by (clear - D5 G1 G2 G3 R1 R2; lia).
          destruct AP as [AP|AP]; pose proof (sh_le _ _ AP); destruct A as [A|A].
          all: try (clear - A AP D4 G6 G7; lia). all: clear - A H D10 G1 R1 SP1; lia.
        - destruct A as (d & Hin & A). pose proof (sec_geo d Hin) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
          clear - A D2 D4 D5 G1 G2 G3 G6 G7 R1 R2. lia.
        - clear - A P1 LP01 G1 G2 G3 G6 G7 R1 R2. lia. }
      split; apply dj_of_Forall; (eapply Forall_impl; [| exact FW]); intros iv A; destruct (KEY iv A) as [K1 K2]; [clear - K1; lia| clear - K2; lia].
    Qed.

    #[using="HC AO WF0 LOH CLO TCH SOK SSEP TSI"] Lemma atouch_clear_sec : forall W d,
      Forall (atouch AL lo q P0 S0 tc tsc) W -> In d (se_chunks S0) -> ~ In d tsc ->
      disjoint_from W (sc_beg d + 32) (sc_msize d - 32) /\ disjoint_from W (sh (sc_beg d)) (sc_msize d / 8).
    Proof.
      intros W d FW HD NI. pose proof (sec_geo d HD) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
      layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
      pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
      layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
      assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
      pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
      set (B := sc_beg d) in *. set (MS := sc_msize d) in *.
      assert (KEY : forall iv, atouch AL lo q P0 S0 tc tsc iv ->
                (B + MS <= fst iv \/ snd iv <= B + 32) /\ (sh B + MS / 8 <= fst iv \/ snd iv <= sh B)).
      { intros iv A. rewrite <- D8. unfold atouch, sub_iv in A.
        destruct A as [A|[A|[A|[A|[A|[A|[A|A]]]]]]].
        - clear - A D3 D10 CLO LOH. lia.
        - clear - A D1 D9. lia.
        - clear - A D7 D9 D10 T3 T4. lia.
        - destruct A as (c0 & Hc0 & [A|[A|A]]).
          + unfold ri_addr, RIB in A. clear - A D5 D10 SP1 Hc0. lia.
          + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K7 & _).
            rewrite !RGE in *. clear - A D5 D10 SP1 Q1 Q2 K7 Hc0. lia.
          + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K7 & K8 & _).
            assert (SHI : sh (region AL (c0 + 1)) <= 17594333495296 /\ 2147450880 <= sh (region AL c0 + p_au (get_cls P0 c0))).
            { rewrite !RGE in *. unfold sh, SHADOW_OFF. clear - Q1 Q2 SP1 SP5 K7. split; Z.div_mod_to_equations; lia. }
            destruct D5 as [D5|D5].
            * pose proof (sh_le (B + MS) (region AL c0 + p_au (get_cls P0 c0)) ltac:(rewrite !RGE in *; clear - D5 Q1 K7; lia)).
              clear - A H SHI D4 D2. lia.
            * pose proof (sh_le (region AL (c0 + 1)) B ltac:(rewrite !RGE in *; clear - D5 Q2; lia)).
              clear - A H SHI D4 D2. lia.
        - destruct A as ([c1 v1] & Hin & A). cbn [fst snd] in A.
          pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo c1 v1 HE1) as G'. cbv zeta in G'.
          set (B1 := region AL c1 + 16 * v1) in *. destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7).
          pose proof (region_range AL c1 Hc1) as [Q1 Q2].
          unfold chunk_iv, chunk_sh_iv in A. fold B1 in A. rewrite <- H5 in A.
          assert (AP : B + MS <= B1 \/ B1 + class_size c1 <= B) by (clear - D5 H1 H2 H3 Q1 Q2; lia).
          destruct AP as [AP|AP]; pose proof (sh_le _ _ AP); destruct A as [A|A].
          all: clear - A AP H D2 D4 D9 D10 H1 H2 H6 H7 Q1 Q2 SP1; lia.
        - destruct A as (sc & Hin & A). pose proof (sec_geo sc (TSI sc Hin)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
          rewrite <- E8 in A.
          assert (NE : sc <> d) by (intros ->; apply NI; exact Hin).
          destruct (chunks_sep_In2 _ SSEP sc d (TSI sc Hin) HD) as [EQ|[AP|AP]]; [contradiction| |]; unfold apart_chunks in AP; fold B MS in AP.
          + assert (AP' : sc_beg sc + sc_msize sc <= B \/ B + MS <= sc_beg sc) by (clear - AP; lia).
            destruct AP' as [AP'|AP']; pose proof (sh_le _ _ AP'); destruct A as [A|A].
            all: clear - A AP' H E4 E2 D4 D2 D9 D10 E9 E10; lia.
          + assert (AP' : sc_beg sc + sc_msize sc <= B \/ B + MS <= sc_beg sc) by (clear - AP; lia).
            destruct AP' as [AP'|AP']; pose proof (sh_le _ _ AP'); destruct A as [A|A].
            all: clear - A AP' H E4 E2 D4 D2 D9 D10 E9 E10; lia.
        - destruct A as (e & Hin & A). pose proof (sec_geo e Hin) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
          destruct (chunks_sep_In2 _ SSEP e d Hin HD) as [EQ|[AP|AP]].
          + subst e. unfold B, MS in *. clear - A D4 D2 D9 D10. lia.
          + unfold apart_chunks in AP. fold B MS in AP. clear - A AP E2 E4 D4 D2 D9 D10. lia.
          + unfold apart_chunks in AP. fold B MS in AP. clear - A AP E2 E4 D4 D2 D9 D10. lia.
        - clear - A P1 D6 D4 D2 D9 D10. lia. }
      split; apply dj_of_Forall; (eapply Forall_impl; [| exact FW]); intros iv A; destruct (KEY iv A) as [K1 K2]; [clear - K1; lia| clear - K2; lia].
    Qed.

  End CLEAR.

  Ltac demodz H z :=
    unfold id in H;
    lazymatch type of H with
    | ?a mod ?b = 0 => apply (proj1 (Z.mod_divide a b ltac:(lia))) in H; unfold Z.divide in H; destruct H as [z H]
    end.

  #[using="Type"] Lemma qchunk_rep_frame_m : forall W (m m' : mem) ch,
    qchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 -> munch W m m' ->
    disjoint_from W (qc_blk AL ch) (qc_bsize ch) -> disjoint_from W (sh (qc_blk AL ch)) (qc_bsize ch / 8) ->
    match qc_kind ch with
    | QPrim _ _ => True
    | QSec sc => disjoint_from W (sc_beg sc + 32) 4064 /\ disjoint_from W (sh (sc_beg sc)) 512
    end ->
    qchunk_rep AL m' ch.
  Proof.
    intros W m m' ch R WF B8 S8 MU DA DS DK. unfold qchunk_rep in *. cbv zeta in *.
    destruct WF as (RZ16 & RZM & NR & RZN & _).
    set (B := qc_blk AL ch) in *. set (bs := qc_bsize ch) in *. set (rz := qc_rz ch) in *. set (n := qc_n ch) in *.
    assert (EH : qc_hdr AL ch = B + rz - 16) by reflexivity. rewrite EH in *. clear EH.
    assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
    demodz B8 kb. demodz S8 ks. demodz RZM kr. destruct N8 as [N8 N8m]. demodz N8m kn.
    assert (SHX : forall k, 0 <= k -> sh (B + 8 * k) = sh B + k) by (intros k Hk; unfold sh; rewrite B8; clear - Hk; Z.div_mod_to_equations; lia).
    assert (DV : rz / 8 = 2 * kr /\ rup8 n / 8 = kn /\ bs / 8 = ks /\ (bs - rz - rup8 n) / 8 = ks - 2 * kr - kn)
      by (rewrite RZM, N8m, S8; clear; Z.div_mod_to_equations; lia).
    destruct DV as (DV1 & DV2 & DV3 & DV4). rewrite DV3 in DS.
    assert (TRA : forall A cs, rw_cells asegs m A cs -> B <= A -> A + Z.of_nat (cells_size cs) <= B + bs -> rw_cells asegs m' A cs).
    { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DA| exact H1| exact H2]. }
    assert (TRS : forall A cs, rw_cells asegs m A cs -> sh B <= A -> A + Z.of_nat (cells_size cs) <= sh B + ks -> rw_cells asegs m' A cs).
    { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DS| exact H1| exact H2]. }
    destruct R as ((bits & actx & R1) & R2 & (j3 & R3) & R4 & R5 & R6 & R7).
    split. { exists bits, actx. apply TRA; [exact R1| clear - RZ16; lia| cbn [cells_size csize Nat.add]; clear - RZ16 RZN N8 NR; lia]. }
    split.
    { intros RZ32. destruct (R2 RZ32) as [R2a (j2 & R2b)]. split.
      - apply TRA; [exact R2a| clear; lia| cbn [cells_size csize Nat.add]; clear - RZ32 RZM RZN N8 NR; lia].
      - exists j2. apply TRA; [exact R2b| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ32 RZM; lia). clear - RZ32 RZM RZN N8 NR. lia. }
    split. { exists j3. apply TRA; [exact R3| clear - RZ16; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZN N8 NR; lia). clear. lia. }
    split. { apply TRS; [exact R4| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV1, Z2Nat.id by (clear - RZ16 RZM; lia). clear - RZN RZM N8m S8 N8 NR. lia. }
    split.
    { replace (B + rz - 16 + 16) with (B + 8 * (2 * kr)) in * by (clear - RZM; lia). rewrite (SHX (2 * kr)) in * by (clear - RZ16 RZM; lia).
      apply TRS; [exact R5| clear - RZ16 RZM; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV2, Z2Nat.id by (clear - N8 NR N8m; lia). clear - RZN RZM N8m S8. lia. }
    split.
    { replace (B + rz - 16 + 16 + rup8 n) with (B + 8 * (2 * kr + kn)) in * by (clear - RZM N8m; lia).
      rewrite (SHX (2 * kr + kn)) in * by (clear - RZ16 RZM N8 NR N8m; lia).
      apply TRS; [exact R6| clear - RZ16 RZM N8 NR N8m; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV4, Z2Nat.id by (clear - RZN RZM N8m S8; lia). clear. lia. }
    destruct (qc_kind ch) as [c v| sc]; [exact I|]. destruct DK as [DK1 DK2]. destruct R7 as [(j7 & R7a) R7b]. split.
    - exists j7. eapply rw_cells_transport_m; [exact R7a| exact MU| cbn [cells_size csize Nat.add]; exact DK1].
    - eapply rw_cells_transport_m; [exact R7b| exact MU| cbn [cells_size csize Nat.add]; exact DK2].
  Qed.

  #[using="Type"] Lemma remove_nodup_mid : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ x :: l2) -> List.remove cv_eq_dec x (l1 ++ x :: l2) = l1 ++ l2.
  Proof.
    intros l1 l2 x ND. apply NoDup_remove_2 in ND as NI. rewrite List.remove_app. cbn [List.remove].
    destruct (cv_eq_dec x x) as [_|NE]; [| contradiction].
    rewrite (List.notin_remove cv_eq_dec l1 x), (List.notin_remove cv_eq_dec l2 x); [reflexivity| |]; intros Hin; apply NI; apply in_or_app; [right| left]; exact Hin.
  Qed.

  #[using="Type"] Lemma get_cls_cdealloc_other : forall P c v c', 1 <= c <= 31 -> c' <> c -> get_cls (cache_dealloc P c v) c' = get_cls P c'.
  Proof.
    intros P c v c' Hc NE. unfold cache_dealloc. destruct P as [cls ini ca cm]. cbn [pr_cls pr_inited pr_calloc pr_cmapped].
    destruct (Z_lt_le_dec c' 0) as [NEG|POS].
    - unfold get_cls. cbn [pr_cls]. replace (Z.to_nat c') with (Z.to_nat 0) by lia. apply nth_set_nth_other. lia.
    - rewrite get_cls_set_other by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma held_ok_cdealloc : forall P hs1 hs2 c v, length (pr_cls P) = 32%nat -> 1 <= c <= 31 ->
    held_ok P (hs1 ++ (c, v) :: hs2) -> held_ok (cache_dealloc P c v) (hs1 ++ hs2).
  Proof.
    intros P hs1 hs2 c v LEN Hc HO. pose proof HO as [ND _]. rewrite <- (remove_nodup_mid hs1 hs2 (c, v) ND).
    assert (EK : get_cls (cache_dealloc P c v) c = cache_dealloc_cls (get_cls P c) c v).
    { unfold cache_dealloc. destruct P as [cls ini ca cm]. cbn [pr_cls pr_inited pr_calloc pr_cmapped] in *. apply get_cls_set_same; [exact LEN| lia]. }
    apply (held_ok_push P (cache_dealloc P c v) _ c v HO).
    - apply in_or_app. right. left. reflexivity.
    - intros c' NE. apply get_cls_cdealloc_other; assumption.
    - rewrite EK. apply cache_push_au.
    - intros x. rewrite EK. unfold cls_free. rewrite cache_dealloc_cls_eq, push_cls_free.
      destruct (p_cnt (get_cls P c) =? max_count c); [rewrite drain_cls_free|]; reflexivity.
  Qed.

  #[using="Type"] Lemma skipn_cons_nth : forall {X} (l : list X) (i : nat) (x : X), nth_error l i = Some x -> skipn i l = x :: skipn (Datatypes.S i) l.
  Proof. induction l as [|y l IH]; intros [|i] x NTH; cbn in *; try discriminate; [injection NTH as <-; reflexivity| exact (IH i x NTH)]. Qed.

  #[using="Type"] Lemma remove_at_keeps : forall (l : list schunk) (i : nat) (c d : schunk),
    nth_error l i = Some c -> In d l -> d <> c -> In d (remove_at l i).
  Proof.
    intros l i c d NTH IN NE. pose proof (nth_error_lt _ _ _ NTH) as Hi.
    destruct (rev l) as [|lastc r] eqn:ER; [apply (f_equal (@length _)) in ER; rewrite length_rev in ER; cbn in ER; lia|].
    pose proof (rev_cons_split l lastc r ER) as EL. set (l' := rev r) in *. rewrite EL in *. rewrite remove_at_snoc.
    rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.eqb_spec i (length l')) as [EI|NEi].
    - subst i. rewrite nth_error_app2, Nat.sub_diag in NTH by lia. cbn in NTH. injection NTH as <-.
      apply in_app_or in IN as [IN|[<-|[]]]; [exact IN| contradiction].
    - assert (Hi' : (i < length l')%nat) by lia. rewrite nth_error_app1 in NTH by exact Hi'.
      apply in_app_or in IN as [IN|[<-|[]]]; [| apply in_or_app; right; left; reflexivity].
      rewrite <- (firstn_skipn i l') in IN. apply in_app_or in IN as [IN|IN]; [apply in_or_app; left; exact IN|].
      rewrite (skipn_cons_nth l' i c NTH) in IN. destruct IN as [<-|IN]; [contradiction|]. apply in_or_app. right. right. exact IN.
  Qed.

  #[using="Type"] Lemma qbatch_rep_frame_m : forall W (m m' : mem) b nx,
    qbatch_rep AL m b nx -> munch W m m' ->
    disjoint_from W (qb_addr AL b) 8192 -> disjoint_from W (sh (qb_addr AL b)) 1024 -> qbatch_rep AL m' b nx.
  Proof.
    intros W m m' b nx (R1 & (ws & R2 & LW & FW) & R3) MU DA DS. unfold qbatch_rep.
    split. { eapply rw_cells_transport_m; [exact R1| exact MU|]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact DA| lia| lia]. }
    split. { exists ws. split; [| split; [exact LW| exact FW]]. eapply u64arr_transport_m; [exact R2| exact MU|]. rewrite LW.
             eapply disjoint_from_sub; [exact DA| lia| lia]. }
    eapply rw_cells_transport_m; [exact R3| exact MU|]. cbn [cells_size csize Nat.add]. exact DS.
  Qed.

  Definition bpair (b : qbatch) : Z * Z := (K_BCLASS, qb_v b).

  Definition qbatch_wf0 (b : qbatch) : Prop :=
    0 <= qb_v b /\ (16 * qb_v b) mod Q_BBYTES = 0 /\ 0 <= qb_count b <= Q_BATCH /\ Forall qchunk_wf (qb_chunks b).

  Definition dr_inv (X : pstate) (H : word -> bool) (m : mem) (WB : list qbatch) (WC : list qchunk) (hrest : list (Z * Z)) : Prop :=
    RPRIM AL (fst X) m /\ prim_ok (fst X) /\ RSEC AL (snd X) m
    /\ mem_inv asegs m /\ poison_env E m /\ thread_env L m /\ shvis H m
    /\ Forall qchunk_wf WC /\ Forall (qchunk_rep AL m) WC /\ Forall (held_kind X) WC
    /\ held_ok (fst X) (map bpair WB ++ flat_map prim_of WC ++ hrest)
    /\ List.NoDup (flat_map sec_of WC)
    /\ Forall qbatch_wf0 WB /\ Forall (fun b => exists nx, qbatch_rep AL m b nx) WB.

  #[using="Type"] Lemma clear_ctx : forall X (m : mem), RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
    (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls (fst X) c)) /\ Forall (chunk_ok AL) (se_chunks (snd X)) /\ chunks_sep (se_chunks (snd X)).
  Proof.
    intros X m (_ & _ & CLS & _) (SWF & _). split; [intros c Hc; exact (proj1 (CLS c Hc))|].
    destruct SWF as (_ & _ & _ & _ & _ & COK & CSEP). split; assumption.
  Qed.

  #[using="Type"] Lemma qchunk_rep_other : forall X (m m' : mem) lo q W tc tsc ch',
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
    RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
    Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
    munch W m m' -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
    qchunk_wf ch' -> qchunk_rep AL m ch' -> held_kind X ch' ->
    (forall cv, In cv (prim_of ch') -> ~ In cv tc) -> (forall sc, In sc (sec_of ch') -> ~ In sc tsc) ->
    qchunk_rep AL m' ch'.
  Proof.
    intros X m m' lo q W tc tsc ch' AO LOH CLO RP RS TCH TSI MU FW WF R HK NP NS.
    destruct (clear_ctx X m RP RS) as (WF0 & SOK & SSEP).
    destruct ch' as [[c v|sc] rz n]; unfold held_kind in HK; cbn [qc_kind] in HK.
    - destruct (atouch_clear_prim lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK TSI W c v FW HK
                  (NP (c, v) ltac:(cbn; left; reflexivity))) as [DA DS].
      pose proof HK as (Hc & _). cbn [fst] in Hc. pose proof (class_size_mod16 c Hc) as CM.
      layout_facts AO 0%nat SPF. destruct SPF as (_ & _ & SPM & _).
      eapply qchunk_rep_frame_m; [exact R| exact WF| | | exact MU| exact DA| exact DS| exact I].
      + unfold qc_blk. cbn [qc_kind]. unfold region. clear - SPM. Z.div_mod_to_equations. lia.
      + unfold qc_bsize. cbn [qc_kind]. clear - CM. Z.div_mod_to_equations. lia.
    - destruct (atouch_clear_sec lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK SSEP TSI W sc FW HK
                  (NS sc ltac:(cbn; left; reflexivity))) as [DA DS].
      pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2].
      destruct CK as (CK1 & _).
      assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
      assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
      eapply qchunk_rep_frame_m; [exact R| exact WF| | | exact MU| | |].
      + unfold qc_blk. cbn [qc_kind]. clear - CK1. Z.div_mod_to_equations. lia.
      + unfold qc_bsize. cbn [qc_kind]. clear - CM2. Z.div_mod_to_equations. lia.
      + unfold qc_blk, qc_bsize. cbn [qc_kind]. eapply disjoint_from_sub; [exact DA| clear; lia| clear; lia].
      + unfold qc_blk, qc_bsize. cbn [qc_kind]. rewrite SHB, DV. eapply disjoint_from_sub; [exact DS| clear; lia| clear; lia].
      + cbn [qc_kind]. split; [eapply disjoint_from_sub; [exact DA| clear; lia| clear - CM1; lia]| eapply disjoint_from_sub; [exact DS| clear; lia| clear - CM1 CM2; Z.div_mod_to_equations; lia]].
  Qed.

  #[using="Type"] Lemma qbatch_rep_other : forall X (m m' : mem) lo q W tc tsc b nx,
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
    RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
    Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
    munch W m m' -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
    qbatch_rep AL m b nx -> held1 (fst X) (bpair b) -> ~ In (bpair b) tc ->
    qbatch_rep AL m' b nx.
  Proof.
    intros X m m' lo q W tc tsc b nx AO LOH CLO RP RS TCH TSI MU FW R HK NP.
    destruct (clear_ctx X m RP RS) as (WF0 & SOK & SSEP).
    destruct (atouch_clear_prim lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK TSI W K_BCLASS (qb_v b) FW HK NP) as [DA DS].
    change (class_size K_BCLASS) with 8192 in DA, DS. change (8192 / 8) with 1024 in DS.
    eapply qbatch_rep_frame_m; [exact R| exact MU| exact DA| exact DS].
  Qed.

  #[using="Type"] Lemma NoDup_app_cons_not_in : forall {X} (l1 : list X) x l2 y, List.NoDup (l1 ++ x :: l2) -> In y (l1 ++ l2) -> y <> x.
  Proof. intros X l1 x l2 y ND IN ->. apply NoDup_remove_2 in ND. exact (ND IN). Qed.

  #[using="Type"] Lemma dr_inv_chunk : forall X H H1 (m m' : mem) ch WC WB hrest lo q W,
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
    dr_inv X H m WB (ch :: WC) hrest ->
    munch W m m' -> Forall (atouch AL lo q (fst X) (snd X) (prim_of ch) (sec_of ch)) W ->
    mem_inv asegs m' -> poison_env E m' -> thread_env L m' -> shvis H1 m' ->
    RPRIM AL (fst (recycle1 X ch)) m' -> prim_ok (fst (recycle1 X ch)) -> RSEC AL (snd (recycle1 X ch)) m' ->
    dr_inv (recycle1 X ch) H1 m' WB WC hrest.
  Proof.
    intros X H H1 m m' ch WC WB hrest lo q W AO LOH CLO INV MU FW MI' PE' TE' SV' RP' POK' RS'.
    destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    apply Forall_cons_iff in WFS as [WFc WFS]. apply Forall_cons_iff in REPS as [REPc REPS]. apply Forall_cons_iff in HKS as [HKc HKS].
    pose proof HOK as [NDH FH].
    assert (TCH : Forall (held1 (fst X)) (prim_of ch)).
    { destruct ch as [[c v|sc] rz n]; cbn [prim_of qc_kind]; [| constructor]. constructor; [exact HKc| constructor]. }
    assert (TSI : incl (sec_of ch) (se_chunks (snd X))).
    { destruct ch as [[c v|sc] rz n]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HKc. }
    assert (NP : forall cv, In cv (map bpair WB ++ flat_map prim_of WC ++ hrest) -> ~ In cv (prim_of ch)).
    { intros cv Hin Hc. destruct ch as [[c v|sc] rz n]; cbn [prim_of qc_kind] in Hc; [| exact Hc]. destruct Hc as [<-|[]].
      cbn [flat_map prim_of qc_kind app] in NDH.
      apply (NoDup_app_cons_not_in (map bpair WB) (c, v) (flat_map prim_of WC ++ hrest) (c, v) NDH Hin). reflexivity. }
    assert (NS : forall sc, In sc (flat_map sec_of WC) -> ~ In sc (sec_of ch)).
    { intros sc Hin Hc. destruct ch as [[c v|sc0] rz n]; cbn [sec_of qc_kind] in Hc; [exact Hc|]. destruct Hc as [<-|[]].
      cbn [flat_map sec_of qc_kind app] in NDS. apply NoDup_cons_iff in NDS as [NI _]. exact (NI Hin). }

    assert (HOK' : held_ok (fst (recycle1 X ch)) (map bpair WB ++ flat_map prim_of WC ++ hrest)).
    { destruct ch as [[c v|sc] rz n]; unfold recycle1; cbn [qc_kind fst snd]; cbn [flat_map prim_of qc_kind app] in HOK; [| exact HOK].
      pose proof RP as (LEN & _). unfold held_kind in HKc. cbn [qc_kind] in HKc. pose proof HKc as (Hc & _). cbn [fst] in Hc.
      exact (held_ok_cdealloc (fst X) (map bpair WB) (flat_map prim_of WC ++ hrest) c v LEN Hc HOK). }
    unfold dr_inv. split; [exact RP'|]. split; [exact POK'|]. split; [exact RS'|]. split; [exact MI'|]. split; [exact PE'|]. split; [exact TE'|]. split; [exact SV'|].
    split; [exact WFS|].
    split.
    { apply Forall_forall. intros ch' Hin.
      eapply (qchunk_rep_other X m m' lo q W (prim_of ch) (sec_of ch) ch' AO LOH CLO RP RS TCH TSI MU FW).
      - exact (proj1 (Forall_forall _ _) WFS ch' Hin).
      - exact (proj1 (Forall_forall _ _) REPS ch' Hin).
      - exact (proj1 (Forall_forall _ _) HKS ch' Hin).
      - intros cv Hcv. apply NP. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists ch'. split; assumption.
      - intros sc Hsc. apply NS. apply in_flat_map. exists ch'. split; assumption. }
    split.
    { apply Forall_forall. intros ch' Hin. pose proof (proj1 (Forall_forall _ _) HKS ch' Hin) as HK'.
      destruct ch' as [[c' v'|sc'] rz' n']; unfold held_kind in *; cbn [qc_kind] in *.
      - destruct HOK' as [_ FH']. apply (proj1 (Forall_forall _ _) FH'). apply in_or_app. right. apply in_or_app. left.
        apply in_flat_map. eexists. split; [exact Hin| cbn; left; reflexivity].
      - destruct ch as [[c v|sc] rz n]; unfold recycle1; cbn [qc_kind fst snd]; [exact HK'|].
        pose proof RS as (SWF & _). destruct SWF as (_ & _ & _ & _ & _ & COK & CSEP).
        assert (POSM : Forall (fun d => 0 < sc_msize d) (se_chunks (snd X))).
        { apply Forall_forall. intros d Hd. pose proof (chunk_ok_msize AL d (proj1 (Forall_forall _ _) COK d Hd)) as [DM _]. lia. }
        cbn [sec_dealloc se_chunks]. eapply remove_at_keeps; [exact (sc_index_nth _ sc CSEP POSM HKc)| exact HK'|].
        intros ->. apply (NS sc); [apply in_flat_map; eexists; split; [exact Hin| cbn; left; reflexivity]| cbn; left; reflexivity]. }
    split; [exact HOK'|].
    split. { destruct ch as [[c v|sc] rz n]; cbn [flat_map sec_of qc_kind app] in NDS; [exact NDS| apply NoDup_cons_iff in NDS as [_ NDS]; exact NDS]. }
    split; [exact BWF|].
    apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) BREP b Hb) as [nx RB]. exists nx.
    eapply (qbatch_rep_other X m m' lo q W (prim_of ch) (sec_of ch) b nx AO LOH CLO RP RS TCH TSI MU FW RB).
    - apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb.
    - apply NP. apply in_or_app. left. apply in_map. exact Hb.
  Qed.

  Definition pzone (lo : Z) (iv : Z * Z) : Prop :=
    (al_space AL <= fst iv /\ snd iv <= al_space AL + K_SPACE + 4096) \/ (2147450880 <= fst iv /\ snd iv <= 17594333495296)
    \/ (THR <= fst iv /\ snd iv <= THR + 4096) \/ lo <= fst iv.

  #[using="Type"] Lemma RSEC_frame_pzone : forall S W (m m' : mem) lo,
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
    RSEC AL S m -> munch W m m' -> wmono asegs m m' -> Forall (pzone lo) W -> RSEC AL S m'.
  Proof.
    intros S W m m' lo AO LOH CLO RS MU WM ZW.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _).
    pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
    layout_facts AO 1%nat LPARR. layout_apart_fact AO 0%nat 1%nat LP01. layout_apart_fact AO 1%nat 3%nat LP13.
    destruct LPARR as (P1 & P2 & _ & _ & _ & _ & _).
    eapply (RSEC_frame_but AL S _ m m' RS MU (wmono_but_of_wmono _ _ _ WM)).
    + eapply Forall_impl; [| exact ZW]. unfold pzone. intros iv Z0. clear - Z0 SP1 T3 LOH. lia.
    + clear - P1. lia.
    + apply dj_of_Forall. eapply Forall_impl; [| exact ZW]. unfold pzone. intros iv Z0. clear - Z0 P1 P2 LP01 LP13 CLO. lia.
    + apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) COK d Hd) as (_ & D2 & _ & _ & D5' & D6 & D7').
      pose proof (chunk_ok_msize AL d (proj1 (Forall_forall _ _) COK d Hd)) as [DM _].
      unfold al_regions in D7'. apply Forall_cons_iff in D7' as [DSP D7']. apply Forall_cons_iff in D7' as [_ D7'].
      apply Forall_cons_iff in D7' as [_ D7']. apply Forall_cons_iff in D7' as [DTH _]. cbn [fst snd] in DSP, DTH. unfold apart in DSP, DTH.
      apply dj_of_Forall. eapply Forall_impl; [| exact ZW]. unfold pzone. intros iv Z0. clear - Z0 D2 D5' D6 DM DSP DTH CLO. lia.
  Qed.

  #[using="Type"] Lemma pzone_prim_W : forall lo q c k k',
    alayout_ok AL -> 1 <= c <= 31 -> 0 <= p_nf k -> 0 <= p_nf k' -> 0 <= p_mfa k <= K_FA_SIZE -> 0 <= p_mfa k' <= K_FA_SIZE ->
    0 <= p_mu k <= FA_OFF -> 0 <= p_mu k' <= FA_OFF ->
    Forall (pzone lo) (prim_W AL lo q c k k').
  Proof.
    intros lo q c k k' AO Hc N1 N2 F1 F2 M1 M2. unfold prim_W.
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    assert (SHB : forall x, 0 <= x <= 2^47 -> 2147450880 <= sh x <= 17594333495296) by (intros x Hx; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
    assert (RG : region AL c = al_space AL + c * K_REGION) by reflexivity.
    assert (RIA : ri_addr AL c = al_space AL + K_SPACE + 128 * c) by reflexivity.
    assert (FAB : fa_base AL c = al_space AL + c * K_REGION + FA_OFF) by reflexivity.
    pose proof (SHB (region AL c + p_mu k) ltac:(rewrite RG; clear - Hc M1 SP1 SP5; lia)) as B1.
    pose proof (SHB (region AL c + p_mu k') ltac:(rewrite RG; clear - Hc M2 SP1 SP5; lia)) as B2.
    pose proof (SHB (fa_base AL c + p_mfa k) ltac:(rewrite FAB; clear - Hc F1 SP1 SP5; lia)) as B3.
    pose proof (SHB (fa_base AL c + p_mfa k') ltac:(rewrite FAB; clear - Hc F2 SP1 SP5; lia)) as B4.
    unfold pzone. rewrite RG, RIA, FAB in *.
    repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd].
    - right; right; right. clear; lia.
    - left. clear - Hc; lia.
    - left. clear - Hc N1 N2 F2; lia.
    - left. clear - Hc M1 M2; lia.
    - right; left. clear - B1 B2; lia.
    - right; left. clear - B3 B4; lia.
    - right; right; left. clear; lia.
    - right; right; left. clear; lia.
  Qed.

  #[using="Type"] Lemma dr_inv_batch : forall X H H1 (m m' : mem) b WB WC hrest lo q,
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
    dr_inv X H m (b :: WB) WC hrest ->
    munch (prim_W AL lo q K_BCLASS (get_cls (fst X) K_BCLASS) (get_cls (cache_dealloc (fst X) K_BCLASS (qb_v b)) K_BCLASS)) m m' ->
    wmono asegs m m' -> mem_inv asegs m' -> poison_env E m' -> thread_env L m' -> shvis H1 m' ->
    RPRIM AL (cache_dealloc (fst X) K_BCLASS (qb_v b)) m' -> prim_ok (cache_dealloc (fst X) K_BCLASS (qb_v b)) ->
    dr_inv (cache_dealloc (fst X) K_BCLASS (qb_v b), snd X) H1 m' WB WC hrest
    /\ Forall (atouch AL lo q (fst X) (snd X) [bpair b] [])
              (prim_W AL lo q K_BCLASS (get_cls (fst X) K_BCLASS) (get_cls (cache_dealloc (fst X) K_BCLASS (qb_v b)) K_BCLASS)).
  Proof.
    intros X H H1 m m' b WB WC hrest lo q AO LOH CLO INV MU WM MI' PE' TE' SV' RP' POK'.
    destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    set (P := fst X) in *. set (S := snd X) in *. set (v := qb_v b) in *.
    set (k := get_cls P K_BCLASS) in *. set (P' := cache_dealloc P K_BCLASS v) in *. set (k' := get_cls P' K_BCLASS) in *.
    assert (H24 : 1 <= K_BCLASS <= 31) by lia.
    pose proof RP as (LEN & _ & CLS & _). pose proof (CLS K_BCLASS H24) as (WFk & _).
    pose proof RP' as (_ & _ & CLS' & _). pose proof (CLS' K_BCLASS H24) as (WFk' & _). fold k in WFk. fold k' in WFk'.
    destruct WFk as (K1 & _ & _ & K4 & K5 & _ & K7 & K8 & _). destruct WFk' as (D1 & _ & _ & D4 & D5 & _ & D7 & D8 & _).
    cbn [map app] in HOK. pose proof HOK as [NDH FH].
    assert (HB : held1 P (bpair b)) by (apply (proj1 (Forall_forall _ _) FH); left; reflexivity).
    assert (FW : Forall (atouch AL lo q P S [bpair b] []) (prim_W AL lo q K_BCLASS k k')).
    { apply atouch_prim_W; [exact H24| | | | | | |]; fold k; clear - K1 K4 K5 K7 K8 D1 D4 D5 D7 D8; lia. }
    split; [| exact FW].
    assert (TCH : Forall (held1 P) [bpair b]) by (constructor; [exact HB| constructor]).
    assert (TSI : incl (@nil schunk) (se_chunks S)) by (intros d []).
    assert (NP : forall cv, In cv (map bpair WB ++ flat_map prim_of WC ++ hrest) -> ~ In cv [bpair b]).
    { intros cv Hin [<-|[]]. apply NoDup_cons_iff in NDH as [NI _]. exact (NI Hin). }
    assert (HOK' : held_ok P' (map bpair WB ++ flat_map prim_of WC ++ hrest)).
    { exact (held_ok_cdealloc P [] (map bpair WB ++ flat_map prim_of WC ++ hrest) K_BCLASS v LEN H24 HOK). }
    assert (RS' : RSEC AL S m').
    { eapply (RSEC_frame_pzone S _ m m' lo AO LOH CLO RS MU WM). apply pzone_prim_W; [exact AO| exact H24| | | | | |]; clear - K1 K4 K5 K7 K8 D1 D4 D5 D7 D8; lia. }
    unfold dr_inv. cbn [fst snd]. split; [exact RP'|]. split; [exact POK'|]. split; [exact RS'|]. split; [exact MI'|]. split; [exact PE'|]. split; [exact TE'|]. split; [exact SV'|].
    split; [exact WFS|].
    split.
    { apply Forall_forall. intros ch' Hin.
      eapply (qchunk_rep_other X m m' lo q _ [bpair b] [] ch' AO LOH CLO RP RS TCH TSI MU FW).
      - exact (proj1 (Forall_forall _ _) WFS ch' Hin).
      - exact (proj1 (Forall_forall _ _) REPS ch' Hin).
      - exact (proj1 (Forall_forall _ _) HKS ch' Hin).
      - intros cv Hcv. apply NP. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists ch'. split; assumption.
      - intros sc _ []. }
    split.
    { apply Forall_forall. intros ch' Hin. pose proof (proj1 (Forall_forall _ _) HKS ch' Hin) as HK'.
      destruct ch' as [[c' v'|sc'] rz' n']; unfold held_kind in *; cbn [qc_kind fst snd] in *; [| exact HK'].
      destruct HOK' as [_ FH']. apply (proj1 (Forall_forall _ _) FH'). apply in_or_app. right. apply in_or_app. left.
      apply in_flat_map. eexists. split; [exact Hin| cbn; left; reflexivity]. }
    split; [exact HOK'|]. split; [exact NDS|].
    apply Forall_cons_iff in BWF as [_ BWF]. apply Forall_cons_iff in BREP as [_ BREP]. split; [exact BWF|].
    apply Forall_forall. intros b' Hb. destruct (proj1 (Forall_forall _ _) BREP b' Hb) as [nx RB]. exists nx.
    eapply (qbatch_rep_other X m m' lo q _ [bpair b] [] b' nx AO LOH CLO RP RS TCH TSI MU FW RB).
    - apply (proj1 (Forall_forall _ _) FH). right. apply in_or_app. left. apply in_map. exact Hb.
    - apply NP. apply in_or_app. left. apply in_map. exact Hb.
  Qed.

  #[using="Type"] Lemma CB_of_u64arr : forall (mm : mem) A ws, u64arr asegs mm A ws -> rw_cells asegs mm A [CB (8 * length ws) (u64s ws)].
  Proof.
    intros mm A ws [HB HW]. split; [split|].
    - cbn [cells_wf cell_wf]. split; [apply u64s_length| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Nat2Z.inj_mul. exact HW.
  Qed.

  #[using="Type"] Lemma qbatch_free_chunk : forall (m : mem) b nx, qbatch_rep AL m b nx -> free_chunk AL m K_BCLASS (qb_v b).
  Proof.
    intros m b nx (R1 & (ws & R2 & LW & _) & R3). unfold free_chunk. change (class_size K_BCLASS) with 8192. change (8192 / 8) with 1024.
    split; [| exact R3]. fold (qb_addr AL b).
    destruct (rw_cells_forget _ _ _ _ R1) as [j1 J1]. cbn [cells_size csize Nat.add] in J1.
    pose proof (CB_of_u64arr m (qb_addr AL b + 24) ws R2) as J2. rewrite LW in J2.
    pose proof (cb_join m (qb_addr AL b) 24 _ j1 _ J1 J2) as J. exists (j1 ++ u64s ws). exact J.
  Qed.

  #[using="Type"] Lemma qlist_rep_other : forall X (m m' : mem) lo q W tc tsc l nxt,
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
    RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
    Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
    munch W m m' -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
    qlist_rep AL m l nxt -> Forall (fun b => held1 (fst X) (bpair b) /\ ~ In (bpair b) tc) l ->
    qlist_rep AL m' l nxt.
  Proof.
    intros X m m' lo q W tc tsc l nxt AO LOH CLO RP RS TCH TSI MU FW. induction l as [|b l IH]; intros QL FB; [exact I|].
    cbn [qlist_rep] in *. destruct QL as [RB QL]. apply Forall_cons_iff in FB as [[HB NB] FB]. split; [| exact (IH QL FB)].
    exact (qbatch_rep_other X m m' lo q W tc tsc b _ AO LOH CLO RP RS TCH TSI MU FW RB HB NB).
  Qed.

  #[using="Type"] Lemma atouch_above : forall X (m : mem) lo q W tc tsc A n,
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q ->
    RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
    Forall (atouch AL lo q (fst X) (snd X) tc tsc) W -> q <= A -> disjoint_from W A n.
  Proof.
    intros X m lo q W tc tsc A n AO LOH CLO LQ RP RS TCH TSI FW QA.
    destruct (clear_ctx X m RP RS) as (WF0 & SOK & SSEP).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
    layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
    assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
    apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros iv AT. right. unfold atouch, sub_iv in AT.
    destruct AT as [AT|[AT|[AT|[AT|[AT|[AT|[AT|AT]]]]]]].
    - clear - AT QA. lia.
    - clear - AT QA LOH LQ. lia.
    - clear - AT QA T4 CLO LQ. lia.
    - destruct AT as (c0 & Hc0 & [AT|[AT|AT]]).
      + unfold ri_addr, RIB in AT. clear - AT QA SP2 CLO LQ Hc0. lia.
      + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. rewrite !RGE in *. clear - AT QA SP2 CLO LQ Q2. lia.
      + pose proof (region_range AL c0 Hc0) as [Q1 Q2].
        assert (SHI : sh (region AL (c0 + 1)) <= 17594333495296) by (rewrite RGE in *; unfold sh, SHADOW_OFF; clear - Q2 SP5; Z.div_mod_to_equations; lia).
        clear - AT QA SHI LOH LQ. lia.
    - destruct AT as ([c1 v1] & Hin & AT). cbn [fst snd] in AT.
      pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo (fst X) AO WF0 c1 v1 HE1) as G'. cbv zeta in G'.
      destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7). pose proof (region_range AL c1 Hc1) as [Q1 Q2].
      unfold chunk_iv, chunk_sh_iv in AT. rewrite <- H5 in AT. destruct AT as [AT|AT]; [clear - AT QA H2 H3 Q2 SP2 CLO LQ; lia| clear - AT QA H7 LOH LQ; lia].
    - destruct AT as (sc & Hin & AT). pose proof (sec_geo (snd X) SOK sc (TSI sc Hin)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
      rewrite <- D8 in AT. destruct AT as [AT|AT]; [clear - AT QA D3 CLO LQ; lia| clear - AT QA D10 LOH LQ; lia].
    - destruct AT as (d & Hin & AT). pose proof (sec_geo (snd X) SOK d Hin) as (D1 & D2 & D3 & _). clear - AT QA D2 D3 CLO LQ. lia.
    - clear - AT QA P2 CLO LQ. lia.
  Qed.

End ARANY.

