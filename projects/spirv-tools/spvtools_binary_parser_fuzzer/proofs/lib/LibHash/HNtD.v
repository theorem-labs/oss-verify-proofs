(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibBudget FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import
  HRep HLib HRepFacts HStmts HConstsS1 HCommon HFpu HFind HBlk HRehashModel HNtCtx S1_code_67e94_68324 S1_code_6db30_6db3c.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition STOPSD : list Z := [NT_NEWE; NT_NEW2R; NT_DELSZ; NT_DELR; NT_BCST; NT_MEMSET; NT_MSR; NT_LOOP; NT_AFTER].

#[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

Section NtD.
Context {AC : AllocCeiling}.

  Variables (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp parser key bl bc : Z) (val : Z * Z * Z) (v2 : Z) (ents : list (Z * (Z * (Z * Z * Z)))) (K : TSet).
  Variable C : @ntctx AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K.
  #[local] Abbreviation NTS := (NT_STACK NEW_STACK DEL_STACK).
  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI (c_HLimg_lo C) (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST (c_HLimg_lo C) (c_HLrw_img C) (c_HLrelro_img C) (c_HLrw_relro C) (c_HLerr_rw C)).
  #[local] Abbreviation ro_clear_via_eff' := (ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff L MI (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation own_sx_via_eff' := (own_sx_via_eff L MI ST (c_HLrw_img C)).
  #[local] Abbreviation hi_unowned' := (hi_unowned L MI (c_HLimg_lo C) (c_HLrw_img C)).
  #[local] Abbreviation obj := (parser + 136).
  #[local] Abbreviation sent := (parser + 152).
  #[local] Abbreviation W := (Wnt NEW_STACK DEL_STACK sp).
  #[local] Abbreviation base_ok := (nt_base_ok L R0 sp parser val v2).
  #[local] Abbreviation pframe := (nt_pframe sp parser key).
  #[local] Abbreviation SPF := (sp_facts C).
  #[local] Abbreviation BCF := (bc_facts C).
  #[local] Ltac ctx := ntctx_pose C.

  Lemma del_call : forall fx1 A M model R (p m spc r : Z),
    ainv MI A M model -> mstd model -> img_ro_clear L M ->
    getr R 1%bv = Z_to_bv 64 r -> ret_ok (Z_to_bv 64 r) -> 0 <= r < 2 ^ 64 ->
    getr R 2%bv = Z_to_bv 64 spc -> spc mod 16 = 0 -> spc < 2 ^ 47 ->
    getr R 3%bv = Z_to_bv 64 (ly_gp L) -> getr R 4%bv = Z_to_bv 64 (ly_tp L) ->
    getr R 10%bv = Z_to_bv 64 p -> (p = 0 /\ m = 0 \/ In (p, m) (live MI A)) ->
    alloc_ceiling + DEL_STACK <= spc -> 0x122000 <= spc - DEL_STACK ->
    defined M (spc - DEL_STACK) DEL_STACK ->
    (forall a, zwin (spc - DEL_STACK) spc a -> ~ owned MI A a) ->
    (forall A' R' M' model',
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
        kept R R' -> live_del p (live MI A) (live MI A') ->
        eff MI A A' M M' (spc - DEL_STACK, spc) (fun a => p <= a < p + m) ->
        defined M' (spc - DEL_STACK) DEL_STACK ->
        (forall a, zwin (spc - DEL_STACK) spc a -> ~ owned MI A' a) ->
        srealizes SEGS (cfg fx1 R' r M' model') K) ->
    srealizes SEGS (cfg fx1 R NT_DELSZ M model) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros fx1 A M model R p m spc r AI MS IROC H1 Hret Hr H2 Hsp16' Hsphi H3 H4 H10 Hp Hce Hlo Hdef Hwin' POST.
    pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ].
    { unfold NT_DELSZ. norm_pc. stepj F_6db34 D_6db34. apply mst_refl. }
    replace (0x6db70%bv : word) with (Z_to_bv 64 (ly_delete L)) by (rewrite HLdel; apply bv_eq; reflexivity).
    eapply (DEL fx1 A R M model p m spc r K AI MS IROC).
    - constructor; assumption.
    - exact H10.
    - exact Hp.
    - lia.
    - apply stack_room_of_defined; [lia | lia | lia | exact Hdef].
    - exact Hwin'.
    - intros A' R2 M' model' AI' MS' Hfs Hfds KEPT LDEL CAPS BIGC OWN FR DEF.
      assert (Hdef' : defined M' (spc - DEL_STACK) DEL_STACK).
      { intros i Hi. destruct (DEF (Z_to_bv 64 (spc - DEL_STACK + i)) (Hdef i Hi)) as [Hm|[Ho|[Hq|He]]];
          [exact Hm| exfalso | exfalso | exfalso].
        - rewrite u64_of_Z in Ho by lia. exact (Hwin' (spc - DEL_STACK + i) ltac:(unfold zwin; lia) Ho).
        - rewrite u64_of_Z in Hq by lia. destruct Hp as [[-> ->]|Hin]; [lia|].
          destruct (live_facts' A M model p m AI Hin) as (_ & _ & Hpc & _). lia.
        - rewrite u64_of_Z in He by lia. pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ He))). lia. }
      assert (Hwin'' : forall a, zwin (spc - DEL_STACK) spc a -> ~ owned MI A' a).
      { intros a Ha Ho. destruct (OWN a Ho) as [Ho0|Hq]; [exact (Hwin' a Ha Ho0)|]. unfold zwin in Ha.
        destruct Hp as [[-> ->]|Hin]; [lia|]. destruct (live_facts' A M model p m AI Hin) as (_ & _ & Hpc & _). lia. }
      apply (POST A' R2 M' model' AI' MS' Hfs Hfds KEPT LDEL); [| exact Hdef' | exact Hwin''].
      eapply eff_of_del; [exact CAPS | exact BIGC | exact OWN | exact FR | exact DEF | | intros a Ha; exact Ha
                        | intros a Ha; destruct Hp as [[-> ->]|Hin]; [lia | exact (live_offimg' A M model p m a AI Hin Ha)]].
      intros a Ha. exact Ha.
  Qed.

  Section Reh.

    Variables (fxr : FPState) (Ar : AS MI) (Mr : mem) (modelr : Model) (Rr : bvmap 5 word) (pn : Z).
    #[local] Abbreviation n := (bseq_next bc).
    Hypothesis AIr : ainv MI Ar Mr modelr.
    Hypothesis MSr : mstd modelr.
    Hypothesis Hfsr : m_fs modelr = m_fs model0.
    Hypothesis Hfdsr : m_fds modelr = m_fds model0.
    Hypothesis SXr : sx_inv ST s Mr.
    Hypothesis RCr : ro_clear L Mr.
    Hypothesis OSXr : forall a, owned MI Ar a -> ~ sx_region ST a.

    Definition dbase (R : bvmap 5 word) : Prop := base_ok R /\ getr R 23%bv = Z_to_bv 64 key /\ getr R 25%bv = Z_to_bv 64 pn.
    Hypothesis Br : dbase Rr.
    Hypothesis Q26r : getr Rr 26%bv = Z_to_bv 64 n.
    Hypothesis Q22r : getr Rr 22%bv = Z_to_bv 64 (8 * n).
    Hypothesis Q10r : getr Rr 10%bv = Z_to_bv 64 (8 * n).
    Hypothesis Q1r : getr Rr 1%bv = Z_to_bv 64 NT_NEW2R.
    Hypothesis Ur : umapx MI 32 (nval32 SEGS) Ar Mr obj bl bc ents.
    Hypothesis DEFWr : defined Mr (sp - NTS) NTS.
    Hypothesis F2r : cell8 SEGS Mr (sp + 24) sent.
    Hypothesis ROOMr : roomL MI Ar (live MI Ar) (8 * n).
    Hypothesis CONTD : forall A' R' M' model' (bl' : Z) (ents' : list ent),
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model0 -> m_fds model' = m_fds model0 ->
        dbase R' ->
        umapx MI 32 (nval32 SEGS) A' M' obj bl' n ents' -> Permutation ents' ents ->
        lapply (live MI Ar) (LAdd bl' (8 * n) :: (if bc =? 0 then [] else [LDel bl])) (live MI A') ->
        eff MI Ar A' Mr M' W (fun a => umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a) ->
        defined M' (sp - NTS) NTS ->
        srealizes SEGS (cfg fxr R' NT_AFTER M' model') K.

    Lemma n_facts : In n BSEQ /\ bc < n /\ 8 * n <= 2 ^ 28 /\ ((bc = 0 /\ n = 2) \/ (3 <= n /\ Z.land n (n - 1) <> 0)).
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C. ctx. exact (bseq_next_facts bc (u_bseq U0) Hlast). Qed.
    #[local] Opaque bseq_next.

    Lemma iroc_r : img_ro_clear L Mr.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C Mr SXr RCr. ctx. apply img_ro_clear_of; [exact RCr |]. intros a Ha. eapply (sx_relro ST); [exact SXr | exact Ha]. Qed.

    Lemma tbl_blocks_live : forall b, In b (umap_blocks 32 bl bc ents) -> In b (live MI Ar).
    Proof using AC L MI NEW_STACK DEL_STACK R0 model0 sp parser key bl bc val v2 ents K fxr Ar Mr pn Ur CONTD.
      intros [p m] Hb. unfold umap_blocks in Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
      - destruct (Z.eqb_spec bc 0); [destruct Hb|]. destruct Hb as [Hb|[]]. injection Hb as <- <-.
        destruct (u_blive Ur) as [[? ?]|[_ Hin]]; [lia | exact Hin].
      - apply in_map_iff in Hb. destruct Hb as ([p' [k v]] & Hpp & Hin). cbn in Hpp. injection Hpp as <- <-.
        exact (proj1 (u_node Ur p' k v Hin)).
    Qed.

    Lemma win_r : forall A M model a, ainv MI A M model -> zwin (sp - NTS) sp a -> ~ owned MI A a /\ ~ sx_region ST a.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
      ctx. intros A M model a AI Ha. destruct SPF as (_ & Hsplo & _). split.
      - eapply hi_unowned'; [exact AI | unfold zwin in Ha; lia].
      - exact (proj2 (Hwin a Ha)).
    Qed.

    Lemma phaseA :
      (forall A1 M1 model1 R1 (p : Z),
          ainv MI A1 M1 model1 -> mstd model1 -> m_fs model1 = m_fs model0 -> m_fds model1 = m_fds model0 -> sx_inv ST s M1 ->
          dbase R1 -> getr R1 10%bv = Z_to_bv 64 p -> getr R1 26%bv = Z_to_bv 64 n -> getr R1 22%bv = Z_to_bv 64 (8 * n) ->
          defined M1 (sp - NTS) NTS ->
          0 < p -> p + 8 * n <= alloc_ceiling -> p mod 16 = 0 -> live_add p (8 * n) (live MI Ar) (live MI A1) ->
          eff MI Ar A1 Mr M1 W (fun a => p <= a < p + 8 * n) ->
          umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
          srealizes SEGS (cfg fxr R1 NT_NEW2R M1 model1) K) ->
      srealizes SEGS (cfg fxr Rr NT_NEWE Mr modelr) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C fxr Ar Mr modelr Rr pn AIr MSr Hfsr Hfdsr SXr RCr OSXr Br Q26r Q22r Q10r Q1r Ur DEFWr ROOMr CONTD.
      ctx. intros POST.
      destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq U0) as HB; unfold BSEQ in HB; cbn in HB; lia).
      destruct Br as (B & Q23 & Q25). pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
      pose proof iroc_r as IROC.
      replace (Z_to_bv 64 NT_NEWE) with (Z_to_bv 64 (ly_new L) : word) by (rewrite HLnew; reflexivity).
      eapply (NEW fxr Ar s Rr Mr modelr (8 * n) sp NT_NEW2R K AIr MSr IROC SXr SXH).
      - constructor; [exact Q1r | apply bv_eq; vm_compute; reflexivity | unfold NT_NEW2R; lia | exact B2
                     | exact Hsp16' | lia | exact B3 | exact B4].
      - exact Q10r.
      - unfold LIB_NMAX in HNMAX. lia.
      - lia.
      - apply stack_room_of_defined; [lia | lia | lia |]. eapply defined_sub; [exact DEFWr | lia | lia].
      - intros a Ha. exact (win_r Ar Mr modelr a AIr ltac:(unfold zwin in *; lia)).
      - exact OSXr.
      - exact Herr_sx.
      - replace (new_size (8 * n)) with (8 * n) by (unfold new_size; lia).
        eapply roomL_room_for; [exact AIr | unfold LIB_NMAX in HNMAX; lia | exact ROOMr].
      -
        intros A1 R1 M1 model1 p AI1 MS1 Hfs1 Hfds1 SX1 KEPT R1a0 Hp LADD CAPS BIGC NEWT FR DEF.
        replace (new_size (8 * n)) with (8 * n) in LADD, FR by (unfold new_size; lia).
        assert (EFF : eff MI Ar A1 Mr M1 (sp - NEW_STACK, sp) (fun a => p <= a < p + 8 * n)).
        { eapply (eff_of_new MI Ar A1 Mr M1 model1); [exact AI1 | exact CAPS | exact BIGC | exact NEWT | exact FR | exact DEF | intros a Ha; exact Ha | intros a Ha; exact Ha]. }
        assert (HinP : In (p, 8 * n) (live MI A1)) by (rewrite (proj1 LADD); left; reflexivity).
        destruct (ai_live_block MI A1 M1 model1 p (8 * n) AI1 HinP) as (_ & Hpal & Hp0 & Hpc & Hpown).
        assert (EFF2 : eff MI Ar A1 Mr M1 W (fun a => p <= a < p + 8 * n)).
        { eapply eff_widen; [exact EFF|]. intros a Ha. unfold W_of, Wnt in Ha |- *. cbn [fst snd] in Ha |- *. lia. }
        apply (POST A1 M1 model1 R1 p AI1 MS1 ltac:(congruence) ltac:(congruence) SX1).
        + split; [| rewrite !(KEPT _) by inl; split; [exact Q23 | exact Q25]].
          unfold nt_base_ok. rewrite !(KEPT _) by inl. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B8|]. split; [exact B24|]. split; [exact B21|]. split; [exact B18|].
          intros r Hr. rewrite (KEPT r); [apply Bs; exact Hr|]. clear - Hr. cbn in Hr. unfold callee_saved. cbn. intuition congruence.
        + exact R1a0.
        + rewrite (KEPT 26%bv) by inl. exact Q26r.
        + rewrite (KEPT 22%bv) by inl. exact Q22r.
        + eapply (defined_via_eff L MI HLimg_lo HLrw_img HLerr_rw Ar A1 Mr M1 _ _ (sp - NTS) NTS EFF ltac:(lia) ltac:(cbn; lia)).
          * intros i Hi. eapply hi_unowned'; [exact AIr | lia].
          * intros i Hi Hf. cbn beta in Hf. lia.
          * exact DEFWr.
        + exact Hp0. + exact Hpc. + exact Hpal. + exact LADD.
        + exact EFF2.
        +
          eapply (umapx_via_eff L MI HLimg_lo HLrw_img HLerr_rw 32 _ (nval32 SEGS) ltac:(lia) (nval32_agree SEGS) Ar A1 Mr M1 modelr obj bl bc ents W _ sp Ur AIr EFF2).
          * lia. * unfold Wnt; cbn; lia. * lia.
          * intros i Hi. eapply hi_unowned'; [exact AIr | lia].
          *
            intros a Ha Hpa. destruct (umap_foot_hb 32 obj bl bc ents a Ha) as [Hh | ([q m] & Hb & Hba)]; [lia|]. cbn in Hba.
            pose proof (tbl_blocks_live _ Hb) as Hq0.
            assert (Hq1 : In (q, m) (live MI A1)) by (rewrite (proj1 LADD); right; exact Hq0).
            assert (Hne : p <> q).
            { intros <-. apply (proj2 LADD). apply (in_map fst _ (p, m)). exact Hq0. }
            pose proof (ai_live_disjoint MI A1 M1 model1 p (8 * n) q m AI1 HinP Hq1 Hne) as Hap. lia.
          * unfold Wnt; cbn; lia.
          * intros q m Hb Hl. rewrite (proj1 LADD). right. exact Hl.
    Qed.

    Lemma dbase_kept : forall R R', dbase R -> kept R R' -> dbase R'.
    Proof using L R0 sp parser key val v2 pn.
      intros R R' (B & Q23 & Q25) KEPT. pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
      split; [| rewrite !(KEPT _) by inl; split; [exact Q23 | exact Q25]].
      unfold nt_base_ok. rewrite !(KEPT _) by inl. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B8|]. split; [exact B24|]. split; [exact B21|]. split; [exact B18|].
      intros r Hr. rewrite (KEPT r); [apply Bs; exact Hr|]. clear - Hr. cbn in Hr. unfold callee_saved. cbn. intuition congruence.
    Qed.

    Lemma dbase_ms : forall R R', dbase R -> ms_agree R R' -> dbase R'.
    Proof using L R0 sp parser key val v2 pn.
      intros R R' (B & Q23 & Q25) AG. pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
      assert (HP : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25]%bv -> getr R' r = getr R r).
      { intros r Hr. apply AG. cbn in Hr. unfold ms_clob. repeat (destruct Hr as [<-|Hr]; [ninl|]). destruct Hr. }
      split; [| rewrite !HP by inl; split; [exact Q23 | exact Q25]].
      unfold nt_base_ok. rewrite !HP by inl. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B8|]. split; [exact B24|]. split; [exact B21|]. split; [exact B18|].
      intros r Hr. rewrite HP; [apply Bs; exact Hr|]. clear - Hr. cbn in Hr |- *. intuition congruence.
    Qed.

    Ltac dbase_from HR' D :=
      let B := fresh in let Q23 := fresh in let Q25 := fresh in
      pose proof D as B; destruct B as (B & Q23 & Q25);
      split; [nt_base_from HR' B
             | split; [ let Q := fresh in rreg HR' 23%bv Q; rewrite Q; first [reflexivity | exact Q23]
                      | let Q := fresh in rreg HR' 25%bv Q; rewrite Q; first [reflexivity | exact Q25] ] ].

    Record rst (F : Z -> Prop) (ops : list lop) (p : Z) (A : AS MI) (M : mem) (model : Model) (R : bvmap 5 word) : Prop := RST {
      r_ai : ainv MI A M model;
      r_ms : mstd model;
      r_fs : m_fs model = m_fs model0;
      r_fds : m_fds model = m_fds model0;
      r_regs : dbase R;
      r_s10 : getr R 26%bv = Z_to_bv 64 n;
      r_s6 : getr R 22%bv = Z_to_bv 64 (8 * n);
      r_def : defined M (sp - NTS) NTS;
      r_eff : eff MI Ar A Mr M W F;
      r_lap : lapply (live MI Ar) ops (live MI A);
      r_p0 : 0 < p; r_pc : p + 8 * n <= alloc_ceiling; r_pal : p mod 16 = 0;
      r_plive : In (p, 8 * n) (live MI A);
      r_pnew : ~ In p (map fst (live MI Ar));
      r_Foff : forall a, F a -> ~ in_ranges (ly_img L) a;
      r_hdef : defined M obj 40
    }.

    Definition FA (p : Z) (a : Z) : Prop := p <= a < p + 8 * n.
    Definition FB (p : Z) (a : Z) : Prop := FA p a \/ (obj <= a < obj + 8) \/ (bc <> 0 /\ bl <= a < bl + 8 * bc).
    Definition opsB (p : Z) : list lop := LAdd p (8 * n) :: (if bc =? 0 then [] else [LDel bl]).

    Lemma f2_via : forall A M (F : Z -> Prop), eff MI Ar A Mr M W F -> (forall a, F a -> ~ (sp + 24 <= a < sp + 32)) -> cell8 SEGS M (sp + 24) (obj + 16).
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C Ar Mr modelr AIr F2r.
      ctx. intros A M F EF HF. destruct SPF as (_ & Hsplo & Hsphi & Hn16 & _). pose proof ac_bounds_lit as Hcv.
      replace (obj + 16) with sent by lia.
      eapply cellw_agree; [exact F2r | | lia | cbn; lia].
      eapply (agree_above_via_eff' Ar A Mr M _ _ (sp + 24) 8 sp EF); [lia | cbn; lia | lia | lia | lia | | |].
      - intros i Hi. eapply hi_unowned'; [exact AIr | lia].
      - exact (cellw_high_defined Mr (sp + 24) 8 _ F2r ltac:(lia) ltac:(cbn; lia)).
      - intros i Hi Hf. exact (HF _ Hf ltac:(lia)).
    Qed.

    Lemma phaseB : forall A1 M1 model1 R1 p,
      rst (FA p) [LAdd p (8 * n)] p A1 M1 model1 R1 -> getr R1 10%bv = Z_to_bv 64 p ->
      umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      (forall A2 M2 model2 R2,
          rst (FB p) (opsB p) p A2 M2 model2 R2 -> getr R2 27%bv = Z_to_bv 64 p ->
          cell8 SEGS M2 obj p ->

          agree_on M1 M2 (obj + 8) 32 -> (forall q k v, In (q, (k, v)) ents -> agree_on M1 M2 q 32 /\ In (q, 32) (live MI A2)) ->
          srealizes SEGS (cfg fxr R2 NT_BCST M2 model2) K) ->
      srealizes SEGS (cfg fxr R1 NT_NEW2R M1 model1) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C fxr Ar Mr modelr pn AIr SXr RCr Ur CONTD.
      ctx. intros A1 M1 model1 R1 p D G10 U1 POST.
      destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq U0) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds DB S10 S6 DEF EFF LAP Hp0 Hpc Hpal Hpl Hpnew HFoff HDEF].
      pose proof DB as DB'. destruct DB' as (B & Q23 & Q25). pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
      pose proof (proj1 (nf_key _ _ _ _ _ _ _ _ _ NF)) as Hkr. cbn in Hkr.
      pose proof (u_hdr U1) as HD. destruct HD as [Cbl Cbc Cp1 Csz Cmlf Cdef]. unfold cell8 in Cbl, Cbc. unfold cell4 in Cmlf.
      pose proof (proj1 Cbl) as Hblr. pose proof (proj1 Cbc) as Hbcr.
      pose (E := Eseed R1 [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 n; Z_to_bv 64 (8 * n); Z_to_bv 64 key; getr R1 25%bv; Z_to_bv 64 0;
                           Z_to_bv 64 bl; Z_to_bv 64 bc]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (26%bv, EVar 35); (22%bv, EVar 36); (23%bv, EVar 37); (25%bv, EVar 38)]) R1).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | reflexivity]. }
      assert (HK : know_ok SEGS E M1 []) by constructor.
      assert (Hdefobj : defined M1 obj 40) by exact Cdef.
      destruct (Z.eq_dec bc 0) as [Hz | Hnz].
      -
        assert (Hbl0 : bl = 0) by (destruct (u_blive U1) as [[_ H]|[H _]]; [exact H | exfalso; exact (H Hz)]).
        rewrite Hbl0 in *.
        xruns HR HK 100%nat STOPSD (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. sc_so. eapply (defined_sub _ _ _ _ _ Hdefobj); lia. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M1 _ _).
        rreg HRc 27%bv G27. rreg HRc 26%bv G26. rreg HRc 22%bv G22.
        assert (HMw : forall x : word, ~ (obj <= bv_unsigned x < obj + 8) -> Mw x = M1 x).
        { intros x Hx. pose proof (u64_range x). unfold Mw.
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M1 x <> None -> Mw x <> None) by (intros x Hx; unfold Mw; apply wbytes_grows; exact Hx).
        assert (HMa : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k obj 8 -> agree_on M1 Mw a k).
        { intros a k Ha Hak H1 i Hi. apply HMw; rewrite u64_of_Z by lia; unfold apart in *; lia. }
        apply (POST A1 Mw model1 Rc).
        + constructor.
          * eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
            intros x Ho. pose proof (u64_range x). apply HMw; intros Hx. exact (hi_unowned' A1 M1 model1 (bv_unsigned x) AI ltac:(lia) Ho).
          * exact MS. * exact Hfs. * exact Hfds.
          * dbase_from HRc DB.
          * exact G26. * exact G22.
          * eapply defined_agree; [exact DEF | apply HMa; unfold apart; lia].
          * eapply eff_weaken; [eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned'; [exact AI | unfold W_of, Wnt in Ha; cbn in Ha; lia]]|].
            -- eapply eff_store with (F := fun a : Z => obj <= a < obj + 8); [|exact HMg]. intros x HF HW. apply HMw. exact HF.
            -- intros a [Ha|Ha]; [left; exact Ha | right; left; exact Ha].
          * unfold opsB. rewrite (proj2 (Z.eqb_eq _ _) Hz). exact LAP.
          * exact Hp0. * exact Hpc. * exact Hpal. * exact Hpl. * exact Hpnew.
          * intros a [Ha|[Ha|[Ha _]]]; [exact (HFoff a Ha) | intros Himg; pose proof (HLimg_lo _ Himg); lia | exfalso; exact (Ha Hz)].
          * intros i Hi. apply HMg. apply Hdefobj. exact Hi.
        + exact G27.
        + unfold cell8, Mw. cellpeel.
        + apply HMa; unfold apart; lia.
        + intros q k v Hin. destruct (u_node U1 q k v Hin) as (Hlv & Hq0 & Hq1 & _).
          destruct (live_facts' A1 M1 model1 q 32 AI Hlv) as (_ & _ & Hqc & _).
          split; [apply HMa; unfold apart; lia | exact Hlv].
      -
        assert (Hblp : 0 < bl) by exact (u_bl_lo U1 Hnz).
        assert (Hbllive : In (bl, 8 * bc) (live MI A1)) by (destruct (u_blive U1) as [[? ?]|[_ H]]; [lia | exact H]).
        destruct (live_facts' A1 M1 model1 bl (8 * bc) AI Hbllive) as (_ & _ & Hblc & _).
        xruns HR HK 100%nat STOPSD (SCR [false] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_so. eapply (defined_sub _ _ _ _ _ Hdefobj); lia. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M1 _ _).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 26%bv G26. rreg HRc 10%bv G10'. rreg HRc 22%bv G22.
        pose proof (syms_id_sound _ _ _ _ [3; 4]%bv HRc eq_refl) as Gs.
        assert (DBc : dbase Rc) by (dbase_from HRc DB).
        assert (HMw : forall x : word, ~ (obj <= bv_unsigned x < obj + 8) -> Mw x = M1 x).
        { intros x Hx. pose proof (u64_range x). unfold Mw.
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M1 x <> None -> Mw x <> None) by (intros x Hx; unfold Mw; apply wbytes_grows; exact Hx).
        assert (HMa : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k obj 8 -> agree_on M1 Mw a k).
        { intros a k Ha Hak H1 i Hi. apply HMw; rewrite u64_of_Z by lia; unfold apart in *; lia. }
        assert (AIw : ainv MI A1 Mw model1).
        { eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
          intros x Ho. pose proof (u64_range x). apply HMw; intros Hx. exact (hi_unowned' A1 M1 model1 (bv_unsigned x) AI ltac:(lia) Ho). }
        assert (EFw : eff MI Ar A1 Mr Mw W (fun a => FA p a \/ (obj <= a < obj + 8))).
        { eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned'; [exact AI | unfold W_of, Wnt in Ha; cbn in Ha; lia]].
          eapply eff_store with (F := fun a : Z => obj <= a < obj + 8); [|exact HMg]. intros x HF HW. apply HMw. exact HF. }
        assert (ROCw : img_ro_clear L Mw).
        { eapply (img_ro_clear_via_eff' Ar A1 Mr Mw modelr W _ iroc_r AIr EFw); [| unfold Wnt; cbn; lia].
          intros a [Ha|Ha]; [exact (HFoff a Ha) | intros Himg; pose proof (HLimg_lo _ Himg); lia]. }
        eapply (del_call fxr A1 Mw model1 Rc bl (8 * bc) sp NT_DELR AIw MS ROCw G1);
          [ apply bv_eq; vm_compute; reflexivity | unfold NT_DELR; lia | exact G2
          | exact Hsp16' | lia
          | rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4 | rewrite G10'; reflexivity
          | right; exact Hbllive
          | lia | lia
          | intros i Hi; apply HMg; eapply (defined_pt _ _ _ _ DEF); lia
          | intros a Ha; eapply hi_unowned'; [exact AI | unfold zwin in Ha; lia] | ].
        intros A2 R2 M2 model2 AI2 MS2 Hfs2 Hfds2 KEPT LDEL EFF2 DEF2 WIN2.

        assert (AG2 : forall a k, 0 <= k -> alloc_ceiling <= a -> (a + k <= sp - DEL_STACK \/ sp <= a) -> a + k <= 2 ^ 47 -> defined Mw a k -> agree_on Mw M2 a k).
        { intros a k Hk Ha Hw Hak Hd i Hi. apply (ef_frame _ _ _ _ _ _ _ _ _ EFF2). rewrite u64_of_Z by lia.
          intros [Ho|[Ho'|[Hnm|[Hf|[Hw'|He]]]]].
          - exact (hi_unowned' A1 Mw model1 (a + i) AIw ltac:(lia) Ho).
          - exact (hi_unowned' A2 M2 model2 (a + i) AI2 ltac:(lia) Ho').
          - destruct Hnm as (_ & _ & Hn0). exact (Hd i Hi Hn0).
          - cbn beta in Hf. lia.
          - unfold W_of in Hw'. cbn in Hw'. lia.
          - pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ He))). lia. }
        assert (AGobj : agree_on Mw M2 obj 40).
        { apply AG2; [lia | lia | lia | lia |]. intros i Hi. apply HMg. apply Hdefobj. exact Hi. }
        assert (Cbl2 : cell8 SEGS M2 obj p).
        { eapply cellw_agree; [| eapply agree_on_sub; [exact AGobj | lia | cbn; lia] | lia | cbn; lia]. unfold Mw. cellpeel. }
        unfold cell8 in Cbl2.
        assert (DB2 : dbase R2) by exact (dbase_kept Rc R2 DBc KEPT).
        pose proof DB2 as DB2'. destruct DB2' as ((B2' & _ & _ & B8' & _) & _ & _).
        pose (E2 := Eseed R2 [Z_to_bv 64 parser; Z_to_bv 64 p]).
        assert (HR2 : regs_ok E2 (srs sr_id [(8%bv, EVar 32)]) R2).
        { apply regs_ok_srs; [apply regs_ok_seed|].
          repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact B8'. }
        assert (HK2 : know_ok SEGS E2 M2 []) by constructor.
        xruns HR2 HK2 100%nat STOPSD (SCR [] [EVar 33] []) 50%N.
        { split_scs; try sc_auto1. }
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRd; rename Rx into Rd end.
        rreg HRd 27%bv Q27. pose proof (syms_id_sound _ _ _ _ [2; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv HRd eq_refl) as Qs.
        apply (POST A2 M2 model2 Rd).
        + constructor.
          * exact AI2. * exact MS2. * congruence. * congruence.
          * dbase_from HRd DB2.
          * rewrite Qs, (KEPT 26%bv) by inl. exact G26.
          * rewrite Qs, (KEPT 22%bv) by inl. exact G22.
          *
            intros i Hi.
            destruct (Z.lt_ge_cases (sp - NTS + i) (sp - DEL_STACK)) as [Hlo | Hhi].
            -- pose proof (AG2 (sp - NTS + i) 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as E1.
               assert (Hd : defined Mw (sp - NTS + i) 1) by (intros j Hj; apply HMg; eapply (defined_pt _ _ _ _ DEF); lia).
               specialize (E1 Hd 0 ltac:(lia)). rewrite Z.add_0_r in E1. rewrite E1. apply HMg. eapply (defined_pt _ _ _ _ DEF); lia.
            -- replace (sp - NTS + i) with (sp - DEL_STACK + (sp - NTS + i - (sp - DEL_STACK))) by lia. apply DEF2. lia.
          * eapply eff_weaken; [eapply eff_trans; [exact EFw | eapply eff_widen; [exact EFF2|] | ]|].
            -- intros a Ha. unfold W_of, Wnt in *. cbn in *. lia.
            -- intros a Ha. eapply hi_unowned'; [exact AI2 | unfold W_of, Wnt in Ha; cbn in Ha; lia].
            -- intros a [[Ha|Ha]|Ha]; [left; exact Ha | right; left; exact Ha | right; right; split; [exact Hnz | exact Ha]].
          * unfold opsB. destruct (Z.eqb_spec bc 0); [lia|]. cbn in LAP. destruct LAP as (lv1 & Hadd & Heq). cbn.
            exists lv1. split; [exact Hadd|]. exists (live MI A2). split; [rewrite <- Heq; exact LDEL | reflexivity].
          * exact Hp0. * exact Hpc. * exact Hpal.
          * apply (proj2 (LDEL p (8 * n))). split; [exact Hpl|]. intros ->. apply Hpnew.
            apply (in_map fst _ (bl, 8 * bc)). apply tbl_blocks_live. unfold umap_blocks. destruct (Z.eqb_spec bc 0); [lia|]. apply in_app_iff. left. left. reflexivity.
          * exact Hpnew.
          * intros a [Ha|[Ha|[_ Ha]]]; [exact (HFoff a Ha) | intros Himg; pose proof (HLimg_lo _ Himg); lia |].
            exact (live_offimg' A1 M1 model1 bl (8 * bc) a AI Hbllive Ha).
          * eapply defined_agree; [| exact AGobj]. intros i Hi. apply HMg. apply Hdefobj. exact Hi.
        + exact Q27.
        + exact Cbl2.
        + eapply agree_on_trans; [apply HMa; unfold apart; lia | eapply agree_on_sub; [exact AGobj | lia | lia]].
        + intros q k v Hin. destruct (u_node U1 q k v Hin) as (Hlv & Hq0 & Hq1 & _ & _ & _ & _ & _ & _ & Hapb).
          destruct (live_facts' A1 M1 model1 q 32 AI Hlv) as (_ & _ & Hqc & Hqown). specialize (Hapb Hnz).
          assert (Hlv2 : In (q, 32) (live MI A2)).
          { apply (proj2 (LDEL q 32)). split; [exact Hlv|]. intros ->. unfold apart in Hapb. lia. }
          split; [| exact Hlv2].
          eapply agree_on_trans; [apply HMa; unfold apart; lia |].
          destruct (live_facts' A2 M2 model2 q 32 AI2 Hlv2) as (_ & _ & _ & Hqown2).
          intros i Hi. apply (ef_frame _ _ _ _ _ _ _ _ _ EFF2). rewrite u64_of_Z by lia.
          intros [Ho|[Ho'|[Hnm|[Hf|[Hw'|He]]]]].
          * exact (proj1 (Hqown (q + i) ltac:(lia)) Ho).
          * exact (proj1 (Hqown2 (q + i) ltac:(lia)) Ho').
          * destruct Hnm as (_ & _ & Hn0). exact (HMg _ (proj2 (Hqown (q + i) ltac:(lia))) Hn0).
          * cbn beta in Hf. unfold apart in Hapb. lia.
          * unfold W_of in Hw'. cbn in Hw'. lia.
          * exact (live_offimg' A1 M1 model1 q 32 (q + i) AI Hlv ltac:(lia) (HLrw_img _ (HLerr_rw _ He))).
    Qed.

    Definition FC (p : Z) (a : Z) : Prop := FB p a \/ (obj + 8 <= a < obj + 16).

#[local] Definition HTHNtD_0 : list (reg * expr) := [(27%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (26%bv, EVar 35); (22%bv, EVar 36)].
    Lemma phaseC : forall A1 M1 A2 M2 model2 R2 p,
      rst (FB p) (opsB p) p A2 M2 model2 R2 -> getr R2 27%bv = Z_to_bv 64 p ->
      umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      cell8 SEGS M2 obj p -> agree_on M1 M2 (obj + 8) 32 ->
      (forall q k v, In (q, (k, v)) ents -> agree_on M1 M2 q 32 /\ In (q, 32) (live MI A2)) ->
      (forall M3 R3,
          rst (FC p) (opsB p) p A2 M3 model2 R3 -> getr R3 27%bv = Z_to_bv 64 p ->
          cell8 SEGS M3 obj p -> cell8 SEGS M3 (obj + 8) n -> agree_on M1 M3 (obj + 16) 24 ->
          (forall q k v, In (q, (k, v)) ents -> agree_on M1 M3 q 32 /\ In (q, 32) (live MI A2)) ->
          (forall i, 0 <= i < n -> cell8 SEGS M3 (p + 8 * i) 0) ->
          srealizes SEGS (cfg fxr R3 NT_MSR M3 model2) K) ->
      srealizes SEGS (cfg fxr R2 NT_BCST M2 model2) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C fxr Ar Mr pn Ur CONTD.
      ctx. intros A1 M1 A2 M2 model2 R2 p D G27 U1 Cbl AGh Hnodes POST.
      destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq U0) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds DB S10 S6 DEF EFF LAP Hp0 Hpc Hpal Hpl Hpnew HFoff HDEF].
      pose proof DB as DB'. destruct DB' as (B & Q23 & Q25). pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
      pose proof HDEF as Hdefobj. unfold cell8 in Cbl. pose proof (proj1 Cbl) as Hpr.
      pose (E := Eseed R2 [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 n; Z_to_bv 64 (8 * n)]).
      assert (HR : regs_ok E (srs sr_id HTHNtD_0) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M2 []) by constructor.
      xruns HR HK 100%nat STOPSD (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. sc_so. eapply (defined_sub _ _ _ _ _ Hdefobj); lia. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
      set (Mw := wbytes M2 _ _).
      rreg HRc 1%bv T1. rreg HRc 10%bv T10. rreg HRc 11%bv T11. rreg HRc 12%bv T12. rreg HRc 26%bv T26. rreg HRc 22%bv T22. rreg HRc 27%bv T27.
      assert (DBc : dbase Rc) by (dbase_from HRc DB).
      assert (HMw : forall x : word, ~ (obj + 8 <= bv_unsigned x < obj + 16) -> Mw x = M2 x).
      { intros x Hx. pose proof (u64_range x). unfold Mw.
        rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      assert (HMg : forall x : word, M2 x <> None -> Mw x <> None) by (intros x Hx; unfold Mw; apply wbytes_grows; exact Hx).
      assert (HMa : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k (obj + 8) 8 -> agree_on M2 Mw a k).
      { intros a k Ha Hak H1 i Hi. apply HMw; rewrite u64_of_Z by lia; unfold apart in *; lia. }
      destruct (ai_live_block MI A2 M2 model2 p (8 * n) AI Hpl) as (_ & _ & _ & _ & Hpown).

      destruct (MEMSETH fxr Mw (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 NT_MSR) (8 * n) Rc) as (R4 & Hms4 & U10 & Hag4).
      { lia. }
      { rewrite u64_of_Z by lia. lia. }
      { apply store_ok_of_defined; [lia | lia |]. intros i Hi. apply HMg. exact (proj2 (proj2 (Hpown (p + i) ltac:(lia)))). }
      { apply bv_eq. vm_compute. reflexivity. }
      { exact T10. }
      { exact T11. }
      { exact T12. }
      { rewrite T1. apply bv_eq. reflexivity. }
      eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | exact Hms4 | ]. clear Hms4.
      set (M3 := wbytes Mw _ _).
      assert (HM3 : forall x : word, ~ (p <= bv_unsigned x < p + 8 * n) -> M3 x = Mw x).
      { intros x Hx. pose proof (u64_range x). unfold M3. rewrite wbytes_outside; [reflexivity | ..]; rewrite ?repeat_length, ?u64_of_Z by lia; lia. }
      assert (HM3g : forall x : word, Mw x <> None -> M3 x <> None) by (intros x Hx; unfold M3; apply wbytes_grows; exact Hx).
      assert (HM3a : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k p (8 * n) -> agree_on Mw M3 a k).
      { intros a k Ha Hak H1 i Hi. apply HM3; rewrite u64_of_Z by lia; unfold apart in *; lia. }
      assert (HP3 : forall r, In r [22; 26; 27]%bv -> getr R4 r = getr Rc r).
      { intros r Hr. apply Hag4. cbn in Hr. unfold ms_clob. repeat (destruct Hr as [<-|Hr]; [ninl|]). destruct Hr. }
      apply (POST M3 R4).
      - constructor.
        + eapply (ai_frame MI); [exact AI | | intros x Hx; apply HM3g, HMg, Hx | reflexivity | reflexivity].
          intros x Ho. pose proof (u64_range x). rewrite HM3; [apply HMw|]; intros Hx.
          * exact (hi_unowned' A2 M2 model2 (bv_unsigned x) AI ltac:(lia) Ho).
          * exact (proj1 (Hpown (bv_unsigned x) Hx) Ho).
        + exact MS. + exact Hfs. + exact Hfds.
        + exact (dbase_ms Rc R4 DBc Hag4).
        + rewrite (HP3 26%bv) by inl. exact T26.
        + rewrite (HP3 22%bv) by inl. exact T22.
        + eapply defined_agree; [exact DEF | eapply agree_on_trans; [apply HMa | apply HM3a]; unfold apart in *; lia].
        + eapply eff_weaken; [eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned'; [exact AI | unfold W_of, Wnt in Ha; cbn in Ha; lia]]|].
          * eapply eff_store with (F := fun a : Z => (obj + 8 <= a < obj + 16) \/ (p <= a < p + 8 * n)); [| intros x Hx; apply HM3g, HMg, Hx].
            intros x HF HW. rewrite HM3; [apply HMw|]; intros Hx; apply HF; [left; exact Hx | right; exact Hx].
          * intros a [Ha|[Ha|Ha]]; [left; exact Ha | right; exact Ha | left; left; exact Ha].
        + exact LAP.
        + exact Hp0. + exact Hpc. + exact Hpal. + exact Hpl. + exact Hpnew.
        + intros a [Ha|Ha]; [exact (HFoff a Ha) | intros Himg; pose proof (HLimg_lo _ Himg); lia].
        + intros i Hi. apply HM3g, HMg. apply Hdefobj. exact Hi.
      - rewrite (HP3 27%bv) by inl. exact T27.
      - eapply cellw_agree; [exact Cbl | eapply agree_on_trans; [apply HMa | apply HM3a]; unfold apart; cbn; lia | lia | cbn; lia].
      - unfold cell8. eapply cellw_agree; [| apply HM3a; unfold apart; cbn; lia | lia | cbn; lia]. unfold Mw. cellpeel.
      - eapply agree_on_trans; [eapply agree_on_sub; [exact AGh | lia | lia] | eapply agree_on_trans; [apply HMa | apply HM3a]; unfold apart; lia].
      - intros q k v Hin. destruct (Hnodes q k v Hin) as [Hag Hlv]. split; [| exact Hlv].
        destruct (u_node U1 q k v Hin) as (_ & Hq0 & Hq1 & _).
        assert (Hne : p <> q).
        { intros <-. apply Hpnew. apply (in_map fst _ (p, 32)). apply tbl_blocks_live. unfold umap_blocks. apply in_app_iff. right.
          apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin]. }
        pose proof (ai_live_disjoint MI A2 M2 model2 p (8 * n) q 32 AI Hpl Hlv Hne) as Hap.
        destruct (live_facts' A2 M2 model2 q 32 AI Hlv) as (_ & _ & Hqc & _).
        eapply agree_on_trans; [exact Hag | eapply agree_on_trans; [apply HMa | apply HM3a]; unfold apart in *; lia].
      - intros i Hi. unfold M3. apply cell8_zeroed; [lia | rewrite Z2Nat.id by lia; lia | lia | rewrite Z2Nat.id by lia; lia].
    Qed.

    #[local] Notation lent := (Z * (Z * (Z * Z * Z)))%type.
    Definition d0 : lent := (0, (0, (0, 0, 0))).
    #[local] Notation addr := (HRehashModel.addr (Z * Z * Z)%type).
    #[local] Notation hkey := (HRehashModel.hkey (Z * Z * Z)%type).
    #[local] Notation hh := (HRehashModel.hh (Z * Z * Z)%type n).
    #[local] Notation snt := (obj + 16).

    Lemma sc_disjZ : forall M E (sa1 sa2 : saddr) (b1 b2 n1 n2 : Z),
      edenot E (a_base sa1) = Z_to_bv 64 b1 -> edenot E (a_base sa2) = Z_to_bv 64 b2 ->
      0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 -> 0 < n1 < 2 ^ 64 -> 0 < n2 < 2 ^ 64 ->
      0 <= b1 + a_off sa1 -> b1 + a_off sa1 + n1 <= 2 ^ 64 -> 0 <= b2 + a_off sa2 -> b2 + a_off sa2 + n2 <= 2 ^ 64 ->
      (b1 + a_off sa1 + n1 <= b2 + a_off sa2 \/ b2 + a_off sa2 + n2 <= b1 + a_off sa1) ->
      sc_denot SEGS M E (SCDisj sa1 (ELit n1) sa2 (ELit n2)).
    Proof using.
      intros M E sa1 sa2 b1 b2 n1 n2 H1 H2 Hb1 Hb2 Hn1 Hn2 Ho1 Ho1' Ho2 Ho2' Hd.
      cbn [sc_denot]. unfold flat, estart, elenZ. cbn [edenot]. rewrite H1, H2, !u64_of_Z by lia. lia.
    Qed.

    Record lst (p : Z) (M1 : mem) (P S : list lent) (B : Z -> Z) (A : AS MI) (M : mem) (R : bvmap 5 word) : Prop := LST {
      l_regs : dbase R;
      l_x27 : getr R 27%bv = Z_to_bv 64 p;
      l_x26 : getr R 26%bv = Z_to_bv 64 n;
      l_x10 : getr R 10%bv = Z_to_bv 64 (addr (last P d0));
      l_x12 : getr R 12%bv = Z_to_bv 64 (hdaddr S);
      l_x11 : getr R 11%bv = Z_to_bv 64 (hh (last P d0));
      l_perm : Permutation (P ++ S) ents;
      l_binv : binv (Z * Z * Z)%type n snt P B;
      l_P : P <> [];
      l_p1 : cell8 SEGS M snt (hdaddr (P ++ S));
      l_chain : chain SEGS M (P ++ S);
      l_hash : forall e, In e ents -> cell8 SEGS M (addr e + 8) (hkey e);
      l_tail : forall e, In e ents -> agree_on M1 M (addr e + 8) 24;
      l_bkt : forall i, 0 <= i < n -> cell8 SEGS M (p + 8 * i) (B i);
      l_defp : defined M p (8 * n);
      l_defh : defined M obj 40;
      l_defn : forall e, In e ents -> defined M (addr e) 32;
      l_live : forall e, In e ents -> In (addr e, 32) (live MI A);
      l_plive : In (p, 8 * n) (live MI A)
    }.

    Definition Wloop (p : Z) (a : Z) : Prop :=
      (p <= a < p + 8 * n) \/ (snt <= a < snt + 8) \/ (exists e, In e ents /\ addr e <= a < addr e + 8).

    Lemma ent_facts : forall A1 M1 e, umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents -> In e ents ->
      0 < addr e /\ addr e + 32 <= 2 ^ 47 /\ addr e mod 16 = 0 /\ 0 <= hkey e < 2 ^ 32.
    Proof using AC L MI parser bl bc ents.
      intros A1 M1 [q [k v]] U Hin. destruct (u_node U q k v Hin) as (_ & Hq0 & Hq1 & Hal & _ & _ & Hkr & _). cbn. lia.
    Qed.

    Ltac rdx Hh H := eapply (sc_read_cellw _ _ _ _ _ _ _ _ H);
      [ cbn; lia | evs; rewrite ?w_remu, ?w_mul, ?w_add by lia; rewrite ?v_addi_Z by lia; rewrite ?Hh; first [reflexivity | f_equal; lia] | evs; first [reflexivity | f_equal; lia] ].

    Lemma last_any : forall {X : Type} (l : list X) a b, l <> [] -> last l a = last l b.
    Proof using.
      intros X l a b Hne. induction l as [|q l IH]; [exfalso; exact (Hne eq_refl)|].
      destruct l as [|r l']; [reflexivity|]. cbn. cbn in IH. apply IH. discriminate.
    Qed.

    Definition hda (L : list lent) (t : Z) : Z := match L with [] => t | b :: _ => addr b end.
    Fixpoint lnk (M : mem) (Ls : list lent) (t : Z) : Prop :=
      match Ls with
      | [] => True
      | a :: Ls' => cell8 SEGS M (addr a) (hda Ls' t) /\ lnk M Ls' t
      end.

    Lemma lnk_chain : forall M Ls, chain SEGS M Ls <-> lnk M Ls 0.
    Proof using.
      intros M Ls. induction Ls as [|[a v] Ls IH]; cbn; [tauto|].
      destruct Ls as [|[b v'] Ls']; cbn in *; tauto.
    Qed.

    Lemma hd_app : forall (A B : list lent) t, hda (A ++ B) t = hda A (hda B t).
    Proof using. intros [|a A] B t; reflexivity. Qed.

    Lemma hdaddr_hda : forall (A : list lent), hdaddr A = hda A 0.
    Proof using. intros [|[a v] A]; reflexivity. Qed.

    Lemma lnk_app : forall M A B t, lnk M (A ++ B) t <-> lnk M A (hda B t) /\ lnk M B t.
    Proof using.
      intros M A B t. induction A as [|a A IH]; cbn; [tauto|].
      rewrite hd_app. rewrite IH. destruct A as [|a' A']; (first [solve [clear; cbn; tauto] | cbn; tauto]).
    Qed.

    Lemma last_app_ne : forall {X : Type} (A B : list X) d, B <> [] -> last (A ++ B) d = last B d.
    Proof using.
      intros X A B d HB. induction A as [|a A IH]; [reflexivity|]. cbn. rewrite IH.
      destruct (A ++ B) as [|c Cc] eqn:HE; [| reflexivity]. apply app_eq_nil in HE. destruct HE as [_ HE]. exfalso. exact (HB HE).
    Qed.

    Lemma lnk_agree : forall M M' Ls t, lnk M Ls t -> (forall a, In a Ls -> agree_on M M' (addr a) 8) ->
      (forall a, In a Ls -> 0 <= addr a /\ addr a + 8 <= 2 ^ 64) -> lnk M' Ls t.
    Proof using.
      intros M M' Ls t. induction Ls as [|a Ls IH]; intros HL HA HR; cbn in *; [exact I|].
      destruct HL as [Hc HL]. split.
      - pose proof (HR a (or_introl eq_refl)). eapply cellw_agree; [exact Hc | apply HA; left; reflexivity | lia | cbn; lia].
      - apply IH; [exact HL | intros b Hb; apply HA; right; exact Hb | intros b Hb; apply HR; right; exact Hb].
    Qed.

    Lemma perm_nodup : forall A1 M1 Ls, umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents -> Permutation Ls ents -> List.NoDup (map addr Ls).
    Proof using AC L MI parser bl bc ents.
      intros A1 M1 Ls U HP. eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact HP|].
      apply base.NoDup_ListNoDup. exact (u_nodup U).
    Qed.

    Lemma nodup_app_ne : forall (l1 l2 : list lent) b b',
      List.NoDup (map addr (l1 ++ l2)) -> In b l1 -> In b' l2 -> addr b <> addr b'.
    Proof using.
      intros l1 l2 b b' Hnd H1 H2 Heq.
      revert Hnd H1. induction l1 as [|x l1 IH]; intros Hnd H1; [destruct H1|].
      cbn in Hnd. inversion Hnd as [|y l Hni Hnd']. subst.
      destruct H1 as [<-|H1].
      - apply Hni. rewrite Heq, map_app. apply in_app_iff. right. apply in_map. exact H2.
      - exact (IH Hnd' H1).
    Qed.

    Lemma last_in : forall (P : list lent) d, P <> [] -> In (last P d) P.
    Proof using.
      intros P d HP. destruct P as [|q P']; [exfalso; exact (HP eq_refl)|].
      assert (Hc : q :: P' <> []) by discriminate. rewrite (app_removelast_last d Hc) at 2. apply in_app_iff. right. left. reflexivity.
    Qed.

    Lemma apart_sub : forall a k b m a' k' b' m', apart a k b m -> a <= a' -> a' + k' <= a + k -> b <= b' -> b' + m' <= b + m -> apart a' k' b' m'.
    Proof using. unfold apart. intros. lia. Qed.
    Lemma apart_sym : forall a k b m, apart a k b m -> apart b m a k.
    Proof using. unfold apart. intros. lia. Qed.

    Lemma splice_facts : forall A1 M1 P S' B x M,
      umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      Permutation (P ++ x :: S') ents -> binv (Z * Z * Z)%type n snt P B -> P <> [] ->
      cell8 SEGS M snt (hdaddr (P ++ x :: S')) -> chain SEGS M (P ++ x :: S') ->
      0 <= hh x < n -> B (hh x) <> 0 ->
      exists nt P',
        cell8 SEGS M (B (hh x)) nt /\ 0 <= nt < 2 ^ 64 /\
        (B (hh x) = snt \/ exists y, In y P /\ B (hh x) = addr y /\ addr y <> addr (last P d0) /\ addr y <> addr x) /\
        last P' d0 = last P d0 /\ P' <> [] /\ Permutation (P' ++ S') (P ++ x :: S') /\ binv (Z * Z * Z)%type n snt P' B /\
        (forall M3, cell8 SEGS M3 (B (hh x)) (addr x) -> cell8 SEGS M3 (addr x) nt -> cell8 SEGS M3 (addr (last P d0)) (hdaddr S') ->
           (forall a, In a (P ++ S') -> addr a <> addr (last P d0) -> addr a <> addr x -> addr a <> B (hh x) -> agree_on M M3 (addr a) 8) ->
           (B (hh x) <> snt -> agree_on M M3 snt 8) ->
           cell8 SEGS M3 snt (hdaddr (P' ++ S')) /\ chain SEGS M3 (P' ++ S')).
    Proof using AC L MI parser bl bc ents.
      intros A1 M1 P S' B x M U1 PERM BI HP Cp1 CH Hh Hfull.
      pose proof (perm_nodup _ _ _ U1 PERM) as NDL.
      pose proof (u_obj_lo U1) as Hobj0.
      assert (Hnoty : forall e, In e (P ++ x :: S') -> addr e <> snt).
      { intros e He. assert (Hin : In e ents) by (eapply Permutation_in; [exact PERM | exact He]).
        destruct e as [q [k v]]. destruct (u_node U1 q k v Hin) as (_ & Hq0 & _ & _ & _ & _ & _ & _ & Hap & _). unfold apart in Hap. cbn. lia. }
      assert (Hrng : forall e, In e (P ++ x :: S') -> 0 <= addr e /\ addr e + 8 <= 2 ^ 64).
      { intros e He. destruct (ent_facts _ _ e U1 ltac:(eapply Permutation_in; [exact PERM | exact He])) as (H0 & H1 & _). lia. }
      apply lnk_chain in CH.
      set (w := last P d0).
      assert (HwP : In w P) by (unfold w; apply last_in; exact HP).

      pose proof NDL as NDxS. rewrite map_app in NDxS. apply NoDup_app_remove_l in NDxS. cbn in NDxS. apply NoDup_cons_iff in NDxS. destruct NDxS as [HxS NDS].
      assert (HSx : forall a, In a S' -> addr a <> addr x) by (intros a Ha He; apply HxS; rewrite <- He; apply in_map; exact Ha).
      assert (HPx : forall a, In a P -> addr a <> addr x) by (intros a Ha; exact (nodup_app_ne P (x :: S') a x NDL Ha (or_introl eq_refl))).
      assert (HPS : forall a b, In a P -> In b S' -> addr a <> addr b) by (intros a b Ha Hb; exact (nodup_app_ne P (x :: S') a b NDL Ha (or_intror Hb))).
      destruct (bi_just _ _ _ _ _ BI (hh x) Hh Hfull) as [[Ht (x0 & P0 & HP0 & Hx0)] | (P1 & y & z & P2 & HPd & Ht & Hz)].
      -
        exists (addr x0), (x :: P).
        assert (Hhd : hdaddr (P ++ x :: S') = addr x0) by (rewrite HP0; destruct x0 as [q v]; reflexivity).
        assert (HPR : P = removelast P ++ [w]) by (unfold w; apply app_removelast_last; exact HP).
        pose proof NDL as NDP. rewrite map_app in NDP. apply NoDup_app_remove_r in NDP.
        split; [rewrite Ht, <- Hhd; exact Cp1|].
        split; [pose proof (Hrng x0 ltac:(rewrite HP0; left; reflexivity)); lia|].
        split; [left; exact Ht|].
        split; [unfold w; rewrite HP0; reflexivity|].
        split; [discriminate|].
        split; [cbn [app]; apply Permutation_middle|].
        split.
        { apply (step_front (Z * Z * Z)%type n snt P x B BI Hh Ht ltac:(lia)).
          intros Q1 y z Q2 HQ. apply Hnoty. apply in_app_iff. left. rewrite HQ. apply in_app_iff. right. left. reflexivity. }
        intros M3 C3t C3x C3w AG AGs.
        split; [replace (hdaddr ((x :: P) ++ S')) with (addr x) by (destruct x as [q v]; reflexivity); rewrite <- Ht; exact C3t|].
        apply lnk_chain. cbn [app lnk]. split; [rewrite hd_app; rewrite HP0; cbn; exact C3x|].
        rewrite HPR in CH |- *. rewrite <- app_assoc in CH |- *. cbn [app] in CH |- *.
        apply lnk_app in CH. destruct CH as [CHR [CHw [CHx CHS]]]. cbn [hda] in CHR.
        apply lnk_app. cbn [lnk hda]. split; [|split; [rewrite <- hdaddr_hda; exact C3w | ]].
        + eapply lnk_agree; [exact CHR | | intros a Ha; apply Hrng; apply in_app_iff; left; rewrite HPR; apply in_app_iff; left; exact Ha].
          intros a Ha. assert (HaP : In a P) by (rewrite HPR; apply in_app_iff; left; exact Ha).
          apply AG; [apply in_app_iff; left; exact HaP | | exact (HPx a HaP) | rewrite Ht; apply Hnoty; apply in_app_iff; left; exact HaP].
          rewrite HPR in NDP. exact (nodup_app_ne _ _ a w NDP Ha (or_introl eq_refl)).
        + eapply lnk_agree; [exact CHS | | intros a Ha; apply Hrng; apply in_app_iff; right; right; exact Ha].
          intros a Ha. apply AG; [apply in_app_iff; right; exact Ha | exact (not_eq_sym (HPS w a HwP Ha)) | exact (HSx a Ha) | rewrite Ht; apply Hnoty; apply in_app_iff; right; right; exact Ha].
      -
        remember (z :: P2) as Q2 eqn:HQ2.
        assert (HQne : Q2 <> []) by (rewrite HQ2; discriminate).
        assert (HhQ : forall u, hda Q2 u = addr z) by (intros u; rewrite HQ2; reflexivity).
        assert (HwQ : last Q2 d0 = w) by (unfold w; rewrite HPd; symmetry; rewrite last_app_ne by discriminate; cbn; rewrite HQ2; reflexivity).
        assert (HQR : Q2 = removelast Q2 ++ [w]) by (rewrite <- HwQ; apply app_removelast_last; exact HQne).
        assert (HwQ2 : In w Q2) by (rewrite HQR; apply in_app_iff; right; left; reflexivity).
        assert (HF1 : P ++ x :: S' = P1 ++ (y :: Q2 ++ x :: S')) by (rewrite HPd, <- app_assoc; reflexivity).
        assert (HF2 : P ++ x :: S' = (P1 ++ [y]) ++ (Q2 ++ x :: S')) by (rewrite HPd, <- !app_assoc; reflexivity).
        assert (HyP : In y P) by (rewrite HPd; apply in_app_iff; right; left; reflexivity).
        assert (HQP : forall a, In a Q2 -> In a P) by (intros a Ha; rewrite HPd; apply in_app_iff; right; right; exact Ha).
        pose proof NDL as ND2. rewrite HF2 in ND2.
        assert (HyQS : forall a, In a (Q2 ++ x :: S') -> addr y <> addr a) by (intros a Ha; exact (nodup_app_ne _ _ y a ND2 ltac:(apply in_app_iff; right; left; reflexivity) Ha)).
        rewrite map_app in ND2. apply NoDup_app_remove_l in ND2.
        pose proof ND2 as NDQ. rewrite map_app in NDQ. apply NoDup_app_remove_r in NDQ. rewrite HQR in NDQ.
        pose proof NDL as ND1. rewrite HF1 in ND1.
        assert (Hyw : addr y <> addr w) by (apply HyQS; apply in_app_iff; left; exact HwQ2).
        exists (addr z), (P1 ++ y :: x :: Q2).
        rewrite HF1 in CH. apply lnk_app in CH. destruct CH as [CH1 CH2]. cbn [lnk hda] in CH1, CH2. destruct CH2 as [Cy CH3].
        rewrite hd_app, HhQ in Cy.
        apply lnk_app in CH3. destruct CH3 as [CHQ [CHx CHS]]. cbn [hda] in CHQ.
        rewrite HQR in CHQ. apply lnk_app in CHQ. destruct CHQ as [CHR [CHw _]]. cbn [hda] in CHR, CHw.
        split; [rewrite Ht; exact Cy|].
        split; [pose proof (Hrng z ltac:(rewrite HF1; apply in_app_iff; right; right; apply in_app_iff; left; rewrite HQ2; left; reflexivity)); lia|].
        split; [right; exists y; split; [exact HyP | split; [exact Ht | split; [exact Hyw | apply HyQS; apply in_app_iff; right; left; reflexivity]]]|].
        split; [rewrite last_app_ne by discriminate; cbn; rewrite <- HwQ; destruct Q2; [exfalso; exact (HQne eq_refl) | reflexivity]|].
        split; [destruct P1; discriminate|].
        split; [rewrite HF1, <- app_assoc; cbn [app]; apply Permutation_app_head; apply perm_skip; apply Permutation_middle|].
        split.
        { rewrite HQ2. apply step_splice; [rewrite <- HQ2, <- HPd; exact BI | exact Ht | rewrite Hz; reflexivity | apply Hnoty; apply in_app_iff; left; exact HyP
          | pose proof (Hnoty y ltac:(apply in_app_iff; left; exact HyP)); destruct (ent_facts _ _ y U1 ltac:(eapply Permutation_in; [exact PERM | apply in_app_iff; left; exact HyP])) as (Hy0 & _); lia
          | pose proof NDL as NDP; rewrite map_app in NDP; apply NoDup_app_remove_r in NDP; rewrite HPd, HQ2 in NDP; exact NDP]. }
        intros M3 C3t C3x C3w AG AGs.
        assert (Hts : B (hh x) <> snt) by (rewrite Ht; apply Hnoty; apply in_app_iff; left; exact HyP).
        split.
        { rewrite hdaddr_hda, <- app_assoc, hd_app. cbn [hda]. rewrite hdaddr_hda, HF1, hd_app in Cp1. cbn [hda] in Cp1.
          pose proof (u_obj_hi U1). eapply cellw_agree; [exact Cp1 | exact (AGs Hts) | lia | cbn; lia]. }
        apply lnk_chain. rewrite <- app_assoc. cbn [app]. apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- Ht; exact C3t | split; [rewrite hd_app, HhQ; exact C3x |]]].
        + eapply lnk_agree; [exact CH1 | | intros a Ha; apply Hrng; rewrite HF1; apply in_app_iff; left; exact Ha].
          intros a Ha. assert (HaP : In a P) by (rewrite HPd; apply in_app_iff; left; exact Ha).
          apply AG; [apply in_app_iff; left; exact HaP | | exact (HPx a HaP) | rewrite Ht].
          * exact (nodup_app_ne _ _ a w ND1 Ha ltac:(right; apply in_app_iff; left; exact HwQ2)).
          * exact (nodup_app_ne _ _ a y ND1 Ha (or_introl eq_refl)).
        + apply lnk_app. split.
          * rewrite HQR. apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- hdaddr_hda; exact C3w | exact I]].
            eapply lnk_agree; [exact CHR | | intros a Ha; apply Hrng; apply in_app_iff; left; apply HQP; rewrite HQR; apply in_app_iff; left; exact Ha].
            intros a Ha. assert (HaQ : In a Q2) by (rewrite HQR; apply in_app_iff; left; exact Ha).
            apply AG; [apply in_app_iff; left; exact (HQP a HaQ) | exact (nodup_app_ne _ _ a w NDQ Ha (or_introl eq_refl)) | exact (HPx a (HQP a HaQ)) | rewrite Ht; exact (not_eq_sym (HyQS a ltac:(apply in_app_iff; left; exact HaQ)))].
          * eapply lnk_agree; [exact CHS | | intros a Ha; apply Hrng; apply in_app_iff; right; right; exact Ha].
            intros a Ha. apply AG; [apply in_app_iff; right; exact Ha | exact (not_eq_sym (HPS w a HwP Ha)) | exact (HSx a Ha) | rewrite Ht; exact (not_eq_sym (HyQS a ltac:(apply in_app_iff; right; right; exact Ha)))].
    Qed.

    Lemma nodes_apart : forall A1 M1 a b, umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents -> In a ents -> In b ents -> addr a <> addr b ->
      apart (addr a) 32 (addr b) 32.
    Proof using AC L MI parser bl bc ents.
      intros A1 M1 a b U Ha Hb Hne. apply (u_napart U); [apply in_map; exact Ha | apply in_map; exact Hb | exact Hne].
    Qed.

    Lemma p_node_apart : forall p A M model e, ainv MI A M model -> In (p, 8 * n) (live MI A) -> ~ In p (map fst (live MI Ar)) ->
      In (addr e, 32) (live MI A) -> In e ents -> apart p (8 * n) (addr e) 32.
    Proof using AC L MI parser bl bc ents Ar Mr Ur.
      intros p A M model e AI Hp Hpnew He Hin.
      apply (ai_live_disjoint MI A M model p (8 * n) (addr e) 32 AI Hp He). intros Heq. apply Hpnew. rewrite Heq.
      apply (in_map fst _ (addr e, 32)). destruct e as [q [k v]]. exact (proj1 (u_node Ur q k v Hin)).
    Qed.

    Ltac sub_of x y := lazymatch y with | x => idtac | Z.add x _ => idtac | Z.add (Z.add x _) _ => idtac end.
    Ltac dj_apart Hr :=
      cbn [a_off]; rewrite ?Z.add_0_r;
      lazymatch goal with |- ?a + ?k <= ?b \/ ?b + ?m <= ?a => change (apart a k b m) end;
      match goal with H : apart ?a0 _ ?b0 _ |- apart ?a _ ?b _ =>
        first [ sub_of a0 a; sub_of b0 b; eapply (apart_sub _ _ _ _ _ _ _ _ H); clear - Hr; lia
              | sub_of a0 b; sub_of b0 a; eapply (apart_sub _ _ _ _ _ _ _ _ (apart_sym _ _ _ _ H)); clear - Hr; lia ] end.
    Ltac dj Hh := eapply sc_disjZ;
      [ evs; rewrite ?w_remu, ?w_mul, ?w_add by lia; rewrite ?v_addi_Z by lia; rewrite ?Hh; reflexivity
      | evs; rewrite ?w_remu, ?w_mul, ?w_add by lia; rewrite ?v_addi_Z by lia; rewrite ?Hh; reflexivity
      | lia | lia | lia | lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; unfold apart in *; lia ].

    Ltac nrm Hrm Hba := rewrite ?Hrm; rewrite ?Hba.
    Ltac rdq Hrm Hba H :=
      lazymatch type of H with cellw _ _ ?a _ _ =>
      eapply (sc_read_cellw _ _ _ _ _ _ _ _ H);
      [ apply N.le_refl
      | evs; nrm Hrm Hba; lazymatch goal with |- v_addi (Z_to_bv 64 ?b) _ = _ => sub_of b a end;
        rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r; first [reflexivity | f_equal; lia]
      | evs; first [reflexivity | f_equal; lia] ] end.
    Ltac djq Hrm Hba Hr := eapply sc_disjZ;
      [ evs; nrm Hrm Hba; reflexivity | evs; nrm Hrm Hba; reflexivity
      | lia | lia | lia | lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | dj_apart Hr ].
    Ltac soq Hrm Hba := eapply (sc_storeok _ _ _ _ _ 8);
      [ evs; nrm Hrm Hba; reflexivity | lia | cbn [a_off]; lia | cbn [a_off]; lia
      | cbn [a_off]; rewrite ?Z.add_0_r;
        first [ lazymatch goal with |- defined _ ?a _ => match goal with D : defined _ a _ |- _ => eapply (defined_sub _ _ _ _ _ D); lia end end
              | match goal with D : defined _ _ _ |- _ => eapply (defined_sub _ _ _ _ _ D); lia end ] ].
    Ltac flq Hrm Hba := eapply sc_flat; [evs; nrm Hrm Hba; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia].
    Ltac brq Hrm Hba := cbn [sc_denot]; evs; nrm Hrm Hba; rewrite ?br_eq, ?br_ne, ?br_ltu by lia; bool_lia.
    Ltac scq Hrm Hba Hr :=
      lazymatch goal with
      | |- sc_denot _ _ _ (SCBr _ _ _ _) => brq Hrm Hba
      | |- sc_denot _ _ _ (SCFlat _ _) => flq Hrm Hba
      | |- sc_denot _ _ _ (SCDisj _ _ _ _) => djq Hrm Hba Hr
      | |- sc_denot _ _ _ (SCStoreOk _ _) => soq Hrm Hba
      | |- sc_denot _ _ _ (SCReadBase _ _ _ _) => match goal with H : cellw _ _ _ 8%N _ |- _ => rdq Hrm Hba H end
      end.
    Ltac scqs Hrm Hba Hr := split_scs; scq Hrm Hba Hr.

    Ltac finq Hrm Hba FIN HR' DB :=
      eapply FIN;
      [ first [ exact (or_intror I) | evs; nrm Hrm Hba; rewrite ?w_add, ?v_addi_Z by lia; rewrite ?Z.add_0_r; reflexivity ]
      | dbase_from HR' DB
      | let Q := fresh in rreg HR' 27%bv Q; exact Q
      | let Q := fresh in rreg HR' 26%bv Q; exact Q
      | let Q := fresh in rreg HR' 10%bv Q; exact Q
      | let Q := fresh in rreg HR' 12%bv Q; rewrite Q; reflexivity
      | let Q := fresh in rreg HR' 11%bv Q; rewrite Q; nrm Hrm Hba; first [reflexivity | f_equal; lia]
      | ].

#[local] Definition HTHNtD_1 : list (reg * expr) := [(27%bv, EVar 32); (26%bv, EVar 33); (10%bv, EVar 35); (12%bv, EVar 36); (11%bv, EVar 37); (2%bv, EVar 38)].
    Lemma loop_step : forall p A1 M1 P S B A M model R x S',
      S = x :: S' ->
      ainv MI A M model -> mstd model -> umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      lst p M1 P S B A M R ->
      0 < p -> p + 8 * n <= alloc_ceiling -> ~ In p (map fst (live MI Ar)) ->
      (forall M' R' P' B' (pc : Z),
          (pc = NT_AFTER /\ S' = [] \/ pc = NT_LOOP /\ S' <> []) ->
          lst p M1 P' S' B' A M' R' ->
          (forall a : word, ~ Wloop p (bv_unsigned a) -> M' a = M a) -> (forall a : word, M a <> None -> M' a <> None) ->
          ainv MI A M' model ->
          srealizes SEGS (cfg fxr R' pc M' model) K) ->
      srealizes SEGS (cfg fxr R NT_LOOP M model) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C fxr Ar Mr pn Ur.
      ctx. intros p A1 M1 P S B A M model R x S' HS AI MS U1 LS Hp0 Hpc Hpnew POST.
      destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof (u_obj_hi Ur) as Hh1.
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq Ur) as HB; unfold BSEQ in HB; cbn in HB; lia).
      destruct LS as [DB X27 X26 X10 X12 X11 PERM BI HP Cp1 CH HASH TAIL BK DEFp DEFh DEFn LIVE PLIVE].
      pose proof DB as DB0. destruct DB0 as (B0 & HQ23 & HQ25). destruct B0 as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
      subst S.

      set (w := last P d0) in *.
      assert (Hxin : In x ents) by (eapply Permutation_in; [exact PERM | apply in_app_iff; right; left; reflexivity]).
      assert (HwinE : In w ents).
      { eapply Permutation_in; [exact PERM | apply in_app_iff; left]. subst w. destruct P as [|p1 P1]; [exfalso; exact (HP eq_refl)|].
        assert (Hc : p1 :: P1 <> []) by discriminate. rewrite (app_removelast_last d0 Hc) at 2. apply in_app_iff. right. left. reflexivity. }
      destruct (ent_facts _ _ x U1 Hxin) as (Hx0 & Hx1 & Hxal & Hxk). destruct (ent_facts _ _ w U1 HwinE) as (Hw0 & Hw1 & Hwal & Hwk).
      pose proof (HASH x Hxin) as Cxh. unfold cell8 in Cxh.
      assert (Hn0 : 0 < n) by lia.
      pose proof (hh_range (Z * Z * Z)%type n Hn0 x) as Hhx. pose proof (hh_range (Z * Z * Z)%type n Hn0 w) as Hhw.
      set (h := hh x) in *.
      pose proof (BK h Hhx) as Cb. unfold cell8 in Cb. pose proof (proj1 Cb) as HBr.

      assert (Cxn : cell8 SEGS M (addr x) (hdaddr S')).
      { clear - CH. revert CH. generalize P. intros P0 CH. induction P0 as [|q P0 IH]; cbn in CH.
        - destruct x as [xa xv]. cbn. exact (proj1 CH).
        - destruct q as [qa qv]. exact (IH (proj2 CH)). }
      unfold cell8 in Cxn. pose proof (proj1 Cxn) as Hnxr.

      assert (Hh : hkey x mod n = h) by reflexivity.
      assert (HPx : (P ++ [x]) ++ S' = P ++ x :: S') by (rewrite <- app_assoc; reflexivity).
      assert (Hlastx : last (P ++ [x]) d0 = x) by (apply last_last).
      assert (HS'r : 0 <= hdaddr S' < 2 ^ 64) by exact Hnxr.

      pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 n; Z_to_bv 64 snt; Z_to_bv 64 (addr w); Z_to_bv 64 (addr x); Z_to_bv 64 (hh w); Z_to_bv 64 sp; Z_to_bv 64 0;
                          Z_to_bv 64 (hkey x); Z_to_bv 64 (hdaddr S'); Z_to_bv 64 (B h)]).
      assert (HR : regs_ok E (srs sr_id HTHNtD_1) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.

      clear Hncase.
      destruct (Z.eq_dec h (hh w)) as [Hsame | Hdiff].
      -
        assert (FIN : forall R', regs_ok E (srs sr_id [(27%bv, EVar 32); (26%bv, EVar 33); (10%bv, EVar 36); (12%bv, EVar 41); (11%bv, EVar 37); (2%bv, EVar 38);
                                                      (13%bv, EVar 13); (14%bv, EVar 14); (15%bv, EVar 15); (16%bv, EVar 16)]) R' \/ True ->
                  dbase R' ->
                  getr R' 27%bv = Z_to_bv 64 p -> getr R' 26%bv = Z_to_bv 64 n ->
                  getr R' 10%bv = Z_to_bv 64 (addr x) -> getr R' 12%bv = Z_to_bv 64 (hdaddr S') -> getr R' 11%bv = Z_to_bv 64 (hh w) ->
                  forall pc, (pc = NT_AFTER /\ S' = [] \/ pc = NT_LOOP /\ S' <> []) ->
                  srealizes SEGS (cfg fxr R' pc M model) K).
        { intros R' _ DB' Q27 Q26 Q10 Q12 Q11 pc Hpc'.
          apply (POST M R' (P ++ [x]) B pc Hpc'); [| intros a _; reflexivity | intros a Ha; exact Ha | exact AI].
          constructor; try assumption.
          - rewrite Hlastx. exact Q10.
          - rewrite Hlastx. rewrite Q11. f_equal. symmetry. exact Hsame.
          - rewrite HPx. exact PERM.
          - apply (step_same (Z * Z * Z)%type n snt P x B BI HP). fold h. rewrite Hsame. f_equal. unfold w. apply last_any. exact HP.
          - intros Heq. destruct P; discriminate Heq.
          - rewrite HPx. exact Cp1.
          - rewrite HPx. exact CH. }
        destruct (Z.lt_ge_cases (hkey x) n) as [Hlt | Hge].
        + assert (Hxh : hkey x = h) by (rewrite <- Hh; symmetry; apply Z.mod_small; lia).
            assert (Hrm : mul_div M_REMU (Z_to_bv 64 (hkey x)) (Z_to_bv 64 n) = Z_to_bv 64 h) by (rewrite w_remu by lia; f_equal; exact Hh).
            assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (hkey x))) = Z_to_bv 64 (p + 8 * h)) by (rewrite w_mul, w_add by lia; f_equal; lia).
          destruct S' as [|x' S''].
          * xruns HR HK 100%nat STOPSD (SCR [true; true; true] [EVar 40; EVar 41] []) 50%N; [scqs Hrm Hba Hhx|].
            finq Hrm Hba FIN HR' DB. left. split; reflexivity.
          * destruct (ent_facts _ _ x' U1 ltac:(eapply Permutation_in; [exact PERM | apply in_app_iff; right; right; left; reflexivity])) as (Hx'0 & Hx'1 & _).
            destruct x' as [xa' xv']. unfold HRehashModel.addr in Hx'0, Hx'1. cbn [hdaddr fst] in *.
            xruns HR HK 100%nat STOPSD (SCR [true; true; false] [EVar 40; EVar 41] []) 50%N; [scqs Hrm Hba Hhx|].
            finq Hrm Hba FIN HR' DB. right. split; [reflexivity | discriminate].
        + assert (Hrm : mul_div M_REMU (Z_to_bv 64 (hkey x)) (Z_to_bv 64 n) = Z_to_bv 64 h) by (rewrite w_remu by lia; f_equal; exact Hh).
            assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 h)) = Z_to_bv 64 (p + 8 * h)) by (rewrite w_mul, w_add by lia; reflexivity).
          destruct S' as [|x' S''].
          * xruns HR HK 100%nat STOPSD (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N; [scqs Hrm Hba Hhx|].
            finq Hrm Hba FIN HR' DB. left. split; reflexivity.
          * destruct (ent_facts _ _ x' U1 ltac:(eapply Permutation_in; [exact PERM | apply in_app_iff; right; right; left; reflexivity])) as (Hx'0 & Hx'1 & _).
            destruct x' as [xa' xv']. unfold HRehashModel.addr in Hx'0, Hx'1. cbn [hdaddr fst] in *.
            xruns HR HK 100%nat STOPSD (SCR [false; true; false] [EVar 40; EVar 41] []) 50%N; [scqs Hrm Hba Hhx|].
            finq Hrm Hba FIN HR' DB. right. split; [reflexivity | discriminate].
      -
        pose proof (perm_nodup _ _ _ U1 PERM) as NDL.
        assert (HwP : In w P) by (unfold w; apply last_in; exact HP).
        assert (Hwx : addr w <> addr x) by (exact (nodup_app_ne P (x :: S') w x NDL HwP (or_introl eq_refl))).

        assert (Hxw_ap : apart (addr x) 32 (addr w) 32) by (exact (nodes_apart _ _ x w U1 Hxin HwinE (not_eq_sym Hwx))).
        assert (Hpx : apart p (8 * n) (addr x) 32) by (exact (p_node_apart p A M model x AI PLIVE Hpnew (LIVE x Hxin) Hxin)).
        assert (Hpw : apart p (8 * n) (addr w) 32) by (exact (p_node_apart p A M model w AI PLIVE Hpnew (LIVE w HwinE) HwinE)).
        destruct (Z.eq_dec (B h) 0) as [Hempty | Hfull].
        +
          assert (FIN : forall R' Mw,
                    Mw = wbytes M (Z_to_bv 64 (p + 8 * h)) (word_to_le_bytes 8 (Z_to_bv 64 (addr w))) ->
                    dbase R' ->
                    getr R' 27%bv = Z_to_bv 64 p -> getr R' 26%bv = Z_to_bv 64 n ->
                    getr R' 10%bv = Z_to_bv 64 (addr x) -> getr R' 12%bv = Z_to_bv 64 (hdaddr S') -> getr R' 11%bv = Z_to_bv 64 h ->
                    forall pc, (pc = NT_AFTER /\ S' = [] \/ pc = NT_LOOP /\ S' <> []) ->
                    srealizes SEGS (cfg fxr R' pc Mw model) K).
          { intros R' Mw -> DB' Q27 Q26 Q10 Q12 Q11 pc Hpc'.
            assert (HMw : forall a : word, ~ (p + 8 * h <= bv_unsigned a < p + 8 * h + 8) -> wbytes M (Z_to_bv 64 (p + 8 * h)) (word_to_le_bytes 8 (Z_to_bv 64 (addr w))) a = M a).
            { intros a Ha. pose proof (u64_range a). rewrite wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
            assert (HMg : forall a : word, M a <> None -> wbytes M (Z_to_bv 64 (p + 8 * h)) (word_to_le_bytes 8 (Z_to_bv 64 (addr w))) a <> None) by (intros a Ha; apply wbytes_grows; exact Ha).
            assert (HMa : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k (p + 8 * h) 8 -> agree_on M (wbytes M (Z_to_bv 64 (p + 8 * h)) (word_to_le_bytes 8 (Z_to_bv 64 (addr w)))) a k).
            { intros a k Ha Hak H1 i Hi. apply HMw; rewrite u64_of_Z by lia; unfold apart in *; lia. }
            apply (POST _ R' (P ++ [x]) (fun i => if i =? hh x then addr (last P x) else B i) pc Hpc');
              [| intros a Ha; apply HMw; intros Hx; apply Ha; left; lia | exact HMg |].
            - constructor; try assumption.
              + rewrite Hlastx. exact Q10.
              + rewrite Hlastx. exact Q11.
              + rewrite HPx. exact PERM.
              + apply (step_empty (Z * Z * Z)%type n snt P x B BI HP Hn0). unfold HRehashModel.ent. replace (last P x) with w by (unfold w; apply last_any; exact HP). lia.
              + intros Heq. destruct P; discriminate Heq.
              + rewrite HPx. eapply cellw_agree; [exact Cp1 | apply HMa; unfold apart; lia | lia | cbn; lia].
              + rewrite HPx. apply lnk_chain. eapply lnk_agree; [apply lnk_chain; exact CH | |].
                * intros a Hin. assert (Ha : In a ents) by (eapply Permutation_in; [exact PERM | exact Hin]).
                  destruct (ent_facts _ _ a U1 Ha) as (Ha0 & Ha1 & _).
                  pose proof (p_node_apart p A M model a AI PLIVE Hpnew (LIVE a Ha) Ha) as Hap. apply HMa; unfold apart in *; lia.
                * intros a Hin. assert (Ha : In a ents) by (eapply Permutation_in; [exact PERM | exact Hin]).
                  destruct (ent_facts _ _ a U1 Ha) as (Ha0 & Ha1 & _). lia.
              + intros e He. destruct (ent_facts _ _ e U1 He) as (He0 & He1 & _).
                pose proof (p_node_apart p A M model e AI PLIVE Hpnew (LIVE e He) He) as Hap.
                eapply cellw_agree; [exact (HASH e He) | apply HMa; unfold apart in *; lia | lia | cbn; lia].
              + intros e He. destruct (ent_facts _ _ e U1 He) as (He0 & He1 & _).
                pose proof (p_node_apart p A M model e AI PLIVE Hpnew (LIVE e He) He) as Hap.
                eapply agree_on_trans; [exact (TAIL e He) | apply HMa; unfold apart in *; lia].
              + intros i Hi. destruct (Z.eqb_spec i (hh x)) as [->|Hne].
                * unfold HRehashModel.ent. replace (last P x) with w by (unfold w; apply last_any; exact HP). replace (hh x) with h by reflexivity. unfold cell8. cellpeel.
                * eapply cellw_agree; [exact (BK i Hi) | apply HMa; unfold apart; lia | lia | cbn; lia].
              + intros i Hi. apply HMg. apply DEFp. exact Hi.
              + eapply defined_agree; [exact DEFh | apply HMa; unfold apart; lia].
              + intros e He i Hi. apply HMg. apply (DEFn e He). exact Hi.
            - eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
              intros a Ho. pose proof (u64_range a). apply HMw. intros Ha.
              destruct (ai_live_block MI A M model p (8 * n) AI PLIVE) as (_ & _ & _ & _ & Hpown). exact (proj1 (Hpown (bv_unsigned a) ltac:(lia)) Ho). }
          destruct (Z.lt_ge_cases (hkey x) n) as [Hlt | Hge].
          * assert (Hxh : hkey x = h) by (rewrite <- Hh; symmetry; apply Z.mod_small; lia).
            assert (Hrm : mul_div M_REMU (Z_to_bv 64 (hkey x)) (Z_to_bv 64 n) = Z_to_bv 64 h) by (rewrite w_remu by lia; f_equal; exact Hh).
            assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (hkey x))) = Z_to_bv 64 (p + 8 * h)) by (rewrite w_mul, w_add by lia; f_equal; lia).
            destruct S' as [|x' S''].
            -- xruns HR HK 100%nat STOPSD (SCR [true; false; false; false] [EVar 40; EVar 42; EVar 41] []) 50%N; [scqs Hrm Hba Hhx|].
               finq Hrm Hba FIN HR' DB. left. split; reflexivity.
            -- destruct (ent_facts _ _ x' U1 ltac:(eapply Permutation_in; [exact PERM | apply in_app_iff; right; right; left; reflexivity])) as (Hx'0 & Hx'1 & _).
               destruct x' as [xa' xv']. unfold HRehashModel.addr in Hx'0, Hx'1. cbn [hdaddr fst] in *.
               xruns HR HK 100%nat STOPSD (SCR [true; false; false; true] [EVar 40; EVar 42; EVar 41] []) 50%N; [scqs Hrm Hba Hhx|].
               finq Hrm Hba FIN HR' DB. right. split; [reflexivity | discriminate].
          * assert (Hrm : mul_div M_REMU (Z_to_bv 64 (hkey x)) (Z_to_bv 64 n) = Z_to_bv 64 h) by (rewrite w_remu by lia; f_equal; exact Hh).
            assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 h)) = Z_to_bv 64 (p + 8 * h)) by (rewrite w_mul, w_add by lia; reflexivity).
            destruct S' as [|x' S''].
            -- xruns HR HK 100%nat STOPSD (SCR [false; false; false; false] [EVar 40; EVar 42; EVar 41] []) 50%N; [scqs Hrm Hba Hhx|].
               finq Hrm Hba FIN HR' DB. left. split; reflexivity.
            -- destruct (ent_facts _ _ x' U1 ltac:(eapply Permutation_in; [exact PERM | apply in_app_iff; right; right; left; reflexivity])) as (Hx'0 & Hx'1 & _).
               destruct x' as [xa' xv']. unfold HRehashModel.addr in Hx'0, Hx'1. cbn [hdaddr fst] in *.
               xruns HR HK 100%nat STOPSD (SCR [false; false; false; true] [EVar 40; EVar 42; EVar 41] []) 50%N; [scqs Hrm Hba Hhx|].
               finq Hrm Hba FIN HR' DB. right. split; [reflexivity | discriminate].
        +
          destruct (splice_facts A1 M1 P S' B x M U1 PERM BI HP Cp1 CH Hhx Hfull) as (nt & P' & Ct & Hnt & Hty & HlP' & HP'ne & PERM' & BI' & HCH').
          fold w in Hty, HlP', HCH'. fold h in Ct, Hty, BI', HCH'.
          pose proof (u_obj_hi U1) as Hobjhi. pose proof (u_obj_lo U1) as Hobjlo.
          assert (HT : 0 < B h /\ B h + 8 <= 2 ^ 47 /\ defined M (B h) 8 /\ apart (B h) 8 (addr w) 32 /\ apart (B h) 8 (addr x) 32 /\ apart p (8 * n) (B h) 8
                       /\ (forall a, B h <= a < B h + 8 -> ~ owned MI A a)
                       /\ (forall e, In e ents -> addr e <> B h -> apart (B h) 8 (addr e) 32)
                       /\ (B h <> snt -> apart (B h) 8 obj 40)
                       /\ (forall a, B h <= a < B h + 8 -> Wloop p a)).
          { destruct Hty as [Ht | (y & HyP & Ht & Hyw & Hyx)]; rewrite Ht.
            - destruct x as [xq [xk xv]]. destruct (u_node U1 xq xk xv Hxin) as (_ & _ & _ & _ & _ & _ & _ & _ & Hxobj & _).
              destruct w as [wq [wk wv]]. destruct (u_node U1 wq wk wv HwinE) as (_ & _ & _ & _ & _ & _ & _ & _ & Hwobj & _).
              unfold HRehashModel.addr. cbn [fst].
              split; [lia|]. split; [lia|]. split; [eapply (defined_sub _ _ _ _ _ DEFh); lia|].
              split; [eapply apart_sub; [exact (apart_sym _ _ _ _ Hwobj) | lia | lia | lia | lia]|].
              split; [eapply apart_sub; [exact (apart_sym _ _ _ _ Hxobj) | lia | lia | lia | lia]|].
              split; [unfold apart; lia|].
              split; [intros a Ha; apply (hi_unowned' A M model a AI); lia|].
              split; [intros e He _; destruct e as [eq [ek evv]]; destruct (u_node U1 eq ek evv He) as (_ & _ & _ & _ & _ & _ & _ & _ & Heobj & _);
                      eapply apart_sub; [exact (apart_sym _ _ _ _ Heobj) | cbn; lia | cbn; lia | cbn; lia | cbn; lia]|].
              split; [intros Hc; exfalso; exact (Hc eq_refl)|].
              intros a Ha. right. left. lia.
            - assert (Hyin : In y ents) by (eapply Permutation_in; [exact PERM | apply in_app_iff; left; exact HyP]).
              destruct (ent_facts _ _ y U1 Hyin) as (Hy0 & Hy1 & _).
              split; [lia|]. split; [lia|]. split; [eapply (defined_sub _ _ _ _ _ (DEFn y Hyin)); lia|].
              split; [eapply apart_sub; [exact (nodes_apart _ _ y w U1 Hyin HwinE Hyw) | lia | lia | lia | lia]|].
              split; [eapply apart_sub; [exact (nodes_apart _ _ y x U1 Hyin Hxin Hyx) | lia | lia | lia | lia]|].
              split; [eapply apart_sub; [exact (p_node_apart p A M model y AI PLIVE Hpnew (LIVE y Hyin) Hyin) | lia | lia | lia | lia]|].
              split; [intros a Ha; destruct (ai_live_block MI A M model (addr y) 32 AI (LIVE y Hyin)) as (_ & _ & _ & _ & Hown); exact (proj1 (Hown a ltac:(lia)))|].
              split; [intros e He Hne; eapply apart_sub; [exact (nodes_apart _ _ y e U1 Hyin He (not_eq_sym Hne)) | lia | lia | lia | lia]|].
              split; [intros _; destruct y as [yq [yk yv]]; destruct (u_node U1 yq yk yv Hyin) as (_ & _ & _ & _ & _ & _ & _ & _ & Hyobj & _);
                      eapply apart_sub; [exact Hyobj | cbn; lia | cbn; lia | lia | lia]|].
              intros a Ha. right. right. exists y. split; [exact Hyin | lia]. }
          destruct HT as (Ht0 & Ht1 & DEFt & Htw & Htx & Hpt & Htown & Hte & Htobj & HtW).
          pose proof (DEFn w HwinE) as DEFw. pose proof (DEFn x Hxin) as DEFx.
          clear HR HK. clear E.
          pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 n; Z_to_bv 64 snt; Z_to_bv 64 (addr w); Z_to_bv 64 (addr x); Z_to_bv 64 (hh w); Z_to_bv 64 sp; Z_to_bv 64 0;
                              Z_to_bv 64 (hkey x); Z_to_bv 64 (hdaddr S'); Z_to_bv 64 (B h); Z_to_bv 64 nt]).
          assert (HR : regs_ok E (srs sr_id HTHNtD_1) R).
          { apply regs_ok_srs; [apply regs_ok_seed|].
            repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
          assert (HK : know_ok SEGS E M []) by constructor.
          assert (FIN : forall R' M3,
                    M3 = wbytes (wbytes (wbytes M (Z_to_bv 64 (addr w)) (word_to_le_bytes 8 (Z_to_bv 64 (hdaddr S'))))
                                        (Z_to_bv 64 (addr x)) (word_to_le_bytes 8 (Z_to_bv 64 nt)))
                                (Z_to_bv 64 (B h)) (word_to_le_bytes 8 (Z_to_bv 64 (addr x))) ->
                    dbase R' ->
                    getr R' 27%bv = Z_to_bv 64 p -> getr R' 26%bv = Z_to_bv 64 n ->
                    getr R' 10%bv = Z_to_bv 64 (addr w) -> getr R' 12%bv = Z_to_bv 64 (hdaddr S') -> getr R' 11%bv = Z_to_bv 64 (hh w) ->
                    forall pc, (pc = NT_AFTER /\ S' = [] \/ pc = NT_LOOP /\ S' <> []) ->
                    srealizes SEGS (cfg fxr R' pc M3 model) K).
          { intros R' M3 HM3 DB' Q27 Q26 Q10 Q12 Q11 pc Hpc'.
            assert (HMw : forall a : word, ~ (addr w <= bv_unsigned a < addr w + 8) -> ~ (addr x <= bv_unsigned a < addr x + 8) -> ~ (B h <= bv_unsigned a < B h + 8) -> M3 a = M a).
            { intros a H1 H2 H3. pose proof (u64_range a). rewrite HM3.
              rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
            assert (HMg : forall a : word, M a <> None -> M3 a <> None) by (intros a Ha; rewrite HM3; do 3 apply wbytes_grows; exact Ha).
            assert (HMa : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k (addr w) 8 -> apart a k (addr x) 8 -> apart a k (B h) 8 -> agree_on M M3 a k).
            { intros a k Ha Hak H1 H2 H3 i Hi. apply HMw; rewrite u64_of_Z by lia; clear - H1 H2 H3 Hi; unfold apart in *; lia. }
            assert (C3t : cell8 SEGS M3 (B h) (addr x)) by (rewrite HM3; unfold cell8; cellpeel).
            assert (C3x : cell8 SEGS M3 (addr x) nt) by (rewrite HM3; unfold cell8; cellpeel).
            assert (C3w : cell8 SEGS M3 (addr w) (hdaddr S')) by (rewrite HM3; unfold cell8; cellpeel).

            assert (HMe : forall e, In e ents -> agree_on M M3 (addr e + 8) 24).
            { intros e He. destruct (ent_facts _ _ e U1 He) as (He0 & He1 & _).
              apply HMa; [lia | lia | | |].
              - destruct (Z.eq_dec (addr e) (addr w)) as [Ee|Ne]; [unfold apart; lia | eapply apart_sub; [exact (nodes_apart _ _ e w U1 He HwinE Ne) | lia | lia | lia | lia]].
              - destruct (Z.eq_dec (addr e) (addr x)) as [Ee|Ne]; [unfold apart; lia | eapply apart_sub; [exact (nodes_apart _ _ e x U1 He Hxin Ne) | lia | lia | lia | lia]].
              - destruct (Z.eq_dec (addr e) (B h)) as [Ee|Ne]; [unfold apart; lia | eapply apart_sub; [exact (apart_sym _ _ _ _ (Hte e He Ne)) | lia | lia | lia | lia]]. }
            destruct (HCH' M3 C3t C3x C3w) as [Cp1' CH'].
            { intros a Ha H1 H2 H3.
              assert (Hain : In a ents) by (eapply Permutation_in; [exact PERM | apply in_app_iff in Ha; apply in_app_iff; destruct Ha as [Ha|Ha]; [left; exact Ha | right; right; exact Ha]]).
              destruct (ent_facts _ _ a U1 Hain) as (Ha0 & Ha1 & _).
              apply HMa; [lia | lia | eapply apart_sub; [exact (nodes_apart _ _ a w U1 Hain HwinE H1) | lia | lia | lia | lia]
                                    | eapply apart_sub; [exact (nodes_apart _ _ a x U1 Hain Hxin H2) | lia | lia | lia | lia]
                                    | eapply apart_sub; [exact (apart_sym _ _ _ _ (Hte a Hain H3)) | lia | lia | lia | lia]]. }
            { intros Hne.
              destruct x as [xq [xk xv]]. destruct (u_node U1 xq xk xv Hxin) as (_ & _ & _ & _ & _ & _ & _ & _ & Hxobj & _).
              destruct w as [wq [wk wv]]. destruct (u_node U1 wq wk wv HwinE) as (_ & _ & _ & _ & _ & _ & _ & _ & Hwobj & _).
              unfold HRehashModel.addr in *. cbn [fst] in *.
              apply HMa; [lia | lia | eapply apart_sub; [exact (apart_sym _ _ _ _ Hwobj) | lia | lia | lia | lia]
                                    | eapply apart_sub; [exact (apart_sym _ _ _ _ Hxobj) | lia | lia | lia | lia]
                                    | eapply apart_sub; [exact (apart_sym _ _ _ _ (Htobj Hne)) | lia | lia | lia | lia]]. }
            apply (POST M3 R' P' B pc Hpc'); [| intros a Hn; apply HMw; intros Ha; apply Hn | exact HMg |].
            - constructor; try assumption.
              + rewrite HlP'. exact Q10.
              + rewrite HlP'. exact Q11.
              + eapply Permutation_trans; [exact PERM' | exact PERM].
              + intros e He. destruct (ent_facts _ _ e U1 He) as (He0 & He1 & _).
                eapply cellw_agree; [exact (HASH e He) | eapply agree_on_sub; [exact (HMe e He) | lia | lia] | lia | cbn; lia].
              + intros e He. eapply agree_on_trans; [exact (TAIL e He) | exact (HMe e He)].
              + intros i Hi. eapply cellw_agree; [exact (BK i Hi) | | lia | cbn; lia].
                apply HMa; [lia | lia | eapply apart_sub; [exact Hpw | lia | lia | lia | lia] | eapply apart_sub; [exact Hpx | lia | lia | lia | lia] | eapply apart_sub; [exact Hpt | lia | lia | lia | lia]].
              + intros i Hi. apply HMg. apply DEFp. exact Hi.
              + intros i Hi. apply HMg. apply DEFh. exact Hi.
              + intros e He i Hi. apply HMg. apply (DEFn e He). exact Hi.
            - right. right. exists w. split; [exact HwinE | lia].
            - right. right. exists x. split; [exact Hxin | lia].
            - apply HtW. lia.
            - eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
              intros a Ho. pose proof (u64_range a). apply HMw; intros Ha.
              * destruct (ai_live_block MI A M model (addr w) 32 AI (LIVE w HwinE)) as (_ & _ & _ & _ & Hown). exact (proj1 (Hown (bv_unsigned a) ltac:(lia)) Ho).
              * destruct (ai_live_block MI A M model (addr x) 32 AI (LIVE x Hxin)) as (_ & _ & _ & _ & Hown). exact (proj1 (Hown (bv_unsigned a) ltac:(lia)) Ho).
              * exact (Htown (bv_unsigned a) Ha Ho). }
          unfold cell8 in Ct.
          destruct (Z.lt_ge_cases (hkey x) n) as [Hlt | Hge].
          * assert (Hxh : hkey x = h) by (rewrite <- Hh; symmetry; apply Z.mod_small; lia).
            assert (Hrm : mul_div M_REMU (Z_to_bv 64 (hkey x)) (Z_to_bv 64 n) = Z_to_bv 64 h) by (rewrite w_remu by lia; f_equal; exact Hh).
            assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (hkey x))) = Z_to_bv 64 (p + 8 * h)) by (rewrite w_mul, w_add by lia; f_equal; lia).
            destruct S' as [|x' S''].
            -- xruns HR HK 100%nat STOPSD (SCR [true; false; true; true] [EVar 40; EVar 42; EVar 41; EVar 42; EVar 43; EVar 42] []) 50%N; [scqs Hrm Hba Hhx|].
               finq Hrm Hba FIN HR' DB. left. split; reflexivity.
            -- destruct (ent_facts _ _ x' U1 ltac:(eapply Permutation_in; [exact PERM | apply in_app_iff; right; right; left; reflexivity])) as (Hx'0 & Hx'1 & _).
               destruct x' as [xa' xv']. unfold HRehashModel.addr in Hx'0, Hx'1. cbn [hdaddr fst] in *.
               xruns HR HK 100%nat STOPSD (SCR [true; false; true; false] [EVar 40; EVar 42; EVar 41; EVar 42; EVar 43; EVar 42] []) 50%N; [scqs Hrm Hba Hhx|].
               finq Hrm Hba FIN HR' DB. right. split; [reflexivity | discriminate].
          * assert (Hrm : mul_div M_REMU (Z_to_bv 64 (hkey x)) (Z_to_bv 64 n) = Z_to_bv 64 h) by (rewrite w_remu by lia; f_equal; exact Hh).
            assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 h)) = Z_to_bv 64 (p + 8 * h)) by (rewrite w_mul, w_add by lia; reflexivity).
            destruct S' as [|x' S''].
            -- xruns HR HK 100%nat STOPSD (SCR [false; false; true; true] [EVar 40; EVar 42; EVar 41; EVar 42; EVar 43; EVar 42] []) 50%N; [scqs Hrm Hba Hhx|].
               finq Hrm Hba FIN HR' DB. left. split; reflexivity.
            -- destruct (ent_facts _ _ x' U1 ltac:(eapply Permutation_in; [exact PERM | apply in_app_iff; right; right; left; reflexivity])) as (Hx'0 & Hx'1 & _).
               destruct x' as [xa' xv']. unfold HRehashModel.addr in Hx'0, Hx'1. cbn [hdaddr fst] in *.
               xruns HR HK 100%nat STOPSD (SCR [false; false; true; false] [EVar 40; EVar 42; EVar 41; EVar 42; EVar 43; EVar 42] []) 50%N; [scqs Hrm Hba Hhx|].
               finq Hrm Hba FIN HR' DB. right. split; [reflexivity | discriminate].
    Qed.

    Lemma phaseD : forall A1 M1 A2 M3 model2 R3 p,
      rst (FC p) (opsB p) p A2 M3 model2 R3 -> getr R3 27%bv = Z_to_bv 64 p ->
      umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      agree_on M1 M3 (obj + 16) 24 ->
      (forall q k v, In (q, (k, v)) ents -> agree_on M1 M3 q 32 /\ In (q, 32) (live MI A2)) ->
      (forall i, 0 <= i < n -> cell8 SEGS M3 (p + 8 * i) 0) ->
      (ents = [] -> forall R4, dbase R4 -> srealizes SEGS (cfg fxr R4 NT_AFTER M3 model2) K) ->
      (forall e S M4 R4 (pc : Z), ents = e :: S -> (pc = NT_AFTER /\ S = [] \/ pc = NT_LOOP /\ S <> []) ->
          lst p M1 [e] S (fun i => if i =? hh e then snt else 0) A2 M4 R4 ->
          (forall a : word, ~ Wloop p (bv_unsigned a) -> M4 a = M3 a) -> (forall a : word, M3 a <> None -> M4 a <> None) ->
          ainv MI A2 M4 model2 ->
          srealizes SEGS (cfg fxr R4 pc M4 model2) K) ->
      srealizes SEGS (cfg fxr R3 NT_MSR M3 model2) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C fxr Ar Mr modelr pn AIr Ur F2r CONTD.
      ctx. intros A1 M1 A2 M3 model2 R3 p D G27 U1 AGh Hnodes Hz PEXIT PLOOP.
      destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof (u_obj_hi Ur) as Hh1.
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq Ur) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds DB S10 S6 DEF EFF LAP Hp0 Hpc Hpal Hpl Hpnew HFoff HDEF]. pose proof DB as DBx. destruct DBx as (B & HQ23 & HQ25). pose proof B as Bx. destruct Bx as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
      pose proof (u_obj_lo U1) as Hobjlo. pose proof (u_obj_hi U1) as Hobjhi.

      assert (Cp1 : cell8 SEGS M3 (obj + 16) (hdaddr ents)).
      { eapply cellw_agree; [exact (h_p1 (u_hdr U1)) | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia]. }
      unfold cell8 in Cp1. pose proof (proj1 Cp1) as Hhdr.
      assert (Hblc : bc <> 0 -> bl + 8 * bc <= alloc_ceiling).
      { intros Hnz. destruct (u_blive Ur) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' Ar Mr modelr bl (8 * bc) AIr Hin) as (_ & _ & Hc & _). exact Hc. }
      pose proof (f2_via A2 M3 (FC p) EFF ltac:(intros a [[Ha|[Ha|[Hnz Ha]]]|Ha]; unfold FA in *; [lia | lia | pose proof (Hblc Hnz); lia | lia])) as F2. unfold cell8 in F2.
      destruct ents as [|e S] eqn:HE.
      -
        rewrite ?HE in Cp1. cbn [hdaddr] in Cp1. clear Hncase.
        pose (E := Eseed R3 [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 n; Z_to_bv 64 (8 * n); Z_to_bv 64 0]).
        assert (HR : regs_ok E (srs sr_id HTHNtD_0) R3).
        { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
        assert (HK : know_ok SEGS E M3 []) by constructor.
        xruns HR HK 100%nat STOPSD (SCR [true] [EVar 37] []) 50%N; [split_scs; try sc_auto1|].
        (apply (PEXIT HE) || apply (PEXIT eq_refl)). dbase_from HR' DB.
      -
        destruct e as [q [k v]]. rewrite ?HE in U1, Hnodes, Cp1.
        destruct (u_node U1 q k v (or_introl eq_refl)) as (_ & Hq0 & Hq1 & Hqal & Chash & _ & Hk & _ & Hqobj & _).
        destruct (Hnodes q k v (or_introl eq_refl)) as [AGq Hlv].
        assert (Cqh : cell8 SEGS M3 (q + 8) k) by (eapply cellw_agree; [exact Chash | eapply agree_on_sub; [exact AGq | lia | cbn; lia] | lia | cbn; lia]).
        assert (Cqn : cell8 SEGS M3 q (hdaddr S)).
        { pose proof (u_chain U1) as CH. cbn in CH. eapply cellw_agree; [exact (proj1 CH) | eapply agree_on_sub; [exact AGq | lia | cbn; lia] | lia | cbn; lia]. }
        unfold cell8 in Cqh, Cqn. pose proof (proj1 Cqn) as HSr. cbn [hdaddr] in Cp1.
        assert (Hbc1 : bc <> 0) by (pose proof (u_load U1) as HL; unfold Zlength in HL; cbn [length] in HL; lia).
        destruct Hncase as [[? ?] | [Hn3 Hland]]; [lia|].
        assert (Hn0 : 0 < n) by lia.
        assert (Hlandr : 0 <= Z.land n (n - 1) < 2 ^ 64).
        { pose proof (Z.add_lor_land n (n - 1)). pose proof (Z.land_nonneg n (n - 1)). pose proof (Z.lor_nonneg n (n - 1)). lia. }
        set (h0 := hmod k n).
        assert (Hh0 : 0 <= h0 < n) by (unfold h0, hmod; apply Z.mod_pos_bound; lia).
        assert (Hh : k mod n = h0) by reflexivity.
        assert (Hpq : apart p (8 * n) q 32).
        { apply (ai_live_disjoint MI A2 M3 model2 p (8 * n) q 32 AI Hpl Hlv). intros <-. apply Hpnew.
          apply (in_map fst _ (p, 32)). exact (proj1 (u_node Ur p k v ltac:(first [rewrite HE; left; reflexivity | left; reflexivity]))). }
        assert (DEFp : defined M3 p (8 * n)) by (intros i Hi; destruct (live_facts' A2 M3 model2 p (8 * n) AI Hpl) as (_ & _ & _ & Hall); exact (proj2 (Hall (p + i) ltac:(lia)))).
        pose (E := Eseed R3 [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 n; Z_to_bv 64 (8 * n); Z_to_bv 64 q; Z_to_bv 64 k; Z_to_bv 64 (hdaddr S); Z_to_bv 64 snt]).
        assert (HR : regs_ok E (srs sr_id HTHNtD_0) R3).
        { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
        assert (HK : know_ok SEGS E M3 []) by constructor.
        assert (Hand : alu64 ALU_AND (Z_to_bv 64 n) (alu64 ALU_ADD (Z_to_bv 64 n) (Z_to_bv 64 (-1))) = Z_to_bv 64 (Z.land n (n - 1))).
        { rewrite w_addm by lia. rewrite w_and by lia. reflexivity. }
        assert (FIN : forall R' M4,
                  M4 = wbytes M3 (Z_to_bv 64 (p + 8 * h0)) (word_to_le_bytes 8 (Z_to_bv 64 snt)) ->
                  dbase R' ->
                  getr R' 27%bv = Z_to_bv 64 p -> getr R' 26%bv = Z_to_bv 64 n ->
                  getr R' 10%bv = Z_to_bv 64 q -> getr R' 12%bv = Z_to_bv 64 (hdaddr S) -> getr R' 11%bv = Z_to_bv 64 h0 ->
                  forall pc, (pc = NT_AFTER /\ S = [] \/ pc = NT_LOOP /\ S <> []) ->
                  srealizes SEGS (cfg fxr R' pc M4 model2) K).
        { intros R' M4 HM4 DB' Q27 Q26 Q10 Q12 Q11 pc Hpc'.
          assert (HMw : forall a : word, ~ (p + 8 * h0 <= bv_unsigned a < p + 8 * h0 + 8) -> M4 a = M3 a).
          { intros a Ha. pose proof (u64_range a). rewrite HM4, wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
          assert (HMg : forall a : word, M3 a <> None -> M4 a <> None) by (intros a Ha; rewrite HM4; apply wbytes_grows; exact Ha).
          assert (HMa : forall a kk, 0 <= a -> a + kk <= 2 ^ 47 -> apart a kk (p + 8 * h0) 8 -> agree_on M3 M4 a kk).
          { intros a kk Ha Hak H1 i Hi. apply HMw; rewrite u64_of_Z by lia; clear - H1 Hi; unfold apart in *; lia. }

          assert (HN : forall q' k' v', In (q', (k', v')) ((q, (k, v)) :: S) -> agree_on M1 M4 q' 32 /\ In (q', 32) (live MI A2) /\ 0 < q' /\ q' + 32 <= 2 ^ 47).
          { intros q' k' v' Hin. destruct (Hnodes q' k' v' Hin) as [AG' Hlv']. destruct (u_node U1 q' k' v' Hin) as (_ & Hq'0 & Hq'1 & _).
            assert (Hne : p <> q') by (intros <-; apply Hpnew; apply (in_map fst _ (p, 32)); exact (proj1 (u_node Ur p k' v' ltac:(first [rewrite HE; exact Hin | exact Hin])))).
            pose proof (ai_live_disjoint MI A2 M3 model2 p (8 * n) q' 32 AI Hpl Hlv' Hne) as Hap.
            split; [| split; [exact Hlv' | lia]].
            eapply agree_on_trans; [exact AG' | apply HMa; [lia | lia | clear - Hap Hh0; unfold apart in *; lia]]. }
          (apply (PLOOP (q, (k, v)) S M4 R' pc HE Hpc') || apply (PLOOP (q, (k, v)) S M4 R' pc eq_refl Hpc')); [| intros a Hn'; apply HMw; intros Ha; apply Hn'; left; lia | exact HMg |].
          - constructor.
            + exact DB'.
            + exact Q27. + exact Q26.
            + unfold HRehashModel.addr. cbn [last fst]. exact Q10.
            + exact Q12.
            + cbn [last]. unfold HRehashModel.hh, HRehashModel.hkey. cbn [fst snd]. exact Q11.
            + rewrite HE. cbn [app]. apply Permutation_refl.
            + apply binv_start; lia.
            + discriminate.
            + cbn [app hdaddr]. eapply cellw_agree; [exact Cp1 | apply HMa; [lia | lia | unfold apart; lia] | lia | cbn; lia].
            + cbn [app]. eapply (chain_agree SEGS (Z * Z * Z)%type M1 M4); [exact (u_chain U1) |].
              intros q' k' v' Hin. destruct (HN q' k' v' Hin) as (AG4 & _ & Hr0 & Hr1). split; [eapply agree_on_sub; [exact AG4 | lia | lia] | lia].
            + intros e He. rewrite HE in He. destruct e as [q' [k' v']]. destruct (HN q' k' v' He) as (AG4 & _ & Hr0 & Hr1).
              destruct (u_node U1 q' k' v' He) as (_ & _ & _ & _ & Ch' & _). unfold HRehashModel.addr, HRehashModel.hkey. cbn [fst snd].
              eapply cellw_agree; [exact Ch' | eapply agree_on_sub; [exact AG4 | lia | cbn; lia] | lia | cbn; lia].
            + intros e He. rewrite HE in He. destruct e as [q' [k' v']]. destruct (HN q' k' v' He) as (AG4 & _ & Hr0 & Hr1). unfold HRehashModel.addr. cbn [fst].
              eapply agree_on_sub; [exact AG4 | lia | lia].
            + intros i Hi. unfold HRehashModel.hh, HRehashModel.hkey. cbn [fst snd]. fold h0. destruct (Z.eqb_spec i h0) as [->|Hne].
              * rewrite HM4. unfold cell8. cellpeel.
              * eapply cellw_agree; [exact (Hz i Hi) | apply HMa; [lia | lia | unfold apart; lia] | lia | cbn; lia].
            + intros i Hi. apply HMg. apply DEFp. exact Hi.
            + intros i Hi. apply HMg. apply HDEF. exact Hi.
            + intros e He i Hi. rewrite HE in He. destruct e as [q' [k' v']]. destruct (HN q' k' v' He) as (_ & Hlv' & _). unfold HRehashModel.addr. cbn [fst].
              apply HMg. destruct (live_facts' A2 M3 model2 q' 32 AI Hlv') as (_ & _ & _ & Hall). exact (proj2 (Hall (q' + i) ltac:(lia))).
            + intros e He. rewrite HE in He. destruct e as [q' [k' v']]. exact (proj1 (proj2 (HN q' k' v' He))).
            + exact Hpl.
          - eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
            intros a Ho. pose proof (u64_range a). apply HMw. intros Ha.
            destruct (live_facts' A2 M3 model2 p (8 * n) AI Hpl) as (_ & _ & _ & Hall). exact (proj1 (Hall (bv_unsigned a) ltac:(lia)) Ho). }
        Ltac scD Hrm Hba Hr Hand := split_scs; first [scq Hrm Hba Hr | cbn [sc_denot]; evs; rewrite Hand; rewrite br_ne by lia; bool_lia].
        destruct (Z.lt_ge_cases k n) as [Hlt | Hge].
        + assert (Hxh : k = h0) by (rewrite <- Hh; symmetry; apply Z.mod_small; lia).
          assert (Hrm : mul_div M_REMU (Z_to_bv 64 k) (Z_to_bv 64 n) = Z_to_bv 64 h0) by (rewrite w_remu by lia; f_equal; exact Hh).
          assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 k)) = Z_to_bv 64 (p + 8 * h0)) by (rewrite w_mul, w_add by lia; f_equal; lia).
          destruct S as [|x' S''].
          * xruns HR HK 100%nat STOPSD (SCR [false; true; true; false] [EVar 37; EVar 38; EVar 40; EVar 39] []) 50%N; [scD Hrm Hba Hh0 Hand|].
            finq Hrm Hba FIN HR' DB. left. split; reflexivity.
          * destruct x' as [xa' xv']. destruct (u_node U1 xa' (fst xv') (snd xv') ltac:(right; left; destruct xv'; reflexivity)) as (_ & Hx'0 & Hx'1 & _). cbn [hdaddr fst] in *.
            xruns HR HK 100%nat STOPSD (SCR [false; true; true; true] [EVar 37; EVar 38; EVar 40; EVar 39] []) 50%N; [scD Hrm Hba Hh0 Hand|].
            finq Hrm Hba FIN HR' DB. right. split; [reflexivity | discriminate].
        + assert (Hrm : mul_div M_REMU (Z_to_bv 64 k) (Z_to_bv 64 n) = Z_to_bv 64 h0) by (rewrite w_remu by lia; f_equal; exact Hh).
          assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 h0)) = Z_to_bv 64 (p + 8 * h0)) by (rewrite w_mul, w_add by lia; reflexivity).
          destruct S as [|x' S''].
          * xruns HR HK 100%nat STOPSD (SCR [false; true; false; false] [EVar 37; EVar 38; EVar 40; EVar 39] []) 50%N; [scD Hrm Hba Hh0 Hand|].
            finq Hrm Hba FIN HR' DB. left. split; reflexivity.
          * destruct x' as [xa' xv']. destruct (u_node U1 xa' (fst xv') (snd xv') ltac:(right; left; destruct xv'; reflexivity)) as (_ & Hx'0 & Hx'1 & _). cbn [hdaddr fst] in *.
            xruns HR HK 100%nat STOPSD (SCR [false; true; false; true] [EVar 37; EVar 38; EVar 40; EVar 39] []) 50%N; [scD Hrm Hba Hh0 Hand|].
            finq Hrm Hba FIN HR' DB. right. split; [reflexivity | discriminate].
    Qed.

    Lemma relink : forall p A1 M1 A M3 model S P B M R (pc : Z),
      (pc = NT_AFTER /\ S = [] \/ pc = NT_LOOP /\ S <> []) ->
      ainv MI A M model -> mstd model -> umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      lst p M1 P S B A M R ->
      0 < p -> p + 8 * n <= alloc_ceiling -> ~ In p (map fst (live MI Ar)) ->
      (forall a : word, ~ Wloop p (bv_unsigned a) -> M a = M3 a) -> (forall a : word, M3 a <> None -> M a <> None) ->
      (forall M' R' P' B',
          lst p M1 P' [] B' A M' R' ->
          (forall a : word, ~ Wloop p (bv_unsigned a) -> M' a = M3 a) -> (forall a : word, M3 a <> None -> M' a <> None) ->
          ainv MI A M' model ->
          srealizes SEGS (cfg fxr R' NT_AFTER M' model) K) ->
      srealizes SEGS (cfg fxr R pc M model) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C fxr Ar Mr pn Ur.
      intros p A1 M1 A M3 model S. induction S as [|x S' IH]; intros P B M R pc Hpc AI MS U1 LS Hp0 Hpc8 Hpnew HM HG POST.
      - destruct Hpc as [[-> _] | [_ Hne]]; [| exfalso; exact (Hne eq_refl)].
        exact (POST M R P B LS HM HG AI).
      - destruct Hpc as [[_ Habs] | [-> _]]; [discriminate Habs|].
        eapply (loop_step p A1 M1 P (x :: S') B A M model R x S' eq_refl AI MS U1 LS Hp0 Hpc8 Hpnew).
        intros M' R' P' B' pc' Hpc' LS' HM' HG' AI'.
        apply (IH P' B' M' R' pc' Hpc' AI' MS U1 LS' Hp0 Hpc8 Hpnew); [| | exact POST].
        + intros a Ha. rewrite (HM' a Ha). exact (HM a Ha).
        + intros a Ha. apply HG'. apply HG. exact Ha.
    Qed.

    Lemma phaseE : forall A1 M1 A2 M3 model2 R3 p M' R',
      rst (FC p) (opsB p) p A2 M3 model2 R3 ->
      umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      cell8 SEGS M3 obj p -> cell8 SEGS M3 (obj + 8) n -> agree_on M1 M3 (obj + 16) 24 ->
      (forall q k v, In (q, (k, v)) ents -> agree_on M1 M3 q 32 /\ In (q, 32) (live MI A2)) ->
      (forall i, 0 <= i < n -> cell8 SEGS M3 (p + 8 * i) 0) ->
      (forall a : word, ~ Wloop p (bv_unsigned a) -> M' a = M3 a) -> (forall a : word, M3 a <> None -> M' a <> None) ->
      ainv MI A2 M' model2 -> dbase R' ->
      ((ents = [] /\ M' = M3) \/ (exists P' B', lst p M1 P' [] B' A2 M' R')) ->
      srealizes SEGS (cfg fxr R' NT_AFTER M' model2) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C fxr Ar Mr pn Ur CONTD.
      ctx. intros A1 M1 A2 M3 model2 R3 p M' R' D U1 Cbl Cbc AGh Hnodes Hz HM HG AI' B' HFIN.
      destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof (u_obj_hi Ur) as Hh1.
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase). clear Hncase.
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq Ur) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds _ _ _ DEF EFF LAP Hp0 Hpc Hpal Hpl Hpnew HFoff HDEF].
      pose proof B' as DBx. destruct DBx as (B & HQ23 & HQ25). pose proof B as Bx. destruct Bx as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
      pose proof (u_obj_lo U1) as Hobjlo. pose proof (u_obj_hi U1) as Hobjhi.
      assert (Hn0 : 0 < n) by lia.

      assert (HMo : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> (forall x, a <= x < a + k -> ~ Wloop p x) -> agree_on M3 M' a k).
      { intros a k Ha Hak Hno i Hi. apply HM. rewrite u64_of_Z by lia. apply Hno. lia. }
      assert (Hhdr_no : forall x, (obj <= x < obj + 16 \/ obj + 24 <= x < obj + 40) -> ~ Wloop p x).
      { intros x Hx [Hw|[Hw|(e & He & Hw)]]; [lia | lia |].
        destruct e as [q [k v]]. destruct (u_node U1 q k v He) as (_ & _ & _ & _ & _ & _ & _ & _ & Hap & _). unfold apart in Hap. cbn in Hw. lia. }
      assert (Hstk_no : forall x, sp - NTS <= x < sp -> ~ Wloop p x).
      { intros x Hx [Hw|[Hw|(e & He & Hw)]]; [lia | lia |].
        destruct e as [q [k v]]. destruct (Hnodes q k v He) as [_ Hlv]. destruct (live_facts' A2 M3 model2 q 32 AI Hlv) as (_ & _ & Hqc & _). cbn in Hw. lia. }

      assert (HU : exists ents', Permutation ents' ents /\ umapx MI 32 (nval32 SEGS) A2 M' obj p n ents').
      { destruct HFIN as [[HE HM'] | (P' & Bk & LS)].
        - exists (@nil lent). subst M'. split; [rewrite HE; apply Permutation_refl|].
          pose proof (u_hdr U1) as HD. rewrite HE in HD. destruct HD as [_ _ Cp1 Csz Cmlf _].
          constructor; try (intros; exfalso; assumption).
          + constructor; [exact Cbl | exact Cbc | | | | exact HDEF].
            * eapply cellw_agree; [exact Cp1 | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
            * eapply cellw_agree; [exact Csz | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
            * eapply cellw_agree; [exact Cmlf | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
          + exact (u_obj_al U1). + exact Hobjlo. + exact Hobjhi. + exact HnB.
          + unfold Zlength. cbn. lia.
          + right. split; [lia | exact Hpl].
          + exact Hpal. + intros _; exact Hp0. + lia. + intros _. unfold apart. lia.
          + intros i Hi. exists 0. split; [exact (Hz i Hi) | left; reflexivity].
          + constructor.
          + exact I.
        - exists P'. destruct LS as [_ _ _ _ _ _ PERM BI HP Cp1 CH HASH TAIL BK DEFp DEFh DEFn LIVE PLIVE].
          rewrite app_nil_r in PERM, Cp1, CH.
          assert (Hnoty : forall P1 y z P2, P' = P1 ++ y :: z :: P2 -> addr y <> snt).
          { intros P1 y z P2 HP' Heq. assert (Hin : In y ents) by (eapply Permutation_in; [exact PERM | rewrite HP'; apply in_app_iff; right; left; reflexivity]).
            destruct y as [q [k v]]. destruct (u_node U1 q k v Hin) as (_ & Hq0 & _ & _ & _ & _ & _ & _ & Hap & _). unfold apart in Hap. cbn in Heq. lia. }
          split; [exact PERM|].
          pose proof (u_hdr U1) as HD. destruct HD as [_ _ _ Csz Cmlf _].
          constructor.
          + constructor; [| | exact Cp1 | | | exact DEFh].
            * eapply cellw_agree; [exact Cbl | apply HMo; [lia | lia | intros x Hx; apply Hhdr_no; lia] | lia | cbn; lia].
            * eapply cellw_agree; [exact Cbc | apply HMo; [lia | lia | intros x Hx; apply Hhdr_no; lia] | lia | cbn; lia].
            * rewrite (Permutation_length PERM : length P' = length ents) || (unfold Zlength; rewrite (Permutation_length PERM)).
              eapply cellw_agree; [exact Csz | eapply agree_on_trans; [eapply agree_on_sub; [exact AGh | lia | cbn; lia] | apply HMo; [lia | cbn; lia | intros x Hx; apply Hhdr_no; cbn in Hx; lia]] | lia | cbn; lia].
            * eapply cellw_agree; [exact Cmlf | eapply agree_on_trans; [eapply agree_on_sub; [exact AGh | lia | cbn; lia] | apply HMo; [lia | cbn; lia | intros x Hx; apply Hhdr_no; cbn in Hx; lia]] | lia | cbn; lia].
          + exact (u_obj_al U1). + exact Hobjlo. + exact Hobjhi. + exact HnB.
          + unfold Zlength. rewrite (Permutation_length PERM). pose proof (u_load U1) as HL. unfold Zlength in HL. lia.
          + right. split; [lia | exact PLIVE].
          + exact Hpal. + intros _; exact Hp0. + lia. + intros _. unfold apart. lia.
          + intros i Hi. exists (Bk i). split; [exact (BK i Hi)|].
            destruct (binv_weak (Z * Z * Z)%type n snt P' Bk i BI Hi Hnoty) as [Hb | [Hb | [Hb (x & P'' & HP' & Hx)]]]; [left; exact Hb | right; left; exact Hb | right; right].
            split; [exact Hb|]. split; [rewrite HP'; discriminate|]. rewrite HP'. destruct x as [q [k v]]. cbn. symmetry. exact Hx.
          + apply (proj2 (base.NoDup_ListNoDup _)). exact (perm_nodup _ _ _ U1 PERM).
          + exact CH.
          + intros q k v Hin. assert (Hine : In (q, (k, v)) ents) by (eapply Permutation_in; [exact PERM | exact Hin]).
            destruct (u_node U1 q k v Hine) as (_ & Hq0 & Hq1 & Hqal & _ & C4 & Hk & Hnv & Hap & _).
            pose proof (TAIL _ Hine) as TL. cbn in TL.
            split; [exact (LIVE _ Hine)|]. split; [exact Hq0|]. split; [exact Hq1|]. split; [exact Hqal|].
            split; [exact (HASH _ Hine)|].
            split; [eapply cellw_agree; [exact C4 | eapply agree_on_sub; [exact TL | lia | cbn; lia] | lia | cbn; lia]|].
            split; [exact Hk|].
            split; [eapply nval32_agree; [exact Hnv | eapply agree_on_sub; [exact TL | lia | lia] | lia | lia]|].
            split; [exact Hap|].
            intros _. apply apart_sym. apply (p_node_apart p A2 M' model2 (q, (k, v)) AI' PLIVE Hpnew (LIVE _ Hine) Hine).
          + intros q q' Hq Hq' Hne. apply (u_napart U1); [| | exact Hne].
            * apply in_map_iff in Hq. destruct Hq as (e & <- & He). apply in_map. eapply Permutation_in; [exact PERM | exact He].
            * apply in_map_iff in Hq'. destruct Hq' as (e & <- & He). apply in_map. eapply Permutation_in; [exact PERM | exact He]. }
      destruct HU as (ents' & PERM' & U').

      assert (EFF' : eff MI Ar A2 Mr M' W (fun a => FC p a \/ Wloop p a)).
      { eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned'; [exact AI' | unfold W_of, Wnt in Ha; cbn in Ha; lia]].
        eapply eff_store; [| exact HG]. intros x HF _. apply HM. exact HF. }
      assert (FOFF' : forall a, FC p a \/ Wloop p a -> ~ in_ranges (ly_img L) a).
      { intros a [Ha | [Ha | [Ha | (e & He & Ha)]]] Himg; pose proof (HLimg_lo _ Himg).
        - exact (HFoff a Ha Himg). - exact (live_offimg' A2 M3 model2 p (8 * n) a AI Hpl Ha Himg). - lia.
        - destruct e as [q [k v]]. destruct (Hnodes q k v He) as [_ Hlv]. cbn in Ha.
          exact (live_offimg' A2 M3 model2 q 32 a AI Hlv ltac:(lia) Himg). }
      apply (CONTD A2 R' M' model2 p ents' AI' MS Hfs Hfds B').
      - exact U'.
      - exact PERM'.
      - exact LAP.
      - eapply eff_weaken; [exact EFF'|].
        intros a [[[Ha | [Ha | Ha]] | Ha] | [Ha | [Ha | (e & He & Ha)]]].
        + right. right. left. split; [lia | exact Ha].
        + left. left. lia.
        + left. right. left. exact Ha.
        + left. left. lia.
        + right. right. left. split; [lia | exact Ha].
        + left. left. lia.
        + left. right. right. exists (addr e). split; [apply in_map; exact He | lia].
      - eapply defined_agree; [exact DEF | apply HMo; [lia | lia | intros x Hx; apply Hstk_no; lia]].
    Qed.

    Theorem rehash_inl : srealizes SEGS (cfg fxr Rr NT_NEWE Mr modelr) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C fxr Ar Mr modelr Rr pn AIr MSr Hfsr Hfdsr SXr RCr OSXr Br Q26r Q22r Q10r Q1r Ur DEFWr F2r ROOMr CONTD.
      apply phaseA. intros A1 M1 model1 R1 p AI1 MS1 Hfs1 Hfds1 SX1 B1 G10 G26 G22 DEF1 Hp0 Hpc Hpal LADD EFF1 U1.
      assert (Hpl : In (p, 8 * n) (live MI A1)) by (rewrite (proj1 LADD); left; reflexivity).
      assert (D1 : rst (FA p) [LAdd p (8 * n)] p A1 M1 model1 R1).
      { constructor; try assumption.
        - exists (live MI A1). split; [exact LADD | reflexivity].
        - exact (proj2 LADD).
        - intros a Ha. exact (live_offimg' A1 M1 model1 p (8 * n) a AI1 Hpl Ha).
        - exact (h_def (u_hdr U1)). }
      apply (phaseB A1 M1 model1 R1 p D1 G10 U1). intros A2 M2 model2 R2 D2 G27 Cbl AG2 Hn2.
      apply (phaseC A1 M1 A2 M2 model2 R2 p D2 G27 U1 Cbl AG2 Hn2). intros M3 R3 D3 G27' Cbl3 Cbc3 AG3 Hn3 Hz3.
      apply (phaseD A1 M1 A2 M3 model2 R3 p D3 G27' U1 AG3 Hn3 Hz3).
      - intros HE R4 B4.
        apply (phaseE A1 M1 A2 M3 model2 R3 p M3 R4 D3 U1 Cbl3 Cbc3 AG3 Hn3 Hz3); [intros a _; reflexivity | intros a Ha; exact Ha | exact (r_ai _ _ _ _ _ _ _ D3) | exact B4 |].
        left. split; [exact HE | reflexivity].
      - intros e S M4 R4 pc HE Hpc' LS HM4 HG4 AI4.
        apply (relink p A1 M1 A2 M3 model2 S [e] _ M4 R4 pc Hpc' AI4 (r_ms _ _ _ _ _ _ _ D3) U1 LS (r_p0 _ _ _ _ _ _ _ D3) (r_pc _ _ _ _ _ _ _ D3) (r_pnew _ _ _ _ _ _ _ D3) HM4 HG4).
        intros M' R' P' B' LS' HM' HG' AI'.
        apply (phaseE A1 M1 A2 M3 model2 R3 p M' R' D3 U1 Cbl3 Cbc3 AG3 Hn3 Hz3 HM' HG' AI' (l_regs _ _ _ _ _ _ _ _ LS')).
        right. exists P', B'. exact LS'.
    Qed.

  End Reh.
End NtD.

Arguments rehash_inl {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C fxr Ar Mr modelr Rr pn.
Arguments dbase {L R0 sp parser key val v2} pn R.
