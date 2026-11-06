(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk SimInv ShapeAlg ShapeLaws Nodes MmapSim FileSim AgentLib Frame MemSplit Hoare RefMemcpyLib SumMemcpyBase SumMemcpy SRealizes SNodes AllocCeil RunRandom LibIface LibBudget LibEff U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import RunsLib U1CxxTable StaticsGen U1Statics S1SpecConsts S1Spec U1Cells U1AddrFacts U1RBase U1RKn DrvMallocTU1 U1ReadW U1RChunkN U1RwWindow.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac reg_in :=
  first [ solve [ cbn [In]; repeat first [ left; reflexivity | right ] ]
        | solve [ cbn [In]; let HH := fresh "HH" in intros HH;
                  repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH ]
        | cbv; tauto ].

Ltac reg_sub Hr :=
  first [ solve [ cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [ reg_in | ]); destruct Hr ]
        | cbv in Hr |- *; intuition (subst; tauto) ].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition cap_of (j : nat) : Z := 65536 * 2 ^ (Z.of_nat j).

Lemma cap_of_S : forall j, cap_of (S j) = 2 * cap_of j.
Proof. intros j. unfold cap_of. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.
Lemma cap_of_0 : cap_of 0 = 65536. Proof. reflexivity. Qed.
Lemma cap_of_10 : cap_of 10 = 2 ^ 26. Proof. reflexivity. Qed.
Lemma cap_of_range : forall j, (j <= 10)%nat -> 65536 <= cap_of j <= 2 ^ 26.
Proof.
  intros j Hj. unfold cap_of. split.
  - assert (2 ^ 0 <= 2 ^ Z.of_nat j) by (apply Z.pow_le_mono_r; lia). change (2 ^ 0) with 1 in H. lia.
  - change (2 ^ 26) with (65536 * 2 ^ 10). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma cap_of_lt10 : forall j, (j < 10)%nat -> cap_of j < 2 ^ 26.
Proof.
  intros j Hj. unfold cap_of. change (2 ^ 26) with (65536 * 2 ^ 10). apply Z.mul_lt_mono_pos_l; [lia|]. apply Z.pow_lt_mono_r; lia.
Qed.

Fixpoint rshape (d j : nat) (L : Z) (KEND : TSet) (fs : Fs.Fs) : TSet :=
  if L <? cap_of j then KEND
  else match d with
       | O => t_die msg_refused fs
       | S d' => rshape d' (S j) L KEND fs
       end.

Section FXALL.
Context {fx : FPState}.
Section Loop.
  Context {AC : AllocCeiling} {RRND : RunRandom} {AMB : Amb}.
  Variable MI : MallocIface SEGS L.
  Variable AINV0 : AS MI -> LibIface.mem -> Model -> Prop.
  Variables (TIGHT FRESH44 : AS MI -> Prop).
  Hypothesis DM : drv_mallocT MI AINV0 TIGHT FRESH44.
  Variables (sp0 tid p1 : Z) (path content : list byte) (fs0 : Fs).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
  Hypothesis Hp1 : sp0 <= p1 /\ p1 + Z.of_nat (length path) + 1 < 2 ^ 63.
  Hypothesis HAC : alloc_ceiling = sp0 - 8388608.
  Let L : Z := Z.of_nat (length content).

  #[local] Notation RMEM := (rmem sp0 tid p1 path).
  #[local] Notation RABS := (rabs MI).
  #[local] Notation OOMPRE := (oom_pre MI sp0 tid p1 path fs0).
  #[local] Notation RST := (rst MI sp0 tid p1 path TIGHT content fs0).

  Record rend (p cap : Z) (A : AS MI) (R : bvmap 5 word) (M : word -> option byte) (mo : Model) : Prop := {
    re_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
    re_gp : getr R 3 = Z_to_bv 64 0x10800;
    re_tp : getr R 4 = Z_to_bv 64 0x102418;
    re_s0 : getr R 8 = Z_to_bv 64 2;
    re_s1 : getr R 9 = Z_to_bv 64 p;
    re_s2 : getr R 18 = Z_to_bv 64 p1;
    re_s3 : getr R 19 = Z_to_bv 64 L;
    re_s4 : getr R 20 = Z_to_bv 64 3;
    re_s5 : getr R 21 = Z_to_bv 64 cap;
    re_s6 : getr R 22 = Z_to_bv 64 0xf0249;
    re_mem : RMEM M;
    re_abs : RABS A M mo;
    re_tight : TIGHT A;
    re_live : live MI A = [(p, cap)];
    re_cap : L < cap /\ (exists j, (j <= 10)%nat /\ cap = cap_of j);
    re_content : rdn RSEGS M (Z_to_bv 64 p) (length content) = Some content;
    re_fds : m_fds mo = fds_std;
    re_fs : m_fs mo = fs0
  }.

  Hypothesis Hfile : fs_lookup fs0 path = Some content.
  Variable KEND : TSet.
  Hypothesis HREF : forall A R M mo, OOMPRE A R M mo ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65a84) M (seg_rom RSEGS)) mo) (t_die msg_refused fs0).
  Hypothesis HEND : forall p cap A R M mo, rend p cap A R M mo ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65938) M (seg_rom RSEGS)) mo) KEND.

  Lemma buf_geom : forall A M mo p cap, RABS A M mo -> live MI A = [(p, cap)] -> 65536 <= cap ->
    0x124000 <= p /\ p + cap <= alloc_ceiling /\ p mod 16 = 0.
  Proof.
    intros A M mo p cap RA LV Hc. pose proof (ra_ainv _ _ _ _ RA) as AI.
    assert (Hin : In (p, cap) (live MI A)) by (rewrite LV; left; reflexivity).
    destruct (ai_live_block MI A M mo p cap AI Hin) as (_ & Hal & _ & Hce & _).
    split; [exact (live_above_img MI A M mo p cap AI Hin Hc) | split; [exact Hce | exact Hal]].
  Qed.

  Lemma loop_client : forall A M M' mo mo' p cap len len',
    RMEM M -> RABS A M mo -> In (p, cap) (live MI A) -> 0x124000 <= p -> p + cap <= alloc_ceiling ->
    0 <= len <= len' -> len' <= cap ->
    post_mem content M M' sp0 p len len' ->
    m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = m_halted mo ->
    m_vm_materialized mo' = m_vm_materialized mo ->
    RMEM M' /\ RABS A M' mo'.
  Proof.
    intros A M M' mo mo' p cap len len' RM RA Hin Hp Hpc Hl Hl' PM Hvm Hlz Hh Hmat.
    pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    apply (rstep_client MI sp0 tid p1 path Hsp Hp1 HAC A M M' mo mo' RM RA (proj2 (proj1 PM))); try assumption.
    intros a Hne. pose proof (u64_range a).
    destruct (Classical_Prop.classic (sp0 - 65536 <= bv_unsigned a < sp0 - 128)) as [Hs|Hs]; [right; left; exact Hs|].
    destruct (Classical_Prop.classic (0xf0249 <= bv_unsigned a < 0x100249)) as [Hr|Hr]; [right; right; exact Hr|].
    left. exists p, cap. split; [exact Hin|].
    destruct (Classical_Prop.classic (p + len <= bv_unsigned a < p + len')) as [Hb|Hb]; [lia|]. exfalso. apply Hne.
    apply (proj1 (proj1 PM)). cbn [outside]. unfold in_rng, RS. rewrite !u64_lit by lia. repeat split; lia.
  Qed.

  Lemma stage_end : forall (j : nat) p len A R M mo R' M',
    (j <= 10)%nat -> 0 <= len -> len <= L -> L < cap_of j ->
    getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x102418 -> getr R 8 = Z_to_bv 64 2 ->
    getr R 18 = Z_to_bv 64 p1 -> getr R 20 = Z_to_bv 64 3 -> getr R 21 = Z_to_bv 64 (cap_of j) ->
    getr R 22 = Z_to_bv 64 0xf0249 ->
    RMEM M -> RABS A M (at_off path mo len) -> TIGHT A -> live MI A = [(p, cap_of j)] ->
    rdn RSEGS M (Z_to_bv 64 p) (Z.to_nat len) = Some (pref len content) -> m_fs mo = fs0 ->
    post_regs R R' sp0 p L -> post_mem content M M' sp0 p len L ->
    srealizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x65938) M' (seg_rom RSEGS)) (closed3 mo)) KEND.
  Proof.
    intros j p len A R M mo R' M' Hj Hlen HlenL HLc Q3 Q4 Q8 Q18 Q20 Q21 Q22 QM QA QT QL QC QFS (P2 & P9 & P19 & PK) PM.
    pose proof HAC as Hcv. pose proof (cap_of_range j Hj) as Hcap.
    destruct (buf_geom A M (at_off path mo len) p (cap_of j) QA QL ltac:(lia)) as (Hpimg & Hpce & Hpal).
    pose proof (ra_ainv _ _ _ _ QA) as AI.
    assert (Hin : In (p, cap_of j) (live MI A)) by (rewrite QL; left; reflexivity).
    destruct (loop_client A M M' (at_off path mo len) (closed3 mo) p (cap_of j) len L QM QA Hin Hpimg Hpce
                ltac:(lia) ltac:(lia) PM) as [RM' RA']; try reflexivity.
    apply (HEND p (cap_of j) A R' M' (closed3 mo)). constructor; try assumption.
    - rewrite PK by reg_in. exact Q3.
    - rewrite PK by reg_in. exact Q4.
    - rewrite PK by reg_in. exact Q8.
    - rewrite PK by reg_in. exact Q18.
    - rewrite PK by reg_in. exact Q20.
    - rewrite PK by reg_in. exact Q21.
    - rewrite PK by reg_in. exact Q22.
    - split; [lia | exists j; split; [lia | reflexivity]].
    - eapply (content_at_buf content M M' sp0 p len); [lia | lia | lia | lia | exact QC | exact PM].
    - reflexivity.
  Qed.

  Theorem stage : forall (d j : nat) p len A R M mo,
    (j + d = 10)%nat ->
    RST p (cap_of j) len A R M mo ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65908) M (seg_rom RSEGS)) mo) (rshape d j L KEND fs0).
  Proof.
    induction d as [|d IH]; intros j p len A R M mo Hjd RQ.
    all: pose proof HAC as Hcv; pose proof ac_bounds_lit as Hcb; pose proof (dm_consts _ _ _ _ DM) as [MSc BIGc NMAXc RBc SCg SCn SCp].
    all: destruct RQ as [Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 QM QA QT QL [Hlen HlenL] QC QFDS QFS].
    all: pose proof (cap_of_range j ltac:(lia)) as Hcap.
    all: destruct (buf_geom A M mo p (cap_of j) QA QL ltac:(lia)) as (Hpimg & Hpce & Hpal).
    all: pose proof (ra_ainv _ _ _ _ QA) as AI; pose proof (ra_mstd _ _ _ _ QA) as MS; destruct MS as [Hh Hlz Hmat Hceil].
    all: assert (Hin : In (p, cap_of j) (live MI A)) by (rewrite QL; left; reflexivity).
    all: pose proof QA as QA0; rewrite <- (at_off_eta path mo len QFDS) in QA; rewrite <- (at_off_eta path mo len QFDS).
    all: apply (chunk_loop path content mo ltac:(rewrite QFS; exact Hfile) Hh Hlz (Z.to_nat (cap_of j)) R M sp0 p len (cap_of j));
      [lia | repeat split; assumption | lia | lia | lia | lia | lia | lia | exact HlenL
      |   replace (Z_to_bv 64 (sp0 - 136)) with (Z_to_bv 64 (sp0 - 8388608 + 8388472)) by (f_equal; lia);
        apply (rm_stack _ _ _ _ _ QM); lia
      |   apply store_ok_rwZ; unfold RS; lia
      |   apply (live_store_ok MI A M _ p (cap_of j) len (Z.to_nat (cap_of j - len)) AI Hin); lia
      | | ].

    2,4: intros HLc R' M' PR P23 PM; cbn [rshape]; destruct (Z.ltb_spec L (cap_of j)) as [Xlt|Xge]; [|lia];
         eapply (stage_end j p len A R M mo R' M'); try eassumption; lia.

    - intros HcL R' M' (P2 & P9 & P19 & PK) P23 PM.
      assert (Hj : j = 10%nat) by lia. subst j. rewrite cap_of_10 in *.
      cbn [rshape]. rewrite cap_of_10. destruct (Z.ltb_spec L (2 ^ 26)) as [Xlt|Xge]; [lia|].
      destruct (walkRef R' M' (seg_rom RSEGS) P19) as (R2 & MS2 & K2).
      replace (Z_to_bv 64 0x658d0) with (0x658d0%bv : word) by (apply bv_eq; reflexivity).
      eapply srz_msteps; [exact Hh | exact Hlz | exact MS2 |].
      replace (0x65a84%bv : word) with (Z_to_bv 64 0x65a84) by (apply bv_eq; reflexivity).
      destruct (loop_client A M M' (at_off path mo len) (at_off path mo (2 ^ 26)) p (2 ^ 26) len (2 ^ 26) QM QA Hin Hpimg Hpce
                  ltac:(lia) ltac:(lia) PM) as [RM' RA']; try reflexivity.
      apply (HREF A R2 M'). constructor; try assumption;
        try (rewrite K2 by (intros E; discriminate E); first [exact P2 | rewrite PK by reg_in; assumption]);
        try reflexivity.

    - intros HcL R' M' (P2 & P9 & P19 & PK) P23 PM.
      assert (Hj : (j < 10)%nat) by lia. pose proof (cap_of_lt10 j Hj) as Hclt.
      cbn [rshape]. destruct (Z.ltb_spec L (cap_of j)) as [Xlt|Xge]; [lia|]. fold (rshape d (S j) L KEND fs0).
      destruct (loop_client A M M' (at_off path mo len) (at_off path mo (cap_of j)) p (cap_of j) len (cap_of j) QM QA Hin Hpimg Hpce
                  ltac:(lia) ltac:(lia) PM) as [RM' RA']; try reflexivity.
      pose proof (ra_ainv _ _ _ _ RA') as AI'.

      assert (QC' : rdn RSEGS M' (Z_to_bv 64 p) (Z.to_nat (cap_of j)) = Some (pref (cap_of j) content)).
      { pose proof (content_at_buf (pref (cap_of j) content) M M' sp0 p len) as CB.
        rewrite (pref_length (cap_of j) content) in CB by lia.
        replace (Z.min (cap_of j) (Z.of_nat (length content))) with (cap_of j) in CB by lia.
        replace (length (pref (cap_of j) content)) with (Z.to_nat (cap_of j)) in CB
          by (pose proof (pref_length (cap_of j) content ltac:(lia)); lia).
        apply CB; [lia | lia | lia | lia | | ].
        - rewrite QC. f_equal. unfold pref. rewrite firstn_firstn. f_equal. lia.
        - destruct PM as [FRM RD]. split; [exact FRM|]. rewrite RD. f_equal.
          unfold pref, dropz.
          replace (Z.to_nat (cap_of j)) with (Z.to_nat len + Z.to_nat (cap_of j - len))%nat by lia.
          rewrite <- firstn_skipn_comm, firstn_firstn. f_equal. lia. }

      destruct (walkG R' M' (seg_rom RSEGS) (cap_of j) P19 ltac:(lia)) as (R2 & MS2 & G1 & G10 & G21 & GK).
      replace (Z_to_bv 64 0x658d0) with (0x658d0%bv : word) by (apply bv_eq; reflexivity).
      eapply srz_msteps; [exact Hh | exact Hlz | exact MS2 |].
      replace (0xd3e38%bv : word) with (Z_to_bv 64 (ly_malloc U1Layout.L)) by (apply bv_eq; reflexivity).
      eapply (dm_malloc _ _ _ _ DM fx A R2 M' (at_off path mo (cap_of j)) (2 * cap_of j) (sp0 - 128) 0x658e4
                (rshape d (S j) L KEND fs0) AI' QT).
      + left. rewrite BIGc. lia.
      + apply mstd_at_off. constructor; assumption.
      +   intros w Hi Hnrw.
        assert (Hw : (0x10000 <= bv_unsigned w < 0xef000)).
        { apply img_iff in Hi. destruct (Z.lt_ge_cases (bv_unsigned w) 0xef000); [lia|]. exfalso. apply Hnrw.
          exists 0xef000, 0x124000. split; [left; reflexivity | lia]. }
        rewrite <- (Z_to_bv_bv_unsigned 64 w).
        pose proof (proj1 (Forall_forall _ _) (rm_img _ _ _ _ _ RM') (0x10000, 0xf0200) ltac:(unfold rimg_ivs; cbn; tauto)) as C.
        cbn [fst snd] in C. apply C. lia.
      + constructor.
        * rewrite G1. apply bv_eq. reflexivity.
        * apply bv_eq. vm_compute. reflexivity.
        * lia.
        * rewrite GK by reg_in. exact P2.
        * rewrite Zminus_mod, (proj2 Hsp). reflexivity.
        * lia.
        * rewrite GK by reg_in. rewrite PK by reg_in. exact Q3.
        * rewrite GK by reg_in. rewrite PK by reg_in. exact Q4.
      + exact G10.
      + rewrite NMAXc. lia.
      + rewrite MSc. lia.
      + rewrite MSc. unfold stack_room.
        replace (Z_to_bv 64 (sp0 - 128 - 8192)) with (Z_to_bv 64 (sp0 - 8388608 + 8380288)) by (f_equal; lia).
        apply (rm_stack _ _ _ _ _ RM'); lia.
      + rewrite MSc. intros a Ha. unfold zwin in Ha. exact (high_not_owned MI A M' (at_off path mo (cap_of j)) a AI' ltac:(lia)).
      +
        apply (room_big MI A M' (at_off path mo (cap_of j)) (2 * cap_of j) AI'); [rewrite BIGc, NMAXc; lia|].
        rewrite (ra_big _ _ _ _ RA'), QL. cbn [big_bytes_f]. rewrite BIGc. unfold LIB_BIGCAP.
        pose proof (RBc (cap_of j) ltac:(lia)). pose proof (RBc (2 * cap_of j) ltac:(lia)).
        destruct (131052 <=? cap_of j); lia.
      +
        intros A' R3 M3 mo3 nb AI3 TI3 MS3 FS3 FDS3 KEPT A10 Hnb LADD CP BG NEWT FR DEF.
        rewrite QL in LADD. destruct LADD as [LV3 Hfresh].
        assert (Hin3 : In (nb, 2 * cap_of j) (live MI A')) by (rewrite LV3; left; reflexivity).
        assert (Hin3p : In (p, cap_of j) (live MI A')) by (rewrite LV3; right; left; reflexivity).
        destruct (ai_live_block MI A' M3 mo3 nb (2 * cap_of j) AI3 Hin3) as (_ & Hnbal & _ & Hnbce & Hnbby).
        pose proof (live_above_img MI A' M3 mo3 nb (2 * cap_of j) AI3 Hin3 ltac:(lia)) as Hnbimg.
        rewrite MSc in FR.
        destruct (rstep_alloc MI sp0 tid p1 path Hsp Hp1 HAC A A' M' M3 (at_off path mo (cap_of j)) mo3
                    (fun a => nb <= a < nb + 2 * cap_of j) (sp0 - 128 - 8192) (sp0 - 128) RM' RA' AI3 MS3 CP BG) as (RM3 & RA3 & AG3).
        * intros a Ho Hi. destruct (NEWT a Ho) as [H|[H _]]; [exact H | exfalso; exact (H Hi)].
        * intros a Ha. split; [lia|]. exact (proj1 (proj2 (Hnbby a Ha))).
        * lia. * lia.
        * intros a Hn. apply FR. intros [H|[H|[H|H]]]; apply Hn; [right; left | right; right; left | right; right; right; left | right; right; right; right]; exact H.
        * intros a Hd. destruct (DEF a Hd) as [H|[H|H]]; [left | right; left | right; right; right]; exact H.
        *
          assert (QC3 : rdn RSEGS M3 (Z_to_bv 64 p) (Z.to_nat (cap_of j)) = Some (pref (cap_of j) content)).
          { rewrite <- QC'. apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
            apply FR. intros [H|[H|[H|H]]].
            - destruct (ai_live_block MI A' M3 mo3 p (cap_of j) AI3 Hin3p) as (_ & _ & _ & _ & Hpb). exact (proj1 (Hpb (bv_unsigned x) ltac:(lia)) H).
            - destruct (ai_live_disjoint MI A' M3 mo3 nb (2 * cap_of j) p (cap_of j) AI3 Hin3 Hin3p) as [Hd|Hd]; try lia.
              intros ->. apply Hfresh. cbn. left. reflexivity.
            - unfold zwin in H. lia.
            - exact (high_not_errno (bv_unsigned x) ltac:(lia) H). }

          destruct (walkG1 R3 M3 (seg_rom RSEGS) nb p (cap_of j) A10
                      ltac:(rewrite (KEPT 23%bv) by reg_in; rewrite GK by reg_in; exact P23)
                      ltac:(rewrite (KEPT 19%bv) by reg_in; rewrite GK by reg_in; exact P19) ltac:(lia) ltac:(lia))
            as (R4 & MS4 & M1 & M10 & M11 & M12 & M9 & MK).
          replace (Z_to_bv 64 0x658e4) with (0x658e4%bv : word) by (apply bv_eq; reflexivity).
          eapply srz_msteps; [exact (ms_halt _ MS3) | exact (ms_lazy _ MS3) | exact MS4 |].
          destruct (u1_memcpy M3 (Z_to_bv 64 nb) (Z_to_bv 64 p) (cap_of j) (pref (cap_of j) content) (seg_rom RSEGS) R4 (0x65900%bv : word))
            as (R5 & MS5 & K5).
          { constructor.
            - lia.
            - pose proof (pref_length (cap_of j) content ltac:(lia)). lia.
            - replace (length (pref (cap_of j) content)) with (Z.to_nat (cap_of j)) by (pose proof (pref_length (cap_of j) content ltac:(lia)); lia). exact QC3.
            - replace (length (pref (cap_of j) content)) with (Z.to_nat (cap_of j)) by (pose proof (pref_length (cap_of j) content ltac:(lia)); lia).
              replace (Z_to_bv 64 nb) with (Z_to_bv 64 (nb + 0)) by (f_equal; lia).
              apply (live_store_ok MI A' M3 mo3 nb (2 * cap_of j) 0 _ AI3 Hin3); lia.
            - rewrite !u64_lit by lia.
              destruct (ai_live_disjoint MI A' M3 mo3 nb (2 * cap_of j) p (cap_of j) AI3 Hin3 Hin3p) as [Hd|Hd]; try lia.
              intros ->. apply Hfresh. cbn. left. reflexivity.
            - rewrite u64_lit by lia. lia.
            - rewrite u64_lit by lia. lia. }
          { apply bv_eq. vm_compute. reflexivity. }
          { rewrite M1. apply bv_eq. reflexivity. } { exact M10. } { exact M11. } { exact M12. }
          change u1_memcpy_entry with (0xe2b9c%bv : word) in MS5.
          eapply srz_msteps; [exact (ms_halt _ MS3) | exact (ms_lazy _ MS3) | exact MS5 |].
          set (M5 := wbytes M3 (Z_to_bv 64 nb) (pref (cap_of j) content)) in *.
          destruct (rstep_client MI sp0 tid p1 path Hsp Hp1 HAC A' M3 M5 mo3 mo3 RM3 RA3 ltac:(subst M5; apply wbytes_grows)) as [RM5 RA5];
            [ | reflexivity | reflexivity | reflexivity | reflexivity | ].
          { intros a Hne. left. exists nb, (2 * cap_of j). split; [exact Hin3|]. pose proof (u64_range a).
            destruct (Classical_Prop.classic (nb <= bv_unsigned a < nb + 2 * cap_of j)) as [Hb|Hb]; [exact Hb|]. exfalso. apply Hne.
            subst M5. apply wbytes_outside; [|rewrite u64_lit by lia; pose proof (pref_length (cap_of j) content ltac:(lia)); lia].
            unfold in_rng. rewrite u64_lit by lia. pose proof (pref_length (cap_of j) content ltac:(lia)). lia. }

          destruct (walkG2 R5 M5 (seg_rom RSEGS) p ltac:(rewrite (K5 23%bv) by reg_in; rewrite MK by reg_in;
                      rewrite (KEPT 23%bv) by reg_in; rewrite GK by reg_in; exact P23)) as (R6 & MS6 & F1 & F10 & FK).
          eapply srz_msteps; [exact (ms_halt _ MS3) | exact (ms_lazy _ MS3) | exact MS6 |].
          replace (0xd3cf8%bv : word) with (Z_to_bv 64 (ly_free U1Layout.L)) by (apply bv_eq; reflexivity).
          pose proof (ra_ainv _ _ _ _ RA5) as AI5.
          assert (KR : forall r : reg, In r [2; 3; 4; 8; 18; 20; 21; 22]%bv -> getr R6 r = getr R2 r).
          { intros r Hr. rewrite FK by reg_sub Hr.
            rewrite (K5 r) by reg_sub Hr.
            rewrite MK by reg_sub Hr.
            apply KEPT. reg_sub Hr. }
          eapply (dm_free _ _ _ _ DM fx A' R6 M5 mo3 p (cap_of j) (sp0 - 128) 0x65908 _ AI5 TI3 MS3).
          -- intros w Hi Hnrw.
             assert (Hw : (0x10000 <= bv_unsigned w < 0xef000)).
             { apply img_iff in Hi. destruct (Z.lt_ge_cases (bv_unsigned w) 0xef000); [lia|]. exfalso. apply Hnrw.
               exists 0xef000, 0x124000. split; [left; reflexivity | lia]. }
             rewrite <- (Z_to_bv_bv_unsigned 64 w).
             pose proof (proj1 (Forall_forall _ _) (rm_img _ _ _ _ _ RM5) (0x10000, 0xf0200) ltac:(unfold rimg_ivs; cbn; tauto)) as C.
             cbn [fst snd] in C. apply C. lia.
          -- constructor.
             ++ rewrite F1. apply bv_eq. reflexivity.
             ++ apply bv_eq. vm_compute. reflexivity.
             ++ lia.
             ++ rewrite (KR 2%bv) by reg_in. rewrite GK by reg_in. exact P2.
             ++ rewrite Zminus_mod, (proj2 Hsp). reflexivity.
             ++ lia.
             ++ rewrite (KR 3%bv) by reg_in. rewrite GK by reg_in. rewrite PK by reg_in. exact Q3.
             ++ rewrite (KR 4%bv) by reg_in. rewrite GK by reg_in. rewrite PK by reg_in. exact Q4.
          -- exact F10.
          -- right. exact Hin3p.
          -- rewrite MSc. lia.
          -- rewrite MSc. unfold stack_room.
             replace (Z_to_bv 64 (sp0 - 128 - 8192)) with (Z_to_bv 64 (sp0 - 8388608 + 8380288)) by (f_equal; lia).
             apply (rm_stack _ _ _ _ _ RM5); lia.
          -- rewrite MSc. intros a Ha. unfold zwin in Ha. exact (high_not_owned MI A' M5 mo3 a AI5 ltac:(lia)).
          --
             intros A7 R7 M7 mo7 AI7 TI7 MS7 FS7 FDS7 KEPT7 LDEL CP7 BG7 OWN7 FR7 DEF7.
             rewrite MSc in FR7.
             destruct (rstep_alloc MI sp0 tid p1 path Hsp Hp1 HAC A' A7 M5 M7 mo3 mo7
                         (fun a => p <= a < p + cap_of j) (sp0 - 128 - 8192) (sp0 - 128) RM5 RA5 AI7 MS7 CP7 BG7) as (RM7 & RA7 & AG7).
             ** intros a Ho Hi. destruct (OWN7 a Ho) as [H|H]; [exact H|]. exfalso.
                destruct (ai_live_block MI A' M5 mo3 p (cap_of j) AI5 Hin3p) as (_ & _ & _ & _ & Hpb). exact (proj1 (proj2 (Hpb _ H)) Hi).
             ** intros a Ha. destruct (ai_live_block MI A' M5 mo3 p (cap_of j) AI5 Hin3p) as (_ & _ & _ & Hpc & Hpb). split; [lia|]. exact (proj1 (proj2 (Hpb _ Ha))).
             ** lia. ** lia.
             ** intros a Hn. apply FR7. intros [H|[H|[H|H]]]; apply Hn; [left | right; right; left | right; right; right; left | right; right; right; right]; exact H.
             ** exact DEF7.
             ** assert (LV7 : live MI A7 = [(nb, 2 * cap_of j)]).
                { apply (live_single MI A7 M7 mo7 _ AI7). intros e.
                  destruct e as [q k]. rewrite (LDEL q k), LV3. cbn. split.
                  - intros [[E|[E|[]]] Hne]; [symmetry; exact E|]. injection E as <- <-. exfalso. apply Hne. reflexivity.
                  - intros E. injection E as -> ->. split; [left; reflexivity|].
                    destruct (ai_live_disjoint MI A' M3 mo3 nb (2 * cap_of j) p (cap_of j) AI3 Hin3 Hin3p) as [Hd|Hd]; try lia.
                    intros ->. apply Hfresh. cbn. left. reflexivity. }
                replace (0x65908%bv : word) with (Z_to_bv 64 0x65908) by (apply bv_eq; reflexivity).
                apply (IH (S j) nb (cap_of j) A7 R7 M7 mo7 ltac:(lia)).
                constructor.
                --- rewrite (KEPT7 2%bv) by reg_in. rewrite (KR 2%bv) by reg_in. rewrite GK by reg_in. exact P2.
                --- rewrite (KEPT7 3%bv) by reg_in. rewrite (KR 3%bv) by reg_in. rewrite GK by reg_in. rewrite PK by reg_in. exact Q3.
                --- rewrite (KEPT7 4%bv) by reg_in. rewrite (KR 4%bv) by reg_in. rewrite GK by reg_in. rewrite PK by reg_in. exact Q4.
                --- rewrite (KEPT7 8%bv) by reg_in. rewrite (KR 8%bv) by reg_in. rewrite GK by reg_in. rewrite PK by reg_in. exact Q8.
                --- rewrite (KEPT7 9%bv) by reg_in. rewrite FK by reg_in. rewrite (K5 9%bv) by reg_in. exact M9.
                --- rewrite (KEPT7 18%bv) by reg_in. rewrite (KR 18%bv) by reg_in. rewrite GK by reg_in. rewrite PK by reg_in. exact Q18.
                --- rewrite (KEPT7 19%bv) by reg_in. rewrite FK by reg_in. rewrite (K5 19%bv) by reg_in.
                    rewrite MK by reg_in. rewrite (KEPT 19%bv) by reg_in. rewrite GK by reg_in. exact P19.
                --- rewrite (KEPT7 20%bv) by reg_in. rewrite (KR 20%bv) by reg_in. rewrite GK by reg_in. rewrite PK by reg_in. exact Q20.
                --- rewrite (KEPT7 21%bv) by reg_in. rewrite (KR 21%bv) by reg_in. rewrite cap_of_S. exact G21.
                --- rewrite (KEPT7 22%bv) by reg_in. rewrite (KR 22%bv) by reg_in. rewrite GK by reg_in. rewrite PK by reg_in. exact Q22.
                --- exact RM7.
                --- exact RA7.
                --- exact TI7.
                --- rewrite cap_of_S. exact LV7.
                --- rewrite cap_of_S. lia.
                ---
                    assert (E5 : rdn RSEGS M5 (Z_to_bv 64 nb) (Z.to_nat (cap_of j)) = Some (pref (cap_of j) content)).
                    { subst M5. replace (Z.to_nat (cap_of j)) with (length (pref (cap_of j) content)) by (pose proof (pref_length (cap_of j) content ltac:(lia)); lia).
                      apply rdn_wbytes_hit. rewrite u64_lit by lia. pose proof (pref_length (cap_of j) content ltac:(lia)). lia. }
                    rewrite <- E5. apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
                    apply FR7. intros [H|[H|[H|H]]].
                    +++ exact (proj1 (Hnbby (bv_unsigned x) ltac:(lia)) H).
                    +++ destruct (ai_live_disjoint MI A' M3 mo3 nb (2 * cap_of j) p (cap_of j) AI3 Hin3 Hin3p) as [Hd|Hd]; try lia.
                        intros ->. apply Hfresh. cbn. left. reflexivity.
                    +++ unfold zwin in H. lia.
                    +++ exact (high_not_errno (bv_unsigned x) ltac:(lia) H).
                --- rewrite FDS7, FDS3. reflexivity.
                --- rewrite FS7, FS3. exact QFS.
  Qed.
End Loop.
End FXALL.
