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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 SumMemcpyBase SumMemcpy U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts U1Facts. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Str_PushBack.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Str_PushBack.U1Lib_Musl_Memmove.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac DiagVia DiagViaU1 DiagU1 DRepU1 DStr Lib_Str_AppendU1 SbOverflowU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition XS_LOOP : Z := 0x91cb0.
Definition XS_RETMM : Z := 0x91cdc.
Definition XS_RETOV : Z := 0x91cf8.
Definition XS_EXIT : Z := 0x91d10.
Definition XS_RETPC : Z := 0x91d34.

Section Xsputn.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : 0 <= MALLOC_STACK MI.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Definition XS_STK : Z := 64 + OVF_STK MI.

  Variable RI : AS MI -> sbuf -> Z -> Prop.
  Hypothesis RI_grow : forall A M model m w, ainv MI A M model -> RI A m w -> w = str_cap m -> w + 1 <= DS_MAXLEN ->
      str_grow m <= NMAX MI /\ roomL MI A (live MI A) (str_grow m).
  Hypothesis RI_step : forall A A' M' model' m w d, ainv MI A' M' model' -> RI A m w -> w = str_cap m ->
      lapply (live MI A) (LAdd d (str_grow m) :: sbuf_del m) (live MI A') ->
      caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
      RI A' (SLong d (str_grow m)) (w + 1).
  Hypothesis RI_mono : forall A m w w', RI A m w -> w <= w' <= str_cap m -> RI A m w'.

  Definition src_ok (A : AS MI) (sp sb : Z) (m : sbuf) (src n : Z) : Prop :=
    forall a, src <= a < src + n ->
      ~ zwin sb (sb + 104) a /\
      ((sp <= a /\ alloc_ceiling <= a) \/ ro_addr Ly.L a
       \/ (exists q k, In (q, k) (live MI A) /\ q <= a < q + k /\ ~ In (q, k) (str_blocks m))).

  Definition xfer (A0 A1 : AS MI) (m0 m1 : sbuf) : Prop :=
    (forall x, In x (live MI A0) -> ~ In x (str_blocks m0) -> In x (live MI A1) /\ ~ In (fst x) (map fst (str_blocks m1)))
    /\ (forall x, In x (str_blocks m1) -> In x (live MI A1))
    /\ (forall x, In x (live MI A1) -> In x (str_blocks m1) \/ (In x (live MI A0) /\ ~ In x (str_blocks m0))).

  Definition junk0 (A0 : AS MI) (m0 : sbuf) (J : Z -> Prop) : Prop :=
    forall a, J a -> 0 < a < alloc_ceiling /\ ~ in_ranges (ly_img Ly.L) a /\
                     (forall q k, In (q, k) (live MI A0) -> ~ In (q, k) (str_blocks m0) -> ~ (q <= a < q + k)).

  Definition FUEL : nat := 200%nat.

  Lemma NoDup_fst_unique : forall (l : list (Z * Z)) d a b, NoDup (map fst l) -> In (d, a) l -> In (d, b) l -> a = b.
  Proof using.
    induction l as [|[q k] l IH]; intros d a b ND Ha Hb; [destruct Ha|]. cbn [map fst] in ND.
    inversion ND as [|q' l' Hq Hl]; subst.
    destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
    - rewrite Ha in Hb; injection Hb; auto.
    - injection Ha as -> ->. exfalso. apply Hq. apply list_elem_of_In. apply (in_map fst) in Hb. exact Hb.
    - injection Hb as -> ->. exfalso. apply Hq. apply list_elem_of_In. apply (in_map fst) in Ha. exact Ha.
    - exact (IH d a b Hl Ha Hb).
  Qed.

  Lemma own_sx_via_eff : forall (A A' : AS MI) M M' Wd F,
    eff MI A A' M M' Wd F -> (forall a, owned MI A a -> ~ sx_region ST a) ->
    forall a, owned MI A' a -> ~ sx_region ST a.
  Proof using AC MI ST.
    intros A A' M M' Wd F EF H a Ho Hs. apply (H a); [|exact Hs].
    apply (ef_oimg _ _ _ _ _ _ _ _ _ EF a Ho). apply ly_rw_img. apply (sx_region_rw ST). exact Hs.
  Qed.

  Section Call.
    Context {fx : FPState}.
    Variables (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
    Variables (sp ret sb src n : Z) (m0 : sbuf) (pp0 hm0 : Z) (bs : list byte) (K : TSet).
    Hypothesis CB : callB MI ST A0 s R0 M0 model0 sp ret XS_STK.
    Hypothesis ROC0 : ro_clear Ly.L M0.
    Hypothesis SB0 : sb_inv A0 M0 sb m0 pp0 hm0.
    Hypothesis Hsb0 : sp <= sb.
    Hypothesis Hsb1 : sb + 104 <= 2 ^ 47.
    Hypothesis HDsb0 : mdef M0 sb 104.
    Hypothesis Hn : 0 < n.
    Hypothesis SRC : src_ok A0 sp sb m0 src n.
    Hypothesis Hsrc : 0 <= src /\ src + n <= 2 ^ 47.
    Hypothesis RD0 : rdn SEGS M0 (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
    Let w0 : Z := pp0 - str_data (sb + 64) m0.
    Hypothesis RI0 : RI A0 m0 w0.
    Hypothesis BUD : w0 + n <= DS_MAXLEN.

    Definition SV : list word := [Z_to_bv 64 ret; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv; getr R0 19%bv; getr R0 20%bv; getr R0 21%bv].
    Definition W : Z * Z := (sp - XS_STK, sp).

    Hypothesis CONT : forall A' R' M' model' (m' : sbuf) (pp' hm' : Z) (J : Z -> Prop),
        retB MI ST A' s R0 R' M' model0 model' ->
        getr R' 10%bv = Z_to_bv 64 n ->
        sb_inv A' M' sb m' pp' hm' -> mdef M' sb 104 -> pp' - str_data (sb + 64) m' = w0 + n ->
        RI A' m' (w0 + n) ->
        xfer A0 A' m0 m' -> junk0 A0 m0 J ->
        eff MI A0 A' M0 M' W (fun a => zwin sb (sb + 104) a \/ sbuf_fp m0 a \/ sbuf_fp m' a \/ J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    Record xinv (i : Z) (A1 : AS MI) (M1 : mem) (model1 : Model) (m1 : sbuf) (pp1 hm1 : Z) (J : Z -> Prop) : Prop := XINV {
      xi_ai   : ainv MI A1 M1 model1;
      xi_ms   : mstd model1;
      xi_fs   : m_fs model1 = m_fs model0;
      xi_fds  : m_fds model1 = m_fds model0;
      xi_sx   : sx_inv ST s M1;
      xi_roc  : ro_clear Ly.L M1;
      xi_caps : caps MI A1 = caps MI A0;
      xi_big  : bigcap MI A1 = bigcap MI A0;
      xi_sb   : sb_inv A1 M1 sb m1 pp1 hm1;
      xi_w    : pp1 - str_data (sb + 64) m1 = w0 + i;
      xi_ri   : RI A1 m1 (w0 + i);
      xi_slots : slots SEGS M1 sp SV;
      xi_win  : mdef M1 (sp - XS_STK) XS_STK;
      xi_src  : rdn SEGS M1 (Z_to_bv 64 src) (Z.to_nat n) = Some bs;
      xi_sbdef : mdef M1 sb 104;
      xi_xfer : xfer A0 A1 m0 m1;
      xi_junk : junk0 A0 m0 J;
      xi_eff  : eff MI A0 A1 M0 M1 W (fun a => zwin sb (sb + 104) a \/ sbuf_fp m0 a \/ sbuf_fp m1 a \/ J a)
    }.

    Definition xregs (R : bvmap 5 word) (i : Z) : Prop :=
      getr R 2%bv = Z_to_bv 64 (sp - 64) /\ getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) /\
      getr R 8%bv = Z_to_bv 64 i /\ getr R 9%bv = Z_to_bv 64 n /\ getr R 18%bv = Z_to_bv 64 (src + i) /\
      getr R 19%bv = Z_to_bv 64 sb /\ getr R 21%bv = Z_to_bv 64 (2 ^ 64 - 1) /\
      (forall r, In r [22; 23; 24; 25; 26; 27]%bv -> getr R r = getr R0 r).

    Lemma sb_data_mdef : forall A M model m pp hm,
      ainv MI A M model -> sb_inv A M sb m pp hm -> mdef M sb 104 ->
      mdef M (str_data (sb + 64) m) (str_cap m + 1)
      /\ 0 <= str_data (sb + 64) m /\ str_data (sb + 64) m + str_cap m + 1 <= 2 ^ 63
      /\ (forall d asz, m = SLong d asz -> In (d, asz) (live MI A) /\ d + asz <= alloc_ceiling /\ 0 < d /\ str_cap m + 1 <= asz).
    Proof using AC MI sb m0 pp0 Hsb1.
      intros A M model m pp hm AI SB HD. destruct SB as [_ _ _ _ _ (cs & STR & HL) _ _ _ _ _ _ _].
      pose proof STR as (Hs0 & Hs1 & HDs & Hlen & HM & _).
      destruct m as [|d asz]; cbn [str_data str_cap] in *.
      - unfold SSO_CAP in *. split; [eapply mdef_sub; [exact HD | lia | lia]|]. split; [lia|]. split; [lia|]. intros d asz E; discriminate E.
      - destruct HM as (Hd0 & _ & Hdsz & _ & Hmin & HIn & _). pose proof (live_range _ _ MI A M model d asz AI HIn) as (_ & _ & _ & Hc).
        split; [eapply mdef_sub; [eapply (live_mdef _ _ MI); [exact AI | exact HIn] | lia | lia]|].
        split; [lia|]. split; [lia|]. intros d1 asz1 E. injection E as <- <-. repeat split; [exact HIn | lia | lia | lia].
    Qed.

    Lemma ctx_bounds : alloc_ceiling + XS_STK <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 0 <= ret < 2 ^ 64
      /\ (forall a, zwin (sp - XS_STK) sp a -> ~ owned MI A0 a /\ ~ sx_region ST a).
    Proof using AC MI ST A0 s R0 M0 model0 sp ret CB.
      destruct CB as [AI MS ROC' SXI SXH [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp] Hceil HROOM Hwin Hown_sx Herr_sx].
      split; [exact Hceil|]. split; [exact Hsphi|]. split; [exact Hsp16|]. split; [exact Hretr|]. exact Hwin.
    Qed.

    Lemma xinv_grow : forall i A1 M1 model1 m1 pp1 hm1 J A' M' model' d',
      xinv i A1 M1 model1 m1 pp1 hm1 J -> 0 <= i < n -> w0 + i = str_cap m1 ->
      ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model1 -> m_fds model' = m_fds model1 -> sx_inv ST s M' ->
      sb_inv A' M' sb (SLong d' (str_grow m1)) (d' + str_cap m1 + 1) (d' + str_cap m1 + 1) ->
      mdef M' sb 104 ->
      lapply (live MI A1) (LAdd d' (str_grow m1) :: sbuf_del m1) (live MI A') ->
      eff MI A1 A' M1 M' (sp - 64 - OVF_STK MI, sp - 64) (fun a => zwin sb (sb + 104) a \/ sbuf_fp m1 a \/ zwin d' (d' + str_grow m1) a) ->
      xinv (i + 1) A' M' model' (SLong d' (str_grow m1)) (d' + str_cap m1 + 1) (d' + str_cap m1 + 1)
           (fun a => J a \/ (m1 <> m0 /\ sbuf_fp m1 a)).
    Proof using AC MI ST MALLOC_STACK_pos RI RI_step A0 s R0 M0 model0 sp ret sb src n m0 pp0 bs CB Hsb0 Hsb1 Hn SRC Hsrc.
      intros i A1 M1 model1 m1 pp1 hm1 J A' M' model' d' XI Hi FULL AI' MS' FS' FDS' SX' SB' HDsb' LAP EFF.
      pose proof ctx_bounds as (Hceil & Hsphi & Hsp16 & Hretr & Hwin). destruct XI.
      assert (HXS : XS_STK = 208 + (16 + MALLOC_STACK MI)) by (unfold XS_STK, OVF_STK, NEW_STACK; lia).
      assert (HOV : OVF_STK MI = 144 + (16 + MALLOC_STACK MI)) by (unfold OVF_STK, NEW_STACK; lia).
      pose proof ac_bounds_lit as Hcv.
      set (g := str_grow m1) in *. set (cap1 := str_cap m1) in *.
      destruct (sb_data_mdef A1 M1 model1 m1 pp1 hm1 xi_ai0 xi_sb0 xi_sbdef0) as (HDdat & Hdat0 & Hdat1 & Hblk).

      destruct SB' as [G0 G8 G16 G24 G32 (cs' & STR' & HL') G40 G48 G56 Gpp G88 Ghm G96]. cbn [str_data str_cap] in *.
      pose proof STR' as (_ & _ & HDp' & Hlen' & (Hd'0 & _ & Hd'sz & _ & _ & HIn' & Hdj' & _) & _ & _).
      pose proof (live_range _ _ MI A' M' model' d' g AI' HIn') as (_ & _ & _ & Hd'ceil).

      destruct LAP as (lv1 & ADD & LAP2).
      assert (LA' : forall x, In x (live MI A') <-> (d', g) = x \/ (In x (live MI A1) /\ ~ In (fst x) (map fst (str_blocks m1)))).
      { intros [q k]. destruct m1 as [|d1 a1]; cbn [sbuf_del str_blocks map fst] in *.
        - cbn in LAP2. subst lv1. destruct ADD as [-> _]. cbn.
          split; [intros [E|H]; [left; exact E | right; split; [exact H | intros []]] | intros [E|[H _]]; [left; exact E | right; exact H]].
        - destruct LAP2 as (lv2 & DEL & ->). rewrite (DEL q k). destruct ADD as [-> Hf]. cbn.
          destruct (Hblk d1 a1 eq_refl) as (HIn1 & _).
          assert (Hd1 : d' <> d1) by (intros ->; apply Hf; apply in_map_iff; exists (d1, a1); split; [reflexivity | exact HIn1]).
          split.
          + intros [[E|Hin] Hne]; [left; exact E | right; split; [exact Hin | intros [E|[]]; exact (Hne (eq_sym E))]].
          + intros [E|[Hin Hnn]]; [split; [left; exact E | injection E as <- <-; intros E2; exact (Hd1 E2)] | split; [right; exact Hin | intros E; apply Hnn; left; symmetry; exact E]]. }
      destruct xi_xfer0 as (XF1 & XF2 & XF3).

      assert (M1blk : forall a, sbuf_fp m1 a -> 0 < a < alloc_ceiling /\ ~ in_ranges (ly_img Ly.L) a /\ ~ owned MI A1 a).
      { intros a Ha. destruct m1 as [|d1 a1]; [destruct Ha|]. cbn in Ha. unfold zwin in Ha. destruct (Hblk d1 a1 eq_refl) as (HIn1 & Hc1 & Hp1 & _).
        split; [lia|]. split; [eapply (live_offimg _ _ MI); [exact xi_ai0 | exact HIn1 | lia] | eapply (live_unowned _ _ MI); [exact xi_ai0 | exact HIn1 | lia]]. }
      assert (NF : forall a, alloc_ceiling <= a -> ~ (sb <= a < sb + 104) -> ~ (zwin sb (sb + 104) a \/ sbuf_fp m1 a \/ zwin d' (d' + g) a)).
      { intros a Ha Hs [Hf|[Hf|Hf]]; unfold zwin in Hf; [lia | destruct (M1blk a Hf); lia | lia]. }
      assert (AGS : agree_on (zwin (sp - 56) sp) M1 M').
      { eapply (agree_hi_via_eff MI A1 A' M1 M'); [exact EFF | exact xi_ai0 | exact AI' | lia | lia | eapply mdef_sub; [exact xi_win0 | lia | lia] | intros a Ha; apply NF; lia | cbn; lia]. }
      constructor.
      - exact AI'. - exact MS'. - rewrite FS'; exact xi_fs0. - rewrite FDS'; exact xi_fds0. - exact SX'.
      - eapply (ro_clear_via_eff MI A1 A' M1 M'); [exact xi_roc0 | exact xi_ai0 | exact EFF | | cbn; lia].
        intros a [Hf|[Hf|Hf]]; unfold zwin in Hf; [apply hi_offimg; lia | exact (proj1 (proj2 (M1blk a Hf))) | eapply (live_offimg _ _ MI); [exact AI' | exact HIn' | lia]].
      - rewrite (ef_caps _ _ _ _ _ _ _ _ _ EFF). exact xi_caps0.
      - rewrite (ef_bigcap _ _ _ _ _ _ _ _ _ EFF). exact xi_big0.
      - constructor; cbn [str_data str_cap]; try assumption. exists cs'. split; [exact STR' | exact HL'].
      - cbn [str_data]. lia.
      - replace (w0 + (i + 1)) with (w0 + i + 1) by lia. rewrite FULL. eapply RI_step; [exact AI' | rewrite <- FULL; exact xi_ri0 | reflexivity | exists lv1; split; [exact ADD | exact LAP2] | exact (ef_caps _ _ _ _ _ _ _ _ _ EFF) | exact (ef_bigcap _ _ _ _ _ _ _ _ _ EFF)].
      - eapply slots_agree; [exact xi_slots0 | cbn; lia | lia | cbn [length SV Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]; exact AGS].
      - eapply (mdef_via_eff MI A1 A' M1 M'); [exact EFF | | | | | | exact xi_win0]; [left; lia | lia | lia | |].
        + intros j Hj. apply (hi_unowned MI A1 M1 model1); [exact xi_ai0 | lia].
        + intros j Hj. apply NF; lia.
      -
        rewrite <- xi_src0. apply rdn_ext; [rewrite u64_of_Z by lia; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia.
        destruct (SRC (bv_unsigned x) ltac:(lia)) as [Hnsb Hk].
        assert (RDx : M1 x <> None \/ in_ranges (ly_img Ly.L) (bv_unsigned x)).
        { destruct Hk as [Hs|[Hro|Hb]]; [left | right; exact (proj1 Hro) | left].
          - destruct (DiagTac.rdn_pointwise SEGS M1 (Z.to_nat n) (Z_to_bv 64 src) bs x xi_src0 ltac:(rewrite u64_of_Z by lia; lia) ltac:(rewrite u64_of_Z by lia; lia)) as [H|H]; [exact H|].
            exfalso. apply H. apply seg_rom_offimg. apply hi_offimg. lia.
          - destruct Hb as (q & k & HIn0 & Hqk & Hnb). destruct (XF1 (q, k) HIn0 Hnb) as [HIn1 _].
            pose proof (live_mdef _ _ MI A1 M1 model1 q k xi_ai0 HIn1 (bv_unsigned x - q) ltac:(lia)) as D.
            replace (q + (bv_unsigned x - q)) with (bv_unsigned x) in D by lia. rewrite Z_to_bv_bv_unsigned in D. exact D. }
        apply (ef_frame _ _ _ _ _ _ _ _ _ EFF). intros [Ho|[Ho|[Hnm|[Hf|[Hw|He]]]]].
        + destruct Hk as [Hs|[Hro|(q & k & HIn0 & Hqk & Hnb)]].
          * exact (hi_unowned MI A1 M1 model1 (bv_unsigned x) xi_ai0 ltac:(lia) Ho).
          * destruct (ai_owned_not_img_ro MI A1 M1 model1 _ xi_ai0 Ho) as [Hrw|Hni]; [exact (proj1 (proj2 Hro) Hrw) | exact (Hni (proj1 Hro))].
          * destruct (XF1 (q, k) HIn0 Hnb) as [HIn1 _]. exact (live_unowned _ _ MI A1 M1 model1 q k _ xi_ai0 HIn1 Hqk Ho).
        + destruct Hk as [Hs|[Hro|(q & k & HIn0 & Hqk & Hnb)]].
          * exact (hi_unowned MI A' M' model' (bv_unsigned x) AI' ltac:(lia) Ho).
          * destruct (ai_owned_not_img_ro MI A' M' model' _ AI' Ho) as [Hrw|Hni]; [exact (proj1 (proj2 Hro) Hrw) | exact (Hni (proj1 Hro))].
          * destruct (XF1 (q, k) HIn0 Hnb) as [HIn1 Hnf].
            assert (HIn2 : In (q, k) (live MI A')) by (apply LA'; right; split; [exact HIn1 | exact Hnf]).
            exact (live_unowned _ _ MI A' M' model' q k _ AI' HIn2 Hqk Ho).
        + destruct Hnm as (Hni & _ & Hn0). rewrite Z_to_bv_bv_unsigned in Hn0. destruct RDx as [H|H]; [exact (H Hn0) | exact (Hni H)].
        + destruct Hf as [Hf|[Hf|Hf]]; [exact (Hnsb Hf) | |].
          * destruct Hk as [Hs|[Hro|(q & k & HIn0 & Hqk & Hnb)]].
            -- destruct (M1blk _ Hf). lia.
            -- exact (proj1 (proj2 (M1blk _ Hf)) (proj1 Hro)).
            -- destruct (XF1 (q, k) HIn0 Hnb) as [HIn1 Hnf]. destruct m1 as [|d1 a1]; [destruct Hf|]. cbn in Hf, Hnf. unfold zwin in Hf.
               destruct (Hblk d1 a1 eq_refl) as (HIn1' & _).
               assert (Hne : q <> d1) by (intros ->; apply Hnf; left; reflexivity).
               destruct (ai_live_disjoint MI A1 M1 model1 q k d1 a1 xi_ai0 HIn1 HIn1' Hne); lia.
          * unfold zwin in Hf. destruct Hk as [Hs|[Hro|(q & k & HIn0 & Hqk & Hnb)]].
            -- lia.
            -- apply (live_offimg _ _ MI A' M' model' d' g (bv_unsigned x) AI' HIn' ltac:(lia)). exact (proj1 Hro).
            -- destruct (XF1 (q, k) HIn0 Hnb) as [HIn1 Hnf].
               assert (HIn2 : In (q, k) (live MI A')) by (apply LA'; right; split; [exact HIn1 | exact Hnf]).
               assert (Hne : q <> d').
               { intros ->. destruct ADD as [_ Hfr]. apply Hfr. apply in_map_iff. exists (d', k). split; [reflexivity | exact HIn1]. }
               destruct (ai_live_disjoint MI A' M' model' q k d' g AI' HIn2 HIn' Hne); lia.
        + unfold W_of in Hw. cbn in Hw. destruct Hk as [Hs|[Hro|(q & k & HIn0 & Hqk & Hnb)]]; [lia | | ].
          * pose proof (ly_img_low _ (proj1 Hro)). lia.
          * destruct (XF1 (q, k) HIn0 Hnb) as [HIn1 _]. pose proof (live_range _ _ MI A1 M1 model1 q k xi_ai0 HIn1). lia.
        + destruct Hk as [Hs|[Hro|(q & k & HIn0 & Hqk & Hnb)]].
          * apply (hi_not_errno (bv_unsigned x)); [lia | exact He].
          * exact (proj1 (proj2 Hro) (ly_errno_rw _ He)).
          * destruct (XF1 (q, k) HIn0 Hnb) as [HIn1 _]. exact (live_offimg _ _ MI A1 M1 model1 q k _ xi_ai0 HIn1 Hqk (ly_errno_img _ He)).
      - exact HDsb'.
      -
        split; [|split].
        + intros x Hx0 Hnb. destruct (XF1 x Hx0 Hnb) as [Hx1 Hnf]. split.
          * apply LA'. right. split; [exact Hx1 | exact Hnf].
          * cbn [str_blocks map fst]. intros [E|[]]. destruct ADD as [_ Hfr]. apply Hfr. rewrite E. apply in_map_iff. exists x. split; [reflexivity | exact Hx1].
        + intros x [<-|[]]. exact HIn'.
        + intros x Hx'. apply LA' in Hx'. destruct Hx' as [<-|[Hx1 Hnf]]; [left; left; reflexivity | right].
          destruct (XF3 x Hx1) as [Hb|Hok]; [|exact Hok]. exfalso. apply Hnf. apply in_map_iff. exists x. split; [reflexivity | exact Hb].
      -
        intros a [Ha|[Hne Ha]]; [exact (xi_junk0 a Ha)|].
        destruct (M1blk a Ha) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
        intros q k HIn0 Hnb Hqk. destruct (XF1 (q, k) HIn0 Hnb) as [HIn1 Hnf].
        destruct m1 as [|d1 a1]; [destruct Ha|]. cbn in Ha, Hnf. unfold zwin in Ha.
        destruct (Hblk d1 a1 eq_refl) as (HIn1' & _).
        assert (Hne1 : q <> d1) by (intros ->; apply Hnf; left; reflexivity).
        destruct (ai_live_disjoint MI A1 M1 model1 q k d1 a1 xi_ai0 HIn1 HIn1' Hne1); lia.
      -
        assert (E12 : eff MI A1 A' M1 M' W (fun a => zwin sb (sb + 104) a \/ sbuf_fp m1 a \/ zwin d' (d' + g) a)).
        { eapply (eff_widen MI); [exact EFF | unfold W; cbn [fst snd]; lia | unfold W; cbn [fst snd]; lia]. }
        assert (WUN : forall a, W_of W a -> ~ owned MI A' a).
        { intros a Ha. unfold W, W_of in Ha. cbn [fst snd] in Ha. apply (hi_unowned MI A' M' model'); [exact AI' | lia]. }
        pose proof (eff_trans _ _ _ _ _ _ _ _ _ _ xi_eff0 E12 WUN) as E02. cbn beta in E02.
        eapply eff_weaken; [exact E02|]. intros a Ha. cbn [sbuf_fp].
        destruct Ha as [[Ha|[Ha|[Ha|Ha]]]|[Ha|[Ha|Ha]]]; try tauto.
        + destruct (sbuf_eq_dec m1 m0) as [->|Hne]; [right; left; exact Ha | right; right; right; right; split; [exact Hne | exact Ha]].
        + destruct (sbuf_eq_dec m1 m0) as [->|Hne]; [right; left; exact Ha | right; right; right; right; split; [exact Hne | exact Ha]].
    Qed.

    Lemma xinv_chunk : forall i A1 M1 model1 m1 pp1 hm1 J (k : Z) (bsk : list byte),
      xinv i A1 M1 model1 m1 pp1 hm1 J -> 0 <= i -> 0 < k -> w0 + i + k <= str_cap m1 -> i + k <= n ->
      Z.of_nat (length bsk) = k ->
      let M3 := wbytes (wbytes M1 (Z_to_bv 64 (str_data (sb + 64) m1 + (w0 + i))) bsk)
                       (Z_to_bv 64 (sb + 48)) (word_to_le_bytes 8 (Z_to_bv 64 (pp1 + k))) in
      xinv (i + k) A1 M3 model1 m1 (pp1 + k) hm1 J.
    Proof using AC MI ST MALLOC_STACK_pos RI RI_mono A0 s R0 M0 model0 sp ret sb src n m0 pp0 bs CB Hsb0 Hsb1 Hn SRC Hsrc.
      intros i A1 M1 model1 m1 pp1 hm1 J k bsk XI Hi Hk Hroom Hik Hlen M3.
      pose proof ctx_bounds as (Hceil & Hsphi & Hsp16 & Hretr & Hwin). destruct XI.
      assert (HXS : XS_STK = 208 + (16 + MALLOC_STACK MI)) by (unfold XS_STK, OVF_STK, NEW_STACK; lia).
      pose proof ac_bounds_lit as Hcv.
      destruct (sb_data_mdef A1 M1 model1 m1 pp1 hm1 xi_ai0 xi_sb0 xi_sbdef0) as (HDdat & Hdat0 & Hdat1 & Hblk).
      set (dat := str_data (sb + 64) m1) in *. set (cap1 := str_cap m1) in *.
      assert (DPOS : (dat = sb + 65 /\ cap1 = 22) \/ (dat + cap1 + 1 <= alloc_ceiling /\ 0 < dat)).
      { subst dat cap1. destruct m1 as [|d1 a1]; cbn [str_data str_cap]; [left; unfold SSO_CAP; lia | right].
        destruct (Hblk d1 a1 eq_refl) as (_ & Hc1 & Hp1 & Hcap). cbn [str_cap] in Hcap. lia. }
      destruct xi_sb0 as [F0 F8 F16 F24 F32 (cs & STR & HL) F40 F48 F56 Hpp F88 Hhm F96]. cbn [str_data str_cap] in *.

      set (G := fun a => (dat + (w0 + i) <= a < dat + (w0 + i) + k) \/ (sb + 48 <= a < sb + 56)).
      assert (STO : stores_in G M1 M3).
      { subst M3. eapply stores_in_wbytes_more; [apply stores_in_wbytes | | |];
          rewrite ?length_N_to_le_bytes, ?Hlen; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros x Hx; subst G; cbn beta; lia. }
      assert (GF : forall a, G a -> zwin sb (sb + 104) a \/ sbuf_fp m1 a).
      { intros a [Ha|Ha]; [|left; unfold zwin; lia]. subst dat cap1. destruct m1 as [|d1 a1]; cbn [str_data str_cap sbuf_fp] in *.
        - left. unfold zwin, SSO_CAP in *. lia.
        - right. destruct (Hblk d1 a1 eq_refl) as (_ & _ & _ & Hc1). unfold zwin. lia. }
      assert (GNO : forall a, G a -> ~ owned MI A1 a /\ ~ in_ranges (ly_img Ly.L) a).
      { intros a Ha. destruct (GF a Ha) as [Hs|Hb].
        - unfold zwin in Hs. split; [apply (hi_unowned MI A1 M1 model1); [exact xi_ai0 | lia] | apply hi_offimg; lia].
        - destruct m1 as [|d1 a1]; [destruct Hb|]. cbn in Hb. unfold zwin in Hb. destruct (Hblk d1 a1 eq_refl) as (HIn1 & _).
          split; [eapply (live_unowned _ _ MI); [exact xi_ai0 | exact HIn1 | lia] | eapply (live_offimg _ _ MI); [exact xi_ai0 | exact HIn1 | lia]]. }
      assert (AG : forall lo hi, (hi <= dat + (w0 + i) \/ dat + (w0 + i) + k <= lo) -> (hi <= sb + 48 \/ sb + 56 <= lo) -> 0 <= lo -> hi <= 2 ^ 64 ->
                   agree_on (zwin lo hi) M1 M3).
      { intros lo hi H1 H2 H3 H4. eapply stores_in_agree; [exact STO|]. intros a Ha. subst G. unfold zwin in *. cbn beta. lia. }
      assert (T : forall a (kk : nat) v, (a + Z.of_nat kk <= dat + (w0 + i) \/ dat + (w0 + i) + k <= a) -> (a + Z.of_nat kk <= sb + 48 \/ sb + 56 <= a) ->
                  0 <= a -> a + Z.of_nat kk < 2 ^ 64 -> fld SEGS M1 a kk v -> fld SEGS M3 a kk v).
      { intros a kk v H1 H2 H3 H4 HF. eapply fld_agree; [lia | lia | exact HF | apply AG; lia]. }
      constructor.
      - eapply stores_in_ainv; [exact xi_ai0 | exact STO | intros a Ha; exact (proj1 (GNO a Ha))].
      - exact xi_ms0. - exact xi_fs0. - exact xi_fds0.
      - eapply stores_in_sx; [exact xi_sx0 | exact STO |]. intros a Ha. pose proof (proj2 (GNO a Ha)) as Hni.
        split; [intros Hs; apply Hni; apply ly_rw_img; apply (sx_region_rw ST); exact Hs | intros Hr; apply Hni; apply ly_relro_img; exact Hr].
      - eapply ro_clear_frame; [exact xi_roc0 | eapply stores_in_frame_eq; [exact STO | intros a Ha; exact Ha] |].
        intros a (Himg & _) Hg. exact (proj2 (GNO a Hg) Himg).
      - exact xi_caps0. - exact xi_big0.
      -
        assert (Hpp1 : pp1 = dat + (w0 + i)) by lia.
        constructor; cbn [str_data str_cap]; fold dat; fold cap1.
        + apply T; [cbn; lia | cbn; lia | lia | cbn; lia | exact F0].
        + apply T; [cbn; lia | cbn; lia | lia | cbn; lia | exact F8].
        + apply T; [cbn; lia | cbn; lia | lia | cbn; lia | exact F16].
        + apply T; [cbn; lia | cbn; lia | lia | cbn; lia | exact F24].
        + apply T; [cbn; lia | cbn; lia | lia | cbn; lia | exact F32].
        + destruct (str_rep_wblob _ _ MI A1 M1 (sb + 64) m1 cs (w0 + i) bsk STR ltac:(lia) ltac:(rewrite HL; lia)) as (cs2 & STR2 & HL2).
          exists cs2. split; [|rewrite HL2; exact HL]. subst M3. eapply str_frame; [exact STR2|].
          eapply stores_in_agree; [apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; [lia | lia | intros x Hx; exact Hx]|].
          intros a Ha. cbn beta. unfold str_fp, zwin in Ha. fold dat in Ha. rewrite HL2, HL in Ha.
          destruct Ha as [Ha|Ha]; [lia|]. subst dat cap1. destruct m1 as [|d1 a1]; [destruct Ha | cbn [str_data str_cap] in *].
          destruct (Hblk d1 a1 eq_refl) as (HIn1 & Hc1 & _). lia.
        + apply T; [cbn; lia | cbn; lia | lia | cbn; lia | exact F40].
        + unfold fld. subst M3. peel.
        + apply T; [cbn; lia | cbn; lia | lia | cbn; lia | exact F56].
        + lia.
        + apply T; [cbn; lia | cbn; lia | lia | cbn; lia | exact F88].
        + lia.
        + apply T; [cbn; lia | cbn; lia | lia | cbn; lia | exact F96].
      - fold dat. lia.
      - replace (w0 + (i + k)) with (w0 + i + k) by lia. eapply RI_mono; [exact xi_ri0 | lia].
      - eapply slots_agree; [exact xi_slots0 | cbn; lia | lia | cbn [length SV Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]; apply AG; lia].
      - eapply stores_in_mdef; [exact STO | exact xi_win0].
      - rewrite <- xi_src0. apply rdn_ext; [rewrite u64_of_Z by lia; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia.
        apply (proj1 STO). intros Hg. destruct (SRC (bv_unsigned x) ltac:(lia)) as [Hnsb Hsrc3].
        destruct (GF _ Hg) as [Hs|Hb]; [exact (Hnsb Hs)|].
        destruct m1 as [|d1 a1]; [destruct Hb|]. cbn in Hb. unfold zwin in Hb. destruct (Hblk d1 a1 eq_refl) as (HIn1 & Hc1 & _).
        destruct Hsrc3 as [Hst|[Hro|(q & kq & HIn0 & Hqk & Hnb)]]; [lia | |].
        + apply (live_offimg _ _ MI A1 M1 model1 d1 a1 (bv_unsigned x) xi_ai0 HIn1 ltac:(lia)). exact (proj1 Hro).
        + destruct xi_xfer0 as (XF1 & _ & _). destruct (XF1 (q, kq) HIn0 Hnb) as [HIn1' Hnf]. cbn in Hnf.
          assert (Hne : q <> d1) by (intros ->; apply Hnf; left; reflexivity).
          destruct (ai_live_disjoint MI A1 M1 model1 q kq d1 a1 xi_ai0 HIn1' HIn1 Hne); lia.
      - eapply stores_in_mdef; [exact STO | exact xi_sbdef0].
      - exact xi_xfer0.
      - exact xi_junk0.
      - assert (E13 : eff MI A1 A1 M1 M3 W (fun a => zwin sb (sb + 104) a \/ sbuf_fp m1 a)).
        { eapply (eff_of_stores MI); [exact STO|]. intros a Ha. left. exact (GF a Ha). }
        assert (WUN : forall a, W_of W a -> ~ owned MI A1 a).
        { intros a Ha. unfold W, W_of in Ha. cbn [fst snd] in Ha. apply (hi_unowned MI A1 M1 model1); [exact xi_ai0 | lia]. }
        pose proof (eff_trans _ _ _ _ _ _ _ _ _ _ xi_eff0 E13 WUN) as E03. cbn beta in E03.
        eapply eff_weaken; [exact E03|]. intros a Ha. cbn beta in Ha. tauto.
    Qed.

    Lemma x_exit : forall A1 R1 M1 model1 m1 pp1 hm1 J,
      xinv n A1 M1 model1 m1 pp1 hm1 J -> xregs R1 n ->
      srealizes SEGS (cfg fx R1 XS_EXIT M1 model1) K.
    Proof using AC MI ST MALLOC_STACK_pos RI fx A0 s R0 M0 model0 sp ret sb src n m0 pp0 bs K CB CONT.
      intros A1 R1 M1 model1 m1 pp1 hm1 J XI (Y2 & Y3 & Y4 & Y8 & Y9 & Y18 & Y19 & Y21 & YS).
      pose proof CB as CB1. destruct CB1 as [AI MS ROC' SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
      destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp]. cbn [ly_gp ly_tp Ly.L] in Hgp, Htp, Y3, Y4.
      unfold XS_STK, OVF_STK, NEW_STACK in *. pose proof ac_bounds_lit as Hcv.
      destruct XI.
      set (E := Eseed R1 [Z_to_bv 64 ret; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv; getr R0 19%bv; getr R0 20%bv; getr R0 21%bv]).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1
        [KRange (EVar 2) (2 ^ 16) (2 ^ 47);
         KWord (SA (EVar 2) 56) (N.to_nat 8) (EVar 32); KWord (SA (EVar 2) 48) (N.to_nat 8) (EVar 33);
         KWord (SA (EVar 2) 40) (N.to_nat 8) (EVar 34); KWord (SA (EVar 2) 32) (N.to_nat 8) (EVar 35);
         KWord (SA (EVar 2) 24) (N.to_nat 8) (EVar 36); KWord (SA (EVar 2) 16) (N.to_nat 8) (EVar 37);
         KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 38)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - krv Y2.
        - kwv (xi_slots0 0%nat ltac:(cbn; lia)) Y2.
        - kwv (xi_slots0 1%nat ltac:(cbn; lia)) Y2.
        - kwv (xi_slots0 2%nat ltac:(cbn; lia)) Y2.
        - kwv (xi_slots0 3%nat ltac:(cbn; lia)) Y2.
        - kwv (xi_slots0 4%nat ltac:(cbn; lia)) Y2.
        - kwv (xi_slots0 5%nat ltac:(cbn; lia)) Y2.
        - kwv (xi_slots0 6%nat ltac:(cbn; lia)) Y2. }
      xruns HR HK FUEL [XS_RETPC] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename R' into R2. rename HR' into HR2.
      regval HR2 (1%bv : reg) ret V1. regval HR2 (10%bv : reg) n V10.
      eapply srz_msteps; [exact (ms_halt _ xi_ms0) | exact (ms_lazy _ xi_ms0) | apply (ret_at SEGS XS_RETPC R2 M1 _ (Z_to_bv 64 ret) ltac:(vm_refl_bv) V1 Hret) |].
      apply (CONT A1 R2 M1 model1 m1 pp1 hm1 J); try assumption.
      constructor; try assumption. intros r Hr. unfold callee_saved in Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [kept_chain HR2 YS|]). destruct Hr.
    Qed.

    Lemma x_full : forall i A1 R1 M1 model1 m1 pp1 hm1 J,
      (forall A2 R2 M2 model2 m2 pp2 hm2 J2,
          xinv (i + 1) A2 M2 model2 m2 pp2 hm2 J2 -> xregs R2 (i + 1) -> i + 1 < n ->
          srealizes SEGS (cfg fx R2 XS_LOOP M2 model2) K) ->
      xinv i A1 M1 model1 m1 pp1 hm1 J -> xregs R1 i -> 0 <= i < n -> w0 + i = str_cap m1 ->
      srealizes SEGS (cfg fx R1 XS_LOOP M1 model1) K.
    Proof using AC MI ST MALLOC_STACK_pos NEW RI RI_grow RI_step fx A0 s R0 M0 model0 sp ret sb src n m0 pp0 bs K CB Hsb0 Hsb1 Hn SRC Hsrc BUD CONT.
      intros i A1 R1 M1 model1 m1 pp1 hm1 J IH XI XR Hi FULL.
      pose proof XR as (Y2 & Y3 & Y4 & Y8 & Y9 & Y18 & Y19 & Y21 & YS).
      pose proof ctx_bounds as (Hceil & Hsphi & Hsp16 & Hretr & Hwin).
      pose proof CB as CB1. destruct CB1 as [_ _ _ _ SXH _ _ _ _ Hown_sx Herr_sx].
      pose proof XI as XI0. destruct XI.
      assert (HXS : XS_STK = 208 + (16 + MALLOC_STACK MI)) by (unfold XS_STK, OVF_STK, NEW_STACK; lia).
      assert (HOV : OVF_STK MI = 144 + (16 + MALLOC_STACK MI)) by (unfold OVF_STK, NEW_STACK; lia).
      pose proof ac_bounds_lit as Hcv. cbn [ly_gp ly_tp Ly.L] in Y3, Y4.
      destruct (sb_data_mdef A1 M1 model1 m1 pp1 hm1 xi_ai0 xi_sb0 xi_sbdef0) as (HDdat & Hdat0 & Hdat1 & Hblk).
      set (dat := str_data (sb + 64) m1) in *. set (cap1 := str_cap m1) in *.
      pose proof xi_sb0 as SB1. destruct xi_sb0 as [F0 F8 F16 F24 F32 (cs & STR & HL) F40 F48 F56 Hpp F88 Hhm F96]. cbn [str_data str_cap] in *.
      fold dat in F40, F48, F56, Hpp, Hhm. fold cap1 in F56, Hpp, Hhm, HL.

      set (cb := nth (Z.to_nat i) bs (Z_to_bv 8 0)).
      assert (Hlenbs : length bs = Z.to_nat n) by (exact (rdn_length _ _ _ _ _ xi_src0)).
      assert (CB8 : cellw SEGS M1 (src + i) 1 (bv_unsigned cb)).
      { split; [pose proof (u8_range cb); cbn; lia|]. change (N.to_nat 1) with 1%nat.
        pose proof (rdn_sub SEGS M1 (Z.to_nat n) (Z_to_bv 64 src) bs (Z.to_nat i) 1 xi_src0 ltac:(lia)) as X.
        unfold at_ in X. rewrite u64_of_Z in X by lia. replace (src + Z.of_nat (Z.to_nat i)) with (src + i) in X by lia.
        etransitivity; [exact X|]. rewrite (sub_1 bs (Z.to_nat i) (Z_to_bv 8 0)) by lia. subst cb.
        rewrite SeqExec.N_to_le_bytes_1_small. pose proof (u8_range (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
        rewrite u64_of_Z by lia. rewrite Z_to_bv_bv_unsigned. reflexivity. }
      pose proof (u8_range cb) as Hcb8.

      assert (F48' : fld SEGS M1 (sb + 48) 8 (dat + cap1)) by (replace (dat + cap1) with pp1 by lia; exact F48).
      set (E := Eseed R1 [Z_to_bv 64 (dat + cap1); Z_to_bv 64 (bv_unsigned cb)]).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1
        [KRange (EVar 2) (2 ^ 16) (2 ^ 47); KRange (EVar 19) 0 (2 ^ 47 - 104); KRange (EVar 18) 0 (2 ^ 47);
         KWord (SA (EVar 19) 0) (N.to_nat 8) (ELit VT_SB);
         KWord (SA (EVar 19) 48) (N.to_nat 8) (EVar 32); KWord (SA (EVar 19) 56) (N.to_nat 8) (EVar 32);
         KWord (SA (EVar 18) 0) (N.to_nat 1) (EVar 33); KRange (EVar 33) 0 255;
         KImg 0xe8000 0xef000]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - krv Y2. - krv Y19. - krv Y18.
        - eapply (kword_var _ _ _ _ sb); [eapply fld_cellw; [fld_fix F0 | unfold VT_SB; cbn; lia] | cbn; lia | evs; exact Y19 | lia | lia | cbn; lia | evs; reflexivity ].
        - kwv F48' Y19. - kwv F56 Y19. - kwv CB8 Y18.
        - eapply krange_var; [evs; reflexivity | lia | lia].
        - apply kimg_of_clear; [lia | lia |]. intros a Ha. apply (sx_relro ST s M1 a xi_sx0).
          exists 0xe8000, 0xef000. split; [left; reflexivity | lia]. }
      xruns HR HK FUEL [A_SB_OVERFLOW] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename R' into R2. rename HR' into HR2.
      regval HR2 (1%bv : reg) XS_RETOV X1. regval HR2 (2%bv : reg) (sp - 64) X2. regval HR2 (3%bv : reg) (ly_gp Ly.L) X3.
      regval HR2 (4%bv : reg) (ly_tp Ly.L) X4. regval HR2 (10%bv : reg) sb X10. regval HR2 (11%bv : reg) (bv_unsigned cb) X11.
      regval HR2 (8%bv : reg) i X8. regval HR2 (9%bv : reg) n X9. regval HR2 (18%bv : reg) (src + i) X18.
      regval HR2 (19%bv : reg) sb X19. regval HR2 (21%bv : reg) (2 ^ 64 - 1) X21.
      assert (Y2S : forall r, In r [22; 23; 24; 25; 26; 27]%bv -> getr R2 r = getr R0 r).
      { intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR2 YS|]). destruct Hr. }
      destruct (RI_grow A1 M1 model1 m1 (w0 + i) xi_ai0 xi_ri0 FULL ltac:(lia)) as (HNMAX & ROOM).
      apply (sb_overflow MI ST MALLOC_STACK_pos NEW fx A1 s R2 M1 model1 (sp - 64) XS_RETOV sb (bv_unsigned cb) m1 pp1 hm1 K).
      -   constructor.
        + exact xi_ai0. + exact xi_ms0.
        + exact (img_ro_clear_of' ST s M1 xi_roc0 xi_sx0).
        + exact xi_sx0. + exact SXH.
        + constructor; [exact X1 | apply bv_eq; vm_compute; reflexivity | unfold XS_RETOV; lia | exact X2 | mlia | lia | exact X3 | exact X4].
        + lia.
        + unfold stack_room. rewrite HOV. apply (mdef_store_ok_off SEGS M1 (sp - XS_STK) XS_STK 0); [exact xi_win0 | lia | lia | lia | lia] || (replace (sp - 64 - (144 + (16 + MALLOC_STACK MI))) with (sp - XS_STK + 0) by lia;
             apply (mdef_store_ok_off SEGS M1 (sp - XS_STK) XS_STK 0); [exact xi_win0 | lia | lia | lia | lia]).
        + intros a Ha. split; [apply (hi_unowned MI A1 M1 model1); [exact xi_ai0 | unfold zwin in Ha; lia] | apply (proj2 (Hwin a ltac:(unfold zwin in *; lia)))].
        + exact (own_sx_via_eff _ _ _ _ _ _ xi_eff0 Hown_sx). + exact Herr_sx.
      - exact xi_roc0.
      - exact X10. - exact X11. - lia.
      - exact SB1.
      - cbn [str_data str_cap]. lia.
      - lia. - lia. - exact xi_sbdef0.
      - exact HNMAX. - exact ROOM.
      -
        intros A' R' M' model' d' RB Ha0 SB' HDsb' LAP EFF.
        pose proof RB as RB0. destruct RB as [AI' MS' FS' FDS' SX' KEPT].
        pose proof (xinv_grow i A1 M1 model1 m1 pp1 hm1 J A' M' model' d' XI0 Hi FULL AI' MS' FS' FDS' SX' SB' HDsb' LAP EFF) as XI1.
        assert (R'2 : getr R' 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KEPT 2%bv) by inl; exact X2).
        assert (R'8 : getr R' 8%bv = Z_to_bv 64 i) by (rewrite (KEPT 8%bv) by inl; exact X8).
        assert (R'9 : getr R' 9%bv = Z_to_bv 64 n) by (rewrite (KEPT 9%bv) by inl; exact X9).
        assert (R'18 : getr R' 18%bv = Z_to_bv 64 (src + i)) by (rewrite (KEPT 18%bv) by inl; exact X18).
        assert (R'21 : getr R' 21%bv = Z_to_bv 64 (2 ^ 64 - 1)) by (rewrite (KEPT 21%bv) by inl; exact X21).
        assert (R'3 : getr R' 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT 3%bv) by inl; exact X3).
        assert (R'4 : getr R' 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT 4%bv) by inl; exact X4).
        assert (R'19 : getr R' 19%bv = Z_to_bv 64 sb) by (rewrite (KEPT 19%bv) by inl; exact X19).
        cbn [ly_gp ly_tp Ly.L] in R'3, R'4.
        set (E3 := Eseed R' []).
        assert (HR3 : regs_ok E3 sr_id R') by (apply regs_ok_seed).
        assert (HK3 : know_ok SEGS E3 M' [KRange (EVar 10) 0 255; KRange (EVar 8) 0 (2 ^ 47); KRange (EVar 9) 0 (2 ^ 47);
                                           KRange (EVar 21) (2 ^ 64 - 1) (2 ^ 64 - 1)]).
        { repeat apply Forall_cons; try apply Forall_nil; [krv Ha0 | krv R'8 | krv R'9 | krv R'21]. }
        destruct (Z.lt_ge_cases (i + 1) n) as [Hlt | Hge].
        + xruns HR3 HK3 FUEL [XS_LOOP; XS_EXIT] (SCR [true] [] []) 40%N.
          { scs_auto. }
          clear HK3. rename R'0 into R4. rename HR' into HR4.
          apply (IH A' R4 M' model' _ _ _ _ XI1); [|exact Hlt].
          unfold xregs. cbn [ly_gp ly_tp Ly.L].
          regval HR4 (2%bv : reg) (sp - 64) Z2. regval HR4 (3%bv : reg) 67584 Z3. regval HR4 (4%bv : reg) 1057816 Z4.
          regval HR4 (8%bv : reg) (i + 1) Z8. regval HR4 (9%bv : reg) n Z9. regval HR4 (18%bv : reg) (src + (i + 1)) Z18.
          regval HR4 (19%bv : reg) sb Z19. regval HR4 (21%bv : reg) (2 ^ 64 - 1) Z21.
          repeat (split; [assumption|]).
          intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR4 KEPT Y2S|]). destruct Hr.
        + xruns HR3 HK3 FUEL [XS_LOOP; XS_EXIT] (SCR [false] [] []) 40%N.
          { scs_auto. }
          clear HK3. rename R'0 into R4. rename HR' into HR4.
          replace (i + 1) with n in XI1 by lia.
          apply (x_exit A' R4 M' model' _ _ _ _ XI1).
          unfold xregs. cbn [ly_gp ly_tp Ly.L].
          regval HR4 (2%bv : reg) (sp - 64) Z2. regval HR4 (3%bv : reg) 67584 Z3. regval HR4 (4%bv : reg) 1057816 Z4.
          regval HR4 (8%bv : reg) n Z8. regval HR4 (9%bv : reg) n Z9. regval HR4 (18%bv : reg) (src + n) Z18.
          regval HR4 (19%bv : reg) sb Z19. regval HR4 (21%bv : reg) (2 ^ 64 - 1) Z21.
          repeat (split; [assumption|]).
          intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR4 KEPT Y2S|]). destruct Hr.
    Qed.

    Lemma ivl_disj : forall p q k, 0 < k -> (forall a, p <= a < p + k -> q <= a < q + k -> False) -> p + k <= q \/ q + k <= p.
    Proof using sb m0 pp0.
      intros p q k Hk H. destruct (Z.lt_ge_cases q p).
      - right. destruct (Z.lt_ge_cases p (q + k)); [|lia]. exfalso. apply (H p); lia.
      - left. destruct (Z.lt_ge_cases q (p + k)); [|lia]. exfalso. apply (H q); lia.
    Qed.

    Lemma x_chunk : forall i k A1 R2 M1 model1 m1 pp1 hm1 J,
      (forall i2 A2 R3 M2 model2 m2 pp2 hm2 J2,
          xinv i2 A2 M2 model2 m2 pp2 hm2 J2 -> xregs R3 i2 -> i < i2 < n ->
          srealizes SEGS (cfg fx R3 XS_LOOP M2 model2) K) ->
      xinv i A1 M1 model1 m1 pp1 hm1 J -> 0 <= i < n -> 0 < k -> i + k <= n -> w0 + i + k <= str_cap m1 ->
      getr R2 1%bv = Z_to_bv 64 XS_RETMM -> getr R2 10%bv = Z_to_bv 64 pp1 -> getr R2 11%bv = Z_to_bv 64 (src + i) ->
      getr R2 12%bv = Z_to_bv 64 k -> getr R2 20%bv = Z_to_bv 64 k -> xregs R2 i ->
      srealizes SEGS (cfg fx R2 MEMMOVE M1 model1) K.
    Proof using AC MI ST MALLOC_STACK_pos RI RI_mono fx A0 s R0 M0 model0 sp ret sb src n m0 pp0 bs K CB Hsb0 Hsb1 Hn SRC Hsrc CONT.
      intros i k A1 R2 M1 model1 m1 pp1 hm1 J IH XI Hi Hk Hik Hroom X1 X10 X11 X12 X20 XR.
      pose proof XR as (Y2 & Y3 & Y4 & Y8 & Y9 & Y18 & Y19 & Y21 & YS).
      pose proof ctx_bounds as (Hceil & Hsphi & Hsp16 & Hretr & Hwin).
      pose proof XI as XI0. destruct XI.
      assert (HXS : XS_STK = 208 + (16 + MALLOC_STACK MI)) by (unfold XS_STK, OVF_STK, NEW_STACK; lia).
      pose proof ac_bounds_lit as Hcv. cbn [ly_gp ly_tp Ly.L] in Y3, Y4.
      destruct (sb_data_mdef A1 M1 model1 m1 pp1 hm1 xi_ai0 xi_sb0 xi_sbdef0) as (HDdat & Hdat0 & Hdat1 & Hblk).
      set (dat := str_data (sb + 64) m1) in *. set (cap1 := str_cap m1) in *.
      pose proof xi_sb0 as SB1. destruct xi_sb0 as [F0 F8 F16 F24 F32 (cs & STR & HL) F40 F48 F56 Hpp F88 Hhm F96]. cbn [str_data str_cap] in *.
      fold dat in F40, F48, F56, Hpp, Hhm. fold cap1 in F56, Hpp, Hhm, HL.
      assert (DPOS : (dat = sb + 65 /\ cap1 = 22) \/ (dat + cap1 + 1 <= alloc_ceiling /\ 0 < dat)).
      { subst dat cap1. destruct m1 as [|d1 a1]; cbn [str_data str_cap]; [left; unfold SSO_CAP; lia | right].
        destruct (Hblk d1 a1 eq_refl) as (_ & Hc1 & Hp1 & Hcap). cbn [str_cap] in Hcap. lia. }
      assert (Hlenbs : length bs = Z.to_nat n) by (exact (rdn_length _ _ _ _ _ xi_src0)).
      set (bsk := sub bs (Z.to_nat i) (Z.to_nat k)).
      assert (Hlenk : length bsk = Z.to_nat k) by (subst bsk; apply sub_length; lia).

      assert (DISJ : forall a, pp1 <= a < pp1 + k -> src + i <= a < src + i + k -> False).
      { intros a Ha Hs. destruct (SRC a ltac:(lia)) as (Hnsb & Hcase). subst dat cap1.
        destruct m1 as [|d1 a1]; cbn [str_data str_cap] in *.
        - apply Hnsb. unfold zwin, SSO_CAP in *. lia.
        - destruct (Hblk d1 a1 eq_refl) as (HIn1 & Hc1 & Hp1 & Hcap).
          destruct Hcase as [Hst|[Hro|(q & kq & HIn0 & Hqk & Hnb)]]; [lia | |].
          + apply (live_offimg _ _ MI A1 M1 model1 d1 a1 a xi_ai0 HIn1 ltac:(lia)). exact (proj1 Hro).
          + destruct xi_xfer0 as (XF1 & _ & _). destruct (XF1 (q, kq) HIn0 Hnb) as [HIn1' Hnf]. cbn in Hnf.
            assert (Hne : q <> d1) by (intros ->; apply Hnf; left; reflexivity).
            destruct (ai_live_disjoint MI A1 M1 model1 q kq d1 a1 xi_ai0 HIn1' HIn1 Hne); lia. }
      assert (MC : mcH SEGS M1 (Z_to_bv 64 pp1) (Z_to_bv 64 (src + i)) k bsk).
      { constructor.
        - lia. - exact Hlenk.
        - rewrite Hlenk. pose proof (rdn_sub SEGS M1 (Z.to_nat n) (Z_to_bv 64 src) bs (Z.to_nat i) (Z.to_nat k) xi_src0 ltac:(lia)) as X.
          unfold at_ in X. rewrite u64_of_Z in X by lia. replace (src + Z.of_nat (Z.to_nat i)) with (src + i) in X by lia. exact X.
        - rewrite Hlenk. replace (Z_to_bv 64 pp1) with (Z_to_bv 64 (dat + (pp1 - dat))) by (f_equal; lia).
          apply (mdef_store_ok_off SEGS M1 dat (cap1 + 1) (pp1 - dat) (Z.to_nat k)); [exact HDdat | lia | lia | lia | lia].
        - rewrite !u64_of_Z by lia. apply ivl_disj; [lia | exact DISJ].
        - rewrite u64_of_Z by lia. lia.
        - rewrite u64_of_Z by lia. lia. }
      destruct (u1_memmove_spec fx M1 (Z_to_bv 64 pp1) (Z_to_bv 64 (src + i)) k bsk (seg_rom SEGS) R2 (Z_to_bv 64 XS_RETMM)
                  MC Hk ltac:(apply bv_eq; vm_compute; reflexivity) X1 X10 X11 X12) as (R3 & MS3 & KP3).
      eapply srz_msteps; [exact (ms_halt _ xi_ms0) | exact (ms_lazy _ xi_ms0) | exact MS3 |]. clear MS3.
      set (M2 := wbytes M1 (Z_to_bv 64 pp1) bsk) in *.

      assert (Z2 : getr R3 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KP3 2%bv) by inl; exact Y2).
      assert (Z8 : getr R3 8%bv = Z_to_bv 64 i) by (rewrite (KP3 8%bv) by inl; exact Y8).
      assert (Z9 : getr R3 9%bv = Z_to_bv 64 n) by (rewrite (KP3 9%bv) by inl; exact Y9).
      assert (Z18 : getr R3 18%bv = Z_to_bv 64 (src + i)) by (rewrite (KP3 18%bv) by inl; exact Y18).
      assert (Z19 : getr R3 19%bv = Z_to_bv 64 sb) by (rewrite (KP3 19%bv) by inl; exact Y19).
      assert (Z20 : getr R3 20%bv = Z_to_bv 64 k) by (rewrite (KP3 20%bv) by inl; exact X20).
      assert (Z21 : getr R3 21%bv = Z_to_bv 64 (2 ^ 64 - 1)) by (rewrite (KP3 21%bv) by inl; exact Y21).
      assert (Z3 : getr R3 3%bv = Z_to_bv 64 67584) by (rewrite (KP3 3%bv) by inl; exact Y3).
      assert (Z4 : getr R3 4%bv = Z_to_bv 64 1057816) by (rewrite (KP3 4%bv) by inl; exact Y4).
      assert (F48' : fld SEGS M2 (sb + 48) 8 pp1).
      { unfold fld. subst M2. rewrite SumWalkTac.rdn_wbytes_out_Z by (rewrite ?Hlenk; cbn; lia). exact F48. }
      assert (HD2 : mdef M2 sb 104) by (subst M2; apply mdef_wbytes; exact xi_sbdef0).
      set (E := Eseed R3 [Z_to_bv 64 pp1]).
      assert (HR : regs_ok E sr_id R3) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M2
        [KRange (EVar 2) (2 ^ 16) (2 ^ 47); KRange (EVar 19) 0 (2 ^ 47 - 104);
         KRange (EVar 8) 0 (2 ^ 47); KRange (EVar 9) 0 (2 ^ 47); KRange (EVar 20) 0 (2 ^ 47); KRange (EVar 32) 0 (2 ^ 63);
         KWord (SA (EVar 19) 48) (N.to_nat 8) (EVar 32);
         KWr (SA (EVar 19) 0) (ELit 104)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - krv Z2. - krv Z19. - krv Z8. - krv Z9. - krv Z20.
        - eapply krange_var; [evs; reflexivity | lia | lia].
        - kwv F48' Z19.
        - eapply (kwr_of_mdef _ _ _ _ sb 0 104); [evs; exact Z19 | lia | lia | lia | lia | replace (sb + 0) with sb by lia; exact HD2]. }
      destruct (Z.lt_ge_cases (i + k) n) as [Hlt | Hge].
      - xruns HR HK FUEL [XS_LOOP; XS_EXIT] (SCR [false] [] []) 40%N.
        { scs_auto. }
        clear HK. rename HR' into HR4. wnorm_goal.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) end.
        pose proof (xinv_chunk i A1 M1 model1 m1 pp1 hm1 J k bsk XI0 ltac:(lia) Hk ltac:(subst cap1; lia) Hik ltac:(lia)) as XI2.
        cbn zeta in XI2. fold dat in XI2. replace (dat + (w0 + i)) with pp1 in XI2 by lia. fold M2 in XI2.
        replace (Z_to_bv 64 (pp1 + k)) with (Z_to_bv 64 (k + pp1)) in XI2 by (f_equal; lia). fold M3 in XI2.
        apply (IH (i + k) A1 R' M3 model1 _ _ _ _ XI2); [|lia].
        unfold xregs. cbn [ly_gp ly_tp Ly.L].
        regval HR4 (2%bv : reg) (sp - 64) V2. regval HR4 (3%bv : reg) 67584 V3. regval HR4 (4%bv : reg) 1057816 V4.
        regval HR4 (8%bv : reg) (i + k) V8. regval HR4 (9%bv : reg) n V9. regval HR4 (18%bv : reg) (src + (i + k)) V18.
        regval HR4 (19%bv : reg) sb V19. regval HR4 (21%bv : reg) (2 ^ 64 - 1) V21.
        repeat (split; [assumption|]).
        intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR4 KP3 YS|]). destruct Hr.
      - xruns HR HK FUEL [XS_LOOP; XS_EXIT] (SCR [true] [] []) 40%N.
        { scs_auto. }
        clear HK. rename HR' into HR4. wnorm_goal.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) end.
        pose proof (xinv_chunk i A1 M1 model1 m1 pp1 hm1 J k bsk XI0 ltac:(lia) Hk ltac:(subst cap1; lia) Hik ltac:(lia)) as XI2.
        cbn zeta in XI2. fold dat in XI2. replace (dat + (w0 + i)) with pp1 in XI2 by lia. fold M2 in XI2.
        replace (Z_to_bv 64 (pp1 + k)) with (Z_to_bv 64 (k + pp1)) in XI2 by (f_equal; lia). fold M3 in XI2.
        replace (i + k) with n in XI2 by lia.
        apply (x_exit A1 R' M3 model1 _ _ _ _ XI2).
        unfold xregs. cbn [ly_gp ly_tp Ly.L].
        regval HR4 (2%bv : reg) (sp - 64) V2. regval HR4 (3%bv : reg) 67584 V3. regval HR4 (4%bv : reg) 1057816 V4.
        regval HR4 (8%bv : reg) n V8. regval HR4 (9%bv : reg) n V9. regval HR4 (18%bv : reg) (src + n) V18.
        regval HR4 (19%bv : reg) sb V19. regval HR4 (21%bv : reg) (2 ^ 64 - 1) V21.
        repeat (split; [assumption|]).
        intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR4 KP3 YS|]). destruct Hr.
    Qed.

    Lemma x_room : forall i A1 R1 M1 model1 m1 pp1 hm1 J,
      (forall i2 A2 R3 M2 model2 m2 pp2 hm2 J2,
          xinv i2 A2 M2 model2 m2 pp2 hm2 J2 -> xregs R3 i2 -> i < i2 < n ->
          srealizes SEGS (cfg fx R3 XS_LOOP M2 model2) K) ->
      xinv i A1 M1 model1 m1 pp1 hm1 J -> xregs R1 i -> 0 <= i < n -> w0 + i < str_cap m1 ->
      srealizes SEGS (cfg fx R1 XS_LOOP M1 model1) K.
    Proof using AC MI ST MALLOC_STACK_pos RI RI_mono fx A0 s R0 M0 model0 sp ret sb src n m0 pp0 bs K CB Hsb0 Hsb1 Hn SRC Hsrc CONT.
      intros i A1 R1 M1 model1 m1 pp1 hm1 J IH XI XR Hi ROOMY.
      pose proof XR as (Y2 & Y3 & Y4 & Y8 & Y9 & Y18 & Y19 & Y21 & YS).
      pose proof ctx_bounds as (Hceil & Hsphi & Hsp16 & Hretr & Hwin).
      pose proof XI as XI0. destruct XI.
      assert (HXS : XS_STK = 208 + (16 + MALLOC_STACK MI)) by (unfold XS_STK, OVF_STK, NEW_STACK; lia).
      pose proof ac_bounds_lit as Hcv. cbn [ly_gp ly_tp Ly.L] in Y3, Y4.
      destruct (sb_data_mdef A1 M1 model1 m1 pp1 hm1 xi_ai0 xi_sb0 xi_sbdef0) as (HDdat & Hdat0 & Hdat1 & Hblk).
      set (dat := str_data (sb + 64) m1) in *. set (cap1 := str_cap m1) in *.
      destruct xi_sb0 as [F0 F8 F16 F24 F32 (cs & STR & HL) F40 F48 F56 Hpp F88 Hhm F96]. cbn [str_data str_cap] in *.
      fold dat in F40, F48, F56, Hpp, Hhm. fold cap1 in F56, Hpp, Hhm, HL.
      set (E := Eseed R1 [Z_to_bv 64 pp1; Z_to_bv 64 (dat + cap1)]).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1
        [KRange (EVar 2) (2 ^ 16) (2 ^ 47); KRange (EVar 19) 0 (2 ^ 47 - 104); KRange (EVar 18) 0 (2 ^ 47);
         KRange (EVar 8) 0 (2 ^ 47); KRange (EVar 9) 0 (2 ^ 47); KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 33) 0 (2 ^ 63);
         KWord (SA (EVar 19) 48) (N.to_nat 8) (EVar 32); KWord (SA (EVar 19) 56) (N.to_nat 8) (EVar 33)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - krv Y2. - krv Y19. - krv Y18. - krv Y8. - krv Y9.
        - eapply krange_var; [evs; reflexivity | lia | lia].
        - eapply krange_var; [evs; reflexivity | lia | lia].
        - kwv F48 Y19. - kwv F56 Y19. }
      destruct (Z.lt_ge_cases (n - i) (dat + cap1 - pp1)) as [Hlt | Hge].
      - xruns HR HK FUEL [MEMMOVE] (SCR [false; true; false] [] []) 40%N.
        { scs_auto. }
        clear HK. rename R' into R2. rename HR' into HR2.
        regval HR2 (1%bv : reg) XS_RETMM X1. regval HR2 (10%bv : reg) pp1 X10. regval HR2 (11%bv : reg) (src + i) X11.
        regval HR2 (12%bv : reg) (n - i) X12. regval HR2 (20%bv : reg) (n - i) X20.
        apply (x_chunk i (n - i) A1 R2 M1 model1 m1 pp1 hm1 J IH XI0 Hi ltac:(lia) ltac:(lia) ltac:(subst cap1; lia) X1 X10 X11 X12 X20).
        unfold xregs. cbn [ly_gp ly_tp Ly.L].
        regval HR2 (2%bv : reg) (sp - 64) V2. regval HR2 (3%bv : reg) 67584 V3. regval HR2 (4%bv : reg) 1057816 V4.
        regval HR2 (8%bv : reg) i V8. regval HR2 (9%bv : reg) n V9. regval HR2 (18%bv : reg) (src + i) V18.
        regval HR2 (19%bv : reg) sb V19. regval HR2 (21%bv : reg) (2 ^ 64 - 1) V21.
        repeat (split; [assumption|]).
        intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR2 YS|]). destruct Hr.
      - xruns HR HK FUEL [MEMMOVE] (SCR [false; false; false] [] []) 40%N.
        { scs_auto. }
        clear HK. rename R' into R2. rename HR' into HR2.
        regval HR2 (1%bv : reg) XS_RETMM X1. regval HR2 (10%bv : reg) pp1 X10. regval HR2 (11%bv : reg) (src + i) X11.
        regval HR2 (12%bv : reg) (dat + cap1 - pp1) X12. regval HR2 (20%bv : reg) (dat + cap1 - pp1) X20.
        apply (x_chunk i (dat + cap1 - pp1) A1 R2 M1 model1 m1 pp1 hm1 J IH XI0 Hi ltac:(lia) ltac:(lia) ltac:(subst cap1; lia) X1 X10 X11 X12 X20).
        unfold xregs. cbn [ly_gp ly_tp Ly.L].
        regval HR2 (2%bv : reg) (sp - 64) V2. regval HR2 (3%bv : reg) 67584 V3. regval HR2 (4%bv : reg) 1057816 V4.
        regval HR2 (8%bv : reg) i V8. regval HR2 (9%bv : reg) n V9. regval HR2 (18%bv : reg) (src + i) V18.
        regval HR2 (19%bv : reg) sb V19. regval HR2 (21%bv : reg) (2 ^ 64 - 1) V21.
        repeat (split; [assumption|]).
        intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR2 YS|]). destruct Hr.
    Qed.

    Lemma x_loop : forall i A1 R1 M1 model1 m1 pp1 hm1 J,
      xinv i A1 M1 model1 m1 pp1 hm1 J -> xregs R1 i -> 0 <= i < n ->
      srealizes SEGS (cfg fx R1 XS_LOOP M1 model1) K.
    Proof using AC MI ST MALLOC_STACK_pos NEW RI RI_grow RI_step RI_mono fx A0 s R0 M0 model0 sp ret sb src n m0 pp0 bs K CB Hsb0 Hsb1 Hn SRC Hsrc BUD CONT.
      assert (G : forall d i A1 R1 M1 model1 m1 pp1 hm1 J, n - i <= Z.of_nat d ->
        xinv i A1 M1 model1 m1 pp1 hm1 J -> xregs R1 i -> 0 <= i < n ->
        srealizes SEGS (cfg fx R1 XS_LOOP M1 model1) K).
      { induction d as [|d IHd]; intros i A1 R1 M1 model1 m1 pp1 hm1 J Hd XI XR Hi; [lia|].
        assert (Hw : w0 + i <= str_cap m1).
        { destruct XI. destruct xi_sb0. lia. }
        destruct (Z.lt_ge_cases (w0 + i) (str_cap m1)) as [Hlt|Hge].
        - apply (x_room i A1 R1 M1 model1 m1 pp1 hm1 J); [|exact XI | exact XR | exact Hi | exact Hlt].
          intros i2 A2 R3 M2 model2 m2 pp2 hm2 J2 XI2 XR2 Hi2. apply (IHd i2 A2 R3 M2 model2 m2 pp2 hm2 J2); [lia | exact XI2 | exact XR2 | lia].
        - apply (x_full i A1 R1 M1 model1 m1 pp1 hm1 J); [|exact XI | exact XR | exact Hi | lia].
          intros A2 R2 M2 model2 m2 pp2 hm2 J2 XI2 XR2 Hi2. apply (IHd (i + 1) A2 R2 M2 model2 m2 pp2 hm2 J2); [lia | exact XI2 | exact XR2 | lia]. }
      intros i A1 R1 M1 model1 m1 pp1 hm1 J XI XR Hi. apply (G (Z.to_nat (n - i)) i A1 R1 M1 model1 m1 pp1 hm1 J); [lia | exact XI | exact XR | exact Hi].
    Qed.

    Theorem xsputn :
      getr R0 10%bv = Z_to_bv 64 sb -> getr R0 11%bv = Z_to_bv 64 src -> getr R0 12%bv = Z_to_bv 64 n ->
      srealizes SEGS (cfg fx R0 A_XSPUTN M0 model0) K.
    Proof using AC MI ST MALLOC_STACK_pos NEW RI RI_grow RI_step RI_mono fx A0 s R0 M0 model0 sp ret sb src n m0 pp0 hm0 bs K CB ROC0 SB0 Hsb0 Hsb1 HDsb0 Hn SRC Hsrc RD0 RI0 BUD CONT.
      intros Ha0 Ha1 Ha2.
      pose proof CB as CB1. destruct CB1 as [AI MS ROC' SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
      destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp]. cbn [ly_gp ly_tp Ly.L] in Hgp, Htp.
      assert (HXS : XS_STK = 208 + (16 + MALLOC_STACK MI)) by (unfold XS_STK, OVF_STK, NEW_STACK; lia).
      pose proof ac_bounds_lit as Hcv.
      destruct (sb_data_mdef A0 M0 model0 m0 pp0 hm0 AI SB0 HDsb0) as (HDdat & Hdat0 & Hdat1 & Hblk).
      pose proof SB0 as SB1. destruct SB1 as [F0 F8 F16 F24 F32 (cs & STR & HL) F40 F48 F56 Hpp F88 Hhm F96].
      set (E := Eseed R0 []).
      assert (HR : regs_ok E sr_id R0) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M0
        [KWr (SA (EVar 2) (-64)) (ELit 64); KRange (EVar 2) (2 ^ 16) (2 ^ 47); KRange (EVar 12) 1 (2 ^ 47)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - eapply kwr_stack; [evs; exact Hsp | reflexivity | lia | lia | eapply stack_room_mono; [exact HROOM | lia | lia | lia]].
        - krv Hsp. - krv Ha2. }
      xruns HR HK FUEL [XS_LOOP] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename R' into R1. rename HR' into HR1. wnorm_goal.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) end.
      assert (ST1 : stores_in (zwin (sp - 64) sp) M0 M1) by (subst M1; stores_tower).
      assert (WUN : forall a, zwin (sp - 64) sp a -> ~ owned MI A0 a /\ ~ in_ranges (ly_img Ly.L) a).
      { intros a Ha. unfold zwin in Ha. split; [apply (proj1 (Hwin a ltac:(unfold zwin; lia))) | apply hi_offimg; lia]. }
      assert (HBLK0 : forall blk, In blk (str_blocks m0) -> In blk (live MI A0)).
      { intros blk Hb. destruct m0 as [|d0 a0]; [destruct Hb|]. cbn in Hb. destruct Hb as [<-|[]]. exact (proj1 (Hblk d0 a0 eq_refl)). }
      apply (x_loop 0 A0 R1 M1 model0 m0 pp0 hm0 (fun _ => False)); [| | lia].
      - constructor.
        + eapply stores_in_ainv; [exact AI | exact ST1 | intros a Ha; exact (proj1 (WUN a Ha))].
        + exact MS. + reflexivity. + reflexivity.
        + eapply stores_in_sx; [exact SXI | exact ST1 |]. intros a Ha. pose proof (proj2 (WUN a Ha)) as Hni.
          split; [intros Hs; apply Hni; apply ly_rw_img; apply (sx_region_rw ST); exact Hs | intros Hr; apply Hni; apply ly_relro_img; exact Hr].
        + eapply ro_clear_frame; [exact ROC0 | eapply stores_in_frame_eq; [exact ST1 | intros a Ha; exact Ha] |].
          intros a (Himg & _) Hg. exact (proj2 (WUN a Hg) Himg).
        + reflexivity. + reflexivity.
        + eapply (sb_inv_frame MI A0 A0 M0 M1); [exact SB0 | lia | lia | | exact HBLK0].
          eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold sb_fp, zwin in Ha. unfold zwin.
          destruct Ha as [Ha|Ha]; [lia|]. destruct m0 as [|d0 a0]; [destruct Ha|]. cbn in Ha. destruct (Hblk d0 a0 eq_refl) as (_ & Hc0 & Hp0 & _). lia.
        + cbn [str_data str_cap] in *. subst w0. lia.
        + rewrite Z.add_0_r. exact RI0.
        + subst M1. unfold SV. slots_tower.
        + eapply stores_in_mdef; [exact ST1|]. eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia | intros x Hx; apply ly_noseg; lia].
        + rewrite <- RD0. apply rdn_ext; [rewrite u64_of_Z by lia; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia.
          apply (proj1 ST1). intros Hw. unfold zwin in Hw. destruct (SRC (bv_unsigned x) ltac:(lia)) as [_ Hsrc3].
          destruct Hsrc3 as [Hst|[Hro|(q & kq & HIn0 & Hqk & Hnb)]]; [lia | |].
          * apply (hi_offimg (bv_unsigned x)); [lia | exact (proj1 Hro)].
          * pose proof (live_range _ _ MI A0 M0 model0 q kq AI HIn0). lia.
        + eapply stores_in_mdef; [exact ST1 | exact HDsb0].
        + split; [|split]; [ | exact HBLK0 | ].
          * intros x Hx Hnb. split; [exact Hx|]. intros Hf. destruct m0 as [|d0 a0]; [destruct Hf|]. cbn in Hf. destruct Hf as [Hf|[]].
            apply Hnb. cbn. left. destruct x as [q kq]. cbn in Hf. subst q.
            pose proof (proj1 (Hblk d0 a0 eq_refl)) as HIn0.
            f_equal. symmetry. eapply (NoDup_fst_unique (live MI A0)); [eapply (ai_live_nodup MI); exact AI | exact Hx | exact HIn0].
          * intros x Hx. destruct m0 as [|d0 a0]; [right; split; [exact Hx | intros []]|]. cbn [str_blocks]. destruct x as [q kq].
            destruct (Z.eq_dec q d0) as [->|Hne]; [|right; split; [exact Hx | intros [E|[]]; injection E; lia]].
            destruct (Z.eq_dec kq a0) as [->|Hne2]; [left; left; reflexivity | right; split; [exact Hx | intros [E|[]]; injection E; lia]].
        + intros a [].
        + eapply (eff_of_stores MI); [exact ST1|]. intros a Ha. right. unfold W, W_of. cbn [fst snd]. unfold zwin in Ha. lia.
      - unfold xregs. cbn [ly_gp ly_tp Ly.L].
        regval HR1 (2%bv : reg) (sp - 64) V2. regval HR1 (3%bv : reg) 67584 V3. regval HR1 (4%bv : reg) 1057816 V4.
        regval HR1 (8%bv : reg) 0 V8. regval HR1 (9%bv : reg) n V9. regval HR1 (18%bv : reg) (src + 0) V18.
        regval HR1 (19%bv : reg) sb V19. regval HR1 (21%bv : reg) (2 ^ 64 - 1) V21.
        repeat (split; [assumption|]).
        intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR1|]). destruct Hr.
    Qed.
  End Call.
End Xsputn.
