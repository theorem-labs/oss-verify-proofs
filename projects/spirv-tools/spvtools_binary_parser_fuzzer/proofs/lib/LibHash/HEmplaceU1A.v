(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibBudget FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HStmts HStmtsU1 HWord HUbsan HConstsU1 HCommonU1 HFpu HFpuU1 HFindU1 HEmplaceSU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HEmplaceSU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HEmplaceSU1.U1_code_6a9c4_6ad6c.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition EMP      : Z := 0x6aa04.
Definition NEWE     : Z := 0xe7b34.
Definition NEWR     : Z := 0x6ab94.
Definition FLW_PC   : Z := 0x6abbc.
Definition FCVT1    : Z := 0x6abcc.
Definition FCVT2    : Z := 0x6abd4.
Definition GROW     : Z := 0x6abe4.
Definition FDIV_A   : Z := 0x6abf8.
Definition FDIV_B   : Z := 0x6ac18.
Definition ROUND    : Z := 0x6ac30.
Definition CHK      : Z := 0x6ac3c.
Definition ARG      : Z := 0x6ac5c.
Definition RW       : Z := 0x6adac.
Definition RWR      : Z := 0x6ac7c.
Definition INS      : Z := 0x6acac.
Definition PN_PC    : Z := 0x6acf0.
Definition EMPTYB   : Z := 0x6ad08.
Definition SIZE_PC  : Z := 0x6ad78.
Definition EPI      : Z := 0x6ad88.
Definition RET_PC   : Z := 0x6ada4.
Definition TRAP_PC  : Z := 0x6ada8.

Definition STOPS : list Z :=
  [SRCH; NF_PC; NEWE; NEWR; FLW_PC; FCVT1; FCVT2; 0x6abd8; 0x6abdc; GROW; FDIV_A; 0x6ac00; 0x6ac04; 0x6ac08; FDIV_B; 0x6ac20; 0x6ac24; 0x6ac28;
   ROUND; 0x6ac34; 0x6ac38; CHK; 0x6ac40; 0x6ac44; 0x6ac50; 0x6ac54; 0x6ac68; RW; RWR; INS; PN_PC; EMPTYB; SIZE_PC; EPI; RET_PC; TRAP_PC].

Section EmpU1.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Variables NEW_STACK DEL_STACK : Z.
  Hypothesis NEW_STACK_nn : 0 <= NEW_STACK.
  Hypothesis DEL_STACK_nn : 0 <= DEL_STACK.
  Hypothesis NEW : new_rule_stmt SEGS L MI ST NEW_STACK.
  Hypothesis RWH : rehashw_stmt SEGS L MI ST NEW_STACK DEL_STACK RW.

  Hypothesis HLnew : ly_new L = NEWE.
  Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
  Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
  Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI HLimg_lo HLrw_img HLerr_rw).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI HLimg_lo HLerr_rw).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw).

  Lemma hi_unowned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
  Proof using AC L MI HLimg_lo HLrw_img.
    intros A M model a AI Ha Ho.
    destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw | Hni].
    - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
    - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hni). lia.
  Qed.

  Lemma eff_widen : forall (A A' : AS MI) M M' (W W' : Z * Z) F,
    eff MI A A' M M' W F -> (forall a, W_of W a -> W_of W' a) -> eff MI A A' M M' W' F.
  Proof using AC L MI.
    intros A A' M M' W0 W' F E HW. destruct E as [C B O FR D OI]. constructor; try assumption.
    intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn; try tauto. right; right; right; right; left. apply HW, H.
  Qed.

  Lemma umap_foot_hb : forall {V : Type} NS obj bl bc (ents : list (Z * (Z * V))) a,
    umap_foot NS obj bl bc ents a ->
    (obj <= a < obj + 40) \/ exists b, In b (umap_blocks NS bl bc ents) /\ fst b <= a < fst b + snd b.
  Proof using.
    intros V NS obj bl bc ents a [Hh | [[Hbc Hb] | (p & Hp & Ha)]]; [left; exact Hh | right | right].
    - exists (bl, 8 * bc). split; [| cbn; lia]. unfold umap_blocks. destruct (Z.eqb_spec bc 0); [lia|]. apply in_app_iff. left. left. reflexivity.
    - exists (p, NS). split; [| cbn; lia]. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff.
      apply in_map_iff in Hp. destruct Hp as (e & <- & He). exists e. split; [reflexivity | exact He].
  Qed.

  Lemma roomL_room_for : forall (A : AS MI) M model n,
    ainv MI A M model -> 0 <= n <= NMAX MI -> roomL MI A (live MI A) n -> room_for MI A n.
  Proof using AC L MI.
    intros A M model n AI Hn [HS HBG].
    destruct (Z.lt_ge_cases n (BIG MI)) as [Hs|Hb].
    - destruct (HS Hs) as [H1 H2]. eapply (room_small MI); [exact AI | lia | exact H1 | exact H2].
    - eapply (room_big MI); [exact AI | lia | apply HBG; lia].
  Qed.

  Lemma seg_rom_high : forall (x : word), 0x124000 <= bv_unsigned x -> seg_rom SEGS x = None.
  Proof using.
    intros x Hx. unfold seg_rom, memory_read.
    unfold SEGS, Plain.M.loaded_segments, Ubsan.Ubsan_loaded_segments.
    cbn [find_segment seg_base seg_size Ubsan.Ubsan_segment_000 Ubsan.Ubsan_segment_001 Ubsan.Ubsan_segment_002 Ubsan.Ubsan_segment_003].
    repeat (match goal with |- context [if ?c then _ else _] =>
              replace c with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; cbn; lia) end).
    reflexivity.
  Qed.
  Lemma rdn_defined_high : forall M n a bs, rdn SEGS M (Z_to_bv 64 a) n = Some bs -> 0x124000 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    defined M a (Z.of_nat n).
  Proof using.
    intros M n. induction n as [|n IH]; intros a bs Hr Ha Han i Hi; [lia|].
    cbn [rdn] in Hr. destruct (M (Z_to_bv 64 a)) as [b|] eqn:HM.
    - destruct (Z.eq_dec i 0) as [->|Hnz]; [rewrite Z.add_0_r, HM; discriminate|].
      destruct (rdn SEGS M (Z_to_bv 64 a + 1) n) as [rest|] eqn:Hr'; [|discriminate Hr].
      rewrite SymExec3Sound.SX2S.w_add_1, u64_of_Z in Hr' by lia.
      replace (a + i) with ((a + 1) + (i - 1)) by lia. apply (IH (a + 1) rest Hr'); lia.
    - rewrite seg_rom_high in Hr; [discriminate Hr | rewrite u64_of_Z by lia; lia].
  Qed.
  Lemma cellw_high_defined : forall M a (w : N) v, cellw SEGS M a w v -> 0x124000 <= a -> a + Z.of_N w <= 2 ^ 64 ->
    defined M a (Z.of_N w).
  Proof using.
    intros M a w v [_ Hr] Ha Haw. rewrite <- N_nat_Z. eapply rdn_defined_high; [exact Hr | exact Ha | rewrite N_nat_Z; exact Haw].
  Qed.

  Lemma ro_clear_via_eff : forall (A A' : AS MI) M M' model (W : Z * Z) (F : Z -> Prop),
    ro_clear L M -> ainv MI A M model -> eff MI A A' M M' W F ->
    (forall a, F a -> ~ in_ranges (ly_img L) a) -> alloc_ceiling <= fst W ->
    ro_clear L M'.
  Proof using AC L MI HLimg_lo HLerr_rw.
    intros A A' M M' model W F RC AI EF HF HW.
    pose proof ceiling_lt as Hcl.
    eapply (ro_clear_frame L _ M M' RC (ef_frame _ _ _ _ _ _ _ _ _ EF)).
    intros a (Himg & Hnrw & Hnrel). pose proof (HLimg_lo _ Himg) as Hlt.
    intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
    - destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
    - destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho') as [Ho | [[Hni _] | Hf]].
      + destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
      + exact (Hni Himg).
      + exact (HF _ Hf Himg).
    - destruct Hnm as (Hni & _). exact (Hni Himg).
    - exact (HF _ Hf Himg).
    - unfold W_of in Hw. lia.
    - exact (Hnrw (HLerr_rw _ He)).
  Qed.

  Lemma apart_sub' : forall a k b m k' m', apart a k b m -> k' <= k /\ m' <= m -> apart a k' b m'.
  Proof using. unfold apart. intros. lia. Qed.

  Lemma w_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
  Proof using.
    intros a b Ha Hb. apply bv_eq. rewrite u_sltu64, !u64_of_Z by lia.
    destruct (a <? b); rewrite u64_of_Z by lia; reflexivity.
  Qed.

  Lemma bseq_next_facts : forall bc, In bc BSEQ -> bc <> BSEQ_LAST ->
    In (bseq_next bc) BSEQ /\ bc < bseq_next bc /\ 8 * bseq_next bc <= 2 ^ 28
    /\ ((bc = 0 /\ bseq_next bc = 2) \/ (3 <= bseq_next bc /\ Z.land (bseq_next bc) (bseq_next bc - 1) <> 0)).
  Proof using.
    intros bc Hin Hlast. unfold BSEQ in Hin. unfold BSEQ_LAST in Hlast.
    repeat (destruct Hin as [<-|Hin];
      [ first [ exfalso; lia
              | match goal with |- context [bseq_next ?b] => let v := eval vm_compute in (bseq_next b) in change (bseq_next b) with v end;
                split; [inl | split; [lia | split; [lia | first [left; split; reflexivity | right; split; [lia | vm_compute; discriminate]]]]] ] |]).
    destruct Hin.
  Qed.

  Lemma nparg_not_pow2 : forall bc, In bc BSEQ -> bc <> 0 -> Z.land (2 * bc + 1) (2 * bc + 1 - 1) <> 0.
  Proof using.
    intros bc Hin Hnz. unfold BSEQ in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [exfalso; lia | vm_compute; discriminate] |]). destruct Hin.
  Qed.

  Lemma getr_other : forall R (r : reg) v r', r' <> r -> getr (regupd R r v) r' = getr R r'.
  Proof using. intros R r v r' Hne. unfold getr. rewrite regupd_other by exact Hne. reflexivity. Qed.

  Lemma accrue_no_flags : forall cs, accrue_csr cs no_flags = cs.
  Proof using.
    intros cs. unfold accrue_csr. change (fflags_bits no_flags) with 0. rewrite Z.lor_0_r. apply Z_to_bv_bv_unsigned.
  Qed.

  Ltac zpc z := lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
                  replace pc with (Z_to_bv 64 z : word) by (apply bv_eq; vm_compute; reflexivity) end.

  Ltac fp_flw MS Fx Dx Qrs Crd off znext :=
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
    [ norm_pc; eapply msteps_one; [reflexivity|];
      eapply fp_step_flw; [exact Fx | reflexivity | exact Dx | rewrite Qrs; change (bv_signed _) with off; apply v_addi_Z; lia | exact Crd]
    | cbn [fp_regs fp_csr]; rewrite flw_nan_box by lia; zpc znext ].

  Ltac fp_fcvt_s_lu MS Fx Dx FZ Qrs n znext :=
    let md := fresh "md" in let Hst := fresh "Hst" in
    lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fx1 ?R _ ?M ?rom) _) _ =>
      destruct (hp_step_fcvt_s_lu fx1 SEGS R _ M rom _ _ _ _ Fx eq_refl Dx FZ ltac:(right; reflexivity)) as [md Hst];
      cbv zeta in Hst; rewrite Qrs, (u64_of_Z n), (of_int_val md n) in Hst by lia; cbn [fst snd] in Hst; rewrite accrue_no_flags in Hst;
      eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
      [ norm_pc; eapply msteps_one; [reflexivity | exact Hst] | clear Hst md; zpc znext ]
    end.

  Ltac fp_fari MS Fx Dx FZ Ha Hb VAL znext :=
    let md := fresh "md" in let Hst := fresh "Hst" in
    lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fx1 ?R _ ?M ?rom) _) _ =>
      destruct (hp_step_fari_s fx1 SEGS R _ M rom _ _ _ _ _ _ _ _ Fx eq_refl Dx FZ ltac:(right; reflexivity) Ha Hb ltac:(unfold one32; lia) ltac:(unfold one32; lia)) as [md Hst];
      cbv zeta in Hst; cbn [fari_op] in Hst; rewrite (VAL md) in Hst by lia; cbn [fst snd] in Hst; rewrite accrue_no_flags in Hst;
      eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
      [ norm_pc; eapply msteps_one; [reflexivity | exact Hst] | clear Hst md; zpc znext ]
    end.

  Ltac fp_flt MS Fx Dx Ha Hb a b znext :=
    let Hst := fresh "Hst" in
    lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fx1 ?R _ ?M ?rom) _) _ =>
      pose proof (hp_step_fcmp_s fx1 SEGS R _ M rom _ _ _ _ _ _ _ Fx eq_refl Dx Ha Hb ltac:(lia) ltac:(lia)) as Hst;
      cbv zeta in Hst; cbn [fcmp_op] in Hst; rewrite (lt_val a b) in Hst by lia; cbn [fst snd] in Hst; rewrite accrue_no_flags in Hst;
      lazymatch type of Hst with context [bv_eqb ?r 0%bv] => replace (bv_eqb r 0%bv) with false in Hst by reflexivity end; cbv beta iota in Hst;
      eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
      [ norm_pc; eapply msteps_one; [reflexivity | exact Hst] | clear Hst; zpc znext ]
    end.

  Ltac fp_fcvt_lu_s MS Fx Dx FZ Ha n znext :=
    let md := fresh "md" in let Hmd := fresh "Hmd" in let Hst := fresh "Hst" in
    lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fx1 ?R _ ?M ?rom) _) _ =>
      destruct (hp_step_fcvt_l_s fx1 SEGS R _ M rom _ false _ _ _ _ Fx eq_refl Dx FZ ltac:(left; vm_compute; discriminate) Ha ltac:(lia)) as (md & Hmd & Hst);
      cbv zeta in Hst; rewrite (to_lu_val md n) in Hst by lia; cbn [fst snd] in Hst; rewrite accrue_no_flags in Hst;
      lazymatch type of Hst with context [bv_eqb ?r 0%bv] => replace (bv_eqb r 0%bv) with false in Hst by reflexivity end; cbv beta iota in Hst;
      eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
      [ norm_pc; eapply msteps_one; [reflexivity | exact Hst] | clear Hst Hmd md; zpc znext ]
    end.

  Lemma agree_block_via_eff : forall (A A' : AS MI) M M' model model' (W : Z * Z) (F : Z -> Prop) q m,
    eff MI A A' M M' W F -> ainv MI A M model -> ainv MI A' M' model' ->
    In (q, m) (live MI A) -> In (q, m) (live MI A') ->
    (forall a, q <= a < q + m -> ~ F a) -> alloc_ceiling <= fst W ->
    agree_on M M' q m.
  Proof using AC L MI HLrw_img HLerr_rw.
    intros A A' M M' model model' W F q m EF AI AI' Hl Hl' HF HW i Hi.
    pose proof ceiling_lt as Hcl.
    destruct (ai_live_block MI A M model q m AI Hl) as (_ & _ & Hq0 & Hqc & Hall).
    destruct (ai_live_block MI A' M' model' q m AI' Hl') as (_ & _ & _ & _ & Hall').
    destruct (Hall (q + i) ltac:(lia)) as (Ho & Hni & Hd). destruct (Hall' (q + i) ltac:(lia)) as (Ho' & _ & _).
    apply (ef_frame _ _ _ _ _ _ _ _ _ EF). rewrite u64_of_Z by lia.
    intros [H | [H | [H | [H | [H | H]]]]].
    - exact (Ho H). - exact (Ho' H). - destruct H as (_ & _ & Hn). exact (Hd Hn). - exact (HF (q + i) ltac:(lia) H).
    - unfold W_of in H. lia.
    - exact (Hni (HLrw_img _ (HLerr_rw _ H))).
  Qed.

  Lemma land_3 : forall a, 0 <= a -> Z.land a 3 = a mod 4.
  Proof using. intros a Ha. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
  Lemma sc_trap_align4 : forall M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 4 = 0 ->
    sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_AND e (ELit 3)) (ELit 0)).
  Proof using.
    intros M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He.
    rewrite w_and by lia. rewrite land_3, Hal by lia. reflexivity.
  Qed.
  Lemma sc_trap_nulleq : forall M E e1 e2 a k, edenot E e2 = Z_to_bv 64 a -> edenot E e1 = Z_to_bv 64 (a + k) ->
    0 < a -> 0 <= k -> a + k < 2 ^ 64 ->
    sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_SLTU (ELit 0) e2) (EAlu ALU_SLTU e1 (ELit 1))).
  Proof using.
    intros M E e1 e2 a k H2 H1 Ha Hk Hak. cbn [sc_denot]. cbn [edenot]. rewrite H1, H2.
    rewrite !w_sltu by lia.
    replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (a + k <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  Lemma fkept_refl : forall f0, fkept_u1 f0 f0.
  Proof using. intros f0 r _. reflexivity. Qed.
  Lemma fkept_base : forall f0 f1 cs, fkept_u1 f0 f1 -> fkept_u1 f0 (mkFP (@fp_regs f1) cs).
  Proof using. intros f0 f1 cs FK r Hr. cbn [fp_regs]. apply FK. exact Hr. Qed.
  Lemma fkept_set : forall f0 fr cs (rd : bv 5) v, fkept_u1 f0 (mkFP fr cs) -> In rd [13; 14; 15]%bv ->
    fkept_u1 f0 (mkFP (bvmap_set rd v fr) cs).
  Proof using.
    intros f0 fr cs rd v FK Hrd r Hr. cbn [fp_regs]. unfold reg_get.
    rewrite bvmap_get_set_other by (intros ->; exact (Hr Hrd)). exact (FK r Hr).
  Qed.
  Lemma fkept_csr : forall f0 fr cs cs', fkept_u1 f0 (mkFP fr cs) -> fkept_u1 f0 (mkFP fr cs').
  Proof using. intros f0 fr cs cs' FK r Hr. exact (FK r Hr). Qed.
  Ltac fk_tac := first
    [ assumption
    | apply fkept_refl
    | apply fkept_set; [fk_tac | cbn; clear; intuition congruence]
    | apply fkept_base; fk_tac
    | match goal with H : fkept_u1 _ (mkFP ?fr _) |- fkept_u1 _ (mkFP ?fr _) => exact (fkept_csr _ _ _ _ H) end ].

  Section Main.
    Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
    Variables (sp ret obj bl bc keyp tupp keyp2 key : Z) (ents : list (Z * (Z * Z))) (K : TSet).
    Hypothesis CB : callB MI ST A0 s R0 M0 model0 sp ret (EMPLACE_STACK NEW_STACK DEL_STACK).
    Hypothesis FRM : frm_zero (@fp_csr fx).
    Hypothesis H10 : getr R0 10%bv = Z_to_bv 64 obj.
    Hypothesis H11 : getr R0 11%bv = Z_to_bv 64 keyp.
    Hypothesis H13 : getr R0 13%bv = Z_to_bv 64 tupp.
    Hypothesis U0 : umapx MI 24 (nval24 SEGS) A0 M0 obj bl bc ents.
    Hypothesis ASP : above_sp MI A0 sp obj 40.
    Hypothesis ASK : above_sp MI A0 sp keyp 4.
    Hypothesis AST : above_sp MI A0 sp tupp 8.
    Hypothesis ASK2 : above_sp MI A0 sp keyp2 4.
    Hypothesis CK : cell4 SEGS M0 keyp key.
    Hypothesis CT : cell8 SEGS M0 tupp keyp2.
    Hypothesis CK2 : cell4 SEGS M0 keyp2 key.
    Hypothesis K2AL : keyp2 mod 4 = 0.
    Hypothesis ROC : ro_clear L M0.
    Hypothesis HSZ : Zlength ents + 1 < 2 ^ 24.
    Hypothesis HNMAX : LIB_NMAX <= NMAX MI.
    Hypothesis Hlast : bc <> BSEQ_LAST.
    Hypothesis ROOM1 : roomL MI A0 (live MI A0) 24.
    Hypothesis ROOM2 : (bc = 0 \/ Zlength ents = bc) -> roomL MI A0 ((0, 24) :: live MI A0) (8 * bseq_next bc).
    Hypothesis CONT : forall (fx' : FPState) A' R' M' model' (p v bl' bc' : Z) (ents' : list (Z * (Z * Z)))
            (inserted rehashed : bool),
        retB MI ST A' s R0 R' M' model0 model' -> frm_zero (@fp_csr fx') -> fkept_u1 fx fx' ->
        getr R' 10%bv = Z_to_bv 64 p -> getr R' 11%bv = Z_to_bv 64 (b2z inserted) ->
        umapx MI 24 (nval24 SEGS) A' M' obj bl' bc' ents' ->
        In (p, (key, v)) ents' ->
        (inserted = false -> ents' = ents /\ rehashed = false) ->
        (inserted = true -> v = 0 /\ Permutation ents' ((p, (key, 0)) :: ents)) ->
        (rehashed = false -> bl' = bl /\ bc' = bc) ->
        (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
        lapply (live MI A0)
               ((if inserted then [LAdd p 24] else [])
                ++ (if rehashed then LAdd bl' (8 * bc') :: (if bc =? 0 then [] else [LDel bl]) else []))
               (live MI A') ->
        eff MI A0 A' M0 M' (sp - EMPLACE_STACK NEW_STACK DEL_STACK, sp)
            (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' bc' ents' a) ->
        srealizes SEGS (cfg fx' R' ret M' model') K.

    Definition SS : Z := 96 + Z.max NEW_STACK DEL_STACK.
    Definition W : Z * Z := (sp - SS, sp).

    Definition base_ok (R : bvmap 5 word) : Prop :=
      getr R 2%bv = Z_to_bv 64 (sp - 48) /\ getr R 3%bv = Z_to_bv 64 (ly_gp L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp L)
      /\ forall r, In r [21; 22; 23; 24; 25; 26; 27]%bv -> getr R r = getr R0 r.

    Definition frame (M : mem) : Prop :=
      cell8 SEGS M (sp - 8) ret /\ cell8 SEGS M (sp - 16) (bv_unsigned (getr R0 8%bv)) /\ cell8 SEGS M (sp - 24) (bv_unsigned (getr R0 9%bv))
      /\ cell8 SEGS M (sp - 32) (bv_unsigned (getr R0 18%bv)) /\ cell8 SEGS M (sp - 40) (bv_unsigned (getr R0 19%bv))
      /\ cell8 SEGS M (sp - 48) (bv_unsigned (getr R0 20%bv)).

    Let AI0 := cb_ainv _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let MS0 := cb_mstd _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let CR0 := cb_regs _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let ROC0 := cb_roc _ _ _ _ _ _ _ _ _ _ _ _ CB.

    Lemma sp_facts : sp mod 16 = 0 /\ alloc_ceiling + SS <= sp /\ sp < 2 ^ 47 /\ 0x124000 <= sp - SS /\ 96 + NEW_STACK <= SS /\ 96 + DEL_STACK <= SS.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret keyp2 CB.
      destruct CR0. pose proof (cb_ceil _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hc. unfold EMPLACE_STACK in Hc. unfold SS.
      pose proof ac_bounds_lit. repeat split; try assumption; lia.
    Qed.
    Let SPF := sp_facts.

    Lemma bc_facts : In bc BSEQ /\ 0 <= bc < 2 ^ 24 /\ Zlength ents <= bc /\ 0 <= Zlength ents.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp ret obj bl bc keyp2 key ents K U0 Hlast ROOM2 CONT.
      pose proof (u_bseq U0) as HB. pose proof (u_load U0) as HL. pose proof (BSEQ_bound bc HB).
      split; [exact HB|]. split; [| split; [exact HL | unfold Zlength; lia]].
      unfold BSEQ in HB. unfold BSEQ_LAST in Hlast. cbn in HB.
      repeat (destruct HB as [<-|HB]; [lia|]). destruct HB.
    Qed.

    Lemma foot_low_or_high : forall a, umap_foot 24 obj bl bc ents a -> 0 <= a /\ (a + 1 <= alloc_ceiling \/ sp <= a < 2 ^ 47).
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn A0 s R0 M0 model0 sp ret obj bl bc keyp2 ents CB U0 ASP.
      pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1.
      intros a [Hh | [[Hbc Hb] | (p & Hp & Ha)]].
      - destruct ASP as (Hs1 & _). lia.
      - destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' A0 M0 model0 bl (8 * bc) AI0 Hin) as (_ & Hb0 & Hc & _). lia.
      - apply in_map_iff in Hp. destruct Hp as ([q [k v]] & Hq & Hin). cbn in Hq. subst q.
        destruct (live_facts' A0 M0 model0 p 24 AI0 (proj1 (u_node U0 p k v Hin))) as (_ & Hp0 & Hc & _). lia.
    Qed.

    Lemma foot_low_or_high_gen : forall A M model bl2 bc2 (ents2 : list (Z * (Z * Z))) a,
      ainv MI A M model -> umapx MI 24 (nval24 SEGS) A M obj bl2 bc2 ents2 ->
      umap_foot 24 obj bl2 bc2 ents2 a -> 0 <= a /\ (a + 1 <= alloc_ceiling \/ sp <= a < 2 ^ 47).
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn A0 s R0 M0 model0 sp ret obj keyp2 CB ASP.
      intros A M model bl2 bc2 ents2 a AI U. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
      intros [Hh | [[Hbc Hb] | (p & Hp & Ha)]].
      - destruct ASP as (Hs1 & _). lia.
      - destruct (u_blive U) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' A M model bl2 (8 * bc2) AI Hin) as (_ & Hb0 & Hc & _). lia.
      - apply in_map_iff in Hp. destruct Hp as ([q [k v]] & Hq & Hin). cbn in Hq. subst q.
        destruct (live_facts' A M model p 24 AI (proj1 (u_node U p k v Hin))) as (_ & Hp0 & Hc & _). lia.
    Qed.

    Lemma foot_offimg_gen : forall A M model bl2 bc2 (ents2 : list (Z * (Z * Z))) a,
      ainv MI A M model -> umapx MI 24 (nval24 SEGS) A M obj bl2 bc2 ents2 ->
      umap_foot 24 obj bl2 bc2 ents2 a -> ~ in_ranges (ly_img L) a.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn HLimg_lo A0 s R0 M0 model0 sp ret obj keyp2 CB ASP.
      intros A M model bl2 bc2 ents2 a AI U Ha Hi. pose proof (HLimg_lo _ Hi) as Hlt.
      destruct Ha as [Hh | [[Hbc Hb] | (p & Hp & Hpa)]].
      - destruct ASP as (Hs1 & _). destruct SPF as (_ & Hsplo & _). unfold SS in Hsplo. lia.
      - destruct (u_blive U) as [[? ?]|[_ Hin]]; [lia|]. exact (live_offimg' A M model bl2 (8 * bc2) a AI Hin Hb Hi).
      - apply in_map_iff in Hp. destruct Hp as ([q [k v]] & Hq & Hin). cbn in Hq. subst q.
        exact (live_offimg' A M model p 24 a AI (proj1 (u_node U p k v Hin)) Hpa Hi).
    Qed.

    Lemma foot_apart_new : forall A M model p n a, ainv MI A M model -> live_add p n (live MI A0) (live MI A) ->
      umap_foot 24 obj bl bc ents a -> ~ (p <= a < p + n).
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn fx A0 s R0 M0 model0 sp ret obj bl bc keyp2 key ents K CB U0 ASP CONT.
      intros A M model p n a AI LADD Ha Hpa.
      assert (HinP : In (p, n) (live MI A)) by (rewrite (proj1 LADD); left; reflexivity).
      destruct (live_facts' A M model p n AI HinP) as (_ & _ & Hpc & _).
      destruct (umap_foot_hb 24 obj bl bc ents a Ha) as [Hh | ([q m] & Hb & Hba)]; [destruct ASP as (Hs1 & _); destruct SPF as (_ & Hsplo & _); unfold SS in Hsplo; lia|]. cbn in Hba.
      assert (Hq0 : In (q, m) (live MI A0)).
      { unfold umap_blocks in Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
        - destruct (Z.eqb_spec bc 0); [destruct Hb|]. destruct Hb as [Hb|[]]. injection Hb as <- <-.
          destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia | exact Hin].
        - apply in_map_iff in Hb. destruct Hb as ([q' [k v]] & Hq & Hin). cbn in Hq. injection Hq as <- <-. exact (proj1 (u_node U0 q' k v Hin)). }
      assert (Hq1 : In (q, m) (live MI A)) by (rewrite (proj1 LADD); right; exact Hq0).
      assert (Hne : p <> q) by (intros <-; apply (proj2 LADD); apply (in_map fst _ (p, m)); exact Hq0).
      pose proof (ai_live_disjoint MI A M model p n q m AI HinP Hq1 Hne) as Hap. lia.
    Qed.

    Record pst (M : mem) (R : bvmap 5 word) : Prop := PST {
      p_regs : base_ok R;
      p_s0 : getr R 8%bv = Z_to_bv 64 obj;
      p_s1 : getr R 9%bv = Z_to_bv 64 tupp;
      p_s2 : getr R 18%bv = Z_to_bv 64 bc;
      p_s3 : getr R 19%bv = Z_to_bv 64 key;
      p_frame : frame M;
      p_def : defined M (sp - SS) SS;
      p_out : forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M a = M0 a;
      p_grow : forall a : word, M0 a <> None -> M a <> None
    }.

    Lemma phaseA :
      (forall M1 R1 (p v : Z),
          pst M1 R1 -> In (p, (key, v)) ents ->
          getr R1 10%bv = Z_to_bv 64 p -> getr R1 11%bv = Z_to_bv 64 0 ->
          srealizes SEGS (cfg fx R1 EPI M1 model0) K) ->
      (forall M1 R1,
          pst M1 R1 -> (bc <> 0 -> getr R1 20%bv = Z_to_bv 64 (hmod key bc)) ->
          srealizes SEGS (cfg fx R1 NF_PC M1 model0) K) ->
      srealizes SEGS (cfg fx R0 EMP M0 model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn fx A0 s R0 M0 model0 sp ret obj bl bc keyp tupp keyp2 key ents K CB H10 H11 H13 U0 ASP ASK CK Hlast ROOM2 CONT.
      intros PFOUND PNF.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct ASP as (Hs1 & Hh1 & Ho1). destruct ASK as (Ks1 & Kh1 & Ko1).
      destruct bc_facts as (HbB & Hbcr & Hload & Hsz0).
      pose proof (cb_room _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hroom. unfold EMPLACE_STACK in Hroom. fold SS in Hroom.
      pose proof (defined_of_stack_room M0 sp SS ltac:(lia) ltac:(unfold SS; lia) ltac:(lia) Hroom) as Hdef0.
      pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
      pose proof (h_bc (u_hdr U0)) as Cbc. unfold cell8 in Cbc. pose proof CK as Ck. unfold cell4 in Ck.
      pose (E := Eseed R0 [Z_to_bv 64 obj; Z_to_bv 64 keyp; Z_to_bv 64 sp; getr R0 1%bv; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv; getr R0 19%bv;
                           getr R0 20%bv; Z_to_bv 64 tupp; Z_to_bv 64 bc; Z_to_bv 64 key]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34);
                                          (1%bv, EVar 35); (8%bv, EVar 36); (9%bv, EVar 37); (18%bv, EVar 38); (19%bv, EVar 39);
                                          (20%bv, EVar 40); (13%bv, EVar 41)]) R0).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | reflexivity]. }
      assert (HK : know_ok SEGS E M0 [KWr (SA (EVar 34) (-48)) (ELit 48);
                                      KDisj (SA (EVar 32) 0) (ELit 40) (SA (EVar 34) (-48)) (ELit 48);
                                      KDisj (SA (EVar 33) 0) (ELit 4) (SA (EVar 34) (-48)) (ELit 48)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - eapply (kwr_stack_sub _ _ _ _ sp SS); [evs; reflexivity | reflexivity | lia | lia | lia | exact Hroom].
        - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia].
        - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia]. }

      assert (POSTC : forall Rc (pc : Z) (Mc : mem),
        Mc = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M0
               (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (getr R0 1%bv)))
               (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 (getr R0 8%bv)))
               (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 (getr R0 9%bv)))
               (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 (getr R0 18%bv)))
               (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 (getr R0 19%bv)))
               (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 (getr R0 20%bv)) ->
        getr Rc 2%bv = Z_to_bv 64 (sp - 48) -> getr Rc 3%bv = getr R0 3%bv -> getr Rc 4%bv = getr R0 4%bv ->
        (forall r, In r [21; 22; 23; 24; 25; 26; 27]%bv -> getr Rc r = getr R0 r) ->
        getr Rc 8%bv = Z_to_bv 64 obj -> getr Rc 9%bv = Z_to_bv 64 tupp -> getr Rc 18%bv = Z_to_bv 64 bc -> getr Rc 19%bv = Z_to_bv 64 key ->
        pst Mc Rc).
      { intros Rc pc Mc -> Q2 Q3 Q4 Qs Q8 Q9 Q18 Q19.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R0 20)), <- (Z_to_bv_bv_unsigned 64 (getr R0 19)), <- (Z_to_bv_bv_unsigned 64 (getr R0 18)),
                <- (Z_to_bv_bv_unsigned 64 (getr R0 9)), <- (Z_to_bv_bv_unsigned 64 (getr R0 8)).
        rewrite Hra.
        pose proof (u64_range (getr R0 8)) as Hr8. pose proof (u64_range (getr R0 9)) as Hr9. pose proof (u64_range (getr R0 18)) as Hr18.
        pose proof (u64_range (getr R0 19)) as Hr19. pose proof (u64_range (getr R0 20)) as Hr20. unfold ret_ok in Hret.
        set (Mc := wbytes _ _ _).
        assert (HMcw : forall x : word, ~ (sp - 48 <= bv_unsigned x < sp) -> Mc x = M0 x).
        { intros x Hx. pose proof (u64_range x). unfold Mc.
          rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMcg : forall x : word, M0 x <> None -> Mc x <> None) by (intros x Hx; unfold Mc; repeat apply wbytes_grows; exact Hx).
        constructor.
        - unfold base_ok. rewrite Q2, Q3, Q4. split; [reflexivity|]. split; [exact Hgp|]. split; [exact Htp|]. exact Qs.
        - exact Q8. - exact Q9. - exact Q18. - exact Q19.
        - unfold frame, cell8. unfold Mc. split; [|split; [|split; [|split; [|split]]]]; cellpeel.
        - unfold Mc. repeat apply defined_wbytes. exact Hdef0.
        - exact HMcw. - exact HMcg. }
      destruct (Z.eq_dec bc 0) as [Hbc0 | Hbc1].
      -
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 42; EVar 43] []) 50%N.
        { split_scs; try sc_auto1.
          all: eapply (sc_read_cellw _ _ _ _ _ _ _ _ Ck); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
        postrun.
        apply PNF; [| intros Hne; exfalso; exact (Hne Hbc0)].
        eapply (POSTC R' 0); [reflexivity | ..];
          first [ let Q := fresh in rreg HR' 2%bv Q; rewrite Q; rewrite ?w_addm, ?v_addi_Z by lia; f_equal; lia
                | let Q := fresh in rreg HR' 3%bv Q; exact Q
                | let Q := fresh in rreg HR' 4%bv Q; exact Q
                | exact (syms_id_sound _ _ _ _ [21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl)
                | let Q := fresh in rreg HR' 8%bv Q; exact Q
                | let Q := fresh in rreg HR' 9%bv Q; exact Q
                | let Q := fresh in rreg HR' 18%bv Q; exact Q
                | let Q := fresh in rreg HR' 19%bv Q; exact Q ].
      -
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 42; EVar 43] []) 50%N.
        { split_scs; try sc_auto1.
          all: eapply (sc_read_cellw _ _ _ _ _ _ _ _ Ck); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
        postrun.
        assert (P1 : pst (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M0
               (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (getr R0 1%bv)))
               (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 (getr R0 8%bv)))
               (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 (getr R0 9%bv)))
               (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 (getr R0 18%bv)))
               (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 (getr R0 19%bv)))
               (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 (getr R0 20%bv))) R').
        { eapply (POSTC R' 0); [reflexivity | ..];
          first [ let Q := fresh in rreg HR' 2%bv Q; rewrite Q; rewrite ?w_addm, ?v_addi_Z by lia; f_equal; lia
                | let Q := fresh in rreg HR' 3%bv Q; exact Q
                | let Q := fresh in rreg HR' 4%bv Q; exact Q
                | exact (syms_id_sound _ _ _ _ [21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl)
                | let Q := fresh in rreg HR' 8%bv Q; exact Q
                | let Q := fresh in rreg HR' 9%bv Q; exact Q
                | let Q := fresh in rreg HR' 18%bv Q; exact Q
                | let Q := fresh in rreg HR' 19%bv Q; exact Q ]. }
        set (Mc := wbytes _ _ _) in *.
        assert (Uc : umapx MI 24 (nval24 SEGS) A0 Mc obj bl bc ents).
        { eapply (umapx_agree SEGS L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia) A0 A0 M0 Mc); [exact U0 | | intros; assumption].
          intros a Ha. pose proof (foot_low_or_high a Ha) as Hlh. pose proof ceiling_lt. apply (p_out _ _ P1). rewrite u64_of_Z by lia. lia. }
        destruct (search_correct L MI 24 Z (nval24 SEGS) (seg_rom SEGS) A0 Mc obj bl bc key ents Uc (proj1 CK) ltac:(lia) Hbc1 R'
                    (p_s0 _ _ P1) (p_s2 _ _ P1) (p_s3 _ _ P1)) as (R2 & SK & G20 & (G8 & G18 & G19) & HW).
        assert (P2 : pst Mc R2).
        { destruct P1 as [B Q8 Q9 Q18 Q19 FR DEF OUT GROW]. destruct B as (B2 & B3 & B4 & Bs).
          constructor; try assumption.
          - unfold base_ok. rewrite !(SK _) by (clear; cbn; tauto). split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
            intros r Hr. rewrite (SK r); [apply Bs; exact Hr|]. clear - Hr. cbn in Hr |- *. tauto.
          - rewrite (SK 9%bv) by (clear; cbn; tauto). exact Q9. }
        destruct HW as [(p & v & Hin & Hms & F10 & F11) | Hms].
        + eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact Hms |].
          exact (PFOUND Mc R2 p v P2 Hin F10 F11).
        + eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact Hms |].
          apply (PNF Mc R2 P2). intros _. exact G20.
    Qed.

    Lemma epilogue : forall (fx1 : FPState) A1 M1 model1 R1 (p v bl' bc' : Z) ents' (inserted rehashed : bool) (F : Z -> Prop),
      ainv MI A1 M1 model1 -> mstd model1 -> m_fs model1 = m_fs model0 -> m_fds model1 = m_fds model0 ->
      frm_zero (@fp_csr fx1) -> fkept_u1 fx fx1 ->
      base_ok R1 -> frame M1 ->
      getr R1 10%bv = Z_to_bv 64 p -> getr R1 11%bv = Z_to_bv 64 (b2z inserted) ->
      umapx MI 24 (nval24 SEGS) A1 M1 obj bl' bc' ents' ->
      In (p, (key, v)) ents' ->
      (inserted = false -> ents' = ents /\ rehashed = false) ->
      (inserted = true -> v = 0 /\ Permutation ents' ((p, (key, 0)) :: ents)) ->
      (rehashed = false -> bl' = bl /\ bc' = bc) ->
      (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
      lapply (live MI A0)
             ((if inserted then [LAdd p 24] else [])
              ++ (if rehashed then LAdd bl' (8 * bc') :: (if bc =? 0 then [] else [LDel bl]) else []))
             (live MI A1) ->
      eff MI A0 A1 M0 M1 W F -> (forall a, F a -> umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' bc' ents' a) ->
      (forall a, F a -> ~ in_ranges (ly_img L) a) ->
      srealizes SEGS (cfg fx1 R1 EPI M1 model1) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc keyp2 key ents K CB CONT.
      intros fx1 A1 M1 model1 R1 p v bl' bc' ents' inserted rehashed F AI MS Hfs Hfds FZ FK B FR G10 G11 U' Hin Hf Ht Hrf Hrt LAP EFF HF FOFF.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct B as (B2 & B3 & B4 & Bs). destruct FR as (F1 & F2 & F3 & F4 & F5 & F6).
      unfold cell8 in F1, F2, F3, F4, F5, F6.
      pose proof (u64_range (getr R0 8%bv)) as Hr8. pose proof (u64_range (getr R0 9%bv)) as Hr9. pose proof (u64_range (getr R0 18%bv)) as Hr18.
      pose proof (u64_range (getr R0 19%bv)) as Hr19. pose proof (u64_range (getr R0 20%bv)) as Hr20.
      unfold ret_ok in Hret.
      pose (E := Eseed R1 [Z_to_bv 64 (sp - 48); Z_to_bv 64 ret; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv; getr R0 19%bv; getr R0 20%bv]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R1).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M1 []) by constructor.
      xruns HR HK 100%nat STOPS (SCR [] [EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38] []) 50%N.
      { split_scs; try sc_auto1;
        first [ eapply (sc_read_cellw _ _ _ _ _ _ _ _ F2); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity]
              | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F3); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity]
              | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F4); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity]
              | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F5); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity]
              | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F6); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity] ]. }
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
      rreg HRr 1%bv G1. rreg HRr 2%bv G2. rreg HRr 8%bv G8. rreg HRr 9%bv G9. rreg HRr 18%bv G18. rreg HRr 19%bv G19. rreg HRr 20%bv G20.
      rreg HRr 10%bv Q10. rreg HRr 11%bv Q11.
      rewrite ?Z_to_bv_bv_unsigned in G8, G9, G18, G19, G20.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.

      eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ].
      { unfold RET_PC. norm_pc. stepjr F_6ad64 D_6ad64 (Z_to_bv 64 ret) ltac:(exact G1).
        change (bv_signed (0%bv : bv 12)) with 0%Z. rewrite Hret. apply mst_refl. }
      apply (CONT fx1 A1 Rr M1 model1 p v bl' bc' ents' inserted rehashed).
      - constructor; [exact AI | exact MS | exact Hfs | exact Hfds | |].
        + eapply (sx_inv_via_eff' s A0 A1 M0 M1 model0 W); [exact (cb_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) | exact AI0 | exact EFF
            | exact (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) | exact (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) | exact FOFF | unfold W; cbn; lia].
        + intros r Hr. unfold callee_saved in Hr. cbn in Hr.
          repeat (destruct Hr as [<-|Hr]); try contradiction;
            first [ rewrite G1; symmetry; exact Hra
                  | rewrite G2, w_add by lia; replace (sp - 48 + 48) with sp by lia; symmetry; exact Hsp2
                  | rewrite G8; reflexivity | rewrite G9; reflexivity | rewrite G18; reflexivity | rewrite G19; reflexivity | rewrite G20; reflexivity
                  | rewrite Gs by inl; first [rewrite B3; symmetry; exact Hgp | rewrite B4; symmetry; exact Htp | apply Bs; inl] ].
      - exact FZ.
      - exact FK.
      - rewrite Q10. exact G10.
      - rewrite Q11. exact G11.
      - exact U'. - exact Hin. - exact Hf. - exact Ht. - exact Hrf. - exact Hrt. - exact LAP.
      - unfold EMPLACE_STACK. fold SS. change (sp - SS, sp) with W. eapply eff_weaken; [exact EFF | exact HF].
    Qed.

    Lemma phaseFound : forall M1 R1 (p v : Z),
      pst M1 R1 -> In (p, (key, v)) ents ->
      getr R1 10%bv = Z_to_bv 64 p -> getr R1 11%bv = Z_to_bv 64 0 ->
      srealizes SEGS (cfg fx R1 EPI M1 model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc tupp keyp2 key ents K CB FRM U0 ASP CONT.
      intros M1 R1 p v P1 Hin G10 G11.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct P1 as [B Q8 Q9 Q18 Q19 FR DEF OUT GROW].
      assert (AI1 : ainv MI A0 M1 model0).
      { eapply (ai_frame MI); [exact AI0 | | exact GROW | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply OUT; intros Hx. exact (hi_unowned A0 M0 model0 (bv_unsigned x) AI0 ltac:(lia) Ho). }
      assert (EF1 : eff MI A0 A0 M0 M1 W (fun _ => False)).
      { apply eff_store; [|exact GROW]. intros x HF HW. pose proof (u64_range x). apply OUT; intros Hx. apply HW. unfold W, W_of, SS. cbn. lia. }
      eapply (epilogue fx A0 M1 model0 R1 p v bl bc ents false false (fun _ => False) AI1 MS0 eq_refl eq_refl FRM (fkept_refl fx) B FR G10 G11).
      - eapply (umapx_agree SEGS L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia) A0 A0 M0 M1); [exact U0 | | intros; assumption].
        intros a Ha. pose proof (foot_low_or_high a Ha) as Hlh. apply OUT. rewrite u64_of_Z by lia. lia.
      - exact Hin.
      - intros _. split; reflexivity.
      - intros HT. discriminate HT.
      - intros _. split; reflexivity.
      - intros HT. discriminate HT.
      - cbn. reflexivity.
      - exact EF1.
      - intros a [].
      - intros a [].
    Qed.

    Record nst (p : Z) (A : AS MI) (M : mem) (model : Model) (R : bvmap 5 word) : Prop := NST {
      n_ai : ainv MI A M model;
      n_ms : mstd model;
      n_fs : m_fs model = m_fs model0;
      n_fds : m_fds model = m_fds model0;
      n_regs : base_ok R;
      n_s0 : getr R 8%bv = Z_to_bv 64 obj;
      n_s1 : getr R 9%bv = Z_to_bv 64 tupp;
      n_s2 : getr R 18%bv = Z_to_bv 64 bc;
      n_s3 : getr R 19%bv = Z_to_bv 64 key;
      n_s4 : bc <> 0 -> getr R 20%bv = Z_to_bv 64 (hmod key bc);
      n_a0 : getr R 10%bv = Z_to_bv 64 p;
      n_frame : frame M;
      n_def : defined M (sp - SS) SS;
      n_eff : eff MI A0 A M0 M W (fun a => p <= a < p + 24);
      n_ladd : live_add p 24 (live MI A0) (live MI A);
      n_p0 : 0 < p; n_pc : p + 24 <= alloc_ceiling; n_pal : p mod 16 = 0;
      n_U : umapx MI 24 (nval24 SEGS) A M obj bl bc ents;
      n_ct : cell8 SEGS M tupp keyp2;
      n_ck2 : cell4 SEGS M keyp2 key;
      n_roc : ro_clear L M
    }.

    Lemma phaseN : forall M1 R1,
      pst M1 R1 -> (bc <> 0 -> getr R1 20%bv = Z_to_bv 64 (hmod key bc)) ->
      (forall p A2 M2 model2 R2, nst p A2 M2 model2 R2 -> srealizes SEGS (cfg fx R2 NEWR M2 model2) K) ->
      srealizes SEGS (cfg fx R1 NF_PC M1 model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn NEW HLnew HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc tupp keyp2 key ents K CB U0 ASP AST ASK2 CT CK2 ROC HNMAX ROOM1 CONT.
      intros M1 R1 P1 G20 POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct ASP as (Hs1 & Hh1 & Ho1). destruct AST as (Ts1 & Th1 & To1). destruct ASK2 as (K2s1 & K2h1 & K2o1).
      pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold EMPLACE_STACK in Hwin0. fold SS in Hwin0.
      destruct P1 as [B Q8 Q9 Q18 Q19 FR DEF OUT GROW]. pose proof B as B'. destruct B' as (B2 & B3 & B4 & Bs).
      assert (AI1 : ainv MI A0 M1 model0).
      { eapply (ai_frame MI); [exact AI0 | | exact GROW | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply OUT; intros Hx. exact (hi_unowned A0 M0 model0 (bv_unsigned x) AI0 ltac:(lia) Ho). }
      assert (EF1 : eff MI A0 A0 M0 M1 W (fun _ => False)).
      { apply eff_store; [|exact GROW]. intros x HF HW. pose proof (u64_range x). apply OUT; intros Hx. apply HW. unfold W, W_of, SS. cbn. lia. }
      assert (ROC1 : img_ro_clear L M1).
      { eapply (img_ro_clear_via_eff' A0 A0 M0 M1 model0 W _ ROC0 AI0 EF1); [intros a [] | unfold W; cbn; lia]. }
      assert (SX1 : sx_inv ST s M1).
      { eapply (sx_inv_via_eff' s A0 A0 M0 M1 model0 W _ (cb_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) AI0 EF1
                 (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB)); [intros a [] | unfold W; cbn; lia]. }
      pose (E := Eseed R1 [Z_to_bv 64 (sp - 48)]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R1).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M1 []) by constructor.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N; [split_scs; try sc_auto1|].
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
      rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 10%bv G10.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
      replace (Z_to_bv 64 949044) with (Z_to_bv 64 (ly_new L) : word) by (rewrite HLnew; reflexivity).
      eapply (NEW fx A0 s Rc M1 model0 24 (sp - 48) NEWR K AI1 MS0 ROC1 SX1 (cb_sxh _ _ _ _ _ _ _ _ _ _ _ _ CB)).
      - constructor; [exact G1 | apply bv_eq; vm_compute; reflexivity | unfold NEWR; lia | rewrite G2; reflexivity
                     | replace (sp - 48) with (sp + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia
                     | rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4].
      - exact G10.
      - unfold LIB_NMAX in HNMAX. lia.
      - lia.
      - apply stack_room_of_defined; [lia | lia | lia |]. eapply defined_sub; [exact DEF | unfold SS; lia | lia].
      - intros a Ha. split; [eapply hi_unowned; [exact AI0 | unfold zwin in Ha; lia]|]. apply (proj2 (Hwin0 a ltac:(unfold zwin in *; lia))).
      - exact (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB).
      - exact (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB).
      - replace (new_size 24) with 24 by reflexivity.
        eapply roomL_room_for; [exact AI0 | unfold LIB_NMAX in HNMAX; lia | exact ROOM1].
      -
        intros A1 R2 M2 model1 p AI2 MS1 Hfs1 Hfds1 SX2 KEPT R1a0 Hp LADD CAPS BIGC NEWT FR2 DEF2.
        replace (new_size 24) with 24 in LADD, FR2 by reflexivity.
        assert (EFF : eff MI A0 A1 M1 M2 (sp - 48 - NEW_STACK, sp - 48) (fun a => p <= a < p + 24)).
        { eapply (eff_of_new MI A0 A1 M1 M2 model1); [exact AI2 | exact CAPS | exact BIGC | exact NEWT | exact FR2 | exact DEF2 | intros a Ha; exact Ha | intros a Ha; exact Ha]. }
        assert (HinP : In (p, 24) (live MI A1)) by (rewrite (proj1 LADD); left; reflexivity).
        destruct (ai_live_block MI A1 M2 model1 p 24 AI2 HinP) as (_ & Hpal & Hp0 & Hpc & Hpown).
        assert (EFF2 : eff MI A0 A1 M0 M2 W (fun a => p <= a < p + 24)).
        { eapply eff_weaken; [eapply eff_trans; [exact EF1 | eapply eff_widen; [exact EFF|] |]|].
          * intros a Ha. unfold W, W_of in Ha |- *. cbn [fst snd] in Ha |- *. unfold SS in Ha, Hsplo |- *. lia.
          * intros a Ha. eapply hi_unowned; [exact AI2 | unfold W, W_of in Ha; cbn in Ha; lia].
          * intros a [[]|Ha]. exact Ha. }
        assert (AGf : agree_on M1 M2 (sp - 48) 48).
        { eapply (agree_above_via_eff' A0 A1 M1 M2 _ _ (sp - 48) 48 (sp - 48) EFF); [lia | cbn; lia | lia | lia | lia | | |].
          - intros i Hi. eapply hi_unowned; [exact AI0 | lia].
          - eapply defined_sub; [exact DEF | unfold SS; lia | lia].
          - intros i Hi Hf. cbn beta in Hf. lia. }

        assert (CT1 : cell8 SEGS M1 tupp keyp2).
        { eapply cellw_agree; [exact CT | | lia | cbn; lia]. intros i Hi. apply OUT. rewrite u64_of_Z by lia. lia. }
        assert (CK21 : cell4 SEGS M1 keyp2 key).
        { eapply cellw_agree; [exact CK2 | | lia | cbn; lia]. intros i Hi. apply OUT. rewrite u64_of_Z by lia. lia. }
        apply (POST p A1 M2 model1 R2). constructor; try assumption.
        + unfold base_ok. rewrite !(KEPT _) by inl. rewrite G2, !Gs by inl.
          split; [reflexivity|]. split; [exact B3|]. split; [exact B4|].
          intros r Hr. rewrite (KEPT r); [rewrite Gs; [apply Bs; exact Hr|]|]; cbn in Hr; unfold callee_saved; cbn; clear - Hr; intuition congruence.
        + rewrite (KEPT 8%bv) by inl. rewrite Gs by inl. exact Q8.
        + rewrite (KEPT 9%bv) by inl. rewrite Gs by inl. exact Q9.
        + rewrite (KEPT 18%bv) by inl. rewrite Gs by inl. exact Q18.
        + rewrite (KEPT 19%bv) by inl. rewrite Gs by inl. exact Q19.
        + intros Hbc. rewrite (KEPT 20%bv) by inl. rewrite Gs by inl. exact (G20 Hbc).
        + destruct FR as (F1 & F2 & F3 & F4 & F5 & F6). unfold frame.
          split; [|split; [|split; [|split; [|split]]]]; (eapply cellw_agree; [| eapply agree_on_sub; [exact AGf | lia | cbn; lia] | lia | cbn; lia]); assumption.
        + eapply (defined_via_eff L MI HLimg_lo HLrw_img HLerr_rw A0 A1 M1 M2 _ _ (sp - SS) SS EFF ltac:(lia) ltac:(lia)).
          * intros i Hi. eapply hi_unowned; [exact AI0 | lia].
          * intros i Hi Hf. cbn beta in Hf. lia.
          * exact DEF.
        +
          eapply (umapx_via_eff L MI HLimg_lo HLrw_img HLerr_rw 24 Z (nval24 SEGS) ltac:(lia) (nval24_agree SEGS) A0 A1 M0 M2 model0 obj bl bc ents W _ sp U0 AI0 EFF2).
          * lia. * unfold W; cbn; lia. * lia.
          * intros i Hi. eapply hi_unowned; [exact AI0 | lia].
          * intros a Ha Hpa. destruct (umap_foot_hb 24 obj bl bc ents a Ha) as [Hh | ([q m] & Hb & Hba)]; [lia|]. cbn in Hba.
            assert (Hq0 : In (q, m) (live MI A0)).
            { unfold umap_blocks in Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
              - destruct (Z.eqb_spec bc 0); [destruct Hb|]. destruct Hb as [Hb|[]]. injection Hb as <- <-.
                destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia | exact Hin].
              - apply in_map_iff in Hb. destruct Hb as ([q' [k v]] & Hq & Hin). cbn in Hq. injection Hq as <- <-. exact (proj1 (u_node U0 q' k v Hin)). }
            assert (Hq1 : In (q, m) (live MI A1)) by (rewrite (proj1 LADD); right; exact Hq0).
            assert (Hne : p <> q) by (intros <-; apply (proj2 LADD); apply (in_map fst _ (p, m)); exact Hq0).
            pose proof (ai_live_disjoint MI A1 M2 model1 p 24 q m AI2 HinP Hq1 Hne) as Hap. lia.
          * unfold W, SS; cbn; lia.
          * intros q m Hb Hl. rewrite (proj1 LADD). right. exact Hl.
        + eapply cellw_agree; [exact CT1 | | lia | cbn; lia].
          eapply (agree_above_via_eff' A0 A1 M1 M2 _ _ tupp 8 (sp - 48) EFF); [lia | cbn; lia | lia | lia | lia | | |].
          * intros i Hi. apply To1. exact Hi.
          * eapply (cellw_high_defined M1 tupp 8); [exact CT1 | lia | cbn; lia].
          * intros i Hi Hf. cbn beta in Hf. lia.
        + eapply cellw_agree; [exact CK21 | | lia | cbn; lia].
          eapply (agree_above_via_eff' A0 A1 M1 M2 _ _ keyp2 4 (sp - 48) EFF); [lia | cbn; lia | lia | lia | lia | | |].
          * intros i Hi. apply K2o1. exact Hi.
          * eapply (cellw_high_defined M1 keyp2 4); [exact CK21 | lia | cbn; lia].
          * intros i Hi Hf. cbn beta in Hf. lia.
        + eapply (ro_clear_via_eff A0 A1 M0 M2 model0 W _ ROC AI0 EFF2); [| unfold W; cbn; lia].
          intros a Ha. exact (live_offimg' A1 M2 model1 p 24 a AI2 HinP Ha).
    Qed.

    Record core (p : Z) (A : AS MI) (M : mem) (model : Model) (R : bvmap 5 word) : Prop := CORE {
      c_ai : ainv MI A M model;
      c_ms : mstd model;
      c_fs : m_fs model = m_fs model0;
      c_fds : m_fds model = m_fds model0;
      c_regs : base_ok R;
      c_s0 : getr R 8%bv = Z_to_bv 64 obj;
      c_s3 : getr R 19%bv = Z_to_bv 64 key;
      c_a0 : getr R 10%bv = Z_to_bv 64 p;
      c_frame : frame M;
      c_def : defined M (sp - SS) SS;
      c_p0 : 0 < p; c_pc : p + 24 <= alloc_ceiling; c_pal : p mod 16 = 0;
      c_plive : In (p, 24) (live MI A);
      c_pnew : ~ In p (map fst (live MI A0));
      c_n0 : cell8 SEGS M p 0;
      c_nh : cell8 SEGS M (p + 8) key;
      c_nk : cell4 SEGS M (p + 16) key;
      c_nv : cell4 SEGS M (p + 20) 0;
      c_pdef : defined M p 24
    }.

    Ltac base_from HR' Bprev :=
      let Q2 := fresh in let Q3 := fresh in let Q4 := fresh in
      rreg HR' 2%bv Q2; rreg HR' 3%bv Q3; rreg HR' 4%bv Q4;
      let Bc := fresh in let B2 := fresh in let B3 := fresh in let B4 := fresh in let Bs := fresh in
      pose proof Bprev as Bc; destruct Bc as (B2 & B3 & B4 & Bs);
      unfold base_ok; rewrite Q2, Q3, Q4; split; [first [reflexivity | exact B2] |]; split; [exact B3|]; split; [exact B4|];
      let r := fresh "r" in let Hr := fresh "Hr" in
      intros r Hr; rewrite (syms_id_sound _ _ _ _ [21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl r Hr); apply Bs; exact Hr.

    Lemma phaseI : forall p A M model R,
      nst p A M model R ->
      (forall (fx1 : FPState) M' R',
          core p A M' model R' -> getr R' 18%bv = Z_to_bv 64 bc -> getr R' 9%bv = Z_to_bv 64 tupp ->
          frm_zero (@fp_csr fx1) -> fkept_u1 fx fx1 -> fholds fx1 14%bv (ieee (Zlength ents + 1)) -> fholds fx1 15%bv one32 ->
          (bc = 0 \/ Zlength ents = bc) ->
          eff MI A0 A M0 M' W (fun a => p <= a < p + 24) -> live_add p 24 (live MI A0) (live MI A) ->
          umapx MI 24 (nval24 SEGS) A M' obj bl bc ents -> ro_clear L M' ->
          srealizes SEGS (cfg fx1 R' GROW M' model) K) ->
      (forall (fx1 : FPState) M' R',
          core p A M' model R' -> frm_zero (@fp_csr fx1) -> fkept_u1 fx fx1 -> bc <> 0 -> Zlength ents + 1 <= bc ->
          getr R' 18%bv = Z_to_bv 64 bc -> getr R' 20%bv = Z_to_bv 64 (hmod key bc) ->
          eff MI A0 A M0 M' W (fun a => p <= a < p + 24) -> live_add p 24 (live MI A0) (live MI A) ->
          umapx MI 24 (nval24 SEGS) A M' obj bl bc ents ->
          srealizes SEGS (cfg fx1 R' INS M' model) K) ->
      srealizes SEGS (cfg fx R NEWR M model) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn HLimg_lo HLrw_img fx A0 s R0 M0 model0 sp ret obj bl bc keyp tupp keyp2 key ents K CB FRM U0 ASP AST ASK2 CK K2AL HSZ Hlast ROOM2 CONT.
      intros p A M model R NS PRH PINS.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hs1 & Hh1 & Ho1). destruct AST as (Ts1 & Th1 & To1). destruct ASK2 as (K2s1 & K2h1 & K2o1).
      destruct bc_facts as (HbB & Hbcr & Hload & Hsz0).
      destruct NS as [AI MS Hfs Hfds B Q8 Q9 Q18 Q19 Q20 Q10 FR DEF EFF LADD Hp0 Hpc Hpal U CT1 CK1 RC].
      pose proof B as B'. destruct B' as (B2 & B3 & B4 & Bs). pose proof (proj1 CK) as Hkr. cbn in Hkr.
      pose proof (u_obj_lo U) as Hobjlo. pose proof (u_obj_hi U) as Hobjhi.
      assert (HinP : In (p, 24) (live MI A)) by (rewrite (proj1 LADD); left; reflexivity).
      destruct (live_facts' A M model p 24 AI HinP) as (_ & _ & _ & Hpall).
      assert (DEFp : defined M p 24) by (intros i Hi; exact (proj2 (Hpall (p + i) ltac:(lia)))).
      pose proof (u_hdr U) as HD. destruct HD as [Cbl Cbc Cp1 Csz Cmlf Cdef].
      unfold cell8 in CT1, Csz. unfold cell4 in CK1, Cmlf.

      pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (sp - 48); Z_to_bv 64 tupp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 keyp2; sxw key; Z_to_bv 64 (Zlength ents)]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 36); (19%bv, EVar 37)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KDisj (SA (EVar 33) 0) (ELit 40) (SA (EVar 32) 0) (ELit 24); KDisj (SA (EVar 40) 0) (ELit 4) (SA (EVar 32) 0) (ELit 24)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia].
        - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [false; false; false] [EVar 40; EVar 41; EVar 42] []) 50%N.
      { split_scs; try sc_auto1;
          first [ eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]
                | eapply (sc_trap_align4 _ _ _ keyp2); [evs; reflexivity | lia | exact K2AL]
                | eapply (sc_trap_null _ _ _ _ keyp2); [evs; reflexivity | lia]
                | sc_rd_sx CK1
                | sc_so; eapply (defined_sub _ _ _ _ _ DEFp); lia ]. }
      postrun.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRa; rename Rx into Ra end.
      set (M2 := wbytes _ _ _).
      rreg HRa 8%bv Qa8. rreg HRa 2%bv Qa2. rreg HRa 9%bv Qa9. rreg HRa 10%bv Qa10. rreg HRa 11%bv Qa11. rreg HRa 12%bv Qa12.
      rreg HRa 18%bv Qa18. rreg HRa 19%bv Qa19.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRa eq_refl) as Pa. clear HRa HR HK.
      assert (HM2w : forall a : word, ~ (p <= bv_unsigned a < p + 24) -> M2 a = M a).
      { intros a Ha. pose proof (u64_range a). unfold M2.
        rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; try (change (Z.of_nat 8) with 8); lia. }
      assert (Cmlf2 : cellw SEGS M2 (obj + 32) 4 1065353216).
      { eapply cellw_agree; [exact Cmlf | | lia | cbn; lia]. intros i Hi. symmetry. first [apply HM2w | symmetry; apply HM2w]. rewrite u64_of_Z by lia. lia. }

      fp_flw MS F_6ab7c D_6ab7c Qa8 (proj2 Cmlf2) 32 0x6abc0.

      pose (E := Eseed Ra [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (sp - 48); Z_to_bv 64 tupp; Z_to_bv 64 bc; Z_to_bv 64 key; sxw key; Z_to_bv 64 (Zlength ents)]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 36); (19%bv, EVar 37); (11%bv, EVar 38); (12%bv, EVar 39)]) Ra).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (DEFp2 : defined M2 p 24) by (intros i Hi; unfold M2; repeat apply wbytes_grows; apply DEFp; exact Hi).
      assert (HK : know_ok SEGS E M2 []) by constructor.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1; sc_so; eapply (defined_sub _ _ _ _ _ DEFp2); lia. }
      postrun.
      assert (Hsw : word_to_le_bytes 4 (sxw key) = word_to_le_bytes 4 (Z_to_bv 64 key)) by (exact (word_to_le_bytes_swrap 4 key ltac:(cbn; lia))).
      rewrite Hsw. clear Hsw.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRb; rename Rx into Rb end.
      set (M3 := wbytes _ _ _).
      rreg HRb 8%bv Qb8. rreg HRb 2%bv Qb2. rreg HRb 9%bv Qb9. rreg HRb 10%bv Qb10. rreg HRb 12%bv Qb12. rreg HRb 18%bv Qb18. rreg HRb 19%bv Qb19.
      rewrite w_add in Qb12 by lia.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRb eq_refl) as Pb. clear HRb HR HK.

      assert (HM3w : forall a : word, ~ (p <= bv_unsigned a < p + 24) -> M3 a = M a).
      { intros a Ha. pose proof (u64_range a). unfold M3.
        rewrite !wbytes_outside; [apply HM2w; exact Ha | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; try (change (Z.of_nat 8) with 8); try (change (Z.of_nat 4) with 4); lia. }
      assert (HM3g : forall a : word, M a <> None -> M3 a <> None) by (intros a Ha; unfold M3, M2; repeat apply wbytes_grows; exact Ha).
      assert (HM3a : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k p 24 -> agree_on M M3 a k).
      { intros a k Ha Hak H1 i Hi. apply HM3w; rewrite u64_of_Z by lia; clear - H1 Hi; unfold apart in *; lia. }
      assert (AI3 : ainv MI A M3 model).
      { eapply (ai_frame MI); [exact AI | | exact HM3g | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HM3w; intros Hx. exact (proj1 (Hpall (bv_unsigned x) Hx) Ho). }
      assert (EFF3 : eff MI A0 A M0 M3 W (fun a => p <= a < p + 24)).
      { eapply eff_weaken; [eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned; [exact AI3 | unfold W, W_of in Ha; cbn in Ha; lia]]|].
        - eapply eff_store with (F := fun a : Z => p <= a < p + 24); [| exact HM3g]. intros x HF _. apply HM3w. exact HF.
        - intros a [Ha|Ha]; exact Ha. }
      assert (U3 : umapx MI 24 (nval24 SEGS) A M3 obj bl bc ents).
      { eapply (umapx_agree SEGS L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia) A A M M3); [exact U | | intros; assumption].
        intros a Ha. pose proof (foot_low_or_high a Ha). apply HM3w. rewrite u64_of_Z by lia. exact (foot_apart_new A M model p 24 a AI LADD Ha). }
      assert (RC3 : ro_clear L M3).
      { eapply (ro_clear_frame L (fun a => p <= a < p + 24) M M3 RC).
        - intros x Hn. apply HM3w. exact Hn.
        - intros a Hro Ha. exact (live_offimg' A M model p 24 a AI HinP Ha (proj1 Hro)). }
      assert (C3 : forall (Rx : bvmap 5 word), base_ok Rx -> getr Rx 8%bv = Z_to_bv 64 obj -> getr Rx 19%bv = Z_to_bv 64 key -> getr Rx 10%bv = Z_to_bv 64 p ->
                   core p A M3 model Rx).
      { intros Rx HB Q8' Q19' Q10'. constructor; try assumption.
        - destruct FR as (F1 & F2 & F3 & F4 & F5 & F6). unfold frame.
          split; [|split; [|split; [|split; [|split]]]]; (eapply cellw_agree; [| apply HM3a; [lia | lia | unfold apart, SS in *; lia] | lia | cbn; lia]); assumption.
        - intros i Hi. apply HM3g. apply DEF. exact Hi.
        - exact (proj2 LADD).
        - unfold M3, M2, cell8. cellpeel. - unfold M3, M2, cell8. cellpeel. - unfold M3, M2, cell4. cellpeel. - unfold M3, M2, cell4. cellpeel.
        - intros i Hi. apply HM3g. apply DEFp. exact Hi. }
      assert (Bb : base_ok Rb).
      { unfold base_ok. rewrite Qb2, !Pb by inl. split; [reflexivity|]. split; [rewrite Pa by inl; exact B3|]. split; [rewrite Pa by inl; exact B4|].
        intros r Hr. rewrite Pb, Pa; [apply Bs; exact Hr | |]; clear - Hr; cbn in Hr |- *; intuition congruence. }

      fp_fcvt_s_lu MS F_6ab8c D_6ab8c FRM Qb12 (Zlength ents + 1) 0x6abd0.
      pose proof (ieee_range (Zlength ents + 1) ltac:(lia)) as Hie1.
      lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
        assert (Hf14 : fholds fxc 14%bv (ieee (Zlength ents + 1))) by (apply fholds_set_same; lia);
        assert (Hf15 : fholds fxc 15%bv one32) by (apply fholds_set_other; [intros X; discriminate X | apply fholds_set_same; unfold one32; lia]) end.

      pose (E := Eseed Rb [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (sp - 48); Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (Zlength ents + 1); Z_to_bv 64 tupp]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (18%bv, EVar 35); (19%bv, EVar 36); (12%bv, EVar 37); (9%bv, EVar 38)]) Rb).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M3 []) by constructor.
      destruct (Z.eq_dec bc 0) as [Hbc0 | Hbc1].
      { xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N; [split_scs; try sc_auto1|].
        apply (PRH _ M3 R');
          [ apply C3; [base_from HR' Bb | let Q := fresh in rreg HR' 8%bv Q; exact Q | let Q := fresh in rreg HR' 19%bv Q; exact Q | let Q := fresh in rreg HR' 10%bv Q; exact Q]
          | let Q := fresh in rreg HR' 18%bv Q; exact Q
          | let Q := fresh in rreg HR' 9%bv Q; exact Q
          | exact FRM | fk_tac | exact Hf14 | exact Hf15 | left; exact Hbc0 | exact EFF3 | exact LADD | exact U3 | exact RC3 ]. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N; [split_scs; try sc_auto1|].
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
      rreg HRc 18%bv Qc18. rreg HRc 8%bv Qc8. rreg HRc 19%bv Qc19. rreg HRc 10%bv Qc10. rreg HRc 2%bv Qc2. rreg HRc 12%bv Qc12. rreg HRc 9%bv Qc9.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Pc.
      assert (Bc : base_ok Rc) by (base_from HRc Bb). clear HRc HR HK.

      fp_fcvt_s_lu MS F_6ab94 D_6ab94 FRM Qc18 bc 0x6abd8.
      pose proof (ieee_range bc ltac:(lia)) as Hie2.
      lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
        assert (Hg13 : fholds fxc 13%bv (ieee bc)) by (apply fholds_set_same; lia);
        assert (Hg15 : fholds fxc 15%bv one32) by (apply fholds_set_other; [intros X; discriminate X | exact Hf15]);
        assert (Hg14 : fholds fxc 14%bv (ieee (Zlength ents + 1))) by (apply fholds_set_other; [intros X; discriminate X | exact Hf14]) end.
      fp_fari MS F_6ab98 D_6ab98 FRM Hg15 Hg13 (fun md => mul_one_val md bc) 0x6abdc.
      lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
        assert (Hh13 : fholds fxc 13%bv (ieee bc)) by (apply fholds_set_same; lia);
        assert (Hh14 : fholds fxc 14%bv (ieee (Zlength ents + 1))) by (apply fholds_set_other; [intros X; discriminate X | exact Hg14]);
        assert (Hh15 : fholds fxc 15%bv one32) by (apply fholds_set_other; [intros X; discriminate X | exact Hg15]) end.
      fp_flt MS F_6ab9c D_6ab9c Hh13 Hh14 bc (Zlength ents + 1) 0x6abe0.
      set (Rd := regupd Rc 11%bv _).
      assert (Qd : forall r, r <> 11%bv -> getr Rd r = getr Rc r) by (intros r Hr; unfold Rd; apply getr_other; exact Hr).
      assert (Qd11 : getr Rd 11%bv = Z_to_bv 64 (if bc <? Zlength ents + 1 then 1 else 0)) by (unfold Rd; apply getr_same; intros X; discriminate X).
      pose proof (Qd 18%bv ltac:(intros X; discriminate X)) as Qd18. rewrite Qc18 in Qd18.
      pose proof (Qd 8%bv ltac:(intros X; discriminate X)) as Qd8. rewrite Qc8 in Qd8.
      pose proof (Qd 9%bv ltac:(intros X; discriminate X)) as Qd9. rewrite Qc9 in Qd9.
      pose proof (Qd 19%bv ltac:(intros X; discriminate X)) as Qd19. rewrite Qc19 in Qd19.
      pose proof (Qd 10%bv ltac:(intros X; discriminate X)) as Qd10. rewrite Qc10 in Qd10.
      pose proof (Qd 2%bv ltac:(intros X; discriminate X)) as Qd2. rewrite Qc2 in Qd2.
      pose proof (Qd 20%bv ltac:(intros X; discriminate X)) as Qd20. rewrite Pc, Pb, Pa, (Q20 Hbc1) in Qd20 by inl.
      assert (Bd : base_ok Rd).
      { unfold base_ok. rewrite !Qd by (intros X; discriminate X). destruct Bc as (? & ? & ? & Bcs). repeat split; try assumption.
        intros r Hr. rewrite Qd; [apply Bcs; exact Hr|]. clear - Hr. cbn in Hr. intros ->. intuition discriminate. }

      pose (E := Eseed Rd [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (sp - 48); Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (if bc <? Zlength ents + 1 then 1 else 0);
                           Z_to_bv 64 (hmod key bc); Z_to_bv 64 tupp]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (18%bv, EVar 35); (19%bv, EVar 36); (11%bv, EVar 37); (20%bv, EVar 38); (9%bv, EVar 39)]) Rd).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M3 []) by constructor.
      destruct (Z.ltb_spec bc (Zlength ents + 1)) as [Hlt | Hge].
      -
        xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N; [split_scs; try sc_auto1|].
        apply (PRH _ M3 R');
          [ apply C3; [base_from HR' Bd | let Q := fresh in rreg HR' 8%bv Q; exact Q | let Q := fresh in rreg HR' 19%bv Q; exact Q | let Q := fresh in rreg HR' 10%bv Q; exact Q]
          | let Q := fresh in rreg HR' 18%bv Q; exact Q
          | let Q := fresh in rreg HR' 9%bv Q; exact Q
          | exact FRM | fk_tac | exact Hh14 | exact Hh15 | right; lia | exact EFF3 | exact LADD | exact U3 | exact RC3 ].
      -
        xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N; [split_scs; try sc_auto1|].
        apply (PINS _ M3 R');
          [ apply C3; [base_from HR' Bd | let Q := fresh in rreg HR' 8%bv Q; exact Q | let Q := fresh in rreg HR' 19%bv Q; exact Q | let Q := fresh in rreg HR' 10%bv Q; exact Q]
          | exact FRM | fk_tac | exact Hbc1 | lia
          | let Q := fresh in rreg HR' 18%bv Q; exact Q
          | let Q := fresh in rreg HR' 20%bv Q; exact Q
          | exact EFF3 | exact LADD | exact U3 ].
    Qed.

    Lemma finish : forall (fx1 : FPState) p A M model R (bl2 bc2 v : Z) (ents2 ents' : list (Z * (Z * Z))) (rh : bool) (F : Z -> Prop),
      ainv MI A M model -> mstd model -> m_fs model = m_fs model0 -> m_fds model = m_fds model0 -> frm_zero (@fp_csr fx1) -> fkept_u1 fx fx1 ->
      base_ok R -> getr R 8%bv = Z_to_bv 64 obj -> getr R 10%bv = Z_to_bv 64 p -> frame M ->
      cell8 SEGS M (obj + 24) (Zlength ents2) -> defined M obj 40 -> 0 <= Zlength ents2 < 2 ^ 60 ->
      (forall M', (forall a : word, ~ (obj + 24 <= bv_unsigned a < obj + 32) -> M' a = M a) -> (forall a : word, M a <> None -> M' a <> None) ->
                  cell8 SEGS M' (obj + 24) (Zlength ents2 + 1) -> umapx MI 24 (nval24 SEGS) A M' obj bl2 bc2 ents') ->
      In (p, (key, v)) ents' -> v = 0 -> Permutation ents' ((p, (key, 0)) :: ents) ->
      (rh = false -> bl2 = bl /\ bc2 = bc) -> (rh = true -> (bc = 0 \/ Zlength ents = bc) /\ bc2 = bseq_next bc) ->
      lapply (live MI A0) (LAdd p 24 :: (if rh then LAdd bl2 (8 * bc2) :: (if bc =? 0 then [] else [LDel bl]) else [])) (live MI A) ->
      eff MI A0 A M0 M W F -> (forall a, F a -> umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl2 bc2 ents' a) ->
      (forall a, F a -> ~ in_ranges (ly_img L) a) ->
      srealizes SEGS (cfg fx1 R SIZE_PC M model) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc keyp2 key ents K CB U0 ASP CONT.
      intros fx1 p A M model R bl2 bc2 v ents2 ents' rh F AI MS Hfs Hfds FZ FK B Q8 Q10 FR Csz HDEF Hszr HU Hin Hv PERM Hrf Hrt LAP EFF HF FOFF.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hs1 & Hh1 & Ho1). pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
      pose proof B as B'. destruct B' as (B2 & B3 & B4 & Bs). unfold cell8 in Csz.
      pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (sp - 48); Z_to_bv 64 (Zlength ents2)]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      xruns HR HK 100%nat STOPS (SCR [] [EVar 35] []) 50%N.
      { split_scs; try sc_auto1. sc_so. eapply (defined_sub _ _ _ _ _ HDEF); lia. }
      postrun. rewrite w_add by lia.
      set (M' := wbytes M _ _).
      assert (HMw : forall a : word, ~ (obj + 24 <= bv_unsigned a < obj + 32) -> M' a = M a).
      { intros a Ha. pose proof (u64_range a). unfold M'.
        rewrite wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      assert (HMg : forall a : word, M a <> None -> M' a <> None) by (intros a Ha; unfold M'; apply wbytes_grows; exact Ha).
      assert (Csz' : cell8 SEGS M' (obj + 24) (Zlength ents2 + 1)) by (unfold M', cell8; cellpeel).
      eapply (epilogue fx1 A M' model R' p v bl2 bc2 ents' true rh (fun a => F a \/ obj + 24 <= a < obj + 32)).
      - eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HMw; intros Hx. exact (hi_unowned A M model (bv_unsigned x) AI ltac:(lia) Ho).
      - exact MS. - exact Hfs. - exact Hfds. - exact FZ. - exact FK.
      - base_from HR' B.
      - destruct FR as (F1 & F2 & F3 & F4 & F5 & F6). unfold frame, M', cell8. unfold SS in *.
        split; [|split; [|split; [|split; [|split]]]]; cellpeel.
      - rreg HR' 10%bv Q. exact Q.
      - rreg HR' 11%bv Q. exact Q.
      - exact (HU M' HMw HMg Csz').
      - exact Hin.
      - intros HT. discriminate HT.
      - intros _. split; [exact Hv | exact PERM].
      - exact Hrf. - exact Hrt.
      - cbn [app]. exact LAP.
      - eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned; [eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity] | unfold W, W_of in Ha; cbn in Ha; lia]].
        + eapply eff_store with (F := fun a : Z => obj + 24 <= a < obj + 32); [| exact HMg]. intros x HFx _. apply HMw. exact HFx.
        + intros x Ho. pose proof (u64_range x). apply HMw; intros Hx. exact (hi_unowned A M model (bv_unsigned x) AI ltac:(lia) Ho).
      - intros a [Ha | Ha]; [exact (HF a Ha) | left; left; lia].
      - intros a [Ha | Ha]; [exact (FOFF a Ha) | intros Hi; pose proof (HLimg_lo _ Hi); lia].
    Qed.

    #[local] Notation ent := (Z * (Z * Z))%type.

    Definition hda (l : list ent) (t : Z) : Z := match l with [] => t | b :: _ => fst b end.
    Fixpoint lnk (M : mem) (Ls : list ent) (t : Z) : Prop :=
      match Ls with
      | [] => True
      | a :: Ls' => cell8 SEGS M (fst a) (hda Ls' t) /\ lnk M Ls' t
      end.
    Lemma lnk_chain : forall M Ls, chain SEGS M Ls <-> lnk M Ls 0.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret bc keyp2 ents CB ROOM2.
      intros M Ls. induction Ls as [|[a v] Ls IH]; cbn; [tauto|].
      destruct Ls as [|[b v'] Ls']; cbn in *; tauto.
    Qed.
    Lemma hd_app : forall (A B : list ent) t, hda (A ++ B) t = hda A (hda B t).
    Proof using. intros [|a A] B t; reflexivity. Qed.
    Lemma hdaddr_hda : forall (A : list ent), hdaddr A = hda A 0.
    Proof using. intros [|[a v] A]; reflexivity. Qed.
    Lemma lnk_app : forall M A B t, lnk M (A ++ B) t <-> lnk M A (hda B t) /\ lnk M B t.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret bc keyp2 ents CB ROOM2.
      intros M A B t. induction A as [|a A IH]; cbn; [tauto|].
      rewrite hd_app. rewrite IH. destruct A as [|a' A']; (first [solve [clear; cbn; tauto] | cbn; tauto]).
    Qed.
    Lemma lnk_agree : forall M M' Ls t, lnk M Ls t -> (forall a, In a Ls -> agree_on M M' (fst a) 8) ->
      (forall a, In a Ls -> 0 <= fst a /\ fst a + 8 <= 2 ^ 64) -> lnk M' Ls t.
    Proof using sp keyp2.
      intros M M' Ls t. induction Ls as [|a Ls IH]; intros HL HA HR; cbn in *; [exact I|].
      destruct HL as [Hc HL]. split.
      - pose proof (HR a (or_introl eq_refl)). eapply cellw_agree; [exact Hc | apply HA; left; reflexivity | lia | cbn; lia].
      - apply IH; [exact HL | intros b Hb; apply HA; right; exact Hb | intros b Hb; apply HR; right; exact Hb].
    Qed.

    Definition lasta (t : Z) (l1 : list ent) : Z := match l1 with [] => t | _ => fst (last l1 (0, (0, 0))) end.

    Lemma nodup_app_ne : forall (l1 l2 : list ent) b b',
      List.NoDup (map fst (l1 ++ l2)) -> In b l1 -> In b' l2 -> fst b <> fst b'.
    Proof using.
      intros l1 l2 b b' Hnd H1 H2 Heq.
      revert Hnd H1. induction l1 as [|x l1 IH]; intros Hnd H1; [destruct H1|].
      cbn in Hnd. inversion Hnd as [|y l Hni Hnd']. subst.
      destruct H1 as [<-|H1].
      - apply Hni. rewrite Heq, map_app. apply in_app_iff. right. apply in_map. exact H2.
      - exact (IH Hnd' H1).
    Qed.

    Lemma umapx_link : forall A M M' (p bl2 bc2 : Z) (l1 l2 : list ent),
      umapx MI 24 (nval24 SEGS) A M obj bl2 bc2 (l1 ++ l2) -> bc2 <> 0 -> Zlength (l1 ++ l2) + 1 <= bc2 ->
      In (p, 24) (live MI A) -> 0 < p -> p + 24 <= alloc_ceiling -> p mod 16 = 0 ->
      (forall q m, In (q, m) (umap_blocks 24 bl2 bc2 (l1 ++ l2)) -> apart p 24 q m) ->
      cell8 SEGS M' p (hdaddr l2) -> cell8 SEGS M' (p + 8) key -> cell4 SEGS M' (p + 16) key -> cell4 SEGS M' (p + 20) 0 ->
      cell8 SEGS M' (lasta (obj + 16) l1) p -> cell8 SEGS M' (obj + 24) (Zlength (l1 ++ l2) + 1) ->
      (forall x : word, M x <> None -> M' x <> None) ->
      (forall a, umap_foot 24 obj bl2 bc2 (l1 ++ l2) a -> ~ (lasta (obj + 16) l1 <= a < lasta (obj + 16) l1 + 8) -> ~ (obj + 24 <= a < obj + 32) ->
                 ~ (bl2 <= a < bl2 + 8 * bc2) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall i, 0 <= i < bc2 -> exists b', cell8 SEGS M' (bl2 + 8 * i) b' /\ bucket_ok obj bc2 (l1 ++ (p, (key, 0)) :: l2) i b') ->
      umapx MI 24 (nval24 SEGS) A M' obj bl2 bc2 (l1 ++ (p, (key, 0)) :: l2).
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn A0 s R0 M0 model0 sp ret obj bc keyp keyp2 key ents CB ASP CK ROOM2.
      intros A M M' p bl2 bc2 l1 l2 U Hbc Hload Hpl Hp0 Hpc Hpal Hpa Cn Ch Ck Cv Cpred Csz HG HM HB.
      pose proof ceiling_lt as Hcl. destruct ASP as (Hs1 & Hh1 & _). destruct SPF as (_ & Hsplo & Hsphi & _). unfold SS in Hsplo.
      pose proof (proj1 CK) as Hkr.
      destruct U as [HD Hoal Holo Hohi Hbseq Hload0 Hblive Hblal Hbllo Hblhi Hblobj Hbkt Hndup Hch Hnode Hapart].
      destruct HD as [Cbl Cbc Cp1 Csz0 Cmlf Cdef].
      pose proof (Hbllo Hbc) as Hbl0. pose proof (Hblobj Hbc) as Hblo.

      assert (NF : forall q k v, In (q, (k, v)) (l1 ++ l2) -> 0 < q /\ q + 24 <= 2 ^ 47 /\ apart q 24 obj 40 /\ apart q 24 bl2 (8 * bc2) /\ apart p 24 q 24).
      { intros q k v Hin. destruct (Hnode q k v Hin) as (_ & Hq0 & Hq1 & _ & _ & _ & _ & _ & Hqo & Hqb).
        split; [exact Hq0|]. split; [exact Hq1|]. split; [exact Hqo|]. split; [exact (Hqb Hbc)|].
        apply Hpa. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (q, (k, v)). split; [reflexivity | exact Hin]. }

      assert (Hpred : (l1 = [] /\ lasta (obj + 16) l1 = obj + 16)
                      \/ (exists r y, l1 = r ++ [y] /\ lasta (obj + 16) l1 = fst y /\ In y (l1 ++ l2))).
      { destruct l1 as [|e l1'] eqn:HL; [left; split; reflexivity | right].
        exists (removelast l1), (last l1 (0, (0, 0))). rewrite <- HL.
        assert (Hne : l1 <> []) by (rewrite HL; discriminate).
        split; [exact (app_removelast_last _ Hne)|]. split; [rewrite HL; reflexivity|].
        apply in_app_iff. left. rewrite (app_removelast_last (0, (0, 0)) Hne) at 2. apply in_app_iff. right. left. reflexivity. }

      assert (AGt : forall q k v, In (q, (k, v)) (l1 ++ l2) -> agree_on M M' (q + 8) 16).
      { intros q k v Hin. destruct (NF q k v Hin) as (Hq0 & Hq1 & Hqo & Hqb & Hqp). intros i Hi. apply HM.
        - right. right. exists q. split; [apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin] | lia].
        - destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [unfold apart in Hqo; lia|].
          destruct y as [yq [yk yv]]. cbn. destruct (Z.eq_dec yq q) as [->|Hne]; [lia|].
          pose proof (Hapart yq q ltac:(apply in_map_iff; exists (yq, (yk, yv)); split; [reflexivity | exact Hy]) ltac:(apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin]) Hne) as Hap.
          unfold apart in Hap. lia.
        - unfold apart in Hqo. lia.
        - unfold apart in Hqb. lia. }
      assert (AGn : forall q k v, In (q, (k, v)) (l1 ++ l2) -> q <> lasta (obj + 16) l1 -> agree_on M M' q 8).
      { intros q k v Hin Hne. destruct (NF q k v Hin) as (Hq0 & Hq1 & Hqo & Hqb & Hqp). intros i Hi. apply HM.
        - right. right. exists q. split; [apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin] | lia].
        - destruct Hpred as [[_ HL] | (r & y & HL & Hly & Hy)]; [rewrite HL in *; unfold apart in Hqo; lia|].
          rewrite Hly in *. destruct y as [yq [yk yv]]. cbn in *.
          pose proof (Hapart yq q ltac:(apply in_map_iff; exists (yq, (yk, yv)); split; [reflexivity | exact Hy]) ltac:(apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin]) (not_eq_sym Hne)) as Hap.
          unfold apart in Hap. lia.
        - unfold apart in Hqo. lia.
        - unfold apart in Hqb. lia. }
      assert (Hlen : Zlength (l1 ++ (p, (key, 0)) :: l2) = Zlength (l1 ++ l2) + 1).
      { unfold Zlength. rewrite !length_app. cbn [length]. lia. }
      assert (HpN : ~ In p (map fst (l1 ++ l2))).
      { intros Hin. apply in_map_iff in Hin. destruct Hin as ([q [k v]] & Hq & Hin). cbn in Hq. subst q.
        destruct (NF p k v Hin) as (_ & _ & _ & _ & Hap). unfold apart in Hap. lia. }
      pose proof Hndup as NDL. apply base.NoDup_ListNoDup in NDL.
      constructor.
      - constructor.
        + eapply cellw_agree; [exact Cbl | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
          destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [lia|]. destruct y as [yq [yk yv]]. destruct (NF yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
        + eapply cellw_agree; [exact Cbc | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
          destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [lia|]. destruct y as [yq [yk yv]]. destruct (NF yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
        + destruct Hpred as [[HL Hla] | (r & y & HL & Hla & Hy)].
          * rewrite HL in *. cbn [app hdaddr]. rewrite Hla in Cpred. exact Cpred.
          * replace (hdaddr (l1 ++ (p, (key, 0)) :: l2)) with (hdaddr (l1 ++ l2)) by (rewrite HL, <- !app_assoc; destruct r as [|[? ?] ?]; reflexivity).
            eapply cellw_agree; [exact Cp1 | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
            rewrite Hla. destruct y as [yq [yk yv]]. destruct (NF yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
        + rewrite Hlen. exact Csz.
        + eapply cellw_agree; [exact Cmlf | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
          destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [lia|]. destruct y as [yq [yk yv]]. destruct (NF yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
        + intros i Hi. apply HG. apply Cdef. exact Hi.
      - exact Hoal. - exact Holo. - exact Hohi. - exact Hbseq.
      - rewrite Hlen. exact Hload.
      - exact Hblive. - exact Hblal. - exact Hbllo. - exact Hblhi. - exact Hblobj.
      - exact HB.
      - rewrite map_app. cbn [map fst]. apply (proj2 (base.NoDup_ListNoDup _)). apply (proj2 (NoDup_Add (Add_app p _ _))).
        rewrite <- map_app. split; [exact NDL | exact HpN].
      -
        apply lnk_chain. apply lnk_chain in Hch. apply lnk_app in Hch. destruct Hch as [L1 L2].
        apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- hdaddr_hda; exact Cn |]].
        + destruct Hpred as [[HL _] | (r & y & HL & Hla & Hy)]; [rewrite HL; exact I|].
          rewrite HL in L1 |- *. apply lnk_app in L1. destruct L1 as [L1 _]. apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- Hla; exact Cpred | exact I]].
          assert (NDl1 : List.NoDup (map fst l1)) by (rewrite map_app in NDL; exact (NoDup_app_remove_r _ _ NDL)). rewrite HL in NDl1.
          eapply lnk_agree; [exact L1 | |].
          * intros a Ha. destruct a as [q [k v]]. apply (AGn q k v); [apply in_app_iff; left; rewrite HL; apply in_app_iff; left; exact Ha|].
            rewrite Hla. exact (nodup_app_ne r [y] (q, (k, v)) y NDl1 Ha (or_introl eq_refl)).
          * intros a Ha. destruct a as [q [k v]]. destruct (NF q k v ltac:(apply in_app_iff; left; rewrite HL; apply in_app_iff; left; exact Ha)) as (Hq0 & Hq1 & _). cbn. lia.
        + eapply lnk_agree; [exact L2 | |].
          * intros a Ha. destruct a as [q [k v]]. apply (AGn q k v); [apply in_app_iff; right; exact Ha|].
            destruct Hpred as [[HL Hla] | (r & y & HL & Hla & Hy)]; rewrite Hla.
            -- destruct (NF q k v ltac:(apply in_app_iff; right; exact Ha)) as (_ & _ & Hqo & _). unfold apart in Hqo. lia.
            -- apply not_eq_sym. apply (nodup_app_ne l1 l2 y (q, (k, v)) NDL); [rewrite HL; apply in_app_iff; right; left; reflexivity | exact Ha].
          * intros a Ha. destruct a as [q [k v]]. destruct (NF q k v ltac:(apply in_app_iff; right; exact Ha)) as (Hq0 & Hq1 & _). cbn. lia.
      -
        intros q k v Hin. apply in_app_iff in Hin. destruct Hin as [Hin | [Hin | Hin]].
        2: { injection Hin as <- <- <-.
             split; [exact Hpl|]. split; [exact Hp0|]. split; [lia|]. split; [exact Hpal|]. split; [exact Ch|]. split; [exact Ck|]. split; [lia|].
             split; [exact Cv|]. split; [unfold apart; lia|]. intros _. apply Hpa. unfold umap_blocks. destruct (Z.eqb_spec bc2 0); [lia|]. apply in_app_iff. left. left. reflexivity. }
        all: assert (Hin' : In (q, (k, v)) (l1 ++ l2)) by (apply in_app_iff; tauto).
        all: destruct (Hnode q k v Hin') as (Hlv & Hq0 & Hq1 & Hqal & Hh & Hk & Hkr' & Hv & Hqo & Hqb); pose proof (AGt q k v Hin') as AG.
        all: split; [exact Hlv|]; split; [exact Hq0|]; split; [exact Hq1|]; split; [exact Hqal|].
        all: split; [eapply cellw_agree; [exact Hh | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | cbn; lia]|].
        all: split; [eapply cellw_agree; [exact Hk | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | cbn; lia]|].
        all: split; [exact Hkr'|].
        all: split; [eapply nval24_agree; [exact Hv | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | lia]|].
        all: split; [exact Hqo | exact Hqb].
      -
        intros q q' Hq Hq' Hne. rewrite map_app in Hq, Hq'. cbn [map fst] in Hq, Hq'.
        assert (Hcase : forall z, In z (map fst l1 ++ p :: map fst l2) -> z = p \/ In z (map fst (l1 ++ l2))).
        { intros z Hz. rewrite map_app. apply in_app_iff in Hz. destruct Hz as [Hz|[<-|Hz]]; [right; apply in_app_iff; left; exact Hz | left; reflexivity | right; apply in_app_iff; right; exact Hz]. }
        destruct (Hcase q Hq) as [-> | Hq2]; destruct (Hcase q' Hq') as [-> | Hq2'].
        + exfalso. exact (Hne eq_refl).
        + apply in_map_iff in Hq2'. destruct Hq2' as ([z [k v]] & Hz & Hin). cbn in Hz. subst z. exact (proj2 (proj2 (proj2 (proj2 (NF q' k v Hin))))).
        + apply in_map_iff in Hq2. destruct Hq2 as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
          pose proof (proj2 (proj2 (proj2 (proj2 (NF q k v Hin))))) as Hap. unfold apart in *. lia.
        + exact (Hapart q q' Hq2 Hq2' Hne).
    Qed.

    Lemma umap_foot_mono : forall bl2 bc2 (l1 l2 : list ent) e a,
      umap_foot 24 obj bl2 bc2 (l1 ++ l2) a -> umap_foot 24 obj bl2 bc2 (l1 ++ e :: l2) a.
    Proof using obj.
      intros bl2 bc2 l1 l2 e a [H|[H|(q & Hq & Ha)]]; [left; exact H | right; left; exact H | right; right].
      exists q. split; [|exact Ha]. rewrite map_app in Hq |- *. cbn. apply in_app_iff in Hq. apply in_app_iff. destruct Hq; [left | right; right]; assumption.
    Qed.

    Lemma phaseF_pn : forall (fx1 : FPState) p A M model R (bl2 bc2 : Z) (ents2 : list ent) (rh : bool) (b : Z) (F : Z -> Prop),
      core p A M model R -> frm_zero (@fp_csr fx1) -> fkept_u1 fx fx1 -> bc2 <> 0 -> Zlength ents + 1 <= bc2 ->
      getr R 18%bv = Z_to_bv 64 bc2 -> getr R 14%bv = Z_to_bv 64 b ->
      bucket_ok obj bc2 ents2 (hmod key bc2) b -> b <> 0 ->
      umapx MI 24 (nval24 SEGS) A M obj bl2 bc2 ents2 -> Permutation ents2 ents ->
      (forall q m, In (q, m) (umap_blocks 24 bl2 bc2 ents2) -> apart p 24 q m) ->
      (rh = false -> bl2 = bl /\ bc2 = bc) -> (rh = true -> (bc = 0 \/ Zlength ents = bc) /\ bc2 = bseq_next bc) ->
      lapply (live MI A0) (LAdd p 24 :: (if rh then LAdd bl2 (8 * bc2) :: (if bc =? 0 then [] else [LDel bl]) else [])) (live MI A) ->
      eff MI A0 A M0 M W F -> (forall a, F a -> p <= a < p + 24 \/ umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl2 bc2 ents2 a) ->
      (forall a, F a -> ~ in_ranges (ly_img L) a) ->
      srealizes SEGS (cfg fx1 R PN_PC M model) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc keyp keyp2 key ents K CB U0 ASP CK HSZ ROOM2 CONT.
      intros fx1 p A M model R bl2 bc2 ents2 rh b F CO FZ FK Hbc2 Hload Q18 Q14 Hbok Hbnz U2 PERM2 Hpa Hrf Hrt LAP EFF HF FOFF.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg & HssN & HssD). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hs1 & Hh1 & Ho1). pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
      pose proof (proj1 CK) as Hkr. cbn in Hkr.
      destruct CO as [AI MS Hfs Hfds B Q8 Q19 Q10 FR DEF Hp0 Hpc Hpal Hpl Hpnew Cn0 Cnh Cnk Cnv DEFp].
      assert (Hlen : Zlength ents2 = Zlength ents) by (unfold Zlength; rewrite (Permutation_length PERM2); reflexivity).
      pose proof (h_def (u_hdr U2)) as HDEF. pose proof (h_size (u_hdr U2)) as Csz.

      assert (HS : exists l1 l2 q0, ents2 = l1 ++ l2 /\ lasta (obj + 16) l1 = b /\ q0 = hdaddr l2 /\ cell8 SEGS M b q0
                   /\ 0 < b /\ b + 8 <= 2 ^ 47 /\ defined M b 8 /\ apart p 24 b 8 /\ (forall a, b <= a < b + 8 -> ~ owned MI A a)
                   /\ (b + 8 <= alloc_ceiling \/ b = obj + 16)
                   /\ (forall a, b <= a < b + 8 -> umap_foot 24 obj bl2 bc2 ents2 a)
                   /\ (l1 = [] -> hmod key bc2 = hmod (hdkey ents2) bc2) /\ b mod 8 = 0).
      { destruct Hbok as [Hb0 | [Hbn | (Hbs & Hne & Hch)]]; [exfalso; exact (Hbnz Hb0) | |].
        - destruct (in_split_ents Z b ents2 Hbn) as (l1 & kb & vb & l2 & HE).
          destruct (u_node U2 b kb vb ltac:(rewrite HE; apply in_app_iff; right; left; reflexivity)) as (Hlv & Hb0 & Hb1 & Hbal & _ & _ & _ & _ & Hbo & _).
          destruct (live_facts' A M model b 24 AI Hlv) as (_ & _ & Hbc & Hall).
          exists (l1 ++ [(b, (kb, vb))]), l2, (hdaddr l2). rewrite HE, <- app_assoc. cbn [app].
          split; [reflexivity|]. split; [unfold lasta; rewrite last_last; destruct l1; reflexivity|]. split; [reflexivity|].
          split; [apply (chain_at Z M l1 b kb vb l2); rewrite <- HE; exact (u_chain U2)|].
          split; [lia|]. split; [lia|]. split; [intros i Hi; exact (proj2 (Hall (b + i) ltac:(lia)))|].
          split; [eapply (apart_sub' p 24 b 24); [apply Hpa; unfold umap_blocks; apply in_app_iff; right; apply in_map_iff; exists (b, (kb, vb)); split; [reflexivity | rewrite HE; apply in_app_iff; right; left; reflexivity] | lia]|].
          split; [intros a Ha; exact (proj1 (Hall a ltac:(lia)))|].
          split; [left; lia|].
          split; [intros a Ha; right; right; exists b; split; [rewrite <- HE; exact Hbn | lia]|].
          split; [intros HL; destruct l1; discriminate HL|]. apply align16_8. exact Hbal.
        - exists (@nil ent), ents2, (hdaddr ents2). subst b.
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (h_p1 (u_hdr U2))|].
          split; [lia|]. split; [lia|]. split; [eapply (defined_sub _ _ _ _ _ HDEF); lia|].
          split; [unfold apart; lia|]. split; [intros a Ha; apply (hi_unowned A M model); [exact AI | lia]|].
          split; [right; reflexivity|]. split; [intros a Ha; left; lia|]. split; [intros _; exact Hch|].
          pose proof (u_obj_al U2) as Hoal. rewrite Z.add_comm. replace 16 with (8 * 2) by reflexivity. apply align8_add. exact Hoal. }
      destruct HS as (l1 & l2 & q0 & HE & Hla & -> & Cb & Hb0 & Hb1 & DEFb & Hpb & Hbown & Hblh & Hbfoot & Hch & HbAL).
      unfold cell8 in Cb. pose proof (proj1 Cb) as Hq0r.
      pose proof B as B'. destruct B' as (B2 & B3 & B4 & Bs).
      pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (sp - 48); Z_to_bv 64 bc2; Z_to_bv 64 key; Z_to_bv 64 b; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (hdaddr l2)]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (18%bv, EVar 35); (19%bv, EVar 36); (14%bv, EVar 37)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 37) 0) (ELit 8)]).
      { repeat apply Forall_cons; try apply Forall_nil. eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | unfold apart in Hpb; lia]. }
      xruns HR HK 100%nat STOPS (SCR [false] [EVar 40] []) 50%N.
      { split_scs; try sc_auto1; first [ eapply (sc_trap_align _ _ _ _ b); [evs; reflexivity | lia | exact HbAL]
                                         | sc_so; first [eapply (defined_sub _ _ _ _ _ DEFp); lia | eapply (defined_sub _ _ _ _ _ DEFb); lia] ]. }
      postrun.
      set (M2 := wbytes (wbytes M _ _) _ _).
      assert (HM2w : forall a : word, ~ (p <= bv_unsigned a < p + 8) -> ~ (b <= bv_unsigned a < b + 8) -> M2 a = M a).
      { intros a H1 H2. pose proof (u64_range a). unfold M2.
        rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      assert (HM2g : forall a : word, M a <> None -> M2 a <> None) by (intros a Ha; unfold M2; repeat apply wbytes_grows; exact Ha).
      assert (AI2 : ainv MI A M2 model).
      { eapply (ai_frame MI); [exact AI | | exact HM2g | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HM2w; intros Hx.
        - destruct (live_facts' A M model p 24 AI Hpl) as (_ & _ & _ & Hall). exact (proj1 (Hall (bv_unsigned x) ltac:(lia)) Ho).
        - exact (Hbown (bv_unsigned x) Hx Ho). }
      assert (Hfoot_p : forall a, umap_foot 24 obj bl2 bc2 ents2 a -> ~ (p <= a < p + 24)).
      { intros a Ha Hpa'. destruct (umap_foot_hb 24 obj bl2 bc2 ents2 a Ha) as [Hh | ([q m] & Hq & Hqa)]; [lia|]. cbn in Hqa.
        pose proof (Hpa q m Hq) as Hap. unfold apart in Hap.
        assert (Hm : 0 < m).
        { unfold umap_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
          - destruct (Z.eqb_spec bc2 0); [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as <- <-. pose proof (u_bseq U2) as HB. unfold BSEQ in HB. cbn in HB. lia.
          - apply in_map_iff in Hq. destruct Hq as (e & He & _). injection He as _ <-. lia. }
        lia. }
      eapply (finish fx1 p A M2 model R' bl2 bc2 0 ents2 (l1 ++ (p, (key, 0)) :: l2) rh (fun a => F a \/ p <= a < p + 8 \/ b <= a < b + 8)).
      - exact AI2. - exact MS. - exact Hfs. - exact Hfds. - exact FZ. - exact FK.
      - base_from HR' B.
      - rreg HR' 8%bv Q. exact Q.
      - rreg HR' 10%bv Q. exact Q.
      - destruct FR as (F1 & F2 & F3 & F4 & F5 & F6). unfold frame, M2, cell8. unfold SS in *.
        split; [|split; [|split; [|split; [|split]]]]; cellpeel.
      - unfold M2, cell8. pose proof Csz as Csz'. unfold cell8 in Csz'. cellpeel.
      - intros i Hi. apply HM2g. apply HDEF. exact Hi.
      - pose proof (u_load U2). pose proof (u_bseq U2) as HB. unfold BSEQ in HB. cbn in HB. unfold Zlength in *. lia.
      -
        intros M' HM'w HM'g Csz'. rewrite HE in U2, Hpa.
        eapply (umapx_link A M M' p bl2 bc2 l1 l2 U2 Hbc2 ltac:(rewrite <- HE; lia) Hpl Hp0 Hpc Hpal Hpa).
        + assert (C2n : cell8 SEGS M2 p (hdaddr l2)) by (unfold M2, cell8; cellpeel).
          eapply cellw_agree; [exact C2n | | lia | cbn; lia]. intros i Hi. apply HM'w. rewrite u64_of_Z by lia. lia.
        + eapply cellw_agree; [exact Cnh | | lia | cbn; lia]. intros i Hi. rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM2w; rewrite u64_of_Z by lia; unfold apart in Hpb; lia.
        + eapply cellw_agree; [exact Cnk | | lia | cbn; lia]. intros i Hi. rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM2w; rewrite u64_of_Z by lia; unfold apart in Hpb; lia.
        + eapply cellw_agree; [exact Cnv | | lia | cbn; lia]. intros i Hi. rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM2w; rewrite u64_of_Z by lia; unfold apart in Hpb; lia.
        + rewrite Hla. assert (C2b : cell8 SEGS M2 b p) by (unfold M2, cell8; cellpeel).
          eapply cellw_agree; [exact C2b | | lia | cbn; lia]. intros i Hi. apply HM'w. rewrite u64_of_Z by lia. lia.
        + rewrite <- HE. exact Csz'.
        + intros x Hx. apply HM'g, HM2g, Hx.
        + rewrite Hla. intros a Ha Hnb Hnsz Hnbl. pose proof (foot_low_or_high_gen A M model bl2 bc2 _ a AI U2 Ha) as Har.
          rewrite HM'w by (rewrite u64_of_Z by lia; lia). apply HM2w; rewrite u64_of_Z by lia; [| exact Hnb].
          pose proof (Hfoot_p a ltac:(rewrite HE; exact Ha)). lia.
        +
          intros i Hi. rewrite <- HE in *. destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split.
          * pose proof (u_bl_lo U2 Hbc2). pose proof (u_bl_hi U2). pose proof (u_bl_obj U2 Hbc2) as Hblo.
            eapply cellw_agree; [exact Cb' | | lia | cbn; lia]. intros j Hj.
            rewrite HM'w by (rewrite u64_of_Z by lia; unfold apart in Hblo; lia).
            apply HM2w; rewrite u64_of_Z by lia.
            -- pose proof (Hfoot_p (bl2 + 8 * i + j) ltac:(right; left; split; [exact Hbc2 | lia])). lia.
            -- intros Hx. pose proof (Hbfoot (bl2 + 8 * i + j) Hx) as Hf.

               destruct Hf as [Hh | [[_ Hba] | (q & Hq & Hqa)]]; [unfold apart in Hblo; lia | | ].
               ++ unfold apart in Hblo. destruct Hblh as [Hlow | Hhigh]; [| lia].
                  destruct Hbok as [Hb0' | [Hbn | (Hbs & _)]]; [exfalso; exact (Hbnz Hb0') | | lia].
                  apply in_map_iff in Hbn. destruct Hbn as ([z [kz vz]] & Hz & Hin). cbn in Hz. subst z.
                  destruct (u_node U2 b kz vz Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hqb). pose proof (Hqb Hbc2) as Hap. unfold apart in Hap. lia.
               ++ apply in_map_iff in Hq. destruct Hq as ([z [kz vz]] & Hz & Hin). cbn in Hz. subst z.
                  destruct (u_node U2 q kz vz Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hqb). pose proof (Hqb Hbc2) as Hap. unfold apart in Hap. lia.
          * destruct Hok' as [H0 | [Hn | (Hs & Hne & Hi')]]; [left; exact H0 | right; left | right; right].
            -- rewrite HE in Hn. rewrite map_app in Hn |- *. cbn. apply in_app_iff in Hn. apply in_app_iff. destruct Hn; [left | right; right]; assumption.
            -- split; [exact Hs|]. split; [destruct l1; discriminate|]. rewrite Hi'. rewrite HE.
               destruct l1 as [|e l1']; [cbn [app hdkey fst snd]; pose proof (Hch eq_refl) as Hc; rewrite HE in Hc; cbn [app] in Hc; symmetry; exact Hc | reflexivity].
      - apply in_app_iff. right. left. reflexivity.
      - reflexivity.
      - eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- HE. exact PERM2.
      - exact Hrf. - exact Hrt. - exact LAP.
      - eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned; [exact AI2 | unfold W, W_of in Ha; cbn in Ha; lia]].
        eapply eff_store with (F := fun a : Z => p <= a < p + 8 \/ b <= a < b + 8); [| exact HM2g].
        intros x HFx _. apply HM2w; intros Hx; apply HFx; [left | right]; exact Hx.
      - intros a [Ha | [Ha | Ha]].
        + destruct (HF a Ha) as [H|[H|H]]; [right; right; right; exists p; split; [rewrite map_app; apply in_app_iff; right; left; reflexivity | lia] | left; exact H | right; rewrite HE in H; exact (umap_foot_mono _ _ _ _ _ _ H)].
        + right. right. right. exists p. split; [rewrite map_app; apply in_app_iff; right; left; reflexivity | lia].
        + right. pose proof (Hbfoot a Ha) as H. rewrite HE in H. exact (umap_foot_mono _ _ _ _ _ _ H).
      - intros a [Ha | [Ha | Ha]] Hi.
        + exact (FOFF a Ha Hi).
        + exact (live_offimg' A M model p 24 a AI Hpl ltac:(lia) Hi).
        + pose proof (HLimg_lo _ Hi). destruct Hblh as [Hlow | Hhigh]; [| lia].
          destruct Hbok as [Hb0' | [Hbn | (Hbs & _)]]; [exact (Hbnz Hb0') | | lia].
          apply in_map_iff in Hbn. destruct Hbn as ([z [kz vz]] & Hz & Hin). cbn in Hz. subst z.
          exact (live_offimg' A M model b 24 a AI (proj1 (u_node U2 b kz vz Hin)) ltac:(lia) Hi).
    Qed.

  End Main.
End EmpU1.
