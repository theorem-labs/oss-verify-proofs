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
  HRep HLib HRepFacts HStmts HConstsS1 HCommon HFpu HFind HBlk.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.
Set Implicit Arguments.

Definition NT_ENTRY  : Z := 0x67ed4.
Definition NT_NF     : Z := 0x67fdc.
Definition NT_NEWE   : Z := 0xe5ddc.
Definition NT_NEWR   : Z := 0x67fe4.
Definition NT_FLW    : Z := 0x67ffc.
Definition NT_FCVT1  : Z := 0x6800c.
Definition NT_FCVT2  : Z := 0x68014.
Definition NT_GROW   : Z := 0x68024.
Definition NT_FDIV   : Z := 0x68044.
Definition NT_FCVTLU : Z := 0x6804c.
Definition NT_NP     : Z := 0x8a4a4.
Definition NT_NPR    : Z := 0x6807c.
Definition NT_CMP    : Z := 0x68084.
Definition NT_NEW2R  : Z := 0x6809c.
Definition NT_DELSZ  : Z := 0x6db74.
Definition NT_DELETE : Z := 0x6db70.
Definition NT_DELR   : Z := 0x680b8.
Definition NT_BCST   : Z := 0x68160.
Definition NT_MEMSET : Z := 0xe13c4.
Definition NT_MSR    : Z := 0x68174.
Definition NT_LOOP   : Z := 0x6824c.
Definition NT_AFTER  : Z := 0x682b0.
Definition NT_INS    : Z := 0x682e0.
Definition NT_EMPTY  : Z := 0x68304.
Definition NT_SIZE   : Z := 0x68348.
Definition NT_VAL    : Z := 0x68354.
Definition NT_EXIT   : Z := 0x68360.

#[local] Abbreviation ent := (Z * (Z * (Z * Z * Z)))%type.

Section Ctx.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Variables NEW_STACK DEL_STACK : Z.
  #[local] Abbreviation NTS := (NT_STACK NEW_STACK DEL_STACK).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp parser key bl bc : Z) (val : Z * Z * Z) (v2 : Z) (ents : list ent) (K : TSet).
  Record ntctx : Prop := NTCTX {

    c_NEW_STACK_nn : 0 <= NEW_STACK;
    c_DEL_STACK_nn : 0 <= DEL_STACK;
    c_NEW : new_rule_stmt SEGS L MI ST NEW_STACK;
    c_DEL : delete_rule_stmt SEGS L MI DEL_STACK;
    c_NP : next_prime_stmt SEGS L hc;
    c_MEMSETH : memset_stmt SEGS hc;

    c_HLnew : ly_new L = NT_NEWE;
    c_HLdel : ly_delete L = NT_DELETE;
    c_HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling;
    c_HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a;
    c_HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a;
    c_HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a;
    c_HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a;

    c_AI0 : ainv MI A0 M0 model0;
    c_MS0 : mstd model0;
    c_SX0 : sx_inv ST s M0;
    c_SXH : sx_handler_set ST s;
    c_Hsp16 : sp mod 16 = 0;
    c_Hceil : alloc_ceiling + NTS <= sp;
    c_Hroom : stack_room SEGS M0 sp NTS;
    c_Hwin : forall a, zwin (sp - NTS) sp a -> ~ owned MI A0 a /\ ~ sx_region ST a;
    c_Hown_sx : forall a, owned MI A0 a -> ~ sx_region ST a;
    c_Herr_sx : forall a, errno_win L a -> ~ sx_region ST a;
    c_FRM : frm_zero (@fp_csr fx);
    c_NF : nt_frame SEGS L R0 M0 sp parser key val v2;
    c_ASP8 : above_sp MI A0 sp (sp + 8) 8;
    c_ASP24 : above_sp MI A0 sp (sp + 24) 48;
    c_ASP244 : above_sp MI A0 sp (sp + 244) 4;
    c_SO8 : store_ok SEGS M0 (Z_to_bv 64 (sp + 8)) 8 = true;
    c_U0 : umapx MI 32 (nval32 SEGS) A0 M0 (parser + 136) bl bc ents;
    c_ASPT : above_sp MI A0 sp (parser + 136) 40;
    c_HPAR : sp + 248 <= parser + 136;
    c_Hv1 : 0 <= t3a val < 2 ^ 32;
    c_Hv2 : 0 <= t3b val < 2 ^ 32;
    c_Hv3 : 0 <= t3c val < 2 ^ 32;
    c_Hv2r : 0 <= v2 < 2 ^ 64;
    c_Hv2m : v2 mod 2 ^ 32 = t3b val;
    c_ROC : ro_clear L M0;
    c_HSZ : Zlength ents + 1 < 2 ^ 24;
    c_HNMAX : LIB_NMAX <= NMAX MI;
    c_Hlast : bc <> BSEQ_LAST;
    c_ROOM1 : roomL MI A0 (live MI A0) 32;
    c_ROOM2 : (bc = 0 \/ Zlength ents = bc) -> roomL MI A0 ((0, 32) :: live MI A0) (8 * bseq_next bc);

    c_CONT : forall (fx' : FPState) A' R' M' model' (p bl' bc' : Z) (ents' : list ent) (inserted rehashed : bool),
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model0 -> m_fds model' = m_fds model0 ->
        sx_inv ST s M' -> frm_zero (@fp_csr fx') ->
        nt_kept R0 R' -> getr R' 25%bv = Z_to_bv 64 p ->
        umapx MI 32 (nval32 SEGS) A' M' (parser + 136) bl' bc' ents' ->
        In (p, (key, val)) ents' ->
        (inserted = false -> exists v0 l1 l2, ents = l1 ++ (p, (key, v0)) :: l2 /\ ents' = l1 ++ (p, (key, val)) :: l2
                             /\ rehashed = false) ->
        (inserted = true -> Permutation ents' ((p, (key, val)) :: ents)) ->
        (rehashed = false -> bl' = bl /\ bc' = bc) ->
        (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
        lapply (live MI A0)
               ((if inserted then [LAdd p 32] else [])
                ++ (if rehashed then LAdd bl' (8 * bc') :: (if bc =? 0 then [] else [LDel bl]) else []))
               (live MI A') ->
        eff MI A0 A' M0 M' (sp - NTS, sp)
            (fun a => umap_foot 32 (parser + 136) bl bc ents a \/ umap_foot 32 (parser + 136) bl' bc' ents' a
                      \/ (sp + 8 <= a < sp + 16)) ->
        defined M' (sp + 8) 8 ->
        srealizes SEGS (cfg fx' R' NT_EXIT M' model') K
  }.
End Ctx.

Ltac ntctx_pose C :=
  pose proof (c_NEW_STACK_nn C) as NEW_STACK_nn;
  pose proof (c_DEL_STACK_nn C) as DEL_STACK_nn;
  pose proof (c_NEW C) as NEW;
  pose proof (c_DEL C) as DEL;
  pose proof (c_NP C) as NP;
  pose proof (c_MEMSETH C) as MEMSETH;
  pose proof (c_HLnew C) as HLnew;
  pose proof (c_HLdel C) as HLdel;
  pose proof (c_HLimg_lo C) as HLimg_lo;
  pose proof (c_HLrw_img C) as HLrw_img;
  pose proof (c_HLrelro_img C) as HLrelro_img;
  pose proof (c_HLrw_relro C) as HLrw_relro;
  pose proof (c_HLerr_rw C) as HLerr_rw;
  pose proof (c_AI0 C) as AI0;
  pose proof (c_MS0 C) as MS0;
  pose proof (c_SX0 C) as SX0;
  pose proof (c_SXH C) as SXH;
  pose proof (c_Hsp16 C) as Hsp16;
  pose proof (c_Hceil C) as Hceil;
  pose proof (c_Hroom C) as Hroom;
  pose proof (c_Hwin C) as Hwin;
  pose proof (c_Hown_sx C) as Hown_sx;
  pose proof (c_Herr_sx C) as Herr_sx;
  pose proof (c_FRM C) as FRM;
  pose proof (c_NF C) as NF;
  pose proof (c_ASP8 C) as ASP8;
  pose proof (c_ASP24 C) as ASP24;
  pose proof (c_ASP244 C) as ASP244;
  pose proof (c_SO8 C) as SO8;
  pose proof (c_U0 C) as U0;
  pose proof (c_ASPT C) as ASPT;
  pose proof (c_HPAR C) as HPAR;
  pose proof (c_Hv1 C) as Hv1;
  pose proof (c_Hv2 C) as Hv2;
  pose proof (c_Hv2r C) as Hv2r;
  pose proof (c_Hv2m C) as Hv2m;
  pose proof (c_Hv3 C) as Hv3;
  pose proof (c_ROC C) as ROC;
  pose proof (c_HSZ C) as HSZ;
  pose proof (c_HNMAX C) as HNMAX;
  pose proof (c_Hlast C) as Hlast;
  pose proof (c_ROOM1 C) as ROOM1;
  pose proof (c_ROOM2 C) as ROOM2;
  pose proof (c_CONT C) as CONT.

Section Shared.
Context {AC : AllocCeiling}.
  Variables (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp parser key bl bc : Z) (val : Z * Z * Z) (v2 : Z) (ents : list ent) (K : TSet).
  Variable C : @ntctx AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K.

  #[local] Abbreviation NTS := (NT_STACK NEW_STACK DEL_STACK).
  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI (c_HLimg_lo C) (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST (c_HLimg_lo C) (c_HLrw_img C) (c_HLrelro_img C) (c_HLrw_relro C) (c_HLerr_rw C)).
  #[local] Abbreviation hi_unowned' := (hi_unowned L MI (c_HLimg_lo C) (c_HLrw_img C)).
  #[local] Abbreviation obj := (parser + 136).
  #[local] Abbreviation sent := (parser + 152).
  #[local] Ltac ctx := ntctx_pose C.

  Definition Wnt : Z * Z := (sp - NTS, sp).
  #[local] Abbreviation W := Wnt.

  Definition nt_base_ok (R : bvmap 5 word) : Prop :=
    getr R 2%bv = Z_to_bv 64 sp /\ getr R 3%bv = Z_to_bv 64 (ly_gp L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp L)
    /\ getr R 8%bv = Z_to_bv 64 parser /\ getr R 24%bv = Z_to_bv 64 1
    /\ getr R 21%bv = Z_to_bv 64 (t3a val) /\ getr R 18%bv = Z_to_bv 64 v2
    /\ forall r, In r [9; 19; 20]%bv -> getr R r = getr R0 r.

  Definition nt_pframe (M : mem) : Prop :=
    cell4 SEGS M (sp + 244) key /\ cell8 SEGS M (sp + 24) sent
    /\ cell8 SEGS M (sp + 40) 0x01010101 /\ cell8 SEGS M (sp + 48) 0x0f0f0f0f /\ cell8 SEGS M (sp + 56) 0x33333333 /\ cell8 SEGS M (sp + 64) 0x55555555.
  #[local] Abbreviation base_ok := nt_base_ok.
  #[local] Abbreviation pframe := nt_pframe.

  Lemma sp_facts : sp mod 16 = 0 /\ alloc_ceiling + NTS <= sp /\ sp + 248 <= 2 ^ 47 /\ 16 <= NTS /\ NEW_STACK <= NTS /\ DEL_STACK <= NTS /\ sp + 248 <= obj /\ 0 <= parser.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. destruct ASP244 as (Hs1 & Hs2 & _). destruct ASPT as (Ht1 & Ht2 & _). pose proof ac_bounds_lit. unfold NT_STACK in *.
    repeat split; try assumption; try lia.
  Qed.
  #[local] Abbreviation SPF := sp_facts.

  Lemma bc_facts : In bc BSEQ /\ 0 <= bc < 2 ^ 24 /\ Zlength ents <= bc /\ 0 <= Zlength ents.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. pose proof (u_bseq U0) as HB. pose proof (u_load U0) as HL. pose proof (BSEQ_bound bc HB).
    split; [exact HB|]. split; [| split; [exact HL | unfold Zlength; lia]].
    unfold BSEQ in HB. unfold BSEQ_LAST in Hlast. cbn in HB.
    repeat (destruct HB as [<-|HB]; [lia|]). destruct HB.
  Qed.

  Lemma base0 : base_ok R0.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. destruct NF. unfold nt_base_ok. repeat split; try assumption; try (intros r Hr; reflexivity).
  Qed.

  Lemma pframe0 : pframe M0.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C. ctx. destruct NF. unfold nt_pframe. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); assumption. Qed.

  Lemma foot_low_or_high_gen : forall A M model bl2 bc2 (ents2 : list ent) a,
    ainv MI A M model -> umapx MI 32 (nval32 SEGS) A M obj bl2 bc2 ents2 ->
    umap_foot 32 obj bl2 bc2 ents2 a -> 0 <= a /\ (a + 1 <= alloc_ceiling \/ sp <= a < 2 ^ 47).
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros A M model bl2 bc2 ents2 a AI U. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1. destruct SPF as (_ & _ & _ & _ & _ & _ & Hs1 & _).
    intros [Hh | [[Hbc Hb] | (p & Hp & Ha)]].
    - lia.
    - destruct (u_blive U) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' A M model bl2 (8 * bc2) AI Hin) as (_ & Hb0 & Hc & _). lia.
    - apply in_map_iff in Hp. destruct Hp as ([q [k v]] & Hq & Hin). cbn in Hq. subst q.
      destruct (live_facts' A M model p 32 AI (proj1 (u_node U p k v Hin))) as (_ & Hp0 & Hc & _). lia.
  Qed.

  Lemma foot_offimg_gen : forall A M model bl2 bc2 (ents2 : list ent) a,
    ainv MI A M model -> umapx MI 32 (nval32 SEGS) A M obj bl2 bc2 ents2 ->
    umap_foot 32 obj bl2 bc2 ents2 a -> ~ in_ranges (ly_img L) a.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros A M model bl2 bc2 ents2 a AI U Ha Hi. pose proof (HLimg_lo _ Hi) as Hlt. destruct SPF as (_ & Hsplo & _ & _ & _ & _ & Hs1 & _).
    destruct Ha as [Hh | [[Hbc Hb] | (p & Hp & Hpa)]].
    - pose proof ac_bounds_lit. unfold NT_STACK in Hsplo. lia.
    - destruct (u_blive U) as [[? ?]|[_ Hin]]; [lia|]. exact (live_offimg' A M model bl2 (8 * bc2) a AI Hin Hb Hi).
    - apply in_map_iff in Hp. destruct Hp as ([q [k v]] & Hq & Hin). cbn in Hq. subst q.
      exact (live_offimg' A M model p 32 a AI (proj1 (u_node U p k v Hin)) Hpa Hi).
  Qed.

  Lemma foot_apart_new : forall A M model p n a, ainv MI A M model -> live_add p n (live MI A0) (live MI A) ->
    umap_foot 32 obj bl bc ents a -> ~ (p <= a < p + n).
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros A M model p n a AI LADD Ha Hpa.
    assert (HinP : In (p, n) (live MI A)) by (rewrite (proj1 LADD); left; reflexivity).
    destruct (live_facts' A M model p n AI HinP) as (_ & _ & Hpc & _).
    destruct (umap_foot_hb 32 obj bl bc ents a Ha) as [Hh | ([q m] & Hb & Hba)]; [destruct SPF as (_ & Hsplo & _ & Hn16 & _ & _ & Hs1 & _); lia|]. cbn in Hba.
    assert (Hq0 : In (q, m) (live MI A0)).
    { unfold umap_blocks in Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
      - destruct (Z.eqb_spec bc 0); [destruct Hb|]. destruct Hb as [Hb|[]]. injection Hb as <- <-.
        destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia | exact Hin].
      - apply in_map_iff in Hb. destruct Hb as ([q' [k v]] & Hq & Hin). cbn in Hq. injection Hq as <- <-. exact (proj1 (u_node U0 q' k v Hin)). }
    assert (Hq1 : In (q, m) (live MI A)) by (rewrite (proj1 LADD); right; exact Hq0).
    assert (Hne : p <> q) by (intros <-; apply (proj2 LADD); apply (in_map fst _ (p, m)); exact Hq0).
    pose proof (ai_live_disjoint MI A M model p n q m AI HinP Hq1 Hne) as Hap. lia.
  Qed.

  Lemma blocks_apart_p : forall p A M model, ainv MI A M model -> live_add p 32 (live MI A0) (live MI A) ->
    forall q m, In (q, m) (umap_blocks 32 bl bc ents) -> apart p 32 q m.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros p A M model AI LADD q m Hq.
    assert (HinP : In (p, 32) (live MI A)) by (rewrite (proj1 LADD); left; reflexivity).
    assert (Hq0 : In (q, m) (live MI A0)).
    { unfold umap_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq | Hq].
      - destruct (Z.eqb_spec bc 0); [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as <- <-.
        destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia | exact Hin].
      - apply in_map_iff in Hq. destruct Hq as ([q' [k v]] & Hq' & Hin). cbn in Hq'. injection Hq' as <- <-. exact (proj1 (u_node U0 q' k v Hin)). }
    assert (Hq1 : In (q, m) (live MI A)) by (rewrite (proj1 LADD); right; exact Hq0).
    assert (Hne : p <> q) by (intros <-; apply (proj2 LADD); apply (in_map fst _ (p, m)); exact Hq0).
    exact (ai_live_disjoint MI A M model p 32 q m AI HinP Hq1 Hne).
  Qed.

  Lemma kept_of_base : forall R, base_ok R -> getr R 27%bv = Z_to_bv 64 (t3c val) -> nt_kept R0 R.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros R (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs) B27 r Hr. destruct NF.
    cbn in Hr. repeat (destruct Hr as [<- | Hr]; [first [rewrite B2 | rewrite B3 | rewrite B4 | rewrite B8 | rewrite B18 | rewrite B21 | rewrite B24 | rewrite B27 | apply Bs; (first [solve [clear; cbn; tauto] | cbn; tauto])]; symmetry; assumption |]).
    destruct Hr.
  Qed.

  Lemma so8_defined : defined M0 (sp + 8) 8.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. destruct SPF as (_ & Hsplo & Hsphi & Hn16 & _). pose proof ac_bounds_lit.
    intros i Hi.
    pose proof (store_ok_all SEGS M0 8%nat (Z_to_bv 64 (sp + 8)) ltac:(rewrite u64_of_Z by lia; change (Z.of_nat 8) with 8; lia) SO8
                  (Z_to_bv 64 (sp + 8 + i)) ltac:(rewrite !u64_of_Z by lia; change (Z.of_nat 8) with 8; lia)) as Hw.
    rewrite wview_high in Hw by (rewrite u64_of_Z by lia; lia). exact Hw.
  Qed.

  Lemma iroc0 : img_ro_clear L M0.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C. ctx. apply img_ro_clear_of; [exact ROC |]. intros a Ha. eapply (sx_relro ST); [exact SX0 | exact Ha]. Qed.

  Lemma win_defined : defined M0 (sp - NTS) NTS.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. destruct SPF as (_ & Hsplo & Hsphi & Hn16 & _). pose proof ac_bounds_lit.
    apply defined_of_stack_room; [lia | lia | lia | exact Hroom].
  Qed.

End Shared.

Arguments sp_facts {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C.
Arguments bc_facts {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C.
Arguments base0 {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C.
Arguments pframe0 {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C.
Arguments so8_defined {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C.
Arguments iroc0 {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C.
Arguments win_defined {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C.
Arguments foot_low_or_high_gen {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C A M model bl2 bc2 ents2 a _ _ _.
Arguments foot_offimg_gen {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C A M model bl2 bc2 ents2 a _ _ _ _.
Arguments foot_apart_new {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C A M model p n a _ _ _ _.
Arguments blocks_apart_p {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C p A M model _ _ q m _.
Arguments kept_of_base {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C R _ _ r _.

Ltac nt_base_from HR' Bprev :=
  let Bc := fresh in let B2 := fresh in let B3 := fresh in let B4 := fresh in let B8 := fresh in
  let B24 := fresh in let B21 := fresh in let B18 := fresh in let Bs := fresh in
  pose proof Bprev as Bc; destruct Bc as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs);
  unfold nt_base_ok;
  let one r B := (let Q := fresh in rreg HR' r Q; rewrite Q; first [reflexivity | exact B | rewrite B; reflexivity]) in
  split; [one (2%bv : reg) B2|]; split; [one (3%bv : reg) B3|]; split; [one (4%bv : reg) B4|]; split; [one (8%bv : reg) B8|];
  split; [one (24%bv : reg) B24|]; split; [one (21%bv : reg) B21|]; split; [one (18%bv : reg) B18|];
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite (syms_id_sound _ _ _ _ [9; 19; 20]%bv HR' eq_refl r Hr); apply Bs; exact Hr.

