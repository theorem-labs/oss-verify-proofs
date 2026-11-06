(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib RefReadLib SumWalkTac LibIface LibEff LibBudget FPSteps SymExec3 SymExec3Sound SymRun3 S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import DrvLibContract.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HCommon HBlk.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PrsStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Definition LLVM_ENTRY : Z := 0x65a88.
Definition EMPTY_OBJ : Z := 0xfe500.
Definition TD_LOCALE : Z := 0x100688.
Definition GLOBAL_LOCALE : Z := 0x120980.

Definition DEL1 : Z := 0x6db74.

Definition TOP_FRAME : Z := 2576.

Definition T_RGC_RET  : Z := 0x65abc.
Definition T_GTE_RET  : Z := 0x65ac4.
Definition T_CTX_RET  : Z := 0x65ac8.
Definition T_RES_RET  : Z := 0x65ae8.
Definition T_LOOP     : Z := 0x65b0c.
Definition T_AFTER    : Z := 0x65b44.
Definition T_PARSE_RET : Z := 0x65b68.
Definition T_DTOR_RET : Z := 0x65b70.
Definition T_EXIT     : Z := 0x65b88.

Lemma kwr_mdef : forall E M (n : N) (b off k : Z),
  ev E n = Z_to_bv 64 b -> mdef M (b + off) k -> 0 <= b < 2 ^ 64 -> 0 <= b + off -> b + off + k < 2 ^ 64 -> 0 <= k ->
  kentry_ok SEGS E M (KWr (SA (EVar n) off) (ELit k)).
Proof.
  intros E M n b off k Hn HD Hb Hbo Hbk Hk. cbn [kentry_ok].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite Hn, !u64_of_Z by lia.
  split; [lia|]. intros d m Hd Hdm.
  replace (b + off + d) with ((b + off) + d) by lia. apply (mdef_store_ok_off SEGS M (b + off) k d m HD); lia.
Qed.

Lemma know_more : forall E M l1 l2, know_ok SEGS E M l2 -> Forall (kentry_ok SEGS E M) l1 -> know_ok SEGS E M (l1 ++ l2).
Proof. intros E M l1 l2 H2 H1. unfold know_ok. apply Forall_app. split; assumption. Qed.

Lemma count_class_le_length : forall cls big lv c, 0 <= count_class_f cls big lv c <= Z.of_nat (length lv).
Proof.
  intros cls big lv c. induction lv as [|[q k] lv IH]; cbn [count_class_f length]; [lia|].
  destruct ((k <? big) && (cls k =? c)); lia.
Qed.
Lemma big_bytes_le : forall rb big lv (B : Z),
  (forall q k, In (q, k) lv -> 0 <= (if big <=? k then rb k else 0) <= B) -> 0 <= B ->
  0 <= big_bytes_f rb big lv <= Z.of_nat (length lv) * B.
Proof.
  intros rb big lv B H HB. induction lv as [|[q k] lv IH]; cbn [big_bytes_f length]; [lia|].
  pose proof (H q k (or_introl eq_refl)) as Hk.
  assert (IH' : 0 <= big_bytes_f rb big lv <= Z.of_nat (length lv) * B) by (apply IH; intros q' k' Hin; apply (H q' k'); right; exact Hin).
  rewrite Nat2Z.inj_succ. lia.
Qed.

Ltac w2blen := rewrite ?length_N_to_le_bytes.
Lemma rdn_wbytes_prefix : forall m (a : word) bs k,
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (k <= length bs)%nat ->
  rdn SEGS (wbytes m a bs) a k = Some (firstn k bs).
Proof. intros m a bs k H Hk. eapply rdn_firstn; [apply rdn_wbytes_self; exact H | exact Hk]. Qed.
Ltac rdback := unfold CRep.fld; repeat (rewrite rdn_wbytes_out_Z by (w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia));
               first [ apply rdn_wbytes_self; w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                     | rewrite rdn_wbytes_prefix; [ reflexivity | w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | w2blen; lia ]
                     | idtac ].

Section Ctx.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Variables (cR : rg_consts) (cC : ctx_consts) (cV : vec_consts) (kc : prs_consts).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp ret p n : Z) (payload : list byte) (K : TSet).

  Record topC : Prop := TOPC {

    c_HcR : rc_ctor cR = 0x6c080 /\ rc_gettargetenv cR = 0x6c1a0 /\ 0 <= rc_ctor_stack cR <= 1024 /\ 0 <= rc_gte_stack cR <= 1024;
    c_HcC : cc_create cC = 0x65eac /\ cc_destroy cC = 0x65f04 /\ 0 <= cc_stack cC <= 1024;
    c_HcV : vc_entry cV = 0x65bd0 /\ 0 <= vc_stack cV <= 1024;
    c_Hkc : kc_parse kc = 0x660f8 /\ 0 <= kc_po_stack kc <= 32768;
    c_MSTK : 0 <= MALLOC_STACK MI <= 16384;
    c_HNMAX : LIB_NMAX <= NMAX MI;
    c_HBIG : BIG MI = 131052;
    c_RB : round_big_law MI;
    c_HEAPOWN : forall A M model a, ainv MI A M model -> 0 < a < alloc_ceiling -> ~ in_ranges (ly_img Ly.L) a ->
                  (forall q k, In (q, k) (live MI A) -> ~ (q <= a < q + k)) -> owned MI A a;

    c_RGC  : rg_ctor_stmt SEGS Ly.L cR;
    c_RGE  : rg_gettargetenv_stmt SEGS Ly.L cR;
    c_CTXC : ctx_create_stmt SEGS Ly.L MI ST cC;
    c_CTXD : ctx_destroy_stmt SEGS Ly.L MI ST cC;
    c_VRES : vec32_resize_stmt SEGS Ly.L MI ST cV;
    c_DEL  : op_delete_stmt SEGS Ly.L MI DEL1 (MALLOC_STACK MI);
    c_PARSE : binary_parse_stmt SEGS Ly.L MI ST kc;
    c_BUDGET : forall (A : AS MI) (lv : list (Z * Z)) (b nw : Z),
        caps MI A = lib_caps -> bigcap MI A = LIB_BIGCAP ->
        (length lv <= 3)%nat -> (forall q k, In (q, k) lv -> 0 < k <= 2 ^ 26) ->
        Permutation (live MI A) ((if nw =? 0 then [] else [(b, 4 * nw)]) ++ lv) ->
        0 <= nw < 2 ^ 24 ->
        pm_budget SEGS Ly.L MI A nw;

    c_AI0 : ainv MI A0 M0 model0;
    c_MS0 : mstd model0;
    c_SX0 : sx_inv ST s M0;
    c_SXH : sx_handler_set ST s;
    c_ROC : ro_clear Ly.L M0;
    c_Hosx : forall a, owned MI A0 a -> ~ sx_region ST a;
    c_Hesx : forall a, errno_win Ly.L a -> ~ sx_region ST a;
    c_CAPS : caps MI A0 = lib_caps;
    c_BIGC : bigcap MI A0 = LIB_BIGCAP;
    c_LLEN : (length (live MI A0) <= 2)%nat;
    c_LSZ : forall q k, In (q, k) (live MI A0) -> 0 < k <= 2 ^ 26;
    c_CR : call_regs Ly.L R0 sp ret;
    c_Qa0 : getr R0 10%bv = Z_to_bv 64 p;
    c_Qa1 : getr R0 11%bv = Z_to_bv 64 n;
    c_FRM : frm_zero (@fp_csr fx);
    c_Hn : 0 <= n < 2 ^ 26;
    c_Hpay : Z.of_nat (length payload) = n;
    c_Hp16 : p mod 16 = 0;
    c_Hp : (n = 0 /\ p = EMPTY_OBJ) \/ (0 < n /\ In (p, n) (live MI A0));
    c_RDP : rdn SEGS M0 (Z_to_bv 64 p) (Z.to_nat n) = Some payload;
    c_Hceil : alloc_ceiling + LIB_STACK <= sp;
    c_Hroom : stack_room SEGS M0 sp LIB_STACK;
    c_Hwin : forall a, zwin (sp - LIB_STACK) sp a -> ~ owned MI A0 a /\ ~ sx_region ST a;

    c_CONT : forall (fx' : FPState) A' s' R' M' model',
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model0 -> m_fds model' = m_fds model0 ->
        sx_inv ST s' M' -> sx_le ST s s' ->
        kept R0 R' -> getr R' 10%bv = Z_to_bv 64 0 ->
        frm_zero (@fp_csr fx') ->
        (forall q k, In (q, k) (live MI A') <-> In (q, k) (live MI A0)) ->
        eff MI A0 A' M0 M' (sp - LIB_STACK, sp) (sx_region ST) ->
        srealizes SEGS (cfg fx' R' ret M' model') K
  }.
End Ctx.

Ltac topctx_pose C :=
  pose proof (c_HcR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as HcR;
  pose proof (c_HcC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as HcC;
  pose proof (c_HcV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as HcV;
  pose proof (c_Hkc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hkc;
  pose proof (c_MSTK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as MSTK;
  pose proof (c_HNMAX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as HNMAX;
  pose proof (c_HBIG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as HBIG;
  pose proof (c_RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as RB;
  pose proof (c_HEAPOWN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as HEAPOWN;
  pose proof (c_RGC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as RGC;
  pose proof (c_RGE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as RGE;
  pose proof (c_CTXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as CTXC;
  pose proof (c_CTXD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as CTXD;
  pose proof (c_VRES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as VRES;
  pose proof (c_DEL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as DEL;
  pose proof (c_PARSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as PARSE;
  pose proof (c_BUDGET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as BUDGET;
  pose proof (c_AI0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as AI0;
  pose proof (c_MS0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as MS0;
  pose proof (c_SX0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as SX0;
  pose proof (c_SXH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as SXH;
  pose proof (c_ROC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as ROC;
  pose proof (c_Hosx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hosx;
  pose proof (c_Hesx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hesx;
  pose proof (c_CAPS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as CAPS;
  pose proof (c_BIGC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as BIGC;
  pose proof (c_LLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as LLEN;
  pose proof (c_LSZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as LSZ;
  pose proof (c_CR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as CR;
  pose proof (c_Qa0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Qa0;
  pose proof (c_Qa1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Qa1;
  pose proof (c_FRM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as FRM;
  pose proof (c_Hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hn;
  pose proof (c_Hpay _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hpay;
  pose proof (c_Hp16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hp16;
  pose proof (c_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hp;
  pose proof (c_RDP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as RDP;
  pose proof (c_Hceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hceil;
  pose proof (c_Hroom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hroom;
  pose proof (c_Hwin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as Hwin;
  pose proof (c_CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as CONT.

Section Shared.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Variables (cR : rg_consts) (cC : ctx_consts) (cV : vec_consts) (kc : prs_consts).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp ret p n : Z) (payload : list byte) (K : TSet).
  Variable C : topC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K.
  #[local] Ltac ctx := topctx_pose C.
  #[local] Abbreviation sp' := (sp - TOP_FRAME).
  #[local] Abbreviation live_facts' := (live_facts Ly.L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff Ly.L MI ly_img_low ly_rw_img ly_errno_rw).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff Ly.L MI ly_rw_img ly_errno_rw).
  #[local] Abbreviation defined_via_eff' := (defined_via_eff Ly.L MI ly_img_low ly_rw_img ly_errno_rw).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff Ly.L MI ly_img_low ly_errno_rw).
  #[local] Abbreviation ro_clear_via_eff' := (ro_clear_via_eff Ly.L MI ly_img_low ly_errno_rw).
  #[local] Abbreviation own_sx_via_eff' := (own_sx_via_eff Ly.L MI ST ly_rw_img).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_rw_not_relro ly_errno_rw).
  #[local] Abbreviation W := (sp - LIB_STACK, sp).

  Lemma sp_facts : sp mod 16 = 0 /\ alloc_ceiling + LIB_STACK <= sp /\ sp < 2 ^ 47 /\ sp' mod 16 = 0.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. destruct CR. unfold TOP_FRAME, LIB_STACK in *. pose proof ac_bounds_lit.
    repeat split; try assumption. replace (sp - 2576) with (sp + (-161) * 16) by lia. rewrite Z.mod_add by lia. assumption.
  Qed.

  Lemma win_defined : defined M0 (sp - LIB_STACK) LIB_STACK.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. pose proof sp_facts as (_ & Hc & Hhi & _). pose proof ac_bounds_lit.
    apply defined_of_stack_room; unfold LIB_STACK in *; [lia | lia | lia | exact Hroom].
  Qed.

  Lemma win_unowned : forall A M model a, ainv MI A M model -> sp - LIB_STACK <= a -> ~ owned MI A a.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model a AI Ha. pose proof sp_facts as (_ & Hc & _ & _).
    eapply (hi_unowned Ly.L MI ly_img_low ly_rw_img); [exact AI | lia].
  Qed.

  Lemma iroc0 : img_ro_clear Ly.L M0.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C. ctx. apply img_ro_clear_of; [exact ROC |]. intros a Ha. eapply (sx_relro ST); [exact SX0 | exact Ha]. Qed.

  Definition J (a : Z) : Prop :=
    0 < a < alloc_ceiling /\ ~ in_ranges (ly_img Ly.L) a /\ forall q k, In (q, k) (live MI A0) -> ~ (q <= a < q + k).
  Definition FJW (a : Z) : Prop := J a \/ W_of W a.

  Lemma eff_close : forall A' M' model', ainv MI A' M' model' ->
    eff MI A0 A' M0 M' W FJW -> defined M' (sp - LIB_STACK) LIB_STACK ->
    eff MI A0 A' M0 M' W (sx_region ST).
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A' M' model' AI' EF DEFW. pose proof sp_facts as (_ & Hc & Hhi & _). pose proof ac_bounds_lit as Hcv.
    assert (HJ : forall a, J a -> owned MI A0 a).
    { intros a (Ha & Hni & Hnl). exact (HEAPOWN A0 M0 model0 a AI0 Ha Hni Hnl). }
    destruct EF as [CA CB O FR D OI]. constructor.
    - exact CA. - exact CB.
    - intros a Ho. destruct (O a Ho) as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | left; exact (HJ a H) |].
      exfalso. exact (win_unowned A' M' model' a AI' ltac:(unfold W_of in H; cbn in H; lia) Ho).
    - intros a Hnn. apply FR. intros [H|[H|[H|[[H|H]|[H|H]]]]]; apply Hnn.
      + left; exact H. + right; left; exact H. + right; right; left; exact H.
      + left. exact (HJ _ H). + right; right; right; right; left; exact H.
      + right; right; right; right; left; exact H. + right; right; right; right; right; exact H.
    - intros a Ha Hd. destruct (D a Ha Hd) as [H|[H|[[H|H]|H]]]; [left; exact H | right; left; exact H | right; left; exact (HJ _ H) | | right; right; right; exact H].
      left. unfold W_of in H. cbn in H. pose proof (DEFW (a - (sp - LIB_STACK)) ltac:(lia)) as Hd'.
      replace (sp - LIB_STACK + (a - (sp - LIB_STACK))) with a in Hd' by lia. exact Hd'.
    - exact OI.
  Qed.

  Definition tframe (M : mem) : Prop :=
    cell8 SEGS M (sp' + 2568) ret /\ cell8 SEGS M (sp' + 2560) (bv_unsigned (getr R0 8%bv))
    /\ cell8 SEGS M (sp' + 2552) (bv_unsigned (getr R0 9%bv)) /\ cell8 SEGS M (sp' + 2544) (bv_unsigned (getr R0 18%bv)).

  Record tinv (A : AS MI) (M : mem) (model : Model) : Prop := TINV {
    ti_ainv : ainv MI A M model;
    ti_mstd : mstd model;
    ti_fs : m_fs model = m_fs model0;
    ti_fds : m_fds model = m_fds model0;
    ti_sx : sx_inv ST s M;
    ti_roc : ro_clear Ly.L M;
    ti_osx : forall a, owned MI A a -> ~ sx_region ST a;
    ti_eff : eff MI A0 A M0 M W FJW;
    ti_defw : defined M (sp - LIB_STACK) LIB_STACK;
    ti_frame : tframe M
  }.

  Definition tregs (R : bvmap 5 word) : Prop :=
    getr R 2%bv = Z_to_bv 64 sp' /\ getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L)
    /\ forall r, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R r = getr R0 r.

  Lemma tregs_kept : forall R R', tregs R -> kept R R' -> tregs R'.
  Proof using R0 sp.
    intros R R' (Q2 & Q3 & Q4 & Qs) KP. unfold tregs.
    rewrite !(KP _) by (clear; inl). split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
    intros r Hr. rewrite (KP r) by (revert Hr; clear; intros Hr; cbn in Hr; unfold callee_saved; cbn; intuition (subst; tauto)). apply Qs, Hr.
  Qed.

  Lemma J_offimg : forall a, J a -> ~ in_ranges (ly_img Ly.L) a.
  Proof using AC MI A0. intros a (_ & H & _). exact H. Qed.

  Lemma tinv_call : forall A M model A' M' model' R R' (STK : Z) (F : Z -> Prop),
    tinv A M model -> retB MI ST A' s R R' M' model model' ->
    eff MI A A' M M' (sp' - STK, sp') F -> 0 <= STK <= LIB_STACK - TOP_FRAME ->
    (forall a, F a -> J a) ->
    tinv A' M' model'.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model A' M' model' R R' STK F TI RB' EF HSTK HF.
    pose proof sp_facts as (_ & Hc & Hhi & _). pose proof ac_bounds_lit as Hcv. assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    destruct TI as [AI MS Hfs Hfds SX RC OSX EF0 DEFW FR]. destruct RB' as [AI' MS' Hfs' Hfds' SX' KP].
    assert (HFi : forall a, F a -> ~ in_ranges (ly_img Ly.L) a) by (intros a Ha; exact (J_offimg a (HF a Ha))).
    assert (EFw : eff MI A A' M M' W (fun a => F a)).
    { eapply (eff_widen Ly.L MI); [exact EF|]. intros a Ha. unfold W_of in *. cbn [fst snd] in *. lia. }
    constructor.
    - exact AI'. - exact MS'. - rewrite Hfs'; exact Hfs. - rewrite Hfds'; exact Hfds. - exact SX'.
    - eapply (ro_clear_via_eff' A A' M M' model); [exact RC | exact AI | exact EF | exact HFi | cbn; lia].
    - eapply (own_sx_via_eff' A A' M M'); [exact EF | exact OSX | exact HFi].
    - eapply eff_weaken; [eapply (eff_trans MI); [exact EF0 | exact EFw | intros a Ha; eapply (win_unowned A' M' model'); [exact AI' | unfold W_of in Ha; cbn [fst snd] in Ha; lia]] |].
      intros a [Ha | Ha]; [exact Ha | left; exact (HF a Ha)].
    - eapply (defined_via_eff' A A' M M'); [exact EF | lia | lia | | | exact DEFW].
      + intros i Hi. eapply (win_unowned A M model); [exact AI | lia].
      + intros i Hi Hf. pose proof (HF _ Hf) as (Hlt & _). lia.
    - assert (AG : forall a k, sp' <= a -> 0 <= k -> a + k <= sp -> defined M a k -> agree_on M M' a k).
      { intros a k Ha Hk Hak Hd. eapply (agree_above_via_eff' A A' M M' _ F a k sp'); [exact EF | lia | cbn; lia | lia | lia | lia | | exact Hd |].
        + intros i Hi. eapply (win_unowned A M model); [exact AI | lia].
        + intros i Hi Hf. pose proof (HF _ Hf) as (Hlt & _). lia. }
      destruct FR as (F1 & F2 & F3 & F4). unfold tframe.
      assert (DW : forall a k, sp - LIB_STACK <= a -> a + k <= sp -> defined M a k) by (intros a k H1 H2 i Hi; pose proof (DEFW (a + i - (sp - LIB_STACK)) ltac:(lia)) as D; replace (sp - LIB_STACK + (a + i - (sp - LIB_STACK))) with (a + i) in D by lia; exact D).
      repeat split; try (eapply cellw_agree; [eassumption | apply AG; try lia; apply DW; lia | lia | cbn; lia]).
  Qed.

  Lemma tinv_store : forall A M model M' (Fw : Z -> Prop),
    tinv A M model -> frame_eq Fw M M' ->
    (forall a, Fw a -> W_of W a /\ ~ (sp' + 2544 <= a < sp)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    tinv A M' model.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model M' Fw TI FE HFw HG.
    pose proof sp_facts as (_ & Hc & Hhi & _). pose proof ac_bounds_lit as Hcv. assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    destruct TI as [AI MS Hfs Hfds SX RC OSX EF0 DEFW FR].
    assert (HWimg : forall a, W_of W a -> ~ in_ranges (ly_img Ly.L) a).
    { intros a Ha Hi. pose proof (ly_img_low _ Hi). unfold W_of in Ha. cbn in Ha. lia. }
    constructor.
    - eapply (ai_frame MI); [exact AI | | exact HG | reflexivity | reflexivity].
      intros x Ho. apply FE. intros Hf. destruct (HFw _ Hf) as [Hw _]. exfalso. refine (win_unowned A M model _ AI _ Ho). unfold W_of in Hw. cbn [fst snd] in Hw. lia.
    - exact MS. - exact Hfs. - exact Hfds.
    - apply (sx_frame ST s M M' SX). intros a Ha. apply FE. intros Hf. destruct (HFw _ Hf) as [Hw _]. apply (HWimg _ Hw).
      destruct Ha as [Hs | Hr]; [exact (ly_rw_img _ (sx_region_rw ST _ Hs)) | exact (ly_relro_img _ Hr)].
    - eapply (ro_clear_frame Ly.L Fw M M' RC FE). intros a (Hi & _) Hf. destruct (HFw _ Hf) as [Hw _]. exact (HWimg _ Hw Hi).
    - exact OSX.
    - eapply eff_weaken; [eapply (eff_trans MI); [exact EF0 | | intros a Ha; eapply (win_unowned A M' model); [| unfold W_of in Ha; cbn [fst snd] in Ha; lia]] |].
      + apply eff_store with (F := fun _ => False); [| exact HG]. intros a _ Hw. apply FE. intros Hf. exact (Hw (proj1 (HFw _ Hf))).
      + eapply (ai_frame MI); [exact AI | | exact HG | reflexivity | reflexivity].
        intros x Ho. apply FE. intros Hf. destruct (HFw _ Hf) as [Hw _]. exfalso. refine (win_unowned A M model _ AI _ Ho). unfold W_of in Hw. cbn [fst snd] in Hw. lia.
      + intros a [Ha | []]. exact Ha.
    - intros i Hi. apply HG. apply DEFW. exact Hi.
    - destruct FR as (F1 & F2 & F3 & F4). unfold tframe.
      assert (AG : forall a k, sp' + 2544 <= a -> a + k <= sp -> 0 <= k -> agree_on M M' a k).
      { intros a k H1 H2 Hk i Hi. apply FE. rewrite u64_of_Z by lia. intros Hf. destruct (HFw _ Hf) as [_ Hs]. apply Hs. lia. }
      repeat split; (eapply cellw_agree; [eassumption | apply AG; lia | lia | cbn; lia]).
  Qed.

  Lemma cell_call : forall A M model A' M' (STK : Z) (F : Z -> Prop) a (w : N) v,
    tinv A M model -> eff MI A A' M M' (sp' - STK, sp') F -> 0 <= STK -> (forall x, F x -> J x) ->
    sp' <= a -> a + Z.of_N w <= sp -> cellw SEGS M a w v -> cellw SEGS M' a w v.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model A' M' STK F a w v TI EF HSTK HF Ha Haw Cc.
    pose proof sp_facts as (_ & Hc & Hhi & _). pose proof ac_bounds_lit as Hcv. assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    destruct TI as [AI MS Hfs Hfds SX RC OSX EF0 DEFW FR].
    eapply cellw_agree; [exact Cc | | lia | lia].
    eapply (agree_above_via_eff' A A' M M' _ F a (Z.of_N w) sp'); [exact EF | lia | cbn; lia | lia | lia | lia | | |].
    - intros i Hi. eapply (win_unowned A M model); [exact AI | lia].
    - intros i Hi. pose proof (DEFW (a + i - (sp - LIB_STACK)) ltac:(lia)) as D. replace (sp - LIB_STACK + (a + i - (sp - LIB_STACK))) with (a + i) in D by lia. exact D.
    - intros i Hi Hf. pose proof (HF _ Hf) as (Hlt & _). lia.
  Qed.

  Lemma mk_callB : forall A M model R (retpc STK : Z),
    tinv A M model -> tregs R -> getr R 1%bv = Z_to_bv 64 retpc -> ret_ok (Z_to_bv 64 retpc) -> 0 <= retpc < 2 ^ 64 ->
    0 <= STK <= LIB_STACK - TOP_FRAME ->
    callB MI ST A s R M model sp' retpc STK.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model R retpc STK TI TR Hra Hrok Hrr HSTK.
    pose proof sp_facts as (Hsp16 & Hc & Hhi & Hsp16'). pose proof ac_bounds_lit as Hcv. assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    destruct TI as [AI MS Hfs Hfds SX RC OSX EF0 DEFW FR]. destruct TR as (Q2 & Q3 & Q4 & Qs).
    constructor.
    - exact AI. - exact MS.
    - apply img_ro_clear_of; [exact RC |]. intros a Ha. eapply (sx_relro ST); [exact SX | exact Ha].
    - exact SX. - exact SXH.
    - constructor; [exact Hra | exact Hrok | exact Hrr | exact Q2 | exact Hsp16' | lia | exact Q3 | exact Q4].
    - lia.
    - apply stack_room_of_defined; [lia | lia | lia |]. intros i Hi. pose proof (DEFW (sp' - STK + i - (sp - LIB_STACK)) ltac:(lia)) as D.
      replace (sp - LIB_STACK + (sp' - STK + i - (sp - LIB_STACK))) with (sp' - STK + i) in D by lia. exact D.
    - intros a Ha. unfold zwin in Ha. split; [eapply (win_unowned A M model); [exact AI | lia] | apply (proj2 (Hwin a ltac:(unfold zwin; lia)))].
    - exact OSX. - exact Hesx.
  Qed.

  Lemma tinv_storeJ : forall A M model M' (Fh : Z -> Prop),
    tinv A M model -> frame_eq Fh M M' ->
    (forall a, Fh a -> J a) -> (forall a, Fh a -> ~ owned MI A a) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    tinv A M' model.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model M' Fh TI FE HFJ HFo HG.
    pose proof sp_facts as (_ & Hc & Hhi & _). pose proof ac_bounds_lit as Hcv. assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    destruct TI as [AI MS Hfs Hfds SX RC OSX EF0 DEFW FR].
    assert (HFimg : forall a, Fh a -> ~ in_ranges (ly_img Ly.L) a) by (intros a Ha; exact (J_offimg a (HFJ a Ha))).
    constructor.
    - eapply (ai_frame MI); [exact AI | | exact HG | reflexivity | reflexivity]. intros x Ho. apply FE. intros Hf. exact (HFo _ Hf Ho).
    - exact MS. - exact Hfs. - exact Hfds.
    - apply (sx_frame ST s M M' SX). intros a Ha. apply FE. intros Hf. apply (HFimg _ Hf).
      destruct Ha as [Hs | Hr]; [exact (ly_rw_img _ (sx_region_rw ST _ Hs)) | exact (ly_relro_img _ Hr)].
    - eapply (ro_clear_frame Ly.L Fh M M' RC FE). intros a (Hi & _) Hf. exact (HFimg _ Hf Hi).
    - exact OSX.
    - eapply eff_weaken; [eapply (eff_trans MI); [exact EF0 | | intros a Ha; eapply (win_unowned A M' model); [| unfold W_of in Ha; cbn [fst snd] in Ha; lia]] |].
      + apply eff_store with (F := Fh); [| exact HG]. intros a Hf _. apply FE. exact Hf.
      + eapply (ai_frame MI); [exact AI | | exact HG | reflexivity | reflexivity]. intros x Ho. apply FE. intros Hf. exact (HFo _ Hf Ho).
      + intros a [Ha | Ha]; [exact Ha | left; exact (HFJ a Ha)].
    - intros i Hi. apply HG. apply DEFW. exact Hi.
    - destruct FR as (F1 & F2 & F3 & F4). unfold tframe.
      assert (AG : forall a k, sp' <= a -> a + k <= sp -> 0 <= k -> agree_on M M' a k).
      { intros a k H1 H2 Hk i Hi. apply FE. rewrite u64_of_Z by lia. intros Hf. pose proof (HFJ _ Hf) as (Hlt & _). lia. }
      repeat split; (eapply cellw_agree; [eassumption | apply AG; lia | lia | cbn; lia]).
  Qed.

  Lemma tinv_callW : forall A M model A' M' model' R R' (STK : Z) (F : Z -> Prop),
    tinv A M model -> retB MI ST A' s R R' M' model model' ->
    eff MI A A' M M' (sp' - STK, sp') F -> 0 <= STK <= LIB_STACK - TOP_FRAME ->
    (forall a, F a -> J a \/ (sp' <= a < sp' + 2544)) ->
    (forall a, F a -> sp' <= a < sp' + 2544 -> M' (Z_to_bv 64 a) <> None) ->
    tinv A' M' model'.
  Proof using AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K C.
    ctx. intros A M model A' M' model' R R' STK F TI RB' EF HSTK HF HFd.
    pose proof sp_facts as (_ & Hc & Hhi & _). pose proof ac_bounds_lit as Hcv. assert (HLS : LIB_STACK = 65536) by reflexivity. assert (HTF : TOP_FRAME = 2576) by reflexivity.
    destruct TI as [AI MS Hfs Hfds SX RC OSX EF0 DEFW FR]. destruct RB' as [AI' MS' Hfs' Hfds' SX' KP].
    assert (HFi : forall a, F a -> ~ in_ranges (ly_img Ly.L) a).
    { intros a Ha. destruct (HF a Ha) as [Hj | Hw]; [exact (J_offimg a Hj)|]. intros Hi. pose proof (ly_img_low _ Hi). lia. }
    assert (EFw : eff MI A A' M M' W (fun a => F a)).
    { eapply (eff_widen Ly.L MI); [exact EF|]. intros a Ha. unfold W_of in *. cbn [fst snd] in *. lia. }
    constructor.
    - exact AI'. - exact MS'. - rewrite Hfs'; exact Hfs. - rewrite Hfds'; exact Hfds. - exact SX'.
    - eapply (ro_clear_via_eff' A A' M M' model); [exact RC | exact AI | exact EF | exact HFi | cbn; lia].
    - eapply (own_sx_via_eff' A A' M M'); [exact EF | exact OSX | exact HFi].
    - eapply eff_weaken; [eapply (eff_trans MI); [exact EF0 | exact EFw | intros a Ha; eapply (win_unowned A' M' model'); [exact AI' | unfold W_of in Ha; cbn [fst snd] in Ha; lia]] |].
      intros a [Ha | Ha]; [exact Ha |]. destruct (HF a Ha) as [Hj | Hw]; [left; exact Hj | right; unfold W_of; cbn [fst snd]; lia].
    - intros i Hi. destruct (ef_def _ _ _ _ _ _ _ _ _ EF (sp - LIB_STACK + i) ltac:(lia) (DEFW i Hi)) as [H|[H|[H|H]]].
      + exact H.
      + exfalso. refine (win_unowned A M model _ AI _ H). lia.
      + destruct (HF _ H) as [(Hlt & _) | Hw]; [lia|]. apply (HFd _ H Hw).
      + exfalso. pose proof (ly_img_low _ (ly_rw_img _ (ly_errno_rw _ H))). lia.
    - assert (AG : forall a k, sp' + 2544 <= a -> 0 <= k -> a + k <= sp -> defined M a k -> agree_on M M' a k).
      { intros a k Ha Hk Hak Hd. eapply (agree_above_via_eff' A A' M M' _ F a k sp'); [exact EF | lia | cbn; lia | lia | lia | lia | | exact Hd |].
        + intros i Hi. eapply (win_unowned A M model); [exact AI | lia].
        + intros i Hi Hf. destruct (HF _ Hf) as [(Hlt & _) | Hw]; lia. }
      destruct FR as (F1 & F2 & F3 & F4). unfold tframe.
      assert (DW : forall a k, sp - LIB_STACK <= a -> a + k <= sp -> defined M a k) by (intros a k H1 H2 i Hi; pose proof (DEFW (a + i - (sp - LIB_STACK)) ltac:(lia)) as D; replace (sp - LIB_STACK + (a + i - (sp - LIB_STACK))) with (a + i) in D by lia; exact D).
      repeat split; try (eapply cellw_agree; [eassumption | apply AG; try lia; apply DW; lia | lia | cbn; lia]).
  Qed.
End Shared.
Arguments cell_call {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C A M model A' M' STK F a w v _ _ _ _ _ _ _.
Arguments mk_callB {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C A M model R retpc STK _ _ _ _ _ _.
Arguments sp_facts {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C.
Arguments win_defined {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C.
Arguments win_unowned {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C A M model a _ _.
Arguments iroc0 {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C.
Arguments eff_close {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C A' M' model' _ _ _.
Arguments tinv_call {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C A M model A' M' model' R R' STK F _ _ _ _ _.
Arguments tinv_store {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C A M model M' Fw _ _ _ _.
Arguments tinv_storeJ {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C A M model M' Fh _ _ _ _ _.
Arguments J_offimg {AC MI A0 a} _.
Arguments tinv_callW {AC MI ST cR cC cV kc fx A0 s R0 M0 model0 sp ret p n payload K} C A M model A' M' model' R R' STK F _ _ _ _ _ _.
