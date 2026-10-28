(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmGlue LbB_PmVops LbB_PmWKit LbB_HKit LbB_PmVCL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition RT_VC1 : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 9040)); (25%bv, ELit 2147450880); (27%bv, EAlu ALU_ADD (EVar 32) (ELit 48))].
Definition RT_VC1R : list (reg * expr) := [(22%bv, EAlu ALU_ADD (EVar 32) (ELit 224)); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (26%bv, EAlu ALU_ADD (EVar 32) (ELit 216))].
Definition VC1_LOG : list sentry :=
  [SE (SA (EVar 35) 416) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); SE (SA (EVar 35) 432) 8 (EAlu ALU_ADD (EVar 32) (ELit 232));
   SE (SA (EVar 35) 440) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); SE (SA (EVar 35) 528) 8 (EAlu ALU_ADD (EVar 32) (ELit 48));
   SE (SA (EVar 35) 640) 8 (EAlu ALU_ADD (EVar 33) (ELit 9136))].
Definition VC1_KS : list Z := [416; 432; 440; 528; 640].
Definition vc1_tbl (tbl : list (Z * expr)) : list (Z * expr) :=
  upd_slots VC1_LOG (EVar WV_S1) tbl ++ add_slots VC1_LOG (EVar WV_S1) VC1_KS.
Definition VC1_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 27]%bv.

Definition RT_VC1X : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EVar 41); (12%bv, EVar 42); (19%bv, EVar 32); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 224)); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 9040)); (25%bv, ELit 2147450880); (26%bv, EAlu ALU_ADD (EVar 32) (ELit 216)); (27%bv, EAlu ALU_ADD (EVar 32) (ELit 48))].
Definition RT_VC1L : list (reg * expr) := RT_VC1X ++ [(11%bv, ELit 20); (13%bv, EVar 42)].
Definition RT_VC1A : list (reg * expr) :=
  [(1%bv, ELit 0xf0a20); (2%bv, EVar 35); (10%bv, EVar 41); (11%bv, EVar 43); (12%bv, EVar 42); (13%bv, EVar 41)] ++ RT_VC1R.
Definition KN_VC1 : list kentry :=
  [KWord (SA (EVar WV_P) 216) 8 (EVar 41); KWord (SA (EVar WV_P) 224) 8 (EVar 42); KWord (SA (EVar WV_P) 232) 8 (EVar 43)].
Definition VC1_LOGA : list sentry := [SE (SA (EVar 35) 416) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880))].
Definition VC1_LOGS : list sentry := [SE (SA (EVar 35) 640) 8 (EAlu ALU_ADD (EVar 33) (ELit 9136)); SE (SA (EVar 35) 528) 8 (EAlu ALU_ADD (EVar 32) (ELit 48)); SE (SA (EVar 35) 432) 8 (EAlu ALU_ADD (EVar 32) (ELit 232)); SE (SA (EVar 35) 440) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880))].
Definition VC1_LOGB : list sentry := VC1_LOGS ++ [SE (SA (EVar 32) 224) 8 (EVar 41)].
Definition VC1_KSB : list Z := [432; 440; 528; 640].
Definition vc1_tbl1 (tbl : list (Z * expr)) : list (Z * expr) :=
  upd_slots VC1_LOGA (EVar WV_S1) tbl ++ add_slots VC1_LOGA (EVar WV_S1) [416].

Lemma upd_slots_ext : forall L1 L2 b tbl, (forall k, lword L1 b k = lword L2 b k) ->
  upd_slots L1 b tbl = upd_slots L2 b tbl.
Proof.
  intros L1 L2 b tbl HL. induction tbl as [|[k e] t IH]; cbn [upd_slots]; [reflexivity|]. rewrite HL, IH. reflexivity.
Qed.

Lemma vc1_upd_closed : forall log b tbl, forallb (fun ke : Z * expr => wclosed (snd ke)) tbl = true ->
  forallb (fun ke : Z * expr => wclosed (snd ke)) (upd_slots log b tbl) = true.
Proof.
  intros log b tbl. induction tbl as [|[k0 e] t IH]; cbn [upd_slots forallb fst snd]; [reflexivity|].
  intros Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
  destruct (lword log b k0) as [[v|]|]; [destruct (wclosed v) eqn:Wv|..]; cbn [forallb fst snd];
    rewrite ?Wv, ?Hc1; cbn [andb]; exact (IH Hc2).
Qed.

Lemma vc1_add_closed : forall log b ks, forallb (fun ke : Z * expr => wclosed (snd ke)) (add_slots log b ks) = true.
Proof.
  intros log b ks. induction ks as [|k0 t IH]; cbn [add_slots forallb]; [reflexivity|].
  destruct (lword log b k0) as [[v|]|]; [destruct (wclosed v) eqn:Wv|..]; cbn [forallb fst snd];
    rewrite ?Wv; cbn [andb]; exact IH.
Qed.

Lemma upd_slots_keys : forall log b tbl k, In k (map fst (upd_slots log b tbl)) -> In k (map fst tbl).
Proof.
  intros log b tbl k. induction tbl as [|[k0 e] t IH]; cbn [upd_slots map]; [tauto|].
  destruct (lword log b k0) as [[v|]|]; [destruct (wclosed v)|..]; cbn [map fst In]; intros Hin;
    first [destruct Hin as [Hin|Hin]; [left; exact Hin | right; exact (IH Hin)] | right; exact (IH Hin)].
Qed.

Lemma add_slots_keys : forall log b ks k, In k (map fst (add_slots log b ks)) -> In k ks.
Proof.
  intros log b ks k. induction ks as [|k0 t IH]; cbn [add_slots map]; [tauto|].
  destruct (lword log b k0) as [[v|]|]; [destruct (wclosed v)|..]; cbn [map fst In]; intros Hin;
    first [destruct Hin as [Hin|Hin]; [left; exact Hin | right; exact (IH Hin)] | right; exact (IH Hin)].
Qed.

Lemma vc1_slots_keys : forall log ks tbl, keys_ok ks = true -> keys_nonneg ks = true ->
  keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
  keys_ok (map fst (upd_slots log (EVar WV_S1) tbl ++ add_slots log (EVar WV_S1) ks)) = true
  /\ keys_nonneg (map fst (upd_slots log (EVar WV_S1) tbl ++ add_slots log (EVar WV_S1) ks)) = true.
Proof.
  intros log ks tbl Hks Hksn Hk Hn.
  assert (KS : forall k, In k (map fst (upd_slots log (EVar WV_S1) tbl ++ add_slots log (EVar WV_S1) ks)) ->
                 In k (map fst tbl) \/ In k ks).
  { intros k Hin. rewrite map_app, in_app_iff in Hin.
    destruct Hin as [Hin|Hin]; [left; exact (upd_slots_keys _ _ _ _ Hin) | right; exact (add_slots_keys _ _ _ _ Hin)]. }
  split.
  - unfold keys_ok in *. apply forallb_forall. intros k Hin. destruct (KS k Hin) as [H1|H1].
    + exact (proj1 (forallb_forall _ _) Hk k H1).
    + exact (proj1 (forallb_forall _ _) Hks k H1).
  - unfold keys_nonneg in *. apply forallb_forall. intros k Hin. destruct (KS k Hin) as [H1|H1].
    + exact (proj1 (forallb_forall _ _) Hn k H1).
    + exact (proj1 (forallb_forall _ _) Hksn k H1).
Qed.

Lemma vc1_tbl_keys : forall tbl, keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
  keys_ok (map fst (vc1_tbl tbl)) = true /\ keys_nonneg (map fst (vc1_tbl tbl)) = true.
Proof.
  intros tbl Hk Hn. exact (vc1_slots_keys VC1_LOG VC1_KS tbl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hk Hn).
Qed.

Lemma vc1_slots_closed : forall log ks tbl, tbl_closed tbl = true ->
  tbl_closed (upd_slots log (EVar WV_S1) tbl ++ add_slots log (EVar WV_S1) ks) = true.
Proof.
  intros log ks tbl Hc. unfold tbl_closed in *. rewrite forallb_app, (vc1_upd_closed _ _ _ Hc), vc1_add_closed. reflexivity.
Qed.

Lemma upd_slots_app : forall log b t1 t2, upd_slots log b (t1 ++ t2) = upd_slots log b t1 ++ upd_slots log b t2.
Proof.
  intros log b t1 t2. induction t1 as [|[k e] t IH]; cbn [upd_slots app]; [reflexivity|].
  destruct (lword log b k) as [[v|]|]; [destruct (wclosed v)|..]; rewrite ?IH; reflexivity.
Qed.

Lemma lword_app : forall L1 L2 b k, lword (L1 ++ L2) b k = match lword L1 b k with None => lword L2 b k | r => r end.
Proof.
  induction L1 as [|[a w v] L1 IH]; intros L2 b k; cbn [app lword]; [reflexivity|].
  destruct ((expr_eqb (a_base a) b && (a_off a <? k + 8) && (k <? a_off a + Z.of_nat w))%bool); [|apply IH].
  destruct ((Z.eqb (a_off a) k && Nat.eqb w 8)%bool); reflexivity.
Qed.

Lemma upd_slots_comp : forall L1 L2 b tbl, (forall k v, lword L1 b k = Some (Some v) -> lword L2 b k = None) ->
  upd_slots L2 b (upd_slots L1 b tbl) = upd_slots (L1 ++ L2) b tbl.
Proof.
  intros L1 L2 b tbl HN. induction tbl as [|[k e] t IH]; [reflexivity|].
  cbn [upd_slots]. rewrite lword_app. destruct (lword L1 b k) as [[v|]|] eqn:E1; cbn [upd_slots].
  - destruct (wclosed v); [cbn [upd_slots]; rewrite (HN k v E1), IH; reflexivity | exact IH].
  - exact IH.
  - destruct (lword L2 b k) as [[v|]|]; [destruct (wclosed v)|..]; rewrite ?IH; reflexivity.
Qed.

Lemma vc1_rlog : forall k, lword (VC1_LOGA ++ VC1_LOGB) (EVar WV_S1) k = lword VC1_LOG (EVar WV_S1) k.
Proof.
  intros k. unfold VC1_LOGA, VC1_LOGB, VC1_LOGS, VC1_LOG. cbn [app lword a_base a_off].
  change (expr_eqb (EVar 35) (EVar WV_S1)) with true. change (expr_eqb (EVar 32) (EVar WV_S1)) with false. cbn [andb].
  repeat (match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; try (exfalso; lia)).
  all: reflexivity.
Qed.

Lemma vc1_hitA : forall k v, lword VC1_LOGA (EVar WV_S1) k = Some (Some v) -> lword VC1_LOGB (EVar WV_S1) k = None.
Proof.
  intros k v Hs. destruct (Z.eqb_spec 416 k) as [<-|NE]; [vm_compute; reflexivity|].
  exfalso. revert Hs. unfold VC1_LOGA. cbn [lword a_base a_off].
  change (expr_eqb (EVar 35) (EVar WV_S1)) with true. rewrite (proj2 (Z.eqb_neq 416 k) NE). cbn [andb].
  match goal with |- context [if ?c then _ else _] => destruct c end; intros Hs; discriminate Hs.
Qed.

Lemma vc1_tbl_eq : forall tbl,
  upd_slots VC1_LOGB (EVar WV_S1) (vc1_tbl1 tbl) ++ add_slots VC1_LOGB (EVar WV_S1) VC1_KSB = vc1_tbl tbl.
Proof.
  intros tbl. unfold vc1_tbl1, vc1_tbl. rewrite upd_slots_app, <- app_assoc.
  rewrite (upd_slots_comp VC1_LOGA VC1_LOGB (EVar WV_S1) tbl vc1_hitA).
  rewrite (upd_slots_ext _ VC1_LOG _ tbl vc1_rlog). f_equal; vm_compute; reflexivity.
Qed.

Lemma vc1_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
  intros a b Ha Hb. apply bv_eq. rewrite u_sltu64, !u64_of_Z by lia.
  destruct (a <? b); rewrite u64_of_Z by lia; reflexivity.
Qed.

Lemma vc1_sc_xor : forall SEGS M E x1 y1 x2 y2 a1 b1 a2 b2,
  edenot E x1 = Z_to_bv 64 a1 -> edenot E y1 = Z_to_bv 64 b1 -> edenot E x2 = Z_to_bv 64 a2 -> edenot E y2 = Z_to_bv 64 b2 ->
  0 <= a1 < 2 ^ 64 -> 0 <= b1 < 2 ^ 64 -> 0 <= a2 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
  xorb (a1 <? b1) (a2 <? b2) = true ->
  sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_SLTU x1 y1) (EAlu ALU_SLTU x2 y2)) (ELit 0)).
Proof.
  intros SEGS M E x1 y1 x2 y2 a1 b1 a2 b2 H1 H2 H3 H4 R1 R2 R3 R4 Hx. cbn [sc_denot edenot].
  rewrite H1, H2, H3, H4, !vc1_sltu by lia.
  destruct (a1 <? b1), (a2 <? b2); cbn in Hx; try discriminate Hx; vm_compute; reflexivity.
Qed.

Lemma vc1_sc_cmp : forall SEGS M E t c x y a b, edenot E x = Z_to_bv 64 a -> edenot E y = Z_to_bv 64 b ->
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken c (Z_to_bv 64 a) (Z_to_bv 64 b) = t ->
  sc_denot SEGS M E (SCBr t c x y).
Proof. intros SEGS M E t c x y a b Hx Hy Ha Hb Ht. cbn [sc_denot]. rewrite Hx, Hy. exact Ht. Qed.

Lemma vc1_keep {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X R R1 RT sr r,
  regs_tblX w X R RT -> tbl_okX (xbound X) RT = true -> regs_ok (Eseed R (wenv_vals w ++ X)) sr R1 ->
  sr_get sr r = sr_get (srs sr_id RT) r -> PropExec.getr R1 r = PropExec.getr R r.
Proof.
  intros w X R R1 RT sr r HT Hok HR Hs. rewrite (HR r), Hs. symmetry. exact (regs_ok_of_tbl w R RT X _ HT Hok r).
Qed.

Lemma vc1_ne13 : forall r : bv 5, bv_unsigned r <> 13 -> r <> 13%bv.
Proof. intros r Hr Hc. apply Hr. rewrite Hc. reflexivity. Qed.

Lemma vc1_kept13 : forall r, In r VC1_KEPT -> r <> 13%bv.
Proof.
  intros r Hr. unfold VC1_KEPT in Hr.
  repeat (destruct Hr as [<-|Hr]; [apply vc1_ne13; vm_compute; congruence|]). destruct Hr.
Qed.

Lemma vc1_kept_sub : forall r, In r VC1_KEPT -> In r KEPT_REGS.
Proof. intros r Hr. unfold VC1_KEPT in Hr. repeat (destruct Hr as [<-|Hr]; [inb|]). destruct Hr. Qed.

Ltac vc1_v S1 S2 S3 := first [ exact S1 | exact S2 | exact S3 | reflexivity ].
Ltac vc1_bool := repeat match goal with
                        | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
                        | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
                        end; cbn; first [reflexivity | exfalso; lia].
Ltac vc1_sc S1 S2 S3 :=
  first
    [ eapply vc1_sc_xor; [vc1_v S1 S2 S3 | vc1_v S1 S2 S3 | vc1_v S1 S2 S3 | vc1_v S1 S2 S3 | lia | lia | lia | lia | vc1_bool]
    | eapply vc1_sc_cmp; [vc1_v S1 S2 S3 | vc1_v S1 S2 S3 | lia | lia |
        first [rewrite br_ltu by lia | rewrite br_eq by lia | rewrite br_geu by lia | rewrite br_ne by lia]; vc1_bool] ].

Section VC1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHc1 : asan_rt_hyps H.
Proof.
  exact (rt_bp_base H HHbp).
Qed.

  Lemma vc1_after1 : forall (w : pmwA H) s LB LBs m mo mo' c ins tbl ftbl TB spal R X,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_ok (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true -> as_MPRES H mo mo' ->
    log_flat (Eseed R (wenv_vals w ++ X)) VC1_LOGA -> mem_inv asegs (mem_denot (Eseed R (wenv_vals w ++ X)) m VC1_LOGA) ->
    PMXAT H LINV w s LB LBs (mem_denot (Eseed R (wenv_vals w ++ X)) m VC1_LOGA) mo' c ins (vc1_tbl1 tbl) ftbl TB spal
    /\ ffkeep w m (mem_denot (Eseed R (wenv_vals w ++ X)) m VC1_LOGA).
  Proof.
    intros w s LB LBs m mo mo' c ins tbl ftbl TB spal R X OK X0 Hk Hfk MP Hlf MI.
    set (E := Eseed R (wenv_vals w ++ X)) in *.
    assert (HE : env_world H w E) by apply env_world_seed.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmx_p_range H w OK) as (PP1 & PP2 & PP3).
    pose proof (munch_sym E m VC1_LOGA [(EVar WV_S1, 416, 424)] Hlf ltac:(vm_compute; reflexivity)) as MU.
    cbn [num_wins map] in MU. rewrite (ev_s1 H w E OK HE) in MU.
    set (m' := mem_denot E m VC1_LOGA) in *.
    assert (WM : wmono asegs m m') by apply wmono_mem_denot.
    assert (FSHL : Z.of_nat (length (pm_fsh ins)) = 1448) by (unfold pm_fsh; rewrite length_map, pm_fsh_len; reflexivity).
    assert (Hkr : forall k, In k (map fst tbl) -> PM_RF_LO <= k /\ k + 8 <= PM_RF_TOP).
    { intros k Hin. pose proof (proj1 (forallb_forall _ _) Hk k Hin) as KK. apply andb_true_iff in KK as [K1 K2].
      apply Z.leb_le in K1. apply Z.leb_le in K2. lia. }
    unfold PARSER_SIZE, O_WIDX, O_ICOUNT, O_ENDIAN, O_FLAGS, PM_RF_LO, PM_RF_TOP in *.
    split.
    - apply (pmxa_mpres H HHc1 LINV w s LB LBs m' mo mo' c ins (vc1_tbl1 tbl) ftbl TB spal); [| exact MP].
      apply (pmxa_own0 H HHc1 LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m' [(wa_s1 w + 416, wa_s1 w + 424)] ins (vc1_tbl1 tbl) ftbl
               OK X0 MU WM).
      + intros x Hx. apply mem_denot_defined. exact Hx.
      + exact MI.
      + apply stk_mem_denot. exact (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0).
      + apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia.
      + apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
      + eapply SHAD_transport; [exact (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | exact WM |].
        rewrite FSHL. cbn [disjoint_from]. split; [lia | exact I].
      + unfold vc1_tbl1.
        apply (slots_mem_denot H w m bvmap_empty tbl E VC1_LOGA [416] (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) Hlf (ev_s1 H w E OK HE) HE).
        * intros k Hin. apply Forall_forall. intros se Hse Hne. unfold VC1_LOGA in Hse. cbn [In] in Hse.
          destruct Hse as [<-|[]]; vm_compute in Hne; discriminate Hne.
        * intros k Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [specialize (Hkr k Hin); lia|].
          cbn [In] in Hin. lia.
        * intros k Hin. pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (W1 & W2 & W3).
          cbn [In] in Hin.
          split; [lia|]. split; [lia|]. intros i Hi.
          exact (proj1 (W3 (wa_s1 w + k + i) ltac:(lia))).
      + pose proof (xa_fslots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as FS. unfold fslots_ok in *.
        apply Forall_forall. intros [k e] Hin. pose proof (proj1 (Forall_forall _ _) FS (k, e) Hin) as FSk. cbn [fst snd] in *.
        assert (Hkf : In k (map fst ftbl)) by (apply in_map_iff; exists (k, e); split; [reflexivity | exact Hin]).
        pose proof (proj1 (forallb_forall _ _) Hfk k Hkf) as KK. apply andb_true_iff in KK as [K1 K2].
        apply Z.leb_le in K1. apply Z.leb_le in K2.
        eapply rw_cells_transport; [exact FSk | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Z.of_nat].
        split; [lia | exact I].
      + eapply fld_munch; [exact (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | | |];
          unfold O_WIDX, O_ICOUNT, O_ENDIAN, O_FLAGS; cbn [disjoint_from]; try split; try exact I; lia.
      + eapply fld_munch; [exact (xa_icount _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | | |];
          unfold O_WIDX, O_ICOUNT, O_ENDIAN, O_FLAGS; cbn [disjoint_from]; try split; try exact I; lia.
      + eapply fld_munch; [exact (xa_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | | |];
          unfold O_WIDX, O_ICOUNT, O_ENDIAN, O_FLAGS; cbn [disjoint_from]; try split; try exact I; lia.
      + eapply fld_munch; [exact (xa_flags _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | | |];
          unfold O_WIDX, O_ICOUNT, O_ENDIAN, O_FLAGS; cbn [disjoint_from]; try split; try exact I; lia.
      + eapply fld_munch; [exact (xa_retry _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | | |];
          unfold O_WIDX, O_ICOUNT, O_ENDIAN, O_FLAGS; cbn [disjoint_from]; try split; try exact I; lia.
    - apply (ffkeep_munch w _ m m' MU WM). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
  Qed.

  Lemma vc1_slotsB : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal E,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins (vc1_tbl1 tbl) ftbl TB spal -> env_world H w E ->
    keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true -> log_flat E VC1_LOGB ->
    slots_ok w (mem_denot E m VC1_LOGB) bvmap_empty (vc1_tbl tbl).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E OK X0 HE Hk Hknn Hlf.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmx_p_range H w OK) as (PP1 & PP2 & PP3).
    pose proof (ev_world_all H w E HE) as (EV32 & _).
    destruct (vc1_slots_keys VC1_LOGA [416] tbl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hk Hknn) as (Hk1 & _).
    assert (Hkr : forall k, In k (map fst (vc1_tbl1 tbl)) -> PM_RF_LO <= k /\ k + 8 <= PM_RF_TOP).
    { intros k Hin. pose proof (proj1 (forallb_forall _ _) Hk1 k Hin) as KK. apply andb_true_iff in KK as [K1 K2].
      apply Z.leb_le in K1. apply Z.leb_le in K2. lia. }
    unfold PARSER_SIZE, PM_RF_LO, PM_RF_TOP in *.
    rewrite <- (vc1_tbl_eq tbl).
    apply (slots_mem_denot H w m bvmap_empty (vc1_tbl1 tbl) E VC1_LOGB VC1_KSB (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) Hlf (ev_s1 H w E OK HE) HE).
    - intros k Hin. apply Forall_forall. intros se Hse Hne. unfold VC1_LOGB, VC1_LOGS in Hse. cbn [In app] in Hse.
      destruct Hse as [<-|[<-|[<-|[<-|[<-|[]]]]]]; vm_compute in Hne; try discriminate Hne.
      cbn [e_addr e_width]. rewrite (estart_var _ 32 224 (wa_p w) EV32) by lia.
      apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [specialize (Hkr k Hin) | unfold VC1_KSB in Hin; cbn [In] in Hin]; lia.
    - intros k Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [specialize (Hkr k Hin); lia|].
      unfold VC1_KSB in Hin. cbn [In] in Hin. lia.
    - intros k Hin. pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (W1 & W2 & W3).
      unfold VC1_KSB in Hin. cbn [In] in Hin.
      split; [lia|]. split; [lia|]. intros i Hi.
      exact (proj1 (W3 (wa_s1 w + k + i) ltac:(lia))).
  Qed.

  Lemma vc1_tail : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins (vc1_tbl1 tbl) ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf09a8) fc None m (seg_rom asegs) -> rfull R ->
    tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
    tbl_closed ftbl = true -> fkeys_ok (map fst ftbl) = true ->
    regs_tblX w [Z_to_bv 64 (t3a (c_v1 c)); Z_to_bv 64 (t3a (c_v1 c) + 20 * t3b (c_v1 c));
                 Z_to_bv 64 (t3a (c_v1 c) + 20 * t3c (c_v1 c))] R RT_VC1X ->
    (forall msF2 mo2 m2 R2, as_AKREL H s (mkCfg msF2 mo2) ->
       as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0xf0a20) fc None m2 (seg_rom asegs) -> rfull R2 ->
       PMXAT H LINV w s LB LBs m2 mo2 (set_v1A c (t3a (c_v1 c), 0, t3c (c_v1 c))) ins (vc1_tbl tbl) ftbl TB spal ->
       (forall r, In r VC1_KEPT -> PropExec.getr R2 r = PropExec.getr R r) ->
       regs_tbl w R2 RT_VC1R ->
       ffkeep w m m2 ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc Q OK X KR VIS RF Hc Hk Hknn Hfc Hfk HT K.
    destruct (vc1_slots_keys VC1_LOGA [416] tbl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hk Hknn) as (Hk1 & Hknn1).
    pose proof (vc1_slots_closed VC1_LOGA [416] tbl Hc) as Hc1. fold (vc1_tbl1 tbl) in Hc1.
    destruct (vc1_tbl_keys tbl Hk Hknn) as (Hk2 & Hknn2).
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmx_p_range H w OK) as (PP1 & PP2 & PP3).
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (p_apart_ff H w OK) as PAF.
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V1.
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as ((_ & _ & _ & SHV1 & _) & _ & _).
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    pose proof (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as ACm.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as PDEF.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK ltac:(lia)) as [STK1 _].
    destruct (c_v1 c) as [[b n] cap] eqn:EV1. cbn [t3a t3b t3c fst snd] in *.
    destruct V1 as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2).
    unfold PARSER_SIZE, O_V1, OPND_SZ, O_WIDX, PM_RF_TOP in *.
    assert (HB : 0 <= b /\ b + 20 * cap <= 2 ^ 63) by (destruct Hb as [[B0 C0]|(B1 & B2 & B3 & B4 & _)]; lia).
    set (Xs := [Z_to_bv 64 b; Z_to_bv 64 (b + 20 * n); Z_to_bv 64 (b + 20 * cap)]) in *.
    set (E := Eseed R (wenv_vals w ++ Xs)).
    assert (HE : env_world H w E) by apply env_world_seed.
    pose proof (ev_world_all H w E HE) as (EV32 & EV33 & EV34 & EV35 & _).
    assert (S41 : edenot E (EVar 41) = Z_to_bv 64 b) by reflexivity.
    assert (S42 : edenot E (EVar 42) = Z_to_bv 64 (b + 20 * n)) by reflexivity.
    assert (S43 : edenot E (EVar 43) = Z_to_bv 64 (b + 20 * cap)) by reflexivity.
    assert (ES : forall k, estart E (SA (EVar 35) k) = wa_s1 w + k) by (intros k; apply estart_var; [exact EV35 | lia]).
    assert (EP : forall k, estart E (SA (EVar 32) k) = wa_p w + k) by (intros k; apply estart_var; [exact EV32 | lia]).
    assert (HKN : know_ok asegs E m (PM_KN_FIX ++ slot_kn (add_slots VC1_LOGA (EVar WV_S1) [416]) ++ KN_VC1)).
    { destruct (pm_kn_fix_ok H HHc1 LINV w s LB LBs m mo c ins (vc1_tbl1 tbl) ftbl TB spal E OK X HE Hc1 Hk1 Hfc Hfk) as (K1 & K2 & _).
      unfold know_ok. apply Forall_app. split; [exact K1|]. apply Forall_app. split.
      - apply Forall_forall. intros ke Hin. unfold slot_kn in Hin. apply in_map_iff in Hin. destruct Hin as ([k e'] & <- & Hin).
        apply K2. unfold vc1_tbl1. apply in_or_app. right. exact Hin.
      - unfold KN_VC1. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
        + apply (kword_of_fld E m (wa_p w + 216) 8 b); [exact F0 | lia | rewrite (estart_p H w E 216 OK HE); reflexivity | lia | cbn [Z.of_nat]; lia | exact S41].
        + apply (kword_of_fld E m (wa_p w + 216 + 8) 8 (b + 20 * n)); [exact F1 | lia | rewrite (estart_p H w E 224 OK HE); lia | lia | cbn [Z.of_nat]; lia | exact S42].
        + apply (kword_of_fld E m (wa_p w + 216 + 16) 8 (b + 20 * cap)); [exact F2 | lia | rewrite (estart_p H w E 232 OK HE); lia | lia | cbn [Z.of_nat]; lia | exact S43]. }
    assert (WRP : wr_at asegs m (wa_p w + 224) 8) by exact (wr_at_of_mdef m (wa_p w) 288 224 8 PDEF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (DLS : Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E (SA (EVar 32) 224)
                                     \/ estart E (SA (EVar 32) 224) + Z.of_nat 8 <= estart E (e_addr e')) VC1_LOGS).
    { unfold VC1_LOGS. repeat apply Forall_cons; try apply Forall_nil; cbn [e_addr e_width]; rewrite ES, EP; cbn [Z.of_nat]; lia. }
    destruct (Z.eq_dec b 0) as [B0|BNZ].
    - assert (C0 : cap = 0) by (destruct Hb as [[_ C0]|(B1 & _)]; [exact C0 | lia]).
      assert (N0 : n = 0) by lia.
      pm_goR HHc1 OK X KR VIS RF HT Xs (PM_KN_FIX ++ slot_kn (add_slots VC1_LOGA (EVar WV_S1) [416]) ++ KN_VC1) HKN
        300%nat [AANNOTATE_CC; 0xf0a20] [false; false; false; false; true] 44%N RT_VC1R.
      { split_scs. all: vc1_sc S41 S42 S43. }
      intros msF2 mo2 R2 KR2 MP2 VIS2 RF2 MI2 HT2 HR2 Hlf2.
      assert (RP : s_pc SSr = 0xf0a20) by (vm_compute; reflexivity).
      assert (RL : s_log SSr = VC1_LOGB) by (vm_compute; reflexivity).
      rewrite RP in VIS2. rewrite RL in VIS2, MI2, Hlf2.
      set (M2 := mem_denot (Eseed R (wenv_vals w ++ Xs)) m VC1_LOGB) in *.
      pose proof (munch_sym E m _ [(EVar WV_P, 224, 232); (EVar WV_S1, 432, 448); (EVar WV_S1, 528, 536); (EVar WV_S1, 640, 648)]
                    Hlf2 ltac:(vm_compute; reflexivity)) as MU2.
      cbn [num_wins map] in MU2. rewrite (ev_p H w E OK HE), (ev_s1 H w E OK HE) in MU2.
      assert (RW2 : rw_cells asegs M2 (wa_p w + 224) [C8 (Z_to_bv 64 b)]).
      { apply (rw_cells_mem_denot_w E m VC1_LOGS (SA (EVar 32) 224) 8 (EVar 41) [] (wa_p w + 224) (C8 (Z_to_bv 64 b)));
          [exact Hlf2 | exact DLS | rewrite EP; lia | exact WRP | reflexivity | exact I | rewrite S41; reflexivity]. }
      assert (X2 : PMXAT H LINV w s LB LBs M2 mo2 (set_v1A c (b, 0, cap)) ins (vc1_tbl tbl) ftbl TB spal).
      { replace (b, 0, cap) with (t3a (c_v1 c), 0, t3c (c_v1 c)) by (rewrite EV1; reflexivity).
        eapply (pmxa_vupd1T H HHc1 LINV LINV_frame w s LB LBs m mo c ins (vc1_tbl1 tbl) ftbl TB spal M2 mo2
                  [(wa_p w + 224, wa_p w + 232); (wa_s1 w + 432, wa_s1 w + 448); (wa_s1 w + 528, wa_s1 w + 536); (wa_s1 w + 640, wa_s1 w + 648)]
                  [] 0 (vc1_tbl tbl));
          [exact OK | exact X | exact Hknn1 | exact Hfk | rewrite app_nil_r; exact MU2 | apply wmono_mem_denot
          | intros x Hx; apply mem_denot_defined; exact Hx | exact MP2 | exact MI2
          | exact (vc1_slotsB w s LB LBs m mo c ins tbl ftbl TB spal E OK X HE Hk Hknn Hlf2)
          | | apply Forall_nil | |].
        - unfold vwinT, vwin, rfw, PM_RF_TOP.
          apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]; cbn [fst snd].
          + left. split; [lia|]. left. unfold O_V1. lia.
          + right. lia.
          + right. lia.
          + right. lia.
        - rewrite EV1. cbn [t3a t3c fst snd]. unfold vec_opnd, OPND_SZ, O_V1.
          split; [exact Hv|]. split; [exact Hv'|]. split; [intros i Hi; apply mem_denot_defined; apply HD; lia|].
          split; [lia|]. split; [exact Hb|]. split; [|split].
          + eapply fld_munch; [exact F0 | exact MU2 | cbn [disjoint_from]; repeat split; lia | lia | lia].
          + replace (wa_p w + 216 + 8) with (wa_p w + 224) by lia.
            replace (b + 20 * 0) with (bv_unsigned (Z_to_bv 64 b)) by (rewrite u64_of_Z by lia; lia).
            apply fld_of_cell8; [exact RW2 | lia].
          + eapply fld_munch; [exact F2 | exact MU2 | cbn [disjoint_from]; repeat split; lia | lia | lia].
        - rewrite EV1. unfold vsh_opnd. cbn [t3a t3b t3c fst snd]. intros NZ. exfalso. exact (NZ B0). }
      eapply (K msF2 mo2 M2 R2 KR2 VIS2 RF2 X2).
      + intros r Hr. apply (vc1_keep w Xs R R2 RT_VC1X _ r HT ltac:(vm_compute; reflexivity) HR2).
        unfold VC1_KEPT in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr.
      + exact (regs_tbl_restrict w [] Xs R2 RT_VC1R HT2 ltac:(vm_compute; reflexivity)).
      + apply (ffkeep_munch w _ m M2 MU2 (wmono_mem_denot _ _ _)).
        repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - pose proof Hb as Hb0. destruct Hb0 as [[B0' _]|(Bpos & B16 & Cpos & Bhi & Hlive & Bapart)]; [exfalso; lia|].
      assert (BLK : exists pid, In (pid, b, 20 * cap) LBs /\ In (pid, b, 20 * cap) LB /\ In (b, 20 * cap) (lbl LB)
                                /\ ablock_range H b (20 * cap) /\ 20 * cap <= 2 ^ 31).
      { apply (cblk_facts H HHc1 LINV w s LB LBs m mo c ins (vc1_tbl1 tbl) ftbl TB spal b (20 * cap) OK X).
        unfold c_blocks. rewrite EV1. cbn [t3a t3c fst snd]. rewrite !in_app_iff. right; right; right; left.
        unfold vec_opnd_blocks, OPND_SZ. destruct (Z.eqb_spec b 0); [lia | left; reflexivity]. }
      destruct BLK as (pid & INs & INL & INl & (R0 & R16 & Rn & RI & RC & RF' & RAPP) & SZ).
      pose proof (aapp_bounds _ _ RAPP ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5).
      pose proof (aapp_bounds _ _ PA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
      pose proof (aapp_disjoint_sh (wa_p w) 288 b (20 * cap) PA ltac:(lia) ltac:(lia) ltac:(lia)) as DSH.
      pose proof (blksh_apart_ff H HHc1 w s LB m pid b (20 * cap) OK RH INL) as (BF1 & BF2).
      assert (SHE : sh b + nsh (20 * cap) <= sh aceil) by (apply sh_end_le; lia).
      assert (SHA : sh aceil <= aceil) by apply sh_aceil_le.
      assert (NSHC : 0 <= nsh (20 * cap)) by (unfold nsh; apply Z.div_pos; lia).
      assert (B8 : b mod 8 = 0) by (Z.div_mod_to_equations; lia).
      pm_goR HHc1 OK X KR VIS RF HT Xs (PM_KN_FIX ++ slot_kn (add_slots VC1_LOGA (EVar WV_S1) [416]) ++ KN_VC1) HKN
        300%nat [AANNOTATE_CC; 0xf0a20] [false; false; false; false; false] 44%N RT_VC1A.
      { split_scs. all: vc1_sc S41 S42 S43. }
      intros msF2 mo2 R2 KR2 MP2 VIS2 RF2 MI2 HT2 HR2 Hlf2.
      assert (RP : s_pc SSr = AANNOTATE_CC) by (vm_compute; reflexivity).
      assert (RL : s_log SSr = VC1_LOGB) by (vm_compute; reflexivity).
      rewrite RP in VIS2. rewrite RL in VIS2, MI2, Hlf2.
      set (M2 := mem_denot (Eseed R (wenv_vals w ++ Xs)) m VC1_LOGB) in *.
      pose proof (munch_sym E m _ [(EVar WV_P, 224, 232); (EVar WV_S1, 432, 448); (EVar WV_S1, 528, 536); (EVar WV_S1, 640, 648)]
                    Hlf2 ltac:(vm_compute; reflexivity)) as MU2.
      cbn [num_wins map] in MU2. rewrite (ev_p H w E OK HE), (ev_s1 H w E OK HE) in MU2.
      assert (RW2 : rw_cells asegs M2 (wa_p w + 224) [C8 (Z_to_bv 64 b)]).
      { apply (rw_cells_mem_denot_w E m VC1_LOGS (SA (EVar 32) 224) 8 (EVar 41) [] (wa_p w + 224) (C8 (Z_to_bv 64 b)));
          [exact Hlf2 | exact DLS | rewrite EP; lia | exact WRP | reflexivity | exact I | rewrite S41; reflexivity]. }
      assert (SL2 : slots_ok w M2 bvmap_empty (vc1_tbl tbl))
        by exact (vc1_slotsB w s LB LBs m mo c ins tbl ftbl TB spal E OK X HE Hk Hknn Hlf2).
      assert (SH2 : SHAD M2 b (cc_gen (20 * cap) (20 * n))).
      { eapply SHAD_transport; [exact (SHV1 BNZ) | exact MU2 | apply wmono_mem_denot |].
        rewrite RtB_Iface.cc_gen_length by lia. cbn [disjoint_from]. repeat split; lia. }
      assert (ACm2 : ACONST M2).
      { eapply ACONST_frame; [exact ACm | exact MU2 | apply wmono_mem_denot |].
        apply Forall_cons; [eapply aconst_ok_app; [exact PA | lia | lia] |].
        repeat (apply Forall_cons; [apply (own_aconst_ok H w _ OK); left; cbn [fst snd]; lia |]). apply Forall_nil. }
      eapply (pm_annot H HHbp w s msF2 mo2 R2 F fc M2 b (20 * cap) (20 * n) 0 0xf0a20 Q OK KR2 VIS2 RF2);
        [ rtf HT2 | rtf HT2 | rtf HT2 | rewrite Z.add_0_r; rtf HT2 | rtf HT2 | rtf HT2 | reflexivity | lia
        | exact B8 | lia | lia | lia | exact RAPP | exact SH2 | apply stk_mem_denot; exact STK1 | exact MI2 | exact ACm2 | ].
      intros msF3 mo3 m3 R3 KR3 MP3 VIS3 RF3 MU3 WM3 MI3 STK3 SH3 ACm3 KEEP3.
      unfold AINTRIN_STACK in MU3.
      assert (DM3' : forall x, M2 x <> None -> m3 x <> None).
      { apply (annot_dm M2 m3 b (20 * cap) (cc_gen (20 * cap) 0) (wa_lo w) (wa_s1 w - 4096) (wa_s1 w) MU3 SH3);
          [rewrite RtB_Iface.cc_gen_length by lia; reflexivity | exact STK3 | lia | lia | lia | lia]. }
      assert (DM3 : forall x, m x <> None -> m3 x <> None) by (intros x Hx; apply DM3'; apply mem_denot_defined; exact Hx).
      assert (MUA : munch ([(wa_p w + 224, wa_p w + 232); (wa_s1 w + 432, wa_s1 w + 448); (wa_s1 w + 528, wa_s1 w + 536);
                            (wa_s1 w + 640, wa_s1 w + 648)] ++ [(sh b, sh b + nsh (20 * cap)); (wa_s1 w - 4096, wa_s1 w)]) m m3)
        by exact (munch_app _ _ _ _ _ MU2 MU3).
      assert (WMA : wmono asegs m m3) by exact (wmono_trans _ _ _ _ (wmono_mem_denot _ _ _) WM3).
      assert (SL3 : slots_ok w m3 bvmap_empty (vc1_tbl tbl)).
      { unfold slots_ok in *. rewrite Forall_forall in *. intros [k e'] Hin. pose proof (SL2 (k, e') Hin) as S0. cbn [fst snd] in *.
        assert (Hkin : In k (map fst (vc1_tbl tbl))) by (apply in_map_iff; exists (k, e'); split; [reflexivity | exact Hin]).
        pose proof (proj1 (forallb_forall _ _) Hk2 k Hkin) as KK1. pose proof (proj1 (forallb_forall _ _) Hknn2 k Hkin) as KK2.
        apply andb_true_iff in KK1 as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2. apply Z.leb_le in KK2.
        eapply rw_cells_transport; [exact S0 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Z.of_nat].
        unfold PM_RF_TOP, PM_RF_LO in *. repeat split; lia. }
      assert (X3 : PMXAT H LINV w s LB LBs m3 mo3 (set_v1A c (b, 0, cap)) ins (vc1_tbl tbl) ftbl TB spal).
      { replace (b, 0, cap) with (t3a (c_v1 c), 0, t3c (c_v1 c)) by (rewrite EV1; reflexivity).
        eapply (pmxa_vupd1T H HHc1 LINV LINV_frame w s LB LBs m mo c ins (vc1_tbl1 tbl) ftbl TB spal m3 mo3
                  [(wa_p w + 224, wa_p w + 232); (wa_s1 w + 432, wa_s1 w + 448); (wa_s1 w + 528, wa_s1 w + 536);
                   (wa_s1 w + 640, wa_s1 w + 648); (sh b, sh b + nsh (20 * cap))]
                  [(wa_s1 w - 4096, wa_s1 w)] 0 (vc1_tbl tbl));
          [exact OK | exact X | exact Hknn1 | exact Hfk | exact MUA | exact WMA | exact DM3
          | exact (ah_mpres_trans H HHc1 _ _ _ MP2 MP3) | exact MI3 | exact SL3 | | | |].
        - unfold vwinT, vwin, rfw, blkV1, PM_RF_TOP. rewrite EV1. cbn [t3a t3c fst snd].
          apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]];
            cbn [fst snd].
          + left. split; [lia|]. left. unfold O_V1. lia.
          + right. lia.
          + right. lia.
          + right. lia.
          + left. split; [lia|]. right; right. unfold OPND_SZ. split; [exact BNZ | lia].
        - apply Forall_cons; [| apply Forall_nil]. unfold swin. cbn [fst snd]. lia.
        - rewrite EV1. cbn [t3a t3c fst snd]. unfold vec_opnd, OPND_SZ, O_V1.
          split; [exact Hv|]. split; [exact Hv'|]. split; [intros i Hi; apply DM3; apply HD; lia|].
          split; [lia|]. split; [exact Hb|]. split; [|split].
          + eapply (fld_munch _ m m3); [exact F0 | exact MUA | cbn [disjoint_from app]; repeat split; lia | lia | lia].
          + replace (wa_p w + 216 + 8) with (wa_p w + 224) by lia.
            replace (b + 20 * 0) with (bv_unsigned (Z_to_bv 64 b)) by (rewrite u64_of_Z by lia; lia).
            apply fld_of_cell8; [| lia].
            eapply rw_cells_transport; [exact RW2 | exact MU3 | exact WM3 |].
            cbn [disjoint_from cells_size csize Z.of_nat]. repeat split; lia.
          + eapply (fld_munch _ m m3); [exact F2 | exact MUA | cbn [disjoint_from app]; repeat split; lia | lia | lia].
        - rewrite EV1. unfold vsh_opnd, OPND_SZ. cbn [t3a t3b t3c fst snd]. intros _. replace (20 * 0) with 0 by lia. exact SH3. }
      eapply (K msF3 mo3 m3 R3 KR3 VIS3 RF3 X3).
      + intros r Hr. rewrite (KEEP3 r (vc1_kept_sub r Hr)).
        apply (vc1_keep w Xs R R2 RT_VC1X _ r HT ltac:(vm_compute; reflexivity) HR2).
        unfold VC1_KEPT in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr.
      + unfold regs_tblX, RT_VC1R. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          rewrite (KEEP3 _ ltac:(inb)); rtf HT2.
      + apply (ffkeep_munch w _ m m3 MUA WMA). cbn [app].
        repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
  Qed.

  Lemma pm_vclear1 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0950) fc None m (seg_rom asegs) -> rfull R ->
    tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
    tbl_closed ftbl = true -> fkeys_ok (map fst ftbl) = true ->
    regs_tbl w R RT_VC1 ->
    (forall msF2 mo2 m2 R2, as_AKREL H s (mkCfg msF2 mo2) ->
       as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0xf0a20) fc None m2 (seg_rom asegs) -> rfull R2 ->
       PMXAT H LINV w s LB LBs m2 mo2 (set_v1A c (t3a (c_v1 c), 0, t3c (c_v1 c))) ins (vc1_tbl tbl) ftbl TB spal ->
       (forall r, In r VC1_KEPT -> PropExec.getr R2 r = PropExec.getr R r) ->
       regs_tbl w R2 RT_VC1R ->
       ffkeep w m m2 ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc Q OK X KR VIS RF Hc Hk Hknn Hfc Hfk HT K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmx_p_range H w OK) as (PP1 & PP2 & PP3).
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V1.
    set (b := t3a (c_v1 c)) in *. set (n := t3b (c_v1 c)) in *. set (cap := t3c (c_v1 c)) in *.
    destruct V1 as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2).
    unfold PARSER_SIZE, O_V1, OPND_SZ in *.
    assert (HB : 0 <= b /\ b + 20 * cap <= 2 ^ 63) by (destruct Hb as [[B0 C0]|(B1 & B2 & B3 & B4 & _)]; lia).
    set (Xs := [Z_to_bv 64 b; Z_to_bv 64 (b + 20 * n); Z_to_bv 64 (b + 20 * cap)]).
    set (E := Eseed R (wenv_vals w ++ Xs)).
    assert (HE : env_world H w E) by apply env_world_seed.
    assert (S41 : edenot E (EVar 41) = Z_to_bv 64 b) by reflexivity.
    assert (S42 : edenot E (EVar 42) = Z_to_bv 64 (b + 20 * n)) by reflexivity.
    assert (S43 : edenot E (EVar 43) = Z_to_bv 64 (b + 20 * cap)) by reflexivity.
    assert (HT1 : regs_tblX w Xs R RT_VC1) by exact (regs_tbl_ext w [] Xs R RT_VC1 HT ltac:(vm_compute; reflexivity)).
    assert (HKN : know_ok asegs E m (PM_KN_FIX ++ KN_VC1)).
    { destruct (pm_kn_fix_ok H HHc1 LINV w s LB LBs m mo c ins tbl ftbl TB spal E OK X HE Hc Hk Hfc Hfk) as (K1 & _ & _).
      unfold know_ok. apply Forall_app. split; [exact K1|].
      unfold KN_VC1. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
      + apply (kword_of_fld E m (wa_p w + 216) 8 b); [exact F0 | lia | rewrite (estart_p H w E 216 OK HE); reflexivity | lia | cbn [Z.of_nat]; lia | exact S41].
      + apply (kword_of_fld E m (wa_p w + 216 + 8) 8 (b + 20 * n)); [exact F1 | lia | rewrite (estart_p H w E 224 OK HE); lia | lia | cbn [Z.of_nat]; lia | exact S42].
      + apply (kword_of_fld E m (wa_p w + 216 + 16) 8 (b + 20 * cap)); [exact F2 | lia | rewrite (estart_p H w E 232 OK HE); lia | lia | cbn [Z.of_nat]; lia | exact S43]. }
    destruct (Z.eq_dec n 0) as [L0|LNZ].
    - pm_goR HHc1 OK X KR VIS RF HT1 Xs (PM_KN_FIX ++ KN_VC1) HKN 300%nat [0xf0998; 0xf09a8] [true] 44%N RT_VC1X.
      { split_scs. all: vc1_sc S41 S42 S43. }
      intros msF1 mo1 R1 KR1 MP1 VIS1 RF1 MI1 HT1' HR1 Hlf1.
      assert (RP : s_pc SSr = 0xf09a8) by (vm_compute; reflexivity).
      assert (RL : s_log SSr = VC1_LOGA) by (vm_compute; reflexivity).
      rewrite RP in VIS1. rewrite RL in VIS1, MI1, Hlf1.
      destruct (vc1_after1 w s LB LBs m mo mo1 c ins tbl ftbl TB spal R Xs OK X Hk Hfk MP1 Hlf1 MI1) as (X1 & FK1).
      eapply (vc1_tail w s LB LBs _ mo1 c ins tbl ftbl TB spal msF1 R1 F fc Q OK X1 KR1 VIS1 RF1 Hc Hk Hknn Hfc Hfk HT1').
      intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KP2 RT2 FK2.
      apply (K msF2 mo2 m2 R2 KR2 VIS2 RF2 X2).
      + intros r Hr. rewrite (KP2 r Hr).
        apply (vc1_keep w Xs R R1 RT_VC1 _ r HT1 ltac:(vm_compute; reflexivity) HR1).
        unfold VC1_KEPT in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr.
      + exact RT2.
      + exact (ffkeep_trans w _ _ _ FK1 FK2).
    - assert (LP : 0 < n) by lia.
      pose proof Hb as Hb0. destruct Hb0 as [[B0 C0]|(Bpos & B16 & Cpos & Bhi & _)]; [exfalso; lia|].
      assert (B16' : 16 <= b) by (Z.div_mod_to_equations; lia).
      assert (KX : exists k, n = Z.of_nat (S k)).
      { exists (Z.to_nat (n - 1)). rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
      destruct KX as [k Hkx].
      pm_goR HHc1 OK X KR VIS RF HT1 Xs (PM_KN_FIX ++ KN_VC1) HKN 300%nat [0xf0998; 0xf09a8] [false] 44%N RT_VC1L.
      { split_scs. all: vc1_sc S41 S42 S43. }
      intros msF1 mo1 R1 KR1 MP1 VIS1 RF1 MI1 HT1' HR1 Hlf1.
      assert (RP : s_pc SSr = 0xf0998) by (vm_compute; reflexivity).
      assert (RL : s_log SSr = VC1_LOGA) by (vm_compute; reflexivity).
      rewrite RP in VIS1. rewrite RL in VIS1, MI1, Hlf1.
      destruct (vc1_after1 w s LB LBs m mo mo1 c ins tbl ftbl TB spal R Xs OK X Hk Hfk MP1 Hlf1 MI1) as (X1 & FK1).
      set (M1 := mem_denot (Eseed R (wenv_vals w ++ Xs)) m VC1_LOGA) in *.
      assert (G10 : PropExec.getr R1 10%bv = Z_to_bv 64 b) by rtf HT1'.
      assert (G13 : PropExec.getr R1 13%bv = Z_to_bv 64 (b + 20 * Z.of_nat (S k))) by (rewrite <- Hkx; rtf HT1').
      assert (G11 : PropExec.getr R1 11%bv = Z_to_bv 64 20) by rtf HT1'.
      destruct (vcl_loop1 F fc M1 b k R1 G10 G13 G11 ltac:(lia) ltac:(rewrite <- Hkx; lia)) as (R1' & MS1 & FR1 & G13').
      pose proof (msteps_full asegs _ _ MS1 RF1) as RF1'. cbn [ms_regs] in RF1'.
      eapply (sr_ms H HHc1 Q s msF1 mo1 _ _ KR1 VIS1 MS1).
      intros msF1' mo1' KR1' MP1' VIS1'.
      eapply (vc1_tail w s LB LBs M1 mo1' c ins tbl ftbl TB spal msF1' R1' F fc Q OK
                (pmxa_mpres H HHc1 LINV w s LB LBs M1 mo1 mo1' c ins (vc1_tbl1 tbl) ftbl TB spal X1 MP1')
                KR1' VIS1' RF1' Hc Hk Hknn Hfc Hfk).
      + unfold regs_tblX, RT_VC1X. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          (rewrite FR1 by (apply vc1_ne13; vm_compute; congruence)); rtf HT1'.
      + intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KP2 RT2 FK2.
        apply (K msF2 mo2 m2 R2 KR2 VIS2 RF2 X2).
        * intros r Hr. rewrite (KP2 r Hr), (FR1 r (vc1_kept13 r Hr)).
          apply (vc1_keep w Xs R R1 RT_VC1 _ r HT1 ltac:(vm_compute; reflexivity) HR1).
          unfold VC1_KEPT in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr.
        * exact RT2.
        * exact (ffkeep_trans w _ _ _ FK1 FK2).
  Qed.
End VC1.
