(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import StoreOk AgentLib AsanAcct BackingAlgebra AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanNodesMmLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB HS2Both B_MainFacts B_ImgZero5 B_MainCells5 B_MainInit5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require RunCeiling MState Mem Cells Step InitMem Arr Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Malloc_ifaceP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanFakeStack AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require BF_fakestack_rep BF_statics B_benv5 BDrv_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma both_ro_addr_range : forall x : word, Mem.ro_addr AImages.bsegs x = true -> 0x10000 <= bv_unsigned x < 0xa5000.
Proof.
  intros x H. unfold Mem.ro_addr in H.
  destruct (Z.lt_ge_cases (bv_unsigned x) 0x10000) as [L|G1].
  { rewrite AImageFacts.both_find_segment_none in H by lia. discriminate H. }
  destruct (Z.lt_ge_cases (bv_unsigned x) 0xa5000) as [L2|G2]; [lia|]. exfalso.
  unfold AImages.bsegs, AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments in H. cbn [find_segment] in H.
  replace (Z.of_N (seg_base AsanUbsan_segment_000)) with 0x10000%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_000)) with 0x21000%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_001)) with 0x31000%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_001)) with 0x74000%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_002)) with 0xa5000%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_002)) with 0x2000%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_003)) with 0xa7000%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_003)) with 0x55c000%Z in H by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x10000 + 0x21000)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 0x31000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x31000 + 0x74000)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 0xa5000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0xa5000 + 0x2000)); cbn [andb] in H; try lia.
  all: try (replace (seg_writable AsanUbsan_segment_002) with true in H by (vm_compute; reflexivity); discriminate H).
  all: destruct (Z.leb_spec0 0xa7000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0xa7000 + 0x55c000)); cbn [andb] in H; try lia.
  all: try (replace (seg_writable AsanUbsan_segment_003) with true in H by (vm_compute; reflexivity); discriminate H).
  all: discriminate H.
Qed.

(* [comment removed for export] *)
Definition e_stop : expr :=
  EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 10)) (EMd Instr.M_MUL (ELit 4096) (EVar 374))).
Definition e_sbot : expr := EAlu Instr.ALU_ADD e_stop (ELit (-8388608)).
Definition e_anchor : expr :=
  EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EMd Instr.M_MUL (ELit 4096) (EVar 10)))) (ELit (-160)).
(* [comment removed for export] *)
Definition e_ri : expr := EAlu Instr.ALU_ADD e_rib (ELit 137439019008).
(* [comment removed for export] *)
Definition e_stk : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 10))) (ELit (-8388608)).
Definition e_stklen : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-32768)) (EVar 0)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 10))) (ELit 140737496743936).
Definition e_stksh : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EVar 10)).
Definition e_stkshlen : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992).
(* [comment removed for export] *)
Definition VIS : list (expr * expr) :=
  [ (pgE 532, ELit 4096); (pgE 515, ELit 8388608); (pgE 514, ELit 1048576); (pgE 438, ELit 11571200); (pgE 340, ELit 4096);
    (pgE 275, ELit 4096); (pgE 246, ELit 65536); (pgE 245, ELit 4096); (e_ri, ELit 4096);
    (pgE 225, ELit 3727360); (pgE 95, ELit 65536); (ELit 65536, ELit 6238208); (e_stk, e_stklen) ].
Definition G1 : list (expr * expr) :=
  [ (pgE 341, ELit 4096); (pgE 455, ELit 4096); (EAlu Instr.ALU_ADD (pgE 456) (ELit 4096), ELit 4096); (pgE 457, ELit 4096);
    (pgE 455, ELit 4096); (EAlu Instr.ALU_ADD (pgE 456) (ELit 4096), ELit 4096); (pgE 457, ELit 4096) ].
Definition G0 : list (expr * expr) := firstn 4 G1 ++ (pgE 5, ELit 8192) :: skipn 4 G1.
#[local] Notation SOFF := 0x7fff8000.
Lemma range_false : forall lo hi x, hi <= x \/ x < lo -> ((lo <=? x) && (x <? hi))%bool = false.
Proof. intros lo hi x H. apply Bool.andb_false_iff. destruct (Z.le_gt_cases lo x); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. Qed.
Ltac dlia := first [lia | Z.div_mod_to_equations; lia].


(* [comment removed for export] *)
Definition val_at (off : Z) : expr :=
  match List.find (fun K => match K with KWord (SA b o) 8%nat _ => saddr_eqb (SA b o) (SA e_sp0 off) | _ => false end) (kn HS_s2_00)
  with Some (KWord _ _ v) => v | _ => ELit 0 end.
Definition V8 : expr := Eval vm_compute in val_at 8.
Definition V16 : expr := Eval vm_compute in val_at 16.
Lemma F8 : hs_fact (KWord (SA e_sp0 8) 8 V8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma F16 : hs_fact (KWord (SA e_sp0 16) 8 V16) = true. Proof. vm_compute. reflexivity. Qed.

Lemma bytes_at_memeq : forall m m' a bs, Mem.bytes_at BSEGS m a bs ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> m' x = m x) -> Mem.bytes_at BSEGS m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & HB) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold Mem.mrd. rewrite HE; [reflexivity|]. unfold Mem.wa. rewrite u64_lit; lia.
Qed.
Lemma firstn2_ptrs : forall base (l : list (list byte)), (1 <= length l)%nat ->
  Arr.u64s (firstn 2 (map (Z_to_bv 64) (InitMem.str_ptrs base l)))
  = (Mem.le8 (Z_to_bv 64 base) ++ (if (2 <=? length l)%nat then Mem.le8 (Z_to_bv 64 (base + Z.of_nat (length (nth 0 l [])) + 1)) ++ [] else []))%list.
Proof. intros base [|s0 [|s1 r]] Hl; cbn -[Mem.le8 Z.add Z.of_nat]; [cbn in Hl; lia| reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hr0_apps (sp : word) (E : env) : list (Z * Z) :=
  [ (pgv E 532, 4096); (pgv E 514, 1048576); (pgv E 438, 11571200); (pgv E 340, 4096); (pgv E 275, 4096); (pgv E 246, 65536);
    (pgv E 245, 4096); (pgv E 225, 3727360); (pgv E 95, 65536);
    (pgv E 341, 4096); (pgv E 455, 4096); (pgv E 456 + 4096, 4096); (pgv E 457, 4096); (pgv E 5, 8192) ].
Definition hr0_shs (sp : word) (E : env) : list (Z * Z) :=
  [ (pgv E 532, 4096); (pgv E 515, 8388608); (pgv E 514, 1048576); (pgv E 340, 4096); (pgv E 275, 4096); (pgv E 246, 65536);
    (pgv E 245, 4096); (pgv E 226 - pgv E 227 + 137439019008, 4096); (pgv E 225, 3727360); (pgv E 95, 65536);
    (pgv E 341, 4096); (pgv E 455, 4096); (pgv E 456 + 4096, 4096); (pgv E 457, 4096); (pgv E 5, 8192) ].
Definition appiv (bl : Z * Z) : Z * Z := (fst bl, fst bl + snd bl).
Definition shiv (bl : Z * Z) : Z * Z := (B_policy5.pgdn (B_bundle.sh (fst bl)), B_policy5.pgup (B_bundle.sh (fst bl + snd bl))).
Definition stack_slack (sp : word) : Z * Z :=
  let pusp := bv_unsigned sp - bv_unsigned sp mod 4096 in
  (B_policy5.pgdn (B_bundle.sh (pusp - 8388608)), B_policy5.pgdn (B_bundle.sh (pusp - 8388608)) + 4096).
Definition hr0_of (sp : word) (E : env) : list (Z * Z) := map appiv (hr0_apps sp E) ++ map shiv (hr0_shs sp E) ++ [stack_slack sp].

Lemma A0_pages_cons : forall iv L, B_policy5.A0_pages (iv :: L) = (snd iv - fst iv) / 4096 + 2 + B_policy5.A0_pages L.
Proof. intros iv L. reflexivity. Qed.
Lemma A0_pages_app : forall l1 l2, B_policy5.A0_pages (l1 ++ l2) = B_policy5.A0_pages l1 + B_policy5.A0_pages l2.
Proof. induction l1 as [|iv l1 IH]; intros l2; [reflexivity|]. cbn [app]. rewrite !A0_pages_cons, IH. lia. Qed.
Lemma A0_pages_appiv : forall L, B_policy5.A0_pages (map appiv L) = fold_right (fun bl acc => snd bl / 4096 + 2 + acc) 0 L.
Proof. induction L as [|[b l] L IH]; [reflexivity|]. cbn [fold_right map fst snd]. rewrite A0_pages_cons, IH. cbn [appiv fst snd]. rewrite Z.add_simpl_l. reflexivity. Qed.
Lemma shiv_pages : forall b l, 0 <= l -> (B_policy5.pgup (B_bundle.sh (b + l)) - B_policy5.pgdn (B_bundle.sh b)) / 4096 <= l / 32768 + 3
  /\ B_policy5.pgdn (B_bundle.sh b) <= B_policy5.pgup (B_bundle.sh (b + l)).
Proof. intros b l Hl. unfold B_policy5.pgup, B_policy5.pgdn, B_bundle.sh. Z.div_mod_to_equations. nia. Qed.
Lemma A0_pages_shiv : forall L, Forall (fun bl => 0 <= snd bl) L -> B_policy5.A0_pages (map shiv L) <= fold_right (fun bl acc => snd bl / 32768 + 5 + acc) 0 L
  /\ Forall (fun iv => fst iv <= snd iv) (map shiv L).
Proof.
  induction L as [|[b l] L IH]; intros HF; [split; [apply Z.le_refl | constructor]|].
  apply Forall_cons_iff in HF as [H1 H2]. cbn [snd] in H1. destruct (IH H2) as [IH1 IH2]. destruct (shiv_pages b l H1) as [P1 P2].
  cbn [fold_right map fst snd]. rewrite A0_pages_cons. cbn [shiv fst snd]. split; [lia|]. constructor; [cbn [fst snd]; exact P2 | exact IH2].
Qed.

Lemma hr0_ok : forall sp E, Forall (fun iv => fst iv <= snd iv) (hr0_of sp E) /\ B_policy5.A0_pages (hr0_of sp E) <= 8192.
Proof.
  intros sp E. unfold hr0_of.
  destruct (A0_pages_shiv (hr0_shs sp E) ltac:(unfold hr0_shs; repeat constructor; cbn [snd]; lia)) as [S1 S2].
  split.
  - apply Forall_app. split; [| apply Forall_app; split; [exact S2|]].
    + unfold hr0_apps. cbn [map]. repeat (apply Forall_cons; [unfold appiv; cbn [fst snd]; lia|]). apply Forall_nil.
    + apply Forall_cons; [| apply Forall_nil]. unfold stack_slack. cbn [fst snd]. lia.
  - rewrite !A0_pages_app, A0_pages_appiv.
    match goal with |- ?a + (_ + ?c) <= _ => let va := eval vm_compute in a in change a with va;
      replace c with 3 by (unfold B_policy5.A0_pages, stack_slack; cbn [fold_right fst snd]; rewrite Z.add_simpl_l; reflexivity) end.
    match type of S1 with _ <= ?r => let vr := eval vm_compute in r in change r with vr in S1 end.
    lia.
Qed.

Section MainBridge.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok BSEGS BOTH5 AsanInit.LIMIT (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) fs E hs R FULL model.

  #[local] Notation E0m := (aenv_of hs E).
  #[local] Notation CXRW := (cxs_rw sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation CXS := (cxs_sound sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation PG := (pgv_range sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  #[local] Notation FACT := (B_MainFacts.fact_sound sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  #[local] Notation MR := (Mr BOTH5 (argH0 BPH sp rdraw argv envp uid hw) E hs model FULL).
  #[local] Notation MRSOME := (Mr_some0 sp rdraw hw argv envp uid E FULL model hs).
  #[local] Notation SX X := (X sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  Let usp := bv_unsigned sp.
  Let pusp := usp - usp mod 4096.

  Lemma u_pg' : forall v, pgv E v < 2 ^ 64 -> uE E (pgE v) = pgv E v.
  Proof. intros v Hv. exact (u_pg sp E v Hv). Qed.


  Lemma u_lit'' : forall z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
  Proof. intros z Hz. unfold uE. cbn [edenot]. apply u64_lit. lia. Qed.
  Lemma u_pg_off'' : forall v z, 0 <= z -> pgv E v + z < 2 ^ 64 -> uE E (EAlu Instr.ALU_ADD (pgE v) (ELit z)) = pgv E v + z.
  Proof. intros v z Hz Hv. exact (u_pg_off sp E v z Hz Hv). Qed.
  Lemma fact_sound1' : forall K, existsb (kentry_eqb K) (kn hs) = true -> kentry_ok BSEGS E MR K.
  Proof.
    intros K HK. apply existsb_exists' in HK as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
    exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K Hin).
  Qed.

  Lemma R226' : 4096 * 4295491576 <= pgv E 226 <= 4096 * 34326181871. Proof. exact (R226 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R227' : 4096 * 0 <= pgv E 227 <= 4096 * 15.                   Proof. exact (R227 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R245' : 4096 * 1 <= pgv E 245 <= 4096 * 34359736319.          Proof. exact (R245 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R244' : 4096 * 1539 <= pgv E 244 <= 4096 * 34359734272.       Proof. exact (R244 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R514' : 4096 * 1539 <= pgv E 514 <= 4096 * 34359736064.       Proof. exact (R514 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R515' : 4096 * 1539 <= pgv E 515 <= 4096 * 34359734272.       Proof. exact (R515 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.

  (* [comment removed for export] *)
  Lemma u_sb : uE E e_sb = pgv E 226 - pgv E 227 + 65536.
  Proof.
    pose proof R226' as R226. pose proof R227' as R227.
    unfold uE, e_sb. cbn [edenot]. rewrite !u_add64, !u_mul64, !u64_lit by lia.
    replace (bv_unsigned (Z_to_bv 64 (-4096))) with (2 ^ 64 - 4096) by (vm_compute; reflexivity).
    unfold pgv in *. pose proof (u64_range (ev E 226%nat)) as Ra. pose proof (u64_range (ev E 227%nat)) as Rb.
    set (u1 := bv_unsigned (ev E 226%nat)) in *. set (u2 := bv_unsigned (ev E 227%nat)) in *.
    rewrite <- (Z.add_mod (4096 * u1) ((2 ^ 64 - 4096) * u2) (2 ^ 64)) by lia.
    replace (4096 * u1 + (2 ^ 64 - 4096) * u2) with ((4096 * u1 - 4096 * u2) + u2 * 2 ^ 64) by lia.
    assert (M0 : 2 ^ 64 <> 0) by (cbv; discriminate).
    rewrite (Z.mod_add _ _ _ M0). rewrite (Z.mod_small (4096 * u1 - 4096 * u2) (2 ^ 64) ltac:(lia)).
    rewrite u64_lit by lia. apply Z.mod_small. lia.
  Qed.

  Lemma u_rib' : uE E e_rib = pgv E 226 - pgv E 227.
  Proof. exact (u_rib sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.

  Lemma u_ri' : uE E e_ri = pgv E 226 - pgv E 227 + 137439019008.
  Proof.
    pose proof R226' as R226. pose proof R227' as R227. pose proof u_rib' as U.
    unfold uE, e_ri in *. cbn [edenot]. rewrite u_add64, U, u64_lit by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_sp0_sum : bv_unsigned (edenot E e_sp0) = 32768 * bv_unsigned (ev E 0%nat) + 16 * bv_unsigned (ev E 6%nat) + 4096 * bv_unsigned (ev E 10%nat)
    /\ 4294901760 <= bv_unsigned (ev E 0%nat) <= 4294967295 /\ 0 <= bv_unsigned (ev E 6%nat) <= 255 /\ 0 <= bv_unsigned (ev E 10%nat) <= 7.
  Proof.
    pose proof (FACT (KRange (EVar 0) 4294901760 4294967295) ltac:(vm_compute; reflexivity)) as R0.
    pose proof (FACT (KRange (EVar 6) 0 255) ltac:(vm_compute; reflexivity)) as R6.
    pose proof (FACT (KRange (EVar 10) 0 7) ltac:(vm_compute; reflexivity)) as R10.
    cbn [kentry_ok edenot] in R0, R6, R10.
    split; [| lia].
    unfold e_sp0, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot. cbn [edenot].
    change (ev E V_S1) with (ev E 0%nat). change (ev E V_S2) with (ev E 6%nat). change (ev E V_PG) with (ev E 10%nat).
    rewrite !u_add64, !u_mul64, (u64_lit 32768), (u64_lit 16), (u64_lit 4096) by lia.
    rewrite (Z.mod_small (32768 * _)), (Z.mod_small (16 * _)), (Z.mod_small (4096 * _)) by lia.
    rewrite (Z.mod_small (32768 * _ + _)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pusp_sum' : pusp = 32768 * bv_unsigned (ev E 0%nat) + 4096 * bv_unsigned (ev E 10%nat) /\ 0x7fff80000000 <= pusp /\ pusp + 4096 <= 2 ^ 47.
  Proof.
    pose proof u_sp0_sum as (USP & R0 & R6 & R10). pose proof (uE_sp0 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC) as U.
    unfold uE in U. rewrite U in USP. pose proof (usp_lo sp Hsp). pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit). subst pusp usp. split; [| dlia].
    rewrite USP. replace (32768 * bv_unsigned (ev E 0%nat) + 16 * bv_unsigned (ev E 6%nat) + 4096 * bv_unsigned (ev E 10%nat))
      with (16 * bv_unsigned (ev E 6%nat) + (8 * bv_unsigned (ev E 0%nat) + bv_unsigned (ev E 10%nat)) * 4096) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma u_stk' : uE E e_stk = pusp - 8388608.
  Proof.
    pose proof pusp_sum' as (P & PL & PH). pose proof u_sp0_sum as (_ & R0 & _ & R10).
    set (z0 := bv_unsigned (ev E 0%nat)) in *. set (z10 := bv_unsigned (ev E 10%nat)) in *.
    unfold uE, e_stk. cbn [edenot]. rewrite !u_add64, !u_mul64, (u64_lit 32768), (u64_lit 4096) by lia. fold z0 z10.
    replace (bv_unsigned (Z_to_bv 64 (-8388608))) with (2 ^ 64 - 8388608) by (vm_compute; reflexivity).
    rewrite (Z.mod_small (32768 * z0)), (Z.mod_small (4096 * z10)), (Z.mod_small (32768 * z0 + _)) by lia.
    replace (32768 * z0 + 4096 * z10 + (2 ^ 64 - 8388608)) with ((32768 * z0 + 4096 * z10 - 8388608) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma u_stklen' : uE E e_stklen = 2 ^ 47 + 8388608 - pusp.
  Proof.
    pose proof pusp_sum' as (P & PL & PH). pose proof u_sp0_sum as (_ & R0 & _ & R10).
    set (z0 := bv_unsigned (ev E 0%nat)) in *. set (z10 := bv_unsigned (ev E 10%nat)) in *.
    unfold uE, e_stklen. cbn [edenot]. rewrite !u_add64, !u_mul64 by lia. fold z0 z10.
    replace (bv_unsigned (Z_to_bv 64 (-32768))) with (2 ^ 64 - 32768) by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 (-4096))) with (2 ^ 64 - 4096) by (vm_compute; reflexivity).
    rewrite (u64_lit 140737496743936) by lia.
    rewrite <- (Z.add_mod ((2 ^ 64 - 32768) * z0) ((2 ^ 64 - 4096) * z10) (2 ^ 64)) by lia.
    rewrite (Z.add_mod_idemp_l) by lia.
    replace ((2 ^ 64 - 32768) * z0 + (2 ^ 64 - 4096) * z10 + 140737496743936) with ((140737496743936 - 32768 * z0 - 4096 * z10) + (z0 + z10) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pg_word_bytes : forall v off (w : nat) val,
    hs_fact (KWord (SA (pgE v) off) w (ELit val)) = true ->
    A_IMG_HI <= pgv E v + off -> pgv E v < 2 ^ 47 -> pgv E v + off + Z.of_nat w <= 2 ^ 47 ->
    Mem.bytes_at AImages.bsegs FULL (pgv E v + off) (word_to_le_bytes w (Z_to_bv 64 val))
    /\ Mem.wr_at AImages.bsegs FULL (pgv E v + off) (Z.of_nat w).
  Proof.
    intros v off w val HK H1 H2 H3. pose proof (FACT _ HK) as (Hw & Hf & Hr). unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI in H1.
    pose proof (flat_u E _ _ Hf) as FU. unfold estart in FU. cbn [a_base a_off] in FU. pose proof (u_pg' v ltac:(lia)) as U. unfold uE in U. rewrite U in FU.
    assert (AD : adenot E (SA (pgE v) off) = Mem.wa (pgv E v + off)).
    { unfold Mem.wa. apply bv_eq. rewrite FU, u64_lit by lia. reflexivity. }
    rewrite AD in Hr. cbn [edenot] in Hr. rewrite LibBridge.rdn_lib in Hr.
    pose proof (CatExec.length_N_to_le_bytes w (Z_to_bv 64 val)) as LEN.
    pose proof (LibBridge.rdn_bytes_at MR (word_to_le_bytes w (Z_to_bv 64 val)) (pgv E v + off) ltac:(lia) ltac:(rewrite LEN; lia)) as BA.
    rewrite LEN in BA. specialize (BA Hr).
    pose proof (high_bytes_at sp rdraw hw argv envp uid E FULL model hs (pgv E v + off) _ ltac:(unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; lia) ltac:(rewrite LEN; lia) BA) as [X Y].
    rewrite LEN in Y. exact (conj X Y).
  Qed.

  (* [comment removed for export] *)
  Lemma pg_zero_bytes : forall v off n,
    hs_fact (KZero (SA (pgE v) off) (ELit n)) = true ->
    A_IMG_HI <= pgv E v + off -> pgv E v < 2 ^ 47 -> 0 <= n -> pgv E v + off + n <= 2 ^ 47 ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (pgv E v + off + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros v off n HK H1 H2 Hn H3 i Hi. pose proof (FACT _ HK) as [_ HZ]. unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI in H1.
    unfold estart, elenZ in HZ. cbn [a_base a_off edenot] in HZ.
    pose proof (u_pg' v ltac:(lia)) as U. unfold uE in U. change (edenot E (pgE v)) with (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar v))) in U.
    rewrite U, u64_lit in HZ by lia. apply MRSOME. apply HZ. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma high_rw_cells : forall A cs, A_IMG_HI <= A -> A + Z.of_nat (Cells.cells_size cs) <= 2 ^ 64 -> Cells.cells_wf cs ->
    (forall i, (i < length (Cells.cells_bytes cs))%nat -> FULL (Mem.wa (A + Z.of_nat i)) = nth_error (Cells.cells_bytes cs) i) ->
    Step.rw_cells AImages.bsegs FULL A cs.
  Proof.
    intros A cs HA HB Hwf HP. pose proof (Cells.cells_bytes_length cs Hwf) as LEN. unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI in HA.
    assert (SB : forall i, (i < length (Cells.cells_bytes cs))%nat -> exists b, FULL (Mem.wa (A + Z.of_nat i)) = Some b /\ nth_error (Cells.cells_bytes cs) i = Some b).
    { intros i Hi. destruct (nth_error (Cells.cells_bytes cs) i) as [b|] eqn:Hn; [exists b; split; [rewrite <- Hn; exact (HP i Hi) | reflexivity]|].
      exfalso. apply nth_error_None in Hn. lia. }
    split; [split; [exact Hwf|]|].
    - split; [lia|]. split; [lia|]. intros i Hi. destruct (SB i Hi) as (b & Hb & Hn). rewrite Hn. unfold Mem.mrd. rewrite Hb. reflexivity.
    - split; [lia|]. split; [lia|]. intros i Hi. destruct (SB (Z.to_nat i) ltac:(lia)) as (b & Hb & _). rewrite Z2Nat.id in Hb by lia.
      rewrite (AImageFacts.both_wview_overlay FULL) by (unfold Mem.wa; rewrite u64_lit by lia; lia). rewrite Hb. discriminate.
  Qed.

  Lemma high_stk : forall lo hi, A_IMG_HI <= lo -> hi <= 2 ^ 64 ->
    (forall a, lo <= a < hi -> exists b, FULL (Mem.wa a) = Some b) -> Frame.stk AImages.bsegs FULL lo hi.
  Proof.
    intros lo hi Hlo Hhi HP. unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI in Hlo. split; [lia|]. split; [lia|]. intros a Ha. destruct (HP a Ha) as [b Hb].
    rewrite (AImageFacts.both_wview_overlay FULL) by (unfold Mem.wa; rewrite u64_lit by lia; lia). unfold Mem.mrd. rewrite Hb.
    split; [discriminate | exists b; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma shadow_zero_pg : forall v l g,
    hs_fact (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar v)) 2147450880) (ELit (l / 8))) = true ->
    pgv E v < 2 ^ 47 -> l mod 8 = 0 -> 0 < l < 2 ^ 47 -> pgv E v <= 8 * g < pgv E v + l ->
    FULL (Z_to_bv 64 (2147450880 + g)) = Some (Z_to_bv 8 0).
  Proof.
    intros v l g HK Hv Hl Hl2 Hg. pose proof (FACT _ HK) as [_ HZ].
    unfold estart, elenZ in HZ. cbn [a_base a_off edenot] in HZ.
    pose proof (u64_range (ev E v)) as Rv. unfold pgv in *.
    assert (Hl8 : 0 <= g - 512 * bv_unsigned (ev E v) < l / 8) by (Z.div_mod_to_equations; lia).
    apply MRSOME. specialize (HZ (g - 512 * bv_unsigned (ev E v))).
    rewrite u_mul64, !u64_lit in HZ by (Z.div_mod_to_equations; lia). rewrite Z.mod_small in HZ by lia.
    replace (512 * bv_unsigned (ev E v) + 2147450880 + (g - 512 * bv_unsigned (ev E v))) with (2147450880 + g) in HZ by lia.
    apply HZ. exact Hl8.
  Qed.

  (* [comment removed for export] *)
  Context {RC__ : RunCeiling.RunCeiling}.
  Hypothesis RCSP : RunCeiling.rc_sp = usp.

  Lemma fs_sizes : AsanFakeStack.fs_nframes 0 = 16384 /\ AsanFakeStack.fs_nframes 1 = 8192 /\ AsanFakeStack.fs_frame_bytes 0 = 64 /\ AsanFakeStack.fs_frame_bytes 1 = 128.
  Proof. repeat split; reflexivity. Qed.

  Theorem init_fsrep : BF_fakestack_rep.FSRep AImages.bsegs E0m (fsbase_of E) AsanFakeStack.fsstate0 [] FULL.
  Proof.
    pose proof (SX R438) as R438. pose proof (SX Z438) as Z438. pose proof (S438 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) as S438.
    pose proof (ceil_eq sp rdraw brk0 argv envp uid Hsp Hva Hve Hfit RCSP) as CE.
    pose proof (pusp_le sp Hsp) as PU. pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH.
    pose proof (pg_zero_bytes 438 0 88 ltac:(vm_compute; reflexivity) ltac:(unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; lia) ltac:(subst pusp usp; lia) ltac:(lia) ltac:(subst pusp usp; lia)) as Z0.
    pose proof (pg_zero_bytes 438 96 11571104 ltac:(vm_compute; reflexivity) ltac:(unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; lia) ltac:(subst pusp usp; lia) ltac:(lia) ltac:(subst pusp usp; lia)) as Z96.
    pose proof (pg_word_bytes 438 88 8 20 ltac:(vm_compute; reflexivity) ltac:(unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; lia) ltac:(subst pusp usp; lia) ltac:(subst pusp usp; lia)) as [W88 W88w].
    assert (NF : forall cid, 0 <= cid <= 1 -> 0 < AsanFakeStack.fs_nframes cid <= 16384 /\ 64 <= AsanFakeStack.fs_frame_bytes cid <= 128
                 /\ AsanFakeStack.fs_frame_bytes cid * AsanFakeStack.fs_nframes cid = 1048576 /\ True).
    { pose proof fs_sizes as (S1 & S2 & S3 & S4). intros cid Hc. assert (cid = 0 \/ cid = 1) as [-> | ->] by lia; rewrite ?S1, ?S2, ?S3, ?S4; lia. }
    unfold BF_fakestack_rep.FSRep, fsbase_of. split; [unfold pgv; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity|].
    split; [lia|]. split; [unfold BF_fakestack_rep.kFsBytes; rewrite CE; subst pusp usp; lia|].
    split; [unfold BF_fakestack_rep.FS_SB, BF_fakestack_rep.kFsBytes; lia|].
    split. { (* [comment removed for export] *) intros cid Hc. exists (Z_to_bv 64 0). unfold BF_fakestack_rep.kFsClasses in Hc.
      apply high_rw_cells; [unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; lia | cbn; subst pusp usp; lia | cbn; exact (conj I I) |]. intros i Hi. cbn in Hi.
      cbn [Cells.cells_bytes Cells.cbytes app]. unfold Mem.wa.
      match goal with |- FULL (Z_to_bv 64 ?a) = _ => replace a with (pgv E 438 + 0 + (8 * cid + Z.of_nat i)) by lia end.
      rewrite (Z0 (8 * cid + Z.of_nat i)) by lia.
      do 8 (destruct i as [|i]; [reflexivity|]). cbn in Hi. lia. }
    split. { (* [comment removed for export] *) split; [split; [cbn; exact (conj I I)|]|]; cbn [Cells.cells_bytes Cells.cbytes Cells.cells_size app Z.of_nat Pos.of_succ_nat Pos.succ].
      - rewrite app_nil_r. exact W88. - exact W88w. }
    split. { (* [comment removed for export] *) apply high_rw_cells; [unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; lia | cbn; subst pusp usp; lia | cbn; exact (conj I I) |]. intros i Hi. cbn in Hi.
      destruct i as [|i]; [|lia]. cbn. unfold Mem.wa.
      match goal with |- FULL (Z_to_bv 64 ?a) = _ => replace a with (pgv E 438 + 96 + 0) by lia end. rewrite (Z96 0) by lia. reflexivity. }
    split. { (* [comment removed for export] *) intros cid pos [Hc Hp]. pose proof (NF cid Hc) as (N1 & N2 & N3 & N4).
      unfold AsanFakeStack.fs_flag_addr, AsanFakeStack.fs_flags_base, AsanFakeStack.fs_flags_off, AsanFakeStack.kFsFlagsOffset.
      assert (FO : 0 <= (if cid =? 0 then 0 else AsanFakeStack.fs_nframes 0) <= 16384).
      { pose proof fs_sizes as (S1 & _). rewrite S1. destruct (cid =? 0); lia. }
      apply high_rw_cells; [unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; lia | cbn; subst pusp usp; lia | cbn; exact (conj I I) |]. intros i Hi. cbn in Hi. destruct i as [|i]; [|lia].
      unfold BF_fakestack_rep.flag_byte, BF_fakestack_rep.lf_mem. cbn. unfold Mem.wa.
      match goal with |- FULL (Z_to_bv 64 ?a) = _ => replace a with (pgv E 438 + 96 + (a - pgv E 438 - 96)) by lia end.
      rewrite Z96 by lia. reflexivity. }
    split. { (* [comment removed for export] *) intros cid pos [Hc Hp]. pose proof (NF cid Hc) as (N1 & N2 & N3 & N4).
      unfold AsanFakeStack.fs_frame_addr, AsanFakeStack.fs_frames_base, AsanFakeStack.kFsFlagsOffset, BF_fakestack_rep.fs_shadow, BF_fakestack_rep.FS_SB.
      change (2 ^ (AsanFakeStack.kFsLog + 1 - AsanFakeStack.kFsMinFrameLog)) with 32768. change (2 ^ AsanFakeStack.kFsLog) with 1048576.
      assert (FR : 36864 <= 4096 + 32768 + cid * 1048576 + AsanFakeStack.fs_frame_bytes cid * pos
                   /\ 4096 + 32768 + cid * 1048576 + AsanFakeStack.fs_frame_bytes cid * pos + AsanFakeStack.fs_frame_bytes cid <= 11571200) by nia.
      split.
      - apply high_stk; [unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; lia | subst pusp usp; lia |]. intros a Ha. exists (Z_to_bv 8 0). unfold Mem.wa.
        replace a with (pgv E 438 + 96 + (a - pgv E 438 - 96)) by lia. apply Z96. lia.
      - apply high_stk; [unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; clear - FR R438 Z438 N2; Z.div_mod_to_equations; lia | clear - FR R438 S438 PU UH N2; Z.div_mod_to_equations; lia |].
        intros a Ha. exists (Z_to_bv 8 0). unfold Mem.wa.
        (* [comment removed for export] *)
        assert (HX : exists g, pgv E 438 <= 8 * g < pgv E 438 + 11571200 /\ a = 2147450880 + g).
        { exists (a - 2147450880). unfold pgv in *. clear - Ha FR N2 R438. Z.div_mod_to_equations. nia. }
        destruct HX as (g & Hg & ->).
        apply (shadow_zero_pg 438 11571200); [vm_compute; reflexivity | lia | reflexivity | lia | exact Hg]. }
    split; [constructor|]. intros N ff [].
  Qed.

  (* [comment removed for export] *)
  #[local] Ltac fin X := first [ exact X
    | lazymatch goal with |- Step.rw_cells _ _ ?A _ => lazymatch type of X with Step.rw_cells _ _ ?B _ =>
        replace A with B by (lazy -[pgv Z.add Z.mul Z.sub Z.opp Z.pow]; lia); exact X end end ].
  #[local] Ltac cx be a l := let X := fresh in
    pose proof (CXRW be a l ltac:(vm_compute; reflexivity) eq_refl) as X; cbn [map cx_cell xv_den length] in X;
    rewrite ?u_abs in X; rewrite ?(edenot_pg sp E) in X by lia;
    repeat match goal with U : uE E (pgE _) = _ |- _ => rewrite U in X end; fin X.

  (* [comment removed for export] *)
  Theorem init_athr5 : Step.rw_cells AImages.bsegs FULL (AsanState.ae_thread E0m) [Cells.C8 (Z_to_bv 64 (BF_fakestack_rep.fp_ctx (plumb_of E)))]
    /\ Step.rw_cells AImages.bsegs FULL (BF_fakestack_rep.fp_ctx (plumb_of E) + 8) [Cells.C4 (Z_to_bv 64 0)].
  Proof.
    pose proof (SX R245) as R245. pose proof (SX R246) as R246.
    assert (U245 : uE E (pgE 245) = pgv E 245) by (apply u_pg'; lia). assert (U246 : uE E (pgE 246) = pgv E 246) by (apply u_pg'; lia).
    change (AsanState.ae_thread E0m) with (pgv E 245). change (BF_fakestack_rep.fp_ctx (plumb_of E)) with (pgv E 246).
    split. { cx (pgE 245) 0 [CX8 (XS (pgE 246))]. } cx (pgE 246) 8 [CX4 0].
  Qed.

  (* [comment removed for export] *)
  Lemma ams_c1 : Step.rw_cells AImages.bsegs FULL 0xa61f8 [Cells.C8 (Z_to_bv 64 0x10)].                           Proof. cx (ELit 0) 0xa61f8 [CX8 (XL 0x10)]. Qed.
  Lemma ams_c2 : Step.rw_cells AImages.bsegs FULL 0x5e1560 [Cells.C4 (Z_to_bv 64 0)].                             Proof. cx (ELit 0) 0x5e1560 [CX4 0]. Qed.
  Lemma ams_c3 : Step.rw_cells AImages.bsegs FULL 0x130822 [Cells.C1 (Z_to_bv 8 0)].                              Proof. cx (ELit 0) 0x130822 [CX1 0]. Qed.
  Lemma ams_c4 : Step.rw_cells AImages.bsegs FULL 0xa55e0 [Cells.C8 (Z_to_bv 64 1); Cells.C8 (Z_to_bv 64 0x1400dc)]. Proof. cx (ELit 0) 0xa55e0 [CX8 (XL 1); CX8 (XL 0x1400dc)]. Qed.
  Lemma ams_c5 : Step.rw_cells AImages.bsegs FULL 0x140178 [Cells.C8 (Z_to_bv 64 0)].                             Proof. cx (ELit 0) 0x140178 [CX8 (XL 0)]. Qed.
  Lemma ams_c6 : Step.rw_cells AImages.bsegs FULL 0x1401ec [Cells.C1 (Z_to_bv 8 0)].                              Proof. cx (ELit 0) 0x1401ec [CX1 0]. Qed.
  Lemma ams_c7 : Step.rw_cells AImages.bsegs FULL 0x1401d8 [Cells.C4 (Z_to_bv 64 0)].                             Proof. cx (ELit 0) 0x1401d8 [CX4 0]. Qed.
  Lemma ams_c8 : Step.rw_cells AImages.bsegs FULL 0x601810 [Cells.C8 (Z_to_bv 64 4096)].                          Proof. cx (ELit 0) 0x601810 [CX8 (XL 4096)]. Qed.
  Lemma ams_c9 : Step.rw_cells AImages.bsegs FULL 0x1401dc [Cells.C1 (Z_to_bv 8 1)].                              Proof. cx (ELit 0) 0x1401dc [CX1 1]. Qed.
  Lemma ams_c10 : Step.rw_cells AImages.bsegs FULL 0xa55c8 [Cells.C8 (Z_to_bv 64 0xa7400)].                       Proof. cx (ELit 0) 0xa55c8 [CX8 (XL 0xa7400)]. Qed.
  Lemma ams_c11 : Step.rw_cells AImages.bsegs FULL 0xa5588 [Cells.C8 (Z_to_bv 64 0xa7440)].                       Proof. cx (ELit 0) 0xa5588 [CX8 (XL 0xa7440)]. Qed.
  Lemma ams_c12 : Step.rw_cells AImages.bsegs FULL 0xa7440 [Cells.C8 (Z_to_bv 64 0x193ca)].                       Proof. cx (ELit 0) 0xa7440 [CX8 (XL 0x193ca)]. Qed.
  Lemma ams_c13 : Step.rw_cells AImages.bsegs FULL 0xa6228 [Cells.C8 (Z_to_bv 64 0x601590)].                      Proof. cx (ELit 0) 0xa6228 [CX8 (XL 0x601590)]. Qed.

  (* [comment removed for export] *)
  Lemma main_atx_table : Step.rw_cells AImages.bsegs FULL 0x6015a0
     [Cells.C1 (Z_to_bv 8 0); Cells.CB 3 (repeat (Z_to_bv 8 0) 3); Cells.C4 (Z_to_bv 64 0); Cells.C4 (Z_to_bv 64 1); Cells.CB 4 (repeat (Z_to_bv 8 0) 4);
      Cells.C8 (Z_to_bv 64 0x6015b8); Cells.C8 (Z_to_bv 64 0); Cells.C8 (Z_to_bv 64 0x928ac); Cells.C8 (Z_to_bv 64 0); Cells.CB 240 (repeat (Z_to_bv 8 0) 240);
      Cells.C8 (Z_to_bv 64 0x71310); Cells.C8 (Z_to_bv 64 0); Cells.CB 240 (repeat (Z_to_bv 8 0) 240)].
  Proof. cx (ELit 0) 0x6015a0 [CX1 0; CXZ 3; CX4 0; CX4 1; CXZ 4; CX8 (XL 0x6015b8); CX8 (XL 0); CX8 (XL 0x928ac); CX8 (XL 0); CXZ 240; CX8 (XL 0x71310); CX8 (XL 0); CXZ 240]. Qed.
  Lemma main_flag : Step.rw_cells AImages.bsegs FULL 0x5e0c14 [Cells.C1 (Z_to_bv 8 0)].
  Proof. cx (ELit 0) 0x5e0c14 [CX1 0]. Qed.

  (* [comment removed for export] *)
  Theorem main_astat : BDrv_ctx.ASTAT FULL.
  Proof.
    unfold BDrv_ctx.ASTAT. split; [| split].
    - cx (ELit 0) 0xa6200 [CX8 (XL 0xa5498); CX8 (XL 0)].
    - cx (ELit 0) 0xa5498 [CX8 (XL 0xa9c68)].
    - exists false, (repeat (Z_to_bv 8 0) 3), (repeat (Z_to_bv 8 0) 4), (repeat (Z_to_bv 8 0) 240), (repeat (Z_to_bv 8 0) 240).
      split; [exact main_atx_table|]. split; [cx (ELit 0) 0x5e0c10 [CX1 0] | exact main_flag].
  Qed.

  (* [comment removed for export] *)
  Lemma init_envdepot : AsanOps.zlen (AsanState.ae_keys0 E0m) <= 1000 /\ 0 <= AsanState.ae_frames0 E0m <= 4096.
  Proof.
    change (AsanState.ae_keys0 E0m) with (keys0_of hs). change (AsanState.ae_frames0 E0m) with (frames0_of hs).
    unfold keys0_of, frames0_of, AsanOps.zlen. destruct (rcase0 hs); cbn; lia.
  Qed.
  Lemma init_keys0 : List.NoDup (map AsanSizeClass.depot_hash (AsanState.ae_keys0 E0m)) /\ AsanOps.zlen (AsanState.ae_keys0 E0m) < AsanConsts.kDepotNodesPerBlock.
  Proof.
    change (AsanState.ae_keys0 E0m) with (keys0_of hs). unfold keys0_of, AsanOps.zlen, AsanConsts.kDepotNodesPerBlock.
    destruct (rcase0 hs); (split; [cbn [List.map]; apply List.NoDup_cons; [intros [] | apply List.NoDup_nil] | cbn; lia]).
  Qed.
  Lemma init_hstot : AsanGap.gw_sizes (segments_reserved BSEGS ++ l0_of E) <= 2 ^ 46 /\ (length (segments_reserved BSEGS ++ l0_of E) <= 256)%nat.
  Proof.
    rewrite res0_val. unfold l0_of, l0_head, l0_tail. cbn [app length AsanGap.gw_sizes fst snd].
    rewrite !u64_lit by lia. split; [lia | lia].
  Qed.
  Lemma init_eb0 : 0 <= A_EB0 <= 2 ^ 32.
  Proof. unfold A_EB0. lia. Qed.

  Lemma init_envok :
    AsanLayout.app_mem (AsanState.ae_store_blk E0m) (2 ^ 23) /\ AsanState.ae_store_blk E0m + 2 ^ 23 <= RunCeiling.alloc_ceiling
    /\ AsanLayout.app_mem (fsbase_of E) BF_fakestack_rep.kFsBytes /\ fsbase_of E + BF_fakestack_rep.kFsBytes <= RunCeiling.alloc_ceiling
    /\ AsanSizeClass.kHighMemBeg <= AsanState.ae_resv_beg E0m
    /\ (fsbase_of E + BF_fakestack_rep.kFsBytes <= AsanState.ae_store_blk E0m \/ AsanState.ae_store_blk E0m + 2 ^ 23 <= fsbase_of E)
    /\ In (fsbase_of E, BF_fakestack_rep.kFsBytes) (AsanState.ae_reserved E0m)
    /\ AsanState.ae_fs_beg E0m = fsbase_of E /\ AsanState.ae_fs_len E0m = BF_fakestack_rep.kFsBytes
    /\ fst (AsanState.ae_img E0m) = 0x10000 /\ 0x5f3000 <= snd (AsanState.ae_img E0m).
  Proof.
    pose proof (SX R515) as R515. pose proof (SX R438) as R438. pose proof (SX R226) as R226.
    pose proof (SX Z515) as Z515. pose proof (SX Z438) as Z438.
    pose proof (S515 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) as S515.
    pose proof (S438 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) as S438.
    pose proof (D438_515 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC) as D.
    pose proof (ceil_eq sp rdraw brk0 argv envp uid Hsp Hva Hve Hfit RCSP) as CE. pose proof (pusp_le sp Hsp) as PU.
    change (AsanState.ae_store_blk E0m) with (pgv E 515). change (AsanState.ae_resv_beg E0m) with (pgv E 226).
    change (AsanState.ae_fs_beg E0m) with (pgv E 438). change (AsanState.ae_fs_len E0m) with 11571200. change (AsanState.ae_img E0m) with A_IMG.
    change (AsanState.ae_reserved E0m) with (reserved_of E). unfold fsbase_of, BF_fakestack_rep.kFsBytes, AsanLayout.app_mem. rewrite CE.
    rewrite AsanLayout.kLowAppEnd_val, AsanSizeClass.kHighMemBeg_val. cbn [A_IMG fst snd].
    split; [clear - R515 Z515 S515 PU; lia|]. split; [clear - S515 PU; lia|].
    split; [clear - R438 Z438 S438 PU; lia|]. split; [clear - S438 PU; lia|].
    split; [clear - R226; lia|]. split; [clear - D; lia|].
    split; [unfold reserved_of; cbn [In]; do 2 right; left; reflexivity|].
    repeat split; reflexivity || lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem main_mem_inv : Mem.mem_inv AImages.bsegs FULL.
  Proof.
    intros a b Hab. destruct (Mem.ro_addr AImages.bsegs a) eqn:Hro; [| reflexivity]. exfalso.
    pose proof (both_ro_addr_range a Hro) as Ra.
    pose proof (B_MainFacts.hull_img sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC 65536 685128 ltac:(vm_compute; reflexivity)
                  ltac:(unfold B_MainFacts.A_IMG_LO; lia) ltac:(unfold B_MainFacts.A_IMG_HI, B_ImgZero5.A_IMG_HI; lia) (bv_unsigned a) ltac:(lia)) as Hn.
    rewrite Z_to_bv_bv_unsigned in Hn. congruence.
  Qed.

  (* [comment removed for export] *)
  Theorem main_stk : Frame.stk AImages.bsegs FULL (usp - 8388608) (usp + -48).
  Proof.
    pose proof (usp_lo sp Hsp) as UL. pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH.
    pose proof (FACT (KWr (SA e_sp0 (-8388608)) (ELit 8388608)) ltac:(vm_compute; reflexivity)) as [_ HW].
    unfold estart, elenZ in HW. cbn [a_base a_off] in HW. change (edenot E (ELit 8388608)) with (Z_to_bv 64 8388608) in HW.
    rewrite (edenot_sp0 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC) in HW. rewrite u64_lit in HW by lia.
    split; [subst usp; lia|]. split; [subst usp; lia|]. intros a Ha.
    specialize (HW (a - (usp - 8388608)) 1%nat ltac:(subst usp; lia) ltac:(subst usp; cbn; lia)).
    cbn [store_ok] in HW. replace (bv_unsigned sp + -8388608 + (a - (usp - 8388608))) with a in HW by (subst usp; lia).
    assert (OUT : bv_unsigned (Mem.wa a) + 1 <= 0x10000 \/ 0x603000 <= bv_unsigned (Mem.wa a)).
    { unfold Mem.wa. rewrite u64_lit by (subst usp; lia). right. subst usp; lia. }
    change (Z_to_bv 64 a) with (Mem.wa a) in HW. change BSEGS with AImages.bsegs in HW.
    rewrite (AImageFacts.both_wview_overlay MR (Mem.wa a) OUT) in HW.
    destruct (MR (Mem.wa a)) as [b|] eqn:Hm; [| discriminate HW].
    apply MRSOME in Hm. split.
    - rewrite (AImageFacts.both_wview_overlay FULL (Mem.wa a) OUT). rewrite Hm. discriminate.
    - exists b. unfold Mem.mrd. rewrite Hm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let bsb := build_stack_bytes BPH sp argv envp uid hw rdraw.
  Let m0 := PropExec.wrap_mem BPH sp argv envp uid hw rdraw.
  #[local] Notation E0a := (E0 BPH sp rdraw brk0 argv envp uid hw).

  (* [comment removed for export] *)
  Lemma hidden_init : forall a : word,
    usp + 8 * argc + 8 * envc + 184 <= bv_unsigned a < usp + Z.of_nat (length bsb) - 16 -> FULL a = m0 a.
  Proof.
    intros a Ha. apply (proj2 (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)).
    pose proof (W_range BPH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
    unfold argH0. apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; subst usp argc envc bsb; lia.
  Qed.

  Lemma Mr_stack_lo : forall a : word, usp <= bv_unsigned a < usp + 8 * argc + 16 -> MR a = FULL a.
  Proof.
    intros a Ha. unfold Mr, mrestrict, hid. pose proof (usp_lo sp Hsp) as UL.
    replace (argH0 BPH sp rdraw argv envp uid hw E a) with false.
    2: { symmetry. unfold argH0. pose proof (len_av BPH sp rdraw argv envp uid hw Hva). pose proof (len_ev BPH sp rdraw argv envp uid hw Hve).
         apply orb_false_intro; apply andb_false_iff; [left|left]; apply Z.leb_gt; subst usp argc envc; lia. }
    unfold vis. rewrite (ptop_eq sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC).
    replace (bv_unsigned sp - bv_unsigned sp mod 4096 - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; pose proof (Z.mod_pos_bound (bv_unsigned sp) 4096); subst usp; lia).
    rewrite orb_true_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma evE : bv_unsigned (ev E 0%nat) = usp / 32768 /\ bv_unsigned (ev E 6%nat) = (usp mod 4096) / 16 /\ bv_unsigned (ev E 1%nat) = argc
    /\ bv_unsigned (ev E 2%nat) = envc /\ bv_unsigned (ev E 3%nat) = Z.of_nat (length (nth 0 argv [])) /\ bv_unsigned (ev E 10%nat) = (usp mod 32768) / 4096.
  Proof.
    pose proof (uE0 BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (U1 & U2 & U3 & U4 & U5 & _ & _).
    pose proof (uE0_pg BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U10. unfold uE in *. cbn [edenot] in *.
    #[local] Ltac ei n := rewrite (ev_init sp rdraw brk0 hw argv envp fs uid E R FULL model hs HC n ltac:(unfold NX0; cbv; lia)).
    ei 0%nat. ei 6%nat. ei 1%nat. ei 2%nat. ei 3%nat. ei 10%nat.
    change V_S1 with 0%nat in U1. change V_S2 with 6%nat in U2. change V_ARGC with 1%nat in U3. change V_ENVC with 2%nat in U4. change V_L0 with 3%nat in U5. change V_PG with 10%nat in U10.
    subst usp argc envc. repeat split; assumption.
  Qed.

  Let str0 := usp + 8 * argc + 8 * envc + 184.
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  (* [comment removed for export] *)
  #[local] Ltac modflat := repeat match goal with |- context [?x mod 2 ^ 64] =>
    lazymatch x with context [_ mod 2 ^ 64] => fail | _ => rewrite (Z.mod_small x (2 ^ 64)) by lia end end.

  Lemma usp_split : usp = 32768 * (usp / 32768) + 4096 * ((usp mod 32768) / 4096) + 16 * ((usp mod 4096) / 16)
    /\ 0 <= usp / 32768 < 2 ^ 32 /\ 0 <= (usp mod 32768) / 4096 <= 7 /\ 0 <= (usp mod 4096) / 16 <= 255.
  Proof.
    pose proof (usp_lo sp Hsp) as UL. pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH. pose proof (usp_al sp Hsp) as AL.
    subst usp. generalize dependent (bv_unsigned sp). intros u UL UH AL. Z.div_mod_to_equations. lia.
  Qed.

  Lemma V8den : uE E V8 = str0.
  Proof.
    pose proof (len_av BPH sp rdraw argv envp uid hw Hva) as LA. pose proof (len_ev BPH sp rdraw argv envp uid hw Hve) as LE.
    pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH.
    pose proof evE as (U0 & U6 & U1 & U2 & U3 & U10). pose proof usp_split as (US & Q1 & Q2 & Q3).
    unfold uE. cbn [edenot V8]. rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U0, U6, U1, U2, U10.
    subst str0 usp argc envc. modflat. lia.
  Qed.

  Lemma V16den : 2 <= argc -> uE E V16 = str0 + L0 + 1.
  Proof.
    intros A2.
    pose proof (len_av BPH sp rdraw argv envp uid hw Hva) as LA. pose proof (len_ev BPH sp rdraw argv envp uid hw Hve) as LE.
    pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH.
    assert (HL0 : 0 <= L0 <= 131071).
    { subst L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; subst argc; lia)). lia. }
    pose proof evE as (U0 & U6 & U1 & U2 & U3 & U10). pose proof usp_split as (US & Q1 & Q2 & Q3).
    unfold uE. cbn [edenot V16]. rewrite !u_mul64, !u_sltu64, !u_add64, !u_mul64, !u64_lit by lia. rewrite U0, U6, U1, U2, U3, U10.
    subst str0 L0 usp argc envc. replace (1 <? Z.of_nat (length argv)) with true by (symmetry; apply Z.ltb_lt; lia).
    modflat. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma word8_at : forall off v, hs_fact (KWord (SA e_sp0 off) 8 v) = true -> 0 <= off -> off + 8 <= 8 * argc + 16 ->
    Mem.bytes_at BSEGS FULL (usp + off) (Mem.le8 (edenot E v)).
  Proof.
    intros off v HK H0 H1. pose proof (usp_lo sp Hsp) as UL. pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH.
    pose proof (len_av BPH sp rdraw argv envp uid hw Hva) as LA.
    pose proof (FACT _ HK) as (_ & _ & Hr).
    remember (edenot E v) as w eqn:Ew. clear Ew.
    unfold adenot in Hr. cbn [a_base a_off] in Hr. rewrite (edenot_sp0 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC) in Hr.
    unfold v_addi in Hr.
    rewrite (rdn_ext BSEGS 8 MR FULL) in Hr.
    2: { rewrite u64_lit; subst usp argc; lia. }
    2: { intros x Hx. rewrite u64_lit in Hx by (subst usp argc; lia). apply Mr_stack_lo. subst usp argc; lia. }
    rewrite LibBridge.rdn_lib in Hr.
    apply LibBridge.rdn_bytes_at; [subst usp; lia | rewrite Mem.length_le8; subst usp argc; lia |].
    rewrite Mem.length_le8. unfold Mem.wa. exact Hr.
  Qed.

  Lemma BPH_b_phdrs : AImages.b_phdrs = BPH. Proof. reflexivity. Qed.

  Theorem main_aimg : BDrv_ctx.AIMG sp argv envp uid hw rdraw FULL.
  Proof.
    unfold BDrv_ctx.AIMG. rewrite BPH_b_phdrs. fold bsb.
    pose proof (usp_lo sp Hsp) as UL. pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH. pose proof (usp_al sp Hsp) as AL.
    pose proof (len_av BPH sp rdraw argv envp uid hw Hva) as LA. pose proof (len_ev BPH sp rdraw argv envp uid hw Hve) as LE.
    pose proof (usp_fit BPH sp rdraw argv envp uid hw Hfit) as UF. pose proof (bsb_ge BPH sp rdraw argv envp uid hw) as [BG BM].
    pose proof (InitMem.build_stack_bytes_length BPH sp argv envp uid hw rdraw) as BL. pose proof (InitMem.raw_len_nonneg BPH sp argv envp uid hw rdraw) as RN.
    pose proof (InitMem.flatten_strings_length argv) as L1. pose proof (InitMem.flatten_strings_length envp) as L2.
    fold bsb in UF, BG, BM, BL.
    split.
    - (* [comment removed for export] *)
      unfold InitMem.argv_ptrs. rewrite firstn2_ptrs by lia.
      apply (proj2 (Mem.bytes_at_app BSEGS FULL _ _ _)). split.
      + pose proof (word8_at 8 V8 F8 ltac:(lia) ltac:(subst argc; lia)) as W8.
        replace (edenot E V8) with (Z_to_bv 64 (InitMem.str_base sp argv envp)) in W8; [exact W8|].
        rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E V8)). f_equal. change (bv_unsigned (edenot E V8)) with (uE E V8).
        rewrite V8den. unfold InitMem.str_base, InitMem.struct_size, InitMem.argc, InitMem.envc. subst str0 usp argc envc. lia.
      + rewrite Mem.length_le8. destruct (Nat.leb_spec0 2 (length argv)) as [A2|A2].
        * rewrite app_nil_r. pose proof (word8_at 16 V16 F16 ltac:(lia) ltac:(subst argc; lia)) as W16.
          replace (bv_unsigned sp + 8 + Z.of_nat 8) with (usp + 16) by (subst usp; lia).
          replace (edenot E V16) with (Z_to_bv 64 (InitMem.str_base sp argv envp + Z.of_nat (length (nth 0 argv [])) + 1)) in W16; [exact W16|].
          rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E V16)). f_equal. change (bv_unsigned (edenot E V16)) with (uE E V16).
          rewrite V16den by (subst argc; lia). unfold InitMem.str_base, InitMem.struct_size, InitMem.argc, InitMem.envc. subst str0 L0 usp argc envc. lia.
        * apply Mem.bytes_at_nil. subst usp; lia.
    - (* [comment removed for export] *)
      intros i s Hi Hn.
      destruct (InitMem.str_ptrs_nth argv (InitMem.str_base sp argv envp) i s Hn) as (off & Hp & Ho & Ht & Hf).
      set (p := InitMem.str_base sp argv envp + off).
      set (e := p + Z.of_nat (length s) + 1).
      set (k := (- e) mod 8).
      assert (HK : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
      assert (SB : InitMem.str_base sp argv envp = str0).
      { unfold InitMem.str_base, InitMem.struct_size, InitMem.argc, InitMem.envc. subst str0 usp argc envc. lia. }
      assert (TOP : e + k <= usp + Z.of_nat (length bsb) - 16).
      { subst k. apply BDrv_ctx.ceil8_le.
        - subst usp bsb argc envc. clear - AL BM BG. Z.div_mod_to_equations. lia.
        - subst e p. rewrite SB. subst str0 usp bsb argc envc. rewrite BL.
          pose proof (Z.mod_pos_bound (8 - InitMem.raw_len argv envp mod 8) 8 ltac:(lia)).
          unfold InitMem.raw_len, InitMem.pad_len, InitMem.struct_size, InitMem.argc, InitMem.envc in *. lia. }
      exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) bsb)).
      split; [unfold InitMem.argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
      assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) bsb)) = Z.to_nat k).
      { rewrite length_firstn, length_skipn. subst e p. subst bsb usp. lia. }
      rewrite LS. split; [subst k e p; subst bsb usp; lia|].
      split; [| split; [subst k e p; rewrite Z2Nat.id by lia; apply Z.le_refl | subst k e p; subst bsb usp; lia]].
      (* [comment removed for export] *)
      assert (IMG0 : Mem.bytes_at BSEGS m0 usp bsb).
      { apply InitMem.init_stack_bytes; subst usp bsb; [unfold stack_max_size; lia | lia]. }
      destruct (BDrv_ctx.stack_pieces sp argv envp uid hw rdraw m0 IMG0) as (_ & _ & _ & _ & B6 & _).
      pose proof (InitMem.bytes_at_slice BSEGS BPH sp argv envp uid hw rdraw m0 (InitMem.str_base sp argv envp) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
      rewrite Hf in BS. replace (InitMem.str_base sp argv envp + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
      pose proof (InitMem.bytes_at_slice BSEGS BPH sp argv envp uid hw rdraw m0 usp bsb (Z.to_nat (e - usp)) (Z.to_nat k) IMG0 ltac:(subst e p; subst bsb usp; lia)) as BK.
      replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e p; subst usp; lia).
      pose proof (proj2 (Mem.bytes_at_app BSEGS m0 p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB.
      (* [comment removed for export] *)
      apply (bytes_at_memeq m0 FULL _ _ BB). intros x Hx. apply hidden_init.
      rewrite length_app in Hx. cbn [length] in Hx. rewrite LS in Hx. fold str0. rewrite <- SB. subst e p k. subst usp bsb. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pgdn_eq : forall a, B_policy5.pgdn a = pagedown a.
  Proof. intros a. unfold B_policy5.pgdn, pagedown. pose proof (Z.div_mod a 4096 ltac:(lia)). lia. Qed.
  Lemma pgup_eq : forall a, B_policy5.pgup a = pageup a.
  Proof. intros a. unfold B_policy5.pgup. rewrite pgdn_eq. unfold pagedown, pageup. reflexivity. Qed.
  Lemma pagedown_al : forall a, a mod 4096 = 0 -> pagedown a = a.
  Proof. intros a Ha. unfold pagedown. Z.div_mod_to_equations. lia. Qed.
  Lemma pageup_al : forall a, a mod 4096 = 0 -> pageup a = a.
  Proof. intros a Ha. unfold pageup. Z.div_mod_to_equations. lia. Qed.
  Lemma pgv_al : forall v, pgv E v mod 4096 = 0.
  Proof. intros v. unfold pgv. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

  Lemma S0_list : B_bundle.S0_ivs5 E0m (fsbase_of E) =
    [ (0x7fff7000, 0x8fff7000);
      (B_policy5.pgdn (B_bundle.sh (pgv E 226 - pgv E 227 + 0x10000)), B_policy5.pgup (B_bundle.sh (pgv E 226 - pgv E 227 + 0x10000 + 2^37)));
      (B_policy5.pgdn (B_bundle.sh RunCeiling.alloc_ceiling), AsanSizeClass.kHighMemBeg);
      (B_policy5.pgdn (B_bundle.sh (pgv E 438)), B_policy5.pgup (B_bundle.sh (pgv E 438 + BF_fakestack_rep.kFsBytes)));
      (pgv E 515, pgv E 515 + 2^23);
      (pgv E 226 - pgv E 227 + 0x10000 + 2^37, pgv E 226 - pgv E 227 + 0x10000 + 2^37 + 4096) ].
  Proof. reflexivity. Qed.

  Lemma vis_ghost_val : (a_vis hs ++ a_ghost hs = VIS ++ G0 /\ existsb (kentry_eqb (KRange (EVar 5) 1539 524277)) (kn hs) = true) \/ a_vis hs ++ a_ghost hs = VIS ++ G1.
  Proof. pose proof Hhs as [-> | [-> | [-> | ->]]]; [left|left|right|right]; vm_compute; repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  #[local] Ltac inlist := first [left; reflexivity | right; inlist].
  (* [comment removed for export] *)
  #[local] Ltac by_app b l Hb1 Hb2 :=
    exists (b, b + l); split; [apply in_or_app; right; unfold hr0_of; apply in_or_app; left; change (b, b + l) with (appiv (b, l)); apply in_map; unfold hr0_apps; cbn [In]; inlist
                              | cbn [fst snd]; unfold pagedown, pageup in Hb1, Hb2; unfold pgv in *; clear - Hb1 Hb2; Z.div_mod_to_equations; lia].
  #[local] Ltac by_sh b l Hb1 Hb2 :=
    exists (B_policy5.pgdn (B_bundle.sh b), B_policy5.pgup (B_bundle.sh (b + l))); split;
      [ apply in_or_app; right; unfold hr0_of; apply in_or_app; right; apply in_or_app; left;
        change (B_policy5.pgdn (B_bundle.sh b), B_policy5.pgup (B_bundle.sh (b + l))) with (shiv (b, l)); apply in_map; unfold hr0_shs; cbn [In]; inlist
      | cbn [fst snd]; rewrite pgdn_eq, pgup_eq; unfold B_bundle.sh; rewrite B_bundle.A_SB_val; clear - Hb1 Hb2; lia ].
  Ltac lit_pages H :=
    repeat match type of H with
    | context [pagedown ?x] => lazymatch x with context [pgv] => fail | context [bv_unsigned] => fail | _ => let v := eval vm_compute in (pagedown x) in change (pagedown x) with v in H end
    | context [pageup ?x] => lazymatch x with context [pgv] => fail | context [bv_unsigned] => fail | _ => let v := eval vm_compute in (pageup x) in change (pageup x) with v in H end
    end.

  Theorem init_mat : Forall (fun w => bv_unsigned w mod 4096 = 0 /\ B_policy5.in_ivs_Z (B_bundle.S0_ivs5 E0m (fsbase_of E) ++ hr0_of sp E) (bv_unsigned w)) (m_vm_materialized model)
    /\ List.NoDup (m_vm_materialized model).
  Proof.
    destruct (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) as [N1 N2 N3 N4 N5]. split; [| exact N1].
    pose proof (SX R532) as R532. pose proof (SX R515) as R515. pose proof (SX R514) as R514. pose proof (SX R438) as R438. pose proof (SX R340) as R340.
    pose proof (SX R275) as R275. pose proof (SX R246) as R246. pose proof (SX R245) as R245. pose proof (SX R244) as R244. pose proof (SX R226) as R226.
    pose proof (SX R227) as R227. pose proof (SX R225) as R225. pose proof (SX R95) as R95.
    assert (R341 : 4096 * 1 <= pgv E 341 <= 4096 * 34359736319) by (apply PG; vm_compute; reflexivity).
    assert (R455 : 4096 * 1 <= pgv E 455 <= 4096 * 34359736319) by (apply PG; vm_compute; reflexivity).
    assert (R456 : 4096 * 1 <= pgv E 456 <= 4096 * 34359736319) by (apply PG; vm_compute; reflexivity).
    assert (R457 : 4096 * 1 <= pgv E 457 <= 4096 * 34359736319) by (apply PG; vm_compute; reflexivity).
    pose proof (S515 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) as S515.
    pose proof (S244 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) as S244.
    pose proof (S226 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) as S226.
    pose proof pusp_sum' as (PP & PL & PH).
    pose proof (ceil_eq sp rdraw brk0 argv envp uid Hsp Hva Hve Hfit RCSP) as CE. pose proof (pusp_le sp Hsp) as PU.
    pose proof u_ri' as URI. pose proof u_stk' as USTK. pose proof u_stklen' as USTKL.
    apply Forall_forall. intros p Hp.
    pose proof (N2 p Hp) as AL. change page_size with 4096 in AL.
    pose proof (N3 p Hp) as PA. unfold AsanAcct.page_allowedb in PA. apply existsb_exists in PA as (iv & Hiv & Hb).
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. change page_size with 4096 in Hb2.
    pose proof (N4 p Hp) as PL'. unfold page_in_ranges in PL'. apply existsb_exists in PL' as (liv & Hliv & Hlb).
    apply andb_prop in Hlb as [Hlb1 Hlb2]. apply Z.leb_le in Hlb1. apply Z.leb_le in Hlb2. change page_size with 4096 in Hlb2.
    pose proof (init_lazy_hull sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC liv Hliv) as [_ LZ].
    set (pp := bv_unsigned p) in *. split; [exact AL|].
    unfold allowA in Hiv. rewrite S0_list.
    (* [comment removed for export] *)
    assert (CASES : exists q, (In q VIS \/ In q G1 \/ (q = (pgE 5, ELit 8192) /\ 4096 * 1539 <= pgv E 5 <= 4096 * 524277)) /\ In iv (allow1 BOTH5 E q)).
    { apply in_flat_map in Hiv as (q & Hq & Hivq). exists q. split; [| exact Hivq].
      destruct vis_ghost_val as [[EQ H5] | EQ]; rewrite EQ in Hq; apply in_app_iff in Hq as [Hq|Hq]; [left; exact Hq | | left; exact Hq | right; left; exact Hq].
      unfold G0 in Hq. cbn [firstn skipn app G1] in Hq. cbn [In] in Hq.
      repeat match type of Hq with _ \/ _ => destruct Hq as [Hq|Hq] | False => destruct Hq end.
      all: first [ right; left; rewrite <- Hq; unfold G1; cbn [In]; inlist
                 | right; right; split; [symmetry; exact Hq|]; pose proof (fact_sound1' _ H5) as R5; cbn [kentry_ok edenot] in R5; unfold pgv; lia ]. }
    clear Hiv. destruct CASES as (q & Hq & Hivq).
    destruct Hq as [Hq | [Hq | [Eq5 R5]]].
    - (* [comment removed for export] *) unfold VIS in Hq. cbn [In] in Hq.
      repeat (destruct Hq as [<- | Hq]); try contradiction;
        destruct Hivq as [<- | [<- | []]]; cbn [fst snd] in Hb1, Hb2; unfold sh_lo, sh_hi in *; cbn [fst snd] in Hb1, Hb2;
        change (shadow_off BOTH5) with 0x7fff8000 in *;
        rewrite ?URI, ?USTK, ?USTKL in Hb1; rewrite ?URI, ?USTK, ?USTKL in Hb2;
        rewrite ?u_pg' in Hb1 by lia; rewrite ?u_pg' in Hb2 by lia; rewrite ?u_lit'' in Hb1 by lia; rewrite ?u_lit'' in Hb2 by lia.
      + by_app (pgv E 532) 4096 Hb1 Hb2.
      + by_sh (pgv E 532) 4096 Hb1 Hb2.
      + (* [comment removed for export] *) exists (pgv E 515, pgv E 515 + 2 ^ 23). split; [apply in_or_app; left; cbn [In]; inlist|]. cbn [fst snd].
        unfold pagedown, pageup in Hb1, Hb2. unfold pgv in *. clear - Hb1 Hb2. Z.div_mod_to_equations. lia.
      + by_sh (pgv E 515) 8388608 Hb1 Hb2.
      + by_app (pgv E 514) 1048576 Hb1 Hb2.
      + by_sh (pgv E 514) 1048576 Hb1 Hb2.
      + by_app (pgv E 438) 11571200 Hb1 Hb2.
      + (* [comment removed for export] *) exists (B_policy5.pgdn (B_bundle.sh (pgv E 438)), B_policy5.pgup (B_bundle.sh (pgv E 438 + BF_fakestack_rep.kFsBytes))).
        split; [apply in_or_app; left; cbn [In]; inlist|]. cbn [fst snd]. rewrite pgdn_eq, pgup_eq. unfold B_bundle.sh, BF_fakestack_rep.kFsBytes. rewrite B_bundle.A_SB_val. clear - Hb1 Hb2; lia.
      + by_app (pgv E 340) 4096 Hb1 Hb2.
      + by_sh (pgv E 340) 4096 Hb1 Hb2.
      + by_app (pgv E 275) 4096 Hb1 Hb2.
      + by_sh (pgv E 275) 4096 Hb1 Hb2.
      + by_app (pgv E 246) 65536 Hb1 Hb2.
      + by_sh (pgv E 246) 65536 Hb1 Hb2.
      + by_app (pgv E 245) 4096 Hb1 Hb2.
      + by_sh (pgv E 245) 4096 Hb1 Hb2.
      + (* [comment removed for export] *) exists (pgv E 226 - pgv E 227 + 0x10000 + 2 ^ 37, pgv E 226 - pgv E 227 + 0x10000 + 2 ^ 37 + 4096).
        split; [apply in_or_app; left; cbn [In]; inlist|]. cbn [fst snd]. change (2 ^ 37) with 137438953472. clear - Hb1 Hb2 R226 R227.
        unfold pagedown, pageup in Hb1, Hb2. unfold pgv in *. Z.div_mod_to_equations. lia.
      + by_sh (pgv E 226 - pgv E 227 + 137439019008) 4096 Hb1 Hb2.
      + by_app (pgv E 225) 3727360 Hb1 Hb2.
      + by_sh (pgv E 225) 3727360 Hb1 Hb2.
      + by_app (pgv E 95) 65536 Hb1 Hb2.
      + by_sh (pgv E 95) 65536 Hb1 Hb2.
      + (* [comment removed for export] *) exfalso. lit_pages Hb1. lit_pages Hb2. clear - Hb1 Hb2 Hlb1 Hlb2 LZ R515 R244 R226. lia.
      + (* [comment removed for export] *) exists (0x7fff7000, 0x8fff7000). split; [apply in_or_app; left; cbn [In]; inlist|]. cbn [fst snd].
        lit_pages Hb1. lit_pages Hb2. clear - Hb1 Hb2; lia.
      + (* [comment removed for export] *) exfalso. change (2 ^ 47) with 140737488355328 in Hb2. unfold pagedown, pageup in Hb1, Hb2. clear - Hb1 Hb2 Hlb1 Hlb2 LZ S515 S244 S226 PL PH PP. subst pusp usp.
        Z.div_mod_to_equations. lia.
      + (* [comment removed for export] *)
        change (2 ^ 47) with 140737488355328 in Hb2. replace (pusp - 8388608 + (140737488355328 + 8388608 - pusp)) with 140737488355328 in Hb2 by lia. lit_pages Hb2.
        rewrite CE. destruct (Z.le_gt_cases (B_policy5.pgdn (B_bundle.sh (usp - 8388608))) pp) as [GE | LT].
        * exists (B_policy5.pgdn (B_bundle.sh (usp - 8388608)), AsanSizeClass.kHighMemBeg). split; [apply in_or_app; left; cbn [In]; inlist|]. cbn [fst snd].
          rewrite AsanSizeClass.kHighMemBeg_val. clear - GE Hb2. lia.
        * exists (stack_slack sp). split; [apply in_or_app; right; unfold hr0_of; apply in_or_app; right; apply in_or_app; right; left; reflexivity|].
          unfold stack_slack. cbn [fst snd]. clear - LT Hb1 AL PL PH PP PU. subst pusp usp.
          unfold B_policy5.pgdn, B_bundle.sh, pagedown in *. rewrite B_bundle.A_SB_val in *. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *) unfold G1 in Hq. cbn [In] in Hq.
      repeat (destruct Hq as [<- | Hq]); try contradiction;
        destruct Hivq as [<- | [<- | []]]; cbn [fst snd] in Hb1, Hb2; unfold sh_lo, sh_hi in *; cbn [fst snd] in Hb1, Hb2;
        change (shadow_off BOTH5) with 0x7fff8000 in *;
        rewrite ?u_pg_off'' in Hb1 by lia; rewrite ?u_pg_off'' in Hb2 by lia; rewrite ?u_pg' in Hb1 by lia; rewrite ?u_pg' in Hb2 by lia; rewrite ?u_lit'' in Hb1 by lia; rewrite ?u_lit'' in Hb2 by lia.
      + by_app (pgv E 341) 4096 Hb1 Hb2. + by_sh (pgv E 341) 4096 Hb1 Hb2.
      + by_app (pgv E 455) 4096 Hb1 Hb2. + by_sh (pgv E 455) 4096 Hb1 Hb2.
      + by_app (pgv E 456 + 4096) 4096 Hb1 Hb2. + by_sh (pgv E 456 + 4096) 4096 Hb1 Hb2.
      + by_app (pgv E 457) 4096 Hb1 Hb2. + by_sh (pgv E 457) 4096 Hb1 Hb2.
      + by_app (pgv E 455) 4096 Hb1 Hb2. + by_sh (pgv E 455) 4096 Hb1 Hb2.
      + by_app (pgv E 456 + 4096) 4096 Hb1 Hb2. + by_sh (pgv E 456 + 4096) 4096 Hb1 Hb2.
      + by_app (pgv E 457) 4096 Hb1 Hb2. + by_sh (pgv E 457) 4096 Hb1 Hb2.
    - (* [comment removed for export] *) subst q.
      assert (U5 : uE E (pgE 5) = pgv E 5) by (apply u_pg'; lia).
      destruct Hivq as [<- | [<- | []]]; cbn [fst snd] in Hb1, Hb2; unfold sh_lo, sh_hi in *; cbn [fst snd] in Hb1, Hb2;
        change (shadow_off BOTH5) with 0x7fff8000 in *; rewrite ?U5 in Hb1; rewrite ?U5 in Hb2; rewrite ?u_lit'' in Hb1 by lia; rewrite ?u_lit'' in Hb2 by lia.
      + by_app (pgv E 5) 8192 Hb1 Hb2. + by_sh (pgv E 5) 8192 Hb1 Hb2.
  Qed.

  (* [comment removed for export] *)
  Theorem init_fsenv : BF_fakestack_rep.FSEnv AImages.bsegs E0m (fsbase_of E) (plumb_of E) FULL.
  Proof.
    pose proof (SX R245) as R245. pose proof (SX R246) as R246. pose proof (SX R340) as R340. pose proof (SX R438) as R438.
    pose proof (S245 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) as S245.
    pose proof (S246 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) as S246.
    pose proof (S340 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) as S340.
    pose proof (ceil_eq sp rdraw brk0 argv envp uid Hsp Hva Hve Hfit RCSP) as CE. pose proof (pusp_le sp Hsp) as PU.
    assert (U245 : uE E (pgE 245) = pgv E 245) by (apply u_pg'; lia). assert (U246 : uE E (pgE 246) = pgv E 246) by (apply u_pg'; lia).
    assert (U340 : uE E (pgE 340) = pgv E 340) by (apply u_pg'; lia).
    unfold BF_fakestack_rep.FSEnv.
    change (AsanState.ae_thread E0m) with (pgv E 245). change (BF_fakestack_rep.fp_ctx (plumb_of E)) with (pgv E 246).
    change (BF_fakestack_rep.fp_dtls (plumb_of E)) with (pgv E 340). change (BF_fakestack_rep.fp_dtv1 (plumb_of E)) with 0x5e1550.
    change (BF_fakestack_rep.fp_tlsb (plumb_of E)) with 0x5e1c88. change (BF_fakestack_rep.fp_tlse (plumb_of E)) with 0x5e1d64.
    unfold fsbase_of, BF_fakestack_rep.FS_TP, BF_fakestack_rep.FS_CF, BF_fakestack_rep.FS_VB, BF_fakestack_rep.FS_DTO. cbn beta.
    split. { cx (ELit 0) 0xa6280 [CX8 (XL 1); CX8 (XL 0xfffffffffffff800)]. }
    split. { cx (ELit 0) 0xa7340 [CX8 (XL 0x9f4c0)]. }
    split. { cx (ELit 0) 0xaf298 [CX1 1]. }
    split. { cx (ELit 0) 0x5e1548 [CX8 (XL 0x5e1570)]. }
    split. { cx (ELit 0) 0x5e1578 [CX8 (XL 0x5e1d50)]. }
    split. { cx (ELit 0) 0x5e1550 [CX8 (XS (pgE 438))]. }
    split. { cx (ELit 0) 0xade20 [CX1 1]. }
    split. { cx (ELit 0) 0xade24 [CX4 0]. }
    split. { cx (ELit 0) 0x5e14f8 [CX8 (XL 0x6028f8)]. }
    split. { cx (ELit 0) 0x6028f8 [CX8 (XS (pgE 246))]. }
    split. { cx (pgE 246) 152 [CX8 (XS (pgE 245))]. }
    split. { cx (pgE 245) 48 [CX8 (XL 0x5e1c88); CX8 (XL 0x5e1d64)]. }
    split. { exists 0x1400e8, 0x13e058, 8.
             split; [cx (ELit 0) 0xa5590 [CX8 (XL 0x1400e8)]|]. split; [cx (ELit 0) (0x1400e8 + 137) [CX1 1]|].
             split; [cx (ELit 0) 0xa55f0 [CX8 (XL 0x13e058)]|]. split; [cx (ELit 0) 0x13e058 [CX4 0]|].
             split; [cx (ELit 0) 0xa6290 [CX8 (XL 8)]|]. split; [cx (ELit 0) (8 + 0x5e1550) [CX8 (XS (pgE 340))]|]. lia. }
    split. { cx (pgE 340) 24 [CX8 (XL 0x5e1550)]. }
    split; [lia|]. split; [lia|]. rewrite CE.
    split; [lia|]. split; [clear - S340 PU; lia|]. split; [unfold pgv; clear; Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [clear - S246 PU; lia|]. split; [unfold pgv; clear; Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [clear - S245 PU; lia|]. split; [unfold pgv; clear; Z.div_mod_to_equations; lia|].
    split. { cx (ELit 0) 0xa55a0 [CX8 (XL 0xae5b8)]. } cx (ELit 0) 0xae5b8 [CX8 (XL 0x7fff8000)].
  Qed.

  (* [comment removed for export] *)
  Theorem init_amalloc_statics : BF_statics.amalloc_statics FULL.
  Proof.
    unfold BF_statics.amalloc_statics.
    exact (conj ams_c1 (conj ams_c2 (conj ams_c3 (conj ams_c4 (conj ams_c5 (conj ams_c6 (conj ams_c7 (conj ams_c8 (conj ams_c9 (conj ams_c10 (conj ams_c11 (conj ams_c12 ams_c13)))))))))))).
  Qed.
End MainBridge.
