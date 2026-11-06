(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "valuation"; "sobj"; "cell"; "sprop"; "SLit"; "holds"; "ss_facts"; "SVar"; "ob_dflt"; "obj_holds"; "obj_range"; "odefault"; "ss_next"; "DUnknown"; "mkObj"; "ob_hi"; "ob_lo"; "sv_eqb"; "cell_holds"; "eval"; "ob_base"; "ob_cells"; "obj_wf"; "ss_objs"; "SMd"; "c_off"; "c_val"; "c_width"; "covered"; "mem_match"; "mkCell"; "rd_bytes"; "rw"; "smatch"; "DArr"; "oaddr"; "obj_hi_of"; "obj_lo_of"; "rd"; "sprop_below"; "ss_lenient"; "sv_below"; "tfact"; "@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "option"; "false"; "true"; "app"; "nat"; "Some"; "cons"; "andb"; "nil"; "fst"; "pair"; "S"; "None"; "snd"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "not"; "or"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JG"; "edesc"; "T_ok"; "tnz"; "tvd"; "tvv"; "T0"; "ed_state"; "tv_below"; "tv_facts"; "tv_sub_eqb"; "eecheckJ"; "ejcert"; "emeas"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "triple"; "etriple"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.X"; "emeasZ"; "entE_check"; "norm_xu"; "nz_entry_check"; "nz_entry"; "cont_check"; "nz_facts"; "contEJ_check"; "nz_contra_check"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "In"; "existsb"; "flat_map"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "map"; "skipn"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "add"; "leb"; "eqb"; "ltb"; "sub"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "edge"; "infer_sub"; "leaves_edges"; "add_facts"; "cuts_edges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.R.Narrow"; "narrow8to4"; "narrow_obj"; "narrow_at"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "uleq"; "leaf"; "set_objs"; "sitv"; "sym_run"; "same_atoms"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "obj_merge_arr"; "merge_arr_at"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "sv_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.R"; "is_lit0"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.PerCut"; "ejcut";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx.X.TRX"; "contE_check"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundW SymSoundR SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjUnbase ObjXform TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section X.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S30S5cA1S5dOF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).

Lemma tvd_forall : ltac2:(tb__ "0|3|
S4S30S31S2S2A2M0A1S47S4cR2R1A2S36S36G0G0S99R4R3A2S41S32G0A1M1S67G0R6R5A3S37G0R3A2M2A3S41G1S67G0R7R5A3G2A3S4bR9R5A2S4bRaR5A2S45S41S31S0S0A2S4dRbR7A2S4dRbR6A2A3A1F_;F_;F_;F_;F_;Ft';Ft;Fj;Fi;A2Ftv;Frho;").
Proof using P0f.
  intros rho tv. induction tv as [|a r IH]; cbn.
  - split; [|exact (fun _ => I)]. intros _ i j t t' _ Hi. destruct i; discriminate.
  - split.
    + intros [Ha Hr] i j t t' Hij Hi Hj. destruct i as [|i]; destruct j as [|j]; try lia; cbn in Hi, Hj.
      * injection Hi as <-. apply Ha. eapply nth_error_In; eauto.
      * apply (proj1 IH Hr i j); auto. lia.
    + intros H. split.
      * intros t' Hin. apply In_nth_error in Hin as [j Hj]. apply (H 0%nat (S j) a t'); auto. lia.
      * apply (proj2 IH). intros i j t t' Hij Hi Hj. apply (H (S i) (S j)); auto. lia.
Qed.

Lemma tvd_sym_forall : ltac2:(tb__ "0|3|
S4S30S31S2S2A2M0A1S4cR2R1A2S36S36G0G0S45S41S36R4R3A3A1S41S32G0A1M1S67G0R7R5A3S37G0R3A2M2A3S41G1S67G0R8R5A3G2A3S4bRaR5A2S4bRbR5A2S45S41S31S0S0A2S4dRcR7A2S4dRcR6A2A3A1F_;F_;F_;F_;F_;Ft';Ft;Fj;Fi;F_;Ftv;Frho;").
Proof using P0f.
  intros rho tv HD i j t t' Hij Hi Hj Hz Hz'.
  destruct (Nat.lt_ge_cases i j).
  - exact (proj1 (tvd_forall rho tv) HD i j t t' H Hi Hj Hz Hz').
  - intros E. apply (proj1 (tvd_forall rho tv) HD j i t' t ltac:(lia) Hj Hi Hz' Hz). symmetry. exact E.
Qed.

Lemma tvd_perm : ltac2:(tb__ "0|2|
S4S30S31S2S2A2M0A1M1G1S70G0R2R1A3S4cR4R3A2S4cR5R3A2F_;F_;Ftv';Ftv;Frho;").
Proof using .
  intros rho tv tv' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn; intros HD.
  - exact I.
  - destruct HD as [Hx Hl]. split; [|exact (IH Hl)].
    intros t' Hin. apply Hx. eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin].
  - destruct HD as (Hy & Hx & Hl). split; [|split; [|exact Hl]].
    + intros t' [<-|Hin]; [|apply Hx; exact Hin]. intros Hzx Hzy E. apply (Hy x (or_introl eq_refl) Hzy Hzx). symmetry. exact E.
    + intros t' Hin. apply Hy. right. exact Hin.
  - exact (IH2 (IH1 HD)).
Qed.

Lemma JG_tv_perm : ltac2:(tb__ "0|2|
S30S31S2S2A2M0A1M1G1S4S30S5cA1S5dS70G0R5R4A3S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R6R4R3R2AbS48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R6R5R4R3AbF_;F_;Fmd;Ftr;Frho;Ftv';Ftv;").
Proof using .
  intros tv tv' rho tr md HP (Ai & Hav & Hk & HM & HPf & (HN & HD & HZ) & HK & HP0).
  exists Ai. split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HPf|]. split; [|split; [exact HK|exact HP0]].
  split; [|split].
  - unfold tvin in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN).
    eapply Permutation_in; [apply Permutation_sym; exact HP | exact Ht].
  - eapply tvd_perm; eauto.
  - unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ).
    eapply Permutation_in; [apply Permutation_sym; exact HP | exact Ht].
Qed.

Lemma perm_move_last {A} : ltac2:(tb__ "0|1|
S30VA;A1M0G0VA;S70VA;S35VA;R3S38VA;R1R2A3A3S35VA;S35VA;R3R2A3S38VA;R1S3aVA;A1A3A3A3Fx;Fl2;Fl1;").
Proof using .
  intros l1 l2 x. rewrite <- app_assoc. apply Permutation_app_head.
  change (x :: l2) with ([x] ++ l2). apply Permutation_app_comm.
Qed.

Lemma JG_tv_move_last : ltac2:(tb__ "0|2|
S30S31S2S2A2M0A1M1G1G0S4S30S5cA1S5dS48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S35G0R6S38G0R4R5A3A3R3R2R1AbS48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S35G0S35G0R7R6A3S38G0R5S3aG0A1A3A3R4R3R2AbF_;Fmd;Ftr;Frho;Fx;Fl2;Fl1;").
Proof using . intros. eapply JG_tv_perm; [apply perm_move_last | eassumption]. Qed.

Lemma JG_tv_move_back : ltac2:(tb__ "0|2|
S30S31S2S2A2M0A1M1G1G0S4S30S5cA1S5dS48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S35G0S35G0R6R5A3S38G0R4S3aG0A1A3A3R3R2R1AbS48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S35G0R7S38G0R5R6A3A3R4R3R2AbF_;Fmd;Ftr;Frho;Fx;Fl2;Fl1;").
Proof using . intros. eapply JG_tv_perm; [apply Permutation_sym; apply perm_move_last | eassumption]. Qed.

Lemma SPJ_JG_move_last : ltac2:(tb__ "0|2|
S30S31S2S2A2M0A1M1G1G0S3S4S59S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S35G0R6S38G0R4R5A3A3A8R3R2R1A5S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S35G0S35G0R7R6A3S38G0R5S3aG0A1A3A3A8R4R3R2A5F_;Fw;Frho;FS;Fx;Fl2;Fl1;").
Proof using . intros l1 l2 x S rho w [Hs HJ]. split; [exact Hs | apply JG_tv_move_last; exact HJ]. Qed.

Lemma SPJ_JG_move_back : ltac2:(tb__ "0|2|
S30S31S2S2A2M0A1M1G1G0S3S4S59S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S35G0S35G0R6R5A3S38G0R4S3aG0A1A3A3A8R3R2R1A5S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S35G0R7S38G0R5R6A3A3A8R4R3R2A5F_;Fw;Frho;FS;Fx;Fl2;Fl1;").
Proof using . intros l1 l2 x S rho w [Hs HJ]. split; [exact Hs | apply JG_tv_move_back; exact HJ]. Qed.

Definition norm_xu (xs : list xform) (i : nat) (c : Z) (T : sstate) : option sstate := ltac2:(tb__ "0|1|
S32S3A1M0G0Lx;S82VT;Vxs;A2S3S9dR1Vi;Vc;A3LT1;S3eS3A1X32x2").

Lemma SPJ_norm_xu : ltac2:(tb__ "0|0|
S57S30S81A1S36S0S3S3S4S59S41S32S3A1S60R7R6R5R4A4S37S3R3A2A3S56Vsegs;R9R5R3R2A5S56Vsegs;RaR5R4R3A5F_;F_;Fw;Frho;FT';FT;Fc;Fi;Fxs;FJ;").
Proof using .
  intros J xs i c T T' rho w H Hw. unfold norm_xu in H.
  destruct (apply_xforms T xs) as [T1|] eqn:E; [|discriminate].
  eapply SPJ_unbase; [exact H|]. eapply SPJ_xforms; [exact E | exact Hw].
Qed.

Hypothesis ML : malloc_laws segs C.

Definition cont_check (xs : list xform) (i : nat) (c : Z) (T A : sstate) (tvi tvj : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
S32S3A1S2fLx;S60Vxs;Vi;Vc;VT;A4S3S7dVNP;R1VA;A3S95S2fS2fL_;M0S94R2VA;R1A3G0S96R1VNP;A2G0S8eVNP;S10R2A1M1A2G0S50G1Vtvi;A2S52R1Vtvi;Vtvj;A3S33X2fx2S33X2fx2S33X2fx2S33X2fx2Ts;LT';S33X32x2").

Lemma cont_check_sound : ltac2:(tb__ "0|1|
S30S81A1S36S0S3S3S30S31S2S2A2A1M0G0S41S2fS63R7R6R5R4R3R2R1A7S34A3S4S59S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R5A8R7R2R1A5S43S4S4S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R6A8R8R1R3A5Lrho';A2F_;Fw;Frho;F_;Ftvj;Ftvi;FA;FT;Fc;Fi;Fxs;").
Proof using ML.
  intros xs i c T A tvi tvj H rho w Hw. unfold cont_check in H.
  destruct (norm_xu xs i c T) as [T'|] eqn:E; [|discriminate].
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H5].
  eexists. eapply (SPJ_entails_JG segs C NP Kc rho0 P0f FB ML); [exact H1 | exact H2 | exact H3 | exact H4 | exact H5 |].
  eapply SPJ_norm_xu; [exact E | exact Hw].
Qed.

Lemma cont_triple : ltac2:(tb__ "0|2|
S59OF_;S58S30S81A1S36S0S3S3S30S31S2S2A2M0A1M1G1G1S41S2fS63R8R7R6R5R4R3R2A7S34A3S70G0R3R2A3S4S5aVsegs;RdS56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R4A8R7R1A4RcA4Frho';S4S5aVsegs;ReS56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7A8R9R1A4RdA4Frho;F_;F_;F_;Ftvj';Ftvj;Ftvi;FA;FT;Fc;Fi;Fxs;FQ;Fok;").
Proof using ML.
  intros ok Q xs i c T A tvi tvj tvj' H HP HA rho.
  eapply triple_conseq; [ | intros w Hw; exact Hw
    | apply (triple_ex (fun rho' => SPJ segs (JG segs C NP Kc rho0 P0f FB tvj') A rho')); intros a; apply HA ].
  intros w Hw. destruct (cont_check_sound xs i c T A tvi tvj H rho w Hw) as [rho' H'].
  exists rho'. destruct H' as [Hs HJ]. split; [exact Hs|]. eapply JG_tv_perm; [exact HP | exact HJ].
Qed.

Definition emeasZ (r : Z) (v : sv) (rho : valuation) : Z := ltac2:(tb__ "0|0|
S74S79Vr;S73Z2Z40A2A2S86Q40S17Vrho;Vv;A2A2A2").

Lemma emeas_emeasZ : ltac2:(tb__ "0|1|
S3S30S31S2S2A2A1M0S0S2S4S41S0S55S3cS31S3G0A2S31S0S2A2S3cS3G0R5R4A4S3cS0S2R3R2A4A4R1A2S5eR3R2R1A3A3Frho;Fv;Fr;Ftv;FS;").
Proof using . intros. reflexivity. Qed.

Definition entE_check (n : positive) (X A : sstate) (tvi tvj : list (sv * sv)) (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|2|
S7dVNP;VX;VA;A3S95S2fS2fL_;M0S94VX;VA;R1A3G0S96R1VNP;A2G0S8eVNP;S10VX;A1M1A2G0S50G1Vtvi;A2G0S52R1Vtvi;Vtvj;A3G0S2dVn;VvE;A2G0S75Z0VrA;A2G0S77VrA;VrE;A2S34G0S76VrA;VrE;A2S88SaVX;A1S97R1VvA;A2Z1VvE;A4S33X2fx2X2fx2S33X2fx2S33X2fx2S33X2fx2S33X2fx2S33X2fx2S33X2fx2S33X2fx2Ts;").

Lemma entE_sound : ltac2:(tb__ "0|2|
S1S3S3S30S31S2S2A2A1M0G0S2S0S0S2S41S2fS5fR9R8R7R6R5R4R3R2R1A9S34A3S4S4S59S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;RaA8RcR2R1A5S7aReR4R3A3S43S4S4S42S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;RcA8ReR1R4A5S42S71Z0S5eRaRbR1A3M1A2S72G1S5eR9R8R6A3A2A2A2Lrho';A2F_;F_;Fw;Frho;FrhoX;F_;FvE;FrE;FrA;FvA;Ftvj;Ftvi;FA;FX;Fn;").
Proof using ML.
  intros n X A tvi tvj vA rA rE vE H rhoX rho w Hw Hag. unfold entE_check in H. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H].
  apply lazy_andb_prop in H as [H4 H]. apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [Hb H].
  apply lazy_andb_prop in H as [H0 H].
  exists (rho_sub rho (infer_sub NP X A)). split.
  - eapply (SPJ_entails_JG segs C NP Kc rho0 P0f FB ML); [exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact Hw].
  - unfold emeasZ. rewrite <- eval_subst.
    rewrite (eval_agree_vals n rhoX rho vE Hag Hb).
    apply Z.leb_le in H0.
    pose proof (urange (eval rho (sv_subst (infer_sub NP X A) vA))) as R1. pose proof (urange (eval rho vE)) as R2.
    apply lazy_orb_prop in H as [Hlt|H].
    + apply Z.ltb_lt in Hlt. nia.
    + apply lazy_andb_prop in H as [Heq Hu]. apply Z.eqb_eq in Heq. subst rE.
      destruct Hw as [Hsm _]. destruct w as [tr [ms md]].
      pose proof (uleq_sound rho _ _ 1 _ (smatch_facts_hold segs _ _ _ Hsm) Hu) as U1. unfold U in U1. lia.
Qed.

Section TRX.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S58S58S58S59R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS58S58R3VTR;R3R2A2F_;VTR;S59S42R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX;").

Lemma entE_TR : ltac2:(tb__ "0|3|
S1S3S3S30S31S2S2A2M0A1M1G1G1S2S0S0S2S4S4S58S41S2fS5fRdRcRbRaR9R7R6R5R4A9S34A3S70G0RaR9A3S7aRfR5R4A3S4S42S71Z0S5eRaRbR1A3M2A2S72G2S5eR9R8R7A3A2A2VTR;S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FX;Fn;").
Proof using ML TR_exw TR_pre TR_pureh.
  intros n X A tvi tvj tvj' vA rA rE vE rhoX rho FAMb H HP Hag HA.
  eapply TR_pre; [ | apply (TR_exw valuation (fun rho' w => (0 <= emeasZ rA vA rho' < emeasZ rE vE rhoX) /\ SPJ segs (JG segs C NP Kc rho0 P0f FB tvj') A rho' w))].
  - intros w Hw. destruct (entE_sound n X A tvi tvj vA rA rE vE H rhoX rho w Hw Hag) as (rho' & H' & Hm).
    exists rho'. split; [exact Hm|]. destruct H' as [Hs HJ]. split; [exact Hs|]. eapply JG_tv_perm; [exact HP | exact HJ].
  - intros rho'. apply TR_pureh. intros Hm. exact (HA rho' Hm).
Qed.

Lemma norm_entE_TR : ltac2:(tb__ "0|3|
S30S81A1S36S0S3S3S3S1S30S31S2S2A2M0A1M1G1G1S2S0S0S2S4S4S58S41S32S3A1S60R11R10RfReA4S37S3RdA2A3S41S2fS5fRcReRdRbRaR8R7R6R5A9S34A3S70G0RbRaA3S7aReR6R5A3S4S42S71Z0S5eRbRcR1A3M2A2S72G2S5eRaR9R8A3A2A2VTR;S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;ReA8R12R2A4R7A2F_;Frho';VTR;S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;RfA8R13R7A4R6A2F_;F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;Fn;FA;FX;FT;Fc;Fi;Fxs;").
Proof using ML TR_exw TR_pre TR_pureh.
  intros xs i c T X A n tvi tvj tvj' vA rA rE vE rhoX rho FAMb HN H HP Hag HA.
  eapply TR_pre; [| apply (entE_TR n X A tvi tvj tvj' vA rA rE vE rhoX rho FAMb H HP Hag HA)].
  intros w Hw. eapply SPJ_norm_xu; [exact HN | exact Hw].
Qed.

Definition contE_check (xs : list xform) (i : nat) (c : Z) (n : positive) (T A : sstate) (tvi tvj : list (sv * sv))
           (vA : sv) (rA rE : Z) (vE : sv) : bool := ltac2:(tb__ "0|0|
S32S3A1S2fLx;S60Vxs;Vi;Vc;VT;A4S3S5fVn;R1VA;Vtvi;Vtvj;VvA;VrA;VrE;VvE;A9LX;S33X32x2").

Lemma contE_TR : ltac2:(tb__ "0|3|
S30S81A1S36S0S1S3S3S30S31S2S2A2M0A1M1G1G1S2S0S0S2S4S4S58S41S2fS9fR10RfReRdRcRbRaR9R7R6R5R4AcS34A3S70G0RaR9A3S7aRfR5R4A3S4S42S71Z0S5eRaRbR1A3M2A2S72G2S5eR9R8R7A3A2A2VTR;S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;RdA8R10R2A4R6A2F_;Frho';VTR;S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;ReA8R10R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;").
Proof using ML TR_exw TR_pre TR_pureh.
  intros xs i c n T A tvi tvj tvj' vA rA rE vE rhoX rho FAMb H HP Hag HA. unfold contE_check in H.
  destruct (norm_xu xs i c T) as [X|] eqn:HN; [|discriminate].
  exact (norm_entE_TR xs i c T X A n tvi tvj tvj' vA rA rE vE rhoX rho FAMb HN H HP Hag HA).
Qed.
End TRX.

Definition nz_entry (x : positive * Z * positive) : sv * sv := ltac2:(tb__ "0|2|
S31S31S1S0A2M0S1A2S31S2S2A2M1Lx;Vx;G0S1G0G1Lp;R2S1S0S3cS2S2SbR2A1S1cS93S8R1A1SbR3A1A3A4Le;Ldv;X31x1Lkv;Lp;X31x1").
Definition nz_entry_check (facts : list sprop) (tvi : list (sv * sv)) (x : positive * Z * positive) : bool := ltac2:(tb__ "0|6|
S31S31S1S0A2M0S1A2S2fLx;Vx;G0S1G0S2fLp;R2S1S0S2fS2fL_;M1S6aS31S2S2A2M2G2S39S15S3bS2S2R1A3SbR3A1M3A2S15S3fS2S2R1A3S1cS93S8R2A1SbR4A1A3A2A2Lt;Vtvi;A3G1S88Vfacts;S8Z1M4A1Z0M5G3A4G1S88Vfacts;G3G5S8S73Z2Z2fA2A1A4S39S75G4R1A2S75R1Z1000A2A2S33X2fx2S33X2fx2S33X2fx2Le;Ldv;X31x1Lkv;Lp;X31x1").

Lemma nz_entry_tnz : ltac2:(tb__ "0|2|
S30S7A1S30S31S2S2A2M0A1S31S31S1S0A2S1A2S4S30S5cA1S5dS41S2fS61R6R5R4A3S34A3S6cS7S9R4A1R7A3S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7R5R4R3AbS42S69G0S62R7A1M1R8A3S4bR6G1A2A2F_;F_;F_;Fmd;Ftr;Frho;Fx;Ftvi;Ffacts;").
Proof using .
  intros facts tvi [[dv e] kv] rho tr md H HF HJ. unfold nz_entry_check in H.
  apply lazy_andb_prop in H as [Hin H]. apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 He].
  apply andb_prop in He as [He1 He2]. apply Z.leb_le in He1. apply Z.leb_le in He2.
  apply existsb_exists in Hin as (t & Ht & Heq). apply andb_prop in Heq as [Ha Hb].
  apply sv_eqb_sound in Ha. apply sv_eqb_sound in Hb.
  assert (Et : t = nz_entry (dv, e, kv)) by (destruct t; cbn in Ha, Hb |- *; subst; reflexivity).
  subst t. split; [exact Ht|].
  pose proof (uleq_sound rho _ _ 0 _ HF H1) as U1. pose proof (uleq_sound rho _ _ 0 _ HF H2) as U2.
  unfold U in U1, U2. rewrite U_lit in U1. rewrite U_lit in U2. unfold M64v in U1, U2.
  rewrite Z.mod_small in U1 by lia. rewrite Z.mod_small in U2 by lia.
  destruct HJ as (Ai & _ & _ & _ & _ & (_ & _ & HZ) & _).
  intros Hz0. pose proof (proj1 (Forall_forall _ _) HZ _ Ht) as Z0. specialize (Z0 ltac:(intros X; exact (X Hz0))).
  unfold tvv, nz_entry in Z0. cbn [fst snd] in Z0. rewrite U_mul, U_lit in Z0. unfold M64v in Z0. cbn [eval] in U1, U2, Z0.
  pose proof (bv_urange (rw rho kv)) as Rk.
  rewrite (Z.mod_small e) in Z0 by lia. rewrite Z.mod_small in Z0 by nia. nia.
Qed.

Lemma nz_entry_facts : ltac2:(tb__ "0|0|
S30S7A1S30S31S2S2A2A1S31S31S1S0A2S1A2S4S30S5cA1S5dS41S2fS61R6R5R4A3S34A3S6cS7S9R4A1R7A3S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7R5R4R3AbS6cS7S9R6A1S51S62R7A1A1A3F_;F_;F_;Fmd;Ftr;Frho;Fx;Ftvi;Ffacts;").
Proof using .
  intros facts tvi x rho tr md H HF HJ. destruct (nz_entry_tnz facts tvi x rho tr md H HF HJ) as [Hin Hnz].
  exact (JG_tv_facts segs C NP Kc rho0 P0f FB tvi rho tr md _ HJ Hin Hnz).
Qed.

Definition nz_facts (nzs : list (positive * Z * positive)) : list sprop := ltac2:(tb__ "0|1|
S6bS31S31S1S0A2S1A2M0S7G0S51S62R1A1A1Lx;Vnzs;A4").

Lemma nz_facts_sound : ltac2:(tb__ "0|1|
S30S7A1S30S31S2S2A2A1S30S31S31S1S0A2S1A2M0A1S4S30S5cA1S5dS41S2fS68G0S61R6R5A2R4A3S34A3S6cS7S9R4A1R7A3S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7R5R4R3AbS6cS7S9R6A1S64R7A1A3F_;F_;F_;Fmd;Ftr;Frho;Fnzs;Ftvi;Ffacts;").
Proof using .
  intros facts tvi nzs rho tr md H HF HJ. unfold nz_facts. induction nzs as [|x nzs IH]; [constructor|].
  cbn [flat_map]. cbn [forallb] in H. apply andb_prop in H as [Hx H]. apply Forall_app. split.
  - exact (nz_entry_facts facts tvi x rho tr md Hx HF HJ).
  - exact (IH H).
Qed.

Definition nz_contra_check (facts : list sprop) (tvi : list (sv * sv)) (x : positive * Z * positive) : bool := ltac2:(tb__ "0|1|
S2fS2fL_;S61Vfacts;Vtvi;Vx;A3S88Vfacts;SbS3bS1S0S3bS31S1S0A2S1Vx;A3A3A1Z0M0S8G0A1A4S33X2fx2").

Lemma nz_contraJ : ltac2:(tb__ "0|0|
S3S30S31S2S2A2A1S31S31S1S0A2S1A2S41S2fS66SaR3A1R2R1A3S34A3S4S30S5cA1S5dS48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R6R3R2R1AbS6cS7S9R4A1SaR8A1A3S44F_;F_;Fmd;Ftr;Frho;F_;Fx;Ftvi;FX;").
Proof using .
  intros X tvi x H rho tr md HJ HF. unfold nz_contra_check in H. apply lazy_andb_prop in H as [H1 H2].
  destruct (nz_entry_tnz _ _ _ rho tr md H1 HF HJ) as [_ Hnz].
  pose proof (uleq_sound rho _ _ 0 _ HF H2) as U2. unfold U in U2. rewrite U_lit in U2. unfold M64v in U2.
  rewrite Z.mod_0_l in U2 by lia. apply Hnz. destruct x as [[dv e] kv]. unfold nz_entry, tnz. cbn [fst snd] in *.
  pose proof (bv_urange (eval rho (SVar dv))). lia.
Qed.

Definition contEJ_check (xs : list xform) (i : nat) (c : Z) (n : positive) (T A : sstate) (tvi tvj : list (sv * sv))
           (vA : sv) (rA rE : Z) (vE : sv) (nzs : list (positive * Z * positive)) : bool := ltac2:(tb__ "0|2|
S32S3A1S2fLx;S60Vxs;Vi;Vc;VT;A4S3S2fS2fL_;M0S68S31S31S1S0A2S1A2S61SaR1A1Vtvi;A2Vnzs;A3G0S68S7S2bS10R1A1A1S64Vnzs;A1M1A3S5fVn;S7fG1R1A2VA;Vtvi;Vtvj;VvA;VrA;VrE;VvE;A9S33X2fx2S33X2fx2LX;S33X32x2").

Section TRXJ.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S58S58S58S59R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS58S58R3VTR;R3R2A2F_;VTR;S59S42R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX;").

Lemma contEJ_TR : ltac2:(tb__ "0|3|
S30S81A1S36S0S1S3S3S30S31S2S2A2M0A1M1G1G1S2S0S0S2S30S31S31S1S0A2S1A2A1S4S4S58S41S2fS65R11R10RfReRdRcRbRaR8R7R6R5R4AdS34A3S70G0RbRaA3S7aR10R5R4A3S4S42S71Z0S5eRbRcR1A3M2A2S72G2S5eRaR9R7A3A2A2VTR;S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;ReA8R11R2A4R6A2F_;Frho';VTR;S56Vsegs;S48Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;RfA8R11R6A4R5A2F_;F_;F_;F_;FFAMb;Frho;FrhoX;Fnzs;FvE;FrE;FrA;FvA;Ftvj';Ftvj;Ftvi;FA;FT;Fn;Fc;Fi;Fxs;").
Proof using ML TR_exw TR_pre TR_pureh.
  intros xs i c n T A tvi tvj tvj' vA rA rE vE nzs rhoX rho FAMb H HP Hag HA. unfold contEJ_check in H.
  destruct (norm_xu xs i c T) as [X|] eqn:HN; [|discriminate].
  apply lazy_andb_prop in H as [Hnz H]. apply lazy_andb_prop in H as [Hb H].
  eapply TR_pre; [| apply (entE_TR TR TR_pre TR_exw TR_pureh n (add_facts (nz_facts nzs) X) A tvi tvj tvj' vA rA rE vE rhoX rho FAMb H HP Hag HA)].
  intros w Hw. apply (SPJ_refacts_J segs _ rho X (nz_facts nzs) w).
  - eapply SPJ_norm_xu; [exact HN | exact Hw].
  - exact Hb.
  - intros tr md HJ HF. exact (nz_facts_sound _ _ _ rho tr md Hnz HF HJ).
Qed.
End TRXJ.

Lemma triple_contraJ : ltac2:(tb__ "0|0|
S59OF_;S57S3S58S4S30S5cA1S5dR6R3R2R1A3S6cS7S9R4A1SaR6A1A3S44F_;F_;Fmd;Ftr;Frho;S4S5aVsegs;R6S56Vsegs;R5R4R1A4R3A4Frho;F_;FQ;FX;FJ;Fok;").
Proof using .
  intros ok J X Q HX rho n Hn w [Hsm HJ]. exfalso. destruct w as [tr [ms md]].
  exact (HX rho tr md HJ (smatch_facts_hold segs _ _ _ Hsm)).
Qed.
Lemma etriple_contraJ : ltac2:(tb__ "0|0|
S57S3S58S4S30S5cA1S5dR6R3R2R1A3S6cS7S9R4A1SaR6A1A3S44F_;F_;Fmd;Ftr;Frho;S4S5bVsegs;S56Vsegs;R5R4R1A4R3A3Frho;F_;FQ;FX;FJ;").
Proof using .
  intros J X Q HX rho w [Hsm HJ]. exfalso. destruct w as [tr [ms md]].
  exact (HX rho tr md HJ (smatch_facts_hold segs _ _ _ Hsm)).
Qed.

Lemma triple_pureh : ltac2:(tb__ "0|0|
S59OF_;OS58S58R3S5aVsegs;R5R3R2A4F_;S5aVsegs;R5S59S42R5R4R1A1A2Lw;R2A4F_;FQ;FP;FX;Fok;").
Proof using . intros ok X P Q H n Hn w [HX HP]. exact (H HX n Hn w HP). Qed.
Lemma etriple_pureh : ltac2:(tb__ "0|0|
OS58S58R3S5bVsegs;R3R2A3F_;S5bVsegs;S59S42R5R4R1A1A2Lw;R2A3F_;FQ;FP;FX;").
Proof using . intros X P Q H w [HX HP]. exact (H HX w HP). Qed.
End X.

Section PerCut.
Variable segs : list Segment. Variable NP : positive.
Variable fuel : nat. Variable cutpcs : list Z. Variable g : positive.

Definition ejcut (nodes : list edesc) (i : nat) (n : edesc) : bool := ltac2:(tb__ "0|3|
S39S40S2cS4fVn;A1M0A1A1S39S8eVg;S10G0A1A2S32S30S89A1M1A1S2fLx;S8cVsegs;Vfuel;Vcutpcs;G0S34A5G1S32S30S7cA1M2A1S2fLx;S7eVg;Vi;R1S6eS49S3S4fVnodes;A4A4G2S68S7cS53VNP;Vnodes;A2R1A3Les;S33X32x2Lleaves;S33X32x2A2A2").

Lemma cuts_edges_ok : ltac2:(tb__ "0|5|
S7cS2fF_;S30S3A1M0G0S36S36S3S41S32S3A1S67S3R4R2A3S37S3R1A2A3S42S41S2fS8eVg;S10R2A1A2S34A3S43S30S89A1M1G1S43S30S7cA1M2G2S42S41S32G1A1S8cVsegs;Vfuel;Vcutpcs;R4S34A5S37G1R2A2A3S42S41S32G2A1M3S7eVg;S92R6R5A2R2R8A4S37G2R1A2M4A3S41S2fS68S7cR9R1A3S34A3A2A2Les;A2Lleaves;A2A2F_;FT;Fk;S43G2G2S42S41G3S80Vsegs;Vfuel;Vcutpcs;Vg;R3R4R5A7G4A3S41S2fS68S7cR6R1A3S34A3A2Les;A2F_;Fi;Frest;Ftargets;FP;").
Proof using .
  intros P targets rest. induction rest as [|T rest IH]; intros i Hk.
  - exists []. split; reflexivity.
  - destruct (Hk 0%nat T eq_refl) as (Hg & leaves & es & Hrun & Hle & Hes).
    cbn [cuts_edges]. rewrite Hg. cbn [negb]. rewrite Hrun. rewrite Nat.add_0_r in Hle. rewrite Hle.
    destruct (IH (S i)) as (es' & Hce & Hes').
    { intros k T' Hn. replace (S i + k)%nat with (i + S k)%nat by lia. exact (Hk (S k) T' Hn). }
    rewrite Hce. exists (es ++ es'). split; [reflexivity|]. rewrite forallb_app, Hes, Hes'. reflexivity.
Qed.

Lemma ejcert_of_cuts : ltac2:(tb__ "0|1|
S30S49A1M0G0S36S49S41S32S49A1S67S49R4R2A3S37S49R1A2A3S41S2fS9eS35S49R5R4A3R3R2A3S34A3F_;Fn;Fi;S41S2fS54Vsegs;VNP;Vfuel;Vcutpcs;Vg;R3R2A7S34A3F_;FexitsE;FcutsE;").
Proof using .
  intros cutsE exitsE Hc. unfold ejcert. apply andb_true_intro. split.
  - apply forallb_forall. intros n Hn. apply In_nth_error in Hn as [i Hi].
    pose proof (Hc i n Hi) as H. unfold ejcut in H. apply andb_prop in H as [H _]. exact H.
  - unfold cfg_edges.
    destruct (cuts_edges_ok (eecheckJ NP (cutsE ++ exitsE)) (map ed_state cutsE ++ map ed_state exitsE)
                (map ed_state cutsE) 0 ) as (es & Hce & Hes).
    { intros k T Hn. rewrite nth_error_map in Hn. destruct (nth_error cutsE k) as [n|] eqn:En; [|discriminate].
      cbn in Hn. injection Hn as <-.
      pose proof (Hc k n En) as H. unfold ejcut in H. apply andb_prop in H as [_ H]. apply andb_prop in H as [Hg H].
      split; [exact Hg|].
      destruct (sym_run segs fuel cutpcs (ed_state n) true) as [leaves|]; [|discriminate].
      cbn [Nat.add].
      destruct (leaves_edges g k leaves (map ed_state (cutsE ++ exitsE))) as [es|] eqn:Hle; [|discriminate].
      exists leaves, es. rewrite map_app in Hle. auto. }
    rewrite Hce. exact Hes.
Qed.
End PerCut.

Section R.
Variable segs : list Segment.

Lemma rd_bytes_split : ltac2:(tb__ "0|3|
S7bS36S36S87Q40A1S30S87Q8A1M0A1M1S41S32G1A1M2S23R5R2S92R4R3A2A3S37G1R1A2A3S41G2S23R6R3R5A3S37G1S6dG0R5R2A3A2A3F_;Fbs;Fa;Fk2;Fk1;Fms;").
Proof using .
  intros ms k1. induction k1 as [|k1 IH]; intros k2 a bs H; [reflexivity|].
  cbn [rd_bytes Nat.add] in H |- *. destruct (rd ms a) as [b|]; [|discriminate].
  destruct (rd_bytes ms (a + 1)%bv (k1 + k2)) as [r|] eqn:E; [|discriminate].
  injection H as <-. rewrite (IH k2 _ r E). reflexivity.
Qed.

Definition is_lit0 (v : sv) : bool := match v with SLit z => Z.eqb z 0 | _ => false end.
Section Narrow.
Variable toff : sv.
Definition narrow8to4 (c : cell) : cell := ltac2:(tb__ "0|1|
S2fS6L_;S39S39S15S1dVc;A1M0Vtoff;A2S76S1fVc;A1Z8A2A2S98S1eVc;A1A1A2S22G0Z4S8Z0A1A3Vc;X2fx2").

Lemma is_lit0_sound : ltac2:(tb__ "0|0|
S2S41S2fS98R1A1S34A3S41S2R2S8Z0A1A3F_;Fv;").
Proof using . intros [z| | | | | | |] H; try discriminate. cbn in H. apply Z.eqb_eq in H. subst. reflexivity. Qed.

Lemma narrow_cases : ltac2:(tb__ "0|2|
S6S46S41S6S83R1A1M0R1A3S42S41S0S1fR1A1Z8A3S42S41S2S1eR1A1S8Z0A1M1A3S41S6G0S22S1dR1A1Z4G1A3A3A2A2A2Fc;").
Proof using .
  intros c. unfold narrow8to4. destruct (sv_eqb (c_off c) toff && (c_width c =? 8) && is_lit0 (c_val c)) eqn:E; [|left; reflexivity].
  apply andb_prop in E as [E E2]. apply andb_prop in E as [E0 E1]. apply Z.eqb_eq in E1. apply is_lit0_sound in E2. right. auto.
Qed.

Lemma narrow_cell_holds : ltac2:(tb__ "0|0|
S4S2S0S0S7bS6S16R6R5R4R3R2R1A6S16R7R6R5R4R3S83R2A1A6F_;Fc;Fms;Fhi;Flo;Fbase;Frho;").
Proof using .
  intros rho base lo hi ms c H. destruct (narrow_cases c) as [E|(Ew & Ev & E)]; rewrite E; [exact H|].
  destruct c as [off w v]. cbn [c_off c_width c_val] in *. subst w v.
  destruct H as (H1 & H2 & H3). unfold cell_holds. cbn [c_off c_width c_val] in *. split; [exact H1|]. split; [lia|].
  change (Z.to_nat 8) with (4 + 4)%nat in H3. apply rd_bytes_split in H3. change (Z.to_nat 4) with 4%nat. rewrite H3. reflexivity.
Qed.

Lemma covered_narrow_or_read : ltac2:(tb__ "0|2|
S4S2S0S0S7bS30S6A1S0S6cS6S16R7R6R5R4R3A5R2A3S71S74S86Q40M0S17R8R7A2A2R5A2S73Z2Z40A2A2S71Z0S74S86G0S17R9R8A2A2R7A2A2S20RaR5R4A3S46S20RbS6eS6S6S83R6A4R5A3S43S87Q8A1M1G1S41S32G1A1S2aR8S27RcRbR6A3A2S37G1R1A2A3Lb;A2A2F_;F_;F_;F_;Foff;Fcells;Fms;Fhi;Flo;Fbase;Frho;").
Proof using .
  intros rho base lo hi ms cells off HC Hhi Hlo Hcov.
  unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hin & Hc).
  pose proof (proj1 (Forall_forall _ _) HC c Hin) as Hch.
  destruct (narrow_cases c) as [E|(Ew & Ev & E)].
  - left. unfold covered. apply Exists_exists. exists c. split; [|exact Hc]. apply in_map_iff. exists c. rewrite E. auto.
  - destruct c as [o w v]. cbn [c_off c_width c_val] in Ew, Ev, E. subst w v.
    unfold in_cell in Hc. cbn [c_off c_width] in Hc.
    destruct (Z.lt_ge_cases off (soff rho o + 4)).
    + left. unfold covered. apply Exists_exists. exists (mkCell o 4 (SLit 0)). split.
      * apply in_map_iff. exists (mkCell o 8 (SLit 0)). split; [exact E | exact Hin].
      * unfold in_cell. cbn [c_off c_width]. lia.
    + right. destruct Hch as (A1 & A2 & A3). cbn [c_off c_width c_val] in A1, A2, A3.
      pose proof (rd_bytes_nth ms 8 (oaddr rho base (soff rho o)) _ (Z.to_nat (off - soff rho o)) A3 ltac:(lia)) as R.
      unfold oaddr in R |- *. rewrite Z_to_bv_unsigned in R. unfold bv_wrap in R. rewrite two64 in R.
      rewrite Z.mod_small in R by lia. rewrite Z2Nat.id in R by lia.
      replace (bv_unsigned (eval rho base) + soff rho o + (off - soff rho o)) with (bv_unsigned (eval rho base) + off) in R by lia.
      eexists. apply R. change (Z.of_nat 8) with 8. lia.
Qed.

Lemma obj_holds_narrow : ltac2:(tb__ "0|0|
S4S7bS2S2S2S30S6A1SdVsegs;R6R5S12R4R3R2R1S11A5A4SdVsegs;R7R6S12R5R4R3S6eS6S6S83R2A4S11A5A4F_;Fcells;Fhi;Flo;Fb;Fms;Frho;").
Proof using .
  intros rho ms b lo hi cells (Hb & Hw & Hc & Hd & Hi).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split; [|exact Hi]].
  - apply Forall_forall. intros c Hin. apply in_map_iff in Hin as (c0 & <- & Hin0). apply narrow_cell_holds.
    exact (proj1 (Forall_forall _ _) Hc c0 Hin0).
  - intros off Hoff Hncov. cbn [dflt_holds].
    destruct (covered_dec rho cells off) as [Hcov|Hncov0].
    + destruct (covered_narrow_or_read rho b _ _ ms cells off Hc ltac:(lia) ltac:(lia) Hcov) as [X|X]; [exfalso; exact (Hncov X) |].
      unfold oaddr in X. exact X.
    + exact (Hd off Hoff Hncov0).
Qed.

Definition narrow_obj (o : sobj) : sobj := ltac2:(tb__ "0|0|
S12S18Vo;A1S14Vo;A1S13Vo;A1S6eS6S6S83S19Vo;A1A4ScVo;A1A5").
Definition narrow_at (S : sstate) (i : nat) : sstate := ltac2:(tb__ "0|2|
S8aVS;S35S5S6dS5Vi;S1bVS;A1M0A3S35S5S32S5A1S30S5A1Lx;S67S5G0Vi;A3S5S38S5S84R1A1S3aS5A1M1A3Lo;G1X32x2S6fS5S3dVi;A1G0A3A3A3A2").

Lemma obj_range_narrow : ltac2:(tb__ "0|0|
S4S5S41S31S0S0A2SeR2S84R1A1A2SeR2R1A2A3Fo;Frho;").
Proof using . intros. reflexivity. Qed.

Lemma mem_match_narrow : ltac2:(tb__ "0|1|
S4S7bS30S5A1M0S5G0S41SfScR2A1S11A3S21Vsegs;R6S35S5R4S38S5R3R2A3A3R5A4S21Vsegs;R7S35S5R5S38S5S84R4A1R3A3A3R6A4F_;F_;FL2;Fo;FL1;Fms;Frho;").
Proof using .
  intros rho ms L1 o L2 Hd (Hall & Hpd & Hfr).
  assert (RNG : forall rho', map (obj_range rho') (L1 ++ narrow_obj o :: L2) = map (obj_range rho') (L1 ++ o :: L2)).
  { intros rho'. rewrite !map_app. reflexivity. }
  split; [|split].
  - rewrite !Forall_app in Hall |- *. destruct Hall as (A & B). split; [exact A|].
    inversion B; subst. constructor; [|assumption]. destruct o as [b lo hi cells d]. cbn in Hd. subst d. apply obj_holds_narrow. assumption.
  - apply (proj2 (pairwise_disjoint_pdr rho _)). rewrite RNG. apply (proj1 (pairwise_disjoint_pdr rho _)). exact Hpd.
  - unfold mem_frame, outside_all in *. intros a Ha. apply Hfr.
    rewrite Forall_app in Ha |- *. destruct Ha as [Ha1 Ha2]. split; [exact Ha1|]. inversion Ha2; subst. constructor; assumption.
Qed.

Lemma split_at_nth {A} : ltac2:(tb__ "0|1|
S30VA;A1M0S36VA;S41S32VA;A1S67VA;R3R2A3S37VA;R1A2A3S41G0R4S35VA;S6dVA;R3R4A3S38VA;R2S6fVA;S3dR3A1R4A3A3A3A3F_;Fx;Fi;Fl;").
Proof using .
  intros l i. revert l. induction i as [|i IH]; intros [|y l] x H; cbn in *; try discriminate.
  - injection H as <-. reflexivity.
  - f_equal. exact (IH l x H).
Qed.

Lemma SPJ_narrow : ltac2:(tb__ "0|0|
S57S4S3S36S5S59S41S32S5A1S67S5S1bR4A1R3A3S37S5R2A2A3S41SfScR3A1S11A3S41S2fS9cR6S85R6R5A2A2S34A3S56Vsegs;R9R7R8R4A5S56Vsegs;RaS85R8R7A2R9R5A5F_;F_;F_;F_;Fw;Fo;Fi;FS;Frho;FJ;").
Proof using .
  intros J rho S i o [tr [ms md]] Hi Hd Hsame Hw.
  eapply SPJ_reobj; [exact Hsame | exact Hw |].
  destruct Hw as [Hsm _]. cbn [w_cfg cfg_ms].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem.
  unfold narrow_at. rewrite Hi. cbn [ss_objs set_objs].
  rewrite (split_at_nth (ss_objs S) i o Hi) in Hmem.
  replace (firstn i (ss_objs S) ++ [narrow_obj o] ++ skipn (Datatypes.S i) (ss_objs S))
     with (firstn i (ss_objs S) ++ narrow_obj o :: skipn (Datatypes.S i) (ss_objs S)) by reflexivity.
  apply mem_match_narrow; [exact Hd | exact Hmem].
Qed.
End Narrow.
End R.

Definition obj_merge_arr (o1 o2 : sobj) : option sobj := ltac2:(tb__ "0|8|
SfS32S5A1M0Lx;M1ScVo1;A1S3eS5A1M2G2G2S1G2Ll;M3G3S0S2S30S31S0S0A2A1M4S30S2eA1M5G1ScVo2;A1S2fG0L_;S39S15S18Vo1;A1M6S18Vo2;A1A2S32S0A1S2fLx;S8dS13Vo1;A1S14Vo2;A1A2S0S0S2fLz;R1S34S1S33Lp;M7G7X0x3Lz;S33X32x2A2S37S5S12G6S14Vo1;A1S13Vo2;A1S35S6S19Vo1;A1S19Vo2;A1A3S26R4R3R2R1A4A5A2G2X2fx2G2G2G3G3S0S2G4G5G2Ltmpl0;Lflds0;Lcnt0;Lesz0;Xfx6Ltmpl;Lflds;Lcnt;Lesz;Xfx6").

Definition merge_arr_at (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|8|
S32S5A1S32S3A1M0Lx;M1S67S5S1bVS;A1M2Vi;A3S5G1S67S5G2S3dVi;A1M3A3S5S32S31S0S0A2M4A1G0Lx;M5S8bSaVS;A1M6S14R2A1A2G4G4G0Lp;R1S0S0G5S8bG6S13R4A1A2G4G4G0Lp0;R1S0S0S2fG0L_;S77S78R1R5A2S73Z2Z3fA2A2G1S90R8R7A2S5S37S3S8aVS;S35S5S6dS5Vi;G2A3S38S5R1S6fS5S3dG3A1G2A3A3A3A2A2Lo;S3eS3A1M7X32x2G7X2fx2Lh2;Lz0;X31x1Lp0;G7X32x2Lz;Ll1;X31x1Lp;G7X32x2Lo2;G7X32x2Lo1;G7X32x2").

Section M.
Variable segs : list Segment.

Lemma obj_merge_arr_holds : ltac2:(tb__ "0|2|
S4S7bS5S5S5S41S32S5A1S90R3R2A2S37S5R1A2A3SdVsegs;R6R5R4A4SdVsegs;R7R6R4A4S72S78S28R8R5A2S29R8R6A2A2S73Z2Z3fA2A2S42SdVsegs;R9R8R5A4S42S41S31S0S0A2SeR9R5A2S3cS0S0S3bS0S0SeR9R7A2M0A3S3fS0S0SeR9R6A2M1A3A4A3S41S0S3fS0S0G0A3S3bS0S0G1A3A3A2A2F_;F_;F_;F_;Fo;Fo2;Fo1;Fms;Frho;").
Proof using .
  intros rho ms o1 o2 o Hm H1 H2 Hw.
  unfold obj_merge_arr in Hm.
  destruct (ob_dflt o1) as [| | | | |esz cnt flds tmpl] eqn:Ed1; try discriminate.
  destruct (ob_dflt o2) eqn:Ed2; try discriminate.
  destruct (sv_eqb (ob_base o1) (ob_base o2)) eqn:Eb; [|discriminate].
  destruct (same_atoms (ob_hi o1) (ob_lo o2)) as [[|p|p]|] eqn:Ea; try discriminate. cbn in Hm. injection Hm as <-.
  apply sv_eqb_sound in Eb.
  pose proof (same_atoms_eq rho _ _ Ea) as Eq.
  assert (ADJ : obj_hi_of rho o1 = obj_lo_of rho o2).
  { unfold obj_hi_of, obj_lo_of, soff. rewrite Eq. reflexivity. }
  destruct H1 as (R1 & W1 & C1 & D1 & L1). destruct H2 as (R2 & W2 & C2 & D2 & L2).
  rewrite Ed1 in *. rewrite Ed2 in *. rewrite <- Eb in *.
  unfold obj_holds, obj_range. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi] in *.
  set (b := bv_unsigned (eval rho (ob_base o1))) in *.
  set (lo1 := soff rho (ob_lo o1)) in *. set (hi1 := soff rho (ob_hi o1)) in *.
  set (lo2 := soff rho (ob_lo o2)) in *. set (hi2 := soff rho (ob_hi o2)) in *.
  split; [|split; [cbn [fst snd]; rewrite <- Eb; reflexivity | cbn [fst snd]; rewrite <- Eb; subst b lo1 hi1 lo2 hi2; lia]].
  split; [lia|].
  split. { intros off Hoff _. destruct (Z_lt_ge_dec off hi1); [apply W1; [lia|reflexivity] | apply W2; [lia|reflexivity]]. }
  split.
  { apply Forall_app. split.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) C1 c Hc) as (A & B & C). repeat split; try lia. exact C.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) C2 c Hc) as (A & B & C). repeat split; try lia. exact C. }
  split.
  { intros off Hoff Hnc.
    assert (NC1 : ~ covered rho (ob_cells o1) off).
    { intros H. apply Hnc. unfold covered in *. apply Exists_exists in H as (c & Hin & Hic). apply Exists_exists. exists c. split; [apply in_or_app; auto|exact Hic]. }
    assert (NC2 : ~ covered rho (ob_cells o2) off).
    { intros H. apply Hnc. unfold covered in *. apply Exists_exists in H as (c & Hin & Hic). apply Exists_exists. exists c. split; [apply in_or_app; auto|exact Hic]. }
    cbn [dflt_holds].
    destruct (Z_lt_ge_dec off hi1).
    - specialize (D1 off ltac:(lia) NC1). cbn in D1. exact D1.
    - specialize (D2 off ltac:(lia) NC2). cbn in D2. exact D2. }
  cbn [dflt_inv] in L1 |- *. destruct L1 as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [exact A2|]. split; [lia|]. exact A4.
Qed.

Lemma obj_wf_merge_arr : ltac2:(tb__ "0|0|
S1S5S5S5S41S32S5A1S90R3R2A2S37S5R1A2A3S41S2fS1aR5R4A2S34A3S41S2fS1aR6R4A2S34A3S41S2fS1aR7R4A2S34A3F_;F_;F_;Fo;Fo2;Fo1;Fn;").
Proof using .
  intros n o1 o2 o Hm W1 W2. unfold obj_merge_arr in Hm.
  destruct (ob_dflt o1) as [| | | | |esz cnt flds tmpl] eqn:Ed1; try discriminate.
  destruct (ob_dflt o2) eqn:Ed2; try discriminate.
  destruct (_ && _)%bool; [|discriminate]. injection Hm as <-.
  unfold obj_wf in *. rewrite Ed1 in W1. rewrite Ed2 in W2. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  apply andb_prop in W1 as [W1 D1]. apply andb_prop in W1 as [W1 C1]. apply andb_prop in W1 as [W1 H1]. apply andb_prop in W1 as [B1 L1].
  apply andb_prop in W2 as [W2 D2]. apply andb_prop in W2 as [W2 C2]. apply andb_prop in W2 as [W2 H2]. apply andb_prop in W2 as [B2 L2].
  rewrite forallb_app, B1, L1, H2, C1, C2, D1. reflexivity.
Qed.

Theorem smatch_merge_arr : ltac2:(tb__ "0|0|
S4S3S36S3S31S30S5cA1S9aA2S41S32S3A1S91R4R3A2S37S3R2A2A3S25Vsegs;R6R5R2A4S25Vsegs;R7R4R3A4F_;F_;Fw;FS';Fi;FS;Frho;").
Proof using .
  intros rho S i S' [tr [ms md]] Hmg Hsm.
  unfold merge_arr_at in Hmg.
  destruct (nth_error (ss_objs S) i) as [o1|] eqn:Hn1; [|discriminate].
  destruct (nth_error (ss_objs S) (Datatypes.S i)) as [o2|] eqn:Hn2; [|discriminate].
  destruct (sitv (ss_facts S) (ob_lo o1)) as [[l1 h1]|] eqn:Hs1; [|discriminate].
  destruct (sitv (ss_facts S) (ob_hi o2)) as [[l2 h2]|] eqn:Hs2; [|discriminate].
  destruct (Z.ltb_spec (h2 - l1) (2 ^ 63)) as [Hlt|]; [|discriminate].
  destruct (obj_merge_arr o1 o2) as [o|] eqn:Ho; [|discriminate]. injection Hmg as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split4 _ _ _ _ Hn1 Hn2) as EQ.
  assert (Ho1 : obj_holds segs rho ms o1 /\ obj_holds segs rho ms o2).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall].
    inversion Hall as [|? ? A B]; subst. inversion B; subst. auto. }
  destruct Ho1 as [Ho1 Ho2].
  pose proof (sitv_sound rho (ss_facts S) (ob_lo o1) l1 h1 Hfacts Hs1) as (B1 & _).
  pose proof (sitv_sound rho (ss_facts S) (ob_hi o2) l2 h2 Hfacts Hs2) as (B2 & _).
  destruct (obj_merge_arr_holds rho ms o1 o2 o Ho Ho1 Ho2 ltac:(unfold obj_lo_of, obj_hi_of; lia)) as (Hoh & Rng & Adj).
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ o :: skipn (Datatypes.S (Datatypes.S i)) (ss_objs S))
      with (firstn i (ss_objs S) ++ [o] ++ skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)).
    pose proof (swf_objs S Hwf) as W. rewrite EQ, forallb_app in W. cbn in W.
    apply andb_prop in W as [Wa W]. apply andb_prop in W as [W1 W]. apply andb_prop in W as [W2 Wb].
    assert (EQ' : ss_objs S = firstn i (ss_objs S) ++ o1 :: ([o2] ++ skipn (Datatypes.S (Datatypes.S i)) (ss_objs S))) by exact EQ.
    pose proof (swf_objs_replace S _ _ _ [] Hwf EQ' eq_refl) as Hwf1. cbn [app] in Hwf1.
    assert (EQ2 : ss_objs (set_objs S (firstn i (ss_objs S) ++ o2 :: skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)))
                  = firstn i (ss_objs S) ++ o2 :: skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)) by reflexivity.
    pose proof (swf_objs_replace _ _ _ _ [o] Hwf1 EQ2) as Hwf2. cbn [app forallb] in Hwf2.
    unfold set_objs in Hwf2. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf2.
    apply Hwf2. rewrite (obj_wf_merge_arr _ _ _ _ Ho W1 W2). reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  destruct Hmem as (Hall & Hpd & Hfr).
  split; [|split].
  - apply Forall_app in Hall as [A1 A2].
    inversion A2 as [|? ? _ A3]; subst. inversion A3 as [|? ? _ A4]; subst.
    apply Forall_app. split; [exact A1|]. constructor; [exact Hoh | exact A4].
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *.
    eapply pdr_merge2; [exact Hpd|].
    intros a. rewrite Rng. unfold in_range. cbn [fst snd]. intros Ha.
    destruct (Z_lt_ge_dec a (snd (obj_range rho o1))); [left; lia | right; lia].
  - intros a Ha. apply Hfr.
    assert (LE1 : fst (obj_range rho o1) <= snd (obj_range rho o1)).
    { destruct Ho1 as ((? & ? & ? & ?) & _). unfold obj_range, obj_lo_of, obj_hi_of in *. cbn. lia. }
    assert (LE2 : fst (obj_range rho o2) <= snd (obj_range rho o2)).
    { destruct Ho2 as ((? & ? & ? & ?) & _). unfold obj_range, obj_lo_of, obj_hi_of in *. cbn. lia. }
    pose proof Adj as ADJ.
    assert (COV : forall x, in_range (obj_range rho o) x <->
                   exists o', In o' [o1; o2] /\ in_range (obj_range rho o') x).
    { intros x. rewrite Rng. unfold in_range. cbn [fst snd]. split.
      + intros Hx. destruct (Z_lt_ge_dec x (snd (obj_range rho o1))).
        * exists o1. split; [cbn; auto | lia].
        * exists o2. split; [cbn; auto | lia].
      + intros (o' & Hin & Hx). cbn in Hin. destruct Hin as [<-|[<-|[]]]; lia. }
    apply (proj1 (outside_all_replace rho (firstn i (ss_objs S)) o
             (skipn (Datatypes.S (Datatypes.S i)) (ss_objs S)) [o1; o2] a COV)). exact Ha.
Qed.

Lemma SPJ_merge_arr : ltac2:(tb__ "0|0|
S57S4S3S36S3S59S41S32S3A1S91R4R3A2S37S3R2A2A3S56Vsegs;R7R5R6R2A5S56Vsegs;R8R4R7R3A5F_;F_;Fw;FS';Fi;FS;Frho;FJ;").
Proof using . intros J rho S i S' w H [Hs Hk]. split; [eapply smatch_merge_arr; eauto | exact Hk]. Qed.
End M.

Lemma T_ok_range30 : ltac2:(tb__ "0|2|
S4S0S4aR2R1A2S42S71S73Z2M0Z2eA2S86Q40S24R3P1eA2A2M1A2S72G1S73G0Z3fA2A2A2F_;FT;Frho;").
Proof. intros rho T [E R]. unfold V_TOP in E. rewrite E. exact R. Qed.
Lemma T_ok_eq30 : ltac2:(tb__ "0|0|
S4S0S4aR2R1A2S41S0S86Q40S24R3P1eA2A2R2A3F_;FT;Frho;").
Proof. intros rho T [E _]. exact E. Qed.

Lemma T_ok_T0_agree : ltac2:(tb__ "0|0|
S1S4S4S0S7aR4R3R2A3S8fP1eR5A2S4aR4R3A2S4aR5S4eR6A1A2F_;F_;F_;FT;Frho;Frho0;Fn;").
Proof.
  intros n rho0 rho T [Hw _] Hn [E R]. unfold T_ok, T0, V_TOP in *. rewrite (Hw 30%positive Hn).
  split; [reflexivity|]. rewrite E. exact R.
Qed.
Lemma T_ok_T0_NF : ltac2:(tb__ "0|0|
S4S4S0S7aS9bR3R2A3S4aR3R2A2S4aR4S4eR5A1A2F_;F_;FT;Frho;Frho0;").
Proof. intros rho0 rho T Hav HT. exact (T_ok_T0_agree NF rho0 rho T Hav (@eq_refl comparison Lt) HT). Qed.
