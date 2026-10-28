From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjXform TobjJV TobjArena TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_aa.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L14 Require Import S_ir.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ir_A : Z := 0x18ca0.
Definition ir_B : Z := 0x18cd8.
Definition ir_X : Z := 0x18cfc.
Definition ir_C : Z := 0x18d30.
Definition FUEL_ir : nat := 400%nat.
Definition cutpcs_ir : list Z := [S_aa.aa_entry; ir_A; ir_B; ir_X; ir_C].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_ir cutpcs_ir S true with Some ls => map lf_state ls | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := filter (fun l => Z.eqb (ss_pc l) pc) (run_of S).
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_ir end.

Definition is_txt (o : sobj) : bool :=
  sv_eqb (ob_base o) vB && sv_eqb (ob_lo o) (SLit 0) && sv_eqb (ob_hi o) vL.
Definition drop_cells_if (f : sobj -> bool) (o : sobj) : sobj :=
  if f o then mkObj (ob_base o) (ob_lo o) (ob_hi o) [] (ob_dflt o) else o.

Definition vJ : sv := SVar 100.  Definition vK : sv := SVar 101.
Definition cin (c : sv) : list sprop := [SPUle vI c; SPUlt c vE; SPUlt c vL; SPUle c (SLit (2 ^ 40))].
Definition cle (c : sv) : list sprop := [SPUle vI c; SPUle c vE; SPUle c (SLit (2 ^ 40))].

Definition X_A0 : sstate := Eval vm_compute in nth 0 (leaves_at Pre_ir ir_A) Pre_ir.
Definition X_B0 : sstate := Eval vm_compute in nth 0 (leaves_at Pre_ir ir_B) Pre_ir.
Definition X_X0 : sstate := Eval vm_compute in nth 0 (leaves_at Pre_ir ir_X) Pre_ir.

Definition C_A : sstate := Eval vm_compute in
  mkSS ir_A (setregs (ss_regs X_A0) [(8%nat, pB vJ); (13%nat, SVar 102)]) pre_fregs FcsrFrm0 None
    (map (drop_cells_if is_txt) (ss_objs X_A0)) (cin vJ ++ base_facts) 103 false.
Definition C_B : sstate := Eval vm_compute in
  mkSS ir_B (setregs (ss_regs X_B0) [(8%nat, pB vJ); (9%nat, pB vK); (14%nat, SAlu ALU_ADD (pB vK) (SLit (-1))); (15%nat, SVar 102)])
    pre_fregs FcsrFrm0 None (map (drop_cells_if is_txt) (ss_objs X_B0)) (cle vJ ++ [SPUlt vJ vK; SPUle vK vE] ++ base_facts) 103 false.
Definition C_X : sstate := Eval vm_compute in
  mkSS ir_X (setregs (ss_regs X_X0) [(8%nat, pB vJ); (9%nat, pB vK); (11%nat, SVar 102); (12%nat, SVar 103); (13%nat, SVar 104); (14%nat, SVar 105); (15%nat, SVar 106)])
    pre_fregs FcsrFrm0 None (map (drop_cells_if is_txt) (ss_objs X_X0)) (cle vJ ++ [SPUle vJ vK; SPUle vK vE] ++ base_facts) 107 false.

Definition PreA : sstate := S_aa.Pre_aa 1.
Definition E_aa : sstate := Eval vm_compute in nth 0 (leaves_at C_X S_aa.aa_entry) Pre_ir.
Definition s_aa : wsub := (19%positive, dlo) :: infer_sub 10 E_aa PreA.
Definition R_aa : list sobj := Eval vm_compute in optR (entails_fr E_aa PreA s_aa).
Definition T_fail : sstate := Eval vm_compute in T_afterN NF E_aa s_aa R_aa S_aa.P_fail.
Definition T_ok : sstate := Eval vm_compute in T_afterN NF E_aa s_aa R_aa (S_aa.P_ok 1).
Definition am_fail : amode := Eval vm_compute in
  am_subst (import_sub s_aa NF S_aa.P_fail (ss_next E_aa)) (AHead S_aa.vHD).
Definition am_loop : amode := Eval vm_compute in
  am_subst (import_sub s_aa NF (S_aa.P_ok 1) (ss_next E_aa))
    (AOpen S_aa.vH S_aa.vNX S_aa.vCAP [(S_aa.vP, S_aa.vSZ)]).

Definition perm_ok : list nat := [5; 0; 1; 6; 7; 8; 2; 9; 3; 4]%nat.
Definition C_ok : sstate := Eval vm_compute in optS (apply_xforms T_ok [XSelect perm_ok]).

Definition vP : sv := Eval vm_compute in match am_loop with AOpen _ _ _ ((p, _) :: _) => p | _ => SLit 0 end.
Definition szq : sv := Eval vm_compute in match am_loop with AOpen _ _ _ ((_, z) :: _) => z | _ => SLit 0 end.
Definition vH : sv := Eval vm_compute in match am_loop with AOpen h _ _ _ => h | _ => SLit 0 end.
Definition vNX : sv := Eval vm_compute in match am_loop with AOpen _ n _ _ => n | _ => SLit 0 end.
Definition vCAP : sv := Eval vm_compute in match am_loop with AOpen _ _ c _ => c | _ => SLit 0 end.
Definition vU : sv := Eval vm_compute in
  match List.find (fun o => sv_eqb (ob_base o) vH) (ss_objs C_ok) with
  | Some o => c_val (nth 2 (ob_cells o) (mkCell (SLit 0) 8 (SLit 0)))
  | None => SLit 0 end.
Definition is_slot (o : sobj) : bool := sv_eqb (ob_base o) vP.

Definition X_ret0 : sstate := Eval vm_compute in nth 0 (leaves_at C_ok ir_ret) Pre_ir.
Definition X_C0 : sstate := Eval vm_compute in nth 0 (leaves_at C_ok ir_C) Pre_ir.
Definition nC0 : positive := Eval vm_compute in ss_next X_C0.
Definition vX : sv := SVar nC0.
Definition lenJK : sv := SAlu ALU_SUB vK vJ.
Definition C_C : sstate := Eval vm_compute in
  mkSS ir_C (setregs (ss_regs X_C0) [(12%nat, vX)]) (ss_fregs X_C0) (ss_fcsr X_C0) (ss_resv X_C0)
    (map (drop_cells_if (fun o => is_txt o || is_slot o)) (ss_objs X_C0))
    ([SPUlt (SAlu ALU_ADD vJ vX) vK; SPUlt vX lenJK; SPUle vX (SLit (2 ^ 40))] ++ ss_facts X_C0) (Pos.succ nC0) false.
Definition X_ret1 : sstate := Eval vm_compute in nth 0 (leaves_at C_C ir_ret) Pre_ir.

Definition z0 : sv := SLit 0.
Definition varA : sv := SAlu ALU_SUB vE vJ.
Definition varB : sv := SAlu ALU_SUB vK vJ.
Definition varC : sv := SAlu ALU_SUB lenJK vX.

Definition cutsE : list aedesc :=
  [ (Pre_ir, (tv0, ahd), (100, z0));
    (C_A, (tv0, ahd), (98, varA));
    (C_B, (tv0, ahd), (97, varB));
    (C_X, (tv0, ahd), (96, z0));
    (T_fail, (tv0, am_fail), (90, z0));
    (C_ok, (tv0, am_loop), (90, z0));
    (C_C, (tv0, am_loop), (50, varC)) ].
Definition exitsE : list aedesc :=
  [ (E_aa, (tv0, ahd), (95, z0));
    (X_ret0, (tv0, am_loop), (10, z0));
    (X_ret1, (tv0, am_loop), (10, z0));
    (P_fail, (tv0, ahd), (0, z0));
    (P_ok, (tv0, am_ok), (0, z0)) ].

Lemma ejcert_ok : ejcertA segsU NF FUEL_ir cutpcs_ir 100 cutsE exitsE = true.
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.

Let nA : sstate * (list (sv * sv) * amode) -> jnode := nodeA segsU C_U NF Kc rho0 (P0_ir FB) FB.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U NF Kc rho0 (P0_ir FB) FB tv am.
Let Q : assn := LQP segsU NF rho0 (Posts_ir Kc FB).

Lemma P0_at : forall rho, agree_vals NF rho0 rho -> P0_ir FB rho0 -> P0_ir FB rho.
Proof using .
  intros rho Hav HP0.
  assert (E15 : rw rho 15%positive = rw rho0 15%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E18 : rw rho 18%positive = rw rho0 18%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold P0_ir. rewrite E15, E18. exact HP0.
Qed.

Lemma txt_pclF : forall (R : list sobj) (facts : list sprop) (rho : valuation) (o : sobj) (a : Z),
  In o R -> is_txt o = true -> P0_ir FB rho0 -> agree_vals NF rho0 rho -> Forall (holds rho) facts ->
  In (SPUle vL (SLit (2 ^ 32))) facts ->
  (fst (obj_range rho o) <= a /\ a < snd (obj_range rho o)) -> pclF segsU C_U rho0 FB a.
Proof using .
  intros R facts rho o a _ Ho HP0 Hav HF Hin Hr. unfold is_txt in Ho.
  apply andb_prop in Ho as [Ho Hh]. apply andb_prop in Ho as [Hb Hl].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  destruct (P0_at rho Hav HP0) as (b & n & Hbin & H1 & H2).
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U in Hr.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as HL. cbn [holds] in HL. rewrite U_lit in HL. unfold vL, vB in *. rewrite !eval_var in *.
  unfold M64v in HL. rewrite Z.mod_small in HL by lia.
  destruct (Zsigned_spec (bv_unsigned (rw rho 18%positive))) as [[_ X]|[X _]]; [|lia]. rewrite X in Hr.
  right; right. exists b, n. split; [exact Hbin | lia].
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall (J : jpred) (S : sstate) (rho : valuation) (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_callP : forall (J Jp : jpred) (C Pre : sstate) (s : wsub) (R : list sobj)
  (Posts : list (sstate * jpost)) (Q' : assn) (rho : valuation),
  entails_fr C Pre s = Some R ->
  call_checkP C Pre s R (map fst Posts) = true ->
  (forall rho1, TR (SPJ segsU Jp Pre rho1) (LQP segsU (ss_next Pre) rho1 Posts)) ->
  (forall tr ms md, smatch segsU rho C (tr, mkCfg ms md) -> J rho tr md -> Jp (rho_sub (rho_absorb rho R ms) s) tr md) ->
  (forall L JL tr ms md rhoL tr' ms' md', In (L, JL) Posts ->
     smatch segsU rho C (tr, mkCfg ms md) -> J rho tr md ->
     agree_vals (ss_next Pre) (rho_sub (rho_absorb rho R ms) s) rhoL ->
     smatch segsU rhoL L (tr', mkCfg ms' md') -> JL (rho_sub (rho_absorb rho R ms) s) rhoL tr' md' ->
     import_okP rho ms R s Pre L rhoL /\
     (forall rho', call_linkP rho ms R s Pre C L rho' rhoL ->
        TR (SPJ segsU (J_ofP JL (rho_sub (rho_absorb rho R ms) s) rhoL) (import_post s (ss_next Pre) L (ss_next C) R) rho') Q')) ->
  TR (SPJ segsU J C rho) Q'.
Hypothesis CAA : forall (FBc : list (Z * Z)) (rho1 : valuation),
  TR (SPJ segsU (JGA_pre segsU C_U Kc (S_aa.P0_aa FBc) FBc S_aa.tv0 (AHead S_aa.vHD)) PreA rho1)
     (LQP segsU NF rho1 (PostsCA segsU C_U Kc S_aa.P0_aa (S_aa.PDA_aa 1) FBc)).
Hypothesis REENTER : forall (T : sstate) (tv : list (sv * sv)) (am : amode) (rT : Z) (vT : sv) (rho : valuation) (b : Z),
  In ((T, (tv, am)), (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b ->
  TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis POST : forall (P : sstate) (tv : list (sv * sv)) (am : amode) (rho : valuation) (b : Z),
  In (P, JLGA segsU C_U Kc (P0_ir FB) FB tv am) (Posts_ir Kc FB) ->
  TR (SPJ segsU (JGv tv am) P rho) (FAM b).

Let CALLAA := client_callAT segsU C_U NF Kc rho0 (P0_ir FB) FB ML S_aa.P0_aa PreA S_aa.tv0 (AHead S_aa.vHD)
  (S_aa.PDA_aa 1) NF (@eq_refl positive (ss_next PreA)) TR TR_facts TR_ex TR_pre TR_callP CAA.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <->
  (r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v)).
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv am rT vT := apply (REENTER T tv am rT vT); [cbn; tauto | lia | first [lia | unfold ameas, ad_rank, ad_var; cbn [fst snd]; apply bound_ge; left; lia]].

Lemma X_P_fail : forall rho b, TR (SPJ segsU (JGv tv0 ahd) P_fail rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_ok : forall rho b, TR (SPJ segsU (JGv tv0 am_ok) P_ok rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.

Ltac ret_ok X :=
  let rho := fresh "rho" in let b := fresh "b" in let w := fresh "w" in let Hw := fresh "Hw" in
  let rho1 := fresh "rho1" in let Hw1 := fresh "Hw1" in let rho2 := fresh "rho2" in let Hw2 := fresh "Hw2" in
  intros rho b;
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0 am_ok) P_ok r w)); [ | apply TR_exw; intros ?; apply X_P_ok ];
  intros w Hw;
  destruct (JGA_unslot segsU C_U NF Kc rho0 (P0_ir FB) FB ML tv0 vH vNX vCAP vP szq
              X (firstn 9 (ss_objs X)) (nth 9 (ss_objs X) O_DD) rho w)
    as (rho1 & _ & Hw1); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |];
  destruct (JGA_close segsU C_U NF Kc rho0 (P0_ir FB) FB ML tv0 vH vNX vCAP vU
              (drop_last_state X (firstn 9 (ss_objs X))) (firstn 8 (firstn 9 (ss_objs X))) (nth 8 (ss_objs X) O_DD) rho1 w)
    as (rho2 & _ & Hw2); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw1 |];
  exists (rho_sub rho2 (infer_sub 100 (drop_last_state (drop_last_state X (firstn 9 (ss_objs X))) (firstn 8 (firstn 9 (ss_objs X)))) P_ok));
  eapply (SPJ_entails_JGA segsU C_U NF Kc rho0 (P0_ir FB) FB ML
            (drop_last_state (drop_last_state X (firstn 9 (ss_objs X))) (firstn 8 (firstn 9 (ss_objs X)))) P_ok
            (infer_sub 100 (drop_last_state (drop_last_state X (firstn 9 (ss_objs X))) (firstn 8 (firstn 9 (ss_objs X)))) P_ok)
            tv0 tv0 (AHead vH) am_ok);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hw2].

Lemma X_ret0_ok : forall rho b, TR (SPJ segsU (JGv tv0 am_loop) X_ret0 rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_ok X_ret0. Qed.
Lemma X_ret1_ok : forall rho b, TR (SPJ segsU (JGv tv0 am_loop) X_ret1 rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_ok X_ret1. Qed.

Lemma X_E_aa : forall rho, TR (SPJ segsU (JGv tv0 ahd) E_aa rho) (FAM (ameas ((E_aa, (tv0, ahd)), (95, z0)) rho)).
Proof using CAA ML REENTER TR_callP TR_ex TR_facts TR_pre.
  intros rho.
  apply (CALLAA E_aa s_aa R_aa rho [] tv0 ahd).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF HP0 Hav HP HN HD HZ HXA HM HT. split; [| exact I].
    eapply (robjs_checkF_sound segsU C_U rho0 FB rho (ss_facts E_aa) [] is_txt R_aa HF
              (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT)); [unfold tvz; constructor | vm_compute; reflexivity |].
    intros o a Ho Hx Hr. apply pclF_FBx.
    eapply (txt_pclF R_aa (ss_facts E_aa) rho o a Ho Hx HP0 Hav HF); [vm_compute; tauto | exact Hr].
  - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[]]]; cbn [fst snd].
    + change (T_afterN NF E_aa s_aa R_aa S_aa.P_fail) with T_fail.
      match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) _ _) _ =>
        replace tv with tv0 by (vm_compute; reflexivity); replace am with am_fail by (vm_compute; reflexivity) end.
      reenter T_fail tv0 am_fail 90 z0.
    + change (T_afterN NF E_aa s_aa R_aa (S_aa.P_ok 1)) with T_ok.
      match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) _ _) _ =>
        replace tv with tv0 by (vm_compute; reflexivity); replace am with am_loop by (vm_compute; reflexivity) end.
      eapply TR_pre; [ | reenter C_ok tv0 am_loop 90 z0 ].
      intros w Hw. exact (SPJ_xforms segsU _ [XSelect perm_ok] rho' T_ok C_ok w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : forall X tvX amX rvX rho, In ((X, (tvX, amX)), rvX) exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas ((X, (tvX, amX)), rvX) rho)).
Proof using CAA ML POST REENTER TR_callP TR_ex TR_exw TR_facts TR_pre.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <- <-.
  - apply X_E_aa.
  - apply X_ret0_ok.
  - apply X_ret1_ok.
  - apply X_P_fail.
  - apply X_P_ok.
Qed.
End SumT.

Section Safety.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis AAS : S_aa.aa_stmt_U.

Theorem intern_rest_sum : triple segsU ok (SPJ segsU (JGA_pre segsU C_U Kc (P0_ir FB) FB tv0 ahd) Pre_ir rho0)
  (LQP segsU NF rho0 (Posts_ir Kc FB)).
Proof using AAS HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segsU C_U NF Kc rho0 (P0_ir FB) FB ML FUEL_ir cutpcs_ir 100 cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nA (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (call_soundP segsU ok)).
       - intros FBc rho1. exact (AAS 1 (or_introl eq_refl) ok Kc FBc rho1 HS ML MC).
       - intros T tv am rT vT rho b Hin _ _. exact (reenter_cutGAE segsU C_U NF Kc rho0 (P0_ir FB) FB ok cutsE T tv am (rT, vT) Q rho Hin).
       - intros P tv am rho b Hin. apply (exit_postGA segsU C_U NF Kc (P0_ir FB) FB ok rho0 tv am (Posts_ir Kc FB) P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis AAX : S_aa.aa_ex_stmt_U.

Theorem intern_rest_sum_ex : etriple segsU (SPJ segsU (JGA_pre segsU C_U Kc (P0_ir FB) FB tv0 ahd) Pre_ir rho0)
  (LQP segsU NF rho0 (Posts_ir Kc FB)).
Proof using AAX Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segsU C_U NF Kc rho0 (P0_ir FB) FB ML FUEL_ir cutpcs_ir 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U NF Kc rho0 (P0_ir FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (call_completeP segsU)).
       - intros FBc rho1. exact (AAX 1 (or_introl eq_refl) Kc FBc rho1 Hvi ML MCX).
       - intros T tv am rT vT rho b Hin H0 Hb. apply (ereenter_cutAE segsU C_U NF Kc rho0 (P0_ir FB) FB cutsE T tv am (rT, vT) Q b rho Hin).
         unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv am rho b Hin. apply (eexit_postGA segsU C_U NF Kc (P0_ir FB) FB rho0 tv am (Posts_ir Kc FB) P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem intern_rest_sum_U : S_aa.aa_stmt_U -> intern_rest_stmt_U.
Proof. intros AAS ok Kc FB rho0 HS ML MC. exact (intern_rest_sum ok Kc FB rho0 HS ML MC AAS). Qed.

Theorem intern_rest_ex_U : S_aa.aa_ex_stmt_U -> intern_rest_ex_stmt_U.
Proof. intros AAX Kc FB rho0 Hvi ML MCX. exact (intern_rest_sum_ex Kc FB rho0 ML Hvi MCX AAX). Qed.
