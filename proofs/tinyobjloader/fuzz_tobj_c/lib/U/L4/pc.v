From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjXform.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require Import S_pc S_si si.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import PcJoin.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ParseCornerAddrU ScanIntAddrU.

Definition FUEL_pc : nat := 400%nat.
Definition cutpcs_pc : list Z := [siU_entry; pcU_ret].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_pc cutpcs_pc S true with Some l => map lf_state l | None => [] end.
Definition leaves_at (pc : Z) (S : sstate) : list sstate := List.filter (fun T => Z.eqb (ss_pc T) pc) (run_of S).
Definition stuck_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_pc cutpcs_pc S true with
  | Some l => map lf_state (List.filter (fun L => match lf_reason L with RsCut => false | _ => true end) l)
  | None => []
  end.

(* The end of the token as one variable, so pointer comparisons against it give offset bounds. *)
Definition vEg : sv := SVar 100.
Definition pEg : sv := SAlu ALU_ADD PC.vB vEg.

Definition set_cell (o : sobj) (off : Z) (v : sv) : sobj :=
  mkObj (ob_base o) (ob_lo o) (ob_hi o)
    (map (fun c => if sv_eqb (c_off c) (SLit off) then mkCell (c_off c) (c_width c) v else c) (ob_cells o)) (ob_dflt o).

(* First call of scan_int. *)
Definition E1 : sstate := Eval vm_compute in nth 0 (leaves_at siU_entry Pre_pc_U) Pre_pc_U.
Definition X1 : sstate :=
  Eval vm_compute in
  mkSS (ss_pc E1) (setregs (ss_regs E1) [(11%nat, pEg)]) (ss_fregs E1) (ss_fcsr E1) (ss_resv E1)
    (match ss_objs E1 with o :: r => set_cell o (-48) pEg :: r | [] => [] end)
    (SPUle vEg PC.vL :: SPUle PC.vT vEg :: ss_facts E1) 101 false.
Definition s_X1 : wsub := [(100%positive, SAlu ALU_ADD PC.vT PC.vTL)].
Definition X1_xf : list xform := [XSplit 0 (SLit (-60)); XSplit 1 (SLit (-56)); XSplit 2 (SLit (-48))].
Definition optS (o : option sstate) : sstate := match o with Some X => X | None => Pre_pc_U end.
Definition optR (o : option (list sobj)) : list sobj := match o with Some r => r | None => [] end.
Definition X1s : sstate := Eval vm_compute in optS (apply_xforms X1 X1_xf).

(* Substitution instantiating scan_int's precondition at a call state. *)
Definition call_sub (C : sstate) : wsub :=
  let curp := reg C 10 in
  let cur := match find (fun o => sv_eqb (SAlu ALU_ADD (ob_base o) (ob_lo o)) curp || sv_eqb (ob_base o) curp) (ss_objs C) with
             | Some o => match ob_cells o with c :: _ => c_val c | [] => SLit 0 end
             | None => SLit 0 end in
  [(15%positive, SVar 15); (18%positive, SVar 18); (17%positive, vEg);
   (16%positive, cur_off cur); (12%positive, curp); (14%positive, reg C 12)] ++ infer_sub 10 C Pre_si_U.

Definition post_cut (C : sstate) (s : wsub) (R : list sobj) (P : sstate) : sstate :=
  let T := import_post s NF P (ss_next C) R in with_facts T (ss_facts T ++ ss_facts C).

Definition s1 : wsub := Eval vm_compute in call_sub X1s.
Definition R1 : list sobj := Eval vm_compute in optR (entails_fr X1s Pre_si_U s1).
Definition W1n : sstate := Eval vm_compute in post_cut X1s s1 R1 P_none_U.
Definition W1u : sstate := Eval vm_compute in post_cut X1s s1 R1 P_num_U.

Definition site (ra : Z) (Ws : list sstate) : list sstate :=
  List.filter (fun X => sv_eqb (reg X 1) (SLit ra)) (flat_map (leaves_at siU_entry) Ws).

(* Call site B: return address 0x18be0. *)
Definition raB : Z := 0x18be0.
Definition LsB : list sstate := Eval vm_compute in site raB [W1n; W1u].
Definition JB := Eval vm_compute in join PC.vB vEg true Pre_pc_U (reg (nth 0 LsB Pre_pc_U) 10) LsB.
Definition GB : sstate := Eval vm_compute in fst JB.
Definition locsB : list (positive * loc) := Eval vm_compute in snd JB.
Definition sB : wsub := Eval vm_compute in call_sub GB.
Definition RB : list sobj := Eval vm_compute in optR (entails_fr GB Pre_si_U sB).
Definition Bn : sstate := Eval vm_compute in post_cut GB sB RB P_none_U.
Definition Bu : sstate := Eval vm_compute in post_cut GB sB RB P_num_U.

(* Call site A: return address 0x18c34, reached from the first and from site B's returns. *)
Definition raA : Z := 0x18c34.
Definition LsA : list sstate := Eval vm_compute in site raA [W1n; W1u; Bn; Bu].
Definition JA := Eval vm_compute in join PC.vB vEg true Pre_pc_U (reg (nth 0 LsA Pre_pc_U) 10) LsA.
Definition GA : sstate := Eval vm_compute in fst JA.
Definition locsA : list (positive * loc) := Eval vm_compute in snd JA.
Definition sA : wsub := Eval vm_compute in call_sub GA.
Definition RA : list sobj := Eval vm_compute in optR (entails_fr GA Pre_si_U sA).
Definition An : sstate := Eval vm_compute in post_cut GA sA RA P_none_U.
Definition Au : sstate := Eval vm_compute in post_cut GA sA RA P_num_U.

Definition cuts_pc : list sstate := [Pre_pc_U; W1n; W1u; Bn; Bu; An; Au].

(* Returns: one joined exit, merged back to the single frame of P_ret_U. *)
Definition LsR : list sstate := Eval vm_compute in flat_map (leaves_at pcU_ret) cuts_pc.
Definition RJ : sstate := Eval vm_compute in fst (join PC.vB vEg false Pre_pc_U (SLit 0) LsR).
Definition RJ_xf : list xform := Eval vm_compute in rebase_plan RJ.
Definition RJr : sstate := Eval vm_compute in optS (apply_xforms RJ RJ_xf).
Definition RJm_xf : list xform := Eval vm_compute in merge_plan RJr.
Definition RJm : sstate := Eval vm_compute in optS (apply_xforms RJr RJm_xf).
Definition s_ret : wsub := Eval vm_compute in infer_sub NF RJm P_ret_U.

(* Paths into the overflow traps after fix (all infeasible). *)
Definition Traps : list sstate := Eval vm_compute in flat_map stuck_of cuts_pc.

Definition exits_pc : list sstate := [E1] ++ LsB ++ LsA ++ [RJ] ++ Traps.

Lemma check_pc : check_cfg segsU FUEL_pc cutpcs_pc NF cuts_pc exits_pc = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_pc_strict : existsb ss_lenient cuts_pc = false.
Proof. vm_compute. reflexivity. Qed.


(* The six error leaves are fix's signed wrap-around check on [n + sext32 i]; n <= 2^47 decides it. *)
Definition ovf_fact (n v : positive) : sprop :=
  SPBranch BC_NE (SAlu ALU_SLT (SExt true 32 (SVar v)) (SLit 0))
    (SAlu ALU_SLT (SAlu ALU_ADD (SVar n) (SExt true 32 (SVar v))) (SVar n)).

Lemma ovf_contra : forall rho n v,
  holds rho (SPUle (SVar n) (SLit PC.two47)) -> holds rho (ovf_fact n v) -> False.
Proof. intros rho n v H1 H2. unfold ovf_fact, PC.two47 in *. zfacts; lia. Qed.

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F H :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF ltac:(vm_compute; reflexivity)) as H end.

Definition Tr (i : nat) : sstate := nth i Traps Pre_pc_U.
Lemma Traps_eq : Traps = map Tr (seq 0 6).
Proof. vm_compute. reflexivity. Qed.

Ltac tr_contra n v :=
  let rho := fresh "rho" in let HF := fresh "HF" in let H0 := fresh "H" in let H1 := fresh "H" in
  intros rho HF; have_fact HF (ovf_fact n v) H0; have_fact HF (SPUle (SVar n) (SLit PC.two47)) H1;
  exact (ovf_contra rho n v H1 H0).
Lemma contra_tr0 : forall rho, Forall (holds rho) (ss_facts (Tr 0)) -> False. Proof. tr_contra 14%positive 144%positive. Qed.
Lemma contra_tr1 : forall rho, Forall (holds rho) (ss_facts (Tr 1)) -> False. Proof. tr_contra 14%positive 143%positive. Qed.
Lemma contra_tr2 : forall rho, Forall (holds rho) (ss_facts (Tr 2)) -> False. Proof. tr_contra 33%positive 195%positive. Qed.
Lemma contra_tr3 : forall rho, Forall (holds rho) (ss_facts (Tr 3)) -> False. Proof. tr_contra 33%positive 194%positive. Qed.
Lemma contra_tr4 : forall rho, Forall (holds rho) (ss_facts (Tr 4)) -> False. Proof. tr_contra 34%positive 256%positive. Qed.
Lemma contra_tr5 : forall rho, Forall (holds rho) (ss_facts (Tr 5)) -> False. Proof. tr_contra 34%positive 255%positive. Qed.

Lemma trap_contra : forall T, In T Traps -> forall rho, Forall (holds rho) (ss_facts T) -> False.
Proof.
  intros T HT. rewrite Traps_eq in HT. cbn [seq map In] in HT.
  destruct HT as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - exact contra_tr0.
  - exact contra_tr1.
  - exact contra_tr2.
  - exact contra_tr3.
  - exact contra_tr4.
  - exact contra_tr5.
Qed.

(* Computed side conditions. *)
Lemma E1_X1 : entails E1 X1 s_X1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_X1_id : wsub_id_below s_X1 NF = true. Proof. vm_compute. reflexivity. Qed.
Lemma X1_split : apply_xforms X1 X1_xf = Some X1s. Proof. vm_compute. reflexivity. Qed.
Lemma LsB_ent : forallb (fun L => entails L GB (sub_of locsB L) && wsub_id_below (sub_of locsB L) NF) LsB = true.
Proof. vm_compute. reflexivity. Qed.
Lemma LsA_ent : forallb (fun L => entails L GA (sub_of locsA L) && wsub_id_below (sub_of locsA L) NF) LsA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma RJ_rebase : apply_xforms RJ RJ_xf = Some RJr. Proof. vm_compute. reflexivity. Qed.
Lemma RJ_merge : apply_xforms RJr RJm_xf = Some RJm. Proof. vm_compute. reflexivity. Qed.
Lemma RJm_ret : entails RJm P_ret_U s_ret = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_ret_id : wsub_id_below s_ret NF = true. Proof. vm_compute. reflexivity. Qed.

Lemma fr_1 : entails_fr X1s Pre_si_U s1 = Some R1. Proof. vm_compute. reflexivity. Qed.
Lemma fr_B : entails_fr GB Pre_si_U sB = Some RB. Proof. vm_compute. reflexivity. Qed.
Lemma fr_A : entails_fr GA Pre_si_U sA = Some RA. Proof. vm_compute. reflexivity. Qed.
Lemma chk_1 : call_check X1s Pre_si_U s1 R1 Posts_si_U = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_B : call_check GB Pre_si_U sB RB Posts_si_U = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_A : call_check GA Pre_si_U sA RA Posts_si_U = true. Proof. vm_compute. reflexivity. Qed.

(* What the scan_int call lemma needs of a call state, all decided by computation. *)
Definition call_side (C : sstate) (s : wsub) (R : list sobj) : bool :=
  Pos.leb NF (ss_next C) && forallb (sprop_below (ss_next C)) (ss_facts C) &&
  (let T := import_post s NF P_none_U (ss_next C) R in forallb (sprop_below (ss_next T)) (ss_facts T ++ ss_facts C)) &&
  (let T := import_post s NF P_num_U (ss_next C) R in forallb (sprop_below (ss_next T)) (ss_facts T ++ ss_facts C)).
Lemma side_1 : call_side X1s s1 R1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma side_B : call_side GB sB RB = true. Proof. vm_compute. reflexivity. Qed.
Lemma side_A : call_side GA sA RA = true. Proof. vm_compute. reflexivity. Qed.

Lemma facts_transport : forall n rho rho' F,
  agree_below n rho rho' -> forallb (sprop_below n) F = true -> Forall (holds rho) F -> Forall (holds rho') F.
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))).
  exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Lemma call_side_split : forall C s R, call_side C s R = true ->
  Pos.le NF (ss_next C) /\ forallb (sprop_below (ss_next C)) (ss_facts C) = true /\
  (forall P, P = P_none_U \/ P = P_num_U ->
     let T := import_post s NF P (ss_next C) R in forallb (sprop_below (ss_next T)) (ss_facts T ++ ss_facts C) = true).
Proof.
  intros C s R H. unfold call_side in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. split; [apply Pos.leb_le; exact H1|]. split; [exact H2|].
  intros P [->| ->]; assumption.
Qed.

Definition z0 : sv := SLit 0.

Section Safe.
Variable ok : world -> Prop.
Variable K : list event -> Model -> Prop.
Variable rho0 : valuation.
Hypothesis Hok : ok_frame segsU ok K.
Let Gp : valuation -> Prop := fun r => agree_below NF rho0 r.
Let Qs : assn := fun w => SPfam segsU K Gp cuts_pc w \/ LQ segsU K NF rho0 Posts_pc_U w.

Lemma si_call_ok : forall C s R rho,
  entails_fr C Pre_si_U s = Some R -> call_check C Pre_si_U s R Posts_si_U = true -> call_side C s R = true ->
  In (post_cut C s R P_none_U) cuts_pc -> In (post_cut C s R P_num_U) cuts_pc -> Gp rho ->
  triple segsU ok (SP segsU K C rho) Qs.
Proof.
  intros C s R rho He Hchk Hside HinN HinU Hg.
  destruct (call_side_split C s R Hside) as (Hle & Hb & HbT).
  apply triple_facts. intros HF.
  apply (call_sound_P segsU (fun _ => True) ok K K C Pre_si_U s R Posts_si_U Qs rho He Hchk).
  - intros rho1 _. apply scan_int_sum_U. exact Hok.
  - intros ms. exact I.
  - intros L rho' HinL Hag.
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hsp. left.
    pose proof (facts_transport _ _ _ _ Hag Hb HF) as HFC.
    assert (Hg' : Gp rho') by (unfold Gp; eapply agree_below_trans; [exact Hg | eapply agree_below_le; [exact Hle | exact Hag]]).
    destruct HinL as [<-|[<-|[]]]; cbn [lf_state] in Hsp.
    + exists (post_cut C s R P_none_U), rho'. split; [exact HinN|]. split; [exact Hg'|].
      unfold post_cut. apply SP_refacts; [exact Hsp | exact (HbT P_none_U (or_introl eq_refl)) |].
      intros HFT. apply Forall_app. split; [exact HFT | exact HFC].
    + exists (post_cut C s R P_num_U), rho'. split; [exact HinU|]. split; [exact Hg'|].
      unfold post_cut. apply SP_refacts; [exact Hsp | exact (HbT P_num_U (or_intror eq_refl)) |].
      intros HFT. apply Forall_app. split; [exact HFT | exact HFC].
Qed.

Lemma via_entails : forall L T s rho,
  entails L T s = true -> wsub_id_below s NF = true -> Gp rho ->
  (forall rho', Gp rho' -> triple segsU ok (SP segsU K T rho') Qs) ->
  triple segsU ok (SP segsU K L rho) Qs.
Proof.
  intros L T s rho He Hid Hg HT. apply (triple_entails segsU ok K L T s rho Qs He). apply HT.
  unfold Gp. eapply agree_below_trans; [exact Hg | apply rho_sub_agree; exact Hid].
Qed.

Lemma exits_ok : forall E rho, In E exits_pc -> Gp rho -> triple segsU ok (SP segsU K E rho) Qs.
Proof.
  intros E rho HE Hg. unfold exits_pc in HE. rewrite !in_app_iff in HE.
  destruct HE as [[<-|[]]|[HE|[HE|[[<-|[]]|HE]]]].
  - apply (via_entails E1 X1 s_X1 rho E1_X1 s_X1_id Hg). intros rho' Hg'.
    apply (triple_xforms segsU ok K X1_xf rho' X1 X1s Qs X1_split).
    apply (si_call_ok X1s s1 R1 rho' fr_1 chk_1 side_1); [in_nth 1 | in_nth 2 | exact Hg'].
  - pose proof (proj1 (forallb_forall _ _) LsB_ent E HE) as H. apply andb_prop in H as [He Hid].
    apply (via_entails E GB _ rho He Hid Hg). intros rho' Hg'.
    apply (si_call_ok GB sB RB rho' fr_B chk_B side_B); [in_nth 3 | in_nth 4 | exact Hg'].
  - pose proof (proj1 (forallb_forall _ _) LsA_ent E HE) as H. apply andb_prop in H as [He Hid].
    apply (via_entails E GA _ rho He Hid Hg). intros rho' Hg'.
    apply (si_call_ok GA sA RA rho' fr_A chk_A side_A); [in_nth 5 | in_nth 6 | exact Hg'].
  - apply (triple_xforms segsU ok K RJ_xf rho RJ RJr Qs RJ_rebase).
    apply (triple_xforms segsU ok K RJm_xf rho RJr RJm Qs RJ_merge).
    apply (triple_entails segsU ok K RJm P_ret_U s_ret rho Qs RJm_ret).
    apply exit_post; [in_nth 0 |]. eapply agree_below_trans; [exact Hg | apply rho_sub_agree; exact s_ret_id].
  - revert Hg. apply (exit_contra segsU ok K Gp). intros r _ HF. exact (trap_contra E HE r HF).
Qed.
End Safe.

Theorem parse_corner_sum_U : parse_corner_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_pc cutpcs_pc NF cuts_pc exits_pc
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_pc_U) Hok).
  - rewrite cuts_pc_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_pc.
  - intros E rhoE HinE HagE. exact (exits_ok ok K rho Hok E rhoE HinE HagE).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

(* Existence: same graph; cuts and call exits measured by rank alone, returns and error leaves last. *)
Definition vcuts_pc : list vnode :=
  [mkVN Pre_pc_U 250 z0; mkVN W1n 200 z0; mkVN W1u 200 z0; mkVN Bn 150 z0; mkVN Bu 150 z0;
   mkVN An 100 z0; mkVN Au 100 z0].
Definition vexits_pc : list vnode :=
  [mkVN E1 220 z0] ++ map (fun L => mkVN L 180 z0) LsB ++ map (fun L => mkVN L 120 z0) LsA ++
  [mkVN RJ 1 vTop] ++ map (fun T => mkVN T 1 vTop) Traps.

Lemma echeck_pc : check_ecfgI segsU FUEL_pc cutpcs_pc NF vcuts_pc vexits_pc = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma vmeasI_z0 : forall S r rho, vmeasI (mkVN S r z0) rho = 2 ^ 64 * 256 + r.
Proof. intros. unfold vmeasI, z0. cbn [vn_var vn_rank eval]. rewrite lit_unsigned. rewrite Z.mod_0_l by lia. lia. Qed.

Lemma vmeasI_top : forall S r rho, vmeasI (mkVN S r vTop) rho = 256 + r.
Proof. intros. unfold vmeasI, vTop. cbn [vn_var vn_rank eval]. rewrite lit_unsigned. rewrite Z.mod_small by lia. lia. Qed.

Section Ex.
Variable K : list event -> Model -> Prop.
Variable rho0 : valuation.
Let Gp : valuation -> Prop := fun r => agree_below NF rho0 r.
Let Qe (b : Z) : world -> Prop :=
  fun w => SPfamE segsU K (map (to_enodeI Gp) vcuts_pc) b w \/ LQ segsU K NF rho0 Posts_pc_U w.

Lemma si_call_ex : forall C s R rho rT b,
  entails_fr C Pre_si_U s = Some R -> call_check C Pre_si_U s R Posts_si_U = true -> call_side C s R = true ->
  In (mkVN (post_cut C s R P_none_U) rT z0) vcuts_pc -> In (mkVN (post_cut C s R P_num_U) rT z0) vcuts_pc ->
  0 <= rT -> 2 ^ 64 * 256 + rT < b -> Gp rho ->
  etriple segsU (SP segsU K C rho) (Qe b).
Proof.
  intros C s R rho rT b He Hchk Hside HinN HinU Hr Hb' Hg.
  destruct (call_side_split C s R Hside) as (Hle & Hb & HbT).
  apply etriple_facts. intros HF.
  apply (call_complete_P segsU (fun _ => True) K K C Pre_si_U s R Posts_si_U (Qe b) rho He Hchk).
  - intros rho1 _. apply scan_int_sum_ex_U.
  - intros ms. exact I.
  - intros L rho' HinL Hag w Hsp. exists w. split; [apply wsteps_refl|]. left.
    pose proof (facts_transport _ _ _ _ Hag Hb HF) as HFC.
    assert (Hg' : Gp rho') by (unfold Gp; eapply agree_below_trans; [exact Hg | eapply agree_below_le; [exact Hle | exact Hag]]).
    destruct HinL as [<-|[<-|[]]]; cbn [lf_state] in Hsp.
    + exists (to_enodeI Gp (mkVN (post_cut C s R P_none_U) rT z0)), rho'.
      split; [apply in_map; exact HinN|]. split; [exact Hg'|]. split.
      * change (SP segsU K (post_cut C s R P_none_U) rho' w).
        unfold post_cut. apply SP_refacts; [exact Hsp | exact (HbT P_none_U (or_introl eq_refl)) |].
        intros HFT. apply Forall_app. split; [exact HFT | exact HFC].
      * change (0 <= vmeasI (mkVN (post_cut C s R P_none_U) rT z0) rho' /\ vmeasI (mkVN (post_cut C s R P_none_U) rT z0) rho' < b).
        rewrite vmeasI_z0. lia.
    + exists (to_enodeI Gp (mkVN (post_cut C s R P_num_U) rT z0)), rho'.
      split; [apply in_map; exact HinU|]. split; [exact Hg'|]. split.
      * change (SP segsU K (post_cut C s R P_num_U) rho' w).
        unfold post_cut. apply SP_refacts; [exact Hsp | exact (HbT P_num_U (or_intror eq_refl)) |].
        intros HFT. apply Forall_app. split; [exact HFT | exact HFC].
      * change (0 <= vmeasI (mkVN (post_cut C s R P_num_U) rT z0) rho' /\ vmeasI (mkVN (post_cut C s R P_num_U) rT z0) rho' < b).
        rewrite vmeasI_z0. lia.
Qed.

Lemma via_entails_ex : forall L T s rho b,
  entails L T s = true -> wsub_id_below s NF = true -> Gp rho ->
  (forall rho', Gp rho' -> etriple segsU (SP segsU K T rho') (Qe b)) ->
  etriple segsU (SP segsU K L rho) (Qe b).
Proof.
  intros L T s rho b He Hid Hg HT. apply (etriple_entails segsU K L T s rho (Qe b) He). apply HT.
  unfold Gp. eapply agree_below_trans; [exact Hg | apply rho_sub_agree; exact Hid].
Qed.

Lemma exits_ex : forall E rho, In E vexits_pc -> Gp rho ->
  etriple segsU (SP segsU K (vn_state E) rho) (Qe (vmeasI E rho)).
Proof.
  intros E rho HE Hg. unfold vexits_pc in HE. rewrite !in_app_iff in HE.
  destruct HE as [[<-|[]]|[HE|[HE|[[<-|[]]|HE]]]].
  - cbn [vn_state]. rewrite vmeasI_z0.
    apply (via_entails_ex E1 X1 s_X1 rho _ E1_X1 s_X1_id Hg). intros rho' Hg'.
    apply (etriple_xforms segsU K X1_xf rho' X1 X1s _ X1_split).
    apply (si_call_ex X1s s1 R1 rho' 200 _ fr_1 chk_1 side_1); [in_nth 1 | in_nth 2 | lia | lia | exact Hg'].
  - apply in_map_iff in HE as (L & <- & HL). cbn [vn_state]. rewrite vmeasI_z0.
    pose proof (proj1 (forallb_forall _ _) LsB_ent L HL) as H. apply andb_prop in H as [He Hid].
    apply (via_entails_ex L GB _ rho _ He Hid Hg). intros rho' Hg'.
    apply (si_call_ex GB sB RB rho' 150 _ fr_B chk_B side_B); [in_nth 3 | in_nth 4 | lia | lia | exact Hg'].
  - apply in_map_iff in HE as (L & <- & HL). cbn [vn_state]. rewrite vmeasI_z0.
    pose proof (proj1 (forallb_forall _ _) LsA_ent L HL) as H. apply andb_prop in H as [He Hid].
    apply (via_entails_ex L GA _ rho _ He Hid Hg). intros rho' Hg'.
    apply (si_call_ex GA sA RA rho' 100 _ fr_A chk_A side_A); [in_nth 5 | in_nth 6 | lia | lia | exact Hg'].
  - cbn [vn_state]. rewrite vmeasI_top.
    apply (etriple_xforms segsU K RJ_xf rho RJ RJr _ RJ_rebase).
    apply (etriple_xforms segsU K RJm_xf rho RJr RJm _ RJ_merge).
    apply (etriple_entails segsU K RJm P_ret_U s_ret rho _ RJm_ret).
    pose proof (eexit_post_I0 segsU K NF rho0 vcuts_pc Posts_pc_U (mkVN P_ret_U 1 vTop) ltac:(in_nth 0)
                  (rho_sub rho s_ret)) as H.
    rewrite vmeasI_top in H. apply H.
    eapply agree_below_trans; [exact Hg | apply rho_sub_agree; exact s_ret_id].
  - apply in_map_iff in HE as (T & <- & HT). cbn [vn_state].
    revert Hg. apply (eexit_contra segsU K Gp). intros r _ HF. exact (trap_contra T HT r HF).
Qed.
End Ex.

Theorem parse_corner_sum_ex_U : parse_corner_sum_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_pc_U with (vn_state (mkVN Pre_pc_U 250 z0)).
  apply (cfg_complete_autoI segsU FUEL_pc cutpcs_pc NF vcuts_pc vexits_pc
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_pc_U)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_pc.
  - intros E rhoE HinE HgE. exact (exits_ex K rho E rhoE HinE HgE).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
