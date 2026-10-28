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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require Import S_aa.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition AL : Z := 16.
Definition aa_open : Z := 0x18fbc.
Definition aa_slow : Z := 0x19004.
Definition aa_K : Z := 0x1901c.
Definition FUEL_aa : nat := 400%nat.
Definition cutpcs_aa : list Z := [aa_open; aa_slow; aa_K; ec_malloc EC_U].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_aa cutpcs_aa S true with Some ls => map lf_state ls | None => [] end.
Definition leaf_k (S : sstate) (k : nat) : sstate := nth k (run_of S) (Pre_aa AL).
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_aa AL end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition PreA : sstate := Pre_aa AL.
Definition ahd : amode := AHead vHD.
Definition X_slow0 : sstate := Eval vm_compute in leaf_k PreA 0.
Definition X_open : sstate := Eval vm_compute in leaf_k PreA 1.
Definition C_open : sstate := Eval vm_compute in open_state X_open vHD.
Definition am_open : amode := AOpen vHD (SVar 100) (SVar 101) [].
Definition X_nofit1 : sstate := Eval vm_compute in leaf_k C_open 0.
Definition X_fit : sstate := Eval vm_compute in leaf_k C_open 1.
Definition X_nofit2 : sstate := Eval vm_compute in leaf_k C_open 2.

Definition C_slow : sstate := Eval vm_compute in
  mkSS aa_slow (setregs (ss_regs X_slow0) [(11%nat, SVar 103); (13%nat, SVar 104); (14%nat, SVar 105); (15%nat, SVar 106); (16%nat, SVar 107)])
    pre_fregs FcsrFrm0 None (ss_objs X_slow0) base_facts 108 false.
Definition X_nofit1c : sstate := Eval vm_compute in drop_last_state X_nofit1 (firstn 3 (ss_objs X_nofit1)).
Definition X_nofit2c : sstate := Eval vm_compute in drop_last_state X_nofit2 (firstn 3 (ss_objs X_nofit2)).
Definition s_nofit1 : wsub := infer_sub 100 X_nofit1c C_slow.
Definition s_nofit2 : wsub := infer_sub 100 X_nofit2c C_slow.

Definition szp : sv := SAlu ALU_ADD vSZ (SAlu ALU_SLTU vSZ (SLit 1)).
Definition vK : sv := SVar 108.
Definition K0 : sstate := Eval vm_compute in leaf_k C_slow 0.
Definition C_K : sstate := Eval vm_compute in
  mkSS aa_K (setregs (ss_regs K0) [(9%nat, vK)]) pre_fregs FcsrFrm0 None (ss_objs K0)
    (SPUle (SAlu ALU_ADD szp (SLit AL)) vK :: base_facts) 109 false.

Definition E_m : sstate := Eval vm_compute in leaf_k C_K 1.
Definition s_m : wsub := (15%positive, vDp) :: infer_sub 10 E_m (Pre_malloc EC_U).
Definition R_m : list sobj := Eval vm_compute in optR (entails_fr E_m (Pre_malloc EC_U) s_m).
Definition vN : positive := 119.
Definition blkN : sv * sv := (SVar vN, SAlu ALU_ADD vK (SLit 32)).
Definition tv_m : list (sv * sv) := blkN :: tv0.
Definition T_mnull : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_null EC_U).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_ok EC_U).
Definition T_mok : sstate := add_facts (tv_facts blkN) T_mok0.

Definition X_push : sstate := Eval vm_compute in leaf_k T_mok 0.
Definition xs_push : list xform := [XSelect [2; 0; 3; 1]%nat; XSplit 3 (SLit 24)].
Definition X_push1 : sstate := Eval vm_compute in optS (apply_xforms X_push xs_push).
Definition X_push2 : sstate := Eval vm_compute in drop_last_state X_push1 (firstn 4 (ss_objs X_push1)).
Definition p_new : sv := SAlu ALU_ADD (SVar vN) (SLit 32).
Definition X_push3 : sstate := Eval vm_compute in carve_state X_push2 p_new vSZ.
Definition am_push : amode := AOpen (SVar vN) vHD vK [(p_new, vSZ)].
Definition s_push : wsub := infer_sub 100 X_push3 (P_ok AL).

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs X_fit) (SLit 0).
Definition fit_add : list sprop :=
  [SPUle (SAlu ALU_ADD vHD (SLit 24)) p_fit;
   SPUle (SAlu ALU_ADD p_fit vSZ) (SAlu ALU_ADD (SAlu ALU_ADD vHD (SLit 32)) (SVar 101));
   SPUle p_fit (SLit hiA);
   SPUle (SAlu ALU_ADD p_fit vSZ) (SLit hiA)].
Definition X_fit3 : sstate := Eval vm_compute in carve_state X_fit p_fit vSZ.
Definition X_fit4 : sstate := add_facts fit_add X_fit3.
Definition am_fit : amode := AOpen vHD (SVar 100) (SVar 101) [(p_fit, vSZ)].
Definition s_fit : wsub := infer_sub 100 X_fit4 (P_ok AL).

Definition curE : sv := SAlu ALU_ADD (SAlu ALU_ADD vHD (SLit 32)) (SVar 102).
Definition pfE : sv := SAlu ALU_AND (SAlu ALU_ADD curE (SLit 15)) (SLit 18446744073709551600).
Definition unewE : sv := SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SUB pfE curE) szp) (SVar 102).
Lemma p_fit_eq : p_fit = pfE.
Proof. reflexivity. Qed.

Ltac msmall_by tac :=
  repeat match goal with
  | Hx : context [?x mod M64v] |- _ =>
      lazymatch x with context [_ mod M64v] => fail | _ => rewrite (Z.mod_small x M64v) in Hx by tac end
  | |- context [?x mod M64v] =>
      lazymatch x with context [_ mod M64v] => fail | _ => rewrite (Z.mod_small x M64v) by tac end
  end.

Lemma fit_vals : forall rho,
  holds rho (SPBranch BC_GEU (SVar 101) unewE) ->
  holds rho (SPUle (SVar 102) (SVar 101)) ->
  holds rho (SPUle (SAlu ALU_ADD (SAlu ALU_ADD vHD (SLit 32)) (SVar 101)) (SLit hiA)) ->
  holds rho (SPUle (SVar 101) (SLit hiA)) ->
  holds rho (SPUle vHD (SLit hiA)) ->
  holds rho (SPUle vSZ (SLit two47)) ->
  exists pd, 0 <= pd <= 15 /\
    bv_unsigned (eval rho pfE) = bv_unsigned (rw rho 15) + 32 + bv_unsigned (rw rho 102) + pd /\
    bv_unsigned (rw rho 15) + 32 + bv_unsigned (rw rho 102) + pd + bv_unsigned (rw rho 13)
      <= bv_unsigned (rw rho 15) + 32 + bv_unsigned (rw rho 101) /\
    bv_unsigned (rw rho 15) + 32 + bv_unsigned (rw rho 101) <= hiA.
Proof.
  intros rho F0 F2 F3 F4 F5 F16.
  apply holds_bgeu in F0. cbn [holds] in F2, F3, F4, F5, F16.
  unfold unewE, pfE, curE, szp, vHD, vSZ, hiA, S_vr.hiA, two47 in *.
  rewrite ?U_add, ?U_sub in *.
  rewrite (U_and_hmask rho _ 18446744073709551600 16 eq_refl) in F0 |- *.
  rewrite ?U_add, ?U_sub, ?U_sltu, ?U_lit, ?eval_var in *.
  pose proof (bv_urange (rw rho 15)) as R15. pose proof (bv_urange (rw rho 101)) as R101.
  pose proof (bv_urange (rw rho 102)) as R102. pose proof (bv_urange (rw rho 13)) as R13.
  set (H := bv_unsigned (rw rho 15)) in *. set (U := bv_unsigned (rw rho 102)) in *.
  set (C := bv_unsigned (rw rho 101)) in *. set (SZ := bv_unsigned (rw rho 13)) in *.
  rewrite ?(Z.mod_small 32 M64v), ?(Z.mod_small 15 M64v), ?(Z.mod_small 1 M64v),
    ?(Z.mod_small 140737479966720 M64v), ?(Z.mod_small (2 ^ 47) M64v) in * by (unfold M64v; lia).
  set (b := if SZ <? 1 then 1 else 0) in *.
  assert (Bnd : 0 <= H <= 140737479966720 /\ 0 <= U <= C /\ C <= 140737479966720 /\ 0 <= SZ <= 2 ^ 47 /\ 0 <= b <= 1)
    by (unfold b; destruct (SZ <? 1); unfold M64v in *; lia).
  clear F2 F4 F5 F16 R15 R101 R102 R13.
  msmall_by ltac:(clear - Bnd; unfold M64v; lia).
  exists (15 - (H + 32 + U + 15) mod 16).
  pose proof (Z.mod_pos_bound (H + 32 + U + 15) 16 ltac:(lia)).
  split; [lia|split; [lia|split; lia]].
Qed.

Definition am_ok : amode := AOpen vH vNX vCAP [(vP, vSZ)].
Definition noextra (o : sobj) : bool := false.

Definition z0 : sv := SLit 0.
Definition cutsE : list aedesc :=
  [(PreA, (tv0, ahd), (100, z0)); (C_open, (tv0, am_open), (90, z0)); (C_slow, (tv0, ahd), (80, z0));
   (C_K, (tv0, ahd), (75, z0)); (T_mnull, (tv0, ahd), (65, z0)); (T_mok, (tv_m, ahd), (65, z0))].
Definition exitsE : list aedesc :=
  [(X_open, (tv0, ahd), (95, z0)); (X_nofit1, (tv0, am_open), (85, z0)); (X_nofit2, (tv0, am_open), (85, z0));
   (X_fit, (tv0, am_open), (0, z0)); (E_m, (tv0, ahd), (70, z0)); (X_push, (tv_m, ahd), (0, z0));
   (P_fail, (tv0, ahd), (0, z0))].

Lemma ejcert_ok : ejcertA segsU NF FUEL_aa cutpcs_aa 100 cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.

Let nA : sstate * (list (sv * sv) * amode) -> jnode := nodeA segsU C_U NF Kc rho0 (P0_aa FB) FB.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U NF Kc rho0 (P0_aa FB) FB tv am.
Let Q : assn := LQP segsU NF rho0 (Posts_aa AL Kc FB).

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
Hypothesis CMALLOC : forall Ai rho1,
  TR (SPJ segsU (J_alloc_pre segsU C_U Ai Kc) (Pre_malloc EC_U) rho1) (LQP segsU NF rho1 (Posts_malloc segsU C_U EC_U Ai Kc)).
Hypothesis REENTER : forall (T : sstate) (tv : list (sv * sv)) (am : amode) (rT : Z) (vT : sv) (rho : valuation) (b : Z),
  In ((T, (tv, am)), (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b ->
  TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis POST : forall (P : sstate) (tv : list (sv * sv)) (am : amode) (rho : valuation) (b : Z),
  In (P, JLGA segsU C_U Kc (P0_aa FB) FB tv am) (Posts_aa AL Kc FB) ->
  TR (SPJ segsU (JGv tv am) P rho) (FAM b).

Let MALLOC := malloc_callAT segsU C_U EC_U NF Kc rho0 (P0_aa FB) FB ML TR TR_facts TR_ex TR_pre TR_callP.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <->
  (r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v)).
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv am rT vT := apply (REENTER T tv am rT vT); [cbn; tauto | lia | first [lia | unfold ameas, ad_rank, ad_var; cbn [fst snd]; apply bound_ge; left; lia]].
Ltac via_ex T tv am rT vT :=
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv am) T r w)); [ | apply TR_exw; intros r; reenter T tv am rT vT ].

Lemma X_P_fail : forall rho b, TR (SPJ segsU (JGv tv0 ahd) P_fail rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_ok : forall rho b, TR (SPJ segsU (JGv tv0 am_ok) (P_ok AL) rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_open_ok : forall rho b, 91 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tv0 ahd) X_open rho) (FAM b).
Proof using ML REENTER TR_exw TR_pre.
  intros rho b Hb. via_ex C_open tv0 am_open 90 z0.
  intros w Hw.
  destruct (JGA_open segsU C_U NF Kc rho0 (P0_aa FB) FB ML TobjJVA.NP_ok_NF tv0 vHD X_open noextra rho w) as (rho' & _ & Hw');
    [vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | vm_compute; reflexivity | exact Hw |].
  - intros o a _ Hx. discriminate Hx.
  - exists rho'. exact Hw'.
Qed.

Ltac nofit X Xc s :=
  intros rho b Hb; via_ex C_slow tv0 ahd 80 z0;
  intros w Hw;
  destruct (JGA_close segsU C_U NF Kc rho0 (P0_aa FB) FB ML tv0 vHD (SVar 100) (SVar 101) (SVar 102) X
              (firstn 3 (ss_objs X)) (nth 3 (ss_objs X) O_D) rho w) as (rho' & _ & Hw');
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |];
  change (drop_last_state X (firstn 3 (ss_objs X))) with Xc in Hw';
  exists (rho_sub rho' s);
  eapply (SPJ_entails_JGA segsU C_U NF Kc rho0 (P0_aa FB) FB ML Xc C_slow s tv0 tv0 ahd ahd);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hw'].
Lemma X_nofit1_ok : forall rho b, 81 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tv0 am_open) X_nofit1 rho) (FAM b).
Proof using ML REENTER TR_exw TR_pre. nofit X_nofit1 X_nofit1c s_nofit1. Qed.
Lemma X_nofit2_ok : forall rho b, 81 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tv0 am_open) X_nofit2 rho) (FAM b).
Proof using ML REENTER TR_exw TR_pre. nofit X_nofit2 X_nofit2c s_nofit2. Qed.

Lemma X_fit_ok : forall rho b, TR (SPJ segsU (JGv tv0 am_open) X_fit rho) (FAM b).
Proof using ML POST TR_exw TR_pre.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0 am_ok) (P_ok AL) r w)); [ | apply TR_exw; intros r; apply X_P_ok ].
  intros w Hw. exists (rho_sub rho s_fit).
  eapply (SPJ_entails_JGA segsU C_U NF Kc rho0 (P0_aa FB) FB ML X_fit4 (P_ok AL) s_fit tv0 tv0 am_fit am_ok);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity |].
  apply SPJ_refacts_J; [| reflexivity |].
  { apply (JGA_carve segsU C_U NF Kc rho0 (P0_aa FB) FB ML TobjJVA.NP_ok_NF tv0 vHD (SVar 100) (SVar 101) p_fit vSZ X_fit noextra rho w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | | | exact Hw].
    - intros o a _ Hx. discriminate Hx.
    - intros HP0 Hav HF. clear - HF. cbv beta. rewrite p_fit_eq. unfold HDR.
      pick_facts HF [0%nat; 2%nat; 3%nat; 4%nat; 5%nat; 16%nat].
      destruct (fit_vals rho ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))
        as (pd & Hpd & Ep & Hle & Hhi).
      unfold vHD, vSZ. rewrite Ep, !eval_var. pose proof (bv_urange (rw rho 102)). lia. }
  intros tr md _ HF. clear - HF. unfold fit_add. rewrite p_fit_eq.
  pick_facts HF [0%nat; 2%nat; 3%nat; 4%nat; 5%nat; 16%nat].
  destruct (fit_vals rho ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))
    as (pd & Hpd & Ep & Hle & Hhi).
  clear - Hpd Ep Hle Hhi.
  pose proof (bv_urange (rw rho 15)). pose proof (bv_urange (rw rho 101)).
  pose proof (bv_urange (rw rho 102)). pose proof (bv_urange (rw rho 13)).
  repeat constructor; apply (proj2 (holds_ule _ _ _)); unfold vHD, vSZ, hiA, S_vr.hiA in *;
    rewrite ?Ep; rewrite ?U_add, ?U_lit, ?eval_var; msmall_by ltac:(unfold M64v; lia); lia.
Qed.

Lemma X_E_m : forall rho, TR (SPJ segsU (JGv tv0 ahd) E_m rho) (FAM (ameas ((E_m, (tv0, ahd)), (70, z0)) rho)).
Proof using CMALLOC ML REENTER TR_callP TR_ex TR_facts TR_pre.
  intros rho.
  apply (MALLOC E_m s_m R_m rho tv0 ahd _ CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT. split.
    + eapply (robjs_check_sound segsU C_U FB Ai rho (ss_facts E_m) tv0 None noextra R_m None rhoM md HM HT HF HN HD HZ);
        [vm_compute; reflexivity | | exact I].
      intros o a _ Hx. discriminate Hx.
    + change (wsub_get s_m 12) with (SAlu ALU_ADD vK (SLit 32)). clear - HF. unfold vK, szp, vSZ.
      pick_facts HF [0%nat; 1%nat]. zfacts; lia.
  - intros rho' _.
    replace (T_after E_m s_m R_m (L_malloc_null EC_U)) with T_mnull by (vm_compute; reflexivity).
    reenter T_mnull tv0 ahd 65 z0.
  - intros rho' _.
    replace (T_after E_m s_m R_m (L_malloc_ok EC_U)) with T_mok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_m) 10) with vN.
    change (wsub_get s_m 12) with (SAlu ALU_ADD vK (SLit 32)).
    eapply TR_pre; [ | reenter T_mok tv_m ahd 65 z0 ].
    intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
    intros tr md HJ HF.
    eapply (JGA_tv_facts segsU C_U NF Kc rho0 (P0_aa FB) FB); [exact HJ | left; reflexivity |].
    eapply (tnz_of_fact rho' (SVar vN)). pick_facts HF [18%nat]. assumption.
Qed.

Lemma X_push_ok : forall rho b, TR (SPJ segsU (JGv tv_m ahd) X_push rho) (FAM b).
Proof using ML POST TR_exw TR_pre.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0 am_ok) (P_ok AL) r w)); [ | apply TR_exw; intros r; apply X_P_ok ].
  intros w Hw.
  pose proof (SPJ_xforms segsU (JGv tv_m ahd) xs_push rho X_push X_push1 w ltac:(vm_compute; reflexivity) Hw) as Hw1.
  destruct (JGA_push_open segsU C_U NF Kc rho0 (P0_aa FB) FB ML tv_m 0%nat blkN vHD vK szp X_push1
              (firstn 3 (ss_objs X_push1)) (nth 3 (ss_objs X_push1) O_D) (nth 4 (ss_objs X_push1) O_D) rho w)
    as (rho1 & _ & Hw2);
    [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | exact Hw1 |].
  change (drop_last_state X_push1 (firstn 3 (ss_objs X_push1) ++ [nth 3 (ss_objs X_push1) O_D])) with X_push2 in Hw2.
  change (remove_nth 0 tv_m) with tv0 in Hw2. change (fst blkN) with (SVar vN) in Hw2.
  exists (rho_sub rho1 s_push).
  eapply (SPJ_entails_JGA segsU C_U NF Kc rho0 (P0_aa FB) FB ML X_push3 (P_ok AL) s_push tv0 tv0 am_push am_ok);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity |].
  apply (JGA_carve segsU C_U NF Kc rho0 (P0_aa FB) FB ML TobjJVA.NP_ok_NF tv0 (SVar vN) vHD vK p_new vSZ X_push2 noextra rho1 w);
    [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | | | exact Hw2].
  - intros o a _ Hx. discriminate Hx.
  - intros HP0 Hav HF. clear - HF. cbv beta. unfold p_new, vHD, vSZ, vK, vN, HDR, szp.
    pick_facts HF [0%nat; 1%nat; 2%nat; 3%nat; 6%nat; 14%nat]. zfacts; lia.
Qed.

Lemma exits_okT : forall X tvX amX rvX rho, In ((X, (tvX, amX)), rvX) exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas ((X, (tvX, amX)), rvX) rho)).
Proof using CMALLOC ML POST REENTER TR_callP TR_ex TR_exw TR_facts TR_pre.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; injection H as <- <- <- <-;
    unfold ameas, ad_rank, ad_var; cbn [fst snd].
  - apply X_open_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_nofit1_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_nofit2_ok. pose proof (urange (eval rho z0)). lia.
  - apply X_fit_ok.
  - apply X_E_m.
  - apply X_push_ok.
  - apply X_P_fail.
Qed.
End SumT.

Section Safety.
Hypothesis MC : malloc_contracts segsU C_U EC_U.

Theorem aa16_sum_S : triple segsU ok (SPJ segsU (JGA_pre segsU C_U Kc (P0_aa FB) FB tv0 ahd) PreA rho0) Q.
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segsU C_U NF Kc rho0 (P0_aa FB) FB ML FUEL_aa cutpcs_aa 100 cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nA (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (call_soundP segsU ok)).
       - intros Ai rho1. apply (mc_malloc _ _ _ MC). exact HS.
       - intros T tv am rT vT rho b Hin _ _. exact (reenter_cutGAE segsU C_U NF Kc rho0 (P0_aa FB) FB ok cutsE T tv am (rT, vT) Q rho Hin).
       - intros P tv am rho b Hin. apply (exit_postGA segsU C_U NF Kc (P0_aa FB) FB ok rho0 tv am (Posts_aa AL Kc FB) P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.

Theorem aa16_sum_E : etriple segsU (SPJ segsU (JGA_pre segsU C_U Kc (P0_aa FB) FB tv0 ahd) PreA rho0) Q.
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segsU C_U NF Kc rho0 (P0_aa FB) FB ML FUEL_aa cutpcs_aa 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U NF Kc rho0 (P0_aa FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (call_completeP segsU)).
       - intros Ai rho1. apply (mcx_malloc _ _ _ MCX). exact Hvi.
       - intros T tv am rT vT rho b Hin H0 Hb. apply (ereenter_cutAE segsU C_U NF Kc rho0 (P0_aa FB) FB cutsE T tv am (rT, vT) Q b rho Hin).
         unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv am rho b Hin. apply (eexit_postGA segsU C_U NF Kc (P0_aa FB) FB rho0 tv am (Posts_aa AL Kc FB) P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
