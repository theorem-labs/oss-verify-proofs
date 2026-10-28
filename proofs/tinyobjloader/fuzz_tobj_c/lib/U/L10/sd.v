From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init UbsanArith.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require Import S_sd.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddrU.

Definition sdU_L1 : Z := 0x183fc.
Definition sdU_Ls : Z := 0x18460.
Definition sdU_Lm : Z := 0x18798.
Definition sdU_Le : Z := 0x188ac.
Definition sdU_Lx : Z := 0x188d4.
Definition sdU_Lp : Z := 0x18984.
Definition sdU_trap : Z := 0x189f8.
Definition FUEL_sdU : nat := 400%nat.

Definition sd_stateU (pc : Z) (regs : list (nat * sv)) (c0 : sv) (facts : list sprop) : sstate :=
  mkSS pc (setregs (cut_regs NF) ([(2%nat, SAlu ALU_ADD (SVar 10) (SLit (-16))); (8%nat, SVar 108); (10%nat, SVar 12);
                                   (11%nat, SD.pB SD.vE); (12%nat, SVar 14)] ++ regs))
    SD.cut_fregs FcsrFrm0 None [SD.O_stk [mkCell (SLit (-8)) 8 (SVar 28)]; SD.O_pp c0; SD.O_txt []; SD.O_out []]
    (facts ++ base_facts_U) SD.NXC false.

Definition v173 : sv := SVar 173.
Definition skipF : list sprop := SD.cur_lt v173 ++ [SPUle SD.v174 (SLit 1)] ++ SD.skip_facts.
Definition cntF : list sprop :=
  [SPUle (SVar 177) v173; SPUle (SVar 178) v173; SPUle (SVar 177) (SLit two26); SPUle (SVar 178) (SLit two26)].

Definition C1_U : sstate :=
  sd_stateU sdU_L1 [(14%nat, SD.pB SD.v172); (13%nat, SLit 32); (15%nat, SLit 9)] (SD.pB SD.vI) (SD.cur_lt SD.v172).
Definition Cs_U : sstate :=
  sd_stateU sdU_Ls [(14%nat, SD.pB v173); (13%nat, SD.v174)] (SD.pB SD.v172) skipF.
Definition Cm_U : sstate :=
  sd_stateU sdU_Lm
    [(14%nat, SD.pB v173); (13%nat, SD.v174); (5%nat, SVar 175); (8%nat, SVar 182); (15%nat, SVar 176);
     (16%nat, SVar 177); (17%nat, SVar 178); (29%nat, SVar 179); (30%nat, SVar 180);
     (31%nat, SAlu ALU_ADD (SD.pB v173) (SLit 1)); (6%nat, SLit 9); (7%nat, SLit 19); (28%nat, SLit 10)]
    (SD.pB SD.v172) (skipF ++ cntF).
Definition Ce_U (es : Z) : sstate :=
  sd_stateU sdU_Le
    [(14%nat, SD.pB v173); (13%nat, SD.v174); (5%nat, SLit es); (6%nat, SVar 181); (15%nat, SVar 176);
     (16%nat, SVar 177); (17%nat, SVar 178); (7%nat, SLit 9); (28%nat, SLit 99999); (29%nat, SLit 10)]
    (SD.pB SD.v172) (skipF ++ cntF ++ [SPUle (SVar 181) (SLit 999999)]).
Definition Cx_U : sstate :=
  sd_stateU sdU_Lx
    [(11%nat, SD.pB v173); (13%nat, SD.v174); (14%nat, SVar 183); (15%nat, SVar 176); (16%nat, SVar 177);
     (17%nat, SVar 178)]
    (SD.pB SD.v172)
    (SD.cur_le v173 ++ [SPUle SD.v174 (SLit 1)] ++ SD.skip_facts ++ cntF ++
     [SPBranch BC_GE (SVar 183) (SLit (-999999)); SPBranch BC_GE (SLit 999999) (SVar 183)]).
Definition Cp_U : sstate :=
  sd_stateU sdU_Lp
    [(11%nat, SD.pB v173); (13%nat, SD.v174); (14%nat, SVar 184); (15%nat, SLit 2); (16%nat, SVar 185)]
    (SD.pB SD.v172) (SD.cur_le v173 ++ [SPUle SD.v174 (SLit 1)] ++ SD.skip_facts).

Definition cutpcs_sdU : list Z := [sdU_L1; sdU_Ls; sdU_Lm; sdU_Le; sdU_Lx; sdU_Lp].
Definition cuts_sdU : list sstate := [Pre_sd_U; C1_U; Cs_U; Cm_U; Ce_U 1; Ce_U (-1); Cx_U; Cp_U].
Definition posts_sdU : list sstate :=
  [P_none_U; P_num_U sdU_ret_nan; P_num_U sdU_ret_num; P_num_U sdU_ret_inf].

Definition leaves_at (C : sstate) (pc : Z) : list sstate :=
  match sym_run segsU FUEL_sdU cutpcs_sdU C true with
  | Some l => filter (fun S => Z.eqb (ss_pc S) pc) (map lf_state l)
  | None => []
  end.

Definition X_t1 : sstate := Eval vm_compute in nth 0 (leaves_at (Ce_U (-1)) sdU_trap) Pre_sd_U.
Definition X_t2 : sstate := Eval vm_compute in nth 1 (leaves_at (Ce_U (-1)) sdU_trap) Pre_sd_U.
Definition X_t3 : sstate := Eval vm_compute in nth 2 (leaves_at (Ce_U (-1)) sdU_trap) Pre_sd_U.

Lemma contra_t1 : forall rho, Forall (holds rho) (ss_facts X_t1) -> False.
Proof.
  intros rho HF. concrete_facts HF.
  pose proof (Forall_pick _ _ 0 _ HF eq_refl) as H0. cbn beta in H0.
  apply (trap_ne_false rho _) in H0; [exact H0|].
  pose proof (Forall_pick _ _ 15 _ HF eq_refl) as H1. cbn beta in H1.
  apply ule_lit' in H1; [lia | unfold M64v; lia].
Qed.
Lemma contra_t2 : forall rho, Forall (holds rho) (ss_facts X_t2) -> False.
Proof.
  intros rho HF. concrete_facts HF.
  pose proof (Forall_pick _ _ 0 _ HF eq_refl) as H0. cbn beta in H0.
  apply (trap_ne_false rho _) in H0; [exact H0|].
  pose proof (Forall_pick _ _ 17 _ HF eq_refl) as H1. cbn beta in H1.
  apply ule_lit' in H1; [lia | unfold M64v; lia].
Qed.
Lemma contra_t3 : forall rho, Forall (holds rho) (ss_facts X_t3) -> False.
Proof.
  intros rho HF. concrete_facts HF.
  pose proof (Forall_pick _ _ 0 _ HF eq_refl) as H0. cbn beta in H0.
  apply (trap_ne_false rho _) in H0; [exact H0|].
  rewrite <- zv_sound. cbn [zv ext_width_ok Z.of_N and_hmask].
  pick_facts HF [3; 17]%nat. zfacts; lia.
Qed.

Definition exits_sdU : list sstate := posts_sdU ++ [X_t1; X_t2; X_t3].

Lemma check_sdU : check_cfg segsU FUEL_sdU cutpcs_sdU NF cuts_sdU exits_sdU = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_sdU_strict : existsb ss_lenient cuts_sdU = false.
Proof. vm_compute. reflexivity. Qed.

Theorem scan_double_sum_U : scan_double_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_sdU cutpcs_sdU NF cuts_sdU exits_sdU
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_sd_U) Hok).
  - rewrite cuts_sdU_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_sdU.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; revert HagE.
    + apply exit_post. in_nth 0.
    + apply exit_post. in_nth 1.
    + apply exit_post. in_nth 2.
    + apply exit_post. in_nth 3.
    + apply (exit_contra segsU ok K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t1 r HF).
    + apply (exit_contra segsU ok K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t2 r HF).
    + apply (exit_contra segsU ok K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t3 r HF).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition Fcp : list sprop :=
  [SPUle (SVar 184) (SLit (2 ^ 30)); SPUle (SAluW ALU_SRA (SVar 184) (SLit 1)) (SLit (2 ^ 30))].
Definition Cp'_U : sstate := add_facts Fcp Cp_U.

Definition varP (e : sv) : sv :=
  SAlu ALU_SUB (SLit (2 ^ 64 - 1)) (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 32 e) (SLit 1)) (SAlu ALU_SLTU (SLit 0) e)).

Definition X_in0 : sstate := Eval vm_compute in nth 0 (leaves_at Cx_U sdU_Lp) Pre_sd_U.
Definition X_in1 : sstate := Eval vm_compute in nth 1 (leaves_at Cx_U sdU_Lp) Pre_sd_U.
Definition X_b0 : sstate := Eval vm_compute in nth 0 (leaves_at Cp'_U sdU_Lp) Pre_sd_U.
Definition X_b1 : sstate := Eval vm_compute in nth 1 (leaves_at Cp'_U sdU_Lp) Pre_sd_U.
Definition s_in0 : wsub := infer_sub NF X_in0 Cp_U.
Definition s_in1 : wsub := infer_sub NF X_in1 Cp_U.
Definition s_b0 : wsub := infer_sub NF X_b0 Cp_U.
Definition s_b1 : wsub := infer_sub NF X_b1 Cp_U.

Definition vcuts_sdU : list vnode :=
  [mkVN Pre_sd_U 20 SD.vI; mkVN C1_U 19 (SVar 172); mkVN Cs_U 18 (SVar 173); mkVN Cm_U 8 (SVar 173);
   mkVN (Ce_U 1) 7 (SVar 173); mkVN (Ce_U (-1)) 7 (SVar 173); mkVN Cx_U 6 (SVar 173);
   mkVN Cp'_U 4 (varP (SVar 184))].
Definition vexits_sdU : list vnode :=
  [mkVN P_none_U 0 vTop; mkVN (P_num_U sdU_ret_nan) 0 vTop; mkVN (P_num_U sdU_ret_num) 0 vTop;
   mkVN (P_num_U sdU_ret_inf) 0 vTop;
   mkVN X_in0 5 (SVar 173); mkVN X_in1 5 (SVar 173); mkVN X_b0 3 (varP (SVar 184)); mkVN X_b1 3 (varP (SVar 184));
   mkVN X_t1 0 vTop; mkVN X_t2 0 vTop; mkVN X_t3 0 vTop].

Lemma echeck_sdU : check_ecfgI segsU FUEL_sdU cutpcs_sdU NF vcuts_sdU vexits_sdU = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma Fcp_of_bound : forall rho', bv_unsigned (rw rho' 184%positive) <= 2 ^ 30 -> Forall (holds rho') Fcp.
Proof.
  intros rho' H. pose proof (urange (rw rho' 184%positive)) as R. unfold Fcp.
  constructor; [|constructor; [|constructor]].
  - cbn [holds]. rewrite eval_var, U_lit. unfold M64v. rewrite Z.mod_small by lia. exact H.
  - cbn [holds]. rewrite U_sraw1_small by (rewrite eval_var; lia). rewrite eval_var, U_lit. unfold M64v.
    rewrite Z.mod_small by lia. apply Z.div_le_upper_bound; lia.
Qed.

Lemma U_varP : forall rho e, bv_unsigned (eval rho (varP e)) =
  2 ^ 64 - 1 - (2 * (bv_unsigned (eval rho e) mod 2 ^ 32) + (if 0 <? bv_unsigned (eval rho e) then 1 else 0)).
Proof.
  intros rho e. unfold varP. rewrite <- zv_sound. cbn [zv ext_width_ok]. rewrite !zv_sound.
  unfold M64v. pose proof (urange (eval rho e)) as R. set (u := bv_unsigned (eval rho e)) in *.
  assert (Hm : 0 <= u mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  change (Z.of_N 32) with 32. change (2 ^ (1 mod 64)) with 2.
  change (0 mod 18446744073709551616) with 0. change ((2 ^ 64 - 1) mod 18446744073709551616) with (2 ^ 64 - 1).
  assert (B : 0 <= (if 0 <? u then 1 else 0) <= 1) by (destruct (0 <? u); lia).
  rewrite (Z.mod_small (u mod 2 ^ 32 * 2)) by lia.
  rewrite (Z.mod_small (u mod 2 ^ 32 * 2 + _)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma varP_sraw_lt : forall rho s, wsub_get s 184%positive = SAluW ALU_SRA (SVar 184) (SLit 1) ->
  2 <= bv_unsigned (rw rho 184%positive) <= 2 ^ 30 ->
  bv_unsigned (eval rho (varP (SVar 184))) < bv_unsigned (eval (rho_sub rho s) (varP (SVar 184))).
Proof.
  intros rho s Hs Hb. rewrite !U_varP.
  change (eval (rho_sub rho s) (SVar 184)) with (rw (rho_sub rho s) 184%positive). cbn [rw rho_sub]. rewrite Hs.
  rewrite U_sraw1_small by (rewrite eval_var; lia). rewrite !eval_var.
  set (u := bv_unsigned (rw rho 184%positive)) in *.
  rewrite (Z.mod_small u) by lia.
  assert (H2 : 1 <= u / 2 <= u) by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
  rewrite (Z.mod_small (u / 2)) by lia.
  replace (0 <? u) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (0 <? u / 2) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (Z.mul_div_le u 2 ltac:(lia)). lia.
Qed.

Lemma eexit_reenter_I_lt : forall K (G : valuation -> Prop) g cuts Q (E C : vnode) F T0 s,
  In C cuts -> vn_state C = add_facts F T0 -> entails (vn_state E) T0 s = true ->
  wsub_id_below s g = true ->
  (forall rho rho', G rho -> agree_below g rho rho' -> G rho') ->
  forallb (sprop_below (ss_next T0)) F = true ->
  (forall rho, G rho -> Forall (holds rho) (ss_facts (vn_state E)) ->
     Forall (holds (rho_sub rho s)) F /\
     bv_unsigned (eval rho (vn_var E)) < bv_unsigned (eval (rho_sub rho s) (vn_var C))) ->
  0 <= vn_rank C < 256 -> 0 <= vn_rank E ->
  forall rho, G rho -> etriple segsU (SP segsU K (vn_state E) rho)
    (fun w => SPfamE segsU K (map (to_enodeI G) cuts) (vmeasI E rho) w \/ Q w).
Proof.
  intros K G g cuts Q E C F T0 s Hin HC He Hid HG Hb HF Hr0 Hr1 rho Hg w Hsp.
  exists w. split; [apply wsteps_refl|]. left.
  destruct (HF rho Hg (SP_facts segsU K (vn_state E) rho w Hsp)) as [HF1 HV].
  exists (to_enodeI G C), (rho_sub rho s). split; [apply in_map; exact Hin|].
  cbn [to_enodeI en_state en_ghost en_meas fst snd]. split.
  - eapply HG; [exact Hg|]. apply rho_sub_agree. exact Hid.
  - split.
    + rewrite HC. eapply SP_entails_sem1; [exact He | exact Hb | intros _; exact HF1 | exact Hsp].
    + unfold vmeasI.
      pose proof (urange (eval (rho_sub rho s) (vn_var C))) as R1.
      pose proof (urange (eval rho (vn_var E))) as R2. nia.
Qed.

Ltac sub184 :=
  cbn [rw rho_sub];
  match goal with |- context [wsub_get ?s 184%positive] =>
    let t := eval vm_compute in (wsub_get s 184%positive) in change (wsub_get s 184%positive) with t end.

Lemma in_var : forall rho rho', holds rho (SPUle (SVar 173) (SLit 1099511627776)) ->
  bv_unsigned (eval rho (SVar 173)) <= bv_unsigned (eval rho' (varP (SVar 184))).
Proof.
  intros rho rho' H. rewrite U_varP. apply ule_lit' in H; [|unfold M64v; lia].
  pose proof (urange (eval rho' (SVar 184))) as R. set (u := bv_unsigned (eval rho' (SVar 184))) in *.
  assert (Hm : 0 <= u mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  destruct (0 <? u); lia.
Qed.

Lemma fcp_in0 : forall rho, Forall (holds rho) (ss_facts X_in0) -> Forall (holds (rho_sub rho s_in0)) Fcp.
Proof.
  intros rho HF. apply Fcp_of_bound. sub184.
  concrete_facts HF. pick_facts HF [1; 12; 13; 14; 15]%nat. zfacts; lia.
Qed.
Lemma fcp_in1 : forall rho, Forall (holds rho) (ss_facts X_in1) -> Forall (holds (rho_sub rho s_in1)) Fcp.
Proof.
  intros rho HF. apply Fcp_of_bound. sub184.
  concrete_facts HF. pick_facts HF [1; 12; 13; 14; 15]%nat. zfacts; lia.
Qed.

Lemma b_bound : forall rho X, Forall (holds rho) (ss_facts X) ->
  nth_error (ss_facts X) 4 = Some (SPNot (SPBranch BC_LTU (SVar 184) (SLit 2))) ->
  nth_error (ss_facts X) 6 = Some (SPUle (SVar 184) (SLit 1073741824)) ->
  2 <= bv_unsigned (rw rho 184%positive) <= 2 ^ 30.
Proof.
  intros rho X HF E4 E6.
  pose proof (Forall_pick _ _ 4 _ HF E4) as F4. pose proof (Forall_pick _ _ 6 _ HF E6) as F6.
  clear HF E4 E6. zfacts; lia.
Qed.

Lemma b_reenter : forall rho s, wsub_get s 184%positive = SAluW ALU_SRA (SVar 184) (SLit 1) ->
  2 <= bv_unsigned (rw rho 184%positive) <= 2 ^ 30 ->
  Forall (holds (rho_sub rho s)) Fcp /\
  bv_unsigned (eval rho (varP (SVar 184))) < bv_unsigned (eval (rho_sub rho s) (varP (SVar 184))).
Proof.
  intros rho s Hs B. split; [|exact (varP_sraw_lt rho s Hs B)].
  apply Fcp_of_bound. cbn [rw rho_sub]. rewrite Hs.
  rewrite U_sraw1_small by (rewrite eval_var; lia). rewrite eval_var.
  apply Z.div_le_upper_bound; lia.
Qed.

Theorem scan_double_sum_ex_U : scan_double_sum_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_sd_U with (vn_state (mkVN Pre_sd_U 20 SD.vI)).
  apply (cfg_complete_autoI segsU FUEL_sdU cutpcs_sdU NF vcuts_sdU vexits_sdU
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_sd_U)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_sdU.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; revert HgE.
    + apply (eexit_post_I0 segsU K NF rho vcuts_sdU Posts_sd_U (mkVN P_none_U 0 vTop)). in_nth 0.
    + apply (eexit_post_I0 segsU K NF rho vcuts_sdU Posts_sd_U (mkVN (P_num_U sdU_ret_nan) 0 vTop)). in_nth 1.
    + apply (eexit_post_I0 segsU K NF rho vcuts_sdU Posts_sd_U (mkVN (P_num_U sdU_ret_num) 0 vTop)). in_nth 2.
    + apply (eexit_post_I0 segsU K NF rho vcuts_sdU Posts_sd_U (mkVN (P_num_U sdU_ret_inf) 0 vTop)). in_nth 3.
    + apply (eexit_reenter_I segsU K (fun r => agree_below NF rho r) NF vcuts_sdU _
               (mkVN X_in0 5 (SVar 173)) (mkVN Cp'_U 4 (varP (SVar 184))) Fcp Cp_U s_in0);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | intros r1 r2 H1 H2; eapply agree_below_trans; eauto | vm_compute; reflexivity | | cbn; lia | cbn; lia].
      intros r _ HF. split; [exact (fcp_in0 r HF)|]. cbn [vn_var vn_state] in *.
      concrete_facts HF. apply in_var. exact (Forall_pick _ _ 5 _ HF eq_refl).
    + apply (eexit_reenter_I segsU K (fun r => agree_below NF rho r) NF vcuts_sdU _
               (mkVN X_in1 5 (SVar 173)) (mkVN Cp'_U 4 (varP (SVar 184))) Fcp Cp_U s_in1);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | intros r1 r2 H1 H2; eapply agree_below_trans; eauto | vm_compute; reflexivity | | cbn; lia | cbn; lia].
      intros r _ HF. split; [exact (fcp_in1 r HF)|]. cbn [vn_var vn_state] in *.
      concrete_facts HF. apply in_var. exact (Forall_pick _ _ 5 _ HF eq_refl).
    + apply (eexit_reenter_I_lt K (fun r => agree_below NF rho r) NF vcuts_sdU _
               (mkVN X_b0 3 (varP (SVar 184))) (mkVN Cp'_U 4 (varP (SVar 184))) Fcp Cp_U s_b0);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | intros r1 r2 H1 H2; eapply agree_below_trans; eauto | vm_compute; reflexivity | | cbn; lia | cbn; lia].
      intros r _ HF. cbn [vn_var vn_state] in *.
      apply (b_reenter r s_b0); [vm_compute; reflexivity|].
      apply (b_bound r X_b0 HF); vm_compute; reflexivity.
    + apply (eexit_reenter_I_lt K (fun r => agree_below NF rho r) NF vcuts_sdU _
               (mkVN X_b1 3 (varP (SVar 184))) (mkVN Cp'_U 4 (varP (SVar 184))) Fcp Cp_U s_b1);
        [in_nth 7 | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | intros r1 r2 H1 H2; eapply agree_below_trans; eauto | vm_compute; reflexivity | | cbn; lia | cbn; lia].
      intros r _ HF. cbn [vn_var vn_state] in *.
      apply (b_reenter r s_b1); [vm_compute; reflexivity|].
      apply (b_bound r X_b1 HF); vm_compute; reflexivity.
    + apply (eexit_contra segsU K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t1 r HF).
    + apply (eexit_contra segsU K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t2 r HF).
    + apply (eexit_contra segsU K (fun r => agree_below NF rho r)). intros r _ HF. exact (contra_t3 r HF).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
