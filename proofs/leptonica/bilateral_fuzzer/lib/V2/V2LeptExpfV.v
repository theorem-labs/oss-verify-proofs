From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec SeqExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV FPStepsB Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib DitherLoop LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_leptB4_expf.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptExpf.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import ExpfModelB.
Import ListNotations.
Open Scope bv_scope.

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition mk_lit (n : N) (z : Z) : bv n := Z_to_bv n z.

Local Ltac canon1 t :=
  match t with
  | context C [@BV ?n ?z _] => let t' := context C [mk_lit n z] in canon1 t'
  | _ => t
  end.

Local Ltac canon2 t :=
  match t with
  | context C [mk_lit ?n ?z] => let t' := context C [@BV n z (I <: BvWf n z)] in canon2 t'
  | _ => t
  end.

Local Ltac canon t := let t1 := canon1 t in canon2 t1.

Local Ltac here F D :=
  lazymatch goal with |- reach ?sg (@mkst _ _ ?p _ _) _ =>
    let f := eval vm_compute in (fetch_word sg p) in
    lazymatch f with Some ?w =>
      assert (F : fetch_word sg p = Some w) by (vm_cast_no_check (eq_refl (Some w)));
      let d0 := eval vm_compute in (decode_any w) in
      let d := canon d0 in
      assert (D : decode_any w = d) by vm_refl_bv
    end
  end.

Local Ltac pcn :=
  lazymatch goal with |- reach _ (@mkst _ _ ?p _ _) _ =>
    lazymatch p with
    | Z_to_bv 64 _ => idtac
    | _ => tryif check_closed_term p then
             (let z := eval vm_compute in (bv_unsigned p) in
              let E := fresh "E" in
              assert (E : p = Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity);
              rewrite E; clear E)
           else idtac
    end
  end.

Local Ltac lits :=
  repeat match goal with
  | |- context [bv_signed (@BV ?n ?z ?pf)] =>
      let v := eval vm_compute in (bv_signed (@BV n z pf)) in change (bv_signed (@BV n z pf)) with v
  | |- context [bv_unsigned (@BV ?n ?z ?pf)] => change (bv_unsigned (@BV n z pf)) with z
  end.

Local Ltac cl_ld :=
  repeat match goal with |- context [bv_extract ?s ?l (le_bytes_to_word ?bs)] =>
    let t := constr:(bv_extract s l (le_bytes_to_word bs)) in
    check_closed_term t;
    let z := eval vm_compute in (bv_unsigned t) in
    replace t with (Z_to_bv l z) by (apply bv_eq; vm_compute; reflexivity)
  end.

Local Ltac disj := first [ (repeat split; reflexivity) | (left; disj) | (right; disj) ].

Local Ltac gsimp :=
  repeat match goal with
  | |- context [getr (regupd ?R ?r ?v) ?r'] =>
      first [ (let E := fresh "E" in
               assert (E : getr (regupd R r v) r' = v) by (replace r' with r by bveq; apply getr_same; reg_neq_tac);
               rewrite E; clear E)
            | (let E := fresh "E" in
               assert (E : getr (regupd R r v) r' = getr R r') by (apply getr_other; reg_neq_tac);
               rewrite E; clear E) ]
  | |- context [getr ?R ?r] =>
      lazymatch r with @BV _ _ _ =>
        let b := eval vm_compute in (bv_eqb r (Z_to_bv 5 0)) in
        lazymatch b with true => change (getr R r) with (Z_to_bv 64 0) end
      end
  end.

Local Ltac rd_ro HRO :=
  gsimp; lits;
  lazymatch goal with |- rdn ?sg ?mm ?a ?n = Some _ =>
    let z := eval vm_compute in (bv_unsigned a) in
    let E := fresh "E" in
    assert (E : a = Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity); rewrite E; clear E;
    let r := eval vm_compute in (rdn sg (fun _ => None) (Z_to_bv 64 z) n) in
    lazymatch r with Some ?bs =>
      transitivity (Some bs);
      [ rewrite (rdn_img sg mm z n _ _ HRO) by lia; vm_cast_no_check (eq_refl r) | reflexivity ]
    end
  end.

Local Ltac rs FZ HRO :=
  let F := fresh "F" in let D := fresh "D" in
  here F D;
  eapply reach_step; [ reflexivity |
    lazymatch type of D with
    | _ = Some (OpImm ALU_ADD _ _ _, _) => eapply step_addi; [exact F | reflexivity | exact D]
    | _ = Some (OpImm ALU_AND _ _ _, _) => eapply step_andi; [exact F | reflexivity | exact D]
    | _ = Some (ShiftImm ALU_SLL _ _ _, _) => eapply step_slli; [exact F | reflexivity | exact D]
    | _ = Some (ShiftImm ALU_SRL _ _ _, _) => eapply PropExec.step_srli; [exact F | reflexivity | exact D]
    | _ = Some (Op ALU_ADD _ _ _, _) => eapply step_add; [exact F | reflexivity | exact D]
    | _ = Some (Auipc _ _, _) => eapply step_auipc; [exact F | reflexivity | exact D]
    | _ = Some (Lui _ _, _) => eapply step_lui; [exact F | reflexivity | exact D]
    | _ = Some (Jal _ _, _) => eapply step_jal_x0; [exact F | reflexivity | exact D]
    | _ = Some (Jalr _ _ _, _) => eapply step_jalr_gen; [exact F | reflexivity | exact D]
    | _ = Some (Fmv FMV_X_F FMT_S _ _, _) => eapply fp_step_fmv_x_w; [exact F | reflexivity | exact D]
    | _ = Some (Fmv FMV_X_F FMT_D _ _, _) => eapply fp_step_fmv_x_d; [exact F | reflexivity | exact D]
    | _ = Some (Fmv FMV_F_X FMT_D _ _, _) => eapply fp_step_fmv_d_x; [exact F | reflexivity | exact D]
    | _ = Some (Fmv FMV_F_X FMT_S _ _, _) => eapply fp_step_fmv_w_x; [exact F | reflexivity | exact D]
    | _ = Some (Fclass _ _ _, _) => eapply fp_step_fclass; [exact F | reflexivity | exact D]
    | _ = Some (Fsgnj _ _ _ _ _, _) => eapply fpv_step_fsgnj; [exact F | reflexivity | exact D]
    | _ = Some (Fcmp _ _ _ _ _, _) => eapply fpv_step_fcmp; [exact F | reflexivity | exact D]
    | _ = Some (FLoad FMT_D _ _ _, _) => eapply fp_step_fld; [exact F | reflexivity | exact D | reflexivity | rd_ro HRO]
    | _ = Some (FLoad FMT_S _ _ _, _) => eapply fp_step_flw; [exact F | reflexivity | exact D | reflexivity | rd_ro HRO]
    | _ = Some (Fari _ _ _ _ _ _, _) =>
        eapply fpv_step_fari; [exact F | reflexivity | exact D | exact FZ | first [exact fpv_rm_dyn | reflexivity]]
    | _ = Some (Fma _ _ _ _ _ _ _, _) =>
        eapply fpv_step_fma; [exact F | reflexivity | exact D | exact FZ | first [exact fpv_rm_dyn | reflexivity]]
    | _ = Some (Fcvt _ _ _ _ _, _) =>
        first [ (eapply fpv_step_fcvt_f_of_f; [exact F | reflexivity | exact D | disj | disj | exact FZ | first [exact fpv_rm_dyn | reflexivity]])
              | (eapply fpv_step_fcvt_f_of_x; [exact F | reflexivity | exact D | disj | disj | exact FZ | first [exact fpv_rm_dyn | reflexivity]]) ]
    end | ];
  clear F D.

Local Ltac fsimp := cbn [fp_regs fp_csr]; unfold fpv_sgnj; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_read_D_same | rewrite fpv_read_other by reg_neq_tac
               | rewrite fpv_get_same | rewrite fpv_get_other by reg_neq_tac ].

Local Ltac b10 FR H10 :=
  lazymatch type of H10 with
  | reg_get FR ?r0 = nan_box ?w =>
    repeat match goal with
    | |- context [fpv_read FR FMT_S ?r] =>
        let E := fresh "E" in
        assert (E : fpv_read FR FMT_S r = bv_unsigned w)
          by (unfold fpv_read; replace r with r0 by bveq; rewrite H10, fpv_unbox_box; reflexivity);
        rewrite E; clear E
    | |- context [reg_get FR ?r] =>
        let E := fresh "E" in
        assert (E : reg_get FR r = nan_box w) by (replace r with r0 by bveq; exact H10);
        rewrite E; clear E
    end
  | _ => idtac
  end; rewrite ?fpv_low32_box, ?fpv_unbox_box.

Local Ltac csgen FZ :=
  repeat lazymatch goal with |- context [mkFP _ (fpv_acc ?c ?fl)] =>
    let H := fresh "FZ" in
    pose proof (fpv_frm_acc c fl FZ) as H;
    let c' := fresh "cs" in
    set (c' := fpv_acc c fl) in *; clearbody c'; clear FZ; rename H into FZ
  end.

Local Ltac wcl :=
  repeat match goal with
  | |- context [v_auipc ?a ?b] => wlit_closed (v_auipc a b)
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_lui ?a] => wlit_closed (v_lui a)
  | |- context [PropExec.v_add ?a ?b] => wlit_closed (PropExec.v_add a b)
  end.

Local Ltac nrm FZ FR H10 :=
  cbn [fp_regs fp_csr]; reduce_bv_eqb_ifs; pcn; fsimp; b10 FR H10; gsimp; lits; cl_ld; wcl; csgen FZ.

Local Ltac rbr tac :=
  let F := fresh "F" in let D := fresh "D" in
  here F D;
  eapply reach_step; [ reflexivity |
    first [ (eapply step_beq_tk; [exact F | reflexivity | exact D | gsimp; lits; tac])
          | (eapply step_beq_ft; [exact F | reflexivity | exact D | gsimp; lits; tac])
          | (eapply step_bgeu_tk; [exact F | reflexivity | exact D | gsimp; lits; tac])
          | (eapply step_bgeu_ft; [exact F | reflexivity | exact D | gsimp; lits; tac]) ] | ];
  clear F D.

Local Ltac hreg H :=
  lazymatch type of H with getr ?R ?r0 = ?v =>
    repeat match goal with |- context [getr R ?r] =>
      let E := fresh "E" in
      assert (E : getr R r = v) by (replace r with r0 by bveq; exact H);
      rewrite E; clear E
    end
  end.

Local Ltac notin :=
  let E := fresh "E" in
  intro E; cbn [In] in E;
  repeat (destruct E as [E|E]; [apply bv_eq in E; vm_compute in E; discriminate E|]);
  exact E.

Local Ltac tab_case :=
  lazymatch goal with |- exists bs, rdn ?sg ?mm ?a ?n = Some bs /\ _ =>
    let r := eval vm_compute in (rdn sg mm a n) in
    lazymatch r with Some ?bs => exists bs; split; [vm_cast_no_check (eq_refl r) | vm_compute; reflexivity] end
  end.

Lemma tab_ld : forall (m : word -> option byte) (X : word),
  (forall j, (0x133a0 <= j < 0x134e8)%Z -> m (Z_to_bv 64 j) = None) ->
  exists bs, rdn SEGS m (v_addi (PropExec.v_add (Z_to_bv 64 0x133a0) (PropExec.v_slli (PropExec.v_andi X 31) 3)) 0) 8 = Some bs /\
    bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (nth (Z.to_nat (bv_unsigned (PropExec.v_andi X 31))) ExpfModelB.EXPF_TAB 0%Z)).
Proof.
  intros m X HRO.
  rewrite expf_tab_addr.
  pose proof (expf_idx_range X) as HR.
  generalize dependent (bv_unsigned (PropExec.v_andi X 31)). intros i HR.
  rewrite (rdn_img SEGS m (V2LeptExpf.EXPF_TAB + 8 * i) 8 0x133a0 0x134e8 HRO) by (unfold V2LeptExpf.EXPF_TAB; lia).
  assert (E : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
               i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
               i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31)%Z) by lia.
  repeat destruct E as [E | E]; subst i; unfold V2LeptExpf.EXPF_TAB; tab_case.
Qed.

Lemma get_same_eq : forall (fr : bvmap 5 word) (r r' : reg) v, r' = r -> reg_get (bvmap_set r v fr) r' = v.
Proof. intros fr r r' v E. subst r'. apply fpv_get_same. Qed.

Local Ltac agree_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  repeat (rewrite getr_other by (let E := fresh "E" in intro E; apply Hr; subst r; repeat first [ (left; bveq) | right ]));
  reflexivity.

Local Ltac ret_pc HRA HRET :=
  lazymatch type of HRA with getr ?R ?r0 = ?rt =>
  lazymatch goal with |- context [jalr_tgt (getr R ?r) ?i] =>
    let E := fresh "E" in
    assert (E : jalr_tgt (getr R r) i = rt) by (replace r with r0 by bveq; rewrite HRA; exact HRET);
    rewrite E; clear E
  end end.

Local Ltac agree2 AG :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  rewrite AG by (let E := fresh "E" in intro E; apply Hr; cbn [In] in E |- *; tauto);
  repeat (rewrite getr_other by (let E := fresh "E" in intro E; apply Hr; subst r; repeat first [ (left; bveq) | right ]));
  reflexivity.

Local Ltac xaddr := gsimp; lits; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia.

Local Ltac xsok SOK := eapply store_ok_sub; [| exact SOK | |]; rewrite ?u_Z2bv by lia; lia.

Local Ltac xrd := apply rdn_wbytes_hit; rewrite u_Z2bv by lia; rewrite length_Z_to_le_bytes; lia.

Section Segs.
Variable rom : word -> option byte.

Definition xpost (V : Z) (fr regs : bvmap 5 word) (m : word -> option byte) (s : Z) (ret : word) (fin : machine_state) : Prop :=
  exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' ret M' rom /\ frm_zero cs' /\
    (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr r) /\
    reg_get fr' (10%bv : reg) = nan_box (Z_to_bv 32 V) /\
    regs_agree (fun r => In r [2; 11]%list) regs regs' /\ getr regs' 2 = Z_to_bv 64 s /\ rinv [((s - 16)%Z, 16%Z)] m M'.

Local Ltac xflow_tac :=
  intros fr cs regs m s ret FZ HRET HRA HSP HA0 HS SOK;
  do 4 (rs FZ HSP; nrm FZ fr HA0);
  rbr ltac:(hreg HA0; reflexivity); nrm FZ fr HA0;
  rs FZ HSP; nrm FZ fr HA0; hreg HSP;
  replace (v_addi (Z_to_bv 64 s) (-16)) with (Z_to_bv 64 (s - 16)) by (unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia);
  (let F := fresh "F" in let D := fresh "D" in here F D;
   eapply reach_step; [reflexivity | eapply fp_step_fsw with (a := Z_to_bv 64 (s - 4)); [exact F | reflexivity | exact D | xaddr | xsok SOK] | ];
   clear F D);
  nrm FZ fr HA0;
  (let F := fresh "F" in let D := fresh "D" in here F D;
   eapply reach_step; [reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 (s - 4)); [exact F | reflexivity | exact D | xaddr | xrd] | ];
   clear F D);
  nrm FZ fr HA0;
  rs FZ HSP; nrm FZ fr HA0;
  rs FZ HSP; nrm FZ fr HA0;
  replace (v_addi (Z_to_bv 64 (s - 16)) 16) with (Z_to_bv 64 s) by (unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia);
  rs FZ HSP; nrm FZ fr HA0;
  ret_pc HRA HRET;
  apply reach_done; unfold xpost;
  do 4 eexists; split; [reflexivity|];
  split; [exact FZ|];
  split; [intros r Hr; fs_tac Hr|];
  split; [rewrite get_same_eq by bveq; apply bv_eq; vm_compute; reflexivity|];
  split; [agree_tac|];
  split; [gsimp; reflexivity|];
  eapply rinv_wbytes;
  [ apply rinv_refl | rewrite length_Z_to_le_bytes; reflexivity | lia | lia
  | exists ((s - 16)%Z, 16%Z); split; [left; reflexivity | cbn [fst snd]; lia] ].

Lemma expf_oflowV : forall fr cs regs m s ret,
  frm_zero cs -> ret_ok ret -> getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 0 ->
  (16 <= s < 2 ^ 63)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3dcb8) m rom) (xpost EXPF_OFLOW fr regs m s ret).
Proof. xflow_tac. Qed.

Lemma expf_uflowV : forall fr cs regs m s ret,
  frm_zero cs -> ret_ok ret -> getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 0 ->
  (16 <= s < 2 ^ 63)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3dce8) m rom) (xpost EXPF_UFLOW fr regs m s ret).
Proof. xflow_tac. Qed.

Definition mpost (w : bv 32) (fr : bvmap 5 word) (regs : bvmap 5 word) (m : word -> option byte) (ret : word) (fin : machine_state) : Prop :=
  exists fr' cs' regs', fin = @mkst (mkFP fr' cs') regs' ret m rom /\ frm_zero cs' /\
    (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr r) /\
    reg_get fr' (10%bv : reg) = nan_box (Z_to_bv 32 (expf_main (bv_unsigned w))) /\
    regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.

Lemma expf_mainV : forall fr cs regs m (ret : word) (w : bv 32),
  frm_zero cs -> ret_ok ret -> getr regs 1 = ret -> reg_get fr (10%bv : reg) = nan_box w ->
  (forall j, (0x133a0 <= j < 0x134e8)%Z -> m (Z_to_bv 64 j) = None) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3dbf0) m rom) (mpost w fr regs m ret).
Proof.
  intros fr cs regs m ret w FZ HRET HRA H10 HRO.
  do 19 (rs FZ HRO; nrm FZ fr H10).
  lazymatch goal with |- context [PropExec.v_andi ?X 31] => destruct (tab_ld m X HRO) as (bs & RB & VB) end.
  let F := fresh "F" in let D := fresh "D" in here F D;
  eapply reach_step; [reflexivity | eapply step_ld; [exact F | reflexivity | exact D | gsimp; lits; exact RB | exact VB] | ].
  clear RB VB. nrm FZ fr H10.
  do 9 (rs FZ HRO; nrm FZ fr H10).
  ret_pc HRA HRET.
  apply reach_done. unfold mpost.
  do 3 eexists. split; [reflexivity|].
  split; [exact FZ|].
  split; [intros r Hr; fs_tac Hr|].
  split; [|agree_tac].
  rewrite get_same_eq by bveq.
  f_equal.
Qed.

Definition expf_postV (w : bv 32) (fr : bvmap 5 word) (regs : bvmap 5 word) (m : word -> option byte) (s : Z) (ret : word) (fin : machine_state) : Prop :=
  exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' ret M' rom /\ frm_zero cs' /\
    (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr r) /\
    reg_get fr' (10%bv : reg) = nan_box (Z_to_bv 32 (expf_model w)) /\
    regs_agree (fun r => In r [2; 10; 11; 12]%list) regs regs' /\ getr regs' 2 = Z_to_bv 64 s /\ rinv [((s - 16)%Z, 16%Z)] m M'.

Local Ltac to_main FZ HRET HRA H10 HRO HSP m ret w :=
  eapply reach_weaken;
  [| eapply (expf_mainV _ _ _ m ret w);
     [exact FZ | exact HRET | gsimp; exact HRA | rewrite ?fpv_get_other by reg_neq_tac; exact H10 | exact HRO]];
  let fin := fresh "fin" in let fr' := fresh "fr'" in let cs' := fresh "cs'" in let regs' := fresh "regs'" in
  let FZ' := fresh "FZ'" in let FS := fresh "FS" in let V := fresh "V" in let AG := fresh "AG" in
  intros fin (fr' & cs' & regs' & -> & FZ' & FS & V & AG); unfold regs_agree in AG;
  exists fr', cs', regs', m; split; [reflexivity|]; split; [exact FZ'|];
  split; [let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite FS by exact Hr; fs_tac Hr|];
  split; [rewrite V|];
  [| split; [agree2 AG|]; split; [rewrite AG by notin; gsimp; exact HSP | apply rinv_refl]].

Local Ltac to_xflow L FZ HRET HRA HSP HS SOK :=
  eapply reach_weaken;
  [| apply L; [exact FZ | exact HRET | gsimp; exact HRA | gsimp; exact HSP | gsimp; reflexivity | exact HS | exact SOK]];
  let fin := fresh "fin" in let fr' := fresh "fr'" in let cs' := fresh "cs'" in let regs' := fresh "regs'" in
  let M' := fresh "M'" in let FZ' := fresh "FZ'" in let FS := fresh "FS" in let V := fresh "V" in
  let AG := fresh "AG" in let SP := fresh "SP" in let RI := fresh "RI" in
  intros fin (fr' & cs' & regs' & M' & -> & FZ' & FS & V & AG & SP & RI); unfold regs_agree in AG;
  exists fr', cs', regs', M'; split; [reflexivity|]; split; [exact FZ'|];
  split; [let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite FS by exact Hr; fs_tac Hr|];
  split; [rewrite V|];
  [| split; [agree2 AG|]; split; [exact SP | exact RI]].

Local Ltac to_ret FZ HRA HRET HSP :=
  ret_pc HRA HRET; apply reach_done; unfold expf_postV;
  do 4 eexists; split; [reflexivity|]; split; [exact FZ|];
  split; [let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; fs_tac Hr|];
  split; [rewrite get_same_eq by bveq|];
  [| split; [agree_tac|]; split; [gsimp; exact HSP | apply rinv_refl]].

Lemma expf_runV : forall (fx : FPState) regs m (s : Z) (ret : word) (w : bv 32),
  frm_zero (@fp_csr fx) -> ret_ok ret -> getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 s ->
  reg_get (@fp_regs fx) (10%bv : reg) = nan_box w ->
  (16 <= s < 2 ^ 63)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
  (forall j, (0x133a0 <= j < 0x134e8)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (0x127b4 <= j < 0x127c0)%Z -> m (Z_to_bv 64 j) = None) ->
  reach SEGS (@mkst fx regs (0x3dbdc : word) m rom) (expf_postV w (@fp_regs fx) regs m s ret).
Proof.
  intros fx regs m s ret w FZ HRET HRA HSP H10 HS SOK HRO1 HRO2.
  destruct fx as [fr cs]. cbn [fp_regs fp_csr] in FZ, H10 |- *.
  replace (0x3dbdc : word) with (Z_to_bv 64 0x3dbdc) by bveq.
  do 4 (rs FZ HRO1; nrm FZ fr H10).
  destruct (c_ltu (v_srli (v_slli (sext 64 w) 33) 53) (Z_to_bv 64 1067)) eqn:HC.
  - rbr ltac:(exact HC). nrm FZ fr H10.
    to_main FZ HRET HRA H10 HRO1 HSP m ret w.
    cbv beta zeta delta [expf_model]; rewrite HC; reflexivity.
  - rbr ltac:(exact HC). nrm FZ fr H10.
    do 2 (rs FZ HRO1; nrm FZ fr H10).
    destruct (c_eq (v_andi (Z_to_bv 64 (fp_class ES (bv_unsigned w))) 1) (Z_to_bv 64 0)) eqn:HK.
    + rbr ltac:(exact HK). nrm FZ fr H10.
      rs FZ HRO1; nrm FZ fr H10.
      destruct (c_ltu (v_srli (v_slli (sext 64 w) 33) 53) (Z_to_bv 64 2040)) eqn:HT.
      * rbr ltac:(exact HT). nrm FZ fr H10.
        do 3 (rs FZ HRO2; nrm FZ fr H10).
        destruct (c_eq (if fst (fp_lt ES EXPF_HI (bv_unsigned w)) then Z_to_bv 64 1 else Z_to_bv 64 0) (Z_to_bv 64 0)) eqn:HH.
        -- rbr ltac:(exact HH). nrm FZ fr H10.
           do 3 (rs FZ HRO2; nrm FZ fr H10).
           destruct (c_eq (if fst (fp_lt ES (bv_unsigned w) EXPF_LO) then Z_to_bv 64 1 else Z_to_bv 64 0) (Z_to_bv 64 0)) eqn:HL.
           ++ rbr ltac:(exact HL). nrm FZ fr H10.
              to_main FZ HRET HRA H10 HRO1 HSP m ret w.
              cbv beta zeta delta [expf_model]; rewrite HC, HK, HT, HH, HL; reflexivity.
           ++ rbr ltac:(exact HL). nrm FZ fr H10.
              do 2 (rs FZ HRO2; nrm FZ fr H10).
              to_xflow expf_uflowV FZ HRET HRA HSP HS SOK.
              cbv beta zeta delta [expf_model]; rewrite HC, HK, HT, HH, HL; reflexivity.
        -- rbr ltac:(exact HH). nrm FZ fr H10.
           do 2 (rs FZ HRO2; nrm FZ fr H10).
           to_xflow expf_oflowV FZ HRET HRA HSP HS SOK.
           cbv beta zeta delta [expf_model]; rewrite HC, HK, HT, HH; reflexivity.
      * rbr ltac:(exact HT). nrm FZ fr H10.
        do 2 (rs FZ HRO1; nrm FZ fr H10).
        to_ret FZ HRA HRET HSP.
        cbv beta zeta delta [expf_model]; rewrite HC, HK, HT; reflexivity.
    + rbr ltac:(exact HK). nrm FZ fr H10.
      do 2 (rs FZ HRO1; nrm FZ fr H10).
      to_ret FZ HRA HRET HSP.
      cbv beta zeta delta [expf_model]; rewrite HC, HK; cbv iota.
      apply bv_eq; vm_compute; reflexivity.
Qed.
End Segs.
