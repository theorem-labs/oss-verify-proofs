From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare.
(* the package's own imports *)
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Lemma reg_neq_of_eqb : forall a b : reg, bv_eqb a b = false -> a <> b.
Proof. intros a b H E. subst b. rewrite bv_eqb_refl in H. discriminate H. Qed.
Ltac getr_proof X r :=
  lazymatch X with
  | regupd ?Y ?rd ?v =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in
             uconstr:(getr_same Y r v (reg_neq_of_eqb r (0%bv) (@eq_refl bool false)))
      | _ => let p := getr_proof Y r in
             uconstr:(eq_trans (getr_other Y rd v r (reg_neq_of_eqb r rd (@eq_refl bool false))) p)
      end
  | _ => uconstr:(@eq_refl word (getr X r))
  end.
Fixpoint regupds (R : bvmap 5 word) (l : list (reg * word)) : bvmap 5 word :=
  match l with
  | nil => R
  | cons p l' => regupd (regupds R l') (fst p) (snd p)
  end.
Fixpoint reg_lookup (r : reg) (l : list (reg * word)) : option word :=
  match l with
  | nil => None
  | cons p l' => if bv_eqb r (fst p) then Some (snd p) else reg_lookup r l'
  end.
Lemma reg_eq_of_eqb : forall a b : reg, bv_eqb a b = true -> a = b.
Proof. intros a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.
Lemma getr_regupds_hit : forall R l r v, bv_eqb r 0 = false -> reg_lookup r l = Some v -> getr (regupds R l) r = v.
Proof.
  intros R l r v H0. induction l as [|p l' IH]; cbn [reg_lookup regupds]; intro H; [discriminate H|].
  destruct (bv_eqb r (fst p)) eqn:E.
  - injection H as <-. apply reg_eq_of_eqb in E. rewrite <- E. apply getr_same. apply reg_neq_of_eqb. exact H0.
  - rewrite getr_other by (apply reg_neq_of_eqb; exact E). apply IH. exact H.
Qed.
Lemma getr_regupds_miss : forall R l r, reg_lookup r l = None -> getr (regupds R l) r = getr R r.
Proof.
  intros R l r. induction l as [|p l' IH]; cbn [reg_lookup regupds]; intro H; [reflexivity|].
  destruct (bv_eqb r (fst p)) eqn:E; [discriminate H|].
  rewrite getr_other by (apply reg_neq_of_eqb; exact E). apply IH. exact H.
Qed.
Lemma getr_chain_hit : forall X R l r v, X = regupds R l -> bv_eqb r 0 = false -> reg_lookup r l = Some v -> getr X r = v.
Proof. intros X R l r v -> H0 H. exact (getr_regupds_hit R l r v H0 H). Qed.
Lemma getr_chain_miss : forall X R l r, X = regupds R l -> reg_lookup r l = None -> getr X r = getr R r.
Proof. intros X R l r -> H. exact (getr_regupds_miss R l r H). Qed.
Module WalkTacG.
Import Ltac2.Ltac2.
Ltac2 rec chain (x : constr) : constr * constr :=
  lazy_match! x with
  | regupd ?y ?rd ?v => let (b, l) := chain y in (b, '(@cons (reg * word) (@pair reg word $rd $v) $l))
  | _ => (x, '(@nil (reg * word)))
  end.
Ltac2 rec find (x : constr) (r : constr) : constr option :=
  lazy_match! x with
  | regupd ?y ?rd ?v => if Constr.equal rd r then Some v else find y r
  | _ => None
  end.
Ltac2 proof (x : constr) (r : constr) : constr :=
  let (b, l) := chain x in
  match find x r with
  | Some v => '(getr_chain_hit $x $b $l $r $v (@eq_refl (bvmap 5 word) $x) (@eq_refl bool false) (@eq_refl (option word) (@Some word $v)))
  | None => '(getr_chain_miss $x $b $l $r (@eq_refl (bvmap 5 word) $x) (@eq_refl (option word) (@None word)))
  end.
Ltac2 rw (x : Ltac1.t) (r : Ltac1.t) : unit :=
  match Ltac1.to_constr x with
  | Some x => match Ltac1.to_constr r with
              | Some r => let p := proof x r in ltac1:(p |- rewrite p) (Ltac1.of_constr p)
              | None => Control.zero (Tactic_failure None)
              end
  | None => Control.zero (Tactic_failure None)
  end.
End WalkTacG.
Module WalkTacG2.
Import Ltac2.Ltac2.
Ltac2 proof (x : constr) (r : constr) : constr :=
  let (b, l) := WalkTacG.chain x in
  match WalkTacG.find x r with
  | Some v => '(getr_regupds_hit $b $l $r $v (@eq_refl bool false) (@eq_refl (option word) (@Some word $v)) : getr $x $r = $v)
  | None => '(getr_regupds_miss $b $l $r (@eq_refl (option word) (@None word)) : getr $x $r = getr $b $r)
  end.
Ltac2 rw (x : Ltac1.t) (r : Ltac1.t) : unit :=
  match Ltac1.to_constr x with
  | Some x => match Ltac1.to_constr r with
              | Some r => let p := proof x r in ltac1:(p |- rewrite p) (Ltac1.of_constr p)
              | None => Control.zero (Tactic_failure None)
              end
  | None => Control.zero (Tactic_failure None)
  end.
End WalkTacG2.
Ltac gres_rw X r :=
  first [ let f := ltac2:(x r |- WalkTacG2.rw x r) in f X r
        | let f := ltac2:(x r |- WalkTacG.rw x r) in f X r ].
Ltac gres :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             first [ gres_rw X r
                   | let p := getr_proof X r in
                     let p' := constr:(p) in rewrite p' ]
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.
Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.
Ltac is_pos_lit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_pos_lit q
  | xI ?q => is_pos_lit q
  end.
Ltac is_Z_lit z :=
  lazymatch z with
  | Z0 => idtac
  | Zpos ?p => is_pos_lit p
  | Zneg ?p => is_pos_lit p
  end.
Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.
Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.
Ltac vnorm :=
  gres; imm_norm;
  match goal with |- context [v_addi _ Z0] => rewrite ?v_addi_0 | _ => idtac end;
  match goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  match goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  vals_lit.
Section WalkTacPc.
Context {fx : FPState}.
Lemma step_addi_at_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_addi_at; eassumption. Qed.
Lemma step_andi_at_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_andi (getr regs rs) (bv_signed imm) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_andi_at; eassumption. Qed.
Lemma step_ori_at_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_OR rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_ori (getr regs rs) (bv_signed imm) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_ori_at; eassumption. Qed.
Lemma step_xori_at_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_XOR rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_xori (getr regs rs) (bv_signed imm) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_xori_at; eassumption. Qed.
Lemma step_sltiu_at_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sltiu (getr regs rs) (bv_signed imm) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_sltiu_at; eassumption. Qed.
Lemma step_slli_at_pc : forall segs regs pc mem rom w rd rs (sh : bv 6) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_slli (getr regs rs) (bv_unsigned sh) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_slli_at; eassumption. Qed.
Lemma step_srli_at_pc : forall segs regs pc mem rom w rd rs (sh : bv 6) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_srli (getr regs rs) (bv_unsigned sh) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_srli_at; eassumption. Qed.
Lemma step_srai_at_pc : forall segs regs pc mem rom w rd rs (sh : bv 6) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_srai (getr regs rs) (bv_unsigned sh) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_srai_at; eassumption. Qed.
Lemma step_add_at_pc : forall segs regs pc mem rom w rd rs1 rs2 v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_add (getr regs rs1) (getr regs rs2) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_add_at; eassumption. Qed.
Lemma step_sub_at_pc : forall segs regs pc mem rom w rd rs1 rs2 v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sub (getr regs rs1) (getr regs rs2) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_sub_at; eassumption. Qed.
Lemma step_addiw_at_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addiw (getr regs rs) (bv_signed imm) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_addiw_at; eassumption. Qed.
Lemma step_mul_at_pc : forall segs regs pc mem rom w rd rs1 rs2 v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MUL rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mul (getr regs rs1) (getr regs rs2) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_mul_at; eassumption. Qed.
Lemma step_lui_at_pc : forall segs regs pc mem rom w rd (imm : bv 20) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_lui (Z.shiftl (bv_signed imm) 12) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_lui_at; eassumption. Qed.
Lemma step_auipc_at_pc : forall segs regs pc mem rom w rd (imm : bv 20) v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_auipc pc (Z.shiftl (bv_signed imm) 12) = v ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros; subst pc'; eapply step_auipc_at; eassumption. Qed.
Lemma step_sd_at_pc : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof. intros; subst pc'; eapply step_sd_at; eassumption. Qed.
Lemma step_sw_at_pc : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof. intros; subst pc'; eapply step_sw_at; eassumption. Qed.
Lemma step_sh_at_pc : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 2%nat = true ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' (wbytes mem a (word_to_le_bytes 2 v)) rom).
Proof. intros; subst pc'; eapply step_sh_at; eassumption. Qed.
Lemma step_sb_at_pc : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word) (b : byte) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  Z_to_bv 8 (bv_unsigned v) = b ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' (wbytes mem a [b]) rom).
Proof. intros; subst pc'; eapply MmapSim.step_sb_at; eassumption. Qed.
Lemma step_ld_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  bv_eqb rd 0 = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof.
  intros; subst pc'; erewrite PropExec.step_ld by eassumption;
  match goal with H : bv_eqb _ _ = false |- _ => rewrite H end; reflexivity.
Qed.
Lemma step_lw_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  bv_eqb rd 0 = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_lw v)) pc' mem rom).
Proof.
  intros; subst pc'; erewrite PropExec.step_lw by eassumption;
  match goal with H : bv_eqb _ _ = false |- _ => rewrite H end; reflexivity.
Qed.
Lemma step_lwu_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  bv_eqb rd 0 = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof.
  intros; subst pc'; erewrite PropExec.step_lwu by eassumption;
  match goal with H : bv_eqb _ _ = false |- _ => rewrite H end; reflexivity.
Qed.
Lemma step_lh_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  bv_eqb rd 0 = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_lh v)) pc' mem rom).
Proof.
  intros; subst pc'; erewrite PropExec.step_lh by eassumption;
  match goal with H : bv_eqb _ _ = false |- _ => rewrite H end; reflexivity.
Qed.
Lemma step_lhu_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  bv_eqb rd 0 = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof.
  intros; subst pc'; erewrite PropExec.step_lhu by eassumption;
  match goal with H : bv_eqb _ _ = false |- _ => rewrite H end; reflexivity.
Qed.
Lemma step_lbu_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) b pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  bv_eqb rd 0 = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) pc' mem rom).
Proof.
  intros; subst pc'; erewrite PropExec.step_lbu by eassumption;
  match goal with H : bv_eqb _ _ = false |- _ => rewrite H end; reflexivity.
Qed.
Lemma step_lb_pc : forall segs regs pc mem rom w rd rs (imm : bv 12) b pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  bv_eqb rd 0 = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_lb b)) pc' mem rom).
Proof.
  intros; subst pc'; erewrite PropExec.step_lb by eassumption;
  match goal with H : bv_eqb _ _ = false |- _ => rewrite H end; reflexivity.
Qed.
Lemma step_beq_tk_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  btgt pc (bv_signed imm) = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_beq_tk; eassumption. Qed.
Lemma step_beq_ft_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_beq_ft; eassumption. Qed.
Lemma step_bne_tk_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  btgt pc (bv_signed imm) = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_bne_tk; eassumption. Qed.
Lemma step_bne_ft_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_bne_ft; eassumption. Qed.
Lemma step_blt_tk_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LT rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = true ->
  btgt pc (bv_signed imm) = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_blt_tk; eassumption. Qed.
Lemma step_blt_ft_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LT rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_blt_ft; eassumption. Qed.
Lemma step_bge_tk_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GE rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = false ->
  btgt pc (bv_signed imm) = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_bge_tk; eassumption. Qed.
Lemma step_bge_ft_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GE rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = true ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_bge_ft; eassumption. Qed.
Lemma step_bltu_tk_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LTU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = true ->
  btgt pc (bv_signed imm) = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_bltu_tk; eassumption. Qed.
Lemma step_bltu_ft_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LTU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = false ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_bltu_ft; eassumption. Qed.
Lemma step_bgeu_tk_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GEU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = false ->
  btgt pc (bv_signed imm) = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_bgeu_tk; eassumption. Qed.
Lemma step_bgeu_ft_pc : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13) pc',
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GEU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = true ->
  v_addi pc 4 = pc' ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc' mem rom).
Proof. intros; subst pc'; eapply PropExec.step_bgeu_ft; eassumption. Qed.
End WalkTacPc.
Ltac pc_lit_side :=
  lazymatch goal with
  | |- ?p = ?e => let l := word_lit p in unify e l; apply bv_eq; vm_compute; reflexivity
  end.
Ltac stepn_val :=
  gres; imm_norm;
  match goal with |- context [v_addi _ Z0] => rewrite ?v_addi_0 | _ => idtac end;
  match goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  match goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  lazymatch goal with |- ?l = _ => try val_lit l end;
  reflexivity.
Ltac stepn_at_old F D :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) => eapply step_addi_at
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) => eapply step_andi_at
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) => eapply step_ori_at
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) => eapply step_xori_at
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) => eapply step_sltiu_at
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) => eapply step_slli_at
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) => eapply step_srli_at
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) => eapply step_srai_at
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) => eapply step_add_at
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) => eapply step_sub_at
    | decode_any _ = Some (OpImm32 _ _ _, _) => eapply step_addiw_at
    | decode_any _ = Some (Mul M_MUL _ _ _, _) => eapply step_mul_at
    | decode_any _ = Some (Lui _ _, _) => eapply step_lui_at
    | decode_any _ = Some (Auipc _ _, _) => eapply step_auipc_at
    end;
    [ exact F | reflexivity | exact D | reflexivity | stepn_val ]
  | step_simpl ].
Ltac stepn_at_pc F D :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) => eapply step_addi_at_pc
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) => eapply step_andi_at_pc
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) => eapply step_ori_at_pc
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) => eapply step_xori_at_pc
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) => eapply step_sltiu_at_pc
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) => eapply step_slli_at_pc
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) => eapply step_srli_at_pc
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) => eapply step_srai_at_pc
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) => eapply step_add_at_pc
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) => eapply step_sub_at_pc
    | decode_any _ = Some (OpImm32 _ _ _, _) => eapply step_addiw_at_pc
    | decode_any _ = Some (Mul M_MUL _ _ _, _) => eapply step_mul_at_pc
    | decode_any _ = Some (Lui _ _, _) => eapply step_lui_at_pc
    | decode_any _ = Some (Auipc _ _, _) => eapply step_auipc_at_pc
    end;
    [ exact F | reflexivity | exact D | reflexivity | stepn_val | pc_lit_side ]
  | step_simpl ].
Ltac stepn_at F D := first [ stepn_at_pc F D | stepn_at_old F D ].
Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => first [ stepn_at F D | stepi F D ]; vnorm
  end.
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.
Ltac stepb_tk_old F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].
Ltac stepb_tk_pc F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk_pc
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk_pc
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk_pc
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk_pc
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk_pc
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk_pc
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac | pc_lit_side ]
  | step_simpl; vnorm ].
Ltac stepb_tk F D tac := first [ stepb_tk_pc F D tac | stepb_tk_old F D tac ].
Ltac stepb_ft_old F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].
Ltac stepb_ft_pc F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft_pc
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft_pc
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft_pc
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft_pc
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft_pc
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft_pc
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac | pc_lit_side ]
  | step_simpl; vnorm ].
Ltac stepb_ft F D tac := first [ stepb_ft_pc F D tac | stepb_ft_old F D tac ].
Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.
Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].
Ltac stepret F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).
Ltac stepsd_old F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].
Ltac stepsd_pc F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at_pc with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac | pc_lit_side ]
  | step_simpl ].
Ltac stepsd F D aa vv oktac := first [ stepsd_pc F D aa vv oktac | stepsd_old F D aa vv oktac ].
Ltac stepld_old F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].
Ltac stepld_pc F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld_pc with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] | reflexivity | pc_lit_side ]
  | step_simpl; vnorm ].
Ltac stepld F D vv rtac := first [ stepld_pc F D vv rtac | stepld_old F D vv rtac ].
Fixpoint wbytes_layers (m : word -> option byte) (ls : list (Z * list byte)) : word -> option byte :=
  match ls with
  | nil => m
  | cons p ls' => wbytes (wbytes_layers m ls') (Z_to_bv 64 (fst p)) (snd p)
  end.
Definition layer_out (za : Z) (n : nat) (p : Z * list byte) : Prop :=
  (0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= fst p < 2^64 /\
   fst p + Z.of_nat (length (snd p)) <= 2^64 /\
   (za + Z.of_nat n <= fst p \/ fst p + Z.of_nat (length (snd p)) <= za))%Z.
Lemma rdn_wbytes_skip : forall segs ls m (za : Z) n,
  Forall (layer_out za n) ls ->
  rdn segs (wbytes_layers m ls) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs ls m za n H. induction H as [|p ls' Hp _ IH]; [reflexivity|].
  cbn [wbytes_layers]. destruct Hp as (Ha & Han & Hb & Hbn & Hd).
  rewrite rdn_wbytes_out by (rewrite ?u_Z2bv by lia; lia). exact IH.
Qed.
Ltac peel_collect sidetac hitstop M a za n k :=
  lazymatch M with
  | wbytes ?M' (Z_to_bv 64 ?zb) ?bs =>
      tryif (lazymatch hitstop with true => constr_eq (Z_to_bv 64 zb) a | _ => fail end)
      then (let L := fresh "PLL" in pose (L := @nil (Z * list byte)); let Lc := constr:(L) in
            k Lc M constr:(@Forall_nil (Z * list byte) (layer_out za n)) constr:(O))
      else (let H := fresh "PL" in
            tryif assert (H : layer_out za n (zb, bs))
                    by (change_no_check ((0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
                                          zb + Z.of_nat (length bs) <= 2^64 /\
                                          (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z); sidetac)
            then peel_collect sidetac hitstop M' a za n ltac:(fun ls m pf cnt =>
                   let L := fresh "PLL" in
                   pose (L := @cons (Z * list byte) (zb, bs) ls);
                   let Lc := constr:(L) in
                   k Lc m constr:(@Forall_cons (Z * list byte) (layer_out za n) (zb, bs) ls H pf) constr:(S cnt))
            else (let L := fresh "PLL" in pose (L := @nil (Z * list byte)); let Lc := constr:(L) in
                  k Lc M constr:(@Forall_nil (Z * list byte) (layer_out za n)) constr:(O)))
  | _ => let L := fresh "PLL" in pose (L := @nil (Z * list byte)); let Lc := constr:(L) in
         k Lc M constr:(@Forall_nil (Z * list byte) (layer_out za n)) constr:(O)
  end.
Ltac peel_multi sidetac hitstop :=
  lazymatch goal with
  | |- rdn ?segs ?M (Z_to_bv 64 ?za) ?n = ?R =>
      peel_collect sidetac hitstop M (Z_to_bv 64 za) za n ltac:(fun L m pf cnt =>
        lazymatch cnt with
        | O => fail
        | S O => fail
        | _ => change_no_check (rdn segs (wbytes_layers m L) (Z_to_bv 64 za) n = R);
               rewrite (rdn_wbytes_skip segs L m za n pf)
        end);
      repeat match goal with H : layer_out _ _ _ |- _ => clear H end;
      repeat match goal with L := _ : list (Z * list byte) |- _ => clear L end
  end.
