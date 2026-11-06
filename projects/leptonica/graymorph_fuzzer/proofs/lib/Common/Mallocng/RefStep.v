(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From Ltac2 Require Ltac2.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps MallocShape RefLrSc.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StepForms.
Context {fx : FPState}.

Lemma step_lbu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) (b : byte),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 1%nat = Some [b] ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm a b Hf He Hd Hrd Ha Hr.
  rewrite (step_lbu segs regs pc mem rom w rd rs imm b Hf He Hd); [rewrite Hrd; reflexivity|].
  rewrite Ha. exact Hr.
Qed.

Lemma step_ld_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) bs (v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm a bs v Hf He Hd Hrd Ha Hr Hv.
  rewrite (step_ld segs regs pc mem rom w rd rs imm bs v Hf He Hd);
    [rewrite Hrd; reflexivity | rewrite Ha; exact Hr | exact Hv].
Qed.

Lemma step_lw_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) bs (v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_lw v)) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm a bs v Hf He Hd Hrd Ha Hr Hv.
  rewrite (step_lw segs regs pc mem rom w rd rs imm bs v Hf He Hd);
    [rewrite Hrd; reflexivity | rewrite Ha; exact Hr | exact Hv].
Qed.

Lemma step_lwu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) bs (v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm a bs v Hf He Hd Hrd Ha Hr Hv.
  rewrite (step_lwu segs regs pc mem rom w rd rs imm bs v Hf He Hd);
    [rewrite Hrd; reflexivity | rewrite Ha; exact Hr | exact Hv].
Qed.

Lemma step_lhu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) (a : word) bs (v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm a bs v Hf He Hd Hrd Ha Hr Hv.
  rewrite (step_lhu segs regs pc mem rom w rd rs imm bs v Hf He Hd);
    [rewrite Hrd; reflexivity | rewrite Ha; exact Hr | exact Hv].
Qed.

(* [comment removed for export] *)
Lemma step_sb_w : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 1 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sb_at segs regs pc mem rom w rs1 rs2 imm a v (Z_to_bv 8 (bv_unsigned v)) Hf He Hd Ha Hv eq_refl Hok).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_step_p : forall segs ms md ms' T,
  md_pure md -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes segs (mkCfg ms' md) T -> realizes segs (mkCfg ms md) T.
Proof.
  intros segs ms md ms' T [Hh Hl Hm] Hsvc Hs H. eapply rz_step; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rz_regupd_eq : forall segs (R : bvmap 5 word) (rd : reg) (v v' : word) pc M rom md T,
  v = v' ->
  realizes segs (mkCfg (mkst (regupd R rd v') pc M rom) md) T ->
  realizes segs (mkCfg (mkst (regupd R rd v) pc M rom) md) T.
Proof. intros segs R rd v v' pc M rom md T -> H. exact H. Qed.

(* [comment removed for export] *)
Lemma rz_step_reg : forall segs (R : bvmap 5 word) pc M rom md T (rd : reg) (e v : word) (pc2 pc' : word),
  md_pure md ->
  RiscvSemantics.step segs (mkst R pc M rom) =
    MachineOk (mkst (if bv_eqb rd 0 then R else regupd R rd e) pc2 M rom) ->
  bv_eqb rd 0 = false -> e = v -> pc2 = pc' ->
  realizes segs (mkCfg (mkst (regupd R rd v) pc' M rom) md) T ->
  realizes segs (mkCfg (mkst R pc M rom) md) T.
Proof.
  intros segs R pc M rom md T rd e v pc2 pc' Hp Hs Hrd <- <- H.
  eapply rz_step_p; [exact Hp | reflexivity | exact Hs |]. rewrite Hrd. exact H.
Qed.

(* [comment removed for export] *)
Lemma rz_step_pc : forall segs (R : bvmap 5 word) pc M rom md T (pc2 pc' : word),
  md_pure md ->
  RiscvSemantics.step segs (mkst R pc M rom) = MachineOk (mkst R pc2 M rom) ->
  pc2 = pc' ->
  realizes segs (mkCfg (mkst R pc' M rom) md) T ->
  realizes segs (mkCfg (mkst R pc M rom) md) T.
Proof.
  intros segs R pc M rom md T pc2 pc' Hp Hs <- H. eapply rz_step_p; [exact Hp | reflexivity | exact Hs | exact H].
Qed.

(* [comment removed for export] *)
Lemma rz_at_pc : forall segs (R : bvmap 5 word) (pc' : word) M rom md T (pc : word),
  realizes segs (mkCfg (mkst R pc' M rom) md) T -> pc' = pc ->
  realizes segs (mkCfg (mkst R pc M rom) md) T.
Proof. intros segs R pc' M rom md T pc H <-. exact H. Qed.

(* [comment removed for export] *)
Lemma rz_step_mem : forall segs (R : bvmap 5 word) pc M M' rom md T (pc2 pc' : word),
  md_pure md ->
  RiscvSemantics.step segs (mkst R pc M rom) = MachineOk (mkst R pc2 M' rom) ->
  pc2 = pc' ->
  realizes segs (mkCfg (mkst R pc' M' rom) md) T ->
  realizes segs (mkCfg (mkst R pc M rom) md) T.
Proof.
  intros segs R pc M M' rom md T pc2 pc' Hp Hs <- H. eapply rz_step_p; [exact Hp | reflexivity | exact Hs | exact H].
Qed.

End StepForms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wtop (s : mstate) : Prop :=
  alloc_ceiling <= alloc_top (ms_vm s) /\ alloc_top (ms_vm s) <= TASK_SIZE /\ alloc_top (ms_vm s) <= ms_lo s.

Definition minv (s0 : mstate) (s : mstate) : Prop :=
  ms_lo s = ms_lo s0 /\ ms_hi s = ms_hi s0 /\ alloc_top (ms_vm s) = alloc_top (ms_vm s0) /\
  0 <= ms_lo s0 /\ ms_lo s0 <= ms_hi s0 /\ ms_hi s0 <= 2^64 /\ wtop s0.

Lemma minv_lo64 : forall s0 s, minv s0 s -> ms_lo s <= 2^64.
Proof. intros s0 s (A & B & T & C & D & E & F). rewrite A. lia. Qed.
Lemma minv_lo : forall s0 s, minv s0 s -> ms_lo s = ms_lo s0.
Proof. intros s0 s (A & B & C). exact A. Qed.
Lemma minv_hi : forall s0 s, minv s0 s -> ms_hi s = ms_hi s0.
Proof. intros s0 s (A & B & C). exact B. Qed.
Lemma minv_top : forall s0 s, minv s0 s -> alloc_top (ms_vm s) = alloc_top (ms_vm s0).
Proof. intros s0 s (A & B & T & C). exact T. Qed.
(* [comment removed for export] *)
Lemma minv_ceil : forall s0 s, minv s0 s -> wtop s.
Proof. intros s0 s (A & B & T & C & D & E & (F1 & F2 & F3)). unfold wtop. rewrite A, T. repeat split; assumption. Qed.
Lemma minv_ceil_num : forall s0 s, minv s0 s ->
  140735332483072 <= alloc_top (ms_vm s) /\ alloc_top (ms_vm s) <= 140737488355328 /\ alloc_top (ms_vm s) <= ms_lo s.
Proof. intros s0 s HI. pose proof (minv_ceil s0 s HI) as H. unfold wtop, TASK_SIZE in H. rewrite alloc_ceiling_val in H. exact H. Qed.
Lemma wtop_task : forall s, wtop s -> alloc_top (ms_vm s) <= TASK_SIZE.
Proof. intros s (A & B & C). exact B. Qed.
Lemma minv_same : forall s0 s s', minv s0 s -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
  alloc_top (ms_vm s') = alloc_top (ms_vm s) -> minv s0 s'.
Proof. intros s0 s s' (A & B & T & C & D & E & (F1 & F2 & F3)) H1 H2 H3. unfold minv, wtop. rewrite H1, H2, H3, A, B, T. repeat split; try lia; assumption. Qed.
Lemma minv_init : forall s0 (sp : word) D,
  0 <= ms_lo s0 -> ms_lo s0 <= bv_unsigned sp - D -> 0 <= D -> bv_unsigned sp <= ms_hi s0 -> ms_hi s0 <= 2^64 ->
  wtop s0 -> minv s0 s0.
Proof. intros s0 sp D H1 H2 H3 H4 H5 (F1 & F2 & F3). unfold minv, wtop. repeat split; try lia; assumption. Qed.

(* [comment removed for export] *)
Lemma alloc_top_vm_mmap : forall a n h, alloc_top (vm_mmap a n h) = alloc_top h. Proof. reflexivity. Qed.
Lemma alloc_top_vm_noacc : forall a n h, alloc_top (vm_noacc a n h) = alloc_top h. Proof. reflexivity. Qed.
Lemma alloc_top_vm_munmap : forall a n h, alloc_top (vm_munmap a n h) = alloc_top h. Proof. reflexivity. Qed.
Lemma alloc_top_vm_fixed_ok : forall a n h, alloc_top (vm_fixed_ok a n h) = alloc_top h. Proof. reflexivity. Qed.
Lemma alloc_top_vm_fixed_destroy : forall a n h, alloc_top (vm_fixed_destroy a n h) = alloc_top h. Proof. reflexivity. Qed.
Lemma alloc_top_vm_unprotect : forall a n h, alloc_top (vm_unprotect a n h) = alloc_top h. Proof. reflexivity. Qed.
Lemma alloc_top_vm_brk_grow : forall r h, alloc_top (vm_brk_grow r h) = alloc_top h. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mwin (s0 : mstate) (mm0 : word -> option byte) (sp : word) (D : Z)
                (mm : word -> option byte) : Prop :=
  (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
     ~ (bv_unsigned sp - D <= bv_unsigned a < bv_unsigned sp) -> mm a = mm0 a)
  /\ (forall a : word, bv_unsigned sp - D <= bv_unsigned a < bv_unsigned sp -> mm a <> None).

Lemma mwin_init : forall s0 mm0 sp D,
  (forall a : word, bv_unsigned sp - D <= bv_unsigned a < bv_unsigned sp -> mm0 a <> None) ->
  mwin s0 mm0 sp D mm0.
Proof. intros. split; [intros; reflexivity | assumption]. Qed.

(* [comment removed for export] *)
Lemma pure_wv : forall md h, md_pure md -> md_pure (with_vmmaps h md).
Proof. intros md h H. apply md_pure_vmmaps. exact H. Qed.

(* [comment removed for export] *)
Definition wreg (l : list Z) (r : reg) : bool := existsb (Z.eqb (bv_unsigned r)) l.

Lemma getr_other_w : forall l R (rd : reg) v (r : reg),
  wreg l rd = true -> wreg l r = false -> getr (regupd R rd v) r = getr R r.
Proof.
  intros l R rd v r Hd Hr. apply getr_other. intros ->. rewrite Hd in Hr. discriminate.
Qed.

(* [comment removed for export] *)
Definition cs_num (z : Z) : bool :=
  ((z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)))%Z.

Lemma wreg_cs : forall wl (x : reg), callee_saved x ->
  forallb (fun z => negb (cs_num z)) wl = true -> wreg wl x = false.
Proof.
  intros wl x Hx Hwl. unfold wreg.
  apply Bool.not_true_iff_false. intros Hex. apply existsb_exists in Hex as (z & Hin & Hz).
  apply Z.eqb_eq in Hz. subst z.
  rewrite forallb_forall in Hwl. specialize (Hwl _ Hin). cbn beta in Hwl.
  apply negb_true_iff in Hwl. unfold cs_num in Hwl.
  unfold callee_saved in Hx.
  destruct Hx as [->|[->|[->|[->|[->|Hr]]]]]; try (cbv in Hwl; discriminate Hwl).
  apply Bool.orb_false_iff in Hwl as [_ Hwl]. apply Bool.andb_false_iff in Hwl as [Hwl|Hwl];
    [apply Z.leb_gt in Hwl | apply Z.leb_gt in Hwl]; lia.
Qed.

Lemma wreg_sub : forall (wl wl' : list Z) (r : reg),
  forallb (fun z => existsb (Z.eqb z) wl) wl' = true -> wreg wl r = false -> wreg wl' r = false.
Proof.
  intros wl wl' r Hsub Hr. unfold wreg in *.
  destruct (existsb (Z.eqb (bv_unsigned r)) wl') eqn:E; [|reflexivity]. exfalso.
  apply existsb_exists in E as (z & Hin & Hz). apply Z.eqb_eq in Hz. subst z.
  rewrite forallb_forall in Hsub. specialize (Hsub _ Hin). cbn beta in Hsub.
  rewrite Hsub in Hr. discriminate.
Qed.

(* [comment removed for export] *)
Ltac keep_facts Hkeep :=
  let one z :=
    let r := constr:(@BV 5 z I) in
    try (let H := fresh "Hk" in
         assert (H := Hkeep r ltac:(reflexivity))) in
  one 1%Z; one 2%Z; one 3%Z; one 4%Z; one 5%Z; one 6%Z; one 7%Z; one 8%Z; one 9%Z; one 10%Z;
  one 11%Z; one 12%Z; one 13%Z; one 14%Z; one 15%Z; one 16%Z; one 17%Z; one 18%Z; one 19%Z; one 20%Z;
  one 21%Z; one 22%Z; one 23%Z; one 24%Z; one 25%Z; one 26%Z; one 27%Z; one 28%Z; one 29%Z; one 30%Z; one 31%Z.

(* [comment removed for export] *)
Ltac keep_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  lazymatch type of Hr with wreg ?wl _ = false =>
    repeat first
      [ (* [comment removed for export] *)
        lazymatch goal with
        | |- getr (regupd ?R0 ?r0 ?v0) r = _ =>
            let R := constr:(regupd R0 r0 v0) in
            let bl := gf_reify R in
            lazymatch bl with
            | (?base, ?l) => rewrite (getr_upds_test (wreg wl) base l r eq_refl Hr : getr R r = getr base r)
            end
        end
      | rewrite (getr_other_w wl _ _ _ r); [ | reflexivity | exact Hr ]
      | match goal with
        | Hk : forall r' : reg, wreg ?wl' r' = false -> getr ?R1 r' = getr _ r' |- getr ?R1 r = _ =>
            rewrite (Hk r (wreg_sub wl wl' r eq_refl Hr))
        end ]
  end;
  reflexivity.

(* [comment removed for export] *)
Ltac cur_pc k :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => let u := eval vm_compute in (bv_unsigned pc) in k u
  end.

(* [comment removed for export] *)
Lemma at_v_addi : forall (b : word) (d : Z), at_ b d = v_addi b d.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma negb_true_eq : forall b, negb b = true -> b = false.
Proof. intros [|]; [discriminate | reflexivity]. Qed.
Lemma negb_false_eq : forall b, negb b = false -> b = true.
Proof. intros [|]; [reflexivity | discriminate]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lit_bv t :=
  let T := type of t in
  lazymatch eval cbv in T with
  | bv ?n => let u := eval vm_compute in (bv_unsigned t) in
             constr:(@BV n u ltac:(vm_compute; exact I))
  end.

(* [comment removed for export] *)
Ltac lit_instr i :=
  lazymatch i with
  | OpImm ?op ?rd ?rs ?imm => let rd := lit_bv rd in let rs := lit_bv rs in let imm := lit_bv imm in constr:(OpImm op rd rs imm)
  | ShiftImm ?op ?rd ?rs ?sh => let rd := lit_bv rd in let rs := lit_bv rs in let sh := lit_bv sh in constr:(ShiftImm op rd rs sh)
  | Op ?op ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Op op rd a b)
  | OpImm32 ?rd ?rs ?imm => let rd := lit_bv rd in let rs := lit_bv rs in let imm := lit_bv imm in constr:(OpImm32 rd rs imm)
  | ShiftImm32 ?op ?rd ?rs ?sh => let rd := lit_bv rd in let rs := lit_bv rs in let sh := lit_bv sh in constr:(ShiftImm32 op rd rs sh)
  | Op32 ?op ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Op32 op rd a b)
  | Mul ?op ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Mul op rd a b)
  | Mul32 ?op ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Mul32 op rd a b)
  | Lui ?rd ?imm => let rd := lit_bv rd in let imm := lit_bv imm in constr:(Lui rd imm)
  | Auipc ?rd ?imm => let rd := lit_bv rd in let imm := lit_bv imm in constr:(Auipc rd imm)
  | Jal ?rd ?imm => let rd := lit_bv rd in let imm := lit_bv imm in constr:(Jal rd imm)
  | Jalr ?rd ?rs ?imm => let rd := lit_bv rd in let rs := lit_bv rs in let imm := lit_bv imm in constr:(Jalr rd rs imm)
  | Branch ?c ?a ?b ?imm => let a := lit_bv a in let b := lit_bv b in let imm := lit_bv imm in constr:(Branch c a b imm)
  | Load ?sz ?sg ?rd ?rs ?imm => let rd := lit_bv rd in let rs := lit_bv rs in let imm := lit_bv imm in constr:(Load sz sg rd rs imm)
  | Store ?sz ?a ?b ?imm => let a := lit_bv a in let b := lit_bv b in let imm := lit_bv imm in constr:(Store sz a b imm)
  | Lr ?wd ?aq ?rl ?rd ?rs => let rd := lit_bv rd in let rs := lit_bv rs in constr:(Lr wd aq rl rd rs)
  | Sc ?wd ?aq ?rl ?rd ?a ?b => let rd := lit_bv rd in let a := lit_bv a in let b := lit_bv b in constr:(Sc wd aq rl rd a b)
  | ?x => x
  end.

(* [comment removed for export] *)
Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Ltac solveF :=
  lazymatch goal with
  | |- fetch_word ?segs ?pc = Some ?w =>
      let f := eval vm_compute in (fetch_word segs pc) in
      lazymatch f with Some ?w0 => let wl := lit_bv w0 in unify w wl; vm_refl end
  end.
Ltac solveD :=
  lazymatch goal with
  | |- decode_any ?w = ?rhs =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with Some (?i, ?sz) => let il := lit_instr i in unify rhs (Some (il, sz)); vm_refl end
  end.

(* [comment removed for export] *)
Ltac gres :=
  gres_loop;          (* [comment removed for export] *)
  rewrite ?getr_zero.

(* [comment removed for export] *)
Ltac eregs :=
  repeat match goal with
  | H : getr ?R ?r = _ |- context [getr ?R ?r] => rewrite !H
  end.

(* [comment removed for export] *)
Ltac regnorm := gres; repeat (progress (eregs; gres)).

(* [comment removed for export] *)
Ltac munf :=
  cbv beta match zeta delta [MallocOps.is0 MallocOps.w0 MallocOps.wlit MallocOps.wm1 PAGEMASK
    DEBRUIJN_MULT MMAP_THRESHOLD_W MAP_FAILED
    m_unlock m_canary_load m_canary_check m_free_meta m_seq_next FREE_FUEL
    m_ctz32 m_size_to_class_big set_errno] in *.

(* [comment removed for export] *)
Ltac zlit t :=
  let u := eval vm_compute in (bv_unsigned t) in constr:(Z_to_bv 64 u).

Ltac klit_g t :=
  lazymatch t with
  | Z_to_bv 64 (bv_unsigned _) => fail
  | Z_to_bv 64 (bytes_le_to_Z _) => fail
  | _ => idtac
  end;
  check_closed_term t;
  let l := zlit t in
  tryif constr_eq t l then fail else
  replace t with l by (apply bv_eq; vm_compute; reflexivity).

Ltac klits_with tac :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?z] => tac (Z_to_bv 64 z)
  | |- context [@BV 64 ?u ?p] => lazymatch goal with |- context [mkst _ (@BV 64 u p) _ _] => fail | _ => tac (@BV 64 u p) end
  | |- context [v_lui ?k] => tac (v_lui k)
  | |- context [v_auipc ?a ?k] => tac (v_auipc a k)
  | |- context [v_addi (Z_to_bv 64 ?a) ?k] => tac (v_addi (Z_to_bv 64 a) k)
  | |- context [v_addiw (Z_to_bv 64 ?a) ?k] => tac (v_addiw (Z_to_bv 64 a) k)
  | |- context [at_ (Z_to_bv 64 ?a) ?k] => tac (at_ (Z_to_bv 64 a) k)
  | |- context [v_andi (Z_to_bv 64 ?a) ?k] => tac (v_andi (Z_to_bv 64 a) k)
  | |- context [v_ori (Z_to_bv 64 ?a) ?k] => tac (v_ori (Z_to_bv 64 a) k)
  | |- context [v_xori (Z_to_bv 64 ?a) ?k] => tac (v_xori (Z_to_bv 64 a) k)
  | |- context [v_slli (Z_to_bv 64 ?a) ?k] => tac (v_slli (Z_to_bv 64 a) k)
  | |- context [v_srli (Z_to_bv 64 ?a) ?k] => tac (v_srli (Z_to_bv 64 a) k)
  | |- context [v_srai (Z_to_bv 64 ?a) ?k] => tac (v_srai (Z_to_bv 64 a) k)
  | |- context [v_slliw (Z_to_bv 64 ?a) ?k] => tac (v_slliw (Z_to_bv 64 a) k)
  | |- context [v_add (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_add (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_sub (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_sub (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_and (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_and (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_or (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_or (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_addw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_addw (Z_to_bv 64 a) (Z_to_bv 64 b))
  | |- context [v_subw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => tac (v_subw (Z_to_bv 64 a) (Z_to_bv 64 b))
  end.

(* [comment removed for export] *)
Ltac klitsg := klits_with klit_g.

(* [comment removed for export] *)
Ltac addr_tac :=
  regnorm; imm_norm; rewrite ?v_addi_0;
  first [ reflexivity | bveq | f_equal; first [reflexivity | bveq]
        | match goal with |- ?g => fail 100 "addr_tac cannot prove" g end ].

(* [comment removed for export] *)
Ltac rz_norm :=
  try lazymatch goal with
  | |- realizes _ (mkCfg ?st _) _ => norm_pc_state st
  end.
Ltac mpost HS := rz_norm.

(* [comment removed for export] *)
Ltac mpure Hp := first [ exact Hp | apply pure_wv; exact Hp ].

(* [comment removed for export] *)
Ltac cur_instr tac :=
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst _ ?pc _ _) _) _ =>
      let f := eval vm_compute in (fetch_word segs pc) in
      lazymatch f with
      | Some ?w =>
          let d := eval vm_compute in (decode_any w) in
          lazymatch d with
          | Some (?i, _) => tac w i
          | _ => fail "cur_instr: no decode at" pc
          end
      | _ => fail "cur_instr: no fetch at" pc
      end
  end.

(* [comment removed for export] *)
Ltac pc_tac :=
  lazymatch goal with
  | |- ?l = ?x => let lit := word_lit l in unify x lit; apply bv_eq; vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Ltac val_tac := regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity.

Ltac rz_plain Hp HS L :=
  first
    [ eapply rz_step_reg;
      [ mpure Hp | eapply L; [solveF | reflexivity | solveD] | reflexivity | val_tac | pc_tac | ]
    | eapply rz_step_pc;
      [ mpure Hp | eapply L; [solveF | reflexivity | solveD] | pc_tac | ] ].

(* [comment removed for export] *)
Ltac mach Hp HS :=
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | OpImm ALU_ADD _ _ _   => rz_plain Hp HS step_addi
    | OpImm ALU_AND _ _ _   => rz_plain Hp HS step_andi
    | OpImm ALU_OR _ _ _    => rz_plain Hp HS step_ori
    | OpImm ALU_XOR _ _ _   => rz_plain Hp HS step_xori
    | OpImm ALU_SLT _ _ _   => rz_plain Hp HS step_slti
    | OpImm ALU_SLTU _ _ _  => rz_plain Hp HS step_sltiu
    | ShiftImm ALU_SLL _ _ _ => rz_plain Hp HS step_slli
    | ShiftImm ALU_SRL _ _ _ => rz_plain Hp HS PropExec.step_srli
    | ShiftImm ALU_SRA _ _ _ => rz_plain Hp HS step_srai
    | Op ALU_ADD _ _ _  => rz_plain Hp HS step_add
    | Op ALU_SUB _ _ _  => rz_plain Hp HS step_sub
    | Op ALU_AND _ _ _  => rz_plain Hp HS step_and
    | Op ALU_OR _ _ _   => rz_plain Hp HS step_or
    | Op ALU_XOR _ _ _  => rz_plain Hp HS step_xor
    | Op ALU_SLL _ _ _  => rz_plain Hp HS step_sll
    | Op ALU_SRL _ _ _  => rz_plain Hp HS step_srl
    | Op ALU_SRA _ _ _  => rz_plain Hp HS step_sra
    | Op ALU_SLT _ _ _  => rz_plain Hp HS step_slt
    | Op ALU_SLTU _ _ _ => rz_plain Hp HS step_sltu
    | OpImm32 _ _ _     => rz_plain Hp HS step_addiw
    | Op32 ALU_ADD _ _ _ => rz_plain Hp HS step_addw
    | Op32 ALU_SUB _ _ _ => rz_plain Hp HS step_subw
    | Op32 ALU_SLL _ _ _ => rz_plain Hp HS step_sllw
    | Op32 ALU_SRL _ _ _ => rz_plain Hp HS step_srlw
    | Op32 ALU_SRA _ _ _ => rz_plain Hp HS step_sraw
    | ShiftImm32 ALU_SLL _ _ _ => rz_plain Hp HS step_slliw
    | ShiftImm32 ALU_SRL _ _ _ => rz_plain Hp HS step_srliw
    | ShiftImm32 ALU_SRA _ _ _ => rz_plain Hp HS step_sraiw
    | Mul M_MUL _ _ _   => rz_plain Hp HS step_mul
    | Mul M_MULHU _ _ _ => rz_plain Hp HS step_mulhu
    | Lui _ _           => rz_plain Hp HS step_lui
    | Auipc _ _         => rz_plain Hp HS step_auipc
    | Jal _ _           => rz_plain Hp HS step_jal_x0
    | _ => fail "mach: not a plain instruction:" i
    end).

(* [comment removed for export] *)
Ltac mach_jal Hp HS := rz_plain Hp HS step_jal_link.
Ltac mach_jr Hp HS :=
  eapply rz_step_pc;
  [ mpure Hp
  | eapply step_jalr_x0; [ solveF | reflexivity | solveD | regnorm; imm_norm; klitsg; reflexivity ]
  | lazymatch goal with
    | |- v_jalr (Z_to_bv 64 _) _ = _ => pc_tac
    | |- v_jalr (@BV _ _ _) _ = _ => pc_tac
    | |- ?g => fail "mach_jr: target not literal:" g
    end
  | ].

(* [comment removed for export] *)
Ltac snorm_in H := rewrite ?upd_mem, ?upd_vm, ?upd_upd in H.

(* [comment removed for export] *)
Ltac mnorm HS :=
  repeat first
    [ progress (cbv beta match zeta delta [negb andb orb fst snd] in HS;
                cbv beta match zeta delta [negb andb orb fst snd])
    | progress (rewrite mbind_assoc in HS; rewrite mbind_assoc)
    | progress (rewrite mret_bind in HS; rewrite mret_bind)
    | progress (rewrite mbind_assoc_k in HS; rewrite mbind_assoc_k)
    | progress (rewrite mret_bind_k in HS; rewrite mret_bind_k)
    | progress (snorm_in HS; rewrite ?upd_mem, ?upd_vm, ?upd_upd) ];
  try match goal with Hag : magree _ _ |- _ => snorm_in Hag end;
  try match goal with HI : minv _ _ |- _ => snorm_in HI end.

(* [comment removed for export] *)
Ltac tnorm_eq :=
  repeat first
    [ progress (cbv beta match zeta delta [negb andb orb fst snd])
    | progress (rewrite mbind_assoc)
    | progress (rewrite mret_bind)
    | progress (rewrite mbind_assoc_k)
    | progress (rewrite mret_bind_k)
    | progress (rewrite ?upd_mem, ?upd_vm, ?upd_upd) ];
  reflexivity.

(* [comment removed for export] *)
Ltac exact_HS HS := first [ exact HS | eapply tsafe_teq; [ exact HS | tnorm_eq ] ].

(* [comment removed for export] *)
Ltac mach_ld Hp HS Hag HI :=
  let bs := fresh "bs" in let Hok := fresh "Hok" in let Hrd := fresh "Hrd" in
  let Hv := fresh "Hv" in let EQ := fresh "EQ" in
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | Load SZ8 true _ _ _ =>
        destruct (tsafe_ld_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_ld_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 8%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) | exact Hv ]
          | mpost HS ]
    | Load SZ4 true _ _ _ =>
        destruct (tsafe_lw_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_lw_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 4%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) | exact Hv ]
          | mpost HS ]
    | Load SZ4 false _ _ _ =>
        destruct (tsafe_lwu_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_lwu_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 4%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) | exact Hv ]
          | mpost HS ]
    | Load SZ2 false _ _ _ =>
        destruct (tsafe_lhu_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_lhu_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 2%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) | exact Hv ]
          | mpost HS ]
    | Load SZ1 false _ _ _ =>
        destruct (tsafe_lbu_inv _ _ _ _ HS) as (bs & Hok & Hrd & EQ);
        rewrite EQ in HS; rewrite EQ; clear EQ;
        eapply rz_step_p; [ mpure Hp | reflexivity
          | lazymatch type of Hok with acc_ok _ ?ma _ = true => eapply step_lbu_at with (a := ma) end;
            [solveF | reflexivity | solveD | reflexivity
            | addr_tac
            | exact (magree_rd _ _ _ 1%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd) ]
          | mpost HS ]
    | _ => fail "mach_ld: not a modeled load:" i
    end);
  mnorm HS.

(* [comment removed for export] *)
Ltac mach_st Hp HS Hag HI :=
  let Hok := fresh "Hok" in let Hso := fresh "Hso" in let EQ := fresh "EQ" in
  let go L n :=
    unfold m_sb, m_sh, m_sw, m_sd in HS |- *;
    let body ma mv :=
      rewrite EQ in HS; rewrite EQ; clear EQ;
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply L with (a := ma) (v := mv);
          [solveF | reflexivity | solveD
          | addr_tac
          | addr_tac
          | exact (magree_sok _ _ _ n Hag (minv_lo64 _ _ HI) Hok Hso) ]
        | mpost HS ];
      lazymatch type of Hag with magree ?s0 _ =>
        apply (magree_wbytes s0 _ ma (word_to_le_bytes n mv) (ms_vm s0)) in Hag end in
    lazymatch type of HS with
    | tsafe (MallocTree.mbind (m_st _ ?ma ?mv) _ _) _ =>
        destruct (tsafe_st_inv _ _ _ _ _ _ HS) as (Hok & Hso & EQ); body ma mv
    | tsafe (m_st _ ?ma ?mv _) _ =>
        destruct (tsafe_st_inv0 _ _ _ _ _ HS) as (Hok & Hso & EQ); body ma mv
    end
  in
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | Store SZ8 _ _ _ => go step_sd_at 8%nat
    | Store SZ4 _ _ _ => go step_sw_at 4%nat
    | Store SZ2 _ _ _ => go step_sh_at 2%nat
    | Store SZ1 _ _ _ => go step_sb_w 1%nat
    | _ => fail "mach_st: not a store:" i
    end);
  mnorm HS.

(* [comment removed for export] *)
Ltac mach_br_dir Hp HS dir ctac :=
  cur_instr ltac:(fun w i =>
    let go Ltk Lft :=
      lazymatch dir with
      | true => eapply rz_step_pc; [ mpure Hp
                 | eapply Ltk; [solveF | reflexivity | solveD | regnorm; imm_norm; ctac] | pc_tac | ]
      | false => eapply rz_step_pc; [ mpure Hp
                 | eapply Lft; [solveF | reflexivity | solveD | regnorm; imm_norm; ctac] | pc_tac | ]
      end in
    lazymatch i with
    | Branch BC_EQ _ _ _  => go step_beq_tk step_beq_ft
    | Branch BC_NE _ _ _  => go step_bne_tk step_bne_ft
    | Branch BC_LT _ _ _  => go step_blt_tk step_blt_ft
    | Branch BC_GE _ _ _  => go step_bge_tk step_bge_ft
    | Branch BC_LTU _ _ _ => go step_bltu_tk step_bltu_ft
    | Branch BC_GEU _ _ _ => go step_bgeu_tk step_bgeu_ft
    | _ => fail "mach_br: not a branch:" i
    end).

(* [comment removed for export] *)
Ltac by_bool Hb :=
  first [ exact Hb
        | exact (negb_true_eq _ Hb)
        | exact (negb_false_eq _ Hb)
        | rewrite <- Hb; reflexivity
        | rewrite <- (negb_true_eq _ Hb); reflexivity
        | rewrite <- (negb_false_eq _ Hb); reflexivity
        | lazymatch goal with |- ?g => let t := type of Hb in fail 1 "by_bool: goal" g "fact" t end ].

(* [comment removed for export] *)
Ltac mach_assert Hp HS :=
  let Hb := fresh "Hb" in let EQ := fresh "EQ" in
  destruct (tsafe_assert_inv _ _ _ _ HS) as [Hb EQ];
  rewrite EQ in HS; rewrite EQ; clear EQ; mnorm HS;
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst _ ?pc _ _) _) _ =>
      let f := eval vm_compute in (match fetch_word segs (v_addi pc 4) with Some w => bv_unsigned w | None => 0%Z end) in
      lazymatch f with
      | 35%Z => first [ mach_br_dir Hp HS true ltac:(by_bool Hb) | mach_br_dir Hp HS false ltac:(by_bool Hb) ]
      | _ => first [ mach_br_dir Hp HS false ltac:(by_bool Hb) | mach_br_dir Hp HS true ltac:(by_bool Hb) ]
      end
  end;
  clear Hb.

(* [comment removed for export] *)
Ltac mach_if Hp HS Hc :=
  first [ mach_br_dir Hp HS true ltac:(by_bool Hc)
        | mach_br_dir Hp HS false ltac:(by_bool Hc) ].

(* [comment removed for export] *)
Ltac mach_case Hp HS :=
  let Hc := fresh "Hc" in
  lazymatch goal with
  | |- realizes _ _ (tshape (MallocTree.mbind (if ?c then _ else _) _ _) _) =>
      destruct c eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc
  | |- realizes _ _ (tshape ((if ?c then _ else _) _) _) =>
      destruct c eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wbytes_win_out : forall s (a : word) (n : nat) bs m (x : word),
  acc_ok s a (Z.of_nat n) = true -> length bs = n ->
  ms_lo s <= bv_unsigned x < ms_hi s ->
  wbytes m a bs x = m x.
Proof.
  intros s a n bs m x Hok Hlen Hx.
  pose proof (u64_range a). pose proof (u64_range x).
  unfold acc_ok in Hok. apply Bool.orb_true_iff in Hok.
  destruct Hok as [Hk|Hk].
  - apply Z.leb_le in Hk. apply wbytes_above. rewrite Hlen. lia.
  - apply andb_prop in Hk as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    apply wbytes_below; rewrite ?Hlen; lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_out : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x) ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [H|H]; [apply wbytes_below; assumption | apply wbytes_above; assumption].
Qed.

Lemma wbytes_nn : forall bs m (a x : word), m x <> None -> wbytes m a bs x <> None.
Proof. intros bs m a x H. apply (wbytes_grows bs m a x). exact H. Qed.

Lemma unfill_out : forall (a n : word) m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  unfill a n m x = m x.
Proof.
  intros a n m x H. unfold unfill.
  destruct (bv_unsigned a <=? bv_unsigned x) eqn:E1; destruct (bv_unsigned x <? bv_unsigned a + bv_unsigned n) eqn:E2;
    cbn; try reflexivity.
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(* [comment removed for export] *)
Lemma zfill_out : forall (a n : word) m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  zfill a n m x = m x.
Proof.
  intros a n m x H. unfold zfill, zmem.
  destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n))%bool eqn:E;
    [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma zfill_nn : forall (a n : word) m (x : word), m x <> None -> zfill a n m x <> None.
Proof.
  intros a n m x H. unfold zfill, zmem.
  destruct (_ && _)%bool; [discriminate | exact H].
Qed.

Lemma apply_zeros1_out : forall (a n : word) m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  apply_zeros m [(a, n)] x = m x.
Proof. intros a n m x H. rewrite apply_zeros_one. apply zfill_out. exact H. Qed.

Lemma apply_zeros1_nn : forall (a n : word) m (x : word), m x <> None -> apply_zeros m [(a, n)] x <> None.
Proof. intros a n m x H. rewrite apply_zeros_one. apply zfill_nn. exact H. Qed.

Lemma apply_zeros0 : forall m, apply_zeros m [] = m.
Proof. reflexivity. Qed.

Lemma length_w2l : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros. apply length_N_to_le_bytes. Qed.

(* [comment removed for export] *)
Lemma u_v_addi : forall (x : word) (k : Z), 0 <= bv_unsigned x + k < 2^64 ->
  bv_unsigned (v_addi x k) = bv_unsigned x + k.
Proof.
  intros x k H. unfold v_addi. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma v_addi_addi' : forall (x : word) (a b : Z), v_addi (v_addi x a) b = v_addi x (a + b).
Proof. intros x a b. exact (at_addi x a b). Qed.

(* [comment removed for export] *)
Definition in_frame (sp : word) (F : Z) (x : word) : Prop :=
  bv_unsigned sp - F <= bv_unsigned x < bv_unsigned sp.

Ltac atop_norm_in H :=
  cbn [ms_lo ms_hi ms_mem ms_vm upd] in H;
  rewrite ?alloc_top_vm_mmap, ?alloc_top_vm_noacc, ?alloc_top_vm_munmap, ?alloc_top_vm_fixed_ok,
    ?alloc_top_vm_fixed_destroy, ?alloc_top_vm_unprotect, ?alloc_top_vm_brk_grow in H.
Ltac atop_norm :=
  cbn [ms_lo ms_hi ms_mem ms_vm upd];
  rewrite ?alloc_top_vm_mmap, ?alloc_top_vm_noacc, ?alloc_top_vm_munmap, ?alloc_top_vm_fixed_ok,
    ?alloc_top_vm_fixed_destroy, ?alloc_top_vm_unprotect, ?alloc_top_vm_brk_grow.

Ltac note_win HI :=
  let H1 := fresh "Hwlo" in let H2 := fresh "Hwhi" in let H3 := fresh "Hwtop" in
  pose proof (minv_lo _ _ HI) as H1; pose proof (minv_hi _ _ HI) as H2;
  pose proof (minv_ceil_num _ _ HI) as H3;
  cbn [ms_lo ms_hi ms_mem ms_vm upd] in H1, H2; atop_norm_in H3.

(* [comment removed for export] *)
Ltac arith_only :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ <= _)%Z => fail | (_ < _)%Z => fail | (_ >= _)%Z => fail | (_ > _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail | (_ < _ < _)%Z => fail
      | @eq Z _ _ => fail | ~ _ => fail | _ /\ _ => fail | _ \/ _ => fail
      | _ => clear H
      end
  end.
(* [comment removed for export] *)
Module RefLiaL2.
  Import Ltac2.
  Ltac2 arith_ty (ty : constr) : bool :=
    lazy_match! ty with
    | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
    | @eq Z _ _ => true | ~ _ => true | _ /\ _ => true | _ \/ _ => true
    | _ => false
    end.
  Ltac2 keep_arith1 () :=
    let hs := Control.hyps () in
    let ids := List.map (fun (h : ident * constr option * constr) => let (id, _, _) := h in id)
                 (List.filter (fun (h : ident * constr option * constr) => let (_, _, ty) := h in arith_ty ty) hs) in
    Std.keep ids.
  Ltac2 keep_arith () := Control.enter keep_arith1.
End RefLiaL2.
Ltac arith_only_fast := ltac2:(RefLiaL2.keep_arith ()).
(* [comment removed for export] *)
Ltac lia_nodiv :=
  intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook;
  xlia zchecker.
Ltac alia := first [ arith_only_fast | arith_only ]; first [ lia_nodiv | lia ].

(* [comment removed for export] *)
Ltac uaddr :=
  cbn [ms_lo ms_hi ms_mem ms_vm upd];
  rewrite ?v_addi_addi'; rewrite ?u_v_addi by alia.
(* [comment removed for export] *)
Ltac uaddrH H :=
  cbn [ms_lo ms_hi ms_mem ms_vm upd] in H;
  rewrite ?v_addi_addi' in H; rewrite ?u_v_addi in H by alia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac peel_by L side := etransitivity; [ apply L; side | ].
Ltac peel1 x :=
  first
    [ (* [comment removed for export] *)
      match goal with
      | Hf : forall a : word, in_frame _ _ a -> ?m1 a = ?m0 a |- ?m1 x = _ =>
          peel_by (Hf x) ltac:(unfold in_frame; uaddr; alia)
      end
    | (* [comment removed for export] *)
      match goal with
      | Hok : acc_ok ?s ?a (Z.of_nat ?n) = true |- wbytes ?m ?a ?bs x = _ =>
          peel_by (wbytes_win_out s a n bs m x Hok (length_w2l _ _)) ltac:(uaddr; alia)
      | Hok : acc_ok ?s ?a ?z = true |- wbytes ?m ?a ?bs x = _ =>
          peel_by (wbytes_win_out s a (Z.to_nat z) bs m x Hok (length_w2l _ _)) ltac:(uaddr; alia)
      end
    | (* [comment removed for export] *)
      lazymatch goal with
      | |- wbytes ?m ?a ?bs x = _ =>
          peel_by (wbytes_out bs m a x) ltac:(rewrite ?length_w2l; uaddr; alia)
      end
    | (* [comment removed for export] *)
      lazymatch goal with
      | |- unfill ?a ?n ?m x = _ => peel_by (unfill_out a n m x) ltac:(uaddr; alia)
      end
    | (* [comment removed for export] *)
      lazymatch goal with
      | |- zfill ?a ?n ?m x = _ => peel_by (zfill_out a n m x) ltac:(uaddr; alia)
      | |- apply_zeros ?m [(?a, ?n)] x = _ => peel_by (apply_zeros1_out a n m x) ltac:(uaddr; alia)
      | |- apply_zeros ?m [] x = _ => rewrite (apply_zeros0 m)
      end
    | (* [comment removed for export] *)
      match goal with
      | HWb : mwin _ ?m0 _ _ ?mb |- ?mb x = _ =>
          peel_by (proj1 HWb x) ltac:(uaddr; alia)
      end
    | (* [comment removed for export] *)
      match goal with
      | Hj : forall a : word, _ -> ?m1 a = ?m0 a |- ?m1 x = _ =>
          peel_by (Hj x) ltac:(uaddr; alia)
      end
    | (* [comment removed for export] *)
      match goal with
      | Hp : forall a : word, _ -> _ -> ?m1 a = ?m0 a |- ?m1 x = _ =>
          peel_by (Hp x) ltac:(uaddr; alia)
      end ].

(* [comment removed for export] *)
Ltac peel_at x :=
  lazymatch goal with
  | |- ?l = ?r => tryif constr_eq l r then reflexivity else peel1 x
  end.
Ltac peel x := repeat (progress (peel_at x)).

(* [comment removed for export] *)
Lemma nn_rew : forall (u v : option byte), u = v -> v <> None -> u <> None.
Proof. intros u v -> H. exact H. Qed.
Ltac nn_by L side := eapply nn_rew; [ apply L; side | ].
Ltac nn_at x :=
  repeat first
    [ lazymatch goal with
      | |- wbytes _ _ _ x <> None => apply wbytes_nn
      | |- unfill ?a ?n ?m x <> None => nn_by (unfill_out a n m x) ltac:(uaddr; alia)
      | |- zfill ?a ?n ?m x <> None => apply zfill_nn
      | |- apply_zeros ?m [(?a, ?n)] x <> None => apply apply_zeros1_nn
      | |- apply_zeros ?m [] x <> None => rewrite (apply_zeros0 m)
      end
    | match goal with
      | Hn : forall a : word, in_frame _ _ a -> ?m1 a <> None |- ?m1 x <> None =>
          apply Hn; unfold in_frame; uaddr; alia
      end
    | match goal with
      | HWb : mwin _ _ _ _ ?mb |- ?mb x <> None =>
          first [ apply (proj2 HWb); uaddr; alia
                | nn_by (proj1 HWb x) ltac:(uaddr; alia) ]
      | Hn : forall a : word, (?lo <= bv_unsigned a < ?hi)%Z -> ?m1 a <> None |- ?m1 x <> None =>
          first [ apply Hn; uaddr; alia
                | match goal with
                  | Hp : forall a : word, _ -> _ -> m1 a = ?m0 a |- _ =>
                      first [ nn_by (Hp x) ltac:(uaddr; alia)
                            | destruct (Z_lt_le_dec (bv_unsigned x) lo);
                              [ nn_by (Hp x) ltac:(uaddr; alia)
                              | destruct (Z_lt_le_dec (bv_unsigned x) hi);
                                [ apply Hn; uaddr; alia
                                | nn_by (Hp x) ltac:(uaddr; alia) ] ] ]
                  end ]
      | Hj : forall a : word, _ -> ?m1 a = ?m0 a |- ?m1 x <> None =>
          nn_by (Hj x) ltac:(uaddr; alia)
      | Hp : forall a : word, _ -> _ -> ?m1 a = ?m0 a |- ?m1 x <> None =>
          nn_by (Hp x) ltac:(uaddr; alia)
      end ].

(* [comment removed for export] *)
Definition frame_base (F : Z) (m : word -> option byte) : Prop := True.

Ltac mark_frame F :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst _ _ ?m _) _) _ => pose proof (I : frame_base F m)
  end.

Ltac frame_facts HW mnew :=
  try (lazymatch goal with
       | HPm : frame_base ?F ?mmP |- _ =>
           lazymatch type of HW with
           | mwin _ _ ?sp0 ?D0 _ =>
               let H1 := fresh "Hfr" in let H2 := fresh "Hnnf" in
               let x := fresh "x" in let Hx := fresh "Hx" in
               try (assert (H2 : forall x : word, in_frame sp0 D0 x -> mnew x <> None)
                      by (intros x Hx; unfold in_frame in Hx; nn_at x));
               try (assert (H1 : forall x : word, in_frame sp0 F x -> mnew x = mmP x)
                      by (intros x Hx; unfold in_frame in Hx; peel x))
           end
       end).

(* [comment removed for export] *)
Ltac win_same :=
  lazymatch goal with
  | |- forall a : word, _ -> ?m1 a = ?m0 a =>
      let x := fresh "x" in let Hw := fresh "Hw" in
      intros x Hw; uaddrH Hw; peel x; try reflexivity
  end.

(* [comment removed for export] *)
Ltac win_pres :=
  lazymatch goal with
  | |- forall a : word, _ -> _ -> ?m1 a = ?m0 a =>
      let x := fresh "x" in let Hw := fresh "Hw" in let Hf := fresh "Hf" in
      intros x Hw Hf; uaddrH Hw; uaddrH Hf; peel x; try reflexivity
  end.

(* [comment removed for export] *)
Ltac win_nn :=
  lazymatch goal with
  | |- forall a : word, _ -> ?m1 a <> None =>
      let x := fresh "x" in let Hf := fresh "Hf" in
      intros x Hf; uaddrH Hf; nn_at x
  end.

(* [comment removed for export] *)
Ltac frame_ok :=
  lazymatch goal with
  | |- store_ok _ ?m ?a ?n = true =>
      apply store_ok_of_all; [ uaddr; alia |];
      let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx; uaddrH Hx;
      let Hs := fresh in
      assert (Hs : m x <> None) by nn_at x;
      unfold wview; destruct (m x); [discriminate | exfalso; apply Hs; reflexivity]
  end.

(* [comment removed for export] *)
Ltac base_mem m :=
  lazymatch m with
  | wbytes ?m0 _ _ => base_mem m0
  | unfill _ _ ?m0 => base_mem m0
  | zfill _ _ ?m0 => base_mem m0
  | apply_zeros ?m0 _ => base_mem m0
  | ?v => v
  end.

Ltac find_store m a k :=
  match m with
  | context [wbytes ?m0 a ?bs] => k constr:(wbytes m0 a bs)
  | _ =>
      let v := base_mem m in
      first
        [ match goal with
          | Hf : forall y : word, in_frame _ _ y -> v y = ?M y |- _ => find_store M a k
          end
        | match goal with
          | Hj : forall y : word, _ -> v y = ?M y |- _ => find_store M a k
          | Hp : forall y : word, _ -> _ -> v y = ?M y |- _ => find_store M a k
          end ]
  end.

Ltac peel_to T x :=
  repeat (lazymatch goal with
          | |- T x = _ => fail
          | |- _ => peel1 x
          end);
  reflexivity.

Ltac frame_rd :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a (word_to_le_bytes 8 _)) ?a 8%nat = Some _ =>
      apply rdn_wbytes_hit8; uaddr; alia
  | |- rdn ?segs ?m ?a ?n = Some _ =>
      first
        [ match goal with H : rdn _ m a n = Some _ |- _ => exact H end
        | find_store m a ltac:(fun T =>
            rewrite (rdn_ext segs n m T);
            [ apply rdn_wbytes_hit8; uaddr; alia
            | rewrite ?length_w2l; uaddr; alia
            | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; uaddrH Hx; peel_to T x ]) ]
  | |- ?g => fail "frame_rd:" g
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zsum_norm :=
  repeat match goal with
  | |- context [v_addi _ ?z] =>
      lazymatch z with
      | (?a + ?b)%Z => check_closed_term z; let z' := eval vm_compute in z in change z with z'
      end
  end.
Ltac spaddr := regnorm; imm_norm; rewrite ?v_addi_addi'; zsum_norm.

Ltac mach_stk_st Hp HS Hag HI :=
  cur_instr ltac:(fun w i =>
    let go L :=
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply L; [ solveF | reflexivity | solveD
                    | spaddr; reflexivity
                    | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity
                    | frame_ok ]
        | mpost HS ];
      (* [comment removed for export] *)
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst _ _ (wbytes ?m ?a ?bs) _) _) _ =>
          apply (magree_wbytes_win _ m a bs) in Hag;
          [ | rewrite length_w2l; uaddr; alia
            | cbn [ms_lo ms_hi upd]; uaddr; alia
            | rewrite length_w2l; cbn [ms_lo ms_hi upd]; uaddr; alia ]
      end in
    lazymatch i with
    | Store SZ8 _ _ _ => go step_sd_at
    | Store SZ4 _ _ _ => go step_sw_at
    | _ => fail "mach_stk_st:" i
    end).

Ltac mach_stk_ld Hp HS Hag HI :=
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | Load SZ8 true _ _ _ =>
        eapply rz_step_p; [ mpure Hp | reflexivity
          | eapply step_ld_at; [ solveF | reflexivity | solveD | reflexivity
                               | spaddr; reflexivity
                               | frame_rd
                               | apply bytes_le_to_Z_8 ]
          | mpost HS ]
    | _ => fail "mach_stk_ld:" i
    end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma callee_saved_of_num : forall r : reg, cs_num (bv_unsigned r) = true -> callee_saved r.
Proof.
  intros r H. unfold callee_saved. unfold cs_num in H.
  repeat (apply Bool.orb_true_iff in H; destruct H as [H|H]);
    try (apply Z.eqb_eq in H; first [left; apply bv_eq; exact H | right; left; apply bv_eq; exact H
      | right; right; left; apply bv_eq; exact H | right; right; right; left; apply bv_eq; exact H
      | right; right; right; right; left; apply bv_eq; exact H]).
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. right; right; right; right; right. lia.
Qed.

(* [comment removed for export] *)
Ltac cs_facts Hcs :=
  let one z :=
    let r := constr:(@BV 5 z I) in
    try (let H := fresh "Hk" in
         assert (H : getr _ r = getr _ r) by (apply Hcs; apply callee_saved_of_num; reflexivity)) in
  one 2%Z; one 3%Z; one 4%Z; one 8%Z; one 9%Z; one 18%Z; one 19%Z; one 20%Z; one 21%Z;
  one 22%Z; one 23%Z; one 24%Z; one 25%Z; one 26%Z; one 27%Z.

Lemma sp_mod16 : forall (sp : word) (k : Z),
  bv_unsigned sp mod 16 = 0 -> k mod 16 = 0 -> 0 <= bv_unsigned sp + k < 2^64 ->
  bv_unsigned (v_addi sp k) mod 16 = 0.
Proof.
  intros sp k Hs Hk Hr. rewrite u_v_addi by exact Hr.
  rewrite Z.add_mod, Hs, Hk by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac call_side Hp Hag HI HW HS :=
  lazymatch goal with
  | |- md_pure _ => mpure Hp
  | |- ms_vm _ = m_vmmaps _ => symmetry; apply with_vmmaps_vmmaps
  | |- magree _ _ => exact Hag
  | |- wtop _ => exact (minv_ceil _ _ HI)
  | |- getr _ _ = _ => regnorm; imm_norm; rewrite ?v_addi_addi', ?v_addi_0; first [reflexivity | klitsg; first [reflexivity | bveq]]
  | |- bv_unsigned _ mod 16 = 0 => first [assumption | apply sp_mod16; [assumption | reflexivity | uaddr; alia]]
  | |- ret_ok _ => first [assumption | apply ret_ok_even; vm_compute; reflexivity]
  | |- tsafe _ _ => first [ exact HS | exact (tsafe_bind_inv _ _ _ HS) ]
  | |- forall a : word, _ -> ?m a <> None => win_nn
  | |- context [alloc_ceiling] => rewrite alloc_ceiling_val; uaddr; alia
  | |- _ => uaddr; alia
  end.

(* [comment removed for export] *)
Ltac call_intro Hag HI HW HS :=
  let r := fresh "cr" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let HP := fresh "HS" in let Hag' := fresh "Hag" in let Hlo' := fresh "Hlo'" in let Hhi' := fresh "Hhi'" in
  let Hr1 := fresh "Hres" in let Hr2 := fresh "Hres" in let Hsp := fresh "Hsp" in
  let Hcs := fresh "Hcs" in let Hpres := fresh "Hpres" in let Hnn := fresh "Hnn" in let HInew := fresh "HI" in
  let Htop' := fresh "Htop'" in let Hwk := fresh "Hwkeep" in
  first
    [ intros r s' mm' R' HP Hag' Hlo' Hhi' Htop' Hr1 Hsp Hcs Hpres Hnn Hwk;
      lazymatch type of Hwk with forall x : reg, wreg _ x = false -> _ => idtac end;
      keep_facts Hwk
    | intros r s' mm' R' HP Hag' Hlo' Hhi' Htop' Hr1 Hsp Hcs Hpres Hnn;
      lazymatch type of Hnn with forall a : word, _ -> _ <> None => idtac end
    | intros r s' mm' R' HP Hag' Hlo' Hhi' Htop' Hr1 Hr2 Hsp Hcs Hpres Hnn;
      lazymatch type of Hnn with forall a : word, _ -> _ <> None => idtac end;
      destruct r as [?r1 ?r2]; cbn [fst snd] in Hr1, Hr2, HP |- * ];
  cbv beta in HP; rewrite with_vmmaps_twice; cbv beta;
  pose proof (minv_same _ _ _ HI Hlo' Hhi' Htop') as HInew;
  cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hsp;
  cbv delta [ALLOC_STACK] in Hpres, Hnn;
  uaddrH Hpres; uaddrH Hnn;
  clear Hlo' Hhi' Htop'; clear HS Hag HI; rename HP into HS; rename Hag' into Hag; rename HInew into HI;
  note_win HI;
  frame_facts HW mm';
  cs_facts Hcs;   (* [comment removed for export] *)
  mnorm HS.

(* [comment removed for export] *)
Ltac mach_call Hp HS Hag HI HW THM :=
  mach_jal Hp HS;
  apply rz_bind_shape;
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (_ ?s) _) =>
      eapply rz_at_pc;
      [ eapply (THM (with_vmmaps (ms_vm s) md) R mm rom s);
        first [ lazymatch goal with |- forall (r : _) (s' : mstate), _ => call_intro Hag HI HW HS end
              | call_side Hp Hag HI HW HS ]
      | bveq ]
  end.

(* [comment removed for export] *)
Lemma v_addi_back : forall (x : word) (a b : Z), a + b = 0 -> v_addi (v_addi x a) b = x.
Proof. intros x a b H. rewrite v_addi_addi', H. apply v_addi_0. Qed.

Lemma v_addi_k0 : forall (x : word) (k : Z), k = 0 -> v_addi x k = x.
Proof. intros x k ->. apply v_addi_0. Qed.

Lemma not_cs_neq : forall (x r : reg), callee_saved x -> ~ callee_saved r -> x <> r.
Proof. intros x r Hx Hr ->. exact (Hr Hx). Qed.

(* [comment removed for export] *)
Lemma callee_saved_cs_num : forall r : reg, callee_saved r -> cs_num (bv_unsigned r) = true.
Proof.
  intros r Hc. unfold cs_num. destruct Hc as [E|[E|[E|[E|[E|R]]]]]; try (subst r; reflexivity).
  apply Bool.orb_true_iff; right. apply Bool.andb_true_iff; split; apply Z.leb_le; lia.
Qed.
Lemma not_callee_saved_of_num : forall r : reg, cs_num (bv_unsigned r) = false -> ~ callee_saved r.
Proof. intros r H Hc. rewrite (callee_saved_cs_num r Hc) in H. discriminate H. Qed.

(* [comment removed for export] *)
Ltac not_cs :=
  first [ apply not_callee_saved_of_num; reflexivity
        | unfold callee_saved; let HH := fresh in intros HH;
          repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]);
          revert HH; imm_norm; lia ].

(* [comment removed for export] *)
Ltac cs_chain Hx :=
  repeat match goal with
  | |- ?a = ?a => reflexivity
  | |- getr (regupd ?R ?r ?v) ?x = _ =>
      rewrite (getr_other R r v x (not_cs_neq x r Hx ltac:(not_cs)))
  | Hk : forall r : reg, wreg ?wl r = false -> getr ?R1 r = getr _ r |- getr ?R1 ?x = _ =>
      rewrite (Hk x (wreg_cs wl x Hx eq_refl))
  end;
  reflexivity.

Lemma cs_enum : forall x : reg, callee_saved x ->
  x = 2%bv \/ x = 3%bv \/ x = 4%bv \/ x = 8%bv \/ x = 9%bv \/ x = 18%bv \/ x = 19%bv \/ x = 20%bv \/ x = 21%bv \/ x = 22%bv \/
  x = 23%bv \/ x = 24%bv \/ x = 25%bv \/ x = 26%bv \/ x = 27%bv.
Proof.
  intros x Hx. unfold callee_saved in Hx.
  destruct Hx as [H|[H|[H|[H|[H|H]]]]]; try (rewrite H; tauto).
  assert (E : x = Z_to_bv 5 (bv_unsigned x)) by (apply bv_eq; rewrite Z_to_bv_unsigned; pose proof (u5_range x); unfold bv_wrap; rewrite Z.mod_small by (change (bv_modulus 5) with 32%Z; lia); reflexivity).
  assert (C : bv_unsigned x = 18 \/ bv_unsigned x = 19 \/ bv_unsigned x = 20 \/ bv_unsigned x = 21 \/ bv_unsigned x = 22 \/
             bv_unsigned x = 23 \/ bv_unsigned x = 24 \/ bv_unsigned x = 25 \/ bv_unsigned x = 26 \/ bv_unsigned x = 27) by lia.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]];
    repeat (first [ apply bv_eq; rewrite C; reflexivity | left; apply bv_eq; rewrite C; reflexivity | right ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kp_skip_w : forall (wl : list Z) (R R2 : bvmap 5 word) (rd : reg) (v : word),
  wreg wl rd = true ->
  (forall x : reg, wreg wl x = false -> getr R2 x = getr R x) ->
  forall x : reg, wreg wl x = false -> getr (regupd R2 rd v) x = getr R x.
Proof.
  intros wl R R2 rd v Hrd IH x Hx. rewrite (getr_other_w wl R2 rd v x Hrd Hx). apply IH; exact Hx.
Qed.
Lemma kp_restore_w : forall (wl : list Z) (R R2 : bvmap 5 word) (rd : reg) (v : word),
  getr (regupd R2 rd v) rd = getr R rd ->
  (forall x : reg, wreg (bv_unsigned rd :: wl) x = false -> getr R2 x = getr R x) ->
  forall x : reg, wreg wl x = false -> getr (regupd R2 rd v) x = getr R x.
Proof.
  intros wl R R2 rd v Hv IH x Hx. destruct (decide (x = rd)) as [->|ne]; [exact Hv|].
  rewrite getr_other by exact ne. apply IH. unfold wreg in *. cbn [existsb]. rewrite Hx.
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned rd)) as [E|NE]; [|reflexivity].
  exfalso. apply ne. apply bv_eq. exact E.
Qed.
(* [comment removed for export] *)
Definition noncs_nums : list Z := [0; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%Z.
Lemma cs_to_wreg : forall (R R' : bvmap 5 word),
  (forall x : reg, wreg noncs_nums x = false -> getr R' x = getr R x) ->
  forall x : reg, callee_saved x -> getr R' x = getr R x.
Proof. intros R R' H x Hx. apply H. apply (wreg_cs noncs_nums x Hx). reflexivity. Qed.
(* [comment removed for export] *)
Lemma wreg_noncs_cs : forall (wl : list Z) (x : reg),
  forallb (fun z => cs_num z || existsb (Z.eqb z) wl)%bool
          [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%Z = true ->
  wreg wl x = false -> callee_saved x.
Proof.
  intros wl x Hall Hx.
  destruct (cs_num (bv_unsigned x)) eqn:E; [apply callee_saved_of_num; exact E|]. exfalso.
  pose proof (u5_range x) as Hr.
  rewrite forallb_forall in Hall.
  assert (Hin : In (bv_unsigned x) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%Z).
  { cbn [In]. lia. }
  specialize (Hall _ Hin). cbn beta in Hall. rewrite E in Hall. cbn [orb] in Hall.
  unfold wreg in Hx. rewrite Hall in Hx. discriminate Hx.
Qed.

(* [comment removed for export] *)
Ltac kp_value :=
  regnorm; imm_norm; rewrite ?v_addi_0;
  first [ reflexivity | apply v_addi_back; reflexivity
        | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity | klitsg; first [reflexivity | bveq]] ].

(* [comment removed for export] *)
Ltac kp_base per_reg :=
  first [ lazymatch goal with |- forall x : reg, _ -> getr ?A x = getr ?B x => constr_eq A B end;
          let x := fresh "x" in intros x _; reflexivity
        | assumption
        | keep_tac
        | let x := fresh "x" in let Hx := fresh "Hx" in
          intros x Hx;
          first [ lazymatch type of Hx with wreg ?wl _ = false =>
                  match goal with
                  | Hk : forall r' : reg, wreg ?wl' r' = false -> getr _ r' = getr _ r' |- getr _ x = _ =>
                      exact (Hk x (wreg_sub wl wl' x eq_refl Hx))
                  | Hc : forall r' : reg, callee_saved r' -> getr _ r' = getr _ r' |- getr _ x = _ =>
                      exact (Hc x (wreg_noncs_cs wl x eq_refl Hx))
                  end end
                | per_reg x Hx ] ].

Ltac kp_chain_w per_reg :=
  lazymatch goal with
  | |- forall x : reg, wreg ?wl x = false -> getr (regupd ?R2 ?rd ?v) x = getr ?R x =>
      first [ apply (kp_skip_w wl R R2 rd v); [ reflexivity | kp_chain_w per_reg ]
            | apply (kp_restore_w wl R R2 rd v);
              [ kp_value
              | let u := eval vm_compute in (bv_unsigned rd) in
                change (bv_unsigned rd) with u; kp_chain_w per_reg ] ]
  | |- _ => kp_base per_reg
  end.

(* [comment removed for export] *)
Ltac cs_per_reg x Hx :=
  lazymatch type of Hx with wreg ?wl _ = false =>
    let Hc := fresh "Hcsx" in
    pose proof (wreg_noncs_cs wl x eq_refl Hx) as Hc;
    first
      [ regnorm; cs_chain Hc
      | destruct (cs_enum x Hc) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        kp_value ]
  end.

Ltac cs_goal :=
  first
    [ apply cs_to_wreg; kp_chain_w cs_per_reg
    | let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx;
      first
        [ regnorm; cs_chain Hx
        | destruct (cs_enum x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          regnorm; imm_norm;
          first [ reflexivity | apply v_addi_back; reflexivity
                | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity | klitsg; first [reflexivity | bveq]] ] ] ].

(* [comment removed for export] *)
Lemma reg_enum : forall x : reg,
  x = 0%bv \/ x = 1%bv \/ x = 2%bv \/ x = 3%bv \/ x = 4%bv \/ x = 5%bv \/ x = 6%bv \/ x = 7%bv \/
  x = 8%bv \/ x = 9%bv \/ x = 10%bv \/ x = 11%bv \/ x = 12%bv \/ x = 13%bv \/ x = 14%bv \/ x = 15%bv \/
  x = 16%bv \/ x = 17%bv \/ x = 18%bv \/ x = 19%bv \/ x = 20%bv \/ x = 21%bv \/ x = 22%bv \/ x = 23%bv \/
  x = 24%bv \/ x = 25%bv \/ x = 26%bv \/ x = 27%bv \/ x = 28%bv \/ x = 29%bv \/ x = 30%bv \/ x = 31%bv.
Proof.
  intros x.
  assert (E : x = Z_to_bv 5 (bv_unsigned x)) by (apply bv_eq; rewrite Z_to_bv_unsigned; pose proof (u5_range x); unfold bv_wrap; rewrite Z.mod_small by (change (bv_modulus 5) with 32%Z; lia); reflexivity).
  pose proof (u5_range x) as Hr.
  assert (C : bv_unsigned x = 0 \/ bv_unsigned x = 1 \/ bv_unsigned x = 2 \/ bv_unsigned x = 3 \/ bv_unsigned x = 4 \/ bv_unsigned x = 5 \/ bv_unsigned x = 6 \/ bv_unsigned x = 7 \/
             bv_unsigned x = 8 \/ bv_unsigned x = 9 \/ bv_unsigned x = 10 \/ bv_unsigned x = 11 \/ bv_unsigned x = 12 \/ bv_unsigned x = 13 \/ bv_unsigned x = 14 \/ bv_unsigned x = 15 \/
             bv_unsigned x = 16 \/ bv_unsigned x = 17 \/ bv_unsigned x = 18 \/ bv_unsigned x = 19 \/ bv_unsigned x = 20 \/ bv_unsigned x = 21 \/ bv_unsigned x = 22 \/ bv_unsigned x = 23 \/
             bv_unsigned x = 24 \/ bv_unsigned x = 25 \/ bv_unsigned x = 26 \/ bv_unsigned x = 27 \/ bv_unsigned x = 28 \/ bv_unsigned x = 29 \/ bv_unsigned x = 30 \/ bv_unsigned x = 31) by lia.
  clear E.
  repeat (destruct C as [C|C];
    [ repeat (first [ apply bv_eq; rewrite C; reflexivity | left; apply bv_eq; rewrite C; reflexivity | right ]) |]).
  repeat (first [ apply bv_eq; rewrite C; reflexivity | left; apply bv_eq; rewrite C; reflexivity | right ]).
Qed.

Ltac wkeep_per_reg x Hx :=
  destruct (reg_enum x) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  first [ discriminate Hx | kp_value ].

Ltac wkeep_goal :=
  first
    [ kp_chain_w wkeep_per_reg
    | keep_tac
    | let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx;
      destruct (reg_enum x) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
      first [ discriminate Hx
            | regnorm; imm_norm;
              first [ reflexivity | apply v_addi_back; reflexivity
                    | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity | klitsg; first [reflexivity | bveq]] ] ] ].

Ltac tail_intro Hag HI HW HS HK :=
  let r := fresh "cr" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let HP := fresh "HP" in let Hag' := fresh "Hag" in let Hlo' := fresh "Hlo'" in let Hhi' := fresh "Hhi'" in
  let Hr1 := fresh "Hres" in let Hsp := fresh "Hsp" in let Hcs := fresh "Hcs" in
  let Hpres := fresh "Hpres" in let Hnn := fresh "Hnn" in let Htop' := fresh "Htop'" in
  intros r s' mm' R' HP Hag' Hlo' Hhi' Htop' Hr1 Hsp Hcs Hpres Hnn;
  rewrite ?with_vmmaps_twice;
  uaddrH Hpres; uaddrH Hnn;
  eapply (HK r s' mm' R');
  [ exact HP
  | exact Hag'
  | rewrite Hlo'; cbn [ms_lo ms_hi ms_vm ms_mem upd]; exact (minv_lo _ _ HI)
  | rewrite Hhi'; cbn [ms_lo ms_hi ms_vm ms_mem upd]; exact (minv_hi _ _ HI)
  | rewrite Htop'; atop_norm; exact (minv_top _ _ HI)
  | .. ];
  [ exact Hr1
  | rewrite Hsp; first [reflexivity | apply v_addi_k0; reflexivity | apply v_addi_back; reflexivity
                       | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity]]
  | let x := fresh "x" in let Hx := fresh "Hx" in
    intros x Hx; rewrite (Hcs x Hx); revert x Hx; cs_goal
  | win_pres
  | win_nn ].

Ltac mach_tailcall Hp HS Hag HI HW HK THM :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (_ ?s) ?L) =>
      eapply rz_at_pc;
      [ eapply (THM (with_vmmaps (ms_vm s) md) R mm rom s);
        first [ lazymatch goal with |- forall (r : _) (s' : mstate), _ => tail_intro Hag HI HW HS HK end
              | call_side Hp Hag HI HW HS ]
      | bveq ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mach_ret Hp HS Hag HK HI Hret :=
  lazymatch goal with
  | |- realizes _ (mkCfg _ ?md) (tshape (MallocTree.mret ?r ?s') ?L) =>
      unfold MallocTree.mret in HS; cbn [tsafe] in HS;
      change (tshape (MallocTree.mret r s') L) with (L r s');
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply step_jalr_x0; [solveF | reflexivity | solveD | regnorm; reflexivity]
        | imm_norm ];
      lazymatch type of Hret with ret_ok ?ra =>
        first [ change (v_jalr ra 0) with ra | pose proof Hret as Hret_eq; unfold ret_ok in Hret_eq; rewrite Hret_eq; clear Hret_eq ] end;
      cbn [ms_lo ms_hi ms_vm ms_mem upd] in HS, Hag |- *;
      lazymatch type of HS with _ ?rv ?sf => eapply (HK rv sf) end;
      [ exact HS | exact Hag
      | cbn [ms_lo ms_hi ms_vm ms_mem upd]; exact (minv_lo _ _ HI)
      | cbn [ms_lo ms_hi ms_vm ms_mem upd]; exact (minv_hi _ _ HI)
      | atop_norm; exact (minv_top _ _ HI)
      | .. ];
      (* [comment removed for export] *)
      repeat match goal with
      | |- getr _ _ = _ => regnorm; imm_norm; rewrite ?v_addi_0;
                           first [reflexivity | apply v_addi_back; reflexivity
                                 | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity | klitsg; first [reflexivity | bveq]]
                                 | idtac]; fail
      | _ => fail
      end;
      try (regnorm; imm_norm; first [reflexivity | apply v_addi_back; reflexivity
                               | rewrite ?v_addi_addi'; first [reflexivity | apply v_addi_k0; reflexivity]]);
      try (lazymatch goal with |- forall x : reg, callee_saved x -> _ => cs_goal end);
      try win_pres;
      try win_nn;
      try (lazymatch goal with |- forall x : reg, wreg _ x = false -> _ => wkeep_goal end)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac branch_cond k :=
  cur_instr ltac:(fun w i =>
    let il := lit_instr i in
    lazymatch goal with
    | |- realizes _ (mkCfg (mkst ?R _ _ _) _) _ =>
      let mk c a b :=
        let H := fresh "Hcond" in
        eassert (H : c (getr R a) (getr R b) = _) by (regnorm; imm_norm; klitsg; reflexivity);
        lazymatch type of H with _ = ?t => clear H; k t end in
      lazymatch il with
      | Branch BC_EQ ?a ?b _  => mk c_eq a b
      | Branch BC_NE ?a ?b _  => mk c_eq a b
      | Branch BC_LT ?a ?b _  => mk c_lts a b
      | Branch BC_GE ?a ?b _  => mk c_lts a b
      | Branch BC_LTU ?a ?b _ => mk c_ltu a b
      | Branch BC_GEU ?a ?b _ => mk c_ltu a b
      end
    end).

(* [comment removed for export] *)
Ltac model_rewrite_cond HS Hc :=
  try (rewrite Hc in HS); try (rewrite Hc); mnorm HS.

(* [comment removed for export] *)
Ltac model_decide_closed HS :=
  let go c :=
    match c with
    | context [?a] =>
        lazymatch type of a with bool => idtac end;
        lazymatch a with true => fail | false => fail | _ => idtac end;
        check_closed_term a;
        let b := eval vm_compute in a in
        let Hc := fresh "Hcc" in
        assert (Hc : a = b) by (vm_compute; reflexivity);
        rewrite ?Hc in HS; rewrite ?Hc; clear Hc; mnorm HS
    end in
  repeat (lazymatch goal with
          | |- realizes _ _ (tshape (MallocTree.mbind (if ?c then _ else _) _ _) _) => go c
          | |- realizes _ _ (tshape ((if ?c then _ else _) _) _) => go c
          end).

(* [comment removed for export] *)
Ltac mach_branch Hp HS :=
  branch_cond ltac:(fun t =>
    first
      [ (* [comment removed for export] *)
        match goal with Hc : ?t' = _ |- _ => unify t' t; model_rewrite_cond HS Hc; mach_if Hp HS Hc end
      | (* [comment removed for export] *)
        check_closed_term t;
        let b := eval vm_compute in t in
        let Hc := fresh "Hc" in
        assert (Hc : t = b) by (vm_compute; reflexivity);
        model_decide_closed HS;
        mach_if Hp HS Hc; clear Hc
      | (* [comment removed for export] *)
        lazymatch goal with
        | |- realizes _ _ (tshape (MallocTree.mbind (if ?c then _ else _) _ _) _) =>
            match c with
            | context [?a] =>
                lazymatch type of a with bool => idtac end; unify a t;
                let Hc := fresh "Hc" in
                destruct a eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc
            end
        | |- realizes _ _ (tshape ((if ?c then _ else _) _) _) =>
            match c with
            | context [?a] =>
                lazymatch type of a with bool => idtac end; unify a t;
                let Hc := fresh "Hc" in
                destruct a eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc
            end
        end
      | let Hc := fresh "Hc" in
        destruct t eqn:Hc; rewrite ?Hc in HS; mnorm HS; mach_if Hp HS Hc ]).

(* [comment removed for export] *)
Ltac mach_passert HS :=
  let Hb := fresh "Hal" in let EQ := fresh "EQ" in
  destruct (tsafe_assert_inv _ _ _ _ HS) as [Hb EQ];
  rewrite EQ in HS; rewrite EQ; clear EQ; mnorm HS.

(* [comment removed for export] *)
Lemma v_addiw0_lw : forall v : word, v_addiw (v_lw v) 0 = v_lw v.
Proof.
  intros v. unfold v_addiw, v_lw. apply bv_eq. rewrite !Z_to_bv_unsigned.
  f_equal. rewrite Z.add_0_r.
  pose proof (bv_swrap_in_range 32 (bv_unsigned v) ltac:(discriminate)) as Hr.
  set (y := bv_swrap 32 (bv_unsigned v)) in *.
  change (bv_half_modulus 32) with (2^31)%Z in Hr.
  unfold bv_swrap. change (bv_half_modulus 32) with (2^31)%Z. unfold bv_wrap.
  change (bv_modulus 64) with (2^64)%Z. change (bv_modulus 32) with (2^32)%Z.
  assert (E : (y mod 2^64 = y \/ y mod 2^64 = y + 2^64)%Z).
  { destruct (Z_lt_le_dec y 0).
    - right. rewrite <- (Z.mod_add y 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
    - left. apply Z.mod_small. lia. }
  destruct E as [E|E]; rewrite E.
  - rewrite Z.mod_small by lia. lia.
  - replace (y + 2^64 + 2^31)%Z with ((y + 2^31) + 2^32 * 2^32)%Z by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma and3_mod4 : forall a : word, c_eq (v_andi a 3) (Z_to_bv 64 0) = true -> (bv_unsigned a mod 4 = 0)%Z.
Proof.
  intros a H. unfold c_eq, bv_eqb in H. apply Z.eqb_eq in H.
  unfold v_andi in H. rewrite !Z_to_bv_unsigned in H.
  pose proof (u64_range a).
  assert (Hl : (0 <= Z.land (bv_unsigned a) 3 <= 3)%Z).
  { split; [apply Z.land_nonneg; lia|].
    change 3%Z with (Z.ones 2) at 1. rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned a) (2^2)). lia. }
  change (bv_wrap 64 3) with 3%Z in H. change (bv_wrap 64 0) with 0%Z in H.
  rewrite bv_wrap_small in H by (change (bv_modulus 64) with (2^64)%Z; lia).
  change 3%Z with (Z.ones 2) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

Ltac mach_cas Hp HS Hag HI :=
  let Hok := fresh "Hok" in let Hso := fresh "Hso" in let EQ := fresh "EQ" in
  unfold m_sb, m_sh, m_sw, m_sd in HS |- *;
  let body ma mv :=
    lazymatch type of Hok with acc_ok ?scur _ _ = true =>
    match goal with
    | Hrd : rdn _ (ms_mem _) ma 4%nat = Some ?bs, Hv : bytes_le_to_Z ?bs = _,
      Hal : c_eq (v_andi ma 3) (Z_to_bv 64 0) = true |- realizes ?segs _ _ =>
      (* [comment removed for export] *)
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply (step_lrw segs _ _ _ _ _ _ _ ma bs (le_val bs));
          [ solveF | reflexivity | solveD | reflexivity
          | addr_tac
          | exact (and3_mod4 _ Hal)
          | exact (magree_rd _ _ _ 4%nat _ Hag (minv_lo64 _ _ HI) Hok Hrd)
          | exact Hv ]
        | ];
      (* [comment removed for export] *)
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply step_bne_ft_r; [ solveF | reflexivity | solveD | regnorm; reflexivity ] | ];
      (* [comment removed for export] *)
      rewrite EQ in HS; rewrite EQ; clear EQ;
      eapply rz_step_p; [ mpure Hp | reflexivity
        | eapply (step_scw_ok segs _ _ _ _ _ _ _ _ ma mv);
          [ solveF | reflexivity | solveD | reflexivity
          | addr_tac | addr_tac
          | exact (and3_mod4 _ Hal)
          | exact (magree_sok _ _ _ 4%nat Hag (minv_lo64 _ _ HI) Hok Hso) ]
        | mpost HS ];
      apply (magree_wbytes scur _ ma (word_to_le_bytes 4 mv) (ms_vm scur)) in Hag;
      (* [comment removed for export] *)
      mach_br_dir Hp HS false ltac:(first [apply c_eq_refl | vm_compute; reflexivity]);
      (* [comment removed for export] *)
      mach Hp HS;
      mach_br_dir Hp HS false ltac:(rewrite ?v_addiw0_lw; apply c_eq_refl)
    end end in
  lazymatch type of HS with
  | tsafe (MallocTree.mbind (m_st _ ?ma ?mv) _ _) _ =>
      destruct (tsafe_st_inv _ _ _ _ _ _ HS) as (Hok & Hso & EQ); body ma mv
  | tsafe (m_st _ ?ma ?mv _) _ =>
      destruct (tsafe_st_inv0 _ _ _ _ _ HS) as (Hok & Hso & EQ); body ma mv
  end;
  mnorm HS.

(* [comment removed for export] *)
Ltac mstep Hp HS Hag HI HW :=
  cur_instr ltac:(fun w i =>
    let il := lit_instr i in
    lazymatch goal with
    | |- realizes _ _ (tshape (MallocTree.mbind (massert (c_eq (v_andi (at_ _ 28) 3) _)) _ _) _) =>
        (* [comment removed for export] *)
        mach_passert HS
    | |- _ =>
    lazymatch il with
    | Load _ _ _ (@BV _ 2 _) _ => mach_stk_ld Hp HS Hag HI
    | Store _ (@BV _ 2 _) _ _ => mach_stk_st Hp HS Hag HI
    | Load _ _ _ _ _ => mach_ld Hp HS Hag HI
    | Store _ _ _ _ => mach_st Hp HS Hag HI
    | Lr _ _ _ _ _ => mach_cas Hp HS Hag HI
    | Branch _ _ _ _ =>
        lazymatch goal with
        | |- realizes _ _ (tshape (MallocTree.mbind (massert _) _ _) _) => mach_assert Hp HS
        | |- _ => mach_branch Hp HS
        end
    | Jalr _ _ _ => mach_jr Hp HS
    | Jal (@BV _ 0 _) _ => mach Hp HS
    | Jal _ _ => fail "mstep: jal call: manual"
    | _ => mach Hp HS
    end end).

Ltac mrun Hp HS Hag HI HW := repeat (mstep Hp HS Hag HI HW).

(* [comment removed for export] *)
Ltac mrun_until Hp HS Hag HI HW pcZ :=
  let pcZ := eval vm_compute in pcZ in
  repeat (cur_pc ltac:(fun u => tryif constr_eq u pcZ then fail else mstep Hp HS Hag HI HW)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac regval r k :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R _ _ _) _) _ =>
      let H := fresh "Hrv" in
      eassert (H : getr R r = _) by (regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity);
      lazymatch type of H with _ = ?v => clear H; k v end
  end.

Ltac cur_mstate HS k :=
  lazymatch type of HS with tsafe (?f ?sb) _ => k sb end.

(* [comment removed for export] *)
Ltac apply_cut tac :=
  lazymatch goal with
  | |- realizes _ ?C (tshape ?tg ?L) =>
      eapply (rz_tshape_eq C _ tg L); [ tac | tnorm_eq ]
  end.

Ltac use_cut CUT res Hag HI HW HS :=
  cur_mstate HS ltac:(fun sb =>
    lazymatch res with
    | @nil Z => apply_cut ltac:(eapply (CUT tt sb))
    | @cons Z ?r1 (@nil Z) =>
        regval constr:(@BV 5 r1 I) ltac:(fun v1 => apply_cut ltac:(eapply (CUT v1 sb)))
    | @cons Z ?r1 (@cons Z ?r2 (@nil Z)) =>
        regval constr:(@BV 5 r1 I) ltac:(fun v1 =>
          regval constr:(@BV 5 r2 I) ltac:(fun v2 => apply_cut ltac:(eapply (CUT v1 v2 sb))))
    end);
  [ exact Hag | exact HI | win_same | keep_tac | .. ];
  [ .. | exact_HS HS ]; try (regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity).

Ltac join_intro Hag HI HW HS res :=
  let x := fresh "jv" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HInew := fresh "HI" in
  clear Hag HS;
  lazymatch res with
  | @nil Z => intros x s' mm' R' Hag HInew HJ Hkeep HS
  | @cons Z _ (@nil Z) => let Hres := fresh "Hres" in intros x s' mm' R' Hag HInew HJ Hkeep Hres HS
  | _ => let Hr1 := fresh "Hres" in let Hr2 := fresh "Hres" in let x2 := fresh "jv" in
         intros x x2 s' mm' R' Hag HInew HJ Hkeep Hr1 Hr2 HS
  end;
  clear HI; rename HInew into HI; note_win HI;
  frame_facts HW mm';
  keep_facts Hkeep; mnorm HS.

Ltac mach_join Hp HS Hag HI HW J wl res :=
  let J := eval vm_compute in J in
  let Jlit := constr:(@BV 64 J ltac:(vm_compute; exact I)) in
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    let CUT := fresh "CUT" in
    lazymatch res with
    | @nil Z =>
      enough (CUT : forall x (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        tsafe (K x s') P ->
        realizes segs (mkCfg (mkst R' Jlit mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (K x s') L))
    | @cons Z ?r1 (@nil Z) =>
      let R1 := constr:(@BV 5 r1 I) in
      enough (CUT : forall x (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        getr R' R1 = x ->
        tsafe (K x s') P ->
        realizes segs (mkCfg (mkst R' Jlit mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (K x s') L))
    | @cons Z ?r1 (@cons Z ?r2 (@nil Z)) =>
      let R1 := constr:(@BV 5 r1 I) in let R2 := constr:(@BV 5 r2 I) in
      enough (CUT : forall x1 x2 (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        getr R' R1 = x1 -> getr R' R2 = x2 ->
        tsafe (K (x1, x2) s') P ->
        realizes segs (mkCfg (mkst R' Jlit mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (K (x1, x2) s') L))
    end;
    [ (* [comment removed for export] *)
      repeat (cur_pc ltac:(fun u => tryif constr_eq u J then fail else mstep Hp HS Hag HI HW));
      [> use_cut CUT res Hag HI HW HS ..]
    | (* [comment removed for export] *)
      join_intro Hag HI HW HS res ]
    end
  end end.

(* [comment removed for export] *)
Ltac use_cut_bool CUT Jt Hag HI HW HS :=
  cur_mstate HS ltac:(fun sb =>
    cur_pc ltac:(fun u => tryif constr_eq u Jt then apply_cut ltac:(eapply (CUT true sb))
                          else apply_cut ltac:(eapply (CUT false sb))));
  [ exact Hag | exact HI | win_same | keep_tac
  | cbv beta iota; first [ exact I | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity | repeat split ]
  | exact_HS HS ].

Ltac join_intro_bool Hag HI HW HS :=
  let x := fresh "jb" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HInew := fresh "HI" in let HX := fresh "HX" in
  clear Hag HS;
  intros x s' mm' R' Hag HInew HJ Hkeep HX HS;
  clear HI; rename HInew into HI; note_win HI;
  frame_facts HW mm';
  keep_facts Hkeep;
  destruct x; cbv beta iota in HX; mnorm HS.

Ltac mach_join_bool Hp HS Hag HI HW Jt Jf wl XR :=
  let Jt := eval vm_compute in Jt in let Jf := eval vm_compute in Jf in
  let Jtl := constr:(@BV 64 Jt ltac:(vm_compute; exact I)) in
  let Jfl := constr:(@BV 64 Jf ltac:(vm_compute; exact I)) in
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    let CUT := fresh "CUT" in
    enough (CUT : forall (x : bool) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' ->
        tsafe (K x s') P ->
        realizes segs (mkCfg (mkst R' (if x then Jtl else Jfl) mm' rom) (with_vmmaps (ms_vm s') md0))
                 (tshape (K x s') L));
    [ repeat (cur_pc ltac:(fun u => tryif constr_eq u Jt then fail else
                               tryif constr_eq u Jf then fail else mstep Hp HS Hag HI HW));
      [> use_cut_bool CUT Jt Hag HI HW HS ..]
    | join_intro_bool Hag HI HW HS ]
    end
  end end.

(* [comment removed for export] *)
Ltac mstepx Hp HS Hag HI HW HK Hret calls :=
  cur_instr ltac:(fun w i =>
    let il := lit_instr i in
    lazymatch il with
    | Jal (@BV _ 1 _) ?imm =>
        lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          let t := eval vm_compute in (bv_unsigned (v_addi pc (bv_signed imm))) in
          calls Hp HS Hag HI HW t
        end
    | Jalr (@BV _ 0 _) (@BV _ 1 _) _ => first [ mach_jr Hp HS | mach_ret Hp HS Hag HK HI Hret ]
    | _ => mstep Hp HS Hag HI HW
    end).

Ltac mrunx Hp HS Hag HI HW HK Hret calls := repeat (mstepx Hp HS Hag HI HW HK Hret calls).
Ltac mrunx_until Hp HS Hag HI HW HK Hret calls pcZ :=
  let pcZ := eval vm_compute in pcZ in
  repeat (cur_pc ltac:(fun u => tryif constr_eq u pcZ then fail else mstepx Hp HS Hag HI HW HK Hret calls)).

(* [comment removed for export] *)
Ltac no_calls Hp HS Hag HI HW t := mach_jal Hp HS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac use_cut_k CUT Kx Hag HI HS :=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb);
      [ exact Hag | exact HI | win_same | keep_tac
      | cbv beta match; repeat split;
        try (regnorm; imm_norm; rewrite ?v_addi_0; klitsg; first [reflexivity | bveq])
      | exact HS ]
  end.

Ltac join_intro_k Kx Hag HI HW HS :=
  let x := fresh "jv" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HInew := fresh "HI" in let HX := fresh "HX" in
  clear Hag HS;
  intros x s' mm' R' Hag HInew HJ Hkeep HX HS;
  clear HI; rename HInew into HI; note_win HI;
  frame_facts HW mm';
  keep_facts Hkeep;
  subst Kx; cbv beta in HS; cbv beta;
  (* [comment removed for export] *)
  revert HS; revert HX; revert x.

Ltac mach_join_k Hp HS Hag HI HW HK Hret calls XTY PCF wl XR :=
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    let Kx := fresh "Kx" in
    set (Kx := K) in HS |- *;
    let CUT := fresh "CUT" in
    enough (CUT : forall (x : XTY) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' ->
        tsafe (Kx x s') P ->
        realizes segs (mkCfg (mkst R' (PCF x) mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (Kx x s') L));
    [ repeat (lazymatch goal with
              | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) (tshape (Kx ?x _) _) =>
                  (* [comment removed for export] *)
                  let u := eval vm_compute in (bv_unsigned pc) in
                  let j := eval lazy in (bv_unsigned (PCF x)) in
                  tryif constr_eq u j then fail else mach Hp HS
              | |- _ => mstepx Hp HS Hag HI HW HK Hret calls
              end);
      [> use_cut_k CUT Kx Hag HI HS ..]
    | join_intro_k Kx Hag HI HW HS ]
    end
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mrun_to_k Hp HS Hag HI HW HK Hret calls Kx PCF :=
  repeat (lazymatch goal with
          | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) (tshape (Kx ?x _) _) =>
              let u := eval vm_compute in (bv_unsigned pc) in
              let j := eval lazy in (bv_unsigned (PCF x)) in
              tryif constr_eq u j then fail else mach Hp HS
          | |- _ => mstepx Hp HS Hag HI HW HK Hret calls
          end).

(* [comment removed for export] *)
Ltac use_cut_kx CUT Kx Hag HI HS :=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb);
      [ exact Hag | exact HI | win_pres | win_nn | keep_tac
      | cbv beta match; repeat split;
        try (regnorm; imm_norm; rewrite ?v_addi_0; klitsg; first [reflexivity | bveq])
      | exact HS ]
  end.

Ltac mach_cut_core HS Hag HI HW XTY PCF wl XR exlo exhi CUT Kx :=
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    set (Kx := K) in HS |- *;
    enough (CUT : forall (x : XTY) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                           ~ (exlo <= bv_unsigned a < exhi) -> mm' a = mmF a) ->
        (forall a : word, exlo <= bv_unsigned a < exhi -> mm' a <> None) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' s' ->
        tsafe (Kx x s') P ->
        realizes segs (mkCfg (mkst R' (PCF x) mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (Kx x s') L));
    [ (* [comment removed for export] *)
    | let x := fresh "jv" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
      let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HJn := fresh "HJnn" in
      let HInew := fresh "HI" in let HX := fresh "HX" in
      clear Hag HS;
      intros x s' mm' R' Hag HInew HJ HJn Hkeep HX HS;
      clear HI; rename HInew into HI; note_win HI;
      uaddrH HJ; uaddrH HJn;
      frame_facts HW mm';
      keep_facts Hkeep;
      subst Kx; cbv beta in HS; cbv beta;
      revert HS; revert HX; revert x ]
    end
  end end.

Tactic Notation "mach_cut" constr(HS) constr(Hag) constr(HI) constr(HW)
    constr(XTY) constr(PCF) constr(wl) constr(XR) constr(exlo) constr(exhi) "as" ident(CUT) ident(Kx) :=
  mach_cut_core HS Hag HI HW XTY PCF wl XR exlo exhi CUT Kx.

(* [comment removed for export] *)
Ltac show := lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) (tshape ?t _) =>
  idtac "PC" pc; lazymatch t with
  | mbind ?a _ _ => idtac "HEAD" a
  | ?x => idtac "TERM" x end end.
