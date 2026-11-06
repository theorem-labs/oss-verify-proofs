(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxImg FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.FxChLoop OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg AsanTblAll AsanTbl AsanEntry AsanPlan.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition TBLd : tree xi := TBLA.       (* [comment removed for export] *)
Definition IMGd : tree Z := mk_img_runs S0_WR TEmpty.
Lemma TBLd_ok : tbl_ok ASEGS TBLd. Proof. exact TBLA_ok. Qed.
Lemma TBLd_ecall : ecall_ok ASEGS TBLd. Proof. exact TBLA_ecall. Qed.
Lemma mk_img_runs_ok : forall rs t, Forall (fun p => 0 <= fst p) rs -> img_ok ASEGS t -> img_ok ASEGS (mk_img_runs rs t).
Proof.
  induction rs as [|[lo n] rs IH]; intros t Hrs Ht; cbn [mk_img_runs]; [exact Ht|].
  inversion Hrs as [|? ? Hp Hrs']; subst. apply IH; [exact Hrs'|]. apply mk_img_acc_ok; [|exact Ht].
  cbn [fst] in Hp. apply Z.shiftr_nonneg. exact Hp.
Qed.
Lemma IMGd_ok : img_ok ASEGS IMGd.
Proof.
  apply mk_img_runs_ok; [|intros p w Hp; rewrite tget_empty in Hp; discriminate].
  assert (H : forallb (fun p => Z.leb 0 (fst p)) S0_WR = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. rewrite Forall_forall. intros p Hp. apply Z.leb_le. exact (H p Hp).
Qed.

(* [comment removed for export] *)
Definition msize_eqb (a b : msize) : bool := match a, b with SZ1, SZ1 | SZ2, SZ2 | SZ4, SZ4 | SZ8, SZ8 => true | _, _ => false end.
Definition tl_ld (t : tree xi) (pc : Z) (sz : msize) (sg : bool) (rd rs : positive) (imm : Z) : bool :=
  match tlookup t pc with XLd sz' sg' rd' rs' imm' => (msize_eqb sz sz' && Bool.eqb sg sg' && Pos.eqb rd rd' && Pos.eqb rs rs' && Z.eqb imm imm')%bool | _ => false end.
Definition tl_st (t : tree xi) (pc : Z) (sz : msize) (rs1 rs2 : positive) (imm : Z) : bool :=
  match tlookup t pc with XSt sz' a b imm' => (msize_eqb sz sz' && Pos.eqb rs1 a && Pos.eqb rs2 b && Z.eqb imm imm')%bool | _ => false end.
Definition tl_addi (t : tree xi) (pc : Z) (rd rs : positive) (imm : Z) : bool :=
  match tlookup t pc with XAluI ALU_ADD rd' rs' imm' => (Pos.eqb rd rd' && Pos.eqb rs rs' && Z.eqb imm imm')%bool | _ => false end.
Definition tl_jal (t : tree xi) (pc : Z) (rd : positive) (tgt link : Z) : bool :=
  match tlookup t pc with XJal rd' tgt' link' => (Pos.eqb rd rd' && Z.eqb tgt tgt' && Z.eqb link link')%bool | _ => false end.
Definition tl_br (t : tree xi) (pc : Z) (c : branch_cond) (rs1 rs2 : positive) (tgt : Z) : bool :=
  match tlookup t pc with XBr c' a b tgt' => (bc_eqb c c' && Pos.eqb rs1 a && Pos.eqb rs2 b && Z.eqb tgt tgt')%bool | _ => false end.

Lemma msize_eqb_eq : forall a b, msize_eqb a b = true -> a = b. Proof. intros [] [] H; try discriminate; reflexivity. Qed.
Lemma bc_eqb_eq' : forall a b, bc_eqb a b = true -> a = b. Proof. intros [] [] H; try discriminate; reflexivity. Qed.
Lemma tl_ld_ok : forall t pc sz sg rd rs imm, tl_ld t pc sz sg rd rs imm = true -> tlookup t pc = XLd sz sg rd rs imm.
Proof.
  intros t pc sz sg rd rs imm H. unfold tl_ld in H. destruct (tlookup t pc); try discriminate.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with
         | H : msize_eqb _ _ = true |- _ => apply msize_eqb_eq in H
         | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
         | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
         | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end. subst. reflexivity.
Qed.
Lemma tl_st_ok : forall t pc sz rs1 rs2 imm, tl_st t pc sz rs1 rs2 imm = true -> tlookup t pc = XSt sz rs1 rs2 imm.
Proof.
  intros t pc sz rs1 rs2 imm H. unfold tl_st in H. destruct (tlookup t pc); try discriminate.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with
         | H : msize_eqb _ _ = true |- _ => apply msize_eqb_eq in H
         | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
         | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end. subst. reflexivity.
Qed.
Lemma tl_addi_ok : forall t pc rd rs imm, tl_addi t pc rd rs imm = true -> tlookup t pc = XAluI ALU_ADD rd rs imm.
Proof.
  intros t pc rd rs imm H. unfold tl_addi in H. destruct (tlookup t pc) as [op rd' rs' imm'| | | | | | | | | | | | | | | | | | | | |]; try discriminate.
  destruct op; try discriminate.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with
         | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
         | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end. subst. reflexivity.
Qed.
Lemma tl_jal_ok : forall t pc rd tgt link, tl_jal t pc rd tgt link = true -> tlookup t pc = XJal rd tgt link.
Proof.
  intros t pc rd tgt link H. unfold tl_jal in H. destruct (tlookup t pc); try discriminate.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with
         | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
         | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end. subst. reflexivity.
Qed.
Lemma tl_br_ok : forall t pc c rs1 rs2 tgt, tl_br t pc c rs1 rs2 tgt = true -> tlookup t pc = XBr c rs1 rs2 tgt.
Proof.
  intros t pc c rs1 rs2 tgt H. unfold tl_br in H. destruct (tlookup t pc); try discriminate.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with
         | H : bc_eqb _ _ = true |- _ => apply bc_eqb_eq' in H
         | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
         | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Definition PLAN0 : plan := PJoin 2000 [] 0xc5858 PFin [].
Definition PLAN1 : plan := PJoin 2000 [] 0xc5908 PFin [].
Definition envp_pc : Z := 0xc5858.
Definition pn_pc : Z := 0xc5908.
Definition PNG : Z := 0x639ac0.
Definition env_tbl_ok (t : tree xi) : bool :=
  (tl_ld t envp_pc SZ8 true (rkey rA0) (rkey rS1) 0 && tl_addi t (envp_pc + 4) (rkey rS1) (rkey rS1) 8 &&
   tl_br t (envp_pc + 8) BC_NE (rkey rA0) (rkey rX0) envp_pc)%bool.
Definition pn_tbl_ok (t : tree xi) : bool :=
  (tl_st t pn_pc SZ8 (rkey rA0) (rkey rS0) 0 && tl_addi t (pn_pc + 4) (rkey rA2) (rkey rX0) 47 &&
   tl_jal t (pn_pc + 8) (rkey rX0) (pn_pc + 20) (pn_pc + 12) && tl_st t (pn_pc + 12) SZ8 (rkey rA0) (rkey rA1) 0 &&
   tl_addi t (pn_pc + 16) (rkey rA1) (rkey rA1) 1 && tl_ld t (pn_pc + 20) SZ1 false (rkey rA3) (rkey rA1) 18446744073709551615 &&
   tl_br t (pn_pc + 24) BC_EQ (rkey rA3) (rkey rA2) (pn_pc + 12) && tl_br t (pn_pc + 28) BC_NE (rkey rA3) (rkey rX0) (pn_pc + 16))%bool.
Definition L1_ok (L1 : sst) : bool :=
  (Z.eqb (s_pc L1) envp_pc && lin_eqb (rget (s_regs L1) (rkey rS1)) ENVP && lwf (s_next L1) AUXV && Pos.leb 17 (s_next L1))%bool.
Definition PN_L1 : lin := laddc (ladd P0 LEN0) 1.
Definition L2_ok (L2 : sst) : bool :=
  (Z.eqb (s_pc L2) pn_pc && match s_resv L2 with RNone => true | _ => false end && lin_eqb (rget (s_regs L2) (rkey rS0)) P0 &&
   lin_eqb (rget (s_regs L2) (rkey rA0)) (lconst PNG) && lin_eqb (rget (s_regs L2) (rkey rA1)) (laddc P0 1) && lwf (s_next L2) PN_L1 &&
   Pos.leb 17 (s_next L2))%bool.
Definition pn_rgs (L2 : sst) : option (list region) := store_at (s_facts L2) (s_rgs L2) (lconst PNG) 8 (st_bytes (lvar (s_next L2)) None 0 8).

(* [comment removed for export] *)
Definition startup_res (S0 : sst) (t : tree xi) (img : tree Z) : option (list (sst * smodel)) :=
  if (bases_ins (pos_below 17) RG0 && env_tbl_ok t && pn_tbl_ok t)%bool then
  match check t img (pos_below 17) 20 PLAN0 S0 with
  | Some [L1] =>
      if L1_ok L1 then
        let S1 := envp_post L1 (envp_pc + 12) AUXV in
        if bases_ins (pos_below (s_next S1)) (s_rgs S1) then
        match check t img (pos_below (s_next S1)) 20 PLAN1 S1 with
        | Some [L2] =>
            if L2_ok L2 then
              match pn_rgs L2 with
              | Some rgs' => check_chain ASEGS LIM t img CH1 (pn_post L2 (pn_pc + 32) PN_L1 rgs') M0
              | None => None
              end
            else None
        | _ => None
        end
        else None
      else None
  | _ => None
  end
  else None.
Definition some_nonempty {A} (o : option (list A)) : bool := match o with Some (_ :: _) => true | _ => false end.
Definition list_of {A} (o : option (list A)) : list A := match o with Some f => f | None => [] end.
(* [comment removed for export] *)
Definition startup_ok_c (olo ohi xlo : Z) : bool := some_nonempty (startup_res (S0c olo ohi xlo) TBLd IMGd).
Definition FINALS_c (olo ohi xlo : Z) : list (sst * smodel) := list_of (startup_res (S0c olo ohi xlo) TBLd IMGd).


(* [comment removed for export] *)
Lemma A_wx : wx_segs_nowrap ASEGS. Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma A_segb : segs_below_b ASEGS 0x800000000000 = true. Proof. vm_compute. reflexivity. Qed.
Lemma A_respos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Proof. rewrite res_eq. repeat constructor; cbn [snd]; rewrite u_small64 by (unfold two64; lia); lia. Qed.
Lemma A_reswf : ivs_wf (segments_reserved ASEGS).
Proof.
  rewrite res_eq. intros q Hq. cbn [In] in Hq. unfold iv_wf, B, S.
  destruct Hq as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite !u_small64 by (unfold two64; lia); lia.
Qed.
Lemma lwf17 : forall l, lwf 17 l = true -> forall E E', agree 17 E E' -> lden E' l = lden E l.
Proof. intros l Hl E E' Ha. symmetry. exact (lden_agree 17 E E' l Hl Ha). Qed.

(* [comment removed for export] *)
Lemma startup_res_inv : forall S0 t img finals, startup_res S0 t img = Some finals ->
  bases_ins (pos_below 17) RG0 = true /\ env_tbl_ok t = true /\ pn_tbl_ok t = true /\
  exists L1, check t img (pos_below 17) 20 PLAN0 S0 = Some [L1] /\ L1_ok L1 = true /\
    bases_ins (pos_below (s_next (envp_post L1 (envp_pc + 12) AUXV))) (s_rgs (envp_post L1 (envp_pc + 12) AUXV)) = true /\
  exists L2, check t img (pos_below (s_next (envp_post L1 (envp_pc + 12) AUXV))) 20 PLAN1 (envp_post L1 (envp_pc + 12) AUXV) = Some [L2] /\
    L2_ok L2 = true /\
  exists rgs', pn_rgs L2 = Some rgs' /\ check_chain ASEGS LIM t img CH1 (pn_post L2 (pn_pc + 32) PN_L1 rgs') M0 = Some finals.
Proof.
  intros S0 t img finals H. unfold startup_res in H.
  destruct (bases_ins (pos_below 17) RG0 && env_tbl_ok t && pn_tbl_ok t)%bool eqn:Hc0; [|discriminate H].
  apply andb_prop in Hc0 as [Hc0 Hpnt]. apply andb_prop in Hc0 as [Hbi0 Henv].
  split; [exact Hbi0|]. split; [exact Henv|]. split; [exact Hpnt|].
  destruct (check t img (pos_below 17) 20 PLAN0 S0) as [[|L1 [|L1' L1s]]|] eqn:HR0; [discriminate H| |discriminate H|discriminate H].
  exists L1. split; [reflexivity|].
  destruct (L1_ok L1) eqn:HL1; [|discriminate H]. split; [reflexivity|].
  destruct (bases_ins (pos_below (s_next (envp_post L1 (envp_pc + 12) AUXV))) (s_rgs (envp_post L1 (envp_pc + 12) AUXV))) eqn:Hbi1;
    [|discriminate H]. split; [reflexivity|].
  destruct (check t img (pos_below (s_next (envp_post L1 (envp_pc + 12) AUXV))) 20 PLAN1 (envp_post L1 (envp_pc + 12) AUXV))
    as [[|L2 [|L2' L2s]]|] eqn:HR1; [discriminate H| |discriminate H|discriminate H].
  exists L2. split; [reflexivity|].
  destruct (L2_ok L2) eqn:HL2; [|discriminate H]. split; [reflexivity|].
  destruct (pn_rgs L2) as [rgs'|] eqn:Hpr; [|discriminate H]. exists rgs'. split; [reflexivity|]. exact H.
Qed.

(* [comment removed for export] *)
Strategy opaque [TBLd IMGd mk_tbl_ranges check check_chain startup_res some_nonempty list_of].
Strategy expand [startup_ok_c FINALS_c].

Section Thm.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Variables (sp brk0 mb : word) (draw : EntryDraw) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS brk0.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hid : valid_id (in_uid inp).
Variables (olo ohi xlo : Z).
Hypothesis HC : olo <= OFS sp <= ohi.
Hypothesis Hxlo : 0 <= olo /\ 64 * xlo <= 200 + olo.

Let mdl := model0 sp brk0 mb LIM inp.
Let mem := m0 sp draw inp.

(* [comment removed for export] *)
#[using="Hoff Hsp Hbrk Hfit Hva Hve Hid HC Hxlo"] Theorem asan_startup_cls : startup_ok_c olo ohi xlo = true -> forall T,
  (forall S' M' E' ms' model', In (S', M') (FINALS_c olo ohi xlo) -> DEN ASEGS LIM mdl mem E' S' M' ms' model' ->
     realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mb draw LIM inp) T.
Proof. LiaFast.lf_pins (fun (Hoff Hsp Hbrk Hfit Hva Hve Hid HC Hxlo : LiaFast.U) => LiaFast.u0).
  intros Hcert T Hk.
  change (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mb draw LIM inp) with (mkCfg (ms0 sp draw inp) mdl).
  pose proof (den_entry sp brk0 mb draw LIM inp Hsp Hbrk Hfit Hva Hve Hid olo ohi xlo HC Hxlo ltac:(clear; unfold LIM; lia)) as Hd0.
  unfold startup_ok_c, FINALS_c in *.
  destruct (startup_res (S0c olo ohi xlo) TBLd IMGd) as [finals|] eqn:HS; [|cbn in Hcert; discriminate Hcert]. cbn [list_of] in Hk.
  destruct (startup_res_inv (S0c olo ohi xlo) TBLd IMGd finals HS) as (Hbi0 & Henv & Hpnt & L1 & HR0 & HL1 & Hbi1 & L2 & HR1 & HL2 & rgs' & Hpr & HCH).
  (* [comment removed for export] *)
  apply (den_seg ASEGS cfg LIM mdl mem A_wx TBLd IMGd (pos_below 17) 20 PLAN0 (S0c olo ohi xlo) [L1] (E0 sp brk0 draw inp) M0 (ms0 sp draw inp) mdl T
           TBLd_ok IMGd_ok HR0 Hd0 Hbi0 (pos_below_In 17)).
  intros L E1 ms1 mdl1 HL Hd1 Ha1. destruct HL as [<-|[]].
  (* [comment removed for export] *)
  pose proof (usp_b sp inp Hsp Hfit Hva Hve) as (U1 & U2).
  pose proof (rel_rp sp draw inp Hsp Hfit Hva Hve) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  pose proof (blk_top sp draw inp Hsp Hfit Hva Hve) as Bt.
  assert (HuE : forall E' l, agree 17 (E0 sp brk0 draw inp) E' -> lwf 17 l = true -> uE E' l = bv_unsigned (lden (E0 sp brk0 draw inp) l)).
  { intros E' l Ha Hl. unfold uE. rewrite (lden_agree 17 (E0 sp brk0 draw inp) E' l Hl Ha). reflexivity. }
  assert (Hw_ENVP : lwf 17 ENVP = true) by (vm_compute; reflexivity).
  assert (Hw_AUXV : lwf 17 AUXV = true) by (vm_compute; reflexivity).
  assert (Hw_ESZ : lwf 17 (laddc (lscale 8 ENVC) 8) = true) by (vm_compute; reflexivity).
  pose proof (u_ENVP sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uENVP. pose proof (u_AUXV sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uAUXV.
  pose proof (u_ESZ sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uESZ.
  unfold L1_ok in HL1. apply andb_prop in HL1 as [HL1 Hn1]. apply Pos.leb_le in Hn1.
  apply andb_prop in HL1 as [HL1 HwA]. apply andb_prop in HL1 as [Hpc1 HS1]. apply Z.eqb_eq in Hpc1. apply lin_eqb_eq in HS1.
  unfold env_tbl_ok in Henv. apply andb_prop in Henv as [Henv T3]. apply andb_prop in Henv as [T1 T2].
  (* [comment removed for export] *)
  apply (den_envp ASEGS cfg LIM mdl mem A_wx TBLd TBLd_ok envp_pc E1 L1 M0 ms1 mdl1 T ENVP AUXV (length (in_envp inp))).
  - unfold envp_pc. clear. lia.
  - unfold envp_pc, two64. clear. lia.
  - exact (tl_ld_ok _ _ _ _ _ _ _ T1).
  - exact (tl_addi_ok _ _ _ _ _ T2).
  - exact (tl_br_ok _ _ _ _ _ _ T3).
  - exact Hd1.
  - exact Hpc1.
  - exact HS1.
  - rewrite (HuE E1 ENVP Ha1 Hw_ENVP), uENVP. unfold two64, EC in *. clear - U1 R7 R8. lia.
  - intros w Hw. exists (ENVP, laddc (lscale 8 ENVC) 8). split; [left; reflexivity|]. cbn [fst snd].
    rewrite (HuE E1 ENVP Ha1 Hw_ENVP) in *. rewrite (HuE E1 _ Ha1 Hw_ESZ), uESZ. rewrite uENVP in *. unfold EC in *. clear - Hw R8. lia.
  - intros i Hi. rewrite (HuE E1 ENVP Ha1 Hw_ENVP), uENVP. exact (envp_words sp draw inp Hsp Hfit Hva Hve i Hi).
  - rewrite (HuE E1 ENVP Ha1 Hw_ENVP), uENVP. pose proof (envp_null sp draw inp Hsp Hfit Hva Hve) as X. unfold EC in X. exact X.
  - apply bv_eq. rewrite <- (lden_agree 17 (E0 sp brk0 draw inp) E1 AUXV Hw_AUXV Ha1), uAUXV. rewrite (HuE E1 ENVP Ha1 Hw_ENVP), uENVP.
    rewrite u_small64 by (unfold two64, EC in *; clear - U1 R7 R8; lia). unfold EC in *. clear - R8. lia.
  - exact HwA.
  - intros E2 ms2 mdl2 Hd2 Ha2.
    assert (Ha12 : agree 17 (E0 sp brk0 draw inp) E2) by (apply (agree_trans 17 _ E1 _ Ha1); exact (agree_mono 17 _ E1 E2 Hn1 Ha2)).
    (* [comment removed for export] *)
    set (S1 := envp_post L1 (envp_pc + 12) AUXV) in *.
    apply (den_seg ASEGS cfg LIM mdl mem A_wx TBLd IMGd (pos_below (s_next S1)) 20 PLAN1 S1 [L2] E2 M0 ms2 mdl2 T
             TBLd_ok IMGd_ok HR1 Hd2 Hbi1 (pos_below_In (s_next S1))).
    intros L E3 ms3 mdl3 HL Hd3 Ha3. destruct HL as [<-|[]].
    assert (Ha13 : agree 17 (E0 sp brk0 draw inp) E3) by (apply (agree_trans 17 _ E2 _ Ha12); exact (agree_mono 17 _ E2 E3 Hn1 Ha3)).
    (* [comment removed for export] *)
    unfold L2_ok in HL2. apply andb_prop in HL2 as [HL2 Hn2]. apply Pos.leb_le in Hn2. apply andb_prop in HL2 as [HL2 HwP].
    apply andb_prop in HL2 as [HL2 HA1]. apply andb_prop in HL2 as [HL2 HA0]. apply andb_prop in HL2 as [HL2 HS0].
    apply andb_prop in HL2 as [Hpc2 Hrv]. apply Z.eqb_eq in Hpc2. apply lin_eqb_eq in HS0, HA0, HA1.
    assert (Hrv' : s_resv L2 = RNone) by (destruct (s_resv L2); [reflexivity | discriminate Hrv | discriminate Hrv]).
    unfold pn_tbl_ok in Hpnt.
    apply andb_prop in Hpnt as [Hpnt P8]. apply andb_prop in Hpnt as [Hpnt P7]. apply andb_prop in Hpnt as [Hpnt P6].
    apply andb_prop in Hpnt as [Hpnt P5]. apply andb_prop in Hpnt as [Hpnt P4]. apply andb_prop in Hpnt as [Hpnt P3].
    apply andb_prop in Hpnt as [P1 P2].
    assert (Hw_P0 : lwf 17 P0 = true) by (vm_compute; reflexivity).
    assert (Hw_STR : lwf 17 (lsub RANDP P0) = true) by (vm_compute; reflexivity).
    assert (Hw_PN : lwf 17 PN_L1 = true) by (vm_compute; reflexivity).
    pose proof (u_P0 sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uP0. pose proof (u_STR sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uSTR.
    pose proof (u_PNL1 sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uPN.
    pose proof (rp_str sp draw inp Hsp Hfit Hva Hve) as Hrs. pose proof (argv0_top sp draw inp Hfit Hva) as Atop.
    set (n0 := Z.of_nat (length (nth 0 (in_argv inp) []))).
    assert (HuP0 : uE E3 P0 = usp sp + 8 * AC inp + 8 * EC inp + 184) by (rewrite (HuE E3 P0 Ha13 Hw_P0); exact uP0).
    assert (Hn0 : 0 <= n0 <= 131071).
    { clear - Hva R7. unfold n0. pose proof (valid_argv_str_len (in_argv inp) 0 Hva ltac:(clear - R7; unfold AC in *; lia)). lia. }
    apply (den_pn ASEGS cfg LIM mdl mem A_wx TBLd TBLd_ok pn_pc E3 L2 M0 ms3 mdl3 T PNG P0 PN_L1 rgs' n0
             (fun i => nth (Z.to_nat i) (nth 0 (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
    + unfold pn_pc. clear. lia.
    + unfold pn_pc, two64. clear. lia.
    + exact (tl_st_ok _ _ _ _ _ _ P1).
    + exact (tl_addi_ok _ _ _ _ _ P2).
    + exact (tl_jal_ok _ _ _ _ _ P3).
    + exact (tl_st_ok _ _ _ _ _ _ P4).
    + exact (tl_addi_ok _ _ _ _ _ P5).
    + exact (tl_ld_ok _ _ _ _ _ _ _ P6).
    + exact (tl_br_ok _ _ _ _ _ _ P7).
    + exact (tl_br_ok _ _ _ _ _ _ P8).
    + exact Hd3.
    + exact Hpc2.
    + exact Hrv'.
    + exact HS0.
    + exact HA0.
    + rewrite HA1, lden_laddc. reflexivity.
    + exact Hpr.
    + rewrite HuP0. clear - U1 R7 R8. unfold AC, EC in *. lia.
    + rewrite HuP0. unfold two64. clear - U1 R7 R8 Hn0 Atop. unfold AC, EC, n0 in *. lia.
    + exact (proj1 Hn0).
    + unfold PNG. clear. lia.
    + unfold PNG, two64. clear. lia.
    + left. rewrite HuP0. unfold PNG. clear - U1 R7 R8. unfold AC, EC in *. lia.
    + intros w Hw. exists (P0, lsub RANDP P0). split; [right; left; reflexivity|]. cbn [fst snd].
      rewrite HuP0 in *. rewrite (HuE E3 _ Ha13 Hw_STR), uSTR. clear - Hw Hrs Hn0. unfold n0, AC, EC in *. lia.
    + intros i Hi. rewrite HuP0. split.
      * pose proof (argv0_byte sp draw inp Hsp Hfit Hva Hve (Z.to_nat i) ltac:(clear - Hi; unfold n0 in *; lia)) as X.
        rewrite Z2Nat.id in X by (clear - Hi; lia). exact X.
      * apply (argv0_nz inp Hva (Z.to_nat i)). clear - Hi. unfold n0 in *. lia.
    + rewrite HuP0. pose proof (argv0_byte sp draw inp Hsp Hfit Hva Hve (length (nth 0 (in_argv inp) [])) ltac:(clear; lia)) as X.
      rewrite (argv0_nul inp) in X. exact X.
    + apply bv_eq. rewrite <- (lden_agree 17 (E0 sp brk0 draw inp) E3 PN_L1 Hw_PN Ha13). unfold PN_L1. rewrite uPN.
      rewrite HuP0. rewrite u_small64 by (unfold two64; clear - U1 R7 R8 Hn0 Atop; unfold AC, EC, n0 in *; lia).
      clear. unfold n0, L0. lia.
    + exact HwP.
    + intros E4 ms4 mdl4 Hd4 Ha4.
      apply (chain_sound ASEGS cfg LIM mdl mem TBLd IMGd A_wx A_segb Hoff A_respos A_reswf TBLd_ok IMGd_ok TBLd_ecall
               CH1 (pn_post L2 (pn_pc + 32) PN_L1 rgs') M0 finals HCH E4 ms4 mdl4 T Hd4).
      intros S' M' E' ms' model' Hin Hd'. exact (Hk S' M' E' ms' model' Hin Hd').
Qed.
End Thm.
(* [comment removed for export] *)
