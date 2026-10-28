(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_vbm_ao_fast_xsrc_T_u5 Cut_vbm_ao_fast_xsrc_u5 Cut_vbm_ao_grow1_xsrc_u5
  Cut_vbm_ao_grow2k1_xsrc_u5 Cut_vbm_ao_grow2k2_xsrc_u5 Cut_vbm_ao_grow2k3_xsrc_u5 Cut_vbm_ao_grow2k4_xsrc_u5 Cut_vbm_ao_grow2k5_xsrc_u5
  Cut_vbm_ao_grow2k6_xsrc_u5 Cut_vbm_ao_grow2k7_xsrc_u5 Cut_vbm_ao_grow2k8_xsrc_u5 Cut_vbm_ao_grow2k9_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Memcpy1_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncAppendK_u5 EncKit_u5 EncKit3_u5 EncOpNew_u5 EncOpNewU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import VbhKitX_u5 VbmKitX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBM_AOU.
Import PML. Import PMES.
Module F := Cut_vbm_ao_fast_xsrc_u5.   Module FT := Cut_vbm_ao_fast_xsrc_T_u5.
Module G0 := Cut_vbm_ao_grow1_xsrc_u5.
Module G1 := Cut_vbm_ao_grow2k1_xsrc_u5.   Module G2 := Cut_vbm_ao_grow2k2_xsrc_u5.   Module G3 := Cut_vbm_ao_grow2k3_xsrc_u5.
Module G4 := Cut_vbm_ao_grow2k4_xsrc_u5.   Module G5 := Cut_vbm_ao_grow2k5_xsrc_u5.   Module G6 := Cut_vbm_ao_grow2k6_xsrc_u5.
Module G7 := Cut_vbm_ao_grow2k7_xsrc_u5.   Module G8 := Cut_vbm_ao_grow2k8_xsrc_u5.   Module G9 := Cut_vbm_ao_grow2k9_xsrc_u5.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.  Definition OPNEW : Z := PML.PC_OPNEW.
Definition MEMCPY : Z := Memcpy1_u5.MC1.MEMCPY.
Definition TAILPC : Z := PMES2.bk_tail PMES2.BK_ARRAY.
Definition KEPTN : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition NFX : nat := 48.
Definition HD : CH.hdecl := FT.HDECL.
Definition has := GK.has.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Lemma kept_lt48 : forall y : reg, In (ridx y) KEPTN -> (ridx y < 48)%nat.
Proof. intros y Hy. unfold KEPTN in Hy. cbn [In] in Hy. intuition lia. Qed.
Lemma kept_in : forall r : reg, In (bv_unsigned r) [3; 20; 21; 22; 23; 24; 25; 26; 27] -> In (ridx r) KEPTN.
Proof. intros r H. unfold ridx, KEPTN. cbn [In] in H. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H. Qed.
Lemma reg_of_leaf : forall segs c ps E' R' (M1 M' : PML.mem) (x : bv 5) n e,
  CC.leaf_facts segs c ps E' R' M1 M' -> CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e.
Proof.
  intros segs c ps E' R' M1 M' x n e HLF Hchk Hx. pose proof (CL.ps_reg_is_sound segs c ps E' R' M1 M' n e HLF Hchk) as G.
  rewrite <- Hx, Z_to_bv_bv_unsigned in G. exact G.
Qed.
Lemma u_add_lit : forall E e (c : Z) x, bv_unsigned (edenot E e) = x -> 0 <= c < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  bv_unsigned (edenot E (EAlu ALU_ADD e (ELit c))) = x + c.
Proof. intros E e c x He Hc Hxc. cbn [edenot]. rewrite u_add64, He, u64_of_Z by lia. apply Z.mod_small. lia. Qed.
Ltac elit_len := unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; first [reflexivity | lia].

Definition no_goto (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther _ => true end.

Definition ctxb_fast : expr := EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 32) (EVar 33)).
Definition exit_fast (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (Z.eqb (SR.ps_pc ps) TAILPC && CL.ps_keeps ps KEPTN && Nat.leb NFX (CC.cp_nx c) && Nat.eqb i 0
   && CH2.blocks_eqb (nth i F.BLS []) [(EVar 32, EVar 34)]
   && CL.ps_reg_is ps 2 (EVar 2) && CL.ps_reg_is ps 8 (EVar 8) && CL.ps_reg_is ps 10 (EAlu ALU_ADD ctxb_fast (ELit 32))
   && has cells (KWord (SA (EVar 8) 264) 8 (EVar 32)) && has cells (KWord (SA (EVar 8) 280) 8 (EAlu ALU_ADD (EVar 32) (EVar 34)))
   && has cells (KWord (SA ctxb_fast 0) 4 (ELit 1)) && has cells (KWord (SA ctxb_fast 4) 1 (ELit 0))
   && has cells (KWord (SA ctxb_fast 6) 1 (ELit 0)) && has cells (KWord (SA ctxb_fast 24) 8 (ELit 0))
   && has cells (KBlob (SA (EVar 32) 0) (EMd M_MUL (ELit 32) (EVar 33)) 0))%bool.
Definition leaf_fast (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [] pc) && exit_fast i c ps)%bool end.
Lemma heap_ok_fast : CH2.heap_chk NFX HD F.BLS F.CPS GK.HULL_LO GK.HULL_HI F.TAGS F.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_fast : CH2.leaves_all F.CPS F.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_fast_ok : CH2.leaves_all F.CPS F.TAGS leaf_fast = true.
Proof. vm_compute. reflexivity. Qed.
Lemma regs_fast : CC.cp_regs F.cp0 = sr_upd (sr_upd (sr_upd sr_id 9 (EAlu ALU_ADD (EVar 8) (ELit 264))) 18 ctxb_fast) 19 (EVar 32).
Proof. vm_compute. reflexivity. Qed.

Definition exit_grow (C : Z) (BLS : list CA.blocks) (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (Z.eqb (SR.ps_pc ps) TAILPC && CL.ps_keeps ps KEPTN && Nat.leb (S NFX) (CC.cp_nx c) && negb (Nat.eqb i 0)
   && CH2.blocks_eqb (nth i BLS []) [(EVar 48, ELit (2 * C))]
   && CL.ps_reg_is ps 2 (EVar 2) && CL.ps_reg_is ps 8 (EVar 8) && CL.ps_reg_is ps 10 (EAlu ALU_ADD (EVar 48) (ELit (C + 32)))
   && has cells (KWord (SA (EVar 8) 264) 8 (EVar 48)) && has cells (KWord (SA (EVar 8) 280) 8 (EAlu ALU_ADD (EVar 48) (ELit (2 * C))))
   && has cells (KWord (SA (EVar 48) C) 4 (ELit 1)) && has cells (KWord (SA (EVar 48) (C + 4)) 1 (ELit 0))
   && has cells (KWord (SA (EVar 48) (C + 6)) 1 (ELit 0)) && has cells (KWord (SA (EVar 48) (C + 24)) 8 (ELit 0))
   && has cells (KBlob (SA (EVar 48) 0) (ELit C) 0))%bool.
Definition leaf_grow (C : Z) (BLS : list CA.blocks) (CPS : list CC.cutpoint) (RETS : list (nat * nat * nat * Z))
    (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [] pc then
        (negb (Z.eqb pc MALLOC) && negb (Nat.eqb i 0) && match CH2.ret_of RETS i k with Some j => negb (Nat.eqb j 0) | None => false end)%bool
      else if Z.eqb pc OPNEW then
        match CH2.ret_of RETS i k with
        | Some j =>
            match nth_error CPS j with
            | Some cj => (Nat.eqb i 0 && negb (Nat.eqb j 0) && Z.eqb (SR.ps_pc ps) OPNEW && Nat.leb NFX (CC.cp_nx c)
                          && expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) (ELit (2 * C))
                          && isSome (EON.opnew_chk NFX HD c ps cj (nth i BLS []) (nth j BLS [])))%bool
            | None => false
            end
        | None => false
        end
      else if Z.eqb pc MEMCPY then
        match CH2.ret_of RETS i k with
        | Some j =>
            match nth_error CPS j with
            | Some cj => (negb (Nat.eqb i 0) && negb (Nat.eqb j 0) && CH2.copy_chk NFX HD MEMCPY c ps cj (nth i BLS []) (nth j BLS []))%bool
            | None => false
            end
        | None => false
        end
      else exit_grow C BLS i c ps
  end.
Definition regs_grow (C : Z) : list expr :=
  sr_upd (sr_upd (sr_upd sr_id 9 (EAlu ALU_ADD (EVar 8) (ELit 264))) 18 (EAlu ALU_ADD (EVar 32) (ELit C))) 19 (EVar 32).
Definition know_grow (C : Z) : list kentry :=
  [KWord (SA (EVar 8) (264)) 8 (EVar 32);
   KWord (SA (EVar 8) (272)) 8 (EAlu ALU_ADD (EVar 32) (ELit C));
   KWord (SA (EVar 8) (280)) 8 (EAlu ALU_ADD (EVar 32) (ELit C));
   KWr (SA (EVar 8) (264)) (ELit (24));
   KWord (SA (EVar 8) (296)) 8 (EVar 35);
   KRange (EVar 35) (0) (18446744073709551615);
   KWord (SA (EVar 8) (376)) 8 (ELit (1));
   KWord (SA (EVar 8) (28)) 1 (ELit (0));
   KWord (SA (EVar 8) (30)) 1 (ELit (0));
   KRange (EVar 8) (1099511627776) (140737488355328);
   KAlign (EVar 8) (8);
   KUnk (SA (EVar 2) (-8384)) (ELit (8384));
   KWr (SA (EVar 2) (-8384)) (ELit (8384));
   KUnk (SA (EVar 2) (0)) (ELit (24));
   KWr (SA (EVar 2) (0)) (ELit (24));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8384)) (ELit (8408)) (SA (EVar 8) (0)) (ELit (408));
   KUnk (SA (EVar 32) (0)) (ELit C);
   KWr (SA (EVar 32) (0)) (ELit C);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (16);
   KDisj (SA (EVar 2) (-8384)) (ELit (8408)) (SA (EVar 32) (0)) (ELit C);
   KDisj (SA (EVar 8) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit C);
   KWord (SA (EVar 32) (C - 28)) 1 (ELit (0));
   KBlob (SA (EVar 32) (0)) (ELit C) 0].

Lemma heap_ok_G0 : CH2.heap_chk NFX HD G0.BLS G0.CPS GK.HULL_LO GK.HULL_HI G0.TAGS G0.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G0 : CH2.leaves_all G0.CPS G0.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G0 : CH2.leaves_all G0.CPS G0.TAGS (leaf_grow (32 * 2 ^ 0) G0.BLS G0.CPS G0.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G0 : CC.cp_pc G0.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G0.cp0 = regs_grow (32 * 2 ^ 0) /\
  CC.cp_know G0.cp0 = know_grow (32 * 2 ^ 0) /\ nth 0 G0.BLS [] = [(EVar 32, ELit (32 * 2 ^ 0))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma heap_ok_G1 : CH2.heap_chk NFX HD G1.BLS G1.CPS GK.HULL_LO GK.HULL_HI G1.TAGS G1.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G1 : CH2.leaves_all G1.CPS G1.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G1 : CH2.leaves_all G1.CPS G1.TAGS (leaf_grow (32 * 2 ^ 1) G1.BLS G1.CPS G1.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G1 : CC.cp_pc G1.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G1.cp0 = regs_grow (32 * 2 ^ 1) /\
  CC.cp_know G1.cp0 = know_grow (32 * 2 ^ 1) /\ nth 0 G1.BLS [] = [(EVar 32, ELit (32 * 2 ^ 1))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma heap_ok_G2 : CH2.heap_chk NFX HD G2.BLS G2.CPS GK.HULL_LO GK.HULL_HI G2.TAGS G2.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G2 : CH2.leaves_all G2.CPS G2.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G2 : CH2.leaves_all G2.CPS G2.TAGS (leaf_grow (32 * 2 ^ 2) G2.BLS G2.CPS G2.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G2 : CC.cp_pc G2.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G2.cp0 = regs_grow (32 * 2 ^ 2) /\
  CC.cp_know G2.cp0 = know_grow (32 * 2 ^ 2) /\ nth 0 G2.BLS [] = [(EVar 32, ELit (32 * 2 ^ 2))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma heap_ok_G3 : CH2.heap_chk NFX HD G3.BLS G3.CPS GK.HULL_LO GK.HULL_HI G3.TAGS G3.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G3 : CH2.leaves_all G3.CPS G3.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G3 : CH2.leaves_all G3.CPS G3.TAGS (leaf_grow (32 * 2 ^ 3) G3.BLS G3.CPS G3.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G3 : CC.cp_pc G3.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G3.cp0 = regs_grow (32 * 2 ^ 3) /\
  CC.cp_know G3.cp0 = know_grow (32 * 2 ^ 3) /\ nth 0 G3.BLS [] = [(EVar 32, ELit (32 * 2 ^ 3))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma heap_ok_G4 : CH2.heap_chk NFX HD G4.BLS G4.CPS GK.HULL_LO GK.HULL_HI G4.TAGS G4.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G4 : CH2.leaves_all G4.CPS G4.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G4 : CH2.leaves_all G4.CPS G4.TAGS (leaf_grow (32 * 2 ^ 4) G4.BLS G4.CPS G4.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G4 : CC.cp_pc G4.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G4.cp0 = regs_grow (32 * 2 ^ 4) /\
  CC.cp_know G4.cp0 = know_grow (32 * 2 ^ 4) /\ nth 0 G4.BLS [] = [(EVar 32, ELit (32 * 2 ^ 4))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma heap_ok_G5 : CH2.heap_chk NFX HD G5.BLS G5.CPS GK.HULL_LO GK.HULL_HI G5.TAGS G5.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G5 : CH2.leaves_all G5.CPS G5.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G5 : CH2.leaves_all G5.CPS G5.TAGS (leaf_grow (32 * 2 ^ 5) G5.BLS G5.CPS G5.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G5 : CC.cp_pc G5.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G5.cp0 = regs_grow (32 * 2 ^ 5) /\
  CC.cp_know G5.cp0 = know_grow (32 * 2 ^ 5) /\ nth 0 G5.BLS [] = [(EVar 32, ELit (32 * 2 ^ 5))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma heap_ok_G6 : CH2.heap_chk NFX HD G6.BLS G6.CPS GK.HULL_LO GK.HULL_HI G6.TAGS G6.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G6 : CH2.leaves_all G6.CPS G6.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G6 : CH2.leaves_all G6.CPS G6.TAGS (leaf_grow (32 * 2 ^ 6) G6.BLS G6.CPS G6.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G6 : CC.cp_pc G6.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G6.cp0 = regs_grow (32 * 2 ^ 6) /\
  CC.cp_know G6.cp0 = know_grow (32 * 2 ^ 6) /\ nth 0 G6.BLS [] = [(EVar 32, ELit (32 * 2 ^ 6))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma heap_ok_G7 : CH2.heap_chk NFX HD G7.BLS G7.CPS GK.HULL_LO GK.HULL_HI G7.TAGS G7.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G7 : CH2.leaves_all G7.CPS G7.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G7 : CH2.leaves_all G7.CPS G7.TAGS (leaf_grow (32 * 2 ^ 7) G7.BLS G7.CPS G7.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G7 : CC.cp_pc G7.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G7.cp0 = regs_grow (32 * 2 ^ 7) /\
  CC.cp_know G7.cp0 = know_grow (32 * 2 ^ 7) /\ nth 0 G7.BLS [] = [(EVar 32, ELit (32 * 2 ^ 7))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma heap_ok_G8 : CH2.heap_chk NFX HD G8.BLS G8.CPS GK.HULL_LO GK.HULL_HI G8.TAGS G8.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G8 : CH2.leaves_all G8.CPS G8.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G8 : CH2.leaves_all G8.CPS G8.TAGS (leaf_grow (32 * 2 ^ 8) G8.BLS G8.CPS G8.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G8 : CC.cp_pc G8.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G8.cp0 = regs_grow (32 * 2 ^ 8) /\
  CC.cp_know G8.cp0 = know_grow (32 * 2 ^ 8) /\ nth 0 G8.BLS [] = [(EVar 32, ELit (32 * 2 ^ 8))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma heap_ok_G9 : CH2.heap_chk NFX HD G9.BLS G9.CPS GK.HULL_LO GK.HULL_HI G9.TAGS G9.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_G9 : CH2.leaves_all G9.CPS G9.TAGS no_goto = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_G9 : CH2.leaves_all G9.CPS G9.TAGS (leaf_grow (32 * 2 ^ 9) G9.BLS G9.CPS G9.RETS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp0_G9 : CC.cp_pc G9.cp0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs G9.cp0 = regs_grow (32 * 2 ^ 9) /\
  CC.cp_know G9.cp0 = know_grow (32 * 2 ^ 9) /\ nth 0 G9.BLS [] = [(EVar 32, ELit (32 * 2 ^ 9))].
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.


Section Mid.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis OPNEWXU : PMES.opnew_x_specU L HI.

Lemma hh_perm : forall LB LB' cr M VM, hi_heap HI LB cr M VM -> Permutation LB LB' -> hi_heap HI LB' cr M VM.
Proof.
  intros LB LB' cr M VM HH HP. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & Hnd & _).
  apply (hio_perm L SCFG HI HIok LB LB' cr M VM HH).
  - intros b0. split; [apply (Permutation_in b0 HP) | apply (Permutation_in b0 (Permutation_sym HP))].
  - apply base.NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst HP)). apply base.NoDup_ListNoDup. exact Hnd.
Qed.

Definition mid_body (LBo : list (Z * Z)) (cr : credit) (sp V S2 b capb dI dD : Z) (es : estate) : Prop :=
    PMES2.cps_seg L HI PMES2.PC_MID_ARR_INOBJ (PMES2.bk_tail PMES2.BK_ARRAY) sp PMES2.MID_SCR (LBo ++ stack_blocks b capb) cr
      (fun R M => getr R 2%bv = Z_to_bv 64 sp /\ getr R 4%bv = Z_to_bv 64 TP /\ L5C.stk (hl_sptop L) M sp PMES2.MID_SCR /\ sp mod 16 = 0 /\
                  getr R 8%bv = Z_to_bv 64 V /\ getr R 9%bv = Z_to_bv 64 (V + O_STACK) /\ PMES2.is_nested es /\ PMES2.RX_ARR_INOBJ R M sp b (b + 32 * depth es) /\
                  PMES2.enc_objx M V S2 dI dD /\ stack_at M V es b capb /\ depth es < MAX_DEPTH /\
                  obj_on_stack L (sp + PMES2.FRAME) V ENC_SIZE /\ L5.defined M sp PMES2.FRAME /\
                  (32 * depth es = capb -> credit_ok L cr (stack_grow capb) /\ stack_grow capb <= NBU))
      (fun R M R' M' LB' cr' LBk W => exists (b' capb' : Z),
          getr R' 2%bv = Z_to_bv 64 sp /\ getr R' 4%bv = Z_to_bv 64 TP /\ getr R' 8%bv = Z_to_bv 64 V /\ getr R' 10%bv = Z_to_bv 64 (b' + 32 * (depth es + 1)) /\
          PMES2.regs_kept (PMES2.bk_arr PMES2.BK_ARRAY) R R' /\
          PMES2.enc_objx M' V S2 dI dD /\ PMES2.stack_mid M' V es (ECtx (PMES2.bk_arr PMES2.BK_ARRAY) 0 false) b' capb' /\
          LB' = LBo ++ [(b', capb')] /\ LBk = LBo /\ W = PMES2.W_mid PMES2.BK_ARRAY V sp /\
          ((32 * depth es < capb /\ b' = b /\ capb' = capb /\ cr' = cr) \/
           (32 * depth es = capb /\ capb' = stack_grow capb /\ cr' = debit L cr (stack_grow capb)))).

Lemma mid_of_body : (forall LBo cr sp V S2 b capb dI dD es, mid_body LBo cr sp V S2 b capb dI dD es) -> PMES2.mid_arr_inobj_spec L HI.
Proof. intros H. exact H. Qed.

Lemma arm_fast : forall LBo cr sp V S2 b capb dI dD es, 32 * depth es < capb -> mid_body LBo cr sp V S2 b capb dI dD es.
Proof.
  intros LBo cr sp V S2 b capb dI dD es Hlt.
  unfold mid_body, PMES2.cps_seg.
  intros fx R M model K HH Hmo HKnil Hfp PRE Hcont.
  destruct PRE as (Hsp & Htp & Hstk & Hsp16 & H8 & H9 & HGX & HRX & HOBJ & HSTK & Hdep & Hobjs & Hdef64 & Hgrow).
  unfold PMES2.RX_ARR_INOBJ in HRX. destruct HRX as (H18 & H19).
  assert (MS : PMES2.MID_SCR = 8384) by reflexivity. rewrite MS in *.
  destruct Hstk as (SK1 & SK2 & SK3 & SK4 & SK5).
  unfold PMES2.FRAME, ENC_SIZE in *. destruct Hobjs as (OV1 & OV2 & OV3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  destruct HSTK as (T1 & T2 & T3 & T4 & T5 & T6). unfold MAX_DEPTH in Hdep.
  assert (Hd0 : 0 <= depth es) by (unfold depth; lia).
  unfold PMES2.is_nested in HGX.
  assert (Hd1 : 1 <= depth es) by (unfold depth; destruct es; [contradiction | cbn [length]; lia]).
  assert (EP4 : u8 M (b + 32 * depth es - 28) 0).
  { assert (Hi : (length es - 1 < length es)%nat) by (unfold depth in Hd1; lia).
    destruct (T6 _ Hi) as (_ & Q4 & _). replace (b + 32 * depth es - 28) with (b + 32 * Z.of_nat (length es - 1) + 4) by (unfold depth in Hd1 |- *; lia). exact Q4. }
  unfold O_STACK in T1, T2, T3. replace (V + 264 + 8) with (V + 272) in T2 by lia. replace (V + 264 + 16) with (V + 280) in T3 by lia.
  assert (Hd264 : L5.defined M (V + 264) 24).
  { intros j Hj. destruct (Z_lt_dec j 8) as [Hj8|Hj8]; [|destruct (Z_lt_dec j 16) as [Hj16|Hj16]].
    - exact (PB.defined_of_u64 M (V + 264) _ T1 ltac:(lia) ltac:(lia) j ltac:(lia)).
    - replace (V + 264 + j) with (V + 272 + (j - 8)) by lia. exact (PB.defined_of_u64 M (V + 272) _ T2 ltac:(lia) ltac:(lia) (j - 8) ltac:(lia)).
    - replace (V + 264 + j) with (V + 280 + (j - 16)) by lia. exact (PB.defined_of_u64 M (V + 280) _ T3 ltac:(lia) ltac:(lia) (j - 16) ltac:(lia)). }
  pose proof HOBJ as HOBJ0.
  destruct HOBJ0 as (_ & _ & _ & _ & _ & E28 & _ & E30 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ecol & _ & _ & _ & _ & _ & (_ & E376) & _).
  unfold O_SPLITS, O_COLUMN, O_OBRACKET in E28, E30, Ecol, E376. replace (V + 28 + 2) with (V + 30) in E30 by lia. replace (V + 368 + 8) with (V + 376) in E376 by lia.
  destruct (EAK.u64_of_defined M (V + 296) Ecol) as (col & Hcolr & Hcolu).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & Hcr0 & _).
  destruct T5 as [[Hc0 Hb0]|(kk & Hkk & Hck)]; [lia|].
  assert (Hpk : 2 ^ kk <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in Hpk.
  assert (Hp0 : 0 < 2 ^ kk) by (apply Z.pow_pos_nonneg; lia).
  assert (Hcnz : capb <> 0) by lia.
  assert (HinLB : In (b, capb) (LBo ++ stack_blocks b capb)) by (rewrite (VBK.stack_blocks_pos b capb Hcnz); apply in_or_app; right; left; reflexivity).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & _). cbn [fst snd] in P0, P1, P2, P3, P4, Pdef.
  assert (PdefL : L5.defined M b capb) by (first [exact Pdef | (intros j Hj; apply Pdef; lia)]).
  rewrite (VBK.stack_blocks_pos b capb Hcnz) in HH.
  pose proof (hh_perm _ _ _ _ _ HH (Permutation_sym (Permutation_cons_append LBo (b, capb)))) as HH0.
  assert (HBC0 : 0 <= b /\ b + capb <= hl_ceil L) by nia.
  assert (HBL : Z.of_nat (Z.to_nat (32 * depth es)) = 32 * depth es) by (apply Z2Nat.id; lia).
  destruct (EAK.bytes_of_defined M (Z.to_nat (32 * depth es)) b ltac:(lia) ltac:(rewrite HBL; lia) ltac:(rewrite HBL; intros j Hj; apply PdefL; lia)) as (bs0 & Hbl & Hbs0).
  assert (Hbl' : Z.of_nat (length bs0) = 32 * depth es) by (rewrite Hbl; exact HBL).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; depth es; capb; col] 0))) (fun n => if Nat.eqb n 0 then map (Z_to_bv 8) bs0 else [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V8 : ev E0 8 = Z_to_bv 64 V) by (rewrite <- H8; exact (EV 8%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 (depth es)) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 capb) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 col) by reflexivity.
  assert (EB0 : eb E0 0 = map (Z_to_bv 8) bs0) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U8 : bv_unsigned (ev E0 8) = V) by (rewrite V8; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = depth es) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = capb) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = col) by (rewrite V35; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree 48 E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 8) = V /\ bv_unsigned (ev E1 32) = b /\ bv_unsigned (ev E1 33) = depth es /\
            bv_unsigned (ev E1 34) = capb /\ bv_unsigned (ev E1 35) = col).
  { intros E1 [AG _]. rewrite <- !AG by lia. repeat split; assumption. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, LER; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  assert (LSTK0 : 0 <= hl_stack L) by (rewrite LSTK; lia).
  set (W := PMES2.W_mid PMES2.BK_ARRAY V sp).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a Hw Hin. unfold W, PMES2.W_mid, PMES2.LOC, O_STACK in Hw. cbn [PMES2.bk_arr PMES2.BK_ARRAY] in Hw.
    destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (FPM0 : forall (fx0 fx' : FPState) R0 pc M1 R' pc' M', msteps (hl_segs L) (@mkst fx0 R0 (Z_to_bv 64 pc) M1 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PML.fp_ok fx0 -> PML.fp_ok fx')
    by (rewrite LS; exact FPM).
  assert (KST : forall (M' : PML.mem) LBk, L5C.hpres L LBk sp 8384 W M M' ->
            forall a, sp + 32 <= a < 2 ^ 64 -> ~ (V + 264 <= a < V + 288) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros M' LBk HP a Ha Hna. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
    apply (L5C.kept_stack_stk L LBk M sp 8384 W a); [repeat split; try lia; exact SK5 | lia | lia | rewrite LER; lia |].
    unfold W, PMES2.W_mid, PMES2.LOC, O_STACK. cbn [PMES2.bk_arr PMES2.BK_ARRAY].
    apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia|]. apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia | apply L5C.outside_nil]. }
  assert (OBJ' : forall (M' : PML.mem) LBk, L5C.hpres L LBk sp 8384 W M M' -> PMES2.enc_objx M' V S2 dI dD).
  { intros M' LBk HP. assert (AGV : forall a n, V <= a -> a + n <= V + 408 -> (a + n <= V + 264 \/ V + 288 <= a) -> L5C.agree_on M M' a n).
    { intros a n Ha Hn Hx i1 Hi1. apply (KST M' LBk HP); lia. }
    apply (EK3.enc_objx_agree M M' V S2 dI dD ltac:(lia) ltac:(unfold ENC_SIZE; lia)); unfold O_STACK, O_INDENT, O_COLON, O_COLUMN, ENC_SIZE.
    - apply AGV; lia. - apply AGV; lia. - apply AGV; lia.
    - apply (L5C.defined_agree M M' (V + 296) 8); [apply AGV; lia | exact Ecol].
    - exact HOBJ. }
  set (Cred := fun (_ : nat) (_ : env) (cr' : credit) => cr' = cr).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr HD <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr HD) with 8384; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr HD) by (change (CH.hd_scr HD) with 8384; lia).
  assert (NF32 : (32 <= NFX)%nat) by (unfold NFX; lia).
  assert (HSTKE : hl_stack L = CH.hd_hstk HD) by (rewrite LSTK; reflexivity).
  assert (DEF0 : L5.defined M (sp - CH.hd_scr HD) (CH.hd_scr HD)) by (change (CH.hd_scr HD) with 8384; exact SK5).
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs HD) -> SGP.region_vars_lt NFX rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg Hrg. unfold HD, FT.HDECL in Hrg. cbn [CH.hd_crs] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    all: rewrite U8 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs HD) -> SGP.region_vars_lt NFX rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg Hrg. unfold HD, FT.HDECL in Hrg. cbn [CH.hd_wrs] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U8 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + O_STACK, 24). split; [left; reflexivity | unfold L5.in_rng, O_STACK; cbn [fst snd]; lia].
    - rewrite U2 in Ha. rewrite u64_of_Z in Ha by lia. exists (sp, 24). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PMES2.PC_MID_ARR_INOBJ with (CC.cp_pc F.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := NFX) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LBo) (sp0 := sp) (d := HD)
    (W := W) (BLS := F.BLS) (Cred := Cred) (CPS := F.CPS) (TAGS := F.TAGS) (RETS := F.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  + exact HIok.
  + exact LYI.
  + exact LYE.
  + exact (PmLayout.ly_ro L LAY).
  + exact LSTK0.
  + exact STKF.
  + exact SCRP.
  + exact HSTKE.
  + exact NF32.
  + exact U2.
  + exact TP0.
  + exact W_OK.
  + exact CRS_OK.
  + exact WRS_OK.
  + intros rg a [].
  + exact HKnil.
  + exact ILO.
  + exact IHI.
  + exact FPM0.
  + rewrite LS. exact F.plans.
  + exact F.tags_ok.
  + exact heap_ok_fast.
  + exact (PmLayout.ly_malloc L LAY).
  + exact (PmLayout.ly_free L LAY).
  + intros pc [].
  + intros i c0' kk0 ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_fast _ _ _ _ _ IL) as X. unfold no_goto in X. discriminate X.
  + intros i c0' kk0 ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_fast_ok _ _ _ _ _ IL) as X. unfold leaf_fast in X. change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. cbn [negb andb] in X. discriminate X.
  + intros i c0' kk0 ps pc j cj IL Hcall Hnm Hret Hcj. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_fast_ok _ _ _ _ _ IL) as X. unfold leaf_fast in X. rewrite Hcall in X. cbn [negb andb] in X. discriminate X.
  + intros i c0' kk0 ps pc IL Hnc.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_fast_ok _ _ _ _ _ IL) as X. unfold leaf_fast in X. rewrite Hnc in X. cbn [negb andb] in X. unfold exit_fast in X.
    intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) NFX E0 M model LBo sp HD W F.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK
                  F.CPS GK.HULL_LO GK.HULL_HI F.TAGS F.RETS MALLOC FREE [] heap_ok_fast i c0' kk0 ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    apply Z.eqb_eq in X.
    match goal with H : Nat.leb _ (CC.cp_nx c0') = true |- _ => apply Nat.leb_le in H; rename H into XNF end.
    match goal with H : Nat.eqb i 0 = true |- _ => apply Nat.eqb_eq in H; rename H into Xi end. subst i.
    match goal with H : CH2.blocks_eqb _ _ = true |- _ => apply CH2.blocks_eqb_eq in H; rename H into XBL end.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    unfold Cred in HC1. subst cr1.
    assert (HagE' : env_agree NFX E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact XNF]]).
    destruct (FR E' HagE') as (F2 & F8 & F32 & F33 & F34 & _).
    assert (A32 : ev E 32 = ev E0 32) by (destruct HagE1 as [AG _]; symmetry; apply AG; unfold NFX; lia).
    assert (A34 : ev E 34 = ev E0 34) by (destruct HagE1 as [AG _]; symmetry; apply AG; unfold NFX; lia).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (REG : forall (x : bv 5) n e, CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e).
    { intros x n e Hc' Hx. exact (reg_of_leaf _ c0' ps E' R' M1 M' x n e HLF Hc' Hx). }
    assert (KEEP : forall y : reg, In (ridx y) KEPTN -> getr R' y = getr R y).
    { intros y Hy. match goal with H : CL.ps_keeps ps KEPTN = true |- _ => rewrite (CL.ps_keeps_sound GK.RSEGS c0' ps E0 E' R' M1 M' KEPTN NFX y HLF H HagE' Hy (kept_lt48 y Hy)) end. exact (EV y). }
    unfold CH2.cur in HH1. rewrite XBL in HH1. cbn [CH2.den map app fst snd edenot] in HH1. rewrite A32, A34, U32, U34 in HH1.
    pose proof (CH2.amb_hpres L HI LYI LYE NFX E0 M model LBo sp HD W F.BLS Cred STKF NF32 0%nat E M' m1 HA2 DEF0) as HP.
    change (CH.hd_scr HD) with 8384 in HP.
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf2 & _).
    destruct (Hwf2 (b, capb) ltac:(left; reflexivity)) as (_ & Bdef & _). cbn [fst snd] in Bdef.
    rewrite X, LS.
    apply (Hcont fx' R' M' m1 (LBo ++ [(b, capb)]) cr LBo W HFP); [| exact HP | exact Hbv1 | apply (hh_perm _ _ _ _ _ HH1); apply Permutation_cons_append].
    exists b, capb.
    split. { rewrite (REG 2%bv 2%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. cbn [edenot]. exact F2. }
    split; [rewrite (KEEP 4%bv ltac:(cbn; tauto)); exact Htp|].
    split. { rewrite (REG 8%bv 8%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. cbn [edenot]. exact F8. }
    split. { rewrite (REG 10%bv 10%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. unfold ctxb_fast. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [intros y Hy; apply KEEP; apply kept_in; exact Hy|].
    split; [exact (OBJ' M' LBo HP)|].
    split.
    { unfold PMES2.stack_mid. unfold O_STACK.
      assert (CB : forall o, 0 <= o <= 32 -> estart E' (SA ctxb_fast o) = b + 32 * depth es + o).
      { intros o Ho. assert (Ub : bv_unsigned (edenot E' ctxb_fast) = b + 32 * depth es) by (unfold ctxb_fast; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
        unfold estart. cbn [a_base a_off]. rewrite Ub. first [reflexivity | lia | (rewrite Z.mod_small; lia)]. }
      assert (C264 : u64 M' (V + 264) b).
      { pose proof (PB2.kword64_elim E' M' _ _ (V + 264) (CELL (KWord (SA (EVar 8) 264) 8 (EVar 32)) ltac:(assumption)) ltac:(ev_start)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite F32 in T. exact T. }
      assert (C280 : u64 M' (V + 264 + 16) (b + capb)).
      { pose proof (PB2.kword64_elim E' M' _ _ (V + 264 + 16) (CELL (KWord (SA (EVar 8) 280) 8 (EAlu ALU_ADD (EVar 32) (EVar 34))) ltac:(assumption)) ltac:(ev_start)) as T.
        replace (PB.uv E' (EAlu ALU_ADD (EVar 32) (EVar 34))) with (b + capb) in T by (unfold PB.uv; symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]). exact T. }
      assert (CX0 : u32 M' (b + 32 * depth es) 1).
      { pose proof (PB2.kword32_elim E' M' _ _ (b + 32 * depth es) (CELL (KWord (SA ctxb_fast 0) 4 (ELit 1)) ltac:(assumption)) ltac:(rewrite CB by lia; lia)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 1) in T by lia. exact T. }
      assert (CX4 : u8 M' (b + 32 * depth es + 4) 0).
      { pose proof (PB2.kword8_elim E' M' _ _ (b + 32 * depth es + 4) (CELL (KWord (SA ctxb_fast 4) 1 (ELit 0)) ltac:(assumption)) ltac:(rewrite CB by lia; lia)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
      assert (CX6 : u8 M' (b + 32 * depth es + 6) 0).
      { pose proof (PB2.kword8_elim E' M' _ _ (b + 32 * depth es + 6) (CELL (KWord (SA ctxb_fast 6) 1 (ELit 0)) ltac:(assumption)) ltac:(rewrite CB by lia; lia)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
      assert (CX24 : u64 M' (b + 32 * depth es + 24) 0).
      { pose proof (PB2.kword64_elim E' M' _ _ (b + 32 * depth es + 24) (CELL (KWord (SA ctxb_fast 24) 8 (ELit 0)) ltac:(assumption)) ltac:(rewrite CB by lia; lia)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
      assert (BL' : L5.bytes_at RSEGS M' b bs0).
      { pose proof (proj2 HagE') as EBE.
        exact (proj1 (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat b bs0 (CELL (KBlob (SA (EVar 32) 0) (EMd M_MUL (ELit 32) (EVar 33)) 0) ltac:(assumption)) ltac:(ev_start) ltac:(rewrite <- EBE; reflexivity))). }
      split; [exact C264|]. split; [exact C280|].
      split; [lia|]. split; [exists kk; lia|].
      split.
      { intros i0 Hi0. pose proof (T6 i0 Hi0) as Ci.
        replace (b + 32 * Z.of_nat i0) with (b + Z.of_nat (32 * i0)) in Ci |- * by lia.
        apply (VBK.ctx_at_xfer M M' b b _ bs0 (32 * i0)); [| lia | lia | lia | lia | exact Hbs0 | exact BL' | | exact Ci].
        - unfold depth in Hbl'. lia.
        - intros j Hj. replace (b + Z.of_nat (32 * i0) + j) with (b + (Z.of_nat (32 * i0) + j)) by lia. apply Bdef. unfold depth in Hbl'. lia. }
      unfold ctx_at. cbn [ec_arr ec_nla ec_count b2z].
      split; [exact CX0|]. split; [exact CX4|]. split; [exact CX6|]. split; [exact CX24|]. split; [lia|].
      intros j0 Hj0. replace (b + 32 * depth es + j0) with (b + (32 * depth es + j0)) by lia. apply Bdef. lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    left. split; [lia|]. split; [reflexivity|]. split; reflexivity.
  + reflexivity.
  + rewrite LS. split.
    { rewrite regs_fast. apply VBK.regs_ok_updn; [lia| |].
      - apply VBK.regs_ok_updn; [lia| |].
        + apply VBK.regs_ok_updn; [lia | exact (regs_ok_id R _ _) |].
          replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H9. unfold O_STACK.
          rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia].
        + replace (Z_to_bv 5 (Z.of_nat 18)) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H18. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. symmetry. unfold ctxb_fast. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia].
      - cbn [edenot]. replace (Z_to_bv 5 (Z.of_nat 19)) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H19, V32. reflexivity. }
    unfold know_ok, F.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil]; first
      [ eapply CL5.kword64_intro; [ev_start | lia | lia | | first [exact T1 | exact T2 | exact T3 | exact Hcolu | exact E376]]; rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)); f_equal; try (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia])
      | eapply PB2.kword8_intro; [ev_start | lia | lia | reflexivity | lia | first [exact E28 | exact E30]]
      | eapply PB2.kword8_intro with (A := b + 32 * depth es - 28); [rewrite (CL5.estart_lin E0 _ (-28) (b + 32 * depth es)); [lia | lin_eval; rw_atoms; lia | lia] | lia | lia | reflexivity | lia | exact EP4]
      | eapply CL5.kblob_intro with (bs := bs0) (A := b); [ev_start | apply CL5.elen_lin; [lin_eval; rw_atoms; lia | lia] | lia | lia | lia | exact EB0 | exact Hbs0 | rewrite Hbl'; intros j Hj; apply PdefL; lia]
      | e_range
      | e_align OV3 | e_align SK1 | e_align P2
      | e_unk | e_wr | e_disj
      | idtac ].
    all: fail "entry knowledge left".
  + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hdd; exact Hdd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. change (nth 0 F.BLS []) with [(EVar 32, EVar 34)]. cbn [CH2.den map app fst snd edenot]. rewrite U32, U34. exact HH0.
  + exact Hfp.
Qed.

Lemma arm_grow : forall (C : Z) (CPS : list CC.cutpoint) (TAGS : list (list CC.tag)) (BLS : list CA.blocks) (RETS : list (nat * nat * nat * Z)) (c0 : CC.cutpoint),
  (forall i c, nth_error CPS i = Some c -> CC.plan_sound GK.RSEGS c) ->
  CC.tags_chk CPS TAGS NFX = true ->
  CH2.heap_chk NFX HD BLS CPS GK.HULL_LO GK.HULL_HI TAGS RETS MALLOC FREE [] = true ->
  CH2.leaves_all CPS TAGS no_goto = true ->
  CH2.leaves_all CPS TAGS (leaf_grow C BLS CPS RETS) = true ->
  nth_error CPS 0 = Some c0 ->
  CC.cp_pc c0 = PMES2.PC_MID_ARR_INOBJ /\ CC.cp_regs c0 = regs_grow C /\
    CC.cp_know c0 = know_grow C /\ nth 0 BLS [] = [(EVar 32, ELit C)] ->
  forall LBo cr sp V S2 b capb dI dD es, capb = C -> 32 * depth es = capb -> mid_body LBo cr sp V S2 b capb dI dD es.
Proof.
  intros C CPS TAGS BLS RETS c0 HPL HTG HCHK HNG HLC Hc0 (PC0 & RG0 & KN0 & BL0) LBo cr sp V S2 b capb dI dD es HcC Hd32.
  unfold mid_body, PMES2.cps_seg.
  intros fx R M model K HH Hmo HKnil Hfp PRE Hcont.
  destruct PRE as (Hsp & Htp & Hstk & Hsp16 & H8 & H9 & HGX & HRX & HOBJ & HSTK & Hdep & Hobjs & Hdef64 & Hgrow).
  unfold PMES2.RX_ARR_INOBJ in HRX. destruct HRX as (H18 & H19). unfold PMES2.is_nested in HGX.
  subst capb.
  assert (MS : PMES2.MID_SCR = 8384) by reflexivity. rewrite MS in *.
  destruct Hstk as (SK1 & SK2 & SK3 & SK4 & SK5).
  unfold PMES2.FRAME, ENC_SIZE in *. destruct Hobjs as (OV1 & OV2 & OV3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  destruct HSTK as (T1 & T2 & T3 & T4 & T5 & T6). unfold MAX_DEPTH in Hdep.
  assert (Hd1 : 1 <= depth es) by (unfold depth; destruct es; [contradiction | cbn [length]; lia]).
  unfold O_STACK in T1, T2, T3. replace (V + 264 + 8) with (V + 272) in T2 by lia. replace (V + 264 + 16) with (V + 280) in T3 by lia.
  rewrite Hd32 in T2.
  assert (EP4 : u8 M (b + (C - 28)) 0).
  { assert (Hi : (length es - 1 < length es)%nat) by (unfold depth in Hd1; lia).
    destruct (T6 _ Hi) as (_ & Q4 & _). replace (b + (C - 28)) with (b + 32 * Z.of_nat (length es - 1) + 4) by (unfold depth in Hd1, Hd32; lia). exact Q4. }
  destruct (Hgrow Hd32) as (Hcredit & HnB).
  assert (SG : stack_grow C = 2 * C) by (unfold stack_grow; destruct (Z.eqb_spec C 0); lia).
  rewrite SG in Hcredit, HnB.
  assert (Hd264 : L5.defined M (V + 264) 24).
  { intros j Hj. destruct (Z_lt_dec j 8) as [Hj8|Hj8]; [|destruct (Z_lt_dec j 16) as [Hj16|Hj16]].
    - exact (PB.defined_of_u64 M (V + 264) _ T1 ltac:(lia) ltac:(lia) j ltac:(lia)).
    - replace (V + 264 + j) with (V + 272 + (j - 8)) by lia. exact (PB.defined_of_u64 M (V + 272) _ T2 ltac:(lia) ltac:(lia) (j - 8) ltac:(lia)).
    - replace (V + 264 + j) with (V + 280 + (j - 16)) by lia. exact (PB.defined_of_u64 M (V + 280) _ T3 ltac:(lia) ltac:(lia) (j - 16) ltac:(lia)). }
  pose proof HOBJ as HOBJ0.
  destruct HOBJ0 as (_ & _ & _ & _ & _ & E28 & _ & E30 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ecol & _ & _ & _ & _ & _ & (_ & E376) & _).
  unfold O_SPLITS, O_COLUMN, O_OBRACKET in E28, E30, Ecol, E376. replace (V + 28 + 2) with (V + 30) in E30 by lia. replace (V + 368 + 8) with (V + 376) in E376 by lia.
  destruct (EAK.u64_of_defined M (V + 296) Ecol) as (col & Hcolr & Hcolu).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & Hcr0 & _).
  destruct T5 as [[Hc0' Hb0]|(kk & Hkk & Hck)]; [lia|].
  assert (Hpk : 2 ^ kk <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in Hpk.
  assert (Hp0 : 0 < 2 ^ kk) by (apply Z.pow_pos_nonneg; lia).
  assert (Hcnz : C <> 0) by lia.
  assert (HinLB : In (b, C) (LBo ++ stack_blocks b C)) by (rewrite (VBK.stack_blocks_pos b C Hcnz); apply in_or_app; right; left; reflexivity).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & _). cbn [fst snd] in P0, P1, P2, P3, P4, Pdef.
  assert (PdefL : L5.defined M b C) by (first [exact Pdef | (intros j Hj; apply Pdef; lia)]).
  rewrite (VBK.stack_blocks_pos b C Hcnz) in HH.
  pose proof (hh_perm _ _ _ _ _ HH (Permutation_sym (Permutation_cons_append LBo (b, C)))) as HH0.
  assert (HBC0 : 0 <= b /\ b + C <= hl_ceil L) by nia.
  assert (HBL : Z.of_nat (Z.to_nat C) = C) by (apply Z2Nat.id; lia).
  destruct (EAK.bytes_of_defined M (Z.to_nat C) b ltac:(lia) ltac:(rewrite HBL; lia) ltac:(rewrite HBL; exact PdefL)) as (bs0 & Hbl & Hbs0).
  assert (Hbl' : Z.of_nat (length bs0) = C) by (rewrite Hbl; exact HBL).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; depth es; C; col] 0))) (fun n => if Nat.eqb n 0 then map (Z_to_bv 8) bs0 else [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V8 : ev E0 8 = Z_to_bv 64 V) by (rewrite <- H8; exact (EV 8%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 (depth es)) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 C) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 col) by reflexivity.
  assert (EB0 : eb E0 0 = map (Z_to_bv 8) bs0) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U8 : bv_unsigned (ev E0 8) = V) by (rewrite V8; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = depth es) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = C) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = col) by (rewrite V35; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree 48 E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 8) = V /\ bv_unsigned (ev E1 32) = b /\ bv_unsigned (ev E1 33) = depth es /\
            bv_unsigned (ev E1 34) = C /\ bv_unsigned (ev E1 35) = col).
  { intros E1 [AG _]. rewrite <- !AG by lia. repeat split; assumption. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, LER; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  assert (LSTK0 : 0 <= hl_stack L) by (rewrite LSTK; lia).
  set (W := PMES2.W_mid PMES2.BK_ARRAY V sp).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a Hw Hin. unfold W, PMES2.W_mid, PMES2.LOC, O_STACK in Hw. cbn [PMES2.bk_arr PMES2.BK_ARRAY] in Hw.
    destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (FPM0 : forall (fx0 fx' : FPState) R0 pc M1 R' pc' M', msteps (hl_segs L) (@mkst fx0 R0 (Z_to_bv 64 pc) M1 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PML.fp_ok fx0 -> PML.fp_ok fx')
    by (rewrite LS; exact FPM).
  assert (KST : forall (M' : PML.mem) LBk, L5C.hpres L LBk sp 8384 W M M' ->
            forall a, sp + 32 <= a < 2 ^ 64 -> ~ (V + 264 <= a < V + 288) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros M' LBk HP a Ha Hna. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
    apply (L5C.kept_stack_stk L LBk M sp 8384 W a); [repeat split; try lia; exact SK5 | lia | lia | rewrite LER; lia |].
    unfold W, PMES2.W_mid, PMES2.LOC, O_STACK. cbn [PMES2.bk_arr PMES2.BK_ARRAY].
    apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia|]. apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia | apply L5C.outside_nil]. }
  assert (OBJ' : forall (M' : PML.mem) LBk, L5C.hpres L LBk sp 8384 W M M' -> PMES2.enc_objx M' V S2 dI dD).
  { intros M' LBk HP. assert (AGV : forall a n, V <= a -> a + n <= V + 408 -> (a + n <= V + 264 \/ V + 288 <= a) -> L5C.agree_on M M' a n).
    { intros a n Ha Hn Hx i1 Hi1. apply (KST M' LBk HP); lia. }
    apply (EK3.enc_objx_agree M M' V S2 dI dD ltac:(lia) ltac:(unfold ENC_SIZE; lia)); unfold O_STACK, O_INDENT, O_COLON, O_COLUMN, ENC_SIZE.
    - apply AGV; lia. - apply AGV; lia. - apply AGV; lia.
    - apply (L5C.defined_agree M M' (V + 296) 8); [apply AGV; lia | exact Ecol].
    - exact HOBJ. }
  set (Cred := fun (i : nat) (_ : env) (cr' : credit) => cr' = if Nat.eqb i 0 then cr else debit L cr (2 * C)).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr HD <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr HD) with 8384; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr HD) by (change (CH.hd_scr HD) with 8384; lia).
  assert (NF32 : (32 <= NFX)%nat) by (unfold NFX; lia).
  assert (HSTKE : hl_stack L = CH.hd_hstk HD) by (rewrite LSTK; reflexivity).
  assert (DEF0 : L5.defined M (sp - CH.hd_scr HD) (CH.hd_scr HD)) by (change (CH.hd_scr HD) with 8384; exact SK5).
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs HD) -> SGP.region_vars_lt NFX rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg Hrg. unfold HD, FT.HDECL in Hrg. cbn [CH.hd_crs] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    all: rewrite U8 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs HD) -> SGP.region_vars_lt NFX rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg Hrg. unfold HD, FT.HDECL in Hrg. cbn [CH.hd_wrs] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U8 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + O_STACK, 24). split; [left; reflexivity | unfold L5.in_rng, O_STACK; cbn [fst snd]; lia].
    - rewrite U2 in Ha. rewrite u64_of_Z in Ha by lia. exists (sp, 24). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. rewrite <- PC0. rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := NFX) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LBo) (sp0 := sp) (d := HD)
    (W := W) (BLS := BLS) (Cred := Cred) (CPS := CPS) (TAGS := TAGS) (RETS := RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  + exact HIok.
  + exact LYI.
  + exact LYE.
  + exact (PmLayout.ly_ro L LAY).
  + exact LSTK0.
  + exact STKF.
  + exact SCRP.
  + exact HSTKE.
  + exact NF32.
  + exact U2.
  + exact TP0.
  + exact W_OK.
  + exact CRS_OK.
  + exact WRS_OK.
  + intros rg a [].
  + exact HKnil.
  + exact ILO.
  + exact IHI.
  + exact FPM0.
  + rewrite LS. exact HPL.
  + exact HTG.
  + exact HCHK.
  + exact (PmLayout.ly_malloc L LAY).
  + exact (PmLayout.ly_free L LAY).
  + intros pc [].
  + intros i c0' kk0 ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ HNG _ _ _ _ _ IL) as X. unfold no_goto in X. discriminate X.
  + intros i c0' kk0 ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ HLC _ _ _ _ _ IL) as X. unfold leaf_grow in X. change (CH2.is_call MALLOC FREE [] MALLOC) with true in X.
    rewrite Z.eqb_refl in X. cbn [negb andb] in X. discriminate X.
  + intros i c0' kk0 ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr1 HagE Hag HLF HC E2 HagE2.
    pose proof (CH2.leaves_all_sound _ _ _ HLC _ _ _ _ _ IL) as X. unfold leaf_grow in X. rewrite Hcall, Hret in X. cbv beta iota in X.
    repeat (apply andb_prop in X as [X ?Y]).
    match goal with H : negb (Nat.eqb i 0) = true |- _ => apply negb_true_iff in H; rename H into Xi end.
    match goal with H : negb (Nat.eqb j 0) = true |- _ => apply negb_true_iff in H; rename H into Xj end.
    unfold Cred in HC |- *. rewrite Xi in HC. rewrite Xj. exact HC.
  + intros i c0' kk0 ps pc IL Hnc.
    pose proof (CH2.leaves_all_sound _ _ _ HLC _ _ _ _ _ IL) as X. unfold leaf_grow in X. rewrite Hnc in X. cbv beta iota in X.
    destruct (Z.eqb_spec pc OPNEW) as [->|Hno].
    {
      destruct (CH2.ret_of RETS i kk0) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error CPS j) as [cj|] eqn:Hcj; [|discriminate].
      repeat (apply andb_prop in X as [X ?Y]).
      apply Nat.eqb_eq in X. apply negb_true_iff in Y3. apply Z.eqb_eq in Y2. apply Nat.leb_le in Y1. apply expr_eqb_eq in Y0.
      destruct (EON.opnew_chk NFX HD c0' ps cj (nth i BLS []) (nth j BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      set (XI := fun (_ : nat) (_ : env) (_ : PML.mem) => True).
      assert (LO : CC.leaf_ok (hl_segs L) CPS (CH2.amb3 L HI NFX E0 M model LBo sp HD W BLS Cred XI) K PML.fp_ok i c0' ps).
      { apply (EONU.opnew_leaf_okU L HI HIok LAY NFX E0 M model LBo sp HD W BLS Cred STKF SCRP NF32 U2 TP0 W_OK
                 CRS_OK WRS_OK ltac:(intros rg a []) CPS TAGS RETS K HKnil XI DEF0 OPNEWXU i c0' kk0 ps j cj ci IL Hret Hcj Y2 Hchk); [|intros; exact I].
        intros E E' R' M1 M1' cr1 HagE' Hag HLF HC. unfold Cred in HC. rewrite X in HC. cbn in HC. subst cr1.
        rewrite Y0. unfold EON.uv, PB.uv. cbn [edenot]. rewrite u64_of_Z by lia.
        split; [lia|]. split; [exact Hcredit|]. intros E2 _. unfold Cred. rewrite Y3. reflexivity. }
      intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF HIH.
      apply (LO fx' E R1 M1 m1 E' R' M' HAt (conj HAmb I) HFP Hag HLF).
      intros j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 [HA2 _] HFP2 Hlt. exact (HIH j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 HA2 HFP2 Hlt). }
    cbv iota in X.
    destruct (Z.eqb_spec pc MEMCPY) as [->|Hnm].
    {
      destruct (CH2.ret_of RETS i kk0) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error CPS j) as [cj|] eqn:Hcj; [|discriminate].
      repeat (apply andb_prop in X as [X ?Y]).
      apply negb_true_iff in X. apply negb_true_iff in Y0.
      refine (CH2.copy_leaf_ok L HI HIok LYI LYE (PmLayout.ly_ro L LAY) LSTK0 NFX E0 M model LBo sp HD W BLS Cred STKF SCRP HSTKE NF32 U2 TP0 W_OK WRS_OK
                CPS K PML.fp_ok i c0' ps j cj MEMCPY FPM0 (Memcpy1_u5.MC1.memcpy_copy1 L LS) Hcj Y _).
      intros E E' R' M1 M1' cr1 _ _ _ HC E2 _. unfold Cred in HC |- *. rewrite X in HC. rewrite Y0. exact HC. }
    cbv iota in X.
    intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _. unfold exit_grow in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) NFX E0 M model LBo sp HD W BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK
                  CPS GK.HULL_LO GK.HULL_HI TAGS RETS MALLOC FREE [] HCHK i c0' kk0 ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    apply Z.eqb_eq in X.
    match goal with H : Nat.leb _ (CC.cp_nx c0') = true |- _ => apply Nat.leb_le in H; rename H into XNF end.
    match goal with H : negb (Nat.eqb i 0) = true |- _ => apply negb_true_iff in H; rename H into Xi end.
    match goal with H : CH2.blocks_eqb _ _ = true |- _ => apply CH2.blocks_eqb_eq in H; rename H into XBL end.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    unfold Cred in HC1. rewrite Xi in HC1. subst cr1.
    assert (HagE' : env_agree NFX E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | unfold NFX in *; lia]]).
    destruct (FR E' HagE') as (F2 & F8 & F32 & _ & _ & _).
    assert (A48 : ev E' 48 = ev E 48) by (destruct Hag as [AG _]; symmetry; apply AG; unfold NFX in XNF; lia).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (REG : forall (x : bv 5) n e, CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e).
    { intros x n e Hc' Hx. exact (reg_of_leaf _ c0' ps E' R' M1 M' x n e HLF Hc' Hx). }
    assert (KEEP : forall y : reg, In (ridx y) KEPTN -> getr R' y = getr R y).
    { intros y Hy. match goal with H : CL.ps_keeps ps KEPTN = true |- _ => rewrite (CL.ps_keeps_sound GK.RSEGS c0' ps E0 E' R' M1 M' KEPTN NFX y HLF H HagE' Hy (kept_lt48 y Hy)) end. exact (EV y). }
    unfold CH2.cur in HH1. rewrite XBL in HH1. cbn [CH2.den map app fst snd edenot] in HH1.
    rewrite (u64_of_Z (2 * C)) in HH1 by lia.
    set (b' := bv_unsigned (ev E 48)) in *.
    assert (U48 : bv_unsigned (ev E' 48) = b') by (rewrite A48; reflexivity).
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf2 & _).
    destruct (Hwf2 (b', 2 * C) ltac:(left; reflexivity)) as ((B0 & B1 & B2 & B3 & B4) & Bdef & _). cbn [fst snd] in B0, B1, B2, B3, B4, Bdef.
    pose proof (CH2.amb_hpres L HI LYI LYE NFX E0 M model LBo sp HD W BLS Cred STKF NF32 i E M' m1 HA2 DEF0) as HP.
    change (CH.hd_scr HD) with 8384 in HP.
    rewrite X, LS.
    apply (Hcont fx' R' M' m1 (LBo ++ [(b', 2 * C)]) (debit L cr (2 * C)) LBo W HFP); [| exact HP | exact Hbv1 | apply (hh_perm _ _ _ _ _ HH1); apply Permutation_cons_append].
    exists b', (2 * C).
    split. { rewrite (REG 2%bv 2%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. cbn [edenot]. exact F2. }
    split; [rewrite (KEEP 4%bv ltac:(cbn; tauto)); exact Htp|].
    split. { rewrite (REG 8%bv 8%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. cbn [edenot]. exact F8. }
    split. { rewrite (REG 10%bv 10%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal.
             rewrite (u_add_lit E' (EVar 48) (C + 32) b' U48) by lia. lia. }
    split; [intros y Hy; apply KEEP; apply kept_in; exact Hy|].
    split; [exact (OBJ' M' LBo HP)|].
    split.
    { unfold PMES2.stack_mid. unfold O_STACK.
      assert (C264 : u64 M' (V + 264) b').
      { pose proof (PB2.kword64_elim E' M' _ _ (V + 264) (CELL (KWord (SA (EVar 8) 264) 8 (EVar 48)) ltac:(assumption)) ltac:(ev_start)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite U48 in T. exact T. }
      assert (C280 : u64 M' (V + 264 + 16) (b' + 2 * C)).
      { pose proof (PB2.kword64_elim E' M' _ _ (V + 264 + 16) (CELL (KWord (SA (EVar 8) 280) 8 (EAlu ALU_ADD (EVar 48) (ELit (2 * C)))) ltac:(assumption)) ltac:(ev_start)) as T.
        replace (PB.uv E' (EAlu ALU_ADD (EVar 48) (ELit (2 * C)))) with (b' + 2 * C) in T by (unfold PB.uv; symmetry; apply u_add_lit; [exact U48 | lia | lia]). exact T. }
      assert (CX0 : u32 M' (b' + C) 1).
      { pose proof (PB2.kword32_elim E' M' _ _ (b' + C) (CELL (KWord (SA (EVar 48) C) 4 (ELit 1)) ltac:(assumption)) ltac:(ev_start)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 1) in T by lia. exact T. }
      assert (CX4 : u8 M' (b' + C + 4) 0).
      { pose proof (PB2.kword8_elim E' M' _ _ (b' + C + 4) (CELL (KWord (SA (EVar 48) (C + 4)) 1 (ELit 0)) ltac:(assumption)) ltac:(ev_start)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
      assert (CX6 : u8 M' (b' + C + 6) 0).
      { pose proof (PB2.kword8_elim E' M' _ _ (b' + C + 6) (CELL (KWord (SA (EVar 48) (C + 6)) 1 (ELit 0)) ltac:(assumption)) ltac:(ev_start)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
      assert (CX24 : u64 M' (b' + C + 24) 0).
      { pose proof (PB2.kword64_elim E' M' _ _ (b' + C + 24) (CELL (KWord (SA (EVar 48) (C + 24)) 8 (ELit 0)) ltac:(assumption)) ltac:(ev_start)) as T.
        unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
      assert (BL' : L5.bytes_at RSEGS M' b' bs0).
      { pose proof (proj2 HagE') as EBE.
        exact (proj1 (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat b' bs0 (CELL (KBlob (SA (EVar 48) 0) (ELit C) 0) ltac:(assumption)) ltac:(ev_start) ltac:(rewrite <- EBE; reflexivity))). }
      split; [exact C264|]. split; [exact C280|].
      split; [lia|]. split.
      { assert (Hk10 : kk <> 10) by (intros Hk; subst kk; change (2 ^ 10) with 1024 in Hck; lia).
        exists (kk + 1). split; [lia|]. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia. }
      split.
      { intros i0 Hi0. pose proof (T6 i0 Hi0) as Ci.
        replace (b + 32 * Z.of_nat i0) with (b + Z.of_nat (32 * i0)) in Ci by lia.
        replace (b' + 32 * Z.of_nat i0) with (b' + Z.of_nat (32 * i0)) by lia.
        apply (VBK.ctx_at_xfer M M' b b' _ bs0 (32 * i0)); [| lia | lia | lia | lia | exact Hbs0 | exact BL' | | exact Ci].
        - unfold depth in Hd32. lia.
        - intros j Hj. replace (b' + Z.of_nat (32 * i0) + j) with (b' + (Z.of_nat (32 * i0) + j)) by lia. apply Bdef. unfold depth in Hd32. lia. }
      replace (b' + 32 * depth es) with (b' + C) by lia.
      unfold ctx_at. cbn [ec_arr ec_nla ec_count b2z].
      split; [exact CX0|]. split; [exact CX4|]. split; [exact CX6|]. split; [exact CX24|]. split; [lia|].
      intros j0 Hj0. replace (b' + C + j0) with (b' + (C + j0)) by lia. apply Bdef. lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    right. split; [lia|]. rewrite SG. split; reflexivity.
  + exact Hc0.
  + rewrite LS. split.
    { rewrite RG0. unfold regs_grow. apply VBK.regs_ok_updn; [lia| |].
      - apply VBK.regs_ok_updn; [lia| |].
        + apply VBK.regs_ok_updn; [lia | exact (regs_ok_id R _ _) |].
          replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H9. unfold O_STACK.
          rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia].
        + replace (Z_to_bv 5 (Z.of_nat 18)) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H18. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. symmetry. rewrite (u_add_lit E0 (EVar 32) C b U32) by lia. lia.
      - cbn [edenot]. replace (Z_to_bv 5 (Z.of_nat 19)) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H19, V32. reflexivity. }
    unfold know_ok. rewrite KN0. unfold know_grow.
    repeat (apply Forall_cons); [.. | apply Forall_nil]; first
      [ eapply CL5.kword64_intro; [ev_start | lia | lia | | first [exact T1 | exact T2 | exact T3 | exact Hcolu | exact E376]]; rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)); f_equal;
        first [apply u_add_lit; [exact U32 | lia | lia] | apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]]
      | eapply PB2.kword8_intro; [ev_start | lia | lia | reflexivity | lia | first [exact E28 | exact E30]]
      | eapply PB2.kword8_intro with (A := b + (C - 28)); [ev_start | lia | lia | reflexivity | lia | exact EP4]
      | eapply CL5.kblob_intro with (bs := bs0) (A := b); [ev_start | elit_len | lia | lia | lia | exact EB0 | exact Hbs0 | rewrite Hbl'; exact PdefL]
      | e_range
      | e_align OV3 | e_align SK1 | e_align P2
      | eapply CL5.kunk_intro; [ev_start | first [elit_len | ev_len] | lia | lia | lia | ev_def]
      | eapply CL5.kwr_intro; [ev_start | first [elit_len | ev_len] | lia | lia | lia | ev_def]
      | eapply CL5.kdisj_intro; [ev_start | first [elit_len | ev_len] | ev_start | first [elit_len | ev_len] | lia]
      | idtac ].
    all: fail "entry knowledge left".
  + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hdd; exact Hdd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. rewrite BL0. cbn [CH2.den map app fst snd edenot]. rewrite U32, (u64_of_Z C) by lia. exact HH0.
  + exact Hfp.
Qed.

Lemma k_cases : forall k, 0 <= k <= 9 -> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9.
Proof.
  intros k Hk.
  destruct (Z_lt_le_dec k 1); [left; lia|]. right.
  destruct (Z_lt_le_dec k 2); [left; lia|]. right.
  destruct (Z_lt_le_dec k 3); [left; lia|]. right.
  destruct (Z_lt_le_dec k 4); [left; lia|]. right.
  destruct (Z_lt_le_dec k 5); [left; lia|]. right.
  destruct (Z_lt_le_dec k 6); [left; lia|]. right.
  destruct (Z_lt_le_dec k 7); [left; lia|]. right.
  destruct (Z_lt_le_dec k 8); [left; lia|]. right.
  lia.
Qed.

Theorem mid_ok : PMES2.mid_arr_inobj_spec L HI.
Proof.
  apply mid_of_body. intros LBo cr sp V S2 b capb dI dD es.
  unfold mid_body, PMES2.cps_seg. intros fx R M model K HH Hmo HKnil Hfp PRE Hcont.
  pose proof PRE as PRE0. cbv beta in PRE0.
  destruct PRE0 as (_ & _ & _ & _ & _ & _ & HGX & _ & _ & HSTK & Hdep & _).
  destruct HSTK as (_ & _ & _ & T4 & T5 & _).
  unfold PMES2.is_nested in HGX. unfold MAX_DEPTH in Hdep.
  assert (Hd1 : 1 <= depth es) by (unfold depth; destruct es; [contradiction | cbn [length]; lia]).
  destruct (Z_lt_ge_dec (32 * depth es) capb) as [Hlt|Hge].
  - exact (arm_fast LBo cr sp V S2 b capb dI dD es Hlt fx R M model K HH Hmo HKnil Hfp PRE Hcont).
  - assert (Heq : 32 * depth es = capb) by lia.
    destruct T5 as [[Hc0 _]|(kk & Hkk & Hck)]; [lia|].
    assert (Hk10 : kk <> 10) by (intros Hk; subst kk; change (32 * 2 ^ 10) with 32768 in Hck; lia).
    assert (Hk9 : 0 <= kk <= 9) by lia. clear Hk10.
    pose proof (k_cases kk Hk9) as Hks.
    destruct Hks as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].
    + exact (arm_grow (32 * 2 ^ 0) G0.CPS G0.TAGS G0.BLS G0.RETS G0.cp0 G0.plans G0.tags_ok heap_ok_G0 no_goto_G0 leaf_G0 eq_refl cp0_G0 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
    + exact (arm_grow (32 * 2 ^ 1) G1.CPS G1.TAGS G1.BLS G1.RETS G1.cp0 G1.plans G1.tags_ok heap_ok_G1 no_goto_G1 leaf_G1 eq_refl cp0_G1 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
    + exact (arm_grow (32 * 2 ^ 2) G2.CPS G2.TAGS G2.BLS G2.RETS G2.cp0 G2.plans G2.tags_ok heap_ok_G2 no_goto_G2 leaf_G2 eq_refl cp0_G2 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
    + exact (arm_grow (32 * 2 ^ 3) G3.CPS G3.TAGS G3.BLS G3.RETS G3.cp0 G3.plans G3.tags_ok heap_ok_G3 no_goto_G3 leaf_G3 eq_refl cp0_G3 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
    + exact (arm_grow (32 * 2 ^ 4) G4.CPS G4.TAGS G4.BLS G4.RETS G4.cp0 G4.plans G4.tags_ok heap_ok_G4 no_goto_G4 leaf_G4 eq_refl cp0_G4 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
    + exact (arm_grow (32 * 2 ^ 5) G5.CPS G5.TAGS G5.BLS G5.RETS G5.cp0 G5.plans G5.tags_ok heap_ok_G5 no_goto_G5 leaf_G5 eq_refl cp0_G5 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
    + exact (arm_grow (32 * 2 ^ 6) G6.CPS G6.TAGS G6.BLS G6.RETS G6.cp0 G6.plans G6.tags_ok heap_ok_G6 no_goto_G6 leaf_G6 eq_refl cp0_G6 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
    + exact (arm_grow (32 * 2 ^ 7) G7.CPS G7.TAGS G7.BLS G7.RETS G7.cp0 G7.plans G7.tags_ok heap_ok_G7 no_goto_G7 leaf_G7 eq_refl cp0_G7 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
    + exact (arm_grow (32 * 2 ^ 8) G8.CPS G8.TAGS G8.BLS G8.RETS G8.cp0 G8.plans G8.tags_ok heap_ok_G8 no_goto_G8 leaf_G8 eq_refl cp0_G8 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
    + exact (arm_grow (32 * 2 ^ 9) G9.CPS G9.TAGS G9.BLS G9.RETS G9.cp0 G9.plans G9.tags_ok heap_ok_G9 no_goto_G9 leaf_G9 eq_refl cp0_G9 LBo cr sp V S2 b capb dI dD es Hck Heq fx R M model K HH Hmo HKnil Hfp PRE Hcont).
Qed.

End Mid.
End VBM_AOU.
