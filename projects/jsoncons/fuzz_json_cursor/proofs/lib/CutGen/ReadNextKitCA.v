(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutShA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs PmCurSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import ReentryCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_rnext_casan_T Cut_rnext_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_rnext_casan.
Module GT := Cut_rnext_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module RNXC.
Definition PC_RN : Z := 735060.
Definition LOOPA : Z := 735328.
Definition PC_RC : Z := 746600.
Definition PC_PS : Z := 748972.
Definition PC_SETEC : Z := 747008.
Definition RETPC : Z := 735864.
Definition G_GUARD : Z := 6877256. Definition AXT : Z := 7015072. Definition ERRNO : Z := 6883756. Definition SBz : Z := 2147450880.
Definition CE := EVar 10. Definition EE := EVar 12. Definition ISE := EVar 32. Definition CHE := EVar 33.
Definition ADDE (a b : expr) : expr := EAlu Instr.ALU_ADD a b.
Definition PE : expr := ADDE CE (ELit 320). Definition VE : expr := ADDE CE (ELit 592).

Definition vBB (i : nat) : nat := match i with 3 => 61 | 4 | 5 => 82 | _ => 34 end%nat.
Definition vBC (i : nat) : nat := (vBB i + 1)%nat.
Definition vSB (i : nat) : nat := (vBB i + 2)%nat.
Definition vSC (i : nat) : nat := (vBB i + 3)%nat.
Definition BLK (i : nat) : list (expr * expr) := [(EVar (vBB i), EVar (vBC i)); (EVar (vSB i), EVar (vSC i)); (CHE, ELit 16384)].
Definition NX (i : nat) : nat := match i with 0 => 42 | 1 => 61 | 2 => 82 | 3 => 88 | _ => 109 end%nat.
Definition CPF0 : list SGP.region := [(EVar 2, -10720, ELit 10720); (CE, 512, ELit 16); (CE, 531, ELit 1); (CE, 640, ELit 1)].
Definition CPF1 : list SGP.region := [(EVar 2, -10720, ELit 10720); (CE, 512, ELit 16)].
Definition CPF3 : list SGP.region := CPF1 ++ [(CE, 640, ELit 1)].
Definition CPF (i : nat) : list SGP.region := if Nat.eqb i 0 then CPF0 else if (i <=? 2)%nat then CPF1 else CPF3.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.

Definition STISH : list kentry := [KImg 1388760 1392480; KWord (SA (ELit 0) 1427896) 8 (ELit SBz); KZero (SA (ELit 0) 2147623346) (ELit 1)].
Definition CKZ (k : Z) : kentry := KZero (SA (CHA.SRL3 (ADDE CE (ELit k))) SBz) (ELit 1).
Definition WREGS_RC : list (expr * Z * expr) :=
  [(CE, 264, ELit 8); (CE, 288, ELit 17); (ISE, 40, ELit 8); (ISE, 152, ELit 4); (EE, 0, ELit 16); (ELit 0, G_GUARD, ELit 2); (ELit 0, AXT, ELit 544)].
Definition NEWS_RC (g : nat) : list kentry :=
  STISH ++ [KWord (SA CE 296) 8 (ELit 0); KWord (SA ISE 40) 8 (EVar (g + 1)); KWord (SA ISE 152) 4 (EVar (g + 2)); KRange (EVar (g + 2)) 0 2; KUnk (SA EE 0) (ELit 16);
            KWord (SA EE 0) 4 (EVar (g + 3)); KRange (EVar (g + 3)) 0 31; KRange (EVar (g + 4)) 20 1099511627775].
Definition WREGS_PS : list (expr * Z * expr) :=
  [(PE, 0, ELit 272); (EE, 0, ELit 16); (ELit 0, G_GUARD, ELit 2); (ELit 0, AXT, ELit 544); (ELit 0, ERRNO, ELit 4); (VE, 8, ELit 40)].
Definition NEWS_PS (g : nat) : list kentry :=
  STISH ++ [KWord (SA CE 512) 8 (EVar (g + 4)); KWord (SA CE 520) 8 (EVar (g + 5)); KWr (SA CE 512) (ELit 16);
            KWord (SA CE 528) 1 (EVar (g + 6)); KRange (EVar (g + 6)) 0 255; KWord (SA CE 531) 1 (EVar (g + 7)); KRange (EVar (g + 7)) 0 1;
            KWord (SA CE 532) 1 (EVar (g + 8)); KRange (EVar (g + 8)) 0 1; KZero (SA (CHA.SRL3 CE) SBz) (ELit 82); CKZ 531; CKZ 532;
            KUnk (SA EE 0) (ELit 16); KWord (SA EE 0) 4 (EVar (g + 9)); KRange (EVar (g + 9)) 0 31; KRange (EVar (g + 10)) 20 1099511627775; KWord (SA CE 640) 1 (ELit 0)].

Fixpoint cell_val (cells : list kentry) (b : expr) (off : Z) (w : nat) : expr :=
  match cells with
  | [] => ELit 0
  | KWord (SA b' o') w' v :: r => if (expr_eqb b' b && Z.eqb o' off && Nat.eqb w' w)%bool then v else cell_val r b off w
  | _ :: r => cell_val r b off w
  end.
Fixpoint reg_val (regs : list (nat * expr)) (r : nat) : expr :=
  match regs with [] => ELit 0 | (r', e) :: rest => if Nat.eqb r' r then e else reg_val rest r end.
Definition DEADR : list (nat * nat) := [(1,43);(5,44);(6,45);(7,46);(10,47);(11,48);(12,49);(13,50);(14,51);(15,52);(16,53);(17,54);(26,55);(28,56);(29,57);(30,58);(31,59)]%nat.

Definition sQ (i : nat) : expr := match i with 0 => ELit 1099511627775 | 3 => EVar 71 | _ => EVar 92 end%nat.
Definition mk_s (i : nat) (ps : SR.post_spec) : CC.subst :=
  let cells := SR.ps_cells ps in let regs := SR.ps_regs ps in
  [(42%nat, sQ i); (34%nat, EVar (vBB i)); (35%nat, EVar (vBC i)); (36%nat, EVar (vSB i)); (37%nat, EVar (vSC i));
   (38%nat, cell_val cells CE 520 8); (39%nat, cell_val cells CE 512 8); (40%nat, cell_val cells ISE 40 8); (41%nat, cell_val cells ISE 152 4);
   (60%nat, cell_val cells EE 0 4)]
  ++ map (fun rv => (snd rv, reg_val regs (fst rv))) DEADR.
Definition MEASX (i : nat) : expr :=
  match i with 0 => ELit 1099511627776 | 1 => EVar 42 | 2 | 3 => ADDE (EVar 42) (ELit (-1)) | _ => ADDE (EVar 42) (ELit (-2)) end%nat.
Definition has := CC.has_cell.

Definition vWB (i : nat) : nat := match i with 3 => 66 | 4 | 5 => 87 | _ => 38 end%nat.
Definition vWE (i : nat) : nat := match i with 3 => 65 | 4 | 5 => 86 | _ => 39 end%nat.
Definition vGP (i : nat) : nat := match i with 2 | 4 | 5 => 62 | _ => 40 end%nat.
Definition vRD (i : nat) : nat := match i with 2 | 4 | 5 => 63 | _ => 41 end%nat.
Definition eCD (i : nat) : expr := match i with 0 => ELit 0 | 1 => EVar 60 | 2 => EVar 64 | 3 => EVar 70 | _ => EVar 91 end%nat.
Definition vCD (i : nat) : nat := match i with 2 => 64 | 3 => 70 | _ => 91 end%nat.
Definition vST (i : nat) : nat := match i with 3 => 67 | _ => 88 end%nat.
Definition vMO (i : nat) : nat := match i with 3 => 68 | _ => 89 end%nat.
Definition vDN (i : nat) : nat := match i with 3 => 69 | _ => 90 end%nat.
Definition vQ (i : nat) : nat := match i with 3 => 71 | _ => 92 end%nat.
Definition SLTU1 (a b : expr) : expr := EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB a b) (ELit 1).
Definition WEQ (i : nat) (v : Z) : kentry := KRange (SLTU1 (EVar (vWB i)) (EVar (vWE i))) v v.
Definition KZ (v : nat) : kentry := KRange (EVar v) 0 0.
Definition K1 (v : nat) : kentry := KRange (EVar v) 1 1.
Definition KGE1 (v : nat) : kentry := KRange (EVar v) 1 18446744073709551615.
Definition KERR (v : nat) : kentry := KRange (EVar v) 1 31.
Definition C640 (b : Z) : kentry := KWord (SA CE 640) 1 (ELit b).
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Definition is_re (i k : nat) : bool :=
  match i, k with 0, 0 | 3, 1 | 4, 1 | 4, 5 | 4, 7 | 5, 1 => true | _, _ => false end%nat.

Definition win_cells (i : nat) (cells : list kentry) : bool :=
  (has cells (KWord (SA CE 512) 8 (EVar (vWE i))) && has cells (KWord (SA CE 520) 8 (EVar (vWB i))))%bool.

Definition link_chk (i : nat) (cells : list kentry) : bool :=
  (expr_eqb (cell_val cells ISE 40 8) (EVar (vGP i)) && expr_eqb (cell_val cells ISE 152 4) (EVar (vRD i)) && expr_eqb (cell_val cells EE 0 4) (eCD i) &&
   expr_eqb (cell_val cells CE 520 8) (EVar (vWB i)) && expr_eqb (cell_val cells CE 512 8) (EVar (vWE i)))%bool.

Definition re_shape (i : nat) (cells : list kentry) : bool :=
  match i with
  | 0 => has cells (KWord (SA CE 531) 1 (ELit 1)) && has cells (C640 0)
  | _ => has cells (K1 (vMO i)) && has cells (KZ (vCD i)) && has cells (C640 0)
  end%nat%bool.

Definition ex_shape (i k : nat) (cells : list kentry) : bool :=
  (win_cells i cells &&
   match i, k with
   | 2, 2 => has cells (KERR 64)
   | 3, 2 | 4, 8 | 5, 2 => has cells (KERR (vCD i)) && has cells (C640 0)
   | 4, 2 => has cells (K1 88) && has cells (KZ 91) && has cells (C640 1)
   | 3, 0 | 4, 0 | 4, 4 | 4, 6 | 5, 0 => has cells (KZ (vMO i)) && has cells (KZ (vCD i)) && has cells (C640 0)
   | _, _ => false
   end)%nat%bool.

Definition tail_shape (cells : list kentry) : bool := (win_cells 4 cells && has cells (KZ 91) && has cells (C640 0))%bool.

Definition call_shape (i j : nat) (cells : list kentry) : bool :=
  match i, j with
  | 1, 2 => has cells (WEQ 1 1)
  | 1, 3 => has cells (WEQ 1 0) && win_cells 1 cells
  | 2, 4 => has cells (KZ 71) && has cells (KZ 64) && win_cells 2 cells
  | 2, 5 => has cells (KGE1 71) && has cells (KZ 64) && has cells (KWord (SA CE 520) 8 (EVar 61)) && has cells (KWord (SA CE 512) 8 (ADDE (EVar 61) (EVar 71)))
  | _, _ => false
  end%nat%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      (CH2.blocks_eqb (nth i G.BLS []) (BLK i) && CHA.foot_chk GT.NF G.HDECL c (BLK i) [] && CBA.regions_eqb (CC.cp_F c) (CPF i) && Nat.eqb (CC.cp_nx c) (NX i) &&
       expr_eqb (CC.cp_meas c) (MEASX i) &&
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (CH2.blocks_eqb (nth j G.BLS []) (BLK j) &&
              if Z.eqb pc PC_RC then
                (Z.eqb (SR.ps_pc ps) PC_RC && Nat.eqb i 1 && Nat.eqb j 2
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 8304 5 (firstn 2 (BLK 1)) [] WREGS_RC (NEWS_RC 61) (Some (EVar 61)) c ps cj (BLK 1) [] (BLK 2) [] with
                    | Some ci => Z.eqb (CH2.ci_csp ci) (-224) && Nat.eqb (CH2.ci_nx ci) 61 | None => false end
                 && CL.ps_reg_is ps 10 (ADDE CE (ELit 8)) && CL.ps_reg_is ps 11 EE && call_shape i j cells)%bool
              else if Z.eqb pc PC_PS then
                (Z.eqb (SR.ps_pc ps) PC_PS && ((Nat.eqb i 1 && Nat.eqb j 3) || (Nat.eqb i 2 && (Nat.eqb j 4 || Nat.eqb j 5)))
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 10496 11 [(CHE, ELit 16384)] [] WREGS_PS (NEWS_PS (NX i)) None c ps cj (BLK i) [] (BLK j) [] with
                    | Some ci => Z.eqb (CH2.ci_csp ci) (-224) && Nat.eqb (CH2.ci_nx ci) (NX i) | None => false end
                 && CL.ps_reg_is ps 10 PE && CL.ps_reg_is ps 11 VE && CL.ps_reg_is ps 12 EE && call_shape i j cells)%bool
              else false)%bool
          | None => false
          end
      | None =>
          if Z.eqb pc RETPC then (CBA.exit_base_chk GT.NF RETPC c ps && Nat.leb 2 i && ex_shape i k cells)%bool
          else if Z.eqb pc LOOPA then
            (is_re i k && Z.eqb (SR.ps_pc ps) pc && link_chk i cells && re_shape i cells && RNA.reentry_chk GT.NF c ps (nth 1 G.CPS G.cp0) (mk_s i ps)
             && CHA.goto_amb_chk GT.NF G.HDECL c (BLK i) (BLK 1) [] [] (mk_s i ps))%bool
          else if Z.eqb pc PC_SETEC then (Nat.eqb i 4 && Nat.eqb k 3 && CRB.tail_base_chk GT.NF PC_SETEC c ps && CL.ps_reg_is ps 10 EE && CL.ps_reg_is ps 11 (ELit 1) && tail_shape cells)%bool
          else false
      end)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End RNXC.
