(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GaWFT.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition e_lo : expr := EExt false 0 4 (EVar 33).
Definition e_x : expr := EExt true 0 4 e_lo.
Definition e_exp : expr := EAlu ALU_SRL (EMd M_MUL (ELit 8589934592) e_x) (ELit 56).
Definition e_mant : expr := EAlu ALU_SRL (EMd M_MUL (ELit 2199023255552) e_x) (ELit 41).

(* [comment removed for export] *)
Definition P_SPEC : Z := 0xb6e6c.   (* [comment removed for export] *)
Definition P_LD1 : Z := 0xb6ec4.    (* [comment removed for export] *)
Definition P_DIA1 : Z := 0xb6f3c.   (* [comment removed for export] *)
Definition J_DIA1 : Z := 0xb6f4c.
Definition P_SIG : Z := 0xb6f58.    (* [comment removed for export] *)
Definition P_HL : Z := 0xb6f80.     (* [comment removed for export] *)
Definition P_T3 : Z := 0xb7074.     (* [comment removed for export] *)
Definition P_POP : Z := 0xb70ac.    (* [comment removed for export] *)
Definition P_NUM : Z := 0xb7108.    (* [comment removed for export] *)
Definition P_IDX : Z := 0xb715c.    (* [comment removed for export] *)
Definition A1 : Z := 0xb717c.  Definition A2 : Z := 0xb73e0.  Definition A3 : Z := 0xb73e8.  Definition A4 : Z := 0xb7504.
Definition B1 : Z := 0xb735c.       (* [comment removed for export] *)
Definition P_ILD1 : Z := 0xb7608.  Definition P_ILD2 : Z := 0xb760c.
Definition P_IX1 : Z := 0xb6ea4.    (* [comment removed for export] *)
Definition P_IIX1 : Z := 0xb75d0.  Definition P_IIX2 : Z := 0xb75ec.   (* [comment removed for export] *)
Definition P_IDIA : Z := 0xb76a8.  Definition J_IDIA : Z := 0xb76b0.   (* [comment removed for export] *)
Definition P_RND : Z := 0xb7734.    (* [comment removed for export] *)
Definition P_SUB : Z := 0xb7764.    (* [comment removed for export] *)

Definition X42 (k : AP.plan) : AP.plan := PExt 42 [] k.
Definition X44 (r : Z) (k : AP.plan) : AP.plan := PExt 44 [ELit r] k.
Definition V_SIG : nat := 60.  Definition V_HL : nat := 61.  Definition V_N : nat := 80.

(* [comment removed for export] *)
Definition tail : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PHandoffW 0 []))).
(* [comment removed for export] *)
Fixpoint creg (r : nat) (lo : Z) (n : nat) (k : AP.plan) : AP.plan :=
  match n with O => k | Datatypes.S n' => PCaseReg r lo k (creg r (lo + 1) n' k) end.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HJ : nat := 39.
Definition LOJ : nat := 34.
Definition deadJ : list nat := [1; 5; 6; 9; 10; 11; 12; 14; 19; 20; 22]%nat.   (* [comment removed for export] *)
Definition J_E : nat := 50.  Definition J_HL : nat := 51.  Definition J_EF : nat := 52.  Definition J_SGN : nat := 53.  Definition NXJ : nat := 54.
Definition regsJ : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_havoc regs0 deadJ LOJ)
    2 (eadd e_sp (ELit (-64))))
    8 (eadd e_buf (EVar J_SGN)))
    13 (eadd (EVar J_E) (ELit (-400))))
    15 (EVar J_HL))
    16 (EVar J_EF))
    17 (EVar J_EF))
    18 (ELit SB))
    21 (ELit 0x22d40).
Definition frameJ : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21) ].
Definition ELO : Z := 355.  Definition EHI : Z := 439.   (* [comment removed for export] *)
Definition knJ : list kentry :=
  [ KRange (EVar J_E) ELO EHI; KRange (EVar J_HL) 0 1; KRange (EVar J_EF) 0 1; KRange (EVar J_SGN) 0 1 ] ++ frameJ ++ kn_in.
Definition jsJ : acs := mkcs YLO WS e_mtr e_fb P_HL regsJ knJ NXJ.

(* [comment removed for export] *)
Definition ESPL (k : AP.plan) : AP.plan :=
  PCaseReg 17 0 (PRespell 17 (ELit 0) (PRespell 16 (ELit 0) k)) (PRespell 17 (ELit 1) (PRespell 16 (ELit 1) k)).
Definition TAILF : AP.plan := PRun [A4] (X42 (PRun [] tail)).
Definition FIXL : AP.plan :=
  PRun [P_IDX] (creg 11 0 10 (PRun [A1] (X42 (PRun [0xb71d4] (ESPL
    (PRun [0xb7250] (PDiamond 0xb73a4 [13%nat]
      (PRun [A2] (X42 (PRun [A3] (X42 (PRun [0xb74d8] (PCaseReg 15 0 (PRun [0xb74dc] (PCase2 (EVar V_N) 0 TAILF TAILF)) TAILF))))))))))))).
Definition SCI0 : AP.plan := PRun [B1] (X42 (PRun [] tail)).
Definition SCIL : AP.plan := ESPL (PRun [0xb72dc] (PCaseReg 15 0 (PRun [0xb72e4] (PCase2 (EVar V_N) 0 SCI0 SCI0)) SCI0)).
Definition WRJL : AP.plan := PCase2 (EVar J_E) 395 SCIL (PCase2 (EVar J_E) 406 FIXL SCIL).
Definition kJ : AP.plan :=
  PRun [P_T3] (X44 10 (PRun [P_POP] (X44 11 (PExt 43 [ELit 11] (PRun [P_NUM] (PBump V_N (PFresh 6 0 None WRJL))))))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hlH : AP.plan := PRun [P_HL] (PBump V_HL (PFresh 15 0 None (PHandoffW HJ []))).
(* [comment removed for export] *)
Definition sigH : AP.plan :=
  PRun [P_SIG] (PBump V_SIG (PExt 44 [ELit 11] (PCase2 (EVar V_SIG) 999999 hlH (PCase2 (EVar V_SIG) 9999999 hlH hlH)))).
(* [comment removed for export] *)
Definition regH : AP.plan :=
  PRun [P_IX1] (PFresh 11 0 None (PRun [P_LD1] (X42 (PRun [P_DIA1] (PDiamond J_DIA1 [5; 15]%nat sigH))))).
(* [comment removed for export] *)
Definition irrH : AP.plan :=
  PRun [P_IIX1] (PFresh 11 0 None (PRun [P_IIX2] (PFresh 12 0 None
    (PRun [P_ILD1] (X42 (PRun [P_ILD2] (X42 (PRun [P_IDIA] (PDiamond J_IDIA [5]%nat sigH))))))))).
(* [comment removed for export] *)
Definition decades : AP.plan :=
  PCase2 (EVar V_SIG) 9 hlH (PCase2 (EVar V_SIG) 99 hlH (PCase2 (EVar V_SIG) 999 hlH (PCase2 (EVar V_SIG) 9999 hlH
  (PCase2 (EVar V_SIG) 99999 hlH (PCase2 (EVar V_SIG) 999999 hlH (PCase2 (EVar V_SIG) 9999999 hlH hlH)))))).
Definition subTail (small : bool) : AP.plan :=
  PRun [P_SUB] (if small then PExt 45 [ELit 10; e_lo] (PBump V_SIG (PFresh 10 0 None decades))
                else PBump V_SIG (PFresh 10 0 None decades)).
Definition armSubK (small : bool) : AP.plan := PRun [P_RND] (PBranch (subTail small) (subTail small)).
Definition armZero : AP.plan := PRun [] tail.
Definition armInf : AP.plan := PRun [] tail.

(* [comment removed for export] *)
Definition Hh (i : nat) : AP.plan := PHandoffW i [].
Definition irrA2 : AP.plan := PCase2 e_exp 113 irrH irrH.
Definition irrC1 : AP.plan := PCase2 e_exp 150 irrH irrH.
Definition regA2 : AP.plan := PCase2 e_exp 113 regH regH.
Definition regC1 : AP.plan := PCase2 e_exp 149 regH regH.
Definition armIrrN (h : nat) : AP.plan :=
  PCase2 e_exp 110 (Hh (4 + h)) (PCase2 e_exp 117 (Hh (5 + h)) (PCase2 e_exp 127 (Hh (6 + h)) (PCase2 e_exp 137 (Hh (7 + h))
  (PCase2 e_exp 147 (Hh (8 + h)) (PCase2 e_exp 153 (Hh (9 + h)) (Hh (10 + h))))))).
Definition armRegN (h : nat) : AP.plan :=
  PCase2 e_exp 110 (Hh (11 + h)) (PCase2 e_exp 116 (Hh (12 + h)) (PCase2 e_exp 126 (Hh (13 + h)) (PCase2 e_exp 136 (Hh (14 + h))
  (PCase2 e_exp 146 (Hh (15 + h)) (PCase2 e_exp 153 (Hh (16 + h)) (Hh (17 + h))))))).
(* [comment removed for export] *)
Definition armSubBig (h : nat) : AP.plan := PRun [P_RND] (PBranch (Hh (2 + h)) (Hh (3 + h))).

(* [comment removed for export] *)
Definition half (b : Z) (h : nat) : AP.plan :=
  PCase2 e_lo b (Hh h)
  (PCase2 e_lo (b + 7) (Hh (1 + h))
  (PCase2 e_lo (b + 2^23 - 1) (armSubBig h)
  (PCase2 e_lo (b + 255 * 2^23 - 1) (PCase2 e_mant 0 (armIrrN h) (armRegN h))
  (Hh (18 + h))))).
Definition NHALF : nat := 19.
Definition plan_top : AP.plan := PRun [P_SPEC] (PCase2 e_lo (2^31 - 1) (half 0 1) (half (2^31) (1 + NHALF))).

(* [comment removed for export] *)
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XB0.
Definition cutT (steps : list dstep) : acs := snd (dpath ASEGS IT AASAN (XN IT NXF) XB BFUEL NXF tin (DRun [P_SPEC] :: steps) 0).
Definition NEGB : Z := 2^31.
Definition steps_half (b : Z) : list (list dstep * AP.plan) :=
  let s0 := if Z.eqb b 0 then [DLo e_lo (2^31 - 1)] else [DHi e_lo (2^31 - 1)] in
  let nrm := s0 ++ [DHi e_lo b; DHi e_lo (b + 7); DHi e_lo (b + 2^23 - 1); DLo e_lo (b + 255 * 2^23 - 1)] in
  let irrm := nrm ++ [DLo e_mant 0] in let regm := nrm ++ [DHi e_mant 0] in
  [ (s0 ++ [DLo e_lo b], armZero);
    (s0 ++ [DHi e_lo b; DLo e_lo (b + 7)], armSubK true);
    (s0 ++ [DHi e_lo b; DHi e_lo (b + 7); DLo e_lo (b + 2^23 - 1); DRun [P_RND]; DBrF], subTail false);
    (s0 ++ [DHi e_lo b; DHi e_lo (b + 7); DLo e_lo (b + 2^23 - 1); DRun [P_RND]; DBrT], subTail false);
    (irrm ++ [DLo e_exp 110], irrH);
    (irrm ++ [DHi e_exp 110; DLo e_exp 117], irrA2);
    (irrm ++ [DHi e_exp 117; DLo e_exp 127], irrH);
    (irrm ++ [DHi e_exp 127; DLo e_exp 137], irrH);
    (irrm ++ [DHi e_exp 137; DLo e_exp 147], irrH);
    (irrm ++ [DHi e_exp 147; DLo e_exp 153], irrC1);
    (irrm ++ [DHi e_exp 153], irrH);
    (regm ++ [DLo e_exp 110], regH);
    (regm ++ [DHi e_exp 110; DLo e_exp 116], regA2);
    (regm ++ [DHi e_exp 116; DLo e_exp 126], regH);
    (regm ++ [DHi e_exp 126; DLo e_exp 136], regH);
    (regm ++ [DHi e_exp 136; DLo e_exp 146], regH);
    (regm ++ [DHi e_exp 146; DLo e_exp 153], regC1);
    (regm ++ [DHi e_exp 153], regH);
    (s0 ++ [DHi e_lo b; DHi e_lo (b + 7); DHi e_lo (b + 2^23 - 1); DHi e_lo (b + 255 * 2^23 - 1)], armInf) ].
Definition CUTSPEC : list (list dstep * AP.plan) := steps_half 0 ++ steps_half NEGB.
Definition CUTS : list (acs * AP.plan) := map (fun c => (cutT (fst c), snd c)) CUTSPEC ++ [(jsJ, kJ)].
Definition NCUTS : nat := 39.
Lemma CUTS_len : length CUTS = NCUTS. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cut_stmt (i : nat) : Prop :=
  match nth_error CUTS i with
  | Some (T, k) => exists sh, gplan_ok k = true /\ holes_only sh = true /\
      check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh
  | None => True
  end.
Definition cut_ok (i : nat) : bool :=
  match nth_error CUTS i with
  | Some (T, k) => gplan_ok k &&
      match check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k with
      | COk sh => holes_only sh | _ => false end
  | None => true
  end%bool.
Lemma cut_ok_sound : forall i, cut_ok i = true -> cut_stmt i.
Proof.
  intros i H. unfold cut_ok in H. unfold cut_stmt. destruct (nth_error CUTS i) as [[T k]|]; [|exact I].
  destruct (gplan_ok k); [|discriminate].
  destruct (check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k) as [sh|c w cs]; try discriminate.
  exists sh. repeat split; try reflexivity. exact H.
Qed.

Lemma top_gplan : gplan_ok plan_top = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma top : check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUEL None (ce_tin ce) plan_top = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
