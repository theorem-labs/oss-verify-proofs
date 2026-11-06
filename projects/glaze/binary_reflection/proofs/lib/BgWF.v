(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgCommon.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export BgWFT.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition e_lo : expr := EExt false 0 4 (EVar 33).
Definition e_x : expr := EExt true 0 4 e_lo.
Definition e_exp : expr := EAlu ALU_SRL (EMd M_MUL (ELit 8589934592) e_x) (ELit 56).
Definition e_mant : expr := EAlu ALU_SRL (EMd M_MUL (ELit 2199023255552) e_x) (ELit 41).

(* [comment removed for export] *)
Definition P_SPEC : Z := 0xbb3d0.   (* [comment removed for export] *)
Definition LD1 : Z := 0xbc26c.      (* [comment removed for export] *)
Definition LD2 : Z := 0xbc270.      (* [comment removed for export] *)
Definition P_IXB : Z := 0xbc1f8.    (* [comment removed for export] *)
Definition P_DIA1 : Z := 0xbb4c0.

Definition P_SIG : Z := 0xbb4e4.    (* [comment removed for export] *)
Definition P_HL : Z := 0xbb514.     (* [comment removed for export] *)
Definition P_T3 : Z := 0xbb608.     (* [comment removed for export] *)
Definition P_POP : Z := 0xbb640.    (* [comment removed for export] *)
Definition P_NUM : Z := 0xbb69c.    (* [comment removed for export] *)
Definition P_IDX : Z := 0xbb6e4.    (* [comment removed for export] *)
Definition A1 : Z := 0xbb718.  Definition A2 : Z := 0xbb8bc.  Definition A3 : Z := 0xbb8d8.  Definition A4 : Z := 0xbbbcc.
Definition B1 : Z := 0xbbb44.       (* [comment removed for export] *)
Definition P_IDIA : Z := 0xbbd8c.
   (* [comment removed for export] *)
Definition P_RND : Z := 0xbbe20.    (* [comment removed for export] *)
Definition P_SUB : Z := 0xbbe48.    (* [comment removed for export] *)

Definition X42 (k : AP.plan) : AP.plan := PExt 42 [] k.
Definition X44 (r : Z) (k : AP.plan) : AP.plan := PExt 44 [ELit r] k.
Definition V_SIG : nat := 60.
  Definition V_N : nat := 80.

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
Definition P_SIGJ : Z := P_SIG.
Definition HJ : nat := 39.
Definition LOJ : nat := 34.
Definition deadJ : list nat := [1; 5; 7; 11; 12; 13; 14; 16; 18; 19; 21; 22; 23; 28; 29; 30; 31]%nat.   (* [comment removed for export] *)
Definition J_SIG : nat := 51.  Definition J_E : nat := 52.  Definition J_HL : nat := 53.  Definition J_D : nat := 54.
Definition J_Q : nat := 55.  Definition J_SGN : nat := 56.  Definition NXJ : nat := 57.
Definition regsJ : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_havoc regs0 deadJ LOJ)
    2 (eadd e_sp (ELit (-80))))
    6 (EVar J_SIG))
    8 (eadd e_buf (EVar J_SGN)))
    9 (ELit TBL))
    10 (eadd (EVar J_E) (ELit (-400))))
    15 (EVar J_HL))
    17 (eadd (EVar J_D) (escale (2 ^ 32) (EVar J_Q))))
    20 (ELit SB).
Definition frameJ : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-72)) 8 (EVar 22) ].
Definition ELO : Z := 357.  Definition EHI : Z := 440.   (* [comment removed for export] *)
Definition knJ : list kentry :=
  [ KRange (EVar J_SIG) 0 (2 ^ 64 - 1); KRange (EVar J_E) ELO EHI; KRange (EVar J_HL) 0 1; KRange (EVar J_D) 0 10; KRange (EVar J_SGN) 0 1 ]
  ++ frameJ ++ kn_in.
Definition jsJ : acs := mkcs YLO WS e_mtr e_fb P_SIGJ regsJ knJ NXJ.

(* [comment removed for export] *)
Definition ncls (k : AP.plan) : AP.plan := PCase2 (EVar V_N) 0 k (PCase2 (EVar V_N) 1 k (PCase2 (EVar V_N) 2 k k)).
(* [comment removed for export] *)
Definition P_SHL : Z := 0xbba7c.   (* [comment removed for export] *)
Definition TAILF : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 (PRun [A4] (X42 (PRun [] tail)))))).
(* [comment removed for export] *)
Definition FIXL : AP.plan :=
  PRun [P_IDX] (creg 11 0 10 (PRun [A1] (X42 (PCaseReg 15 0 (PRespell 15 (ELit 0) TAILF) (PRespell 15 (ELit 1) TAILF))))).
Definition SCIL : AP.plan := PRun [P_SHL] (PCaseReg 15 0 (ncls (PRun [B1] (X42 (PRun [] tail)))) (PRun [B1] (X42 (PRun [] tail)))).
Definition WRJ (lo : Z) : AP.plan := PCase2 (EVar J_E) (lo - 1) SCIL (PCase2 (EVar J_E) (lo + 10) FIXL SCIL).
Definition OUTJ (lo : Z) : AP.plan :=
  PRun [P_T3] (X44 10 (PRun [P_POP] (X44 11 (PExt 43 [ELit 11] (PRun [P_NUM] (PBump V_N (PFresh 5 0 None (WRJ lo)))))))).
Definition HLJ (lo : Z) : AP.plan := PRun [P_HL] (OUTJ lo).
(* [comment removed for export] *)
Definition S2HL : acs := Eval vm_compute in snd (dpath BSEGS IT ABOTH (XN IT NXF) XB0 BFUEL NXJ jsJ [DHi (EVar J_SIG) 999999; DLo (EVar J_SIG) 9999999; DRun [P_HL]] 0).
Definition SG2 : nat := 57.  Definition JE3 : nat := 58.  Definition HL2 : nat := 59.  Definition LOHL : nat := 57.  Definition NXHL : nat := 61.
Definition is_sc (K : kentry) : bool := match K with KRange (EVar 51) lo _ => negb (Z.eqb lo 0) | _ => false end.
Definition jsHL : acs :=
  mkcs YLO WS e_mtr e_fb P_HL
    (sr_upd (sr_upd (sr_upd (sr_upd (s_regs (a_ss S2HL)) 10 (EVar SG2)) 12 (EVar 60)) 13 (eadd (EVar JE3) (ELit (-402)))) 15 (EVar HL2))
    ([KRange (EVar J_SIG) 0 9999999; KRange (EVar SG2) 0 (2 ^ 64 - 1); KRange (EVar JE3) (ELO - 1) EHI; KRange (EVar HL2) 0 1]
     ++ filter (fun K => negb (is_sc K)) (kn S2HL)) NXHL.
Definition WRJ2 : AP.plan := PCase2 (EVar JE3) (398 - 1) SCIL (PCase2 (EVar JE3) (398 + 10) FIXL SCIL).
Definition OUTJ2 : AP.plan :=
  PRun [P_T3] (X44 10 (PRun [P_POP] (X44 11 (PExt 43 [ELit 11] (PRun [P_NUM] (PBump V_N (PFresh 5 0 None WRJ2))))))).
Definition sig_dt : expr := EAlu ALU_ADD (EMd M_MUL (ELit 10) (EVar J_SIG)) (EAlu ALU_AND (EMd M_MUL (ELit (-1)) (EVar J_HL)) (EVar J_D)).
Definition kJ : AP.plan :=
  PVia 2 jsHL LOHL
    (PCase2 (EVar J_SIG) 999999 (PRun [P_HL] (PMergeW 2 [(SG2, sig_dt); (JE3, eaddz (EVar J_E) (-1)); (HL2, ELit 0)]))
    (PCase2 (EVar J_SIG) 9999999 (PRun [P_HL] (PMergeW 2 [(SG2, EVar J_SIG); (JE3, EVar J_E); (HL2, EVar J_HL)]))
                                 (HLJ 397)))
    OUTJ2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sigH : AP.plan :=
  PRun [P_SIG] (PBump V_SIG (PExt 44 [ELit 6] (PFresh 15 0 None (PFresh 17 0 None
    (PHandoffW HJ [(J_D, EVar (V_SIG + 2)%nat); (J_Q, ELit 0)]))))).
(* [comment removed for export] *)
Definition regH : AP.plan :=
  PRun [P_IXB] (PFresh 13 0 None (PRun [LD1; LD2; P_DIA1] (X42 (PRun [LD1; LD2; P_DIA1] (X42 (PRun [P_DIA1] (PBranch sigH sigH))))))).
(* [comment removed for export] *)
Definition irrH : AP.plan :=
  PRun [P_IXB] (PFresh 13 0 None (PRun [LD1; LD2; P_IDIA] (X42 (PRun [LD1; LD2; P_IDIA] (X42 (PRun [P_IDIA] (PBranch sigH sigH))))))).
(* [comment removed for export] *)
Definition P_Q : Z := 0xbbed0.      (* [comment removed for export] *)
Definition M10 : Z := 0x199999999999999a.   (* [comment removed for export] *)
Definition V_W : nat := 64.  Definition V_HLS : nat := 70.
Definition QW : expr := EMd M_MULHU (EVar V_W) (ELit M10).
Definition subtail : AP.plan :=
  PRun [P_Q] (PBump V_W (PFresh 10 0 None (divfact (EVar V_W) QW 10
    (PRun [P_SIG] (PBump V_HLS (PExt 44 [ELit 6] (PFresh 15 0 None
      (PHandoffW HJ [(J_D, esub (EVar V_W) (escale 10 QW)); (J_Q, QW)])))))))).
Definition decades : AP.plan :=
  PCase2 (EVar V_SIG) 9 subtail (PCase2 (EVar V_SIG) 99 subtail (PCase2 (EVar V_SIG) 999 subtail (PCase2 (EVar V_SIG) 9999 subtail
  (PCase2 (EVar V_SIG) 99999 subtail (PCase2 (EVar V_SIG) 999999 subtail (PCase2 (EVar V_SIG) 9999999 subtail subtail)))))).
Definition subTail (small : bool) : AP.plan :=
  PRun [P_SUB] (if small then PExt 45 [ELit 10; e_lo] (PBump V_SIG (PFresh 10 0 None decades))
                else PBump V_SIG (PFresh 10 0 None decades)).
Definition armSubK (small : bool) : AP.plan := PRun [P_RND] (PBranch (subTail small) (subTail small)).
Definition armZero : AP.plan := PRun [] tail.
Definition armInf : AP.plan := PRun [] tail.

(* [comment removed for export] *)
Definition Hh (i : nat) : AP.plan := PHandoffW i [].
Definition armIrrN (h : nat) : AP.plan :=
  PCase2 e_exp 110 (Hh (4 + h)) (PCase2 e_exp 117 (Hh (5 + h)) (PCase2 e_exp 127 (Hh (6 + h)) (PCase2 e_exp 137 (Hh (7 + h))
  (PCase2 e_exp 147 (Hh (8 + h)) (PCase2 e_exp 153 (Hh (9 + h)) (Hh (10 + h))))))).
Definition armRegN (h : nat) : AP.plan :=
  PCase2 e_exp 110 (Hh (11 + h)) (PCase2 e_exp 116 (Hh (12 + h)) (PCase2 e_exp 126 (Hh (13 + h)) (PCase2 e_exp 136 (Hh (14 + h))
  (PCase2 e_exp 146 (Hh (15 + h)) (PCase2 e_exp 153 (Hh (16 + h)) (Hh (17 + h))))))).
(* [comment removed for export] *)
Definition irrA2 : AP.plan := PCase2 e_exp 113 irrH irrH.
Definition irrC1 : AP.plan := PCase2 e_exp 150 irrH irrH.
Definition regA2 : AP.plan := PCase2 e_exp 113 regH regH.
Definition regC1 : AP.plan := PCase2 e_exp 149 regH regH.
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
Definition cutT (steps : list dstep) : acs := snd (dpath BSEGS IT ABOTH (XN IT NXF) XB BFUEL NXF tin (DRun [P_SPEC] :: steps) 0).
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
      check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh
  | None => True
  end.
Definition cut_ok (i : nat) : bool :=
  match nth_error CUTS i with
  | Some (T, k) => gplan_ok k &&
      match check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k with
      | COk sh => holes_only sh | _ => false end
  | None => true
  end%bool.
Lemma cut_ok_sound : forall i, cut_ok i = true -> cut_stmt i.
Proof.
  intros i H. unfold cut_ok in H. unfold cut_stmt. destruct (nth_error CUTS i) as [[T k]|]; [|exact I].
  destruct (gplan_ok k); [|discriminate].
  destruct (check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k) as [sh|c w cs]; try discriminate.
  exists sh. repeat split; try reflexivity. exact H.
Qed.

Lemma top_gplan : gplan_ok plan_top = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma top : check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUEL None (ce_tin ce) plan_top = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
