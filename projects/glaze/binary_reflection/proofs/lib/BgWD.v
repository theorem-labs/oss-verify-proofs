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
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export BgWDT.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition e_x : expr := EExt false 0 8 (EVar 33).
Definition e_exp : expr := EAlu ALU_AND (EAlu ALU_SRL e_x (ELit 52)) (ELit 2047).
Definition e_mant : expr := EAlu ALU_AND e_x (ELit 4503599627370495).
Definition two52 : Z := 2 ^ 52.  Definition two63 : Z := 2 ^ 63.

(* [comment removed for export] *)
Definition P_SPEC : Z := 0xbc324.
Definition P_SH : Z := 0xbc394.     (* [comment removed for export] *)
Definition P_IXB : Z := 0xbc1f8.    (* [comment removed for export] *)
Definition LD1 : Z := 0xbc26c.  Definition LD2 : Z := 0xbc270.      (* [comment removed for export] *)
Definition P_DIA1 : Z := 0xbc400.  Definition J_DIA1 : Z := 0xbc428.  (* [comment removed for export] *)
Definition P_IDIA : Z := 0xbcd74.  Definition J_IDIA : Z := 0xbcd7c.  (* [comment removed for export] *)
Definition P_J : Z := 0xbc450.      (* [comment removed for export] *)
Definition P_T6 : Z := 0xbc564.     (* [comment removed for export] *)
Definition P_POPA : Z := 0xbc65c.  Definition P_POPB : Z := 0xbc6f4.   (* [comment removed for export] *)
Definition P_N : Z := 0xbc748.      (* [comment removed for export] *)
Definition P_IDX : Z := 0xbc798.    (* [comment removed for export] *)
Definition A1 : Z := 0xbc7cc.  Definition A2 : Z := 0xbc918.  Definition A3 : Z := 0xbc934.  Definition A4 : Z := 0xbc9ac.
Definition B1 : Z := 0xbcb80.       (* [comment removed for export] *)
Definition P_SDIA : Z := 0xbce2c.   (* [comment removed for export] *)
Definition P_SUB : Z := 0xbce70.    (* [comment removed for export] *)
Definition P_Q : Z := 0xbcec0.      (* [comment removed for export] *)
Definition M10 : Z := 0x199999999999999a.

Definition X42 (k : AP.plan) : AP.plan := PExt 42 [] k.
Definition X44 (r : Z) (k : AP.plan) : AP.plan := PExt 44 [ELit r] k.
Definition MEMMOVE (k : AP.plan) : AP.plan := PExt ID_AMEMMOVE [] k.
Definition V_T6 : nat := 70.  Definition V_N : nat := 80.

(* [comment removed for export] *)
Definition tail : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PHandoffW 0 []))).
(* [comment removed for export] *)
Fixpoint creg (r : nat) (lo : Z) (n : nat) (k : AP.plan) : AP.plan :=
  match n with O => k | Datatypes.S n' => PCaseReg r lo k (creg r (lo + 1) n' k) end.



(* [comment removed for export] *)
Definition LOJ : nat := 34.
Definition J_E : nat := 55.  Definition J_SIG : nat := 56.  Definition J_HL : nat := 57.  Definition J_SGN : nat := 58.  Definition J_D : nat := 59.  Definition J_Q : nat := 60.
Definition deadJ : list nat := [1; 5; 6; 7; 9; 10; 12; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 28; 29; 30; 31]%nat.   (* [comment removed for export] *)

Definition regsJ : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_havoc regsT deadJ LOJ)
    2 (eadd e_sp (ELit (-96))))
    8 (eadd e_buf (EVar J_SGN)))
    18 (eadd (EVar J_E) (ELit (-340))))
    11 (EVar J_SIG))
    20 (ELit SB))
    19 (EVar J_HL))
    21 (eadd (EVar J_D) (escale (2 ^ 32) (EVar J_Q))).
Definition frameJ : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-72)) 8 (EVar 22);
    KWord (SA e_sp (-80)) 8 (EVar 23); KWord (SA e_sp (-88)) 8 (EVar 24); KWord (SA e_sp (-96)) 8 (EVar 25) ].
Definition SIG15 : Z := 999999999999999.   (* [comment removed for export] *)
Definition knJ (slo shi : Z) : list kentry :=
  [ KRange (EVar J_E) 18 649; KRange (EVar J_SIG) slo shi; KRange (EVar J_HL) 0 1; KRange (EVar J_SGN) 0 1;
    KRange (EVar J_D) 0 10 ]
  ++ frameJ ++ kn_in.
Definition jsJ (slo shi : Z) : acs := mkcs YLO WS e_mtr e_fb P_J regsJ (knJ slo shi) 61.
Definition jsJa : acs := jsJ 0 SIG15.                 (* [comment removed for export] *)
Definition jsJb : acs := jsJ (SIG15 + 1) (2 ^ 64 - 1).



Definition ncls (k : AP.plan) : AP.plan := PCase2 (EVar V_N) 0 k (PCase2 (EVar V_N) 1 k (PCase2 (EVar V_N) 2 k k)).
  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_SHLD : Z := 0xbcab8.   (* [comment removed for export] *)
Definition T1 : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 (PRun [] (MEMMOVE (PRun [A4] (X42 (PRun [] tail)))))))).
Definition T0 : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 (PRun [] (MEMMOVE (ncls (PRun [A4] (X42 (PRun [] tail))))))))).
Definition FIXLD : AP.plan :=
  PRun [P_IDX] (creg 16 0 19 (PRun [A1] (X42 (PRun [] (MEMMOVE (PCaseReg 19 0 (PRespell 19 (ELit 0) T0) (PRespell 19 (ELit 1) T1))))))).
Definition SCILD : AP.plan := PRun [P_SHLD] (PCaseReg 19 0 (ncls (PRun [B1] (X42 (PRun [] tail)))) (PRun [B1] (X42 (PRun [] tail)))).
Definition WRJL (b : Z) : AP.plan := PCase2 (EVar J_E) (b - 1) SCILD (PCase2 (EVar J_E) (b + 19) FIXLD SCILD).
Definition outsJL : AP.plan := PCase2 (EVar J_SIG) 999999999999999 (PRespell 22 (ELit 0) (WRJL 338)) (PRespell 22 (ELit 1) (WRJL 337)).
Definition numtailJ : AP.plan := X44 12 (X44 15 (PBump V_N (PFresh 23 0 None outsJL))).
(* [comment removed for export] *)
Definition lo1J : AP.plan :=
  PRun [0xbc57c] (X44 30 (PRun [0xbc59c] (X44 6 (PRun [0xbc5b4] (X44 13
    (PRun [P_POPA] (X44 15 (PExt 43 [ELit 15] (PRun [P_N] numtailJ))))))))).
Definition lo0J : AP.plan := PRun [P_POPB] (X44 13 (PExt 43 [ELit 13] (PRun [P_N] numtailJ))).
Definition kJ : AP.plan :=
  PRun [0xbc4cc] (X44 10 (PRun [0xbc4e0] (X44 10 (PRun [0xbc4f4] (X44 23
    (PRun [P_T6] (X44 12 (PBump V_T6 (X44 31 (PCase2 (EVar V_T6) 0 lo0J lo1J)))))))))).

(* [comment removed for export] *)
Definition HJ : nat := 13.
Definition MR : AP.plan :=
  PRun [P_J] (X44 11 (PBump 64 (PFresh 21 0 None (PCaseReg 11 SIG15 (PHandoffW HJ [(J_D, EVar 64); (J_Q, ELit 0)]) (PHandoffW (1 + HJ) [(J_D, EVar 64); (J_Q, ELit 0)]))))).
Definition pow10 (stop : Z) (k : AP.plan) : AP.plan :=
  PRun [P_IXB] (PFresh 13 0 None (PRun [LD1; LD2; stop] (X42 (PRun [LD1; LD2; stop] (X42 k))))).
Definition regpre (k : AP.plan) : AP.plan :=
  PRun [P_SH] (X42 (pow10 P_DIA1 (PRun [P_DIA1] (PBranch (PRun [J_DIA1] k) (PRun [J_DIA1] k))))).
Definition irrpre (k : AP.plan) : AP.plan :=
  pow10 P_IDIA (PRun [P_IDIA] (PBranch (PRun [J_IDIA] k) (PRun [J_IDIA] k))).
(* [comment removed for export] *)
Definition armReg : AP.plan :=
  PCase2 e_exp 1008 (regpre MR) (PCase2 e_exp 1011 (regpre MR) (PCase2 e_exp 1074 (regpre MR) (PCase2 e_exp 1078 (regpre MR) (regpre MR)))).
Definition armIrr : AP.plan :=
  PCase2 e_exp 1008 (irrpre MR) (PCase2 e_exp 1012 (irrpre MR) (PCase2 e_exp 1075 (irrpre MR) (PCase2 e_exp 1078 (irrpre MR) (irrpre MR)))).
Definition armInf : AP.plan := PRun [] tail.                       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition V_W : nat := 62.
Definition QW : expr := EMd M_MULHU (EVar V_W) (ELit M10).
Definition subtail : AP.plan :=
  PRun [P_Q] (PBump V_W (PFresh 10 0 None (divfact (EVar V_W) QW 10
    (PRun [P_J] (X44 11 (PCaseReg 11 SIG15 (PHandoffW HJ [(J_D, esub (EVar V_W) (escale 10 QW)); (J_Q, QW)])
                                           (PHandoffW (1 + HJ) [(J_D, esub (EVar V_W) (escale 10 QW)); (J_Q, QW)]))))))).
Fixpoint decs (ts : list Z) : AP.plan :=
  match ts with [] => subtail | t :: r => PCase2 (EVar 48) t subtail (decs r) end.
Definition decades : AP.plan :=
  decs [9; 99; 999; 9999; 99999; 999999; 9999999; 99999999; 999999999; 9999999999; 99999999999; 999999999999;
        9999999999999; 99999999999999; 999999999999999].
Definition subL2 : AP.plan := PRun [P_SUB] (PBump 48 (PFresh 10 0 None decades)).
Definition subLarge : AP.plan :=
  PRun [P_SDIA] (PBump 46 (X44 12 (PCase2 (EVar 46) (2 ^ 62 - 1) subL2 (PCase2 (EVar 46) (2 ^ 62) subL2 subL2)))).
Definition subSmall : AP.plan :=
  PRun [P_SUB] (PExt 45 [ELit 10; e_x] (PBump 48 (PFresh 10 0 None decades))).
Definition armZero : AP.plan := PRun [] tail.

(* [comment removed for export] *)
Definition half (b : Z) (h : nat) : AP.plan :=
  PCase2 e_x b (PHandoffW h [])
  (PCase2 e_x (b + 63) (PHandoffW (1 + h) [])
  (PCase2 e_x (b + two52 - 1) (PHandoffW (2 + h) [])
  (PCase2 e_x (b + 2047 * two52 - 1) (PCase2 e_mant 0 (PHandoffW (3 + h) []) (PHandoffW (4 + h) []))
  (PHandoffW (5 + h) [])))).
(* [comment removed for export] *)
Definition half_g (b : Z) (h : nat) : AP.plan :=
  PCase2 e_x b (PHandoffW h [])
  (PCase2 e_x (b + 63) (PHandoffW (1 + h) [])
  (PCase2 e_x (b + two52 - 1) (PHandoffW 3 [])
  (PCase2 e_x (b + 2047 * two52 - 1) (PCase2 e_mant 0 (PHandoffW 4 []) (PHandoffW 5 []))
  (PHandoffW (5 + h) [])))).
Definition plan_top : AP.plan := PRun [P_SPEC] (PCase2 e_x (two63 - 1) (half 0 1) (half_g two63 7)).

(* [comment removed for export] *)
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XB0.
Definition cutT (steps : list dstep) : acs := snd (dpath BSEGS IT ABOTH (XN IT NXF) XB BFUEL NXF tin (DRun [P_SPEC] :: steps) 0).
Definition steps_half (b : Z) : list (list dstep * AP.plan) :=
  let s0 := if Z.eqb b 0 then [DLo e_x (two63 - 1)] else [DHi e_x (two63 - 1)] in
  [ (s0 ++ [DLo e_x b], armZero);
    (s0 ++ [DHi e_x b; DLo e_x (b + 63)], subSmall);
    (s0 ++ [DHi e_x b; DHi e_x (b + 63); DLo e_x (b + two52 - 1)], subLarge);
    (s0 ++ [DHi e_x b; DHi e_x (b + 63); DHi e_x (b + two52 - 1); DLo e_x (b + 2047 * two52 - 1); DLo e_mant 0], armIrr);
    (s0 ++ [DHi e_x b; DHi e_x (b + 63); DHi e_x (b + two52 - 1); DLo e_x (b + 2047 * two52 - 1); DHi e_mant 0], armReg);
    (s0 ++ [DHi e_x b; DHi e_x (b + 63); DHi e_x (b + two52 - 1); DHi e_x (b + 2047 * two52 - 1)], armInf) ].
Definition CUTS0 : list (acs * AP.plan) := map (fun c => (cutT (fst c), snd c)) (steps_half 0 ++ steps_half two63) ++ [(jsJa, kJ); (jsJb, kJ)].
(* [comment removed for export] *)
Definition is_xr (K : kentry) : bool :=
  match K with KRange e lo hi => (expr_eqb e e_x && negb (Z.eqb lo 0 && Z.eqb hi (2 ^ 64 - 1)))%bool | _ => false end.
Definition gcut (i : nat) (extra : list kentry) : acs * AP.plan :=
  let c := nth i CUTS0 (tin, PContra) in (set_kn (fst c) (extra ++ filter (fun K => negb (is_xr K)) (kn (fst c))), snd c).
Definition deadc : acs * AP.plan := (set_kn tin (KRange (ELit 1) 0 0 :: kn tin), PContraH 0).
Definition CUTS : list (acs * AP.plan) :=
  [ nth 0 CUTS0 (tin, PContra); nth 1 CUTS0 (tin, PContra);
    gcut 2 [KRange e_exp 0 0; KRange e_mant 64 (two52 - 1)]; gcut 3 [KRange e_exp 1 2046]; gcut 4 [KRange e_exp 1 2046; KRange e_mant 1 (two52 - 1)];
    nth 5 CUTS0 (tin, PContra); nth 6 CUTS0 (tin, PContra); nth 7 CUTS0 (tin, PContra); deadc; deadc; deadc; nth 11 CUTS0 (tin, PContra);
    nth 12 CUTS0 (tin, PContra); nth 13 CUTS0 (tin, PContra) ].
Definition NCUTS : nat := 14.
Lemma CUTS_len : length CUTS = NCUTS. Proof. reflexivity. Qed.

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
