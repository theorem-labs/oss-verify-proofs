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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GuCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Record acfg := ACFG {
  c_entry : Z; c_ninstr : nat;
  c_fr : Z;                      (* [comment removed for export] *)
  c_nsaved : nat;                (* [comment removed for export] *)
  c_K : Z;                       (* [comment removed for export] *)
  c_hr : Z;                      (* [comment removed for export] *)
  c_wmx : Z;                     (* [comment removed for export] *)
  c_head : Z; c_join1 : Z; c_ret : Z;
  c_jreg : nat;                  (* [comment removed for export] *)
  c_lits : list (nat * Z);       (* [comment removed for export] *)
  c_mregs : list (nat * expr);   (* [comment removed for export] *)
  c_vw : nat;                    (* [comment removed for export] *)
  c_vhi : Z;                     (* [comment removed for export] *)
  c_ixpc : Z; c_ixreg : nat;     (* [comment removed for export] *)
  c_ix2pc : Z; c_ix2reg : nat    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GUBSAN)).    (* [comment removed for export] *)
Definition C : expr := EVar 9.
Definition T : expr := eaddz C (-8).
Definition G : expr := EVar 31.   Definition OBJ : expr := EVar 32.
Definition INLO : expr := EVar 40.      (* [comment removed for export] *)
Definition ITO : expr := EVar 33.       (* [comment removed for export] *)
Definition IT0 : expr := eadd INLO ITO. (* [comment removed for export] *)
Definition REM : expr := EVar 34. Definition IX : expr := EVar 35.
Definition D : expr := EVar 36.   Definition S : expr := EVar 37.

Definition ERR : expr := EVar 39. Definition NV : expr := EVar 41.
Definition BLEN : expr := eadd ITO REM.  (* [comment removed for export] *)
Definition NXF : nat := 42.
(* [comment removed for export] *)
Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition CAPHI : Z := 4 * IXHI + 8 * INSZ + CAPK.
Definition AHI : Z := CAPHI / 8.
Definition NVHI : Z := 2 ^ 48.              (* [comment removed for export] *)
Definition two62 : Z := 2 ^ 62.
Definition FRK (c : acfg) : Z := c_fr c + 2048.

Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 CAPHI.
Definition strL (c : acfg) (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);                                         (* [comment removed for export] *)
    KDisj (SA d 0) (escale 8 a) (SA C (-8)) (ELit 72); KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 112);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BLEN;
    KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRK c)) (ELit ((FRK c) + WSTK)); img_apart d 0 (escale 8 a) ].
(* [comment removed for export] *)
Definition str (c : acfg) (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL c ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
Definition kn_fixed (c : acfg) : list kentry :=
  [ KRange C (CEIL + 16) HI47; KWord (SA C 0) 8 (eaddz C 56); KWord (SA C 8) 8 (eaddz G 88); KWord (SA C 16) 8 (eaddz G 96);
    KWord (SA C 24) 8 G; KWord (SA C 32) 8 OBJ; KWord (SA C 40) 8 (eaddz G 104); KWord (SA C 56) 8 NV; KRange NV 0 NVHI;
    KWr (SA C (-8)) (ELit 8);
    KRange G CEIL (objhi 112); KWr (SA G 0) (ELit 4); KWr (SA G 96) (ELit 16); KWord (SA G 88) 8 (eadd IT0 REM);
    KRange OBJ CEIL (objhi 24); KWr (SA OBJ 0) (ELit 24); KUnk (SA OBJ 0) (ELit 24);
    KRange INLO PTRLO PTRHI; KRange ITO 1 INSZ; KRange REM 0 REMHI; KRange BLEN 1 INSZ;
    KUnk (SA INLO 0) BLEN; KDisj (SA INLO 0) BLEN (SA e_sp (- FRK c)) (ELit ((FRK c) + WSTK)); img_apart INLO 0 BLEN; KRange (eadd INLO BLEN) (PTRLO + 1) PTRHI;
    KDisj (SA C (-8)) (ELit 72) (SA G 0) (ELit 112); KDisj (SA C (-8)) (ELit 72) (SA OBJ 0) (ELit 24);
    KDisj (SA G 0) (ELit 112) (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BLEN (SA C (-8)) (ELit 72); KDisj (SA INLO 0) BLEN (SA G 0) (ELit 112); KDisj (SA INLO 0) BLEN (SA OBJ 0) (ELit 24);
    KAlign e_sp 16; KRange e_sp (CEIL + 8192) HI47; KWr (SA e_sp (- FRK c)) (ELit (FRK c));
    KRange (esub C e_sp) 16 (2 ^ 62); KRange (esub G e_sp) 0 (2 ^ 62); KRange (esub OBJ e_sp) 0 (2 ^ 62);   (* [comment removed for export] *)
    KDisj (SA e_sp (- FRK c)) (ELit (FRK c)) (SA C (-8)) (ELit 72); KDisj (SA e_sp (- FRK c)) (ELit (FRK c)) (SA G 0) (ELit 112);
    KDisj (SA e_sp (- FRK c)) (ELit (FRK c)) (SA OBJ 0) (ELit 24);
    KAlign G 8; KAlign OBJ 8;                                          (* [comment removed for export] *)
    KWr (SA C (-8)) (ELit 72); KWr (SA G 0) (ELit 112);    (* [comment removed for export] *)
    KImg 0x10000 0x75000 ].
Definition kn_in (c : acfg) (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA G 96) 8 IT0; KWord (SA G 104) 8 IX; KRange IX 0 BIG;
    KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG ]
  ++ str c m IX IT0 36 ++ kn_fixed c.
Definition WS : list (expr * expr) := [(T, ELit 8); (G, ELit 4); (eaddz G 96, ELit 16); (OBJ, ELit 24); (INLO, BLEN)].
Definition mkcsV (c : acfg) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 (FRK c) 0 vis WS 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition regs_in : list expr := sr_upd regsW 11 T.
Definition tin (c : acfg) (m : smode) : acs := mkcsV c (c_entry c) regs_in (kn_in c m) NXF (vis m 36).
Definition IT (c : acfg) : itab := mk_itab_ranges USEGS [(c_entry c, c_ninstr c)].
Lemma IT_ok : forall c, itab_sound USEGS (IT c). Proof. intro. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition saved_reg (k : nat) : nat := match k with O => 1 | 1 => 8 | 2 => 9 | _ => (k + 15) end%nat.
Fixpoint frame_go (k n : nat) : list kentry :=
  match n with O => [] | Datatypes.S n' => KWord (SA e_sp (- (8 * (Z.of_nat k + 1)))) 8 (EVar (saved_reg k - 1)%nat) :: frame_go (Datatypes.S k) n' end.
Definition frame (c : acfg) : list kentry := frame_go 0 (c_nsaved c).
(* [comment removed for export] *)
Fixpoint saved_upto (i k n : nat) : bool :=
  match n with O => false | Datatypes.S n' => (Nat.eqb (saved_reg k) i || saved_upto i (Datatypes.S k) n')%bool end.
Definition callee_saved (i : nat) : bool := (Nat.eqb i 8 || Nat.eqb i 9 || (Nat.leb 18 i && Nat.leb i 27))%bool.
Fixpoint assocn {X : Type} (l : list (nat * X)) (i : nat) : option X :=
  match l with [] => None | (j, x) :: r => if Nat.eqb i j then Some x else assocn r i end.

(* [comment removed for export] *)
Definition fixed_loop (c : acfg) (J : expr) (extra : list (nat * expr)) (i : nat) : option expr :=
  if Nat.eqb i 0 then Some (ELit 0)
  else if Nat.eqb i 2 then Some (eaddz e_sp (- c_fr c))
  else if Nat.eqb i 3 then Some (EVar 2)
  else if Nat.eqb i 4 then Some (ELit (g_tp GUBSAN))
  else match assocn (c_lits c) i with Some z => Some (ELit z) | None =>
       match assocn extra i with Some e => Some e | None =>
       if Nat.eqb i 8 then Some C else if Nat.eqb i 9 then Some T else if Nat.eqb i (c_jreg c) then Some J
       else if (callee_saved i && negb (saved_upto i 0 (c_nsaved c)))%bool then Some (EVar (i - 1)%nat) else None
       end end.
Fixpoint build_regs (fixed : nat -> option expr) (i n v : nat) : list expr :=
  match n with
  | O => []
  | Datatypes.S n' => match fixed i with
                      | Some e => e :: build_regs fixed (Datatypes.S i) n' v
                      | None => EVar v :: build_regs fixed (Datatypes.S i) n' (Datatypes.S v)
                      end
  end.
Fixpoint count_slots (fixed : nat -> option expr) (i n : nat) : nat :=
  match n with
  | O => O
  | Datatypes.S n' => match fixed i with Some _ => count_slots fixed (Datatypes.S i) n' | None => Datatypes.S (count_slots fixed (Datatypes.S i) n') end
  end.

(* [comment removed for export] *)
Definition xERR := EVar 42. Definition xDI := EVar 43. Definition xIX := EVar 44.
 Definition xS := EVar 46.

Definition XLO : nat := 48.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition kn_out (c : acfg) (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 22; KWord (SA G 96) 8 (eadd IT0 xDI); KRange xDI 0 REMHI; KRange (esub REM xDI) 0 REMHI;
    KWord (SA G 104) 8 xIX; KRange xIX 0 IXHI; KRange (esub xIX IX) 0 two62;
    KRange (esub (escale 24 (esub (eadd IT0 xDI) INLO)) xIX) 0 BIG;
    KRange (esub (eadd IT0 xDI) INLO) 0 INSZ;
    relx xDI xERR xIX IX 0 ]                                                            (* [comment removed for export] *)
  ++ str c m xIX (eadd IT0 xDI) 45 ++ kn_fixed c.
Definition tout (c : acfg) (m : smode) : acs := mkcsV c (c_ret c) regs_out (kn_out c m) (XLO + 15)%nat (vis m 45).
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
(* [comment removed for export] *)
Definition ce2 (c : acfg) (m : smode) : gcallee2 := GCE2 NXF (tin c m) [tout c MS] [tout c ML] BCAP CCAP.
Definition ce (c : acfg) (m : smode) : gcallee := c2_merged (ce2 c m).
(* [comment removed for export] *)
Definition ceL1 (c : acfg) : gcallee := GCE NXF (tin c ML) [tout c ML; tout c ML] BCAP CCAP.

(* [comment removed for export] *)
Definition JV : nat := 70.
Definition J : expr := EVar JV.
Definition IXv := EVar 71. Definition Dv := EVar 72. Definition Sv := EVar 73. Definition Av := EVar 74.
Definition itK (c : acfg) (j : expr) : expr := eadd IT0 (escale (c_K c) j).       (* [comment removed for export] *)
Definition remK (c : acfg) (j : expr) : expr := esub REM (escale (c_K c) j).     (* [comment removed for export] *)
Definition relJe (c : acfg) (j ix : expr) : expr := esub (escale (24 * c_K c) j) (esub ix IX).
Definition relJ (c : acfg) (j ix : expr) (lo : Z) : kentry := KRange (relJe c j ix) lo BIG.
Definition kn_loop (c : acfg) (m : smode) (ix : expr) (v : nat) : list kentry :=
  frame c ++
  [ KRange NV 1 NVHI; KRange (esub NV J) 1 NVHI; KWord (SA G 96) 8 (itK c J); KRange (remK c J) 0 REMHI;
    KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA G 104) 8 ix; KRange ix 0 IXHI; KRange IX 0 BIG; KRange (esub ix IX) 0 two62;
    KRange (esub (escale 24 (esub (itK c J) INLO)) ix) 0 BIG; KRange (esub (itK c J) INLO) 0 INSZ;
    relJ c J ix 0 ]                                                                     (* [comment removed for export] *)
  ++ str c m ix (itK c J) v ++ kn_fixed c.
Definition INV (c : acfg) (m : smode) : acs :=
  let fx := fixed_loop c J [] in
  mkcsV c (c_head c) (build_regs fx 0 32 75) (kn_loop c m IXv 72) (75 + count_slots fx 0 32)%nat (vis m 72).

(* [comment removed for export] *)
Definition LO1 : nat := 130.                 (* [comment removed for export] *)
Definition D1 := EVar 130. Definition S1 := EVar 131. Definition A1 := EVar 132. Definition VAL := EVar 133.
(* [comment removed for export] *)
Definition room (c : acfg) (m : smode) : list kentry :=
  match m with MS => [KRange (esub (EVar 130) IXv) (c_hr c) (2 ^ 40)] | ML => [KRange (esub S1 IXv) (c_hr c) (2 ^ 37)] end.
Definition kn_js1 (c : acfg) (m : smode) : list kentry :=
  room c m ++ [ KRange J 0 (NVHI - 1); KRange (remK c J) (c_K c) REMHI ]
  ++ (match c_vw c with O => [] | w => [KWord (SA C (-8)) w VAL] end)
  ++ (if Z.eqb (c_vhi c) 0 then [] else [KRange VAL 0 (c_vhi c)])
  ++ kn_loop c m IXv 130.
Definition JS1 (c : acfg) (m : smode) : acs :=
  let fx := fixed_loop c J (c_mregs c) in
  mkcsV c (c_join1 c) (build_regs fx 0 32 134) (kn_js1 c m) (134 + count_slots fx 0 32)%nat (vis m 130).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PH : nat := 255.
Definition XPH : expr := EVar PH.
Definition CAPBJ (c : acfg) : expr := eaddz (eadd (escale 4 IXv) (escale 8 (esub (itK c J) INLO))) CAPK.
(* [comment removed for export] *)
Definition RSZ (c : acfg) (m : smode) : list expr := match m with MS => [ELit 0; Dv; CAPBJ c] | ML => [ELit 1; Dv; Av; Sv; CAPBJ c] end.

(* [comment removed for export] *)
Definition capA (m : smode) (r : nat) (itn cons' : expr) (k : plan) : plan :=
  match m with ML => PFactLeX r PH (capexpr XPH itn INLO A1) (eaddz (escale 104 cons') CAPK) CAPHI k | MS => k end.
Definition chainA (c : acfg) (m : smode) (r : nat) (k : plan) : plan :=
  let itn := itK c (eaddz J 1) in let cons' := esub itn INLO in
  PFactLe cons' (eadd (esub IT0 INLO) REM) INSZ
  (PFactLe (escale (c_K c) (eaddz J 1)) REM REMHI
  (PFactLeX r PH XPH (escale 24 cons') IXHI
  (PFactLeX r PH (esub (escale 24 cons') XPH) (escale 24 cons') BIG
  (PFactLeX r PH (esub XPH IX) XPH two62
  (PFactX r PH (relJe c (eaddz J 1) XPH) 1 BIG                  (* [comment removed for export] *)
  (capA m r itn cons' k)))))).
(* [comment removed for export] *)
Definition chainB (c : acfg) (m : smode) (r : nat) (k : plan) : plan :=
  let itn := itK c (eaddz J 1) in let cons' := esub itn INLO in
  PFactLe (remK c (eaddz J 1)) (remK c J) REMHI
  (PFactLeX r PH XPH (escale 24 cons') IXHI
  (PFactLeX r PH (esub (escale 24 cons') XPH) (escale 24 cons') BIG
  (PFactLeX r PH (esub XPH IX) XPH two62
  (PFactX r PH (relJe c (eaddz J 1) XPH) 0 BIG                  (* [comment removed for export] *)
  (capA m r itn cons' k))))).

Definition EXIT0 (m : smode) : plan := PRun [] (PHandoffW (hole m) [(43%nat, ELit 0)]).                   (* [comment removed for export] *)
Definition errJ (c : acfg) (m : smode) : plan :=                                                         (* [comment removed for export] *)
  PRun [] (PFactLe (escale (c_K c) J) REM REMHI (PHandoffW (hole m) [(43%nat, escale (c_K c) J)])).
Definition after_elem (c : acfg) (m : smode) : plan :=
  chainA c m (c_ixreg c)
    (PCase2 (esub NV J) 1
       (PRun [] (PHandoffW (hole m) [(43%nat, escale (c_K c) (eaddz J 1))]))                           (* [comment removed for export] *)
       (PRun [c_ix2pc c] (chainB c m (c_ix2reg c) (PRun [c_head c] PNext)))).                           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition after1 (c : acfg) (elem : smode -> plan -> plan) (m : smode) : plan :=
  match m with
  | ML => PFactVia (esub (escale 8 A1) IXv) (esub S1 IXv) (c_hr c + 1) (2 ^ 40) (elem ML (after_elem c ML))
  | MS => elem MS (after_elem c MS)
  end.                                                                (* [comment removed for export] *)
(* [comment removed for export] *)
Definition diamondL (c : acfg) : plan :=
  PBranch (PRun [c_join1 c] (PMerge 1))
          (PRun [] (PExt2 31 (RSZ c ML) (PRun [c_join1 c] (PMerge 1)) (PRun [c_join1 c] (PMerge 1)))).
Definition diamondS (c : acfg) : plan :=
  if Z.leb 23 (c_hr c) then PExt2 31 (RSZ c MS) (PContraH 0) (PRun [c_join1 c] (PMerge 1))
  else PBranch (PRun [c_join1 c] (PMerge 1))
               (PRun [] (PExt2 31 (RSZ c MS) (if Z.leb 12 (c_hr c) then PContraH 0 else PRun [c_join1 c] (PMerge 1))
                                             (PRun [c_join1 c] (PMerge 1)))).
Definition alts1 (c : acfg) (elem : smode -> plan -> plan) (m : smode) : list (acs * plan) :=
  match m with
  | ML => [(JS1 c ML, after1 c elem ML)]
  | MS => if Z.leb 23 (c_hr c) then [(JS1 c ML, after1 c elem ML)] else [(JS1 c MS, after1 c elem MS); (JS1 c ML, after1 c elem ML)]
  end.
Definition body (c : acfg) (elem : smode -> plan -> plan) (m : smode) : plan :=
  PCase2 (remK c J) (c_K c - 1) (errJ c m)
    (PRun [] (PViaM 1 (alts1 c elem m) LO1 (match m with ML => diamondL c | MS => diamondS c end))).

Definition SHAPE : shape := SHole 0.

(* [comment removed for export] *)
Definition CT2_0 (id : nat) : option gcallee2 := None.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc USEGS AUBSAN NXF GUBSAN BCAP CCAP CT2_0.
Definition FUELA : nat := 4000.
