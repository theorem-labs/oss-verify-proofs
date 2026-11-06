(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaStep.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Inductive xstep : Type := XD (d : dstep) | XFresh (r : nat) (logc : Z) (base : option expr) | XRespell (r : nat) (e : expr) | XBump (n : nat)
| XC (id : nat) (pre : list expr) | XCa (id : nat) (pre : list expr) | XCb (id : nat) (pre : list expr) | XFact (K : kentry).
Section S.
Variable IT : itab. Variable NXF : nat.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Definition xgo (cs : acs) (st : xstep) : option acs :=
  match st with
  | XD d => dgo ASEGS IT AASAN XN XB BFUEL NXF cs d
  | XFresh r logc base => node_fresh NXF cs r logc base
  | XRespell r e => node_respell cs r e
  | XBump n => node_bump cs n
  | XC id pre => XN id (pre ++ [a_meter cs; a_fbud cs]) cs
  | XCa id pre => match XB id (pre ++ [a_meter cs; a_fbud cs]) cs with Some (a, _) => Some a | None => None end
  | XCb id pre => match XB id (pre ++ [a_meter cs; a_fbud cs]) cs with Some (_, b) => Some b | None => None end
  | XFact K => if fact_ok (kn cs) K then Some (add_kn cs [K]) else None
  end.
Fixpoint xpath (cs : acs) (l : list xstep) (n : nat) : nat * acs :=
  match l with [] => (n, cs) | st :: r => match xgo cs st with Some cs' => xpath cs' r (S n) | None => (n, cs) end end.
End S.
Definition R (s : list Z) := XD (DRun s).
Definition X (id : nat) (args : list expr) := XD (DExt id args).
End GaStep.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaStrCtor.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0x9e544.
Definition RETPC : Z := 0x9e668.
Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, 88%nat)].
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 33.
Definition e_p := e_a0.
Definition e_mtr : expr := EVar 31.  Definition e_fb : expr := EVar 32.
Definition HELLO : Z := g_hello GASAN.
Definition HLEN : Z := 11.
(* [comment removed for export] *)
Definition regsT : list expr := sr_upd (sr_upd regs0 11 (ELit HELLO)) 4 (ELit (g_tp GASAN)).
(* [comment removed for export] *)
Definition FR : Z := 2368.
Definition YLO : Z := FR.         (* [comment removed for export] *)
Definition WS : list (expr * expr) := [(e_p, ELit 24)].
(* [comment removed for export] *)
Definition kn_x : list kentry :=
  [ KRange e_p PTRLO (objhi 24); KWr (SA e_p 0) (ELit 24); KAlign e_p 8; KShOk (SA e_p 0) (ELit 24);
    KWr (SA e_sp (- FR)) (ELit FR); KDisj (SA e_p 0) (ELit 24) (SA e_sp (- FR)) (ELit FR) ]
  ++ [ KIMGA ] ++ RTC
  ++ [ KShOk (SA (ELit HELLO) 0) (ELit (HLEN + 1)) ]
  ++ [img_apart e_p 0 (ELit 24); shmap_apart e_p 0 (ELit 24)].
Definition kn_in : list kentry :=
  [ KRange e_p PTRLO (objhi 24); KWr (SA e_p 0) (ELit 24); KAlign e_p 8; KShOk (SA e_p 0) (ELit 24);
    KWr (SA e_sp (- FR)) (ELit FR); KDisj (SA e_p 0) (ELit 24) (SA e_sp (- FR)) (ELit FR) ]
  ++ sp_facts YLO ++ [ KIMGA ] ++ RTC
  ++ [ KShOk (SA (ELit HELLO) 0) (ELit (HLEN + 1)) ]
  ++ [img_apart e_p 0 (ELit 24); shmap_apart e_p 0 (ELit 24)].   (* [comment removed for export] *)     (* [comment removed for export] *)
Definition tin : acs := mkcs YLO WS e_mtr e_fb ENTRY regsT kn_in NXF.

(* [comment removed for export] *)
Definition LO : nat := 33.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition x_regs : list expr := sr_havoc regsT clobbered LO.
Definition kn_out : list kentry := [KWord (SA e_p 0) 1 (ELit (2 * HLEN)); KWord (SA e_p (HLEN + 1)) 1 (ELit 0)] ++ kn_x.
Definition tout : acs := mkcs YLO WS e_mtr e_fb RETPC x_regs kn_out (LO + 15)%nat.
Definition ce : gcallee := GCE NXF tin [tout] 0 0.

(* [comment removed for export] *)
Definition plan_ctor : plan :=
  PVia 0 tout LO (PRun [] (PExt ID_STRLEN [] (PRun [] (PExt ID_AMEMMOVE [] (PRun [] (PMerge 0)))))) (PHandoff 0).

End GaStrCtor.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GaBJCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsFZP.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT.GaDedup OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaJT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ GaStep.


Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ANNOT : Z := 0x70554.
Definition SF5_ENTRY : Z := 0x703e4.
(* [comment removed for export] *)
Definition SPX : expr := EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD e_sp (ELit (-192))) (ELit 5)).
Definition F : expr := EVar 33.     (* [comment removed for export] *)

(* [comment removed for export] *)
Section Tpl.
Variable allowed : nat -> bool.
Definition eok (e : expr) : bool := forallb allowed (expr_vars e []).
Fixpoint tregs (rs : list expr) (i : nat) (dead : list nat) (v : nat) : list expr :=
  match rs with
  | [] => []
  | e :: r => if (eok e && negb (existsb (Nat.eqb i) dead))%bool then e :: tregs r (S i) dead v else EVar v :: tregs r (S i) dead (S v)
  end.
Definition content_ok (b : expr) (o : Z) : bool :=
  (expr_eqb b e_sp && Z.leb (-104) o && Z.ltb o 0) || (expr_eqb b SPX && Z.eqb o 24)
  || (expr_eqb b F && (Z.eqb o 224 || Z.eqb o 232 || Z.eqb o 240)) || match b with ELit _ => true | _ => false end.
Definition kkeep (K : kentry) : bool :=
  match K with
  | KWord (SA b o) _ v => eok b && eok v && content_ok b o
  | KZero (SA b o) n => match b with ELit _ => eok n | _ => false end
  | KBlob _ _ _ | KFill _ _ _ => false
  | KImg _ _ => true
  | KAlign e _ | KRange e _ _ => eok e
  | KWr (SA b _) n | KUnk (SA b _) n | KShOk (SA b _) n => eok b && eok n
  | KDisj (SA b1 _) n1 (SA b2 _) n2 => eok b1 && eok n1 && eok b2 && eok n2
  | _ => false
  end%bool.
Definition mkT (cs : acs) (dead : list nat) (G : Z) : acs :=
  let rs := tregs (s_regs (a_ss cs)) 0 dead (nxt cs) in
  let m := maxvar_regs rs (nxt cs) in
  let M := EVar m in
  ACS (mk_ss (pc cs) rs (List.filter kkeep (kn cs) ++ [KRange (esub M FuzzN.e_mtr) 0 G; KRange M 0 (FuzzN.MTRIN + G)]) (S m))
      [] 0 FuzzN.YLO 0 (a_vis cs) [] 0 e_sp FdStd false M (a_fake cs) (a_fbud cs).
End Tpl.

Module FuzzNP.
Import FuzzN.
(* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, NINSTR); (0x9e038, 72%nat); (0x9df94, 41%nat); (0x9e158, 40%nat)].
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 110 then Some GaNumT.GaVecT.Ctor.ce else if Nat.eqb id 111 then Some GaStrCtor.ce else None.
Definition CT2 (id : nat) : option gcallee2 :=
  if Nat.eqb id 112 then Some GaNumT.GaRead.ce2 else if Nat.eqb id 113 then Some GaBJCert.GaBJT.ce2 else if Nat.eqb id 114 then Some GaNumT.GaVecT.Push.ce2 else None.
Definition XN : nat -> list expr -> acs -> option acs :=
  XNsf5 NXF GASAN SF5_ENTRY (XNann NXF GASAN ANNOT (XNd (XNp (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CT)))).
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2.


(* [comment removed for export] *)
Definition pseq (fs : list (plan -> plan)) (k : plan) : plan := fold_right (fun f acc => f acc) k fs.     (* [comment removed for export] *)
Definition TIDY (k : plan) : plan := PExt 48 [] (PExt 47 [] k).
Definition SHOK (off n : Z) (k : plan) : plan := PExt 46 [F; ELit off; ELit n] (PExt 47 [F] k).   (* [comment removed for export] *)
Definition P1 : expr := EVar 66.                          (* [comment removed for export] *)
Definition MTR0 : expr := eaddz e_mtr EVT.    (* [comment removed for export] *)
Definition FB1 : expr := eaddz e_fb (-1).                 (* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMSG : Z := GaNumT.GaFMST.FMSGROW.
Definition G1 : Z := EVT + FMSG.                          (* [comment removed for export] *)
Definition G2 : Z := G1 + KFREE + GaBJCert.GaBJT.BJGROW.           (* [comment removed for export] *)
Definition GJ2 : Z := G2 + 2 * KFREE.                     (* [comment removed for export] *)
Definition GJ3 : Z := GJ2 + EVT + KFREE.                  (* [comment removed for export] *)
Definition G4 : Z := GJ3 + FMSG.                          (* [comment removed for export] *)
Definition GJ4 : Z := G4 + 2 * KFREE.                     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition B1 : nat := 120.  Definition MTR1 : expr := EVar 137.  Definition DL1 : expr := EVar 138.    (* [comment removed for export] *)
Definition B2 : nat := 200.  Definition MTR2 : expr := EVar 217.                                          (* [comment removed for export] *)
Definition B3 : nat := 260.  Definition P2 : expr := EVar 260.                                            (* [comment removed for export] *)
Definition B4 : nat := 360.  Definition MTR4 : expr := EVar 377.  Definition DL4 : expr := EVar 378.    (* [comment removed for export] *)
Definition READ1_ARGS : list expr := [ELit 0; P1; eadd SIZE P1; ELit 11; eadd SIZE P1; MTR0; FB1].
Definition B2J_ARGS (m : expr) : list expr := [ELit 0; P1; SIZE; eadd SIZE P1; m; FB1].
Definition HJ2 : nat := 3.
Definition toJ2 : plan := PRun [0x9cd6c] (PHandoff HJ2).
(* [comment removed for export] *)
Definition AFT (c : smode) (ok : bool) (j : smode) : plan :=
  let rest := match c, ok with ML, true => PRun [] (PExt 22 [] (PHandoff HJ2)) | _, _ => toJ2 end in      (* [comment removed for export] *)
  PFact (KRange (esub MTR2 e_mtr) 0 G2) (TIDY (match j with ML => PExt 13 [EVar 218] (PRun [] (PExt 22 [] rest)) | MS => rest end)).
Definition B2J (c : smode) (ok : bool) : plan :=
  let m := match c, ok with ML, false => eaddz MTR1 KFREE | _, _ => MTR1 end in      (* [comment removed for export] *)
  PBump B2 (PExt2 113 (B2J_ARGS m) (AFT c ok MS) (AFT c ok ML)).
Definition JSON (k : plan) : plan := SHOK 288 24 (PExt 6 [] (PRun [] k)).     (* [comment removed for export] *)
Definition N13 (c : smode) (d : expr) (k : plan) : plan := match c with ML => PExt 13 [d] k | MS => k end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition planA (c : smode) : plan :=
  pseq [PFact (KRange (esub MTR1 e_mtr) 0 G1); TIDY; N13 c DL1; PRun [0x9cc98]]
    (PBranch
       (pseq [PRun []; PExt 6 []; PRun []; JSON] (B2J c true))                                   (* [comment removed for export] *)
       (match c with MS => pseq [PRun []; JSON] (B2J MS false) | ML => pseq [PRun []; PExt 22 []; PRun []; JSON] (B2J ML false) end)).
Definition plan_top : plan :=
  pseq [PRun []; PExt 50 [ELit 3]; PExt 47 []; PRun []; SHOK 224 24; PExt 6 []; PRun []; PExt 110 [ELit 0; ELit 0; e_mtr; FB1]; TIDY; PExt 13 [P1]; PRun [];
        SHOK 128 64; PExt 111 [ELit 0; ELit 0; MTR0; FB1]; TIDY; PRun []; PExt 5 []; PRun []; PBump B1]
       (PExt2 112 READ1_ARGS (PHandoff 1) (PHandoff 2)).
(* [comment removed for export] *)
Definition XP := xpath IT NXF XN XB.
Definition st (cs : acs) (l : list xstep) : acs := snd (XP cs l 0).
Definition TD : list xstep := [X 48 []; X 47 []].
Definition SH (off n : Z) : list xstep := [X 46 [F; ELit off; ELit n]; X 47 [F]].
Definition pre_top : list xstep :=
  [R []; X 50 [ELit 3]; X 47 []; R []] ++ SH 224 24 ++ [X 6 []; R []; X 110 [ELit 0; ELit 0; e_mtr; FB1]] ++ TD ++ [X 13 [P1]; R []] ++ SH 128 64
  ++ [X 111 [ELit 0; ELit 0; MTR0; FB1]] ++ TD ++ [R []; X 5 []; R []; XBump B1].
Definition ST_pre : acs := Eval vm_compute in st tin pre_top.
(* [comment removed for export] *)
Definition A_S : acs := Eval vm_compute in st ST_pre [XD (DX2a 112 READ1_ARGS)].
Definition A_L : acs := Eval vm_compute in st ST_pre [XD (DX2b 112 READ1_ARGS)].

(* [comment removed for export] *)
Definition DEADJ : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.     (* [comment removed for export] *)
Definition allow2 (v : nat) : bool := Nat.ltb v 67.
Definition ST_J2 : acs := Eval vm_compute in
  st A_S ([XFact (KRange (esub MTR1 e_mtr) 0 G1)] ++ TD ++ [R [0x9cc98]; XD DBrF; R []; X 6 []; R []] ++ SH 288 24 ++ [X 6 []; R []; XBump B2;
           XD (DX2a 113 (B2J_ARGS MTR1)); XFact (KRange (esub MTR2 e_mtr) 0 G2)] ++ TD ++ [R [0x9cd6c]]).
Definition J2 : acs := Eval vm_compute in mkT allow2 ST_J2 DEADJ GJ2.
Definition MJ2 : expr := Eval vm_compute in a_meter J2.
(* [comment removed for export] *)
Definition allow3 (v : nat) : bool := Nat.ltb v 67 || Nat.eqb v 260.
Definition PUSH_ARGS : list expr := [ELit 0; P1; SIZE; MJ2; FB1].
Definition ST_J3 (cls : nat) : acs :=
  st J2 ([R []; XBump B3; XD (match cls with O => DX2a 114 PUSH_ARGS | _ => DX2b 114 PUSH_ARGS end)] ++ TD ++ [X 13 [P2]]).
Definition J3_0 : acs := Eval vm_compute in mkT allow3 (ST_J3 0) DEADJ GJ3.
Definition J3_1 : acs := Eval vm_compute in mkT allow3 (ST_J3 1) DEADJ GJ3.
Definition J3 (cls : nat) : acs := match cls with O => J3_0 | _ => J3_1 end.
Definition MJ3 (cls : nat) : expr := a_meter (J3 cls).
Definition READ2_ARGS (cls : nat) : list expr :=
  match cls with
  | O => [ELit 0; P2; eaddz (eadd SIZE P2) 1; ELit 11; eadd (escale 2 SIZE) P2; MJ3 0; FB1]
  | _ => [ELit 0; P2; eaddz P2 2; ELit 11; eaddz P2 2; MJ3 1; FB1]
  end.
(* [comment removed for export] *)
Definition ST_J4 (cls : nat) : acs :=
  st (J3 cls) ([R []] ++ SH 32 64 ++ [X 111 [ELit 0; ELit 0; MJ3 cls; FB1]] ++ TD ++ [R []; X 5 []; R []; XBump B4; XD (DX2a 112 (READ2_ARGS cls));
                XFact (KRange (esub MTR4 e_mtr) 0 G4)] ++ TD ++ [R [0x9cde8]; XD DBrF; R []; X 6 []; R [0x9ce5c]]).
Definition J4_0 : acs := Eval vm_compute in mkT allow3 (ST_J4 0) DEADJ GJ4.
Definition J4_1 : acs := Eval vm_compute in mkT allow3 (ST_J4 1) DEADJ GJ4.


(* [comment removed for export] *)
Definition planJ2 : plan :=
  pseq [PRun []; PBump B3] (PExt2 114 PUSH_ARGS (pseq [TIDY; PExt 13 [P2]] (PHandoff 4)) (pseq [TIDY; PExt 13 [P2]] (PHandoff 5))).
Definition toJ4 (cls : nat) : plan := PRun [0x9ce5c] (PHandoff (6 + cls)).
Definition AFTR (cls : nat) (c : smode) : plan :=
  pseq [PFact (KRange (esub MTR4 e_mtr) 0 G4); TIDY; N13 c DL4; PRun [0x9cde8]]
    (PBranch
       (match c with MS => pseq [PRun []; PExt 6 []] (toJ4 cls) | ML => pseq [PRun []; PExt 6 []; PRun []; PExt 22 []] (PHandoff (6 + cls)) end)   (* [comment removed for export] *)
       (match c with MS => toJ4 cls | ML => pseq [PRun []; PExt 22 []] (toJ4 cls) end)).
Definition planJ3 (cls : nat) : plan :=
  pseq [PRun []; SHOK 32 64; PExt 111 [ELit 0; ELit 0; MJ3 cls; FB1]; TIDY; PRun []; PExt 5 []; PRun []; PBump B4]
       (PExt2 112 (READ2_ARGS cls) (AFTR cls MS) (AFTR cls ML)).
Definition planJ4 : plan :=
  pseq [PRun []; PExt 8 []; PRun []; PExt 8 []; PRun []; PExt 22 []; PRun []; PExt 52 []; PExt 51 []; PRun []] (PHandoff 0).
Definition CUTS : list (acs * plan) :=
  [(A_S, planA MS); (A_L, planA ML); (J2, planJ2); (J3_0, planJ3 0); (J3_1, planJ3 1); (J4_0, planJ4); (J4_1, planJ4)].
Definition FUELB : nat := 20000.


End FuzzNP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module FuzzEP.
Import FuzzN. Import FuzzE.
(* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, NINSTR); (0x9e038, 72%nat); (0x9df94, 41%nat); (0x9e158, 40%nat); (0x9dac8, 27%nat)].
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 111 then Some GaStrCtor.ce else if Nat.eqb id 115 then Some GaNumT.GaReadE.RdE.ceE else if Nat.eqb id 116 then Some GaBJCert.GaBJT.ceE
  else if Nat.eqb id 117 then Some GaNumT.GaVecT.Push.ceE else None.
Definition CT2 (id : nat) : option gcallee2 := if Nat.eqb id 112 then Some GaNumT.GaRead.ce2 else None.
Definition XN : nat -> list expr -> acs -> option acs :=
  XNsf5 NXF GASAN SF5_ENTRY (XNann NXF GASAN ANNOT (XNd (XNp (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CT)))).
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2.
Definition TIDY := FuzzNP.TIDY.  Definition SHOK := FuzzNP.SHOK.  Definition pseq := FuzzNP.pseq.  Definition N13 := FuzzNP.N13.
Definition FB1 : expr := eaddz e_fb (-1).
Definition P2E : expr := EVar 200.                       (* [comment removed for export] *)
Definition MTRE : expr := eaddz e_mtr EVT.                (* [comment removed for export] *)
Definition MTR4E : expr := EVar 277.  Definition DL4E : expr := EVar 278.     (* [comment removed for export] *)
Definition G4E : Z := 1 + EVT + FuzzNP.FMSG.
Definition READ2E_ARGS : list expr := [ELit 0; P2E; eaddz P2E 1; ELit 11; eaddz P2E 1; MTRE; FB1].
(* [comment removed for export] *)
Definition DT : plan := pseq [PExt 8 []; PRun []; PExt 8 []; PRun []; PExt 22 []; PRun []; PExt 52 []; PExt 51 []; PRun []] (PHandoff 0).

(* [comment removed for export] *)
Definition SHx (off n : Z) : list xstep := [X 46 [F; ELit off; ELit n]; X 47 [F]].
Definition TDx : list xstep := [X 48 []; X 47 []].
Definition preEx : list xstep :=
  [R []; X 50 [ELit 3]; X 47 []; R []] ++ SHx 224 24 ++ [X 6 []; R []] ++ SHx 128 64 ++ [X 111 [ELit 0; ELit 0; e_mtr; FB1]] ++ TDx ++ [R []; X 5 []; R [];
   X 115 [ELit 0; ELit 11; e_mtr; FB1]] ++ TDx ++ [R []] ++ SHx 288 24 ++ [X 6 []; R []; X 116 [ELit 0; e_mtr; FB1]] ++ TDx ++ [R []; XBump 200;
   X 117 [ELit 0; e_mtr; FB1]] ++ TDx ++ [X 13 [P2E]; R []] ++ SHx 32 64 ++ [X 111 [ELit 0; ELit 0; MTRE; FB1]] ++ TDx ++ [R []; X 5 []; R []; XBump 260].
Definition armEx : list xstep := [XD (DX2a 112 READ2E_ARGS); XFact (KRange (esub MTR4E e_mtr) 0 G4E)] ++ TDx ++ [R [0x9cde8]; XD DBrF; R []; X 6 []; R [0x9ce5c]].
Definition allowE (v : nat) : bool := Nat.ltb v 67 || Nat.eqb v 200.
Definition GJ4E : Z := G4E + 2 * KFREE.
Definition JE : acs := Eval vm_compute in mkT allowE (snd (xpath IT NXF XN XB tin (preEx ++ armEx) 0)) FuzzNP.DEADJ GJ4E.
Definition AFTREJ (c : smode) : plan :=
  pseq [PFact (KRange (esub MTR4E e_mtr) 0 G4E); TIDY; N13 c DL4E; PRun [0x9cde8]]
    (PBranch
       (match c with MS => pseq [PRun []; PExt 6 []; PRun [0x9ce5c]] (PMerge 1) | ML => pseq [PRun []; PExt 6 []; PRun []; PExt 22 []] (PMerge 1) end)
       (match c with MS => pseq [PRun [0x9ce5c]] (PMerge 1) | ML => pseq [PRun []; PExt 22 []; PRun [0x9ce5c]] (PMerge 1) end)).
Definition planE : plan :=
  pseq [PRun []; PExt 50 [ELit 3]; PExt 47 []; PRun []; SHOK 224 24; PExt 6 []; PRun [];                    (* [comment removed for export] *)
        SHOK 128 64; PExt 111 [ELit 0; ELit 0; e_mtr; FB1]; TIDY; PRun []; PExt 5 []; PRun [];               (* [comment removed for export] *)
        PExt 115 [ELit 0; ELit 11; e_mtr; FB1]; TIDY; PRun [];                                                (* [comment removed for export] *)
        SHOK 288 24; PExt 6 []; PRun []; PExt 116 [ELit 0; e_mtr; FB1]; TIDY; PRun [];                        (* [comment removed for export] *)
        PBump 200; PExt 117 [ELit 0; e_mtr; FB1]; TIDY; PExt 13 [P2E]; PRun [];                               (* [comment removed for export] *)
        SHOK 32 64; PExt 111 [ELit 0; ELit 0; MTRE; FB1]; TIDY; PRun []; PExt 5 []; PRun []; PBump 260]        (* [comment removed for export] *)
       (PVia 1 JE 260 (PExt2 112 READ2E_ARGS (AFTREJ MS) (AFTREJ ML)) (PRun [] DT)).   (* [comment removed for export] *)
Definition FUELB : nat := 20000.

End FuzzEP.
End AsFZP.
Module AsFZCertE.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ AsFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzE. Import FuzzEP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma certE : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HSce ce) 0%nat BFUEL FUELB None (ce_tin ce) planE = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan_E : gplan_ok planE = true. Proof. vm_compute. reflexivity. Qed.
End AsFZCertE.
Module AsFZCertN0.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ AsFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma top : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUELB None (ce_tin ce) plan_top = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cut2 : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 3) 0%nat BFUEL FUELB None J2 planJ2 = COk (SHole 4).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 4))). Qed.
Lemma cut5 : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 6) 0%nat BFUEL FUELB None J4_0 planJ4 = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cut6 : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 7) 0%nat BFUEL FUELB None J4_1 planJ4 = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan_top : gplan_ok plan_top = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_AS : gplan_ok (planA MS) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_AL : gplan_ok (planA ML) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_J2 : gplan_ok planJ2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_J30 : gplan_ok (planJ3 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_J31 : gplan_ok (planJ3 1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_J4 : gplan_ok planJ4 = true. Proof. vm_compute. reflexivity. Qed.
End AsFZCertN0.
Module AsFZCertN1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ AsFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cut0 : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 1) 0%nat BFUEL FUELB None A_S (planA MS) = COk (SHole 3).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 3))). Qed.
End AsFZCertN1.
Module AsFZCertN2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ AsFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cut1 : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 2) 0%nat BFUEL FUELB None A_L (planA ML) = COk (SHole 3).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 3))). Qed.
End AsFZCertN2.
Module AsFZCertN3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ AsFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cut3 : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 4) 0%nat BFUEL FUELB None J3_0 (planJ3 0) = COk (SHole 6).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 6))). Qed.
End AsFZCertN3.
Module AsFZCertN4.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ AsFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzNP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cut4 : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 5) 0%nat BFUEL FUELB None J3_1 (planJ3 1) = COk (SHole 7).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 7))). Qed.
End AsFZCertN4.
Module GaBJCertX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaBJCert.GaBJ.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma cutS : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 1) 0%nat BFUEL FUELB None (EPI MS) (EPIK MS) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cutL : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 2) 0%nat BFUEL FUELB None (EPI ML) (EPIK ML) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma certE : check ASEGS IT AASAN NXFE LIMIT ISP0 (GaCommon.XN IT NXFE) XE0 XB0 (HSce ceE) 0%nat BFUEL FUEL None (ce_tin ceE) plan_E = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan_bj : gplan_ok plan_bj = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_S : gplan_ok (EPIK MS) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_L : gplan_ok (EPIK ML) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_E : gplan_ok plan_E = true. Proof. vm_compute. reflexivity. Qed.
End GaBJCertX.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaBJC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT.GaDedup OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.GaBJCert.GaBJ OSSVerify.Proofs.glaze.binary_reflection.lib.GaBJCert GaBJCertX.

Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs2 : holes_only (SHole 2) = true. Proof. reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
  check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUELB None T k = COk sh.
Proof.
  intros i T k H. destruct i as [|[|i]]; [| |destruct i; discriminate H].
  - injection H as <- <-. exists (SHole 0). split; [exact gplan_S|]. split; [reflexivity|]. exact GaBJCertX.cutS.
  - injection H as <- <-. exists (SHole 1). split; [exact gplan_L|]. split; [reflexivity|]. exact GaBJCertX.cutL.
Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN bc cc.
Notation CC := (callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH).

Lemma CT_sound : forall id c, CT id = Some c -> CC c.
Proof.
  intros id c H. unfold CT in H. destruct (Nat.eqb id 201); [|discriminate H]. injection H as <-.
  exact (GaB2JC.b2jv_asan_callee_L1 RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all).
Qed.
Lemma CT2_sound : forall id c, CT2 id = Some c -> CC (c2_merged c).
Proof.
  intros id c H. unfold CT2 in H.
  destruct (Nat.eqb id 200); [injection H as <-; exact (GaB2JC.b2jv_asan_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  exact (AzStrResizeC.CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c H).
Qed.

Theorem b2j_asan_callee : CC ce.
Proof.
  refine (contract_of_cert_xb_cut ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUELB XN _ XB _ CUTS cuts_ok plan_bj (SHole 2) gplan_bj hs2 GaBJCert.top).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
    apply XNw_sound. apply XNd_sound. apply XNp_sound.
    refine (XNc_sound ASEGS IT AASAN asan_in_hull asan_hull_ok IT_ok NXF [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
              asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT CT_sound _).
    apply GC_all; first [assumption | exact IT_ok].
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XB.
    exact (XBc_sound0 ASEGS AASAN asan_in_hull asan_hull_ok NXF [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
              asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 CT2_sound).
Qed.

Theorem b2j_asan_callee_E : CC ceE.
Proof.
  refine (contract_of_cert ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            ceE IT IT_ok LIMIT 0%nat BFUEL FUEL (GaCommon.XN IT NXFE) _ plan_E _ gplan_E hs0 GaBJCertX.certE).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXFE RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GaBJC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaFA OSSVerify.Proofs.glaze.binary_reflection.lib.GaFAPlanDef OSSVerify.Proofs.glaze.binary_reflection.lib.GaFATop OSSVerify.Proofs.glaze.binary_reflection.lib.GaFAcM0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaFAC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaFA OSSVerify.Proofs.glaze.binary_reflection.lib.GaFAPlanDef OSSVerify.Proofs.glaze.binary_reflection.lib.GaFA OSSVerify.Proofs.glaze.binary_reflection.lib.GaFATop OSSVerify.Proofs.glaze.binary_reflection.lib.GaFAcM0. Import GaFAcM0.GaFA_A0 GaFAcM0.GaFA_A1 GaFAcM0.GaFA_A2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) ->
  exists sh, gplan_ok k = true /\ holes_only sh = true /\
    check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh.
Proof.
  intros i T k H.
  assert (X : cut_stmt i).
  {
  destruct i as [|i]; [apply cut_ok_sound; exact GaFAcM0.GaFA_A0.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact GaFAcM0.GaFA_A1.cut|].
  destruct i as [|i]; [apply cut_ok_sound; exact GaFAcM0.GaFA_A2.cut|].
  exfalso. rewrite (proj2 (nth_error_None CUTS _)) in H; [discriminate|]. rewrite CUTS_len. unfold NCUTS. lia. }
  unfold cut_stmt in X. rewrite H in X. exact X.
Qed.
Lemma top_cert : exists sh, holes_only sh = true /\
  check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 (XN IT NXF) XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUEL None (ce_tin ce) plan_top = COk sh.
Proof. eexists. split; [| exact GaFATop.top]. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN 0 0.

Theorem fa_asan_callee : callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH ce.
Proof.
  destruct top_cert as (sh & Hsh & CERT).
  refine (contract_of_cert_xb_cut ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ XB _ CUTS cuts_ok plan_top sh top_gplan Hsh CERT).
  -   intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn. discriminate Hn.
Qed.
End Contract.
End GaFAC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaFMSL OSSVerify.Proofs.glaze.binary_reflection.lib.GaFMSH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaFMS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaFMST.

Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.



Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, 828%nat)].   (* [comment removed for export] *)
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 100 then Some GaFA.ce else if Nat.eqb id 101 then Some GaFMSL.ceI else if Nat.eqb id 102 then Some GaFMSL.ceD else None.
Definition XN : nat -> list expr -> acs -> option acs := XNp (XNw (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CT)).   (* [comment removed for export] *)
Definition CT2 (id : nat) : option gcallee2 := if Nat.eqb id 103 then Some (GaFMSH.ce2 MS) else if Nat.eqb id 113 then Some (GaFMSH.ce2 ML) else None.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2.

(* [comment removed for export] *)
Definition F : expr := EVar 36.
Definition shF : expr := EAlu ALU_SRL F (ELit 3).
Definition F_facts : list kentry :=
  [KRange F PTRLO (PTRHI - 128); KRange (eaddz F 128) (PTRLO + 128) PTRHI; KAlign F 128;
   KWr (SA F 0) (ELit 128); KUnk (SA F 0) (ELit 128);
   KUnk (SA shF SB) (ELit 16); KWr (SA shF SB) (ELit 16);
   KDisj (SA shF SB) (ELit 16) (SA (ELit 0) (SB + IMG_LO / 8)) (ELit (IMG_SZ / 8));
   KDisj (SA F 0) (ELit 128) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart F 0 (ELit 128); shmap_apart F 0 (ELit 128);
   KDisj (SA F 0) (ELit 128) (SA v 0) (ELit 64); KDisj (SA F 0) (ELit 128) (SA c 0) (ELit 8); KDisj (SA F 0) (ELit 128) (SA c 32) (ELit 8);
   KDisj (SA F 0) (ELit 128) (SA q 0) (ELit 8); KDisj (SA F 0) (ELit 128) (SA I 0) (esub E I);
   KDisj (SA F 0) (ELit 128) (SA e_sp (- FRX)) (ELit FRX);
   KWord (SA F 32) 8 E; KShOk (SA F 32) (ELit 8)].

(* [comment removed for export] *)
Definition HEAD : Z := 0x9f3a4.
Definition SP1 : expr := eaddz e_sp (-256).        (* [comment removed for export] *)
Definition shof (x : expr) (k : Z) : expr := EAlu ALU_ADD (EAlu ALU_SRL x (ELit 3)) (ELit (SB + k)).
(* [comment removed for export] *)
Definition loop_slots : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 25; 28; 29; 30; 31]%nat.
Definition loop_regs (a0 : expr) (slot0 : nat) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regsT
    2 SP1) 8 e_sp) 9 SP1) 10 a0) 18 (shof F 0)) 19 c) 20 q) 21 (shof q 0)) 22 (eaddz F 96)) 23 (eaddz F 32)) 24 (eaddz F 64)) 26 (ELit SB)) 27 (shof c 0))
    loop_slots slot0.
Definition frame_kn : list kentry :=
  [KWord (SA e_sp (-240)) 8 (ELit 3); KWord (SA e_sp (-232)) 8 (shof c 4); KWord (SA e_sp (-224)) 8 (eaddz c 32);
   KWord (SA e_sp (-216)) 8 F; KWord (SA e_sp (-208)) 8 F; KWord (SA e_sp (-200)) 8 (eaddz v 40); KWord (SA e_sp (-192)) 8 (ELit 29281);
   KWord (SA e_sp (-184)) 8 (ELit 0x22bd0); KWord (SA e_sp (-176)) 8 (ELit 0x22bc0); KWord (SA e_sp (-168)) 8 v; KWord (SA e_sp (-160)) 8 F;
   KWord (SA e_sp (-104)) 8 (EVar 26); KWord (SA e_sp (-96)) 8 (EVar 25); KWord (SA e_sp (-88)) 8 (EVar 24); KWord (SA e_sp (-80)) 8 (EVar 23);
   KWord (SA e_sp (-72)) 8 (EVar 22); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-48)) 8 (EVar 19);
   KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-24)) 8 (EVar 8); KWord (SA e_sp (-16)) 8 (EVar 7);
   KWord (SA e_sp (-8)) 8 (EVar 0)].
(* [comment removed for export] *)
Definition itk (o : expr) : list kentry :=
  [KWord (SA q 0) 8 (eadd I o); KRange o 0 BUFMAX; KRange (esub (esub E I) o) 0 BUFMAX].
(* [comment removed for export] *)
Definition mtrk (mtr : expr) : list kentry := [KRange (esub mtr e_mtr) 0 FMSGROW; KRange mtr 0 (MTRIN + FMSGROW)].
Definition ladder (a mtr : expr) : list kentry := pw_facts e_mtr (escale 8 a) mtr.
(* [comment removed for export] *)
Definition strLF (d s a : expr) : list kentry := strL d s a ++ [KDisj (SA d 0) (escale 8 a) (SA F 0) (ELit 128)].
Definition loop_common : list kentry := [KRange e_mtr 0 MTRIN] ++ frame_kn ++ F_facts ++ sp_in ++ kn_common.
Definition mkcsL (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRX 0 vis WS 0 e_sp FdStd false mtr [(F, ELit 128)] (eaddz e_fb (-1)).

Definition NV : expr := EVar 100. Definition O1 : expr := EVar 101.
Definition j1_kn : list kentry :=
  itk O1 ++ [KRange (esub E I) 1 BUFMAX; KRange NV 1 (2^62); KWord (SA v 16) 1 (escale 2 sv); KRange sv 0 22; KWord (SA c 0) 4 (ELit 0);
             KWord (SA c 32) 4 (eaddz dep 1)]
  ++ loop_common.   (* [comment removed for export] *)
Definition J1 : acs := mkcsL HEAD (loop_regs (eaddz NV (-1)) 102) j1_kn 118 [] e_mtr.
(* [comment removed for export] *)
Definition JJ : nat := 118.
Definition OJ : expr := EVar 119. Definition SVJ : expr := EVar 120. Definition ERJ : expr := EVar 121.   (* [comment removed for export] *)
Definition cnt (n : expr) (j : nat) : expr := esub (eaddz n (-1)) (EVar j).     (* [comment removed for export] *)
Definition inv_kn_S : list kentry :=
  itk OJ ++ [KRange (esub NV (EVar JJ)) 1 (2^62); KRange (esub E I) 1 BUFMAX; KRange NV 1 (2^62); KWord (SA v 16) 1 (escale 2 SVJ); KRange SVJ 0 22;
             KWord (SA c 0) 4 ERJ; KRange ERJ 0 0; KWord (SA c 32) 4 (eaddz dep 1)] ++ loop_common.
Definition INV_S : acs := mkcsL HEAD (loop_regs (cnt NV JJ) 123) inv_kn_S 160 [] e_mtr.
Definition OK : expr := EVar 119. Definition DK : expr := EVar 120. Definition SK : expr := EVar 121. Definition AK : expr := EVar 122.
Definition ERK : expr := EVar 123. Definition MTRK : expr := EVar 124.
Definition inv_kn_L : list kentry :=
  itk OK ++ [KRange (esub NV (EVar JJ)) 1 (2^62); KRange (esub E I) 1 BUFMAX; KRange NV 1 (2^62); KWord (SA c 0) 4 ERK; KRange ERK 0 0; KWord (SA c 32) 4 (eaddz dep 1)]
  ++ mtrk MTRK ++ ladder AK MTRK ++ strLF DK SK AK ++ loop_common.
Definition INV_L : acs := mkcsL HEAD (loop_regs (cnt NV JJ) 125) inv_kn_L 160 [(DK, escale 8 AK)] MTRK.

(* [comment removed for export] *)
Definition NB : expr := eaddz NV (-1).
Definition J2PC : Z := 0x9f558.

Definition O2 : expr := EVar 200. Definition KL : expr := EVar 201.
Definition j2_regs (base : list expr) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd base
    5 (EVar 202)) 10 (EVar 203)) 11 (EVar 204)) 12 KL) 13 E) 14 (ELit 22)) 15 (EVar 205)) 16 (EVar 206)) 17 (EVar 207)) 25 (cnt NV JJ).
Definition j2_facts : list kentry :=
  [KWord (SA q 0) 8 (eadd I O2); KRange O2 0 BUFMAX; KRange (esub (esub E I) O2) 0 BUFMAX; KRange KL 0 (2^62 - 1); KShOk (SA F 64) (ELit 8)].
Definition jfacts : list kentry := [KRange (EVar JJ) 0 (2^62 - 1)].   (* [comment removed for export] *)
Definition J2S (last : bool) : acs :=
  let T := mkcsL J2PC (j2_regs (loop_regs (cnt NV JJ) 123)) (j2_facts ++ (if last then [] else jfacts) ++ skipn 3 inv_kn_S) 208 [] e_mtr in
  if last then inst T JJ NB else T.


Definition TL : acs := INV_L.
Definition JC : nat := 160.
Definition NC : expr := esub NV (EVar JJ).
Definition cntC : expr := esub (esub (eaddz NV (-1)) (EVar JJ)) (EVar JC).
Definition OKc : expr := EVar 161. Definition DKc : expr := EVar 162. Definition SKc : expr := EVar 163. Definition AKc : expr := EVar 164.
Definition ERKc : expr := EVar 165. Definition MTRKc : expr := EVar 166.
Definition inv_kn_LC : list kentry :=
  itk OKc ++ [KRange (esub NC (EVar JC)) 1 (2^62); KRange (esub E I) 1 BUFMAX; KRange NC 1 (2^62); KWord (SA c 0) 4 ERKc; KRange ERKc 0 0; KWord (SA c 32) 4 (eaddz dep 1)]
  ++ mtrk MTRKc ++ ladder AKc MTRKc ++ strLF DKc SKc AKc ++ loop_common.
Definition INV_LC : acs := mkcsL HEAD (loop_regs cntC 167) inv_kn_LC 200 [(DKc, escale 8 AKc)] MTRKc.
Definition O2c : expr := EVar 240. Definition KLc : expr := EVar 241.
Definition j2_regsC (base : list expr) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd base
    5 (EVar 242)) 10 (EVar 243)) 11 (EVar 244)) 12 KLc) 13 E) 14 (ELit 22)) 15 (EVar 245)) 16 (EVar 246)) 17 (EVar 247)) 25 cntC.
Definition j2_factsC : list kentry :=
  [KWord (SA q 0) 8 (eadd I O2c); KRange O2c 0 BUFMAX; KRange (esub (esub E I) O2c) 0 BUFMAX; KRange KLc 0 (2^62 - 1); KShOk (SA F 64) (ELit 8)].
Definition J2LC : acs :=
  mkcsL J2PC (j2_regsC (loop_regs cntC 167)) (j2_factsC ++ [KRange (EVar JC) 0 (2^62 - 1)] ++ skipn 3 inv_kn_LC) 248 [(DKc, escale 8 AKc)] MTRKc.



(* [comment removed for export] *)
Definition XPC : Z := 0x9f7d0.
Definition exit_slots : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 25; 28; 29; 30; 31]%nat.
Definition exit_regs (slot0 : nat) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regsT
    2 SP1) 8 e_sp) 9 SP1) 18 (shof F 0)) 19 c) 20 q) 21 (shof q 0)) 22 (eaddz F 96)) 23 (eaddz F 32)) 24 (eaddz F 64)) 26 (ELit SB)) 27 (shof c 0))
    exit_slots slot0.
Definition XP : expr := EVar 300.  Definition XER : expr := EVar 301.  Definition XMTR : expr := EVar 302.
Definition XSV : expr := EVar 303.
Definition XD : expr := EVar 303. Definition XS_ : expr := EVar 304. Definition XA : expr := EVar 305.
Definition xcut_kn_S : list kentry :=
  [KWord (SA q 0) 8 XP; KWord (SA c 0) 4 XER; KWord (SA c 32) 4 (eaddz dep 1); KRange (esub E I) 1 BUFMAX; KWord (SA v 16) 1 (escale 2 XSV); KRange XSV 0 22] ++ mtrk XMTR ++ loop_common.
Definition xcut_kn_L : list kentry :=
  [KWord (SA q 0) 8 XP; KWord (SA c 0) 4 XER; KWord (SA c 32) 4 (eaddz dep 1); KRange (esub E I) 1 BUFMAX] ++ mtrk XMTR ++ strLF XD XS_ XA ++ loop_common.
Definition XCUT_S : acs := mkcsL XPC (exit_regs 306) xcut_kn_S 323 [] XMTR.
Definition XCUT_L : acs := mkcsL XPC (exit_regs 306) xcut_kn_L 323 [(XD, escale 8 XA)] XMTR.
Definition REL : Z := 0x9f848.     (* [comment removed for export] *)
Definition plan_exit (h : nat) : plan := PRun [REL] (PExt 51 [] (PRun [] (PHandoff h))).
Definition CUTS : list (acs * plan) := [(XCUT_S, plan_exit 0); (XCUT_L, plan_exit 1)].














End GaFMS.
Module GaFMSPlan.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaFMST GaFMS.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ladS (k : plan) : plan :=
  PExt 49 [e_mtr; ELit 23; escale 8 (EVar 265); e_mtr; ELit 2]
    (PFactLe (eadd e_mtr (EVar 262)) (pwtop_e e_mtr (escale 8 (EVar 265))) (MTRIN + FMSGROW)
      (PFactLe (esub (eadd e_mtr (EVar 262)) e_mtr) (pwtop_d (escale 8 (EVar 265))) FMSGROW k)).
Definition ladL (k : plan) : plan :=
  PExt 49 [MTRKc; escale 8 AKc; escale 8 (EVar 305); e_mtr; ELit 2]
    (PFactLe (eadd MTRKc (EVar 302)) (pwtop_e e_mtr (escale 8 (EVar 305))) (MTRIN + FMSGROW)
      (PFactLe (esub (eadd MTRKc (EVar 302)) e_mtr) (pwtop_d (escale 8 (EVar 305))) FMSGROW k)).

(* [comment removed for export] *)
Definition XPC2 : Z := 0x9f7dc.
Definition XS : acs := mkcsL XPC2 (exit_regs 306) xcut_kn_S 323 [] XMTR.
Definition XL : acs := mkcsL XPC2 (exit_regs 306) xcut_kn_L 323 [(XD, escale 8 XA)] XMTR.
Definition plan_top : plan :=
  (PVia 1 J1 100 (PCase2 (esub E I) 0 (PRun [] (PExt 50 [ELit 1] (PExt 47 [] (PRun [0x9f848] (PExt 51 [] (PRun [] (PExt 46 [I; ELit 0; esub E I] (PHandoff 0)))))))) (PRun [] (PExt 50 [ELit 1] (PExt 47 [] (PRun [0x9f12c] (PExt 46 [F; ELit 32; ELit 8] (PRun [0x9f150] (PBranch (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 0 (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0x9f1c4] (PCaseReg 15 1 (PCaseReg 15 0 (PRespell 15 (ELit 0) (PRun [0x9f35c] (PCaseReg 10 0 (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0x9f3a4] (PMergeW 1 [(101%nat, ELit 2)]))))) (PRespell 15 (ELit 1) (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 1 (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0x9f35c] (PCaseReg 10 0 (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0x9f3a4] (PMergeW 1 [(101%nat, ELit 3)]))))))) (PCaseReg 15 2 (PRespell 15 (ELit 2) (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 3 (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0x9f35c] (PCaseReg 10 0 (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0x9f3a4] (PMergeW 1 [(101%nat, ELit 5)])))))) (PRespell 15 (ELit 3) (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 7 (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0x9f340] (PBranch (PRun [0x9f35c] (PCaseReg 10 0 (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0x9f3a4] (PMergeW 1 [(101%nat, ELit 9)])))) (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))))))))))) (PRun [0x9f848] (PExt 51 [] (PRun [] (PHandoff 0)))))))))))) (PLoopM 118 NV [(INV_S, (PVia 2 (J2S false) 200 (PRun [0x9f3a8] (PExt 46 [F; ELit 64; ELit 8] (PCase2 (esub (esub E I) OJ) 0 (PRun [0x9f7dc] (PHandoff 3)) (PRun [0x9f3dc] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x9f558] (PMergeW 2 [(200%nat, (eaddz OJ (1)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub E I) OJ) 1 (PRun [0x9f7dc] (PHandoff 3)) (PRun [0x9f558] (PMergeW 2 [(200%nat, (eaddz OJ (2)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub E I) OJ) 3 (PRun [0x9f7dc] (PHandoff 3)) (PRun [0x9f558] (PMergeW 2 [(200%nat, (eaddz OJ (4)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub E I) OJ) 7 (PRun [0x9f7dc] (PHandoff 3)) (PRun [0x9f550] (PBranch (PRun [0x9f558] (PMergeW 2 [(200%nat, (eaddz OJ (8)))])) (PRun [0x9f7dc] (PHandoff 3)))))))))))) (PCase2 (esub (esub E I) O2) 0 (PRun [0x9f7dc] (PHandoff 3)) (PCase2 KL 0 (PRun [0x9f580] (PBranch (PRun [0x9f7dc] (PHandoff 3)) (PRun [0x9f7dc] (PHandoff 3)))) (PCase2 KL 5 (PRun [0x9f580] (PBranch (PRun [0x9f5a8] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x9f5c4] (PExt 42 [] (PRun [0x9f7dc] (PHandoff 3)))) (PRespell 11 (ELit 97) (PRun [0x9f5d8] (PExt 46 [F; ELit 96; ELit 16] (PRun [0x9f5f4] (PRun [0x9f670] (PBranch (PRun [0x9f690] (PFact (KRange (esub (esub E I) (eaddz O2 2)) 1 BUFMAX) (PRun [0x9f6b8] (PBranch (PRun [0x9f6c4] (PBranch (PRun [] (PFactLe (eaddz O2 3) (esub E I) BUFMAX (PBump 260 (PExt 100 [ELit 0; I; eaddz O2 3; ERJ; e_mtr; eaddz e_fb (-1)] (PFact (KRange (esub E I) 1 BUFMAX) (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PNextW [(119%nat, (EVar 264))])) (PRun [0x9f7dc] (PHandoff 3)))) (PRun [0x9f7dc] (PHandoff 3))))))))) (PRun [0x9f7dc] (PHandoff 3)))) (PRun [0x9f7dc] (PHandoff 3)))))) (PRun [0x9f7dc] (PHandoff 3))))))))) (PCaseReg 11 99 (PRun [0x9f5c4] (PExt 42 [] (PRun [0x9f7dc] (PHandoff 3)))) (PRespell 11 (ELit 100) (PRun [0x9f5d8] (PExt 46 [F; ELit 96; ELit 16] (PRun [0x9f5f4] (PRun [0xa06e8] (PBump 260 (PExt 102 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KL; eadd I O2; ELit 0; E; e_mtr; eaddz e_fb (-1)] (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PFactLe (eadd (eadd O2 KL) (EVar 260)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2 KL) (EVar 260))) 0 BUFMAX) (PNextW [(119%nat, (eadd (eadd O2 KL) (EVar 260)))])))) (PRun [0x9f7dc] (PHandoff 3)))) (PRun [0x9f7dc] (PHandoff 3))))))))))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x9f5c4] (PExt 42 [] (PRun [0x9f7dc] (PHandoff 3)))) (PRespell 11 (ELit 104) (PRun [0x9f5d8] (PExt 46 [F; ELit 96; ELit 16] (PRun [0x9f5f4] (PRun [0xa1268] (PBump 260 (PExt2 103 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KL; I; O2; E; e_mtr; eaddz e_fb (-1); SVJ] (PExt 47 [] (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PFactLe (eadd (eadd O2 KL) (EVar 260)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2 KL) (EVar 260))) 0 BUFMAX) (PNextW [(119%nat, (eadd (eadd O2 KL) (EVar 260)))])))) (PRun [0x9f7dc] (PHandoff 3)))) (PRun [0x9f7dc] (PHandoff 3))))) (PExt 47 [] (PExt 13 [EVar 263] (ladS (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PFactLe (eadd (eadd O2 KL) (EVar 260)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2 KL) (EVar 260))) 0 BUFMAX) (PHandoffW 2 [(100%nat, NV); (118%nat, eaddz (EVar 118) 1); (119%nat, (eadd (eadd O2 KL) (EVar 260)))])))) (PRun [0x9f7dc] (PHandoff 4)))) (PRun [0x9f7dc] (PHandoff 4))))))))))))))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [0x9f5d8] (PExt 46 [F; ELit 96; ELit 16] (PRun [0x9f5f4] (PRun [0x9fcdc] (PBump 260 (PExt 101 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KL; eadd I O2; ELit 0; E; e_mtr; eaddz e_fb (-1)] (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PFactLe (eadd (eadd O2 KL) (EVar 260)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2 KL) (EVar 260))) 0 BUFMAX) (PNextW [(119%nat, (eadd (eadd O2 KL) (EVar 260)))])))) (PRun [0x9f7dc] (PHandoff 3)))) (PRun [0x9f7dc] (PHandoff 3))))))))))) (PRun [0x9f5c4] (PExt 42 [] (PRun [0x9f7dc] (PHandoff 3)))))))) (PRun [0x9f7dc] (PHandoff 3)))) (PRun [0x9f580] (PBranch (PRun [0x9f7dc] (PHandoff 3)) (PRun [0x9f7dc] (PHandoff 3)))))))), PContraH 0)] [])).

Definition plan_L : plan :=
  (PLoopM 160 NC [(INV_LC, (PVia 2 J2LC 240 (PRun [0x9f3a8] (PExt 46 [F; ELit 64; ELit 8] (PCase2 (esub (esub E I) OKc) 0 (PRun [0x9f7dc] (PHandoff 4)) (PRun [0x9f3dc] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x9f558] (PMergeW 2 [(240%nat, (eaddz OKc (1)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub E I) OKc) 1 (PRun [0x9f7dc] (PHandoff 4)) (PRun [0x9f558] (PMergeW 2 [(240%nat, (eaddz OKc (2)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub E I) OKc) 3 (PRun [0x9f7dc] (PHandoff 4)) (PRun [0x9f558] (PMergeW 2 [(240%nat, (eaddz OKc (4)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub E I) OKc) 7 (PRun [0x9f7dc] (PHandoff 4)) (PRun [0x9f550] (PBranch (PRun [0x9f558] (PMergeW 2 [(240%nat, (eaddz OKc (8)))])) (PRun [0x9f7dc] (PHandoff 4)))))))))))) (PCase2 (esub (esub E I) O2c) 0 (PRun [0x9f7dc] (PHandoff 4)) (PCase2 KLc 0 (PRun [0x9f580] (PBranch (PRun [0x9f7dc] (PHandoff 4)) (PRun [0x9f7dc] (PHandoff 4)))) (PCase2 KLc 5 (PRun [0x9f580] (PBranch (PRun [0x9f5a8] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x9f5c4] (PExt 42 [] (PRun [0x9f7dc] (PHandoff 4)))) (PRespell 11 (ELit 97) (PRun [0x9f5d8] (PExt 46 [F; ELit 96; ELit 16] (PRun [0x9f5f4] (PRun [0x9f670] (PBranch (PRun [0x9f690] (PFact (KRange (esub (esub E I) (eaddz O2c 2)) 1 BUFMAX) (PRun [0x9f6b8] (PBranch (PRun [0x9f6c4] (PBranch (PRun [] (PFactLe (eaddz O2c 3) (esub E I) BUFMAX (PBump 300 (PExt 100 [ELit 0; I; eaddz O2c 3; ERKc; MTRKc; eaddz e_fb (-1)] (PFact (KRange (esub E I) 1 BUFMAX) (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PNextW [(161%nat, (EVar 304))])) (PRun [0x9f7dc] (PHandoff 4)))) (PRun [0x9f7dc] (PHandoff 4))))))))) (PRun [0x9f7dc] (PHandoff 4)))) (PRun [0x9f7dc] (PHandoff 4)))))) (PRun [0x9f7dc] (PHandoff 4))))))))) (PCaseReg 11 99 (PRun [0x9f5c4] (PExt 42 [] (PRun [0x9f7dc] (PHandoff 4)))) (PRespell 11 (ELit 100) (PRun [0x9f5d8] (PExt 46 [F; ELit 96; ELit 16] (PRun [0x9f5f4] (PRun [0xa06e8] (PBump 300 (PExt 102 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KLc; eadd I O2c; ELit 0; E; MTRKc; eaddz e_fb (-1)] (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PFactLe (eadd (eadd O2c KLc) (EVar 300)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2c KLc) (EVar 300))) 0 BUFMAX) (PNextW [(161%nat, (eadd (eadd O2c KLc) (EVar 300)))])))) (PRun [0x9f7dc] (PHandoff 4)))) (PRun [0x9f7dc] (PHandoff 4))))))))))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x9f5c4] (PExt 42 [] (PRun [0x9f7dc] (PHandoff 4)))) (PRespell 11 (ELit 104) (PRun [0x9f5d8] (PExt 46 [F; ELit 96; ELit 16] (PRun [0x9f5f4] (PRun [0xa1268] (PBump 300 (PExt2 113 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KLc; I; O2c; E; MTRKc; eaddz e_fb (-1); DKc; SKc; AKc] (PExt 47 [] (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PFactLe (eadd (eadd O2c KLc) (EVar 300)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2c KLc) (EVar 300))) 0 BUFMAX) (PNextW [(161%nat, (eadd (eadd O2c KLc) (EVar 300)))])))) (PRun [0x9f7dc] (PHandoff 4)))) (PRun [0x9f7dc] (PHandoff 4))))) (PExt 47 [] (PExt 13 [EVar 303] (ladL (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PFactLe (eadd (eadd O2c KLc) (EVar 300)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2c KLc) (EVar 300))) 0 BUFMAX) (PNextW [(161%nat, (eadd (eadd O2c KLc) (EVar 300)))])))) (PRun [0x9f7dc] (PHandoff 4)))) (PRun [0x9f7dc] (PHandoff 4))))))))))))))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [0x9f5d8] (PExt 46 [F; ELit 96; ELit 16] (PRun [0x9f5f4] (PRun [0x9fcdc] (PBump 300 (PExt 101 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KLc; eadd I O2c; ELit 0; E; MTRKc; eaddz e_fb (-1)] (PRun [0x9f6f4] (PBranch (PRun [0x9f6fc] (PBranch (PRun [0x9f3a4] (PFactLe (eadd (eadd O2c KLc) (EVar 300)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2c KLc) (EVar 300))) 0 BUFMAX) (PNextW [(161%nat, (eadd (eadd O2c KLc) (EVar 300)))])))) (PRun [0x9f7dc] (PHandoff 4)))) (PRun [0x9f7dc] (PHandoff 4))))))))))) (PRun [0x9f5c4] (PExt 42 [] (PRun [0x9f7dc] (PHandoff 4)))))))) (PRun [0x9f7dc] (PHandoff 4)))) (PRun [0x9f580] (PBranch (PRun [0x9f7dc] (PHandoff 4)) (PRun [0x9f7dc] (PHandoff 4)))))))), PContraH 1)] []).

Definition CUTS : list (acs * plan) := [(TL, plan_L); (XS, plan_exit 0); (XL, plan_exit 1)].   (* [comment removed for export] *)
Lemma gplan_top : gplan_ok plan_top = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_L : gplan_ok plan_L = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_X0 : gplan_ok (plan_exit 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_X1 : gplan_ok (plan_exit 1) = true. Proof. vm_compute. reflexivity. Qed.
End GaFMSPlan.
Module GaFMSCertTop.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaFMST GaFMS GaFMSPlan.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma top : check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUEL None (ce_tin ce) plan_top = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End GaFMSCertTop.
Module GaFMSCertL.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaFMST GaFMS GaFMSPlan.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma cutL : check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS 1) 0%nat BFUEL FUEL None TL plan_L = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cutXS : check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS 2) 0%nat BFUEL FUEL None XS (plan_exit 0) = COk (SHole 0).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cutXL : check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS 3) 0%nat BFUEL FUEL None XL (plan_exit 1) = COk (SHole 1).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
End GaFMSCertL.
Module GaFMSI.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaFMSL.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition plan_lam : plan :=
  (PCase2 KLN 1 (PRun [0x9fd68] (PBranch (PCase2 (esub EE IT0) 0 (PRun [] (PHandoffW 0 [(43%nat, ELit 0)])) (PCase2 (esub (esub EE IT0) (ELit 1)) 0 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [0x9fe24] (PBranch (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 5)]))) (PRun [0x9feb0] (PCaseReg 6 0 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PCaseReg 6 1 (PRun [0x9fec0] (PCaseReg 5 6 (PCaseReg 5 2 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [] (PHandoffW 0 [(43%nat, ELit 2)]))) (PCaseReg 5 1 (PRespell 5 (ELit 1) (PRun [] (PHandoffW 0 [(43%nat, ELit 2)]))) (PRespell 5 (ELit 2) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))))) (PCaseReg 5 4 (PCaseReg 5 3 (PRespell 5 (ELit 3) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))) (PRespell 5 (ELit 4) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 3)]))))) (PCaseReg 5 5 (PRespell 5 (ELit 5) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 3)])))) (PRespell 5 (ELit 6) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])))))) (PCaseReg 5 10 (PCaseReg 5 8 (PCaseReg 5 7 (PRespell 5 (ELit 7) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))) (PRespell 5 (ELit 8) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 5)]))))) (PCaseReg 5 9 (PRespell 5 (ELit 9) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 5)])))) (PRespell 5 (ELit 10) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))))) (PCaseReg 5 12 (PCaseReg 5 11 (PRespell 5 (ELit 11) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))) (PRespell 5 (ELit 12) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 9)]))))) (PCaseReg 5 13 (PRespell 5 (ELit 13) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 9)])))) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))))))) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))))))))) (PRun [] (PHandoffW 0 [(43%nat, ELit 0)])))) (PRun [] (PHandoffW 0 [(43%nat, ELit 0)]))).

Lemma gplan : gplan_ok plan_lam = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert : check ASEGS IT_I AASAN NXF LIMIT ISP0 (XN IT_I NXF) XE0 XB0 (HSce ceI) 0%nat BFUEL FUEL None (ce_tin ceI) plan_lam = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End GaFMSI.
Module GaFMSD.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaFMSL.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition plan_lam : plan :=
  (PCase2 KLN 1 (PRun [0xa0774] (PBranch (PCase2 (esub EE IT0) 0 (PRun [] (PHandoffW 0 [(43%nat, ELit 0)])) (PCase2 (esub (esub EE IT0) (ELit 1)) 0 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [0xa0834] (PBranch (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 9)]))) (PRun [0xa08f0] (PCaseReg 6 0 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PCaseReg 6 1 (PRun [0xa0900] (PCaseReg 5 6 (PCaseReg 5 2 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [] (PHandoffW 0 [(43%nat, ELit 2)]))) (PCaseReg 5 1 (PRespell 5 (ELit 1) (PRun [] (PHandoffW 0 [(43%nat, ELit 2)]))) (PRespell 5 (ELit 2) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))))) (PCaseReg 5 4 (PCaseReg 5 3 (PRespell 5 (ELit 3) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))) (PRespell 5 (ELit 4) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 3)]))))) (PCaseReg 5 5 (PRespell 5 (ELit 5) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 3)])))) (PRespell 5 (ELit 6) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])))))) (PCaseReg 5 10 (PCaseReg 5 8 (PCaseReg 5 7 (PRespell 5 (ELit 7) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 5)])))) (PRespell 5 (ELit 8) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 5)]))))) (PCaseReg 5 9 (PRespell 5 (ELit 9) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 5)])))) (PRespell 5 (ELit 10) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))))) (PCaseReg 5 12 (PCaseReg 5 11 (PRespell 5 (ELit 11) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 9)])))) (PRespell 5 (ELit 12) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 9)]))))) (PCaseReg 5 13 (PRespell 5 (ELit 13) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(43%nat, ELit 1)])) (PRun [] (PHandoffW 0 [(43%nat, ELit 9)])))) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))))))) (PRun [] (PHandoffW 0 [(43%nat, ELit 1)]))))))))) (PRun [] (PHandoffW 0 [(43%nat, ELit 0)])))) (PRun [] (PHandoffW 0 [(43%nat, ELit 0)]))).

Lemma gplan : gplan_ok plan_lam = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert : check ASEGS IT_D AASAN NXF LIMIT ISP0 (XN IT_D NXF) XE0 XB0 (HSce ceD) 0%nat BFUEL FUEL None (ce_tin ceD) plan_lam = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End GaFMSD.
Module GaFMSLC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaFMSL.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.

Section CI.
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT_I -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT_I AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN 0 0.
Theorem lam_i_asan_callee : callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH ceI.
Proof.
  refine (contract_of_cert ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            ceI IT_I IT_I_ok LIMIT 0%nat BFUEL FUEL (XN IT_I NXF) _ GaFMSI.plan_lam _ GaFMSI.gplan GaFMSI.hshape GaFMSI.cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT_I IT_I_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_I_ok]).
Qed.
End CI.

Section CD.
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT_D -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT_D AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN 0 0.
Theorem lam_d_asan_callee : callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH ceD.
Proof.
  refine (contract_of_cert ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            ceD IT_D IT_D_ok LIMIT 0%nat BFUEL FUEL (XN IT_D NXF) _ GaFMSD.plan_lam _ GaFMSD.gplan GaFMSD.hshape GaFMSD.cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
    apply (XN_sound IT_D IT_D_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
    (apply GC_all; first [assumption | exact IT_D_ok]).
Qed.
End CD.
End Contract.
End GaFMSLC.
Module GaFMSHCertS.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.GaFMSH.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fj_JO : expr := EVar 120.
Definition fj_JN : expr := EVar 121.
Definition fj_steps : list (list dstep) :=
  [ [DHi KLN 4; DRun [0xa1364]; DBrF; DRun [0xa1370]; DBrF; DHi (esub EE IT0) 0; DRun [0xa1418]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa144c]; DRLo 16 1; DRLo 16 0; DRun [0xa15cc]];
    [DHi KLN 4; DRun [0xa1364]; DBrF; DRun [0xa1370]; DBrF; DHi (esub EE IT0) 0; DRun [0xa1418]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa144c]; DRLo 16 1; DRHi 16 0; DHi (esub (esub EE IT0) (ELit 1)) 1; DRun [0xa15cc]];
    [DHi KLN 4; DRun [0xa1364]; DBrF; DRun [0xa1370]; DBrF; DHi (esub EE IT0) 0; DRun [0xa1418]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa144c]; DRHi 16 1; DRLo 16 2; DHi (esub (esub EE IT0) (ELit 1)) 3; DRun [0xa15cc]];
    [DHi KLN 4; DRun [0xa1364]; DBrF; DRun [0xa1370]; DBrF; DHi (esub EE IT0) 0; DRun [0xa1418]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa144c]; DRHi 16 1; DRHi 16 2; DHi (esub (esub EE IT0) (ELit 1)) 7; DRun [0xa15c4]; DBrF; DRun [0xa15cc]] ].
Definition fj_state (l : list dstep) : acs := snd (dpath ASEGS IT AASAN (XN MS) (XB MS) BFUEL 44%nat (ce_tin (ce MS)) l 0).
Definition fj_kmem (K : kentry) (k : list kentry) : bool := existsb (APC.kentry_eqb K) k.
Definition fj_kcommon (s0 : acs) (ss : list acs) : list kentry := List.filter (fun K => forallb (fun s => fj_kmem K (kn s)) ss) (kn s0).
Fixpoint fj_regs (rs : list expr) (rss : list (list expr)) (i v : nat) (ov : list (nat * expr)) : list expr :=
  match rs with
  | [] => []
  | r :: rs' =>
      match find (fun p => Nat.eqb (fst p) i) ov with
      | Some (_, e) => e :: fj_regs rs' rss (Datatypes.S i) v ov
      | None =>
          if forallb (fun l => expr_eqb (nth i l (ELit 0)) r) rss then r :: fj_regs rs' rss (Datatypes.S i) v ov
          else EVar v :: fj_regs rs' rss (Datatypes.S i) (Datatypes.S v) ov
      end
  end.
Definition fj_JH : acs := Eval vm_compute in
  match map fj_state fj_steps with
  | s0 :: ss =>
      let regs := fj_regs (s_regs (a_ss s0)) (map (fun s => s_regs (a_ss s)) ss) 0%nat 122%nat [(18%nat, fj_JN); (16%nat, EVar 140)] in
      let kq := List.filter (fun K => match K with KWord (SA b 0) _ _ => negb (expr_eqb b Q) && kentry_vars_lt 44 K
                                                | _ => kentry_vars_lt 44 K end) (fj_kcommon s0 ss) in
      let kj := [KWord (SA Q 0) 8 (eadd IT0 fj_JO); KRange fj_JO 2 9; KRange (esub (esub EE IT0) fj_JO) 0 BUFMAX; KRange fj_JN 0 (2 ^ 48)] in
      with_ss s0 (mk_ss 0xa15cc regs (kj ++ kq) 150%nat)
  | [] => ce_tin (ce MS)
  end.

Definition plan_hello : plan :=
  (PCase2 KLN 4 (PRun [] (PHandoffW 0 [(44%nat, ELit 0)])) (PRun [0xa1364] (PBranch (PRun [0xa1370] (PBranch (PCase2 (esub EE IT0) 0 (PRun [] (PHandoffW 0 [(44%nat, ELit 0)])) (PRun [0xa1418] (PBranch (PCase2 (esub (esub EE IT0) (ELit 1)) 0 (PRun [] (PHandoffW 0 [(44%nat, ELit 1)])) (PRun [0xa144c] (PVia 1 fj_JH 120 (PCaseReg 16 1 (PCaseReg 16 0 (PRespell 16 (ELit 0) (PRun [0xa15cc] (PMergeW 1 [(120%nat, ELit 2)]))) (PRespell 16 (ELit 1) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [] (PHandoffW 0 [(44%nat, ELit 1)])) (PRun [0xa15cc] (PMergeW 1 [(120%nat, ELit 3)]))))) (PCaseReg 16 2 (PRespell 16 (ELit 2) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(44%nat, ELit 1)])) (PRun [0xa15cc] (PMergeW 1 [(120%nat, ELit 5)])))) (PRespell 16 (ELit 3) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(44%nat, ELit 1)])) (PRun [0xa15c4] (PBranch (PRun [0xa15cc] (PMergeW 1 [(120%nat, ELit 9)])) (PRun [] (PHandoffW 0 [(44%nat, ELit 9)])))))))) (PBump 150 (PFresh 18 0 None (PRun [0xa15f4] (PBranch (PFactLe (EVar 150) (esub (esub EE IT0) (EVar 120)) BUFMAX (PRun [] (PBump 200 (PExt2 102 (resize_args_S (EVar 43) e_mtr e_fb) (PFact (KRange (eaddz e_sp (-80)) (CEIL + RFRK) (HI47 - 80)) (PExt 47 [] (PRun [] (PCase2 (EVar 150) 0 (PExt 5 [] (PRun [] (PHandoffW 0 [(44%nat, (eadd (EVar 150) (EVar 120))); (47%nat, (EVar 150))]))) (PExt 5 [] (PRun [] (PHandoffW 0 [(44%nat, (eadd (EVar 150) (EVar 120))); (47%nat, (EVar 150))]))))))) (PFact (KRange (eaddz e_sp (-80)) (CEIL + RFRK) (HI47 - 80)) (PExt 47 [] (PRun [] (PCase2 (EVar 150) 0 (PExt 5 [] (PRun [] (PHandoffW 1 [(44%nat, (eadd (EVar 150) (EVar 120))); (46%nat, EVar 202); (47%nat, EVar 200); (48%nat, (EVar 150)); (49%nat, EVar 201)]))) (PExt 5 [] (PRun [] (PHandoffW 1 [(44%nat, (eadd (EVar 150) (EVar 120))); (46%nat, EVar 202); (47%nat, EVar 200); (48%nat, (EVar 150)); (49%nat, EVar 201)]))))))))))) (PRun [] (PHandoffW 0 [(44%nat, EVar 120)]))))))))) (PRun [] (PHandoffW 0 [(44%nat, ELit 0)]))))) (PRun [] (PHandoffW 0 [(44%nat, ELit 0)])))) (PRun [] (PHandoffW 0 [(44%nat, ELit 0)]))))).

Lemma gplan : gplan_ok plan_hello = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert : check ASEGS IT AASAN (ce_nxf (ce MS)) LIMIT ISP0 (XN MS) XE0 (XB MS) (HSce (ce MS)) 0%nat BFUEL FUEL None (ce_tin (ce MS)) plan_hello = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End GaFMSHCertS.
Module GaFMSHCertL.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.GaFMSH.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fj_JO : expr := EVar 120.
Definition fj_JN : expr := EVar 121.
Definition fj_steps : list (list dstep) :=
  [ [DHi KLN 4; DRun [0xa1364]; DBrF; DRun [0xa1370]; DBrF; DHi (esub EE IT0) 0; DRun [0xa1418]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa144c]; DRLo 16 1; DRLo 16 0; DRun [0xa15cc]];
    [DHi KLN 4; DRun [0xa1364]; DBrF; DRun [0xa1370]; DBrF; DHi (esub EE IT0) 0; DRun [0xa1418]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa144c]; DRLo 16 1; DRHi 16 0; DHi (esub (esub EE IT0) (ELit 1)) 1; DRun [0xa15cc]];
    [DHi KLN 4; DRun [0xa1364]; DBrF; DRun [0xa1370]; DBrF; DHi (esub EE IT0) 0; DRun [0xa1418]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa144c]; DRHi 16 1; DRLo 16 2; DHi (esub (esub EE IT0) (ELit 1)) 3; DRun [0xa15cc]];
    [DHi KLN 4; DRun [0xa1364]; DBrF; DRun [0xa1370]; DBrF; DHi (esub EE IT0) 0; DRun [0xa1418]; DBrF; DHi (esub (esub EE IT0) (ELit 1)) 0; DRun [0xa144c]; DRHi 16 1; DRHi 16 2; DHi (esub (esub EE IT0) (ELit 1)) 7; DRun [0xa15c4]; DBrF; DRun [0xa15cc]] ].
Definition fj_state (l : list dstep) : acs := snd (dpath ASEGS IT AASAN (XN ML) (XB ML) BFUEL 46%nat (ce_tin (ce ML)) l 0).
Definition fj_kmem (K : kentry) (k : list kentry) : bool := existsb (APC.kentry_eqb K) k.
Definition fj_kcommon (s0 : acs) (ss : list acs) : list kentry := List.filter (fun K => forallb (fun s => fj_kmem K (kn s)) ss) (kn s0).
Fixpoint fj_regs (rs : list expr) (rss : list (list expr)) (i v : nat) (ov : list (nat * expr)) : list expr :=
  match rs with
  | [] => []
  | r :: rs' =>
      match find (fun p => Nat.eqb (fst p) i) ov with
      | Some (_, e) => e :: fj_regs rs' rss (Datatypes.S i) v ov
      | None =>
          if forallb (fun l => expr_eqb (nth i l (ELit 0)) r) rss then r :: fj_regs rs' rss (Datatypes.S i) v ov
          else EVar v :: fj_regs rs' rss (Datatypes.S i) (Datatypes.S v) ov
      end
  end.
Definition fj_JH : acs := Eval vm_compute in
  match map fj_state fj_steps with
  | s0 :: ss =>
      let regs := fj_regs (s_regs (a_ss s0)) (map (fun s => s_regs (a_ss s)) ss) 0%nat 122%nat [(18%nat, fj_JN); (16%nat, EVar 140)] in
      let kq := List.filter (fun K => match K with KWord (SA b 0) _ _ => negb (expr_eqb b Q) && kentry_vars_lt 46 K
                                                | _ => kentry_vars_lt 46 K end) (fj_kcommon s0 ss) in
      let kj := [KWord (SA Q 0) 8 (eadd IT0 fj_JO); KRange fj_JO 2 9; KRange (esub (esub EE IT0) fj_JO) 0 BUFMAX; KRange fj_JN 0 (2 ^ 48)] in
      with_ss s0 (mk_ss 0xa15cc regs (kj ++ kq) 150%nat)
  | [] => ce_tin (ce ML)
  end.

Definition plan_hello : plan :=
  (PCase2 KLN 4 (PRun [] (PHandoffW 0 [(46%nat, ELit 0)])) (PRun [0xa1364] (PBranch (PRun [0xa1370] (PBranch (PCase2 (esub EE IT0) 0 (PRun [] (PHandoffW 0 [(46%nat, ELit 0)])) (PRun [0xa1418] (PBranch (PCase2 (esub (esub EE IT0) (ELit 1)) 0 (PRun [] (PHandoffW 0 [(46%nat, ELit 1)])) (PRun [0xa144c] (PVia 1 fj_JH 120 (PCaseReg 16 1 (PCaseReg 16 0 (PRespell 16 (ELit 0) (PRun [0xa15cc] (PMergeW 1 [(120%nat, ELit 2)]))) (PRespell 16 (ELit 1) (PCase2 (esub (esub EE IT0) (ELit 1)) 1 (PRun [] (PHandoffW 0 [(46%nat, ELit 1)])) (PRun [0xa15cc] (PMergeW 1 [(120%nat, ELit 3)]))))) (PCaseReg 16 2 (PRespell 16 (ELit 2) (PCase2 (esub (esub EE IT0) (ELit 1)) 3 (PRun [] (PHandoffW 0 [(46%nat, ELit 1)])) (PRun [0xa15cc] (PMergeW 1 [(120%nat, ELit 5)])))) (PRespell 16 (ELit 3) (PCase2 (esub (esub EE IT0) (ELit 1)) 7 (PRun [] (PHandoffW 0 [(46%nat, ELit 1)])) (PRun [0xa15c4] (PBranch (PRun [0xa15cc] (PMergeW 1 [(120%nat, ELit 9)])) (PRun [] (PHandoffW 0 [(46%nat, ELit 9)])))))))) (PBump 150 (PFresh 18 0 None (PRun [0xa15f4] (PBranch (PFactLe (EVar 150) (esub (esub EE IT0) (EVar 120)) BUFMAX (PRun [] (PBump 200 (PExt2 112 (resize_args_L (EVar 43) (EVar 44) (EVar 45) e_mtr e_fb) (PFact (KRange (eaddz e_sp (-80)) (CEIL + RFRK) (HI47 - 80)) (PExt 47 [] (PRun [] (PCase2 (EVar 150) 0 (PExt 5 [] (PRun [] (PHandoffW 0 [(46%nat, (eadd (EVar 150) (EVar 120))); (49%nat, EVar 43); (50%nat, (EVar 150)); (51%nat, EVar 45)]))) (PExt 5 [] (PRun [] (PHandoffW 0 [(46%nat, (eadd (EVar 150) (EVar 120))); (49%nat, EVar 43); (50%nat, (EVar 150)); (51%nat, EVar 45)]))))))) (PFact (KRange (eaddz e_sp (-80)) (CEIL + RFRK) (HI47 - 80)) (PExt 47 [] (PRun [] (PCase2 (EVar 150) 0 (PExt 5 [] (PRun [] (PHandoffW 1 [(46%nat, (eadd (EVar 150) (EVar 120))); (48%nat, EVar 202); (49%nat, EVar 200); (50%nat, (EVar 150)); (51%nat, EVar 201)]))) (PExt 5 [] (PRun [] (PHandoffW 1 [(46%nat, (eadd (EVar 150) (EVar 120))); (48%nat, EVar 202); (49%nat, EVar 200); (50%nat, (EVar 150)); (51%nat, EVar 201)]))))))))))) (PRun [] (PHandoffW 0 [(46%nat, EVar 120)]))))))))) (PRun [] (PHandoffW 0 [(46%nat, ELit 0)]))))) (PRun [] (PHandoffW 0 [(46%nat, ELit 0)])))) (PRun [] (PHandoffW 0 [(46%nat, ELit 0)]))))).

Lemma gplan : gplan_ok plan_hello = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert : check ASEGS IT AASAN (ce_nxf (ce ML)) LIMIT ISP0 (XN ML) XE0 (XB ML) (HSce (ce ML)) 0%nat BFUEL FUEL None (ce_tin (ce ML)) plan_hello = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End GaFMSHCertL.
Module GaFMSHC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.GaFMSH.

Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN bc cc.

Lemma hello_callee_gen : forall (m : smode) (p : plan),
  gplan_ok p = true ->
  check ASEGS IT AASAN (ce_nxf (ce m)) LIMIT ISP0 (XN m) XE0 (XB m) (HSce (ce m)) 0%nat BFUEL FUEL None (ce_tin (ce m)) p = COk (SHole 0) ->
  callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH (ce m).
Proof.
  intros m p HG CERT.
  refine (contract_of_cert_xb ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            (ce m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN m) _ (XB m) _ p _ HG hs0 CERT).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
    apply XNp_sound.
    refine (XNc_sound ASEGS IT AASAN asan_in_hull asan_hull_ok IT_ok (NXF m) [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
              asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XB.
    refine (XBc_sound0 ASEGS AASAN asan_in_hull asan_hull_ok (NXF m) [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
              asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2_resize _).
    intros id c' H. exact (CT2_resize_sound RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all id c' H).
Qed.

Theorem lam_hello_asan_callee_S : callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH (ce MS).
Proof. exact (hello_callee_gen MS GaFMSHCertS.plan_hello GaFMSHCertS.gplan GaFMSHCertS.cert). Qed.
Theorem lam_hello_asan_callee_L : callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH (ce ML).
Proof. exact (hello_callee_gen ML GaFMSHCertL.plan_hello GaFMSHCertL.gplan GaFMSHCertL.cert). Qed.
End Contract.
End GaFMSHC.
Module GaFMSC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaFMST GaFMS GaFMSPlan GaFMSCertTop GaFMSCertL.

Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma cuts_ok : forall i T k, nth_error CUTS i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
  check ASEGS IT AASAN (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh.
Proof.
  intros i T k H. destruct i as [|[|[|i]]]; [| | |destruct i; discriminate H].
  - injection H as <- <-. exists (SHole 1). split; [exact gplan_L|]. split; [reflexivity|]. exact GaFMSCertL.cutL.
  - injection H as <- <-. exists (SHole 0). split; [exact gplan_X0|]. split; [reflexivity|]. exact GaFMSCertL.cutXS.   (* [comment removed for export] *)
  - injection H as <- <-. exists (SHole 1). split; [exact gplan_X1|]. split; [reflexivity|]. exact GaFMSCertL.cutXL.
Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN bc cc.

Theorem from_my_struct_asan_callee : callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH ce.
Proof.
  refine (contract_of_cert_xb_cut ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL XN _ XB _ CUTS cuts_ok plan_top (SHole 0) gplan_top hs0 GaFMSCertTop.top).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
    apply XNp_sound. apply GaNumT.GaPw.XNw_sound.   (* [comment removed for export] *)
    refine (XNc_sound ASEGS IT AASAN asan_in_hull asan_hull_ok IT_ok NXF [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
              asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT _ _).
    + intros id ce' H. unfold CT in H.
      destruct (Nat.eqb id 100); [injection H as <-; exact (GaFAC.fa_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 101); [injection H as <-; exact (GaFMSLC.lam_i_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0))|].
      destruct (Nat.eqb id 102); [|discriminate H]. injection H as <-.
      exact (GaFMSLC.lam_d_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all _ _ 0 0)).
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XB.
    refine (XBc_sound0 ASEGS AASAN asan_in_hull asan_hull_ok NXF [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
              asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 _).
    intros id c' H. unfold CT2 in H.
    destruct (Nat.eqb id 103); [injection H as <-; exact (GaFMSHC.lam_hello_asan_callee_S RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
    destruct (Nat.eqb id 113); [|discriminate H]. injection H as <-.
    exact (GaFMSHC.lam_hello_asan_callee_L RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all).
Qed.
End Contract.
End GaFMSC.
Module GaReadC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaRead OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaReadCert.

Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN bc cc.

Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

Theorem read_asan_callee : callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH ce.
Proof.
  refine (contract_of_cert_xb ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL XN _ XB _ plan_read _ read_gplan hs0 read_cert).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XN.
    apply XNp_sound.
    refine (XNc_sound ASEGS IT AASAN asan_in_hull asan_hull_ok IT_ok NXF [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
              asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold XB.
    refine (XBc_sound0 ASEGS AASAN asan_in_hull asan_hull_ok NXF [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
              asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
              PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 _).
    intros id c' H. unfold CT2 in H. destruct (Nat.eqb id 101); [|discriminate H]. injection H as <-.
    exact (GaFMSC.from_my_struct_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all).
Qed.
End Contract.
End GaReadC.
Module GaReadEC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaRead OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaReadE.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN bc cc.

Theorem read_asan_callee_E : callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH RdE.ceE.
Proof.
  refine (contract_of_cert ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            RdE.ceE IT IT_ok LIMIT 0%nat BFUEL FUEL RdE.XNE _ RdE.plan_readE _ readE_gplan hs0 readE_cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold RdE.XNE.
  apply XNp_sound.
  refine (XNc_sound ASEGS IT AASAN asan_in_hull asan_hull_ok IT_ok RdE.NXFE [] GASAN 0 0 fx_ok SHC KCAP AINVH HP
            asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - apply GC_all; first [assumption | exact IT_ok].
Qed.
End Contract.
End GaReadEC.
Module GaStrCtorC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaStrCtor.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma cert : check ASEGS IT AASAN NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_ctor = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
Lemma gplan : gplan_ok plan_ctor = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN 0 0.

Theorem str_ctor_asan_callee : callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH ce.
Proof.
  refine (contract_of_cert ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_ctor _ gplan hshape cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_silent1 SHC KCAP AINVH HP PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GaStrCtorC.
Module GaVec.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaJT.
Export OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaVecT.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CtorP.
Import Ctor.
Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, 27%nat); (0x9db50, 39%nat); (0x9dc0c, 87%nat); (0x9dda0, 26%nat); (0x9def0, 32%nat)].
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition XN : nat -> list expr -> acs -> option acs := XNann NXF GASAN ANNOT (XNp (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CT0)).
Definition HEAD : Z := 0x9dc88.       (* [comment removed for export] *)
Definition DPATH := dpath ASEGS IT AASAN XN XB0 BFUEL.
Definition ST_first : acs := snd (DPATH 0%nat tin [DRun []; DExt 20 []; DRun []; DExt 8 []; DRun []; DExt 8 []; DRun [HEAD]] 0).
Definition ST_second : acs := snd (DPATH 0%nat ST_first [DRun [0x9dcc0]; DBrT; DRun [HEAD]] 0).
(* [comment removed for export] *)
Definition JV : nat := 90.  Definition J : expr := EVar 90.
Definition kn_loop : list kentry :=
  [ KRange J 0 SZHI; KRange (esub SZ J) 1 SZHI; KWord (SA V 0) 8 P; KWord (SA V 8) 8 P; KWord (SA V 16) 8 (eadd SZ P) ]
  ++ blkP P SZ ++ kn_fixed ++ stk_facts ++ [KShOk (SA e_sp (- FRS)) (ELit FRS)].
Definition INV_d : acs :=
  let ss := [ST_first; ST_second] in
  let rs := jregs (map (fun s => s_regs (a_ss s)) ss) 0 32 [(10%nat, eadd P J); (11%nat, eadd FIRST J); (12%nat, eadd P J); (20%nat, eadd FIRST J)] 90 91 in
  mkcsV [(P, SZ); (FIRST, SZ)] MTRX HEAD rs (jframe 144 ss 90 ++ kn_loop) (maxvar_regs rs 91).
Definition INV : acs := Eval vm_compute in INV_d.
Definition body : plan := PRun [0x9dcc0] (PCase2 (esub SZ J) 1 (PRun [] (PHandoff 0)) (PRun [HEAD] PNext)).
Definition plan_ctor : plan :=
  PRun [] (PExt 20 [] (PRun [] (PExt 8 [] (PRun [] (PExt 8 [] (PRun [HEAD] (PLoop JV SZ INV [] body (PContraH 0)))))))).

End CtorP.

Module PushP.
Import Push.
Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, 65%nat); (0x9e1f8, 120%nat); (0x9e3d8, 91%nat); (0x9def0, 32%nat); (0x9e158, 40%nat); (0x9dda0, 26%nat)].
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition XN : nat -> list expr -> acs -> option acs := XNann NXF GASAN ANNOT (XNp (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CT0)).
Definition XNE : nat -> list expr -> acs -> option acs := XNann NXFE GASAN ANNOT (XNp (XNc ASEGS IT AASAN NXFE GASAN BCAPE 1 CT0)).
(* [comment removed for export] *)
Definition tail_push (g : plan -> plan) : plan :=
  PRun [] (PExt 20 [] (PRun [] (PExt 8 [] (PRun [] (PExt 5 [] (PRun [] (PExt 8 [] (PRun [] (g (PExt 22 [] (PRun [] (PHandoff 0)))))))))))).
Definition plan_push : plan :=
  PCase2 SZ 1
    (PRun [] (PExt 20 [] (PRun [] (PExt 8 [] (PRun [] (PExt 5 [] (PRun [] (PExt 8 [] (PRun [] (PRespell 8 (eaddz P2 2) (PExt 22 [] (PRun [] (PHandoff 1)))))))))))))
    (tail_push (fun k => PFact (KRange (eaddz (eadd SZ P2) 1) PTRLO PTRHI) k)).
Definition plan_pushE : plan := PRun [] (PExt 20 [] (PRun [] (PExt 5 [] (PRun [] (PExt 8 [] (PRun [] (PHandoff 0))))))).


End PushP.
End GaVec.
Module GaVecCert.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaVec.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma ctor_cert : check ASEGS CtorP.IT AASAN Ctor.NXF LIMIT ISP0 CtorP.XN XE0 XB0 (HSce Ctor.ce) 0%nat BFUEL FUEL None (ce_tin Ctor.ce) CtorP.plan_ctor = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma ctor_gplan : gplan_ok CtorP.plan_ctor = true. Proof. vm_compute. reflexivity. Qed.
Lemma push_cert : check ASEGS PushP.IT AASAN Push.NXF LIMIT ISP0 PushP.XN XE0 XB0 (HSce Push.ce) 0%nat BFUEL FUEL None (ce_tin Push.ce) PushP.plan_push = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma push_gplan : gplan_ok PushP.plan_push = true. Proof. vm_compute. reflexivity. Qed.
Lemma pushE_cert : check ASEGS PushP.IT AASAN Push.NXFE LIMIT ISP0 PushP.XNE XE0 XB0 (HSce Push.ceE) 0%nat BFUEL FUEL None (ce_tin Push.ceE) PushP.plan_pushE = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma pushE_gplan : gplan_ok PushP.plan_pushE = true. Proof. vm_compute. reflexivity. Qed.
End GaVecCert.
Module GaVecC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn GaVec GaVecCert.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN bc cc.
Hypothesis HANN : h_annot_at ASEGS GASAN fx_ok AINVH RZ ANNOT.
Notation CC := (callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH).

Theorem vec_ctor_asan_callee : CC Ctor.ce.
Proof.
  refine (contract_of_cert ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            Ctor.ce CtorP.IT CtorP.IT_ok LIMIT 0%nat BFUEL FUEL CtorP.XN _ CtorP.plan_ctor _ ctor_gplan hs0 ctor_cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold CtorP.XN.
  refine (XNann_sound ASEGS [] GASAN fx_ok SHC AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            AASAN asan_A_img_hi asan_A_img_lo asan_in_hull KCAP Ctor.NXF FS0 UINV HUa ANNOT HANN _ _).
  apply XNp_sound.
  refine (XNc_sound ASEGS CtorP.IT AASAN asan_in_hull asan_hull_ok CtorP.IT_ok Ctor.NXF [] GASAN Ctor.BCAP Ctor.CCAP fx_ok SHC KCAP AINVH HP
            asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - apply GC_all; first [assumption | exact CtorP.IT_ok].
Qed.

(* [comment removed for export] *)
Theorem vec_push_asan_callee : CC Push.ce.
Proof.
  refine (contract_of_cert ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            Push.ce PushP.IT PushP.IT_ok LIMIT 0%nat BFUEL FUEL PushP.XN _ PushP.plan_push _ push_gplan hs1 push_cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold PushP.XN.
  refine (XNann_sound ASEGS [] GASAN fx_ok SHC AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            AASAN asan_A_img_hi asan_A_img_lo asan_in_hull KCAP Push.NXF FS0 UINV HUa ANNOT HANN _ _).
  apply XNp_sound.
  refine (XNc_sound ASEGS PushP.IT AASAN asan_in_hull asan_hull_ok PushP.IT_ok Push.NXF [] GASAN Push.BCAP Push.CCAP fx_ok SHC KCAP AINVH HP
            asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - apply GC_all; first [assumption | exact PushP.IT_ok].
Qed.
(* [comment removed for export] *)
Theorem vec_push_asan_callee_E : CC Push.ceE.
Proof.
  refine (contract_of_cert ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            Push.ceE PushP.IT PushP.IT_ok LIMIT 0%nat BFUEL FUEL PushP.XNE _ PushP.plan_pushE _ pushE_gplan hs0 pushE_cert).
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa. unfold PushP.XNE.
  refine (XNann_sound ASEGS [] GASAN fx_ok SHC AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            AASAN asan_A_img_hi asan_A_img_lo asan_in_hull KCAP Push.NXFE FS0 UINV HUa ANNOT HANN _ _).
  apply XNp_sound.
  refine (XNc_sound ASEGS PushP.IT AASAN asan_in_hull asan_hull_ok PushP.IT_ok Push.NXFE [] GASAN Push.BCAPE 1 fx_ok SHC KCAP AINVH HP
            asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT0 _ _).
  - intros id ce' H. discriminate H.
  - apply GC_all; first [assumption | exact PushP.IT_ok].
Qed.
End Contract.
End GaVecC.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT.GaDedup OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsFZ AsFZP.

Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GaBJCert.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.
Lemma cuts_ok : forall i T k, nth_error FuzzNP.CUTS i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
  check ASEGS FuzzNP.IT AASAN (ce_nxf FuzzN.ce) LIMIT ISP0 FuzzNP.XN XE0 FuzzNP.XB (HScut FuzzN.ce FuzzNP.CUTS (Datatypes.S i)) 0%nat BFUEL FuzzNP.FUELB None T k = COk sh.
Proof.
  intros i T k H.
  destruct i as [|[|[|[|[|[|[|i]]]]]]]; [| | | | | | |destruct i; discriminate H]; injection H as <- <-.
  - exists (SHole 3). split; [exact AsFZCertN0.gplan_AS|]. split; [reflexivity|]. exact AsFZCertN1.cut0.
  - exists (SHole 3). split; [exact AsFZCertN0.gplan_AL|]. split; [reflexivity|]. exact AsFZCertN2.cut1.
  - exists (SHole 4). split; [exact AsFZCertN0.gplan_J2|]. split; [reflexivity|]. exact AsFZCertN0.cut2.
  - exists (SHole 6). split; [exact AsFZCertN0.gplan_J30|]. split; [reflexivity|]. exact AsFZCertN3.cut3.
  - exists (SHole 7). split; [exact AsFZCertN0.gplan_J31|]. split; [reflexivity|]. exact AsFZCertN4.cut4.
  - exists (SHole 0). split; [exact AsFZCertN0.gplan_J4|]. split; [reflexivity|]. exact AsFZCertN0.cut5.
  - exists (SHole 0). split; [exact AsFZCertN0.gplan_J4|]. split; [reflexivity|]. exact AsFZCertN0.cut6.
Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 ASEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT ASEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops [] GASAN SHC AINVH.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV,
  itab_sound ASEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> Z.of_nat (length HIDF) + FTOPf <= FMIN ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts ASEGS IT AASAN NXF PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV_f [] GASAN AINVH PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf fx_ok UINV RZ GASAN bc cc.
Hypothesis HANN : h_annot_at ASEGS GASAN fx_ok AINVH RZ ANNOT.
Hypothesis HSF5 : h_setsh_at ASEGS GASAN fx_ok AINVH RZ SF5_ENTRY.
Notation CC := (callee_contract ASEGS [] GASAN fx_ok RZ SHC KCAP AINVH).

Lemma CTN_sound : forall id c, FuzzNP.CT id = Some c -> CC c.
Proof.
  intros id c H. unfold FuzzNP.CT in H.
  destruct (Nat.eqb id 110); [injection H as <-; exact (GaVecC.vec_ctor_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all HANN)|].
  destruct (Nat.eqb id 111); [injection H as <-; exact (GaStrCtorC.str_ctor_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all GaStrCtor.IT GaStrCtor.NXF 0 0))|].
  discriminate H.
Qed.
Lemma CT2N_sound : forall id c, FuzzNP.CT2 id = Some c -> CC (c2_merged c).
Proof.
  intros id c H. unfold FuzzNP.CT2 in H.
  destruct (Nat.eqb id 112); [injection H as <-; exact (GaReadC.read_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 113); [injection H as <-; exact (GaBJC.b2j_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 114); [injection H as <-; exact (GaVecC.vec_push_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all HANN)|].
  discriminate H.
Qed.
Lemma CTE_sound : forall id c, FuzzEP.CT id = Some c -> CC c.
Proof.
  intros id c H. unfold FuzzEP.CT in H.
  destruct (Nat.eqb id 111); [injection H as <-; exact (GaStrCtorC.str_ctor_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP (GC_all GaStrCtor.IT GaStrCtor.NXF 0 0))|].
  destruct (Nat.eqb id 115); [injection H as <-; exact (GaReadEC.read_asan_callee_E RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 116); [injection H as <-; exact (GaBJC.b2j_asan_callee_E RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  destruct (Nat.eqb id 117); [injection H as <-; exact (GaVecC.vec_push_asan_callee_E RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all HANN)|].
  discriminate H.
Qed.
Lemma CT2E_sound : forall id c, FuzzEP.CT2 id = Some c -> CC (c2_merged c).
Proof.
  intros id c H. unfold FuzzEP.CT2 in H.
  destruct (Nat.eqb id 112); [injection H as <-; exact (GaReadC.read_asan_callee RZ RZ_silent1 RZ_exit RZ_conseq SHC KCAP AINVH HP GC_all)|].
  discriminate H.
Qed.

(* [comment removed for export] *)
Ltac xn_stack IT IT_ok NXF BCAP CCAP CT CT_sound :=
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa;
  refine (XNsf5_sound ASEGS [] GASAN fx_ok SHC AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            AASAN asan_A_img_hi asan_A_img_lo KCAP NXF FS0 UINV HUa SF5_ENTRY HSF5 _ _);
  refine (XNann_sound ASEGS [] GASAN fx_ok SHC AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img RZ PERMf TOPf HID HIDF M0 B0 C0 FTOPf
            AASAN asan_A_img_hi asan_A_img_lo asan_in_hull KCAP NXF FS0 UINV HUa ANNOT HANN _ _);
  apply XNd_sound; apply XNp_sound;
  refine (XNc_sound ASEGS IT AASAN asan_in_hull asan_hull_ok IT_ok NXF [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
            asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT CT_sound _);
  apply GC_all; first [assumption | exact IT_ok].
Ltac xb_stack NXF BCAP CCAP CT2 CT2_sound :=
  intros PERMf TOPf HID HIDF M0 B0 C0 FTOPf FS0 UINV HB0 HC0 HBc HCc HFB HUa;
  exact (XBc_sound0 ASEGS AASAN asan_in_hull asan_hull_ok NXF [] GASAN BCAP CCAP fx_ok SHC KCAP AINVH HP
            asan_G_ro_img2 asan_G_img_al asan_G_img_shlo nil_SWIN_img asan_segs_out asan_A_img_hi asan_A_img_lo asan_segs_wx
            PERMf TOPf FS0 HID HIDF M0 B0 C0 HB0 HC0 HBc HCc FTOPf HFB UINV HUa RZ RZ_silent1 CT2 CT2_sound).

Theorem fz_asan_callee_N : CC AsDrvHooksA.AsFZ.ceN.
Proof.
  refine (contract_of_cert_xb_cut ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            FuzzN.ce FuzzNP.IT FuzzNP.IT_ok LIMIT 0%nat BFUEL FuzzNP.FUELB FuzzNP.XN _ FuzzNP.XB _ FuzzNP.CUTS cuts_ok FuzzNP.plan_top (SHole 1)
            AsFZCertN0.gplan_top hs1 AsFZCertN0.top).
  - unfold FuzzNP.XN. xn_stack FuzzNP.IT FuzzNP.IT_ok FuzzN.NXF FuzzN.BCAP FuzzN.CCAP FuzzNP.CT CTN_sound.
  - unfold FuzzNP.XB. xb_stack FuzzN.NXF FuzzN.BCAP FuzzN.CCAP FuzzNP.CT2 CT2N_sound.
Qed.

Theorem fz_asan_callee_E : CC AsDrvHooksA.AsFZ.ceE.
Proof.
  refine (contract_of_cert_xb ASEGS AASAN asan_in_hull asan_hull_ok [] GASAN fx_ok (RUN_sound_fx ASEGS) RZ RZ_silent1 RZ_exit RZ_conseq
            SHC KCAP AINVH HP asan_G_ro_img2 asan_G_img_al asan_G_img_shlo asan_A_img_hi asan_A_img_lo asan_segs_wx
            FuzzE.ce FuzzEP.IT FuzzEP.IT_ok LIMIT 0%nat BFUEL FuzzEP.FUELB FuzzEP.XN _ FuzzEP.XB _ FuzzEP.planE _ AsFZCertE.gplan_E hs0 AsFZCertE.certE).
  - unfold FuzzEP.XN. xn_stack FuzzEP.IT FuzzEP.IT_ok FuzzN.NXF FuzzE.BCAP FuzzE.CCAP FuzzEP.CT CTE_sound.
  - unfold FuzzEP.XB. xb_stack FuzzN.NXF FuzzE.BCAP FuzzE.CCAP FuzzEP.CT2 CT2E_sound.
Qed.
End Contract.
