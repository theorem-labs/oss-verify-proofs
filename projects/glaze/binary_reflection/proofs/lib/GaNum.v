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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.GaTc32 OSSVerify.Proofs.glaze.binary_reflection.lib.GaU32 OSSVerify.Proofs.glaze.binary_reflection.lib.GaI32 OSSVerify.Proofs.glaze.binary_reflection.lib.GaU64 OSSVerify.Proofs.glaze.binary_reflection.lib.GaI64 OSSVerify.Proofs.glaze.binary_reflection.lib.GaWFT OSSVerify.Proofs.glaze.binary_reflection.lib.GaWDT OSSVerify.Proofs.glaze.binary_reflection.lib.GaW16. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.GaTc32 OSSVerify.Proofs.glaze.binary_reflection.lib.GaU32 OSSVerify.Proofs.glaze.binary_reflection.lib.GaI32 OSSVerify.Proofs.glaze.binary_reflection.lib.GaU64 OSSVerify.Proofs.glaze.binary_reflection.lib.GaI64 OSSVerify.Proofs.glaze.binary_reflection.lib.GaWFT OSSVerify.Proofs.glaze.binary_reflection.lib.GaWDT OSSVerify.Proofs.glaze.binary_reflection.lib.GaW16.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GaNumT.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 130 then Some GaTc32.ce else if Nat.eqb id 132 then Some GaI32.ce else if Nat.eqb id 133 then Some GaU32.ce
  else if Nat.eqb id 134 then Some GaI64.ce else if Nat.eqb id 135 then Some GaU64.ce
  else if Nat.eqb id 136 then Some GaWFT.ce else if Nat.eqb id 137 then Some GaWDT.ce
  else if Nat.eqb id 142 then Some GaI32.ceS else if Nat.eqb id 143 then Some GaU32.ceS else None.
Definition B16 (B : Z) : Z := if is_int B then GaW16.B16I else GaW16.B16U.
Definition CT2w (B : Z) (id : nat) : option gcallee2 :=
  if Nat.eqb id 138 then Some (GaW16.ce2 ML (B16 B)) else if Nat.eqb id 139 then Some (GaW16.ce2 MS (B16 B)) else None.
Definition CT2 (B : Z) : nat -> option gcallee2 := ct2_or (CT2w B) CT2_resize.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNw (XNc ASEGS (IT B) AASAN NXF GASAN BCAP CCAP CT).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CT1 (B : Z) (id : nat) : option gcallee := if Nat.eqb id 148 then Some (GaW16.ceL1 (B16 B)) else CT id.
Definition XN1 (B : Z) : nat -> list expr -> acs -> option acs := XNw (XNc ASEGS (IT B) AASAN NXF GASAN BCAP CCAP (CT1 B)).
Definition XB (B : Z) : nat -> list expr -> acs -> option (acs * acs) := XBc ASEGS AASAN NXF GASAN BCAP CCAP (CT2 B).
Definition FUELN : nat := 4000.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RSZID (m : smode) : nat := match m with MS => 105%nat | ML => 115%nat end.
Definition RSZ (m : smode) (d s a : expr) : list expr :=
  match m with MS => resize_args_S d e_mtr e_fb | ML => resize_args_L d s a e_mtr e_fb end.
Definition B2 : nat := 130.           (* [comment removed for export] *)
Definition BMP : nat := 170.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition exitD (m : smode) (K : Z) (XI a : expr) : plan :=
  let it' := eaddz IT0 K in let cons' := esub it' INLO in
  PFactLe cons' (eadd (esub IT0 INLO) REM) INSZ
  (PFact (KRange ITO 1 (INSZ - K))                   (* [comment removed for export] *)
  (PFactLe XI (escale 24 cons') IXHI
  (PFactLe (esub (escale 24 cons') XI) (escale 24 cons') BIG
  (match m with                  (* [comment removed for export] *)
   | ML => PFactLe (capexpr XI it' INLO a) (eaddz (escale 104 cons') CAPK) CAPHI (PHandoffW 1 [(43%nat, ELit K)])
   | MS => PHandoffW 0 [(43%nat, ELit K)]
   end)))).
(* [comment removed for export] *)
Definition pre (k : plan) : plan := PRun [] (PExt 42 [] (PRun [] k)).
Definition ERRX (m : smode) : plan := PRun [] (PHandoffW (hole m) [(43%nat, ELit 0)]).      (* [comment removed for export] *)
Definition EXITERR (m : smode) : plan := pre (ERRX m).                                        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition grown (k : plan) : plan := PExt 13 [EVar B2] k.
(* [comment removed for export] *)
Definition NSZ (hr : Z) : expr := eaddz (escale 2 IX) (2 * hr).
(* [comment removed for export] *)
Definition MGROWN : expr := eadd e_mtr (EVar 132).
Definition PWK (m : smode) (hr : Z) (k : plan) : plan := PExt 49 [e_mtr; szin m; NSZ hr; CPW; ELit 1] k.    (* [comment removed for export] *)
Definition PWG (m : smode) (hr : Z) (k : plan) : plan := PExt 49 [e_mtr; szin m; NSZ hr; CPW; ELit 0] k.    (* [comment removed for export] *)
Definition diamond (m : smode) (hr : Z) (cont : smode -> expr -> expr -> expr -> expr -> plan) : plan :=
  match m with
  | ML => PBranch (cont ML D S A e_mtr)
                  (PRun [] (PBump B2 (PExt2 (RSZID ML) (RSZ ML D S A) (PWK ML hr (cont ML D (NSZ hr) A e_mtr)) (PWG ML hr (grown (cont ML (EVar 130) (NSZ hr) (EVar 131) MGROWN))))))
  | MS => if Z.leb 23 hr then PBump B2 (PExt2 (RSZID MS) (RSZ MS D D A) (PContraH 0) (PWG MS hr (grown (cont ML (EVar 130) (NSZ hr) (EVar 131) MGROWN))))
          else PBranch (cont MS D D A e_mtr)
                       (PRun [] (PBump B2 (PExt2 (RSZID MS) (RSZ MS D D A)
                                   (if Z.leb 12 hr then PContraH 0
                                    else PCase2 IX (11 - hr) (PWK MS hr (cont MS D (NSZ hr) A e_mtr)) PContra)   (* [comment removed for export] *)
                                   (PWG MS hr (grown (cont ML (EVar 130) (NSZ hr) (EVar 131) MGROWN))))))
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition JLO : nat := 121.
Definition D1 : expr := EVar 121.  Definition S1 : expr := EVar 122.  Definition A1 : expr := EVar 123.  Definition MTR1 : expr := EVar 124.
Definition JRS : nat := 125.        (* [comment removed for export] *)
Definition JNX : nat := 150.
Definition GROWMAXN : Z := kcost (2 * NBN + 8) + KFREE.
Definition roomJ (m : smode) (hr : Z) : list kentry :=
  match m with MS => [KRange (esub D1 IX) hr (2 ^ 40)] | ML => [KRange (esub S1 IX) hr (2 ^ 37)] end.
Definition sz1 (m : smode) : expr := match m with MS => D1 | ML => S1 end.
Definition mfacts1 (m : smode) : list kentry :=
  [ ] ++ pw_facts CPW (sz1 m) MTR1 ++ [ KRange (esub MTR1 e_mtr) 0 GROWMAXN; KRange MTR1 0 MTRJ ].
Definition mkcsJ (p : Z) (regs : list expr) (k : list kentry) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k JNX) [] 0 FRK 0 vis WS 0 e_sp FdStd false MTR1 [] e_fb.
(* [comment removed for export] *)
Definition csregs_ra : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Fixpoint ehas (lo hi : nat) (e : expr) : bool :=
  match e with
  | EVar n => (Nat.leb lo n && Nat.ltb n hi)%bool
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (ehas lo hi a || ehas lo hi b)%bool
  | EExt _ _ _ a => ehas lo hi a
  | _ => false
  end.
Definition ahas (lo hi : nat) (a : saddr) : bool := ehas lo hi (a_base a).
Definition khas (lo hi : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => ahas lo hi a || ehas lo hi v
  | KZero a n | KWr a n | KUnk a n | KShOk a n | KBlob a n _ | KFill a n _ => ahas lo hi a || ehas lo hi n
  | KImg _ _ => false
  | KAlign x _ | KRange x _ _ => ehas lo hi x
  | KDisj a1 n1 a2 n2 => ahas lo hi a1 || ehas lo hi n1 || ahas lo hi a2 || ehas lo hi n2
  | KFpc v l _ => ehas lo hi v || ehas lo hi l
  end%bool.
(* [comment removed for export] *)
Inductive jstep : Type := JD (d : dstep) | JB (n : nat).
Fixpoint jpath (B : Z) (cs : acs) (l : list jstep) : acs :=
  match l with
  | [] => cs
  | JD d :: r => match dgo ASEGS (IT B) AASAN (XN B) (XB B) BFUEL NXF cs d with Some c => jpath B c r | None => cs end
  | JB n :: r => match APC.node_bump cs n with Some c => jpath B c r | None => cs end
  end.
(* [comment removed for export] *)
Definition JSJ (r0 : acs) (J hr : Z) (m : smode) : acs :=
  mkcsJ J (sr_havoc (s_regs (a_ss r0)) csregs_ra JRS)
        (roomJ m hr ++ mfacts1 m ++ str m IX IT0 121 ++ filter (fun K => negb (khas 34 37 K)) (kn r0)) (vis m 121).
(* [comment removed for export] *)
Definition mrgJ (J : Z) : plan := PRun [J] (PMerge 1).
Definition diamondJ (m : smode) (hr J : Z) : plan :=
  match m with
  | ML => PBranch (mrgJ J) (PRun [] (PBump B2 (PExt2 (RSZID ML) (RSZ ML D S A) (PWK ML hr (mrgJ J)) (PWG ML hr (grown (mrgJ J))))))
  | MS => PBranch (mrgJ J)
                  (PRun [] (PBump B2 (PExt2 (RSZID MS) (RSZ MS D D A)
                              (if Z.leb 12 hr then PContraH 0 else PCase2 IX (11 - hr) (PWK MS hr (mrgJ J)) PContra)
                              (PWG MS hr (grown (mrgJ J))))))
  end.
(* [comment removed for export] *)
Definition tagsteps (k : Z) : list jstep := (if Z.eqb k 0 then [] else [JD (DHi TAGV (8 * k - 1))]) ++ [JD (DLo TAGV (8 * k + 7))].
Definition pre3 : list jstep := [JD (DRun []); JD (DExt 42 []); JD (DRun [])].
Definition intpre (B stpc K : Z) : list jstep := [JD (DHi REM (K - 1)); JD (DRun [at_ B stpc]); JB 120; JD (DExt 44 [ELit 10]); JD (DRun [])].
Definition armpre (B k : Z) : list jstep :=
  tagsteps k ++ pre3 ++
  match k with
  | 1 | 2 => [JD (DHi REM 0); JB 110; JD (DRun [])]
  | 5 => [JD (DHi REM 1); JB 110; JD (DRun [])]
  | 8 => [JD (DHi REM 3); JD (DRun [])]
  | 12 => [JD (DHi REM 7); JD (DRun [])]
  | 9 => intpre B 0x828 4 | 10 => intpre B 0x76c 4 | 13 => intpre B 0x498 8 | 14 => intpre B 0x390 8
  | _ => []
  end.
(* [comment removed for export] *)
Definition JR0 (B : Z) (m : smode) (k : Z) : Z * acs :=
  let s := jpath B (tin m B) (armpre B k) in let J := pc s + 4 in (J, set_kn (jpath B s [JD DBrF; JD (DRun [J])]) (kn s)).
  (* [comment removed for export] *)
Definition DARMS : list Z := [1; 2; 5; 8; 9; 10; 12; 13; 14].
Definition JR0_UL : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNU ML k)) DARMS.
Definition JR0_US : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNU MS k)) DARMS.
Definition JR0_IL : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNI ML k)) DARMS.
Definition JR0_IS : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNI MS k)) DARMS.
Definition JR0L (B : Z) (m : smode) : list (Z * (Z * acs)) :=
  if Z.eqb B BNU then match m with ML => JR0_UL | MS => JR0_US end else match m with ML => JR0_IL | MS => JR0_IS end.
Definition jr0 (B : Z) (m : smode) (k : Z) : Z * acs :=
  match find (fun p => Z.eqb (fst p) k) (JR0L B m) with Some (_, x) => x | None => (0, tin m B) end.
(* [comment removed for export] *)
Definition joinJ (B : Z) (m : smode) (k : Z) (hr : Z) (cont : smode -> expr -> expr -> expr -> expr -> plan) : plan :=
  (* [comment removed for export] *)
  match m with
  | MS => if Z.leb 23 hr then diamond m hr cont else
      PViaM 1 [(JSJ (snd (jr0 B MS k)) (fst (jr0 B MS k)) hr MS, cont MS D1 D1 A1 MTR1); (JSJ (snd (jr0 B MS k)) (fst (jr0 B MS k)) hr ML, cont ML D1 S1 A1 MTR1)]
              JLO (diamondJ MS hr (fst (jr0 B MS k)))
  | ML => PViaM 1 [(JSJ (snd (jr0 B ML k)) (fst (jr0 B ML k)) hr ML, cont ML D1 S1 A1 MTR1)] JLO (diamondJ ML hr (fst (jr0 B ML k)))
  end.

(* [comment removed for export] *)
Definition room (m : smode) (hr : Z) (s a : expr) (k : plan) : plan :=
  match m with ML => PFactVia (esub (escale 8 a) IX) (esub s IX) (hr + 1) (2 ^ 40) k | MS => k end.
(* [comment removed for export] *)
Definition bufx (m : smode) (d : expr) : expr := match m with ML => eadd d IX | MS => eadd (eaddz OBJ 1) IX end.
Definition bufimg (m : smode) (d a : expr) (w : Z) (k : plan) : plan :=
  let buf := bufx m d in
  let k' := PFact (img_apart buf 0 (ELit w)) (PFact (shmap_apart buf 0 (ELit w)) k) in   (* [comment removed for export] *)
  match m with ML => PFactLe buf (eaddz (eadd d (escale 8 a)) (- w)) (PTRHI - w) k' | MS => k' end.   (* [comment removed for export] *)

Section Arms.
Variable B : Z.
Definition o (x : Z) : Z := at_ B x.

(* [comment removed for export] *)
Definition VB0 : expr := EExt false 0 1 (EVar 112).
Definition VB1 : expr := EExt false 0 1 (EVar 115).
Definition HV : expr := EVar 120.
Definition X44 (r : Z) (k : plan) : plan := PExt 44 [ELit r] k.

(* [comment removed for export] *)
Definition i8_cont (m : smode) (d s a mtr : expr) : plan :=
  room m 8 s a (bufimg m d a 6 (PCase2 VB0 127
    (PRun [] (PBump BMP (PExt 130 [mtr; e_fb] (PRun [] (exitD m 1 (eadd IX (EVar 197)) a)))))
    (PRun [] (PBump BMP (PExt 130 [mtr; e_fb] (PRun [] (exitD m 1 (eaddz (eadd IX (EVar 197)) 1) a))))))).   (* [comment removed for export] *)
Definition arm_i8 (m : smode) : plan :=
  pre (PCase2 REM 0 (ERRX m) (PBump 110 (PRun [] (joinJ B m 1 8 i8_cont)))).
(* [comment removed for export] *)
Definition q8 : expr := EMd Instr.M_MULHU VB0 (ELit 0x28f5c28f5c28f5d).
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition u8_cont (m : smode) (d s a mtr : expr) : plan :=
  room m 8 s a (PCase2 VB0 9 (xl (xl (PRun [] (exitD m 1 (eaddz IX 1) a))))
               (PCase2 VB0 99 (xl (xl (PRun [] (exitD m 1 (eaddz IX 2) a))))
               (divfact VB0 q8 100 (zfact VB0 q8 100 (xl (PRun [] (exitD m 1 (eaddz IX 3) a))))))).
Definition arm_u8 (m : smode) : plan :=
  pre (PCase2 REM 0 (ERRX m) (PBump 110 (PRun [] (joinJ B m 2 8 u8_cont)))).
(* [comment removed for export] *)
Definition i16_cont (m : smode) (d s a mtr : expr) : plan :=
  room m 8 s a (bufimg m d a 6 (PCase2 VB1 127
    (PRun [] (PBump BMP (PExt 130 [mtr; e_fb] (PRun [] (exitD m 2 (eadd IX (EVar 197)) a)))))
    (PRun [] (PBump BMP (PExt 130 [mtr; e_fb] (PRun [] (exitD m 2 (eaddz (eadd IX (EVar 197)) 1) a))))))).
Definition arm_i16 (m : smode) : plan :=
  pre (PCase2 REM 1 (ERRX m) (PBump 110 (PRun [] (joinJ B m 5 8 i16_cont)))).
(* [comment removed for export] *)
Definition W16ARGS : list expr := [CPW; ELit 0; G; OBJ; ITO; REM; IX; D; S; A; ERR; INLO; PEND; PIT; PIX; e_mtr; e_fb].
Definition arm_u16 (m : smode) : plan :=
  pre (PBump BMP (PExt2 (match m with ML => 138%nat | MS => 139%nat end) W16ARGS
         (PRun [] (PHandoff 0)) (PRun [] (PExt 13 [EVar (BMP + 3)] (PHandoff 1))))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition int_cont (cid cidS : nat) (K hr w : Z) (m : smode) (d s a mtr : expr) : plan :=
  room m hr s a (PRun [] (bufimg m d a w (PBump BMP (PExt (match m with ML => cid | MS => cidS end)
                                         (match m with ML => [HV; a; s; d; IX; mtr; e_fb] | MS => [HV; ELit 0; s; ELit 0; IX; mtr; e_fb] end)
                                         (PRun [] (exitD m K (eadd IX (EVar 192)) a)))))).
Definition arm_int (k : Z) (stpc : Z) (cid cidS : nat) (K hr w : Z) (m : smode) : plan :=
  pre (PCase2 REM (K - 1) (ERRX m) (PRun [o stpc] (PBump 120 (X44 10 (PRun []
    (joinJ B m k hr (int_cont cid cidS K hr w))))))).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fp_args (cid : nat) (mtr : expr) : list expr := if Nat.eqb cid 137 then [ELit (g_tp GASAN); mtr; e_fb] else [mtr; e_fb].
Definition fp_cont (cid : nat) (K hr W ylo : Z) (mj : nat) (m : smode) (d s a mtr : expr) : plan :=
  let frw := SA e_sp (- FR - ylo) in
  let buf := bufx m d in
  room m hr s a
   (bufimg m d a W
    (PFact (KDisj (SA buf 0) (ELit W) frw (ELit ylo))
    ((match m with ML => PFact (KRange buf PTRLO (objhi W)) | MS => fun k => k end)   (* [comment removed for export] *)
    (PRun [] (PBump BMP (PExt cid (fp_args cid mtr) (PRun [] (exitD m K (eadd IX (EVar mj)) a)))))))).
Definition arm_fp (k : Z) (cid : nat) (K hr W ylo : Z) (mj : nat) (m : smode) : plan :=
  pre (PCase2 REM (K - 1) (ERRX m) (PRun [] (joinJ B m k hr (fp_cont cid K hr W ylo mj)))).

(* [comment removed for export] *)
Definition arm_of (m : smode) (k : Z) : plan :=
  match k with
  | 1 => arm_i8 m | 2 => arm_u8 m | 5 => arm_i16 m | 6 => arm_u16 m
  | 8 => arm_fp 8 136 4 21 GaWFT.K GaWFT.YLO 277 m | 9 => arm_int 9 0x828 132 142 4 16 11 m | 10 => arm_int 10 0x76c 133 143 4 16 10 m
  | 12 => arm_fp 12 137 8 38 GaWDT.K GaWDT.YLO 297 m | 13 => arm_int 13 0x498 134 134 8 24 20 m | 14 => arm_int 14 0x390 135 135 8 24 20 m
  | _ => EXITERR m
  end.


(* [comment removed for export] *)
Definition arm_u16L1 (m : smode) : plan :=
  pre (PBump BMP (PExt 148 W16ARGS (PRun [] (PExt 13 [EVar (BMP + 3)] (PHandoff 1))))).
Definition arm_ofL1 (m : smode) (k : Z) : plan :=
  match k with
  | 1 => arm_i8 m | 2 => arm_u8 m | 5 => arm_i16 m | 6 => arm_u16L1 m
  | 8 => arm_fp 8 136 4 21 GaWFT.K GaWFT.YLO 277 m | 9 => arm_int 9 0x828 132 142 4 16 11 m | 10 => arm_int 10 0x76c 133 143 4 16 10 m
  | 12 => arm_fp 12 137 8 38 GaWDT.K GaWDT.YLO 297 m | 13 => arm_int 13 0x498 134 134 8 24 20 m | 14 => arm_int 14 0x390 135 135 8 24 20 m
  | _ => EXITERR m
  end.

   (* [comment removed for export] *)
End Arms.



Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint classes_rng (arm : smode -> Z -> plan) (m : smode) (k : Z) (n : nat) : plan :=
  match n with
  | O => arm m k
  | Datatypes.S n' => PCase2 TAGV (8 * k + 7) (arm m k) (classes_rng arm m (k + 1) n')
  end.
(* [comment removed for export] *)
Definition QS : list (Z * nat) := [(0, 3%nat); (4, 3%nat); (8, 3%nat); (12, 3%nat); (16, 15%nat)].
Definition plan_top : plan :=
  PCase2 TAGV 31 (PHandoffW 2 []) (PCase2 TAGV 63 (PHandoffW 3 []) (PCase2 TAGV 95 (PHandoffW 4 []) (PCase2 TAGV 127 (PHandoffW 5 []) (PHandoffW 6 [])))).
Lemma top_gplan : gplan_ok plan_top = true. Proof. reflexivity. Qed.
Section Cuts.
Variable B : Z.
Variable m : smode.                                   (* [comment removed for export] *)
Variable CE : gcallee.                                (* [comment removed for export] *)
Variable XNV : nat -> list expr -> acs -> option acs. (* [comment removed for export] *)
Variable ARM : smode -> Z -> plan.                    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cutT (steps : list dstep) : acs := snd (dpath ASEGS (IT B) AASAN XNV (XB B) BFUEL (ce_nxf CE) (tin m B) steps 0).
(* [comment removed for export] *)
Definition cut_of (q : Z * nat) : acs * plan :=
  let lo := 8 * fst q in let hi := 8 * (fst q + Z.of_nat (snd q)) + 7 in
  (cutT ((if Z.eqb lo 0 then [] else [DHi TAGV (lo - 1)]) ++ (if Z.eqb hi 255 then [] else [DLo TAGV hi])), classes_rng ARM m (fst q) (snd q)).
Definition CUTS : list (acs * plan) := map cut_of QS.
Definition NCUTS : nat := 5.
Lemma CUTS_len : length CUTS = NCUTS. Proof. reflexivity. Qed.
Definition cut_stmt (i : nat) : Prop :=
  match nth_error CUTS i with
  | Some (T, k) => exists sh, gplan_ok k = true /\ holes_only sh = true /\
      check ASEGS (IT B) AASAN (ce_nxf CE) LIMIT ISP0 XNV XE0 (XB B) (HScut CE CUTS (Datatypes.S i)) 0%nat BFUEL FUELN None T k = COk sh
  | None => True
  end.
Definition cut_ok (i : nat) : bool :=
  match nth_error CUTS i with
  | Some (T, k) => match check ASEGS (IT B) AASAN (ce_nxf CE) LIMIT ISP0 XNV XE0 (XB B) (HScut CE CUTS (Datatypes.S i)) 0%nat BFUEL FUELN None T k with
                 | COk sh => (holes_only sh && gplan_ok k)%bool | _ => false end
  | None => false
  end.
Lemma cut_ok_sound : forall i, cut_ok i = true -> cut_stmt i.
Proof.
  intros i H. unfold cut_ok in H. unfold cut_stmt. destruct (nth_error CUTS i) as [[T k]|]; [|exact I].
  destruct (check ASEGS (IT B) AASAN (ce_nxf CE) LIMIT ISP0 XNV XE0 (XB B) (HScut CE CUTS (Datatypes.S i)) 0%nat BFUEL FUELN None T k) as [sh|c w cs]; try discriminate.
  apply andb_prop in H as [H1 H2]. exists sh. split; [exact H2|]. split; [exact H1|]. reflexivity.
Qed.
(* [comment removed for export] *)
Definition top_stmt : Prop :=
  check ASEGS (IT B) AASAN (ce_nxf CE) LIMIT ISP0 XNV XE0 (XB B) (HScut CE CUTS 0) 0%nat BFUEL FUELN None (ce_tin CE) plan_top = COk (SHole 2).
End Cuts.
