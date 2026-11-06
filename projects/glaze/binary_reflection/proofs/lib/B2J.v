(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallRec OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import Esc.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpAAT OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.GpNum.GpWAT.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export B2JT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module B2J.

(* [comment removed for export] *)
Definition AAcfg (k : nat) : GpAA.acfg :=
  nth k [GpNum.GpAAT.cfg_i8; GpNum.GpAAT.cfg_i16; GpNum.GpAAT.cfg_i32; GpNum.GpAAT.cfg_i64; GpNum.GpAAT.cfg_u8; GpNum.GpAAT.cfg_u16; GpNum.GpAAT.cfg_u32; GpNum.GpAAT.cfg_u64; GpNum.GpAAT.cfg_f32; GpNum.GpAAT.cfg_f64] GpNum.GpAAT.cfg_i8.
Definition WAcfg (k : nat) : GpWA.acfg :=
  nth k [GpNum.GpWAT.cfg_i8; GpNum.GpWAT.cfg_i16; GpNum.GpWAT.cfg_i32; GpNum.GpWAT.cfg_i64; GpNum.GpWAT.cfg_u8; GpNum.GpWAT.cfg_u16; GpNum.GpWAT.cfg_u32; GpNum.GpWAT.cfg_u64; GpNum.GpWAT.cfg_f32; GpNum.GpWAT.cfg_f64] GpNum.GpWAT.cfg_i8.
Definition AAL1 (c : GpAA.acfg) : gcallee := GCE GpAA.NXF (GpAA.tin c ML) [GpAA.tout c ML; GpAA.tout c ML] GpAA.BCAP GpAA.CCAP.
Definition WAL1 (c : GpWA.acfg) : gcallee := GCE GpWA.NXF (GpWA.tin c ML) [GpWA.tout c ML; GpWA.tout c ML] GpWA.BCAP GpWA.CCAP.
Definition NUML1 (B : Z) : gcallee := GCE GpNum.GpNumT.NXF (GpNum.GpNumT.tin ML B) [GpNum.GpNumT.tout ML B; GpNum.GpNumT.tout ML B] GpNum.GpNumT.BCAP GpNum.GpNumT.CCAP.
Definition CT0 (id : nat) : option gcallee :=
  match id with
  | 203%nat => Some Esc.ceL1 | 223%nat => Some (NUML1 GpNum.GpNumT.BNU) | 233%nat => Some (NUML1 GpNum.GpNumT.BNI)
  | _ => if (Nat.leb 310 id && Nat.ltb id 320)%bool then Some (AAL1 (AAcfg (id - 310)))
         else if (Nat.leb 330 id && Nat.ltb id 340)%bool then Some (WAL1 (WAcfg (id - 330))) else None
  end.
Definition CTs (id : nat) : option gcallee := if Nat.eqb id 213 then Some ceL1 else CT0 id.   (* [comment removed for export] *)
Definition XN (m : smode) : nat -> list expr -> acs -> option acs :=
  match m with
  | ML => XNr PSEGS IT APLAIN GPLAIN NXF BCAP CCAP 213 14 ceL1 CT0       (* [comment removed for export] *)
  | MS => XNc PSEGS IT APLAIN NXF GPLAIN BCAP CCAP CTs                  (* [comment removed for export] *)
  end.
Definition CT2 (id : nat) : option gcallee2 :=
  match id with
  | 200%nat => Some (Esc.ce2 MS) | 220%nat => Some (GpNum.GpNumT.ce2 MS GpNum.GpNumT.BNU) | 230%nat => Some (GpNum.GpNumT.ce2 MS GpNum.GpNumT.BNI)
  | _ => if (Nat.leb 300 id && Nat.ltb id 310)%bool then Some (GpAA.ce2 (AAcfg (id - 300)) MS)
         else if (Nat.leb 320 id && Nat.ltb id 330)%bool then Some (GpWA.ce2 (WAcfg (id - 320)) MS) else None
  end.
Definition XB (m : smode) : nat -> list expr -> acs -> option (acs * acs) :=
  match m with
  | MS => XBr PSEGS APLAIN GPLAIN NXF BCAP CCAP 14 210 (ce2 MS) CT2      (* [comment removed for export] *)
  | ML => XBc PSEGS APLAIN NXF GPLAIN BCAP CCAP CT2
  end.
Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 20000.
Definition BFUEL : nat := 1000.
Definition DPATH := dpath PSEGS IT APLAIN (XN ML) (XB ML) BFUEL.

(* [comment removed for export] *)
Definition frame : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-72)) 8 (EVar 22);
    KWord (SA e_sp (-80)) 8 (EVar 23); KWord (SA e_sp (-88)) 8 (EVar 24); KWord (SA e_sp (-96)) 8 (EVar 25);
    KWord (SA e_sp (-104)) 8 (EVar 26) ].
Definition TAGv : expr := EExt false 0 1 (EVar 39).          (* [comment removed for export] *)
Definition TAG7 : expr := EAlu Instr.ALU_AND TAGv (ELit 7).

(* [comment removed for export] *)
Definition hv_emit : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_emit (a0 : expr) (ss : list expr) (v : nat) : list expr :=
  let r := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
             2 (eaddz e_sp (- FR))) 8 (eaddz G 104)) 9 OBJ) 18 G) 19 (eaddz G 96)) 20 (eaddz G 88)) 10 a0 in
  let r := fold_left (fun r p => sr_upd r (fst p) (snd p)) (combine [21; 22; 23; 24; 25; 26; 27]%nat ss) r in
  sr_havoc r hv_emit v.
(* [comment removed for export] *)
Definition regs_free (ss : list expr) (v : nat) : list expr :=
  let r := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
             2 (eaddz e_sp (- FR))) 8 (eaddz G 104)) 9 OBJ) 18 G) 19 (eaddz G 96)) 20 (eaddz G 88) in
  let r := fold_left (fun r p => sr_upd r (fst p) (snd p)) (combine [21; 22; 23; 24; 25; 26; 27]%nat ss) r in
  sr_havoc r (10%nat :: hv_emit) v.
Definition room (m : smode) (req : expr) (v : nat) : list kentry :=
  match m with
  | MS => [KRange (esub (EVar v) req) 0 22]
  | ML => [KRange (esub (escale 8 (EVar (2 + v))) (eaddz req 1)) 0 (8 * AHI); KRange (esub (EVar (1 + v)) req) 0 (8 * AHI)]
  end.
(* [comment removed for export] *)
Definition JS_geng (psg : expr -> expr -> expr -> Z -> Z -> list kentry) (m : smode) (p : Z) (err ito ix a0 : expr) (k rlo : Z) (ss : list expr) (extra : list kentry) (v : nat) : acs :=
  mkcs p (regs_emit a0 ss (3 + v))
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; rel ito ix rlo] ++ extra
        ++ psg ito ix err k BIG ++ str m ix ito err v ++ kn_fixed)
       (18 + v)%nat (vis m v).
Definition JS_gen := JS_geng pos.
(* [comment removed for export] *)
Definition JS_emit0 (m : smode) (p : Z) (err ito ix req : expr) (k rlo : Z) (ss : list expr) (extra : list kentry) (v : nat) : acs :=
  JS_geng pos0 m p err ito ix ix k rlo ss (room m req v ++ extra) v.
Definition JS_emit (m : smode) (p : Z) (err ito ix req : expr) (k rlo : Z) (ss : list expr) (extra : list kentry) (v : nat) : acs :=
  JS_gen m p err ito ix ix k rlo ss (room m req v ++ extra) v.
(* [comment removed for export] *)
Definition TP : expr := ELit (g_tp GPLAIN).
Definition DUM : expr := ELit 0.
(* [comment removed for export] *)
Definition RSZ (m : smode) (v : nat) : list expr :=
  match m with MS => [ELit 0; EVar v] | ML => [ELit 1; EVar v; EVar (2 + v); EVar (1 + v)] end.
Definition ENSURE (j : nat) (m : smode) (sv : nat) (JS : smode -> acs) (lo : nat) (bpc back : Z) (k : smode -> plan) : plan :=
  PViaM j (match m with MS => [(JS MS, k MS); (JS ML, k ML)] | ML => [(JS ML, k ML)] end) lo
    (PRun [bpc] (PBranch
       (PRun [] (PExt2 31 (RSZ m sv) (PRun [back] (PMerge j)) (PRun [back] (PMerge j))))   (* [comment removed for export] *)
       (PRun [back] (PMerge j)))).                                                       (* [comment removed for export] *)
Definition EXIT (m : smode) : plan := PRun [] (PHandoffW (match m with MS => 0 | ML => 1 end) []).

(* [comment removed for export] *)
Definition SS0 : list expr := [DEPTH; EVar 21; TAGv].   (* [comment removed for export] *)
Definition JS_null (m : smode) := JS_emit0 m 0x30b4c (ELit 0) ITO IX (eaddz IX 4) 1 0 SS0 [] 60.
Definition JS_true (m : smode) := JS_emit0 m 0x30c64 (ELit 0) ITO IX (eaddz IX 4) 1 0 SS0 [] 60.
Definition JS_false (m : smode) := JS_emit0 m 0x307fc (ELit 0) ITO IX (eaddz IX 5) 1 0 SS0 [] 60.
(* [comment removed for export] *)
Definition tag0 (m : smode) : plan :=
  PRun [] (PBranchP
    (* [comment removed for export] *) (PRun [0x307ec] (PBranch
        (ENSURE 0 m 36 JS_false 60 0x307f4 0x307fc (fun mm => PRun [] (PExt 1 [] (EXIT mm))))     (* [comment removed for export] *)
        (ENSURE 0 m 36 JS_true 60 0x30c5c 0x30c64 EXIT)))
    (* [comment removed for export] *) (ENSURE 0 m 36 JS_null 60 0x30b44 0x30b4c EXIT)).

(* [comment removed for export] *)
Definition HL : expr := EVar 80.
     (* [comment removed for export] *)
Definition JS_hdr (m : smode) : acs :=
  mkcs 0x30de8 (regs_emit (eadd INLO (eadd (eaddz ITO 1) HL)) SS0 63)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange (EVar 67) 0 (2 ^ 50 + 3);
                  rel (eadd (eaddz ITO 1) HL) IX 48]
        ++ pos (eadd (eaddz ITO 1) HL) IX (ELit 0) 0 BIG ++ str m IX (eadd (eaddz ITO 1) HL) (ELit 0) 60 ++ kn_fixed)
       82%nat (vis m 60).
Definition NSTR : expr := EAlu Instr.ALU_SRL (EVar 67) (ELit 2).    (* [comment removed for export] *)
Definition ESC_ARGS (ito n ix : expr) (sv : nat) : list expr := [TP; DUM; ito; n; BSZ; ix; INLO; EVar sv; EVar (1 + sv); EVar (2 + sv)].
Definition ERR_EXIT (m : smode) : plan := EXIT m.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition after_esc (m : smode) : plan := PRun [] (PBranchP (EXIT m) (EXIT m)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition hdr_arm (m : smode) (hl : Z) : plan :=   (* [comment removed for export] *)
  PExt 42 [] (PRun [0x30840] (PBranch (ERR_EXIT m)
    (if Z.eqb hl 8 then PRun [0x30de0] (PBranch (ERR_EXIT m) (PRun [0x30de8] (PMergeW 2 [(80%nat, ELit hl)])))
     else PRun [0x30de8] (PMergeW 2 [(80%nat, ELit hl)])))).
(* [comment removed for export] *)
Definition CALL (m : smode) (idS idL : nat) (args : list expr) (k : smode -> plan) : plan :=
  match m with MS => PExt2 idS args (k MS) (k ML) | ML => PExt idL args (k ML) end.
Definition esc_call (m : smode) : plan :=
  PRun [0x30e00] (PBranch (ERR_EXIT m) (PRun [] (CALL m 200 203 (ESC_ARGS (eadd (eaddz ITO 1) HL) NSTR IX 60) after_esc))).
Definition tag2 (m : smode) : plan :=
  PRun [0x3081c] (PBranch (ERR_EXIT m)                                            (* [comment removed for export] *)
  (PViaM 2 (match m with MS => [(JS_hdr MS, esc_call MS); (JS_hdr ML, esc_call ML)] | ML => [(JS_hdr ML, esc_call ML)] end) 60
     (PRun [0x30838] (PCaseReg 12 0 (hdr_arm m 1) (PCaseReg 12 1 (hdr_arm m 2) (PCaseReg 12 2 (hdr_arm m 4) (hdr_arm m 8))))))).

(* [comment removed for export] *)
Definition NUM_ARGS (m : smode) (ito ix : expr) (sv : nat) : list expr :=
  [TP; DUM; DUM; DUM; ito; esub BSZ ito; ix] ++
  (match m with MS => [EVar sv; DUM; DUM] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end) ++ [ELit 0; INLO; TAGv].
Definition tag1 (m : smode) : plan := PRun [0x32810] (CALL m 220 223 (NUM_ARGS m (eaddz ITO 1) IX 36) EXIT).
(* [comment removed for export] *)
Definition tag7 (m : smode) : plan := EXIT m.
(* [comment removed for export] *)
Definition NVv : expr := EVar 81.
Definition SS5 (n : expr) : list expr := [DEPTH; n; TAGv].                      (* [comment removed for export] *)
Definition JS_ahdr (m : smode) : acs :=
  mkcs 0x30f0c (regs_free (SS5 NVv) 63)                                        (* [comment removed for export] *)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 0 (2 ^ 48);
                  rel (eadd (eaddz ITO 1) HL) IX 48]
        ++ pos (eadd (eaddz ITO 1) HL) IX (ELit 0) 0 BIG ++ str m IX (eadd (eaddz ITO 1) HL) (ELit 0) 60 ++ kn_fixed)
       82%nat (vis m 60).
Definition ahdr_arm (m : smode) (hl : Z) : plan :=
  PExt 42 [] (PRun [0x309fc] (PBranch (ERR_EXIT m)
    (if Z.eqb hl 8 then PRun [0x30f00] (PBranch (ERR_EXIT m) (PRun [0x30f0c] (PMergeW 5 [(80%nat, ELit hl)])))
     else PRun [0x30f0c] (PMergeW 5 [(80%nat, ELit hl)])))).
(* [comment removed for export] *)
Definition JS_lbr (m : smode) : acs :=      (* [comment removed for export] *)
  JS_emit m 0x30f40 (ELit 0) (eadd (eaddz ITO 1) HL) IX (eaddz IX 1) 0 48 (SS5 NVv) [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 0 (2 ^ 48)] 100.
(* [comment removed for export] *)
Definition J5 : expr := EVar 130.
Definition ITOJ : expr := EVar 131. Definition IXJ : expr := EVar 132.
Definition SSL (j : expr) : list expr := [eaddz DEPTH 1; esub NVv j; eaddz OBJ 1; ELit 1; ELit 44].   (* [comment removed for export] *)
Definition INV5 (m : smode) : acs :=
  mkcs 0x30f84 (regs_free (SSL J5) 136)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 1 (2 ^ 48);
                  KRange (esub NVv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 133 ++ kn_fixed)
       152%nat (vis m 133).
Definition SELF_ARGS (ito ix : expr) (sv : nat) : list expr :=
  [TP; DUM; DUM; DUM; ito; DUM; BSZ; ix; INLO; EVar sv; EVar (1 + sv); EVar (2 + sv)].
(* [comment removed for export] *)
Definition ITO2 : expr := EVar 200. Definition IX2 : expr := EVar 201.
Definition JS_elem (m : smode) : acs :=
  mkcs 0x30fac (regs_free (SSL J5) 205)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 1 (2 ^ 48);
                  KRange (esub NVv J5) 1 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange ITO2 0 INSZ; rel ITO2 IX2 48]
        ++ pos ITO2 IX2 (ELit 0) 0 BIG ++ strc m IX2 ITO2 (ELit 0) 202 ++ kn_fixed)
       221%nat (vis m 202).
(* [comment removed for export] *)
Definition JS_comma (m : smode) : acs :=
  JS_emit m 0x30fd4 (ELit 0) ITO2 IX2 (eaddz IX2 1) 0 48 (SSL J5)
          [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 1 (2 ^ 48); KRange (esub NVv J5) 2 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange ITO2 0 INSZ] 230.
(* [comment removed for export] *)
Definition ITOR : expr := EVar 260. Definition IXR : expr := EVar 261.
Definition JS_rbr (m : smode) : acs :=
  JS_emit m 0x32570 (ELit 0) ITOR IXR (eaddz IXR 1) 0 2 (map EVar (seq 262 7))          (* [comment removed for export] *)
          [KRange ITOR 0 INSZ; KRange ITO 0 (INSZ - 2)] 269.
(* [comment removed for export] *)
Definition ENSURE' (j : nat) (m : smode) (sv : nat) (JS : smode -> acs) (lo : nat) (bpc back : Z) (k : smode -> plan) : plan :=
  PViaM j (match m with MS => [(JS MS, k MS); (JS ML, k ML)] | ML => [(JS ML, k ML)] end) lo
    (PRun [bpc] (PBranch
       (PRun [back] (PMerge j))                                                          (* [comment removed for export] *)
       (PRun [] (PExt2 31 (RSZ m sv) (PRun [back] (PMerge j)) (PRun [back] (PMerge j)))))).  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENSUREL (j : nat) (m : smode) (sv : nat) (JS : smode -> acs) (lo : nat) (bpc back : Z) (k : smode -> plan) : plan :=
  PViaM j [(JS ML, k ML)] lo
    (PRun [bpc] (PBranch
       (PRun [] (PExt2 31 (RSZ m sv) (PRun [back] (PMerge j)) (PRun [back] (PMerge j))))
       (PRun [back] (PMerge j)))).
Definition ENSUREL' (j : nat) (m : smode) (sv : nat) (JS : smode -> acs) (lo : nat) (bpc back : Z) (k : smode -> plan) : plan :=
  PViaM j [(JS ML, k ML)] lo
    (PRun [bpc] (PBranch
       (PRun [back] (PMerge j))
       (PRun [] (PExt2 31 (RSZ m sv) (PRun [back] (PMerge j)) (PRun [back] (PMerge j)))))).
Definition close5 (m : smode) (sv : nat) : plan :=           (* [comment removed for export] *)
  ENSURE' 8 m sv JS_rbr 260 0x3256c 0x32570 EXIT.
Definition after_elem (m : smode) : plan :=                 (* [comment removed for export] *)
  PCase2 (esub NVv J5) 1
     (PRun [0x3256c] (close5 m 202))                                                    (* [comment removed for export] *)
     (ENSURE' 7 m 202 JS_comma 230 0x30fd0 0x30fd4 (fun m' => PRun [0x30f84] PNext)).  (* [comment removed for export] *)
Definition post_call (m : smode) : plan :=                  (* [comment removed for export] *)
  PRun [] (PBranchP (EXIT m) (PViaM 6 [(JS_elem m, n13 (JS_elem m) (after_elem m))] 200 (PRun [0x30fac] (PMerge 6)))).
Definition body5 (m : smode) : plan := PRun [ENTRY] (CALL m 210 213 (SELF_ARGS ITOJ IXJ 133) post_call).
Definition loop5 (m : smode) : plan :=
  PLoopM 130 NVv (match m with MS => [(INV5 MS, body5 MS, PContraH 0); (INV5 ML, body5 ML, PContraH 0)]
                              | ML => [(INV5 ML, body5 ML, PContraH 0)] end) [].
Definition after_lbr (m : smode) : plan :=                  (* [comment removed for export] *)
  PRun [0x30f70] (PBranch (PRun [0x30f84] (loop5 m)) (PRun [0x3256c] (close5 m 100))).
Definition tag5 (m : smode) : plan :=
  PRun [0x309d8] (PBranch (ERR_EXIT m)
  (PViaM 5 (match m with MS => [(JS_ahdr MS, ENSURE 4 MS 60 JS_lbr 100 0x30f38 0x30f40 after_lbr);
                                (JS_ahdr ML, ENSURE 4 ML 60 JS_lbr 100 0x30f38 0x30f40 after_lbr)]
                       | ML => [(JS_ahdr ML, ENSURE 4 ML 60 JS_lbr 100 0x30f38 0x30f40 after_lbr)] end) 60
     (PRun [0x309f4] (PCaseReg 12 0 (ahdr_arm m 1) (PCaseReg 12 1 (ahdr_arm m 2) (PCaseReg 12 2 (ahdr_arm m 4) (ahdr_arm m 8))))))).

(* [comment removed for export] *)
Definition HOLE (c : nat) (m : smode) : nat := (9 + 2 * c + match m with MS => 0 | ML => 1 end)%nat.
Definition GO (c : nat) (m : smode) : plan := PHandoffW (HOLE c m) [].
(* [comment removed for export] *)
Definition CPV (k : nat) : nat := (7 + k)%nat.   Definition CAB (k : nat) : nat := (10 + k)%nat.
Definition CKEY : nat := 13.  Definition CCOL : nat := 14.  Definition COVAL : nat := 15.  Definition COL : nat := 16.
Definition CQ1 : nat := 17.  Definition CNUM : nat := 18.  Definition CQ2 : nat := 19.  Definition CC2 : nat := 20.  Definition CNVAL : nat := 21.  Definition CNL : nat := 22.
Definition CCB1 : nat := 23.  Definition CCB2 : nat := 24.  Definition CCB3 : nat := 25.  Definition CCB4 : nat := 26.  Definition CCB5 : nat := 27.  Definition CCL : nat := 28.
Definition CPW : nat := 29.
Inductive lmode := LMS | LMT | LML.   (* [comment removed for export] *)
Definition lmo (m : smode) : lmode := match m with MS => LMS | ML => LML end.
(* [comment removed for export] *)
Definition kS (lm : lmode) (c : nat) (k : smode -> plan) (m' : smode) : plan :=
  match lm, m' with LMS, ML | LMT, ML => GO c ML | _, _ => k m' end.
(* [comment removed for export] *)
Fixpoint assocn (l : list (nat * expr)) (i : nat) : option expr :=
  match l with [] => None | (j, x) :: r => if Nat.eqb i j then Some x else assocn r i end.
Fixpoint bregs (fixed : list (nat * expr)) (i n v : nat) : list expr :=
  match n with
  | O => []
  | Datatypes.S n' => match assocn fixed i with
                      | Some e => e :: bregs fixed (Datatypes.S i) n' v
                      | None => EVar v :: bregs fixed (Datatypes.S i) n' (Datatypes.S v)
                      end
  end.
(* [comment removed for export] *)
Definition STDREGS : list (nat * expr) :=
  [(0, ELit 0); (2, eaddz e_sp (- FR)); (3, EVar 2); (4, TP); (8, eaddz G 104); (9, OBJ); (18, G); (19, eaddz G 96); (20, eaddz G 88)]%nat.
Definition mkregs (extra : list (nat * expr)) (v : nat) : list expr := bregs (STDREGS ++ extra) 0 32 v.
(* [comment removed for export] *)
Definition posK (ito ix err : expr) (k : Z) (ixhi : Z) : list kentry :=
  [ KWord (SA G 0) 4 err; KWord (SA G 96) 8 (eadd INLO ito); KRange ito 0 (INSZ - k); KRange (esub BSZ ito) k INSZ;
    KWord (SA G 104) 8 ix; KRange ix 0 ixhi; iixE ITO IX (ELit 0);
    KRange (esub ito ITO) 1 INSZ ].
Definition JS_lcb (m : smode) := JS_emit m 0x30a24 (ELit 0) (eaddz ITO 1) IX (eaddz IX 1) 0 24 SS0 [] 60.

Definition TBL : expr := ELit 0x13210.
(* [comment removed for export] *)
Definition NFv : expr := EVar 81.
Definition SSo0 (nf : expr) : list (nat * expr) :=
  [(21, DEPTH); (22, EVar 21); (23, TBL); (24, nf); (25, EVar 24); (26, EVar 25); (27, EVar 26)]%nat.  (* [comment removed for export] *)
Definition ITO1 : expr := eadd (eaddz ITO 1) HL.      (* [comment removed for export] *)
Definition JS_ohdr (m : smode) : acs :=
  mkcs 0x318bc (mkregs (SSo0 NFv) 85)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 0 (2 ^ 48);
                  rel ITO1 (eaddz IX 1) 47]
        ++ pos ITO1 (eaddz IX 1) (ELit 0) 0 BIG ++ str m (eaddz IX 1) ITO1 (ELit 0) 82 ++ kn_fixed)
       110%nat (vis m 82).
(* [comment removed for export] *)
Definition HDR4r (r : nat) (m : smode) (ld chk chk8 jn : Z) (j hs : nat) : plan :=
  let arm (hl : Z) := PExt 42 [] (PRun [chk] (PBranch
       (if Z.eqb hl 8 then PRun [chk8] (PBranch (PRun [jn] (PMergeW j [(hs, ELit hl)])) (ERR_EXIT m))
        else PRun [jn] (PMergeW j [(hs, ELit hl)]))
       (ERR_EXIT m))) in
  PRun [ld] (PCaseReg r 0 (arm 1) (PCaseReg r 1 (arm 2) (PCaseReg r 2 (arm 4) (arm 8)))).
Definition HDR4 := HDR4r 12.
(* [comment removed for export] *)
Definition HDR4h (r : nat) (m : smode) (ld chk chk8 jn : Z) (h hs : nat) : plan :=
  let arm (hl : Z) := PExt 42 [] (PRun [chk] (PBranch
       (if Z.eqb hl 8 then PRun [chk8] (PBranch (PRun [jn] (PHandoffW h [(hs, ELit hl)])) (ERR_EXIT m))
        else PRun [jn] (PHandoffW h [(hs, ELit hl)]))
       (ERR_EXIT m))) in
  PRun [ld] (PCaseReg r 0 (arm 1) (PCaseReg r 1 (arm 2) (PCaseReg r 2 (arm 4) (arm 8)))).
(* [comment removed for export] *)
Definition SSo (j : expr) : list (nat * expr) :=
  [(21, eaddz DEPTH 1); (23, TBL); (24, esub NFv j); (25, eaddz OBJ 1); (26, ELit 1); (27, ELit 58)]%nat.
Definition kn_o : list kentry :=     (* [comment removed for export] *)
  frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 1 (2 ^ 48);
            KRange J5 0 (2 ^ 48)].
Definition INVo (m : smode) : acs :=
  mkcs 0x318e8 (mkregs (SSo J5) 136)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 133 ++ kn_fixed)
       160%nat (vis m 133).
(* [comment removed for export] *)
Definition HLK : expr := EVar 160. Definition KVv : expr := EVar 161.
Definition NK : expr := EAlu Instr.ALU_SRL KVv (ELit 2).
Definition ITOK : expr := eadd ITOJ HLK.
Definition JS_khdr (m : smode) : acs :=
  mkcs 0x319dc (mkregs (SSo J5 ++ [(10, eadd INLO ITOK); (11, KVv)])%nat 165)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 (INSZ - 1); KRange HLK 1 8; KRange KVv 0 (2 ^ 50 + 3);
                 KRange ITOK 0 INSZ; rel ITOK IXJ 71]
        ++ pos ITOK IXJ (ELit 0) 0 BIG ++ str m IXJ ITOK (ELit 0) 162 ++ kn_fixed)
       190%nat (vis m 162).
(* [comment removed for export] *)
Definition IXC : expr := EVar 221.
Definition relK (ix : expr) (lo : Z) : kentry :=
  KRange (eadd (esub (escale 24 (esub ITOK ITO)) (esub ix IX)) (escale 2 NK)) lo RELHI.
Definition kn_k : list kentry :=
  kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 (INSZ - 1); KRange HLK 1 8; KRange KVv 0 (2 ^ 50 + 3);
           KRange ITOK 0 INSZ; KRange (esub BSZ (eadd ITOK NK)) 0 INSZ].
Definition JS_key (m : smode) : acs :=
  mkcs 0x31a18 (mkregs (SSo J5 ++ [(22, NK)])%nat 225)
       (kn_k ++ [KRange IXC 0 IXHI2; relK IXC 69] ++ posK ITOK IXC (ELit 0) 0 IXHI2 ++ strc m IXC (eadd ITOK NK) (ELit 0) 222 ++ kn_fixed)
       242%nat (vis m 222).
(* [comment removed for export] *)
Definition JS_colon (m : smode) : acs :=
  mkcs 0x31a3c (mkregs (SSo J5 ++ [(10, IXC); (22, NK)])%nat 246)
       (kn_k ++ [KRange IXC 0 IXHI2; relK IXC 69] ++ room m (eaddz IXC 1) 243
        ++ posK ITOK IXC (ELit 0) 0 IXHI2 ++ str m IXC (eadd ITOK NK) (ELit 0) 243 ++ kn_fixed)
       262%nat (vis m 243).
(* [comment removed for export] *)
Definition ITOV : expr := EVar 285. Definition IXV : expr := EVar 286.
Definition JS_oval (m : smode) : acs :=
  mkcs 0x31a94 (mkregs (SSo J5) 290)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOV 0 INSZ; rel ITOV IXV 48]
        ++ pos ITOV IXV (ELit 0) 0 BIG ++ strc m IXV ITOV (ELit 0) 287 ++ kn_fixed)
       308%nat (vis m 287).
(* [comment removed for export] *)
Definition JS_ocomma (m : smode) : acs :=
  mkcs 0x31abc (mkregs (SSo J5 ++ [(10, IXV)])%nat 313)
       (kn_o ++ [KRange (esub NFv J5) 2 (2 ^ 48); KRange ITOV 0 INSZ; rel ITOV IXV 48] ++ room m (eaddz IXV 1) 310
        ++ pos ITOV IXV (ELit 0) 0 BIG ++ str m IXV ITOV (ELit 0) 310 ++ kn_fixed)
       330%nat (vis m 310).
(* [comment removed for export] *)
Definition ITOE : expr := EVar 340. Definition IXE : expr := EVar 341.
Definition JS_rcb (m : smode) : acs :=
  mkcs 0x31e40 (mkregs [(10%nat, IXE)] 345)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange ITO 0 (INSZ - 2); KRange ITOE 0 INSZ; rel ITOE IXE 2]
        ++ room m (eaddz IXE 1) 342
        ++ pos ITOE IXE (ELit 0) 0 BIG ++ str m IXE ITOE (ELit 0) 342 ++ kn_fixed)
       368%nat (vis m 342).
Definition closeo (m : smode) (sv : nat) : plan := ENSURE' 38 m sv JS_rcb 340 0x31e3c 0x31e40 EXIT.
Definition loop_end_o (lm : lmode) (m' : smode) : plan :=       (* [comment removed for export] *)
  match lm, m' with LML, _ => PRun [0x318e8] PNext | LMS, MS => PRun [0x318e8] PNext | _, _ => PRun [0x318e8] (GO COL ML) end.
Definition after_oval (lm : lmode) (m : smode) : plan :=                  (* [comment removed for export] *)
  PCase2 (esub NFv J5) 1
     (PRun [0x31e3c] (closeo m 287))                                                     (* [comment removed for export] *)
     (ENSURE' 37 m 287 JS_ocomma 310 0x31ab8 0x31abc (loop_end_o lm)).  (* [comment removed for export] *)
Definition post_oval (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x31a94] (GO COVAL ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 36 [(JS_oval m, n13 (JS_oval m) (after_oval lm m))] 285 (PRun [0x31a94] (PMerge 36))))
  end.
Definition after_colon (lm : lmode) (m : smode) : plan :=                 (* [comment removed for export] *)
  PRun [ENTRY] (PFact (iixE (eadd ITOK NK) (eaddz IXC 1) (ELit 0))         (* [comment removed for export] *)
               (PFact (KRange (eaddz IXC 1) 0 BIG)                             (* [comment removed for export] *)
               (CALL m 210 213 (SELF_ARGS (eadd ITOK NK) (eaddz IXC 1) 243) (post_oval lm)))).
Definition after_keyj (lm : lmode) (m : smode) : plan :=                  (* [comment removed for export] *)
  ENSURE' 35 m 222 JS_colon 243 0x31a38 0x31a3c (kS lm CCOL (after_colon lm)).
Definition after_key (lm : lmode) (m : smode) : plan :=                   (* [comment removed for export] *)
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x31a18] (GO CKEY ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 39 [(JS_key m, n13 (JS_key m) (after_keyj lm m))] 221 (PRun [0x31a18] (PMerge 39))))
  end.
Definition after_khdr (lm : lmode) (m : smode) : plan :=                  (* [comment removed for export] *)
  PRun [0x319f0] (PBranch
     (PRun [0x39a28] (CALL m 200 203 (ESC_ARGS ITOK NK IXJ 162) (after_key lm)))
     (ERR_EXIT m)).
Definition bodyo (lm : lmode) (m : smode) : plan :=
  PRun [0x318f0] (PBranch
    (PViaM 34 [(JS_khdr m, after_khdr lm m)] 160 (HDR4 m 0x31900 0x31908 0x319d8 0x319dc 34 160))
    (ERR_EXIT m)).
Definition loopo (m : smode) : plan :=      (* [comment removed for export] *)
  PLoopM 130 NFv [(INVo m, bodyo (lmo m) m, PContraH 0)] [].
Definition after_ohdr (m : smode) : plan :=                  (* [comment removed for export] *)
  PRun [0x318d4] (PBranch (PRun [0x318e8] (match m with MS => loopo MS | ML => GO COL ML end)) (PRun [0x31e3c] (closeo m 82))).
Definition P_HEADo : Z := 0x318e8.
Definition okeys_str (m : smode) : plan :=                   (* [comment removed for export] *)
  PRun [0x30c20] (PBranch (HDR4h 12 m 0x30c38 0x30c40 0x318b4 0x318bc (HOLE 0 m) 80) (ERR_EXIT m)).
(* [comment removed for export] *)
Definition SSn0 (nf : expr) : list (nat * expr) :=
  [(21, DEPTH); (22, nf); (23, TAGv); (24, EVar 23); (25, EVar 24); (26, EVar 25); (27, EVar 26)]%nat.
Definition JS_nhdr (m : smode) : acs :=
  mkcs 0x3123c (mkregs (SSn0 NFv) 85)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 0 (2 ^ 48);
                  rel ITO1 (eaddz IX 1) 47]
        ++ pos ITO1 (eaddz IX 1) (ELit 0) 0 BIG ++ str m (eaddz IX 1) ITO1 (ELit 0) 82 ++ kn_fixed)
       110%nat (vis m 82).
Definition SSn (j : expr) : list (nat * expr) :=
  [(21, eaddz DEPTH 1); (22, esub NFv j); (23, eaddz OBJ 1); (24, ELit 34); (25, ELit 58); (26, ELit 1); (27, ELit 44)]%nat.
Definition INVn (m : smode) : acs :=
  mkcs 0x31260 (mkregs (SSn J5) 136)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 1 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 133 ++ kn_fixed)
       160%nat (vis m 133).
(* [comment removed for export] *)
Definition JS_q1 (m : smode) : acs :=
  mkcs 0x31284 (mkregs (SSn J5 ++ [(10, IXJ)])%nat 163)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 1 INSZ; rel ITOJ IXJ 47] ++ room m (eaddz IXJ 1) 160
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 160 ++ kn_fixed)
       180%nat (vis m 160).
(* [comment removed for export] *)
Definition DIn : expr := EVar 205. Definition IXN : expr := EVar 206.
Definition ITON : expr := eadd ITOJ DIn.
Definition JS_num (m : smode) : acs :=
  mkcs 0x312d0 (mkregs (SSn J5) 210)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange DIn 0 8; KRange ITON 0 INSZ; KRange (esub ITON ITO) 1 INSZ; KRange IXN 0 BIG; rel ITON IXN 54]
        ++ pos ITON IXN (ELit 0) 0 BIG ++ strc m IXN ITON (ELit 0) 207 ++ kn_fixed)
       228%nat (vis m 207).
(* [comment removed for export] *)
Definition JS_q2 (m : smode) : acs :=
  mkcs 0x312f4 (mkregs (SSn J5 ++ [(10, IXN)])%nat 231)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange DIn 0 8; KRange ITON 0 INSZ; KRange (esub ITON ITO) 1 INSZ; KRange IXN 0 BIG; rel ITON IXN 54]
        ++ room m (eaddz IXN 1) 228
        ++ pos ITON IXN (ELit 0) 0 BIG ++ str m IXN ITON (ELit 0) 228 ++ kn_fixed)
       248%nat (vis m 228).
(* [comment removed for export] *)
Definition JS_c2 (m : smode) : acs :=
  mkcs 0x3133c (mkregs (SSn J5 ++ [(10, eaddz IXN 1)])%nat 251)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange DIn 0 8; KRange ITON 0 INSZ; KRange (esub ITON ITO) 1 INSZ; KRange IXN 0 BIG; rel ITON IXN 54]
        ++ room m (eaddz IXN 2) 248
        ++ pos ITON (eaddz IXN 1) (ELit 0) 0 BIG ++ str m (eaddz IXN 1) ITON (ELit 0) 248 ++ kn_fixed)
       268%nat (vis m 248).
(* [comment removed for export] *)
Definition ITOV2 : expr := EVar 290. Definition IXV2 : expr := EVar 291.
Definition JS_nval (m : smode) : acs :=
  mkcs 0x31388 (mkregs (SSn J5) 295)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOV2 0 INSZ; KRange (esub ITOV2 ITO) 1 INSZ; rel ITOV2 IXV2 48]
        ++ pos ITOV2 IXV2 (ELit 0) 0 BIG ++ strc m IXV2 ITOV2 (ELit 0) 292 ++ kn_fixed)
       313%nat (vis m 292).
Definition JS_ncomma (m : smode) : acs :=
  mkcs 0x313b0 (mkregs (SSn J5 ++ [(10, IXV2)])%nat 318)
       (kn_o ++ [KRange (esub NFv J5) 2 (2 ^ 48); KRange ITOV2 0 INSZ; KRange (esub ITOV2 ITO) 1 INSZ; rel ITOV2 IXV2 48] ++ room m (eaddz IXV2 1) 315
        ++ pos ITOV2 IXV2 (ELit 0) 0 BIG ++ str m IXV2 ITOV2 (ELit 0) 315 ++ kn_fixed)
       335%nat (vis m 315).
Definition loop_end_n (lm : lmode) (m' : smode) : plan :=
  match lm, m' with LML, _ => PRun [0x31260] PNext | LMS, MS => PRun [0x31260] PNext | _, _ => PRun [0x31260] (GO CNL ML) end.
Definition after_nval (lm : lmode) (m : smode) : plan :=
  PCase2 (esub NFv J5) 1
     (PRun [0x31e3c] (closeo m 292))
     (ENSURE' 47 m 292 JS_ncomma 315 0x313ac 0x313b0 (loop_end_n lm)).
Definition post_nval (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x31388] (GO CNVAL ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 46 [(JS_nval m, n13 (JS_nval m) (after_nval lm m))] 290 (PRun [0x31388] (PMerge 46))))
  end.
Definition after_c2 (lm : lmode) (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [ENTRY] (CALL m 210 213 (SELF_ARGS ITON (eaddz IXN 2) 248) (post_nval lm)).
Definition after_q2 (lm : lmode) (m : smode) : plan :=                    (* [comment removed for export] *)
  ENSURE' 45 m 228 JS_c2 248 0x31338 0x3133c (kS lm CC2 (after_c2 lm)).
Definition after_num (lm : lmode) (m : smode) : plan := ENSURE' 44 m 207 JS_q2 228 0x312f0 0x312f4 (kS lm CQ2 (after_q2 lm)).
Definition post_num (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x312d0] (GO CNUM ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 43 [(JS_num m, n13 (JS_num m) (after_num lm m))] 205 (PRun [0x312d0] (PMerge 43))))
  end.
Definition after_q1 (lm : lmode) (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [0x32810] (CALL m 220 223 (NUM_ARGS m ITOJ (eaddz IXJ 1) 160) (post_num lm)).
Definition bodyn (lm : lmode) (m : smode) : plan := ENSURE' 42 m 133 JS_q1 160 0x31280 0x31284 (kS lm CQ1 (after_q1 lm)).
Definition loopn (m : smode) : plan := PLoopM 130 NFv [(INVn m, bodyn (lmo m) m, PContraH 0)] [].
Definition after_nhdr (m : smode) : plan :=                  (* [comment removed for export] *)
  PRun [0x31244] (PBranch (PRun [0x31260] (match m with MS => loopn MS | ML => GO CNL ML end)) (PRun [0x31e3c] (closeo m 82))).
Definition P_HEADn : Z := 0x31260.
Definition okeys_num (m : smode) : plan :=                   (* [comment removed for export] *)
  PRun [0x30a84] (PBranch (HDR4h 12 m 0x30a9c 0x30aa4 0x31234 0x3123c (HOLE 1 m) 80) (ERR_EXIT m)).
Definition after_lcb (m : smode) : plan :=                   (* [comment removed for export] *)
  PRun [0x30a74] (PCaseReg 10 0 (PRun [0x30c14] (okeys_str m))
                 (PCaseReg 10 2 (PRun [0x30a78] (okeys_num m))
                                 (ERR_EXIT m))).
Definition tag3 (m : smode) : plan :=
  ENSURE 30 m 36 JS_lcb 60 0x30a1c 0x30a24 after_lcb.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition JX (m : smode) (p : Z) (ss : list (nat * expr)) (ito ix : expr) (rlo : Z) (rq : option expr)
              (extra : list kentry) (v : nat) : acs :=
  mkcs p (mkregs ss (3 + v))
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; rel ito ix rlo] ++ extra
        ++ match rq with Some r => room m r v | None => [] end
        ++ pos ito ix (ELit 0) 0 BIG ++ str m ix ito (ELit 0) v ++ kn_fixed)
       (3 + v + (32 - length STDREGS - length ss) + 1)%nat (vis m v).
(* [comment removed for export] *)
Definition JXc (m : smode) (p : Z) (ss : list (nat * expr)) (ito ix : expr) (rlo : Z) (rq : option expr)
              (extra : list kentry) (v : nat) : acs :=
  mkcs p (mkregs ss (3 + v))
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; rel ito ix rlo] ++ extra
        ++ match rq with Some r => room m r v | None => [] end
        ++ pos ito ix (ELit 0) 0 BIG ++ strc m ix ito (ELit 0) v ++ kn_fixed)
       (3 + v + (32 - length STDREGS - length ss) + 1)%nat (vis m v).
(* [comment removed for export] *)
Definition JS_rcbv (v : nat) (m : smode) : acs :=
  JX m 0x31e40 [(10%nat, EVar (1 + v))] (EVar v) (EVar (1 + v)) 2 (Some (eaddz (EVar (1 + v)) 1)) [KRange (EVar v) 0 INSZ] (2 + v).
Definition closev (j : nat) (v : nat) (m : smode) (sv : nat) : plan := ENSURE' j m sv (JS_rcbv v) v 0x31e3c 0x31e40 EXIT.
(* [comment removed for export] *)
Definition SS6 (s5 s6 : expr) : list (nat * expr) := [(21, s5); (22, s6); (23, TAGv); (24, EVar 23); (25, EVar 24); (26, EVar 25); (27, EVar 26)]%nat.
Definition JS_nl (m : smode) := JX m 0x3163c ((10%nat, IX) :: SS6 DEPTH (EVar 21)) (eaddz ITO 1) IX 24 (Some (eaddz IX 1)) [] 60.
Definition ext0 (m : smode) : plan := ENSURE 60 m 36 JS_nl 60 0x31634 0x3163c EXIT.
(* [comment removed for export] *)
Definition ext1 (m : smode) : plan :=
  let tarm (hl : Z) := PExt 42 [] (PRun [0x308cc] (PBranch (ERR_EXIT m)
                         (PRun [ENTRY] (CALL m 210 213 (SELF_ARGS (eaddz ITO (1 + hl)) IX 36) EXIT)))) in
  PRun [0x308a8] (PBranch (ERR_EXIT m)
    (PRun [0x308c4] (PCaseReg 13 0 (tarm 1) (PCaseReg 13 1 (tarm 2) (PCaseReg 13 2 (tarm 4) (tarm 8)))))).
(* [comment removed for export] *)
Definition HB : expr := EVar 59.     (* [comment removed for export] *)
Definition ITO2e : expr := eaddz ITO 2.
Definition JS_m0 (m : smode) := JX m 0x3109c ((10%nat, eadd INLO ITO) :: SS6 DEPTH HB) (eaddz ITO 1) IX 24 None [KRange HB 0 255; KRange (esub BSZ ITO) 2 INSZ] 61.
Definition JS_m1 (m : smode) := JX m 0x316ac ((10%nat, IX) :: SS6 DEPTH HB) ITO2e IX 48 (Some (eaddz IX 1)) [KRange HB 0 255] 90.
Definition JS_m2 (m : smode) := JX m 0x3170c ((10%nat, eaddz IX 1) :: SS6 DEPTH HB) ITO2e (eaddz IX 1) 47 (Some (eaddz IX 10)) [KRange HB 0 255] 120.
Definition JS_m3l (m : smode) := JX m 0x31770 ((10%nat, eaddz IX 10) :: SS6 DEPTH HB) ITO2e (eaddz IX 10) 38 (Some (eaddz IX 23)) [KRange HB 0 255] 160.
Definition JS_m3r (m : smode) := JX m 0x31790 ((10%nat, eaddz IX 10) :: SS6 DEPTH HB) ITO2e (eaddz IX 10) 38 (Some (eaddz IX 24)) [KRange HB 0 255] 160.
Definition LEN : expr := EVar 200.
Definition JS_m4 (m : smode) := JX m 0x31c44 ((10%nat, eadd (eaddz IX 10) LEN) :: SS6 DEPTH LEN) ITO2e (eadd (eaddz IX 10) LEN) 24 None [KRange LEN 13 14] 201.
Definition JS_m5 (m : smode) := JX m 0x31c64 ((10%nat, eadd (eaddz IX 10) LEN) :: SS6 DEPTH LEN) ITO2e (eadd (eaddz IX 10) LEN) 24 (Some (eadd (eaddz IX 11) LEN)) [KRange LEN 13 14] 230.
Definition JS_m6 (m : smode) := JX m 0x31cb4 ((10%nat, eadd (eaddz IX 11) LEN) :: SS6 DEPTH LEN) ITO2e (eadd (eaddz IX 11) LEN) 23 (Some (eadd (eaddz IX 21) LEN)) [KRange LEN 13 14] 260.
Definition ITOS1 : expr := EVar 330. Definition IXS1 : expr := EVar 331.
Definition JS_m7 (m : smode) := JXc m 0x31d14 (SS6 (eaddz DEPTH 1) LEN) ITOS1 IXS1 14 None [KRange LEN 13 14; KRange ITOS1 0 INSZ] 332.
Definition JS_m8 (m : smode) := JX m 0x31d38 ((10%nat, IXS1) :: SS6 (eaddz DEPTH 1) LEN) ITOS1 IXS1 14 (Some (eaddz IXS1 1)) [KRange LEN 13 14; KRange ITOS1 0 INSZ] 360.
Definition JS_m9 (m : smode) := JX m 0x31d88 ((10%nat, eaddz IXS1 1) :: SS6 (eaddz DEPTH 1) LEN) ITOS1 (eaddz IXS1 1) 13 (Some (eaddz IXS1 9)) [KRange LEN 13 14; KRange ITOS1 0 INSZ; KRange IXS1 0 BIG] 380.
Definition ITOS2 : expr := EVar 440. Definition IXS2 : expr := EVar 441.
Definition JS_m10 (m : smode) := JXc m 0x31e1c (SS6 (eaddz DEPTH 1) LEN) ITOS2 IXS2 5 None [KRange LEN 13 14; KRange ITOS2 0 INSZ] 442.
Definition after_m10 (m : smode) : plan := PRun [0x31e3c] (closev 71 470 m 442).
Definition post_m2 (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 70 [(JS_m10 m, n13 (JS_m10 m) (after_m10 m))] 440 (PRun [0x31e1c] (PMerge 70)))).
Definition after_m9 (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [ENTRY] (CALL m 210 213 (SELF_ARGS ITOS1 (eaddz IXS1 9) 380) post_m2).
Definition after_m8 (m : smode) : plan := ENSUREL' 69 m 360 JS_m9 380 0x31d84 0x31d88 after_m9.
Definition after_m7 (m : smode) : plan := ENSUREL' 68 m 332 JS_m8 360 0x31d34 0x31d38 after_m8.
Definition post_m1 (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 67 [(JS_m7 m, n13 (JS_m7 m) (after_m7 m))] 330 (PRun [0x31d14] (PMerge 67)))).
Definition after_m6 (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [0x6ec40] (PExt 1 [] (PRun [ENTRY] (CALL m 210 213 (SELF_ARGS ITO2e (eadd (eaddz IX 21) LEN) 260) post_m1))).
Definition after_m5 (m : smode) : plan := ENSUREL' 66 m 230 JS_m6 260 0x31cb0 0x31cb4 after_m6.
Definition after_m4 (m : smode) : plan := ENSUREL' 65 m 201 JS_m5 230 0x31c60 0x31c64 after_m5.
Definition after_m3 (len : Z) (m : smode) : plan :=          (* [comment removed for export] *)
  PRun [0x6ec40] (PExt 1 [] (PRun [0x31c44] (PMergeW 64 [(200%nat, ELit len)]))).
Definition after_m2 (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [0x6ec40] (PExt 1 [] (PViaM 64 [(JS_m4 ML, GO 6 ML)] 200
    (PRun [0x31760] (PBranch (ENSUREL 63 m 120 JS_m3l 160 0x31768 0x31770 (after_m3 13))
                             (ENSUREL 63 m 120 JS_m3r 160 0x31788 0x31790 (after_m3 14)))))).
Definition after_m1 (m : smode) : plan := ENSURE 62 m 90 JS_m2 120 0x31704 0x3170c after_m2.   (* [comment removed for export] *)
Definition after_m0 (m : smode) : plan := ENSURE 61 m 61 JS_m1 90 0x316a4 0x316ac after_m1.    (* [comment removed for export] *)
Definition ext2 (m : smode) : plan :=
  PRun [0x31094] (PBranch (PViaM 60 [(JS_m0 m, after_m0 m)] 59 (PRun [0x3109c] (PMerge 60))) (ERR_EXIT m)).
(* [comment removed for export] *)
Definition CB : expr := EVar 59.
Definition NTAG : expr := escale 32 (EAlu Instr.ALU_SRL CB (ELit 5)).   (* [comment removed for export] *)
Definition NUMI_ARGS (m : smode) (ito ix : expr) (sv : nat) : list expr :=
  [TP; DUM; DUM; DUM; ito; esub BSZ ito; ix] ++
  (match m with MS => [EVar sv; DUM; DUM] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end) ++ [ELit 0; INLO; NTAG].
Definition kn_x : list kentry := [KRange CB 0 255; KWord (SA e_sp (-176)) 4 NTAG].
Definition JS_x0 (m : smode) := JX m 0x30afc ((10%nat, eadd INLO ITO) :: (11%nat, CB) :: SS6 DEPTH (EVar 21)) (eaddz ITO 1) IX 24 None [KRange CB 0 255; KRange (esub BSZ ITO) 2 INSZ] 61.
Definition JS_x1 (m : smode) := JX m 0x31b90 ((10%nat, IX) :: SS6 DEPTH (EVar 21)) ITO2e IX 48 (Some (eaddz IX 1)) kn_x 90.
Definition ITOC1 : expr := EVar 140. Definition IXC1 : expr := EVar 141.
Definition JS_x2 (m : smode) := JXc m 0x31be4 (SS6 DEPTH (EVar 21)) ITOC1 IXC1 55 None (kn_x ++ [KRange ITOC1 0 INSZ; KRange (esub ITOC1 ITO) 2 INSZ]) 142.
Definition JS_x3 (m : smode) := JX m 0x31e6c ((10%nat, IXC1) :: SS6 DEPTH (EVar 21)) ITOC1 IXC1 55 (Some (eaddz IXC1 1)) (kn_x ++ [KRange ITOC1 0 INSZ; KRange (esub ITOC1 ITO) 2 INSZ]) 170.
Definition ITOC2 : expr := EVar 220. Definition IXC2 : expr := EVar 221.
Definition JS_x4 (m : smode) := JXc m 0x3254c (SS6 DEPTH (EVar 21)) ITOC2 IXC2 61 None [KRange ITOC2 0 INSZ; KRange (esub ITOC2 ITO) 2 INSZ] 222.
Definition post_x2 (m : smode) : plan :=                     (* [comment removed for export] *)
  PRun [] (PBranchP (EXIT m) (PViaM 83 [(JS_x4 m, n13 (JS_x4 m) (PRun [0x3256c] (close5 m 222)))] 220 (PRun [0x3254c] (PMerge 83)))).
Definition after_x3 (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [0x36330] (CALL m 230 233 (NUMI_ARGS m ITOC1 (eaddz IXC1 1) 170) post_x2).
Definition after_x2 (m : smode) : plan := ENSURE' 82 m 142 JS_x3 170 0x31e68 0x31e6c after_x3.
Definition post_x1 (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 81 [(JS_x2 m, n13 (JS_x2 m) (after_x2 m))] 140 (PRun [0x31be4] (PMerge 81)))).
Definition after_x1 (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [0x36330] (CALL m 230 233 (NUMI_ARGS m ITO2e (eaddz IX 1) 90) post_x1).
Definition cplx_single (m : smode) : plan := ENSURE' 80 m 61 JS_x1 90 0x31b8c 0x31b90 after_x1.
(* [comment removed for export] *)
Definition JS_rbrv (v : nat) (m : smode) : acs :=
  JS_emit m 0x32570 (ELit 0) (EVar v) (EVar (1 + v)) (eaddz (EVar (1 + v)) 1) 0 2 (map EVar (seq (2 + v) 7))
          [KRange (EVar v) 0 INSZ] (9 + v).
Definition close5v (j v : nat) (m : smode) (sv : nat) : plan := ENSURE' j m sv (JS_rbrv v) v 0x3256c 0x32570 EXIT.
(* [comment removed for export] *)
Definition NCv : expr := EVar 81.
Definition ITO2c : expr := eadd (eaddz ITO 2) HL.            (* [comment removed for export] *)
Definition JS_ca0 (m : smode) := JX m 0x3204c (SS6 NCv (EVar 21)) ITO2c IX 72 None (kn_x ++ [KRange HL 1 8; KRange NCv 0 (2 ^ 48)]) 82.
Definition JS_ca1 (m : smode) := JX m 0x32078 ((10%nat, IX) :: SS6 NCv (EVar 21)) ITO2c IX 72 (Some (eaddz IX 1)) (kn_x ++ [KRange HL 1 8; KRange NCv 0 (2 ^ 48)]) 104.
Definition SSc (j : expr) : list (nat * expr) :=
  [(21, esub NCv j); (22, ELit 91); (23, eaddz OBJ 1); (24, ELit 44); (25, ELit 93); (26, ELit 1); (27, EVar 26)]%nat.
Definition kn_ca : list kentry := kn_x ++ [KRange HL 1 8; KRange NCv 1 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange (esub NCv J5) 1 (2 ^ 48)].
Definition INVc (m : smode) : acs :=
  mkcs 0x320c0 (mkregs ((10%nat, IXJ) :: SSc J5) 136)       (* [comment removed for export] *)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255] ++ kn_ca ++ [KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 3 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 133 ++ kn_fixed)
       160%nat (vis m 133).
Definition JS_cb1 (m : smode) := JX m 0x320e0 ((10%nat, IXJ) :: SSc J5) ITOJ IXJ 47 (Some (eaddz IXJ 1)) (kn_ca ++ [KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 3 INSZ]) 160.
Definition DI1 : expr := EVar 205. Definition IXN1 : expr := EVar 206. Definition ITON1 : expr := eadd ITOJ DI1.
Definition kn_cb2 : list kentry := kn_ca ++ [KRange ITOJ 0 INSZ; KRange DI1 0 8; KRange ITON1 0 INSZ; KRange (esub ITON1 ITO) 3 INSZ; KRange IXN1 0 BIG].
Definition JS_cb2 (m : smode) := JXc m 0x3212c (SSc J5) ITON1 IXN1 54 None kn_cb2 207.
Definition JS_cb3 (m : smode) := JX m 0x32150 ((10%nat, IXN1) :: SSc J5) ITON1 IXN1 54 (Some (eaddz IXN1 1)) kn_cb2 228.
Definition DI2 : expr := EVar 270. Definition IXN2 : expr := EVar 271. Definition ITON2 : expr := eadd ITOJ DI2.
Definition kn_cb4 : list kentry := kn_ca ++ [KRange ITOJ 0 INSZ; KRange DI2 0 16; KRange ITON2 0 INSZ; KRange (esub ITON2 ITO) 3 INSZ; KRange IXN2 0 BIG].
Definition JS_cb4 (m : smode) := JXc m 0x3219c (SSc J5) ITON2 IXN2 61 None kn_cb4 272.
Definition JS_cb5 (m : smode) := JX m 0x321c0 ((10%nat, IXN2) :: SSc J5) ITON2 IXN2 61 (Some (eaddz IXN2 1)) kn_cb4 292.
Definition JS_cb6 (m : smode) := JX m 0x3220c ((10%nat, eaddz IXN2 1) :: SSc J5) ITON2 (eaddz IXN2 1) 60 (Some (eaddz IXN2 2))
                                    (kn_cb4 ++ [KRange (esub NCv J5) 2 (2 ^ 48)]) 315.
Definition loop_end_c (lm : lmode) (m' : smode) : plan :=
  match lm, m' with LML, _ => PRun [0x320c0] PNext | LMS, MS => PRun [0x320c0] PNext | _, _ => PRun [0x320c0] (GO CCL ML) end.
Definition after_cb5 (lm : lmode) (m : smode) : plan :=                   (* [comment removed for export] *)
  PCase2 (esub NCv J5) 1
     (PRun [0x3256c] (close5v 98 340 m 292))
     (ENSURE' 97 m 292 JS_cb6 315 0x32208 0x3220c (loop_end_c lm)).
Definition after_cb4 (lm : lmode) (m : smode) : plan := ENSURE' 96 m 272 JS_cb5 292 0x321bc 0x321c0 (kS lm CCB5 (after_cb5 lm)).
Definition post_cb2 (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x3219c] (GO CCB4 ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 95 [(JS_cb4 m, n13 (JS_cb4 m) (after_cb4 lm m))] 270 (PRun [0x3219c] (PMerge 95))))
  end.
Definition after_cb3 (lm : lmode) (m : smode) : plan :=                   (* [comment removed for export] *)
  PRun [0x36330] (CALL m 230 233 (NUMI_ARGS m ITON1 (eaddz IXN1 1) 228) (post_cb2 lm)).
Definition after_cb2 (lm : lmode) (m : smode) : plan := ENSURE' 94 m 207 JS_cb3 228 0x3214c 0x32150 (kS lm CCB3 (after_cb3 lm)).
Definition post_cb1 (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x3212c] (GO CCB2 ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 93 [(JS_cb2 m, n13 (JS_cb2 m) (after_cb2 lm m))] 205 (PRun [0x3212c] (PMerge 93))))
  end.
Definition after_cb1 (lm : lmode) (m : smode) : plan :=                   (* [comment removed for export] *)
  PRun [0x36330] (CALL m 230 233 (NUMI_ARGS m ITOJ (eaddz IXJ 1) 160) (post_cb1 lm)).
Definition bodyc (lm : lmode) (m : smode) : plan := ENSURE' 92 m 133 JS_cb1 160 0x320dc 0x320e0 (kS lm CCB1 (after_cb1 lm)).
Definition loopc (m : smode) : plan := PLoopM 130 NCv [(INVc m, bodyc (lmo m) m, PContraH 0)] [].
Definition after_ca1 (m : smode) : plan :=                   (* [comment removed for export] *)
  PRun [0x320a8] (PBranch (PRun [0x3256c] (close5v 91 340 m 104)) (PRun [0x320c0] (match m with MS => loopc MS | ML => GO CCL ML end))).
Definition P_HEADc : Z := 0x320c0.
Definition after_ca0 (m : smode) : plan := ENSURE' 90 m 82 JS_ca1 104 0x32074 0x32078 after_ca1.
Definition cplx_array (m : smode) : plan :=                  (* [comment removed for export] *)
  PRun [0x31668] (PBranch (HDR4h 13 m 0x31680 0x31688 0x32044 0x3204c (HOLE 5 m) 80) (ERR_EXIT m)).
Definition after_x0 (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [0x30b0c] (PBranch (PRun [0x31b8c] (cplx_single m)) (PRun [0x31660] (cplx_array m))).
Definition ext3 (m : smode) : plan :=
  PRun [0x30af0] (PBranch (ERR_EXIT m) (PViaM 79 [(JS_x0 m, after_x0 m)] 59 (PRun [0x30afc] (PMerge 79)))).
Definition tag6 (m : smode) : plan :=
  PRun [0x30888] (PCaseReg 11 0 (PRun [0x31064] (ext0 m)) (PCaseReg 11 1 (PRun [0x3089c] (ext1 m))
                 (PCaseReg 11 2 (PRun [0x31088] (ext2 m)) (PCaseReg 11 3 (PRun [0x30ae4] (ext3 m)) (ERR_EXIT m))))).

(* [comment removed for export] *)
Definition str3 (m : smode) (sv : nat) : list expr :=
  match m with MS => [EVar sv; DUM; DUM] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end.
Definition AA_ARGS (m : smode) (ito ix nv : expr) (sv : nat) : list expr :=
  [TP; DUM; G; OBJ; ito; esub BSZ ito; ix] ++ str3 m sv ++ [ELit 0; INLO; nv].
Definition WA_ARGS (m : smode) (ito ix : expr) (sv : nat) : list expr :=
  [TP; DUM; G; OBJ; ito; esub BSZ ito; ix] ++ str3 m sv ++ [ELit 0; INLO].
(* [comment removed for export] *)
Definition JS_rbre (v : nat) (m : smode) : acs :=
  mkcs 0x32570 (mkregs [(10%nat, EVar (1 + v))] (6 + v))
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange (EVar v) 0 INSZ; KRange (EVar (2 + v)) 0 24;
                  relE (EVar v) (EVar (1 + v)) (EVar (2 + v)) 2]
        ++ room m (eaddz (EVar (1 + v)) 1) (3 + v)
        ++ pos (EVar v) (EVar (1 + v)) (EVar (2 + v)) 0 BIG ++ str m (EVar (1 + v)) (EVar v) (EVar (2 + v)) (3 + v) ++ kn_fixed)
       (29 + v)%nat (vis m (3 + v)).
Definition closeE (j v : nat) (m : smode) (sv : nat) : plan := ENSURE' j m sv (JS_rbre v) v 0x3256c 0x32570 EXIT.
(* [comment removed for export] *)
Definition ITOW : expr := EVar 260. Definition IXW : expr := EVar 261. Definition ERW : expr := EVar 262.
Definition JS_pw (m : smode) : acs :=
  mkcs 0x3254c (mkregs [] 266)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange ITOW 0 INSZ; KRange ERW 0 24; relE ITOW IXW ERW 22]
        ++ pos ITOW IXW ERW 0 BIG ++ strc m IXW ITOW ERW 263 ++ kn_fixed)
       290%nat (vis m 263).
Definition cont_pw (m : smode) : plan := n13 (JS_pw m) (PRun [0x3256c] (closeE 102 290 m 263)).
Definition post_w (m : smode) : plan :=      (* [comment removed for export] *)
  match m with MS => PViaM 101 [(JS_pw MS, cont_pw MS)] 260 (PRun [0x3254c] (PMerge 101)) | ML => PRun [0x3254c] (GO CPW ML) end.
(* [comment removed for export] *)
Definition CLOp : list kentry :=
  [KWord (SA e_sp (-176)) 8 G; KWord (SA e_sp (-168)) 8 (eaddz G 96); KWord (SA e_sp (-160)) 8 (eaddz G 88);
   KWord (SA e_sp (-152)) 8 OBJ; KWord (SA e_sp (-144)) 8 (eaddz G 104)].

(* [comment removed for export] *)
Definition BCv : expr := EVar 59.
Definition SSp (bc : expr) : list (nat * expr) := [(21, TBL); (22, bc); (23, TAGv); (24, EVar 23); (25, EVar 24); (26, EVar 25); (27, EVar 26)]%nat.
Definition JS_p1 (m : smode) := JX m 0x30ca8 ((10%nat, IX) :: SSp BCv) (eaddz ITO 1) IX 24 (Some (eaddz IX 1)) (CLOp ++ [KRange BCv 1 128]) 60.
Definition callW (m : smode) (k : nat) : plan :=
  PRun [GpWA.c_entry (WAcfg k)] (CALL m (320 + k) (330 + k) (WA_ARGS m (eaddz ITO 1) (eaddz IX 1) 60) post_w).
Definition pvt0 (m : smode) : plan :=      (* [comment removed for export] *)
  PCaseReg 22 3 (ERR_EXIT m) (PCaseReg 22 4 (callW m 8) (PCaseReg 22 7 (ERR_EXIT m) (PCaseReg 22 8 (callW m 9) (ERR_EXIT m)))).
Definition pvt1 (m : smode) : plan :=      (* [comment removed for export] *)
  PCaseReg 22 1 (callW m 0) (PCaseReg 22 2 (callW m 1) (PCaseReg 22 3 (ERR_EXIT m) (PCaseReg 22 4 (callW m 2)
    (PCaseReg 22 7 (ERR_EXIT m) (PCaseReg 22 8 (callW m 3) (ERR_EXIT m)))))).
Definition pvt2 (m : smode) : plan :=      (* [comment removed for export] *)
  PCaseReg 22 1 (callW m 4) (PCaseReg 22 2 (callW m 5) (PCaseReg 22 3 (ERR_EXIT m) (PCaseReg 22 4 (callW m 6)
    (PCaseReg 22 7 (ERR_EXIT m) (PCaseReg 22 8 (callW m 7) (ERR_EXIT m)))))).
(* [comment removed for export] *)
Definition NSv : expr := EVar 81.
Definition JS_sa0 (m : smode) := JX m 0x32384 ([(21, TBL); (22, BCv); (23, NSv); (24, EVar 23); (25, EVar 24); (26, EVar 25); (27, EVar 26)]%nat)
                                    ITO1 (eaddz IX 1) 47 None (CLOp ++ [KRange BCv 1 128; KRange HL 1 8; KRange NSv 0 (2 ^ 48)]) 82.
Definition SSs (j : expr) : list (nat * expr) := [(21, TBL); (22, ELit (2 ^ 50 + 3)); (23, esub NSv j); (24, eaddz OBJ 1); (25, ELit 1); (27, ELit 2)]%nat.
Definition kn_s : list kentry := [KRange HL 1 8; KRange NSv 1 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange (esub NSv J5) 1 (2 ^ 48)].
Definition INVs (m : smode) : acs :=
  mkcs 0x323a4 (mkregs (SSs J5) 136)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255] ++ kn_s ++ [KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 2 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 133 ++ kn_fixed)
       160%nat (vis m 133).
Definition JS_sk (m : smode) := JX m 0x3248c ((10%nat, eadd INLO ITOK) :: (11%nat, KVv) :: SSs J5) ITOK IXJ 71 None
                                   (kn_s ++ [KRange ITOJ 0 (INSZ - 1); KRange (esub ITOJ ITO) 2 INSZ; KRange HLK 1 8; KRange KVv 0 (2 ^ 50 + 3); KRange ITOK 0 INSZ]) 162.
Definition kn_sk : list kentry := kn_s ++ [KRange ITOJ 0 (INSZ - 1); KRange (esub ITOJ ITO) 2 INSZ; KRange HLK 1 8; KRange KVv 0 (2 ^ 50 + 3);
                                           KRange ITOK 0 INSZ; KRange (esub BSZ (eadd ITOK NK)) 0 INSZ].
Definition JS_se (m : smode) : acs :=
  mkcs 0x324c8 (mkregs ((26%nat, NK) :: SSs J5) 225)      (* [comment removed for export] *)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255] ++ kn_sk ++ [KRange IXC 0 IXHI2; relK IXC 69]
        ++ posK ITOK IXC (ELit 0) 0 IXHI2 ++ strc m IXC (eadd ITOK NK) (ELit 0) 222 ++ kn_fixed)
       242%nat (vis m 222).
Definition JS_sc (m : smode) := JX m 0x324fc ((10%nat, IXC) :: (26%nat, NK) :: SSs J5) (eadd ITOK NK) IXC 68 (Some (eaddz IXC 1))
                                   (kn_sk ++ [KRange IXC 0 BIG; KRange (esub NSv J5) 2 (2 ^ 48)]) 243.
Definition after_se2 (m : smode) : plan :=                   (* [comment removed for export] *)
  PCase2 (esub NSv J5) 1
     (PRun [0x3256c] (closeE 111 250 m 222))
     (ENSURE' 108 m 222 JS_sc 243 0x324f8 0x324fc (fun m' => PRun [0x323a4] PNext)).
Definition after_se (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 107 [(JS_se m, n13 (JS_se m) (after_se2 m))] 220 (PRun [0x324c8] (PMerge 107)))).
Definition after_sk (m : smode) : plan :=
  PRun [0x324a0] (PBranch (PRun [0x39a28] (CALL m 200 203 (ESC_ARGS ITOK NK IXJ 162) after_se)) (ERR_EXIT m)).
Definition bodys (m : smode) : plan :=
  PRun [0x323ac] (PBranch (PViaM 106 [(JS_sk m, after_sk m)] 160 (HDR4 m 0x323bc 0x323c4 0x32488 0x3248c 106 160)) (ERR_EXIT m)).
Definition loops (m : smode) : plan :=
  PLoopM 130 NSv (match m with MS => [(INVs MS, bodys MS, PContraH 0); (INVs ML, bodys ML, PContraH 0)]
                              | ML => [(INVs ML, bodys ML, PContraH 0)] end) [].
Definition after_sa0 (m : smode) : plan :=
  PRun [0x3238c] (PBranch (PRun [0x323a4] (loops m)) (PRun [0x3256c] (closeE 110 120 m 82))).
Definition strarr (m : smode) : plan :=                      (* [comment removed for export] *)
  PRun [0x317f8] (PBranch (HDR4h 12 m 0x31808 0x31810 0x3237c 0x32384 (HOLE 4 m) 80) (ERR_EXIT m)).
Definition pvt3 (m : smode) : plan :=      (* [comment removed for export] *)
  PRun [0x31160] (PBranch (PRun [0x3256c] (closeE 109 120 m 60)) (PRun [0x317ec] (strarr m))).
Definition P_PVT : Z := 0x30ce4.
Definition after_p1 (m : smode) : plan :=
  PRun [0x30ce4] (PCaseReg 10 0 (GO (CPV 0) m) (PCaseReg 10 1 (GO (CPV 1) m) (PCaseReg 10 2 (GO (CPV 2) m) (pvt3 m)))).
Definition plain4 (m : smode) : plan := PRun [0x30b78] (PExt 42 [] (ENSURE 100 m 36 JS_p1 59 0x30ca0 0x30ca8 (GO 2))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NTv : expr := EVar 81. Definition RAWv : expr := EVar 82. Definition BCa : expr := EVar 83.
Definition NVa : expr := EAlu Instr.ALU_SRL RAWv (ELit 2).
Definition SSa (bc s6 : expr) : list (nat * expr) := [(21, bc); (22, s6); (23, TAGv); (24, EVar 23); (25, EVar 24); (26, EVar 25); (27, EVar 26)]%nat.
Definition kn_a : list kentry := [KRange HL 1 8; KRange NTv 0 255; KRange RAWv 0 (2 ^ 50 + 3); KRange BCa 1 128].
Definition JS_ag (m : smode) := JX m 0x314d4 ((10%nat, eadd INLO (eadd (eaddz ITO 2) HL)) :: (11%nat, NTv) :: (12%nat, RAWv) :: SSa BCa (EVar 21))
                                   (eadd (eaddz ITO 2) HL) IX 72 None (kn_a ++ [KRange (esub BSZ ITO) 3 INSZ]) 84.
Definition ITOA : expr := EVar 104.
Definition kn_ab : list kentry := kn_a ++ [KRange ITOA 0 INSZ; KRange (esub ITOA ITO) 3 INSZ; KRange (esub BSZ ITOA) 0 INSZ; KWord (SA e_sp (-120)) 8 NVa].
  (* [comment removed for export] *)
Definition JS_ab (m : smode) := JX m 0x31550 ((12%nat, IX) :: SSa BCa (escale (2 ^ 59) NTv)) ITOA IX 72 (Some (eaddz IX 1)) kn_ab 105.
Definition callA (m : smode) (k : nat) : plan :=
  PRun [GpAA.c_entry (AAcfg k)] (CALL m (300 + k) (310 + k) (AA_ARGS m ITOA (eaddz IX 1) NVa 105) post_w).
Definition avt0 (m : smode) : plan :=
  PCaseReg 21 3 (ERR_EXIT m) (PCaseReg 21 4 (callA m 8) (PCaseReg 21 7 (ERR_EXIT m) (PCaseReg 21 8 (callA m 9) (ERR_EXIT m)))).
Definition avt1 (m : smode) : plan :=
  PCaseReg 21 1 (callA m 0) (PCaseReg 21 2 (callA m 1) (PCaseReg 21 3 (ERR_EXIT m) (PCaseReg 21 4 (callA m 2)
    (PCaseReg 21 7 (ERR_EXIT m) (PCaseReg 21 8 (callA m 3) (ERR_EXIT m)))))).
Definition avt2 (m : smode) : plan :=
  PCaseReg 21 1 (callA m 4) (PCaseReg 21 2 (callA m 5) (PCaseReg 21 3 (ERR_EXIT m) (PCaseReg 21 4 (callA m 6)
    (PCaseReg 21 7 (ERR_EXIT m) (PCaseReg 21 8 (callA m 7) (ERR_EXIT m)))))).
(* [comment removed for export] *)
Definition P_AVT : Z := 0x315a4.
Definition after_ab (m : smode) : plan :=
  PRun [0x315a4] (PCaseReg 10 0 (GO (CAB 0) m) (PCaseReg 10 1 (GO (CAB 1) m) (PCaseReg 10 2 (GO (CAB 2) m) (ERR_EXIT m)))).
Definition after_ag (m : smode) : plan :=
  PRun [0x314ec] (PBranch (ERR_EXIT m)
    (PRun [0x31500] (PBranch
       (PRun [0x31514] (PBranch (ERR_EXIT m) (ENSURE 104 m 84 JS_ab 104 0x31548 0x31550 after_ab)))
       (ERR_EXIT m)))).
Definition HDRa (m : smode) : plan :=
  let aarm (hl : Z) := PExt 42 [] (PRun [0x309a4] (PBranch (ERR_EXIT m) (PRun [0x309b4] (PExt 42 []
       (if Z.eqb hl 8 then PRun [0x314cc] (PBranch (ERR_EXIT m) (PRun [0x314d4] (PHandoffW (HOLE 3 m) [(80%nat, ELit hl)])))
        else PRun [0x314d4] (PHandoffW (HOLE 3 m) [(80%nat, ELit hl)])))))) in
  PRun [0x3099c] (PCaseReg 13 0 (aarm 1) (PCaseReg 13 1 (aarm 2) (PCaseReg 13 2 (aarm 4) (aarm 8)))).
Definition aligned4 (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [0x30958] (PBranch (ERR_EXIT m) (PRun [0x3096c] (PBranch (ERR_EXIT m) (PRun [0x30980] (PBranch (ERR_EXIT m) (HDRa m)))))).
Definition tag4 (m : smode) : plan := PRun [0x30950] (PBranch (aligned4 m) (plain4 m)).

(* [comment removed for export] *)
Definition dispatch (m : smode) : plan :=
  let arm (k : nat) := PExt 42 [] (PHandoffW (2 + k) []) in
  PCase2 TAG7 0 (arm 0%nat) (PCase2 TAG7 1 (arm 1%nat) (PCase2 TAG7 2 (arm 2%nat) (PCase2 TAG7 3 (arm 3%nat)
  (PCase2 TAG7 4 (arm 4%nat) (PCase2 TAG7 5 (arm 5%nat) (PCase2 TAG7 6 (arm 6%nat) (PExt 42 [] (PRun [] (tag7 m))))))))).
Definition top (m : smode) : plan :=
  n13 (tin m) (                            (* [comment removed for export] *)
  PRun [] (PBranch (EXIT m)                (* [comment removed for export] *)
 (PRun [] (PBranch (EXIT m)                (* [comment removed for export] *)
 (PRun [] (dispatch m)))))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition D13 (m : smode) : list dstep := match vis m 36 with [(b, _)] => [DExt 13 [b]] | _ => [] end.   (* [comment removed for export] *)
Definition p0 (m : smode) := DPATH NXF (tin m) (D13 m ++ [DRun []; DBrT; DRun []; DBrT; DRun []]) 0.
Definition ATs (k : Z) (m : smode) : acs :=
  snd (let cs := snd (p0 m) in let e := EAlu Instr.ALU_AND (reg cs 23) (ELit 7) in
       DPATH NXF cs ((DLo e k :: (if Z.eqb k 0 then [] else [DHi e (k - 1)])) ++ [DExt 42 []]) 0).
Definition tagk (k : nat) (m : smode) : plan :=
  match k with 0 => tag0 m | 1 => tag1 m | 2 => tag2 m | 3 => tag3 m | 4 => tag4 m | 5 => tag5 m | _ => tag6 m end%nat.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ITOh : expr := EVar 82. Definition IXh : expr := EVar 83.
Definition SSoR : list (nat * expr) := [(21, eaddz DEPTH 1); (23, TBL); (24, NFv); (25, eaddz OBJ 1); (26, ELit 1); (27, ELit 58)]%nat.
Definition T_oL : acs := JX ML P_HEADo SSoR ITOh IXh 47 None [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 1 (2 ^ 48); KRange ITOh 0 INSZ] 84.
Definition SSnR : list (nat * expr) := [(21, eaddz DEPTH 1); (22, NFv); (23, eaddz OBJ 1); (24, ELit 34); (25, ELit 58); (26, ELit 1); (27, ELit 44)]%nat.
Definition T_nL : acs := JX ML P_HEADn SSnR ITOh IXh 47 None [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 1 (2 ^ 48); KRange ITOh 0 INSZ; KRange (esub ITOh ITO) 1 INSZ] 84.
Definition SScR : list (nat * expr) := [(21, NCv); (22, ELit 91); (23, eaddz OBJ 1); (24, ELit 44); (25, ELit 93); (26, ELit 1); (27, EVar 26)]%nat.
Definition T_cL : acs := JX ML P_HEADc ((10%nat, IXh) :: SScR) ITOh IXh 47 None (kn_x ++ [KRange HL 1 8; KRange NCv 1 (2 ^ 48); KRange ITOh 0 INSZ; KRange (esub ITOh ITO) 3 INSZ]) 84.
(* [comment removed for export] *)
Definition rsteps (k : Z) : list dstep := (if Z.eqb k 0 then [] else [DRHi 10 0]) ++ (if Z.leb k 1 then [] else [DRHi 10 1]) ++ [DRLo 10 k].
Definition PVs (k : Z) (m : smode) : acs := snd (DPATH NXF (JS_p1 m) (DRun [P_PVT] :: rsteps k) 0).
Definition ABs (k : Z) (m : smode) : acs := snd (DPATH NXF (JS_ab m) (DRun [P_AVT] :: rsteps k) 0).
Definition cutT (c : nat) (m : smode) : acs :=
  match c with
  | 0 => JS_ohdr m | 1 => JS_nhdr m | 2 => JS_p1 m | 3 => JS_ag m | 4 => JS_sa0 m | 5 => JS_ca0 m | 6 => JS_m4 m
  | 7 => PVs 0 m | 8 => PVs 1 m | 9 => PVs 2 m | 10 => ABs 0 m | 11 => ABs 1 m | 12 => ABs 2 m
  | 13 => JS_key m | 14 => JS_colon m | 15 => JS_oval m | 16 => T_oL
  | 17 => JS_q1 m | 18 => JS_num m | 19 => JS_q2 m | 20 => JS_c2 m | 21 => JS_nval m | 22 => T_nL
  | 23 => JS_cb1 m | 24 => JS_cb2 m | 25 => JS_cb3 m | 26 => JS_cb4 m | 27 => JS_cb5 m | 28 => T_cL
  | _ => JS_pw m end%nat.
Definition cutK (c : nat) (m : smode) : plan :=
  match c with
  | 0 => PRun [] (after_ohdr m) | 1 => PRun [] (after_nhdr m) | 2 => PRun [] (after_p1 m) | 3 => PRun [] (after_ag m) | 4 => PRun [] (after_sa0 m)
  | 5 => PRun [] (after_ca0 m) | 6 => PRun [] (after_m4 m)
  | 7 => pvt0 m | 8 => pvt1 m | 9 => pvt2 m | 10 => avt0 m | 11 => avt1 m | 12 => avt2 m
  | 13 => n13 (JS_key m) (after_keyj LMT m) | 14 => after_colon LMT m | 15 => n13 (JS_oval m) (after_oval LMT m) | 16 => loopo ML
  | 17 => after_q1 LMT m | 18 => n13 (JS_num m) (after_num LMT m) | 19 => after_q2 LMT m | 20 => after_c2 LMT m
  | 21 => n13 (JS_nval m) (after_nval LMT m) | 22 => loopn ML
  | 23 => after_cb1 LMT m | 24 => n13 (JS_cb2 m) (after_cb2 LMT m) | 25 => after_cb3 LMT m | 26 => n13 (JS_cb4 m) (after_cb4 LMT m)
  | 27 => after_cb5 LMT m | 28 => loopc ML
  | _ => cont_pw m end%nat.
(* [comment removed for export] *)
Definition lonly (c : nat) : bool := Nat.leb 13 c.
(* [comment removed for export] *)
Definition CUT (t : acs) (k : plan) : plan := PViaM 199 [(t, k)] (nxt t) (PMerge 199).
(* [comment removed for export] *)
Definition dead (cs : acs) : acs := set_kn cs (KRange (ELit 1) 0 0 :: kn cs).
Definition cut_entry (w : smode) (c : nat) (m : smode) : acs * plan :=
  match w, m with
  | ML, MS => (dead (cutT c MS), PContraH 0)          (* [comment removed for export] *)
  | _, MS => if (Nat.eqb c 6 || lonly c)%bool then (dead (cutT c MS), PContraH 0)   (* [comment removed for export] *)
             else (cutT c m, if Nat.leb 7 c then CUT (cutT c m) (cutK c m) else cutK c m)
  | _, _ => (cutT c m, if Nat.leb 7 c then CUT (cutT c m) (cutK c m) else cutK c m)
  end.

Definition NCUT : nat := 30.

(* [comment removed for export] *)
Definition CL_0 : acs * plan := Eval vm_compute in cut_entry ML 0 ML.
Definition CL_1 : acs * plan := Eval vm_compute in cut_entry ML 1 ML.
Definition CL_2 : acs * plan := Eval vm_compute in cut_entry ML 2 ML.
Definition CL_3 : acs * plan := Eval vm_compute in cut_entry ML 3 ML.
Definition CL_4 : acs * plan := Eval vm_compute in cut_entry ML 4 ML.
Definition CL_5 : acs * plan := Eval vm_compute in cut_entry ML 5 ML.
Definition CL_6 : acs * plan := Eval vm_compute in cut_entry ML 6 ML.
Definition CL_7 : acs * plan := Eval vm_compute in cut_entry ML 7 ML.
Definition CL_8 : acs * plan := Eval vm_compute in cut_entry ML 8 ML.
Definition CL_9 : acs * plan := Eval vm_compute in cut_entry ML 9 ML.
Definition CL_10 : acs * plan := Eval vm_compute in cut_entry ML 10 ML.
Definition CL_11 : acs * plan := Eval vm_compute in cut_entry ML 11 ML.
Definition CL_12 : acs * plan := Eval vm_compute in cut_entry ML 12 ML.
Definition CL_13 : acs * plan := Eval vm_compute in cut_entry ML 13 ML.
Definition CL_14 : acs * plan := Eval vm_compute in cut_entry ML 14 ML.
Definition CL_15 : acs * plan := Eval vm_compute in cut_entry ML 15 ML.
Definition CL_16 : acs * plan := Eval vm_compute in cut_entry ML 16 ML.
Definition CL_17 : acs * plan := Eval vm_compute in cut_entry ML 17 ML.
Definition CL_18 : acs * plan := Eval vm_compute in cut_entry ML 18 ML.
Definition CL_19 : acs * plan := Eval vm_compute in cut_entry ML 19 ML.
Definition CL_20 : acs * plan := Eval vm_compute in cut_entry ML 20 ML.
Definition CL_21 : acs * plan := Eval vm_compute in cut_entry ML 21 ML.
Definition CL_22 : acs * plan := Eval vm_compute in cut_entry ML 22 ML.
Definition CL_23 : acs * plan := Eval vm_compute in cut_entry ML 23 ML.
Definition CL_24 : acs * plan := Eval vm_compute in cut_entry ML 24 ML.
Definition CL_25 : acs * plan := Eval vm_compute in cut_entry ML 25 ML.
Definition CL_26 : acs * plan := Eval vm_compute in cut_entry ML 26 ML.
Definition CL_27 : acs * plan := Eval vm_compute in cut_entry ML 27 ML.
Definition CL_28 : acs * plan := Eval vm_compute in cut_entry ML 28 ML.
Definition CL_29 : acs * plan := Eval vm_compute in cut_entry ML 29 ML.
Definition CL (c : nat) : acs * plan := match c with 0 => CL_0 | 1 => CL_1 | 2 => CL_2 | 3 => CL_3 | 4 => CL_4 | 5 => CL_5 | 6 => CL_6 | 7 => CL_7 | 8 => CL_8 | 9 => CL_9 | 10 => CL_10 | 11 => CL_11 | 12 => CL_12 | 13 => CL_13 | 14 => CL_14 | 15 => CL_15 | 16 => CL_16 | 17 => CL_17 | 18 => CL_18 | 19 => CL_19 | 20 => CL_20 | 21 => CL_21 | 22 => CL_22 | 23 => CL_23 | 24 => CL_24 | 25 => CL_25 | 26 => CL_26 | 27 => CL_27 | 28 => CL_28 | _ => CL_29 end%nat.
Fixpoint weave (ms : list (acs * plan)) (c : nat) : list (acs * plan) :=
  match ms with [] => [] | e :: r => e :: CL c :: weave r (Datatypes.S c) end.
Definition TAGS_ML : list (acs * plan) := Eval vm_compute in map (fun k => (ATs (Z.of_nat k) ML, PRun [] (tagk k ML))) (seq 0 7).
Definition TAGS_MS : list (acs * plan) := Eval vm_compute in map (fun k => (ATs (Z.of_nat k) MS, PRun [] (tagk k MS))) (seq 0 7).
Definition MSE_ML : list (acs * plan) := Eval vm_compute in map (fun c => cut_entry ML c MS) (seq 0 NCUT).
Definition MSE_MS : list (acs * plan) := Eval vm_compute in map (fun c => cut_entry MS c MS) (seq 0 NCUT).
Definition CUTSL_ML : list (acs * plan) := TAGS_ML ++ weave MSE_ML 0.
Definition CUTSL_MS : list (acs * plan) := TAGS_MS ++ weave MSE_MS 0.
Definition CUTS (w : smode) : list (acs * plan) := match w with ML => CUTSL_ML | MS => CUTSL_MS end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cert_stmt (w : smode) (i : nat) : Prop :=
  match nth_error (CUTS w) i with
  | Some (T, k) => exists sh, gplan_ok k = true /\ holes_only sh = true /\
      check PSEGS IT APLAIN (ce_nxf (ce w)) LIMIT (XN w) (B2JCutShare.GlzCallCert.XE0) (XB w) (B2JCutShare.GlzCallCert.XC0) (HScut (ce w) (CUTS w) (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh
  | None => True
  end.
Definition top_stmt (w : smode) : Prop :=
  exists sh, gplan_ok (top w) = true /\ holes_only sh = true /\
      check PSEGS IT APLAIN (ce_nxf (ce w)) LIMIT (XN w) (B2JCutShare.GlzCallCert.XE0) (XB w) (B2JCutShare.GlzCallCert.XC0) (HScut (ce w) (CUTS w) 0) 0%nat BFUEL FUEL None (ce_tin (ce w)) (top w) = COk sh.










End B2J.
