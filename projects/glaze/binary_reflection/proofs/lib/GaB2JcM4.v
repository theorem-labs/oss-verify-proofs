(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec OSSVerify.Proofs.glaze.binary_reflection.lib.GaEsc OSSVerify.Proofs.glaze.binary_reflection.lib.GaAA OSSVerify.Proofs.glaze.binary_reflection.lib.GaWA OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JTpl OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JTpl4 OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JTpl6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaB2J.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT.GaDedup OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec.


Export OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JTpl OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JTpl4 OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JTpl6.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Definition TIDY (k : plan) : plan := PExt 48 [] (PExt 47 [] k).
Definition GO (c : nat) (m : smode) : plan := PHandoffW (HOLE c m) [].
(* [comment removed for export] *)
Definition EXITX (m : smode) (ito : expr) : plan := PRun [EPIPC] (PHandoffW (HOLE CEPI m) [(63%nat, ito)]).
Definition EXIT0 (m : smode) : plan := EXITX m ITO.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition EPIK (m : smode) : plan := PRun [REL] (PExt 51 [] (PRun [] (PHandoffW (hole m) [(41%nat, eERR); (42%nat, eITO); (43%nat, eIX)]))).
Definition dispatch (m : smode) : plan :=
  let arm (k : nat) := PExt 42 [] (PHandoffW (2 + k) []) in
  PCase2 TAG7 0 (arm 0%nat) (PCase2 TAG7 1 (arm 1%nat) (PCase2 TAG7 2 (arm 2%nat) (PCase2 TAG7 3 (arm 3%nat)
  (PCase2 TAG7 4 (arm 4%nat) (PCase2 TAG7 5 (arm 5%nat) (PCase2 TAG7 6 (arm 6%nat) (PExt 42 [] (EXIT0 m)))))))).   (* [comment removed for export] *)
Definition top (m : smode) : plan :=
  PRun [] (PExt 50 [ELit 0] (PExt 47 []
  (PRun [] (PBranch (EXIT0 m)               (* [comment removed for export] *)
  (PRun [] (PBranch (EXIT0 m)               (* [comment removed for export] *)
  (PRun [] (dispatch m)))))))).

(* [comment removed for export] *)
Definition vprep2 (w : smode) (sz0 ito0 mtr0 : expr) (c0 : Z) (sz1 ito1 mtr1 : expr) (c1 : Z) (k : plan) : plan :=
  PFactLe mtr1 (pwtop_e CPX sz1) MTRTOP k.      (* [comment removed for export] *)
Definition STEP (w : smode) (sz0 ito0 mtr0 : expr) (c0 : Z) (sz1 ito1 mtr1 : expr) (c1 : Z) (via : expr) (k : plan) : plan :=
  vprep2 w sz0 ito0 mtr0 c0 sz1 ito1 mtr1 c1 k.


(* [comment removed for export] *)
Definition ENSUREg (stub_taken : bool) (bump : nat) (j : nat) (w m : smode) (sv : nat) (req ito mtr : expr) (c0 c : Z) (JS : smode -> acs) (lo : nat)
           (bpc back : Z) (k : smode -> plan) : plan :=
  let n := escale 2 req in
  let sz := szof m sv in
  let stub :=
       PRun [] (PBump bump (PExt2 (RID m) (RARGS m sv mtr)
          (TIDY (PExt 49 [mtr; sz; n; CPX; ELit 1] (PRun [back] (PMerge j))))                        (* [comment removed for export] *)
          (TIDY (PExt 13 [EVar bump]                                                                  (* [comment removed for export] *)
                (PExt 49 [mtr; sz; n; CPX; ELit 0] (PRun [back] (PMerge j))))))) in                   (* [comment removed for export] *)
  let room := PRun [back] (PMerge j) in                                                               (* [comment removed for export] *)
  PViaM j (match m with MS => [(JS MS, k MS); (JS ML, k ML)] | ML => [(JS ML, k ML)] end) lo
    (PRun [bpc] (if stub_taken then PBranch room stub else PBranch stub room)).
Definition ENSURE := ENSUREg false BUMP1.

(* [comment removed for export] *)
Definition EXITP (w m : smode) (v : nat) (ito0 : expr) (c : Z) (ito1 err : expr) : plan :=
  PFactLe (EVar (3 + v)) (pwtop_e CPX (szof m v)) MTRTOP (EXITX m ito1).
Definition tag0_null (w m : smode) : plan := ENSURE 0 w m 36 (eaddz IX 4) ITO e_mtr 0 GEV (JS_null w) 62 0xa47d4 0xa47dc (fun m' => EXITP w m' 62 ITO GEV (eaddz ITO 1) (ELit 0)).
(* [comment removed for export] *)
Definition tag0 (w m : smode) : plan :=
  PRun [] (PBranch (tag0_null w m)
  (PRun [] (PBranch
     (ENSURE 0 w m 36 (eaddz IX 5) ITO e_mtr 0 GEV (JS_false w) 62 0xa51f0 0xa51f8 (fun m' => PRun [] (PExt 5 [] (EXITP w m' 62 ITO GEV (eaddz ITO 1) (ELit 0)))))
     (ENSURE 0 w m 36 (eaddz IX 4) ITO e_mtr 0 GEV (JS_true w) 62 0xa524c 0xa5254 (fun m' => EXITP w m' 62 ITO GEV (eaddz ITO 1) (ELit 0)))))).

(* [comment removed for export] *)
Definition CALL (m : smode) (idS idL : nat) (args : list expr) (k : smode -> plan) : plan :=
  match m with MS => PExt2 idS args (k MS) (k ML) | ML => PExt idL args (k ML) end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GFIX (k : plan) : plan := TIDY (PFact (KRange (eaddz G 36) (PTRLO + 36) HI47) k).     (* [comment removed for export] *)
Definition num_post (w m' : smode) (sz0 ito0 mtr0 : expr) (c0 c1 : Z) (k : plan) : plan :=
  let sz' := match m' with MS => EVar (3 + BN) | ML => EVar (4 + BN) end in
  let mtr' := EVar (6 + BN) in
  let ito' := eadd ito0 (EVar (1 + BN)) in
  GFIX ((match m' with ML => PExt 13 [EVar (3 + BN)] | MS => fun k => k end)
  (STEP w sz0 ito0 mtr0 c0 sz' ito' mtr' c1 (esub (eaddz (escale 6 (esub sz' sz0)) GEV) (esub mtr' mtr0)) k)).
Definition tag1 (w : smode) : plan :=
  PRun [GaNumT.BNU] (PBump BN (CALL w 220 223 (NUM_ARGS w (eaddz ITO 1) IX 36 TAGv e_mtr)
    (fun m' => num_post w m' (szin w) (eaddz ITO 1) e_mtr (- CG) (- CG + GEV)
       (EXITX m' (eadd (eaddz ITO 1) (EVar (1 + BN))))))).

(* [comment removed for export] *)
Definition EXITE (w m : smode) (v : nat) (ito : expr) (c : Z) (err : expr) : plan := EXITP w m v ito c ito err.
Definition hdr_arm (w : smode) (hl : Z) (chk chk8 jn : Z) (j : nat) : plan :=
  let go := vprep2 w (szin w) ITO e_mtr 0 (szin w) (eaddz ITO (1 + hl)) e_mtr (- 2 * CG) (PRun [jn] (PMergeW j [(62%nat, ELit hl)])) in
  PExt 42 [] (PRun [chk] (PBranch (EXITX w (eaddz ITO 1))
    (if Z.eqb hl 8 then PRun [chk8] (PBranch (EXITX w (eaddz ITO (1 + hl))) go) else go))).     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition esc_post (w m' : smode) (sz0 ito0 mtr0 : expr) (c0 c1 : Z) (k : plan) : plan :=
  let sz' := match m' with MS => EVar (2 + BE) | ML => EVar (3 + BE) end in
  let mtr' := EVar (5 + BE) in
  GFIX ((match m' with ML => PExt 13 [EVar (2 + BE)] | MS => fun k => k end)
  (STEP w sz0 ito0 mtr0 c0 sz' ito0 mtr' c1 (esub (eaddz (escale 6 (esub sz' sz0)) GEV) (esub mtr' mtr0)) k)).
Definition esc_call (w m : smode) : plan :=
  let c1 := - 2 * CG + GEV in
  PRun [0xa4ab4] (PBranch (EXITE w m 64 ITOH (- 2 * CG) ERR22)
  (PRun [GaEsc.ENTRY] (PBump BE (CALL m 200 203 (ESC_ARGS m ITOH NS IX 64 (EVar 67))
     (fun m' => esc_post w m' (szof m 64) ITOH (EVar 67) (- 2 * CG) c1
        (PRun [0xa4aec] (PBranch
           (EXITP w m' (2 + BE) ITOH c1 ITOH (EVar BE))                     (* [comment removed for export] *)
           (EXITP w m' (2 + BE) ITOH c1 (eadd ITOH NS) (ELit 0))))))))).    (* [comment removed for export] *)
Definition tag2 (w : smode) : plan :=
  PRun [0xa3fb8] (PBranch (EXITX w (eaddz ITO 1))                                             (* [comment removed for export] *)
  (PViaM 2 (match w with MS => [(JS_hdr w MS, esc_call w MS)] | ML => [(JS_hdr w ML, esc_call w ML)] end) 62
     (PRun [0xa3ffc] (PCaseReg 16 0 (hdr_arm w 1 0xa4004 0 0xa4a6c 2) (PCaseReg 16 1 (hdr_arm w 2 0xa4004 0 0xa4a6c 2)
                     (PCaseReg 16 2 (hdr_arm w 4 0xa4004 0 0xa4a6c 2) (hdr_arm w 8 0xa4004 0xa4a60 0xa4a6c 2))))))).

Definition close5K (w m : smode) : plan :=
  ENSUREg false 140 8 w m V5x (eaddz IXC 1) ITOC (EVar (3 + V5x)) C5 (C5 + GEV) (JS_rbr w) V5r 0xa4f50 0xa4f58
          (fun m' => EXITP w m' V5r ITOC (C5 + GEV) ITOC (ELit 0)).
(* [comment removed for export] *)
Definition GO_close (w m : smode) (sv : nat) (ito ix : expr) (c0 : Z) : plan :=
  vprep2 w (szof m sv) ito (EVar (3 + sv)) c0 (szof m sv) ito (EVar (3 + sv)) C5
    (PRun [0xa4efc] (PHandoffW (HOLE C5CLOSE m) [(62%nat, ito); (63%nat, ix)])).
Definition GO_loop (m : smode) (cnt ito ix : expr) : plan := PRun [0xa4da0] (PHandoffW (HOLE C5LOOP m) [(62%nat, cnt); (63%nat, ito); (64%nat, ix)]).
(* [comment removed for export] *)
Definition post5 (w cm m m' : smode) : plan :=
  let szJ := szof m V5i in let mtrJ := EVar (3 + V5i) in
  let cpe := esub (eaddz (eadd (eadd (escale 6 (esub (xsz5 m') szJ)) (escale CG (esub xI5 ITOJ))) (escale GEV xE5)) (- GEV)) (esub (EVar (6 + B5)) mtrJ) in
  TIDY                                       (* [comment removed for export] *)
  (PRun [0xa4dd0] (PBranch
     (EXITX m' xI5)     (* [comment removed for export] *)
     (STEP w szJ ITOJ mtrJ C5 (xsz5 m') xI5 (EVar (6 + B5)) (C5 - GEV) cpe
        (PCase2 (esub RC J5) 1
           (GO_close w m' (3 + B5) xI5 xX5 (C5 - GEV))
           (ENSUREg true 216 7 w m' (3 + B5) (eaddz xX5 1) xI5 (EVar (6 + B5)) (C5 - GEV) C5 (JS_comma w) V5c 0xa4e28 0xa4e2c
                    (fun m'' => match cm, m'' with
                                | MS, ML => GO_loop ML (esub (esub RC J5) (ELit 1)) ITO2 (eaddz IX2 1)
                                | _, _ => PRun [0xa4da0] PNext
                                end)))))).
Definition body5 (w m : smode) : plan := PRun [ENTRY] (PBump B5 (CALL m 210 213 (SELF_ARGS m ITOJ IXJ V5i (EVar (3 + V5i))) (post5 w m m))).
Definition loop5K (w m : smode) : plan := PLoopM 104 RC [(INV5 w m, body5 w m, PContraH 0)] [(105%nat, ITOL); (106%nat, IXL)].
Definition after_lbr (w m : smode) : plan :=
  PRun [0xa4d50] (PBranch (GO_loop m NV ITOH (eaddz IX 1)) (GO_close w m V5b ITOH (eaddz IX 1) C5)).
Definition tag5 (w : smode) : plan :=
  PRun [0xa410c] (PBranch (EXITX w (eaddz ITO 1))
  (PViaM 5 [(JS_ahdr w w, ENSUREg false 124 4 w w 64 (eaddz IX 1) ITOH (EVar 67) (- 2 * CG) C5 (JS_lbr w) V5b 0xa4cbc 0xa4cc4 (after_lbr w))] 62
     (PRun [0xa4150] (PCaseReg 16 0 (hdr_arm w 1 0xa4158 0 0xa4c24 5) (PCaseReg 16 1 (hdr_arm w 2 0xa4158 0 0xa4c24 5)
                     (PCaseReg 16 2 (hdr_arm w 4 0xa4158 0 0xa4c24 5) (hdr_arm w 8 0xa4158 0xa4c10 0xa4c24 5))))))).

(* [comment removed for export] *)
Definition hdr_armG (w m : smode) (sv : nat) (ito0 : expr) (c0 c1 : Z) (hl : Z) (chk : Z) (chk_ok_taken : bool) (chk8 : Z) (chk8_ok_taken : bool)
           (jn : Z) (j hs : nat) : plan :=
  let sz := szof m sv in let mtr := EVar (3 + sv) in
  let go := vprep2 w sz ito0 mtr c0 sz (eaddz ito0 hl) mtr c1 (PRun [jn] (PMergeW j [(hs, ELit hl)])) in
  let br (ok_taken : bool) (bad ok : plan) := if ok_taken then PBranch bad ok else PBranch ok bad in
  PExt 42 [] (PRun [chk] (br chk_ok_taken (EXITP w m sv ito0 c0 ito0 ERR22)
    (if Z.eqb hl 8 then PRun [chk8] (br chk8_ok_taken (EXITP w m sv ito0 c0 (eaddz ito0 hl) ERR22) go) else go))).
Definition HDR4G (w m : smode) (sv : nat) (ito0 : expr) (c0 c1 : Z) (r : nat) (ld chk : Z) (chk_ok_taken : bool) (chk8 : Z) (chk8_ok_taken : bool)
           (jn : Z) (j hs : nat) : plan :=
  let arm hl := hdr_armG w m sv ito0 c0 c1 hl chk chk_ok_taken chk8 chk8_ok_taken jn j hs in
  PRun [ld] (PCaseReg r 0 (arm 1) (PCaseReg r 1 (arm 2) (PCaseReg r 2 (arm 4) (arm 8)))).
Definition close3K (w m : smode) : plan :=
  ENSUREg false 140 8 w m V5x (eaddz IXC 1) ITOC (EVar (3 + V5x)) C5 (C5 + GEV) (JS_rcb w) V5r 0xa6930 0xa6938
          (fun m' => EXITP w m' V5r ITOC (C5 + GEV) ITOC (ELit 0)).
Definition GO_close3 (w m : smode) (sv : nat) (ito ix : expr) (c0 : Z) : plan :=
  vprep2 w (szof m sv) ito (EVar (3 + sv)) c0 (szof m sv) ito (EVar (3 + sv)) C5
    (PRun [0xa68c0] (PHandoffW (HOLE C3CLOSE m) [(62%nat, ito); (63%nat, ix)])).
Definition GO_loop3 (m : smode) (cnt ito ix : expr) : plan := PRun [0xa6368] (PHandoffW (HOLE (match m with MS => C3LOOP | ML => C3LOOPL end) m) [(62%nat, cnt); (63%nat, ito); (64%nat, ix)]).
(* [comment removed for export] *)
Definition IDH (vs : list nat) : list (nat * expr) := map (fun v => (v, EVar v)) vs.
(* [comment removed for export] *)
Definition oval_k (w cm m' : smode) : plan :=
  let c1 := C5 - CG + GEV in
  PCase2 (esub RC J5) 1
     (GO_close3 w m' (3 + BV) xIv xXv c1)
     (ENSUREg true 330 37 w m' (3 + BV) (eaddz xXv 1) xIv (EVar (6 + BV)) c1 C5 (JS_ocomma w) V3m 0xa672c 0xa6730
              (fun m'' => match cm, m'' with
                          | MS, ML => GO_loop3 ML (esub (esub RC J5) (ELit 1)) ITO3 (eaddz IX3 1)
                          | _, _ => PRun [0xa6368] PNext
                          end)).
Definition post_oval (w cm m m' : smode) : plan :=
  let sz := szof m V3c in let mtr := EVar (3 + V3c) in
  let itos := eadd ITOK NK in
  let c0 := C5 - CG + 2 * GEV in
  let cpe := esub (eaddz (eadd (eadd (escale 6 (esub (xszv m') sz)) (escale CG (esub xIv itos))) (escale GEV xEv)) (- GEV)) (esub (EVar (6 + BV)) mtr) in
  TIDY
  (PRun [0xa66d8] (PBranch
     (STEP w sz itos mtr c0 (xszv m') xIv (EVar (6 + BV)) (c0 - GEV) cpe
        (match cm, m' with
         | MS, ML => PRun [0xa66dc] (PHandoffW (HOLE COVALL ML) (IDH [62; 104; 261; 262]%nat))      (* [comment removed for export] *)
         | _, _ => oval_k w cm m'
         end))
     (EXITX m' xIv))).      (* [comment removed for export] *)
Definition after_colon (w cm m : smode) : plan :=
  let sz := szof m V3c in let mtr := EVar (3 + V3c) in
  let itos := eadd ITOK NK in
  let c0 := C5 - CG + 2 * GEV in
  PRun [ENTRY]
    (PFactVia (esub (escale 24 itos) (eaddz xXk 1)) (esub (eaddz (eadd IXJ (escale 2 NK)) 2) xXk) 0 (2 * RELHI)      (* [comment removed for export] *)
    (PFactLe (eaddz xXk 1) (escale 24 itos) BIG
    (vprep2 w sz ITOK mtr c0 sz itos mtr c0
    (PBump BV (CALL m 210 213 (SELF_ARGS m itos (eaddz xXk 1) V3c mtr) (post_oval w cm m)))))).
(* [comment removed for export] *)
Definition key_k (w cm m' : smode) : plan :=
  let c1 := C5 - CG + GEV in
  ENSUREg true 254 35 w m' (2 + BK) (eaddz xXk 1) ITOK (EVar (5 + BK)) c1 (c1 + GEV) (JS_colon w) V3c 0xa6608 0xa660c
          (fun m'' => match cm, m'' with MS, ML => GO CCOLL ML | _, _ => after_colon w cm m'' end).
Definition after_key (w cm m m' : smode) : plan :=
  let sz := szof m V3k in let mtr := EVar (3 + V3k) in
  let c0 := C5 - CG in
  GFIX ((match m' with ML => PExt 13 [EVar (2 + BK)] | MS => fun k => k end)
  (STEP w sz ITOK mtr c0 (xszk m') ITOK (EVar (5 + BK)) (c0 + GEV) (esub (eaddz (escale 6 (esub (xszk m') sz)) GEV) (esub (EVar (5 + BK)) mtr))
  (PFactVia (eaddz (eadd (esub (escale 24 (esub ITOK ITO)) (esub xXk IX)) (escale 2 NK)) 2) (esub (escale 24 (esub ITOK ITO)) (esub IXJ IX)) 71 (2 * RELHI)   (* [comment removed for export] *)
  (PRun [0xa65bc] (PBranch
     (match cm, m' with
      | MS, ML => PRun [0xa65c0] (PHandoffW (HOLE CKEYL ML) (IDH [62; 104; 105; 106; 150; 151; 191]%nat))     (* [comment removed for export] *)
      | _, _ => key_k w cm m'
      end)
     (EXITP w m' (2 + BK) ITOK (c0 + GEV) ITOK xEk)))))).                                                           (* [comment removed for export] *)
Definition after_khdr (w cm m : smode) : plan :=
  PRun [0xa657c] (PBranch (EXITP w m V3k ITOK (C5 - CG) ITOK ERR22)
  (PRun [GaEsc.ENTRY] (PBump BK (CALL m 200 203 (ESC_ARGS m ITOK NK IXJ V3k (EVar (3 + V3k))) (after_key w cm m))))).
Definition bodyo (w m : smode) : plan :=
  PRun [0xa638c] (PBranch (EXITP w m V5i ITOJ C5 ITOJ ERR22)
  (PViaM 34 [(JS_khdr w m, after_khdr w m m)] 150
     (HDR4G w m V5i ITOJ C5 (C5 - CG) 15 0xa63c4 0xa63cc true 0xa6538 true 0xa6544 34 150))).
Definition loop3K (w m : smode) : plan := PLoopM 104 RC [(INV3 w m, bodyo w m, PContraH 0)] [(105%nat, ITOL); (106%nat, IXL)].
Definition after_ohdr (w m : smode) : plan :=
  PRun [0xa6330] (PBranch (GO_loop3 m NF ITOH3 (eaddz IX 1)) (GO_close3 w m V3h ITOH3 (eaddz IX 1) C5)).
Definition okeys_str (w m : smode) : plan :=
  PRun [0xa48f0] (PBranch
    (PViaM 3 [(JS_ohdr w m, after_ohdr w m)] 100 (HDR4G w m 62 ITO1 C3a C5 15 0xa4934 0xa493c false 0xa62e0 true 0xa62ec 3 100))
    (EXITP w m 62 ITO1 C3a ITO1 ERR22)).
(* [comment removed for export] *)
Definition GO_loopn (m : smode) (cnt ito ix : expr) : plan :=
  PRun [0xa5580] (PHandoffW (HOLE (match m with MS => CNLOOP | ML => CNLOOPL end) m) [(62%nat, cnt); (63%nat, ito); (64%nat, ix)]).
Definition relx_e (ito ix : expr) : expr := esub (escale 24 (esub ito ITO)) (esub ix IX).
Definition xszw (m' : smode) : expr := match m' with MS => EVar (3 + BVN) | ML => EVar (4 + BVN) end.
(* [comment removed for export] *)
Definition nval_k (w cm m' : smode) : plan :=
  PCase2 (esub RC J5) 1
     (GO_close3 w m' (3 + BVN) xIw xXw (C5 - GEV))
     (ENSUREg true 372 47 w m' (3 + BVN) (eaddz xXw 1) xIw (EVar (6 + BVN)) (C5 - GEV) C5 (JS_ncomma w) Vnc 0xa587c 0xa5880
              (fun m'' => match cm, m'' with
                          | MS, ML => GO_loopn ML (esub (esub RC J5) (ELit 1)) ITO4 (eaddz IX4 1)
                          | _, _ => PRun [0xa5580] PNext
                          end)).
Definition post_nval (w cm m m' : smode) : plan :=
  let sz := szof m Vc2 in let mtr := EVar (3 + Vc2) in
  let cpe := esub (eaddz (eadd (eadd (escale 6 (esub (xszw m') sz)) (escale CG (esub xIw ITON))) (escale GEV xEw)) (- GEV)) (esub (EVar (6 + BVN)) mtr) in
  TIDY
  (PRun [0xa5828] (PBranch
     (STEP w sz ITON mtr C5 (xszw m') xIw (EVar (6 + BVN)) (C5 - GEV) cpe
        (match cm, m' with
         | MS, ML => PRun [0xa582c] (PHandoffW (HOLE CNVALL ML) (IDH [62; 104; 301; 302]%nat))
         | _, _ => nval_k w cm m'
         end))
     (EXITX m' xIw))).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition after_c2 (w cm m : smode) : plan :=
  let mtr := EVar (3 + Vc2) in
  PRun [ENTRY]
    (PFactVia (esub (escale 24 ITON) (eaddz xXn 2)) (esub (escale 24 ITO) IX) 0 (2 * RELHI)      (* [comment removed for export] *)
    (PFactLe (eaddz xXn 2) (escale 24 ITON) BIG
    (PBump BVN (CALL m 210 213 (SELF_ARGS m ITON (eaddz xXn 2) Vc2 mtr) (post_nval w cm m))))).
Definition after_q2 (w cm m : smode) : plan :=
  ENSUREg true 300 45 w m Vq2 (eaddz xXn 2) ITON (EVar (3 + Vq2)) (C5 - GEV) C5 (JS_c2 w) Vc2 0xa577c 0xa5780
          (fun m'' => match cm, m'' with MS, ML => GO CC2L ML | _, _ => after_c2 w cm m'' end).
Definition num_k (w cm m' : smode) : plan :=
  ENSUREg true 260 44 w m' (3 + BNK) (eaddz xXn 1) ITON (EVar (6 + BNK)) (C5 - 2 * GEV) (C5 - GEV) (JS_q2 w) Vq2 0xa56cc 0xa56d0
          (fun m'' => match cm, m'' with MS, ML => GO CQ2L ML | _, _ => after_q2 w cm m'' end).
Definition xszn (m' : smode) : expr := match m' with MS => EVar (3 + BNK) | ML => EVar (4 + BNK) end.
Definition post_numk (w cm m m' : smode) : plan :=
  let sz := szof m Vq1 in let mtr := EVar (3 + Vq1) in
  let mtr' := EVar (6 + BNK) in
  let c0 := C5 + GEV in
  GFIX ((match m' with ML => PExt 13 [EVar (3 + BNK)] | MS => fun k => k end)
  (PRun [0xa5678] (PBranch
     (PFact (KRange xDn 1 8)                                                                    (* [comment removed for export] *)
     (STEP w sz ITOJ mtr c0 (xszn m') ITON mtr' (C5 - 2 * GEV) (esub (eaddz (escale 6 (esub (xszn m') sz)) GEV) (esub mtr' mtr))
     (PFactVia (relx_e ITON xXn) (relx_e ITOJ IXJ) 54 (2 * RELHI)
        (match cm, m' with
         | MS, ML => PRun [0xa567c] (PHandoffW (HOLE CNUML ML) (IDH [62; 104; 105; 106; 191; 192]%nat))
         | _, _ => num_k w cm m'
         end))))
     (EXITX m' ITON)))).            (* [comment removed for export] *)
Definition after_q1 (w cm m : smode) : plan :=
  PRun [GaNumT.BNU] (PBump BNK (CALL m 220 223 (NUM_ARGS m ITOJ (eaddz IXJ 1) Vq1 TAGv (EVar (3 + Vq1))) (post_numk w cm m))).
Definition bodyn (w cm m : smode) : plan :=
  ENSUREg true 190 42 w m V5i (eaddz IXJ 1) ITOJ (EVar (3 + V5i)) C5 (C5 + GEV) (JS_q1 w) Vq1 0xa55c8 0xa55cc
          (fun m'' => match cm, m'' with MS, ML => GO CQ1L ML | _, _ => after_q1 w cm m'' end).
Definition loopnK (w m : smode) : plan := PLoopM 104 RC [(INVn w m, bodyn w m m, PContraH 0)] [(105%nat, ITOL); (106%nat, IXL)].
Definition after_nhdr (w m : smode) : plan :=
  PRun [0xa554c] (PBranch (GO_close3 w m V3h ITOH3 (eaddz IX 1) C5) (GO_loopn m NF ITOH3 (eaddz IX 1))).
Definition okeys_num (w m : smode) : plan :=
  PRun [0xa452c] (PBranch
    (PViaM 31 [(JS_nhdr w m, after_nhdr w m)] 100 (HDR4G w m 62 ITO1 C3a C5 15 0xa456c 0xa4574 false 0xa5528 false 0xa5530 31 100))
    (EXITP w m 62 ITO1 C3a ITO1 ERR22)).
Definition after_lcb (w m : smode) : plan :=
  PRun [0xa4500] (PBranch (okeys_num w m)                                              (* [comment removed for export] *)
  (PRun [0xa45a4] (PBranch (EXITP w m 62 ITO1 C3a ITO1 (ELit 24)) (okeys_str w m)))).
Definition tag3 (w : smode) : plan := ENSURE 30 w w 36 (eaddz IX 1) ITO1 e_mtr (- CG) C3a (JS_lcb w) 62 0xa4374 0xa437c (after_lcb w).

(* [comment removed for export] *)
Definition str3 (m : smode) (sv : nat) : list expr :=
  match m with MS => [EVar sv; ELit 0; ELit 0] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end.
Definition BW : nat := 200.           (* [comment removed for export] *)
Definition xszW (m' : smode) : expr := match m' with MS => EVar (3 + BW) | ML => EVar (4 + BW) end.
Definition relE_e (ito ix err : expr) : expr := esub (eadd (escale 24 (esub ito ITO)) (escale IXMAX err)) (esub ix IX).
(* [comment removed for export] *)
Definition post_w (w m : smode) (sv : nat) (itm ito0 ix0 : expr) (c K : Z) (ppc : Z) (at_ppc : bool) (cpw : nat) (m' : smode) : plan :=
  let sz := szof m sv in let mtr := EVar (3 + sv) in
  let err' := EVar BW in let di := EVar (1 + BW) in let ix' := EVar (2 + BW) in let mtr' := EVar (6 + BW) in
  let ito' := eadd ito0 di in
  GFIX ((match m' with ML => PExt 13 [EVar (3 + BW)] | MS => fun k => k end)
  (STEP w sz itm mtr c (xszW m') ito' mtr' c (esub (eadd (escale 6 (esub (xszW m') sz)) (escale (GEV / K) di)) (esub mtr' mtr))
  (PFactVia (relE_e ito' ix' err') (esub (eadd (escale 24 di) (escale 40 err')) (esub ix' ix0)) 2 (2 ^ 63)
  ((if at_ppc then fun k => k else PRun [ppc]) (PHandoffW (HOLE cpw m') [(62%nat, ito'); (63%nat, ix'); (64%nat, err')]))))).
Definition AA_ARGS (m : smode) : list expr :=
  [TPL; ELit 0; G; OBJ; ITOA; esub BSZ ITOA; eaddz IX 1] ++ str3 m V4b
  ++ [ELit 0; INLO; NVA; eaddz F 32; PEND; PIT; PIX; szof m V4b; EVar (3 + V4b); FB1].
Definition callA (w m : smode) (k : nat) : plan :=
  PRun [GaAA.c_entry (AAcfg k)] (PBump BW (CALL m (300 + k) (310 + k) (AA_ARGS m)
    (post_w w m V4b ITOG ITOA (eaddz IX 1) C5 (GaAA.c_K (AAcfg k)) 0xa7df8 (Nat.eqb k 2) CPWA))).     (* [comment removed for export] *)
Definition WA_ARGS (m : smode) : list expr :=
  [TPL; ELit 0; G; OBJ; eaddz ITO 1; esub BSZ (eaddz ITO 1); eaddz IX 1] ++ str3 m V4p
  ++ [ELit 0; INLO; PEND; PIT; PIX; szof m V4p; EVar (3 + V4p); FB1].
Definition callW (w m : smode) (k : nat) : plan :=
  PRun [GaWA.c_entry (WAcfg k)] (PBump BW (CALL m (320 + k) (330 + k) (WA_ARGS m)
    (post_w w m V4p (eaddz ITO 1) (eaddz ITO 1) (eaddz IX 1) C4p (GaWA.c_K (WAcfg k)) 0xa74d4 false CPWP))).
(* [comment removed for export] *)
Definition bc_float (r : nat) (bad : plan) (call : nat -> plan) : plan :=
  PCaseReg r 3 bad (PCaseReg r 4 (call 8%nat) (PCaseReg r 7 bad (PCaseReg r 8 (call 9%nat) bad))).
Definition bc_int (r : nat) (bad : plan) (call : nat -> plan) (k0 : nat) : plan :=
  PCaseReg r 1 (call k0) (PCaseReg r 2 (call (1 + k0)%nat) (PCaseReg r 3 bad (PCaseReg r 4 (call (2 + k0)%nat)
    (PCaseReg r 7 bad (PCaseReg r 8 (call (3 + k0)%nat) bad))))).
Definition ERR24 : expr := ELit 24.
Definition avt (w m : smode) (vt : nat) : plan :=
  let bad := EXITP w m V4b ITOG C5 ITOA ERR24 in     (* [comment removed for export] *)
  match vt with 0 => bc_float 18 bad (callA w m) | 1 => bc_int 18 bad (callA w m) 0 | _ => bc_int 18 bad (callA w m) 4 end%nat.
Definition pvt (w m : smode) (vt : nat) : plan :=
  let bad := EXITE w m V4p (eaddz ITO 1) C4p ERR24 in
  match vt with 0 => bc_float 23 bad (callW w m) | 1 => bc_int 23 bad (callW w m) 0 | _ => bc_int 23 bad (callW w m) 4 end%nat.
Definition after_ab (w m : smode) : plan :=
  PRun [0xa5d18] (PCaseReg 10 0 (GO (CAB 0) m) (PCaseReg 10 1 (GO (CAB 1) m) (PCaseReg 10 2 (GO (CAB 2) m)
                 (PRun [0xa5dc0] (PBranch (EXITP w m V4b ITOG C5 ITOA ERR24) (EXITP w m V4b ITOG C5 ITOA ERR24)))))).
                 (* [comment removed for export] *)
Definition after_ag (w m : smode) : plan :=
  let c0 := - 2 * CG in
  PRun [0xa5b78] (PBranch (EXITE w m V4g ITOG c0 ERR22)                                      (* [comment removed for export] *)
  (PRun [0xa5bac] (PBranch (EXITP w m V4g ITOG c0 (eaddz ITOG 1) ERR24)                      (* [comment removed for export] *)
  (PRun [0xa5bd0] (PBranch (EXITP w m V4g ITOG c0 (eaddz ITOG 1) ERR22)                      (* [comment removed for export] *)
  (ENSUREg false 170 104 w m V4g (eaddz IX 1) ITOG (EVar (3 + V4g)) c0 C5 (JS_ab w) 128 0xa5c60 0xa5c68 (after_ab w))))))).
Definition aligned4 (w : smode) : plan :=
  PRun [0xa3e94] (PBranch (EXITX w ITO1)
  (PRun [0xa3ebc] (PBranch (EXITX w ITO1)
  (PRun [0xa3efc] (PExt 42 [] (PRun [0xa3f04] (PExt 46 [F; ELit 32; ELit 8]
  (PRun [0xa3f14] (PBranch (EXITX w (eaddz ITO 2))
  (PViaM 103 [(JS_ag w w, after_ag w w)] 80
     (HDR4G w w 36 (eaddz ITO 2) (- 2 * CG) (- 2 * CG) 17 0xa3f50 0xa3f58 true 0xa5b20 true 0xa5b30 103 80))))))))))).
(* [comment removed for export] *)
Definition GO_pwp (w m : smode) (sv : nat) (ito ix : expr) (c0 : Z) : plan :=
  vprep2 w (szof m sv) ito (EVar (3 + sv)) c0 (szof m sv) ito (EVar (3 + sv)) C4p
    (PRun [0xa74d4] (PHandoffW (HOLE CPWP m) [(62%nat, ito); (63%nat, ix); (64%nat, ELit 0)])).
Definition GO_loops (m : smode) (cnt ito ix : expr) : plan :=
  PRun [0xa80d4] (PHandoffW (HOLE (match m with MS => CSLOOP | ML => CSLOOPL end) m) [(62%nat, cnt); (63%nat, ito); (64%nat, ix)]).
(* [comment removed for export] *)
Definition se_k (w cm m' : smode) : plan :=
  let sz := xszk m' in let mtr := EVar (5 + BK) in
  let c1 := C5 - CG + GEV in
  PFactVia (esub (escale 24 ITOS) xXk) (esub (eaddz (eadd IXJ (escale 2 NK)) 2) xXk) 0 (2 * RELHI)      (* [comment removed for export] *)
  (PFactLe xXk (escale 24 ITOS) BIG
  (vprep2 w sz ITOK mtr c1 sz ITOS mtr c1
  (PCase2 (esub RC J5) 1
     (GO_pwp w m' (2 + BK) ITOS xXk c1)
     (ENSUREg true 254 108 w m' (2 + BK) (eaddz xXk 1) ITOS mtr c1 C5 (JS_sc w) V3c 0xa839c 0xa83a0
              (fun m'' => match cm, m'' with
                          | MS, ML => GO_loops ML (esub (esub RC J5) (ELit 1)) ITOS (eaddz xXk 1)
                          | _, _ => PRun [0xa80d4] PNext
                          end))))).
Definition after_se (w cm m m' : smode) : plan :=
  let sz := szof m V3k in let mtr := EVar (3 + V3k) in
  let c0 := C5 - CG in
  GFIX ((match m' with ML => PExt 13 [EVar (2 + BK)] | MS => fun k => k end)
  (STEP w sz ITOK mtr c0 (xszk m') ITOK (EVar (5 + BK)) (c0 + GEV) (esub (eaddz (escale 6 (esub (xszk m') sz)) GEV) (esub (EVar (5 + BK)) mtr))
  (PFactVia (eaddz (eadd (esub (escale 24 (esub ITOK ITO)) (esub xXk IX)) (escale 2 NK)) 2) (esub (escale 24 (esub ITOK ITO)) (esub IXJ IX)) 71 (2 * RELHI)
  (PRun [0xa831c] (PBranch
     (match cm, m' with
      | MS, ML => PRun [0xa8320] (PHandoffW (HOLE CSEL ML) (IDH [62; 104; 105; 106; 150; 151; 191]%nat))
      | _, _ => se_k w cm m'
      end)
     (EXITP w m' (2 + BK) ITOK (c0 + GEV) ITOK xEk)))))).                                                           (* [comment removed for export] *)
Definition after_sk (w cm m : smode) : plan :=
  PRun [0xa82d8] (PBranch
    (PRun [GaEsc.ENTRY] (PBump BK (CALL m 200 203 (ESC_ARGS m ITOK NK IXJ V3k (EVar (3 + V3k))) (after_se w cm m))))
    (EXITP w m V3k ITOK (C5 - CG) ITOK ERR22)).                                                                     (* [comment removed for export] *)
Definition bodys (w cm m : smode) : plan :=
  PRun [0xa80f8] (PBranch
    (PViaM 106 [(JS_sk w m, after_sk w cm m)] 150 (HDR4G w m V5i ITOJ C5 (C5 - CG) 15 0xa8130 0xa8138 false 0xa8294 false 0xa829c 106 150))
    (EXITP w m V5i ITOJ C5 ITOJ ERR22)).
Definition loopsK (w m : smode) : plan := PLoopM 104 RC [(INVs w m, bodys w m m, PContraH 0)] [(105%nat, ITOL); (106%nat, IXL)].
Definition after_sa0 (w m : smode) : plan :=
  PRun [0xa80a8] (PBranch (GO_loops m NSs ITOHs (eaddz IX 1)) (GO_pwp w m V4s ITOHs (eaddz IX 1) C5)).
Definition strarr (w m : smode) : plan :=
  PRun [0xa6174] (PBranch (EXITP w m V4p ITO1 C4p ITO1 ERR22)
    (PViaM 105 [(JS_sa0 w m, after_sa0 w m)] 110 (HDR4G w m V4p ITO1 C4p C5 15 0xa61b4 0xa61bc true 0xa8078 false 0xa8080 105 110))).
Definition pvt3 (w m : smode) : plan :=
  PRun [0xa52c8] (PBranch
    (PRun [0xa74d4] (PHandoffW (HOLE CPWP m) [(62%nat, ITO1); (63%nat, eaddz IX 1); (64%nat, ERR24)]))        (* [comment removed for export] *)
    (strarr w m)).
Definition after_p1 (w m : smode) : plan :=
  PRun [0xa4780] (PCaseReg 10 0 (GO (CPV 0) m) (PCaseReg 10 1 (GO (CPV 1) m) (PCaseReg 10 2 (GO (CPV 2) m) (pvt3 w m)))).   (* [comment removed for export] *)
Definition plain4 (w : smode) : plan :=
  PRun [0xa42f0] (PExt 42 [] (ENSUREg false 110 100 w w 36 (eaddz IX 1) ITO1 e_mtr (- CG) C4p (JS_p1 w) 64 0xa46d0 0xa46d8 (after_p1 w))).
Definition tag4 (w : smode) : plan := PRun [0xa3e80] (PBranch (aligned4 w) (plain4 w)).
(* [comment removed for export] *)
Definition pwaK (w m : smode) : plan :=
  ENSUREg true 150 9 w m V4w (eaddz wIX 1) wITO (EVar (3 + V4w)) C5 (C5 + GEV) (JS_rbra w) V4r 0xa7e50 0xa7e54
          (fun m' => EXITP w m' V4r wITO (C5 + GEV) wITO wERR).
Definition pwpK (w m : smode) : plan :=
  ENSUREg false 150 9 w m V4w (eaddz wIX 1) wITO (EVar (3 + V4w)) C4p (C4p + GEV) (JS_rbrp w) V4r 0xa7524 0xa752c
          (fun m' => EXITP w m' V4r wITO (C4p + GEV) wITO wERR).
(* [comment removed for export] *)
Definition ext0 (w : smode) : plan :=
  ENSURE 60 w w 36 (eaddz IX 1) ITO1 e_mtr (- CG) (- CG + GEV) (JS_nl w) 62 0xa5e00 0xa5e08 (fun m' => EXITP w m' 62 ITO1 (- CG + GEV) ITO1 (ELit 0)).
(* [comment removed for export] *)
Definition BX : nat := 100.

Definition ext1_post (w : smode) (hl : Z) (m' : smode) : plan :=
  let ito0 := eaddz ITO (1 + hl) in
  let err' := EVar BX in let ito' := EVar (1 + BX) in let mtr' := EVar (6 + BX) in
  TIDY (PFactVia (relE_e ito' (EVar (2 + BX)) err') (esub (eadd (escale 24 (esub ito' ito0)) (escale IXMAX err')) (esub (EVar (2 + BX)) IX)) 1 (2 * RELHI)
       (EXITX m' ito')).
Definition ext1 (w : smode) : plan :=
  let arm (hl : Z) :=
    PExt 42 [] (PRun [0xa421c] (PBranch (EXITX w ITO1)
      (PRun [0xa4254] (PExt 42 [] (PRun [ENTRY] (PBump BX (CALL w 210 213 (SELF_ARGS w (eaddz ITO (1 + hl)) IX 36 e_mtr) (ext1_post w hl)))))))) in
  PRun [0xa41d0] (PBranch (EXITX w ITO1)
    (PRun [0xa4214] (PCaseReg 14 0 (arm 1) (PCaseReg 14 1 (arm 2) (PCaseReg 14 2 (arm 4) (arm 8)))))).
(* [comment removed for export] *)
Definition xsz_at (B : nat) (m' : smode) : expr := match m' with MS => EVar (3 + B) | ML => EVar (4 + B) end.
Definition n13_at (B : nat) (m' : smode) (k : plan) : plan := match m' with ML => PExt 13 [EVar (3 + B)] k | MS => k end.
Definition cpn_e (sz sz' mtr mtr' : expr) : expr := esub (eaddz (escale 6 (esub sz' sz)) GEV) (esub mtr' mtr).     (* [comment removed for export] *)
Definition C6a : Z := - 2 * CG + GEV.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition x3K (w m : smode) : plan :=
  let sz := szof m Vx3 in let mtr := EVar (3 + Vx3) in
  let c2 := C6a + 2 * GEV in
  PRun [GaNumT.BNI] (PBump BX2 (CALL m 230 233 (NUM_ARGS m ITOX1 (eaddz xX1 1) Vx3 NTAG mtr)
    (fun m' =>
       let sz' := xsz_at BX2 m' in let mtr' := EVar (6 + BX2) in
       GFIX (n13_at BX2 m' (PRun [0xa71bc] (PBranch
         (STEP w sz ITOX1 mtr c2 sz' ITOX2 mtr' (c2 + GEV) (cpn_e sz sz' mtr mtr')
         (PFactVia (relx_e ITOX2 xX2) (relx_e ITOX1 xX1) 61 (2 * RELHI)
         (ENSUREg false 240 84 w m' (3 + BX2) (eaddz xX2 1) ITOX2 mtr' (c2 + GEV) (c2 + 2 * GEV) (JS_x5 w) Vx5 0xa7278 0xa7280
                  (fun m'' => EXITP w m'' Vx5 ITOX2 (c2 + 2 * GEV) ITOX2 (ELit 0)))))
         (EXITX m' ITOX2))))))).     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition x1K (w m : smode) : plan :=
  let sz := szof m Vx1 in let mtr := EVar (3 + Vx1) in
  PRun [GaNumT.BNI] (PBump BX1 (CALL m 230 233 (NUM_ARGS m ITO2e (eaddz IX 1) Vx1 NTAG mtr)
    (fun m' =>
       let sz' := xsz_at BX1 m' in let mtr' := EVar (6 + BX1) in
       GFIX (n13_at BX1 m' (PRun [0xa6b04] (PBranch
         (EXITX m' ITOX1)                  (* [comment removed for export] *)
         (STEP w sz ITO2e mtr C6a sz' ITOX1 mtr' (C6a + GEV) (cpn_e sz sz' mtr mtr')
         (PFactVia (relx_e ITOX1 xX1) (relx_e ITO2e IX) 55 (2 * RELHI)
         (ENSUREg false 150 82 w m' (3 + BX1) (eaddz xX1 1) ITOX1 mtr' (C6a + GEV) (C6a + 2 * GEV) (JS_x3 w) Vx3 0xa7100 0xa7108 (x3K w)))))))))).
(* [comment removed for export] *)
Definition GO_loopc (m : smode) (cnt ito ix : expr) : plan :=
  PRun [0xa77dc] (PHandoffW (HOLE (match m with MS => CCLOOP | ML => CCLOOPL end) m) [(62%nat, cnt); (63%nat, ito); (64%nat, EVar 64); (65%nat, ix)]).
Definition GO_closec (w m : smode) (sv : nat) (ito ix : expr) (c0 : Z) : plan :=
  vprep2 w (szof m sv) ito (EVar (3 + sv)) c0 (szof m sv) ito (EVar (3 + sv)) C5
    (PRun [0xa7cb0] (PHandoffW (HOLE CCCLOSE m) [(62%nat, ito); (63%nat, ix)])).
Definition closecK (w m : smode) : plan :=
  ENSUREg true 140 8 w m V5x (eaddz IXC 1) ITOC (EVar (3 + V5x)) C5 (C5 + GEV) (JS_rbc w) V5r 0xa7cfc 0xa7d00
          (fun m' => EXITP w m' V5r ITOC (C5 + GEV) ITOC (ELit 0)).
Definition cb5_k (w cm m : smode) : plan :=
  PCase2 (esub RCc J5) 1
     (GO_closec w m Vc5 ITON2 (eaddz xX2c 1) (C5 - 3 * GEV))
     (ENSUREg true 370 97 w m Vc5 (eaddz xX2c 2) ITON2 (EVar (3 + Vc5)) (C5 - 3 * GEV) C5 (JS_cb6 w) Vc6 0xa7ae4 0xa7ae8
              (fun m'' => match cm, m'' with
                          | MS, ML => GO_loopc ML (esub (esub RCc J5) (ELit 1)) ITON2 (eaddz xX2c 2)
                          | _, _ => PRun [0xa77dc] PNext
                          end)).
Definition cn2_k (w cm m' : smode) : plan :=
  ENSUREg true 296 96 w m' (3 + BN2) (eaddz xX2c 1) ITON2 (EVar (6 + BN2)) (C5 - 4 * GEV) (C5 - 3 * GEV) (JS_cb5 w) Vc5 0xa7a1c 0xa7a20
          (fun m'' => match cm, m'' with MS, ML => GO CCB5L ML | _, _ => cb5_k w cm m'' end).
Definition cb3_k (w cm m : smode) : plan :=
  let sz := szof m Vq2 in let mtr := EVar (3 + Vq2) in
  PRun [GaNumT.BNI] (PBump BN2 (CALL m 230 233 (NUM_ARGS m ITON (eaddz xXn 1) Vq2 NTAG mtr)
    (fun m' =>
       let sz' := xsz_at BN2 m' in let mtr' := EVar (6 + BN2) in
       GFIX (n13_at BN2 m' (PRun [0xa79c8] (PBranch
         (PFact (KRange xD2 1 8)
         (STEP w sz ITON mtr (C5 - GEV) sz' ITON2 mtr' (C5 - 4 * GEV) (cpn_e sz sz' mtr mtr')
         (PFactVia (relx_e ITON2 xX2c) (relx_e ITON xXn) 60 (2 * RELHI)
            (match cm, m' with
             | MS, ML => PRun [0xa79cc] (PHandoffW (HOLE CCN2L ML) (IDH [62; 64; 104; 105; 106; 191; 192; 261; 262]%nat))
             | _, _ => cn2_k w cm m'
             end))))
         (EXITX m' ITON2))))))).     (* [comment removed for export] *)
Definition cn1_k (w cm m' : smode) : plan :=
  ENSUREg true 226 94 w m' (3 + BNK) (eaddz xXn 1) ITON (EVar (6 + BNK)) (C5 - 2 * GEV) (C5 - GEV) (JS_cb3 w) Vq2 0xa7920 0xa7924
          (fun m'' => match cm, m'' with MS, ML => GO CCB3L ML | _, _ => cb3_k w cm m'' end).
Definition cb1_k (w cm m : smode) : plan :=
  let sz := szof m Vq1 in let mtr := EVar (3 + Vq1) in
  PRun [GaNumT.BNI] (PBump BNK (CALL m 230 233 (NUM_ARGS m ITOJ (eaddz IXJ 1) Vq1 NTAG mtr)
    (fun m' =>
       let sz' := xsz_at BNK m' in let mtr' := EVar (6 + BNK) in
       GFIX (n13_at BNK m' (PRun [0xa78d4] (PBranch
         (PFact (KRange xDn 1 8)
         (STEP w sz ITOJ mtr (C5 + GEV) sz' ITON mtr' (C5 - 2 * GEV) (cpn_e sz sz' mtr mtr')
         (PFactVia (relx_e ITON xXn) (relx_e ITOJ IXJ) 54 (2 * RELHI)
            (match cm, m' with
             | MS, ML => PRun [0xa78d8] (PHandoffW (HOLE CCN1L ML) (IDH [62; 64; 104; 105; 106; 191; 192]%nat))
             | _, _ => cn1_k w cm m'
             end))))
         (EXITX m' ITON))))))).        (* [comment removed for export] *)
Definition bodyc (w cm m : smode) : plan :=
  ENSUREg true 190 92 w m V5i (eaddz IXJ 1) ITOJ (EVar (3 + V5i)) C5 (C5 + GEV) (JS_cb1 w) Vq1 0xa7824 0xa7828
          (fun m'' => match cm, m'' with MS, ML => GO CCB1L ML | _, _ => cb1_k w cm m'' end).
Definition loopcK (w m : smode) : plan := PLoopM 104 RCc [(INVca w m, bodyc w m m, PContraH 0)] [(105%nat, ITOLc); (106%nat, IXLc)].
Definition after_ca1 (w m : smode) : plan :=
  PRun [0xa77c0] (PBranch (GO_loopc m NCc ITOHc (eaddz IX 1)) (GO_closec w m Vc1 ITOHc (eaddz IX 1) C5)).
Definition cplx_array (w : smode) : plan :=
  PRun [0xa5e9c] (PBranch (EXITX w ITO2e)
  (PViaM 79 [(JS_ca0 w w, ENSUREg false 180 90 w w Vc0 (eaddz IX 1) ITOHc (EVar (3 + Vc0)) (- 2 * CG) C5 (JS_ca1 w) Vc1 0xa7734 0xa773c (after_ca1 w))] 100
     (HDR4G w w 36 ITO2e (- 2 * CG) (- 2 * CG) 16 0xa5ee0 0xa5ee8 true 0xa76a0 true 0xa76ac 79 100))).
Definition ext3 (w : smode) : plan :=
  PRun [0xa43e0] (PBranch (EXITX w ITO1)
  (PRun [0xa441c] (PBranch (cplx_array w)
     (ENSUREg false 100 80 w w 36 (eaddz IX 1) ITO2e e_mtr (- 2 * CG) C6a (JS_x1 w) Vx1 0xa6a2c 0xa6a34 (fun m' => GO C6X1 m'))))).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENSUREgL (stub_taken : bool) (bump : nat) (j : nat) (w m : smode) (sv : nat) (req ito mtr : expr) (c0 c : Z) (JS : smode -> acs) (lo : nat)
           (bpc back : Z) (k : plan) : plan :=
  let n := escale 2 req in
  let sz := szof m sv in
  let stub :=
       PRun [] (PBump bump (PExt2 (RID m) (RARGS m sv mtr)
          (match m with
           | MS => PContra
           | ML => TIDY (PExt 49 [mtr; sz; n; CPX; ELit 1] (PRun [back] (PMerge j)))
           end)
          (TIDY (PExt 13 [EVar bump] (PExt 49 [mtr; sz; n; CPX; ELit 0] (PRun [back] (PMerge j))))))) in
  let room := PRun [back] (PMerge j) in
  PViaM j [(JS ML, k)] lo (PRun [bpc] (if stub_taken then PBranch room stub else PBranch stub room)).
Definition m7K (w : smode) : plan :=
  let sz := szof ML Vm7 in let mtr := EVar (3 + Vm7) in
  let ix0 := eaddz xXm1 9 in
  PRun [ENTRY]
    (PFactVia (esub (escale 24 xIm1) ix0) (esub (escale 24 ITO) IX) 0 (2 * RELHI)
    (PFactLe ix0 (escale 24 xIm1) BIG
    (PBump BM2 (CALL ML 210 213 (SELF_ARGS ML xIm1 ix0 Vm7 mtr)
      (fun m' =>
         let sz' := xsz_at BM2 m' in let mtr' := EVar (6 + BM2) in let err' := EVar BM2 in
         let cpe := esub (eaddz (eadd (eadd (escale 6 (esub sz' sz)) (escale CG (esub xIm2 xIm1))) (escale GEV err')) (- GEV)) (esub mtr' mtr) in
         TIDY (PRun [0xa70ac] (PBranch
           (STEP w sz xIm1 mtr (G8 6) sz' xIm2 mtr' (G8 5) cpe
           (PFactVia (relx_e xIm2 xXm2) (esub (eadd (escale 24 (esub xIm2 xIm1)) (escale IXMAX err')) (esub xXm2 ix0)) 6 (2 * RELHI)
           (ENSUREg false 440 67 w m' (3 + BM2) (eaddz xXm2 1) xIm2 mtr' (G8 5) (G8 6) (JS_m8 w) Vm8 0xa7388 0xa7390
                    (fun m'' => EXITP w m'' Vm8 xIm2 (G8 6) xIm2 (ELit 0)))))
           (EXITX m' xIm2)))))))).      (* [comment removed for export] *)
Definition m6K (w : smode) : plan :=
  ENSUREg false 350 66 w ML Vm6 (eaddz xXm1 9) xIm1 (EVar (3 + Vm6)) (G8 5) (G8 6) (JS_m7 w) Vm7 0xa6f88 0xa6f90 (fun m' => GO CM7 ML).
Definition m5K (w : smode) : plan :=
  let sz := szof ML Vm5 in let mtr := EVar (3 + Vm5) in
  let ix0 := eaddz IXm 11 in
  PRun [0x6c76c] (PExt 5 [] (PRun [ENTRY]
    (PFactVia (esub (escale 24 ITO2e) ix0) (esub (escale 24 ITO) IX) 0 (2 * RELHI)
    (PFactLe ix0 (escale 24 ITO2e) BIG
    (PBump BM1 (CALL ML 210 213 (SELF_ARGS ML ITO2e ix0 Vm5 mtr)
      (fun m' =>
         let sz' := xsz_at BM1 m' in let mtr' := EVar (6 + BM1) in let err' := EVar BM1 in
         let cpe := esub (eaddz (eadd (eadd (escale 6 (esub sz' sz)) (escale CG (esub xIm1 ITO2e))) (escale GEV err')) (- GEV)) (esub mtr' mtr) in
         TIDY (PRun [0xa6e64] (PBranch
           (EXITX m' xIm1)                    (* [comment removed for export] *)
           (STEP w sz ITO2e mtr (G8 5) sz' xIm1 mtr' (G8 4) cpe
           (PFactVia (relx_e xIm1 xXm1) (esub (eadd (escale 24 (esub xIm1 ITO2e)) (escale IXMAX err')) (esub xXm1 ix0)) 14 (2 * RELHI)
           (ENSUREg false 310 65 w m' (3 + BM1) (eaddz xXm1 1) xIm1 mtr' (G8 4) (G8 5) (JS_m6 w) Vm6 0xa6ebc 0xa6ec4 (fun m'' => GO CM6 ML))))))))))))).
Definition m4K (w : smode) : plan :=
  ENSUREg false 270 64 w ML Vm4 (eaddz IXm 11) ITO2e (EVar (3 + Vm4)) (G8 4) (G8 5) (JS_m5 w) Vm5 0xa6d94 0xa6d9c (fun m' => GO CM5 ML).
Definition m3K (w : smode) (right : bool) : plan :=
  let ix := eaddz IX (if right then 24 else 23) in
  PRun [0x6c76c] (PExt 5 []
    (ENSUREg false 230 63 w ML Vm3 (eaddz ix 1) ITO2e (EVar (3 + Vm3)) (G8 3) (G8 4) (JS_m4 w) 184 0xa6cc8 0xa6cd0 (fun m' => GO CM4 ML))).
Definition m2K (w m : smode) : plan :=
  PRun [0x6c76c] (PExt 5 [] (PRun [0xa60d0] (PBranch
    (ENSUREgL false 190 62 w m Vm2 (eaddz IX 23) ITO2e (EVar (3 + Vm2)) (G8 2) (G8 3) (JS_m3l w) Vm3 0xa6b60 0xa6b68 (GO CM3L ML))
    (ENSUREgL false 190 62 w m Vm2 (eaddz IX 24) ITO2e (EVar (3 + Vm2)) (G8 2) (G8 3) (JS_m3r w) Vm3 0xa6bc0 0xa6bc8 (GO CM3R ML))))).
Definition m1K (w m : smode) : plan :=
  ENSUREg false 150 61 w m Vm1 (eaddz IX 10) ITO2e (EVar (3 + Vm1)) (G8 1) (G8 2) (JS_m2 w) Vm2 0xa6034 0xa603c (fun m' => GO CM2 m').
Definition ext2 (w : smode) : plan :=
  PRun [0xa5158] (PBranch (EXITX w ITO1)
    (ENSUREg false 100 60 w w 36 (eaddz IX 1) ITO2e e_mtr (G8 0) (G8 1) (JS_m1 w) Vm1 0xa5f40 0xa5f48 (fun m' => GO CM1 m'))).
Definition tag6 (w : smode) : plan :=
  PRun [0xa419c] (PCaseReg 11 0 (ext0 w) (PCaseReg 11 1 (ext1 w) (PCaseReg 11 2 (ext2 w) (PCaseReg 11 3 (ext3 w)
                 (PRun [0xa50b8] (PBranch (EXITX w ITO) (EXITX w ITO))))))).     (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CUT (t : acs) (k : plan) : plan := PViaM 199 [(t, k)] (nxt t) (PMerge 199).
(* [comment removed for export] *)
Definition dead (cs : acs) : acs := set_kn cs (KRange (ELit 1) 0 0 :: kn cs).
Definition cutT (w : smode) (c : nat) (m : smode) : option acs :=
  match c with
  | 0 => Some (T5 w m) | 1 => Some (TC5 w m)
  | 2 => match m with MS => Some (T3 w m) | ML => None end
  | 4 => match w, m with MS, ML => Some (JS_key w m) | _, _ => None end            (* [comment removed for export] *)
  | 5 => match w, m with MS, ML => Some (JS_colon w m) | _, _ => None end
  | 6 => match w, m with MS, ML => Some (JS_oval w m) | _, _ => None end
  | 7 => match m with ML => Some (T3 w m) | MS => None end
  | 10 => match m with MS => Some (Tn w m) | ML => None end
  | 11 => match w, m with MS, ML => Some (JS_q1 w m) | _, _ => None end
  | 12 => match w, m with MS, ML => Some (JS_num w m) | _, _ => None end
  | 13 => match w, m with MS, ML => Some (JS_q2 w m) | _, _ => None end
  | 14 => match w, m with MS, ML => Some (JS_c2 w m) | _, _ => None end
  | 15 => match w, m with MS, ML => Some (JS_nval w m) | _, _ => None end
  | 16 => match m with ML => Some (Tn w m) | MS => None end
  | 17 => Some (TC3 w m)
  | 20 => Some (ABs 0 w m) | 21 => Some (ABs 1 w m) | 22 => Some (ABs 2 w m)
  | 23 => Some (PVs 0 w m) | 24 => Some (PVs 1 w m) | 25 => Some (PVs 2 w m)
  | 28 => match m with MS => Some (Ts w m) | ML => None end
  | 29 => match w, m with MS, ML => Some (JS_se w m) | _, _ => None end
  | 30 => match m with ML => Some (Ts w m) | MS => None end
  | 3 => match m with MS => Some (Tca w m) | ML => None end
  | 8 => match w, m with MS, ML => Some (JS_cb1 w m) | _, _ => None end
  | 9 => match w, m with MS, ML => Some (JS_cn1 w m) | _, _ => None end
  | 18 => match w, m with MS, ML => Some (JS_cb3 w m) | _, _ => None end
  | 19 => match w, m with MS, ML => Some (JS_cn2 w m) | _, _ => None end
  | 32 => match w, m with MS, ML => Some (JS_cb5 w m) | _, _ => None end
  | 33 => match m with ML => Some (Tca w m) | MS => None end
  | 36 => Some (TCc w m)
  | 31 => Some (JS_x1 w m)
  | 40 => Some (JS_m1 w m) | 41 => Some (JS_m2 w m)
  | 42 => match m with ML => Some (JS_m3l w m) | MS => None end
  | 43 => match m with ML => Some (JS_m3r w m) | MS => None end
  | 44 => match m with ML => Some (JS_m4 w m) | MS => None end
  | 45 => match m with ML => Some (JS_m5 w m) | MS => None end
  | 46 => match m with ML => Some (JS_m6 w m) | MS => None end
  | 47 => match m with ML => Some (JS_m7 w m) | MS => None end
  | 34 => Some (TPWA w m) | 35 => Some (TPWP w m)
  | 59 => Some (EPI w m)
  | _ => None end%nat.
Definition cutK (w : smode) (c : nat) (m : smode) : plan :=
  match c with
  | 0 => loop5K w m | 1 => close5K w m
  | 2 => loop3K w m | 4 => key_k w MS ML | 5 => after_colon w MS ML | 6 => oval_k w MS ML | 7 => loop3K w m
  | 10 => loopnK w m | 11 => after_q1 w MS ML | 12 => num_k w MS ML | 13 => after_q2 w MS ML | 14 => after_c2 w MS ML | 15 => nval_k w MS ML | 16 => loopnK w m
  | 17 => close3K w m
  | 20 => avt w m 0 | 21 => avt w m 1 | 22 => avt w m 2 | 23 => pvt w m 0 | 24 => pvt w m 1 | 25 => pvt w m 2
  | 28 => loopsK w m | 29 => se_k w MS ML | 30 => loopsK w m
  | 3 => loopcK w m | 8 => cb1_k w MS ML | 9 => cn1_k w MS ML | 18 => cb3_k w MS ML | 19 => cn2_k w MS ML | 32 => cb5_k w MS ML | 33 => loopcK w m
  | 36 => closecK w m
  | 31 => x1K w m
  | 40 => m1K w m | 41 => m2K w m | 42 => m3K w false | 43 => m3K w true | 44 => m4K w | 45 => m5K w | 46 => m6K w | 47 => m7K w
  | 34 => pwaK w m | 35 => pwpK w m
  | 59 => EPIK m
  | _ => PContraH 0 end%nat.
(* [comment removed for export] *)
Definition cut_entry (w : smode) (c : nat) (m : smode) : acs * plan :=
  match m with
  | ML => match cutT ML c ML with
          | Some t => (t, CUT t (cutK ML c ML))
          | None => match w, cutT w c ML with
                    | MS, Some t => (t, CUT t (cutK w c ML))
                    | _, _ => (dead (tin w), PContraH 0)
                    end
          end
  | MS => match w, cutT w c MS with
          | MS, Some t => (t, CUT t (cutK w c MS))
          | _, _ => (dead (tin w), PContraH 0)           (* [comment removed for export] *)
          end
  end.
Fixpoint cut_entries (w : smode) (c n : nat) : list (acs * plan) :=
  match n with O => [] | Datatypes.S n' => cut_entry w c MS :: cut_entry w c ML :: cut_entries w (Datatypes.S c) n' end.
Definition tagk (k : nat) (w : smode) : plan :=
  match k with
  | 0 => tag0 w w | 1 => tag1 w | 2 => tag2 w | 3 => tag3 w | 4 => tag4 w | 5 => tag5 w | 6 => tag6 w
  | _ => PContra                                                   (* [comment removed for export] *)
  end%nat.
Definition CUTS (w : smode) : list (acs * plan) :=
  map (fun k => (ATs (Z.of_nat k) w, PRun [] (tagk k w))) (seq 0 7) ++ cut_entries w 0 NCUT.

(* [comment removed for export] *)
Definition CUTS_ML : list (acs * plan) := CUTS ML.
Definition CUTS_MS : list (acs * plan) := CUTS MS.
Definition CUTSc (w : smode) : list (acs * plan) := match w with ML => CUTS_ML | MS => CUTS_MS end.
Lemma CUTSc_eq : forall w, CUTSc w = CUTS w.
Proof. intros [|]; reflexivity. Qed.

(* [comment removed for export] *)
Definition cert_stmt (w : smode) (i : nat) : Prop :=
  match nth_error (CUTS w) i with
  | Some (T, k) => exists sh, gplan_ok k = true /\ holes_only sh = true /\
      check ASEGS IT AASAN (ce_nxf (ce w)) LIMIT ISP0 (XN w) XE0 (XB w) (HScut (ce w) (CUTS w) (Datatypes.S i)) 0%nat BFUEL FUELB None T k = COk sh
  | None => True
  end.
Definition top_stmt (w : smode) : Prop :=
  exists sh, gplan_ok (top w) = true /\ holes_only sh = true /\
      check ASEGS IT AASAN (ce_nxf (ce w)) LIMIT ISP0 (XN w) XE0 (XB w) (HScut (ce w) (CUTS w) 0) 0%nat BFUEL FUELB None (ce_tin (ce w)) (top w) = COk sh.
(* [comment removed for export] *)
Lemma okb_sound_gen : forall (c : cres) (g : bool),
  match c with COk sh => g && holes_only sh | _ => false end = true ->
  exists sh, g = true /\ holes_only sh = true /\ c = COk sh.
Proof.
  intros c g H. destruct c as [sh|? ? ?]; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2]. exists sh. split; [exact H1|]. split; [exact H2|]. reflexivity.
Qed.
Definition cert_okb (w : smode) (i : nat) : bool :=
  match nth_error (CUTSc w) i with
  | Some (T, k) =>
      match check ASEGS IT AASAN (ce_nxf (ce w)) LIMIT ISP0 (XN w) XE0 (XB w) (HScut (ce w) (CUTSc w) (Datatypes.S i)) 0%nat BFUEL FUELB None T k with
      | COk sh => gplan_ok k && holes_only sh
      | _ => false
      end
  | None => true
  end.
Lemma cert_okb_sound : forall w i, cert_okb w i = true -> cert_stmt w i.
Proof.
  intros w i. unfold cert_okb, cert_stmt. rewrite !CUTSc_eq.
  generalize (nth_error (CUTS w) i). intros o. destruct o as [[T k]|]; [|intros _; exact I].
  intros H. exact (okb_sound_gen _ _ H).
Qed.
Definition top_okb (w : smode) : bool :=
  match check ASEGS IT AASAN (ce_nxf (ce w)) LIMIT ISP0 (XN w) XE0 (XB w) (HScut (ce w) (CUTSc w) 0) 0%nat BFUEL FUELB None (ce_tin (ce w)) (top w) with
  | COk sh => gplan_ok (top w) && holes_only sh
  | _ => false
  end.
Lemma top_okb_sound : forall w, top_okb w = true -> top_stmt w.
Proof. intros w. unfold top_okb, top_stmt. rewrite CUTSc_eq. intros H. exact (okb_sound_gen _ _ H). Qed.


End GaB2J.
Module GaB2JcM6.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaB2J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma b2j_cert_ML_126 : cert_stmt ML 126.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_top_ML : top_stmt ML.
Proof. apply top_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_125 : cert_stmt MS 125.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_top_MS : top_stmt MS.
Proof. apply top_okb_sound. vm_cast_no_check (eq_refl true). Qed.
End GaB2JcM6.
Module GaB2JcM7.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaB2J.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition b2j_dead_ML : list nat := [7; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 41; 43; 44; 45; 46; 47; 49; 51; 53; 55; 57; 59; 60; 61; 62; 63; 64; 65; 66; 67; 69; 71; 72; 73; 75; 77; 79; 81; 82; 83; 84; 85; 86; 87; 89; 91; 93; 95; 97; 99; 101; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122; 123; 124; 125]%nat.
Definition b2j_okb_with_ML (cuts : list (acs * plan)) (i : nat) : bool :=
  match nth_error cuts i with
  | Some (T, k) =>
      match check ASEGS IT AASAN (ce_nxf (ce ML)) LIMIT ISP0 (XN ML) XE0 (XB ML) (HScut (ce ML) cuts (Datatypes.S i)) 0%nat BFUEL FUELB None T k with
      | COk sh => gplan_ok k && holes_only sh
      | _ => false
      end
  | None => true
  end.
Lemma b2j_okb_with_ML_eq : forall i, b2j_okb_with_ML (CUTS ML) i = cert_okb ML i.
Proof. intros i. reflexivity. Qed.
Definition b2j_dead_okb_ML : bool := let cuts := CUTS ML in forallb (b2j_okb_with_ML cuts) b2j_dead_ML.
Lemma b2j_dead_ok_ML : b2j_dead_okb_ML = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_dead_sound_ML : forall i, existsb (Nat.eqb i) b2j_dead_ML = true -> cert_stmt ML i.
Proof.
  intros i H. apply cert_okb_sound. rewrite <- b2j_okb_with_ML_eq.
  pose proof b2j_dead_ok_ML as A. unfold b2j_dead_okb_ML in A. cbv zeta in A. rewrite forallb_forall in A.
  apply existsb_exists in H. destruct H as [x [Hx E]]. apply Nat.eqb_eq in E. subst x. exact (A i Hx).
Qed.
Lemma b2j_cert_ML_7 : cert_stmt ML 7.
Proof. exact (b2j_dead_sound_ML 7 eq_refl). Qed.
Lemma b2j_cert_ML_9 : cert_stmt ML 9.
Proof. exact (b2j_dead_sound_ML 9 eq_refl). Qed.
Lemma b2j_cert_ML_11 : cert_stmt ML 11.
Proof. exact (b2j_dead_sound_ML 11 eq_refl). Qed.
Lemma b2j_cert_ML_12 : cert_stmt ML 12.
Proof. exact (b2j_dead_sound_ML 12 eq_refl). Qed.
Lemma b2j_cert_ML_13 : cert_stmt ML 13.
Proof. exact (b2j_dead_sound_ML 13 eq_refl). Qed.
Lemma b2j_cert_ML_14 : cert_stmt ML 14.
Proof. exact (b2j_dead_sound_ML 14 eq_refl). Qed.
Lemma b2j_cert_ML_15 : cert_stmt ML 15.
Proof. exact (b2j_dead_sound_ML 15 eq_refl). Qed.
Lemma b2j_cert_ML_16 : cert_stmt ML 16.
Proof. exact (b2j_dead_sound_ML 16 eq_refl). Qed.
Lemma b2j_cert_ML_17 : cert_stmt ML 17.
Proof. exact (b2j_dead_sound_ML 17 eq_refl). Qed.
Lemma b2j_cert_ML_18 : cert_stmt ML 18.
Proof. exact (b2j_dead_sound_ML 18 eq_refl). Qed.
Lemma b2j_cert_ML_19 : cert_stmt ML 19.
Proof. exact (b2j_dead_sound_ML 19 eq_refl). Qed.
Lemma b2j_cert_ML_20 : cert_stmt ML 20.
Proof. exact (b2j_dead_sound_ML 20 eq_refl). Qed.
Lemma b2j_cert_ML_21 : cert_stmt ML 21.
Proof. exact (b2j_dead_sound_ML 21 eq_refl). Qed.
Lemma b2j_cert_ML_23 : cert_stmt ML 23.
Proof. exact (b2j_dead_sound_ML 23 eq_refl). Qed.
Lemma b2j_cert_ML_24 : cert_stmt ML 24.
Proof. exact (b2j_dead_sound_ML 24 eq_refl). Qed.
Lemma b2j_cert_ML_25 : cert_stmt ML 25.
Proof. exact (b2j_dead_sound_ML 25 eq_refl). Qed.
Lemma b2j_cert_ML_26 : cert_stmt ML 26.
Proof. exact (b2j_dead_sound_ML 26 eq_refl). Qed.
Lemma b2j_cert_ML_27 : cert_stmt ML 27.
Proof. exact (b2j_dead_sound_ML 27 eq_refl). Qed.
Lemma b2j_cert_ML_28 : cert_stmt ML 28.
Proof. exact (b2j_dead_sound_ML 28 eq_refl). Qed.
Lemma b2j_cert_ML_29 : cert_stmt ML 29.
Proof. exact (b2j_dead_sound_ML 29 eq_refl). Qed.
Lemma b2j_cert_ML_30 : cert_stmt ML 30.
Proof. exact (b2j_dead_sound_ML 30 eq_refl). Qed.
Lemma b2j_cert_ML_31 : cert_stmt ML 31.
Proof. exact (b2j_dead_sound_ML 31 eq_refl). Qed.
Lemma b2j_cert_ML_32 : cert_stmt ML 32.
Proof. exact (b2j_dead_sound_ML 32 eq_refl). Qed.
Lemma b2j_cert_ML_33 : cert_stmt ML 33.
Proof. exact (b2j_dead_sound_ML 33 eq_refl). Qed.
Lemma b2j_cert_ML_34 : cert_stmt ML 34.
Proof. exact (b2j_dead_sound_ML 34 eq_refl). Qed.
Lemma b2j_cert_ML_35 : cert_stmt ML 35.
Proof. exact (b2j_dead_sound_ML 35 eq_refl). Qed.
Lemma b2j_cert_ML_36 : cert_stmt ML 36.
Proof. exact (b2j_dead_sound_ML 36 eq_refl). Qed.
Lemma b2j_cert_ML_37 : cert_stmt ML 37.
Proof. exact (b2j_dead_sound_ML 37 eq_refl). Qed.
Lemma b2j_cert_ML_38 : cert_stmt ML 38.
Proof. exact (b2j_dead_sound_ML 38 eq_refl). Qed.
Lemma b2j_cert_ML_39 : cert_stmt ML 39.
Proof. exact (b2j_dead_sound_ML 39 eq_refl). Qed.
Lemma b2j_cert_ML_41 : cert_stmt ML 41.
Proof. exact (b2j_dead_sound_ML 41 eq_refl). Qed.
Lemma b2j_cert_ML_43 : cert_stmt ML 43.
Proof. exact (b2j_dead_sound_ML 43 eq_refl). Qed.
Lemma b2j_cert_ML_44 : cert_stmt ML 44.
Proof. exact (b2j_dead_sound_ML 44 eq_refl). Qed.
Lemma b2j_cert_ML_45 : cert_stmt ML 45.
Proof. exact (b2j_dead_sound_ML 45 eq_refl). Qed.
Lemma b2j_cert_ML_46 : cert_stmt ML 46.
Proof. exact (b2j_dead_sound_ML 46 eq_refl). Qed.
Lemma b2j_cert_ML_47 : cert_stmt ML 47.
Proof. exact (b2j_dead_sound_ML 47 eq_refl). Qed.
Lemma b2j_cert_ML_49 : cert_stmt ML 49.
Proof. exact (b2j_dead_sound_ML 49 eq_refl). Qed.
Lemma b2j_cert_ML_51 : cert_stmt ML 51.
Proof. exact (b2j_dead_sound_ML 51 eq_refl). Qed.
Lemma b2j_cert_ML_53 : cert_stmt ML 53.
Proof. exact (b2j_dead_sound_ML 53 eq_refl). Qed.
Lemma b2j_cert_ML_55 : cert_stmt ML 55.
Proof. exact (b2j_dead_sound_ML 55 eq_refl). Qed.
Lemma b2j_cert_ML_57 : cert_stmt ML 57.
Proof. exact (b2j_dead_sound_ML 57 eq_refl). Qed.
Lemma b2j_cert_ML_59 : cert_stmt ML 59.
Proof. exact (b2j_dead_sound_ML 59 eq_refl). Qed.
Lemma b2j_cert_ML_60 : cert_stmt ML 60.
Proof. exact (b2j_dead_sound_ML 60 eq_refl). Qed.
Lemma b2j_cert_ML_61 : cert_stmt ML 61.
Proof. exact (b2j_dead_sound_ML 61 eq_refl). Qed.
Lemma b2j_cert_ML_62 : cert_stmt ML 62.
Proof. exact (b2j_dead_sound_ML 62 eq_refl). Qed.
Lemma b2j_cert_ML_63 : cert_stmt ML 63.
Proof. exact (b2j_dead_sound_ML 63 eq_refl). Qed.
Lemma b2j_cert_ML_64 : cert_stmt ML 64.
Proof. exact (b2j_dead_sound_ML 64 eq_refl). Qed.
Lemma b2j_cert_ML_65 : cert_stmt ML 65.
Proof. exact (b2j_dead_sound_ML 65 eq_refl). Qed.
Lemma b2j_cert_ML_66 : cert_stmt ML 66.
Proof. exact (b2j_dead_sound_ML 66 eq_refl). Qed.
Lemma b2j_cert_ML_67 : cert_stmt ML 67.
Proof. exact (b2j_dead_sound_ML 67 eq_refl). Qed.
Lemma b2j_cert_ML_69 : cert_stmt ML 69.
Proof. exact (b2j_dead_sound_ML 69 eq_refl). Qed.
Lemma b2j_cert_ML_71 : cert_stmt ML 71.
Proof. exact (b2j_dead_sound_ML 71 eq_refl). Qed.
Lemma b2j_cert_ML_72 : cert_stmt ML 72.
Proof. exact (b2j_dead_sound_ML 72 eq_refl). Qed.
Lemma b2j_cert_ML_73 : cert_stmt ML 73.
Proof. exact (b2j_dead_sound_ML 73 eq_refl). Qed.
Lemma b2j_cert_ML_75 : cert_stmt ML 75.
Proof. exact (b2j_dead_sound_ML 75 eq_refl). Qed.
Lemma b2j_cert_ML_77 : cert_stmt ML 77.
Proof. exact (b2j_dead_sound_ML 77 eq_refl). Qed.
Lemma b2j_cert_ML_79 : cert_stmt ML 79.
Proof. exact (b2j_dead_sound_ML 79 eq_refl). Qed.
Lemma b2j_cert_ML_81 : cert_stmt ML 81.
Proof. exact (b2j_dead_sound_ML 81 eq_refl). Qed.
Lemma b2j_cert_ML_82 : cert_stmt ML 82.
Proof. exact (b2j_dead_sound_ML 82 eq_refl). Qed.
Lemma b2j_cert_ML_83 : cert_stmt ML 83.
Proof. exact (b2j_dead_sound_ML 83 eq_refl). Qed.
Lemma b2j_cert_ML_84 : cert_stmt ML 84.
Proof. exact (b2j_dead_sound_ML 84 eq_refl). Qed.
Lemma b2j_cert_ML_85 : cert_stmt ML 85.
Proof. exact (b2j_dead_sound_ML 85 eq_refl). Qed.
Lemma b2j_cert_ML_86 : cert_stmt ML 86.
Proof. exact (b2j_dead_sound_ML 86 eq_refl). Qed.
Lemma b2j_cert_ML_87 : cert_stmt ML 87.
Proof. exact (b2j_dead_sound_ML 87 eq_refl). Qed.
Lemma b2j_cert_ML_89 : cert_stmt ML 89.
Proof. exact (b2j_dead_sound_ML 89 eq_refl). Qed.
Lemma b2j_cert_ML_91 : cert_stmt ML 91.
Proof. exact (b2j_dead_sound_ML 91 eq_refl). Qed.
Lemma b2j_cert_ML_93 : cert_stmt ML 93.
Proof. exact (b2j_dead_sound_ML 93 eq_refl). Qed.
Lemma b2j_cert_ML_95 : cert_stmt ML 95.
Proof. exact (b2j_dead_sound_ML 95 eq_refl). Qed.
Lemma b2j_cert_ML_97 : cert_stmt ML 97.
Proof. exact (b2j_dead_sound_ML 97 eq_refl). Qed.
Lemma b2j_cert_ML_99 : cert_stmt ML 99.
Proof. exact (b2j_dead_sound_ML 99 eq_refl). Qed.
Lemma b2j_cert_ML_101 : cert_stmt ML 101.
Proof. exact (b2j_dead_sound_ML 101 eq_refl). Qed.
Lemma b2j_cert_ML_103 : cert_stmt ML 103.
Proof. exact (b2j_dead_sound_ML 103 eq_refl). Qed.
Lemma b2j_cert_ML_104 : cert_stmt ML 104.
Proof. exact (b2j_dead_sound_ML 104 eq_refl). Qed.
Lemma b2j_cert_ML_105 : cert_stmt ML 105.
Proof. exact (b2j_dead_sound_ML 105 eq_refl). Qed.
Lemma b2j_cert_ML_106 : cert_stmt ML 106.
Proof. exact (b2j_dead_sound_ML 106 eq_refl). Qed.
Lemma b2j_cert_ML_107 : cert_stmt ML 107.
Proof. exact (b2j_dead_sound_ML 107 eq_refl). Qed.
Lemma b2j_cert_ML_108 : cert_stmt ML 108.
Proof. exact (b2j_dead_sound_ML 108 eq_refl). Qed.
Lemma b2j_cert_ML_109 : cert_stmt ML 109.
Proof. exact (b2j_dead_sound_ML 109 eq_refl). Qed.
Lemma b2j_cert_ML_110 : cert_stmt ML 110.
Proof. exact (b2j_dead_sound_ML 110 eq_refl). Qed.
Lemma b2j_cert_ML_111 : cert_stmt ML 111.
Proof. exact (b2j_dead_sound_ML 111 eq_refl). Qed.
Lemma b2j_cert_ML_112 : cert_stmt ML 112.
Proof. exact (b2j_dead_sound_ML 112 eq_refl). Qed.
Lemma b2j_cert_ML_113 : cert_stmt ML 113.
Proof. exact (b2j_dead_sound_ML 113 eq_refl). Qed.
Lemma b2j_cert_ML_114 : cert_stmt ML 114.
Proof. exact (b2j_dead_sound_ML 114 eq_refl). Qed.
Lemma b2j_cert_ML_115 : cert_stmt ML 115.
Proof. exact (b2j_dead_sound_ML 115 eq_refl). Qed.
Lemma b2j_cert_ML_116 : cert_stmt ML 116.
Proof. exact (b2j_dead_sound_ML 116 eq_refl). Qed.
Lemma b2j_cert_ML_117 : cert_stmt ML 117.
Proof. exact (b2j_dead_sound_ML 117 eq_refl). Qed.
Lemma b2j_cert_ML_118 : cert_stmt ML 118.
Proof. exact (b2j_dead_sound_ML 118 eq_refl). Qed.
Lemma b2j_cert_ML_119 : cert_stmt ML 119.
Proof. exact (b2j_dead_sound_ML 119 eq_refl). Qed.
Lemma b2j_cert_ML_120 : cert_stmt ML 120.
Proof. exact (b2j_dead_sound_ML 120 eq_refl). Qed.
Lemma b2j_cert_ML_121 : cert_stmt ML 121.
Proof. exact (b2j_dead_sound_ML 121 eq_refl). Qed.
Lemma b2j_cert_ML_122 : cert_stmt ML 122.
Proof. exact (b2j_dead_sound_ML 122 eq_refl). Qed.
Lemma b2j_cert_ML_123 : cert_stmt ML 123.
Proof. exact (b2j_dead_sound_ML 123 eq_refl). Qed.
Lemma b2j_cert_ML_124 : cert_stmt ML 124.
Proof. exact (b2j_dead_sound_ML 124 eq_refl). Qed.
Lemma b2j_cert_ML_125 : cert_stmt ML 125.
Proof. exact (b2j_dead_sound_ML 125 eq_refl). Qed.

(* [comment removed for export] *)
Definition b2j_dead_MS : list nat := [12; 14; 15; 17; 19; 21; 23; 25; 28; 29; 31; 33; 35; 37; 39; 43; 45; 59; 60; 61; 62; 64; 65; 67; 71; 73; 81; 82; 83; 84; 85; 86; 91; 93; 95; 97; 99; 101; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122; 123; 124]%nat.
Definition b2j_okb_with_MS (cuts : list (acs * plan)) (i : nat) : bool :=
  match nth_error cuts i with
  | Some (T, k) =>
      match check ASEGS IT AASAN (ce_nxf (ce MS)) LIMIT ISP0 (XN MS) XE0 (XB MS) (HScut (ce MS) cuts (Datatypes.S i)) 0%nat BFUEL FUELB None T k with
      | COk sh => gplan_ok k && holes_only sh
      | _ => false
      end
  | None => true
  end.
Lemma b2j_okb_with_MS_eq : forall i, b2j_okb_with_MS (CUTS MS) i = cert_okb MS i.
Proof. intros i. reflexivity. Qed.
Definition b2j_dead_okb_MS : bool := let cuts := CUTS MS in forallb (b2j_okb_with_MS cuts) b2j_dead_MS.
Lemma b2j_dead_ok_MS : b2j_dead_okb_MS = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma b2j_dead_sound_MS : forall i, existsb (Nat.eqb i) b2j_dead_MS = true -> cert_stmt MS i.
Proof.
  intros i H. apply cert_okb_sound. rewrite <- b2j_okb_with_MS_eq.
  pose proof b2j_dead_ok_MS as A. unfold b2j_dead_okb_MS in A. cbv zeta in A. rewrite forallb_forall in A.
  apply existsb_exists in H. destruct H as [x [Hx E]]. apply Nat.eqb_eq in E. subst x. exact (A i Hx).
Qed.
Lemma b2j_cert_MS_12 : cert_stmt MS 12.
Proof. exact (b2j_dead_sound_MS 12 eq_refl). Qed.
Lemma b2j_cert_MS_14 : cert_stmt MS 14.
Proof. exact (b2j_dead_sound_MS 14 eq_refl). Qed.
Lemma b2j_cert_MS_15 : cert_stmt MS 15.
Proof. exact (b2j_dead_sound_MS 15 eq_refl). Qed.
Lemma b2j_cert_MS_17 : cert_stmt MS 17.
Proof. exact (b2j_dead_sound_MS 17 eq_refl). Qed.
Lemma b2j_cert_MS_19 : cert_stmt MS 19.
Proof. exact (b2j_dead_sound_MS 19 eq_refl). Qed.
Lemma b2j_cert_MS_21 : cert_stmt MS 21.
Proof. exact (b2j_dead_sound_MS 21 eq_refl). Qed.
Lemma b2j_cert_MS_23 : cert_stmt MS 23.
Proof. exact (b2j_dead_sound_MS 23 eq_refl). Qed.
Lemma b2j_cert_MS_25 : cert_stmt MS 25.
Proof. exact (b2j_dead_sound_MS 25 eq_refl). Qed.
Lemma b2j_cert_MS_28 : cert_stmt MS 28.
Proof. exact (b2j_dead_sound_MS 28 eq_refl). Qed.
Lemma b2j_cert_MS_29 : cert_stmt MS 29.
Proof. exact (b2j_dead_sound_MS 29 eq_refl). Qed.
Lemma b2j_cert_MS_31 : cert_stmt MS 31.
Proof. exact (b2j_dead_sound_MS 31 eq_refl). Qed.
Lemma b2j_cert_MS_33 : cert_stmt MS 33.
Proof. exact (b2j_dead_sound_MS 33 eq_refl). Qed.
Lemma b2j_cert_MS_35 : cert_stmt MS 35.
Proof. exact (b2j_dead_sound_MS 35 eq_refl). Qed.
Lemma b2j_cert_MS_37 : cert_stmt MS 37.
Proof. exact (b2j_dead_sound_MS 37 eq_refl). Qed.
Lemma b2j_cert_MS_39 : cert_stmt MS 39.
Proof. exact (b2j_dead_sound_MS 39 eq_refl). Qed.
Lemma b2j_cert_MS_43 : cert_stmt MS 43.
Proof. exact (b2j_dead_sound_MS 43 eq_refl). Qed.
Lemma b2j_cert_MS_45 : cert_stmt MS 45.
Proof. exact (b2j_dead_sound_MS 45 eq_refl). Qed.
Lemma b2j_cert_MS_59 : cert_stmt MS 59.
Proof. exact (b2j_dead_sound_MS 59 eq_refl). Qed.
Lemma b2j_cert_MS_60 : cert_stmt MS 60.
Proof. exact (b2j_dead_sound_MS 60 eq_refl). Qed.
Lemma b2j_cert_MS_61 : cert_stmt MS 61.
Proof. exact (b2j_dead_sound_MS 61 eq_refl). Qed.
Lemma b2j_cert_MS_62 : cert_stmt MS 62.
Proof. exact (b2j_dead_sound_MS 62 eq_refl). Qed.
Lemma b2j_cert_MS_64 : cert_stmt MS 64.
Proof. exact (b2j_dead_sound_MS 64 eq_refl). Qed.
Lemma b2j_cert_MS_65 : cert_stmt MS 65.
Proof. exact (b2j_dead_sound_MS 65 eq_refl). Qed.
Lemma b2j_cert_MS_67 : cert_stmt MS 67.
Proof. exact (b2j_dead_sound_MS 67 eq_refl). Qed.
Lemma b2j_cert_MS_71 : cert_stmt MS 71.
Proof. exact (b2j_dead_sound_MS 71 eq_refl). Qed.
Lemma b2j_cert_MS_73 : cert_stmt MS 73.
Proof. exact (b2j_dead_sound_MS 73 eq_refl). Qed.
Lemma b2j_cert_MS_81 : cert_stmt MS 81.
Proof. exact (b2j_dead_sound_MS 81 eq_refl). Qed.
Lemma b2j_cert_MS_82 : cert_stmt MS 82.
Proof. exact (b2j_dead_sound_MS 82 eq_refl). Qed.
Lemma b2j_cert_MS_83 : cert_stmt MS 83.
Proof. exact (b2j_dead_sound_MS 83 eq_refl). Qed.
Lemma b2j_cert_MS_84 : cert_stmt MS 84.
Proof. exact (b2j_dead_sound_MS 84 eq_refl). Qed.
Lemma b2j_cert_MS_85 : cert_stmt MS 85.
Proof. exact (b2j_dead_sound_MS 85 eq_refl). Qed.
Lemma b2j_cert_MS_86 : cert_stmt MS 86.
Proof. exact (b2j_dead_sound_MS 86 eq_refl). Qed.
Lemma b2j_cert_MS_91 : cert_stmt MS 91.
Proof. exact (b2j_dead_sound_MS 91 eq_refl). Qed.
Lemma b2j_cert_MS_93 : cert_stmt MS 93.
Proof. exact (b2j_dead_sound_MS 93 eq_refl). Qed.
Lemma b2j_cert_MS_95 : cert_stmt MS 95.
Proof. exact (b2j_dead_sound_MS 95 eq_refl). Qed.
Lemma b2j_cert_MS_97 : cert_stmt MS 97.
Proof. exact (b2j_dead_sound_MS 97 eq_refl). Qed.
Lemma b2j_cert_MS_99 : cert_stmt MS 99.
Proof. exact (b2j_dead_sound_MS 99 eq_refl). Qed.
Lemma b2j_cert_MS_101 : cert_stmt MS 101.
Proof. exact (b2j_dead_sound_MS 101 eq_refl). Qed.
Lemma b2j_cert_MS_103 : cert_stmt MS 103.
Proof. exact (b2j_dead_sound_MS 103 eq_refl). Qed.
Lemma b2j_cert_MS_104 : cert_stmt MS 104.
Proof. exact (b2j_dead_sound_MS 104 eq_refl). Qed.
Lemma b2j_cert_MS_105 : cert_stmt MS 105.
Proof. exact (b2j_dead_sound_MS 105 eq_refl). Qed.
Lemma b2j_cert_MS_106 : cert_stmt MS 106.
Proof. exact (b2j_dead_sound_MS 106 eq_refl). Qed.
Lemma b2j_cert_MS_107 : cert_stmt MS 107.
Proof. exact (b2j_dead_sound_MS 107 eq_refl). Qed.
Lemma b2j_cert_MS_108 : cert_stmt MS 108.
Proof. exact (b2j_dead_sound_MS 108 eq_refl). Qed.
Lemma b2j_cert_MS_109 : cert_stmt MS 109.
Proof. exact (b2j_dead_sound_MS 109 eq_refl). Qed.
Lemma b2j_cert_MS_110 : cert_stmt MS 110.
Proof. exact (b2j_dead_sound_MS 110 eq_refl). Qed.
Lemma b2j_cert_MS_111 : cert_stmt MS 111.
Proof. exact (b2j_dead_sound_MS 111 eq_refl). Qed.
Lemma b2j_cert_MS_112 : cert_stmt MS 112.
Proof. exact (b2j_dead_sound_MS 112 eq_refl). Qed.
Lemma b2j_cert_MS_113 : cert_stmt MS 113.
Proof. exact (b2j_dead_sound_MS 113 eq_refl). Qed.
Lemma b2j_cert_MS_114 : cert_stmt MS 114.
Proof. exact (b2j_dead_sound_MS 114 eq_refl). Qed.
Lemma b2j_cert_MS_115 : cert_stmt MS 115.
Proof. exact (b2j_dead_sound_MS 115 eq_refl). Qed.
Lemma b2j_cert_MS_116 : cert_stmt MS 116.
Proof. exact (b2j_dead_sound_MS 116 eq_refl). Qed.
Lemma b2j_cert_MS_117 : cert_stmt MS 117.
Proof. exact (b2j_dead_sound_MS 117 eq_refl). Qed.
Lemma b2j_cert_MS_118 : cert_stmt MS 118.
Proof. exact (b2j_dead_sound_MS 118 eq_refl). Qed.
Lemma b2j_cert_MS_119 : cert_stmt MS 119.
Proof. exact (b2j_dead_sound_MS 119 eq_refl). Qed.
Lemma b2j_cert_MS_120 : cert_stmt MS 120.
Proof. exact (b2j_dead_sound_MS 120 eq_refl). Qed.
Lemma b2j_cert_MS_121 : cert_stmt MS 121.
Proof. exact (b2j_dead_sound_MS 121 eq_refl). Qed.
Lemma b2j_cert_MS_122 : cert_stmt MS 122.
Proof. exact (b2j_dead_sound_MS 122 eq_refl). Qed.
Lemma b2j_cert_MS_123 : cert_stmt MS 123.
Proof. exact (b2j_dead_sound_MS 123 eq_refl). Qed.
Lemma b2j_cert_MS_124 : cert_stmt MS 124.
Proof. exact (b2j_dead_sound_MS 124 eq_refl). Qed.
End GaB2JcM7.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaB2J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma b2j_cert_MS_32 : cert_stmt MS 32.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_34 : cert_stmt MS 34.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_36 : cert_stmt MS 36.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_38 : cert_stmt MS 38.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_41 : cert_stmt MS 41.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_44 : cert_stmt MS 44.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_46 : cert_stmt MS 46.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_47 : cert_stmt MS 47.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_49 : cert_stmt MS 49.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_51 : cert_stmt MS 51.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_53 : cert_stmt MS 53.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_55 : cert_stmt MS 55.
Proof. apply cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
