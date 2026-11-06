(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT.GaDedup OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require GaNumT GaEsc GaAA GaWA.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require GaAAi8 GaAAi16 GaAAi32 GaAAi64 GaAAu8 GaAAu16 GaAAu32 GaAAu64 GaAAf32 GaAAf64.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require GaWAi8 GaWAi16 GaWAi32 GaWAi64 GaWAu8 GaWAu16 GaWAu32 GaWAu64 GaWAf32 GaWAf64.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GaB2JT.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AAcfg (k : nat) : GaAA.acfg :=
  nth k [GaAAi8.cfg; GaAAi16.cfg; GaAAi32.cfg; GaAAi64.cfg; GaAAu8.cfg; GaAAu16.cfg; GaAAu32.cfg; GaAAu64.cfg; GaAAf32.cfg; GaAAf64.cfg] GaAAi8.cfg.
Definition WAcfg (k : nat) : GaWA.acfg :=
  nth k [GaWAi8.cfg; GaWAi16.cfg; GaWAi32.cfg; GaWAi64.cfg; GaWAu8.cfg; GaWAu16.cfg; GaWAu32.cfg; GaWAu64.cfg; GaWAf32.cfg; GaWAf64.cfg] GaWAi8.cfg.
(* [comment removed for export] *)
Definition CT0 (id : nat) : option gcallee :=
  if Nat.eqb id 203 then Some GaEsc.ceL1 else if Nat.eqb id 223 then Some (GaNumT.ceL1 GaNumT.BNU) else if Nat.eqb id 233 then Some (GaNumT.ceL1 GaNumT.BNI)
  else if (Nat.leb 310 id && Nat.ltb id 320)%bool then Some (GaAA.ceL1 (AAcfg (id - 310)))
  else if (Nat.leb 330 id && Nat.ltb id 340)%bool then Some (GaWA.ceL1 (WAcfg (id - 330))) else None.
Definition CTs (id : nat) : option gcallee := if Nat.eqb id 213 then Some ceL1 else CT0 id.
Definition XN (m : smode) : nat -> list expr -> acs -> option acs :=
  match m with
  | ML => XNw (XNd (XNp (XNr_gen ASEGS AASAN GASAN NXF BCAP CCAP 213 14 ceL1 (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CT0))))
  | MS => XNw (XNd (XNp (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CTs)))
  end.
Definition CT2 (id : nat) : option gcallee2 :=
  if Nat.eqb id 200 then Some (GaEsc.ce2 MS) else if Nat.eqb id 220 then Some (GaNumT.ce2 MS GaNumT.BNU) else if Nat.eqb id 230 then Some (GaNumT.ce2 MS GaNumT.BNI)
  else if (Nat.leb 300 id && Nat.ltb id 310)%bool then Some (GaAA.ce2 (AAcfg (id - 300)) MS)
  else if (Nat.leb 320 id && Nat.ltb id 330)%bool then Some (GaWA.ce2 (WAcfg (id - 320)) MS) else CT2_resize id.
Definition XB (m : smode) : nat -> list expr -> acs -> option (acs * acs) :=
  match m with
  | MS => XBr_gen ASEGS AASAN GASAN NXF BCAP CCAP 14 210 (ce2 MS) (XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2)
  | ML => XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2
  end.
Definition FUELB : nat := 20000.

(* [comment removed for export] *)
Definition F_facts : list kentry :=
  [ KRange F PTRLO (PTRHI - 64); KRange (eaddz F 64) (PTRLO + 64) PTRHI; KAlign F 64; KWr (SA F 0) (ELit 64); KUnk (SA F 0) (ELit 64);
    KUnk (SA shF SB) (ELit 8); KWr (SA shF SB) (ELit 8);
    KDisj (SA shF SB) (ELit 8) (SA (ELit 0) (SB + IMG_LO / 8)) (ELit (IMG_SZ / 8));
    flo F 0 (ELit 64); img_apart F 0 (ELit 64); shmap_apart F 0 (ELit 64);
    KDisj (SA F 0) (ELit 64) (SA G 0) (ELit 4); KDisj (SA F 0) (ELit 64) (SA G 32) (ELit 4); KDisj (SA F 0) (ELit 64) (SA PEND 0) (ELit 8); KDisj (SA F 0) (ELit 64) (SA PIT 0) (ELit 8);
    KDisj (SA F 0) (ELit 64) (SA PIX 0) (ELit 8); KDisj (SA F 0) (ELit 64) (SA OBJ 0) (ELit 24); KDisj (SA F 0) (ELit 64) (SA INLO 0) BSZ;
    KDisj (SA F 0) (ELit 64) (SA SLO 0) XD ].

(* [comment removed for export] *)
Fixpoint assocn (l : list (nat * expr)) (i : nat) : option expr :=
  match l with [] => None | (j, x) :: r => if Nat.eqb i j then Some x else assocn r i end.
(* [comment removed for export] *)
Fixpoint jregs (rss : list (list expr)) (i n : nat) (ov : list (nat * expr)) (keep v : nat) : list expr :=
  match n with
  | O => []
  | Datatypes.S n' =>
      let col := map (fun rs => nth i rs (ELit 0)) rss in
      match assocn ov i with
      | Some x => x :: jregs rss (Datatypes.S i) n' ov keep v
      | None =>
          match col with
          | e :: r => if (forallb (expr_eqb e) r && expr_vars_lt keep e)%bool then e :: jregs rss (Datatypes.S i) n' ov keep v
                      else EVar v :: jregs rss (Datatypes.S i) n' ov keep (Datatypes.S v)
          | [] => EVar v :: jregs rss (Datatypes.S i) n' ov keep (Datatypes.S v)
          end
      end
  end.
(* [comment removed for export] *)
Definition is_frame_word (keep : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w x => (expr_eqb b e_sp && Z.leb (- FR) o && Z.ltb o 0 && negb (Z.eqb o (-176)) && negb (Z.eqb o (-168)) || expr_eqb b F) && expr_vars_lt keep x     (* [comment removed for export] *)
  | _ => false
  end.
Definition jframe (ss : list acs) (keep : nat) : list kentry :=
  match ss with
  | [] => []
  | s0 :: r => List.filter (fun K => is_frame_word keep K && forallb (fun s => existsb (kentry_eqb K) (kn s)) r)%bool (kn s0)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint maxvar_regs (rs : list expr) (acc : nat) : nat :=
  match rs with [] => acc | EVar i :: r => maxvar_regs r (Nat.max acc (Datatypes.S i)) | _ :: r => maxvar_regs r acc end.
Definition JT (ss : list acs) (p : Z) (ov : list (nat * expr)) (keep v : nat) (facts : list kentry) (vs : list (expr * expr)) (mtr : expr) : acs :=
  let rs := jregs (map (fun s => s_regs (a_ss s)) ss) 0 32 ov keep v in
  mkcs p rs (jframe ss keep ++ facts) (maxvar_regs rs v) vs mtr [(F, ELit 64)] (eaddz e_fb (-1)).

(* [comment removed for export] *)
Definition caller_saved : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition fake_ret (ret : Z) (cs : acs) : acs :=
  let ss := a_ss cs in
  with_ss cs (mk_ss ret (sr_havoc (s_regs ss) caller_saved (nxt cs)) (kn cs) (nxt cs + 16)%nat).

(* [comment removed for export] *)
Definition TAGv : expr := EExt false 0 1 (EVar 60).          (* [comment removed for export] *)
Definition TAG7 : expr := EAlu ALU_AND TAGv (ELit 7).
Definition KEEP : nat := 62.                                 (* [comment removed for export] *)
Definition REL : Z := 0xa7f20.                               (* [comment removed for export] *)
Definition hole (m : smode) : nat := match m with MS => 0 | ML => 1 end%nat.
(* [comment removed for export] *)
Definition HOLE (c : nat) (m : smode) : nat := (9 + 2 * c + match m with MS => 0 | ML => 1 end)%nat.
Definition NCUT : nat := 60.
Definition CEPI : nat := 59.
Definition C5LOOP : nat := 0.        (* [comment removed for export] *)
Definition C5CLOSE : nat := 1.       (* [comment removed for export] *)
Definition EPIPC : Z := 0xa7eec.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition EV : nat := 62.
Definition eERR : expr := EVar 62.  Definition eITO : expr := EVar 63.  Definition eIX : expr := EVar 64.
Definition DPATH (m : smode) := dpath ASEGS IT AASAN (XN m) (XB m) BFUEL.
Definition pre : list dstep := [DRun []; DExt 50 [ELit 0]; DExt 47 []; DRun []; DBrT; DRun []; DBrT; DRun []].
(* [comment removed for export] *)
Definition P0c : acs * acs := Eval vm_compute in (snd (DPATH MS NXF (tin MS) pre 0), snd (DPATH ML NXF (tin ML) pre 0)).
Definition p0 (m : smode) : acs := match m with MS => fst P0c | ML => snd P0c end.
(* [comment removed for export] *)
Definition ATs_d (k : Z) (m : smode) : acs :=
  snd (DPATH m NXF (p0 m) ((DLo TAG7 k :: (if Z.eqb k 0 then [] else [DHi TAG7 (k - 1)])) ++ [DExt 42 []]) 0).
Definition ATc : list acs * list acs := Eval vm_compute in (map (fun k => ATs_d k MS) [0; 1; 2; 3; 4; 5; 6], map (fun k => ATs_d k ML) [0; 1; 2; 3; 4; 5; 6]).
Definition ATs (k : Z) (m : smode) : acs := nth (Z.to_nat k) (match m with MS => fst ATc | ML => snd ATc end) (tin m).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tri (f : smode -> smode -> acs) : acs * acs := (f MS MS, f ML ML).
Definition sel3 (t : acs * acs) (w m : smode) : acs := match m with MS => fst t | ML => snd t end.
(* [comment removed for export] *)
Definition RID (m : smode) : nat := match m with MS => 104%nat | ML => 114%nat end.
Definition RARGS (m : smode) (sv : nat) (mtr : expr) : list expr :=
  match m with MS => resize_args_S (EVar sv) mtr (eaddz e_fb (-1)) | ML => resize_args_L (EVar sv) (EVar (1 + sv)) (EVar (2 + sv)) mtr (eaddz e_fb (-1)) end.
Definition room (m : smode) (req : expr) (v : nat) : list kentry :=
  match m with
  | MS => [KRange (esub (EVar v) req) 0 22]
  | ML => [KRange (esub (escale 8 (EVar (2 + v))) (eaddz req 1)) 0 (8 * AHI); KRange (esub (EVar (1 + v)) req) 0 (8 * AHI)]
  end.
Definition szof (m : smode) (v : nat) : expr := match m with MS => EVar v | ML => EVar (1 + v) end.




Definition mfacts (w m : smode) (v : nat) (ito mtr : expr) (c : Z) : list kentry :=      (* [comment removed for export] *)
  [ ] ++ pw_facts CPX (szof m v) mtr ++ [ KRange mtr 0 MTRTOP ]
  ++ match m with MS => [KRange (szin w) 0 SZMAX] | ML => [] end.


(* [comment removed for export] *)
Definition site_statesP (stub_taken : bool) (m : smode) (S0 : acs) (path : list dstep) (bpc back stubret : Z) : list acs :=
  let s1 := snd (DPATH m NXF S0 (path ++ [DRun [bpc]]) 0) in
  let a := snd (DPATH m NXF s1 [if stub_taken then DBrF else DBrT; DRun [back]] 0) in
  let b0 := snd (DPATH m NXF s1 [if stub_taken then DBrT else DBrF; DRun []] 0) in
  let b := snd (DPATH m NXF (fake_ret stubret b0) [DRun [back]] 0) in
  [a; b].
Definition site_states := site_statesP false.
(* [comment removed for export] *)
Definition blkF (m : smode) (v : nat) : list kentry :=
  match m with MS => [] | ML => [KDisj (SA F 0) (ELit 64) (SA (EVar v) 0) (escale 8 (EVar (2 + v)))] end.
(* [comment removed for export] *)
Definition JSGk (keep : nat) (psg : expr -> expr -> expr -> Z -> Z -> list kentry) (w m : smode) (ss : list acs) (p : Z) (ov : list (nat * expr))
           (err ito ix : expr) (k rlo c : Z) (extra : list kentry) (v : nat) : acs :=
  JT ss p ov keep (4 + v)
     ([KRange DEPTH 0 255; stk_shok; rel ito ix rlo] ++ extra ++ mfacts w m v ito (EVar (3 + v)) c
      ++ psg ito ix err k BIG ++ str m ix ito err v ++ blkF m v ++ F_facts ++ kn_fixed)
     (vis m v) (EVar (3 + v)).
Definition JSG := JSGk KEEP.
(* [comment removed for export] *)
Definition JSEk (keep : nat) (psg : expr -> expr -> expr -> Z -> Z -> list kentry) (w m : smode) (ss : list acs) (p : Z) (err ito ix req : expr) (k rlo c : Z)
           (extra : list kentry) (v : nat) : acs :=
  JSGk keep psg w m ss p [] err ito ix k rlo c (room m req v ++ extra) v.
Definition JSE := JSEk KEEP.
(* [comment removed for export] *)
Definition havoc_all : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition ST_epi (m : smode) : list acs :=
  let s := snd (DPATH m NXF (tin m) [DRun []; DExt 50 [ELit 0]; DExt 47 []; DRun []; DBrF; DRun [EPIPC]] 0) in
  [s; with_ss s (mk_ss (pc s) (sr_havoc (s_regs (a_ss s)) havoc_all (nxt s)) (kn s) (nxt s + 26)%nat)].
Definition EPI_d (w m : smode) : acs :=
  let v := (3 + EV)%nat in let mtr := EVar (3 + v) in
  let s0 := hd (tin m) (ST_epi m) in
  JT (ST_epi m) EPIPC [(21, reg s0 21); (22, reg s0 22); (27, reg s0 27)]%nat KEEP (4 + v)
     ([ KRange eERR 0 255; relE eITO eIX eERR 1; KRange (eadd (esub eITO ITO) eERR) 1 (INSZ + 255)
        ] ++ pw_facts CPX (szof m v) mtr ++ [ KRange mtr 0 MTRTOP ]
      ++ pos0 eITO eIX eERR 0 IXMAX ++ str m eIX eITO eERR v ++ blkF m v ++ F_facts ++ kn_fixed)
     (vis m v) mtr.
Definition EPI_c := Eval vm_compute in tri EPI_d.
Definition EPI := sel3 EPI_c.

(* [comment removed for export] *)
Definition BUMP1 : nat := 100.
(* [comment removed for export] *)
Definition A0 (m : smode) : acs := ATs 0 m.
Definition ST_null (m : smode) := site_states m (A0 m) [DRun []; DBrF] 0xa47d4 0xa47dc 0xa86b0.
Definition JS_null_c := Eval vm_compute in tri (fun w m => JSE pos0 w m (ST_null m) 0xa47dc (ELit 0) ITO IX (eaddz IX 4) 1 0 GEV [] 62).
Definition JS_null := sel3 JS_null_c.
Definition ST_false (m : smode) := site_states m (A0 m) [DRun []; DBrT; DRun []; DBrF] 0xa51f0 0xa51f8 0xa87a8.
Definition JS_false_c := Eval vm_compute in tri (fun w m => JSE pos0 w m (ST_false m) 0xa51f8 (ELit 0) ITO IX (eaddz IX 5) 1 0 GEV [] 62).
Definition JS_false := sel3 JS_false_c.
Definition ST_true (m : smode) := site_states m (A0 m) [DRun []; DBrT; DRun []; DBrT] 0xa524c 0xa5254 0xa87c0.
Definition JS_true_c := Eval vm_compute in tri (fun w m => JSE pos0 w m (ST_true m) 0xa5254 (ELit 0) ITO IX (eaddz IX 4) 1 0 GEV [] 62).
Definition JS_true := sel3 JS_true_c.
Definition TPL : expr := CPX.      (* [comment removed for export] *)
Definition FB1 : expr := eaddz e_fb (-1).                   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NUM_ARGS (m : smode) (ito ix : expr) (sv : nat) (tagv mtr : expr) : list expr :=
  [TPL; ito; esub (esub BSZ ito) (ELit 0); ix] ++
  (match m with MS => [EVar sv; ELit 0; ELit 0] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end) ++ [ELit 0; INLO; tagv; mtr; FB1].
Definition BN : nat := 100.
(* [comment removed for export] *)
Definition HL : expr := EVar 62.      (* [comment removed for export] *)
Definition NS : expr := EVar 63.      (* [comment removed for export] *)
Definition ITOH : expr := eadd (eaddz ITO 1) HL.
Definition hdr_path (cfg : Z) (ld chk chk8 jn : Z) : list dstep :=
  [DRun []; DBrT; DRun [ld]] ++ (if Z.eqb cfg 0 then [DRLo 16 0] else [DRHi 16 (cfg - 1)] ++ (if Z.eqb cfg 3 then [] else [DRLo 16 cfg]))
  ++ [DExt 42 []; DRun [chk]; DBrT] ++ (if Z.eqb cfg 3 then [DRun [chk8]; DBrT] else []) ++ [DRun [jn]].
(* [comment removed for export] *)
Definition ST_hdr2 (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (ATs 2 m) (hdr_path cfg 0xa3ffc 0xa4004 0xa4a60 0xa4a6c) 0)) [0; 1; 2; 3].
Definition JS_hdr_c := Eval vm_compute in tri (fun w m =>
  JSG pos w m (ST_hdr2 m) 0xa4a6c [(18%nat, NS)] (ELit 0) ITOH IX 0 48 (- 2 * CG) [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NS 0 (2 ^ 50)] 64).
Definition JS_hdr := sel3 JS_hdr_c.
Definition ERR22 : expr := ELit 22.
Definition BE : nat := 100.
Definition ESC_ARGS (m : smode) (ito n ix : expr) (sv : nat) (mtr : expr) : list expr :=
  [TPL; ito; n; BSZ; ix; INLO] ++ (match m with MS => [EVar sv; ELit 0; ELit 0] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end) ++ [mtr; FB1].
(* [comment removed for export] *)
Definition NV : expr := EVar 63.
Definition K5 : nat := 64.            (* [comment removed for export] *)
Definition ST_ahdr (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (ATs 5 m) (hdr_path cfg 0xa4150 0xa4158 0xa4c10 0xa4c24) 0)) [0; 1; 2; 3].
Definition hdr5 (nlo : Z) : list kentry := [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NV nlo (2 ^ 48)].
Definition JS_ahdr_c := Eval vm_compute in tri (fun w m => JSG pos w m (ST_ahdr m) 0xa4c24 [(27%nat, NV)] (ELit 0) ITOH IX 0 48 (- 2 * CG) (hdr5 0) 64).
Definition JS_ahdr := sel3 JS_ahdr_c.
Definition C5 : Z := - 2 * CG + GEV.
Definition V5b : nat := 80.
Definition JS_lbr_c := Eval vm_compute in tri (fun w m =>
  JSEk K5 pos w m (site_states m (JS_ahdr m m) [] 0xa4cbc 0xa4cc4 0xa8634) 0xa4cc4 (ELit 0) ITOH IX (eaddz IX 1) 0 48 C5 (hdr5 0) V5b).
Definition JS_lbr := sel3 JS_lbr_c.
(* [comment removed for export] *)
Definition RC : expr := EVar 62.  Definition ITOL : expr := EVar 63.  Definition IXL : expr := EVar 64.
Definition V5t : nat := 65.
Definition SELF_ARGS (m : smode) (ito ix : expr) (sv : nat) (mtr : expr) : list expr :=
  [TPL; ito; ELit 0; BSZ; ix; INLO] ++ (match m with MS => [EVar sv; ELit 0; ELit 0] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end) ++ [mtr; FB1].
(* [comment removed for export] *)
Definition ST5_first (m : smode) : acs := snd (DPATH m NXF (JS_lbr m m) [DRun [0xa4d50]; DBrF; DRun [0xa4da0]] 0).
Definition ST5_ret (m : smode) : acs := fake_ret 0xa4dc0 (snd (DPATH m NXF (ST5_first m) [DRun [ENTRY]] 0)).
Definition ST5_second (m : smode) : acs := snd (DPATH m NXF (ST5_ret m) [DRun []; DBrF; DRun [0xa4e28]; DBrF; DRun [0xa4da0]] 0).
Definition loop_facts (w m : smode) (cnt ito ix : expr) (v : nat) : list kentry :=
  [KRange DEPTH 0 255; stk_shok; KRange ITO 0 (INSZ - 2); KRange cnt 1 (2 ^ 48); KRange ito 0 INSZ; rel ito ix 47]
  ++ mfacts w m v ito (EVar (3 + v)) C5 ++ pos ito ix (ELit 0) 0 BIG ++ str m ix ito (ELit 0) v ++ blkF m v ++ F_facts ++ kn_fixed.
Definition T5_c := Eval vm_compute in tri (fun w m =>
  JT [ST5_first m; ST5_second m] 0xa4da0 [(27%nat, RC)] KEEP (4 + V5t) (loop_facts w m RC ITOL IXL V5t) (vis m V5t) (EVar (3 + V5t))).
Definition T5 := sel3 T5_c.
(* [comment removed for export] *)
Definition J5 : expr := EVar 104.  Definition ITOJ : expr := EVar 105.  Definition IXJ : expr := EVar 106.
Definition V5i : nat := 107.
Definition K5L : nat := 63.           (* [comment removed for export] *)
Definition INV5_c := Eval vm_compute in tri (fun w m =>
  JT [ST5_first m; ST5_second m] 0xa4da0 [(27%nat, esub RC J5)] KEEP (4 + V5i)
     (KRange RC 1 (2 ^ 48) :: loop_facts w m (esub RC J5) ITOJ IXJ V5i) (vis m V5i) (EVar (3 + V5i))).
Definition INV5 := sel3 INV5_c.
Definition B5 : nat := 150.
Definition xE5 : expr := EVar 150.  Definition xI5 : expr := EVar 151.  Definition xX5 : expr := EVar 152.
(* [comment removed for export] *)
Definition V5c : nat := 176.
Definition ITO2 : expr := EVar 176.  Definition IX2 : expr := EVar 177.
Definition ST5_iret (m : smode) : acs := fake_ret 0xa4dc0 (snd (DPATH m NXF (INV5 m m) [DRun [ENTRY]] 0)).
Definition ST5_comma (m : smode) : list acs := site_statesP true m (ST5_iret m) [DRun []; DBrF] 0xa4e28 0xa4e2c 0xa4ec0.
Definition JS_comma_c := Eval vm_compute in tri (fun w m =>
  JSGk K5L pos w m (ST5_comma m) 0xa4e2c [(27%nat, esub RC J5)] (ELit 0) ITO2 IX2 0 48 C5
       (room m (eaddz IX2 1) (2 + V5c) ++ [KRange ITO 0 (INSZ - 2); KRange RC 1 (2 ^ 48); KRange (esub RC J5) 2 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange ITO2 0 INSZ]) (2 + V5c)).
Definition JS_comma := sel3 JS_comma_c.
(* [comment removed for export] *)
Definition ITOC : expr := EVar 62.  Definition IXC : expr := EVar 63.
Definition V5x : nat := 64.
Definition ST5_close (m : smode) : list acs :=
  [snd (DPATH m NXF (JS_lbr m m) [DRun [0xa4d50]; DBrT; DRun [0xa4efc]] 0); snd (DPATH m NXF (ST5_iret m) [DRun []; DBrT; DRun [0xa4efc]] 0)].
Definition TC5_c := Eval vm_compute in tri (fun w m =>
  JT (ST5_close m) 0xa4efc [] KEEP (4 + V5x)
     ([KRange DEPTH 0 255; stk_shok; KRange ITO 0 (INSZ - 2); KRange ITOC 0 INSZ; rel ITOC IXC 2]
      ++ mfacts w m V5x ITOC (EVar (3 + V5x)) C5 ++ pos ITOC IXC (ELit 0) 0 BIG ++ str m IXC ITOC (ELit 0) V5x ++ blkF m V5x ++ F_facts ++ kn_fixed)
     (vis m V5x) (EVar (3 + V5x))).
Definition TC5 := sel3 TC5_c.
(* [comment removed for export] *)
Definition V5r : nat := 100.
Definition JS_rbr_c := Eval vm_compute in tri (fun w m =>
  JSEk K5 pos w m (site_states m (TC5 m m) [] 0xa4f50 0xa4f58 0xa8650) 0xa4f58 (ELit 0) ITOC IXC (eaddz IXC 1) 0 2 (C5 + GEV)
       [KRange ITO 0 (INSZ - 2); KRange ITOC 0 INSZ] V5r).
Definition JS_rbr := sel3 JS_rbr_c.
Definition xsz5 (m' : smode) : expr := match m' with MS => EVar (3 + B5) | ML => EVar (4 + B5) end.
(* [comment removed for export] *)
Definition hdr_pathG (pre : list dstep) (r : nat) (cfg : Z) (ld chk : Z) (chk_ok_taken : bool) (chk8 : Z) (chk8_ok_taken : bool) (jn : Z) : list dstep :=
  pre ++ [DRun [ld]] ++ (if Z.eqb cfg 0 then [DRLo r 0] else [DRHi r (cfg - 1)] ++ (if Z.eqb cfg 3 then [] else [DRLo r cfg]))
  ++ [DExt 42 []; DRun [chk]; if chk_ok_taken then DBrT else DBrF]
  ++ (if Z.eqb cfg 3 then [DRun [chk8]; if chk8_ok_taken then DBrT else DBrF] else []) ++ [DRun [jn]].
(* [comment removed for export] *)
Definition C3LOOP : nat := 2.  Definition CKEYL : nat := 4.  Definition CCOLL : nat := 5.  Definition COVALL : nat := 6.
Definition C3LOOPL : nat := 7.  Definition C3CLOSE : nat := 17.     (* [comment removed for export] *)
Definition C3a : Z := - CG + GEV.     (* [comment removed for export] *)
Definition ITO1 : expr := eaddz ITO 1.
Definition JS_lcb_c := Eval vm_compute in tri (fun w m =>
  JSE pos w m (site_states m (ATs 3 m) [] 0xa4374 0xa437c 0xa8594) 0xa437c (ELit 0) ITO1 IX (eaddz IX 1) 0 24 C3a [] 62).
Definition JS_lcb := sel3 JS_lcb_c.
(* [comment removed for export] *)
Definition HL3 : expr := EVar 100.  Definition NF : expr := EVar 101.
Definition V3h : nat := 102.
Definition ITOH3 : expr := eadd ITO1 HL3.
Definition pre3s : list dstep := [DRun [0xa4500]; DBrT; DRun [0xa45a4]; DBrT; DRun [0xa48f0]; DBrF].
Definition ST_ohdr (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (JS_lcb m m) (hdr_pathG pre3s 15 cfg 0xa4934 0xa493c false 0xa62e0 true 0xa62ec) 0)) [0; 1; 2; 3].
Definition JS_ohdr_c := Eval vm_compute in tri (fun w m =>
  JSG pos w m (ST_ohdr m) 0xa62ec [(27%nat, NF)] (ELit 0) ITOH3 (eaddz IX 1) 0 47 C5 [KRange HL3 1 8; KRange ITO 0 (INSZ - 2); KRange NF 0 (2 ^ 48)] V3h).
Definition JS_ohdr := sel3 JS_ohdr_c.
(* [comment removed for export] *)
Definition ST3_first (m : smode) : acs := snd (DPATH m NXF (JS_ohdr m m) [DRun [0xa6330]; DBrF; DRun [0xa6368]] 0).
Definition ST3_esc (m : smode) (s0 : acs) : acs :=
  fake_ret 0xa65a4 (snd (DPATH m NXF s0 [DRun [0xa638c]; DBrT; DRun [0xa63c4]; DRLo 15 0; DExt 42 []; DRun [0xa63cc]; DBrT; DRun [0xa657c]; DBrT; DRun [GaEsc.ENTRY]] 0)).
Definition ST3_self (m : smode) (s0 : acs) : acs := fake_ret 0xa66bc (snd (DPATH m NXF (ST3_esc m s0) [DRun [0xa6608]; DBrF; DRun [ENTRY]] 0)).
Definition ST3_second (m : smode) : acs := snd (DPATH m NXF (ST3_self m (ST3_first m)) [DRun [0xa66e0]; DBrF; DRun [0xa672c]; DBrF; DRun [0xa6368]] 0).
Definition T3_c := Eval vm_compute in tri (fun w m =>
  JT [ST3_first m; ST3_second m] 0xa6368 [(27%nat, RC)] KEEP (4 + V5t) (loop_facts w m RC ITOL IXL V5t) (vis m V5t) (EVar (3 + V5t))).
Definition T3 := sel3 T3_c.
Definition INV3_c := Eval vm_compute in tri (fun w m =>
  JT [ST3_first m; ST3_second m] 0xa6368 [(27%nat, esub RC J5)] KEEP (4 + V5i)
     (KRange RC 1 (2 ^ 48) :: loop_facts w m (esub RC J5) ITOJ IXJ V5i) (vis m V5i) (EVar (3 + V5i))).
Definition INV3 := sel3 INV3_c.
(* [comment removed for export] *)
Definition HLK : expr := EVar 150.  Definition NK : expr := EVar 151.
Definition V3k : nat := 152.
Definition ITOK : expr := eadd ITOJ HLK.
Definition pre3k : list dstep := [DRun [0xa638c]; DBrT].
Definition ST_khdr (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (INV3 m m) (hdr_pathG pre3k 15 cfg 0xa63c4 0xa63cc true 0xa6538 true 0xa6544) 0)) [0; 1; 2; 3].
Definition kfacts : list kentry :=
  [KRange ITO 0 (INSZ - 2); KRange RC 1 (2 ^ 48); KRange (esub RC J5) 1 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange ITOJ 0 INSZ; iixE ITOJ IXJ (ELit 0); KRange IXJ 0 BIG].
Definition JS_khdr_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (ST_khdr m) 0xa6544 [(20%nat, NK); (27%nat, esub RC J5)] (ELit 0) ITOK IXJ 0 71 (C5 - CG)
       (kfacts ++ [KRange HLK 1 8; KRange NK 0 (2 ^ 50)]) V3k).
Definition JS_khdr := sel3 JS_khdr_c.
(* [comment removed for export] *)
Definition BK : nat := 190.
Definition xEk : expr := EVar 190.  Definition xXk : expr := EVar 191.
Definition V3c : nat := 216.
Definition ST3_kret (m : smode) : acs := ST3_esc m (INV3 m m).

          (* [comment removed for export] *)
Definition colon_facts : list kentry :=
  kfacts ++ [KRange HLK 1 8; KRange NK 0 INSZ; KRange (esub BSZ (eadd ITOK NK)) 0 INSZ; KRange xXk 0 IXMAX;
             KRange (esub (eaddz (eadd IXJ (escale 2 NK)) 2) xXk) 0 IXMAX].
(* [comment removed for export] *)
Definition relK (ix : expr) (lo : Z) : kentry := KRange (eadd (esub (escale 24 (esub ITOK ITO)) (esub ix IX)) (escale 2 NK)) lo RELHI.
Definition posK (ito ix err : expr) (ixhi : Z) : list kentry :=
  [ KWord (SA G 0) 4 err; KWord (SA PIT 0) 8 (eadd INLO ito); KRange ito 0 INSZ; KRange (esub BSZ ito) 0 INSZ;
    KWord (SA PIX 0) 8 ix; KRange ix 0 ixhi; iixE ITO IX (ELit 0); KRange (esub ito ITO) 1 INSZ ].
Definition JS_colon_c := Eval vm_compute in tri (fun w m =>
  JT (site_statesP true m (ST3_kret m) [] 0xa6608 0xa660c 0xa67d0) 0xa660c [(20%nat, NK); (27%nat, esub RC J5)] 107 (4 + V3c)     (* [comment removed for export] *)
     ([KRange DEPTH 0 255; stk_shok; relK xXk 69] ++ room m (eaddz xXk 1) V3c ++ colon_facts ++ mfacts w m V3c ITOK (EVar (3 + V3c)) (C5 - CG + 2 * GEV)
      ++ posK ITOK xXk (ELit 0) IXMAX ++ str m xXk (eadd ITOK NK) (ELit 0) V3c ++ blkF m V3c ++ F_facts ++ kn_fixed)
     (vis m V3c) (EVar (3 + V3c))).
Definition JS_colon := sel3 JS_colon_c.
(* [comment removed for export] *)
Definition BV : nat := 260.
Definition xEv : expr := EVar 260.  Definition xIv : expr := EVar 261.  Definition xXv : expr := EVar 262.
Definition V3m : nat := 290.
Definition ITO3 : expr := EVar 290.  Definition IX3 : expr := EVar 291.
Definition ST3_vret (m : smode) : acs := ST3_self m (INV3 m m).
Definition JS_ocomma_c := Eval vm_compute in tri (fun w m =>
  JSGk K5L pos w m (site_statesP true m (ST3_vret m) [DRun [0xa66e0]; DBrF] 0xa672c 0xa6730 0xa67e4) 0xa6730 [(27%nat, esub RC J5)] (ELit 0) ITO3 IX3 0 48 C5
       (room m (eaddz IX3 1) (2 + V3m) ++ [KRange ITO 0 (INSZ - 2); KRange RC 1 (2 ^ 48); KRange (esub RC J5) 2 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange ITO3 0 INSZ]) (2 + V3m)).
Definition JS_ocomma := sel3 JS_ocomma_c.
(* [comment removed for export] *)
Definition ST3_kretJ (m : smode) : acs := fake_ret 0xa65a4 (snd (DPATH m NXF (JS_khdr m m) [DRun [0xa657c]; DBrT; DRun [GaEsc.ENTRY]] 0)).
Definition JS_key_c := Eval vm_compute in tri (fun w m =>
  JT [snd (DPATH m NXF (ST3_kretJ m) [DRun [0xa65c0]] 0)] 0xa65c0 [(20%nat, NK); (27%nat, esub RC J5)] 107 (4 + (2 + BK))
     ([KRange DEPTH 0 255; stk_shok; relK xXk 69] ++ colon_facts ++ mfacts w m (2 + BK) ITOK (EVar (5 + BK)) (C5 - CG + GEV)
      ++ posK ITOK xXk (ELit 0) IXMAX ++ str m xXk (eadd ITOK NK) (ELit 0) (2 + BK) ++ blkF m (2 + BK) ++ F_facts ++ kn_fixed)
     (vis m (2 + BK)) (EVar (5 + BK))).
Definition JS_key := sel3 JS_key_c.
Definition ST3_vretJ (m : smode) : acs := fake_ret 0xa66bc (snd (DPATH m NXF (JS_colon m m) [DRun [ENTRY]] 0)).
Definition JS_oval_c := Eval vm_compute in tri (fun w m =>
  JT [snd (DPATH m NXF (ST3_vretJ m) [DRun [0xa66dc]] 0)] 0xa66dc [(27%nat, esub RC J5)] 107 (4 + (3 + BV))
     ([KRange DEPTH 0 255; stk_shok; rel xIv xXv 48; KRange ITO 0 (INSZ - 2); KRange RC 1 (2 ^ 48); KRange (esub RC J5) 1 (2 ^ 48); KRange J5 0 (2 ^ 48);
       KRange xIv 0 INSZ]
      ++ mfacts w m (3 + BV) xIv (EVar (6 + BV)) (C5 - CG + GEV) ++ pos xIv xXv (ELit 0) 0 BIG ++ str m xXv xIv (ELit 0) (3 + BV) ++ blkF m (3 + BV)
      ++ F_facts ++ kn_fixed)
     (vis m (3 + BV)) (EVar (6 + BV))).
Definition JS_oval := sel3 JS_oval_c.


(* [comment removed for export] *)
Definition CNLOOP : nat := 10.  Definition CQ1L : nat := 11.  Definition CNUML : nat := 12.  Definition CQ2L : nat := 13.  Definition CC2L : nat := 14.
Definition CNVALL : nat := 15.  Definition CNLOOPL : nat := 16.
(* [comment removed for export] *)
Definition pre3n : list dstep := [DRun [0xa4500]; DBrF; DRun [0xa452c]; DBrF].
Definition ST_nhdr (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (JS_lcb m m) (hdr_pathG pre3n 15 cfg 0xa456c 0xa4574 false 0xa5528 false 0xa5530) 0)) [0; 1; 2; 3].
Definition JS_nhdr_c := Eval vm_compute in tri (fun w m =>
  JSG pos w m (ST_nhdr m) 0xa5530 [(25%nat, NF)] (ELit 0) ITOH3 (eaddz IX 1) 0 47 C5 [KRange HL3 1 8; KRange ITO 0 (INSZ - 2); KRange NF 0 (2 ^ 48)] V3h).
Definition JS_nhdr := sel3 JS_nhdr_c.
(* [comment removed for export] *)
Definition BNK : nat := 190.
  Definition xDn : expr := EVar 191.  Definition xXn : expr := EVar 192.
Definition BVN : nat := 300.          (* [comment removed for export] *)
Definition xEw : expr := EVar 300.  Definition xIw : expr := EVar 301.  Definition xXw : expr := EVar 302.
Definition STn_first (m : smode) : acs := snd (DPATH m NXF (JS_nhdr m m) [DRun [0xa554c]; DBrT; DRun [0xa5580]] 0).
Definition STn_num (m : smode) (s0 : acs) : acs := fake_ret 0xa5664 (snd (DPATH m NXF s0 [DRun [0xa55c8]; DBrF; DRun [GaNumT.BNU]] 0)).
Definition STn_self (m : smode) (s0 : acs) : acs :=
  fake_ret 0xa5810 (snd (DPATH m NXF (STn_num m s0) [DRun [0xa56cc]; DBrF; DRun [0xa577c]; DBrF; DRun [ENTRY]] 0)).
Definition STn_second (m : smode) : acs := snd (DPATH m NXF (STn_self m (STn_first m)) [DRun [0xa5830]; DBrF; DRun [0xa587c]; DBrF; DRun [0xa5580]] 0).
Definition Tn_c := Eval vm_compute in tri (fun w m =>
  JT [STn_first m; STn_second m] 0xa5580 [(25%nat, RC)] KEEP (4 + V5t) (loop_facts w m RC ITOL IXL V5t) (vis m V5t) (EVar (3 + V5t))).
Definition Tn := sel3 Tn_c.
Definition INVn_c := Eval vm_compute in tri (fun w m =>
  JT [STn_first m; STn_second m] 0xa5580 [(25%nat, esub RC J5)] KEEP (4 + V5i)
     (KRange RC 1 (2 ^ 48) :: loop_facts w m (esub RC J5) ITOJ IXJ V5i) (vis m V5i) (EVar (3 + V5i))).
Definition INVn := sel3 INVn_c.
Definition nfacts : list kentry := [KRange ITO 0 (INSZ - 2); KRange RC 1 (2 ^ 48); KRange (esub RC J5) 1 (2 ^ 48); KRange J5 0 (2 ^ 48)].
Definition OVN : list (nat * expr) := [(25%nat, esub RC J5)].
(* [comment removed for export] *)
Definition Vq1 : nat := 150.
Definition JS_q1_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (INVn m m) [] 0xa55c8 0xa55cc 0xa5914) 0xa55cc OVN (ELit 0) ITOJ IXJ 0 47 (C5 + GEV)
       (room m (eaddz IXJ 1) Vq1 ++ nfacts ++ [KRange ITOJ 0 INSZ]) Vq1).
Definition JS_q1 := sel3 JS_q1_c.
(* [comment removed for export] *)
Definition ITON : expr := eadd ITOJ xDn.
Definition num_facts : list kentry := nfacts ++ [KRange ITOJ 0 INSZ; KRange xDn 1 8; KRange ITON 0 INSZ; KRange xXn 0 BIG].
Definition STn_numJ (m : smode) : acs := fake_ret 0xa5664 (snd (DPATH m NXF (JS_q1 m m) [DRun [GaNumT.BNU]] 0)).
Definition JS_num_c := Eval vm_compute in tri (fun w m =>
  JT [snd (DPATH m NXF (STn_numJ m) [DRun [0xa567c]] 0)] 0xa567c OVN 107 (4 + (3 + BNK))
     ([KRange DEPTH 0 255; stk_shok; rel ITON xXn 54] ++ num_facts ++ mfacts w m (3 + BNK) ITON (EVar (6 + BNK)) (C5 - 2 * GEV)
      ++ pos ITON xXn (ELit 0) 0 BIG ++ str m xXn ITON (ELit 0) (3 + BNK) ++ blkF m (3 + BNK) ++ F_facts ++ kn_fixed)
     (vis m (3 + BNK)) (EVar (6 + BNK))).
Definition JS_num := sel3 JS_num_c.
(* [comment removed for export] *)
Definition Vq2 : nat := 220.
          (* [comment removed for export] *)
Definition JS_q2_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (JS_num m m) [] 0xa56cc 0xa56d0 0xa5938) 0xa56d0 OVN (ELit 0) ITON xXn 0 53 (C5 - GEV)
       (room m (eaddz xXn 1) Vq2 ++ num_facts) Vq2).
Definition JS_q2 := sel3 JS_q2_c.
(* [comment removed for export] *)
Definition Vc2 : nat := 260.
Definition JS_c2_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (JS_q2 m m) [] 0xa577c 0xa5780 0xa595c) 0xa5780 OVN (ELit 0) ITON (eaddz xXn 1) 0 52 C5
       (room m (eaddz xXn 2) Vc2 ++ num_facts) Vc2).
Definition JS_c2 := sel3 JS_c2_c.
(* [comment removed for export] *)
Definition STn_valJ (m : smode) : acs := fake_ret 0xa5810 (snd (DPATH m NXF (JS_c2 m m) [DRun [ENTRY]] 0)).
Definition JS_nval_c := Eval vm_compute in tri (fun w m =>
  JT [snd (DPATH m NXF (STn_valJ m) [DRun [0xa582c]] 0)] 0xa582c OVN 107 (4 + (3 + BVN))
     ([KRange DEPTH 0 255; stk_shok; rel xIw xXw 48] ++ nfacts ++ [KRange xIw 0 INSZ]
      ++ mfacts w m (3 + BVN) xIw (EVar (6 + BVN)) (C5 - GEV) ++ pos xIw xXw (ELit 0) 0 BIG ++ str m xXw xIw (ELit 0) (3 + BVN) ++ blkF m (3 + BVN)
      ++ F_facts ++ kn_fixed)
     (vis m (3 + BVN)) (EVar (6 + BVN))).
Definition JS_nval := sel3 JS_nval_c.
(* [comment removed for export] *)
Definition Vnc : nat := 330.
Definition ITO4 : expr := EVar 330.  Definition IX4 : expr := EVar 331.
Definition JS_ncomma_c := Eval vm_compute in tri (fun w m =>
  JSGk K5L pos w m (site_statesP true m (JS_nval m m) [DRun [0xa5830]; DBrF] 0xa587c 0xa5880 0xa597c) 0xa5880 OVN (ELit 0) ITO4 IX4 0 48 C5
       (room m (eaddz IX4 1) (2 + Vnc) ++ [KRange ITO 0 (INSZ - 2); KRange RC 1 (2 ^ 48); KRange (esub RC J5) 2 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange ITO4 0 INSZ]) (2 + Vnc)).
Definition JS_ncomma := sel3 JS_ncomma_c.
(* [comment removed for export] *)
Definition ST3_close (m : smode) : list acs :=
  [snd (DPATH m NXF (JS_ohdr m m) [DRun [0xa6330]; DBrT; DRun [0xa68c0]] 0); snd (DPATH m NXF (ST3_vret m) [DRun [0xa66e0]; DBrT; DRun [0xa68c0]] 0);
   snd (DPATH m NXF (JS_nhdr m m) [DRun [0xa554c]; DBrF; DRun [0xa68c0]] 0);                                  (* [comment removed for export] *)
   snd (DPATH m NXF (STn_self m (INVn m m)) [DRun [0xa5830]; DBrT; DRun [0xa68c0]] 0)].
Definition TC3_c := Eval vm_compute in tri (fun w m =>
  JT (ST3_close m) 0xa68c0 [] KEEP (4 + V5x)
     ([KRange DEPTH 0 255; stk_shok; KRange ITO 0 (INSZ - 2); KRange ITOC 0 INSZ; rel ITOC IXC 2]
      ++ mfacts w m V5x ITOC (EVar (3 + V5x)) C5 ++ pos ITOC IXC (ELit 0) 0 BIG ++ str m IXC ITOC (ELit 0) V5x ++ blkF m V5x ++ F_facts ++ kn_fixed)
     (vis m V5x) (EVar (3 + V5x))).
Definition TC3 := sel3 TC3_c.
Definition JS_rcb_c := Eval vm_compute in tri (fun w m =>
  JSEk K5 pos w m (site_states m (TC3 m m) [] 0xa6930 0xa6938 0xa8790) 0xa6938 (ELit 0) ITOC IXC (eaddz IXC 1) 0 2 (C5 + GEV)
       [KRange ITO 0 (INSZ - 2); KRange ITOC 0 INSZ] V5r).
Definition JS_rcb := sel3 JS_rcb_c.

(* [comment removed for export] *)
Definition xszv (m' : smode) : expr := match m' with MS => EVar (3 + BV) | ML => EVar (4 + BV) end.
Definition xszk (m' : smode) : expr := match m' with MS => EVar (2 + BK) | ML => EVar (3 + BK) end.
