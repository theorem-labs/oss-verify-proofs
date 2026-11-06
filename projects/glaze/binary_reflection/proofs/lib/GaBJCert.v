(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaBJT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw.

Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0x9d190.
Definition NINSTR : nat := 525.
Definition RET : Z := 0x9d7c8.

(* [comment removed for export] *)
Definition NXF : nat := 36.
Definition regsT : list expr := sr_upd regs0 4 (ELit (g_tp GASAN)).
Definition R : expr := EVar 9.  Definition BV : expr := EVar 10.  Definition OBJ : expr := EVar 11.
Definition INLO : expr := EVar 31.  Definition BSZ : expr := EVar 32.  Definition CAPW : expr := EVar 33.
Definition e_mtr : expr := EVar 34.  Definition e_fb : expr := EVar 35.
Definition EEND : expr := eadd INLO BSZ.
Definition INSZ : Z := GaB2JT.INSZ.
Definition GEV : Z := GaB2JT.GEV.  Definition CG : Z := GaB2JT.CG.  Definition SZMAX : Z := GaB2JT.SZMAX.  Definition MTRTOP : Z := GaB2JT.MTRTOP.
Definition AHI : Z := GaB2JT.AHI.
Definition FR : Z := 224.
Definition FRX : Z := FR + GaB2JT.XDMAX.       (* [comment removed for export] *)
Definition MTRIN : Z := GaB2JT.CMAXB.                     (* [comment removed for export] *)
Definition BJGROW : Z := pwtop SZMAX + (EVT + KFREE).   (* [comment removed for export] *)        (* [comment removed for export] *)
Definition FBNEED : Z := 259.
(* [comment removed for export] *)
Definition fobj (x : expr) (k n : Z) : list kentry :=
  [KRange (eaddz x k) PTRLO (objhi (n + 8)); KDisj (SA x k) (ELit n) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart x k (ELit n); shmap_apart x k (ELit n)].
(* [comment removed for export] *)
Definition robj (x : expr) (n : Z) : list kentry :=
  [KRange x (CEIL + FRX) (HI47 - (n + 8)); KRange (esub x e_sp) 0 (2 ^ 46); img_apart x 0 (ELit n); shmap_apart x 0 (ELit n)].
(* [comment removed for export] *)
Definition kn_stat : list kentry := [KIMGA] ++ RTC ++ GLZ_LOWSH ++ NEWH.
Definition kn_obj : list kentry :=
  [KWr (SA R 0) (ELit 32); KWr (SA OBJ 0) (ELit 24); KUnk (SA OBJ 0) (ELit 24); shok R 0 32; shok BV 0 24; shok OBJ 0 24].
Definition kn_mem : list kentry :=
  [KWord (SA BV 0) 8 INLO; KWord (SA BV 8) 8 EEND; KWord (SA BV 16) 8 CAPW; KUnk (SA INLO 0) BSZ; KShOk (SA INLO 0) BSZ] ++ kn_obj ++ kn_stat.
Definition obj_pure : list kentry :=
  [KAlign R 8; KAlign BV 8; KAlign OBJ 8] ++ robj R 32 ++ fobj BV 0 24 ++ fobj OBJ 0 24
  ++ [KDisj (SA R 0) (ELit 32) (SA BV 0) (ELit 24); KDisj (SA R 0) (ELit 32) (SA OBJ 0) (ELit 24); KDisj (SA OBJ 0) (ELit 24) (SA BV 0) (ELit 24)].
Definition kn_pure : list kentry :=
  [KRange BSZ 1 INSZ; KRange INLO PTRLO PTRHI; KRange EEND (PTRLO + 1) PTRHI;
   img_apart INLO 0 BSZ; shmap_apart INLO 0 BSZ;
   KDisj (SA INLO 0) BSZ (SA e_sp (- FRX)) (ELit (FRX + WSTK));
   KDisj (SA INLO 0) BSZ (SA R 0) (ELit 32); KDisj (SA INLO 0) BSZ (SA BV 0) (ELit 24); KDisj (SA INLO 0) BSZ (SA OBJ 0) (ELit 24)]
  ++ obj_pure ++ [KRange e_fb FBNEED FBMAX; KRange e_mtr 0 MTRIN].
(* [comment removed for export] *)
Definition sp_in : list kentry :=
  [KWr (SA e_sp (- FRX)) (ELit FRX); KAlign e_sp 32; KRange e_sp (CEIL + FRX) HI47; KShOk (SA e_sp (- FRX)) (ELit FRX)].
Definition out0 : list kentry := [KWord (SA OBJ 0) 8 (ELit 0)].       (* [comment removed for export] *)
Definition kn0 : list kentry := out0 ++ sp_in ++ kn_mem ++ kn_pure.
Definition WS : list (expr * expr) := [(R, ELit 32); (BV, ELit 24); (OBJ, ELit 24); (INLO, BSZ)].
Definition tin : acs := mkcs FRX WS e_mtr e_fb ENTRY regsT kn0 NXF.

(* [comment removed for export] *)
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition x_regs : list expr := sr_havoc regsT clobbered 36.
Definition CNT : expr := EVar 51.  Definition ER : expr := EVar 52.  Definition MTR : expr := EVar 53.
Definition resk : list kentry := [KWord (SA R 0) 8 CNT; KWord (SA R 8) 4 ER; KZero (SA R 16) (ELit 16)].
Definition mtr_out : list kentry := [KRange (esub MTR e_mtr) 0 BJGROW; KRange MTR 0 (MTRIN + BJGROW)].
Definition mkcsR (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRX 0 vis WS 0 e_sp FdStd false mtr [] e_fb.
Definition SV : expr := EVar 54.
Definition x_kn_S : list kentry := resk ++ [KWord (SA OBJ 0) 1 (escale 2 SV); KRange SV 0 22] ++ mtr_out ++ kn_mem.
Definition toutS : acs := mkcsR RET x_regs x_kn_S 55 [] MTR.
Definition DL : expr := EVar 54.  Definition SL : expr := EVar 55.  Definition AL : expr := EVar 56.
Definition strLx (d s a : expr) : list kentry :=
  [KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
   KRange a 3 AHI; KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
   KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
   KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA R 0) (ELit 32);
   KDisj (SA d 0) (escale 8 a) (SA BV 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BSZ].
Definition x_kn_L : list kentry := resk ++ mtr_out ++ strLx DL SL AL ++ kn_mem.
Definition toutL : acs := mkcsR RET x_regs x_kn_L 57 [(DL, escale 8 AL)] MTR.
Definition BCAP : Z := GaB2JT.BCAP + 2 ^ 24.  Definition CCAP : Z := 4.
Definition ce2 : gcallee2 := GCE2 NXF tin [toutS] [toutL] BCAP CCAP.
Definition ce : gcallee := c2_merged ce2.

(* [comment removed for export] *)
Definition NXFE : nat := 33.
Definition e_mtrE : expr := EVar 31.  Definition e_fbE : expr := EVar 32.
Definition kn_objE : list kentry := kn_obj ++ kn_stat.
Definition kn0E : list kentry :=
  out0 ++ [KWord (SA BV 0) 8 (ELit 0); KWord (SA BV 8) 8 (ELit 0); KWord (SA BV 16) 8 (ELit 0)] ++ sp_in ++ kn_objE ++ obj_pure ++ [KRange e_fbE 1 FBMAX; KRange e_mtrE 0 MTRIN].
Definition WSE : list (expr * expr) := [(R, ELit 32); (BV, ELit 24); (OBJ, ELit 24)].
Definition tinE : acs := mkcs FRX WSE e_mtrE e_fbE ENTRY regsT kn0E NXFE.
Definition x_regsE : list expr := sr_havoc regsT clobbered 33.
Definition x_knE : list kentry :=
  [KWord (SA R 0) 8 (ELit 0); KWord (SA R 8) 4 (ELit 22); KZero (SA R 16) (ELit 16)] ++ out0 ++ [KWord (SA BV 0) 8 (ELit 0); KWord (SA BV 8) 8 (ELit 0); KWord (SA BV 16) 8 (ELit 0)] ++ kn_objE.   (* [comment removed for export] *)
Definition toutE : acs := ACS (mk_ss RET x_regsE x_knE 48) [] 0 FRX 0 [] WSE 0 e_sp FdStd false e_mtrE [] e_fbE.
Definition ceE : gcallee := GCE NXFE tinE [toutE] 0 0.
End GaBJT.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GaBJ.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPrune OSSVerify.Proofs.glaze.binary_reflection.lib.GaB2JT.GaDedup OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA.

Export GaBJT.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, NINSTR)].
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 201 then Some GaB2JT.ceL1 else None.
Definition CT2 (id : nat) : option gcallee2 := if Nat.eqb id 200 then Some (GaB2JT.ce2 MS) else CT2_resize id.
Definition XN : nat -> list expr -> acs -> option acs := XNw (XNd (XNp (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CT))).   (* [comment removed for export] *)
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2.
Definition FUELB : nat := 20000.

(* [comment removed for export] *)
Definition F : expr := EVar 36.
Definition shF : expr := EAlu ALU_SRL F (ELit 3).
Definition BIG : Z := GaB2JT.BIG.


Definition HEAD : Z := 0x9d3e8.       (* [comment removed for export] *)
Definition CALLV : Z := GaB2JT.ENTRY. (* [comment removed for export] *)
Definition REL : Z := 0x9d700.        (* [comment removed for export] *)
Definition F_facts : list kentry :=
  [ KRange F PTRLO (PTRHI - 256); KRange (eaddz F 256) (PTRLO + 256) PTRHI; KAlign F 256; KWr (SA F 0) (ELit 256); KUnk (SA F 0) (ELit 256);
    KUnk (SA shF SB) (ELit 32); KWr (SA shF SB) (ELit 32);
    KDisj (SA shF SB) (ELit 32) (SA (ELit 0) (SB + IMG_LO / 8)) (ELit (IMG_SZ / 8));
    KDisj (SA F 0) (ELit 256) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart F 0 (ELit 256); shmap_apart F 0 (ELit 256);
    KDisj (SA F 0) (ELit 256) (SA R 0) (ELit 32); KDisj (SA F 0) (ELit 256) (SA BV 0) (ELit 24); KDisj (SA F 0) (ELit 256) (SA OBJ 0) (ELit 24);
    KDisj (SA F 0) (ELit 256) (SA INLO 0) BSZ;
    shok F 32 8; shok F 64 8; shok F 96 8; shok F 128 4; shok F 160 4;
    KZero (SA F 168) (ELit 48) ].      (* [comment removed for export] *)
Definition kn_fixed : list kentry := F_facts ++ sp_in ++ kn_mem ++ kn_pure.

(* [comment removed for export] *)
Fixpoint assocn (l : list (nat * expr)) (i : nat) : option expr :=
  match l with [] => None | (j, x) :: r => if Nat.eqb i j then Some x else assocn r i end.
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
Definition is_frame_word (keep : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w x => (expr_eqb b e_sp && Z.leb (- FR) o && Z.ltb o 0) && expr_vars_lt keep x
  | _ => false
  end.
Definition jframe (ss : list acs) (keep : nat) : list kentry :=
  match ss with
  | [] => []
  | s0 :: r => List.filter (fun K => is_frame_word keep K && forallb (fun s => existsb (kentry_eqb K) (kn s)) r)%bool (kn s0)
  end.
Fixpoint maxvar_regs (rs : list expr) (acc : nat) : nat :=
  match rs with [] => acc | EVar i :: r => maxvar_regs r (Nat.max acc (Datatypes.S i)) | _ :: r => maxvar_regs r acc end.
Definition mkcsF (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRX 0 vis WS 0 e_sp FdStd false mtr [(F, ELit 256)] (eaddz e_fb (-1)).
(* [comment removed for export] *)
Definition JT (ss : list acs) (p : Z) (ov : list (nat * expr)) (keep v nx : nat) (facts : list kentry) (vs : list (expr * expr)) (mtr : expr) : acs :=
  let rs := jregs (map (fun s => s_regs (a_ss s)) ss) 0 32 ov keep v in
  mkcsF p rs (jframe ss keep ++ facts) (Nat.max nx (maxvar_regs rs v)) vs mtr.
Definition caller_saved : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition fake_ret (ret : Z) (cs : acs) : acs :=
  let ss := a_ss cs in
  with_ss cs (mk_ss ret (sr_havoc (s_regs ss) caller_saved (nxt cs)) (kn cs) (nxt cs + 16)%nat).

(* [comment removed for export] *)
Definition szof (m : smode) (v : nat) : expr := match m with MS => EVar v | ML => EVar (1 + v) end.
Definition strLT (ix ito d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; GaB2JT.capE ix ito a (ELit 0);
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a);
    KDisj (SA F 0) (ELit 256) (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA R 0) (ELit 32);
    KDisj (SA d 0) (escale 8 a) (SA BV 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BSZ ].
Definition str (m : smode) (ix ito : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strLT ix ito (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) := match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
Definition room (m : smode) (req : expr) (v : nat) : list kentry :=
  match m with
  | MS => [KRange (esub (EVar v) req) 0 22]
  | ML => [KRange (esub (escale 8 (EVar (2 + v))) (eaddz req 1)) 0 (8 * AHI); KRange (esub (EVar (1 + v)) req) 0 (8 * AHI)]
  end.


Definition mfacts (m : smode) (v : nat) (ito mtr : expr) (c : Z) : list kentry :=        (* [comment removed for export] *)
  pw_facts e_mtr (szof m v) mtr ++ [ KRange mtr 0 MTRTOP ].

(* [comment removed for export] *)
Definition posk (ito ix sep : expr) : list kentry :=
  [ KWord (SA F 128) 4 (ELit 0); KWord (SA F 64) 8 (eadd INLO ito); KWord (SA F 32) 8 ix; KWord (SA F 96) 8 EEND;
    KRange ito 0 INSZ; KRange (esub BSZ ito) 0 INSZ; KRange ix 0 BIG;
    KRange sep 0 1; KRange (esub (esub (escale 24 ito) ix) sep) 0 BIG ].

(* [comment removed for export] *)
Definition DPATH := dpath ASEGS IT AASAN XN XB BFUEL.
Definition S0 : acs := set_kn tin (KWord (SA OBJ 0) 1 (ELit 0) :: kn tin).
Definition F46 (k : list dstep) : list dstep :=
  DExt 46 [F; ELit 128; ELit 88] :: DExt 46 [F; ELit 96; ELit 8] :: DExt 46 [F; ELit 64; ELit 8] :: DExt 46 [F; ELit 32; ELit 8]
  :: DExt 46 [F; ELit 128; ELit 4] :: DExt 46 [F; ELit 160; ELit 4] :: DExt 47 [F] :: k.
Definition pre_d : list dstep := [DRun []; DExt 50 [ELit 2]; DExt 47 []; DRun []] ++ F46 [DExt 6 []; DRun []; DExt 6 []; DRun [HEAD]].
Definition VARGS (m : smode) (ito ix : expr) (sv : nat) (mtr : expr) : list expr :=
  [e_mtr; ito; ELit 0; BSZ; ix; INLO] ++ (match m with MS => [EVar sv; ELit 0; ELit 0] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end)
  ++ [mtr; eaddz e_fb (-1)].
Definition ST_first : acs := snd (DPATH 0%nat S0 pre_d 0).
Definition ST_second : acs :=
  snd (DPATH 0%nat ST_first [DRun [CALLV]; DX2a 200 [e_mtr; ELit 0; ELit 0; BSZ; ELit 0; INLO; ELit 0; ELit 0; ELit 0; e_mtr; eaddz e_fb (-1)]; DRun []; DBrT; DRun [HEAD]] 0).

(* [comment removed for export] *)
Definition KEEP : nat := 85.
Definition JV : nat := 85.  Definition J : expr := EVar 85.
Definition SEP : expr := EVar 86.  Definition ITOJ : expr := EVar 87.  Definition IXJ : expr := EVar 88.
Definition SSTR : nat := 89.  Definition MTRJ : expr := EVar 92.
Definition CH : Z := - GEV.
Definition loop_facts (m : smode) : list kentry :=
  [ KRange (esub ITOJ J) 0 INSZ ] ++ posk ITOJ IXJ SEP ++ mfacts m SSTR ITOJ MTRJ CH ++ str m IXJ ITOJ SSTR ++ kn_fixed.
Definition INV_d (m : smode) : acs := JT [ST_first; ST_second] HEAD [(11%nat, SEP)] KEEP 93 112 (loop_facts m) (vis m SSTR) MTRJ.
Definition INV_c : acs * acs := Eval vm_compute in (INV_d MS, INV_d ML).
Definition INV (m : smode) : acs := match m with MS => fst INV_c | ML => snd INV_c end.

(* [comment removed for export] *)
Definition BPC : Z := 0x9d454.  Definition BACK : Z := 0x9d458.  Definition STUBRET : Z := 0x9d4ec.
Definition KEEPJ : nat := 120.
Definition VJ : nat := 160.
Definition body0 (m : smode) : acs := add_kn (INV m) [KRange J 0 (INSZ - 1); KRange (esub BSZ J) 1 INSZ; KRange SEP 1 1].
Definition ST_sep (m : smode) : list acs :=
  let s1 := snd (DPATH 0%nat (body0 m) [DRun [0x9d3f0]; DBrF; DRun [0x9d418]; DBrF; DRun [BPC]] 0) in
  let a := snd (DPATH 0%nat s1 [DBrF; DRun [BACK]] 0) in
  let b0 := snd (DPATH 0%nat s1 [DBrT; DRun []] 0) in
  let b := snd (DPATH 0%nat (fake_ret STUBRET b0) [DRun [BACK]] 0) in
  [a; b].
Definition sep_facts (m : smode) : list kentry :=
  [ KRange J 0 (INSZ - 1); KRange (esub BSZ J) 1 INSZ; KRange (esub ITOJ J) 0 INSZ; KRange SEP 1 1 ] ++ posk ITOJ IXJ SEP
  ++ mfacts m VJ ITOJ (EVar (3 + VJ)) (CH + GEV) ++ str m IXJ ITOJ VJ ++ room m (eaddz IXJ 1) VJ ++ kn_fixed.
Definition JSEP_d (m : smode) : acs := JT (ST_sep MS) BACK [] KEEPJ (4 + VJ) 185 (sep_facts m) (vis m VJ) (EVar (3 + VJ)).
Definition JSEP_c : acs * acs := Eval vm_compute in (JSEP_d MS, JSEP_d ML).
Definition JSEP (m : smode) : acs := match m with MS => fst JSEP_c | ML => snd JSEP_c end.

(* [comment removed for export] *)
Definition EPIPC : Z := 0x9d5e4.
Definition eCNT : expr := EVar 85.  Definition eER : expr := EVar 86.
Definition VE : nat := 87.
Definition strLE (d s a : expr) : list kentry := strLx d s a ++ [KDisj (SA F 0) (ELit 256) (SA d 0) (escale 8 a)].
Definition ST_epi : list acs :=
  let b0 := add_kn (INV MS) [KRange J 0 (INSZ - 1); KRange (esub BSZ J) 1 INSZ; KRange SEP 0 0] in
  let s1 := snd (DPATH 0%nat b0 [DRun [0x9d3f0]; DBrT; DRun []] 0) in                                   (* [comment removed for export] *)
  let a := snd (DPATH 0%nat (fake_ret 0x9d568 s1) [DRun [EPIPC]] 0) in
  let s2 := snd (DPATH 0%nat b0 [DRun [0x9d3f0]; DBrF; DRun [CALLV]] 0) in                              (* [comment removed for export] *)
  let s3 := fake_ret 0x9d4cc s2 in
  let s4 := with_ss s3 (mk_ss (pc s3) (s_regs (a_ss s3))                                                 (* [comment removed for export] *)
              (KWord (SA F 128) 4 (EVar (nxt s3)) :: List.filter (fun K => negb (kentry_eqb K (KWord (SA F 128) 4 (ELit 0)))) (kn s3)) (Datatypes.S (nxt s3))) in
  let b := snd (DPATH 0%nat s4 [DRun [0x9d4d4]; DBrF; DRun [EPIPC]] 0) in
  [a; b].
Definition epi_facts (m : smode) : list kentry :=
  [ KWord (SA R 0) 8 eCNT; KWord (SA R 8) 4 eER; KRange (esub (EVar (3 + VE)) e_mtr) 0 BJGROW; KRange (EVar (3 + VE)) 0 (MTRIN + BJGROW) ]
  ++ (match m with MS => strS OBJ (EVar VE) | ML => strLE (EVar VE) (EVar (1 + VE)) (EVar (2 + VE)) end) ++ kn_fixed.
Definition EPI_d (m : smode) : acs := JT ST_epi EPIPC [] KEEP (4 + VE) 110 (epi_facts m) (vis m VE) (EVar (3 + VE)).
Definition EPI_c : acs * acs := Eval vm_compute in (EPI_d MS, EPI_d ML).
Definition EPI (m : smode) : acs := match m with MS => fst EPI_c | ML => snd EPI_c end.
Definition HEPI (m : smode) : nat := match m with MS => 2 | ML => 3 end%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TIDY (k : plan) : plan := PExt 48 [] (PExt 47 [] k).
Definition hole (m : smode) : nat := match m with MS => 0 | ML => 1 end%nat.
(* [comment removed for export] *)
Definition EPIK (m : smode) : plan := PRun [] (PExt 6 [] (PRun [REL] (PExt 51 [] (PRun [] (PHandoff (hole m)))))).
Definition EXIT (m : smode) : plan := PRun [EPIPC] (PHandoffW (HEPI m) []).
(* [comment removed for export] *)
Definition MOUT (sz ito mtr : expr) (c : Z) (k : plan) : plan :=
  PFactLe (esub mtr e_mtr) (pwtop_d sz) BJGROW k.   (* [comment removed for export] *)                       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition vprep2 (sz0 ito0 mtr0 : expr) (c0 : Z) (sz1 ito1 mtr1 : expr) (c1 : Z) (k : plan) : plan :=
  PFactLe mtr1 (pwtop_e e_mtr sz1) MTRTOP k.
Definition STEP (sz0 ito0 mtr0 : expr) (c0 : Z) (sz1 ito1 mtr1 : expr) (c1 : Z) (via : expr) (k : plan) : plan :=
  vprep2 sz0 ito0 mtr0 c0 sz1 ito1 mtr1 c1 k.
Definition RID (m : smode) : nat := match m with MS => 104%nat | ML => 114%nat end.
Definition FB1 : expr := eaddz e_fb (-1).
Definition RARGS (m : smode) (sv : nat) (mtr : expr) : list expr :=
  match m with MS => resize_args_S (EVar sv) mtr FB1 | ML => resize_args_L (EVar sv) (EVar (1 + sv)) (EVar (2 + sv)) mtr FB1 end.

(* [comment removed for export] *)
Definition BVX : nat := 190.
Definition xE : expr := EVar 190.  Definition xI : expr := EVar 191.
  Definition xM : expr := EVar 196.
Definition xsz (m' : smode) : expr := match m' with MS => EVar 193 | ML => EVar 194 end.
Definition post (leaf : plan) (m m' : smode) (sv : nat) (ito mtr : expr) (c0 : Z) : plan :=
  let sz0 := szof m sv in
  let cpe := esub (eaddz (eadd (eadd (escale 6 (esub (xsz m') sz0)) (escale CG (esub xI ito))) (escale GEV xE)) (- GEV)) (esub xM mtr) in
  TIDY ((match m' with ML => PExt 13 [EVar 193] | MS => fun k => k end)
  (PRun [0x9d4d4] (PBranch
     (* [comment removed for export] *)
        (MOUT (xsz m') xI xM (c0 + 256 * GEV) (EXIT m'))
     (STEP sz0 ito mtr c0 (xsz m') xI xM (c0 - GEV) cpe (PRun [HEAD] leaf))))).
Definition CALL (leaf : plan) (m : smode) (sv : nat) (ito ix mtr : expr) (c0 : Z) : plan :=
  PRun [CALLV] (PBump BVX (match m with
  | MS => PExt2 200 (VARGS MS ito ix sv mtr) (post leaf MS MS sv ito mtr c0) (post leaf MS ML sv ito mtr c0)
  | ML => PExt 201 (VARGS ML ito ix sv mtr) (post leaf ML ML sv ito mtr c0)
  end)).
(* [comment removed for export] *)
Definition BS : nat := 130.
Definition sep (leaf : plan) (m : smode) : plan :=
  let req := eaddz IXJ 1 in let n := escale 2 req in let sz := szof m SSTR in
  let c := CH + GEV in
  let stub :=
       PRun [] (PBump BS (PExt2 (RID m) (RARGS m SSTR MTRJ)
          (TIDY (PExt 49 [MTRJ; sz; n; e_mtr; ELit 1] (PRun [BACK] (PMerge 1))))
          (TIDY (PExt 13 [EVar BS] (PExt 49 [MTRJ; sz; n; e_mtr; ELit 0] (PRun [BACK] (PMerge 1))))))) in
  let roomk := PRun [BACK] (PMerge 1) in
  let after (m2 : smode) := CALL leaf m2 VJ ITOJ (eaddz IXJ 1) (EVar (3 + VJ)) c in
  PViaM 1 (match m with MS => [(JSEP MS, after MS); (JSEP ML, after ML)] | ML => [(JSEP ML, after ML)] end) VJ
    (PRun [BPC] (PBranch roomk stub)).
(* [comment removed for export] *)
Definition BD : nat := 130.
(* [comment removed for export] *)
Definition SPFIX (k : plan) : plan := PFact (KRange (eaddz e_sp (- FR)) (CEIL + FRX - FR) (HI47 - FR)) k.
Definition DONE (m : smode) : plan :=
  let sz := szof m SSTR in let m' := EVar (2 + BD) in
  PRun [] (PBump BD (PExt2 (RID m) (RARGS m SSTR MTRJ)
     (TIDY (SPFIX (MOUT sz ITOJ MTRJ CH (EXIT m))))
     (TIDY (SPFIX (PExt 13 [EVar BD]
        (PFactLe (esub (eadd MTRJ m') e_mtr) (eadd (pwtop_d sz) m') BJGROW (EXIT ML))))))).
Definition NEXT : plan := PNextW [(87%nat, xI)].
Definition body_gen (leaf : plan) (m : smode) : plan :=
  PRun [0x9d3f0] (PBranch                                                                        (* [comment removed for export] *)
    (PCase2 SEP 0
       (CALL leaf m SSTR ITOJ IXJ MTRJ CH)                                                             (* [comment removed for export] *)
       (PRun [0x9d418] (PBranch (sep leaf m) (CALL leaf m SSTR ITOJ IXJ MTRJ CH))))                         (* [comment removed for export] *)
    (DONE m)).
Definition body := body_gen NEXT.
Definition loop : plan :=
  PLoopM JV BSZ [(INV MS, body MS, DONE MS); (INV ML, body ML, DONE ML)] [(86%nat, ELit 0); (87%nat, ELit 0); (88%nat, ELit 0); (89%nat, ELit 0); (92%nat, e_mtr)].
Definition F46p (k : plan) : plan :=
  PExt 46 [F; ELit 128; ELit 88] (PExt 46 [F; ELit 96; ELit 8] (PExt 46 [F; ELit 64; ELit 8] (PExt 46 [F; ELit 32; ELit 8]
  (PExt 46 [F; ELit 128; ELit 4] (PExt 46 [F; ELit 160; ELit 4] (PExt 47 [F] k)))))).
Definition plan_bj : plan :=
  PJoin OBJ 0 1 (PRun [] (PExt 50 [ELit 2] (PExt 47 [] (PRun [] (F46p (PExt 6 [] (PRun [] (PExt 6 [] (PRun [HEAD] loop))))))))).

Definition CUTS : list (acs * AP.plan) := [(EPI MS, EPIK MS); (EPI ML, EPIK ML)].





(* [comment removed for export] *)
Definition FE : expr := EVar 33.
Definition plan_E : plan :=
  PRun [] (PExt 50 [ELit 2] (PRun [] (PExt 46 [FE; ELit 128; ELit 88] (PExt 6 [] (PRun [] (PExt 6 []
  (PRun [] (PExt 6 [] (PRun [REL] (PExt 51 [] (PRun [] (PHandoff 0)))))))))))).

End GaBJ.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon GaBJ.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma top : check ASEGS IT AASAN NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUELB None (ce_tin ce) plan_bj = COk (SHole 2).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 2))). Qed.
