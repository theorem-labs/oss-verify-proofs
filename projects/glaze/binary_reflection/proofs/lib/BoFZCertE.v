(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgBJT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.

Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0x9dcb4.
Definition NINSTR : nat := 545.
Definition RET : Z := 0x9e338.

(* [comment removed for export] *)
Definition NXF : nat := 36.
Definition regsT : list expr := sr_upd regs0 4 (ELit (g_tp GBOTH)).
Definition R : expr := EVar 9.  Definition BV : expr := EVar 10.  Definition OBJ : expr := EVar 11.
Definition INLO : expr := EVar 31.  Definition BSZ : expr := EVar 32.  Definition CAPW : expr := EVar 33.
Definition e_mtr : expr := EVar 34.  Definition e_fb : expr := EVar 35.
Definition EEND : expr := eadd INLO BSZ.
Definition INSZ : Z := BgB2JT.INSZ.
Definition GEV : Z := BgB2JT.GEV.  Definition CG : Z := BgB2JT.CG.  Definition SZMAX : Z := BgB2JT.SZMAX.  Definition MTRTOP : Z := BgB2JT.MTRTOP.
Definition AHI : Z := BgB2JT.AHI.
Definition FR : Z := 224.
Definition FRX : Z := FR + BgB2JT.XDMAX.       (* [comment removed for export] *)
Definition MTRIN : Z := BgB2JT.CMAXB.                     (* [comment removed for export] *)
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
Definition BCAP : Z := BgB2JT.BCAP + 2 ^ 24.  Definition CCAP : Z := 4.
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
End BgBJT.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgBJ.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT.BgDedup OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA.

Export BgBJT.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, NINSTR)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 201 then Some BgB2JT.ceL1 else None.
Definition CT2 (id : nat) : option gcallee2 := if Nat.eqb id 200 then Some (BgB2JT.ce2 MS) else CT2_resize id.
Definition XN : nat -> list expr -> acs -> option acs := XNw (XNd (XNp (XNc BSEGS IT ABOTH NXF GBOTH BCAP CCAP CT))).   (* [comment removed for export] *)
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc BSEGS ABOTH NXF GBOTH BCAP CCAP CT2.
Definition FUELB : nat := 20000.

(* [comment removed for export] *)
Definition F : expr := EVar 36.
Definition shF : expr := EAlu ALU_SRL F (ELit 3).
Definition BIG : Z := BgB2JT.BIG.


Definition HEAD : Z := 0x9df28.       (* [comment removed for export] *)
Definition CALLV : Z := BgB2JT.ENTRY. (* [comment removed for export] *)
Definition REL : Z := 0x9e270.        (* [comment removed for export] *)
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
    KRange a 3 AHI; BgB2JT.capE ix ito a (ELit 0);
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
Definition DPATH := dpath BSEGS IT ABOTH XN XB BFUEL.
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
Definition BPC : Z := 0x9df98.  Definition BACK : Z := 0x9df9c.  Definition STUBRET : Z := 0x9e048.
Definition KEEPJ : nat := 120.
Definition VJ : nat := 160.
Definition body0 (m : smode) : acs := add_kn (INV m) [KRange J 0 (INSZ - 1); KRange (esub BSZ J) 1 INSZ; KRange SEP 1 1].
Definition ST_sep (m : smode) : list acs :=
  let s1 := snd (DPATH 0%nat (body0 m) [DRun [0x9df30]; DBrF; DRun [0x9df5c]; DBrF; DRun [BPC]] 0) in
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
Definition EPIPC : Z := 0x9e154.
Definition eCNT : expr := EVar 85.  Definition eER : expr := EVar 86.
Definition VE : nat := 87.
Definition strLE (d s a : expr) : list kentry := strLx d s a ++ [KDisj (SA F 0) (ELit 256) (SA d 0) (escale 8 a)].
Definition ST_epi : list acs :=
  let b0 := add_kn (INV MS) [KRange J 0 (INSZ - 1); KRange (esub BSZ J) 1 INSZ; KRange SEP 0 0] in
  let s1 := snd (DPATH 0%nat b0 [DRun [0x9df30]; DBrT; DRun []] 0) in                                   (* [comment removed for export] *)
  let a := snd (DPATH 0%nat (fake_ret 0x9e0d8 s1) [DRun [EPIPC]] 0) in
  let s2 := snd (DPATH 0%nat b0 [DRun [0x9df30]; DBrF; DRun [CALLV]] 0) in                              (* [comment removed for export] *)
  let s3 := fake_ret 0x9e028 s2 in
  let s4 := with_ss s3 (mk_ss (pc s3) (s_regs (a_ss s3))                                                 (* [comment removed for export] *)
              (KWord (SA F 128) 4 (EVar (nxt s3)) :: List.filter (fun K => negb (kentry_eqb K (KWord (SA F 128) 4 (ELit 0)))) (kn s3)) (Datatypes.S (nxt s3))) in
  let b := snd (DPATH 0%nat s4 [DRun [0x9e030]; DBrF; DRun [EPIPC]] 0) in
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
  (PRun [0x9e030] (PBranch
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
  PRun [0x9df30] (PBranch                                                                        (* [comment removed for export] *)
    (PCase2 SEP 0
       (CALL leaf m SSTR ITOJ IXJ MTRJ CH)                                                             (* [comment removed for export] *)
       (PRun [0x9df5c] (PBranch (sep leaf m) (CALL leaf m SSTR ITOJ IXJ MTRJ CH))))                         (* [comment removed for export] *)
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

End BgBJ.
Module BgBJCert.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon BgBJ.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma top : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUELB None (ce_tin ce) plan_bj = COk (SHole 2).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 2))). Qed.
End BgBJCert.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgNameW.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ID_NAMEW : nat := 53.

Definition namew_val (segs : list Segment) (k : list kentry) (b : expr) (off : Z) (v : nat) : expr :=
  match split_read_lo k segs k b off 7 with
  | Some (w1, v1) => split_value v1 w1 (EExt false 0 (8 - w1) (EVar v))
  | None => EVar v
  end.
Definition namew_lo_ok (segs : list Segment) (k : list kentry) (b : expr) (off : Z) (v : nat) : bool :=
  match split_read_lo k segs k b off 7 with
  | Some (w1, v1) => expr_vars_lt v v1
  | None => true
  end.
Definition node_namew (segs : list Segment) (nx0 : nat) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off] =>
      let k := kn cs in let v := nxt cs in
      if (fresh_ok nx0 cs && expr_vars_lt v b && kn_readable segs k k b off 8 && namew_lo_ok segs k b off v)%bool
      then Some (set_kn (bump cs 1) (KWord (SA b off) 8 (namew_val segs k b off v) :: kn cs))
      else None
  | _ => None
  end.
Definition XNn (segs : list Segment) (nx0 : nat) (XN0 : nat -> list expr -> acs -> option acs) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id ID_NAMEW then node_namew segs nx0 args cs else XN0 id args cs.

(* [comment removed for export] *)
Lemma le_bytes_of_word : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hl. unfold word_to_le_bytes.
  pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B'. rewrite Hl in B.
  rewrite AX2S.u_small by (change (8 * Z.of_nat 8) with 64 in B; lia).
  rewrite <- Hl at 1. apply GCL.Z_to_le_bytes_of_bytes.
Qed.

Section Sound.
Context {RC : run_ceil}.
Variable NXF : nat.
Variable RZ : GPS.rz_t.
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable VSHc : list (Z * Z).
Variable AINVc : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FTOPc : Z.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXF E E' -> UINV E -> UINV E'.
Variable XN0 : nat -> list expr -> acs -> option acs.

(* [comment removed for export] *)
Lemma namew_val_sound : forall E Mb k b off v bs,
  know_ok BSEGS E Mb k -> flat E (SA b off) 8 -> rdn BSEGS Mb (adenot E (SA b off)) 8 = Some bs -> length bs = 8%nat ->
  namew_lo_ok BSEGS k b off v = true ->
  exists a, forall E', env_agree v E E' -> ev E' v = a ->
    edenot E' (namew_val BSEGS k b off v) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros E Mb k b off v bs HK Hfl Hbs Hlen Hlo. unfold namew_val, namew_lo_ok in *.
  destruct (split_read_lo k BSEGS k b off 7) as [[w1 v1]|] eqn:Hsp.
  - destruct (split_read_lo_sound BSEGS E Mb k Mb k b off 7 w1 v1 HK HK ltac:(lia) Hsp) as (Hw1 & Hw7 & HS1).
    assert (Hfl1 : flat E (SA b off) (Z.of_nat w1)) by (eapply flat_mono; [exact Hfl | lia]).
    destruct (HS1 Hfl1) as (bs1 & Hrd1 & Hlen1 & Hval1).
    pose proof (Hoare.SeqExec.rdn_firstn BSEGS Mb 8 _ bs w1 Hbs ltac:(lia)) as Hf. rewrite Hrd1 in Hf. injection Hf as Hbs1.
    set (bs2 := skipn w1 bs).
    assert (Hlen2 : length bs2 = (8 - w1)%nat) by (unfold bs2; rewrite length_skipn; lia).
    assert (Hcat : bs = bs1 ++ bs2) by (rewrite Hbs1; unfold bs2; symmetry; apply firstn_skipn).
    exists (Z_to_bv 64 (bytes_le_to_Z bs2)). intros E' Hag Hev.
    assert (Hv1 : edenot E' v1 = edenot E v1) by (symmetry; eapply (APS.edenot_agree' v); [exact Hag | exact Hlo]).
    pose proof (PropExec.bytes_le_to_Z_bound bs1) as B1. rewrite Hlen1 in B1.
    pose proof (PropExec.bytes_le_to_Z_nonneg bs1) as B1'. pose proof (PropExec.bytes_le_to_Z_nonneg bs2) as B2'.
    pose proof (PropExec.bytes_le_to_Z_bound bs2) as B2. rewrite Hlen2 in B2.
    rewrite Hcat, PropExec.bytes_le_app, Hlen1.
    rewrite (lor_shiftl_disjoint (bytes_le_to_Z bs1) (bytes_le_to_Z bs2) (8 * Z.of_nat w1)%Z ltac:(lia) ltac:(lia) B2').
    unfold split_value. cbn [edenot]. rewrite Hev, Hv1, <- Hval1. unfold extz.
    set (P := (2 ^ (8 * Z.of_nat w1))%Z) in *. set (Q := (2 ^ (8 * Z.of_nat (8 - w1)))%Z) in *.
    set (X1 := bytes_le_to_Z bs1) in *. set (X2 := bytes_le_to_Z bs2) in *.
    assert (HPQ : (P * Q = 2 ^ 64)%Z).
    { subst P Q. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (HP1 : (1 <= P)%Z) by (subst P; pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat w1)); lia).
    assert (HQ1 : (1 <= Q)%Z) by (subst Q; pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat (8 - w1))); lia).
    assert (HPlt : (P < 2 ^ 64)%Z) by (subst P; apply Z.pow_lt_mono_r; lia).
    assert (HX2 : ext_val false 0 (8 - w1) (Z_to_bv 64 X2) = Z_to_bv 64 X2).
    { unfold ext_val, ext_Z. rewrite AX2S.u_small by nia. f_equal.
      change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r. fold Q. apply Z.mod_small. lia. }
    rewrite HX2. apply bv_eq.
    rewrite u_add64, u_mul64, u_lit64, two64_eq.
    rewrite (AX2S.u_small P) by lia. rewrite (AX2S.u_small X2) by nia. rewrite (AX2S.u_small (X1 + X2 * P)) by nia.
    rewrite (Z.mod_small X1) by nia. rewrite (Z.mod_small (P * X2)) by nia. rewrite Z.mod_small by nia. lia.
  - exists (Z_to_bv 64 (bytes_le_to_Z bs)). intros E' Hag Hev. cbn [edenot]. exact Hev.
Qed.

Theorem XNn_sound :
  GPS.ext_stmt BSEGS NXF XN0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ ->
  GPS.ext_stmt BSEGS NXF (XNn BSEGS NXF XN0) PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV RZ.
Proof.
  intros H0 id args. unfold XNn. destruct (Nat.eqb id ID_NAMEW); [|exact (H0 id args)].
  intros cs cs' E fx R M model T HT HC _ Hn Hk. unfold node_namew in Hn.
  destruct args as [|b [|o [|? ?]]]; try discriminate; destruct o as [off| | | | | | |]; try discriminate.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlo]. apply andb_prop in Hc as [Hc Hrd]. apply andb_prop in Hc as [Hf Hvb].
  destruct (APS.fresh_ok_parts NXF cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs) in *.
  pose proof (co_know HC) as HK.
  destruct (kn_readable_sound BSEGS E _ (kn cs) _ (kn cs) b off 8 HK HK ltac:(lia) ltac:(lia) Hrd) as (Hfl & bs & Hbs & Hlen).
  destruct (namew_val_sound E _ (kn cs) b off v bs HK Hfl Hbs Hlen Hlo) as (a & Ha).
  set (E' := APS.ext1 E v a).
  assert (Hag : env_agree v E E') by apply APS.ext1_agree.
  assert (HC' : cs_ok BSEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc fx_ok UINV E' cs fx R M model) by (eapply cs_ok_agree; [exact UINV_agree | exact Hag | exact Hf | exact HC]).
  assert (Hb : edenot E' b = edenot E b) by (symmetry; eapply (APS.edenot_agree' v); [exact Hag | exact Hvb]).
  apply (Hk E' fx R M model).
  - split; [eapply APS.env_agree_le; [exact Hag | exact Fle] | exact Hag].
  - apply cs_ok_set_kn; [apply cs_ok_bump; exact HC'|].
    constructor; [|exact (co_know HC')].
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl' : flat E' (SA b off) (Z.of_nat 8)).
    { unfold flat, estart in *. cbn [a_base a_off] in *. rewrite Hb. exact Hfl. }
    split; [exact Hfl'|].
    rewrite (Ha E' Hag (APS.ext1_at E v a)).
    rewrite (le_bytes_of_word bs Hlen).
    replace (adenot E' (SA b off)) with (adenot E (SA b off)) by (unfold adenot; cbn [a_base a_off]; rewrite Hb; reflexivity).
    change (Mr SHC VSHc E' (bump cs 1) model M) with (Mr SHC VSHc E' cs model M).
    rewrite (Mr_agreeE NXF SHC VSHc E E' cs model M Hag Hf). exact Hbs.
  - reflexivity.
Qed.
End Sound.
End BgNameW.
Module BgStep.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon.
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
  | XD d => dgo BSEGS IT ABOTH XN XB BFUEL NXF cs d
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
End BgStep.
Module BgStrCtor.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0x9fa90.
Definition RETPC : Z := 0x9fbc0.
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, 92%nat)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 33.
Definition e_p := e_a0.
Definition e_mtr : expr := EVar 31.  Definition e_fb : expr := EVar 32.
Definition HELLO : Z := g_hello GBOTH.
Definition HLEN : Z := 11.
(* [comment removed for export] *)
Definition regsT : list expr := sr_upd (sr_upd regs0 11 (ELit HELLO)) 4 (ELit (g_tp GBOTH)).
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

End BgStrCtor.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoFZP.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT.BgDedup OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeAnn OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodeSf5 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgJT BgNameW.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ BgStep.


Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ANNOT : Z := 0x70fc4.
Definition SF5_ENTRY : Z := 0x70e54.
(* [comment removed for export] *)
Definition SPX : expr := EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD e_sp (ELit (-224))) (ELit 5)).
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
(* [comment removed for export] *)
Definition tmpaddr (b : expr) (o : Z) : bool := expr_eqb b SPX && Z.leb 32 o && Z.ltb o 104.
Definition kkeep (K : kentry) : bool :=
  match K with
  | KWord (SA b o) _ v => eok b && eok v && content_ok b o
  | KZero (SA b o) n => match b with ELit _ => eok n | _ => false end
  | KBlob _ _ _ | KFill _ _ _ => false
  | KImg _ _ => true
  | KAlign e _ | KRange e _ _ => eok e
  | KWr (SA b o) n | KUnk (SA b o) n | KShOk (SA b o) n => eok b && eok n && negb (tmpaddr b o)
  | KDisj (SA b1 o1) n1 (SA b2 o2) n2 => eok b1 && eok n1 && eok b2 && eok n2 && negb (tmpaddr b1 o1) && negb (tmpaddr b2 o2)
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
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, NINSTR); (0x9f0c8, 72%nat); (0x9f1e8, 35%nat); (0x9f028, 40%nat); (0x9f274, 47%nat); (0x9e9b0, 34%nat); (0x9f330, 40%nat)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 110 then Some BgWN.BgVecT.Ctor.ce else if Nat.eqb id 111 then Some BgStrCtor.ce else None.
Definition CT2 (id : nat) : option gcallee2 :=
  if Nat.eqb id 112 then Some BgReadCert.BgRead.ce2 else if Nat.eqb id 113 then Some BgBJT.ce2 else if Nat.eqb id 114 then Some BgWN.BgVecT.Push.ce2 else None.
Definition XN : nat -> list expr -> acs -> option acs :=
  XNn BSEGS NXF (XNsf5 NXF GBOTH SF5_ENTRY (XNann NXF GBOTH ANNOT (XNd (XNp (XNc BSEGS IT ABOTH NXF GBOTH BCAP CCAP CT))))).
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc BSEGS ABOTH NXF GBOTH BCAP CCAP CT2.


(* [comment removed for export] *)
Definition pseq (fs : list (plan -> plan)) (k : plan) : plan := fold_right (fun f acc => f acc) k fs.     (* [comment removed for export] *)
Definition TIDY (k : plan) : plan := PExt 48 [] (PExt 47 [] k).
Definition SHOK (off n : Z) (k : plan) : plan := PExt 46 [F; ELit off; ELit n] (PExt 47 [F] k).   (* [comment removed for export] *)
Definition P1 : expr := EVar 66.                          (* [comment removed for export] *)
Definition MTR0 : expr := eaddz e_mtr EVT.    (* [comment removed for export] *)
Definition FB1 : expr := eaddz e_fb (-1).                 (* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMSG : Z := BgReadCert.BgFMST.FMSGROW.
Definition G1 : Z := EVT + FMSG.                          (* [comment removed for export] *)
Definition G2 : Z := G1 + KFREE + BgBJT.BJGROW.           (* [comment removed for export] *)
Definition GJ2 : Z := G2 + 2 * KFREE.                     (* [comment removed for export] *)
Definition GJ3 : Z := GJ2 + EVT + KFREE.                  (* [comment removed for export] *)
Definition G4 : Z := GJ3 + FMSG.                          (* [comment removed for export] *)
Definition GJ4 : Z := G4 + 2 * KFREE.                     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition B1 : nat := 120.  Definition MTR1 : expr := EVar 137.  Definition DL1 : expr := EVar 138.    (* [comment removed for export] *)
Definition B2 : nat := 300.  Definition MTR2 : expr := EVar 317.                                          (* [comment removed for export] *)
Definition B3 : nat := 400.  Definition P2 : expr := EVar 400.                                            (* [comment removed for export] *)
Definition B4 : nat := 500.  Definition MTR4 : expr := EVar 517.  Definition DL4 : expr := EVar 518.    (* [comment removed for export] *)
Definition READ1_ARGS : list expr := [ELit 0; P1; eadd SIZE P1; ELit 11; eadd SIZE P1; MTR0; FB1].
Definition B2J_ARGS (m : expr) : list expr := [ELit 0; P1; SIZE; eadd SIZE P1; m; FB1].
Definition HJ2 : nat := 3.
Definition J2PC : Z := 0x9d818.  Definition J4PC : Z := 0x9d968.
Definition toJ2 (ok : bool) : plan := if ok then PRun [J2PC] (PRun [J2PC] (PHandoff HJ2)) else PRun [J2PC] (PHandoff HJ2).     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFT (c : smode) (ok : bool) (j : smode) : plan :=
  let rest := match c, ok with ML, true => PRun [] (PRun [] (PExt 22 [] (PHandoff HJ2))) | _, _ => toJ2 ok end in      (* [comment removed for export] *)
  PFact (KRange (esub MTR2 e_mtr) 0 G2) (TIDY (match j with ML => PExt 13 [EVar 318] (PRun [] (PExt 22 [] rest)) | MS => rest end)).
Definition B2J (c : smode) (ok : bool) : plan :=
  let m := match c, ok with ML, false => eaddz MTR1 KFREE | _, _ => MTR1 end in      (* [comment removed for export] *)
  PBump B2 (PExt2 113 (B2J_ARGS m) (AFT c ok MS) (AFT c ok ML)).
(* [comment removed for export] *)
Definition NW3 (c : smode) (o : Z) (k : plan) : plan :=
  match c with MS => PExt 53 [F; ELit o] (PExt 53 [F; ELit (o + 8)] (PExt 53 [F; ELit (o + 16)] k)) | ML => k end.
(* [comment removed for export] *)
Definition MOVE (c : smode) (o : Z) : list (plan -> plan) :=
  [PRun []; PExt 5 []; PRun []; NW3 c o; PExt 5 []; PRun []; PExt 6 []; PRun []; PExt 5 []].
Definition JSON (k : plan) : plan := SHOK 288 24 (PExt 6 [] (PRun [] k)).     (* [comment removed for export] *)
Definition N13 (c : smode) (d : expr) (k : plan) : plan := match c with ML => PExt 13 [d] k | MS => k end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition planA (c : smode) : plan :=
  pseq [PFact (KRange (esub MTR1 e_mtr) 0 G1); TIDY; N13 c DL1; PRun [0x9d714]]
    (PBranch
       (pseq (MOVE c 144 ++ [PRun []; JSON]) (B2J c true))                                                  (* [comment removed for export] *)
       (match c with MS => pseq [PRun []; PExt 5 []; PRun []; JSON] (B2J MS false) | ML => pseq [PRun []; PExt 5 []; PRun []; PExt 22 []; PRun []; JSON] (B2J ML false) end)).   (* [comment removed for export] *)
Definition plan_top : plan :=
  pseq [PRun []; PExt 50 [ELit 3]; PExt 47 []; PRun []; SHOK 224 24; PExt 6 []; PRun []; PExt 110 [ELit 0; ELit 0; e_mtr; FB1]; TIDY; PExt 13 [P1]; PRun [];
        SHOK 128 64; PExt 111 [ELit 0; ELit 0; MTR0; FB1]; TIDY; PRun []; PExt 5 []; PRun []; PBump B1]
       (PExt2 112 READ1_ARGS (PHandoff 1) (PHandoff 2)).
(* [comment removed for export] *)
Definition XP := xpath IT NXF XN XB.
Definition st (cs : acs) (l : list xstep) : acs := snd (XP cs l 0).
Definition TD : list xstep := [X 48 []; X 47 []].
Definition SH (off n : Z) : list xstep := [X 46 [F; ELit off; ELit n]; X 47 [F]].
Definition NW (o : Z) : list xstep := [X 53 [F; ELit o]; X 53 [F; ELit (o + 8)]; X 53 [F; ELit (o + 16)]].
Definition MV (o : Z) : list xstep := [R []; X 5 []; R []] ++ NW o ++ [X 5 []; R []; X 6 []; R []; X 5 []].     (* [comment removed for export] *)
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
  st A_S ([XFact (KRange (esub MTR1 e_mtr) 0 G1)] ++ TD ++ [R [0x9d714]; XD DBrF] ++ MV 144 ++ [R []] ++ SH 288 24 ++ [X 6 []; R []; XBump B2;
           XD (DX2a 113 (B2J_ARGS MTR1)); XFact (KRange (esub MTR2 e_mtr) 0 G2)] ++ TD ++ [R [J2PC]; R [J2PC]]).
Definition J2 : acs := Eval vm_compute in mkT allow2 ST_J2 DEADJ GJ2.
Definition MJ2 : expr := Eval vm_compute in a_meter J2.
(* [comment removed for export] *)
Definition allow3 (v : nat) : bool := Nat.ltb v 67 || Nat.eqb v 400.
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
                XFact (KRange (esub MTR4 e_mtr) 0 G4)] ++ TD ++ [R [0x9d898]; XD DBrF] ++ MV 48 ++ [R [J4PC]; R [J4PC]]).
Definition J4_0 : acs := Eval vm_compute in mkT allow3 (ST_J4 0) DEADJ GJ4.
Definition J4_1 : acs := Eval vm_compute in mkT allow3 (ST_J4 1) DEADJ GJ4.


(* [comment removed for export] *)
Definition planJ2 : plan :=
  pseq [PRun []; PBump B3] (PExt2 114 PUSH_ARGS (pseq [TIDY; PExt 13 [P2]] (PHandoff 4)) (pseq [TIDY; PExt 13 [P2]] (PHandoff 5))).
Definition toJ4 (ok : bool) (cls : nat) : plan := if ok then PRun [J4PC] (PRun [J4PC] (PHandoff (6 + cls))) else PRun [J4PC] (PHandoff (6 + cls)).
Definition AFTR (cls : nat) (c : smode) : plan :=
  pseq [PFact (KRange (esub MTR4 e_mtr) 0 G4); TIDY; N13 c DL4; PRun [0x9d898]]
    (PBranch
       (match c with MS => pseq (MOVE MS 48) (toJ4 true cls) | ML => pseq (MOVE ML 48 ++ [PRun []; PRun []; PExt 22 []]) (PHandoff (6 + cls)) end)   (* [comment removed for export] *)
       (match c with MS => pseq [PRun []; PExt 5 []] (toJ4 false cls) | ML => pseq [PRun []; PExt 5 []; PRun []; PExt 22 []] (toJ4 false cls) end)).
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
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, NINSTR); (0x9f0c8, 72%nat); (0x9f1e8, 35%nat); (0x9f028, 40%nat); (0x9f274, 47%nat); (0x9e9b0, 34%nat); (0x9f330, 40%nat); (0x9e5ec, 38%nat)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 111 then Some BgStrCtor.ce else if Nat.eqb id 115 then Some BgReadCert.BgReadE.RdE.ceE else if Nat.eqb id 116 then Some BgBJT.ceE
  else if Nat.eqb id 117 then Some BgWN.BgVecT.Push.ceE else None.
Definition CT2 (id : nat) : option gcallee2 := if Nat.eqb id 112 then Some BgReadCert.BgRead.ce2 else None.
Definition XN : nat -> list expr -> acs -> option acs :=
  XNn BSEGS NXF (XNsf5 NXF GBOTH SF5_ENTRY (XNann NXF GBOTH ANNOT (XNd (XNp (XNc BSEGS IT ABOTH NXF GBOTH BCAP CCAP CT))))).
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc BSEGS ABOTH NXF GBOTH BCAP CCAP CT2.
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
   X 115 [ELit 0; ELit 11; e_mtr; FB1]] ++ TDx ++ [R []; X 5 []; R []] ++ SHx 288 24 ++ [X 6 []; R []; X 116 [ELit 0; e_mtr; FB1]] ++ TDx ++ [R []; XBump 200;
   X 117 [ELit 0; e_mtr; FB1]] ++ TDx ++ [X 13 [P2E]; R []] ++ SHx 32 64 ++ [X 111 [ELit 0; ELit 0; MTRE; FB1]] ++ TDx ++ [R []; X 5 []; R []; XBump 260].
Definition armEx : list xstep :=
  [XD (DX2a 112 READ2E_ARGS); XFact (KRange (esub MTR4E e_mtr) 0 G4E)] ++ TDx ++ [R [0x9d898]; XD DBrF] ++ FuzzNP.MV 48 ++ [R [FuzzNP.J4PC]; R [FuzzNP.J4PC]].
Definition allowE (v : nat) : bool := Nat.ltb v 67 || Nat.eqb v 200.
Definition GJ4E : Z := G4E + 2 * KFREE.
Definition JE : acs := Eval vm_compute in mkT allowE (snd (xpath IT NXF XN XB tin (preEx ++ armEx) 0)) FuzzNP.DEADJ GJ4E.
Definition AFTREJ (c : smode) : plan :=
  pseq [PFact (KRange (esub MTR4E e_mtr) 0 G4E); TIDY; N13 c DL4E; PRun [0x9d898]]
    (PBranch
       (match c with MS => pseq (FuzzNP.MOVE MS 48 ++ [PRun [FuzzNP.J4PC]; PRun [FuzzNP.J4PC]]) (PMerge 1) | ML => pseq (FuzzNP.MOVE ML 48 ++ [PRun []; PRun []; PExt 22 []]) (PMerge 1) end)
       (match c with MS => pseq [PRun []; PExt 5 []; PRun [FuzzNP.J4PC]] (PMerge 1) | ML => pseq [PRun []; PExt 5 []; PRun []; PExt 22 []; PRun [FuzzNP.J4PC]] (PMerge 1) end)).
Definition planE : plan :=
  pseq [PRun []; PExt 50 [ELit 3]; PExt 47 []; PRun []; SHOK 224 24; PExt 6 []; PRun [];                    (* [comment removed for export] *)
        SHOK 128 64; PExt 111 [ELit 0; ELit 0; e_mtr; FB1]; TIDY; PRun []; PExt 5 []; PRun [];               (* [comment removed for export] *)
        PExt 115 [ELit 0; ELit 11; e_mtr; FB1]; TIDY; PRun []; PExt 5 []; PRun [];                            (* [comment removed for export] *)
        SHOK 288 24; PExt 6 []; PRun []; PExt 116 [ELit 0; e_mtr; FB1]; TIDY; PRun [];                        (* [comment removed for export] *)
        PBump 200; PExt 117 [ELit 0; e_mtr; FB1]; TIDY; PExt 13 [P2E]; PRun [];                               (* [comment removed for export] *)
        SHOK 32 64; PExt 111 [ELit 0; ELit 0; MTRE; FB1]; TIDY; PRun []; PExt 5 []; PRun []; PBump 260]        (* [comment removed for export] *)
       (PVia 1 JE 260 (PExt2 112 READ2E_ARGS (AFTREJ MS) (AFTREJ ML)) (PRun [] DT)).   (* [comment removed for export] *)
Definition FUELB : nat := 20000.

End FuzzEP.
End BoFZP.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoFZ BoFZP.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import FuzzN. Import FuzzE. Import FuzzEP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma certE : check BSEGS IT ABOTH NXF LIMIT ISP0 XN XE0 XB (HSce ce) 0%nat BFUEL FUELB None (ce_tin ce) planE = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan_E : gplan_ok planE = true. Proof. vm_compute. reflexivity. Qed.
