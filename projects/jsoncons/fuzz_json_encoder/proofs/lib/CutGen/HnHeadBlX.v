(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA HeapIfaceANull L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutBridgeB CutRtCpsA CutRtA CutRtB CutRtC CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecsXA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopKitXA RdKitXA HnKitXA XKitXA PmTopSpecsXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_harness_bl_xasan_T Cut_harness_bl_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_harness_bl_xasan.
Module GT := Cut_harness_bl_xasan_T.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.

Module HNA.
(* [comment removed for export] *)
Definition PC_SM5 : Z := 419464.      (* [comment removed for export] *)
Definition PC_SFREE5 : Z := 419988.   (* [comment removed for export] *)
Definition PC_SETSH00 : Z := 540080.  (* [comment removed for export] *)
Definition PC_SETSHF8 : Z := 540368.  (* [comment removed for export] *)
Definition PC_FREE : Z := 531904.     (* [comment removed for export] *)
Definition PC_STRINIT : Z := 724956.  (* [comment removed for export] *)
Definition PC_ISS : Z := 725300.      (* [comment removed for export] *)
Definition PC_RCTOR : Z := 727172.    (* [comment removed for export] *)
Definition PC_READ : Z := 728576.     (* [comment removed for export] *)
Definition PC_PDTOR : Z := 729216.    (* [comment removed for export] *)
Definition PC_SDTOR : Z := 730848.    (* [comment removed for export] *)
Definition PC_OPDEL : Z := 1031544.    (* [comment removed for export] *)
Definition PC_SYSCAT : Z := 1058428.   (* [comment removed for export] *)
Definition PC_LOCDTOR : Z := 1212636. (* [comment removed for export] *)
Definition PC_AMEMSET : Z := 526044.  (* [comment removed for export] *)
Definition PC_ENCCTOR : Z := 725968.  (* [comment removed for export] *)
Definition PC_ENCDTOR : Z := 728724.  (* [comment removed for export] *)
Definition RETPC : Z := 724360.       (* [comment removed for export] *)
Definition SPX : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit 16).      (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition IMP : Z := 6934032. Definition VT_ISS : Z := 1435784. Definition VT_SBUF : Z := 1435544. Definition VT_IOS : Z := 1435824. Definition VT_VIS : Z := 1421608.
Definition OBJ_SYSCAT : Z := 1463216. Definition G_GUARD : Z := 6931840. Definition SYSCAT_GUARD : Z := 6932480. Definition AXT : Z := 7069728. Definition ERRNO : Z := 6938412.
Definition IMGHI : Z := 7077888.
Definition FE := EVar 45. Definition FLE := EVar 40. Definition PTRE := EVar 10. Definition NE := EVar 11.
Definition IAF (k : Z) : expr := EAlu Instr.ALU_ADD FE (ELit k).
Definition SHF (g : Z) : saddr := SA (CHA.SRL3 FE) (SBz + g).
Definition SKT : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)).      (* [comment removed for export] *)
Definition ALLOCT : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-113)).   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALN : Z := 16.         (* [comment removed for export] *)
Definition LNG : bool := true.    (* [comment removed for export] *)
Definition NCUT : nat := 34.
Definition I_STR : nat := 2. Definition I_ISS : nat := 3. Definition I_MS : nat := 4. Definition I_EC : nat := 5. Definition I_SH0 : nat := 6. Definition I_RC : nat := 7. Definition I_SC : nat := 8.
Definition I_RD : nat := 9. Definition I_PD : nat := 10. Definition I_SD : nat := 11. Definition I_SH2 : nat := 12. Definition I_ED : nat := 13. Definition I_S2 : nat := 14.
(* [comment removed for export] *)
Definition C_OD1 : list nat := [14; 16]%nat. Definition C_LD1 : list nat := [15; 18]%nat. Definition C_LD2 : list nat := [17; 20]%nat.
Definition C_FR : list nat := [19; 21; 23; 25; 22; 24; 26; 28]%nat. Definition C_OD2 : list nat := [27; 30]%nat.
Definition C_SF : list nat := [29; 32]%nat. Definition C_EX : list nat := [31; 33]%nat.
Definition inb (i : nat) (l : list nat) : bool := existsb (Nat.eqb i) l.
Definition NX (i : nat) : nat := nth i [40; 57; 73; 92; 111; 127; 143; 159; 178; 194; 215; 231; 247; 263; 281; 297; 298; 313; 314; 329; 330; 345; 346; 361; 362; 377; 378; 393; 394; 409; 410; 425; 426; 442]%nat 0%nat.
Definition gRC : nat := 159. Definition gRD : nat := 194.     (* [comment removed for export] *)
Definition RCB : list (expr * expr) := [(EVar gRC, ELit 264); (EVar (gRC + 1), ELit 66); (EVar (gRC + 2), ELit 16384)].
Definition RDB : list (expr * expr) := [(EVar gRD, EVar (gRD + 1)); (EVar (gRD + 2), EVar (gRD + 3)); (EVar (gRD + 4), ELit 16384)].
Definition gS : nat := 73. Definition gI : nat := 92.        (* [comment removed for export] *)
Definition NG_STR : nat := 3.                                (* [comment removed for export] *)
Definition SB1 : (expr * expr) := (EVar (gS + 1), EVar (gS + 2)).     (* [comment removed for export] *)
Definition SB2 : (expr * expr) := (EVar (gI + 1), EVar (gI + 2)).     (* [comment removed for export] *)
Definition SBLK (i : nat) : list (expr * expr) :=
  if Nat.ltb i 3 then [] else if Nat.eqb i 3 then [SB1] else if (Nat.leb i 14 || Nat.eqb i 16)%bool then [SB2; SB1] else if (Nat.leb i 28 || Nat.eqb i 30)%bool then [SB1] else [].
Definition BLK (i : nat) : list (expr * expr) :=
  (if (Nat.eqb i 8 || Nat.eqb i 9)%bool then RCB else if Nat.eqb i 10 then RDB else if Nat.eqb i 11 then [(EVar (gRD + 4), ELit 16384)] else []) ++ SBLK i.
Definition FRM : list (expr * Z * Z) := [(FE, 5, -160)].
(* [comment removed for export] *)
Definition FFS : list (list (expr * Z * Z)) := map (fun i => if (Nat.eqb i 0 || inb i C_EX)%bool then [] else FRM) (seq 0 NCUT).
(* [comment removed for export] *)
Definition CSP (i : nat) : Z := if inb i [17; 19; 20; 21; 22; 23; 24; 26]%nat then -208 else -160.
(* [comment removed for export] *)
Definition STKR : SGP.region := (EVar 2, -18416, ELit 18416).
Definition TOPR : SGP.region := (EVar 2, 0, ELit 16).        (* [comment removed for export] *)
Definition FSHR : SGP.region := (CHA.SRL3 FE, SBz, ELit 256).
Definition CPF (i : nat) : list SGP.region :=
  if (Nat.eqb i 0 || inb i C_EX)%bool then [STKR; TOPR]
  else if Nat.leb i 2 then [STKR; TOPR; (FE, 0, ELit 24); (FE, 32, ELit 2008); FSHR]
  else if (Nat.eqb i 8 || Nat.eqb i 9)%bool then [STKR; TOPR; (FE, 1696, ELit 16); FSHR]
  else if Nat.leb 14 i then [STKR; TOPR; (FE, 0, ELit 24); (FE, 96, ELit 272); FSHR]
  else [STKR; TOPR; FSHR].
Definition gED : nat := 263.                               (* [comment removed for export] *)
Definition RJ2 : list nat := [15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30]%nat.      (* [comment removed for export] *)
Ltac dcut i := do 34 (destruct i as [|i]; [reflexivity|]).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1482488) 8 (ELit SBz); KWord (SA (ELit 0) 1482496) 4 (ELit 1)].
Definition ISHS : list Z := [2147630360; 2147630363; 2147630350].       (* [comment removed for export] *)
Definition ISHZ : list kentry := map (fun a => KZero (SA (ELit 0) a) (ELit 1)) ISHS.
Definition FLAGN : list kentry := [KWord (SA FE 2040) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition G216 : saddr := SA (CHA.SRL3 (IAF 216)) SBz.
Definition FRK : list kentry := [KZero G216 (ELit 1); KDisj (SHF 0) (ELit 27) G216 (ELit 1); KDisj (SHF 28) (ELit 228) G216 (ELit 1)].
Definition NEWS0 : list kentry := STAT ++ ISHZ ++ FLAGN.
Definition TWON : expr := EMd Instr.M_MUL (ELit 2) NE.
(* [comment removed for export] *)
Definition CAPW (g : nat) : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar g)) (ELit 1).
Definition BNEWSE (v : nat) (sz : expr) : list kentry :=
  [KRange (EVar v) 4096 140737479966719; KAlign (EVar v) 16; KUnk (SA (EVar v) 0) sz; KWr (SA (EVar v) 0) sz; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar v) 0) sz].
(* [comment removed for export] *)
Definition BNEWS (v : nat) (lo n : Z) : list kentry :=
  [KRange (EVar v) lo 140737479966719; KAlign (EVar v) 16; KUnk (SA (EVar v) 0) (ELit n); KWr (SA (EVar v) 0) (ELit n); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar v) 0) (ELit n)].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition SNEWS : list kentry := [KWord (SA FE 32) 8 (CAPW gS); KWord (SA FE 40) 8 NE; KWord (SA FE 48) 8 (EVar (gS + 1)); KUnk (SA FE 32) (ELit 24)].
Definition SBN : list kentry := BNEWSE (gS + 1) (EVar (gS + 2)) ++ [KRange (EVar (gS + 2)) 24 67108874].        (* [comment removed for export] *)
Definition ISNEWS : list kentry :=
  [KWord (SA FE 96) 8 (ELit VT_ISS); KWord (SA FE 112) 8 (ELit VT_SBUF); KWord (SA FE 120) 8 (ELit IMP); KWord (SA FE 216) 8 (ELit VT_IOS); KWord (SA FE 264) 8 (ELit IMP);
   KWord (SA FE 272) 8 (ELit 0); KWord (SA FE 280) 8 (ELit 0); KWord (SA FE 288) 8 (ELit 0); KWord (SA FE 304) 8 (ELit 0); KWord (SA FE 328) 8 (ELit 0); KUnk (SA FE 96) (ELit 272);
   KWord (SA FE 176) 8 (CAPW gI); KWord (SA FE 184) 8 NE; KWord (SA FE 192) 8 (EVar (gI + 1))].
Definition IBN : list kentry := BNEWSE (gI + 1) (EVar (gI + 2)) ++ [KRange (EVar (gI + 2)) 48 67108916].       (* [comment removed for export] *)
Definition NEWS_STR : list kentry := NEWS0 ++ SNEWS ++ SBN.
Definition NEWS_ISS : list kentry := NEWS0 ++ FRK ++ ISNEWS ++ IBN.
Definition s_has (cells : list kentry) : bool := (has cells (KWord (SA FE 32) 8 (CAPW gS)) && has cells (KWord (SA FE 40) 8 NE) && has cells (KWord (SA FE 48) 8 (EVar (gS + 1))))%bool.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NEWS_SH0 : list kentry := NEWS0 ++ [KZero (SHF 122) (ELit 74)].
Definition NEWS_RD2 (g : nat) : list kentry := NEWS0 ++ ISNEWS ++ [KRange (EVar (g + 1)) 264 134217728; KRange (EVar (g + 3)) 1 4096; KUnk (SA FE 432) (ELit 24)].   (* [comment removed for export] *)
Definition NEWS_RC : list kentry := NEWS0 ++ BNEWS gRC 17594333495296 264 ++ BNEWS (gRC + 1) 17594333495296 66 ++ BNEWS (gRC + 2) 4096 16384.
(* [comment removed for export] *)
Definition sm_ok (ps : SR.post_spec) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok IMGHI G.HDECL (SR.ps_cells ps) 40 [] [] 5 45 40 X)%bool.
Definition NEWS_SM (ps : SR.post_spec) (cj : CC.cutpoint) : list kentry := List.filter (fun X => sm_ok ps X || CC.has_cell ISHZ X) (CC.cp_know cj).
Definition NEWS_SF (cj : CC.cutpoint) : list kentry := List.filter (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) (CC.cp_know cj).
(* [comment removed for export] *)
Definition fsh (cells : list kentry) (lo n : nat) : bool := forallb (fun g => has cells (KWord (SHF (Z.of_nat g)) 1 (ELit 0))) (seq lo n).
(* [comment removed for export] *)
Definition RDRSH : SGP.region := (CHA.SRL3 FE, SBz + 122, ELit 74).
Definition FOOTW : list SGP.region :=
  [(ELit 0, 6931840, ELit 2); (ELit 0, 6932480, ELit 2); (ELit 0, 6932496, ELit 504); (ELit 0, 6933176, ELit 1152); (ELit 0, 6936168, ELit 96); (ELit 0, 7069728, ELit 544); (ELit 0, 7070307, ELit 1); (ELit 0, 7070528, ELit 4)].
Definition LITLO : Z := 6931848.      (* [comment removed for export] *)
Definition W_RD : list SGP.region := [(IAF 976, 0, ELit 592); (IAF 96, 0, ELit 272); (IAF 1696, 0, ELit 16); (IAF 496, 0, ELit 408); (IAF 432, 0, ELit 24); (ELit 0, LITLO, ELit 72); (ELit 0, G_GUARD, ELit 2); (ELit 0, AXT, ELit 544); (ELit 0, ERRNO, ELit 4)].
(* [comment removed for export] *)
Definition ISNEWS_X : list kentry :=
  [KWord (SA FE 96) 8 (ELit VT_ISS); KWord (SA FE 112) 8 (ELit VT_SBUF); KWord (SA FE 120) 8 (ELit IMP); KWord (SA FE 216) 8 (ELit VT_IOS); KWord (SA FE 264) 8 (ELit IMP);
   KWord (SA FE 272) 8 (ELit 0); KWord (SA FE 280) 8 (ELit 0); KWord (SA FE 288) 8 (ELit 0); KWord (SA FE 304) 8 (ELit 0); KWord (SA FE 328) 8 (ELit 0); KUnk (SA FE 96) (ELit 272)].
Definition ISKEEP (cells : list kentry) : list kentry :=
  match CAX.cell_at cells FE 176 1 with Some v => [KWord (SA FE 176) 1 v] | None => [] end ++ match CAX.cell_at cells FE 176 8 with Some v => [KWord (SA FE 176) 8 v] | None => [] end ++
  match CAX.cell_at cells FE 184 8 with Some v => [KWord (SA FE 184) 8 v] | None => [] end ++ match CAX.cell_at cells FE 192 8 with Some v => [KWord (SA FE 192) 8 v] | None => [] end.
Definition NEWS_RDX (g : nat) (cells : list kentry) : list kentry := NEWS0 ++ ISNEWS_X ++ [KRange (EVar (g + 1)) 264 134217728; KRange (EVar (g + 3)) 1 4096; KUnk (SA FE 432) (ELit 24)] ++ ISKEEP cells.
Definition NEWS_MS : list kentry := NEWS0 ++ [KZero (SA FE 432) (ELit 24)].
Definition NEWS_EC : list kentry := NEWS0 ++ [KUnk (SA FE 496) (ELit 408)].
(* [comment removed for export] *)
Definition kd_ok (c : CC.cutpoint) : bool :=
  has (CC.cp_know c) (KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA FE 0) (ELit 2048)) && has (CC.cp_know c) (KDisj (SA (EVar 2) (-18416)) (ELit 18416) (SA FE 0) (ELit 2048)).
(* [comment removed for export] *)
Definition gchk (scr : Z) (ng : nat) (BLk : list (expr * expr)) (wregs : list SGP.region) (news : list kentry) (a0x : option expr)
           (i j : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool :=
  match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr ng BLk FRM wregs news a0x c ps cj (BLK i) FRM (BLK j) FRM with
  | Some ci => (Z.eqb (CH2.ci_csp ci) (CSP i) && Nat.eqb (CH2.ci_nx ci) (NX i))%bool
  | None => false
  end.
Definition gchkn (nx : nat) (scr : Z) (ng : nat) (BLk : list (expr * expr)) (wregs : list SGP.region) (news : list kentry) (a0x : option expr)
           (i j : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool :=
  match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr ng BLk FRM wregs news a0x c ps cj (BLK i) FRM (BLK j) FRM with
  | Some ci => (Z.eqb (CH2.ci_csp ci) (CSP i) && Nat.eqb (CH2.ci_nx ci) nx)%bool
  | None => false
  end.
Definition RJ (i : nat) (ps : SR.post_spec) : nat := if Nat.eqb i I_S2 then (if CL.ps_reg_is ps 10 (EVar (gED + 1)) then i + 2 else i + 1) else if inb i RJ2 then i + 2 else i + 1.   (* [comment removed for export] *)
Definition NX_LD1 (i : nat) : nat := NX i.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NEWS_ED (g : nat) : list kentry := NEWS0 ++ [KWord (SA FE 432) 1 (EVar g); KRange (EVar g) 0 255; KWord (SA FE 448) 8 (EVar (g + 1))].
Definition S2BIT (g : nat) (b : Z) : kentry := KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EVar g) (ELit 1)) (ELit 0)) (ELit 1)) b b.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition od_chk (pc : Z) (i j : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool :=
  (Z.eqb pc PC_OPDEL &&
   ((inb i C_OD1 && CL.ps_reg_is ps 10 (EVar (gI + 1)) && gchk 4096 0 (BLK j) [] NEWS0 None i j c ps cj
       && (negb (Nat.eqb i I_S2) || (has (SR.ps_cells ps) (KWord (SA FE 432) 1 (EVar gED)) && has (SR.ps_cells ps) (S2BIT gED 1) && negb (CL.ps_reg_is ps 10 (EVar (gED + 1))))))      (* [comment removed for export] *)
    || (inb i C_OD2 && CL.ps_reg_is ps 10 (EVar (gS + 1)) && gchk 4096 0 (BLK j) [] NEWS0 None i j c ps cj)
    || (Nat.eqb i I_S2 && CL.ps_reg_is ps 10 (EVar (gED + 1)) && gchkn (NX i + 1)%nat 4096 0 (BLK j) [] NEWS0 None i j c ps cj
        && has (SR.ps_cells ps) (KWord (SA FE 432) 1 (EVar gED)) && has (SR.ps_cells ps) (KWord (SA FE 448) 8 (EVar (gED + 1))) && has (SR.ps_cells ps) (S2BIT gED 0))))%bool.      (* [comment removed for export] *)
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      (CH2.blocks_eqb (nth i G.BLS []) (BLK i) && CHA.foot_chk GT.NF G.HDECL c (BLK i) (nth i FFS []) && CBA.regions_eqb (CC.cp_F c) (CPF i) && Nat.eqb (CC.cp_nx c) (NX i)
       && CH2.blocks_vars_lt (CC.cp_nx c) (BLK i) && (Nat.eqb i 0 || inb i C_EX || (kd_ok c && has cells (KWord (SA FE 2040) 8 FLE))) && Z.eqb (SR.ps_pc ps) pc &&
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (Nat.eqb j (RJ i ps) && CH2.blocks_eqb (nth j G.BLS []) (BLK j) &&
              if Z.eqb pc PC_SM5 then
                (Nat.eqb i 0 && CHA.frames_eqb (nth 1 FFS []) FRM
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 [] [] [] (NEWS_SM ps cj) None c ps cj [] [] [] FRM with
                    | Some ci => (Nat.eqb (CH2.ci_nx ci) 40 && Z.eqb (CH2.ci_csp ci) (-160))%bool | None => false end
                 && CL.ps_reg_is ps 10 (ELit 1728))%bool
              else if Z.eqb pc PC_SFREE5 then
                (inb i C_SF && CHA.frames_eqb (nth i FFS []) FRM && CHA.frames_eqb (nth j FFS []) []
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 0 [] [] [] (NEWS_SF cj) None c ps cj [] FRM [] [] with
                    | Some ci => (Z.eqb (CH2.ci_csp ci) (-160) && Nat.eqb (CH2.ci_nx ci) (NX i))%bool | None => false end
                 && CL.ps_reg_is ps 10 FE && CL.ps_reg_is ps 11 (ELit 1728))%bool
              else
               (CHA.frames_eqb (nth i FFS []) FRM && CHA.frames_eqb (nth j FFS []) FRM &&
                if Z.eqb pc PC_SETSHF8 then
                  ((Nat.eqb i 1 || Nat.eqb i I_SH2) && gchk 256 0 (BLK i) [RDRSH] NEWS0 None i j c ps cj
                   && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD (CHA.SRL3 FE) (ELit (SBz + 122))) && CL.ps_reg_is ps 11 (ELit 74))%bool
                else if Z.eqb pc PC_SETSH00 then
                  (Nat.eqb i I_SH0 && gchk 256 0 (BLK i) [RDRSH] NEWS_SH0 None i j c ps cj
                   && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD (CHA.SRL3 FE) (ELit (SBz + 122))) && CL.ps_reg_is ps 11 (ELit 74))%bool
                else if Z.eqb pc PC_STRINIT then
                  (Nat.eqb i I_STR && gchk 4176 NG_STR (BLK i) [(IAF 32, 0, ELit 24)] NEWS_STR None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 32) && CL.ps_reg_is ps 11 PTRE && CL.ps_reg_is ps 12 NE && fsh cells 4 3)%bool
                else if Z.eqb pc PC_ISS then
                  (Nat.eqb i I_ISS && gchk 10752 NG_STR (BLK i) ((IAF 96, 0, ELit 272) :: FOOTW) NEWS_ISS None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 96) && CL.ps_reg_is ps 11 (IAF 32) && CL.ps_reg_is ps 12 (ELit 8) && fsh cells 4 3 && fsh cells 12 34
                   && s_has cells)%bool
                else if Z.eqb pc PC_AMEMSET then
                  (Nat.eqb i I_MS && gchk 2560 0 (BLK i) [(IAF 432, 0, ELit 24)] NEWS_MS (Some (IAF 432)) i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 432) && CL.ps_reg_is ps 11 (ELit 0) && CL.ps_reg_is ps 12 (ELit 24) && fsh cells 54 3)%bool
                else if Z.eqb pc PC_ENCCTOR then
                  (Nat.eqb i I_EC && gchk 4880 0 (BLK i) [(IAF 496, 0, ELit 408); (SKT, 0, ELit 8)] NEWS_EC None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 496) && CL.ps_reg_is ps 11 SKT && CL.ps_reg_is ps 12 ALLOCT && fsh cells 62 51 && fsh cells 54 3
                   && has cells (KWord (SA (EVar 2) (-112)) 8 (IAF 432)) && has cells (KZero (SA FE 432) (ELit 24)))%bool
                else if Z.eqb pc PC_ENCDTOR then
                  (Nat.eqb i I_ED && gchk 4224 2 (BLK i) [(IAF 496, 0, ELit 408)] (NEWS_ED (NX i)) None i j c ps cj && CL.ps_reg_is ps 10 (IAF 496) && fsh cells 62 51 && fsh cells 54 3)%bool
                else if Z.eqb pc PC_RCTOR then
                  (Nat.eqb i I_RC && gchk 9440 3 (BLK i) [(IAF 976, 0, ELit 592)] NEWS_RC None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 976) && CL.ps_reg_is ps 11 (IAF 96) && CL.ps_reg_is ps 12 (IAF 496) && CL.ps_reg_is ps 13 SKT
                   && fsh cells 12 34 && fsh cells 62 51 && has cells (KZero (SHF 122) (ELit 74)))%bool
                else if Z.eqb pc PC_SYSCAT then
                  (Nat.eqb i I_SC && gchk 128 0 (BLK i) [(ELit 0, SYSCAT_GUARD, ELit 2)] NEWS0 (Some (ELit OBJ_SYSCAT)) i j c ps cj)%bool
                else if Z.eqb pc PC_READ then
                  (Nat.eqb i I_RD && gchk 17856 5 (SBLK i) W_RD (NEWS_RD2 (NX i)) None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 976) && CL.ps_reg_is ps 11 (IAF 1696)
                   && fsh cells 12 34 && fsh cells 62 51 && fsh cells 54 3 && has cells (KZero (SHF 122) (ELit 74)) && fsh cells 212 2
                   && has cells (KWord (SA FE 1696) 4 (ELit 0)) && has cells (KWord (SA FE 1704) 8 (ELit OBJ_SYSCAT)))%bool
                else if Z.eqb pc PC_PDTOR then
                  (Nat.eqb i I_PD && gchk 4272 0 (skipn 2 (BLK i)) [(IAF 1296, 0, ELit 272)] NEWS0 None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 1296) && has cells (KZero (SHF 122) (ELit 74)) && has cells (KRange (EVar (gRD + 3)) 1 4096) && has cells (KRange (EVar (gRD + 1)) 264 134217728))%bool
                else if Z.eqb pc PC_SDTOR then
                  (Nat.eqb i I_SD && gchk 4224 0 (tl (BLK i)) [(IAF 976, 0, ELit 592)] NEWS0 None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 976) && has cells (KZero (SHF 122) (ELit 74)))%bool
                else if Z.eqb pc PC_LOCDTOR then
                  (((inb i C_LD1 && CL.ps_reg_is ps 10 (IAF 120) && has cells (KWord (SA FE 120) 8 (ELit IMP)))
                    || (inb i C_LD2 && CL.ps_reg_is ps 10 (IAF 264) && has cells (KWord (SA FE 264) 8 (ELit IMP))))
                   && gchk 0 0 (BLK i) [] NEWS0 None i j c ps cj
                   && (negb (Nat.eqb i I_S2) || (has cells (KWord (SA FE 432) 1 (EVar gED)) && has cells (S2BIT gED 1) && negb (CL.ps_reg_is ps 10 (EVar (gED + 1))))))%bool      (* [comment removed for export] *)
                else if Z.eqb pc PC_FREE then
                  (inb i C_FR && gchk 4096 0 (BLK i) [] NEWS0 None i j c ps cj && CL.ps_reg_is ps 10 (ELit 0))%bool
                else od_chk pc i j c ps cj))%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && inb i C_EX && CBB.exit_base_chk_sp GT.NF RETPC SPX c ps && CHA.frames_eqb (nth i FFS []) [] && CL.ps_reg_is ps 10 (ELit 0))%bool
      end)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma scr_eq : CH.hd_scr G.HDECL = 18416. Proof. reflexivity. Qed.
Lemma FFSi : forall i, nth i FFS [] = (if (Nat.eqb i 0 || inb i C_EX || Nat.leb NCUT i)%bool then [] else FRM).
Proof. intros i. unfold FFS, NCUT, C_EX, inb. dcut i. cbn. destruct i; reflexivity. Qed.
Lemma CPF_cases : forall i r, In r (CPF i) ->
  r = STKR \/ r = FSHR \/ r = (FE, 0, ELit 24) \/ r = (FE, 32, ELit 2008) \/ r = (FE, 1696, ELit 16) \/ r = (FE, 96, ELit 272) \/ r = TOPR.
Proof.
  intros i r. unfold CPF. repeat match goal with |- In r (if ?b then _ else _) -> _ => destruct b end; cbn [In]; intros H; decompose [or] H; clear H; subst; tauto.
Qed.
Lemma BLS_i : forall i, (i < NCUT)%nat -> nth i G.BLS [] = BLK i.
Proof. intros i Hi. unfold NCUT in Hi. dcut i. exfalso. lia. Qed.
End HNA.
