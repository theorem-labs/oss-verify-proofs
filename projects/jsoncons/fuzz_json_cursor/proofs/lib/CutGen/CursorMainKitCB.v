(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutRtC CutRtD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs PmCurSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCB RdKitCb CurKitCB2 CurTopKitCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_cmain_cboth_T Cut_cmain_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_cmain_cboth.
Module GT := Cut_cmain_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module CMX.
Definition PC_SM0 : Z := 413284.
Definition PC_AMEMSET : Z := 521936.
Definition PC_MEMSET : Z := 520744.
Definition PC_LOCALE : Z := 1161604.
Definition PC_OPNEW : Z := 1363704.
Definition PC_AMEMCPY : Z := 520756.
Definition PC_STRRES : Z := 989296.
Definition PC_VECRES : Z := 829676.
Definition PC_VPUSH : Z := 807908.
Definition PC_SYSCAT : Z := 1007612.
Definition PC_RDNEXT : Z := 737356.
Definition PC_SETEC2 : Z := 827556.
Definition RETPC : Z := 822624.
Definition R0PC : Z := 822468.
Definition SBz : Z := 2147450880.
Definition IMP : Z := 6884304.
Definition OBJ_SYSCAT : Z := 1412240.
Definition OBJ_JSON : Z := 1412184.
Definition CE := EVar 10. Definition ISE := EVar 13. Definition OE := EVar 14. Definition EE := EVar 15. Definition FLE := EVar 40. Definition FE := EVar 45.
Definition CHE := EVar 157. Definition PE := EVar 265. Definition BE := EVar 282.
Definition IA (k : Z) : expr := EAlu Instr.ALU_ADD CE (ELit k).
Definition IAO (k : Z) : expr := EAlu Instr.ALU_ADD OE (ELit k).
Definition IAF (k : Z) : expr := EAlu Instr.ALU_ADD FE (ELit k).

Definition RNB : list (expr * expr) := [(EVar 347, EVar 348); (EVar 349, EVar 350); (EVar 351, ELit 16384)].
Definition R0B : list (expr * expr) := [(EVar 80, EVar 81); (EVar 82, EVar 83); (EVar 84, ELit 16384)].
Definition BLKS (i : nat) : list (expr * expr) :=
  if Nat.eqb i 1 then R0B else if (21 <=? i)%nat then RNB else
  (if (17 <=? i)%nat then [(BE, ELit 66)] else []) ++ (if (16 <=? i)%nat then [(PE, ELit 264)] else []) ++ (if (9 <=? i)%nat then [(CHE, ELit 16384)] else []).
Definition FRM : list (expr * Z * Z) := [(FE, 0, -128)].
Definition FFS : list (list (expr * Z * Z)) := [] :: map (fun _ => FRM) (tl G.CPS).

Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz); KWord (SA (ELit 0) 1432832) 4 (ELit 1)].
Definition OKS : list Z := [8; 9; 10; 11; 16; 48; 64; 72; 80; 104; 128; 152; 176; 200; 224].
Definition ISHS : list Z := [2147622168; 2147622194; 2147622195; 2147623979].
Definition OSHNEWS : list kentry := KZero (SA (CHA.SRL3 OE) SBz) (ELit 1) :: map (fun k => KZero (SA (CHA.SRL3 (IAO k)) SBz) (ELit 1)) OKS.
Definition ISHNEWS : list kentry := map (fun a => KZero (SA (ELit 0) a) (ELit 1)) ISHS.
Definition FRNEWS : list kentry := OSHNEWS ++ ISHNEWS.
Definition FLAGN : list kentry := [KWord (SA FE 56) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition NEWS_MS (base : expr) (off n : Z) : list kentry := STAT ++ FRNEWS ++ [KZero (SA base off) (ELit n)] ++ FLAGN.
Definition NEWS_LOC (off : Z) : list kentry := STAT ++ FRNEWS ++ [KWord (SA CE off) 8 (ELit IMP)] ++ FLAGN.
Definition NEWS_STR : list kentry := [KWord (SA CE 544) 8 (ELit 265); KWord (SA CE 552) 8 (ELit 0); KWord (SA CE 560) 8 PE; KZero (SA CE 568) (ELit 24)] ++ FLAGN.
Definition NEWS_VEC : list kentry := [KWord (SA CE 568) 8 BE; KWord (SA CE 576) 8 BE; KWord (SA CE 584) 8 (EAlu Instr.ALU_ADD BE (ELit 66))] ++ FLAGN.
Definition NEWS_PUSH : list kentry := STAT ++ FRNEWS ++ [KWord (SA CE 568) 8 BE; KWord (SA CE 576) 8 (EAlu Instr.ALU_ADD BE (ELit 1)); KWord (SA CE 584) 8 (EAlu Instr.ALU_ADD BE (ELit 66))] ++ FLAGN.
Definition NEWS_SYS : list kentry := STAT ++ FRNEWS ++ FLAGN.
Definition RN_W : list (expr * Z * expr) :=
  [(CE, 0, ELit 656); (ISE, 0, ELit 272); (IAF 32, 0, ELit 16); (ELit 0, 6882184, ELit 2); (ELit 0, 7020000, ELit 544); (ELit 0, 6888684, ELit 4)].
Definition NEWS_RN : list kentry :=
  STAT ++ FRNEWS ++ [KWord (SA FE 32) 4 (EVar 352); KRange (EVar 352) 0 31; KUnk (SA FE 32) (ELit 16); KWord (SA FE 40) 8 (EVar 355); KWr (SA CE 640) (ELit 1);
                      KWord (SA CE 640) 1 (EVar 354)] ++ FLAGN.
Definition TMP : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)).
Definition EC2_W : list (expr * Z * expr) := [(TMP, 0, ELit 16); (ELit 0, 6882184, ELit 2); (ELit 0, 7020000, ELit 544)].
Definition NEWS_EC2 : list kentry := STAT ++ FRNEWS ++ [KUnk (SA TMP 0) (ELit 16); KWord (SA TMP 0) 4 (ELit 1); KWord (SA TMP 8) 8 (ELit OBJ_JSON);
  KWord (SA (EVar 2) (-120)) 4 (ELit 1); KWord (SA (EVar 2) (-112)) 8 (ELit OBJ_JSON)] ++ FLAGN.
Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
Definition DEADPC : Z := 822628.
Definition CATE : expr := EVar 355.  Definition CODEE : expr := EVar 352.
Definition IMGHI : Z := 7028736.

Definition sm_ok (ps : SR.post_spec) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok IMGHI G.HDECL (SR.ps_cells ps) 40 [] [] 0 45 40 X)%bool.
Definition NEWS_SM (ps : SR.post_spec) (cj : CC.cutpoint) : list kentry := List.filter (fun X => sm_ok ps X || CC.has_cell ISHNEWS X) (CC.cp_know cj).
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.

Definition MSITE (i : nat) : option (Z * expr * Z * Z) :=
  match i with
  | 2%nat => Some (PC_MEMSET, CE, 152, 80) | 5%nat => Some (PC_AMEMSET, CE, 48, 48) | 6%nat => Some (PC_AMEMSET, CE, 264, 16)
  | 7%nat => Some (PC_AMEMSET, CE, 288, 16) | 12%nat => Some (PC_AMEMSET, CE, 488, 40) | 13%nat => Some (PC_AMEMSET, CE, 544, 24) | 14%nat => Some (PC_AMEMSET, CE, 568, 24) | 18%nat => Some (PC_AMEMSET, CE, 616, 25) | _ => None
  end.
Definition MCSITE (i : nat) : option (Z * Z) := match i with 9%nat => Some (344, 176) | 10%nat => Some (368, 200) | 11%nat => Some (392, 152) | _ => None end.
Definition LOCSITE (i : nat) : option Z := match i with 3%nat => Some 144 | 4%nat => Some 40 | _ => None end.
Definition CPF0 : list SGP.region := [(EVar 2, -10848, ELit 10848); (CE, 0, ELit 656)].
Definition CPF : list SGP.region := [(EVar 2, -10848, ELit 10848); (CE, 0, ELit 656); (FE, 0, ELit 24); (FE, 32, ELit 24); (CHA.SRL3 FE, SBz, ELit 8)].

Definition CPFN : list SGP.region := [(EVar 2, -10848, ELit 10848); (CHA.SRL3 FE, SBz, ELit 8)].
Definition CPFE : list SGP.region := CPFN ++ [(CE, 640, ELit 1)].
Definition CPFR : list SGP.region := [(EVar 2, -10848, ELit 10848); (FE, 0, ELit 24); (FE, 32, ELit 24); (CHA.SRL3 FE, SBz, ELit 8); (FLE, 0, ELit 1)].

Definition kd_ok (c : CC.cutpoint) : bool :=
  has (CC.cp_know c) (KDisj (SA FE 0) (ELit 64) (SA CE 0) (ELit 656)) && has (CC.cp_know c) (KDisj (SA FE 0) (ELit 64) (SA ISE 0) (ELit 272)) &&
  has (CC.cp_know c) (KDisj (SA FE 0) (ELit 64) (SA EE 0) (ELit 16)) && has (CC.cp_know c) (KDisj (SA FE 0) (ELit 64) (SA OE 0) (ELit 240)).

Definition RNCL : list kentry :=
  [KWord (SA CE 40) 8 (ELit IMP); KWord (SA CE 128) 4 (ELit 0); KWord (SA CE 132) 4 (ELit 0); KWord (SA CE 136) 8 (IA 32); KWord (SA CE 144) 8 (ELit IMP); KZero (SA CE 152) (ELit 80);
   KWord (SA CE 248) 8 ISE; KWord (SA CE 256) 8 (EAlu Instr.ALU_ADD ISE (ELit 16)); KWord (SA CE 272) 8 CHE; KWord (SA CE 280) 8 (ELit 16384); KWord (SA CE 288) 8 CHE; KZero (SA CE 296) (ELit 8);
   KWord (SA CE 304) 1 (ELit 1); KWord (SA CE 320) 8 (ELit 1369536); KWord (SA CE 328) 4 (ELit 1024);
   KWord (SA CE 332) 1 (ELit 0); KWord (SA CE 333) 1 (ELit 1); KWord (SA CE 334) 1 (ELit 0); KWord (SA CE 335) 1 (ELit 1); KWord (SA CE 336) 1 (ELit 0); KWord (SA CE 337) 1 (ELit 0); KWord (SA CE 338) 1 (ELit 0);
   KZero (SA CE 344) (ELit 24); KZero (SA CE 368) (ELit 24); KZero (SA CE 392) (ELit 24); KWord (SA CE 416) 8 (ELit 1370488); KWord (SA CE 448) 8 (IA 416); KWord (SA CE 464) 4 (ELit 0);
   KZero (SA CE 488) (ELit 40); KWord (SA CE 528) 1 (ELit 1); KWord (SA CE 529) 1 (ELit 0); KWord (SA CE 530) 1 (ELit 0); KWord (SA CE 531) 1 (ELit 1); KWord (SA CE 532) 1 (ELit 0); KWord (SA CE 533) 1 (ELit 1);
   KWord (SA CE 536) 4 (ELit 0); KWord (SA CE 544) 8 (ELit 265); KWord (SA CE 552) 8 (ELit 0); KWord (SA CE 560) 8 PE;
   KWord (SA CE 568) 8 BE; KWord (SA CE 576) 8 (EAlu Instr.ALU_ADD BE (ELit 1)); KWord (SA CE 584) 8 (EAlu Instr.ALU_ADD BE (ELit 66));
   KWord (SA CE 592) 8 (ELit 1370856); KZero (SA CE 616) (ELit 25);
   KWord (SA FE 32) 4 (ELit 0); KWord (SA (CHA.SRL3 FE) (SBz + 4)) 1 (ELit 0); KWord (SA (CHA.SRL3 FE) (SBz + 5)) 1 (ELit 0); KZero (SA (CHA.SRL3 CE) SBz) (ELit 82)].
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto j s => (Nat.eqb j 1 && (21 <=? i)%nat && (i <=? 24)%nat && CBA.regions_eqb (CC.cp_F c) (if (22 <=? i)%nat then CPFE else CPFN)
                     && CH2.blocks_eqb (nth i G.BLS []) RNB && CHA.frames_eqb (nth i FFS []) FRM && Nat.leb 356 (CC.cp_nx c) && kd_ok c
                     && expr_eqb (CC.slook s 40) FLE && expr_eqb (CC.slook s 45) FE && expr_eqb (CC.slook s 80) (EVar 347) && expr_eqb (CC.slook s 81) (EVar 348)
                     && expr_eqb (CC.slook s 82) (EVar 349) && expr_eqb (CC.slook s 83) (EVar 350) && expr_eqb (CC.slook s 84) (EVar 351)
                     && (if Nat.eqb i 21 then has cells (KRange (EVar 352) 0 0) && has cells (KWord (SA CE 640) 1 (EVar 354))
                         else if Nat.eqb i 22 then has cells (KWord (SA CE 640) 1 (ELit 1))
                         else has cells (KRange (EVar 352) 1 31) && has cells (KWord (SA CE 640) 1 (EVar 354))))%bool
  | CC.TOther pc =>
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (CH2.blocks_eqb (nth i G.BLS []) (BLKS i) && CH2.blocks_eqb (nth j G.BLS []) (BLKS j) && CHA.frames_eqb (nth i FFS []) (if Nat.eqb i 0 then [] else FRM)
               && CHA.frames_eqb (nth j FFS []) FRM && CHA.foot_chk GT.NF G.HDECL c (BLKS i) (nth i FFS []) && CH2.blocks_vars_lt (CC.cp_nx c) (BLKS i)
               && (Nat.eqb i 0 || (kd_ok c && Nat.leb 46 (CC.cp_nx c) && (Nat.eqb i 2 || forallb (has cells) OSHNEWS))) &&
              if Z.eqb pc PC_SM0 then
                (Z.eqb (SR.ps_pc ps) PC_SM0 && Nat.eqb i 0 && Nat.eqb j 2 && CBA.regions_eqb (CC.cp_F c) CPF0
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 [] [] [] (NEWS_SM ps cj) None c ps cj [] [] [] FRM with
                    | Some ci => (Nat.eqb (CH2.ci_nx ci) 40 && Z.eqb (CH2.ci_csp ci) (-128))%bool | None => false end)%bool
              else if Z.eqb pc PC_AMEMSET || Z.eqb pc PC_MEMSET then
                match MSITE i with
                | Some (pcx, base, off, n) =>
                    (Z.eqb (SR.ps_pc ps) pcx && Z.eqb pc pcx && Nat.eqb j (i + 1) && CBA.regions_eqb (CC.cp_F c) CPF
                     && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 (BLKS i) FRM [(EAlu Instr.ALU_ADD base (ELit off), 0, ELit n)] (NEWS_MS base off n) (Some (EAlu Instr.ALU_ADD base (ELit off))) c ps cj (BLKS i) FRM (BLKS j) FRM)
                     && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD base (ELit off)) && CL.ps_reg_is ps 11 (ELit 0) && CL.ps_reg_is ps 12 (ELit n)
                     && has cells (KZero (SA (CHA.SRL3 CE) SBz) (ELit 82)) && has cells (KWord (SA FE 56) 8 FLE))%bool
                | None => false
                end
              else if Z.eqb pc PC_LOCALE then
                match LOCSITE i with
                | Some off =>
                    (Z.eqb (SR.ps_pc ps) PC_LOCALE && Nat.eqb j (i + 1) && CBA.regions_eqb (CC.cp_F c) CPF
                     && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 64 0 (BLKS i) FRM [(IA off, 0, ELit 8)] (NEWS_LOC off) None c ps cj (BLKS i) FRM (BLKS j) FRM)
                     && CL.ps_reg_is ps 10 (IA off) && has cells (KWord (SA FE 56) 8 FLE))%bool
                | None => false
                end
              else if Z.eqb pc PC_OPNEW then
                let nx := (CC.cp_nx cj - APC.NCS)%nat in let news := news_of (nx + 4) cj in
                (Z.eqb (SR.ps_pc ps) PC_OPNEW && Nat.eqb i 8 && Nat.eqb j 9 && Nat.eqb nx 153 && CBA.regions_eqb (CC.cp_F c) CPF
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4112 0 [] FRM [] (news ++ FRNEWS ++ FLAGN) None c ps cj [] FRM (BLKS 9) FRM)
                 && CRB.fresh_news_ok 65536 7028736 G.HDECL GT.SCELLS GT.GLO GT.GHI cells nx [] FRM (nx + 4) (ELit 16384) news
                 && CL.ps_reg_is ps 10 (ELit 16384) && has cells (KWord (SA FE 56) 8 FLE))%bool
              else if Z.eqb pc PC_AMEMCPY then
                match MCSITE i with
                | Some (doff, soff) =>
                    (Z.eqb (SR.ps_pc ps) PC_AMEMCPY && Nat.eqb j (i + 1) && CBA.regions_eqb (CC.cp_F c) CPF
                     && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 (BLKS i) FRM [(IA doff, 0, ELit 24)] (NEWS_MS CE doff 24) (Some (IA doff)) c ps cj (BLKS i) FRM (BLKS j) FRM)
                     && CL.ps_reg_is ps 10 (IA doff) && CL.ps_reg_is ps 11 (IAO soff) && CL.ps_reg_is ps 12 (ELit 24)
                     && has cells (KZero (SA (CHA.SRL3 CE) SBz) (ELit 82)) && has cells (KZero (SA OE 80) (ELit 144)) && has cells (KWord (SA FE 56) 8 FLE))%bool
                | None =>

                    (Z.eqb (SR.ps_pc ps) PC_AMEMCPY && Nat.eqb i 22 && ((Nat.eqb j 23) || (Nat.eqb j 24)) && CBA.regions_eqb (CC.cp_F c) CPFE && Nat.leb 356 (CC.cp_nx c)
                     && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 RNB FRM [(EE, 0, ELit 16)] NEWS_SYS (Some EE) c ps cj RNB FRM RNB FRM)
                     && CL.ps_reg_is ps 10 EE && CL.ps_reg_is ps 11 (IAF 32) && CL.ps_reg_is ps 12 (ELit 16) && has cells (KWord (SA FE 56) 8 FLE)
                     && has cells (KWord (SA CE 640) 1 (EVar 354))
                     && has cells (KWord (SA (CHA.SRL3 FE) (SBz + 4)) 1 (ELit 0)) && has cells (KWord (SA (CHA.SRL3 FE) (SBz + 5)) 1 (ELit 0)))%bool
                end
              else if Z.eqb pc PC_STRRES then
                let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in let news := news_of nx cj in
                (Z.eqb (SR.ps_pc ps) PC_STRRES && Nat.eqb i 15 && Nat.eqb j 16 && Nat.eqb nx 265 && CBA.regions_eqb (CC.cp_F c) CPF
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4368 1 (BLKS 15) FRM [(IA 544, 0, ELit 24)] (news ++ FRNEWS ++ NEWS_STR ++ STAT) None c ps cj (BLKS 15) FRM (BLKS 16) FRM)
                 && CL.ps_reg_is ps 10 (IA 544) && CL.ps_reg_is ps 11 (ELit 256)
                 && has cells (KZero (SA CE 544) (ELit 24)) && has cells (KZero (SA CE 568) (ELit 24))
                 && has cells (KZero (SA (CHA.SRL3 CE) SBz) (ELit 82)) && has cells (KWord (SA FE 56) 8 FLE))%bool
              else if Z.eqb pc PC_VECRES then
                let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in let news := news_of nx cj in
                (Z.eqb (SR.ps_pc ps) PC_VECRES && Nat.eqb i 16 && Nat.eqb j 17 && Nat.eqb nx 282 && CBA.regions_eqb (CC.cp_F c) CPF
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 8192 1 (BLKS 16) FRM [(IA 568, 0, ELit 24)] (news ++ FRNEWS ++ NEWS_VEC ++ STAT) None c ps cj (BLKS 16) FRM (BLKS 17) FRM)
                 && CL.ps_reg_is ps 10 (IA 568) && CL.ps_reg_is ps 11 (ELit 66) && has cells (KZero (SA CE 568) (ELit 24))
                 && has cells (KZero (SA (CHA.SRL3 CE) SBz) (ELit 82)) && has cells (KWord (SA FE 56) 8 FLE))%bool
              else if Z.eqb pc PC_VPUSH then
                (Z.eqb (SR.ps_pc ps) PC_VPUSH && Nat.eqb i 17 && Nat.eqb j 18 && CBA.regions_eqb (CC.cp_F c) CPF
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 8240 0 (BLKS 16) FRM [(IA 568, 0, ELit 24)] NEWS_PUSH None c ps cj (BLKS 17) FRM (BLKS 18) FRM)
                 && CL.ps_reg_is ps 10 (IA 568) && CL.ps_reg_is ps 11 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-225))) && CL.ps_reg_is ps 2 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-240)))
                 && has cells (KWord (SA CE 568) 8 BE) && has cells (KWord (SA CE 576) 8 BE) && has cells (KWord (SA CE 584) 8 (EAlu Instr.ALU_ADD BE (ELit 66)))
                 && has cells (KWord (SA (EVar 2) (-225)) 1 (ELit 0)) && has cells (KZero (SA (CHA.SRL3 CE) SBz) (ELit 82)) && has cells (KWord (SA FE 56) 8 FLE))%bool
              else if Z.eqb pc PC_SYSCAT then
                (Z.eqb (SR.ps_pc ps) PC_SYSCAT && Nat.eqb i 19 && Nat.eqb j 20 && CBA.regions_eqb (CC.cp_F c) CPF
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 128 0 (BLKS 18) FRM [(ELit 0, 6882752, ELit 2)] NEWS_SYS (Some (ELit OBJ_SYSCAT)) c ps cj (BLKS 19) FRM (BLKS 20) FRM)
                 && has cells (KWord (SA FE 56) 8 FLE))%bool
              else if Z.eqb pc PC_RDNEXT then
                (Z.eqb (SR.ps_pc ps) PC_RDNEXT && Nat.eqb i 20 && Nat.eqb j 21 && CBA.regions_eqb (CC.cp_F c) CPF
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 10720 9 [] FRM RN_W NEWS_RN None c ps cj (BLKS 20) FRM RNB FRM with
                    | Some ci => (Z.eqb (CH2.ci_csp ci) (-128) && Nat.eqb (CH2.ci_nx ci) 347)%bool | None => false end
                 && CL.ps_reg_is ps 10 CE && CL.ps_reg_is ps 11 (IA 592) && CL.ps_reg_is ps 12 (IAF 32) && has cells (KWord (SA FE 56) 8 FLE) && forallb (has cells) RNCL)%bool
              else if Z.eqb pc PC_SETEC2 then
                (Z.eqb (SR.ps_pc ps) PC_SETEC2 && Nat.eqb i 21 && Nat.eqb j 22 && CBA.regions_eqb (CC.cp_F c) CPFN && Nat.leb 356 (CC.cp_nx c)
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 1024 0 RNB FRM EC2_W NEWS_EC2 None c ps cj RNB FRM RNB FRM with
                    | Some ci => Z.eqb (CH2.ci_csp ci) (-128) | None => false end
                 && CL.ps_reg_is ps 10 TMP && CL.ps_reg_is ps 11 (ELit 1) && has cells (KWord (SA FE 56) 8 FLE) && has cells (KRange (EVar 352) 1 31))%bool
              else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && Nat.eqb i 1 && CBA.exit_base_chk GT.NF RETPC c ps && CBA.regions_eqb (CC.cp_F c) CPFR && CH2.blocks_eqb (nth i G.BLS []) R0B
           && CHA.frames_eqb (nth i FFS []) FRM
           && match CHA.retire_chk GT.NF G.HDECL c R0B FRM with Some fl => expr_eqb fl FLE | None => false end
           && has cells (KWord (SA FLE 0) 1 (ELit 0)) && CL.ps_reg_is ps 10 FLE && Nat.leb 85 (CC.cp_nx c))%bool
          || (Z.eqb pc DEADPC && Nat.eqb i 22 && CBA.regions_eqb (CC.cp_F c) CPFE && Nat.leb 356 (CC.cp_nx c) && kd_ok c
              && has cells (KWord (SA FE 40) 8 CATE) && has cells (KRange CODEE 1 31)
              && (has cells (KRange CATE 0 0) || has cells (KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND CATE (ELit 7)) (ELit 0)) (ELit 1)) 0 0)))%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End CMX.
