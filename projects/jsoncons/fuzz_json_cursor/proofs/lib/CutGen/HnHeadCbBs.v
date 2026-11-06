(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA HeapIfaceANull L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutBridgeB CutRtCpsA CutRtA CutRtB CutRtC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs PmCurSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_harness_bs_cboth_T Cut_harness_bs_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_harness_bs_cboth.
Module GT := Cut_harness_bs_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module HNC.

Definition PC_HN : Z := 718148.
Definition PC_SM5 : Z := 415356.
Definition PC_SFREE5 : Z := 415880.
Definition PC_SETSH00 : Z := 535972.
Definition PC_SETSHF8 : Z := 536260.
Definition PC_FREE : Z := 527796.
Definition PC_STRINIT : Z := 720088.
Definition PC_ISS : Z := 720448.
Definition PC_CCTOR : Z := 721120.
Definition PC_GET : Z := 841728.
Definition PC_RN : Z := 737356.
Definition PC_PDTOR : Z := 726328.
Definition PC_SDTOR : Z := 728272.
Definition PC_OPDEL : Z := 980676.
Definition PC_SYSCAT : Z := 1007612.
Definition PC_LOCDTOR : Z := 1161820.
Definition RETPC : Z := 719704.
Definition SPX : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit 16).
Definition SBz : Z := 2147450880.
Definition IMP : Z := 6884304. Definition VT_ISS : Z := 1384816. Definition VT_SBUF : Z := 1384576. Definition VT_IOS : Z := 1384856.
Definition OBJ_SYSCAT : Z := 1412240. Definition G_GUARD : Z := 6882184. Definition CONV_GUARD : Z := 6882176. Definition SYSCAT_GUARD : Z := 6882752.
Definition AXT : Z := 7020000. Definition ERRNO : Z := 6888684.
Definition IMGHI : Z := 7028736.
Definition FE := EVar 45. Definition FLE := EVar 40. Definition PTRE := EVar 10. Definition NE := EVar 11.
Definition IAF (k : Z) : expr := EAlu Instr.ALU_ADD FE (ELit k).
Definition SHF (g : Z) : saddr := SA (CHA.SRL3 FE) (SBz + g).
Definition FRM : list (expr * Z * Z) := [(FE, 5, -160)].
Definition FSHR : SGP.region := (CHA.SRL3 FE, SBz, ELit 256).

Definition I_SM : nat := 0. Definition I_SH8A : nat := 7. Definition I_STR : nat := 12. Definition I_ISS : nat := 18. Definition I_SC : nat := 21. Definition I_SH0 : nat := 23.
Definition I_CC : nat := 25. Definition I_CCR : nat := 27.
Definition I_HA : nat := 1. Definition I_HA2 : nat := 2. Definition I_HB : nat := 3. Definition I_TS : nat := 4. Definition I_TR : nat := 5. Definition I_X : nat := 6.
Definition I_J1 : nat := 8. Definition I_J2 : nat := 9. Definition I_J3 : nat := 10. Definition I_PDR : nat := 11. Definition I_J1R : nat := 13. Definition I_J2R : nat := 14.
Definition I_J2D1 : nat := 15. Definition I_J3R : nat := 16. Definition I_SDR : nat := 17. Definition I_J2D2 : nat := 19.

Definition VAC (i : nat) : bool := Nat.eqb i I_HA2 || Nat.eqb i I_J3 || Nat.eqb i I_J3R.

Definition VB : nat := 200. Definition VEC : nat := 250. Definition VPD : nat := 251. Definition VDN : nat := 252. Definition GG : nat := 260. Definition GRN : nat := 281.
Definition BLD3 : list (expr * expr) := [(EVar 200, EVar 201); (EVar 202, EVar 203); (EVar 204, ELit 16384)].
Definition RNB3 : list (expr * expr) := [(EVar 281, EVar 282); (EVar 283, EVar 284); (EVar 285, ELit 16384)].
Definition S2B : expr * expr := (EVar 263, EVar 264).

Definition ALN : Z := 16.
Definition LNG : bool := false.
Definition NCUT : nat := 32.
Definition NX (i : nat) : nat := nth i [40; 260; 260; 260; 260; 260; 260; 57; 281; 281; 281; 276; 73; 305; 305; 297; 305; 292; 89; 321; 308; 105; 324; 121; 340; 137; 356; 161; 372; 388; 404; 420]%nat 0%nat.

Definition I_OD1 : nat := 99.
Definition I_LD1 : nat := 20.
Definition I_LD2 : nat := 22.
Definition I_FR1 : nat := 24.
Definition I_FR2 : nat := 26.
Definition I_FR3 : nat := 28.
Definition I_FR4 : nat := 29.
Definition I_OD2 : nat := 99.
Definition I_SF : nat := 30.
Definition I_EX : nat := 31.
Definition gCC : nat := 137.
Definition gS : nat := 73.
Definition gI : nat := 89.
Definition SBL : list (expr * expr) := [].
Definition BLK (i : nat) : list (expr * expr) :=
  if Nat.eqb i 0 || Nat.eqb i 7 || Nat.eqb i 12 then []
  else if Nat.eqb i 18 then []
  else if Nat.eqb i 21 || Nat.eqb i 23 || Nat.eqb i 25 then SBL
  else if Nat.eqb i 27 then [(EVar gCC, EVar (gCC + 1)); (EVar (gCC + 2), EVar (gCC + 3)); (EVar (gCC + 4), ELit 16384)] ++ SBL
  else if Nat.eqb i 9 then BLD3 ++ S2B :: SBL
  else if Nat.eqb i 13 || Nat.eqb i 16 || Nat.eqb i 19 then RNB3 ++ SBL
  else if Nat.eqb i 14 then RNB3 ++ S2B :: SBL
  else if (Nat.leb i 6 || Nat.eqb i 8 || Nat.eqb i 10 || Nat.eqb i 15)%bool then BLD3 ++ SBL
  else if Nat.eqb i 11 then (EVar 204, ELit 16384) :: SBL
  else if Nat.eqb i 17 then SBL
  else [].
Definition STKR : SGP.region := (EVar 2, -16368, ELit 16368).
Definition TOPR : SGP.region := (EVar 2, 0, ELit 16).
Definition TAILF : list nat := [17; 20; 22; 24; 26; 28; 29; 30]%nat.
Definition CPF (i : nat) : list SGP.region :=
  if Nat.eqb i 0 || Nat.eqb i I_EX then [STKR; TOPR]
  else if Nat.eqb i 7 || Nat.eqb i 12 then [STKR; TOPR; (FE, 0, ELit 24); (FE, 32, ELit 2008); FSHR]
  else if Nat.eqb i 21 || Nat.eqb i 23 then [STKR; TOPR; (FE, 432, ELit 16); FSHR]
  else if Nat.eqb i 6 then [STKR; TOPR; (FE, 464, ELit 8); (FE, 1112, ELit 8); FSHR]
  else if existsb (Nat.eqb i) TAILF then [STKR; TOPR; (FE, 0, ELit 24); (FE, 96, ELit 272); FSHR]
  else [STKR; TOPR; FSHR].
Definition FFS : list (list (expr * Z * Z)) := map (fun i => if Nat.eqb i 0 || Nat.eqb i I_EX then [] else FRM) (seq 0 NCUT).
Definition CSP (i : nat) : Z := if Nat.eqb i I_LD2 || Nat.eqb i I_FR1 || Nat.eqb i I_FR2 || Nat.eqb i I_FR3 then -208 else -160.
Ltac dcut i := do 32 (destruct i as [|i]; [reflexivity|]).

Definition STAT : list kentry := [KImg 1393824 1397544; KWord (SA (ELit 0) 1432824) 8 (ELit SBz); KWord (SA (ELit 0) 1432832) 4 (ELit 1)].
Definition ISHS : list Z := [2147623989; 2147623992; 2147623979].
Definition ISHZ : list kentry := map (fun a => KZero (SA (ELit 0) a) (ELit 1)) ISHS.
Definition FLAGN : list kentry := [KWord (SA FE 2040) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition G216 : saddr := SA (CHA.SRL3 (IAF 216)) SBz.
Definition FRK : list kentry := [KZero G216 (ELit 1); KDisj (SHF 0) (ELit 27) G216 (ELit 1); KDisj (SHF 28) (ELit 228) G216 (ELit 1)].
Definition NEWS0 : list kentry := STAT ++ ISHZ ++ FLAGN.
Definition TWON : expr := EMd Instr.M_MUL (ELit 2) NE.
Definition CAPW (g : nat) : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar g)) (ELit 1).
Definition BNEWSE (v : nat) (sz : expr) : list kentry :=
  [KRange (EVar v) 4096 140737479966719; KAlign (EVar v) 16; KUnk (SA (EVar v) 0) sz; KWr (SA (EVar v) 0) sz; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar v) 0) sz].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition ISNEWS0 : list kentry :=
  [KWord (SA FE 96) 8 (ELit VT_ISS); KWord (SA FE 112) 8 (ELit VT_SBUF); KWord (SA FE 120) 8 (ELit IMP); KWord (SA FE 216) 8 (ELit VT_IOS); KWord (SA FE 264) 8 (ELit IMP);
   KWord (SA FE 272) 8 (ELit 0); KWord (SA FE 280) 8 (ELit 0); KWord (SA FE 288) 8 (ELit 0); KWord (SA FE 304) 8 (ELit 0); KWord (SA FE 328) 8 (ELit 0); KUnk (SA FE 96) (ELit 272)].

Definition CURN (g : nat) : list kentry := [KWord (SA FE 996) 1 (EVar g); KRange (EVar g) 0 1; KWord (SA FE 1104) 1 (EVar (g + 1)); KRange (EVar (g + 1)) 0 1; KWord (SA FE 432) 4 (EVar (g + 2)); KUnk (SA FE 432) (ELit 16)].
Definition SNEWS : list kentry := [KWord (SA FE 32) 1 TWON; KUnk (SA FE 32) (ELit 24)].
Definition SBN : list kentry := [].
Definition ISW : list kentry := [KWord (SA FE 176) 1 TWON].
Definition IBN : list kentry := [].
Definition NG_STR : nat := 0.
Definition s_has (cells : list kentry) : bool := has cells (KWord (SA FE 32) 1 TWON).

Definition ISNEWS : list kentry := ISNEWS0 ++ ISW.
Definition NEWS_STR : list kentry := NEWS0 ++ SNEWS ++ SBN.
Definition NEWS_ISS : list kentry := NEWS0 ++ FRK ++ ISNEWS ++ IBN.
Definition NEWS_SH0 : list kentry := NEWS0 ++ [KZero (SHF 58) (ELit 82)].
Definition NEWS_CC (g : nat) : list kentry := NEWS0 ++ ISNEWS ++ [KRange (EVar (g + 1)) 264 134217728; KRange (EVar (g + 3)) 1 4096] ++ CURN (g + 5).
Definition NEWS_RN (g : nat) : list kentry := NEWS0 ++ ISNEWS ++ [KRange (EVar (g + 1)) 264 134217728; KRange (EVar (g + 3)) 1 4096] ++ CURN (g + 5).
Definition GET_EC (g : nat) : list kentry := [KWord (SA FE 432) 4 (EVar g); KRange (EVar g) 0 11; KUnk (SA FE 432) (ELit 16)].
Definition NEWS_GETS (g : nat) : list kentry :=
  NEWS0 ++ GET_EC g ++ [KWord (SA FE 1248) 1 (EMd Instr.M_MUL (ELit 2) (EVar (g + 1))); KRange (EVar (g + 1)) 0 22; KUnk (SA FE 1248) (ELit 24)].
Definition NEWS_GETL (g : nat) : list kentry :=
  NEWS0 ++ GET_EC g ++ [KWord (SA FE 1248) 8 (CAPW (g + 1)); KWord (SA FE 1256) 8 (EVar (g + 2)); KWord (SA FE 1264) 8 (EVar (g + 3)); KUnk (SA FE 1248) (ELit 24)]
        ++ BNEWSE (g + 3) (EVar (g + 4)) ++ [KRange (EVar (g + 4)) 24 67108874].

Definition sm_ok (ps : SR.post_spec) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok IMGHI G.HDECL (SR.ps_cells ps) 40 [] [] 5 45 40 X)%bool.
Definition NEWS_SM (ps : SR.post_spec) (cj : CC.cutpoint) : list kentry := List.filter (fun X => sm_ok ps X || CC.has_cell ISHZ X) (CC.cp_know cj).
Definition NEWS_SF (cj : CC.cutpoint) : list kentry := List.filter (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) (CC.cp_know cj).

Definition fsh (cells : list kentry) (lo n : nat) : bool := forallb (fun g => has cells (KWord (SHF (Z.of_nat g)) 1 (ELit 0))) (seq lo n).

Definition RDRSH : SGP.region := (CHA.SRL3 FE, SBz + 58, ELit 82).
Definition FOOTW : list SGP.region :=
  [(ELit 0, 6882184, ELit 2); (ELit 0, 6882752, ELit 2); (ELit 0, 6882768, ELit 504); (ELit 0, 6883448, ELit 1152); (ELit 0, 6886440, ELit 96); (ELit 0, 7020000, ELit 544);
   (ELit 0, 7020579, ELit 1); (ELit 0, 7020800, ELit 4); (ELit 0, 6882176, ELit 2)].
Definition W_CC : list SGP.region :=
  [(IAF 464, 0, ELit 656); (IAF 96, 0, ELit 272); (IAF 432, 0, ELit 16); (ELit 0, G_GUARD, ELit 2); (ELit 0, AXT, ELit 544); (ELit 0, ERRNO, ELit 4); (ELit 0, SYSCAT_GUARD, ELit 2)].
Definition W_RN : list SGP.region :=
  [(IAF 464, 0, ELit 656); (IAF 96, 0, ELit 272); (IAF 432, 0, ELit 16); (ELit 0, G_GUARD, ELit 2); (ELit 0, AXT, ELit 544); (ELit 0, ERRNO, ELit 4)].
Definition W_GET : list SGP.region := [(IAF 1248, 0, ELit 24); (IAF 432, 0, ELit 16); (ELit 0, CONV_GUARD, ELit 2); (ELit 0, AXT, ELit 544); (ELit 0, ERRNO, ELit 4)].

Definition kd_ok (c : CC.cutpoint) : bool :=
  has (CC.cp_know c) (KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA FE 0) (ELit 2048)) && has (CC.cp_know c) (KDisj (SA (EVar 2) (-16368)) (ELit 16368) (SA FE 0) (ELit 2048)).

Definition gchk (scr : Z) (ng : nat) (BLk : list (expr * expr)) (wregs : list SGP.region) (news : list kentry) (a0x : option expr)
           (i j : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool :=
  match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr ng BLk FRM wregs news a0x c ps cj (BLK i) FRM (BLK j) FRM with
  | Some ci => (Z.eqb (CH2.ci_csp ci) (CSP i) && Nat.eqb (CH2.ci_nx ci) (NX i))%bool
  | None => false
  end.

Definition BZ (v : nat) : kentry := KRange (EVar v) 0 0.
Definition WZ (v : nat) : kentry := KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar v)) (ELit 0)) (ELit 1)) 1 1.

Definition slook_ids (s : CC.subst) (vs : list nat) : bool := forallb (fun v => expr_eqb (CC.slook s v) (EVar v)) vs.
Definition slook_map (s : CC.subst) (ps : list (nat * nat)) : bool := forallb (fun p => expr_eqb (CC.slook s (fst p)) (EVar (snd p))) ps.
Definition SGI : list nat := if LNG then [73; 74; 75; 92; 93; 94]%nat else [].
Definition BLKV : list nat := [200; 201; 202; 203; 204]%nat.
Definition goto_ok (i j : nat) (c : CC.cutpoint) (ps : SR.post_spec) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in
  (CBA.regions_eqb (CC.cp_F c) (CPF i) && CH2.blocks_eqb (nth i G.BLS []) (BLK i) && Nat.eqb (CC.cp_nx c) (NX i) && kd_ok c && slook_ids s (40%nat :: 45%nat :: SGI) &&
   (if Nat.eqb i I_CCR then
      slook_map s [(200, gCC); (201, gCC + 1); (202, gCC + 2); (203, gCC + 3); (204, gCC + 4)]%nat
      && (if Nat.eqb j I_HA then slook_map s [(VEC, gCC + 7); (VPD, gCC + 5); (VDN, gCC + 6)]%nat && has cells (BZ (gCC + 5)) && has cells (KWord (SA FE 996) 1 (EVar (gCC + 5))) else Nat.eqb j I_X)
    else if Nat.eqb i I_J1R || Nat.eqb i I_J2D2 then
      Nat.eqb j I_TR && slook_map s [(200, GRN); (201, GRN + 1); (202, GRN + 2); (203, GRN + 3); (204, GRN + 4); (VEC, GRN + 7); (VPD, GRN + 5); (VDN, GRN + 6)]%nat
    else if Nat.eqb i I_J1 || Nat.eqb i I_J2D1 then
      Nat.eqb j I_TS && slook_ids s BLKV && slook_map s [(VEC, GG); (VPD, VPD); (VDN, VDN)]%nat && has cells (KRange (EVar GG) 1 11)
    else if Nat.eqb i I_TS || Nat.eqb i I_TR then
      slook_ids s BLKV && (if Nat.eqb j I_HB then slook_ids s [VEC; VPD; VDN] && has cells (BZ VPD) && has cells (KWord (SA FE 996) 1 (EVar VPD)) else Nat.eqb j I_X)
    else if Nat.eqb i I_HA || Nat.eqb i I_HB then
      Nat.eqb j I_X && slook_ids s BLKV
    else VAC i))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  if VAC i then true else
  match t with
  | CC.TGoto j s => goto_ok i j c ps s
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      (CH2.blocks_eqb (nth i G.BLS []) (BLK i) && CHA.foot_chk GT.NF G.HDECL c (BLK i) (nth i FFS []) && CBA.regions_eqb (CC.cp_F c) (CPF i) && Nat.eqb (CC.cp_nx c) (NX i)
       && CH2.blocks_vars_lt (CC.cp_nx c) (BLK i) && (Nat.eqb i 0 || Nat.eqb i I_EX || (kd_ok c && has cells (KWord (SA FE 2040) 8 FLE))) && Z.eqb (SR.ps_pc ps) pc &&
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (CH2.blocks_eqb (nth j G.BLS []) (BLK j) &&
              if Z.eqb pc PC_SM5 then
                (Nat.eqb i 0 && Nat.eqb j I_SH8A && CHA.frames_eqb (nth I_SH8A FFS []) FRM
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 [] [] [] (NEWS_SM ps cj) None c ps cj [] [] [] FRM with
                    | Some ci => (Nat.eqb (CH2.ci_nx ci) 40 && Z.eqb (CH2.ci_csp ci) (-160))%bool | None => false end
                 && CL.ps_reg_is ps 10 (ELit 1312))%bool
              else if Z.eqb pc PC_SFREE5 then
                (Nat.eqb i I_SF && Nat.eqb j I_EX && CHA.frames_eqb (nth i FFS []) FRM && CHA.frames_eqb (nth j FFS []) []
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 0 [] [] [] (NEWS_SF cj) None c ps cj [] FRM [] [] with
                    | Some ci => (Z.eqb (CH2.ci_csp ci) (-160) && Nat.eqb (CH2.ci_nx ci) (NX i))%bool | None => false end
                 && CL.ps_reg_is ps 10 FE && CL.ps_reg_is ps 11 (ELit 1312))%bool
              else
               (CHA.frames_eqb (nth i FFS []) FRM && CHA.frames_eqb (nth j FFS []) FRM &&
                if Z.eqb pc PC_SETSHF8 then
                  ((Nat.eqb i I_SH8A && Nat.eqb j I_STR || Nat.eqb i I_SDR && Nat.eqb j (if LNG then I_OD1 else I_LD1)) && gchk 256 0 (BLK i) [RDRSH] NEWS0 None i j c ps cj
                   && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD (CHA.SRL3 FE) (ELit (SBz + 58))) && CL.ps_reg_is ps 11 (ELit 82))%bool
                else if Z.eqb pc PC_SETSH00 then
                  (Nat.eqb i I_SH0 && Nat.eqb j I_CC && gchk 256 0 (BLK i) [RDRSH] NEWS_SH0 None i j c ps cj
                   && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD (CHA.SRL3 FE) (ELit (SBz + 58))) && CL.ps_reg_is ps 11 (ELit 82))%bool
                else if Z.eqb pc PC_STRINIT then
                  (Nat.eqb i I_STR && Nat.eqb j I_ISS && gchk 4176 NG_STR (BLK i) [(IAF 32, 0, ELit 24)] NEWS_STR None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 32) && CL.ps_reg_is ps 11 PTRE && CL.ps_reg_is ps 12 NE && fsh cells 4 3)%bool
                else if Z.eqb pc PC_ISS then
                  (Nat.eqb i I_ISS && Nat.eqb j I_SC && gchk 10752 NG_STR (BLK i) ((IAF 96, 0, ELit 272) :: FOOTW) NEWS_ISS None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 96) && CL.ps_reg_is ps 11 (IAF 32) && CL.ps_reg_is ps 12 (ELit 8) && fsh cells 4 3 && fsh cells 12 34
                   && s_has cells)%bool
                else if Z.eqb pc PC_SYSCAT then
                  (Nat.eqb i I_SC && Nat.eqb j I_SH0 && gchk 128 0 (BLK i) [(ELit 0, SYSCAT_GUARD, ELit 2)] NEWS0 (Some (ELit OBJ_SYSCAT)) i j c ps cj
                   && fsh cells 54 2 && has cells (KWord (SA FE 432) 4 (ELit 0)))%bool
                else if Z.eqb pc PC_CCTOR then
                  (Nat.eqb i I_CC && Nat.eqb j I_CCR && gchk 11008 8 (BLK i) W_CC (NEWS_CC (NX i)) None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 464) && CL.ps_reg_is ps 11 (IAF 96) && CL.ps_reg_is ps 12 (IAF 432)
                   && fsh cells 12 34 && fsh cells 54 2 && has cells (KZero (SHF 58) (ELit 82))
                   && has cells (KWord (SA FE 432) 4 (ELit 0)) && has cells (KWord (SA FE 440) 8 (ELit OBJ_SYSCAT)))%bool
                else if Z.eqb pc PC_GET then
                  ((Nat.eqb i I_HA && Nat.eqb j I_J1 && gchk 14384 5 (BLK i) W_GET (NEWS_GETS GG) None i j c ps cj
                     && match nth_error G.CPS I_J2 with
                        | Some cj2 => match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 14384 5 (BLK i) FRM W_GET (NEWS_GETL GG) None c ps cj2 (BLK i) FRM (BLK I_J2) FRM with
                                      | Some ci2 => (Z.eqb (CH2.ci_csp ci2) (CSP i) && Nat.eqb (CH2.ci_nx ci2) (NX i) && Z.eqb (CC.cp_pc cj2) (CC.cp_pc cj))%bool
                                      | None => false end
                        | None => false end
                     && has cells (BZ VDN) && has cells (WZ VEC) && fsh cells 54 2 && has cells (KZero (SHF 58) (ELit 82))
                     && CL.ps_reg_is ps 10 (IAF 1248) && CL.ps_reg_is ps 11 (IAF 1064) && CL.ps_reg_is ps 12 (ELit 0) && CL.ps_reg_is ps 13 (IAF 432) && fsh cells 156 3)
                    || (Nat.eqb i I_HB && Nat.eqb j I_J3 && has cells (WZ VEC)))%bool
                else if Z.eqb pc PC_RN then
                  ((Nat.eqb i I_J1 && Nat.eqb j I_J1R || Nat.eqb i I_J2 && Nat.eqb j I_J2R) && gchk 10720 8 (skipn 3 (BLK i)) W_RN (NEWS_RN (NX i)) None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 464) && CL.ps_reg_is ps 11 (IAF 1056) && CL.ps_reg_is ps 12 (IAF 432) && has cells (KRange (EVar GG) 0 0)
                   && fsh cells 12 34 && fsh cells 54 2 && has cells (KZero (SHF 58) (ELit 82)))%bool
                else if Z.eqb pc PC_PDTOR then
                  (Nat.eqb i I_X && Nat.eqb j I_PDR && gchk 4272 0 (skipn 2 (BLK i)) [(IAF 784, 0, ELit 272)] NEWS0 None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 784) && has cells (KZero (SHF 58) (ELit 82)))%bool
                else if Z.eqb pc PC_SDTOR then
                  (Nat.eqb i I_PDR && Nat.eqb j I_SDR && gchk 4224 0 (tl (BLK i)) [(IAF 472, 0, ELit 592)] NEWS0 None i j c ps cj
                   && CL.ps_reg_is ps 10 (IAF 472) && has cells (KZero (SHF 58) (ELit 82)))%bool
                else if Z.eqb pc PC_LOCDTOR then
                  (((Nat.eqb i I_LD1 && Nat.eqb j I_LD2 && CL.ps_reg_is ps 10 (IAF 120) && has cells (KWord (SA FE 120) 8 (ELit IMP)))
                    || (Nat.eqb i I_LD2 && Nat.eqb j I_FR1 && CL.ps_reg_is ps 10 (IAF 264) && has cells (KWord (SA FE 264) 8 (ELit IMP))))
                   && gchk 0 0 (BLK i) [] NEWS0 None i j c ps cj)%bool
                else if Z.eqb pc PC_FREE then
                  ((Nat.eqb i I_FR1 && Nat.eqb j I_FR2 || Nat.eqb i I_FR2 && Nat.eqb j I_FR3 || Nat.eqb i I_FR3 && Nat.eqb j I_FR4 || Nat.eqb i I_FR4 && Nat.eqb j (if LNG then I_OD2 else I_SF))
                   && gchk 4096 0 (BLK i) [] NEWS0 None i j c ps cj && CL.ps_reg_is ps 10 (ELit 0))%bool
                else if Z.eqb pc PC_OPDEL then
                  (((Nat.eqb i I_J2 && Nat.eqb j I_J2D1 && has cells (KRange (EVar GG) 1 11) || Nat.eqb i I_J2R && Nat.eqb j I_J2D2) && CL.ps_reg_is ps 10 (EVar 263))
                   || (LNG && Nat.eqb i I_OD1 && Nat.eqb j I_LD1 && CL.ps_reg_is ps 10 (EVar 93))
                   || (LNG && Nat.eqb i I_OD2 && Nat.eqb j I_SF && CL.ps_reg_is ps 10 (EVar 74)))
                  && gchk 4096 0 (BLK j) [] NEWS0 None i j c ps cj
                else false))%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && Nat.eqb i I_EX && CBB.exit_base_chk_sp GT.NF RETPC SPX c ps && CHA.frames_eqb (nth i FFS []) [] && CL.ps_reg_is ps 10 (ELit 0))%bool
      end)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma scr_eq : CH.hd_scr G.HDECL = 16368. Proof. reflexivity. Qed.
Lemma FFSi : forall i, nth i FFS [] = (if Nat.eqb i 0 || Nat.eqb i I_EX then [] else if Nat.ltb i NCUT then FRM else []).
Proof. intros i. unfold FFS, NCUT, I_EX. dcut i. destruct i; reflexivity. Qed.
Lemma BLS_i : forall i, (i < NCUT)%nat -> nth i G.BLS [] = BLK i.
Proof. intros i Hi. unfold NCUT in Hi. dcut i. exfalso. lia. Qed.

Definition MIDB (i : nat) : bool := (negb (Nat.eqb i 0) && negb (Nat.eqb i I_EX) && Nat.ltb i NCUT)%bool.
Lemma MIDB_ne : forall i, MIDB i = true -> (Nat.eqb i 0 || Nat.eqb i I_EX)%bool = false.
Proof. intros i H. unfold MIDB in H. destruct (Nat.eqb i 0); [discriminate H|]. destruct (Nat.eqb i I_EX); [discriminate H | reflexivity]. Qed.
Lemma CPF_cases : forall i r, In r (CPF i) ->
  r = STKR \/ r = FSHR \/ r = (FE, 0, ELit 24) \/ r = (FE, 32, ELit 2008) \/ r = (FE, 432, ELit 16) \/ r = (FE, 464, ELit 8) \/ r = (FE, 1112, ELit 8) \/ r = (FE, 96, ELit 272) \/ r = TOPR.
Proof.
  intros i r. unfold CPF. repeat match goal with |- In r (if ?b then _ else _) -> _ => destruct b end; cbn [In]; intros H; decompose [or] H; clear H; subst; tauto.
Qed.

Definition CPFL : list SGP.region := [STKR; TOPR; FSHR].
Lemma CPFL_i : forall i, In i [1; 2; 3; 4; 5; 8; 9; 10; 11; 13; 14; 15; 16; 18; 19; 25; 27]%nat -> CPF i = CPFL.
Proof. intros i Hi. repeat (destruct Hi as [<-|Hi]; [reflexivity|]). destruct Hi. Qed.
End HNC.
