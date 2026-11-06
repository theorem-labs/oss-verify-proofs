(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgFA OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSL OSSVerify.Proofs.glaze.binary_reflection.lib.BgFMSH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgFMS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgFMST.

Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


  Definition DISPATCH : Z := 0xa11f0.

Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, 803%nat); (DISPATCH, 174%nat)].   (* [comment removed for export] *)
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 100 then Some BgFA.ce else if Nat.eqb id 101 then Some BgFMSL.ceI else if Nat.eqb id 102 then Some BgFMSL.ceD else None.
Definition XN : nat -> list expr -> acs -> option acs := XNp (XNw (XNc BSEGS IT ABOTH NXF GBOTH BCAP CCAP CT)).   (* [comment removed for export] *)
Definition CT2 (id : nat) : option gcallee2 := if Nat.eqb id 103 then Some (BgFMSH.ce2 MS) else if Nat.eqb id 113 then Some (BgFMSH.ce2 ML) else None.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc BSEGS ABOTH NXF GBOTH BCAP CCAP CT2.

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
Definition HEAD : Z := 0xa0958.
Definition SP1 : expr := eaddz e_sp (-256).        (* [comment removed for export] *)
Definition shof (x : expr) (k : Z) : expr := EAlu ALU_ADD (EAlu ALU_SRL x (ELit 3)) (ELit (SB + k)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TBLHK : Z := 0x22b80.
Definition loop_slots : list nat := [5; 10; 11; 12; 13; 14; 16; 17; 18; 19; 21; 23; 25; 27; 28]%nat.
Definition loop_regs (a5 : expr) (slot0 : nat) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regsT
    2 SP1) 8 e_sp) 9 SP1) 1 (ELit SB)) 6 c) 7 (ELit TBLHK)) 15 a5) 20 (shof q 0)) 22 (shof F 0)) 24 q) 26 (shof c 0)) 29 (eaddz F 32)) 30 (eaddz F 64)) 31 (eaddz F 96))
    loop_slots slot0.
Definition frame_kn : list kentry :=
  [KWord (SA e_sp (-256)) 8 (ELit 0); KWord (SA e_sp (-232)) 8 (ELit 3); KWord (SA e_sp (-224)) 8 (shof c 4); KWord (SA e_sp (-216)) 8 (eaddz c 32);
   KWord (SA e_sp (-208)) 8 F; KWord (SA e_sp (-200)) 8 F; KWord (SA e_sp (-192)) 8 (shof e_sp (-18)); KWord (SA e_sp (-184)) 8 (shof F 0);
   KWord (SA e_sp (-176)) 8 (ELit 0x22b90); KWord (SA e_sp (-168)) 8 v; KWord (SA e_sp (-160)) 8 F;
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
Definition J2PC : Z := 0xa0b2c.

Definition O2 : expr := EVar 200. Definition KL : expr := EVar 201.
Definition j2_regs (base : list expr) : list expr :=
  (* [comment removed for export] *)
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd base
    5 (EVar 202)) 10 (EVar 203)) 11 (EVar 204)) 12 KL) 13 (ELit 22)) 14 E) 15 (EVar 205)) 16 (EVar 206)) 17 (EVar 207)) 19 (cnt NV JJ).
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
    5 (EVar 242)) 10 (EVar 243)) 11 (EVar 244)) 12 KLc) 13 (ELit 22)) 14 E) 15 (EVar 245)) 16 (EVar 246)) 17 (EVar 247)) 19 cntC.
Definition j2_factsC : list kentry :=
  [KWord (SA q 0) 8 (eadd I O2c); KRange O2c 0 BUFMAX; KRange (esub (esub E I) O2c) 0 BUFMAX; KRange KLc 0 (2^62 - 1); KShOk (SA F 64) (ELit 8)].
Definition J2LC : acs :=
  mkcsL J2PC (j2_regsC (loop_regs cntC 167)) (j2_factsC ++ [KRange (EVar JC) 0 (2^62 - 1)] ++ skipn 3 inv_kn_LC) 248 [(DKc, escale 8 AKc)] MTRKc.



(* [comment removed for export] *)
Definition XPC : Z := 0xa0d28.
(* [comment removed for export] *)
Definition exit_slots : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition exit_regs (slot0 : nat) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd regsT 2 SP1) 8 e_sp) 9 SP1) 22 (shof F 0)) exit_slots slot0.
Definition XP : expr := EVar 300.  Definition XER : expr := EVar 301.  Definition XMTR : expr := EVar 302.
Definition XSV : expr := EVar 303.
Definition XD : expr := EVar 303. Definition XS_ : expr := EVar 304. Definition XA : expr := EVar 305.
Definition xcut_kn_S : list kentry :=
  [KWord (SA q 0) 8 XP; KWord (SA c 0) 4 XER; KWord (SA c 32) 4 (eaddz dep 1); KRange (esub E I) 1 BUFMAX; KWord (SA v 16) 1 (escale 2 XSV); KRange XSV 0 22] ++ mtrk XMTR ++ loop_common.
Definition xcut_kn_L : list kentry :=
  [KWord (SA q 0) 8 XP; KWord (SA c 0) 4 XER; KWord (SA c 32) 4 (eaddz dep 1); KRange (esub E I) 1 BUFMAX] ++ mtrk XMTR ++ strLF XD XS_ XA ++ loop_common.
Definition XCUT_S : acs := mkcsL XPC (exit_regs 306) xcut_kn_S 331 [] XMTR.
Definition XCUT_L : acs := mkcsL XPC (exit_regs 306) xcut_kn_L 331 [(XD, escale 8 XA)] XMTR.
Definition REL : Z := 0xa0da0.     (* [comment removed for export] *)
Definition plan_exit (h : nat) : plan := PRun [REL] (PExt 51 [] (PRun [] (PHandoff h))).
Definition CUTS : list (acs * plan) := [(XCUT_S, plan_exit 0); (XCUT_L, plan_exit 1)].














End BgFMS.
Module BgFMSPlan.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgFMST BgFMS.
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
Definition XPC2 : Z := 0xa0d34.
Definition XS : acs := mkcsL XPC2 (exit_regs 306) xcut_kn_S 331 [] XMTR.
Definition XL : acs := mkcsL XPC2 (exit_regs 306) xcut_kn_L 331 [(XD, escale 8 XA)] XMTR.
Definition plan_top : plan :=
  (PVia 1 J1 100 (PCase2 (esub E I) 0 (PRun [] (PExt 50 [ELit 1] (PExt 47 [] (PRun [0xa06a8] (PRun [0xa0da0] (PExt 51 [] (PRun [] (PExt 46 [I; ELit 0; esub E I] (PHandoff 0))))))))) (PRun [] (PExt 50 [ELit 1] (PExt 47 [] (PRun [0xa06a8] (PExt 46 [F; ELit 32; ELit 8] (PRun [0xa06dc] (PBranch (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 0 (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0xa075c] (PCaseReg 16 1 (PCaseReg 16 0 (PRespell 16 (ELit 0) (PRun [0xa0914] (PCaseReg 15 0 (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0xa0958] (PMergeW 1 [(101%nat, ELit 2)]))))) (PRespell 16 (ELit 1) (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 1 (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0xa0914] (PCaseReg 15 0 (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0xa0958] (PMergeW 1 [(101%nat, ELit 3)]))))))) (PCaseReg 16 2 (PRespell 16 (ELit 2) (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 3 (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0xa0914] (PCaseReg 15 0 (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0xa0958] (PMergeW 1 [(101%nat, ELit 5)])))))) (PRespell 16 (ELit 3) (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 7 (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0xa08f8] (PBranch (PRun [0xa0914] (PCaseReg 15 0 (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))) (PRun [0xa0958] (PMergeW 1 [(101%nat, ELit 9)])))) (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))))))))))) (PRun [0xa0da0] (PExt 51 [] (PRun [] (PHandoff 0)))))))))))) (PLoopM 118 NV [(INV_S, (PVia 2 (J2S false) 200 (PRun [0xa095c] (PExt 46 [F; ELit 64; ELit 8] (PCase2 (esub (esub E I) OJ) 0 (PRun [0xa0d34] (PHandoff 3)) (PRun [0xa0990] (PCaseReg 16 1 (PCaseReg 16 0 (PRespell 16 (ELit 0) (PRun [0xa0b2c] (PMergeW 2 [(200%nat, (eaddz OJ (1)))]))) (PRespell 16 (ELit 1) (PCase2 (esub (esub E I) OJ) 1 (PRun [0xa0d34] (PHandoff 3)) (PRun [0xa0b2c] (PMergeW 2 [(200%nat, (eaddz OJ (2)))]))))) (PCaseReg 16 2 (PRespell 16 (ELit 2) (PCase2 (esub (esub E I) OJ) 3 (PRun [0xa0d34] (PHandoff 3)) (PRun [0xa0b2c] (PMergeW 2 [(200%nat, (eaddz OJ (4)))])))) (PRespell 16 (ELit 3) (PCase2 (esub (esub E I) OJ) 7 (PRun [0xa0d34] (PHandoff 3)) (PRun [0xa0b24] (PBranch (PRun [0xa0b2c] (PMergeW 2 [(200%nat, (eaddz OJ (8)))])) (PRun [0xa0d34] (PHandoff 3)))))))))))) (PCase2 (esub (esub E I) O2) 0 (PRun [0xa0d34] (PHandoff 3)) (PCase2 KL 0 (PRun [0xa0b54] (PBranch (PRun [0xa0d34] (PHandoff 3)) (PRun [0xa0d34] (PHandoff 3)))) (PCase2 KL 5 (PRun [0xa0b54] (PBranch (PRun [0xa0b80] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0xa0b9c] (PExt 42 [] (PRun [0xa0d34] (PHandoff 3)))) (PRespell 11 (ELit 97) (PRun [0xa0bb0] (PExt 46 [F; ELit 96; ELit 16] (PRun [0xa0bd0] (PRun [0xa1260] (PBranch (PRun [0xa12d4] (PFact (KRange (esub (esub E I) (eaddz O2 2)) 1 BUFMAX) (PRun [0xa1300] (PBranch (PRun [0xa130c] (PBranch (PRun [] (PFactLe (eaddz O2 3) (esub E I) BUFMAX (PBump 260 (PExt 100 [ELit 0; I; eaddz O2 3; ERJ; e_mtr; eaddz e_fb (-1)] (PFact (KRange (esub E I) 1 BUFMAX) (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PNextW [(119%nat, (EVar 264))])) (PRun [0xa0d34] (PHandoff 3)))) (PRun [0xa0d34] (PHandoff 3))))))))) (PRun [0xa0d34] (PHandoff 3)))) (PRun [0xa0d34] (PHandoff 3)))))) (PRun [0xa0d34] (PHandoff 3))))))))) (PCaseReg 11 99 (PRun [0xa0b9c] (PExt 42 [] (PRun [0xa0d34] (PHandoff 3)))) (PRespell 11 (ELit 100) (PRun [0xa0bb0] (PExt 46 [F; ELit 96; ELit 16] (PRun [0xa0bd0] (PRun [0xa1aec] (PBump 260 (PExt 102 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KL; eadd I O2; ELit 0; E; e_mtr; eaddz e_fb (-1)] (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PFactLe (eadd (eadd O2 KL) (EVar 260)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2 KL) (EVar 260))) 0 BUFMAX) (PNextW [(119%nat, (eadd (eadd O2 KL) (EVar 260)))])))) (PRun [0xa0d34] (PHandoff 3)))) (PRun [0xa0d34] (PHandoff 3))))))))))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0xa0b9c] (PExt 42 [] (PRun [0xa0d34] (PHandoff 3)))) (PRespell 11 (ELit 104) (PRun [0xa0bb0] (PExt 46 [F; ELit 96; ELit 16] (PRun [0xa0bd0] (PRun [0xa214c] (PBump 260 (PExt2 103 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KL; I; O2; E; e_mtr; eaddz e_fb (-1); SVJ] (PExt 47 [] (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PFactLe (eadd (eadd O2 KL) (EVar 260)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2 KL) (EVar 260))) 0 BUFMAX) (PNextW [(119%nat, (eadd (eadd O2 KL) (EVar 260)))])))) (PRun [0xa0d34] (PHandoff 3)))) (PRun [0xa0d34] (PHandoff 3))))) (PExt 47 [] (PExt 13 [EVar 263] (ladS (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PFactLe (eadd (eadd O2 KL) (EVar 260)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2 KL) (EVar 260))) 0 BUFMAX) (PHandoffW 2 [(100%nat, NV); (118%nat, eaddz (EVar 118) 1); (119%nat, (eadd (eadd O2 KL) (EVar 260)))])))) (PRun [0xa0d34] (PHandoff 4)))) (PRun [0xa0d34] (PHandoff 4))))))))))))))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [0xa0bb0] (PExt 46 [F; ELit 96; ELit 16] (PRun [0xa0bd0] (PRun [0xa14a8] (PBump 260 (PExt 101 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KL; eadd I O2; ELit 0; E; e_mtr; eaddz e_fb (-1)] (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PFactLe (eadd (eadd O2 KL) (EVar 260)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2 KL) (EVar 260))) 0 BUFMAX) (PNextW [(119%nat, (eadd (eadd O2 KL) (EVar 260)))])))) (PRun [0xa0d34] (PHandoff 3)))) (PRun [0xa0d34] (PHandoff 3))))))))))) (PRun [0xa0b9c] (PExt 42 [] (PRun [0xa0d34] (PHandoff 3)))))))) (PRun [0xa0d34] (PHandoff 3)))) (PRun [0xa0b54] (PBranch (PRun [0xa0d34] (PHandoff 3)) (PRun [0xa0d34] (PHandoff 3)))))))), PContraH 0)] [])).

Definition plan_L : plan :=
  (PLoopM 160 NC [(INV_LC, (PVia 2 J2LC 240 (PRun [0xa095c] (PExt 46 [F; ELit 64; ELit 8] (PCase2 (esub (esub E I) OKc) 0 (PRun [0xa0d34] (PHandoff 4)) (PRun [0xa0990] (PCaseReg 16 1 (PCaseReg 16 0 (PRespell 16 (ELit 0) (PRun [0xa0b2c] (PMergeW 2 [(240%nat, (eaddz OKc (1)))]))) (PRespell 16 (ELit 1) (PCase2 (esub (esub E I) OKc) 1 (PRun [0xa0d34] (PHandoff 4)) (PRun [0xa0b2c] (PMergeW 2 [(240%nat, (eaddz OKc (2)))]))))) (PCaseReg 16 2 (PRespell 16 (ELit 2) (PCase2 (esub (esub E I) OKc) 3 (PRun [0xa0d34] (PHandoff 4)) (PRun [0xa0b2c] (PMergeW 2 [(240%nat, (eaddz OKc (4)))])))) (PRespell 16 (ELit 3) (PCase2 (esub (esub E I) OKc) 7 (PRun [0xa0d34] (PHandoff 4)) (PRun [0xa0b24] (PBranch (PRun [0xa0b2c] (PMergeW 2 [(240%nat, (eaddz OKc (8)))])) (PRun [0xa0d34] (PHandoff 4)))))))))))) (PCase2 (esub (esub E I) O2c) 0 (PRun [0xa0d34] (PHandoff 4)) (PCase2 KLc 0 (PRun [0xa0b54] (PBranch (PRun [0xa0d34] (PHandoff 4)) (PRun [0xa0d34] (PHandoff 4)))) (PCase2 KLc 5 (PRun [0xa0b54] (PBranch (PRun [0xa0b80] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0xa0b9c] (PExt 42 [] (PRun [0xa0d34] (PHandoff 4)))) (PRespell 11 (ELit 97) (PRun [0xa0bb0] (PExt 46 [F; ELit 96; ELit 16] (PRun [0xa0bd0] (PRun [0xa1260] (PBranch (PRun [0xa12d4] (PFact (KRange (esub (esub E I) (eaddz O2c 2)) 1 BUFMAX) (PRun [0xa1300] (PBranch (PRun [0xa130c] (PBranch (PRun [] (PFactLe (eaddz O2c 3) (esub E I) BUFMAX (PBump 300 (PExt 100 [ELit 0; I; eaddz O2c 3; ERKc; MTRKc; eaddz e_fb (-1)] (PFact (KRange (esub E I) 1 BUFMAX) (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PNextW [(161%nat, (EVar 304))])) (PRun [0xa0d34] (PHandoff 4)))) (PRun [0xa0d34] (PHandoff 4))))))))) (PRun [0xa0d34] (PHandoff 4)))) (PRun [0xa0d34] (PHandoff 4)))))) (PRun [0xa0d34] (PHandoff 4))))))))) (PCaseReg 11 99 (PRun [0xa0b9c] (PExt 42 [] (PRun [0xa0d34] (PHandoff 4)))) (PRespell 11 (ELit 100) (PRun [0xa0bb0] (PExt 46 [F; ELit 96; ELit 16] (PRun [0xa0bd0] (PRun [0xa1aec] (PBump 300 (PExt 102 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KLc; eadd I O2c; ELit 0; E; MTRKc; eaddz e_fb (-1)] (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PFactLe (eadd (eadd O2c KLc) (EVar 300)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2c KLc) (EVar 300))) 0 BUFMAX) (PNextW [(161%nat, (eadd (eadd O2c KLc) (EVar 300)))])))) (PRun [0xa0d34] (PHandoff 4)))) (PRun [0xa0d34] (PHandoff 4))))))))))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0xa0b9c] (PExt 42 [] (PRun [0xa0d34] (PHandoff 4)))) (PRespell 11 (ELit 104) (PRun [0xa0bb0] (PExt 46 [F; ELit 96; ELit 16] (PRun [0xa0bd0] (PRun [0xa214c] (PBump 300 (PExt2 113 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KLc; I; O2c; E; MTRKc; eaddz e_fb (-1); DKc; SKc; AKc] (PExt 47 [] (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PFactLe (eadd (eadd O2c KLc) (EVar 300)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2c KLc) (EVar 300))) 0 BUFMAX) (PNextW [(161%nat, (eadd (eadd O2c KLc) (EVar 300)))])))) (PRun [0xa0d34] (PHandoff 4)))) (PRun [0xa0d34] (PHandoff 4))))) (PExt 47 [] (PExt 13 [EVar 303] (ladL (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PFactLe (eadd (eadd O2c KLc) (EVar 300)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2c KLc) (EVar 300))) 0 BUFMAX) (PNextW [(161%nat, (eadd (eadd O2c KLc) (EVar 300)))])))) (PRun [0xa0d34] (PHandoff 4)))) (PRun [0xa0d34] (PHandoff 4))))))))))))))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [0xa0bb0] (PExt 46 [F; ELit 96; ELit 16] (PRun [0xa0bd0] (PRun [0xa14a8] (PBump 300 (PExt 101 [ELit 0; eaddz F 64; eaddz F 96; v; c; q; eaddz F 32; KLc; eadd I O2c; ELit 0; E; MTRKc; eaddz e_fb (-1)] (PRun [0xa0c58] (PBranch (PRun [0xa0c74] (PBranch (PRun [0xa0958] (PFactLe (eadd (eadd O2c KLc) (EVar 300)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eadd O2c KLc) (EVar 300))) 0 BUFMAX) (PNextW [(161%nat, (eadd (eadd O2c KLc) (EVar 300)))])))) (PRun [0xa0d34] (PHandoff 4)))) (PRun [0xa0d34] (PHandoff 4))))))))))) (PRun [0xa0b9c] (PExt 42 [] (PRun [0xa0d34] (PHandoff 4)))))))) (PRun [0xa0d34] (PHandoff 4)))) (PRun [0xa0b54] (PBranch (PRun [0xa0d34] (PHandoff 4)) (PRun [0xa0d34] (PHandoff 4)))))))), PContraH 1)] []).

Definition CUTS : list (acs * plan) := [(TL, plan_L); (XS, plan_exit 0); (XL, plan_exit 1)].   (* [comment removed for export] *)
Lemma gplan_top : gplan_ok plan_top = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_L : gplan_ok plan_L = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_X0 : gplan_ok (plan_exit 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_X1 : gplan_ok (plan_exit 1) = true. Proof. vm_compute. reflexivity. Qed.
End BgFMSPlan.
Module BgFMSCertTop.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgFMST BgFMS BgFMSPlan.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma top : check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS 0) 0%nat BFUEL FUEL None (ce_tin ce) plan_top = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
End BgFMSCertTop.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgFMST BgFMS BgFMSPlan.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma cutL : check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS 1) 0%nat BFUEL FUEL None TL plan_L = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cutXS : check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS 2) 0%nat BFUEL FUEL None XS (plan_exit 0) = COk (SHole 0).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cutXL : check BSEGS IT ABOTH (ce_nxf ce) LIMIT ISP0 XN XE0 XB (HScut ce CUTS 3) 0%nat BFUEL FUEL None XL (plan_exit 1) = COk (SHole 1).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
