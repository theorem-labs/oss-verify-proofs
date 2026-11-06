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
From OSSVerify.Proofs.glaze.binary_reflection.lib Require GaNumT GaEsc.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GaB2JT GaB2JTpl.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ext_split (k : Z) : list dstep := if Z.eqb k 0 then [DRLo 11 0] else [DRHi 11 (k - 1); DRLo 11 k].
Definition S6 (k : Z) (m : smode) : acs := snd (DPATH m (nxt (ATs 6 m)) (ATs 6 m) (DRun [0xa419c] :: ext_split k) 0).
(* [comment removed for export] *)
Definition JS_nl_c := Eval vm_compute in tri (fun w m =>
  JSE pos w m (site_states m (S6 0 m) [] 0xa5e00 0xa5e08 0xa88bc) 0xa5e08 (ELit 0) (eaddz ITO 1) IX (eaddz IX 1) 0 24 (- CG + GEV) [] 62).
Definition JS_nl := sel3 JS_nl_c.

(* [comment removed for export] *)
Definition C6X1 : nat := 31.
Definition CB64 : expr := EExt false 0 1 (EVar 64).
Definition NTAG : expr := escale 32 (EAlu ALU_SRL CB64 (ELit 5)).        (* [comment removed for export] *)
Definition ITO2e : expr := eaddz ITO 2.
Definition kn_x : list kentry := [KWord (SA e_sp (-176)) 4 NTAG].
Definition pre6x : list dstep := [DRun [0xa43e0]; DBrT; DRun [0xa441c]; DBrT].
Definition Vx1 : nat := 66.
Definition JS_x1_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (S6 3 m) pre6x 0xa6a2c 0xa6a34 0xa89b0) 0xa6a34 (ELit 0) ITO2e IX (eaddz IX 1) 0 48 (- 2 * CG + GEV) kn_x Vx1).
Definition JS_x1 := sel3 JS_x1_c.
(* [comment removed for export] *)
Definition BX1 : nat := 110.
Definition ITOX1 : expr := eadd ITO2e (EVar 111).  Definition xX1 : expr := EVar 112.
Definition Vx3 : nat := 140.
Definition x_facts1 : list kentry := kn_x ++ [KRange (EVar 111) 0 8; KRange ITOX1 0 INSZ].
Definition STx_n1 (m : smode) : acs := fake_ret 0xa6ae4 (snd (DPATH m NXF (JS_x1 m m) [DRun [GaNumT.BNI]] 0)).
Definition JS_x3_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (STx_n1 m) [] 0xa7100 0xa7108 0xa8a00) 0xa7108 (ELit 0) ITOX1 xX1 (eaddz xX1 1) 0 55 (- 2 * CG + 3 * GEV) x_facts1 Vx3).
Definition JS_x3 := sel3 JS_x3_c.
(* [comment removed for export] *)
Definition BX2 : nat := 180.
Definition ITOX2 : expr := eadd ITOX1 (EVar 181).  Definition xX2 : expr := EVar 182.
Definition Vx5 : nat := 210.
Definition STx_n2 (m : smode) : acs := fake_ret 0xa71a8 (snd (DPATH m NXF (JS_x3 m m) [DRun [GaNumT.BNI]] 0)).
Definition JS_x5_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (STx_n2 m) [] 0xa7278 0xa7280 0xa8a1c) 0xa7280 (ELit 0) ITOX2 xX2 (eaddz xX2 1) 0 61 (- 2 * CG + 5 * GEV)
       (x_facts1 ++ [KRange (EVar 181) 0 8; KRange ITOX2 0 INSZ]) Vx5).
Definition JS_x5 := sel3 JS_x5_c.

(* [comment removed for export] *)
Definition CCLOOP : nat := 3.  Definition CCB1L : nat := 8.  Definition CCN1L : nat := 9.  Definition CCB3L : nat := 18.  Definition CCN2L : nat := 19.
Definition CCB5L : nat := 32.  Definition CCLOOPL : nat := 33.  Definition CCCLOSE : nat := 36.
Definition HLc : expr := EVar 100.  Definition NCc : expr := EVar 101.
Definition Vc0 : nat := 102.
Definition ITOHc : expr := eadd ITO2e HLc.
Definition pre6c : list dstep := [DRun [0xa43e0]; DBrT; DRun [0xa441c]; DBrF; DRun [0xa5e9c]; DBrT].
Definition ST_ca0 (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (S6 3 m) (hdr_pathG pre6c 16 cfg 0xa5ee0 0xa5ee8 true 0xa76a0 true 0xa76ac) 0)) [0; 1; 2; 3].
Definition ca_facts (nlo : Z) : list kentry := kn_x ++ [KRange HLc 1 8; KRange ITO 0 (INSZ - 3); KRange NCc nlo (2 ^ 48)].
Definition JS_ca0_c := Eval vm_compute in tri (fun w m =>
  JSGk 65 pos w m (ST_ca0 m) 0xa76ac [(27%nat, NCc)] (ELit 0) ITOHc IX 0 72 (- 2 * CG) (ca_facts 0) Vc0).
Definition JS_ca0 := sel3 JS_ca0_c.
Definition Vc1 : nat := 140.
Definition JS_ca1_c := Eval vm_compute in tri (fun w m =>
  JSEk 102 pos w m (site_states m (JS_ca0 m m) [] 0xa7734 0xa773c 0xa8a34) 0xa773c (ELit 0) ITOHc IX (eaddz IX 1) 0 72 C5 (ca_facts 0) Vc1).
Definition JS_ca1 := sel3 JS_ca1_c.
(* [comment removed for export] *)
Definition RCc : expr := EVar 62.  Definition ITOLc : expr := EVar 63.  Definition IXLc : expr := EVar 65.
Definition Vct : nat := 66.
Definition STc_first (m : smode) : acs := snd (DPATH m NXF (JS_ca1 m m) [DRun [0xa77c0]; DBrF; DRun [0xa77dc]] 0).
Definition STc_n1 (m : smode) (s0 : acs) : acs := fake_ret 0xa78bc (snd (DPATH m NXF s0 [DRun [0xa7824]; DBrF; DRun [GaNumT.BNI]] 0)).
Definition STc_n2 (m : smode) (s0 : acs) : acs := fake_ret 0xa79b4 (snd (DPATH m NXF (STc_n1 m s0) [DRun [0xa7920]; DBrF; DRun [GaNumT.BNI]] 0)).
Definition STc_second (m : smode) : acs :=
  snd (DPATH m NXF (STc_n2 m (STc_first m)) [DRun [0xa7a1c]; DBrF; DRun [0xa7a98]; DBrF; DRun [0xa7ae4]; DBrF; DRun [0xa77dc]] 0).
Definition cloop_facts (w m : smode) (cnt ito ix : expr) (v : nat) : list kentry := kn_x ++ loop_facts w m cnt ito ix v.
Definition Tca_c := Eval vm_compute in tri (fun w m =>
  JT [STc_first m; STc_second m] 0xa77dc [(27%nat, RCc)] KEEP (4 + Vct) (cloop_facts w m RCc ITOLc IXLc Vct) (vis m Vct) (EVar (3 + Vct))).
Definition Tca := sel3 Tca_c.
Definition OVC : list (nat * expr) := [(27%nat, esub RCc J5)].
Definition INVca_c := Eval vm_compute in tri (fun w m =>
  JT [STc_first m; STc_second m] 0xa77dc OVC KEEP (4 + V5i)
     (KRange RCc 1 (2 ^ 48) :: cloop_facts w m (esub RCc J5) ITOJ IXJ V5i) (vis m V5i) (EVar (3 + V5i))).
Definition INVca := sel3 INVca_c.
Definition cfacts : list kentry := kn_x ++ [KRange ITO 0 (INSZ - 2); KRange RCc 1 (2 ^ 48); KRange (esub RCc J5) 1 (2 ^ 48); KRange J5 0 (2 ^ 48)].
(* [comment removed for export] *)
Definition JS_cb1_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (INVca m m) [] 0xa7824 0xa7828 0xa7b80) 0xa7828 OVC (ELit 0) ITOJ IXJ 0 47 (C5 + GEV)
       (room m (eaddz IXJ 1) Vq1 ++ cfacts ++ [KRange ITOJ 0 INSZ]) Vq1).
Definition JS_cb1 := sel3 JS_cb1_c.
(* [comment removed for export] *)
Definition cn_facts : list kentry := cfacts ++ [KRange ITOJ 0 INSZ; KRange xDn 1 8; KRange ITON 0 INSZ; KRange xXn 0 BIG].
Definition STc_n1J (m : smode) : acs := fake_ret 0xa78bc (snd (DPATH m NXF (JS_cb1 m m) [DRun [GaNumT.BNI]] 0)).
Definition JS_cn1_c := Eval vm_compute in tri (fun w m =>
  JT [snd (DPATH m NXF (STc_n1J m) [DRun [0xa78d8]] 0)] 0xa78d8 OVC 107 (4 + (3 + BNK))
     ([KRange DEPTH 0 255; stk_shok; rel ITON xXn 54] ++ cn_facts ++ mfacts w m (3 + BNK) ITON (EVar (6 + BNK)) (C5 - 2 * GEV)
      ++ pos ITON xXn (ELit 0) 0 BIG ++ str m xXn ITON (ELit 0) (3 + BNK) ++ blkF m (3 + BNK) ++ F_facts ++ kn_fixed)
     (vis m (3 + BNK)) (EVar (6 + BNK))).
Definition JS_cn1 := sel3 JS_cn1_c.
(* [comment removed for export] *)
Definition JS_cb3_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (JS_cn1 m m) [] 0xa7920 0xa7924 0xa7ba4) 0xa7924 OVC (ELit 0) ITON xXn 0 54 (C5 - GEV)
       (room m (eaddz xXn 1) Vq2 ++ cn_facts) Vq2).
Definition JS_cb3 := sel3 JS_cb3_c.
(* [comment removed for export] *)
Definition BN2 : nat := 260.
  Definition xD2 : expr := EVar 261.  Definition xX2c : expr := EVar 262.
Definition ITON2 : expr := eadd ITON xD2.
Definition cn2_facts : list kentry := cn_facts ++ [KRange xD2 1 8; KRange ITON2 0 INSZ; KRange xX2c 0 BIG].
Definition STc_n2J (m : smode) : acs := fake_ret 0xa79b4 (snd (DPATH m NXF (JS_cb3 m m) [DRun [GaNumT.BNI]] 0)).
Definition JS_cn2_c := Eval vm_compute in tri (fun w m =>
  JT [snd (DPATH m NXF (STc_n2J m) [DRun [0xa79cc]] 0)] 0xa79cc OVC 107 (4 + (3 + BN2))
     ([KRange DEPTH 0 255; stk_shok; rel ITON2 xX2c 60] ++ cn2_facts ++ mfacts w m (3 + BN2) ITON2 (EVar (6 + BN2)) (C5 - 4 * GEV)
      ++ pos ITON2 xX2c (ELit 0) 0 BIG ++ str m xX2c ITON2 (ELit 0) (3 + BN2) ++ blkF m (3 + BN2) ++ F_facts ++ kn_fixed)
     (vis m (3 + BN2)) (EVar (6 + BN2))).
Definition JS_cn2 := sel3 JS_cn2_c.
(* [comment removed for export] *)
Definition Vc5 : nat := 290.
Definition JS_cb5_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (JS_cn2 m m) [] 0xa7a1c 0xa7a20 0xa7bc8) 0xa7a20 OVC (ELit 0) ITON2 xX2c 0 60 (C5 - 3 * GEV)
       (room m (eaddz xX2c 1) Vc5 ++ cn2_facts) Vc5).
Definition JS_cb5 := sel3 JS_cb5_c.
(* [comment removed for export] *)
Definition Vc6 : nat := 330.
Definition JS_cb6_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (JS_cb5 m m) [DRun [0xa7a98]; DBrF] 0xa7ae4 0xa7ae8 0xa7bf4) 0xa7ae8 OVC (ELit 0) ITON2 (eaddz xX2c 1) 0 59 C5
       (room m (eaddz xX2c 2) Vc6 ++ cn2_facts ++ [KRange (esub RCc J5) 2 (2 ^ 48)]) Vc6).
Definition JS_cb6 := sel3 JS_cb6_c.
(* [comment removed for export] *)
Definition STc_close (m : smode) : list acs :=
  [snd (DPATH m NXF (JS_ca1 m m) [DRun [0xa77c0]; DBrT; DRun [0xa7cb0]] 0); snd (DPATH m NXF (JS_cb5 m m) [DRun [0xa7a98]; DBrT; DRun [0xa7cb0]] 0)].
Definition TCc_c := Eval vm_compute in tri (fun w m =>
  JT (STc_close m) 0xa7cb0 [] KEEP (4 + V5x)
     ([KRange DEPTH 0 255; stk_shok; KRange ITO 0 (INSZ - 2); KRange ITOC 0 INSZ; rel ITOC IXC 2]
      ++ mfacts w m V5x ITOC (EVar (3 + V5x)) C5 ++ pos ITOC IXC (ELit 0) 0 BIG ++ str m IXC ITOC (ELit 0) V5x ++ blkF m V5x ++ F_facts ++ kn_fixed)
     (vis m V5x) (EVar (3 + V5x))).
Definition TCc := sel3 TCc_c.
Definition JS_rbc_c := Eval vm_compute in tri (fun w m =>
  JSEk K5 pos w m (site_statesP true m (TCc m m) [] 0xa7cfc 0xa7d00 0xa8a54) 0xa7d00 (ELit 0) ITOC IXC (eaddz IXC 1) 0 2 (C5 + GEV)
       [KRange ITO 0 (INSZ - 2); KRange ITOC 0 INSZ] V5r).
Definition JS_rbc := sel3 JS_rbc_c.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CM1 : nat := 40.  Definition CM2 : nat := 41.  Definition CM3L : nat := 42.  Definition CM3R : nat := 43.
Definition CM4 : nat := 44.  Definition CM5 : nat := 45.  Definition CM6 : nat := 46.  Definition CM7 : nat := 47.

Definition G8 (k : Z) : Z := - 2 * CG + k * GEV.
Definition pre6m : list dstep := [DRun [0xa5158]; DBrT].
Definition Vm1 : nat := 66.
Definition JS_m1_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (S6 2 m) pre6m 0xa5f40 0xa5f48 0xa88f4) 0xa5f48 (ELit 0) ITO2e IX (eaddz IX 1) 0 48 (G8 1) [] Vm1).
Definition JS_m1 := sel3 JS_m1_c.
Definition Vm2 : nat := 104.
Definition JS_m2_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (JS_m1 m m) [] 0xa6034 0xa603c 0xa8910) 0xa603c (ELit 0) ITO2e (eaddz IX 1) (eaddz IX 10) 0 47 (G8 2) [] Vm2).
Definition JS_m2 := sel3 JS_m2_c.

(* [comment removed for export] *)
Definition triL (f : smode -> smode -> acs) : acs * acs := (tin MS, f ML ML).
Definition Vm3 : nat := 144.
Definition stub_state (S0 : acs) (path : list dstep) (bpc back stubret : Z) : list acs :=      (* [comment removed for export] *)
  let s1 := snd (DPATH ML NXF S0 (path ++ [DRun [bpc]; DBrT; DRun [back]]) 0) in
  let b0 := snd (DPATH ML NXF S0 (path ++ [DRun [bpc]; DBrF; DRun []]) 0) in
  [s1; snd (DPATH ML NXF (fake_ret stubret b0) [DRun [back]] 0)].
Definition pre_m3 (right : bool) : list dstep := [DRun [0x6c76c]; DExt 5 []; DRun [0xa60d0]; if right then DBrT else DBrF].
Definition JS_m3l_c := Eval vm_compute in triL (fun w m =>
  JSEk 65 pos w m (stub_state (JS_m2 ML ML) (pre_m3 false) 0xa6b60 0xa6b68 0xa89d0) 0xa6b68 (ELit 0) ITO2e (eaddz IX 10) (eaddz IX 23) 0 38 (G8 3) [] Vm3).
Definition JS_m3l := sel3 JS_m3l_c.
Definition JS_m3r_c := Eval vm_compute in triL (fun w m =>
  JSEk 65 pos w m (stub_state (JS_m2 ML ML) (pre_m3 true) 0xa6bc0 0xa6bc8 0xa89e8) 0xa6bc8 (ELit 0) ITO2e (eaddz IX 10) (eaddz IX 24) 0 38 (G8 3) [] Vm3).
Definition JS_m3r := sel3 JS_m3r_c.
(* [comment removed for export] *)
Definition IXm : expr := EVar 184.
Definition Vm4 : nat := 185.
Definition mfx : list kentry :=      (* [comment removed for export] *)
  [KRange ITO 0 (INSZ - 2); KRange IXm 0 BIG; KRange (esub IXm IX) 23 24; KRange (esub (escale 24 ITO2e) IXm) 24 (BIG + 48)].     (* [comment removed for export] *)
Definition pre_m4 : list dstep := [DRun [0x6c76c]; DExt 5 []].
Definition JS_m4_c := Eval vm_compute in triL (fun w m =>
  JSEk 65 pos w m (stub_state (JS_m3l ML ML) pre_m4 0xa6cc8 0xa6cd0 0xa8928 ++ stub_state (JS_m3r ML ML) pre_m4 0xa6cc8 0xa6cd0 0xa8928)
       0xa6cd0 (ELit 0) ITO2e IXm (eaddz IXm 1) 0 24 (G8 4) mfx Vm4).
Definition JS_m4 := sel3 JS_m4_c.
Definition Vm5 : nat := 226.
Definition JS_m5_c := Eval vm_compute in triL (fun w m =>
  JSEk 185 pos w m (stub_state (JS_m4 ML ML) [] 0xa6d94 0xa6d9c 0xa8940) 0xa6d9c (ELit 0) ITO2e (eaddz IXm 1) (eaddz IXm 11) 0 23 (G8 5) mfx Vm5).
Definition JS_m5 := sel3 JS_m5_c.
(* [comment removed for export] *)
Definition BM1 : nat := 270.
Definition xIm1 : expr := EVar 271.  Definition xXm1 : expr := EVar 272.
Definition Vm6 : nat := 296.
Definition m6facts : list kentry := mfx ++ [KRange xIm1 0 INSZ; KRange (esub xIm1 ITO) 2 INSZ; KRange xXm1 0 BIG].     (* [comment removed for export] *)
Definition STm_s1 : acs := fake_ret 0xa6e40 (snd (DPATH ML NXF (JS_m5 ML ML) [DRun [0x6c76c]; DExt 5 []; DRun [ENTRY]] 0)).
Definition JS_m6_c := Eval vm_compute in triL (fun w m =>
  JSEk 273 pos w m (stub_state STm_s1 [] 0xa6ebc 0xa6ec4 0xa8978) 0xa6ec4 (ELit 0) xIm1 xXm1 (eaddz xXm1 1) 0 14 (G8 5) m6facts Vm6).
Definition JS_m6 := sel3 JS_m6_c.
Definition Vm7 : nat := 336.
Definition JS_m7_c := Eval vm_compute in triL (fun w m =>
  JSEk 273 pos w m (stub_state (JS_m6 ML ML) [] 0xa6f88 0xa6f90 0xa8994) 0xa6f90 (ELit 0) xIm1 (eaddz xXm1 1) (eaddz xXm1 9) 0 13 (G8 6) m6facts Vm7).
Definition JS_m7 := sel3 JS_m7_c.
(* [comment removed for export] *)
Definition BM2 : nat := 380.
Definition xIm2 : expr := EVar 381.  Definition xXm2 : expr := EVar 382.
Definition Vm8 : nat := 412.
Definition STm_s2 : acs := fake_ret 0xa7078 (snd (DPATH ML NXF (JS_m7 ML ML) [DRun [ENTRY]] 0)).
Definition JS_m8_c := Eval vm_compute in triL (fun w m =>
  JSEk 383 pos w m (stub_state STm_s2 [] 0xa7388 0xa7390 0xa8a6c) 0xa7390 (ELit 0) xIm2 xXm2 (eaddz xXm2 1) 0 6 (G8 6) [KRange xIm2 0 INSZ] Vm8).
Definition JS_m8 := sel3 JS_m8_c.
