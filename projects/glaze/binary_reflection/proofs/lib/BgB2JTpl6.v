(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgB2JT.BgDedup OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallRec.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum OSSVerify.Proofs.glaze.binary_reflection.lib.BgEsc.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export BgB2JT BgB2JTpl.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ext_split (k : Z) : list dstep := if Z.eqb k 0 then [DRLo 11 0] else [DRHi 11 (k - 1); DRLo 11 k].
Definition S6 (k : Z) (m : smode) : acs := snd (DPATH m (nxt (ATs 6 m)) (ATs 6 m) (DRun [0xa82cc] :: ext_split k) 0).
(* [comment removed for export] *)
Definition JS_nl_c := Eval vm_compute in tri (fun w m =>
  JSE pos w m (site_states m (S6 0 m) [] 0xaa248 0xaa250 0xaccd4) 0xaa250 (ELit 0) (eaddz ITO 1) IX (eaddz IX 1) 0 24 (- CG + GEV) [] 62).
Definition JS_nl := sel3 JS_nl_c.

(* [comment removed for export] *)
Definition C6X1 : nat := 31.
Definition CB64 : expr := EExt false 0 1 (EVar 64).
Definition NTAG : expr := escale 32 (EAlu ALU_SRL CB64 (ELit 5)).        (* [comment removed for export] *)
Definition ITO2e : expr := eaddz ITO 2.
Definition kn_x : list kentry := [KWord (SA e_sp (-176)) 4 NTAG].
Definition pre6x : list dstep := [DRun [0xa84d4]; DBrT; DRun [0xa8528]; DBrT].
Definition Vx1 : nat := 66.
Definition JS_x1_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (S6 3 m) pre6x 0xaaf78 0xaaf80 0xacdbc) 0xaaf80 (ELit 0) ITO2e IX (eaddz IX 1) 0 48 (- 2 * CG + GEV) kn_x Vx1).
Definition JS_x1 := sel3 JS_x1_c.
(* [comment removed for export] *)
Definition BX1 : nat := 110.
Definition ITOX1 : expr := eadd ITO2e (EVar 111).  Definition xX1 : expr := EVar 112.
Definition Vx3 : nat := 140.
Definition x_facts1 : list kentry := kn_x ++ [KRange (EVar 111) 0 8; KRange ITOX1 0 INSZ].
Definition STx_n1 (m : smode) : acs := fake_ret 0xaafe8 (snd (DPATH m NXF (JS_x1 m m) [DRun [BgNum.BgNumT.BNI]] 0)).
Definition JS_x3_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (STx_n1 m) [] 0xab510 0xab518 0xace04) 0xab518 (ELit 0) ITOX1 xX1 (eaddz xX1 1) 0 55 (- 2 * CG + 3 * GEV) x_facts1 Vx3).
Definition JS_x3 := sel3 JS_x3_c.
(* [comment removed for export] *)
Definition BX2 : nat := 180.
Definition ITOX2 : expr := eadd ITOX1 (EVar 181).  Definition xX2 : expr := EVar 182.
Definition Vx5 : nat := 210.
Definition STx_n2 (m : smode) : acs := fake_ret 0xab584 (snd (DPATH m NXF (JS_x3 m m) [DRun [BgNum.BgNumT.BNI]] 0)).
Definition JS_x5_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (STx_n2 m) [] 0xab5ec 0xab5f4 0xace1c) 0xab5f4 (ELit 0) ITOX2 xX2 (eaddz xX2 1) 0 61 (- 2 * CG + 5 * GEV)
       (x_facts1 ++ [KRange (EVar 181) 0 8; KRange ITOX2 0 INSZ]) Vx5).
Definition JS_x5 := sel3 JS_x5_c.

(* [comment removed for export] *)
Definition CCLOOP : nat := 3.  Definition CCB1L : nat := 8.  Definition CCN1L : nat := 9.  Definition CCB3L : nat := 18.  Definition CCN2L : nat := 19.
Definition CCB5L : nat := 32.  Definition CCLOOPL : nat := 33.  Definition CCCLOSE : nat := 36.
Definition HLc : expr := EVar 100.  Definition NCc : expr := EVar 101.
Definition Vc0 : nat := 102.
Definition ITOHc : expr := eadd ITO2e HLc.
Definition pre6c : list dstep := [DRun [0xa84d4]; DBrT; DRun [0xa8528]; DBrF; DRun [0xaa308]; DBrT].
Definition ST_ca0 (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (S6 3 m) (hdr_pathG pre6c 16 cfg 0xaa358 0xaa360 true 0xaba50 true 0xaba5c) 0)) [0; 1; 2; 3].
Definition ca_facts (nlo : Z) : list kentry := kn_x ++ [KRange HLc 1 8; KRange ITO 0 (INSZ - 3); KRange NCc nlo (2 ^ 48)].
Definition JS_ca0_c := Eval vm_compute in tri (fun w m =>
  JSGk 65 pos w m (ST_ca0 m) 0xaba5c [(26%nat, NCc)] (ELit 0) ITOHc IX 0 72 (- 2 * CG) (ca_facts 0) Vc0).
Definition JS_ca0 := sel3 JS_ca0_c.
Definition Vc1 : nat := 140.
Definition JS_ca1_c := Eval vm_compute in tri (fun w m =>
  JSEk 102 pos w m (site_states m (JS_ca0 m m) [] 0xabad8 0xabae0 0xace34) 0xabae0 (ELit 0) ITOHc IX (eaddz IX 1) 0 72 C5 (ca_facts 0) Vc1).
Definition JS_ca1 := sel3 JS_ca1_c.
(* [comment removed for export] *)
Definition RCc : expr := EVar 62.  Definition ITOLc : expr := EVar 63.  Definition IXLc : expr := EVar 65.
Definition Vct : nat := 66.
Definition STc_first (m : smode) : acs := snd (DPATH m NXF (JS_ca1 m m) [DRun [0xabb34]; DBrF; DRun [0xabb54]] 0).
Definition STc_n1 (m : smode) (s0 : acs) : acs := fake_ret 0xabc54 (snd (DPATH m NXF s0 [DRun [0xabb9c]; DBrF; DRun [BgNum.BgNumT.BNI]] 0)).
Definition STc_n2 (m : smode) (s0 : acs) : acs := fake_ret 0xabd64 (snd (DPATH m NXF (STc_n1 m s0) [DRun [0xabcb8]; DBrF; DRun [BgNum.BgNumT.BNI]] 0)).
Definition STc_second (m : smode) : acs :=
  snd (DPATH m NXF (STc_n2 m (STc_first m)) [DRun [0xabdc8]; DBrF; DRun [0xabe5c]; DBrF; DRun [0xabea8]; DBrF; DRun [0xabb54]] 0).
Definition cloop_facts (w m : smode) (cnt ito ix : expr) (v : nat) : list kentry := kn_x ++ loop_facts w m cnt ito ix v.
Definition Tca_c := Eval vm_compute in tri (fun w m =>
  JT [STc_first m; STc_second m] 0xabb54 [(26%nat, RCc)] KEEP (4 + Vct) (cloop_facts w m RCc ITOLc IXLc Vct) (vis m Vct) (EVar (3 + Vct))).
Definition Tca := sel3 Tca_c.
Definition OVC : list (nat * expr) := [(26%nat, esub RCc J5)].
Definition INVca_c := Eval vm_compute in tri (fun w m =>
  JT [STc_first m; STc_second m] 0xabb54 OVC KEEP (4 + V5i)
     (KRange RCc 1 (2 ^ 48) :: cloop_facts w m (esub RCc J5) ITOJ IXJ V5i) (vis m V5i) (EVar (3 + V5i))).
Definition INVca := sel3 INVca_c.
Definition cfacts : list kentry := kn_x ++ [KRange ITO 0 (INSZ - 2); KRange RCc 1 (2 ^ 48); KRange (esub RCc J5) 1 (2 ^ 48); KRange J5 0 (2 ^ 48)].
(* [comment removed for export] *)
Definition JS_cb1_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (INVca m m) [] 0xabb9c 0xabba0 0xabf54) 0xabba0 OVC (ELit 0) ITOJ IXJ 0 47 (C5 + GEV)
       (room m (eaddz IXJ 1) Vq1 ++ cfacts ++ [KRange ITOJ 0 INSZ]) Vq1).
Definition JS_cb1 := sel3 JS_cb1_c.
(* [comment removed for export] *)
Definition cn_facts : list kentry := cfacts ++ [KRange ITOJ 0 INSZ; KRange xDn 1 8; KRange ITON 0 INSZ; KRange xXn 0 BIG].
Definition STc_n1J (m : smode) : acs := fake_ret 0xabc54 (snd (DPATH m NXF (JS_cb1 m m) [DRun [BgNum.BgNumT.BNI]] 0)).
Definition JS_cn1_c := Eval vm_compute in tri (fun w m =>
  JT [snd (DPATH m NXF (STc_n1J m) [DRun [0xabc70]] 0)] 0xabc70 OVC 107 (4 + (3 + BNK))
     ([KRange DEPTH 0 255; stk_shok; rel ITON xXn 54] ++ cn_facts ++ mfacts w m (3 + BNK) ITON (EVar (6 + BNK)) (C5 - 2 * GEV)
      ++ pos ITON xXn (ELit 0) 0 BIG ++ str m xXn ITON (ELit 0) (3 + BNK) ++ blkF m (3 + BNK) ++ F_facts ++ kn_fixed)
     (vis m (3 + BNK)) (EVar (6 + BNK))).
Definition JS_cn1 := sel3 JS_cn1_c.
(* [comment removed for export] *)
Definition JS_cb3_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (JS_cn1 m m) [] 0xabcb8 0xabcbc 0xabf70) 0xabcbc OVC (ELit 0) ITON xXn 0 54 (C5 - GEV)
       (room m (eaddz xXn 1) Vq2 ++ cn_facts) Vq2).
Definition JS_cb3 := sel3 JS_cb3_c.
(* [comment removed for export] *)
Definition BN2 : nat := 260.
  Definition xD2 : expr := EVar 261.  Definition xX2c : expr := EVar 262.
Definition ITON2 : expr := eadd ITON xD2.
Definition cn2_facts : list kentry := cn_facts ++ [KRange xD2 1 8; KRange ITON2 0 INSZ; KRange xX2c 0 BIG].
Definition STc_n2J (m : smode) : acs := fake_ret 0xabd64 (snd (DPATH m NXF (JS_cb3 m m) [DRun [BgNum.BgNumT.BNI]] 0)).
Definition JS_cn2_c := Eval vm_compute in tri (fun w m =>
  JT [snd (DPATH m NXF (STc_n2J m) [DRun [0xabd80]] 0)] 0xabd80 OVC 107 (4 + (3 + BN2))
     ([KRange DEPTH 0 255; stk_shok; rel ITON2 xX2c 60] ++ cn2_facts ++ mfacts w m (3 + BN2) ITON2 (EVar (6 + BN2)) (C5 - 4 * GEV)
      ++ pos ITON2 xX2c (ELit 0) 0 BIG ++ str m xX2c ITON2 (ELit 0) (3 + BN2) ++ blkF m (3 + BN2) ++ F_facts ++ kn_fixed)
     (vis m (3 + BN2)) (EVar (6 + BN2))).
Definition JS_cn2 := sel3 JS_cn2_c.
(* [comment removed for export] *)
Definition Vc5 : nat := 290.
Definition JS_cb5_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (JS_cn2 m m) [] 0xabdc8 0xabdcc 0xabf8c) 0xabdcc OVC (ELit 0) ITON2 xX2c 0 60 (C5 - 3 * GEV)
       (room m (eaddz xX2c 1) Vc5 ++ cn2_facts) Vc5).
Definition JS_cb5 := sel3 JS_cb5_c.
(* [comment removed for export] *)
Definition Vc6 : nat := 330.
Definition JS_cb6_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (JS_cb5 m m) [DRun [0xabe5c]; DBrF] 0xabea8 0xabeac 0xabfa8) 0xabeac OVC (ELit 0) ITON2 (eaddz xX2c 1) 0 59 C5
       (room m (eaddz xX2c 2) Vc6 ++ cn2_facts ++ [KRange (esub RCc J5) 2 (2 ^ 48)]) Vc6).
Definition JS_cb6 := sel3 JS_cb6_c.
(* [comment removed for export] *)
Definition STc_close (m : smode) : list acs :=
  [snd (DPATH m NXF (JS_ca1 m m) [DRun [0xabb34]; DBrT; DRun [0xac05c]] 0); snd (DPATH m NXF (JS_cb5 m m) [DRun [0xabe5c]; DBrT; DRun [0xac05c]] 0)].
Definition TCc_c := Eval vm_compute in tri (fun w m =>
  JT (STc_close m) 0xac05c [] KEEP (4 + V5x)
     ([KRange DEPTH 0 255; stk_shok; KRange ITO 0 (INSZ - 2); KRange ITOC 0 INSZ; rel ITOC IXC 2]
      ++ mfacts w m V5x ITOC (EVar (3 + V5x)) C5 ++ pos ITOC IXC (ELit 0) 0 BIG ++ str m IXC ITOC (ELit 0) V5x ++ blkF m V5x ++ F_facts ++ kn_fixed)
     (vis m V5x) (EVar (3 + V5x))).
Definition TCc := sel3 TCc_c.
Definition JS_rbc_c := Eval vm_compute in tri (fun w m =>
  JSEk K5 pos w m (site_statesP true m (TCc m m) [] 0xac0a8 0xac0ac 0xace4c) 0xac0ac (ELit 0) ITOC IXC (eaddz IXC 1) 0 2 (C5 + GEV)
       [KRange ITO 0 (INSZ - 2); KRange ITOC 0 INSZ] V5r).
Definition JS_rbc := sel3 JS_rbc_c.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CM1 : nat := 40.  Definition CM2 : nat := 41.  Definition CM3L : nat := 42.  Definition CM3R : nat := 43.
Definition CM4 : nat := 44.  Definition CM5 : nat := 45.  Definition CM6 : nat := 46.  Definition CM7 : nat := 47.

Definition G8 (k : Z) : Z := - 2 * CG + k * GEV.
Definition pre6m : list dstep := [DRun [0xa9434]; DBrT].
Definition Vm1 : nat := 66.
Definition JS_m1_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (S6 2 m) pre6m 0xaa3cc 0xaa3d4 0xacd0c) 0xaa3d4 (ELit 0) ITO2e IX (eaddz IX 1) 0 48 (G8 1) [] Vm1).
Definition JS_m1 := sel3 JS_m1_c.
Definition Vm2 : nat := 104.
Definition JS_m2_c := Eval vm_compute in tri (fun w m =>
  JSEk 65 pos w m (site_states m (JS_m1 m m) [] 0xaa4e0 0xaa4e8 0xacd28) 0xaa4e8 (ELit 0) ITO2e (eaddz IX 1) (eaddz IX 10) 0 47 (G8 2) [] Vm2).
Definition JS_m2 := sel3 JS_m2_c.

(* [comment removed for export] *)
Definition triL (f : smode -> smode -> acs) : acs * acs := (tin MS, f ML ML).
Definition Vm3 : nat := 144.
Definition stub_state (S0 : acs) (path : list dstep) (bpc back stubret : Z) : list acs :=      (* [comment removed for export] *)
  let s1 := snd (DPATH ML NXF S0 (path ++ [DRun [bpc]; DBrT; DRun [back]]) 0) in
  let b0 := snd (DPATH ML NXF S0 (path ++ [DRun [bpc]; DBrF; DRun []]) 0) in
  [s1; snd (DPATH ML NXF (fake_ret stubret b0) [DRun [back]] 0)].
Definition pre_m3 (right : bool) : list dstep := [DRun [0x6d1dc]; DExt 5 []; DRun [0xaa544]; if right then DBrT else DBrF].
Definition JS_m3l_c := Eval vm_compute in triL (fun w m =>
  JSEk 65 pos w m (stub_state (JS_m2 ML ML) (pre_m3 false) 0xab060 0xab068 0xacdd4) 0xab068 (ELit 0) ITO2e (eaddz IX 10) (eaddz IX 23) 0 38 (G8 3) [] Vm3).
Definition JS_m3l := sel3 JS_m3l_c.
Definition JS_m3r_c := Eval vm_compute in triL (fun w m =>
  JSEk 65 pos w m (stub_state (JS_m2 ML ML) (pre_m3 true) 0xab0b4 0xab0bc 0xacdec) 0xab0bc (ELit 0) ITO2e (eaddz IX 10) (eaddz IX 24) 0 38 (G8 3) [] Vm3).
Definition JS_m3r := sel3 JS_m3r_c.
(* [comment removed for export] *)
Definition IXm : expr := EVar 184.
Definition Vm4 : nat := 185.
Definition mfx : list kentry :=      (* [comment removed for export] *)
  [KRange ITO 0 (INSZ - 2); KRange IXm 0 BIG; KRange (esub IXm IX) 23 24; KRange (esub (escale 24 ITO2e) IXm) 24 (BIG + 48)].     (* [comment removed for export] *)
Definition pre_m4 : list dstep := [DRun [0x6d1dc]; DExt 5 []].
Definition JS_m4_c := Eval vm_compute in triL (fun w m =>
  JSEk 65 pos w m (stub_state (JS_m3l ML ML) pre_m4 0xab144 0xab14c 0xacd40 ++ stub_state (JS_m3r ML ML) pre_m4 0xab144 0xab14c 0xacd40)
       0xab14c (ELit 0) ITO2e IXm (eaddz IXm 1) 0 24 (G8 4) mfx Vm4).
Definition JS_m4 := sel3 JS_m4_c.
Definition Vm5 : nat := 226.
Definition JS_m5_c := Eval vm_compute in triL (fun w m =>
  JSEk 185 pos w m (stub_state (JS_m4 ML ML) [] 0xab1dc 0xab1e4 0xacd58) 0xab1e4 (ELit 0) ITO2e (eaddz IXm 1) (eaddz IXm 11) 0 23 (G8 5) mfx Vm5).
Definition JS_m5 := sel3 JS_m5_c.
(* [comment removed for export] *)
Definition BM1 : nat := 270.
Definition xIm1 : expr := EVar 271.  Definition xXm1 : expr := EVar 272.
Definition Vm6 : nat := 296.
Definition m6facts : list kentry := mfx ++ [KRange xIm1 0 INSZ; KRange (esub xIm1 ITO) 2 INSZ; KRange xXm1 0 BIG].     (* [comment removed for export] *)
Definition STm_s1 : acs := fake_ret 0xab244 (snd (DPATH ML NXF (JS_m5 ML ML) [DRun [0x6d1dc]; DExt 5 []; DRun [ENTRY]] 0)).
Definition JS_m6_c := Eval vm_compute in triL (fun w m =>
  JSEk 273 pos w m (stub_state STm_s1 [] 0xab2b8 0xab2c0 0xacd8c) 0xab2c0 (ELit 0) xIm1 xXm1 (eaddz xXm1 1) 0 14 (G8 5) m6facts Vm6).
Definition JS_m6 := sel3 JS_m6_c.
Definition Vm7 : nat := 336.
Definition JS_m7_c := Eval vm_compute in triL (fun w m =>
  JSEk 273 pos w m (stub_state (JS_m6 ML ML) [] 0xab350 0xab358 0xacda4) 0xab358 (ELit 0) xIm1 (eaddz xXm1 1) (eaddz xXm1 9) 0 13 (G8 6) m6facts Vm7).
Definition JS_m7 := sel3 JS_m7_c.
(* [comment removed for export] *)
Definition BM2 : nat := 380.
Definition xIm2 : expr := EVar 381.  Definition xXm2 : expr := EVar 382.
Definition Vm8 : nat := 412.
Definition STm_s2 : acs := fake_ret 0xab410 (snd (DPATH ML NXF (JS_m7 ML ML) [DRun [ENTRY]] 0)).
Definition JS_m8_c := Eval vm_compute in triL (fun w m =>
  JSEk 383 pos w m (stub_state STm_s2 [] 0xab730 0xab738 0xace64) 0xab738 (ELit 0) xIm2 xXm2 (eaddz xXm2 1) 0 6 (G8 6) [KRange xIm2 0 INSZ] Vm8).
Definition JS_m8 := sel3 JS_m8_c.
