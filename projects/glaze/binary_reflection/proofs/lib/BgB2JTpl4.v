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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum OSSVerify.Proofs.glaze.binary_reflection.lib.BgEsc OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export BgB2JT BgB2JTpl.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CAB (vt : nat) : nat := (20 + vt)%nat.   Definition CPV (vt : nat) : nat := (23 + vt)%nat.
Definition CPWA : nat := 34.  Definition CPWP : nat := 35.
Definition CSLOOP : nat := 28.  Definition CSEL : nat := 29.  Definition CSLOOPL : nat := 30.     (* [comment removed for export] *)
Definition vt_split (r : nat) (vt : Z) : list dstep := if Z.eqb vt 0 then [DRLo r 0] else [DRHi r (vt - 1); DRLo r vt].

(* [comment removed for export] *)
Definition HLa : expr := EVar 80.  Definition NTa : expr := EVar 81.  Definition BCa : expr := EVar 82.  Definition NVA : expr := EVar 83.
Definition V4g : nat := 84.
Definition ITOG : expr := eadd (eaddz ITO 2) HLa.
Definition pre4a : list dstep :=
  [DRun [0xa7ecc]; DBrF; DRun [0xa7f08]; DBrT; DRun [0xa7f30]; DBrT; DRun [0xa7f90]; DExt 42 []; DRun [0xa7f9c]; DExt 46 [F; ELit 32; ELit 8];
   DRun [0xa7fac]; DBrT].
Definition ST_ag (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (ATs 4 m) (hdr_pathG pre4a 5 cfg 0xa7ff0 0xa7ff8 true 0xa9f24 true 0xa9f30) 0)) [0; 1; 2; 3].
Definition afacts : list kentry :=
  [KRange HLa 1 8; KRange ITO 0 (INSZ - 3); KRange NTa 0 255; KRange BCa 1 128; KRange NVA 0 (2 ^ 48); KShOk (SA F 32) (ELit 8)].
Definition JS_ag_c := Eval vm_compute in tri (fun w m =>
  JSGk 80 pos w m (ST_ag m) 0xa9f30 [(20%nat, NTa); (18%nat, BCa); (11%nat, NVA)] (ELit 0) ITOG IX 0 72 (- 2 * CG) afacts V4g).
Definition JS_ag := sel3 JS_ag_c.
(* [comment removed for export] *)
Definition ITOA : expr := EVar 128.
Definition V4b : nat := 129.
Definition pre4b : list dstep := [DRun [0xa9f80]; DBrT; DRun [0xa9fd0]; DBrT; DRun [0xa9ff4]; DBrT].
(* [comment removed for export] *)
Definition JS_ab_c := Eval vm_compute in tri (fun w m =>
  JT (site_states m (JS_ag m m) pre4b 0xaa088 0xaa090 0xacb48) 0xaa090 [] 84 (4 + V4b)
     ([KRange DEPTH 0 255; stk_shok; rel ITOA IX 72] ++ room m (eaddz IX 1) V4b
      ++ afacts ++ [KWord (SA F 32) 8 NVA; KRange ITOA 0 INSZ; KRange (esub ITOA ITO) 3 INSZ; KRange (esub ITOA ITOG) 1 129]
      ++ mfacts w m V4b ITOG (EVar (3 + V4b)) C5 ++ pos ITOA IX (ELit 0) 0 BIG ++ str m IX ITOA (ELit 0) V4b ++ blkF m V4b ++ F_facts ++ kn_fixed)
     (vis m V4b) (EVar (3 + V4b))).
Definition JS_ab := sel3 JS_ab_c.
Definition ABs_c := Eval vm_compute in
  map (fun vt => tri (fun w m => snd (DPATH m (nxt (JS_ab w m)) (JS_ab w m) (DRun [0xaa160] :: vt_split 10 vt) 0))) [0; 1; 2].     (* [comment removed for export] *)
Definition ABs (vt : nat) := sel3 (nth vt ABs_c (tin MS, tin ML)).
(* [comment removed for export] *)
Definition V4w : nat := 65.
Definition wITO : expr := EVar 62.  Definition wIX : expr := EVar 63.  Definition wERR : expr := EVar 64.
Definition pw_facts (w m : smode) (c : Z) : list kentry :=
  [KRange DEPTH 0 255; stk_shok; KRange wITO 0 INSZ; KRange wERR 0 24; relE wITO wIX wERR 2]
  ++ mfacts w m V4w wITO (EVar (3 + V4w)) c ++ pos wITO wIX wERR 0 BIG ++ str m wIX wITO wERR V4w ++ blkF m V4w ++ F_facts ++ kn_fixed.
(* [comment removed for export] *)
Definition drop_clo (cs : acs) : acs :=
  set_kn cs (List.filter (fun K => match K with
                                   | KWord (SA b o) _ _ => negb (expr_eqb b e_sp && Z.leb (-176) o && Z.ltb o (-112))
                                   | _ => true end) (kn cs)).
Definition ST_pwa (m : smode) : list acs :=
  [snd (DPATH m NXF (drop_clo (fake_ret 0xaa190 (snd (DPATH m NXF (ABs 0 m m) [DRHi 18 3; DRLo 18 4; DRun [0xaeeec]] 0)))) [DRun [0xac180]] 0);
   snd (DPATH m NXF (drop_clo (fake_ret 0xaa1cc (snd (DPATH m NXF (ABs 2 m m) [DRHi 18 1; DRLo 18 2; DRun [0xb1fd4]] 0)))) [DRun [0xac180]] 0)].
Definition TPWA_c := Eval vm_compute in tri (fun w m => JT (ST_pwa m) 0xac180 [] KEEP (4 + V4w) (pw_facts w m C5) (vis m V4w) (EVar (3 + V4w))).
Definition TPWA := sel3 TPWA_c.
(* [comment removed for export] *)
Definition V4r : nat := 104.
Definition rbr_facts (w m : smode) (c : Z) (v : nat) : list kentry :=
  [KRange DEPTH 0 255; stk_shok; KRange wITO 0 INSZ; KRange wERR 0 24; relE wITO wIX wERR 2] ++ room m (eaddz wIX 1) v
  ++ mfacts w m v wITO (EVar (3 + v)) c ++ pos wITO wIX wERR 0 BIG ++ str m wIX wITO wERR v ++ blkF m v ++ F_facts ++ kn_fixed.
Definition JS_rbra_c := Eval vm_compute in tri (fun w m =>
  JT (site_statesP true m (TPWA m m) [] 0xac1d4 0xac1d8 0xacb7c) 0xac1d8 [] 65 (4 + V4r) (rbr_facts w m (C5 + GEV) V4r) (vis m V4r) (EVar (3 + V4r))).
Definition JS_rbra := sel3 JS_rbra_c.

(* [comment removed for export] *)
Definition BCp : expr := EVar 62.     (* [comment removed for export] *)
Definition V4p : nat := 64.
Definition C4p : Z := - CG + GEV.
Definition pre4p : list dstep := [DRun [0xa7ecc]; DBrT; DRun [0xa842c]; DExt 42 []].
Definition JS_p1_c := Eval vm_compute in tri (fun w m =>
  JSEk 63 pos w m (site_states m (ATs 4 m) pre4p 0xa8974 0xa897c 0xacaa4) 0xa897c (ELit 0) (eaddz ITO 1) IX (eaddz IX 1) 0 24 C4p
       [KRange BCp 1 128; KWord (SA e_sp (-176)) 8 G; KWord (SA e_sp (-168)) 8 PIT] V4p).     (* [comment removed for export] *)
Definition JS_p1 := sel3 JS_p1_c.
Definition PVs_c := Eval vm_compute in
  map (fun vt => tri (fun w m => snd (DPATH m (nxt (JS_p1 w m)) (JS_p1 w m) (DRun [0xa8a30] :: vt_split 10 vt) 0))) [0; 1; 2].
Definition PVs (vt : nat) := sel3 (nth vt PVs_c (tin MS, tin ML)).


(* [comment removed for export] *)
Definition HLs : expr := EVar 110.  Definition NSs : expr := EVar 111.
Definition V4s : nat := 112.
Definition ITOHs : expr := eadd ITO1 HLs.
Definition pre4s : list dstep := [DRun [0xa8a30]; DRHi 10 2; DRun [0xa9700]; DBrT; DRun [0xaa5f8]; DBrT].
Definition ST_sa0 (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (JS_p1 m m) (hdr_pathG pre4s 15 cfg 0xaa63c 0xaa644 true 0xac3e8 false 0xac3f0) 0)) [0; 1; 2; 3].
Definition JS_sa0_c := Eval vm_compute in tri (fun w m =>
  JSGk 63 pos w m (ST_sa0 m) 0xac3f0 [(20%nat, NSs)] (ELit 0) ITOHs (eaddz IX 1) 0 47 C5 [KRange HLs 1 8; KRange ITO 0 (INSZ - 2); KRange NSs 0 (2 ^ 48)] V4s).
Definition JS_sa0 := sel3 JS_sa0_c.
Definition STs_first (m : smode) : acs := snd (DPATH m NXF (JS_sa0 m m) [DRun [0xac414]; DBrF; DRun [0xac444]] 0).
Definition STs_esc (m : smode) (s0 : acs) : acs :=
  fake_ret 0xac69c (snd (DPATH m NXF s0 [DRun [0xac468]; DBrF; DRun [0xac498]; DRLo 15 0; DExt 42 []; DRun [0xac4a0]; DBrF; DRun [0xac66c]; DBrF; DRun [BgEsc.ENTRY]] 0)).
Definition STs_second (m : smode) : acs := snd (DPATH m NXF (STs_esc m (STs_first m)) [DRun [0xac70c]; DBrF; DRun [0xac75c]; DBrF; DRun [0xac444]] 0).
Definition Ts_c := Eval vm_compute in tri (fun w m =>
  JT [STs_first m; STs_second m] 0xac444 [(20%nat, RC)] KEEP (4 + V5t) (loop_facts w m RC ITOL IXL V5t) (vis m V5t) (EVar (3 + V5t))).
Definition Ts := sel3 Ts_c.
Definition INVs_c := Eval vm_compute in tri (fun w m =>
  JT [STs_first m; STs_second m] 0xac444 [(20%nat, esub RC J5)] KEEP (4 + V5i)
     (KRange RC 1 (2 ^ 48) :: loop_facts w m (esub RC J5) ITOJ IXJ V5i) (vis m V5i) (EVar (3 + V5i))).
Definition INVs := sel3 INVs_c.
Definition OVS : list (nat * expr) := [(19%nat, NK); (20%nat, esub RC J5)].
Definition ST_sk (m : smode) : list acs :=
  map (fun cfg => snd (DPATH m NXF (INVs m m) (hdr_pathG [DRun [0xac468]; DBrF] 15 cfg 0xac498 0xac4a0 false 0xac628 false 0xac630) 0)) [0; 1; 2; 3].
Definition JS_sk_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (ST_sk m) 0xac630 OVS (ELit 0) ITOK IXJ 0 71 (C5 - CG) (kfacts ++ [KRange HLK 1 8; KRange NK 0 (2 ^ 50)]) V3k).
Definition JS_sk := sel3 JS_sk_c.
Definition STs_escJ (m : smode) : acs := fake_ret 0xac69c (snd (DPATH m NXF (JS_sk m m) [DRun [0xac66c]; DBrF; DRun [BgEsc.ENTRY]] 0)).
(* [comment removed for export] *)
Definition JS_se_c := Eval vm_compute in tri (fun w m =>
  JT [snd (DPATH m NXF (STs_escJ m) [DRun [0xac6c0]] 0)] 0xac6c0 OVS 107 (4 + (2 + BK))
     ([KRange DEPTH 0 255; stk_shok; relK xXk 69] ++ colon_facts ++ mfacts w m (2 + BK) ITOK (EVar (5 + BK)) (C5 - CG + GEV)
      ++ posK ITOK xXk (ELit 0) IXMAX ++ str m xXk (eadd ITOK NK) (ELit 0) (2 + BK) ++ blkF m (2 + BK) ++ F_facts ++ kn_fixed)
     (vis m (2 + BK)) (EVar (5 + BK))).
Definition JS_se := sel3 JS_se_c.
(* [comment removed for export] *)
Definition ITOS : expr := eadd ITOK NK.
Definition JS_sc_c := Eval vm_compute in tri (fun w m =>
  JSGk 107 pos w m (site_statesP true m (JS_se m m) [DRun [0xac70c]; DBrF] 0xac75c 0xac760 0xac814) 0xac760 [(20%nat, esub RC J5)] (ELit 0) ITOS xXk 0 68 C5     (* [comment removed for export] *)
       (room m (eaddz xXk 1) V3c ++ kfacts ++ [KRange HLK 1 8; KRange NK 0 INSZ; KRange (esub RC J5) 2 (2 ^ 48)]) V3c).
Definition JS_sc := sel3 JS_sc_c.
(* [comment removed for export] *)
Definition ST_pwp (m : smode) : list acs :=
  [snd (DPATH m NXF (drop_clo (fake_ret 0xa8a60 (snd (DPATH m NXF (PVs 0 m m) [DRHi 27 3; DRLo 27 4; DRun [0xb3304]] 0)))) [DRun [0xab840]] 0);
   snd (DPATH m NXF (drop_clo (fake_ret 0xa8b64 (snd (DPATH m NXF (PVs 2 m m) [DRHi 27 1; DRLo 27 2; DRun [0xb75c4]] 0)))) [DRun [0xab840]] 0);
   (* [comment removed for export] *)
   snd (DPATH m NXF (JS_p1 m m) [DRun [0xa8a30]; DRHi 10 2; DRun [0xa9700]; DBrF; DRun [0xab840]] 0);
   snd (DPATH m NXF (JS_sa0 m m) [DRun [0xac414]; DBrT; DRun [0xab840]] 0);
   snd (DPATH m NXF (STs_escJ m) [DRun [0xac70c]; DBrT; DRun [0xab840]] 0)].
Definition TPWP_c := Eval vm_compute in tri (fun w m => JT (ST_pwp m) 0xab840 [] KEEP (4 + V4w) (pw_facts w m C4p) (vis m V4w) (EVar (3 + V4w))).
Definition TPWP := sel3 TPWP_c.
Definition JS_rbrp_c := Eval vm_compute in tri (fun w m =>
  JT (site_states m (TPWP m m) [] 0xab890 0xab898 0xacb64) 0xab898 [] 65 (4 + V4r) (rbr_facts w m (C4p + GEV) V4r) (vis m V4r) (EVar (3 + V4r))).
Definition JS_rbrp := sel3 JS_rbrp_c.
