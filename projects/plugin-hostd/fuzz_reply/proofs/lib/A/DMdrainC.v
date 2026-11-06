(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainC.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail; file sha256 e00664a4181f) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): DoRecycle's call premise DMwalkIF.dr_pre_r (the interface at
   dc3949af11c) at Recycle's call site 0x33afc, from the state DMdeq.ATDR (DMdeq.v:193-207) leaves and the
   instance's re-quarantine field DMiface.di_requar_r (DMiface.v:218-225).  It also discharges the three
   conjuncts the interface gained for H2 (layout_ok, img_cover and the stack outside the owned set), which is
   what that head change promised: they cost the instance nothing because the drain has them at Drain's entry
   (DMiface.qview's qv_ly / qv_img) and through di_requar_r's owned shrink.
   rule 24: no function proved (kind: the premise of a call already walked; the lane's reuse search is
   LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   - [ret_ok_3326c]: Recycle's return address is a return address;
   - [plist_of]: YFeuC.plist_cells from the temp list's four header words and its batches' cells;
   - [dr_pre_at_call]: DMwalkIF.dr_pre_r.
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFey AFhf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface DMwalkIF DMdrainK DMdrainP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Recycle's return address after the call of DoRecycle (DMdeq.ATDR, DMdeq.v:197). *)
Lemma ret_ok_3326c : YK0s.ret_ok (w64 0x33b00).
Proof. vm_compute. reflexivity. Qed.

Section dc.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables (W : world tfibsegs) (ly : alayout) (S' : astate) (P : list batch).
Variables (inst : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Let m := mrestrict (w_H W) mem.
Let sp1 : Z := spZ regs.

(* what di_requar_r gives at the cut *)
Hypothesis HAR : ARXr inst ly S' W mem md.
Hypothesis HDRq : DRq S' (flat_map b_items P) (map b_self P).
Hypothesis Hinst : inst = as_inst B.
(* the three conjuncts the interface gained for H2 *)
Hypothesis HLY : layout_ok ly.
Hypothesis HIMG : img_cover ly.
Hypothesis HSTK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S' a.
(* the model side *)
Hypothesis HIT : Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) P.
Hypothesis HLEN : zl P < 2 ^ 40.
Hypothesis HCI : st_cache_inited S' = true.
(* the machine state at the call (DMdeq.ATDR) *)
Hypothesis Hra : getr regs 1 = w64 0x33b00.
Hypothesis Hsp : ly_stk_lo ly + DMwalkIF.DRSTACK_X <= sp1 /\ sp1 + 32 <= ly_stk_hi ly.
Hypothesis Hal : sp1 mod 16 = 0.
Hypothesis Hpres : forall a, sp1 - DMwalkIF.DRSTACK_X <= a < sp1 + 32 -> apresent (w_H W) mem a.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis Ha0 : getr regs 10 = w64 (inst + o_quar).
Hypothesis Ha1 : getr regs 11 = w64 sp1.
Hypothesis Ha2 : getr regs 12 = w64 (ly_T ly + t_cache).
(* the temp list at Recycle's sp: its four header words and its batches, linked *)
Hypothesis HT0 : val_mem tfibsegs m sp1 8 (zl P).
Hypothesis HT8 : val_mem tfibsegs m (sp1 + 8) 8 (fa ly P 0).
Hypothesis HT16 : val_mem tfibsegs m (sp1 + 16) 8 (la ly P).
Hypothesis HT24 : val_mem tfibsegs m (sp1 + 24) 8 (sum_bytes P).
Hypothesis HPL : lcn ly (iwB B ly) m P 0.

Lemma plist_of : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (YFeuC.plist_cells sp1 P).
Proof.
unfold YFeuC.plist_cells, qc_cells. cbn [qc_list qc_bytes].
apply Forall_cons.
{ apply val_mem_cellZ. cbn [aeval aoff].
  match goal with |- val_mem _ _ ?a _ _ => replace a with sp1 by lia end. exact HT0. }
apply Forall_cons.
{ apply val_mem_cell. cbn [aeval aoff batch_exp].
  match goal with |- val_mem _ _ ?a _ ?v =>
    replace a with (sp1 + 8) by lia; replace v with (fa ly P 0) by (destruct P; cbn [aeval batch_exp fa addrb]; reflexivity) end.
  exact HT8. }
apply Forall_cons.
{ apply val_mem_cell. cbn [aeval aoff batch_exp].
  match goal with |- val_mem _ _ ?a _ ?v =>
    replace a with (sp1 + 16) by lia; replace v with (la ly P) by (unfold la; destruct (rev P); cbn [aeval batch_exp addrb]; reflexivity) end.
  exact HT16. }
apply Forall_cons.
{ apply val_mem_cellZ. cbn [aeval aoff].
  match goal with |- val_mem _ _ ?a _ _ => replace a with (sp1 + 24) by lia end. exact HT24. }
exact (batch_cells_of_lcn B ly (w_H W) mem P HPL).
Qed.

Theorem dr_pre_at_call : DMwalkIF.dr_pre_r B ARXr AOX DRq inst ly S' P W regs mem md.
Proof.
unfold DMwalkIF.dr_pre_r. splits.
- exact HAR.
- exact Hinst.
- exact HDRq.
- exact HLY.
- exact HIMG.
- exact HSTK.
- exact HIT.
- exact HLEN.
- exact HCI.
- rewrite Hra. exact ret_ok_3326c.
- unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small by lia. lia.
- exact Hal.
- exact (proj1 Hsp).
- exact (proj2 Hsp).
- exact Hpres.
- exact Hgp.
- exact Htp.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- exact plist_of.
Qed.
End dc.
End c.
