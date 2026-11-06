(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainU7.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail and top; file sha256 0e254743c581) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU7.v, with its module paths, module names and addresses changed; 12 of its 82 lines of code are new or changed and 10 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU7Rh.v at commit b93d7a87dae, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (3 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): DoRecycle's walk at the drain's recycle cut, at the RE-HIDE twins - the
   primed counterpart of DMdrainU7.dorecycle_at_cut (cgif proofs/cgif/cgif_file_fuzzer/lib/DMdrainU7.v at commit
   67fc7ef5787c).  Recycle's secondary arm hides the dead shadow hull's interior at its return
   (YA0nR.SRr'_rehide_ret), so DoRecycle is stated over YG0dH.amreal' at YGcfRehidePost.RZ_cf with the leaf
   DMwalkIFRh.dr_leaf_rh (F1 priming row R3).  This file discharges DoRecycle's call premise at the cut
   (DMdrainC.dr_pre_at_call) exactly as DMdrainU7 does, and runs the primed DoRecycle contract
   DMwalkIFRh.dorecycle_ok_rh_t, an explicit premise of [dorecycle_at_cut_rh_of]: its proof is the primed DoRecycle
   chain (a Theorem Labs lane's dorecycle_ok_rh), so this file needs no DMrec* file.
   Reply's literal: Recycle's return address after its call of DoRecycle is 0x33b58 (cgif 0x3326c, Recycle+0x170,
   FN-SAME-CODE), the value reply's relocated DMdrainC.dr_pre_at_call takes (lib/B/DMdrainC.v:69 at image B).
   rule 24: proves function __sanitizer::QuarantineCache::DoRecycle at the drain's recycle cut at the re-hide twins
   (the walk is DMwalkIFRh.dorecycle_ok_rh_t; this file supplies its premise at the cut).  The lane's reuse search is
   LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM.
   Additive: a new file; DMdrainU7-style call premise, no existing file touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey YFhf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DMwalkIF DMdrainK DMdrainC.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MnRecycle DIfaceRh DMwalkIFRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Hypothesis TB : TfibSyms B.
Hypothesis HRM : rmaxd_ok RMAXD.
Hypothesis FR : di_frame_t ARXr AOX.
Hypothesis RV : di_rview_x_t B ARXr DRq RMAXD.
(* Recycle's contract at the twin (H4's primed head), CacheDealloc's released (it re-hides nothing) *)
Hypothesis RCHh : DIfaceRh.de_rchunk_m_rh_t B ARXr AOX DRq.
Hypothesis CDH : MnRecycle.de_cdealloc_m_t B ARXr AOX DRq.

Variables (W : world tfibsegs) (ly : alayout) (S' : astate) (P : list batch).
Variables (regs' : bvmap 5 word) (mem' : word -> option byte) (md : Model).
Variable inst : Z.
Let m' := mrestrict (w_H W) mem'.
Let sp1 : Z := spZ regs'.

(* what DMdrainU6.cut_invariant gives *)
Hypothesis HAR : ARXr inst ly S' W mem' md.
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
Hypothesis Hra : getr regs' 1 = w64 0x33b58.
Hypothesis Hsp : ly_stk_lo ly + DMwalkIF.DRSTACK_X <= sp1 /\ sp1 + 32 <= ly_stk_hi ly.
Hypothesis Hal : sp1 mod 16 = 0.
Hypothesis Hpres : forall a, sp1 - DMwalkIF.DRSTACK_X <= a < sp1 + 32 -> apresent (w_H W) mem' a.
Hypothesis Hgp : getr regs' 3 = w64 (as_gp B).
Hypothesis Htp : getr regs' 4 = w64 (as_tp B).
Hypothesis Ha0 : getr regs' 10 = w64 (inst + o_quar).
Hypothesis Ha1 : getr regs' 11 = w64 sp1.
Hypothesis Ha2 : getr regs' 12 = w64 (ly_T ly + t_cache).
Hypothesis HT0 : val_mem tfibsegs m' sp1 8 (zl P).
Hypothesis HT8 : val_mem tfibsegs m' (sp1 + 8) 8 (fa ly P 0).
Hypothesis HT16 : val_mem tfibsegs m' (sp1 + 16) 8 (la ly P).
Hypothesis HT24 : val_mem tfibsegs m' (sp1 + 24) 8 (sum_bytes P).
Hypothesis HPL : lcn ly (DMdrainK.iwB B ly) m' P 0.

Lemma dr_pre_cut : DMwalkIF.dr_pre_r B ARXr AOX DRq inst ly S' P W regs' mem' md.
Proof.
apply (DMdrainC.dr_pre_at_call B ARXr AOX DRq W ly S' P inst regs' mem' md);
first [ exact HAR | exact HDRq | exact Hinst | exact HLY | exact HIMG | exact HSTK
      | exact HIT | exact HLEN | exact HCI | exact Hra | exact Hsp | exact Hal | exact Hpres
      | exact Hgp | exact Htp | exact Ha0 | exact Ha1 | exact Ha2
      | exact HT0 | exact HT8 | exact HT16 | exact HT24 | exact HPL ].
Qed.

(* The primed DoRecycle walk at the cut, from the primed DoRecycle contract DMwalkIFRh.dorecycle_ok_rh_t (DMwalkIFRh.v:89),
   which the primed DoRecycle chain proves (a Theorem Labs lane's dorecycle_ok_rh). *)
Theorem dorecycle_at_cut_rh_of : DMwalkIFRh.dorecycle_ok_rh_t B ARXr AOX DRq RMAXD ->
amreal' tfibsegs YGcfRehidePost.RZ_cf (do_recycle (length P) P S') W (cfg_at tfibsegs A_DoRecycle regs' mem' md)
  (DMwalkIFRh.dr_leaf_rh B ARXr AOX DRq inst ly S' W regs' mem' md).
Proof.
intros DOK. exact (DOK TB HRM FR RV RCHh CDH inst ly S' P W regs' mem' md dr_pre_cut).
Qed.
End g.
End f.

Print Assumptions dorecycle_at_cut_rh_of.
