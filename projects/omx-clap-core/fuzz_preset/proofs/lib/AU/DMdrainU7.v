(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainU7.v (commit ce1a656b52b7, file sha256 e4966ce81df0) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 1 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainU7.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail and top; file sha256 0e254743c581) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 11371006ce4b on the cgif twin ce511d541cda; 1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (the internal file accept.tsv, re-measured each run): _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE7RecycleEmS2_+0x74 (a lui-built CONSTANT (strictcmp3 rule 8): the same value on both images, its use measured to be a size / flag / mask operand, never a pointer)), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU7.v at commit 2e76ed2595c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): DoRecycle's walk AT the drain's recycle cut.  With the cut's
   invariant in hand (DMdrainU6.cut_invariant) this file discharges DMdrainC.dr_pre_at_call's remaining
   premises - the machine state DMdeq.ATDR leaves at 0x345c8 - and runs H2's walk
   (DMrecF.dorecycle_ok_r : DMwalkIF.dorecycle_ok_t), so the arm holds
   [amreal (do_recycle (length P) P S') ... (dr_leaf_r ...)] at DoRecycle's entry.
   Like DMdrainU6 it is stated over the lists, so both arms use it.
   rule 24: proves function __sanitizer::QuarantineCache::DoRecycle at the drain's recycle cut (the walk is
   H2's DMrecF.dorecycle_ok_r; this file supplies its premise at the cut).  The lane's reuse search is
   the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM.
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import MnRecycle.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMdrainK DMdrainQ DMdrainC DMrecF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
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
Hypothesis RCH : MnRecycle.de_rchunk_m_t B ARXr AOX DRq.
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
(* the machine state at the call (DMdeq.ATDR, DMdeq.v:193-207) *)
Hypothesis Hra : getr regs' 1 = w64 0x345cc.
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

(* H2's DoRecycle walk at the cut. *)
Theorem dorecycle_at_cut :
amreal tfibsegs (do_recycle (length P) P S') W (cfg_at tfibsegs A_DoRecycle regs' mem' md)
  (DMwalkIF.dr_leaf_r B ARXr AOX DRq inst ly S' W regs' mem' md).
Proof.
exact (DMrecF.dorecycle_ok_r B ARXr AOX DRq RMAXD TB HRM FR RV RCH CDH inst ly S' P W regs' mem' md dr_pre_cut).
Qed.
End g.
End f.
