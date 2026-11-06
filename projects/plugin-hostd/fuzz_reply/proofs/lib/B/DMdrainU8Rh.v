(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainU8.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail; file sha256 9a62bc6647de) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU8.v, with its module paths, module names and addresses changed; 16 of its 120 lines of code are new or changed and 2 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU8Rh.v at commit b93d7a87dae, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the drain's EPILOGUE after DoRecycle returns, at the RE-HIDE twins - the
   primed counterpart of DMdrainU8.epi_after_recycle (reply lib/A/DMdrainU8.v, relocated from cgif's DMdrainU8.v at commit
   67fc7ef5787c).  DoRecycle's post is now DMwalkIFRh.dr_leaf_rh's YGcfRehidePost.acall_post_x_rh: the same as
   acall_post_x except that the world only grows outside the dead shadow (wle_in) and the view frame also excludes
   the dead shadow (YGcfRehidePost.acall_post_x_rh).  Recycle's six saved words sit on the stack at sp1 + 32 .. sp1 + 80, in
   high memory, and the dead shadow lies in the shadow ranges RZ_cf (YGcfRehidePost.dead_shadow_new_RZ), all of which end
   below kHighMemBeg:
   - [stack_not_RZ]: no address at or above kHighMemBeg is in RZ_cf (shadow_addr ASAN_CEIL + 4096 <=
     0x7fff8000 + 0x7fffff800000 / 8 + 4096 = 0x10007fef9000 < kHighMemBeg = 0x10007fff8000, by ASAN_CEIL_range);
   - [saved_byte] / [saved_kept]: a word of Recycle's saved area reads the same after the primed DoRecycle as at the
     call - DMdrainU8's proof with that one more premise of the frame discharged;
   - [epi_after_recycle_rh]: YFh8.segX (reply YFh8.segX) from DoRecycle's return 0x33b58, as DMdrainU8.
   rule 24: no function proved (kind: the seed and run of a segment already walked, YFh8.segX, at the re-hide twin's
   post).  The lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle
   QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM.
   Additive: a new file; no existing file touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey YFgt YFh8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DMwalkIF DMdrainG1 DMdrainT9.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DGg2 YFhf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* No address at or above kHighMemBeg is in the re-hide shadow ranges. *)
Lemma stack_not_RZ : forall a, kHighMemBeg <= a -> ~ YGcfRehidePost.RZ_cf a.
Proof.
intros a Ha HZ. unfold YGcfRehidePost.RZ_cf, shadow_addr in HZ.
pose proof (@ASAN_CEIL_range _) as [[C1 C2] _].
assert (D : ASAN_CEIL / 8 <= 17592184995840).
{ change 17592184995840 with (0x7fffff800000 / 8). apply Z.div_le_mono; lia. }
change (kLowShadowBeg / 8) with 268430848 in HZ. change (4096 / 8) with 512 in HZ.
change (kHighMemBeg / 8) with 2199291686912 in HZ.
unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.

Section g.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Hypothesis TB : TfibSyms B.
Variables (inst : Z) (ly : alayout) (S' Sr : astate) (W W' : world tfibsegs).
Variables (regs' regs'' : bvmap 5 word) (mem' mem'' : word -> option byte) (md md'' : Model).
Variables (vra vs0 vs1 vs2 vs3 vs4 : Z).
Let sp1 : Z := spZ regs'.

(* DoRecycle's post at the twin (DMwalkIFRh.dr_leaf_rh's acall_post_x_rh) and what the cut gives *)
Hypothesis HPOST : YGcfRehidePost.acall_post_x_rh B ARXr AOX inst DMwalkIF.DRSTACK_X ly S' W regs' mem' md
  (fun a => spZ regs' <= a < spZ regs' + 32) ly Sr W' regs'' mem'' md''.
Hypothesis HSTK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S' a.
Hypothesis HMONO : forall a, AOX ly Sr a -> AOX ly S' a.
Hypothesis LY : layout_ok ly.
Hypothesis Hsp : ly_stk_lo ly + DMwalkIF.DRSTACK_X <= sp1 /\ sp1 + 80 <= ly_stk_hi ly.
Hypothesis Hal : sp1 mod 16 = 0.
Hypothesis Htp : getr regs' 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (w64 vra).
Hypothesis Hvals : 0 <= vra < 2 ^ 64 /\ 0 <= vs0 < 2 ^ 64 /\ 0 <= vs1 < 2 ^ 64 /\ 0 <= vs2 < 2 ^ 64 /\
  0 <= vs3 < 2 ^ 64 /\ 0 <= vs4 < 2 ^ 64.
(* the six saved words at the call (Recycle's prologue wrote them; the loop does not touch them) *)
Hypothesis W72 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 72) 8 vra.
Hypothesis W64 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 64) 8 vs0.
Hypothesis W56 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 56) 8 vs1.
Hypothesis W48 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 48) 8 vs2.
Hypothesis W40 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 40) 8 vs3.
Hypothesis W32 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 32) 8 vs4.

(* a byte of Recycle's saved area reads the same after the primed DoRecycle as at the call *)
Lemma saved_byte : forall a, sp1 + 32 <= a < sp1 + 80 ->
mbyte tfibsegs (mrestrict (w_H W') mem'') a = mbyte tfibsegs (mrestrict (w_H W) mem') a.
Proof.
intros a Ha.
pose proof (DMdrainG1.STKR ly LY) as [K1 K2].
pose proof (ts_errno _ TB) as EE.
destruct Hsp as [S1 S2].
destruct HPOST as (_ & _ & _ & _ & _ & HFR & _).
apply DGg2.aview_eq_mbyte.
apply HFR.
- unfold sp1, DMwalkIF.DRSTACK_X, kHighMemBeg, kHighMemEnd in *. lia.
- apply HSTK. unfold sp1, DMwalkIF.DRSTACK_X in *. lia.
- intros HA. apply (HSTK a); [unfold sp1, DMwalkIF.DRSTACK_X in *; lia | exact (HMONO a HA)].
- unfold ascratch. rewrite EE. unfold TFIB_ERRNO, sp1, DMwalkIF.DRSTACK_X, kHighMemBeg in *. intros [HX|HX]; lia.
- unfold sp1 in *. lia.
- intros HD. apply (stack_not_RZ a); [unfold sp1, DMwalkIF.DRSTACK_X in *; lia |].
  exact (YGcfRehidePost.dead_shadow_new_RZ _ _ _ _ HD).
Qed.

Lemma saved_kept : forall off v, 32 <= off -> off + 8 <= 80 ->
val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + off) 8 v ->
val_mem tfibsegs (mrestrict (w_H W') mem'') (sp1 + off) 8 v.
Proof.
intros off v H1 H2 HV k Hk. rewrite saved_byte by lia. exact (HV k Hk).
Qed.

(* the registers after DoRecycle: sp and tp are callee-saved *)
Lemma sp_after : spZ regs'' = sp1.
Proof.
destruct HPOST as (_ & _ & _ & HRP & _).
unfold sp1, spZ. exact (f_equal bv_unsigned (HRP 2 ltac:(unfold acallee_saved; lia))).
Qed.

Lemma tp_after : getr regs'' 4 = w64 TFIB_TP.
Proof.
destruct HPOST as (_ & _ & _ & HRP & _).
transitivity (getr regs' 4); [exact (HRP 4 ltac:(unfold acallee_saved; lia)) | exact Htp].
Qed.

(* Recycle's epilogue from DoRecycle's return, after the primed DoRecycle. *)
Theorem epi_after_recycle_rh : forall mat0,
SRr tfibsegs W' (mkCfg (mkst regs'' (w64 0x33b58) mem'' (seg_rom tfibsegs))
  (with_vm_backing (m_vm_lazy md'') mat0 md''))
  (YFgt.at_RETX W' regs'' mem'' md'' vra vs0 vs1 vs2 vs3 vs4).
Proof.
intros mat0.
pose proof sp_after as ESP. unfold spZ in ESP.
pose proof (DMdrainG1.STKR ly LY) as [K1 K2].
destruct Hsp as [S1 S2].
assert (V72 := saved_kept 72 vra ltac:(lia) ltac:(lia) W72).
assert (V64 := saved_kept 64 vs0 ltac:(lia) ltac:(lia) W64).
assert (V56 := saved_kept 56 vs1 ltac:(lia) ltac:(lia) W56).
assert (V48 := saved_kept 48 vs2 ltac:(lia) ltac:(lia) W48).
assert (V40 := saved_kept 40 vs3 ltac:(lia) ltac:(lia) W40).
assert (V32 := saved_kept 32 vs4 ltac:(lia) ltac:(lia) W32).
fold sp1 in ESP. rewrite <- ESP in V72, V64, V56, V48, V40, V32.
apply YFh8.segX.
apply DMdrainT9.epi_free_hyps;
first [ exact tp_after | exact Hra | exact Hvals | exact V72 | exact V64 | exact V56 | exact V48 | exact V40 | exact V32
      | (rewrite ESP; exact Hal)
      | (rewrite ESP; unfold sp1, DMwalkIF.DRSTACK_X, YFeu.LFRAME, kHighMemBeg, kHighMemEnd in *; split; lia) ].
Qed.
End g.
End f.

Print Assumptions epi_after_recycle_rh.
