(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU8Rh.v (commit 67deba317dfb, blob 3ee7b0445a97) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 1 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgt AFh8.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainG1 DMdrainT9.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGg2 AFhf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

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

Hypothesis HPOST : YGcfRehidePost.acall_post_x_rh B ARXr AOX inst DMwalkIFA.DRSTACK_X ly S' W regs' mem' md
  (fun a => spZ regs' <= a < spZ regs' + 32) ly Sr W' regs'' mem'' md''.
Hypothesis HSTK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S' a.
Hypothesis HMONO : forall a, AOX ly Sr a -> AOX ly S' a.
Hypothesis LY : layout_ok ly.
Hypothesis Hsp : ly_stk_lo ly + DMwalkIFA.DRSTACK_X <= sp1 /\ sp1 + 80 <= ly_stk_hi ly.
Hypothesis Hal : sp1 mod 16 = 0.
Hypothesis Htp : getr regs' 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (w64 vra).
Hypothesis Hvals : 0 <= vra < 2 ^ 64 /\ 0 <= vs0 < 2 ^ 64 /\ 0 <= vs1 < 2 ^ 64 /\ 0 <= vs2 < 2 ^ 64 /\
  0 <= vs3 < 2 ^ 64 /\ 0 <= vs4 < 2 ^ 64.

Hypothesis W72 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 72) 8 vra.
Hypothesis W64 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 64) 8 vs0.
Hypothesis W56 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 56) 8 vs1.
Hypothesis W48 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 48) 8 vs2.
Hypothesis W40 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 40) 8 vs3.
Hypothesis W32 : val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + 32) 8 vs4.

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
- unfold sp1, DMwalkIFA.DRSTACK_X, kHighMemBeg, kHighMemEnd in *. lia.
- apply HSTK. unfold sp1, DMwalkIFA.DRSTACK_X in *. lia.
- intros HA. apply (HSTK a); [unfold sp1, DMwalkIFA.DRSTACK_X in *; lia | exact (HMONO a HA)].
- unfold ascratch. rewrite EE. unfold TFIB_ERRNO, sp1, DMwalkIFA.DRSTACK_X, kHighMemBeg in *. intros [HX|HX]; lia.
- unfold sp1 in *. lia.
- intros HD. apply (stack_not_RZ a); [unfold sp1, DMwalkIFA.DRSTACK_X in *; lia |].
  exact (YGcfRehidePost.dead_shadow_new_RZ _ _ _ _ HD).
Qed.

Lemma saved_kept : forall off v, 32 <= off -> off + 8 <= 80 ->
val_mem tfibsegs (mrestrict (w_H W) mem') (sp1 + off) 8 v ->
val_mem tfibsegs (mrestrict (w_H W') mem'') (sp1 + off) 8 v.
Proof.
intros off v H1 H2 HV k Hk. rewrite saved_byte by lia. exact (HV k Hk).
Qed.

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

Theorem epi_after_recycle_rh : forall mat0,
SRr tfibsegs W' (mkCfg (mkst regs'' (w64 0x344e0) mem'' (seg_rom tfibsegs))
  (with_vm_backing (m_vm_lazy md'') mat0 md''))
  (AFgt.at_RETX W' regs'' mem'' md'' vra vs0 vs1 vs2 vs3 vs4).
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
apply AFh8.segX.
apply DMdrainT9.epi_free_hyps;
first [ exact tp_after | exact Hra | exact Hvals | exact V72 | exact V64 | exact V56 | exact V48 | exact V40 | exact V32
      | (rewrite ESP; exact Hal)
      | (rewrite ESP; unfold sp1, DMwalkIFA.DRSTACK_X, AFeu.LFRAME, kHighMemBeg, kHighMemEnd in *; split; lia) ].
Qed.
End g.
End f.

Print Assumptions epi_after_recycle_rh.
