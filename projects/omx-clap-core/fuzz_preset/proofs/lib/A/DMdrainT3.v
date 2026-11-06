(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT3.v (commit 67deba317dfb, blob d3443fdc9929) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0h YK14 YK1b YK1a YK15 YK18 YP03 YP02 YP0k YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainK DMdrainN.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable ly : alayout.
Variable iw : chunk -> Z.
Variable H : word -> bool.

Lemma lcn_keep : forall (Win : Z -> Prop) (mem mem' : word -> option byte) (l : list batch) (z : Z),
(forall x : word, ~ Win (bv_unsigned x) -> mem' x = mem x) ->
(forall b, In b l -> 0 <= addrb ly b /\ addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64 /\
   forall a, addrb ly b <= a < addrb ly b + 24 + 8 * zl (b_items b) -> ~ Win a) ->
lcn ly iw (mrestrict H mem) l z -> lcn ly iw (mrestrict H mem') l z.
Proof.
intros Win mem mem' l. induction l as [|b t IH]; intros z HM HB HL; [exact I|].
cbn [lcn] in HL |- *. destruct HL as [Hb Ht]. destruct (HB b (or_introl eq_refl)) as (A1 & A2 & A3).
split.
- destruct Hb as (V0 & V8 & V16 & VS). unfold bcell. splits.
  + apply (val_mem_frame H mem mem' _ 8 _); [|exact V0].
    intros k Hk. assert (HZ : 0 <= zl (b_items b)) by (unfold zl; lia).
    apply HM. rewrite unsigned_lit_small by lia. apply A3. lia.
  + apply (val_mem_frame H mem mem' _ 8 _); [|exact V8].
    intros k Hk. assert (HZ : 0 <= zl (b_items b)) by (unfold zl; lia).
    apply HM. rewrite unsigned_lit_small by lia. apply A3. lia.
  + apply (val_mem_frame H mem mem' _ 8 _); [|exact V16].
    intros k Hk. assert (HZ : 0 <= zl (b_items b)) by (unfold zl; lia).
    apply HM. rewrite unsigned_lit_small by lia. apply A3. lia.
  + intros j k Hj. pose proof (proj1 (nth_error_Some (b_items b) j) ltac:(rewrite Hj; discriminate)) as LT.
    apply (val_mem_frame H mem mem' _ 8 _); [|exact (VS j k Hj)].
    intros i Hi. apply HM. assert (HZ : 0 <= zl (b_items b)) by (unfold zl; lia).
    rewrite unsigned_lit_small by (unfold zl in *; lia). apply A3. unfold zl in *. lia.
- apply (IH z HM); [intros b' Hb'; exact (HB b' (or_intror Hb')) | exact Ht].
Qed.

Lemma lcn_transfer : forall (m : word -> option byte) (G T : list batch),
lcn ly iw m G 0 -> lcn ly iw m T 0 ->
(G <> [] -> val_mem tfibsegs m (la ly G) 8 (fa ly T 0)) ->
lcn ly iw m (G ++ T) 0.
Proof.
intros m G T HG HT HR. apply (lcn_app_link ly iw m G T 0); [|exact HT].
destruct G as [|b t]; [exact I|].
apply (lcn_relink ly iw m (b :: t) (fa ly T 0)); [exact HG|]. intros _. apply HR. discriminate.
Qed.
End e.
End c.
