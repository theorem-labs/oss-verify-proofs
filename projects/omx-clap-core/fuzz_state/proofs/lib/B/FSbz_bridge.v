(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YEvtSRr.v, with its module paths changed; 17 of its 51 lines of code are new or changed and 88 lines of the source are left out. *)
(* Image B (fs.asan-ubsan) twin of lib/A/FSbz_bridge.v, itself
   Ported from: a working branch cedf3d02589 proofs/omx-clap-core/fuzz_manifest/lib/A/FMbz_bridge.v (a Theorem Labs lane).
   Changes from A's twin (a Theorem Labs lane, 2026-10-29): the Bz tree is image B's (lib/B/Bz, a Theorem Labs lane's, by path from
   a working branch 51f06361767), the donor's segments B's (lib/B/YB1v.v tfibsegs), FSbz_str B's;
   proofs unchanged. *)
(* The generic half of the bridge between a body walk written over the machine state alone
   (lib/B/Bz: `evt asegs Q ms`, that is "some step chain from ms reaches a state in Q") and the
   donor's call-site form (`SRr segs W (cfg_at segs pc regs mem md) POST`).

   Three facts make it one short file:
   - the two trees name the same image: `asegs = tfibsegs` by reflexivity (FSbz_str.asegs_tfibsegs);
   - the two step relations are the same relation: Bz `mstep` (lib/B/Bz/Lib/Exec.v:15) is
     `ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'`, which is what each
     step of the donor's `msteps` (lib/Reusable/YK0i.v:284-290) asks;
   - the donor already lifts its own `msteps` into `SRr` (`SRr_msteps`, lib/Reusable/YA0n.v:148),
     and the donor's own walks of library code use it that way (cgif_file A/AE6x.v:190).

   The shadow half of the bridge (chk_ok from the donor's range facts) is a Theorem Labs lane's, in FSbz_str.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK04 YK0i YK14 YK1b YK1a YK18 YP09 YP02 YG0n YG00 YG0a YG01 YG0f YG0d YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Bz.Lib Require Import ImageA.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Bz.Lib Require Exec Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSbz_str.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14 YI16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* one step of a body walk is one step of the donor's walk *)
Lemma bz_msteps_tfib : forall ms ms', Exec.msteps asegs ms ms' -> YK0i.msteps tfibsegs ms ms'.
Proof.
intros ms ms' H. induction H as [ms | ms ms1 ms2 Hstep _ IH].
- apply YK0i.mst_refl.
- destruct Hstep as [Hsvc Hok]. eapply YK0i.mst_step; [exact Hsvc | exact Hok | exact IH].
Qed.

(* a body walk that reaches Q, read at a donor call site: the walk runs on the restricted memory,
   and what it reaches is the configuration the donor continues from *)
(* Hwx is the image's own W^X fact (A/AF0x.v `Hwx_tfa` once that file carries fm's addresses); it is
   a premise here so that this bridge does not wait for it. *)
Lemma srr_of_evt : forall (Hwx : wx_segs_nowrap tfibsegs) (W : world tfibsegs) (pc : Z) regs mem md
(Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
Exec.evt asegs Q (restrict (w_H W) (mkst regs (w64 pc) mem (seg_rom tfibsegs))) ->
(forall ms' model', Q ms' -> same_but_materialized md model' -> hclean (w_H W) ms' ->
POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof.
intros Hwx W pc regs mem md Q POST (ms' & Hms & HQ) HK.
unfold cfg_at.
eapply (SRr_msteps tfibsegs Hwx W (mkst regs (w64 pc) mem (seg_rom tfibsegs)) ms' md POST).
- exact (bz_msteps_tfib _ _ Hms).
- intros model' Hsame Hcl. apply SRr_ret. cbn [ms_mem mkst]. exact (HK ms' model' HQ Hsame Hcl).
Qed.

(* the stack window the donor's call-site premise gives is the window a body walk asks for *)
Lemma stk_of_apresent : forall (H : word -> bool) (mem : word -> option byte) (lo hi : Z),
0 <= lo -> hi <= 2 ^ 64 ->
(forall a, lo <= a < hi -> apresent H mem a) ->
Frame.stk asegs (mrestrict H mem) lo hi.
Proof.
intros H mem lo hi Hlo Hhi HP. split; [exact Hlo|]. split; [exact Hhi|].
intros a Ha. destruct (HP a Ha) as (HH & b & Hb).
assert (Em : mrestrict H mem (Mem.wa a) = Some b).
{ unfold mrestrict, Mem.wa. rewrite HH. exact Hb. }
split.
- unfold wview. rewrite Em. discriminate.
- exists b. unfold Mem.mrd. rewrite Em. reflexivity.
Qed.

End b.
