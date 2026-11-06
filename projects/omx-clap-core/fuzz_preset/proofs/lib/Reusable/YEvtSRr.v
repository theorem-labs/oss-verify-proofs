(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (PresetStr, c-libc-stdio lane): the bridge from a K-kit machine walk (`evt` over a
   machine_state) to cgif_file's call-site form (`SRr segs W (cfg_at segs pc regs mem md) POST`). PORTED, not new:

   DONOR: origin/cold/port-fm-rtscan 10d0c5cd0be, proofs/omx-clap-core/fuzz_manifest/lib/A/FMbz_bridge.v (port-fm's
   RtScan; blob 7449bf6e). Its three lemmas, ported in that order:
     bz_msteps_tfib   FMbz_bridge.v:32-37   a kit `msteps` is cgif's `msteps` (YK0i.v:284)
     srr_of_evt       FMbz_bridge.v:46-58   a kit `evt` walk from the restricted state gives SRr, through cgif's own
                                            SRr_msteps (YA0n.v) and SRr_ret
     stk_of_apresent  FMbz_bridge.v:61-73   cgif's stack-presence premise gives the kit's `Frame.stk`
   The donor's recorded build is rc=0 (its commit f8664b31b9c); I did not re-run it.
   fuzz_state carries a copy (origin/cold/port-state-rt-str 17818dd9abc lib/A/FSbz_bridge.v).

   WHAT CHANGED, so this file can be diffed against the donor:
   - SEGS-GENERIC. The donor states all three lemmas over its image: `Exec.msteps asegs`, `SRr tfibsegs`,
     `Frame.stk asegs`, with `asegs = tfibsegs` by reflexivity in its unit (FMbz_str.v:26). Here each takes
     `segs : list Segment` as a Section Variable instead. ALL THREE needed the parameter: none was generic in its
     statement. None needed it in its PROOF: the proof scripts are the donor's, with `tfibsegs` / `asegs` replaced by
     `segs` and nothing else.
   - THREE KITS. The donor has one kit (its lib/A/Bz, bzip2's). This unit has three whose `mstep` / `msteps` / `evt`
     texts are identical (measured: definitions compared after module paths are normalised): lib/K/Lib/Exec.v
     (bzip2's, the donor's own kit), lib/K5/Lib/Exec.v (leptonica's) and lib/Lib/Exec.v (this unit's). So each lemma
     is stated once per kit: the bzip2-kit ones keep the donor's names; the other two add a suffix (_K5, _Lib).
   - Module paths: fuzz_manifest -> fuzz_preset. The donor's `From ...lib.A Require Import AB1v` and `...A.Bz.Lib
     Require Import ImageA` / `FMbz_str` are dropped: they supply only the donor's image names.
   NO PREMISE ADDED. `Hwx : wx_segs_nowrap segs` is the donor's own premise (SRr_msteps needs it); the caller supplies
   it for its image. No image value, address or unit constant appears in this file.

   rule 24 record. Not in the released set (proof-index v5 built 2026-10-28T21:58:24Z, rc=1 read directly; and
   no released unit carries both a kit Exec.v and cgif's YA0n.v). Cold grep 2026-10-28T23:38Z over the 9,176
   refs/remotes/origin/cold refs (152,121 unique .v blobs of the 14 units carrying both): found the donor above. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK04 YK0i YK14 YK1b YK1a YK18 YP09 YP02 YG0n YG00 YG0a YG01 YG0f YG0d YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib Require Exec Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Exec Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Exec Mem Frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module KE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Exec.
Module KM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Mem.
Module KF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Frame.
Module LE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Exec.
Module LM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Mem.
Module LF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Frame.
Module UE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Exec.
Module UM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.
Module UF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Frame.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* ---- the bzip2 kit (lib/K), the donor's own kit: donor names ---- *)

(* FMbz_bridge.v:32-37 *)
Lemma bz_msteps_tfib : forall ms ms', KE.msteps segs ms ms' -> YK0i.msteps segs ms ms'.
Proof.
intros ms ms' H. induction H as [ms | ms ms1 ms2 Hstep _ IH].
- apply YK0i.mst_refl.
- destruct Hstep as [Hsvc Hok]. eapply YK0i.mst_step; [exact Hsvc | exact Hok | exact IH].
Qed.

(* FMbz_bridge.v:46-58 *)
Lemma srr_of_evt : forall (Hwx : wx_segs_nowrap segs) (W : world segs) (pc : Z) regs mem md
(Q : machine_state -> Prop) (POST : world segs -> config -> Prop),
KE.evt segs Q (restrict (w_H W) (YK11.mkst regs (w64 pc) mem (YK11.seg_rom segs))) ->
(forall ms' model', Q ms' -> same_but_materialized md model' -> hclean (w_H W) ms' ->
POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
SRr segs W (cfg_at segs pc regs mem md) POST.
Proof.
intros Hwx W pc regs mem md Q POST (ms' & Hms & HQ) HK.
unfold cfg_at.
eapply (SRr_msteps segs Hwx W (YK11.mkst regs (w64 pc) mem (YK11.seg_rom segs)) ms' md POST).
- exact (bz_msteps_tfib _ _ Hms).
- intros model' Hsame Hcl. apply SRr_ret. cbn [ms_mem YK11.mkst]. exact (HK ms' model' HQ Hsame Hcl).
Qed.

(* FMbz_bridge.v:61-73 *)
Lemma stk_of_apresent : forall (H : word -> bool) (mem : word -> option byte) (lo hi : Z),
0 <= lo -> hi <= 2 ^ 64 ->
(forall a, lo <= a < hi -> apresent H mem a) ->
KF.stk segs (mrestrict H mem) lo hi.
Proof.
intros H mem lo hi Hlo Hhi HP. split; [exact Hlo|]. split; [exact Hhi|].
intros a Ha. destruct (HP a Ha) as (HH & b & Hb).
assert (Em : mrestrict H mem (KM.wa a) = Some b).
{ unfold mrestrict, KM.wa. rewrite HH. exact Hb. }
split.
- unfold wview. rewrite Em. discriminate.
- exists b. unfold KM.mrd. rewrite Em. reflexivity.
Qed.

(* ---- the leptonica kit (lib/K5): the same three, the same proofs ---- *)

Lemma bz_msteps_tfib_K5 : forall ms ms', LE.msteps segs ms ms' -> YK0i.msteps segs ms ms'.
Proof.
intros ms ms' H. induction H as [ms | ms ms1 ms2 Hstep _ IH].
- apply YK0i.mst_refl.
- destruct Hstep as [Hsvc Hok]. eapply YK0i.mst_step; [exact Hsvc | exact Hok | exact IH].
Qed.

Lemma srr_of_evt_K5 : forall (Hwx : wx_segs_nowrap segs) (W : world segs) (pc : Z) regs mem md
(Q : machine_state -> Prop) (POST : world segs -> config -> Prop),
LE.evt segs Q (restrict (w_H W) (YK11.mkst regs (w64 pc) mem (YK11.seg_rom segs))) ->
(forall ms' model', Q ms' -> same_but_materialized md model' -> hclean (w_H W) ms' ->
POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
SRr segs W (cfg_at segs pc regs mem md) POST.
Proof.
intros Hwx W pc regs mem md Q POST (ms' & Hms & HQ) HK.
unfold cfg_at.
eapply (SRr_msteps segs Hwx W (YK11.mkst regs (w64 pc) mem (YK11.seg_rom segs)) ms' md POST).
- exact (bz_msteps_tfib_K5 _ _ Hms).
- intros model' Hsame Hcl. apply SRr_ret. cbn [ms_mem YK11.mkst]. exact (HK ms' model' HQ Hsame Hcl).
Qed.

Lemma stk_of_apresent_K5 : forall (H : word -> bool) (mem : word -> option byte) (lo hi : Z),
0 <= lo -> hi <= 2 ^ 64 ->
(forall a, lo <= a < hi -> apresent H mem a) ->
LF.stk segs (mrestrict H mem) lo hi.
Proof.
intros H mem lo hi Hlo Hhi HP. split; [exact Hlo|]. split; [exact Hhi|].
intros a Ha. destruct (HP a Ha) as (HH & b & Hb).
assert (Em : mrestrict H mem (LM.wa a) = Some b).
{ unfold mrestrict, LM.wa. rewrite HH. exact Hb. }
split.
- unfold wview. rewrite Em. discriminate.
- exists b. unfold LM.mrd. rewrite Em. reflexivity.
Qed.

(* ---- this unit's own kit (lib/Lib): the same three, the same proofs ---- *)

Lemma bz_msteps_tfib_Lib : forall ms ms', UE.msteps segs ms ms' -> YK0i.msteps segs ms ms'.
Proof.
intros ms ms' H. induction H as [ms | ms ms1 ms2 Hstep _ IH].
- apply YK0i.mst_refl.
- destruct Hstep as [Hsvc Hok]. eapply YK0i.mst_step; [exact Hsvc | exact Hok | exact IH].
Qed.

Lemma srr_of_evt_Lib : forall (Hwx : wx_segs_nowrap segs) (W : world segs) (pc : Z) regs mem md
(Q : machine_state -> Prop) (POST : world segs -> config -> Prop),
UE.evt segs Q (restrict (w_H W) (YK11.mkst regs (w64 pc) mem (YK11.seg_rom segs))) ->
(forall ms' model', Q ms' -> same_but_materialized md model' -> hclean (w_H W) ms' ->
POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
SRr segs W (cfg_at segs pc regs mem md) POST.
Proof.
intros Hwx W pc regs mem md Q POST (ms' & Hms & HQ) HK.
unfold cfg_at.
eapply (SRr_msteps segs Hwx W (YK11.mkst regs (w64 pc) mem (YK11.seg_rom segs)) ms' md POST).
- exact (bz_msteps_tfib_Lib _ _ Hms).
- intros model' Hsame Hcl. apply SRr_ret. cbn [ms_mem YK11.mkst]. exact (HK ms' model' HQ Hsame Hcl).
Qed.

Lemma stk_of_apresent_Lib : forall (H : word -> bool) (mem : word -> option byte) (lo hi : Z),
0 <= lo -> hi <= 2 ^ 64 ->
(forall a, lo <= a < hi -> apresent H mem a) ->
UF.stk segs (mrestrict H mem) lo hi.
Proof.
intros H mem lo hi Hlo Hhi HP. split; [exact Hlo|]. split; [exact Hhi|].
intros a Ha. destruct (HP a Ha) as (HH & b & Hb).
assert (Em : mrestrict H mem (UM.wa a) = Some b).
{ unfold mrestrict, UM.wa. rewrite HH. exact Hb. }
split.
- unfold wview. rewrite Em. discriminate.
- exists b. unfold UM.mrd. rewrite Em. reflexivity.
Qed.

End b.
