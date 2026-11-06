(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode.
Import ListNotations.
Open Scope Z_scope.
Ltac dm mo := destruct mo as [? [? ? ?] ? ? ? ? ?].
Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010=10408162934.5000001S".
induction l1 as [|[a n] l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma live_bytes_iv_subtract : forall a sz lo hi, lo <= hi ->
live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
intros a sz lo hi Hlh. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn.
- Local Ltac2 Set LiaHints.tbl := fun () => "0040=37721066392.958195669799.963760286509.98929201440.9 00000@00F00L00\S3Hlh1H2H02H12H2S1H2H0S1H2H0S3Hlh1H2H02H12H2".
rewrite (unsigned_lit (Z.min (bv_unsigned sz) (lo - bv_unsigned a))) by lia.
rewrite (unsigned_lit (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) by lia. lia.
- rewrite (unsigned_lit (Z.min (bv_unsigned sz) (lo - bv_unsigned a))) by lia. lia.
- rewrite (unsigned_lit (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) by lia. lia.
- lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma live_bytes_maps_subtract : forall maps lo hi, lo <= hi ->
live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=15047223386.329993687489.8000001007SS2IH1H".
induction maps as [|[a sz] maps IH]; intros lo hi Hlh; cbn; [lia|].
rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma live_bytes_maps_subtract_all : forall cuts maps,
live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=2937320822.6 32271520093.1000003004S1HS".
induction cuts as [|[a n] cuts IH]; intros maps; cbn; [lia|].
etransitivity; [apply IH|]. apply live_bytes_maps_subtract. pose proof (bv_unsigned_in_range 64 n). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma backing_le_live : forall mo, m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof.
intros mo Hl Hm. unfold vm_backing_used, vm_backed_maps, vm_live_bytes. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat].
rewrite Z.mul_0_l, Z.add_0_r. apply live_bytes_maps_subtract_all.
Qed.
Lemma m_vm_lazy_with_vmmaps : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m. Proof. intros h m; dm m; reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m. Proof. intros h m; dm m; reflexivity. Qed.
