(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngWk.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngMWP MngMWQ MngMW0 AXG_ffstep MngL4 AXG_am8 AXG_asq AXG_asw AXG_mwc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma HFORB_P : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB_P -> ranges_disjoint (a, n) (0x10000, 0x89000).
Proof.
  intros a n Hn H. unfold FORB_P in H. rewrite Forall_forall in H.
  pose proof (H (0x10000, 0x12000) ltac:(left; reflexivity)) as D1.
  pose proof (H (0x22000, 0x40000) ltac:(right; left; reflexivity)) as D2.
  pose proof (H (0x62000, 0x4000) ltac:(right; right; left; reflexivity)) as D3.
  pose proof (H (0x66000, 0x33000) ltac:(right; right; right; left; reflexivity)) as D4.
  unfold ranges_disjoint in *. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Definition mw_pre (HTOP : Z) (L : layout) (s : astate) (m : word -> option byte) (regs : bvmap 5 word) (n : Z) : Prop :=
  Heap0 L s m /\ (forall c, 0 <= c < 48 -> usage_of s c < 2^40) /\ ly_ctx L = 0x97c98 /\ rgeoA HTOP L s /\ rdisj L s /\
  HTOP <= 2^47 /\ 2^20 <= HTOP /\ MENV m /\
  getr regs 10 = wa n /\
  bv_unsigned (getr regs 2) mod 16 = 0 /\ bv_unsigned (getr regs 2) <= 2^47 /\ HTOP <= bv_unsigned (getr regs 2) - 8192 /\
  stk_ok SEGS m (getr regs 2) 8192 /\
  PGSZ <= ly_brk0 L /\ ly_brk0 L mod PGSZ = 0 /\ ly_brk0 L <= HTOP /\
  (st_init_done s = true \/ AMI L m (bv_unsigned (getr regs 2))).

(* [comment removed for export] *)
Definition direct_wk_stmt {fx : FPState} : Prop :=
  forall FORB, (forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x89000)) ->
  forall HTOP rom L s m (regs : bvmap 5 word) n,
  mw_pre HTOP L s m regs n -> 131052 <= n <= 2^26 ->
  wk SEGS FORB HTOP rom L regs (wa 0x530c8) m (malloc n s) (mw_post HTOP regs m L s).

Section MWK.
Context {fx : FPState}.
Hypothesis DIRWK : @direct_wk_stmt fx.

#[using="DIRWK"] Theorem malloc_wk : forall HTOP rom L s m (regs : bvmap 5 word) n,
  mw_pre HTOP L s m regs n -> 1 <= n <= 2^26 ->
  wk SEGS FORB_P HTOP rom L regs (wa 0x530c8) m (malloc n s) (mw_post HTOP regs m L s).
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0).
  intros HTOP rom L s m regs n P Hn.
  destruct (Z_le_gt_dec n 131051) as [Hc|Hd].
  - destruct P as (H0 & HUS & Hctx & HG & HD & HTB & HT20 & HME & HR10 & Hsp16 & Hsp47 & Htop & HSTK & B1 & B2 & B3 & Hini).
    exact (class_wk FORB_P HTOP rom HFORB_P (@as_wk fx) L s m regs n H0 HUS Hctx HG HD HTB HT20 HME ltac:(lia) HR10 Hsp16 Hsp47 Htop HSTK B1 B2 B3 Hini).
  - exact (DIRWK FORB_P HFORB_P HTOP rom L s m regs n P ltac:(lia)).
Qed.
End MWK.
