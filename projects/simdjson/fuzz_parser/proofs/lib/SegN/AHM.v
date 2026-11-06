(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require PropExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec FP Image RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S.
Open Scope Z_scope.

Module AHM.
Section HM.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).

Definition hmH (M : word -> option byte) : Prop := AHEAP AI L RNGh st LB M /\ mem_inv asegs M.
Definition hmA (a : Z) : Prop := aclient_addr (aci AI) LB (2^47) a \/ (exists y, in_block LB y /\ a = shad y).
Definition hmC (lo hi : Z) : Prop := aclient_range (aci AI) LB (ATOP + 4096) lo (hi - lo).
Definition hmR (rom : word -> option byte) : Prop := rom = seg_rom asegs.

Lemma HMC_sub : forall lo hi lo' hi', hmC lo hi -> lo <= lo' -> hi' <= hi -> hmC lo' hi'.
Proof.
  intros lo hi lo' hi' H A B. unfold hmC, aclient_range, aclient_app_range in *.
  destruct H as [[H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]] | [(b & Hb & H1 & H2) | [H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]]]].
  - left. left. lia.
  - left. right. left. exists iv. split; [exact Hiv | lia].
  - left. right. right. exists c, FA, fn. split; [exact Hb | lia].
  - right. left. exists b. split; [exact Hb | lia].
  - right. right. left. lia.
  - right. right. right. left. exists iv. split; [exact Hiv | lia].
  - right. right. right. right. exists c, FA, fn. split; [exact Hb | lia].
Qed.

Lemma HMF : forall E W M M', SP.wins_client hmC E W -> hmH M -> PIosRegs.wrel asegs M M' ->
  (forall x : word, SP.outside_wins E W (bv_unsigned x) -> M' x = M x) -> hmH M'.
Proof.
  intros E W M M' HWC [HH MI] HW HO. split; [|exact (wrel_mem_inv asegs _ _ HW MI)].
  apply (AI_frame AI L RNGh st LB M M' (map (SP.win_den E) W) HH).
  - intros x Hx. apply HO. unfold SP.outside_wins. clear -Hx. induction W as [|w W IH]; [constructor|].
    cbn [map outside] in Hx. destruct (SP.win_den E w) as [lo hi] eqn:Ew. destruct Hx as [H1 H2].
    constructor; [rewrite Ew; lia | exact (IH H2)].
  - exact (wrel_wmono asegs _ _ HW).
  - unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw).
Qed.

(* [comment removed for export] *)
Lemma hmA_of_block : forall b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> hmA a.
Proof. intros b a Hb Ha. left. right. right. left. exists b. split; [exact Hb | exact Ha]. Qed.
Lemma hmA_of_ci : forall iv a, In iv (aci AI) -> fst iv <= a < snd iv -> hmA a.
Proof. intros iv a Hiv Ha. left. right. left. exists iv. split; [exact Hiv | exact Ha]. Qed.
Lemma hmA_of_stack_shadow : forall a', ATOP <= a' < 2^47 -> hmA (shad a').
Proof. intros a' Ha. left. right. right. right. exists a'. split; [left; exact Ha | reflexivity]. Qed.
Lemma hmA_of_fake_shadow : forall a', in_fake LB a' -> hmA (shad a').
Proof. intros a' Ha. left. right. right. right. exists a'. split; [right; right; exact Ha | reflexivity]. Qed.
Lemma hmA_of_ci_shadow : forall a', in_ranges (aci AI) a' -> hmA (shad a').
Proof. intros a' Ha. left. right. right. right. exists a'. split; [right; left; exact Ha | reflexivity]. Qed.
Lemma hmA_of_block_shadow : forall a', in_block LB a' -> hmA (shad a').
Proof. intros a' Ha. right. exists a'. split; [exact Ha | reflexivity]. Qed.

(* [comment removed for export] *)
Definition hmF : ExecF.footprint := RNGh.
Definition hmS (s n : Z) : Prop := ATOP + 4096 <= s - n /\ s <= al_top L /\ rng RNGh (s - n) (al_top L - (s - n)).
Lemma HMS_mono : forall s n s' n', hmS s n -> s - n <= s' - n' -> s' <= s -> hmS s' n'.
Proof.
  intros s n s' n' (H1 & H2 & H3) A B. split; [lia|]. split; [lia|].
  apply (rng_sub RNGh (s - n) (al_top L - (s - n))); [exact H3 | lia | lia].
Qed.
Lemma hmS_stack : forall s n sp lo, hmS s n -> s - n <= lo -> sp <= s ->
  ATOP + 4096 <= lo /\ sp <= al_top L /\ rng RNGh lo (al_top L - lo).
Proof.
  intros s n sp lo (H1 & H2 & H3) A B. split; [lia|]. split; [lia|].
  apply (rng_sub RNGh (s - n) (al_top L - (s - n))); [exact H3 | lia | lia].
Qed.
End HM.
End AHM.
