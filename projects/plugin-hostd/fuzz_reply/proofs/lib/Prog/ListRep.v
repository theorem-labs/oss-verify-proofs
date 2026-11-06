From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayFrame HarnessRep.
Import ListNotations.
Local Open Scope Z_scope.

Definition grow_cap (n cap : Z) : Z := if n =? cap then (if cap =? 0 then 8 else 2 * cap) else cap.

Definition text_len (r : Z * list byte) : Z := Z.of_nat (length (snd r)) + 1.

Definition free_recs (b : rbound) (rs : list (Z * list byte)) : rbound :=
  fold_right (fun r b0 => rb_free b0 (text_len r)) b rs.

Definition free_list (b : rbound) (l : hlist) : rbound :=
  if hl_cap l =? 0 then free_recs b (hl_recs l) else rb_free (free_recs b (hl_recs l)) (16 * hl_cap l).

Definition empty_list : hlist := HL 0 0 [] [].

Section LR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Let segs := ms_segs Bm.

Definition src_home (L : layout) (A : astate) (sp s n V : Z) : Prop :=
  (sp <= s /\ s + n <= 2 ^ 64) \/
  (exists q k, In (q, k) (blocks L A) /\ q <> V /\ q <= s /\ s + n <= q + k) \/
  (0 < n /\ 0 <= s /\ s + n <= 2 ^ 64 /\ forall i, 0 <= i < n -> ro_addr segs (Z_to_bv 64 (s + i)) = true).

End LR.
