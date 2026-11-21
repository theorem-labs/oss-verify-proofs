(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS8 Require PImgRun.  (* a worker (A1) miss kit *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Frame OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8TargetPre OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8World.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS8 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrRulesS8.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP8 Require Import S8HBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma wview_above {RCa1 : RunCtx}  : forall (m : word -> option byte) a, 0x94000 <= a < 2^64 -> wview (run_segments psegs rc_inp rc_sp rc_mb) m (wa a) = m (wa a).
Proof.
  (* a worker (A1) route (A): over the run the vDSO pair is read-only, so off the image the writable view is the
     overlay *)
  intros m a Ha. apply PImgRun.run_ref_wview_overlay. rewrite wa_unsigned by lia. lia.
Qed.

Lemma stk_of_store_ok {RCa1 : RunCtx}  : forall (m : word -> option byte) lo hi, 0x94000 <= lo -> hi <= 2^64 ->
  (forall a, lo <= a < hi -> store_ok (run_segments psegs rc_inp rc_sp rc_mb) m (wa a) 1 = true) -> stk (run_segments psegs rc_inp rc_sp rc_mb) m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as S. cbn [store_ok] in S.
  destruct (wview (run_segments psegs rc_inp rc_sp rc_mb) m (wa a)) as [b|] eqn:E; [|discriminate].
  split; [congruence|]. rewrite wview_above in E by lia. exists b. unfold mrd. rewrite E. reflexivity.
Qed.

Lemma stk_of_stack_writable {RCa1 : RunCtx}  : forall M sp0 hi, 0x94000 + 8388608 <= sp0 -> sp0 <= 2^64 -> hi <= sp0 ->
  S8TargetPre.stack_writableZ M sp0 -> stk (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 6144513) hi.
Proof.
  intros M sp0 hi H0 H1 Hhi SW. apply stk_of_store_ok; [lia | lia |]. intros a Ha.
  specialize (SW (a - (sp0 - 6144513)) 1%nat ltac:(lia) ltac:(lia)).
  replace (sp0 - 6144513 + (a - (sp0 - 6144513))) with a in SW by lia. exact SW.
Qed.

(* [comment removed for export] *)
Lemma pristine_word : forall (M : word -> option byte) lo hi,
  (forall a : Z, lo <= a < hi -> M (Z_to_bv 64 a) = None) ->
  forall w : word, lo <= bv_unsigned w < hi -> M w = None.
Proof. intros M lo hi H w Hw. rewrite <- (Z_to_bv_bv_unsigned w). apply H. exact Hw. Qed.

(* [comment removed for export] *)
Lemma mrd_of_rdn1 {RCa1 : RunCtx}  : forall (M : word -> option byte) (a : word) n b bs,
  rdn (run_segments psegs rc_inp rc_sp rc_mb) M a (S n) = Some (b :: bs) -> mrd (run_segments psegs rc_inp rc_sp rc_mb) M a = Some b /\ rdn (run_segments psegs rc_inp rc_sp rc_mb) M (a + 1)%bv n = Some bs.
Proof.
  intros M a n b bs H. rewrite rdn_unfold in H. unfold mrd in *.
  destruct (match M a with Some b0 => Some b0 | None => seg_rom (run_segments psegs rc_inp rc_sp rc_mb) a end) as [b0|]; [|discriminate].
  destruct (rdn (run_segments psegs rc_inp rc_sp rc_mb) M (a + 1)%bv n) as [r|]; [|discriminate]. injection H as -> ->. split; reflexivity.
Qed.

Lemma bytes_at_of_rdn {RCa1 : RunCtx}  : forall n (M : word -> option byte) A bs,
  rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa A) n = Some bs -> 0 <= A -> A + Z.of_nat n <= 2^64 -> bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M A bs.
Proof.
  induction n as [|n IH]; intros M A bs H HA Hn.
  - cbn in H. injection H as <-. apply bytes_at_nil. lia.
  - destruct bs as [|b bs].
    { rewrite rdn_unfold in H. destruct (mrd (run_segments psegs rc_inp rc_sp rc_mb) M (wa A)); [|discriminate].
      destruct (rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa A + 1)%bv n); discriminate. }
    apply mrd_of_rdn1 in H. destruct H as [H1 H2]. rewrite wa_succ in H2.
    pose proof (IH M (A + 1) bs H2 ltac:(lia) ltac:(lia)) as (B1 & B2 & B3).
    pose proof (OP.rdn_length _ _ _ _ _ H2) as L.
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
    + cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact H1.
    + cbn [nth_error]. cbn [length] in Hi. rewrite <- (B3 i ltac:(lia)). f_equal. f_equal. lia.
Qed.

Lemma wr_at_of_store_ok {RCa1 : RunCtx}  : forall (M : word -> option byte) A (n : nat),
  0 <= A -> A + Z.of_nat n <= 2^64 -> store_ok (run_segments psegs rc_inp rc_sp rc_mb) M (wa A) n = true -> wr_at (run_segments psegs rc_inp rc_sp rc_mb) M A (Z.of_nat n).
Proof.
  intros M A n HA Hn S. split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (store_ok_wview (run_segments psegs rc_inp rc_sp rc_mb) M (wa A) n (Z.to_nat i) S ltac:(lia)) as W.
  rewrite wa_unsigned in W by lia. rewrite Z2Nat.id in W by lia. exact W.
Qed.

Lemma rw_cells_of_rdn {RCa1 : RunCtx}  : forall (M : word -> option byte) A (n : nat) bs,
  rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa A) n = Some bs -> store_ok (run_segments psegs rc_inp rc_sp rc_mb) M (wa A) n = true -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A [CB n bs].
Proof.
  intros M A n bs H S HA Hn. pose proof (OP.rdn_length _ _ _ _ _ H) as L.
  split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. eapply bytes_at_of_rdn; eassumption.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. apply wr_at_of_store_ok; assumption.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_stk {RCa1 : RunCtx}  : forall (M : word -> option byte) lo hi a (n : nat),
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo hi -> lo <= a -> a + Z.of_nat n <= hi -> store_ok (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) n = true.
Proof.
  intros M lo hi a n (H0 & H1 & H) Ha Hn.
  assert (W : wr_at (run_segments psegs rc_inp rc_sp rc_mb) M a (Z.of_nat n)).
  { split; [lia|]. split; [lia|]. intros i Hi. apply (H (a + i)). lia. }
  pose proof (wr_at_store_ok (run_segments psegs rc_inp rc_sp rc_mb) M a (Z.of_nat n) 0 n W ltac:(lia) ltac:(lia)) as X.
  rewrite Z.add_0_r in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma stk_wmono {RCa1 : RunCtx}  : forall (M M' : word -> option byte) lo hi,
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo hi -> 0x94000 <= lo -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo hi.
Proof.
  intros M M' lo hi (H0 & H1 & H) Hlo WM. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W _]. pose proof (WM _ W) as W'. split; [exact W'|].
  rewrite wview_above in W' by lia. unfold mrd. destruct (M' (wa a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_cons {RCa1 : RunCtx}  : forall (M : word -> option byte) A c cs,
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A [c] -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (A + Z.of_nat (csize c)) cs -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A (c :: cs).
Proof.
  intros M A c cs H1 H2. apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M A [c] cs)). split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma rw_cell8_of_cell {RCa1 : RunCtx}  : forall (M : word -> option byte) a v,
  S8World.cell M a 8 v -> store_ok (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) 8 = true -> 0 <= a -> a + 8 <= 2^64 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M a [C8 (Z_to_bv 64 v)].
Proof.
  intros M a v C S Ha Hb. unfold S8World.cell in C.
  pose proof (rw_cells_of_rdn M a 8 _ C S Ha ltac:(lia)) as R.
  eapply rw_cells_recast; [exact R | cbn; exact (conj I I) | reflexivity | reflexivity].
Qed.
