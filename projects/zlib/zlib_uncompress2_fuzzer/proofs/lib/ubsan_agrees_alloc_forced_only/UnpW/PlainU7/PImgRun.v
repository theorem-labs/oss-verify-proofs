(* my PlainU7 twin of a worker's (A1) miss kit PlainU8/PImgRun.v (md5 ), the import and the image's bounds from PlainU7/PImg.v substituted (AgentSubmission.PlainU8 Require Import PImg. -> AgentSubmission.PlainU7 Require Import PImg.: 1; 0x75000 -> 0x75000: 7; 0x22000 -> 0x22000: 3). *)
(* the U8 TWIN of PlainS8/PImgRun.v (bounds 0x22000 / 0x75000 from PlainU8/PImg.v).
   ((A1) miss kit, port727, a worker's ruling (c)): PImg's six image-MISS facts over the
   RUN's segments.  PImg itself stays over the image.  Over the run a miss also needs the address OFF the vDSO pair
   ([RunHit.off_vdso]), except for the writable view: the pair is read-only, so [wview] still answers the overlay.
   Every proof is PImg's own image miss plus RunHit's first-match lemmas. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Image.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunHit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma run_ref_find_segment_none : forall inp sp mb z n, 1 <= n -> (z + n <= 0x10000 \/ 0x95000 <= z) ->
  off_vdso inp sp mb z n ->
  find_segment (run_segments psegs inp sp mb) z n = None.
Proof.
  intros inp sp mb z n Hn Hz Hoff. apply run_find_segment_none; [lia | apply ref_find_segment_none; assumption | exact Hoff].
Qed.

Lemma run_ref_ro_addr_false : forall inp sp mb (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x95000 <= bv_unsigned x)%Z -> off_vdso inp sp mb (bv_unsigned x) 1 ->
  ro_addr (run_segments psegs inp sp mb) x = false.
Proof. intros inp sp mb x Hx Hoff. unfold ro_addr. rewrite run_ref_find_segment_none by (assumption || lia). reflexivity. Qed.

Lemma run_ref_memory_read_none : forall inp sp mb (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x95000 <= bv_unsigned x)%Z ->
  off_vdso inp sp mb (bv_unsigned x) (Z.of_N n) ->
  memory_read (run_segments psegs inp sp mb) x n = None.
Proof. intros inp sp mb x n Hn Hx Hoff. unfold memory_read. rewrite run_ref_find_segment_none by (assumption || lia). reflexivity. Qed.

(** No pair premise: the pair is read-only. *)
Lemma run_ref_wview_overlay : forall inp sp mb m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x95000 <= bv_unsigned x)%Z -> wview (run_segments psegs inp sp mb) m x = m x.
Proof. intros inp sp mb m x Hx. apply run_wview_miss. apply ref_find_segment_none; lia. Qed.

Lemma run_ref_seg_rom_none : forall inp sp mb (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x95000 <= bv_unsigned x)%Z -> off_vdso inp sp mb (bv_unsigned x) 1 ->
  seg_rom (run_segments psegs inp sp mb) x = None.
Proof. intros inp sp mb x Hx Hoff. unfold seg_rom. rewrite run_ref_memory_read_none by (cbn; assumption || lia). reflexivity. Qed.

Lemma run_ref_mrd_overlay : forall inp sp mb m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x95000 <= bv_unsigned x)%Z -> off_vdso inp sp mb (bv_unsigned x) 1 ->
  mrd (run_segments psegs inp sp mb) m x = m x.
Proof.
  intros inp sp mb m x Hx Hoff. unfold mrd. destruct (m x); [reflexivity|]. apply run_ref_seg_rom_none; assumption.
Qed.

(** A HIT in the image's read-only range is the run's (first match): no pair premise (whole1, S8SoOk). *)
Lemma run_p_ro_addr_in : forall inp sp mb (a : word), (0x10000 <= bv_unsigned a < 0x22000)%Z ->
  ro_addr (run_segments psegs inp sp mb) a = ro_addr psegs a.
Proof.
  intros inp sp mb a Ha. pose proof (p_ro_addr a) as P. unfold ro_addr in P |- *.
  destruct (find_segment psegs (bv_unsigned a) 1) as [s|] eqn:E.
  - unfold run_segments. rewrite (find_segment_app_hit _ _ _ _ _ E). reflexivity.
  - exfalso. destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.ltb_spec0 (bv_unsigned a) 0x22000);
      cbn in P; try discriminate P; lia.
Qed.

(** An overlay byte needs no pair premise either (the read view is overlay-first). *)
Lemma run_mrd_overlay_some : forall segs m (x : word) b, m x = Some b -> mrd segs m x = Some b.
Proof. intros segs m x b H. unfold mrd. rewrite H. reflexivity. Qed.
