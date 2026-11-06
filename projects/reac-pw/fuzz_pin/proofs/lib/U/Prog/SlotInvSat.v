(* Satisfiability of the slot entry invariant of reac-pw/fuzz_pin LLVMFuzzerTestOneInput (UBSan): SlotInv.Inv_ENTRY
   (U/Prog/SlotInv.v:199-205) holds of a concrete state at the frame's REAL instance, the one
   U/FrameProof.frame_ubsan_holds exhibits (B = src0_msyms, APIf = @zlib_API, SH = src0_sink_head, SK = src0_sink,
   ra = RA_LIB, empty = EMPTY, all of lib/U), with the real allocator relation aa_MR (@zlib_API rc) =
   U/Reusable/YN2b.MRx src0_msyms. The plain file (lib/Prog/SlotInvSat.v) with the UBSan image's numbers.

   This file proves no program function: it is a satisfiability audit of a contract premise (the stream rule
   `CHECK A CONTRACT BEFORE PROVERS USE IT`). Nothing here is an Axiom, a Parameter, an admit or an Admitted.

   The witness.
   - rc: the frame quantifies over every RunCeil and FPState; the witness takes the RunCeil the frame's own run
     takes (U/ZComplete.v:78: RunCeilOf (bv_unsigned sp) _ lim_source) at the entry sp W_SP0 = 0x7fffffff0000, so
     alloc_ceiling = run_ceil W_SP0 = 0x7fffff7f0000, rc_lim = lim_source; fx is YK11.fx0, the start-up FP state.
   - model: U/Reusable/YL0k.MD0, the frame's own at-main model (init_model at the entry sp, brk = the image's
     reserved top, mmap base = mmap_base_max, lim_source; tid 2; an input with argv ["p"]).
   - allocator: init_state with st_init_done set (set_init_done true init_state): the state mallocng's alloc_meta
     leaves when it has done its init step (ctx.init_done = 1, secret 0) and taken no memory, built by the
     allocator's own lemmas: MRx at init_state (YN03.MRc_init, YN2b.ledger_x_init, from heap_pristine of the
     at-main memory), then YN2m.post_fail0 (the init-done step with only ctx.init_done written).
   - input: the EMPTY input (n = 0, p = EMPTY). A non-empty input needs a live user block in the allocator state,
     i.e. a forward malloc run of the real allocator; the empty input's witness exercises every conjunct of
     Inv_ENTRY except the n > 0 disjunct of GV / lib_pre.
   - memory: the stack [alloc_ceiling, W_SP0) and the musl statics the allocator relation reads (ctx, lock,
     need_locks, page_size, the stack-guard GOT slot and the guard, errno, the stdio lock / open-file list fields
     of sink_none) hold explicit bytes; every other byte reads the image (None). sbound: SB 0 0 CAPMAX. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import
  YK11 YM05 YO0i YO0f YO0d YO0j YO0m YO04 YO0s YH00 YH02 YN03 YN2b YN2h YN2m YN31 YL00 YL0g YL0s YL0k YI14 YI16
  YI5b YI5c YM0b YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require YN0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import
  ZAllocator AllocSlots AllocRoom AllocSI AllocGS AllocMB FrameAPI Contract MemNorm Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import SlotInv.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The run's numbers.                                                                                           *)
(* ---------------------------------------------------------------------------------------------------------- *)

Definition W_SP0 : Z := 0x7fffffff0000.
Lemma W_SP0_win : sp_window_lo <= W_SP0 <= sp_window_hi.
Proof. unfold W_SP0, sp_window_lo, sp_window_hi. lia. Qed.
Definition W_RC : RunCeil := RunCeilOf W_SP0 W_SP0_win Budgets.Standard.lim_source.
#[local] Existing Instance W_RC.
#[local] Existing Instance YK11.fx0.

Lemma W_ceil : @alloc_ceiling W_RC = 0x7fffff7f0000.
Proof. vm_compute. reflexivity. Qed.

(* The slot's entry sp: one page below the process entry sp. *)
Definition W_S : Z := 0x7ffffffef000.
Definition W_BRK : Z := Eval vm_compute in reserved_top (segments_reserved src0segs).
Definition W_MBASE : Z := mmap_base_max.
Definition W_INP : ProcInput :=
  mkProcInput [[Z_to_bv 8 112]] [] [] (stream_const (Z_to_bv 8 0)) (Z_to_bv 64 1000) (Z_to_bv 64 1000) []
    net_silent (Z_to_bv 64 1024) (Z_to_bv 64 0) hwcap_rv64gc false Sv48.
Definition W_MD : Model :=
  MD0 (Z_to_bv 64 2) (Z_to_bv 64 W_BRK) (Z_to_bv 64 W_MBASE) (Z_to_bv 64 W_SP0) Budgets.Standard.lim_source W_INP.

Lemma W_MD_vm : m_vmmaps W_MD =
  mkVmMapsFull (segments_reserved src0segs) [] [] (Z_to_bv 64 W_BRK) (Z_to_bv 64 W_BRK) Budgets.Standard.lim_source
    (Z_to_bv 64 W_MBASE) (Z_to_bv 64 W_SP0).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The memory.                                                                                                  *)
(* ---------------------------------------------------------------------------------------------------------- *)

Definition rng (lo len x : Z) : bool := (lo <=? x) && (x <? lo + len).
Lemma rng_t : forall lo len x, lo <= x < lo + len -> rng lo len x = true.
Proof. intros lo len x H. unfold rng. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma rng_f : forall lo len x, ~ (lo <= x < lo + len) -> rng lo len x = false.
Proof.
  intros lo len x H. unfold rng. apply andb_false_iff.
  destruct (Z.leb_spec lo x); [right; apply Z.ltb_ge; lia | left; reflexivity].
Qed.
Ltac rng_solve :=
  repeat match goal with
  | |- context [rng ?lo ?len ?x] =>
      first [ rewrite (rng_t lo len x) by lia | rewrite (rng_f lo len x) by lia ]
  | |- context [?x =? ?c] =>
      first [ rewrite (proj2 (Z.eqb_eq x c)) by lia | rewrite (proj2 (Z.eqb_neq x c)) by lia ]
  end.

(* The byte values (as Z) of the explicit part of the memory; addresses (UBSan image, U/Reusable/YH03.v):
   [0x7fffff7f0000, W_SP0) the stack; ctx 0x4ec18 (CTX_SIZE 928); malloc lock 0x4ec10 (4); __libc 0x4eba0:
   threaded +1, need_locks +3, page_size +48 (8 bytes, 4096); the stack-guard GOT slot 0x1d590 (the guard's address
   0x4eb80, 8 bytes); the guard 0x4eb80 (8); errno tp - 164 = 0x2e86c (4); ofl_lock 0x4efc8 (4); ofl_head 0x4efd0
   (8). *)
Definition wm0 (x : Z) : option Z :=
  if rng 0x7fffff7f0000 0x800000 x then Some 0
  else if rng 0x4ec18 928 x then Some 0
  else if rng 0x4ec10 4 x then Some 0
  else if rng 0x4eba1 1 x then Some 0
  else if rng 0x4eba3 1 x then Some 0
  else if rng 0x4ebd0 8 x then Some (le_byte 4096 8 (Z.to_nat (x - 0x4ebd0)))
  else if rng 0x1d590 8 x then Some (le_byte 0x4eb80 8 (Z.to_nat (x - 0x1d590)))
  else if rng 0x4eb80 8 x then Some 0
  else if rng 0x2e86c 4 x then Some 0
  else if rng 0x4efc8 4 x then Some 0
  else if rng 0x4efd0 8 x then Some 0
  else None.

(* The at-main memory (heap pristine: ctx all zero) and the post-init memory (ctx.init_done = 1 at ctx + 8). *)
Definition W_MEM0 (a : word) : option byte := option_map (Z_to_bv 8) (wm0 (bv_unsigned a)).
Definition W_MEM (a : word) : option byte :=
  if bv_unsigned a =? 0x4ec18 + 8 then Some (Z_to_bv 8 1) else W_MEM0 a.

Lemma bu64 : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. exact Hx.
Qed.

Lemma W_MEM0_at : forall x, 0 <= x < 2 ^ 64 -> W_MEM0 (Z_to_bv 64 x) = option_map (Z_to_bv 8) (wm0 x).
Proof. intros x Hx. unfold W_MEM0. rewrite bu64 by exact Hx. reflexivity. Qed.

Lemma W_MEM_at : forall x, 0 <= x < 2 ^ 64 -> W_MEM (Z_to_bv 64 x) =
  if x =? 0x4ec18 + 8 then Some (Z_to_bv 8 1) else option_map (Z_to_bv 8) (wm0 x).
Proof. intros x Hx. unfold W_MEM. rewrite bu64 by exact Hx. rewrite W_MEM0_at by exact Hx. reflexivity. Qed.

(* Below the RELRO end every byte but the GOT guard slot reads the image. *)
Lemma wm0_low : forall x, (0 <= x < 0x1d590 \/ 0x1d598 <= x < 0x1d5a8) -> wm0 x = None.
Proof. intros x Hx. unfold wm0. rng_solve. reflexivity. Qed.

Lemma W_MEM_low : forall a : word, bv_unsigned a < 0x1d590 -> W_MEM a = None.
Proof.
  intros a Ha. pose proof (u64_range a) as R.
  unfold W_MEM, W_MEM0. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite wm0_low by lia. reflexivity.
Qed.

Lemma W_MEM_low_Z : forall x, (0 <= x < 0x1d590 \/ 0x1d598 <= x < 0x1d5a8) -> W_MEM (Z_to_bv 64 x) = None.
Proof.
  intros x Hx. rewrite W_MEM_at by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite wm0_low by exact Hx.
  reflexivity.
Qed.

Lemma W_MEM0_low_Z : forall x, (0 <= x < 0x1d590 \/ 0x1d598 <= x < 0x1d5a8) -> W_MEM0 (Z_to_bv 64 x) = None.
Proof. intros x Hx. rewrite W_MEM0_at by lia. rewrite wm0_low by exact Hx. reflexivity. Qed.

(* The read-only segments of the image end below 0x1c000. *)
Lemma src0_ro_low : forall s, In s src0segs -> seg_writable s = false ->
  Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x1c000.
Proof.
  intros s Hin Hw.
  assert (H : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x1c000)) src0segs
              = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). rewrite Hw in H. cbn [orb] in H. apply Z.leb_le. exact H.
Qed.

Lemma find_segment_spec : forall segs x n s, find_segment segs x n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= x /\ x + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|sg r IH]; intros x n s H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) x) as [Hb1|Hb1];
    destruct (Z.leb_spec (x + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) as [Hb2|Hb2];
    cbn [andb] in H.
  - injection H as <-. split; [left; reflexivity | lia].
  - destruct (IH x n s H) as (Hi1 & Hi2). split; [right; exact Hi1 | exact Hi2].
  - destruct (IH x n s H) as (Hi1 & Hi2). split; [right; exact Hi1 | exact Hi2].
  - destruct (IH x n s H) as (Hi1 & Hi2). split; [right; exact Hi1 | exact Hi2].
Qed.

Lemma ro_addr_low : forall a, ro_addr src0segs a = true -> bv_unsigned a < 0x1c000.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment src0segs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate].
  destruct (find_segment_spec _ _ _ _ E) as (Hin & H1 & H2).
  assert (Hw : seg_writable s = false) by (destruct (seg_writable s); [discriminate | reflexivity]).
  pose proof (src0_ro_low s Hin Hw). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* heap_pristine at the at-main memory, MRx at init_state.                                                       *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma W_tables : forall a,
  (ms_debruijn src0_msyms - 108 <= a < ms_debruijn src0_msyms + Z.max 32 (ms_debruijn_len src0_msyms) \/
   ms_size_classes src0_msyms <= a < ms_size_classes src0_msyms + 96 \/
   ms_small_cnt src0_msyms <= a < ms_small_cnt src0_msyms + 27 \/ ms_med_cnt src0_msyms <= a < ms_med_cnt src0_msyms + 4) ->
  0 <= a < 0x1d590.
Proof.
  intros a Ha.
  change (ms_debruijn src0_msyms) with 0x10547 in Ha. change (ms_debruijn_len src0_msyms) with 33 in Ha.
  change (ms_size_classes src0_msyms) with 0x10568 in Ha. change (ms_small_cnt src0_msyms) with 0x105c8 in Ha.
  change (ms_med_cnt src0_msyms) with 0x105e3 in Ha. lia.
Qed.

Lemma W_pristine : heap_pristine src0_msyms W_MEM0 W_MD.
Proof.
  assert (S : forall x v, 0 <= x < 2 ^ 64 -> wm0 x = Some v -> mbyte (ms_segs src0_msyms) W_MEM0 x = Some (Z_to_bv 8 v)).
  { intros x v Hx H. unfold mbyte. rewrite W_MEM0_at by exact Hx. rewrite H. reflexivity. }
  split.
  - intros i Hi. change (ms_ctx src0_msyms) with 0x4ec18. unfold CTX_SIZE in Hi.
    apply S; [lia|]. unfold wm0. rng_solve. reflexivity.
  - intros k Hk. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - vm_compute. reflexivity.
  - intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - exists 0. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - intros a Ha. pose proof (W_tables a Ha) as Hr. unfold mbyte. rewrite W_MEM0_low_Z by lia. reflexivity.
  - rewrite W_MD_vm. cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_limit].
    assert (ER : reserved_top (segments_reserved (ms_segs src0_msyms)) = W_BRK) by (vm_compute; reflexivity).
    assert (EB : bv_unsigned (Z_to_bv 64 W_BRK) = W_BRK) by (apply bu64; unfold W_BRK; lia).
    assert (EL : Budgets.Standard.lim_source = 0x400000000) by exact (proj1 standard_budgets).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold valid_brk; rewrite ER, EB; unfold W_BRK, page_size, brk_aslr_max; split; [lia|]; split; lia|].
    split; [rewrite EB, W_ceil; unfold W_BRK; lia|].
    split; [reflexivity|].
    split; [rewrite EL; unfold SRC_LIM_MIN; lia|].
    unfold vm_backing_used. rewrite W_MD_vm. vm_compute. discriminate.
  - split; [reflexivity | split; reflexivity].
  - unfold ceil_of_top, alloc_top. rewrite W_MD_vm. vm_compute. reflexivity.
  - intros i Hi. assert (E : vml_len src0_msyms = 0) by reflexivity. rewrite E in Hi. lia.
  - rewrite W_MD_vm. reflexivity.
Qed.

Definition W_L : layout := layout0 src0_msyms W_BRK 0.

Lemma W_MRx0 : MRx src0_msyms W_L init_state W_MEM0 W_MD.
Proof.
  assert (HL : W_L = layout0 src0_msyms (bv_unsigned (vm_brk (m_vmmaps W_MD))) 0).
  { rewrite W_MD_vm. cbn [vm_brk]. rewrite bu64 by (unfold W_BRK; lia). reflexivity. }
  rewrite HL. apply MRx_intro.
  - apply MRc_init; [exact src0_syms_ok | exact W_pristine | lia].
  - apply ledger_x_init; rewrite W_MD_vm; reflexivity.
  - exact rsv_ok_init.
  - exact ama_ok_init.
  - exact span_ok_init.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The post-init allocator state.                                                                               *)
(* ---------------------------------------------------------------------------------------------------------- *)

Definition W_A : astate := set_init_done true init_state.

Lemma W_A_wf : WF W_A.
Proof. exact (Inv_set_init_done [] None U0 init_state wf_init). Qed.

Lemma W_ctx_byte : forall i, 0 <= i < CTX_SIZE ->
  mbyte (ms_segs src0_msyms) W_MEM (ms_ctx src0_msyms + i) = Some (Z_to_bv 8 (if i =? 8 then 1 else 0)).
Proof.
  intros i Hi. unfold CTX_SIZE in Hi. change (ms_ctx src0_msyms) with 0x4ec18.
  unfold mbyte. rewrite W_MEM_at by lia.
  destruct (Z.eqb_spec i 8) as [->|Hne].
  - reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _)) by lia. unfold wm0. rng_solve. reflexivity.
Qed.

Ltac ctx_at_tac :=
  intros k Hk; rewrite <- Z.add_assoc; rewrite W_ctx_byte by (unfold CTX_SIZE; lia);
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.

Lemma W_ctx11 : ctx11 src0_msyms W_L W_MEM W_A.
Proof.
  unfold ctx11. repeat split; unfold ctx_at; ctx_at_tac.
Qed.

Lemma W_MRx : MRx src0_msyms W_L W_A W_MEM W_MD.
Proof.
  destruct (post_fail0 src0_msyms [] None U0 W_L init_state W_MEM0 W_MD wf_init (Xclean_nil init_state) ama_ok_init
              (proj2 init_ok) (MRx_midrep src0_msyms W_L init_state W_MEM0 W_MD W_MRx0)
              YN0i.src0_ENC YN0i.src0_ENS YN0i.src0_ERRIMG YN0i.src0_SNC W_A
              eq_refl eq_refl eq_refl (or_introl eq_refl) ltac:(repeat split; reflexivity) eq_refl eq_refl
              W_S W_MEM W_MD) as (MID & AMA & BND).
  - rewrite W_ceil. unfold AM_STACK, W_S. lia.
  - intros x Hx HW. rewrite W_MEM_at by exact Hx. rewrite W_MEM0_at by exact Hx.
    destruct (Z.eqb_spec x (0x4ec18 + 8)) as [E|E]; [|reflexivity].
    exfalso. apply HW. right. unfold ctxW. change (ms_ctx src0_msyms) with 0x4ec18. lia.
  - exact W_ctx11.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (midrep_MRx src0_msyms W_L W_A W_MEM W_MD MID W_A_wf BND); [| exact AMA |].
    + intros g am i fr Hin. cbn in Hin. destruct Hin.
    + intros g am H. unfold MT, W_A, set_init_done, init_state in H. cbn in H. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The resources.                                                                                               *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma W_res : res_ok_slots W_A (SB 0 0 CAPMAX).
Proof.
  assert (NU : forall X g am, ~ usedX X W_A g am).
  { intros X g am H. unfold usedX, MTX, MT, W_A, set_init_done, init_state in H. destruct (memb g X); cbn in H; discriminate. }
  unfold res_ok_slots. cbn [sb_live sb_bytes sb_cap].
  split.
  { unfold II. split; [intros r Hr; destruct Hr|].
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|intros r Hr; destruct Hr]]]]]]]].
    all: cbn; unfold hand, nareas, METAS_PER_AREA, PGSZ; cbn; lia. }
  split.
  { unfold SI, SIX. split; [|split; [|split; [|split]]].
    - intros k rg Hk. unfold region_of in Hk. cbn in Hk. destruct k; discriminate.
    - intros g am H. exfalso. exact (NU _ _ _ H).
    - intros g1 a1 g2 a2 H. exfalso. exact (NU _ _ _ H).
    - intros g am i fr H. exfalso. exact (NU _ _ _ H).
    - unfold hand_keys, hand, nareas. cbn. reflexivity. }
  split; [intros g am H; exfalso; exact (NU _ _ _ H)|].
  split; [intros g am H; exfalso; exact (NU _ _ _ H)|].
  split; [intros q H; unfold MT, W_A, set_init_done, init_state in H; cbn in H; discriminate|].
  split; [unfold MB, brk_bytes, resv_count, nareas, shift; cbn; unfold PGSZ; lia|].
  unfold nblocks, ubytes, hand, nareas, HCAP, CAPMAX. cbn. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The registers, the ghost, the configuration.                                                                 *)
(* ---------------------------------------------------------------------------------------------------------- *)

Definition W_REGS : bvmap 5 word :=
  regupd (regupd (regupd (regupd (regupd bvmap_empty (Z_to_bv 5 1) (Z_to_bv 64 RA_LIB))
    (Z_to_bv 5 2) (Z_to_bv 64 W_S)) (Z_to_bv 5 4) (Z_to_bv 64 (ms_tp src0_msyms)))
    (Z_to_bv 5 10) (Z_to_bv 64 EMPTY)) (Z_to_bv 5 11) (Z_to_bv 64 0).

Definition W_G : ghost := Ghost [] EMPTY W_S W_REGS W_L W_A W_MEM W_MD (SB 0 0 CAPMAX).

Definition W_C : config :=
  mkCfg (mkst W_REGS (Z_to_bv 64 ENTRY) W_MEM (seg_rom (ms_segs src0_msyms))) W_MD.

Lemma W_spZ : spZ W_REGS = W_S.
Proof. vm_compute. reflexivity. Qed.

Lemma W_writable : forall a, W_S - SLOT_STACK <= a < W_S -> writable_at (ms_segs src0_msyms) W_MEM a.
Proof.
  intros a Ha. unfold SLOT_STACK, W_S in Ha. unfold writable_at, wview.
  rewrite W_MEM_at by lia. rng_solve. unfold wm0. rng_solve. cbn. discriminate.
Qed.

Lemma W_errno_writable : forall a, errno_addr src0_msyms <= a < errno_addr src0_msyms + 4 ->
  writable_at (ms_segs src0_msyms) W_MEM a.
Proof.
  intros a Ha. assert (E : errno_addr src0_msyms = 0x2e86c) by reflexivity. rewrite E in Ha.
  unfold writable_at, wview. rewrite W_MEM_at by lia. rng_solve. unfold wm0. rng_solve.
  cbn. discriminate.
Qed.

Lemma W_rodata : rodata_ok src0_msyms W_MEM.
Proof.
  intros a ((s & Hin & Hw & Hr) & _).
  pose proof (src0_ro_low s Hin Hw) as Hlo.
  unfold mbyte. rewrite W_MEM_low_Z by lia. reflexivity.
Qed.

Lemma W_MI : MI src0_msyms W_MEM.
Proof.
  intros a Ha. unfold mrd. rewrite W_MEM_low; [reflexivity|].
  pose proof (ro_addr_low a Ha). lia.
Qed.

Lemma W_relro : relro src0_msyms W_MEM.
Proof.
  intros a (lo & len & Hin & Ha). unfold frame_RELRO in Hin. cbn [In] in Hin.
  unfold mbyte. rewrite W_MEM_low_Z; [reflexivity|].
  destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
Qed.

Lemma W_sink : sink_none src0_msyms W_MEM W_MD.
Proof.
  split; [split|split].
  - intros k Hk. do 1 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - intros k Hk. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - vm_compute. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The witness.                                                                                                 *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma W_entry : Inv_ENTRY (fx:=YK11.fx0) (rc:=W_RC) (SH:=src0_sink_head) (SK:=src0_sink)
  src0_msyms (@zlib_API) RA_LIB EMPTY W_G W_C.
Proof.
  assert (GV0 : GV (rc:=W_RC) src0_msyms EMPTY W_G).
  { split; [change (g_n W_G) with 0; lia|]. split; [left; split; reflexivity|]. split; [apply blk_data_nil|].
    cbn [g_S g_b g_regs W_G]. rewrite W_ceil. unfold SLOT_K, SLOT_STACK, W_S.
    split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [unfold slot_room, CAPMAX; cbn [g_b W_G sb_live sb_bytes sb_cap]; lia|].
    split; vm_compute; reflexivity. }
  assert (HB : bounded W_A) by exact (mc_bounded _ _ _ _ _ (MRx_MRc _ _ _ _ _ W_MRx)).
  split; [reflexivity|].
  split; [exact GV0|].
  split.
  { cbn [g_L g_A g_regs g_mem g_md g_p g_n g_in W_G].
    split; [exact W_MRx|]. split; [exact W_A_wf|]. split; [exact HB|]. split; [reflexivity|].
    split; [vm_compute; reflexivity|].
    rewrite W_spZ. rewrite W_ceil. unfold SLOT_STACK, W_S.
    split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [exact W_writable|].
    split; [vm_compute; reflexivity|].
    split; [exact W_errno_writable|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [left; split; reflexivity|].
    exact W_rodata. }
  split; [vm_compute; reflexivity|].
  split; [exact W_sink|].
  split; [exact W_MI|].
  split; [exact W_relro|].
  exact W_res.
Qed.

(* THE SATISFIABILITY THEOREM (UBSan): Inv_ENTRY holds of a concrete state at the frame's real instance. The
   witness is W_RC (the RunCeil of the frame's own run at entry sp W_SP0), YK11.fx0, the ghost W_G (empty input,
   p = EMPTY, S = W_S, layout W_L, allocator W_A = set_init_done true init_state, memory W_MEM, model W_MD, sbound
   SB 0 0 CAPMAX) and the configuration W_C at ENTRY (0x12cbc). *)
Theorem slotinv_entry_sat : exists (rc : RunCeil) (fx : FPState) (g : ghost) (c : config),
  Inv_ENTRY (fx:=fx) (rc:=rc) (SH:=src0_sink_head) (SK:=src0_sink) src0_msyms (@zlib_API) RA_LIB EMPTY g c.
Proof. exists W_RC, YK11.fx0, W_G, W_C. exact W_entry. Qed.
