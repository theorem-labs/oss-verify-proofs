(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 150 of its 167 lines of code are new or changed and 50 lines of the source are left out. *)
(* The frame step for a fuzz target that returns 0 or -1, stated for fuzz_lock.ubsan: the text of
   lib/Prog/FrameRet.v (frame_ret_hyp of fuzz_lock.plain) at the UBSan image, as the specification of a change to
   the K2 kit; nothing here is proved about the image.

   fuzz_lock's LLVMFuzzerTestOneInput (fuzz_lock.c:181-207, 0x12bbc in fuzz_lock.ubsan) returns -1 when the name
   length is 0 (fuzz_lock.c:191-192) or a name byte is NUL, LF, space, tab or CR (fuzz_lock.c:196-197): 0x12d08
   `addi a0, zero, -1`. The kit's frame takes a return of 0 only: U/Contract.v lib_post_g has
   `getr regs' 10 = Z_to_bv 64 0` and `ll_ret l = 0`, U/FrameAPI.v frame_ubsan binds
   `LIBK LS pl fs K = K (LL 0 fs [])`, and the driver tree U/Reusable/YO09.v run_shape writes the first call's row
   line0 = "0\n" after that call and the rows of the later calls, concat (repeat line0 m), at exit (run_tail).
   The driver writes printf("%d\n", r) for each return value r and exits with status 0 when every call
   returned 0 or -1 (docs/running.md, "Exit statuses").

   This file states, in the words of U/FrameAPI.v frame_ubsan, the frame the kit change must prove:
   - lib_post_gr r is U/Contract.v lib_post_g for the return value r: the return register is the leaf's return,
     ll_ret l, and ll_ret l = r in place of ll_ret l = 0; lib_post_gr_0_iff: lib_post_gr 0 and lib_post_g are
     equivalent;
   - lib_contract_gr ret is U/Contract.v lib_contract_g with lib_post_gr (ret pl) in place of lib_post_g, pl the
     payload: every call on pl returns ret pl, so every row the driver writes for pl is ret_row (ret pl);
     lib_contract_gr_0_iff: lib_contract_gr (fun _ => 0) and lib_contract_g are equivalent;
   - frame_ret_hyp is U/FrameAPI.v frame_ubsan for any return function ret with values 0 and -1: the shape binds
     LIBK LS pl fs K = K (LL (ret pl) fs []), and each call is given by lib_contract_gr ret. At
     ret = fun _ => 0 the shape premise is frame_ubsan's by conversion, frame_ret_call_0_iff shows the call
     premise equivalent to frame_ubsan's, and every other conjunct is frame_ubsan's word for word;
   - the driver rows: ret_row r is printf("%d\n", r) for r in {0, -1} (ret_row_0: it is line0 for 0), and
     run_shape_r is U/Reusable/YO09.v run_shape with the row ret_row (ll_ret l) in place of line0, after the first
     call and at exit (run_tail_r); run_shape_r_0: the two agree when every return is 0. The proof of
     frame_ret_hyp walks the driver against run_shape_r.
   The halting statement of fuzz_lock's UBSan build is concluded from frame_ret_hyp, as a hypothesis, in
   U/Prog/Statement.v and U/Prog/LLVMFuzzerTestOneInput_halts.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
From OSSVerify.reac_repacer.fuzz_lock Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Section R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* U/Contract.v lib_post_g, with a0 = ll_ret l and ll_ret l = r *)
Definition lib_post_gr (r : Z) (G : list (Z * Z)) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (l : lleaf)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
  getr regs' 10 = Z_to_bv 64 (ll_ret l) /\
  regs_preserved regs regs' /\
  (exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
  (forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_globals G a -> writable_at segs mem a <-> writable_at segs mem' a) /\
  (forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
     mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
  (forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
  ll_ret l = r /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  sink_none B mem' md' /\
  ro_agree segs mem' /\
  res_ok_slots A' (lib_delta n b) /\
  (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)).

(* U/Contract.v lib_contract_g, with lib_post_gr (ret pl) *)
Definition lib_contract_gr (ret : list byte -> Z) (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (j : nat) (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b (K : lleaf -> TSet),
    lib_pre_x B API stk empty L A regs mem md ra p n pl b ->
    GI j mem ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_gr (ret pl) G stk L A regs mem md p n b l L' A' regs' mem' md' /\
          GI (S j) mem') ->
       realizes segs c' (K l)) ->
    realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Lemma lib_post_gr_of_g : forall G stk L A regs mem md p n b l L' A' regs' mem' md',
  lib_post_g B API G stk L A regs mem md p n b l L' A' regs' mem' md' ->
  lib_post_gr 0 G stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof.
  intros G stk L A regs mem md p n b l L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 H20))))))))))))))))))).
  rewrite H14. exact H5.
Qed.

(* every function that meets U/Contract.v lib_contract_g meets lib_contract_gr for the return 0 *)
Lemma lib_contract_gr_of_g : forall G R GI j pc ra empty stk,
  lib_contract_g B API G R GI j pc ra empty stk -> lib_contract_gr (fun _ => 0) G R GI j pc ra empty stk.
Proof.
  intros G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & HGI').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_gr_of_g G stk L A regs mem md p n b l L' A' regs' mem' md' Hpost) | exact HGI'].
Qed.

Lemma lib_post_g_of_gr0 : forall G stk L A regs mem md p n b l L' A' regs' mem' md',
  lib_post_gr 0 G stk L A regs mem md p n b l L' A' regs' mem' md' ->
  lib_post_g B API G stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof.
  intros G stk L A regs mem md p n b l L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 H20))))))))))))))))))).
  rewrite H5, H14. reflexivity.
Qed.

(* at the return 0 the two posts are the same: a0 = ll_ret l = 0 *)
Lemma lib_post_gr_0_iff : forall G stk L A regs mem md p n b l L' A' regs' mem' md',
  lib_post_gr 0 G stk L A regs mem md p n b l L' A' regs' mem' md' <->
  lib_post_g B API G stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof.
  intros. split; [apply lib_post_g_of_gr0 | apply lib_post_gr_of_g].
Qed.

(* every function that meets lib_contract_gr for the return 0 meets U/Contract.v lib_contract_g *)
Lemma lib_contract_g_of_gr0 : forall G R GI j pc ra empty stk,
  lib_contract_gr (fun _ => 0) G R GI j pc ra empty stk -> lib_contract_g B API G R GI j pc ra empty stk.
Proof.
  intros G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & HGI').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_g_of_gr0 G stk L A regs mem md p n b l L' A' regs' mem' md' Hpost) | exact HGI'].
Qed.

(* at the return 0 the two contracts are the same *)
Lemma lib_contract_gr_0_iff : forall G R GI j pc ra empty stk,
  lib_contract_gr (fun _ => 0) G R GI j pc ra empty stk <-> lib_contract_g B API G R GI j pc ra empty stk.
Proof.
  intros. split; [apply lib_contract_g_of_gr0 | apply lib_contract_gr_of_g].
Qed.

End R.

(* The driver's row for a return value r: printf("%d\n", r), for r = 0 ("0\n" = line0) and r = -1 ("-1\n", the
   bytes 0x2d 0x31 0x0a). *)
Definition ret_row (r : Z) : list byte :=
  if r =? 0 then line0 else [Z_to_bv 8 45; Z_to_bv 8 49] ++ nlB.

Lemma ret_row_0 : ret_row 0 = line0.
Proof. reflexivity. Qed.

Section D.
Context {LS : lib_shape}.

(* U/Reusable/YO09.v run_tail and run_shape, with the row of the leaf's return in place of line0: the driver tree
   the proof of frame_ret_hyp walks, for one to four calls of the fuzz target on the payload pl. *)
Definition run_tail_r (row : list byte) (m : nat) (fs : Fs) : TSet :=
  match m with O => ex 0 fs | S _ => wr ch_stdout (concat (repeat row m)) (ex 0 fs) end.

Definition run_shape_r (pl : list byte) (k : nat) (fs : Fs) : TSet :=
  match k with
  | O => ex 0 fs
  | S k' => LIBK pl fs (fun l => wr ch_stdout (ret_row (ll_ret l))
                                   (lib_iter pl k' (run_tail_r (ret_row (ll_ret l)) k') (ll_fs l)))
  end.

Lemma run_shape_r_0 : (forall pl fs K, LIBK pl fs K = K (LL 0 fs [])) ->
  forall pl k fs, run_shape_r pl k fs = run_shape pl k fs.
Proof. intros H pl [|k] fs; [reflexivity|]. cbn [run_shape_r run_shape]. rewrite !H. reflexivity. Qed.

End D.

(* U/FrameAPI.v frame_ubsan, for a fuzz target whose return on the payload pl is ret pl, 0 or -1: the shape's leaf
   carries ret pl, and each call meets lib_contract_gr. *)
Definition frame_ret_hyp : Prop :=
  forall ret : list byte -> Z, (forall pl, ret pl = 0 \/ ret pl = -1) ->
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x14178 /\ ms_free B = 0x14038 /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x4e0e0 /\ ms_got_guard B = 0x1caf8 /\
    ms_ctx B = 0x4e178 /\ ms_lock B = 0x4e170 /\ ms_libc B = 0x4e100 /\ ms_size_classes B = 0x10434 /\
    ms_small_cnt B = 0x10494 /\ ms_med_cnt B = 0x104af /\ ms_debruijn B = 0x10414 /\ ms_tp B = 0x2de70 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x4e530 /\ @sk_ofl_lock SK = 0x4e528 /\ @sk_threaded SK = 0x4e100 + 1 /\
    empty = 0x2dd80 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL (ret pl) fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) /\
    (forall (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_gr fx rc LS B (API rc) SH SK ret G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.ubsan_halts).

(* At ret = fun _ => 0 the call premise of frame_ret_hyp is equivalent to the call premise of
   U/FrameAPI.v frame_ubsan; its shape premise LIBK LS pl fs K = K (LL ((fun _ => 0) pl) fs []) is frame_ubsan's by
   conversion. *)
Lemma frame_ret_call_0_iff : forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_gr fx rc LS B (API rc) SH SK (fun _ => 0) G frame_RELRO GI j ENTRY ra empty SLOT_STACK) <->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_g fx rc LS B (API rc) SH SK G frame_RELRO GI j ENTRY ra empty SLOT_STACK).
Proof.
  intros B API LS SH SK ra empty G GI.
  split; intros H rc fx j Hj; [apply lib_contract_g_of_gr0 | apply lib_contract_gr_of_g]; exact (H rc fx j Hj).
Qed.
