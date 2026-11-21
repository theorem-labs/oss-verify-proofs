(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: rctx carries the launch's (inp, mb, ph, entry, sp, rnd) with argv, envp, uid, gid and hwcap read off inp, the libc cell reads InitMem.argv_ptrs, CORE_STK pairs the launch fact rc_launch with the entry stack image (rc_span, after CatSim's launch_string_base_arith, and rc_top_align added), and rc_lo is sp - 6144512 (was sp - 8388608) while GIo keeps the 8388608 ceiling, in both kits. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore Stdio Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Notation CEILZ := alloc_ceiling (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
(* PORTED to 75d69e00.  [rctx] now carries [InitMem]'s [Section Layout] tuple
   (InitMem.v:369-371) -- (inp, mb, ph, entry, sp, rnd) -- in place of the
   deleted seven-tuple (sp0, argv, envp, uid, hw, rnd).  argv, envp, the exec
   file name and the credentials are READ OFF [inp]: [Run.entry_stack_image]
   (Run.v:1344) feeds [StackLayout.build_stack_bytes]'s twelve arguments
   (StackLayout.v:483) from it.  [rc_argv], [rc_envp], [rc_uid], [rc_gid] and
   [rc_hw] therefore survive as DERIVED DEFINITIONS rather than fields, so
   every call site that reads them is unchanged.  CONFIG_RSEQ,
   [kb_rseq (in_kernel inp)], is carried symbolically and pinned nowhere. *)
Record rctx := mkRC { rc_inp : ProcInput; rc_mb : word; rc_ph : PhdrInfo;
                      rc_entry : word; rc_sp0 : word; rc_rnd : EntryDraw;
                      rc_tp : word; rc_cb : bool }.
Definition rc_argv (R : rctx) : list (list byte) := in_argv (rc_inp R).
Definition rc_envp (R : rctx) : list (list byte) := in_envp (rc_inp R).
Definition rc_uid (R : rctx) : word := in_uid (rc_inp R).
Definition rc_gid (R : rctx) : word := in_gid (rc_inp R).
Definition rc_hw (R : rctx) : word := in_hwcap (rc_inp R).
(* the stack VMA's end: the image now runs from [sp] to [ed_top] *)
Definition rc_top (R : rctx) : word := ed_top (rc_rnd R).
(* [comment removed for export] *)
Definition set_cb (R : rctx) (b : bool) : rctx :=
  mkRC (rc_inp R) (rc_mb R) (rc_ph R) (rc_entry R) (rc_sp0 R) (rc_rnd R) (rc_tp R) b.
Lemma set_cb_same : forall R, set_cb R (rc_cb R) = R.
Proof. intros []. reflexivity. Qed.
Definition rc_canary (R : rctx) : word := ssp_canary (rc_rnd R).
Definition utp (R : rctx) : Z := bv_unsigned (rc_tp R).
Definition usp0 (R : rctx) : Z := bv_unsigned (rc_sp0 R).
(* The main stack floor.  At LPS 727298f3 [wrap_mem] zero-maps only
   [stack_window_lo, sp), and [StoreOk.stack_window_lo_valid] puts that floor at
   or below [sp + stack_window_reach - stack_max_size] = [sp - 6144513]; the
   16-aligned floor above it is [sp - 6144512] (boost-json's [wok_lo] floor). *)
Definition rc_lo (R : rctx) : Z := usp0 R - 6144512.
(* [comment removed for export] *)
Definition rc_spmain (R : rctx) : Z := usp0 R - 48.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Blocks.
  Context {hptr : Type}.
  Definition cblock : Type := (hptr * Z * Z)%type.     (* [comment removed for export] *)
  Definition cb_tok (b : cblock) : hptr := fst (fst b).
  Definition cb_addr (b : cblock) : Z := snd (fst b).
  Definition cb_size (b : cblock) : Z := snd b.

  (* [comment removed for export] *)
  Definition in_block (LB : list cblock) (a : Z) : Prop :=
    Exists (fun b => cb_addr b <= a < cb_addr b + cb_size b) LB.
  Definition iv_in_block (LB : list cblock) (iv : Z * Z) : Prop :=
    Exists (fun b => cb_addr b <= fst iv /\ snd iv <= cb_addr b + cb_size b) LB.

  Lemma in_block_In : forall LB a, in_block LB a <-> exists b, In b LB /\ cb_addr b <= a < cb_addr b + cb_size b.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros LB a. unfold in_block. rewrite Exists_exists. reflexivity. Qed.
  Lemma in_block_app : forall L1 L2 a, in_block (L1 ++ L2) a <-> in_block L1 a \/ in_block L2 a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. unfold in_block. rewrite Exists_app. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition client_keeps (CL : list cblock) (SP : Z) (a : Z) : Prop := SP <= a \/ in_block CL a.

  Definition block_ok (u : Z) (b : cblock) : Prop :=
    0 < cb_addr b /\ cb_addr b mod 16 = 0 /\ 0 <= cb_size b /\ cb_addr b + cb_size b <= CEILZ
    /\ (cb_addr b + cb_size b <= 0x10000 \/ 0x55000 <= cb_addr b)
    /\ (cb_addr b + cb_size b <= u - 200 \/ u - 200 + 4096 <= cb_addr b).
  Definition apart (b b' : cblock) : Prop :=
    cb_addr b + cb_size b <= cb_addr b' \/ cb_addr b' + cb_size b' <= cb_addr b.
  Fixpoint blocks_apart (LB : list cblock) : Prop :=
    match LB with [] => True | b :: LB' => Forall (apart b) LB' /\ blocks_apart LB' end.
  Definition blocks_ok (u : Z) (LB : list cblock) : Prop := Forall (block_ok u) LB /\ blocks_apart LB.

  Lemma blocks_ok_cons_inv : forall u b LB, blocks_ok u (b :: LB) -> block_ok u b /\ Forall (apart b) LB /\ blocks_ok u LB.
  Proof using Type. pin_using tt. ceil_facts. intros u b LB [H1 [H2 H3]]. apply Forall_cons_iff in H1. destruct H1 as [A B]. split; [exact A|]. split; [exact H2|]. split; [exact B| exact H3]. Qed.

  Lemma blocks_apart_In : forall LB b b', blocks_apart LB -> In b LB -> In b' LB -> b = b' \/ apart b b'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction LB as [|c LB IH]; intros b b' H Hb Hb'; [destruct Hb|].
    destruct H as [Hc H]. destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb'].
    - left; reflexivity.
    - right. exact (proj1 (Forall_forall _ _) Hc _ Hb').
    - right. pose proof (proj1 (Forall_forall _ _) Hc _ Hb) as A. unfold apart in *. lia.
    - apply IH; assumption.
  Qed.

  Lemma blocks_apart_app_inv : forall L1 L2, blocks_apart (L1 ++ L2) ->
    blocks_apart L1 /\ blocks_apart L2 /\ (forall b b', In b L1 -> In b' L2 -> apart b b').
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction L1 as [|c L1 IH]; intros L2 H; cbn in *.
    - repeat split; auto. intros b b' [].
    - destruct H as [Hc H]. apply IH in H as (A & B & C). apply Forall_app in Hc as [Hc1 Hc2].
      repeat split; auto. intros b b' [<-|Hb] Hb'; [exact (proj1 (Forall_forall _ _) Hc2 _ Hb') | apply C; assumption].
  Qed.
End Blocks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shared_const (a : Z) : Prop :=
  (0x53d08 <= a < 0x53d90) \/ (0x22558 <= a < 0x22668).
(* [comment removed for export] *)
Definition heap_static (a : Z) : Prop := 0x53d90 <= a < 0x54148.
(* [comment removed for export] *)
Definition stdio_static (a : Z) : Prop := (0x23660 <= a < 0x23930) \/ (0x54148 <= a < 0x54970).
(* [comment removed for export] *)
Definition harn_static (a : Z) : Prop := 0x33990 <= a < 0x339c8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition agrees_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a -> m' (wa a) = m (wa a) /\ (wview ssegs m (wa a) <> None -> wview ssegs m' (wa a) <> None).

Lemma agrees_on_refl : forall P m, agrees_on P m m.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P m a _ _. auto. Qed.
Lemma agrees_on_trans : forall P m1 m2 m3, agrees_on P m1 m2 -> agrees_on P m2 m3 -> agrees_on P m1 m3.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P m1 m2 m3 H1 H2 a Ha Hp. destruct (H1 a Ha Hp) as [E1 W1]. destruct (H2 a Ha Hp) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agrees_on_weaken : forall (P Q : Z -> Prop) m m', agrees_on P m m' -> (forall a, Q a -> P a) -> agrees_on Q m m'.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P Q m m' H HQ a Ha Hq. apply H; auto. Qed.

(* [comment removed for export] *)
Lemma agrees_on_of_munch : forall (P : Z -> Prop) W m m',
  munch W m m' -> wmono ssegs m m' -> (forall a, 0 <= a < 2^64 -> P a -> outside W a) -> agrees_on P m m'.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P W m m' MU WM HP a Ha Hp. split.
  - apply MU. rewrite wa_unsigned by lia. apply HP; [exact Ha | exact Hp].
  - apply WM.
Qed.

Lemma agrees_bytes_at : forall P m m' A bs,
  agrees_on P m m' -> bytes_at ssegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at ssegs m' A bs.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd. destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _].
  rewrite E. reflexivity.
Qed.
Lemma agrees_wr_at : forall P m m' A n,
  agrees_on P m m' -> wr_at ssegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at ssegs m' A n.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.
Lemma agrees_rw_cells : forall P m m' A cs,
  agrees_on P m m' -> rw_cells ssegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells ssegs m' A cs.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply agrees_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply agrees_wr_at; eauto.
Qed.
Lemma agrees_stk : forall P m m' lo hi,
  agrees_on P m m' -> stk ssegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk ssegs m' lo hi.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P m m' lo hi HP (H0 & H1 & HS) HR. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HS a Ha) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kit.
  Context {H hptr : Type}.
  Notation cblk := (@cblock hptr).

  Record modkit := mkMK {
    (* [comment removed for export] *)
    mk_heap : H -> rctx -> list cblk -> mem -> Prop;
    (* [comment removed for export] *)
    mk_stdio : @libc_st hptr -> rctx -> list cblk -> mem -> Prop
  }.

  (* [comment removed for export] *)
  Definition heap_client_iv (R : rctx) (LB : list cblk) (iv : Z * Z) : Prop :=
    CEILZ <= fst iv \/ iv_in_block LB iv
    \/ (0x22000 <= fst iv /\ snd iv <= 0x55000 /\ (snd iv <= 0x22558 \/ 0x22668 <= fst iv) /\ (snd iv <= 0x53d08 \/ 0x54148 <= fst iv))
    \/ (utp R - 200 <= fst iv /\ snd iv <= utp R - 200 + 4096).

  (* [comment removed for export] *)
  Definition heap_keeps (R : rctx) (LB : list cblk) (SP : Z) (a : Z) : Prop :=
    SP <= a \/ in_block LB a
    \/ (0x22000 <= a < 0x55000 /\ ~ heap_static a /\ ~ (utp R - 164 <= a < utp R - 160))
    \/ (utp R - 200 <= a < utp R - 200 + 4096 /\ ~ (utp R - 164 <= a < utp R - 160)).
  Definition heap_pres (R : rctx) (LB : list cblk) (SP : Z) (m m' : mem) : Prop :=
    agrees_on (heap_keeps R LB SP) m m'.

  Definition stdio_fp (R : rctx) (FB : list cblk) (a : Z) : Prop := stdio_static a \/ in_block FB a.

  Variable K : modkit.

  (* [comment removed for export] *)
  Definition heap_frame_law : Prop :=
    forall h R LB m m' W, mk_heap K h R LB m -> munch W m m' -> wmono ssegs m m' -> Forall (heap_client_iv R LB) W -> mk_heap K h R LB m'.
  Definition heap_blocks_law : Prop :=
    forall h R LB m, mk_heap K h R LB m -> blocks_ok (utp R) LB.
  Definition heap_perm_law : Prop :=
    forall h R LB LB' m, mk_heap K h R LB m -> Permutation.Permutation LB LB' -> mk_heap K h R LB' m.
  Definition heap_addr_law (HO : HeapOps H hptr) : Prop :=
    forall h R LB m b, mk_heap K h R LB m -> In b LB -> ho_addr HO h (cb_tok b) = cb_addr b.
  Definition stdio_fp_law : Prop :=
    forall l R FB m m', mk_stdio K l R FB m -> agrees_on (stdio_fp R FB) m m' -> mk_stdio K l R FB m'.
  (* [comment removed for export] *)
  Definition heap_cb_law : Prop :=
    forall h R LB m b, mk_heap K h R LB m -> mk_heap K h (set_cb R b) LB m.
  Definition stdio_cb_law : Prop :=
    forall l R FB m b, mk_stdio K l R FB m -> mk_stdio K l (set_cb R b) FB m.
  Definition stdio_blocks_law : Prop :=
    forall l R FB m b, mk_stdio K l R FB m -> In b FB -> cb_addr b + cb_size b <= CEILZ /\ (cb_addr b + cb_size b <= 0x10000 \/ 0x55000 <= cb_addr b).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition HARNR (o : option hptr) (FB : list cblk) (m : mem) : Prop :=
    (exists ib : byte, rw_cells ssegs m 0x33990 [C1 ib])
    /\ (exists ej : list byte, rw_cells ssegs m 0x339a0 [CB 32 ej])
    /\ match o with
       | None => rw_cells ssegs m 0x339c0 [C8 (Z_to_bv 64 0)]
       | Some q => exists A, In (q, A, 1264) FB /\ rw_cells ssegs m 0x339c0 [C8 (Z_to_bv 64 A)]
       end.
  Definition harn_fp (a : Z) : Prop := harn_static a.

  (* [comment removed for export] *)
  Definition CORE_TLS (R : rctx) (m : mem) : Prop :=
    let u := utp R in
    exists (t : Z) (e : word),
       rw_cells ssegs m (u + -200) [C8 (Z_to_bv 64 (u - 200)); C8 (Z_to_bv 64 (u - 200)); C8 (Z_to_bv 64 (u - 200)); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 t)]
    /\ rw_cells ssegs m (u + -164) [C4 e]
    /\ rw_cells ssegs m (u + -160) [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 (u - 80));
                                   CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x53d60); CB 24 (repeat (Z_to_bv 8 0) 24)]
    /\ rw_cells ssegs m (u + -16) [C8 (rc_canary R)]                      (* [comment removed for export] *)
    /\ rw_cells ssegs m (u + -8) [C8 (Z_to_bv 64 (u + 264))]
    /\ rw_cells ssegs m (u + 256) [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (u + 2048)); CB 3616 (repeat (Z_to_bv 8 0) 3616)]
    /\ (0 < t < 4194304).
  Definition core_tls_fp (R : rctx) (a : Z) : Prop := (utp R - 200 <= a < utp R) \/ (utp R + 256 <= a < utp R - 200 + 4096).

  (* [comment removed for export] *)
  Definition PCAP_TLS (R : rctx) (m : mem) : Prop := exists bs, rw_cells ssegs m (utp R) [CB 256 bs].
  Definition pcap_tls_fp (R : rctx) (a : Z) : Prop := utp R <= a < utp R + 256.

  (* [comment removed for export] *)
  Definition CORE_LIBC (R : rctx) (m : mem) : Prop :=
    rw_cells ssegs m 0x53d28 (libc_cells (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 64 0)
                                (Z_to_bv 64 (auxv_addr (rc_sp0 R) (rc_argv R) (rc_envp R))) (Z_to_bv 64 0x53aa8) (Z_to_bv 64 480)
                                (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 4096) (repeat (Z_to_bv 8 0) 48))
    /\ rw_cells ssegs m 0x22620 [C8 (Z_to_bv 64 0x53d08)]
    /\ rw_cells ssegs m 0x53d08 [C8 (rc_canary R)]                        (* [comment removed for export] *)
    /\ rw_cells ssegs m 0x53d10 [C8 (Z_to_bv 64 0)]
    /\ (exists (pg : word) (P0 : Z), rw_cells ssegs m 0x53d18 [C8 pg; C8 (Z_to_bv 64 P0)]
                                  /\ nth_error (InitMem.argv_ptrs (rc_inp R) (rc_sp0 R) (rc_rnd R)) 0 = Some (Z_to_bv 64 P0)).
  Definition core_libc_fp (a : Z) : Prop := (0x53d08 <= a < 0x53d90) \/ (0x22620 <= a < 0x22628).

  (* [comment removed for export] *)
  Definition CORE_MISC (m : mem) : Prop :=
       rw_cells ssegs m 0x225b8 [C8 (Z_to_bv 64 0x22560)] /\ rw_cells ssegs m 0x22560 [C8 (Z_to_bv 64 0x23660)]   (* [comment removed for export] *)
    /\ rw_cells ssegs m 0x225f0 [C8 (Z_to_bv 64 0x22568)] /\ rw_cells ssegs m 0x22568 [C8 (Z_to_bv 64 0x23750)]   (* [comment removed for export] *)
    /\ rw_cells ssegs m 0x225c0 [C8 (Z_to_bv 64 0)]                                                               (* [comment removed for export] *)
    /\ rw_cells ssegs m 0x225d0 [C8 (Z_to_bv 64 0x1496c); C8 (Z_to_bv 64 0x14694); C8 (Z_to_bv 64 0x148a8); C8 (Z_to_bv 64 0x14190)]. (* [comment removed for export] *)
  Definition core_misc_fp (a : Z) : Prop :=
    (0x225b8 <= a < 0x225f0) \/ (0x22560 <= a < 0x22570) \/ (0x225f0 <= a < 0x225f8).

  (* [comment removed for export] *)
  Definition ATX (cb : bool) (m : mem) : Prop :=
    exists (reg : bool) (pad : list byte) (f0 g0 : word) (j1 j2 : list byte),
       rw_cells ssegs m 0x33990 [C1 (bool8 reg); CB 3 pad; C1 (bool8 cb)]
    /\ rw_cells ssegs m 0x53ae0 (atexit_cells (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 3) (atx_slot reg) (repeat (Z_to_bv 8 0) 4) (atx_head reg))
    /\ rw_cells ssegs m 0x53af8 (builtin_cells f0 j1 g0 j2)
    /\ (reg = true -> f0 = Z_to_bv 64 0x18408 /\ g0 = Z_to_bv 64 0x13f38).
  Definition atx_fp (a : Z) : Prop := (0x33990 <= a < 0x33995) \/ (0x53ae0 <= a < 0x53d00).

  (* [comment removed for export] *)
  Definition CORE_EXIT (cb : bool) (m : mem) : Prop :=
       rw_cells ssegs m 0x53d00 [C4 (Z_to_bv 64 0)]
    /\ ATX cb m
    /\ rw_cells ssegs m 0x22628 [C8 (Z_to_bv 64 0x22560); C8 (Z_to_bv 64 0x22558)]
    /\ rw_cells ssegs m 0x22558 [C8 (Z_to_bv 64 0x13a80)]
    /\ rw_cells ssegs m 0x23988 [C1 (Z_to_bv 8 0)]
    /\ rw_cells ssegs m 0x225a8 [C8 (Z_to_bv 64 0x18340); C8 (Z_to_bv 64 0)]
    /\ rw_cells ssegs m 0x23638 [C8 (Z_to_bv 64 0x23638)].
  Definition core_exit_fp (a : Z) : Prop :=
    (0x53d00 <= a < 0x53d04) \/ (0x53ae0 <= a < 0x53d00) \/ (0x22628 <= a < 0x22638) \/ (0x22558 <= a < 0x22560)
    \/ (0x23988 <= a < 0x23989) \/ (0x225a8 <= a < 0x225b8) \/ (0x23638 <= a < 0x23640) \/ (0x33990 <= a < 0x33995).

  (* PORTED to 75d69e00.  The image is [Run.entry_stack_image] of the ported
     tuple (Run.v:1344); the seven-argument [build_stack_bytes] it used to name
     no longer exists (StackLayout.v:483 takes twelve).  The image is now the
     WHOLE block, running from [sp] to [ed_top], so the launch fact travels
     with it: without it [block_pad_len]'s [Z.to_nat] clamp can bite and none
     of [Printf_kit__Musl]'s piece lemmas apply (their [SPAN] hypothesis,
     Printf_kit__Musl.v:194).  [brk] is existential because nothing here reads
     it; [entry_launch_ok_va] is the premise shape the rest of this unit
     already ports to (AmoStep__Musl.v:236-238). *)
  Definition rc_launch (R : rctx) : Prop :=
    exists brk : word,
      entry_launch_ok_va Sv48 (mkEntry (rc_sp0 R) brk (rc_mb R) (rc_rnd R)) (rc_inp R).
  Definition CORE_STK (R : rctx) (m : mem) : Prop :=
    rc_launch R
    /\ bytes_at ssegs m (usp0 R)
         (entry_stack_image (rc_inp R) (rc_mb R) (rc_ph R) (rc_entry R) (rc_sp0 R) (rc_rnd R)).
  Definition core_stk_fp (R : rctx) (a : Z) : Prop :=
    usp0 R <= a < usp0 R
      + Z.of_nat (length (entry_stack_image (rc_inp R) (rc_mb R) (rc_ph R) (rc_entry R) (rc_sp0 R) (rc_rnd R))).

  (* [SPAN], the premise [Printf_kit__Musl.Section StackImage] carries
     (Printf_kit__Musl.v:194) and [InitMem.Section Layout] carries
     (InitMem.v:465): read off [valid_launch_sp]'s upper bound,
     75d69e00:theories/LinuxProcessSem/Run.v:3656, whose [launch_sp_hi]
     (Run.v:3641) is [align_down16 (top - 8 - L) - C] with
     [align_down16 x = x - x mod 16] (Run.v:3572), so [align_down16 x <= x].
     PROVENANCE (rule 23c): this is [Common/CatSim__Common.v:1361]
     [launch_string_base_arith], whose unit this one does not depend on; the
     proof is its proof.  The literal numbers are never named --
     [InitMem.struct_size] is [block_head_size rseq argv envp] with [rseq] =
     [kb_rseq (in_kernel inp)] symbolic. *)
  Lemma rc_span : forall R, rc_launch R ->
    (usp0 R + InitMem.struct_size (rc_inp R) + InitMem.str_len (rc_inp R) + 8
     <= bv_unsigned (rc_top R))%Z.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros R [brk LA]. cbn [entry_launch_ok_va] in LA.
    destruct LA as (_ & (_ & _ & Hhi) & _).
    unfold usp0, rc_top, InitMem.struct_size, InitMem.str_len.
    unfold launch_sp_hi, align_down16 in Hhi.
    pose proof (Z.mod_pos_bound
      (bv_unsigned (ed_top (rc_rnd R)) - 8
       - Z.of_nat (launch_string_bytes (in_argv (rc_inp R)) (in_envp (rc_inp R))
                     (in_execfn (rc_inp R)))) 16 ltac:(lia)).
    lia.
  Qed.

  (* The image ENDS at [ed_top], so [sp]'s alignment says nothing about its end
     and [stack_argv_string_slack]'s premise moved onto [top]
     (Printf_kit__Musl.v:318).  [valid_stack_top_va]'s first conjunct
     (75d69e00:theories/LinuxProcessSem/Run.v:3610) gives
     [bv_unsigned top mod page_size = 0], which is strictly stronger. *)
  Lemma rc_top_align : forall R, rc_launch R -> (bv_unsigned (rc_top R) mod 8 = 0)%Z.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros R [brk LA]. cbn [entry_launch_ok_va] in LA.
    destruct LA as ((HP & _ & _) & _ & _). unfold rc_top.
    unfold page_size in HP.
    pose proof (Z.div_mod (bv_unsigned (ed_top (rc_rnd R))) 4096 ltac:(lia)) as D.
    assert (E : bv_unsigned (ed_top (rc_rnd R))
                = (512 * (bv_unsigned (ed_top (rc_rnd R)) / 4096) * 8)%Z) by lia.
    rewrite E. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition GI (R : rctx) (s : PState H hptr) (CL : list cblk) (m : mem) : Prop :=
    exists FB : list cblk,
       mk_heap K (ps_heap s) R (CL ++ FB) m
    /\ mk_stdio K (ps_libc s) R FB m
    /\ HARNR (ps_outfile s) FB m
    /\ CORE_TLS R m /\ PCAP_TLS R m /\ CORE_LIBC R m /\ CORE_MISC m /\ CORE_EXIT (rc_cb R) m /\ CORE_STK R m
    /\ ps_tls s = utp R - 200 /\ tls_block_ok (utp R - 200)
    /\ blocks_ok (utp R) (CL ++ FB)
    /\ 0x7fff80000000 <= usp0 R <= 2^47       (* [comment removed for export] *)
    /\ CEILZ <= usp0 R - 8388608.             (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition SXGI (s : PState H hptr) (tp : word) (m : mem) : Prop :=
    exists (R : rctx) (CL FB : list cblk),
       rc_tp R = tp
    /\ mk_heap K (ps_heap s) R (CL ++ FB) m
    /\ mk_stdio K (ps_libc s) R FB m
    /\ HARNR (ps_outfile s) FB m
    /\ CORE_TLS R m /\ PCAP_TLS R m /\ CORE_LIBC R m /\ CORE_MISC m
    /\ ps_tls s = utp R - 200 /\ tls_block_ok (utp R - 200)
    /\ blocks_ok (utp R) (CL ++ FB).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac tr AG HP A := eapply agrees_rw_cells; [exact AG | exact A | intros a Ha; apply HP; sl_lit_sizes_in Ha; cbn in Ha; lia].

  Lemma HARNR_agree : forall P o FB m m', agrees_on P m m' -> (forall a, harn_fp a -> P a) -> HARNR o FB m -> HARNR o FB m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P o FB m m' AG HP ((ib & A1) & (ej & A2) & A3). unfold harn_fp, harn_static in HP. split; [|split].
    - exists ib. tr AG HP A1.
    - exists ej. tr AG HP A2.
    - destruct o as [q|]; [destruct A3 as (A & HA & A3); exists A; split; [exact HA|] |]; tr AG HP A3.
  Qed.

  Lemma CORE_TLS_agree : forall P R m m', agrees_on P m m' -> (forall a, core_tls_fp R a -> P a) -> CORE_TLS R m -> CORE_TLS R m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P R m m' AG HP (t & e & A1 & A2 & A3 & A4 & A5 & A6 & Ht). unfold core_tls_fp in HP. exists t, e.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|]. split; [tr AG HP A5|]. split; [tr AG HP A6| exact Ht].
  Qed.

  Lemma PCAP_TLS_agree : forall P R m m', agrees_on P m m' -> (forall a, pcap_tls_fp R a -> P a) -> PCAP_TLS R m -> PCAP_TLS R m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P R m m' AG HP (bs & A1). unfold pcap_tls_fp in HP. exists bs. tr AG HP A1. Qed.

  Lemma CORE_LIBC_agree : forall P R m m', agrees_on P m m' -> (forall a, core_libc_fp a -> P a) -> CORE_LIBC R m -> CORE_LIBC R m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P R m m' AG HP (A1 & A2 & A3 & A4 & (pg & P0 & A5 & HP0)). unfold core_libc_fp in HP. unfold libc_cells in *.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|]. exists pg, P0. split; [tr AG HP A5| exact HP0].
  Qed.

  Lemma CORE_MISC_agree : forall P m m', agrees_on P m m' -> (forall a, core_misc_fp a -> P a) -> CORE_MISC m -> CORE_MISC m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6). unfold core_misc_fp in HP.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|]. split; [tr AG HP A5| tr AG HP A6].
  Qed.

  Lemma ATX_agree : forall P cb m m', agrees_on P m m' -> (forall a, atx_fp a -> P a) -> ATX cb m -> ATX cb m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P cb m m' AG HP (reg & pad & f0 & g0 & j1 & j2 & A1 & A2 & A3 & A4). unfold atx_fp in HP. unfold atexit_cells, builtin_cells in *.
    exists reg, pad, f0, g0, j1, j2. split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3| exact A4].
  Qed.

  Lemma CORE_EXIT_agree : forall P cb m m', agrees_on P m m' -> (forall a, core_exit_fp a -> P a) -> CORE_EXIT cb m -> CORE_EXIT cb m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P cb m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold core_exit_fp in HP.
    split; [tr AG HP A1|]. split; [eapply ATX_agree; [exact AG| |exact A2]; intros a Ha; apply HP; unfold atx_fp in Ha; lia|].
    split; [tr AG HP A3|]. split; [tr AG HP A4|]. split; [tr AG HP A5|]. split; [tr AG HP A6| tr AG HP A7].
  Qed.

  Lemma CORE_STK_agree : forall P R m m', agrees_on P m m' -> (forall a, core_stk_fp R a -> P a) -> CORE_STK R m -> CORE_STK R m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P R m m' AG HP (LA & A1). unfold core_stk_fp in HP. unfold CORE_STK in *. split; [exact LA|]. eapply agrees_bytes_at; [exact AG| exact A1| intros a Ha; apply HP; lia]. Qed.
End Kit.
End WithCeil.

Arguments modkit H hptr : clear implicits.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Notation CEILZ := alloc_ceiling (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
(* PORTED to 75d69e00, identically to the Plain kit above (GI.v:29-50): [rctx]
   carries [InitMem]'s [Section Layout] tuple (inp, mb, ph, entry, sp, rnd) and
   argv, envp, the exec file name and the credentials are read off [inp].
   [kb_rseq (in_kernel inp)] is carried symbolically and pinned nowhere. *)
Record rctx := mkRC { rc_inp : ProcInput; rc_mb : word; rc_ph : PhdrInfo;
                      rc_entry : word; rc_sp0 : word; rc_rnd : EntryDraw;
                      rc_tp : word; rc_cb : bool }.
Definition rc_argv (R : rctx) : list (list byte) := in_argv (rc_inp R).
Definition rc_envp (R : rctx) : list (list byte) := in_envp (rc_inp R).
Definition rc_uid (R : rctx) : word := in_uid (rc_inp R).
Definition rc_gid (R : rctx) : word := in_gid (rc_inp R).
Definition rc_hw (R : rctx) : word := in_hwcap (rc_inp R).
(* the stack VMA's end: the image now runs from [sp] to [ed_top] *)
Definition rc_top (R : rctx) : word := ed_top (rc_rnd R).
(* [comment removed for export] *)
Definition set_cb (R : rctx) (b : bool) : rctx :=
  mkRC (rc_inp R) (rc_mb R) (rc_ph R) (rc_entry R) (rc_sp0 R) (rc_rnd R) (rc_tp R) b.
Lemma set_cb_same : forall R, set_cb R (rc_cb R) = R.
Proof. intros []. reflexivity. Qed.
Definition rc_canary (R : rctx) : word := ssp_canary (rc_rnd R).
Definition utp (R : rctx) : Z := bv_unsigned (rc_tp R).
Definition usp0 (R : rctx) : Z := bv_unsigned (rc_sp0 R).
(* the main stack floor, as in the plain copy above *)
Definition rc_lo (R : rctx) : Z := usp0 R - 6144512.
(* [comment removed for export] *)
Definition rc_spmain (R : rctx) : Z := usp0 R - 48.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Blocks.
  Context {hptr : Type}.
  Definition cblock : Type := (hptr * Z * Z)%type.     (* [comment removed for export] *)
  Definition cb_tok (b : cblock) : hptr := fst (fst b).
  Definition cb_addr (b : cblock) : Z := snd (fst b).
  Definition cb_size (b : cblock) : Z := snd b.

  (* [comment removed for export] *)
  Definition in_block (LB : list cblock) (a : Z) : Prop :=
    Exists (fun b => cb_addr b <= a < cb_addr b + cb_size b) LB.
  Definition iv_in_block (LB : list cblock) (iv : Z * Z) : Prop :=
    Exists (fun b => cb_addr b <= fst iv /\ snd iv <= cb_addr b + cb_size b) LB.

  Lemma in_block_In : forall LB a, in_block LB a <-> exists b, In b LB /\ cb_addr b <= a < cb_addr b + cb_size b.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros LB a. unfold in_block. rewrite Exists_exists. reflexivity. Qed.
  Lemma in_block_app : forall L1 L2 a, in_block (L1 ++ L2) a <-> in_block L1 a \/ in_block L2 a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. unfold in_block. rewrite Exists_app. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition client_keeps (CL : list cblock) (SP : Z) (a : Z) : Prop := SP <= a \/ in_block CL a.

  Definition block_ok (u : Z) (b : cblock) : Prop :=
    0 < cb_addr b /\ cb_addr b mod 16 = 0 /\ 0 <= cb_size b /\ cb_addr b + cb_size b <= CEILZ
    /\ (cb_addr b + cb_size b <= 0x10000 \/ 0x56000 <= cb_addr b)
    /\ (cb_addr b + cb_size b <= u - 200 \/ u - 200 + 4096 <= cb_addr b).
  Definition apart (b b' : cblock) : Prop :=
    cb_addr b + cb_size b <= cb_addr b' \/ cb_addr b' + cb_size b' <= cb_addr b.
  Fixpoint blocks_apart (LB : list cblock) : Prop :=
    match LB with [] => True | b :: LB' => Forall (apart b) LB' /\ blocks_apart LB' end.
  Definition blocks_ok (u : Z) (LB : list cblock) : Prop := Forall (block_ok u) LB /\ blocks_apart LB.

  Lemma blocks_ok_cons_inv : forall u b LB, blocks_ok u (b :: LB) -> block_ok u b /\ Forall (apart b) LB /\ blocks_ok u LB.
  Proof using Type. pin_using tt. ceil_facts. intros u b LB [H1 [H2 H3]]. apply Forall_cons_iff in H1. destruct H1 as [A B]. split; [exact A|]. split; [exact H2|]. split; [exact B| exact H3]. Qed.

  Lemma blocks_apart_In : forall LB b b', blocks_apart LB -> In b LB -> In b' LB -> b = b' \/ apart b b'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction LB as [|c LB IH]; intros b b' H Hb Hb'; [destruct Hb|].
    destruct H as [Hc H]. destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb'].
    - left; reflexivity.
    - right. exact (proj1 (Forall_forall _ _) Hc _ Hb').
    - right. pose proof (proj1 (Forall_forall _ _) Hc _ Hb) as A. unfold apart in *. lia.
    - apply IH; assumption.
  Qed.

  Lemma blocks_apart_app_inv : forall L1 L2, blocks_apart (L1 ++ L2) ->
    blocks_apart L1 /\ blocks_apart L2 /\ (forall b b', In b L1 -> In b' L2 -> apart b b').
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction L1 as [|c L1 IH]; intros L2 H; cbn in *.
    - repeat split; auto. intros b b' [].
    - destruct H as [Hc H]. apply IH in H as (A & B & C). apply Forall_app in Hc as [Hc1 Hc2].
      repeat split; auto. intros b b' [<-|Hb] Hb'; [exact (proj1 (Forall_forall _ _) Hc2 _ Hb') | apply C; assumption].
  Qed.
End Blocks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shared_const (a : Z) : Prop :=
  (0x544c8 <= a < 0x54550) \/ (0x22d18 <= a < 0x22e28).
(* [comment removed for export] *)
Definition heap_static (a : Z) : Prop := 0x54550 <= a < 0x54908.
(* [comment removed for export] *)
Definition stdio_static (a : Z) : Prop := (0x23e20 <= a < 0x240f0) \/ (0x54908 <= a < 0x55130).
(* [comment removed for export] *)
Definition harn_static (a : Z) : Prop := 0x34150 <= a < 0x34188.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition agrees_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a -> m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Lemma agrees_on_refl : forall P m, agrees_on P m m.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P m a _ _. auto. Qed.
Lemma agrees_on_trans : forall P m1 m2 m3, agrees_on P m1 m2 -> agrees_on P m2 m3 -> agrees_on P m1 m3.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P m1 m2 m3 H1 H2 a Ha Hp. destruct (H1 a Ha Hp) as [E1 W1]. destruct (H2 a Ha Hp) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agrees_on_weaken : forall (P Q : Z -> Prop) m m', agrees_on P m m' -> (forall a, Q a -> P a) -> agrees_on Q m m'.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P Q m m' H HQ a Ha Hq. apply H; auto. Qed.

(* [comment removed for export] *)
Lemma agrees_on_of_munch : forall (P : Z -> Prop) W m m',
  munch W m m' -> wmono usegs m m' -> (forall a, 0 <= a < 2^64 -> P a -> outside W a) -> agrees_on P m m'.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P W m m' MU WM HP a Ha Hp. split.
  - apply MU. rewrite wa_unsigned by lia. apply HP; [exact Ha | exact Hp].
  - apply WM.
Qed.

Lemma agrees_bytes_at : forall P m m' A bs,
  agrees_on P m m' -> bytes_at usegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at usegs m' A bs.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd. destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _].
  rewrite E. reflexivity.
Qed.
Lemma agrees_wr_at : forall P m m' A n,
  agrees_on P m m' -> wr_at usegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at usegs m' A n.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.
Lemma agrees_rw_cells : forall P m m' A cs,
  agrees_on P m m' -> rw_cells usegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells usegs m' A cs.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply agrees_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply agrees_wr_at; eauto.
Qed.
Lemma agrees_stk : forall P m m' lo hi,
  agrees_on P m m' -> stk usegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk usegs m' lo hi.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P m m' lo hi HP (H0 & H1 & HS) HR. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HS a Ha) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kit.
  Context {H hptr : Type}.
  Notation cblk := (@cblock hptr).

  Record modkit := mkMK {
    (* [comment removed for export] *)
    mk_heap : H -> rctx -> list cblk -> mem -> Prop;
    (* [comment removed for export] *)
    mk_stdio : @libc_st hptr -> rctx -> list cblk -> mem -> Prop
  }.

  (* [comment removed for export] *)
  Definition heap_client_iv (R : rctx) (LB : list cblk) (iv : Z * Z) : Prop :=
    CEILZ <= fst iv \/ iv_in_block LB iv
    \/ (0x22000 <= fst iv /\ snd iv <= 0x56000 /\ (snd iv <= 0x22d18 \/ 0x22e28 <= fst iv) /\ (snd iv <= 0x544c8 \/ 0x54908 <= fst iv))
    \/ (utp R - 200 <= fst iv /\ snd iv <= utp R - 200 + 4096).

  (* [comment removed for export] *)
  Definition heap_keeps (R : rctx) (LB : list cblk) (SP : Z) (a : Z) : Prop :=
    SP <= a \/ in_block LB a
    \/ (0x22000 <= a < 0x56000 /\ ~ heap_static a /\ ~ (utp R - 164 <= a < utp R - 160))
    \/ (utp R - 200 <= a < utp R - 200 + 4096 /\ ~ (utp R - 164 <= a < utp R - 160)).
  Definition heap_pres (R : rctx) (LB : list cblk) (SP : Z) (m m' : mem) : Prop :=
    agrees_on (heap_keeps R LB SP) m m'.

  Definition stdio_fp (R : rctx) (FB : list cblk) (a : Z) : Prop := stdio_static a \/ in_block FB a.

  Variable K : modkit.

  (* [comment removed for export] *)
  Definition heap_frame_law : Prop :=
    forall h R LB m m' W, mk_heap K h R LB m -> munch W m m' -> wmono usegs m m' -> Forall (heap_client_iv R LB) W -> mk_heap K h R LB m'.
  Definition heap_blocks_law : Prop :=
    forall h R LB m, mk_heap K h R LB m -> blocks_ok (utp R) LB.
  Definition heap_perm_law : Prop :=
    forall h R LB LB' m, mk_heap K h R LB m -> Permutation.Permutation LB LB' -> mk_heap K h R LB' m.
  Definition heap_addr_law (HO : HeapOps H hptr) : Prop :=
    forall h R LB m b, mk_heap K h R LB m -> In b LB -> ho_addr HO h (cb_tok b) = cb_addr b.
  Definition stdio_fp_law : Prop :=
    forall l R FB m m', mk_stdio K l R FB m -> agrees_on (stdio_fp R FB) m m' -> mk_stdio K l R FB m'.
  (* [comment removed for export] *)
  Definition heap_cb_law : Prop :=
    forall h R LB m b, mk_heap K h R LB m -> mk_heap K h (set_cb R b) LB m.
  Definition stdio_cb_law : Prop :=
    forall l R FB m b, mk_stdio K l R FB m -> mk_stdio K l (set_cb R b) FB m.
  Definition stdio_blocks_law : Prop :=
    forall l R FB m b, mk_stdio K l R FB m -> In b FB -> cb_addr b + cb_size b <= CEILZ /\ (cb_addr b + cb_size b <= 0x10000 \/ 0x56000 <= cb_addr b).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition HARNR (o : option hptr) (FB : list cblk) (m : mem) : Prop :=
    (exists ib : byte, rw_cells usegs m 0x34150 [C1 ib])
    /\ (exists ej : list byte, rw_cells usegs m 0x34160 [CB 32 ej])
    /\ match o with
       | None => rw_cells usegs m 0x34180 [C8 (Z_to_bv 64 0)]
       | Some q => exists A, In (q, A, 1264) FB /\ rw_cells usegs m 0x34180 [C8 (Z_to_bv 64 A)]
       end.
  Definition harn_fp (a : Z) : Prop := harn_static a.

  (* [comment removed for export] *)
  Definition CORE_TLS (R : rctx) (m : mem) : Prop :=
    let u := utp R in
    exists (t : Z) (e : word),
       rw_cells usegs m (u + -200) [C8 (Z_to_bv 64 (u - 200)); C8 (Z_to_bv 64 (u - 200)); C8 (Z_to_bv 64 (u - 200)); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m (u + -164) [C4 e]
    /\ rw_cells usegs m (u + -160) [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 (u - 80));
                                   CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x54520); CB 24 (repeat (Z_to_bv 8 0) 24)]
    /\ rw_cells usegs m (u + -16) [C8 (rc_canary R)]                      (* [comment removed for export] *)
    /\ rw_cells usegs m (u + -8) [C8 (Z_to_bv 64 (u + 264))]
    /\ rw_cells usegs m (u + 256) [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (u + 2048)); CB 3616 (repeat (Z_to_bv 8 0) 3616)]
    /\ (0 < t < 4194304).
  Definition core_tls_fp (R : rctx) (a : Z) : Prop := (utp R - 200 <= a < utp R) \/ (utp R + 256 <= a < utp R - 200 + 4096).

  (* [comment removed for export] *)
  Definition PCAP_TLS (R : rctx) (m : mem) : Prop := exists bs, rw_cells usegs m (utp R) [CB 256 bs].
  Definition pcap_tls_fp (R : rctx) (a : Z) : Prop := utp R <= a < utp R + 256.

  (* [comment removed for export] *)
  Definition CORE_LIBC (R : rctx) (m : mem) : Prop :=
    rw_cells usegs m 0x544e8 (libc_cells (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 64 0)
                                (Z_to_bv 64 (auxv_addr (rc_sp0 R) (rc_argv R) (rc_envp R))) (Z_to_bv 64 0x54268) (Z_to_bv 64 480)
                                (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 4096) (repeat (Z_to_bv 8 0) 48))
    /\ rw_cells usegs m 0x22de0 [C8 (Z_to_bv 64 0x544c8)]
    /\ rw_cells usegs m 0x544c8 [C8 (rc_canary R)]                        (* [comment removed for export] *)
    /\ rw_cells usegs m 0x544d0 [C8 (Z_to_bv 64 0)]
    /\ (exists (pg : word) (P0 : Z), rw_cells usegs m 0x544d8 [C8 pg; C8 (Z_to_bv 64 P0)]
                                  /\ nth_error (InitMem.argv_ptrs (rc_inp R) (rc_sp0 R) (rc_rnd R)) 0 = Some (Z_to_bv 64 P0)).
  Definition core_libc_fp (a : Z) : Prop := (0x544c8 <= a < 0x54550) \/ (0x22de0 <= a < 0x22de8).

  (* [comment removed for export] *)
  Definition CORE_MISC (m : mem) : Prop :=
       rw_cells usegs m 0x22d78 [C8 (Z_to_bv 64 0x22d20)] /\ rw_cells usegs m 0x22d20 [C8 (Z_to_bv 64 0x23e20)]   (* [comment removed for export] *)
    /\ rw_cells usegs m 0x22db0 [C8 (Z_to_bv 64 0x22d28)] /\ rw_cells usegs m 0x22d28 [C8 (Z_to_bv 64 0x23f10)]   (* [comment removed for export] *)
    /\ rw_cells usegs m 0x22d80 [C8 (Z_to_bv 64 0)]                                                               (* [comment removed for export] *)
    /\ rw_cells usegs m 0x22d90 [C8 (Z_to_bv 64 0x14b64); C8 (Z_to_bv 64 0x147dc); C8 (Z_to_bv 64 0x14a64); C8 (Z_to_bv 64 0x1422c)]. (* [comment removed for export] *)
  Definition core_misc_fp (a : Z) : Prop :=
    (0x22d78 <= a < 0x22db0) \/ (0x22d20 <= a < 0x22d30) \/ (0x22db0 <= a < 0x22db8).

  (* [comment removed for export] *)
  Definition ATX (cb : bool) (m : mem) : Prop :=
    exists (reg : bool) (pad : list byte) (f0 g0 : word) (j1 j2 : list byte),
       rw_cells usegs m 0x34150 [C1 (bool8 reg); CB 3 pad; C1 (bool8 cb)]
    /\ rw_cells usegs m 0x542a0 (atexit_cells (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 3) (atx_slot reg) (repeat (Z_to_bv 8 0) 4) (atx_head reg))
    /\ rw_cells usegs m 0x542b8 (builtin_cells f0 j1 g0 j2)
    /\ (reg = true -> f0 = Z_to_bv 64 0x18bc8 /\ g0 = Z_to_bv 64 0x13fac).
  Definition atx_fp (a : Z) : Prop := (0x34150 <= a < 0x34155) \/ (0x542a0 <= a < 0x544c0).

  (* [comment removed for export] *)
  Definition CORE_EXIT (cb : bool) (m : mem) : Prop :=
       rw_cells usegs m 0x544c0 [C4 (Z_to_bv 64 0)]
    /\ ATX cb m
    /\ rw_cells usegs m 0x22de8 [C8 (Z_to_bv 64 0x22d20); C8 (Z_to_bv 64 0x22d18)]
    /\ rw_cells usegs m 0x22d18 [C8 (Z_to_bv 64 0x13af4)]
    /\ rw_cells usegs m 0x24148 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs m 0x22d68 [C8 (Z_to_bv 64 0x18b00); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m 0x23df8 [C8 (Z_to_bv 64 0x23df8)].
  Definition core_exit_fp (a : Z) : Prop :=
    (0x544c0 <= a < 0x544c4) \/ (0x542a0 <= a < 0x544c0) \/ (0x22de8 <= a < 0x22df8) \/ (0x22d18 <= a < 0x22d20)
    \/ (0x24148 <= a < 0x24149) \/ (0x22d68 <= a < 0x22d78) \/ (0x23df8 <= a < 0x23e00) \/ (0x34150 <= a < 0x34155).

  (* PORTED to 75d69e00, identically to the Plain kit (GI.v:306-367): the image
     is [Run.entry_stack_image] of the ported tuple (Run.v:1344) and the launch
     fact travels with it, because the image now runs from [sp] to [ed_top]. *)
  Definition rc_launch (R : rctx) : Prop :=
    exists brk : word,
      entry_launch_ok_va Sv48 (mkEntry (rc_sp0 R) brk (rc_mb R) (rc_rnd R)) (rc_inp R).
  Definition CORE_STK (R : rctx) (m : mem) : Prop :=
    rc_launch R
    /\ bytes_at usegs m (usp0 R)
         (entry_stack_image (rc_inp R) (rc_mb R) (rc_ph R) (rc_entry R) (rc_sp0 R) (rc_rnd R)).
  Definition core_stk_fp (R : rctx) (a : Z) : Prop :=
    usp0 R <= a < usp0 R
      + Z.of_nat (length (entry_stack_image (rc_inp R) (rc_mb R) (rc_ph R) (rc_entry R) (rc_sp0 R) (rc_rnd R))).

  (* PROVENANCE (rule 23c): [Common/CatSim__Common.v:1361]
     [launch_string_base_arith], whose unit this one does not depend on.
     [valid_launch_sp]'s upper bound, 75d69e00:theories/LinuxProcessSem/Run.v:3656
     with [launch_sp_hi] at :3641 and [align_down16] at :3572. *)
  Lemma rc_span : forall R, rc_launch R ->
    (usp0 R + InitMem.struct_size (rc_inp R) + InitMem.str_len (rc_inp R) + 8
     <= bv_unsigned (rc_top R))%Z.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros R [brk LA]. cbn [entry_launch_ok_va] in LA.
    destruct LA as (_ & (_ & _ & Hhi) & _).
    unfold usp0, rc_top, InitMem.struct_size, InitMem.str_len.
    unfold launch_sp_hi, align_down16 in Hhi.
    pose proof (Z.mod_pos_bound
      (bv_unsigned (ed_top (rc_rnd R)) - 8
       - Z.of_nat (launch_string_bytes (in_argv (rc_inp R)) (in_envp (rc_inp R))
                     (in_execfn (rc_inp R)))) 16 ltac:(lia)).
    lia.
  Qed.

  (* [valid_stack_top_va]'s first conjunct (Run.v:3610): [top mod page_size = 0],
     strictly stronger than the [mod 8] [stack_argv_string_slack] now needs. *)
  Lemma rc_top_align : forall R, rc_launch R -> (bv_unsigned (rc_top R) mod 8 = 0)%Z.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros R [brk LA]. cbn [entry_launch_ok_va] in LA.
    destruct LA as ((HP & _ & _) & _ & _). unfold rc_top.
    unfold page_size in HP.
    pose proof (Z.div_mod (bv_unsigned (ed_top (rc_rnd R))) 4096 ltac:(lia)) as D.
    assert (E : bv_unsigned (ed_top (rc_rnd R))
                = (512 * (bv_unsigned (ed_top (rc_rnd R)) / 4096) * 8)%Z) by lia.
    rewrite E. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition GI (R : rctx) (s : PState H hptr) (CL : list cblk) (m : mem) : Prop :=
    exists FB : list cblk,
       mk_heap K (ps_heap s) R (CL ++ FB) m
    /\ mk_stdio K (ps_libc s) R FB m
    /\ HARNR (ps_outfile s) FB m
    /\ CORE_TLS R m /\ PCAP_TLS R m /\ CORE_LIBC R m /\ CORE_MISC m /\ CORE_EXIT (rc_cb R) m /\ CORE_STK R m
    /\ ps_tls s = utp R - 200 /\ tls_block_ok_u (utp R - 200)
    /\ blocks_ok (utp R) (CL ++ FB)
    /\ 0x7fff80000000 <= usp0 R <= 2^47       (* [comment removed for export] *)
    /\ CEILZ <= usp0 R - 8388608.             (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition SXGI (s : PState H hptr) (tp : word) (m : mem) : Prop :=
    exists (R : rctx) (CL FB : list cblk),
       rc_tp R = tp
    /\ mk_heap K (ps_heap s) R (CL ++ FB) m
    /\ mk_stdio K (ps_libc s) R FB m
    /\ HARNR (ps_outfile s) FB m
    /\ CORE_TLS R m /\ PCAP_TLS R m /\ CORE_LIBC R m /\ CORE_MISC m
    /\ ps_tls s = utp R - 200 /\ tls_block_ok_u (utp R - 200)
    /\ blocks_ok (utp R) (CL ++ FB).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac tr AG HP A := eapply agrees_rw_cells; [exact AG | exact A | intros a Ha; apply HP; sl_lit_sizes_in Ha; cbn in Ha; lia].

  Lemma HARNR_agree : forall P o FB m m', agrees_on P m m' -> (forall a, harn_fp a -> P a) -> HARNR o FB m -> HARNR o FB m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P o FB m m' AG HP ((ib & A1) & (ej & A2) & A3). unfold harn_fp, harn_static in HP. split; [|split].
    - exists ib. tr AG HP A1.
    - exists ej. tr AG HP A2.
    - destruct o as [q|]; [destruct A3 as (A & HA & A3); exists A; split; [exact HA|] |]; tr AG HP A3.
  Qed.

  Lemma CORE_TLS_agree : forall P R m m', agrees_on P m m' -> (forall a, core_tls_fp R a -> P a) -> CORE_TLS R m -> CORE_TLS R m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P R m m' AG HP (t & e & A1 & A2 & A3 & A4 & A5 & A6 & Ht). unfold core_tls_fp in HP. exists t, e.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|]. split; [tr AG HP A5|]. split; [tr AG HP A6| exact Ht].
  Qed.

  Lemma PCAP_TLS_agree : forall P R m m', agrees_on P m m' -> (forall a, pcap_tls_fp R a -> P a) -> PCAP_TLS R m -> PCAP_TLS R m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P R m m' AG HP (bs & A1). unfold pcap_tls_fp in HP. exists bs. tr AG HP A1. Qed.

  Lemma CORE_LIBC_agree : forall P R m m', agrees_on P m m' -> (forall a, core_libc_fp a -> P a) -> CORE_LIBC R m -> CORE_LIBC R m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P R m m' AG HP (A1 & A2 & A3 & A4 & (pg & P0 & A5 & HP0)). unfold core_libc_fp in HP. unfold libc_cells in *.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|]. exists pg, P0. split; [tr AG HP A5| exact HP0].
  Qed.

  Lemma CORE_MISC_agree : forall P m m', agrees_on P m m' -> (forall a, core_misc_fp a -> P a) -> CORE_MISC m -> CORE_MISC m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6). unfold core_misc_fp in HP.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|]. split; [tr AG HP A5| tr AG HP A6].
  Qed.

  Lemma ATX_agree : forall P cb m m', agrees_on P m m' -> (forall a, atx_fp a -> P a) -> ATX cb m -> ATX cb m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P cb m m' AG HP (reg & pad & f0 & g0 & j1 & j2 & A1 & A2 & A3 & A4). unfold atx_fp in HP. unfold atexit_cells, builtin_cells in *.
    exists reg, pad, f0, g0, j1, j2. split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3| exact A4].
  Qed.

  Lemma CORE_EXIT_agree : forall P cb m m', agrees_on P m m' -> (forall a, core_exit_fp a -> P a) -> CORE_EXIT cb m -> CORE_EXIT cb m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros P cb m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold core_exit_fp in HP.
    split; [tr AG HP A1|]. split; [eapply ATX_agree; [exact AG| |exact A2]; intros a Ha; apply HP; unfold atx_fp in Ha; lia|].
    split; [tr AG HP A3|]. split; [tr AG HP A4|]. split; [tr AG HP A5|]. split; [tr AG HP A6| tr AG HP A7].
  Qed.

  Lemma CORE_STK_agree : forall P R m m', agrees_on P m m' -> (forall a, core_stk_fp R a -> P a) -> CORE_STK R m -> CORE_STK R m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros P R m m' AG HP (LA & A1). unfold core_stk_fp in HP. unfold CORE_STK in *. split; [exact LA|]. eapply agrees_bytes_at; [exact AG| exact A1| intros a Ha; apply HP; lia]. Qed.
End Kit.
End WithCeil.

Arguments modkit H hptr : clear implicits.
End TwB.
