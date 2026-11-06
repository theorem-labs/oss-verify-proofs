(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 823 of its 864 lines of code are new or changed and 970 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3F.v, with its module names changed; 207 of its 257 lines of code are new or changed and 814 lines of the source are left out. *)
(* lib/B/Prog/reac_ctrl_identity_reply_c_on.v -- route (C) (a Theorem Labs lane 09:20Z; form of record lib/B/ShadowRwOn.v; wave lead
   a Theorem Labs lane; stream lead a Theorem Labs lane 11:13Z, route (C) phase 2 for the image-B reply run, writer a Theorem Labs lane): the ADDITIVE
   `_on` twins of lib/B/Prog/reac_ctrl_identity_reply_c.v's two contracts, with the three bridge lemmas of the image-B
   `_on` family (a Theorem Labs lane's twins). reac_ctrl_identity_reply_c.v
   stays unchanged apart from comment text. Image-B twin of a Theorem Labs lane's image-A text (lib/A/Prog/reac_ctrl_identity_reply_c.v (a version not in this delivery),
   a working branch): the three Definitions are A's apart from the image prefix (lib.A to lib.B) and one
   comment line of the plain contract, `asan-ubsan` in B's accepted contract where A's says `asan`.
   Each `_on` contract is the accepted Definition with exactly two changes: the premise `shadow_rw m` becomes
   `shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) m`, and the post's `shadow_rw m'` becomes
   `forall P, shadow_rw_on P m -> shadow_rw_on P m'`.
   The run that proves reac_ctrl_identity_reply_contract_F_on is lib/B/Prog/reac_ctrl_identity_replyF_on.v (not in this delivery).
   rule 24: proof-index reac_ctrl_identity_reply reac_ctrl_identity_reply_contract_F (recorded in the lane's
   lookup-reac_ctrl_identity_reply.txt (a working note, not in this delivery); checker's verdict CONFIRM, lookup-check.md (a working note, not in this delivery)): At ossv/recipes c5e779efe8c (2026-10-31), no released
   proof outside this unit; this file proves no function (statement text and bridge lemmas between statements only). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c RcAsanFP
  reac_ctrl_parse_c asan_stack_malloc_c_on reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.
Import ListNotations.
Local Open Scope Z_scope.

(* The shadow bytes the run reaches through shadow_rw. A = (S - 128) / 32 * 32 (the 128-byte frame below S, rounded
   down to 32: `rA` below; lib/B/Prog/reac_ctrl_identity_replyF.v rA) and G = A - 128.
   Derivation: the measurement of the proved run lib/B/Prog/reac_ctrl_identity_replyF.v (blob 157b9195af24). The run's
   own shadow_rw need is the 16 shadow bytes of one frame G: rk_facts (replyF :1493) and rr_shadow16_stk (replyF
   :995-1003, used at :3012, :3714, :3780, :4041), where G is the real-stack frame rA - 128 or the side-stack frame
   fs_frame FS 1 j (replyF rFK :1448-1450). The shadow of the window, of fr and of the OUT cells comes from the
   `addressable` premises, not from shadow_rw; so does the shadow of reac_ctrl_parse's window that the run reads back
   after the call (addressable at the callee's return). The rest flows through the callees' contracts, at the
   call-site arguments of the K comment of reac_ctrl_identity_reply_c.v: reac_ctrl_parse runs at G on the real stack or
   at A on the side stack, __asan_stack_malloc_1 at A; reac_ctrl_record_cksum_verify's narrowed contract names no
   shadow.
   - (1) the real-stack frame G = rA - 128: its 16 shadow bytes [shadow_addr G, shadow_addr G + 16);
   - (2) asan_stack_malloc_shadow_R FS 1%nat: the class-1 fake-stack block, __asan_stack_malloc_1's own region (its
     `_on` premise, lib/B/Prog/asan_stack_malloc_c_on.v); the side-stack frame fs_frame FS 1 j it returns has its 16
     shadow bytes inside it;
   - (3) reac_ctrl_parse called on the real-stack arm: sp = G = rA - 128, record o = G + 32 = rA - 96;
   - (4) reac_ctrl_parse called on the side-stack arm: sp = rA, record o = fs_frame FS 1 j + 32, for the class-1 frame j
     that __asan_stack_malloc_1 chooses (0 <= j < fs_M 1).
   (3) and (4) hold only under `reply_args fr pa pp pn = true` (ruling via a Theorem Labs lane 13:37Z, lockstep with image A): the
   run calls reac_ctrl_parse only past its null checks (replyF rKN), and parse's region names the words of the 50
   bytes at fr, which the spec gives a heap block only under reply_args. (1) and (2) are unguarded: the prologue and
   __asan_stack_malloc_1 run before the null checks.
   At a cut (lib/B/ACtlRtC.v cut_shadow, the three current disjuncts (F) frames, (L) live blocks, (Z)
   zero_shadow_ranges, and img_shadow (I)): (1), the real-stack frames inside (3) and (4) and the box words of the
   real-stack arm are machine-stack shadow, the first entry of zero_shadow_ranges (Reusable/YG0n.v:188-189), so (Z)
   closes them; (2), and the class-1 block parts of
   (3) and (4) (their asan_stack_malloc_shadow_R FS 1 disjunct, and the box words of a side frame), need a Theorem Labs lane's
   4th disjunct (the class-c side-stack block shadow), or (F) for the one frame that is live; the words of the 50 bytes
   at fr lie in (L) or (Z) by where the caller's buffer lives, and the words of the 6 bytes at BC in (I). *)
Definition reac_ctrl_identity_reply_shadow_R (fr len pa pp pn S FS : Z) (a : Z) : Prop :=
  let rA := (S - 128) / 32 * 32 in
  (shadow_addr (rA - 128) <= a < shadow_addr (rA - 128) + 16) \/
  asan_stack_malloc_shadow_R FS 1%nat a \/
  (reply_args fr pa pp pn = true /\ reac_ctrl_parse_shadow_R fr len (rA - 96) (rA - 128) FS a) \/
  (reply_args fr pa pp pn = true /\
   exists j, 0 <= j < fs_M 1 /\ reac_ctrl_parse_shadow_R fr len (fs_frame FS 1 j + 32) rA FS a).

(* reac_ctrl_identity_reply_contract with the narrowed shadow premise and post; nothing else differs. *)
Definition reac_ctrl_identity_reply_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr len pa pp pn S FS : Z)
         (g ja jp jn : list byte),
    a0 = Z_to_bv 64 fr -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 pa -> a3 = Z_to_bv 64 pp -> a4 = Z_to_bv 64 pn ->
    sp = Z_to_bv 64 S ->
    0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_IDENTITY_REPLY_K <= S -> stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    mem_inv rsegs m ->
    length g = 50%nat ->
    (reply_args fr pa pp pn = true -> 50 <= len ->
       fr + 50 <= 2^64 /\ bytes_at rsegs m fr g /\ (fr + 50 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= fr)) ->
    (reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn) /\
       (pa + 2 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pa) /\
       (pp + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pp) /\
       (pn + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pn)) ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    (reply_args fr pa pp pn = true -> 50 <= len -> addressable m fr 50) ->
    (reply_args fr pa pp pn = true ->
       addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S (reac_ctrl_identity_reply_W fr pa pp pn S)
      (reac_ctrl_identity_reply_D fr len pa pp pn) ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (reply_ret fr len pa pp pn g))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_identity_reply_fp fr len pa pp pn S g ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
         (reply_ok fr len pa pp pn g = true ->
            rw_cells rsegs m' pa [CB 2 (reply_addr g)] /\
            rw_cells rsegs m' pp [CB 8 (le8 (Z_to_bv 64 (fr + 38)))] /\
            rw_cells rsegs m' pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))]) /\
         asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
           (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) /\
         reac_ctrl_identity_reply_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs)).

(* reac_ctrl_identity_reply_contract_F with the narrowed shadow premise and post; nothing else differs (the footprint
   premises are the accepted ones). *)
Definition reac_ctrl_identity_reply_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr len pa pp pn S FS : Z)
         (g ja jp jn : list byte),
    a0 = Z_to_bv 64 fr -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 pa -> a3 = Z_to_bv 64 pp -> a4 = Z_to_bv 64 pn ->
    sp = Z_to_bv 64 S ->
    0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_IDENTITY_REPLY_K <= S -> stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    mem_inv rsegs m ->
    length g = 50%nat ->
    (reply_args fr pa pp pn = true -> 50 <= len ->
       fr + 50 <= 2^64 /\ bytes_at rsegs m fr g /\ (fr + 50 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= fr) /\
       (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)) ->
    (reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pa) /\
       (pp + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pp) /\
       (pn + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pn)) ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    (reply_args fr pa pp pn = true -> 50 <= len -> addressable m fr 50) ->
    (reply_args fr pa pp pn = true ->
       addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S (reac_ctrl_identity_reply_W fr pa pp pn S)
      (reac_ctrl_identity_reply_D fr len pa pp pn) ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    (* footprint *)
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K))
      (shadow_addr S - shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K)) ->
    (reply_args fr pa pp pn = true -> 50 <= len -> ExecF.rng RNG fr 50) ->
    (reply_args fr pa pp pn = true -> 50 <= len ->
       ExecF.rng RNG (shadow_addr fr / 8 * 8) (shadow_addr (fr + 49) / 8 * 8 + 8 - shadow_addr fr / 8 * 8)) ->
    (reply_args fr pa pp pn = true -> ExecF.rng RNG pa 2) ->
    (reply_args fr pa pp pn = true -> ExecF.rng RNG (shadow_addr pa) (shadow_addr (pa + 1) - shadow_addr pa + 1)) ->
    (reply_args fr pa pp pn = true -> ExecF.rng RNG pp 8) ->
    (reply_args fr pa pp pn = true -> ExecF.rng RNG (shadow_addr pp) (shadow_addr (pp + 7) - shadow_addr pp + 1)) ->
    (reply_args fr pa pp pn = true -> ExecF.rng RNG pn 8) ->
    (reply_args fr pa pp pn = true -> ExecF.rng RNG (shadow_addr pn) (shadow_addr (pn + 7) - shadow_addr pn + 1)) ->
    ExecF.rng RNG (shadow_addr REAC_CTRL_PARSE_BC / 8 * 8)
      (shadow_addr (REAC_CTRL_PARSE_BC + 5) / 8 * 8 + 8 - shadow_addr REAC_CTRL_PARSE_BC / 8 * 8) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (reply_ret fr len pa pp pn g))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_identity_reply_fp fr len pa pp pn S g ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
         (reply_ok fr len pa pp pn g = true ->
            rw_cells rsegs m' pa [CB 2 (reply_addr g)] /\
            rw_cells rsegs m' pp [CB 8 (le8 (Z_to_bv 64 (fr + 38)))] /\
            rw_cells rsegs m' pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))]) /\
         asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
           (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) /\
         reac_ctrl_identity_reply_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs)).

(* The old contracts from the `_on` forms: the narrowed premise by shadow_rw_on_of_shadow_rw, the old post's
   shadow_rw m' by the `_on` post at P := fun _ => True and shadow_rw_of_on_all (Lib/Exec.v evt_mono, ExecF.evtF_mono
   weaken the post); and the `_on` pair's reac_ctrl_identity_reply_contract_of_F (its proof, unchanged: the region
   premise and the post pass through). Names and shapes as a Theorem Labs lane's image-B twins (lib/B/Prog/ctrl_lay_block_c.v,
   a working branch 1d3f3f868d5): _contract_of_on, _contract_F_of_F_on, _contract_on_of_F_on. *)
Lemma reac_ctrl_identity_reply_contract_of_on :
  reac_ctrl_identity_reply_contract_on -> reac_ctrl_identity_reply_contract.
Proof.
  intros HO. unfold reac_ctrl_identity_reply_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    fr len pa pp pn S FS g ja jp jn.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Hsp Hfr Hlen Hpa Hpp Hpn HS HS16 HKS Hstk Hmi Hg Hfrb Hargs Hac Hsw Hhm Hae Haddr
    Hfra Hargsa Hbc Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  eapply lib.Lib.Exec.evt_mono.
  - apply (HO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m fr len pa pp pn S FS g ja jp jn);
      first [ assumption | exact (shadow_rw_on_of_shadow_rw _ m Hsw) ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hok & Hac' & Hsw' & Haddr' & Hfp' & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hok|]. split; [exact Hac'|].
    split; [exact (shadow_rw_of_on_all m' (Hsw' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m Hsw)))|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. exact Htls'.
Qed.

Lemma reac_ctrl_identity_reply_contract_F_of_F_on :
  reac_ctrl_identity_reply_contract_F_on -> reac_ctrl_identity_reply_contract_F.
Proof.
  intros HO. unfold reac_ctrl_identity_reply_contract_F. intros RNG.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    fr len pa pp pn S FS g ja jp jn.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Hsp Hfr Hlen Hpa Hpp Hpn HS HS16 HKS Hstk Hmi Hg Hfrb Hargs Hac Hsw Hhm Hae Haddr
    Hfra Hargsa Hbc Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  intros Hrbt Himg Hwin Hwins Hfrr Hfrs Hpar Hpas Hppr Hpps Hpnr Hpns Hbcs Hhdr Hfw Htlsr.
  eapply ExecF.evtF_mono.
  - apply (HO RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m fr len pa pp pn S FS g ja jp jn);
      first [ assumption | exact (shadow_rw_on_of_shadow_rw _ m Hsw) ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hok & Hac' & Hsw' & Haddr' & Hfp' & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hok|]. split; [exact Hac'|].
    split; [exact (shadow_rw_of_on_all m' (Hsw' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m Hsw)))|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. exact Htls'.
Qed.

Lemma reac_ctrl_identity_reply_contract_on_of_F_on :
  reac_ctrl_identity_reply_contract_F_on -> reac_ctrl_identity_reply_contract_on.
Proof.
  unfold reac_ctrl_identity_reply_contract_F_on, reac_ctrl_identity_reply_contract_on. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    fr len pa pp pn S FS g ja jp jn.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Hsp Hfr Hlen Hpa Hpp Hpn HS HS16 HKS Hstk Hmi Hg Hrd Hout Hac Hsw Hhm Hae Haddr
    Hfa Houta Hbc Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  pose proof (eq_refl : REAC_CTRL_IDENTITY_REPLY_K = 9072) as HK.
  pose proof Hfp as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
           t5 t6 F fc m fr len pa pp pn S FS g ja jp jn); try assumption.
  - (* fr's data premise, with the fr apartness of the out premise *)
    intros Har H50. destruct (Hrd Har H50) as (Hf1 & Hf2 & Hf3).
    destruct (Hout Har) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ha & Hp & Hn & _).
    exact (conj Hf1 (conj Hf2 (conj Hf3 (conj Ha (conj Hp Hn))))).
  - (* the out premise, without the fr apartness *)
    intros Har. destruct (Hout Har) as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & _ & _ & _ & O10 & O11 & O12).
    exact (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 (conj O7 (conj O8 (conj O9
      (conj O10 (conj O11 O12))))))))))).
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; lia.
  - (* window *) apply ExecF.rng_all; clear - HS HKS; lia.
  - apply ExecF.rng_all; clear - HS HKS HK; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* fr *) intros Har H50. destruct (Hrd Har H50) as (Hf1 & _). apply ExecF.rng_all; clear - Hfr Hf1; lia.
  - intros Har H50. destruct (Hrd Har H50) as (Hf1 & _).
    apply ExecF.rng_all; clear - Hfr Hf1; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* pa *) intros Har. destruct (Hout Har) as (Hpa2 & _). apply ExecF.rng_all; clear - Hpa Hpa2;
      Z.div_mod_to_equations; lia.
  - intros _. apply ExecF.rng_all; clear - Hpa; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* pp *) intros Har. destruct (Hout Har) as (_ & Hpp8 & _). apply ExecF.rng_all; clear - Hpp Hpp8;
      Z.div_mod_to_equations; lia.
  - intros _. apply ExecF.rng_all; clear - Hpp; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* pn *) intros Har. destruct (Hout Har) as (_ & _ & Hpn8 & _). apply ExecF.rng_all; clear - Hpn Hpn8;
      Z.div_mod_to_equations; lia.
  - intros _. apply ExecF.rng_all; clear - Hpn; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* BC *)
    apply ExecF.rng_all; unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; clear - HFS0 HFSl HS HK E0; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      clear - HFS0 HFSl HS HK EM E1 EF EH;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    clear - Hiv Hc1 Hc1' Hc2 Hc2' Hc3 Hc3' Hc4 Hc4' Hc5 Hc5' Hc6 Hc6' Hc7 Hc7' Hc8 Hc8' Hc9 Hc9' Hc10 Hc10'
      Hc11 Hc11' Hc12 Hc12' Hc13 Hc13' Hc14 Hc14' Hc15 Hc15' Hc16 Hc16' Hc17 Hc17'.
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.
