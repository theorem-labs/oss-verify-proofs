From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c RcAsanFP
  reac_ctrl_parse_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_IDENTITY_REPLY : Z := 0x83f8c.
(* K = 272 + max(K of reac_ctrl_parse 8800, __asan_stack_malloc_1 208): the frame is 128 bytes, A = S - 128 rounded
   down to 32; the 128-byte ASan frame G (class 1) is A - 128 >= S - 272 on the real stack or a side-stack frame;
   reac_ctrl_parse runs at G (real stack) or A (side stack), __asan_stack_malloc_1 at A; the probe writes 8 bytes at
   A - 4096 >= S - 4240 (contracts/libreac/reac_ctrl_identity_reply.md Names). *)
Definition REAC_CTRL_IDENTITY_REPLY_K : Z := 9072.

Definition reac_ctrl_identity_reply_fp (fr len pa pp pn S : Z) (g : list byte) : list (Z * Z) :=
  (if reply_ok fr len pa pp pn g then [(pa, pa + 2); (pp, pp + 8); (pn, pn + 8)] else []) ++
  [(S - REAC_CTRL_IDENTITY_REPLY_K, S)].

(* The writes outside the side stack (fp's W) and the data ranges (fp's D). *)
Definition reac_ctrl_identity_reply_W (fr pa pp pn S : Z) : list ivl :=
  (S - REAC_CTRL_IDENTITY_REPLY_K, S) ::
  (if reply_args fr pa pp pn then [(pa, pa + 2); (pp, pp + 8); (pn, pn + 8)] else []).
Definition reac_ctrl_identity_reply_D (fr len pa pp pn : Z) : list ivl :=
  if reply_args fr pa pp pn
  then (if len <? 50 then [] else [(fr, fr + 50)]) ++ [(pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]
  else [].

(* The thread cells that fp names are apart from the class-1 side-stack bytes (struct.asan.runtime RT4.3) and from
   the shadow of the function's own window [lo, hi): the function's own frame and reac_ctrl_parse's frame on the side
   stack or on the real stack keep them. *)
Definition reac_ctrl_identity_reply_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [1%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

(* The plain contract (lib/Prog/reac_ctrl_identity_reply_c.v) with K = 9072 and the premises of the asan build (S1.5,
   S1.6 of the English contract): the runtime's cells and shadow (asan_cells, shadow_rw), the window in AppMem and
   addressable, the addressable bytes at fr (own shadow checks and reac_ctrl_parse) and at OUT (own store checks),
   OUT apart from [RT_LO, RT_HI) (asan_cells at the return); for reac_ctrl_parse the addressable bytes at BC and the
   cells the bcmp wrapper reads; and the side-stack state for the own __asan_stack_malloc_1 and reac_ctrl_parse's
   (fp [1%nat], reac_ctrl_identity_reply_tls). The run may also write the class-1 side-stack bytes (fp_w [1%nat] FS)
   and the shadow of its window. *)
Definition reac_ctrl_identity_reply_contract : Prop :=
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
    (* asan *)
    asan_cells m -> shadow_rw m ->
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
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
           (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) /\
         reac_ctrl_identity_reply_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs)).

(* ==== Route (C) (a Theorem Labs lane 09:20Z; form of record lib/A/ShadowRwOn.v, a working branch ea8776b2302; wave lead
   a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery); writer a Theorem Labs lane): reac_ctrl_identity_reply_contract above with the
   universal premise `shadow_rw m` narrowed to
   `shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) m` and the post's `shadow_rw m'` stated as
   `forall P, shadow_rw_on P m -> shadow_rw_on P m'`. Every Definition above stays
   byte-identical; the old contract is the corollary reac_ctrl_identity_reply_contract_of_on at the end.
   rule 24: no function proved here (two Definitions and a one-line corollary; no run proof). ==== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c_on sh_word_on.

(* The shadow bytes the run reaches through shadow_rw. A = (S - 128) / 32 * 32 (the 128-byte frame below S, rounded
   down to 32: `rA` below) and G = A - 128.
   Derivation: a Theorem Labs lane's measurement of the proved image-B twin lib/B/Prog/reac_ctrl_identity_replyF.v (not in this delivery).
   The run's own shadow_rw need is the 16 shadow bytes of one frame G: rr_shadow16_stk (replyF (an earlier version, blob 157b9195af24, not in this delivery)
   :995-1003) and rk_facts (replyF :1493), where G is the real-stack frame rA - 128 or the side-stack frame
   fs_frame FS 1 j (replyF rFK). The shadow of the window, of fr and of the OUT cells comes from the `addressable`
   premises, not from shadow_rw. The rest flows through the callees' contracts, at the call-site arguments of the
   K comment above: reac_ctrl_parse runs at G on the real stack or at A on the side stack, __asan_stack_malloc_1 at A.
   - the real-stack frame G = rA - 128: its 16 shadow bytes [shadow_addr G, shadow_addr G + 16);
   - asan_stack_malloc_shadow_R FS 1%nat: the shadow of the class-1 fake-stack block, __asan_stack_malloc_1's own
     region (its `_on` premise at c = 1); the side-stack frame fs_frame FS 1 j it returns has its 16 shadow bytes
     inside it;
   - reac_ctrl_parse called on the real-stack arm: sp = G = rA - 128, record o = G + 32 = rA - 96;
   - reac_ctrl_parse called on the side-stack arm: sp = rA, record o = fs_frame FS 1 j + 32, for the class-1 frame j
     that __asan_stack_malloc_1 chooses (0 <= j < fs_M 1).
   The two reac_ctrl_parse disjuncts are guarded by `reply_args fr pa pp pn = true` (found by a Theorem Labs lane;
   agreed in lockstep with the image-B twin, 2026-10-29 13:3xZ). Why: reac_ctrl_parse_shadow_R holds the aligned
   shadow words of fr's 50 bytes (its `50 <= n` disjunct), and fr is a real block only under reply_args (the fr
   premises of the contract sit under `reply_args ... = true -> 50 <= len`), so without the guard a caller with a null
   argument would owe the shadow of fr = 0's cover. And when reply_args is false the run never reaches the call: in
   the image-B twin's proof the prologue (segment 1: the frame, __asan_stack_malloc_1, the frame's 16 shadow bytes)
   comes first, then the null tests (segment 2, rp_null) send a null fr, pa, pp or pn to the epilogue with a0 = -1
   (reply_ret) before reac_ctrl_parse. The own-frame and __asan_stack_malloc_1 disjuncts stay unguarded: they belong
   to the prologue. The guard only removes bytes: every byte of this R is in the unguarded R, so R shrinks and the
   `_on` premise weakens. *)
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
    (* asan *)
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

(* The old contract from its `_on` form: the narrowed premise by shadow_rw_on_of_shadow_rw, the old post's shadow_rw m'
   by the `_on` post at P := fun _ => True and shadow_rw_of_on_all (Lib/Exec.v:126 evt_mono weakens the post). *)
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
