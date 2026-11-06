From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c RcAsanFP
  reac_ctrl_parse_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_IDENTITY_REPLY : Z := 0x848fc.
(* K = 272 + max(K of reac_ctrl_parse 8800, reac_ctrl_record_cksum_verify 16, __asan_stack_malloc_1 208): the frame
   is 128 bytes, A = S - 128 rounded down to 32; the 128-byte ASan frame G (class 1) is A - 128 >= S - 272 on the
   real stack or a side-stack frame; reac_ctrl_parse and reac_ctrl_record_cksum_verify run at G (real stack) or A
   (side stack), __asan_stack_malloc_1 at A; the probe writes 8 bytes at A - 4096 >= S - 4240
   (contracts/libreac/reac_ctrl_identity_reply.md Names). *)
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

(* The ubsan contract (lib/U/Prog/reac_ctrl_identity_reply_c.v, the plain form) with K = 9072 and the premises of
   the asan-ubsan build (S1.5, S1.6 of the English contract): the runtime's cells and shadow (asan_cells, shadow_rw),
   the window in AppMem and addressable, the addressable bytes at fr (own shadow checks, reac_ctrl_parse and
   reac_ctrl_record_cksum_verify at fr + 34) and at OUT (own store checks), OUT apart from [RT_LO, RT_HI) (asan_cells
   at the return); for reac_ctrl_parse the addressable bytes at BC and the cells the bcmp wrapper reads; and the
   side-stack state for the own __asan_stack_malloc_1 and reac_ctrl_parse's (fp [1%nat], reac_ctrl_identity_reply_tls).
   The run may also write the class-1 side-stack bytes (fp_w [1%nat] FS) and the shadow of its window. *)
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
    (* asan-ubsan *)
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

(* ---- The footprint form (RECIPE.md step 1 (a working note, not in this delivery)): the same run, from the same start state and with the same
   post as reac_ctrl_identity_reply_contract, as an ExecF.evtF under a footprint RNG (the first binder). The premises
   of reac_ctrl_identity_reply_contract are unchanged and in their order; then one rng premise per region the run
   and its callees (reac_ctrl_parse, reac_ctrl_record_cksum_verify, __asan_stack_malloc_1) read or write, each under
   the guard of the data premise of that region:
   - the image [0x10000, 0x5fe000): every instruction fetch, the runtime's cells and GOT words, CF, REAL_BCMP,
     REAL_MEMCMP and the 6 bytes at REAC_CTRL_PARSE_BC;
   - the window [S - K, S) and its shadow bytes [shadow_addr (S - K), shadow_addr S) (the frame's own shadow, and the
     window and frame shadow of reac_ctrl_parse, whose statement names that byte-exact span);
   - the 50 bytes at fr (reply_args, 50 <= len) and the 8-aligned shadow WORD cover of them (reac_ctrl_parse's
     statement names that cover);
   - the bytes at pa (2), pp (8), pn (8) (reply_args), each with its shadow bytes, byte-exact (the run checks them
     with single-byte loads);
   - the 8-aligned shadow word cover of the 6 bytes at REAC_CTRL_PARSE_BC (reac_ctrl_parse's bcmp wrapper);
   - the side stack's header [FS, fs_frame FS 0 0), the class-1 bytes fp_w [1%nat] FS (hint, flags, frames, their
     shadow) and the dynamic thread cells fp_tls of asan_tls_cells (__asan_stack_malloc_1 and reac_ctrl_parse).
   rng_bytes (lib/Lib/RngBytes.v): RNG is decided byte by byte, as reac_ctrl_parse_contract_x_F asks of its caller.
   reac_ctrl_identity_reply_contract_of_F gives reac_ctrl_identity_reply_contract back at ExecF.RNG_all. ---- *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.

Definition reac_ctrl_identity_reply_contract_F : Prop :=
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
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
           (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) /\
         reac_ctrl_identity_reply_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs)).

(* The footprint form at the footprint that admits every access is the contract: each rng premise by rng_all from
   the bounds the contract's premises carry (the window, fr, pa, pp, pn and FS bounds; fs_place; the bytes_at bounds
   of the cells of asan_tls_cells), so the footprint form asks for nothing new. *)
Lemma reac_ctrl_identity_reply_contract_of_F :
  reac_ctrl_identity_reply_contract_F -> reac_ctrl_identity_reply_contract.
Proof.
  unfold reac_ctrl_identity_reply_contract_F, reac_ctrl_identity_reply_contract. intros HF.
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
