From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c RcAsanFP
  reac_ctrl_parse_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_CATALOGUE_MATCH : Z := 0x84498.
(* T: the patched BOX_CATALOGUE (11 rows of 296 bytes). *)
Definition CM_T : Z := 0x9e800.
(* K = max(4240, 336 + max(K of reac_ctrl_parse 8800, reac_box_model_block 4272, the bcmp wrapper 4560,
   __asan_stack_malloc_2 208)) = 336 + 8800: the frame is 128 bytes, A = S - 128 rounded down to 32; the 192-byte
   ASan frame (class 2) is A - 192 >= S - 336 on the real stack or a side-stack frame; the callees run at it (real
   stack) or at A (side stack), __asan_stack_malloc_2 at A; the probe writes 8 bytes at A - 4096 >= S - 4240
   (contracts/libreac/reac_box_catalogue_match.md Names). *)
Definition CM_K : Z := 9136.

(* The writes outside the side stack (fp's W) and the data ranges (fp's D). *)
Definition reac_box_catalogue_match_W (S : Z) : list ivl := [(S - CM_K, S)].
Definition reac_box_catalogue_match_D (f len : Z) : list ivl := if len <? 50 then [] else [(f, f + 50)].

(* The thread cells that fp names are apart from the class-0, class-1 and class-2 side-stack bytes
   (struct.asan.runtime RT4.3) and from the shadow of the function's own window [lo, hi): the function's own frame
   (class 2), reac_ctrl_parse's (class 1) and reac_box_model_block's (class 0) on the side stack or on the real stack
   keep them. *)
Definition reac_box_catalogue_match_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

(* The plain contract (lib/Prog/reac_box_catalogue_match_c.v) with K = 9136 and T = 0x9e800, and the premises of the
   asan build (S1.2, S1.5-S1.7 of the English contract): the runtime's cells and shadow (asan_cells, shadow_rw), the
   window in AppMem and addressable; the addressable 50 bytes at f (own shadow checks, reac_ctrl_parse, the bcmp
   wrapper at f + 18) and f + 50 in AppMem (the bcmp wrapper's end of f + 18); the addressable 3256 bytes at T
   (reac_box_model_block's rows); for reac_ctrl_parse the addressable bytes at BC and the cells the bcmp wrapper
   reads; and the side-stack state for the own __asan_stack_malloc_2, reac_ctrl_parse's __asan_stack_malloc_1 and
   reac_box_model_block's __asan_stack_malloc_0 (fp [0; 1; 2], reac_box_catalogue_match_tls). The run may also write
   the side-stack bytes of these classes (fp_w [0; 1; 2] FS) and the shadow of its window. *)
Definition reac_box_catalogue_match_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f len S FS : Z) (fb : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= len < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - CM_K \/ S <= f)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m f 50 /\ app_mem (f + 50)) ->
    addressable m CM_T 3256 ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D f len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(S - CM_K, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - CM_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
           (reac_box_catalogue_match_D f len) /\
         reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (S - CM_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).

(* ---- The footprint form (RECIPE.md step 1 (a working note, not in this delivery); the form agreed with a Theorem Labs lane on 2026-10-28 at 18:08Z; templates
   reac_ctrl_classify_box_frame_contract_F, lib/A/Prog/reac_ctrl_classify_box_frame_c.v (at head lib/A/Prog/reac_ctrl_classify_box_frame_c.v:126), and
   bcmp_wrap_contract_F (written on a working branch dcf92cb416), lib/A/Prog/bcmp_wrap_c.v (at head lib/A/Prog/bcmp_wrap_c.v:51-95)): the same run, from the same
   start state and with the same post as reac_box_catalogue_match_contract, as an ExecF.evtF under a footprint RNG (the
   first binder). The plain premises are unchanged and in the same order; then one rng premise per region that the run
   and its callees read or write:
   (a) rng_bytes RNG (lib/Lib/RngBytes.v: RNG is decided byte by byte); the bcmp wrapper's bcmp_wrap_holds_F needs it;
   (b) the image [0x10000, 0x5fe000), stated in the literal form of the base's lib/A/Prog/bcmp_wrap_c.v:79
       (`rng RNG 0x10000 0x5ee000`; 0x5fe000 = Eval compute in Contract.GT on both bases): the 3256 catalogue bytes at
       CM_T, the 6 bytes at REAC_CTRL_PARSE_BC, the cells GOT_CF, REAL_BCMP, REAL_MEMCMP, CF + 254, CF + 255 and the
       runtime's cells;
   (c) the stack window [S - CM_K, S);
   (d) when 50 <= len, the 50 bytes at f and the 8-ALIGNED shadow words of them (the function's own shadow checks and
       the bcmp wrapper's aligned words at f + 18);
   (e) the 8-aligned shadow words of the catalogue [CM_T, CM_T + 3256) and of [REAC_CTRL_PARSE_BC, REAC_CTRL_PARSE_BC + 6);
   (f) the shadow of the window [shadow_addr (S - CM_K), shadow_addr S), as the post's munch names it;
   (g) rng_fp_cm: the side stack of the classes 0, 1 and 2 (its header, fp_w [0; 1; 2] FS and the thread cells of
       asan_tls_cells).
   reac_box_catalogue_match_contract_of_F gives reac_box_catalogue_match_contract back at ExecF.RNG_all. ---- *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require RcAsanFPLib reac_ctrl_classify_box_frame_c.
(* ExecF opens bv_scope on Import; the statements below are Z arithmetic. *)
Open Scope Z_scope.

(* Every byte of every range of l is in RNG, bound free: the unit's one rng_ivls, of reac_ctrl_classify_box_frame_c.v
   (a Theorem Labs lane's appended block, classify a working branch's text). *)
Local Notation rng_ivls := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.rng_ivls.

(* The bridges to the per-range form of reac_ctrl_parse_c.v's footprint premises. *)
Lemma rng_ivls_of_Forall : forall (RNG : ExecF.footprint) (l : list ivl),
  Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) l -> rng_ivls RNG l.
Proof.
  intros RNG l H. eapply Forall_impl; [|exact H].
  intros [lo hi] (_ & _ & R) b j Hb Hj. cbn [fst snd] in *. apply R; lia.
Qed.

Lemma Forall_of_rng_ivls : forall (RNG : ExecF.footprint) (l : list ivl),
  Forall (fun iv => 0 <= fst iv /\ snd iv <= 2^64) l -> rng_ivls RNG l ->
  Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) l.
Proof.
  intros RNG l HB H. induction l as [|[lo hi] l IH]; [constructor|].
  apply Forall_cons_iff in HB as [(B1 & B2) HB]. apply Forall_cons_iff in H as [R H].
  constructor; [|exact (IH HB H)]. cbn [fst snd] in *.
  split; [lia|]. split; [lia|]. intros b j Hb Hj. apply R; lia.
Qed.

(* (g): the side-stack state of the classes 0 (reac_box_model_block's __asan_stack_malloc_0), 1 (reac_ctrl_parse's
   __asan_stack_malloc_1) and 2 (this function's __asan_stack_malloc_2) in RNG: the header [FS, FS + 36864) (the hint
   words, the words at FS + 88 and FS + 96, the flag bytes of every class), the class ranges fp_w [0; 1; 2] FS (hint
   word, flag bytes, frames and their shadow) and the thread cells that the allocations read. A premise only (the
   shape of rng_fp_cls1 in the classify template): the caller gives the cell coverage; rng_fp_cm_of_fp builds it from
   one tuple of asan_tls_cells. *)
Definition rng_fp_cm (RNG : ExecF.footprint) (m : word -> option byte) (TP FS : Z) : Prop :=
  ExecF.rng RNG FS 36864 /\ rng_ivls RNG (fp_w [0%nat; 1%nat; 2%nat] FS) /\
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k -> rng_ivls RNG (fp_tls TP DT TS C T DB k)).

(* rng_fp_cm from ONE tuple of the thread cells (a caller pins the tuple that its fp carries): asan_tls_cells fixes
   the tuple in a memory (RcAsanFPLib.fl_tls_same with no write), so every tuple is that one. *)
Lemma rng_fp_cm_of_fp : forall (RNG : ExecF.footprint) (m : word -> option byte) (TP FS : Z)
    (DT0 TS0 C0 T0 DB0 : word) (k0 : Z),
  asan_tls_cells m TP DT0 TS0 C0 T0 DB0 k0 ->
  ExecF.rng RNG FS 36864 -> rng_ivls RNG (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  rng_ivls RNG (fp_tls TP DT0 TS0 C0 T0 DB0 k0) ->
  rng_fp_cm RNG m TP FS.
Proof.
  intros RNG m TP FS DT0 TS0 C0 T0 DB0 k0 HT0 RH RW RT.
  split; [exact RH|]. split; [exact RW|].
  intros DT TS C T DB k HT.
  destruct (RcAsanFPLib.fl_tls_same m m [] TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT (munch_refl [] m)
              ltac:(apply Forall_forall; intros d _ x _; exact I)) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0. exact RT.
Qed.

Definition reac_box_catalogue_match_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f len S FS : Z) (fb : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= len < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - CM_K \/ S <= f)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m f 50 /\ app_mem (f + 50)) ->
    addressable m CM_T 3256 ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D f len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    (* footprint *)
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (S - CM_K) CM_K ->
    (50 <= len -> ExecF.rng RNG f 50 /\
                  ExecF.rng RNG (8 * (shadow_addr f / 8)) (8 * (shadow_addr (f + 49) / 8) + 8 - 8 * (shadow_addr f / 8))) ->
    ExecF.rng RNG (8 * (shadow_addr CM_T / 8)) (8 * (shadow_addr (CM_T + 3255) / 8) + 8 - 8 * (shadow_addr CM_T / 8)) ->
    ExecF.rng RNG (8 * (shadow_addr REAC_CTRL_PARSE_BC / 8))
      (8 * (shadow_addr (REAC_CTRL_PARSE_BC + 5) / 8) + 8 - 8 * (shadow_addr REAC_CTRL_PARSE_BC / 8)) ->
    ExecF.rng RNG (shadow_addr (S - CM_K)) (shadow_addr S - shadow_addr (S - CM_K)) ->
    rng_fp_cm RNG m (bv_unsigned tp) FS ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(S - CM_K, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - CM_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
           (reac_box_catalogue_match_D f len) /\
         reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (S - CM_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).

(* The footprint form at the footprint that admits every access is the plain contract: each rng premise by rng_all
   from the bounds that the plain premises carry (the window, f and FS bounds; fs_place), and the bound-free ranges of
   rng_fp_cm hold at RNG_all outright. *)
Lemma reac_box_catalogue_match_contract_of_F :
  reac_box_catalogue_match_contract_F -> reac_box_catalogue_match_contract.
Proof.
  unfold reac_box_catalogue_match_contract_F, reac_box_catalogue_match_contract. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f len S FS fb.
  intros Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HFB HT MI AC SR HHM HAE AW AFU AT ABC
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0.
  pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl. unfold CM_K in *.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
           t5 t6 F fc m f len S FS fb); try assumption.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - (* f *) intros H50. destruct (HFB H50) as (Hf0 & Hf1 & _).
    split; apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* catalogue shadow *) apply ExecF.rng_all; unfold shadow_addr, ASAN_K, CM_T; Z.div_mod_to_equations; lia.
  - (* BC shadow *)
    apply ExecF.rng_all; unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* window shadow *) apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* side stack *)
    split; [apply ExecF.rng_all; lia|]. split.
    + apply Forall_forall. intros iv _ b j _ _. exact I.
    + intros DT TS C T DB k _. apply Forall_forall. intros iv _ b j _ _. exact I.
Qed.

(* ---- Route (C) (a Theorem Labs lane 09:20Z, form of a Theorem Labs lane 09:38Z; lib/A/ShadowRwOn.v): the two contracts above with the
   universal premise `shadow_rw m` narrowed to `shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m` and the
   post's `shadow_rw m'` widened to `forall P, shadow_rw_on P m -> shadow_rw_on P m'`; nothing else changes.
   The region (a Theorem Labs lane's derivation from the run reac_box_catalogue_match.v 6770846641b, checked against a Theorem Labs lane's):
   the shadow bytes the run reaches through shadow_rw (its own shadow loads and stores, and every callee's `_on`
   region at its call):
   (W)  the window's shadow [shadow_addr (S - CM_K), shadow_addr S);
   (FS) the shadow of the class-c side-stack block, asan_stack_malloc_shadow_R FS c, for c = 2 (this function's frame
        and __asan_stack_malloc_2) and c = 1, 0 (the frames of reac_ctrl_parse and reac_box_model_block);
   and, when 50 <= len (only then are reac_ctrl_parse, reac_box_model_block and the bcmp wrapper called):
   (D)  sh_word_on f 50, (T) sh_word_on CM_T 3256, (BC) sh_word_on REAC_CTRL_PARSE_BC 6. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on asan_stack_malloc_c_on.

Definition reac_box_catalogue_match_shadow_R (f len S FS : Z) (a : Z) : Prop :=
  shadow_addr (S - CM_K) <= a < shadow_addr S \/
  (exists c, (c <= 2)%nat /\ asan_stack_malloc_shadow_R FS c a) \/
  (50 <= len /\ (sh_word_on f 50 a \/ sh_word_on CM_T 3256 a \/ sh_word_on REAC_CTRL_PARSE_BC 6 a)).

Definition reac_box_catalogue_match_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f len S FS : Z) (fb : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= len < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - CM_K \/ S <= f)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m f 50 /\ app_mem (f + 50)) ->
    addressable m CM_T 3256 ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D f len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(S - CM_K, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - CM_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
           (reac_box_catalogue_match_D f len) /\
         reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (S - CM_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).

Definition reac_box_catalogue_match_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f len S FS : Z) (fb : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= len < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - CM_K \/ S <= f)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m f 50 /\ app_mem (f + 50)) ->
    addressable m CM_T 3256 ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D f len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    (* footprint *)
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (S - CM_K) CM_K ->
    (50 <= len -> ExecF.rng RNG f 50 /\
                  ExecF.rng RNG (8 * (shadow_addr f / 8)) (8 * (shadow_addr (f + 49) / 8) + 8 - 8 * (shadow_addr f / 8))) ->
    ExecF.rng RNG (8 * (shadow_addr CM_T / 8)) (8 * (shadow_addr (CM_T + 3255) / 8) + 8 - 8 * (shadow_addr CM_T / 8)) ->
    ExecF.rng RNG (8 * (shadow_addr REAC_CTRL_PARSE_BC / 8))
      (8 * (shadow_addr (REAC_CTRL_PARSE_BC + 5) / 8) + 8 - 8 * (shadow_addr REAC_CTRL_PARSE_BC / 8)) ->
    ExecF.rng RNG (shadow_addr (S - CM_K)) (shadow_addr S - shadow_addr (S - CM_K)) ->
    rng_fp_cm RNG m (bv_unsigned tp) FS ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(S - CM_K, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - CM_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
           (reac_box_catalogue_match_D f len) /\
         reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (S - CM_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).

(* The old contracts from the narrowed ones: the premise by shadow_rw_on_of_shadow_rw, the post at P := fun _ => True
   by shadow_rw_of_on_all. *)
Lemma reac_box_catalogue_match_contract_of_on :
  reac_box_catalogue_match_contract_on -> reac_box_catalogue_match_contract.
Proof.
  unfold reac_box_catalogue_match_contract_on, reac_box_catalogue_match_contract. intros HO.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f len S FS fb.
  intros Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HFB HT MI AC SR HHM HAE AW AFU AT ABC
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0.
  eapply lib.Lib.Exec.evt_mono.
  - exact (HO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             f len S FS fb Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HFB HT MI AC (shadow_rw_on_of_shadow_rw _ m SR)
             HHM HAE AW AFU AT ABC HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E' & MU' & WM' & MI' & ST' & AC' & SW' & AW' & FP' & TL').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj E' (conj MU' (conj WM' (conj MI' (conj ST' (conj AC' (conj _ (conj AW' (conj FP' TL'))))))))).
    exact (shadow_rw_of_on_all m' (SW' (fun _ => True) (shadow_rw_on_of_shadow_rw (fun _ => True) m SR))).
Qed.

Lemma reac_box_catalogue_match_contract_F_of_on :
  reac_box_catalogue_match_contract_F_on -> reac_box_catalogue_match_contract_F.
Proof.
  unfold reac_box_catalogue_match_contract_F_on, reac_box_catalogue_match_contract_F. intros HO.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f len S FS fb.
  intros Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HFB HT MI AC SR HHM HAE AW AFU AT ABC
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0 RB RI RW RF RC RBC RWS RFP.
  eapply ExecF.evtF_mono.
  - exact (HO RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             f len S FS fb Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HFB HT MI AC (shadow_rw_on_of_shadow_rw _ m SR)
             HHM HAE AW AFU AT ABC HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0 RB RI RW RF RC RBC RWS RFP).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E' & MU' & WM' & MI' & ST' & AC' & SW' & AW' & FP' & TL').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj E' (conj MU' (conj WM' (conj MI' (conj ST' (conj AC' (conj _ (conj AW' (conj FP' TL'))))))))).
    exact (shadow_rw_of_on_all m' (SW' (fun _ => True) (shadow_rw_on_of_shadow_rw (fun _ => True) m SR))).
Qed.

(* reac_box_catalogue_match_contract_of_F's proof between the narrowed forms: the shadow_rw_on premise and the post
   pass through unchanged. *)
Lemma reac_box_catalogue_match_contract_on_of_F_on :
  reac_box_catalogue_match_contract_F_on -> reac_box_catalogue_match_contract_on.
Proof.
  unfold reac_box_catalogue_match_contract_F_on, reac_box_catalogue_match_contract_on. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f len S FS fb.
  intros Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HFB HT MI AC SR HHM HAE AW AFU AT ABC
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0.
  pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl. unfold CM_K in *.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
           t5 t6 F fc m f len S FS fb); try assumption.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - (* f *) intros H50. destruct (HFB H50) as (Hf0 & Hf1 & _).
    split; apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* catalogue shadow *) apply ExecF.rng_all; unfold shadow_addr, ASAN_K, CM_T; Z.div_mod_to_equations; lia.
  - (* BC shadow *)
    apply ExecF.rng_all; unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* window shadow *) apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* side stack *)
    split; [apply ExecF.rng_all; lia|]. split.
    + apply Forall_forall. intros iv _ b j _ _. exact I.
    + intros DT TS C T DB k _. apply Forall_forall. intros iv _ b j _ _. exact I.
Qed.
