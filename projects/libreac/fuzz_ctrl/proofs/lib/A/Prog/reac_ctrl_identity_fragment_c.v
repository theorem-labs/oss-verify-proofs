From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_IDENTITY_FRAGMENT : Z := 0x84f68.
Definition REAC_CTRL_IDENTITY_FRAGMENT_FRAME : Z := 96.
(* K = 96 + max(K(__asan_memcpy) 2224, K(the bcmp wrapper) 4560): the callees run at S - 96
   (contracts/libreac/reac_ctrl_identity_fragment.md Names). No ASan stack frame. *)
Definition REAC_CTRL_IDENTITY_FRAGMENT_K : Z := 4656.

(* The plain fg_mem (lib/Prog/reac_ctrl_identity_fragment_c.v) on the memory of this image. *)
Definition fg_mem (f pa pp pn : Z) (st g : list byte) (c : fg_case) (m' : word -> option byte) : Prop :=
  match c with
  | FgRefuse | FgNone => True
  | FgFirst => bytes_at rsegs m' f (fg_first st g)
  | FgDrop => bytes_at rsegs m' f (fg_clear st)
  | FgJoin => bytes_at rsegs m' f (fg_clear (fg_join st g))
  | FgClose =>
      bytes_at rsegs m' f (fg_clear (fg_join st g)) /\
      bytes_at rsegs m' pa (le2 (Z_to_bv 64 (fg_addr st g))) /\
      bytes_at rsegs m' pp (le8 (Z_to_bv 64 (f + 19))) /\
      bytes_at rsegs m' pn (le8 (Z_to_bv 64 (fg_T st g - 13)))
  end.

(* The plain contract (lib/Prog/reac_ctrl_identity_fragment_c.v) with the window K of this build and the premises of
   the asan build (S1.5, S1.6 of the English contract and those of __asan_memcpy at the copies to f, f + 8, f + 8 + lf
   and of the bcmp wrapper at (f, fr + 6, 6)): the runtime's cells and shadow, the window in AppMem above the shadow,
   the 50 bytes at fr, the 72 bytes at f and OUT addressable, f + 78 in AppMem (the end f + 8 + lf + 7, lf <= 63,
   of the third copy), [f, f + 72) and OUT apart from [RT_LO, RT_HI), and the cells the bcmp wrapper reads. The
   post adds the runtime's cells and shadow. *)
Definition reac_ctrl_identity_fragment_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f fr len pa pp pn : Z) (st g : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 fr -> a2 = Z_to_bv 64 len ->
    a3 = Z_to_bv 64 pa -> a4 = Z_to_bv 64 pp -> a5 = Z_to_bv 64 pn ->
    0 <= f < 2^64 -> 0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length g = 50%nat -> length st = 72%nat ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m fr g) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m fr 50) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret (fg_class f fr pa pp pn len st g)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp) (fg_class f fr pa pp pn len st g))
           m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) /\
         fg_mem f pa pp pn st g (fg_class f fr pa pp pn len st g) m' /\
         asan_cells m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).

(* Footprint form (the re-walk form (D)): the same run, from the same start state and with the same post, as an
   ExecF.evtF under a footprint RNG, with one rng premise per region the run touches, so the pages the run
   touches are known and no lazy first touch of this run is refused.
   The regions: the image [IMG_LO, IMG_HI) (lib/A/Prog/ImgBounds.v; every instruction fetch, and every cell this
   run and its callees read by absolute address: REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254, CF + 255, GOT_CELL_K,
   CELL_K); the stack window [sp - K, sp) of this frame and of the frames of __asan_memcpy and of the bcmp wrapper
   below it; the 8-aligned shadow WORD span of that window (sh_word_rng of lib/A/Prog/asan_memcpy_cF.v), which
   holds the shadow of the frame of __asan_memcpy that its footprint contract takes; and, under the guards the
   buffer premises of the plain contract carry (the fr one also needs 50 <= len), each buffer with the cover of its
   shadow bytes. The shadow cover is rounded out to whole 8-byte WORDS at both ends, because the callees of this
   function load shadow WORDS, not single shadow bytes. The rng_bytes premise (lib/Lib/RngBytes.v) says the
   footprint is decided byte by byte; the footprint contracts of __asan_memcpy and of the bcmp wrapper, which this
   run calls, take it. *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_cF.

Definition reac_ctrl_identity_fragment_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f fr len pa pp pn : Z) (st g : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 fr -> a2 = Z_to_bv 64 len ->
    a3 = Z_to_bv 64 pa -> a4 = Z_to_bv 64 pp -> a5 = Z_to_bv 64 pn ->
    0 <= f < 2^64 -> 0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length g = 50%nat -> length st = 72%nat ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m fr g) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m fr 50) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> rng RNG fr 50) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len ->
       rng RNG (shadow_addr fr / 8 * 8) (shadow_addr (fr + 49) / 8 * 8 + 8 - shadow_addr fr / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> rng RNG f 72) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 71) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> rng RNG pa 2) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG (shadow_addr pa / 8 * 8) (shadow_addr (pa + 1) / 8 * 8 + 8 - shadow_addr pa / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> rng RNG pp 8) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG (shadow_addr pp / 8 * 8) (shadow_addr (pp + 7) / 8 * 8 + 8 - shadow_addr pp / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> rng RNG pn 8) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG (shadow_addr pn / 8 * 8) (shadow_addr (pn + 7) / 8 * 8 + 8 - shadow_addr pn / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret (fg_class f fr pa pp pn len st g)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp) (fg_class f fr pa pp pn len st g))
           m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) /\
         fg_mem f pa pp pn st g (fg_class f fr pa pp pn len st g) m' /\
         asan_cells m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).

(* The old statement is the _F statement at the footprint that admits every access (rng_bytes by RNG_all's
   definition, the window's shadow word span by sh_word_rng_all, every rng premise by rng_all). *)
Lemma reac_ctrl_identity_fragment_contract_of_F :
  reac_ctrl_identity_fragment_contract_F -> reac_ctrl_identity_fragment_contract.
Proof.
  unfold reac_ctrl_identity_fragment_contract_F, reac_ctrl_identity_fragment_contract. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f fr len pa pp pn st g E0 E1 E2 E3 E4 E5 Rf Rfr Rlen Rpa Rpp Rpn HSP HST Lg Lst HG HC1 HMI HAC HSR HLO HHI
    HD1 HD2 HRB HRM HGCF HCF1 HCF2.
  apply (evtF_evt rsegs RNG_all). apply HF; try assumption.
  all: first
    [ intros ? ? ? ? ?; exact I
    | apply sh_word_rng_all; unfold HIGHMEM_BEG, APPMEM_END, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia
    | intros;
      repeat match goal with
      | H : ?a -> _, Ha : ?a |- _ => specialize (H Ha)
      end;
      repeat match goal with
      | H : _ /\ _ |- _ => destruct H
      | H : addressable _ _ _ |- _ => destruct H as (? & ? & ? & _)
      end;
      unfold HIGHMEM_BEG, APPMEM_END, REAC_CTRL_IDENTITY_FRAGMENT_K, shadow_addr, ASAN_K, IMG_LO, IMG_HI in *;
      apply rng_all; Z.div_mod_to_equations; lia ].
Qed.

(* Route (C) (a Theorem Labs lane 09:20Z; form of record 09:38Z, amended 09:58Z and 10:33Z): the narrowed forms of the two
   contracts above.  The callees' statements: a Theorem Labs lane's asan_memcpy_c_on.v (asan_memcpy_shadow_R) and a Theorem Labs lane's
   bcmp_wrap_c_on.v (bcmp_wrap_shadow_R), both leaves. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.Prog.asan_memcpy_c_on A.Prog.bcmp_wrap_c_on.

(* The shadow bytes the run needs PRESENT through its shadow_rw premise.  The function's own shadow checks read through
   the addressable premises (RcAsanRT.rt_shadow_rd), never through shadow_rw; the run uses shadow_rw only to give its
   callees their shadow premise and to carry the shadow to its post.  So R is the union of the callees' own R at the
   four call sites, each under the path guard of its call: on the first-record path (g[19] = 1) __asan_memcpy
   (D, S, N) = (f, fr + 6, 6) and (f + 8, fr + 27, n); on the second-record path when hf <> 0, the bcmp wrapper
   (f, fr + 6, 6), and on its keep (join) arm __asan_memcpy (f + 8 + lf, fr + 27, n).  Each callee R covers the
   source and the destination ranges, whose shadow words the callee's range check reads.  STORES: the run stores
   no shadow byte: its own stores are at f, pa, pp, pn and in its frame (fg_fp), its callees' at their destinations
   inside [f, f + 72) and in their frames below sp - 96 (asan_memcpy_post_on, bcmp_wrap_post_on), all in application
   memory. *)
Definition reac_ctrl_identity_fragment_shadow_R (f fr len pa pp pn : Z) (st g : list byte) (a : Z) : Prop :=
  f <> 0 /\ fr <> 0 /\ pa <> 0 /\ pp <> 0 /\ pn <> 0 /\ fg_fr len g = true /\
  ((bat g 19 = 1 /\
    (A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R (Z_to_bv 64 f) (Z_to_bv 64 (fr + 6)) (Z_to_bv 64 6) a \/
     A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R (Z_to_bv 64 (f + 8)) (Z_to_bv 64 (fr + 27)) (Z_to_bv 64 (fg_n g))
       a)) \/
   (bat g 19 <> 1 /\ fg_hf st <> 0 /\
    (A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R f (fr + 6) 6 a \/
     (fg_keep st g = true /\
      A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R (Z_to_bv 64 (f + 8 + fg_lf st)) (Z_to_bv 64 (fr + 27))
        (Z_to_bv 64 (fg_n g)) a)))).

(* reac_ctrl_identity_fragment_contract with `shadow_rw m` narrowed to reac_ctrl_identity_fragment_shadow_R and the
   post's `shadow_rw m'` in the wave's form: every shadow region present before the call is present after it. *)
Definition reac_ctrl_identity_fragment_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f fr len pa pp pn : Z) (st g : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 fr -> a2 = Z_to_bv 64 len ->
    a3 = Z_to_bv 64 pa -> a4 = Z_to_bv 64 pp -> a5 = Z_to_bv 64 pn ->
    0 <= f < 2^64 -> 0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length g = 50%nat -> length st = 72%nat ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m fr g) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    mem_inv rsegs m ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g) m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m fr 50) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret (fg_class f fr pa pp pn len st g)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp) (fg_class f fr pa pp pn len st g))
           m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) /\
         fg_mem f pa pp pn st g (fg_class f fr pa pp pn len st g) m' /\
         asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).

(* The old statement from the narrowed one: shadow_rw m gives every shadow_rw_on, and the post's shadow conjunct at
   the whole shadow (P := fun _ => True) gives shadow_rw m' back. *)
Lemma reac_ctrl_identity_fragment_contract_of_on :
  reac_ctrl_identity_fragment_contract_on -> reac_ctrl_identity_fragment_contract.
Proof.
  unfold reac_ctrl_identity_fragment_contract_on, reac_ctrl_identity_fragment_contract. intros H.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f fr len pa pp pn st g E0 E1 E2 E3 E4 E5 Rf Rfr Rlen Rpa Rpp Rpn HSP HST Lg Lst HG HC1 HMI HAC HSR HLO HHI
    HD1 HD2 HRB HRM HGCF HCF1 HCF2.
  eapply evt_mono.
  - exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             f fr len pa pp pn st g E0 E1 E2 E3 E4 E5 Rf Rfr Rlen Rpa Rpp Rpn HSP HST Lg Lst HG HC1 HMI HAC
             (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSR) HLO HHI HD1 HD2 HRB HRM HGCF HCF1 HCF2).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E & MU & WM & MI & ST & FG & AC & SW).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj E (conj MU (conj WM (conj MI (conj ST (conj FG (conj AC _))))))).
    exact (A.ShadowRwOn.shadow_rw_of_on_all m'
             (SW (fun _ => True) (A.ShadowRwOn.shadow_rw_on_of_shadow_rw (fun _ => True) m HSR))).
Qed.

(* reac_ctrl_identity_fragment_contract_F with the same two changes; the footprint premises are unchanged. *)
Definition reac_ctrl_identity_fragment_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f fr len pa pp pn : Z) (st g : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 fr -> a2 = Z_to_bv 64 len ->
    a3 = Z_to_bv 64 pa -> a4 = Z_to_bv 64 pp -> a5 = Z_to_bv 64 pn ->
    0 <= f < 2^64 -> 0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length g = 50%nat -> length st = 72%nat ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m fr g) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    mem_inv rsegs m ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g) m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m fr 50) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> rng RNG fr 50) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len ->
       rng RNG (shadow_addr fr / 8 * 8) (shadow_addr (fr + 49) / 8 * 8 + 8 - shadow_addr fr / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> rng RNG f 72) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 71) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> rng RNG pa 2) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG (shadow_addr pa / 8 * 8) (shadow_addr (pa + 1) / 8 * 8 + 8 - shadow_addr pa / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> rng RNG pp 8) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG (shadow_addr pp / 8 * 8) (shadow_addr (pp + 7) / 8 * 8 + 8 - shadow_addr pp / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> rng RNG pn 8) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG (shadow_addr pn / 8 * 8) (shadow_addr (pn + 7) / 8 * 8 + 8 - shadow_addr pn / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret (fg_class f fr pa pp pn len st g)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp) (fg_class f fr pa pp pn len st g))
           m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) /\
         fg_mem f pa pp pn st g (fg_class f fr pa pp pn len st g) m' /\
         asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).

(* The old footprint statement from the narrowed one (contract_of_on's argument, under evtF). *)
Lemma reac_ctrl_identity_fragment_contract_F_of_on :
  reac_ctrl_identity_fragment_contract_F_on -> reac_ctrl_identity_fragment_contract_F.
Proof.
  unfold reac_ctrl_identity_fragment_contract_F_on, reac_ctrl_identity_fragment_contract_F. intros H.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f fr len pa pp pn st g E0 E1 E2 E3 E4 E5 Rf Rfr Rlen Rpa Rpp Rpn HSP HST Lg Lst HG HC1 HMI HAC HSR HLO HHI
    HD1 HD2 HRB HRM HGCF HCF1 HCF2 RBY RIMG RSTK RSTKS RGr RGrs RGf RGfs RGa RGas RGp RGps RGn RGns.
  eapply evtF_mono.
  - exact (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
             m f fr len pa pp pn st g E0 E1 E2 E3 E4 E5 Rf Rfr Rlen Rpa Rpp Rpn HSP HST Lg Lst HG HC1 HMI HAC
             (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSR) HLO HHI HD1 HD2 HRB HRM HGCF HCF1 HCF2
             RBY RIMG RSTK RSTKS RGr RGrs RGf RGfs RGa RGas RGp RGps RGn RGns).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E & MU & WM & MI & ST & FG & AC & SW).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj E (conj MU (conj WM (conj MI (conj ST (conj FG (conj AC _))))))).
    exact (A.ShadowRwOn.shadow_rw_of_on_all m'
             (SW (fun _ => True) (A.ShadowRwOn.shadow_rw_on_of_shadow_rw (fun _ => True) m HSR))).
Qed.

(* The same step between the narrowed statements, by reac_ctrl_identity_fragment_contract_of_F's script.  The old
   lemma keeps its own proof: its premise contract_F does not give contract_F_on. *)
Lemma reac_ctrl_identity_fragment_contract_of_F_on :
  reac_ctrl_identity_fragment_contract_F_on -> reac_ctrl_identity_fragment_contract_on.
Proof.
  unfold reac_ctrl_identity_fragment_contract_F_on, reac_ctrl_identity_fragment_contract_on. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f fr len pa pp pn st g E0 E1 E2 E3 E4 E5 Rf Rfr Rlen Rpa Rpp Rpn HSP HST Lg Lst HG HC1 HMI HAC HSR HLO HHI
    HD1 HD2 HRB HRM HGCF HCF1 HCF2.
  apply (evtF_evt rsegs RNG_all). apply HF; try assumption.
  all: first
    [ intros ? ? ? ? ?; exact I
    | apply sh_word_rng_all; unfold HIGHMEM_BEG, APPMEM_END, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia
    | intros;
      repeat match goal with
      | H : ?a -> _, Ha : ?a |- _ => specialize (H Ha)
      end;
      repeat match goal with
      | H : _ /\ _ |- _ => destruct H
      | H : addressable _ _ _ |- _ => destruct H as (? & ? & ? & _)
      end;
      unfold HIGHMEM_BEG, APPMEM_END, REAC_CTRL_IDENTITY_FRAGMENT_K, shadow_addr, ASAN_K, IMG_LO, IMG_HI in *;
      apply rng_all; Z.div_mod_to_equations; lia ].
Qed.
