From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c RcAsanFP
  reac_ctrl_parse_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_CATALOGUE_MATCH : Z := 0x84e40.
(* T: the patched BOX_CATALOGUE (11 rows of 296 bytes). *)
Definition CM_T : Z := 0x9f620.
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

(* The ubsan contract (lib/U/Prog/reac_box_catalogue_match_c.v, the plain form) with K = 9136 and T = 0x9f520, and
   the premises of the asan-ubsan build (S1.2, S1.5-S1.7 of the English contract): the runtime's cells and shadow
   (asan_cells, shadow_rw), the window in AppMem and addressable; the addressable 50 bytes at f (own shadow checks,
   reac_ctrl_parse, the bcmp wrapper at f + 18) and f + 50 in AppMem (the bcmp wrapper's end of f + 18); the
   addressable 3256 bytes at T (reac_box_model_block's rows); for reac_ctrl_parse the addressable bytes at BC and the
   cells the bcmp wrapper reads; and the side-stack state for the own __asan_stack_malloc_2, reac_ctrl_parse's
   __asan_stack_malloc_1 and reac_box_model_block's __asan_stack_malloc_0 (fp [0; 1; 2], reac_box_catalogue_match_tls).
   The run may also write the side-stack bytes of these classes (fp_w [0; 1; 2] FS) and the shadow of its window. *)
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
    (* asan-ubsan *)
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

(* ---- Footprint form (RECIPE.md step 1 (a working note, not in this delivery)): the same run, from the same start state and with the same post
   as reac_box_catalogue_match_contract, as an ExecF.evtF under a footprint RNG (the first binder), with the premises
   of reac_box_catalogue_match_contract unchanged and one rng premise per region the run and its callees
   (__asan_stack_malloc_2, reac_ctrl_parse, reac_box_model_block, the bcmp wrapper) read or write, each under the
   guard its data premise carries:
     the image [0x10000, 0x5fe000)      the instruction-side cells (GOT words, the runtime's cells, CF), read
     the window [S - K, S)              the frame, the saves, the probe, the real-stack ASan frame, the callees'
                                        frames, read/write
     the window's shadow                byte-exact [shadow_addr (S - K), shadow_addr S): the single-byte shadow
                                        stores of a real-stack frame and the callees' window shadow
     the 50 bytes at f (50 <= len)      the own lb loads of f + 12, 13, 16, 17, reac_ctrl_parse, the bcmp wrapper
     the table T (3256 bytes)           reac_box_model_block's row
     the 6 bytes at BC                  reac_ctrl_parse's bcmp
     the side stack's header            [FS, fs_frame FS 0 0): hints, flags, FS + 88, FS + 96
     the class-0/1/2 side-stack bytes   fp_w [0; 1; 2] FS: hint, flags, frames (the class-2 ASan frame) and their
                                        shadow
     the cells of asan_tls_cells        fp_tls, read by the three __asan_stack_malloc_N
   A buffer that a callee checks (f, T, BC) gets the 8-aligned shadow WORD cover (the wrappers and the instrumented
   callees load aligned shadow words); f is also checked here with single-byte lb loads, inside that cover.
   rng_bytes RNG is carried for reac_ctrl_parse's and the bcmp wrapper's _F contracts.
   reac_box_catalogue_match_contract_of_F gives reac_box_catalogue_match_contract back at ExecF.RNG_all. ---- *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.

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
    (* asan-ubsan *)
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
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (S - CM_K) CM_K ->
    ExecF.rng RNG (shadow_addr (S - CM_K)) (shadow_addr S - shadow_addr (S - CM_K)) ->
    (50 <= len -> ExecF.rng RNG f 50) ->
    (50 <= len -> ExecF.rng RNG (shadow_addr f / 8 * 8)
                    (shadow_addr (f + 50 - 1) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    ExecF.rng RNG CM_T 3256 ->
    ExecF.rng RNG (shadow_addr CM_T / 8 * 8) (shadow_addr (CM_T + 3256 - 1) / 8 * 8 + 8 - shadow_addr CM_T / 8 * 8) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (shadow_addr REAC_CTRL_PARSE_BC / 8 * 8)
      (shadow_addr (REAC_CTRL_PARSE_BC + 6 - 1) / 8 * 8 + 8 - shadow_addr REAC_CTRL_PARSE_BC / 8 * 8) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
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

(* The _F statement at the footprint that admits every access is the old statement: each rng premise by rng_all from
   the bounds the old premises carry (the window, f, the literal T and BC; fs_place and FS + FS_SIZE <= S - K for the
   side stack; the bytes_at bounds of the cells of asan_tls_cells), so the _F statement asks for nothing new. *)
Lemma reac_box_catalogue_match_contract_of_F :
  reac_box_catalogue_match_contract_F -> reac_box_catalogue_match_contract.
Proof.
  unfold reac_box_catalogue_match_contract_F, reac_box_catalogue_match_contract. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f len S FS fb Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HFI HT MI AC SR HHM HAE AW AFU AT ABC
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0.
  pose proof (eq_refl : CM_K = 9136) as EK.
  pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl. unfold HIGHMEM_BEG, APPMEM_END in HHM, HAE.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (EFR : forall c j, fs_frame FS c j = FS + 36864 + Z.of_nat c * 1048576 + j * fs_B c)
    by (intros c j; unfold fs_frame; change (2 ^ 20) with 1048576; lia).
  assert (EB0 : fs_B 0 = 64) by reflexivity. assert (EB1 : fs_B 1 = 128) by reflexivity.
  assert (EB2 : fs_B 2 = 256) by reflexivity.
  assert (EM0 : fs_M 0 = 16384) by reflexivity. assert (EM1 : fs_M 1 = 8192) by reflexivity.
  assert (EM2 : fs_M 2 = 4096) by reflexivity.
  assert (EFL0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 0)) with 32768; lia).
  assert (EFL1 : fs_flag FS 1 0 = FS + 20480) by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EFL2 : fs_flag FS 2 0 = FS + 28672) by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 2)) with 8192; lia).
  assert (EH : forall c, fs_hint FS c = FS + 8 * Z.of_nat c) by (intros c; reflexivity).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5
           t6 F fc m f len S FS fb); try assumption.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - (* the window's shadow *) apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (HFI H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (HFI H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* T *) apply ExecF.rng_all; unfold CM_T; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K, CM_T; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-0/1/2 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; cbn [fst snd];
      apply ExecF.rng_all; rewrite ?EH, ?EFR, ?EFL0, ?EFL1, ?EFL2, ?EM0, ?EM1, ?EM2, ?EB0, ?EB1, ?EB2;
      cbn [Z.of_nat Pos.of_succ_nat]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* the cells of asan_tls_cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

(* ---- Route (C) (a Theorem Labs lane 09:20Z, form of a Theorem Labs lane 09:38Z; lib/B/ShadowRwOn.v): the image-B twin of a Theorem Labs lane's A text
   (lib/A/Prog/reac_box_catalogue_match_c.v (at head lib/A/Prog/reac_box_catalogue_match_c.v:232-405; written on a working branch f07a91c47f01)). The two contracts
   above with the universal premise `shadow_rw m` narrowed to `shadow_rw_on (reac_box_catalogue_match_shadow_R f len S
   FS) m` and the post's `shadow_rw m'` widened to `forall P, shadow_rw_on P m -> shadow_rw_on P m'`; nothing else
   changes. The region is a Theorem Labs lane's text character for character (a Theorem Labs lane's derivation); its constants are this file's
   by name (CM_K = 9136, CM_T = 0x9f620, REAC_CTRL_PARSE_BC = 0x21200 of reac_ctrl_parse_c.v; A has CM_T = 0x9e800):
   the shadow bytes the run reaches through shadow_rw (its own shadow loads and stores, and every callee's `_on`
   region at its call):
   (W)  the window's shadow [shadow_addr (S - CM_K), shadow_addr S);
   (FS) the shadow of the class-c side-stack block, asan_stack_malloc_shadow_R FS c, for c = 2 (this function's frame
        and __asan_stack_malloc_2) and c = 1, 0 (the frames of reac_ctrl_parse and reac_box_model_block);
   and, when 50 <= len (only then are reac_ctrl_parse, reac_box_model_block and the bcmp wrapper called):
   (D)  sh_word_on f 50, (T) sh_word_on CM_T 3256, (BC) sh_word_on REAC_CTRL_PARSE_BC 6. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import sh_word_on asan_stack_malloc_c_on.

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
    (* asan-ubsan *)
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
    (* asan-ubsan *)
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
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (S - CM_K) CM_K ->
    ExecF.rng RNG (shadow_addr (S - CM_K)) (shadow_addr S - shadow_addr (S - CM_K)) ->
    (50 <= len -> ExecF.rng RNG f 50) ->
    (50 <= len -> ExecF.rng RNG (shadow_addr f / 8 * 8)
                    (shadow_addr (f + 50 - 1) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    ExecF.rng RNG CM_T 3256 ->
    ExecF.rng RNG (shadow_addr CM_T / 8 * 8) (shadow_addr (CM_T + 3256 - 1) / 8 * 8 + 8 - shadow_addr CM_T / 8 * 8) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (shadow_addr REAC_CTRL_PARSE_BC / 8 * 8)
      (shadow_addr (REAC_CTRL_PARSE_BC + 6 - 1) / 8 * 8 + 8 - shadow_addr REAC_CTRL_PARSE_BC / 8 * 8) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
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
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0
    RB RI RW RWS RFD RFSH RT RTSH RBC RBCSH RHDR RFPW RTLS.
  eapply ExecF.evtF_mono.
  - exact (HO RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             f len S FS fb Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HFB HT MI AC (shadow_rw_on_of_shadow_rw _ m SR)
             HHM HAE AW AFU AT ABC HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0 RB RI RW RWS RFD RFSH RT RTSH RBC RBCSH RHDR RFPW RTLS).
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
    f len S FS fb Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HFI HT MI AC SR HHM HAE AW AFU AT ABC
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0.
  pose proof (eq_refl : CM_K = 9136) as EK.
  pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl. unfold HIGHMEM_BEG, APPMEM_END in HHM, HAE.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (EFR : forall c j, fs_frame FS c j = FS + 36864 + Z.of_nat c * 1048576 + j * fs_B c)
    by (intros c j; unfold fs_frame; change (2 ^ 20) with 1048576; lia).
  assert (EB0 : fs_B 0 = 64) by reflexivity. assert (EB1 : fs_B 1 = 128) by reflexivity.
  assert (EB2 : fs_B 2 = 256) by reflexivity.
  assert (EM0 : fs_M 0 = 16384) by reflexivity. assert (EM1 : fs_M 1 = 8192) by reflexivity.
  assert (EM2 : fs_M 2 = 4096) by reflexivity.
  assert (EFL0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 0)) with 32768; lia).
  assert (EFL1 : fs_flag FS 1 0 = FS + 20480) by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EFL2 : fs_flag FS 2 0 = FS + 28672) by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 2)) with 8192; lia).
  assert (EH : forall c, fs_hint FS c = FS + 8 * Z.of_nat c) by (intros c; reflexivity).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5
           t6 F fc m f len S FS fb); try assumption.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - (* the window's shadow *) apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (HFI H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (HFI H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* T *) apply ExecF.rng_all; unfold CM_T; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K, CM_T; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-0/1/2 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; cbn [fst snd];
      apply ExecF.rng_all; rewrite ?EH, ?EFR, ?EFL0, ?EFL1, ?EFL2, ?EM0, ?EM1, ?EM2, ?EB0, ?EB1, ?EB2;
      cbn [Z.of_nat Pos.of_succ_nat]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* the cells of asan_tls_cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.
