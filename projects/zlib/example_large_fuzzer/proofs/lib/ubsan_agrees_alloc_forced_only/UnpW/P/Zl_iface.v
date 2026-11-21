(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZTarget ZApiL ZHarnessL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInstL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTargetL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Target Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require ZIface ZApiInst.          (* [comment removed for export] *)
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Layout Exit Printf_wfile.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Export Zlib_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ZHL_TEST_DEFLATE : Z := 0x15e6c.   (* [comment removed for export] *)
Definition ZHL_TEST_INFLATE : Z := 0x16078.   (* [comment removed for export] *)
Definition ZHL_ILOOP : Z := 0x160bc.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition Z_DEFLATEPARAMS : Z := 0x16ce8.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AL_N_DEFLATE1 : Z := 0x1037f.     (* [comment removed for export] *)
Definition AL_N_DEFLATE2 : Z := 0x104f8.     (* [comment removed for export] *)
Definition AL_N_DEFLATE3 : Z := 0x103f8.     (* [comment removed for export] *)
Definition AL_N_INFLATE : Z := 0x104df.      (* [comment removed for export] *)
Definition AL_GREEDY : Z := 0x1041d.         (* [comment removed for export] *)
Definition AL_FINISH : Z := 0x10431.         (* [comment removed for export] *)
Definition AL_FMT_BAD : Z := 0x1048f.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ZHL_DIFF : Z := ZH_STATICS.
Definition ZHL_DATA : Z := ZH_STATICS + 8.

(* [comment removed for export] *)
Definition Z_DEFLATEPARAMS_STACK : Z := 48 + Z_DEFLATE_STACK.
Definition ZHL_TEST_STACK : Z := ZH_TEST_STACK.
Definition LXL_FUZZ_STACK : Z := LX_FUZZ_STACK.

(* [comment removed for export] *)

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapiL.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zhl_diff (m : mem) (diff : Z) : Prop := rw_cells psegs m ZHL_DIFF [C4 (wz diff)].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dsl_tin (ds : DSL za) : Z := ZIface.zs_total_in (ZApiInst.dz_z ds).
Definition dsl_tout (ds : DSL za) : Z := ZIface.zs_total_out (ZApiInst.dz_z ds).

(* [comment removed for export] *)
Definition blk5L (b : bptr * bptr * bptr * bptr * bptr) (As Aw Ap Ah Ab : Z) : list block :=
  let '(sp, wp, pp, hp, bp) := b in
  [(bp, Ab, zl_dpend za); (hp, Ah, zl_dhead za); (pp, Ap, zl_dprev za); (wp, Aw, zl_dwin za); (sp, As, zl_dstate za)].

Definition iblocksL (w : option bptr) (Aw : Z) (sp : bptr) (As : Z) : list block :=
  match w with Some wp => [(wp, Aw, zl_wsize za)] | None => [] end ++ [(sp, As, zl_isize za)].

(* [comment removed for export] *)
Record zrepsL : Type := mkZrepsL {
  zrd : mem -> Z -> list block -> DSL za -> Prop;
  zri : mem -> Z -> list block -> ISL za -> Prop;
  zrd_frame : forall m m' S LBz ds, zrd m S LBz ds ->
    (forall a, 0 <= a < 2^64 -> (S + ZS_PUB <= a < S + ZS_SIZEOF \/ in_block LBz a) ->
       m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
    zrd m' S LBz ds;
  zri_frame : forall m m' S LBz is, zri m S LBz is ->
    (forall a, 0 <= a < 2^64 -> (S + ZS_PUB <= a < S + ZS_SIZEOF \/ in_block LBz a) ->
       m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
    zri m' S LBz is;
  zrd_stream : forall m S LBz ds, zrd m S LBz ds -> exists j : list byte, rw_cells psegs m (S + ZS_PUB) [CB 64 j];
  zri_stream : forall m S LBz is, zri m S LBz is -> exists j : list byte, rw_cells psegs m (S + ZS_PUB) [CB 64 j]
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Api.
Variable R : zrepsL.

(* [comment removed for export] *)
Definition deflateInit9_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S ni ai no ao : Z) (p1 p2 : list byte) (lo B : Z) (canary : word) (m : mem)
    (r : option (bptr * bptr * bptr * bptr * bptr)) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ match r with
       | Some b => exists As Aw Ap Ah Ab,
           lx_post_env m m' s s' (blk5L b As Aw Ap Ah Ab) LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_OK
           /\ rw_cells psegs m' S (zs_pub ni ai (dsl_tin (dl_init9 za)) no ao (dsl_tout (dl_init9 za)) p1 p2)
           /\ dsl_tin (dl_init9 za) = 0 /\ dsl_tout (dl_init9 za) = 0
           /\ zrd R m' S (blk5L b As Aw Ap Ah Ab) (dl_init9 za)
       | None =>
           lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_MEM_ERROR
           /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j])
       end.

Definition deflateInit9_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S ni ai ti no ao to : Z) (p1 p2 : list byte) (jmsg jstate : word) (jrest : list byte)
         (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jrest]) ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_DEFLATEINIT_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S -> a1 = wz Z_BEST_COMPRESSION -> a2 = wz A_ZVERSION -> a3 = wz ZS_SIZEOF ->
  implM psegs (deflate_initL lops za) s
        (deflateInit9_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DEFLATEINIT_) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition deflate_postL (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S NI NO : Z) (LBz : list block) (inp oldc : list Z) (ds : DSL za) (ao flush : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' p1' p2',
    let '(ds', consumed, bs, rc) := dl_deflate za inp ds ao flush in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch ([(lo, bv_unsigned sp); (S, S + ZS_SIZEOF); (NO, NO + zlength bs)]
              ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ a0 = wint rc
    /\ 0 <= consumed <= zlength inp /\ zlength bs <= ao /\ Forall (fun c => 0 <= c < 256) bs
    /\ 0 <= dsl_tin ds' <= dsl_tin ds + zlength inp /\ 0 <= dsl_tout ds' <= dsl_tout ds + ao
    /\ rw_cells psegs m' S (zs_pub (NI + consumed) (zlength inp - consumed) (dsl_tin ds') (NO + zlength bs) (ao - zlength bs) (dsl_tout ds') p1' p2')
    /\ zrd R m' S LBz ds'
    /\ u8arr psegs m' NO (to_bytes (zstore oldc 0 bs)).

Definition deflate_stmtL : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (S NI NO : Z) (LBz : list block) (inp oldc : list Z) (ds : DSL za) (ao flush : Z) (p1 p2 : list byte) (lo B : Z),
  rw_cells psegs m S (zs_pub NI (zlength inp) (dsl_tin ds) NO ao (dsl_tout ds) p1 p2) ->
  zrd R m S LBz ds ->
  bytes_at psegs m NI (to_bytes inp) -> Forall (fun c => 0 <= c < 256) inp -> 0 < NI -> NI + zlength inp < 2^63 ->
  u8arr psegs m NO (to_bytes oldc) -> zlength oldc = ao -> 0 < NO -> NO + ao < 2^63 ->
  zlength inp < 2^31 -> 0 <= ao < 2^31 ->
  0 <= dsl_tin ds -> dsl_tin ds + zlength inp < 2^63 -> 0 <= dsl_tout ds -> dsl_tout ds + ao < 2^63 ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  (* [comment removed for export] *)
  NO + ao <= lo -> NI + zlength inp <= lo -> (NO + ao <= 0x10000 \/ 0x5c000 <= NO) ->
  (forall b, In b LBz -> blk_addr b + blk_size b <= NO \/ NO + ao <= blk_addr b) ->
  (forall b, In b LBz -> blk_addr b + blk_size b <= NI \/ NI + zlength inp <= blk_addr b) ->
  (NI + zlength inp <= NO \/ NO + ao <= NI) ->
  zl_statics m ->
  strm_in_frame sp S B -> stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  lo <= bv_unsigned sp - Z_DEFLATE_STACK -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= B -> B < 2^63 ->
  mem_inv psegs m ->
  a0 = wz S -> a1 = wz flush ->
  evt psegs (deflate_postL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S NI NO LBz inp oldc ds ao flush lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition deflateParams_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S NI NO : Z) (LBz : list block) (inp oldc : list Z) (ds : DSL za) (ao level strategy : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' p1' p2',
    let '(ds', consumed, bs, rc) := dl_params za inp ds ao level strategy in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch ([(lo, bv_unsigned sp); (S, S + ZS_SIZEOF); (NO, NO + zlength bs)]
              ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ a0 = wint rc
    /\ 0 <= consumed <= zlength inp /\ zlength bs <= ao /\ Forall (fun c => 0 <= c < 256) bs
    /\ 0 <= dsl_tin ds' <= dsl_tin ds + zlength inp /\ 0 <= dsl_tout ds' <= dsl_tout ds + ao
    /\ rw_cells psegs m' S (zs_pub (NI + consumed) (zlength inp - consumed) (dsl_tin ds') (NO + zlength bs) (ao - zlength bs) (dsl_tout ds') p1' p2')
    /\ zrd R m' S LBz ds'
    /\ u8arr psegs m' NO (to_bytes (zstore oldc 0 bs)).

Definition deflateParams_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (S NI NO : Z) (LBz : list block) (inp oldc : list Z) (ds : DSL za) (ao level strategy : Z) (p1 p2 : list byte) (lo B : Z),
  rw_cells psegs m S (zs_pub NI (zlength inp) (dsl_tin ds) NO ao (dsl_tout ds) p1 p2) ->
  zrd R m S LBz ds ->
  bytes_at psegs m NI (to_bytes inp) -> Forall (fun c => 0 <= c < 256) inp -> 0 < NI -> NI + zlength inp < 2^63 ->
  u8arr psegs m NO (to_bytes oldc) -> zlength oldc = ao -> 0 < NO -> NO + ao < 2^63 ->
  zlength inp < 2^31 -> 0 <= ao < 2^31 ->
  0 <= dsl_tin ds -> dsl_tin ds + zlength inp < 2^63 -> 0 <= dsl_tout ds -> dsl_tout ds + ao < 2^63 ->
  ((level = Z_NO_COMPRESSION /\ strategy = Z_DEFAULT_STRATEGY) \/ (level = Z_BEST_COMPRESSION /\ strategy = Z_FILTERED)) ->
  NO + ao <= lo -> NI + zlength inp <= lo -> (NO + ao <= 0x10000 \/ 0x5c000 <= NO) ->
  (forall b, In b LBz -> blk_addr b + blk_size b <= NO \/ NO + ao <= blk_addr b) ->
  (forall b, In b LBz -> blk_addr b + blk_size b <= NI \/ NI + zlength inp <= blk_addr b) ->
  (NI + zlength inp <= NO \/ NO + ao <= NI) ->
  zl_statics m ->
  strm_in_frame sp S B -> stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  lo <= bv_unsigned sp - Z_DEFLATEPARAMS_STACK -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= B -> B < 2^63 ->
  mem_inv psegs m ->
  a0 = wz S -> a1 = wz level -> a2 = wz strategy ->
  evt psegs (deflateParams_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S NI NO LBz inp oldc ds ao level strategy lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATEPARAMS) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition deflateEnd_postL (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S : Z) (ds : DSL za) (lo B : Z) (canary : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
    /\ a0 = wint (dl_end za ds)
    /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j]).

Definition deflateEnd_stmtL : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S : Z) (b : bptr * bptr * bptr * bptr * bptr) (As Aw Ap Ah Ab : Z) (ds : DSL za)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (blk5L b As Aw Ap Ah Ab) LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2) ->
  zrd R m S (blk5L b As Aw Ap Ah Ab) ds ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_DEFLATEEND_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S ->
  implM psegs (deflate_endL lops b) s
        (deflateEnd_postL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ds lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DEFLATEEND) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition inflateInit_postL (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S ni ai no ao : Z) (p1 p2 : list byte) (lo B : Z) (canary : word) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ match r with
       | Some p => exists As,
           lx_post_env m m' s s' (iblocksL None 0 p As) LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_OK
           /\ rw_cells psegs m' S (zs_pub ni ai (il_total_in za (il_init za)) no ao (il_total_out za (il_init za)) p1 p2)
           /\ zri R m' S (iblocksL None 0 p As) (il_init za)
       | None =>
           lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_MEM_ERROR
           /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j])
       end.

Definition inflateInit_stmtL : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S ni ai ti no ao to : Z) (p1 p2 : list byte) (jmsg jstate : word) (jrest : list byte)
         (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jrest]) ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_INFLATEINIT_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S -> a1 = wz A_ZVERSION -> a2 = wz ZS_SIZEOF ->
  implM psegs (lib_malloc lops (zl_isize za)) s
        (inflateInit_postL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_INFLATEINIT_) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition i_wantsbL (cl size : Z) (comprc : list Z) (is : ISL za) (w : option bptr) : bool :=
  il_wants_window za (zdrop (il_total_in za is) comprc) is size && (match w with None => true | Some _ => false end).
Definition i_okL (cl size : Z) (comprc : list Z) (is : ISL za) (w r : option bptr) : bool :=
  if i_wantsbL cl size comprc is w then (match r with Some _ => true | None => false end) else true.
Definition i_windowL (cl size : Z) (comprc : list Z) (is : ISL za) (w r : option bptr) : option bptr :=
  if i_wantsbL cl size comprc is w then r else w.

#[local] Transparent the_zapiL.
Definition iz_six_eqL (a b : ISL za) : Prop :=
  exists (total check total_in total_out adler data_type : Z),
    b = OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z.ZApiInst.mkIZ
          (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z.InflateState.iset_check (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z.InflateState.iset_total (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z.ZApiInst.iz_s a) total) check)
          (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z.ZIface.zs_set_data_type data_type (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z.ZIface.zs_set_adler adler
             (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z.ZIface.zs_set_total_out total_out (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z.ZIface.zs_set_total_in total_in (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z.ZApiInst.iz_z a))))).
Definition inflate_postL (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S C U cl size : Z) (comprc uc : list Z) (is : ISL za)
    (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z) (lo B : Z) (canary : word) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' p1' p2' Aw' ni' ai' (isr : ISL za),
    let '(is', consumed, bs, rc) := il_inflate za (zdrop (il_total_in za is) comprc) is size (i_okL cl size comprc is w r) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' (iblocksL (i_windowL cl size comprc is w r) Aw' sp_ As) LB sp tp B lo canary
                   [(S, S + ZS_SIZEOF); (U, U + size)] fc'
    /\ (w <> None -> Aw' = Aw)
    /\ a0 = wint rc
    /\ zlength bs <= size
    /\ rw_cells psegs m' S (zs_pub ni' ai' (il_total_in za isr) (U + zlength bs) (size - zlength bs) (il_total_out za isr) p1' p2')
    /\ (rc = Z_OK -> ni' = C + il_total_in za is' /\ ai' = cl - il_total_in za is' /\ 0 <= il_total_in za is' <= cl)
    /\ (rc = Z_OK \/ rc = Z_STREAM_END -> il_total_out za is' = il_total_out za is + zlength bs)
    /\ zri R m' S (iblocksL (i_windowL cl size comprc is w r) Aw' sp_ As) isr
    /\ u8arr psegs m' U (to_bytes (zstore uc 0 bs))
    /\ (rc = Z_MEM_ERROR -> iz_six_eqL is' isr) /\ (rc <> Z_MEM_ERROR -> isr = is').
#[local] Opaque the_zapiL.

Definition inflate_stmtL : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S C U cl size : Z) (comprc uc : list Z) (is : ISL za)
         (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (iblocksL w Aw sp_ As) LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub (C + il_total_in za is) (cl - il_total_in za is) (il_total_in za is) U size (il_total_out za is) p1 p2) ->
  zri R m S (iblocksL w Aw sp_ As) is ->
  (exists b, In b LB /\ blk_addr b = C /\ blk_size b = cl) -> u8arr psegs m C (to_bytes comprc) -> zlength comprc = cl ->
  Forall (fun c => 0 <= c < 256) comprc ->
  (exists b, In b LB /\ blk_addr b = U /\ blk_size b = size) -> u8arr psegs m U (to_bytes uc) -> zlength uc = size ->
  0 <= il_total_in za is <= cl -> cl < 2^31 -> 0 <= size < 2^31 ->
  0 <= il_total_out za is -> il_total_out za is + size < 2^63 ->
  (U + size <= C \/ C + cl <= U) ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_INFLATE_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S -> a1 = wz Z_NO_FLUSH ->
  implM psegs (if i_wantsbL cl size comprc is w then lib_malloc lops (zl_wsize za) else ret lops None) s
        (inflate_postL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S C U cl size comprc uc is w Aw sp_ As lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_INFLATE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition inflateEnd_postL (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S : Z) (is : ISL za) (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (canary : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
    /\ a0 = wint (il_end za is)
    /\ (exists j : list byte, rw_cells psegs m' S (zs_pub ni ai ti no ao to p1 p2 ++ [CB 64 j])).

Definition inflateEnd_stmtL : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S : Z) (is : ISL za) (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (iblocksL w Aw sp_ As) LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2) ->
  zri R m S (iblocksL w Aw sp_ As) is ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_INFLATEEND_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S ->
  implM psegs (bind lops (lib_free lops w) (fun _ => lib_free lops (Some sp_))) s
        (inflateEnd_postL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S is ni ai ti no ao to p1 p2 lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_INFLATEEND) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition zlib_okL : Prop :=
  deflateInit9_stmt /\ deflate_stmtL /\ deflateParams_stmt /\ deflateEnd_stmtL
  /\ inflateInit_stmtL /\ inflate_stmtL /\ inflateEnd_stmtL.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rtest_large_deflate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (C N : Z) (lo B : Z) (canary : word) (m : mem)
    (r : list Z * Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' LK,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' LK LB sp tp B lo canary [(C, C + N); LXW_ZH; LXW_STDERR] fc'
    /\ (length LK <= 5)%nat
    /\ u8arr psegs m' C (to_bytes (fst r)) /\ zlength (fst r) = N
    /\ zhl_diff m' (snd r) /\ 0 <= snd r < 2^32.

Definition rtest_large_deflate_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (C U size N diff : Z) (cp up : bptr) (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  zhl_diff m diff -> 0 <= diff < 2^32 ->
  1 <= size <= ZL_MAX -> N = NofL size ->
  In (cp, C, N) LB -> u8arr psegs m C (to_bytes (zrepeat 0 N)) ->
  In (up, U, N) LB -> u8arr psegs m U (to_bytes (zrepeat 0 N)) -> cp <> up ->
  lo <= bv_unsigned sp - ZHL_TEST_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz C -> a1 = wz N -> a2 = wz U -> a3 = wz N ->
  implM psegs (test_large_deflateM lops za N diff) s
        (rtest_large_deflate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB C N lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ZHL_TEST_DEFLATE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition rtest_large_inflate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (U N : Z) (lo B : Z) (canary : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' LK,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' LK LB sp tp B lo canary [(U, U + N); LXW_STDERR] fc'
    /\ (length LK <= 2)%nat.

Definition rtest_large_inflate_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (C U size N diff : Z) (comprc uc : list Z) (cp up : bptr) (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  zhl_diff m diff -> 0 <= diff < 2^32 ->
  1 <= size <= ZL_MAX -> N = NofL size ->
  In (cp, C, N) LB -> u8arr psegs m C (to_bytes comprc) -> zlength comprc = N ->
  In (up, U, N) LB -> u8arr psegs m U (to_bytes uc) -> zlength uc = N -> cp <> up ->
  lo <= bv_unsigned sp - ZHL_TEST_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz C -> a1 = wz N -> a2 = wz U -> a3 = wz N ->
  implM psegs (test_large_inflateM lops za N comprc diff) s
        (rtest_large_inflate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB U N lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ZHL_TEST_INFLATE) fc None m (seg_rom psegs)).
End Api.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rfuzz_oneL_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word) (m : mem)
    (r : Z * Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' LK,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' LK LB sp tp B lo canary [LXW_ZH; LXW_STDERR] fc'
    /\ (length LK <= 7)%nat
    /\ fst r = 0 /\ a0 = wz 0
    /\ payload_ok m' LB D d
    /\ zhl_diff m' (snd r) /\ 0 <= snd r < 2^32.

Definition rfuzz_oneL_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (D : Z) (d : list Z) (diff : Z) (lo B : Z) (errv canary : word),
  RHEAP s LB m -> lx_statics m -> zl_statics m -> stderr_wfile0 m -> ssp_cells m canary ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv psegs m ->
  bv_unsigned sp mod 16 = 0 ->
  payload_ok m LB D d ->
  zhl_diff m diff -> 0 <= diff < 2^32 ->
  frm0 fc ->
  a0 = wz D -> a1 = wz (zlength d) ->
  implM psegs (fuzz_oneL lops za d diff) s
        (rfuzz_oneL_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz LX_FUZZ) fc None m (seg_rom psegs)).
End WithCeiling0.
