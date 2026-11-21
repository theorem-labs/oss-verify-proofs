(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget ZApiL ZHarnessL ZApiC ZHarnessC ZInstC ZTargetC Target Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZIface ZApiInst.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Layout F_atexit Exit Exit_cb Printf_wfile Zg_zlib_iface Driver_iface Drv_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Export Zlib_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition ZC_COMPRESS2 : Z := 0x16248.
Definition ZC_UNCOMPRESS2 : Z := 0x1cd28.  (* 1.4: uncompress calls uncompress2_z (uncompr.c); uncompress2 itself is not in this binary *)
Definition ZC_UNCOMPRESS : Z := 0x1ceb0.

Definition RC_MALLOC : Z := 0x20b28.
Definition RC_FREE : Z := 0x209e8.
Definition RC_MEMCPY : Z := 0x27998.
Definition RC_EXIT : Z := 0x206ac.

Definition A_MAGIC5 : Z := 0x10688.

Definition ZHC_DATA : Z := ZH_STATICS.
Definition ZHC_DATALEN : Z := ZH_STATICS + 8.

Definition ZC_WRAP_STACK : Z := 176 + Z_INFLATE_STACK.
Definition ZC_UNC_STACK : Z := 32 + ZC_WRAP_STACK.  (* 1.4: uncompress's frame is 32 bytes (1.3.1: 16) *)

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.
Notation zc := the_zapiC.

Definition zhc_statics (m : mem) (D n : Z) : Prop := rw_cells psegs m ZH_STATICS [C8 (wz D); C8 (wz n)].

Definition REXIT_LOCK : Z := 0x5ab68.
Definition xcb_cells (m : mem) : Prop :=
  exists (td0 td1 td2 td3 : word) (t : Z),
    rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] /\ 0 < t < 4194304
    /\ rw_cells psegs m REXIT_LOCK [C4 (Z_to_bv 64 0)].
Definition xcb_addr (a : Z) : Prop := (RTD <= a < RTD + 36) \/ (REXIT_LOCK <= a < REXIT_LOCK + 4).

Definition got_stdout_cells (m : mem) : Prop :=
  rw_cells psegs m RGOT_STDOUTP [C8 (Z_to_bv 64 RSTDOUTP)] /\ rw_cells psegs m RSTDOUTP [C8 (Z_to_bv 64 RSTDOUT)].

Definition dsc_tin (ds : DSC zc) : Z := ZIface.zs_total_in (ZApiInst.dz_z ds).
Definition dsc_tout (ds : DSC zc) : Z := ZIface.zs_total_out (ZApiInst.dz_z ds).

Section Api.
Variable R : zreps.

Definition deflateInit_postC (lv : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S ni ai no ao : Z) (p1 p2 : list byte) (lo B : Z) (canary : word) (m : mem)
    (r : option (bptr * bptr * bptr * bptr * bptr)) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ match r with
       | Some b => exists As Aw Ap Ah Ab,
           lx_post_env m m' s s' (blk5_blocks b As Aw Ap Ah Ab) LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_OK
           /\ rw_cells psegs m' S (zs_pub ni ai 0 no ao 0 p1 p2)
           /\ dsc_tin (dc_init zc lv) = 0 /\ dsc_tout (dc_init zc lv) = 0
           /\ zr_d R m' S (blk5_blocks b As Aw Ap Ah Ab) (dc_init zc lv)
       | None =>
           lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_MEM_ERROR
           /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j])
       end.

Definition deflateInit_stmtC (lv : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S ni ai ti no ao to : Z) (p1 p2 : list byte) (jmsg jstate : word) (jrest : list byte)
         (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jrest]) ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_DEFLATEINIT_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S -> a1 = wint lv -> a2 = wz A_ZVERSION -> a3 = wz ZS_SIZEOF ->
  implM psegs (deflate_initC lops zc) s
        (deflateInit_postC lv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DEFLATEINIT_) fc None m (seg_rom psegs)).

Definition deflate_postC (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S NI NO : Z) (LBz : list block) (inp oldc : list Z) (ds : DSC zc) (ao flush : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' p1' p2',
    let '(ds', consumed, bs, rc) := dc_deflate zc inp ds ao flush in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch ([(lo, bv_unsigned sp); (S, S + ZS_SIZEOF); (NO, NO + zlength bs)]
              ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ a0 = wint rc
    /\ 0 <= consumed <= zlength inp /\ zlength bs <= ao /\ Forall (fun c => 0 <= c < 256) bs
    /\ 0 <= dsc_tin ds' <= dsc_tin ds + zlength inp /\ 0 <= dsc_tout ds' <= dsc_tout ds + ao
    /\ rw_cells psegs m' S (zs_pub (NI + consumed) (zlength inp - consumed) (dsc_tin ds') (NO + zlength bs) (ao - zlength bs) (dsc_tout ds') p1' p2')
    /\ zr_d R m' S LBz ds'
    /\ u8arr psegs m' NO (to_bytes (zstore oldc 0 bs)).

Definition deflate_stmtC : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (S NI NO : Z) (LBz : list block) (inp oldc : list Z) (ds : DSC zc) (ao flush : Z) (p1 p2 : list byte) (lo B : Z),
  rw_cells psegs m S (zs_pub NI (zlength inp) (dsc_tin ds) NO ao (dsc_tout ds) p1 p2) ->
  zr_d R m S LBz ds ->
  bytes_at psegs m NI (to_bytes inp) -> Forall (fun c => 0 <= c < 256) inp -> 0 < NI -> NI + zlength inp < 2^63 ->
  u8arr psegs m NO (to_bytes oldc) -> zlength oldc = ao -> 0 < NO -> NO + ao < 2^63 ->
  zlength inp < 2^31 -> 0 <= ao < 2^31 ->
  0 <= dsc_tin ds -> dsc_tin ds + zlength inp < 2^63 -> 0 <= dsc_tout ds -> dsc_tout ds + ao < 2^63 ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->

  NO + ao <= lo -> NI + zlength inp <= lo -> (NO + ao <= 0x10000 \/ 0x5c000 <= NO) ->
  (forall b, In b LBz -> blk_addr b + blk_size b <= NO \/ NO + ao <= blk_addr b) ->
  (forall b, In b LBz -> blk_addr b + blk_size b <= NI \/ NI + zlength inp <= blk_addr b) ->
  (NI + zlength inp <= NO \/ NO + ao <= NI) ->
  zl_statics m ->
  strm_in_frame sp S B -> stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  lo <= bv_unsigned sp - Z_DEFLATE_STACK -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= B -> B < 2^63 ->
  mem_inv psegs m ->
  a0 = wz S -> a1 = wz flush ->
  evt psegs (deflate_postC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S NI NO LBz inp oldc ds ao flush lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATE) fc None m (seg_rom psegs)).

Definition deflateEnd_postC (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S : Z) (ds : DSC zc) (lo B : Z) (canary : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
    /\ a0 = wint (dc_end zc ds)
    /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j]).

Definition deflateEnd_stmtC : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S : Z) (b : bptr * bptr * bptr * bptr * bptr) (As Aw Ap Ah Ab : Z) (ds : DSC zc)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (blk5_blocks b As Aw Ap Ah Ab) LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2) ->
  zr_d R m S (blk5_blocks b As Aw Ap Ah Ab) ds ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_DEFLATEEND_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S ->
  implM psegs (deflate_endC lops b) s
        (deflateEnd_postC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ds lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DEFLATEEND) fc None m (seg_rom psegs)).

Definition inflateEnd_postX (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (canary : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
    /\ a0 = wint Z_OK
    /\ (exists j : list byte, rw_cells psegs m' S (zs_pub ni ai ti no ao to p1 p2 ++ [CB 64 j])).

Definition inflateEnd_stmtX : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S : Z) (is : IS za) (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (iblocks w Aw sp_ As) LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2) ->
  zr_i R m S (iblocks w Aw sp_ As) is ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_INFLATEEND_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S ->
  implM psegs (bind lops (lib_free lops w) (fun _ => lib_free lops (Some sp_))) s
        (inflateEnd_postX ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai ti no ao to p1 p2 lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_INFLATEEND) fc None m (seg_rom psegs)).

Definition zlib_okC : Prop :=
  (forall lv, 0 <= lv <= 9 -> deflateInit_stmtC lv) /\ deflate_stmtC /\ deflateEnd_stmtC
  /\ inflateInit_stmt R /\ inflate_stmtG R /\ inflateEnd_stmtX.
End Api.

Definition rcompress2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (C cl PL : Z) (oldc : list Z) (lo B : Z) (canary : word) (m : mem)
    (r : list Z * Z * Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (rc : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(C, C + cl); (PL, PL + 8)] fc'
    /\ a0 = wint rc /\ rc = snd r /\ - 2^31 <= rc < 2^31
    /\ u8arr psegs m' C (to_bytes (zstore oldc 0 (fst (fst r))))
    /\ snd (fst r) = zlength (fst (fst r)) /\ zlength (fst (fst r)) <= cl /\ Forall (fun c => 0 <= c < 256) (fst (fst r))
    /\ rw_cells psegs m' PL [C8 (wz (snd (fst r)))].

Definition rcompress2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (cp : bptr) (C cl PL NI n lv : Z) (oldc src : list Z) (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  In (cp, C, cl) LB -> u8arr psegs m C (to_bytes oldc) -> zlength oldc = cl ->
  rw_cells psegs m PL [C8 (wz cl)] -> bv_unsigned sp <= PL -> PL + 8 <= B -> PL mod 8 = 0 ->
  bytes_at psegs m NI (to_bytes src) -> Forall (fun c => 0 <= c < 256) src -> zlength src = n ->
  (exists b, In b LB /\ blk_addr b <= NI /\ NI + n <= blk_addr b + blk_size b) ->
  (NI + n <= C \/ C + cl <= NI) ->
  ZC_MIN - 3 <= n <= ZC_MAX - 3 -> cl = zc_bound zc n -> 0 <= lv <= 9 ->
  lo <= bv_unsigned sp - ZC_WRAP_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz C -> a1 = wz PL -> a2 = wz NI -> a3 = wz n -> a4 = wz lv ->
  implM psegs (compress2M lops zc cl src lv) s
        (rcompress2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB C cl PL oldc lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ZC_COMPRESS2) fc None m (seg_rom psegs)).

Definition runcompress2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (U dlen PL PS : Z) (uc : list Z) (lo B : Z) (canary : word) (m : mem)
    (r : list Z * Z * Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (rc slen' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(U, U + dlen); (PL, PL + 8); (PS, PS + 8)] fc'
    /\ a0 = wint rc /\ rc = snd r /\ - 2^31 <= rc < 2^31
    /\ u8arr psegs m' U (to_bytes (zstore uc 0 (fst (fst r))))
    /\ zlength (fst (fst r)) <= dlen /\ 0 <= snd (fst r) < 2^64
    /\ rw_cells psegs m' PL [C8 (wz (snd (fst r)))]
    /\ rw_cells psegs m' PS [C8 (wz slen')].

Definition runcompress2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (up cpS : bptr) (U dlen PL C cl slen PS : Z) (uc comprc src : list Z) (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  In (up, U, dlen) LB -> u8arr psegs m U (to_bytes uc) -> zlength uc = dlen ->
  rw_cells psegs m PL [C8 (wz dlen)] -> bv_unsigned sp <= PL -> PL + 8 <= B -> PL mod 8 = 0 ->
  In (cpS, C, cl) LB -> u8arr psegs m C (to_bytes comprc) -> zlength comprc = cl -> Forall (fun c => 0 <= c < 256) comprc ->
  0 <= slen <= cl -> ztake slen comprc = src ->
  rw_cells psegs m PS [C8 (wz slen)] -> bv_unsigned sp <= PS -> PS + 8 <= B -> PS mod 8 = 0 ->
  (PL + 8 <= PS \/ PS + 8 <= PL) ->
  up <> cpS ->
  0 < dlen <= zc_bound zc (ZC_MAX - 3) -> cl <= zc_bound zc (ZC_MAX - 3) ->
  lo <= bv_unsigned sp - ZC_WRAP_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz U -> a1 = wz PL -> a2 = wz C -> a3 = wz PS ->
  implM psegs (uncompress2M lops zc dlen src) s
        (runcompress2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB U dlen PL PS uc lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ZC_UNCOMPRESS2) fc None m (seg_rom psegs)).

Definition runcompress_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (U dlen PL : Z) (uc : list Z) (lo B : Z) (canary : word) (m : mem)
    (r : list Z * Z * Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (rc : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(U, U + dlen); (PL, PL + 8)] fc'
    /\ a0 = wint rc /\ rc = snd r /\ - 2^31 <= rc < 2^31
    /\ u8arr psegs m' U (to_bytes (zstore uc 0 (fst (fst r))))
    /\ zlength (fst (fst r)) <= dlen /\ 0 <= snd (fst r) < 2^64
    /\ rw_cells psegs m' PL [C8 (wz (snd (fst r)))].

Definition runcompress_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (up cpS : bptr) (U dlen PL C cl slen : Z) (uc comprc src : list Z) (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  In (up, U, dlen) LB -> u8arr psegs m U (to_bytes uc) -> zlength uc = dlen ->
  rw_cells psegs m PL [C8 (wz dlen)] -> bv_unsigned sp <= PL -> PL + 8 <= B -> PL mod 8 = 0 ->
  In (cpS, C, cl) LB -> u8arr psegs m C (to_bytes comprc) -> zlength comprc = cl -> Forall (fun c => 0 <= c < 256) comprc ->
  0 <= slen <= cl -> ztake slen comprc = src ->
  up <> cpS ->
  0 < dlen <= zc_bound zc (ZC_MAX - 3) -> cl <= zc_bound zc (ZC_MAX - 3) ->
  lo <= bv_unsigned sp - ZC_UNC_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz U -> a1 = wz PL -> a2 = wz C -> a3 = wz slen ->
  implM psegs (uncompress2M lops zc dlen src) s
        (runcompress_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB U dlen PL uc lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ZC_UNCOMPRESS) fc None m (seg_rom psegs)).

Definition rfuzz_oneC_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (errv canary : word),
  RHEAP s LB m -> lx_statics m -> zl_statics m -> stderr_wfile0 m -> ssp_cells m canary ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv psegs m ->
  bv_unsigned sp mod 16 = 0 ->
  payload_ok m LB D d ->
  stdout_file m (ps_so s) -> adp_cells_cb m -> xcb_cells m ->
  frm0 fc ->
  a0 = wz D -> a1 = wz (zlength d) ->
  implM psegs (fuzz_oneC lops (@Target.err_pieces PState) (Target.cb_exit ps_so set_so_ps) zc d) s
        (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz LX_FUZZ) fc None m (seg_rom psegs)).

Lemma xcb_cells_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, xcb_addr a -> P a) -> xcb_cells m -> xcb_cells m'.
Proof.
  intros P m m' AG HP (td0 & td1 & td2 & td3 & t & X1 & Ht & X2). exists td0, td1, td2, td3, t.
  split; [eapply rw_cells_agree; [exact AG| exact X1| intros a Ha; cbn in Ha; apply HP; unfold xcb_addr; lia]|]. split; [exact Ht|].
  eapply rw_cells_agree; [exact AG| exact X2| intros a Ha; cbn in Ha; apply HP; unfold xcb_addr; lia].
Qed.

Definition rtarget_run_stmtC : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (B lo : Z)
         (errv : word),
  RHEAP s LB m -> In (p, A, cap) LB ->
  bytes_at psegs m A (to_bytes content) -> Forall (fun c => 0 <= c < 256) content ->
  zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
  lx_statics m -> zl_statics m -> stderr_wfile0 m -> ssp_cells m rr_guard ->
  stdout_file m (ps_so s) -> xcb_cells m ->
  rdrv_statics m -> rw_cells psegs m RGOT_LLVMINIT [C8 (wz 0)] ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - RTARGET_RUN_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv psegs m -> frm0 fc ->
  bv_unsigned sp mod 16 = 0 ->
  a0 = wz (A + 2) -> a1 = wz L -> a2 = wz (A + 6 + L) -> a3 = wz (zlength content - 6 - L) ->
  implM psegs (run (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
        (rtarget_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB B lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz RTARGET_RUN) fc None m (seg_rom psegs)).

End WithCeiling0.
