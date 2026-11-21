(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Layout Exit Printf_wfile.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition lops : target_ops (M PState) bptr := Target.ops raw_malloc raw_free ps_so set_so_ps.
Notation za := the_zapi.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LX_FUZZ : Z := 0x161a4.            (* [comment removed for export] *)
Definition ZH_TEST_DEFLATE : Z := 0x15dec.    (* [comment removed for export] *)
Definition ZH_TEST_INFLATE : Z := 0x15f50.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition Z_COMPRESSBOUND : Z := 0x1fb2c.    (* [comment removed for export] *)
Definition Z_DEFLATEINIT_ : Z := 0x16258.     (* [comment removed for export] *)
Definition Z_DEFLATE : Z := 0x16ed8.          (* [comment removed for export] *)
Definition Z_DEFLATEEND : Z := 0x165ac.       (* [comment removed for export] *)
Definition Z_INFLATEINIT_ : Z := 0x1d0f4.     (* [comment removed for export] *)
Definition Z_INFLATE : Z := 0x1d24c.          (* [comment removed for export] *)
Definition Z_INFLATEEND : Z := 0x1f164.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition R_CALLOC : Z := 0x2086c.           (* [comment removed for export] *)
Definition R_BCMP : Z := 0x27504.             (* [comment removed for export] *)
Definition R_FPRINTF : Z := 0x2279c.
Definition R_FWRITE : Z := 0x22938.

(* [comment removed for export] *)
Definition A_ZVERSION : Z := 0x10415.         (* [comment removed for export] *)
Definition A_FMT_ERR : Z := 0x102f2.          (* [comment removed for export] *)
Definition A_N_DEFLATEINIT : Z := 0x102ae.    (* [comment removed for export] *)
Definition A_N_DEFLATE1 : Z := 0x10476.       (* [comment removed for export] *)
Definition A_N_DEFLATE2 : Z := 0x105ec.       (* [comment removed for export] *)
Definition A_N_DEFLATEEND : Z := 0x1030b.     (* [comment removed for export] *)
Definition A_N_INFLATEINIT : Z := 0x102a2.    (* [comment removed for export] *)
Definition A_N_INFLATE : Z := 0x10561.        (* [comment removed for export] *)
Definition A_N_INFLATEEND : Z := 0x10346.     (* [comment removed for export] *)
Definition A_BAD_INFLATE : Z := 0x10298.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LX_GOT_STDERR : Z := 0x293d8.   (* [comment removed for export] *)
Definition LX_STDERR_PTR : Z := 0x29388.   (* [comment removed for export] *)
Definition LX_STDERR_FILE : Z := 0x2a460.  (* [comment removed for export] *)
Definition LX_EMPTY : Z := 0x3a6b0.        (* [comment removed for export] *)
Definition ZH_STATICS : Z := 0x3a6d0.      (* [comment removed for export] *)
Definition ZL_MREPL : Z := 0x5ae50.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ZL_RELRO_LO : Z := 0x29238.
Definition ZL_RELRO_HI : Z := 0x29398.
(* [comment removed for export] *)
Definition ZL_GOT_LO : Z := 0x29398.
Definition ZL_GOT_HI : Z := 0x29420.

(* [comment removed for export] *)
Definition ZS_SIZEOF : Z := 112.
Definition ZS_PUB : Z := 48.

(* [comment removed for export] *)
Definition LX_PRINTF_STACK : Z := 8192.                              (* [comment removed for export] *)
Definition Z_DEFLATE_STACK : Z := 4096.                              (* [comment removed for export] *)
Definition Z_DEFLATEINIT_STACK : Z := 256 + RMALLOC_STACK.           (* [comment removed for export] *)
Definition Z_DEFLATEEND_STACK : Z := 64 + RFREE_STACK.
Definition Z_INFLATEINIT_STACK : Z := 128 + RMALLOC_STACK.
Definition Z_INFLATE_STACK : Z := 1024 + RMALLOC_STACK.              (* [comment removed for export] *)
Definition Z_INFLATEEND_STACK : Z := 64 + RFREE_STACK.
Definition ZH_TEST_STACK : Z := 160 + LX_PRINTF_STACK + 4096.        (* [comment removed for export] *)
Definition LX_FUZZ_STACK : Z := 48 + ZH_TEST_STACK.                  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lx_statics (m : mem) : Prop :=
  rw_cells psegs m LX_GOT_STDERR [C8 (wz LX_STDERR_PTR)]
  /\ rw_cells psegs m LX_STDERR_PTR [C8 (wz LX_STDERR_FILE)].

(* [comment removed for export] *)
Definition zl_statics (m : mem) : Prop :=
  (forall a : word, ZL_RELRO_LO <= bv_unsigned a < ZL_RELRO_HI -> m a = None)
  /\ (forall a : word, ZL_GOT_LO <= bv_unsigned a < ZL_GOT_HI -> m a = None)
  /\ (exists v1 v2 : word, rw_cells psegs m ZH_STATICS [C8 v1; C8 v2])
  /\ rw_cells psegs m ZL_MREPL [C4 (wz 0)].

(* [comment removed for export] *)
Definition LXW_ZH : Z * Z := (ZH_STATICS, ZH_STATICS + 16).
Definition LXW_STDERR : Z * Z := (LX_STDERR_FILE, LX_STDERR_FILE + 232).

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition lx_client (LB : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop :=
  ~ rin_ivs X a /\ (SP <= a \/ in_block LB a \/ (0x29000 <= a < 0x5c000 /\ ~ ralloc_static a)).

Definition lx_pres (LB : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> lx_client LB SP X a ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).

Lemma lx_pres_refl : forall LB SP X m, lx_pres LB SP X m m.
Proof. intros LB SP X m a _ _. auto. Qed.

Lemma lx_pres_trans : forall LB SP X m1 m2 m3,
  lx_pres LB SP X m1 m2 -> lx_pres LB SP X m2 m3 -> lx_pres LB SP X m1 m3.
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

(* [comment removed for export] *)
Lemma lx_pres_weaken : forall LB LB' SP SP' X X' m m',
  lx_pres LB SP X m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
  lx_pres LB' SP' X' m m'.
Proof.
  intros LB LB' SP SP' X X' m m' H HS HL HX a Ha [Hx Hc]. apply H; [exact Ha|].
  split; [intros Hx'; apply Hx; apply HX; exact Hx'|].
  destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia| right; left| right; right; exact Hc].
  exists b. split; [apply HL; exact Hb|exact Hr].
Qed.

(* [comment removed for export] *)
Lemma lx_pres_of_heap_pres : forall LB SP X m m', rheap_pres LB SP m m' -> lx_pres LB SP X m m'.
Proof.
  intros LB SP X m m' H a Ha [_ Hc]. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc| right; right; exact Hc| right; left; exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition payload_ok (m : mem) (LB : list block) (D : Z) (d : list Z) : Prop :=
  bytes_at psegs m D (to_bytes d) /\ Forall (fun c => 0 <= c < 256) d
  /\ 0 < D /\ D + zlength d < 2^63 /\ zlength d < 2^30
  /\ (d = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lx_env (m : mem) (s : PState) (OW LB : list block) (sp tp : word) (B lo : Z) (errv canary : word) : Prop :=
  RHEAP s (OW ++ LB) m /\ lx_statics m /\ zl_statics m /\ stderr_wfile0 m /\ ssp_cells m canary
  /\ rauxv_ok m B /\ bv_unsigned sp <= B /\ B < 2^63
  /\ stk psegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
  /\ rw_cells psegs m (errno_addr tp) [C4 errv] /\ tp = wz RATP
  /\ mem_inv psegs m.

(* [comment removed for export] *)
Definition lx_post_env (m m' : mem) (s s' : PState) (OW' LB : list block) (sp tp : word) (B lo : Z) (canary : word)
    (X : list (Z * Z)) (fc' : bv 32) : Prop :=
  (exists errv' : word, lx_env m' s' OW' LB sp tp B lo errv' canary)
  /\ frm0 fc'
  /\ lx_pres LB (bv_unsigned sp) X m m'
  /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zs_pub (next_in avail_in total_in next_out avail_out total_out : Z) (pad1 pad2 : list byte) : list cell :=
  [C8 (wz next_in); C4 (wz avail_in); CB 4 pad1; C8 (wz total_in); C8 (wz next_out); C4 (wz avail_out); CB 4 pad2; C8 (wz total_out)].

(* [comment removed for export] *)
Definition wint (rc : Z) : word := wz (rc mod 2^64).

(* [comment removed for export] *)
Definition blk5_blocks (b : bptr * bptr * bptr * bptr * bptr) (As Aw Ap Ah Ab : Z) : list block :=
  let '(sp, wp, pp, hp, bp) := b in
  [(bp, Ab, z_dpend za); (hp, Ah, z_dhead za); (pp, Ap, z_dprev za); (wp, Aw, z_dwin za); (sp, As, z_dstate za)].

(* [comment removed for export] *)
Definition iblocks (w : option bptr) (Aw : Z) (sp : bptr) (As : Z) : list block :=
  match w with Some wp => [(wp, Aw, z_wsize za)] | None => [] end ++ [(sp, As, z_isize za)].

(* [comment removed for export] *)
Record zreps : Type := mkZreps {
  zr_d : mem -> Z -> list block -> DS za -> Prop;
  zr_i : mem -> Z -> list block -> IS za -> Prop;
  zr_d_frame : forall m m' S LBz ds, zr_d m S LBz ds ->
    (forall a, 0 <= a < 2^64 -> (S + ZS_PUB <= a < S + ZS_SIZEOF \/ in_block LBz a) ->
       m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
    zr_d m' S LBz ds;
  zr_i_frame : forall m m' S LBz is, zr_i m S LBz is ->
    (forall a, 0 <= a < 2^64 -> (S + ZS_PUB <= a < S + ZS_SIZEOF \/ in_block LBz a) ->
       m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
    zr_i m' S LBz is;
  (* [comment removed for export] *)
  zr_d_stream : forall m S LBz ds, zr_d m S LBz ds -> exists j : list byte, rw_cells psegs m (S + ZS_PUB) [CB 64 j];
  zr_i_stream : forall m S LBz is, zr_i m S LBz is -> exists j : list byte, rw_cells psegs m (S + ZS_PUB) [CB 64 j]
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Api.
Variable R : zreps.

(* [comment removed for export] *)
Definition strm_in_frame (sp : word) (S B : Z) : Prop :=
  bv_unsigned sp <= S /\ S + ZS_SIZEOF <= B /\ S mod 8 = 0.

(* [comment removed for export] *)
Definition compressBound_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom psegs)
    /\ (1 <= n <= ZH_MAX -> a0 = wz (z_bound za n)).

Definition compressBound_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (n : Z),
  0 <= n < 2^30 -> a0 = wz n -> mem_inv psegs m ->
  evt psegs (compressBound_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_COMPRESSBOUND) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition deflateInit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
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
           /\ zr_d R m' S (blk5_blocks b As Aw Ap Ah Ab) (d_init za)
       | None =>
           lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_MEM_ERROR
           /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j])
       end.

Definition deflateInit_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S ni ai ti no ao to : Z) (p1 p2 : list byte) (jmsg jstate : word) (jrest : list byte)
         (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jrest]) ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_DEFLATEINIT_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S -> a1 = wint (-1) -> a2 = wz A_ZVERSION -> a3 = wz ZS_SIZEOF ->
  implM psegs (deflate_init lops za) s
        (deflateInit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DEFLATEINIT_) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition deflate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S D C : Z) (LBz : list block) (d out : list Z) (ds : DS za) (ai ao flush : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' p1' p2',
    let '(ds', ai', ao', bs, rc) := d_deflate za d ds ai ao flush in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch ([(lo, bv_unsigned sp); (S, S + ZS_SIZEOF); (C + d_total_out za ds, C + d_total_out za ds + zlength bs)]
              ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ a0 = wint rc
    /\ rw_cells psegs m' S (zs_pub (D + d_total_in za ds') ai' (d_total_in za ds') (C + d_total_out za ds') ao' (d_total_out za ds') p1' p2')
    /\ zr_d R m' S LBz ds'
    /\ u8arr psegs m' C (to_bytes (zstore out (d_total_out za ds) bs))
    /\ bytes_at psegs m' D (to_bytes d).

Definition deflate_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (S D C cl : Z) (LBz : list block) (d out : list Z) (ds : DS za) (ai ao flush : Z) (p1 p2 : list byte) (lo B : Z),
  rw_cells psegs m S (zs_pub (D + d_total_in za ds) ai (d_total_in za ds) (C + d_total_out za ds) ao (d_total_out za ds) p1 p2) ->
  zr_d R m S LBz ds ->
  bytes_at psegs m D (to_bytes d) -> Forall (fun c => 0 <= c < 256) d -> 0 < D -> D + zlength d < 2^63 ->
  u8arr psegs m C (to_bytes out) -> zlength out = cl -> 0 < C -> C + cl < 2^63 ->
  0 <= ai <= 1 -> d_total_in za ds + ai <= zlength d -> 0 <= ao <= 1 ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  (* [comment removed for export] *)
  C + cl <= lo -> D + zlength d <= lo -> (C + cl <= 0x10000 \/ 0x5c000 <= C) ->     (* [comment removed for export] *)
  (forall b, In b LBz -> blk_addr b + blk_size b <= C \/ C + cl <= blk_addr b) ->
  (forall b, In b LBz -> blk_addr b + blk_size b <= D \/ D + zlength d <= blk_addr b) ->
  (D + zlength d <= C \/ C + cl <= D) ->
  d_total_out za ds + zlength (snd (fst (d_deflate za d ds ai ao flush))) <= cl ->
  zl_statics m ->
  strm_in_frame sp S B -> stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  lo <= bv_unsigned sp - Z_DEFLATE_STACK -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= B -> B < 2^63 ->
  mem_inv psegs m ->
  a0 = wz S -> a1 = wz flush ->
  evt psegs (deflate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S D C LBz d out ds ai ao flush lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition deflateEnd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S : Z) (lo B : Z) (canary : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
    /\ a0 = wint Z_OK
    /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j]).

Definition deflateEnd_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S : Z) (b : bptr * bptr * bptr * bptr * bptr) (As Aw Ap Ah Ab : Z) (ds : DS za)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (blk5_blocks b As Aw Ap Ah Ab) LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2) ->
  zr_d R m S (blk5_blocks b As Aw Ap Ah Ab) ds ->
  d_end za ds = Z_OK ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_DEFLATEEND_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S ->
  implM psegs (deflate_end lops b) s
        (deflateEnd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DEFLATEEND) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition inflateInit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S ni ai no ao : Z) (p1 p2 : list byte) (lo B : Z) (canary : word) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ match r with
       | Some p => exists As,
           lx_post_env m m' s s' (iblocks None 0 p As) LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_OK
           /\ rw_cells psegs m' S (zs_pub ni ai 0 no ao 0 p1 p2)
           /\ zr_i R m' S (iblocks None 0 p As) (i_init za)
       | None =>
           lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
           /\ a0 = wint Z_MEM_ERROR
           /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j])
       end.

Definition inflateInit_stmt : Prop :=
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
  implM psegs (lib_malloc lops (z_isize za)) s
        (inflateInit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_INFLATEINIT_) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition i_wants (comprc : list Z) (is : IS za) (w : option bptr) : bool :=
  i_wants_window za comprc is && (match w with None => true | Some _ => false end).
Definition i_ok (comprc : list Z) (is : IS za) (w r : option bptr) : bool :=
  if i_wants comprc is w then (match r with Some _ => true | None => false end) else true.
Definition i_window (comprc : list Z) (is : IS za) (w r : option bptr) : option bptr :=
  if i_wants comprc is w then r else w.

Definition inflate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S C U : Z) (comprc uc : list Z) (is : IS za) (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z)
    (lo B : Z) (canary : word) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' p1' p2' Aw' ni',
    let '(is', ai', ao', bs, rc) := i_inflate za comprc is 1 1 (i_ok comprc is w r) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' (iblocks (i_window comprc is w r) Aw' sp_ As) LB sp tp B lo canary
                   [(S, S + ZS_SIZEOF); (U + i_total_out za is, U + i_total_out za is + zlength bs)] fc'
    /\ (w <> None -> Aw' = Aw)
    /\ a0 = wint rc
    (* [comment removed for export] *)
    /\ rw_cells psegs m' S (zs_pub ni' ai' (i_total_in za is') (U + i_total_out za is') ao' (i_total_out za is') p1' p2')
    /\ (rc = Z_OK -> ni' = C + i_total_in za is')
    /\ zr_i R m' S (iblocks (i_window comprc is w r) Aw' sp_ As) is'
    /\ u8arr psegs m' U (to_bytes (zstore uc (i_total_out za is) bs)).

Definition inflate_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S C U cl size : Z) (comprc uc : list Z) (is : IS za)
         (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (iblocks w Aw sp_ As) LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub (C + i_total_in za is) 1 (i_total_in za is) (U + i_total_out za is) 1 (i_total_out za is) p1 p2) ->
  zr_i R m S (iblocks w Aw sp_ As) is ->
  (exists b, In b LB /\ blk_addr b = C /\ blk_size b = cl) -> u8arr psegs m C (to_bytes comprc) -> zlength comprc = cl ->
  Forall (fun c => 0 <= c < 256) comprc ->
  (exists b, In b LB /\ blk_addr b = U /\ blk_size b = size) -> u8arr psegs m U (to_bytes uc) -> zlength uc = size ->
  0 <= i_total_in za is < cl -> 0 <= i_total_out za is < size ->
  (U + size <= C \/ C + cl <= U) ->                       (* [comment removed for export] *)
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_INFLATE_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S -> a1 = wz Z_NO_FLUSH ->
  implM psegs (if i_wants comprc is w then lib_malloc lops (z_wsize za) else ret lops None) s
        (inflate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S C U comprc uc is w Aw sp_ As lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_INFLATE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition inflateEnd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S : Z) (lo B : Z) (canary : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
    /\ a0 = wint Z_OK
    /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j]).

Definition inflateEnd_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S : Z) (is : IS za) (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (iblocks w Aw sp_ As) LB sp tp B lo errv canary ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2) ->
  zr_i R m S (iblocks w Aw sp_ As) is ->
  i_end za is = Z_OK ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_INFLATEEND_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S ->
  implM psegs (bind lops (lib_free lops w) (fun _ => lib_free lops (Some sp_))) s
        (inflateEnd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_INFLATEEND) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition zlib_ok : Prop :=
  compressBound_stmt /\ deflateInit_stmt /\ deflate_stmt /\ deflateEnd_stmt
  /\ inflateInit_stmt /\ inflate_stmt /\ inflateEnd_stmt.

End Api.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rfuzz_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word) (m : mem)
    (r : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' LK,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ lx_post_env m m' s s' LK LB sp tp B lo canary [LXW_ZH; LXW_STDERR] fc'
    /\ (length LK <= 2)%nat
    /\ r = 0 /\ a0 = wz 0
    /\ payload_ok m' LB D d.

Definition rfuzz_one_stmt : Prop :=
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
  frm0 fc ->
  a0 = wz D -> a1 = wz (zlength d) ->
  implM psegs (fuzz_one lops za d) s
        (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz LX_FUZZ) fc None m (seg_rom psegs)).
End WithCeiling0.
