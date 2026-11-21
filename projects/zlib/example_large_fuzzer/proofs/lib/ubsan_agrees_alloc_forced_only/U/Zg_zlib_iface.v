(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocU Require Import RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Zg_zlib_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Layout Zlib_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState Inflate HarnessSmall ZApiInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
#[local] Transparent the_zapi.

(* [comment removed for export] *)
Notation zi_wantsG := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zg_zlib_iface.zi_wantsG.
Notation i_wantsG := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zg_zlib_iface.i_wantsG.
Notation i_okG := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zg_zlib_iface.i_okG.
Notation i_windowG := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zg_zlib_iface.i_windowG.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.

Section Api.
Variable R : zreps.

Definition inflate_postG (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S C U : Z) (comprc uc : list Z) (is : IS za) (ain no aout : Z)
    (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z) (lo B : Z) (canary : word) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' p1' p2' Aw' ni',
    let '(is', ai', ao', bs, rc) := i_inflate za comprc is ain aout (i_okG comprc is ain aout w r) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ lx_post_env m m' s s' (iblocks (i_windowG comprc is ain aout w r) Aw' sp_ As) LB sp tp B lo canary
                   [(S, S + ZS_SIZEOF); (U + no, U + no + aout)] fc'
    /\ (w <> None -> Aw' = Aw)
    /\ a0 = wint rc
    (* [comment removed for export] *)
    /\ rw_cells usegs m' S (zs_pub ni' ai' (i_total_in za is') (U + no + zlength bs) ao' (i_total_out za is') p1' p2')
    /\ (rc = Z_OK -> ni' = C + i_total_in za is')
    /\ zr_i R m' S (iblocks (i_windowG comprc is ain aout w r) Aw' sp_ As) is'
    /\ u8arr usegs m' U (to_bytes (zstore uc no bs)).

Definition inflate_stmtG : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S C U cl size : Z) (comprc uc : list Z) (is : IS za) (ain no aout : Z)
         (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (iblocks w Aw sp_ As) LB sp tp B lo errv canary ->
  rw_cells usegs m S (zs_pub (C + i_total_in za is) ain (i_total_in za is) (U + no) aout (i_total_out za is) p1 p2) ->
  zr_i R m S (iblocks w Aw sp_ As) is ->
  (exists b, In b LB /\ blk_addr b = C /\ blk_size b = cl) -> u8arr usegs m C (to_bytes comprc) -> zlength comprc = cl ->
  Forall (fun c => 0 <= c < 256) comprc ->
  (exists b, In b LB /\ blk_addr b = U /\ blk_size b = size) -> u8arr usegs m U (to_bytes uc) -> zlength uc = size ->
  0 <= i_total_in za is -> 0 <= ain -> i_total_in za is + ain <= cl -> ain < 2^31 ->
  0 <= no -> 0 <= aout -> no + aout <= size -> aout < 2^31 ->
  0 <= i_total_out za is -> i_total_out za is + aout < 2^63 ->
  (U + size <= C \/ C + cl <= U) ->                       (* [comment removed for export] *)
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_INFLATE_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S -> a1 = wz Z_NO_FLUSH ->
  implM usegs (if i_wantsG comprc is ain aout w then lib_malloc lops (z_wsize za) else ret lops None) s
        (inflate_postG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S C U comprc uc is ain no aout w Aw sp_ As lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_INFLATE) fc None m (seg_rom usegs)).
End Api.
End WithCeiling0.
