(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState Inftrees ItableModel RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_INFLATE_TABLE : Z := 0x1f200.
Definition Z_ITABLE_STACK : Z := 512.

Definition ity_code (ty : codetype) : Z := match ty with CODES => 0 | LENS => 1 | DISTS => 2 end.

Definition it_bits_get (dsel : bool) (s : inflate_state) : Z := if dsel then is_distbits s else is_lenbits s.
Definition it_bits_set (dsel : bool) (s : inflate_state) (v : Z) : inflate_state := if dsel then iset_distbits s v else iset_lenbits s v.

Definition it_result (ty : codetype) (dsel : bool) (lens_ofs codes : Z) (s : inflate_state) : Z * inflate_state :=
  let '(ret, tbl, next, bits, work) :=
    inflate_table ty (is_lens s) lens_ofs codes (is_codes s) (is_next s) (it_bits_get dsel s) (is_work s) in
  (ret, iset_work (it_bits_set dsel (iset_next (iset_codes s tbl) next) bits) work).

Definition inflate_table_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : ilay) (s : inflate_state) (ty : codetype) (dsel : bool) (lens_ofs codes lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (il_As L, il_As L + ZI_SIZE)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ a0 = wz (fst (it_result ty dsel lens_ofs codes s) mod 2^64)
    /\ IST m' L (snd (it_result ty dsel lens_ofs codes s)).

(* 1.4 (a worker's inflate_table template): the code-count bound each caller knows. 1.4's lext[29] differs from the
   model's, and 1.4 passes NULL base / extra for CODES, so the walk needs every symbol below 286 (LENS) and below 19
   (CODES). *)
Definition it_codes_ok (ty : codetype) (codes : Z) : Prop :=
  match ty with CODES => codes <= 19 | LENS => codes <= 286 | DISTS => True end.

Definition inflate_table_stmt : Prop :=
  forall (L : ilay) (s : inflate_state) (ty : codetype) (dsel : bool) (lens_ofs codes lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  IST m L s -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_ITABLE_STACK -> il_As L + ZI_SIZE <= lo ->
  (is_window_blk s <> None -> il_Aw L + ZI_WIN <= lo) ->
  0 <= lens_ofs -> 0 <= codes -> lens_ofs + codes <= 320 -> 0 <= is_next s <= 1444 -> 0 <= it_bits_get dsel s <= 15 ->
  it_safe ty (is_lens s) lens_ofs codes (is_codes s) (is_next s) (it_bits_get dsel s) (is_work s) = true ->

  ATY s ->
  (forall i, 0 <= i < codes -> arr_get (is_lens s) (lens_ofs + i) <= 15) ->
  it_codes_ok ty codes ->
  a0 = wz (ity_code ty) -> a1 = wz (il_As L + 168 + 2 * lens_ofs) -> a2 = wz codes -> a3 = wz (il_As L + 160) ->
  a4 = wz (il_As L + (if dsel then 140 else 136)) -> a5 = wz (il_As L + 808) ->
  evt psegs (inflate_table_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s ty dsel lens_ofs codes lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_INFLATE_TABLE) fc None m (seg_rom psegs)).
