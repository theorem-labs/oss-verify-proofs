(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Zlib_iface Zh_kit Z_ikit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* zlib 1.4 (a worker): inflateReset2 is gone; this file now walks 1.4's inflateReset
   (a worker's Z_ireset14 template at the compress binary's addresses). The file name is kept. *)
(* 1.4 (a worker, zl14-small): inflateReset2 is gone. inflateInit_ zeroes the new state (memset(state + 8, 0, 7168)),
   stores strm, mode = HEAD, wrap = reqwrap = 5 and reqbits = wbits = 15, then calls the new inflateReset. With
   wbits = reqbits, inflateReset sets wrap := reqwrap, clears wsize / whave / wnext, then does inflateResetKeep's work.
   Every byte it does not store is 0, so the head's pre and post cells are concrete. *)
Definition Z_INFLATERESET : Z := 0x1cf70.

(* [the head (168 bytes) as inflateInit_ leaves it: strm, mode HEAD, last 0, wrap 5, reqwrap 5, reqbits 15, wbits 15,
    every other byte 0; one cell per access width of inflateReset] *)
Definition ireset14_pre (S : Z) : list cell :=
  [C8 (wz S); C4 (wz 16180); C4 (wz 0); C4 (wz 5); C4 (wz 5); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
(* [after inflateReset: mode + last as one word, havedict 0 + flags -1 as one word, dmax 32768, lencode = distcode =
    next = the codes array] *)
Definition ireset14_post (S As : Z) : list cell :=
  [C8 (wz S); C8 (wz 16180); C4 (wz 5); C4 (wz 5); C8 (wz (-4294967296)); C4 (wz 32768); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (As + 1384)); C8 (wz (As + 1384));
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (As + 1384))].

Definition ireset14_post_st (S As lo : Z) (ni ai no ao : Z) (p1 p2 jdt jrs : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (S, S + 112); (As, As + 168); (As + 7160, As + 7168)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' S (zs_pub ni ai 0 no ao 0 p1 p2 ++ [C8 (wz 0); C8 (wz As); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); C4 (wz 0); CB 4 jdt; C8 (wz 1); CB 8 jrs])
    /\ rw_cells psegs m' As (ireset14_post S As)
    /\ rw_cells psegs m' (As + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)].

Lemma ireset14_spec : forall (S As lo : Z) (ni ai ti no ao to : Z) (p1 p2 jdt0 jdt jad jrs : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x5c000 <= lo ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 (wz 0); C8 (wz As); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); CB 4 jdt0; CB 4 jdt; CB 8 jad; CB 8 jrs]) ->
  rw_cells psegs m As (ireset14_pre S) ->
  rw_cells psegs m (As + 7160) [C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  bv_unsigned sp <= S -> S + 112 < 2^63 -> 0 < As -> As + 7176 <= lo ->
  mem_inv psegs m ->
  evt psegs (ireset14_post_st S As lo ni ai no ao p1 p2 jdt jrs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_INFLATERESET) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros STK LO1 LO2 ZS GA GT SPS S63 As0 As1 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112); (As, As + 168); (As + 7160, As + 7168)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold zs_pub in ZS. cbn [app] in ZS. unfold ireset14_pre in GA. unfold Z_ZCALLOC, Z_ZCFREE in ZS.
  unfold Z_INFLATERESET. carve_frame 32%nat STK.
  do 8 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_true.
  do 6 zs. br_false. do 3 zs. br_true.
  do 4 zs.
  do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 4 zs. br_false.
  do 10 zs. br_false.
  do 3 zs.
  do 11 zs.
  apply (rw_cells_merge psegs _ As [C8 (wz S)] [C4 (wz 16180); C4 (wz 0)]) in GA. cbn [cells_size csize cells_bytes cbytes app Nat.add] in GA.
  zs.
  do 5 zs.
  do 5 zs.
  release_frame FR STK (bv_unsigned sp).
  zs.
  apply evt_done. unfold ireset14_post_st. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
  split; [unfold zs_pub, Z_ZCALLOC, Z_ZCFREE; cbn [app]; exact ZS|]. split; [exact GA| exact GT].
Qed.
