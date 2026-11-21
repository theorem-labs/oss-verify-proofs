(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Stdio Prog ZTarget Target ZApi ZHarness ZInst.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocU Require Import RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Monad.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd Z_kit Startup_glue.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Layout Drv_kit F_fwrite Zlib_iface Zh_kit Z_img.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dinit_kit Z_irep Z_ikit Z_iinit_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState RefInflateSafeTY RefInflateInit1 RefInflateInit_run ZApiInst ZTaintI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition Z_INFLATERESET : Z := 0x1ef84.
Definition ireset14_pre (S : Z) : list cell :=
  [C8 (wz S); C4 (wz 16180); C4 (wz 0); C4 (wz 5); C4 (wz 5); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Definition ireset14_post (S As : Z) : list cell :=
  [C8 (wz S); C8 (wz 16180); C4 (wz 5); C4 (wz 5); C8 (wz (-4294967296)); C4 (wz 32768); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (As + 1384)); C8 (wz (As + 1384));
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (As + 1384))].
Definition ireset14_post_st (S As lo : Z) (ni ai no ao : Z) (p1 p2 jdt jrs : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (S, S + 112); (As, As + 168); (As + 7160, As + 7168)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' S (zs_pub ni ai 0 no ao 0 p1 p2 ++ [C8 (wz 0); C8 (wz As); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); C4 (wz 0); CB 4 jdt; C8 (wz 1); CB 8 jrs])
    /\ rw_cells usegs m' As (ireset14_post S As)
    /\ rw_cells usegs m' (As + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)].
Local Ltac wk X := repeat (tryif at_pc X then fail else zs).

Lemma ireset14_spec : forall (S As lo : Z) (ni ai ti no ao to : Z) (p1 p2 jdt0 jdt jad jrs : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x5dfe0 <= lo ->
  rw_cells usegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 (wz 0); C8 (wz As); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); CB 4 jdt0; CB 4 jdt; CB 8 jad; CB 8 jrs]) ->
  rw_cells usegs m As (ireset14_pre S) ->
  rw_cells usegs m (As + 7160) [C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  bv_unsigned sp <= S -> S + 112 < 2^63 -> 0 < As -> As + 7176 <= lo ->
  mem_inv usegs m ->
  S mod 8 = 0 -> As mod 16 = 0 ->
  evt usegs (ireset14_post_st S As lo ni ai no ao p1 p2 jdt jrs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_INFLATERESET) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STK LO1 LO2 ZS GA GT SPS S63 As0 As1 MI ALS ALA.
  pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112); (As, As + 168); (As + 7160, As + 7168)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold zs_pub in ZS. cbn [app] in ZS. unfold ireset14_pre in GA. unfold Z_ZCALLOC, Z_ZCFREE in ZS.
  unfold Z_INFLATERESET. carve_frame 32%nat STK.
  wk 0x1efa0. zs. br_false.
  wk 0x1efa8. zs. try al8 S. br_false.
  wk 0x1efb0. zs. br_false.
  wk 0x1efb8. zs. br_false.
  wk 0x1efc0. zs. br_false.
  wk 0x1efc8. zs. try al8 As. br_false.
  wk 0x1efd0. zs. br_true.
  wk 0x1f000. zs. br_false.
  wk 0x1f00c. zs. br_true.
  wk 0x1f044. zs. br_false.
  wk 0x1f04c. zs. br_false.
  wk 0x1f054. zs. br_false.
  wk 0x1f05c. zs. try al8 As. br_false.
  wk 0x1f064. zs. br_false.
  wk 0x1f074. zs. br_false.
  wk 0x1f09c. zs. br_false.
  wk 0x1f0d8.
  apply (rw_cells_merge usegs _ As [C8 (wz S)] [C4 (wz 16180); C4 (wz 0)]) in GA. cbn [cells_size csize cells_bytes cbytes app Nat.add] in GA.
  wk 0x1f0dc.
  wk 0x1f104.
  release_frame FR STK (bv_unsigned sp).
  zs.
  apply evt_done. unfold ireset14_post_st. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
  split; [unfold zs_pub, Z_ZCALLOC, Z_ZCFREE; cbn [app]; exact ZS|]. split; [exact GA| exact GT].
Qed.
#[local] Transparent the_zapi.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition PC_II_RET : Z := 0x1f178.
Definition ii_at_malloc (S lo : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (jstate : word) (jrest : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' x8v,
    ms' = MS (mkR (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8v (wz 7176) (wz 7176) a1 a2 a3 a4 a5 a6 a7
                  (wz S) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x23b00) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk usegs m' lo (bv_unsigned sp + -32)
    /\ rw_cells usegs m' S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 (wz 0); C8 jstate; C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); CB 24 jrest])
    /\ munch [(lo, bv_unsigned sp); (S, S + 112)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.
Lemma iinit_to_malloc : forall (S lo : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (jmsg jstate : word) (jrest : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo ->
  rw_cells usegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jrest]) ->
  bv_unsigned sp <= S -> S + 112 < 2^63 ->
  mem_inv usegs m ->
  S mod 8 = 0 ->
  evt usegs (ii_at_malloc S lo ni ai ti no ao to p1 p2 jstate jrest ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) (wz A_ZVERSION) (wz ZS_SIZEOF) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_INFLATEINIT_) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STK LO1 LO2 ZS SPS S63 MI ALS.
  pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold zs_pub in ZS. cbn [app] in ZS.
  unfold Z_INFLATEINIT_, A_ZVERSION, ZS_SIZEOF. carve_frame 32%nat STK.
  do 5 zs.
  do 2 zs. br_false. do 2 zs. br_false. do 3 zs. br_false. zs. br_false.
  zs. al8 S. gF.
  do 3 zs. br_true.
  do 6 zs. br_false. do 4 zs.
  do 7 zs.
  do 4 zs.
  apply evt_done. unfold ii_at_malloc. do 16 eexists. split; [reflexivity|].
  split; [exact FR|]. split; [exact STK|]. split; [unfold zs_pub, Z_ZCALLOC, Z_ZCFREE; cbn [app]; exact ZS|].
  split; [exact MU|]. split; [exact WM| eassumption].
Qed.
Lemma iinit_null : forall (lo : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1 x8v x9v x18 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells usegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp < 2^63 ->
  mem_inv usegs m ->
  evt usegs (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (-4)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
    (MS (mkR (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8v x9v (wz 0) a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_II_RET) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 SP63 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold PC_II_RET. zs. br_true. do 3 zs. do 5 zs.
  release_frame FR STK (bv_unsigned sp).
  zs.
  apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact STK].
Qed.
Definition hz_tail : list cell :=
  [C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Definition ii_block_post14 (S A lo : Z) (ni ai no ao : Z) (p1 p2 jrest : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (S, S + 112); (A, A + 7176)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' S (zs_pub ni ai 0 no ao 0 p1 p2 ++ [C8 (wz 0); C8 (wz A); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
                                                           C4 (wz 0); CB 4 (firstn 4 (skipn 4 jrest)); C8 (wz 1);
                                                           CB 8 (firstn 8 (skipn 8 (skipn 4 (skipn 4 jrest))))])
    /\ rw_cells usegs m' A (ireset14_post S A)
    /\ rw_cells usegs m' (A + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)]
    /\ rw_cells usegs m' (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))]
    /\ rw_cells usegs m' (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))]
    /\ rw_cells usegs m' (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))].
Lemma iinit_block14 : forall (S A lo : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (jstate : word) (jrest junk : list byte)
    (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1 x8v : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells usegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 128 -> 0x5dfe0 <= lo ->
  rw_cells usegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 (wz 0); C8 jstate; C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); CB 24 jrest]) ->
  rw_cells usegs m A [CB (Z.to_nat 7176) junk] ->
  bv_unsigned sp <= S -> S + 112 < 2^63 -> 0 < A -> A + 7176 <= lo ->
  mem_inv usegs m ->
  S mod 8 = 0 -> A mod 16 = 0 ->
  evt usegs (ii_block_post14 S A lo ni ai no ao p1 p2 jrest ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8v (wz 7176) (wz A) a1 a2 a3 a4 a5 a6 a7 (wz S) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_II_RET) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 ZS WJ SPS S63 A0 A1 MI ALS ALA.
  pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112); (A, A + 7176)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold zs_pub in ZS. cbn [app] in ZS. unfold Z_ZCALLOC, Z_ZCFREE in ZS.
  apply (rw_cells_split_CB usegs m S [C8 (wz ni); C4 (wz ai); CB 4 p1; C8 (wz ti); C8 (wz no); C4 (wz ao); CB 4 p2; C8 (wz to); C8 (wz 0); C8 jstate; C8 (wz 109952); C8 (wz 109968); C8 (wz 0)]
           24 jrest [] [4; 4; 8; 8]%nat) in ZS; [|reflexivity]. cbn [app mk_CB_cells] in ZS.
  assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  unfold PC_II_RET. zs. br_false.
  do 4 zs.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U.F_memset.memset_callZ with (D := A) (C := 0) (N := 7176); [exact WJ| eassumption| lia| lia| lia| lia] | post_call segs mm] end.
  change (0 mod 256) with 0 in POST.
  lazymatch type of POST with rw_cells _ ?mm _ _ => rename mm into mz end.
  assert (POST' : rw_cells usegs mz A [CB (length (repeat (Z_to_bv 8 0) (Z.to_nat 7176))) (repeat (Z_to_bv 8 0) (Z.to_nat 7176))])
    by (rewrite repeat_length; exact POST).
  pose proof (cb_subZ mz A _ 0 8 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as C8l.
  pose proof (cb_subZ mz A _ 8 160 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as HZ.
  pose proof (cb_subZ mz A _ 168 640 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZL0.
  pose proof (cb_subZ mz A _ 808 576 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZW0.
  pose proof (cb_subZ mz A _ 1384 5776 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZC0.
  pose proof (cb_subZ mz A _ 7160 16 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZT.
  clear POST POST'.
  rewrite Z.add_0_r in C8l. change (Z.to_nat 8) with 8%nat in C8l.
  assert (HZ8 : rw_cells usegs mz (A + 8) hz_tail).
  { eapply rw_cells_recast; [exact HZ| unfold hz_tail; cbn [cells_wf cell_wf]; repeat split| vm_compute; reflexivity]. }
  assert (ZL : rw_cells usegs mz (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))]).
  { eapply rw_cells_recast; [exact ZL0| cbn [cells_wf cell_wf]; rewrite repeat_length; repeat split| vm_compute; reflexivity]. }
  assert (ZW : rw_cells usegs mz (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))]).
  { eapply rw_cells_recast; [exact ZW0| cbn [cells_wf cell_wf]; rewrite repeat_length; repeat split| vm_compute; reflexivity]. }
  assert (ZC : rw_cells usegs mz (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))]).
  { eapply rw_cells_recast; [exact ZC0| cbn [cells_wf cell_wf]; rewrite repeat_length; repeat split| vm_compute; reflexivity]. }
  assert (GT : rw_cells usegs mz (A + 7160) [C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
  { eapply rw_cells_recast; [exact ZT| cbn [cells_wf cell_wf]; repeat split| vm_compute; reflexivity]. }
  clear HZ ZL0 ZW0 ZC0 ZT.
  unfold hz_tail in HZ8.
  zs. zs. al8 A. gF.
  do 6 zs. zs. br_false.
  do 8 zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (GA : rw_cells usegs mm A (ireset14_pre S)) end.
  { unfold ireset14_pre.
    change [C8 (wz S); C4 (wz 16180); C4 (wz 0); C4 (wz 5); C4 (wz 5); C8 (wz 0); C4 (wz 0); C4 (wz 0);
            C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
            C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
            C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)]
      with ([C8 (wz S)] ++ [C4 (wz 16180); C4 (wz 0); C4 (wz 5); C4 (wz 5); C8 (wz 0); C4 (wz 0); C4 (wz 0);
            C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15); C8 (wz 0); C4 (wz 0); C4 (wz 0);
            C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
            C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)]).
    apply rw_cells_app. split; [exact C8l|]. cbn [cells_size csize]. replace (A + Z.of_nat (8 + 0)) with (A + 8) by lia.
    eapply rw_cells_recast; [exact HZ8| cbn [cells_wf cell_wf]; repeat split|
      vm_compute; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity]. }
  clear C8l HZ8.
  do 2 zs.
  eapply evt_cut.
  { eapply (ireset14_spec S A lo ni ai ti no ao to p1 p2 (firstn 4 jrest) (firstn 4 (skipn 4 jrest))
              (firstn 8 (skipn 4 (skipn 4 jrest))) (firstn 8 (skipn 8 (skipn 4 (skipn 4 jrest)))));
      [rewrite E32; exact STK| rewrite E32; lia| exact LO2| unfold zs_pub, Z_ZCALLOC, Z_ZCFREE; cbn [app]; exact ZS| exact GA| exact GT
      | rewrite E32; lia| exact S63| exact A0| exact A1| eassumption| exact ALS| exact ALA]. }
  intros ms' PO. unfold ireset14_post_st in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STK' & ZS' & GA' & GT').
  rewrite E32 in *. clear ZS GA GT STK.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc end. clear MUc WMc.
  replace (ret_pc (wz 127452)) with (wz 127452) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  zs. br_true. do 2 zs. do 5 zs.
  release_frame FR STK' (bv_unsigned sp).
  zs.
  apply evt_done. unfold ii_block_post14. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK'|].
  split; [exact ZS'|]. split; [exact GA'|]. split; [exact GT'|]. split; [exact ZL|]. split; [exact ZW| exact ZC].
Qed.
Lemma le8_mode_last : le8 (wz 16180) = le4 (wz 16180) ++ le4 (wz 0).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_hd_flags : le8 (wz (-4294967296)) = le4 (wz 0) ++ le4 (wz (-1)).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_flags_dmax : le8 (wz 140741783322623) = le4 (wz (-1)) ++ le4 (wz 32768).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_00 : le8 (wz 0) = le4 (wz 0) ++ le4 (wz 0).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_sane_back : le8 (wz 18446744069414584321) = le4 (wz 1) ++ le4 (wz (-1)).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Ltac ired14 := cbn [w_s w_c w_r is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk is_reqwrap is_reqbits ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk iset_reqwrap iset_reqbits icset_input icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out icset_adler icset_data_type icset_msg irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret wset_s wset_c wset_r].
Ltac iinit_red :=
  unfold iinit_of, ireset_s, s_pre, is_of_oracle, lay_ref;
  cbn [lay_mode lay_last lay_wrap lay_havedict lay_flags lay_dmax lay_check lay_total lay_head lay_wbits lay_wsize lay_whave lay_wnext lay_window lay_hold lay_bits
       lay_length lay_offset lay_extra lay_lencode lay_distcode lay_lenbits lay_distbits lay_ncode lay_nlen lay_ndist lay_have lay_next lay_lens lay_work lay_codes
       lay_sane lay_back lay_was il_S il_As il_Aw il_NI il_NO win_addr cp_addr];
  ired14; change (ir2_wrap MAX_WBITS) with 5; change (ir2_wb MAX_WBITS) with 15.
Section Zeros.
Variable junk : list byte.
Hypothesis HZ : forall k, 8 <= Z.of_nat k < 7176 -> nth k junk (Z_to_bv 8 0) = Z_to_bv 8 0.

Lemma orc_zero : forall k, 8 <= k < 7176 -> orc junk k = 0.
Proof. intros k Hk. unfold orc. rewrite HZ by lia. reflexivity. Qed.
Lemma izero16 : forall b i, 8 <= b + 2 * i -> b + 2 * i + 2 <= 7176 -> init_u16 (orc junk) b i = 0.
Proof.
  intros b i H1 H2. rewrite (init_u16_ole (orc junk) (orc_range junk)). apply ole_zero.
  intros k Hk. apply orc_zero. cbn in Hk. lia.
Qed.
Lemma izero32 : forall b i, 8 <= b + 4 * i -> b + 4 * i + 4 <= 7176 -> init_u32 (orc junk) b i = 0.
Proof.
  intros b i H1 H2. rewrite (init_u32_ole (orc junk) (orc_range junk)). apply ole_zero.
  intros k Hk. apply orc_zero. cbn in Hk. lia.
Qed.
Lemma izero64 : forall b i, 8 <= b + 8 * i -> b + 8 * i + 8 <= 7176 -> init_u64 (orc junk) b i = 0.
Proof.
  intros b i H1 H2. rewrite (init_u64_ole (orc junk) (orc_range junk)). apply ole_zero.
  intros k Hk. apply orc_zero. cbn in Hk. lia.
Qed.
End Zeros.

Local Transparent zseq.
Lemma u32s_zero_seq : forall (f : Z -> Z) n s, (forall i, Z.of_nat s <= i < Z.of_nat (s + n) -> f i = 0) ->
  u32s (map (fun i => wz (f i)) (map Z.of_nat (seq s n))) = repeat (Z_to_bv 8 0) (4 * n).
Proof.
  intros f n. induction n as [|n IH]; intros s Hf; [reflexivity|].
  cbn [seq map u32s]. rewrite Hf by lia. rewrite (IH (S s)) by (intros i Hi; apply Hf; lia).
  replace (4 * S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.
Lemma av32_zero : forall (a : arr) n, 0 <= n -> (forall i, 0 <= i < n -> arr_get a i = 0) ->
  u32s (av32 a n) = repeat (Z_to_bv 8 0) (Z.to_nat (4 * n)).
Proof.
  intros a n Hn Hf. unfold av32, zseq. rewrite (u32s_zero_seq (arr_get a) (Z.to_nat n) 0) by (intros i Hi; apply Hf; lia).
  f_equal. lia.
Qed.
Lemma iinit_IST14 : forall m S A NI NO (junk : list byte),
  (forall k, 8 <= Z.of_nat k < 7176 -> nth k junk (Z_to_bv 8 0) = Z_to_bv 8 0) ->
  rw_cells usegs m A (ireset14_post S A) ->
  rw_cells usegs m (A + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)] ->
  rw_cells usegs m (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))] ->
  rw_cells usegs m (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))] ->
  rw_cells usegs m (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))] ->
  blk_ok A 7176 ->
  IST m (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof.
  intros m S A NI NO junk HZ GA GT ZL ZW ZC BOK.
  unfold ireset14_post in GA.
  apply (cells_split8_0 m A [C8 (wz S); C8 (wz 16180); C4 (wz 5); C4 (wz 5); C8 (wz (-4294967296)); C4 (wz 32768); C4 (wz 0);
                            C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15)]) in GA. cbn [app] in GA.
  constructor.
  - unfold isA. eapply rw_cells_recast; [exact GA| |].
    + unfold isA_cells. cbn [cells_wf cell_wf]. repeat split.
    + unfold isA_cells. iinit_red. cbn [win_addr cp_addr il_As il_Aw].
      rewrite ?(izero32 junk HZ), ?(izero64 junk HZ) by lia.
      cbn [cells_bytes cbytes]. unfold HEAD. rewrite le8_mode_last, le8_hd_flags.
      rewrite <- !app_assoc. rewrite !Z.mul_0_r, !Z.add_0_r. reflexivity.
  - exists (le4 (wz 0)). eapply rw_cells_recast; [exact GT| |].
    + unfold isT_cells. cbn [cells_wf cell_wf]. repeat split; try apply length_le4.
    + unfold isT_cells. iinit_red. rewrite ?(izero32 junk HZ) by lia. cbn [cells_bytes cbytes]. rewrite le8_sane_back.
      rewrite <- !app_assoc. reflexivity.
  - unfold ilens, u16arr. iinit_red. apply u8arr_of_rw_cells in ZL.
    rewrite (av16_zero _ 320) by (try lia; intros i Hi; unfold iarr_u16_of; rewrite arr_get_init; first [reflexivity | apply (izero16 junk HZ); lia]).
    exact ZL.
  - unfold iwork, u16arr. iinit_red. apply u8arr_of_rw_cells in ZW.
    rewrite (av16_zero _ 288) by (try lia; intros i Hi; unfold iarr_u16_of; rewrite arr_get_init; first [reflexivity | apply (izero16 junk HZ); lia]).
    exact ZW.
  - unfold icodes, u32arr. iinit_red. apply u8arr_of_rw_cells in ZC. destruct ZC as [ZB ZW']. split.
    + rewrite (av32_zero _ 1444) by (try lia; intros i Hi; unfold iarr_u32_of; rewrite arr_get_init; first [reflexivity | apply (izero32 junk HZ); lia]).
      exact ZB.
    + replace (4 * Z.of_nat (length (av32 (iarr_u32_of (orc junk) 1368 1444) 1444)))
        with (Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat 5776)))) by (rewrite av32_length, repeat_length; lia).
      exact ZW'.
  - unfold iwin. iinit_red. exact I.
  - unfold iarrs. iinit_red. unfold iarr_u16_of, iarr_u32_of. rewrite !arr_len_init. repeat split; try reflexivity. intros NE. exfalso. apply NE. reflexivity.
  - unfold ilay_ok. iinit_red. split; [exact BOK|]. intros NE. exfalso. apply NE. reflexivity.
Qed.
Lemma zi_init_z : zs_msg (iz_z zi_init) = MSG_NULL /\ zs_adler (iz_z zi_init) = 1 /\ zs_total_in (iz_z zi_init) = 0 /\ zs_total_out (iz_z zi_init) = 0.
Proof.
  unfold zi_init, iz0, iinit0. cbn [iz_z]. rewrite iinit_run_of. cbn [zr_strm zret0]. unfold ireset_z, z_pre.
  change (is_wrap (s_pre HarnessSmall.g0 5%N MAX_WBITS)) with 5. cbn. repeat split; reflexivity.
Qed.
Section INIT.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Variable R : zreps.
  Hypothesis ER : zr_i R = zr_i_def.
  Theorem inflateInit_ok : inflateInit_stmt R.
  Proof.
    unfold inflateInit_stmt. intros until canary. intros ENV ZS SIF LOSP SP16 FRM0 -> -> ->.
    change (lib_malloc lops (z_isize the_zapi)) with (raw_malloc 7176).
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (HP & LXS & ZLS & SEW & SSP & AUX & SPB & B63 & STK & LOC & LOG & ERR & TP & MI).
    destruct SIF as (SF1 & SF2 & SF3). unfold ZS_SIZEOF in SF2. unfold Z_INFLATEINIT_STACK, RMALLOC_STACK in LOSP. unfold GLOBALS_TOP in LOG.
    pose proof alloc_ceiling_range as CR.
    eapply implM_evt; [exact (iinit_to_malloc S lo ni ai ti no ao to p1 p2 jmsg jstate jrest ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                               STK ltac:(lia) ltac:(lia) ZS SF1 ltac:(lia) MI SF3)|].
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & x8v & -> & FR & STK1 & ZS1 & MU1 & WM1 & MI1).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (ENV1 : lx_env m1 s [] LB (wz (bv_unsigned sp + -32)) tp B lo errv canary).
    { eapply (lx_env_munch [(lo, bv_unsigned sp); (S, S + 112)] m m1 s [] LB sp (wz (bv_unsigned sp + -32)) tp B lo errv canary HFRAME ENV MU1 WM1 MI1);
        [rewrite E32; exact STK1| rewrite E32; lia| |].
      - constructor; [|constructor; [|constructor]]; unfold rclient_write_ok; cbn [fst snd]; left; lia.
      - intros a Ha. cbn [outside]. repeat split; lia. }
    pose proof ENV1 as E1. unfold lx_env in E1. destruct E1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & _ & ST1 & LOC1 & _ & ERR1 & TP1 & _).
    eapply implM_post_evt''.
    { eapply (MALLOC (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0' t1' t2' _ _ (wz 7176) a1' a2' a3' a4' a5' a6' a7' _ _ _ _ _ _ _ _ _ _ t3' t4' t5' t6' F fc m1 s LB 7176 lo B errv);
        [exact HP1| exact AUX1| exact SPB1| exact ST1| exact LOC1| rewrite E32; unfold RMALLOC_STACK; lia| exact ERR1| exact MI1| exact TP1| reflexivity| lia]. }
    intros r st' ms2 PO.
    destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & errv2 & -> & MI2 & STK2 & ERR2 & AUX2 & HPR & EFA & ESO & HR).
    rewrite E32 in STK2, HPR.
    replace (ret_pc (wz PC_II_RET)) with (wz PC_II_RET) by (symmetry; apply ret_pc_even; [unfold PC_II_RET; lia| reflexivity]).
    assert (HPRc : rheap_pres LB (bv_unsigned (wz (bv_unsigned sp + -32))) m1 m2) by (rewrite E32; exact HPR).
    assert (AGC : forall A0 n, bv_unsigned sp + -32 <= A0 -> 0 <= n -> A0 + n <= 2^64 -> Z_dview.agree_on A0 (A0 + n) m1 m2).
    { intros A0 n H1 H2 H3 a Ha. apply HPR; [lia|]. left. lia. }
    apply (Z_dview.rw_cells_agree m1 m2) in FR; [|apply AGC; cbn [cells_size csize Nat.add]; lia].
    apply (Z_dview.rw_cells_agree m1 m2) in ZS1; [|apply AGC; unfold zs_pub; cbn [app cells_size csize Nat.add]; lia].
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= lo /\ 0 < blk_addr b).
    { intros b Hb. pose proof (HBR _ _ _ b HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    assert (PRES1 : lx_pres LB (bv_unsigned sp) [(S, S + ZS_SIZEOF)] m m1).
    { apply (lx_pres_of_munch LB (bv_unsigned sp) _ [(lo, bv_unsigned sp); (S, S + 112)] m m1 MU1 WM1).
      intros a (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX. cbn [outside].
      destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb)|]; repeat split; lia. }
    assert (PRES2 : lx_pres LB (bv_unsigned sp) [(S, S + ZS_SIZEOF)] m1 m2).
    { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR| lia| auto]. }
    destruct r as [p|].
    -
      destruct HR as (A & junk & -> & RBR & HP2 & WJ & _).
      destruct RBR as (RB1 & RB2 & RB3 & RB4 & RB5).
      assert (BOK : blk_ok A 7176) by (unfold blk_ok; repeat split; try assumption; lia).
      assert (A1 : A + 7176 <= lo) by lia.
      assert (SEPB : forall b, In b LB -> blk_addr b + blk_size b <= A \/ A + 7176 <= blk_addr b).
      { intros b Hb. pose proof (heap_sep st' [(p, A, 7176)] LB m2 (p, A, 7176) b HND HBD HP2 (or_introl eq_refl) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
      assert (ENV2 : lx_env m2 st' [(p, A, 7176)] LB (wz (bv_unsigned sp + -32)) tp B lo errv2 canary).
      { apply (lx_env_heap m1 m2 s st' [] [(p, A, 7176)] LB (wz (bv_unsigned sp + -32)) tp B lo errv errv2 canary ENV1 HPRc HP2 MI2); [rewrite E32; exact STK2| exact ERR2| exact AUX2]. }
      assert (LJ' : length junk = Z.to_nat 7176) by exact (proj1 (proj1 (proj1 WJ))).
      eapply evt_mono; [exact (iinit_block14 S A lo ni ai ti no ao to p1 p2 jstate jrest junk ra sp gp tp t0'' t1'' t2'' s0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                  t3'' t4'' t5'' t6'' s1 x8v F fc m2 FR STK2 ltac:(lia) ltac:(lia) ZS1 WJ SF1 ltac:(lia) RB1 A1 MI2 SF3 RB2)|].
      clear WJ.
      intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & STK' & ZS' & GA' & GT' & ZL & ZW & ZC).
      remember (sub junk (Z.to_nat 0) (Z.to_nat 8) ++ repeat (Z_to_bv 8 0) (Z.to_nat 7168)) as jkz eqn:Ejkz.
      assert (HZz : forall k, 8 <= Z.of_nat k < 7176 -> nth k jkz (Z_to_bv 8 0) = Z_to_bv 8 0).
      { intros k Hk. subst jkz. rewrite app_nth2.
        - apply nth_repeat.
        - rewrite sub_length; [lia| rewrite LJ'; lia]. }
      pose proof (iinit_IST14 m' S A 0 0 jkz HZz GA' GT' ZL ZW ZC BOK) as HIST.
      apply rw_cells_app in ZS'. destruct ZS' as [ZPUB ZPRIV]. unfold zs_pub in ZPRIV. cbn [cells_size csize Nat.add] in ZPRIV.
      unfold inflateInit_post. exists u0, u1, u2, (wz 0), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m'.
      split; [reflexivity|]. exists A. change (Zlib_iface.iblocks None 0 p A) with [(p, A, 7176)].
      split; [|split; [|split]].
      + unfold lx_post_env. split.
        { exists errv2. eapply (lx_env_munch _ m2 m' st' [(p, A, 7176)] LB (wz (bv_unsigned sp + -32)) sp tp B lo errv2 canary HFRAME ENV2 MU' WM' MI' STK'); [lia| |].
          - constructor; [|constructor; [|constructor; [|constructor]]]; unfold rclient_write_ok; cbn [fst snd].
            + left; lia.
            + left; lia.
            + right; right. exists (p, A, 7176). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
          - intros a Ha. cbn [outside]. repeat split; lia. }
        split; [exact FRM0|]. split; [|split; assumption].
        eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans; [exact PRES2|].
        apply (lx_pres_of_munch LB (bv_unsigned sp) _ _ m2 m' MU' WM').
        intros a (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX. cbn [outside].
        destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb); pose proof (SEPB _ Hb)|]; repeat split; lia.
      + unfold wint, Z_OK. reflexivity.
      + exact ZPUB.
      + rewrite ER. destruct zi_init_z as (EMSG & EADL & _ & _).
        exists (iinit_of (orc jkz)), (Z_irep.mkIL S A 0 0 0), None, p. cbn [il_S il_As il_Aw].
        split; [reflexivity|]. split; [reflexivity|]. split; [split; intros _; reflexivity|].
        split; [split; [|exact HIST]|].
        {
          pose proof (proj1 (proj1 ZPRIV)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & _ & _ & _ & _ & _ & L1 & _ & L2 & _).
          destruct (le8_of_bytes (firstn 8 (skipn 8 (skipn 4 (skipn 4 jrest))))) as (zrs & _ & Ers); [exact L2|].
          exists (wz 0), (firstn 4 (skipn 4 jrest)), (wz zrs). cbn [il_S].
          eapply rw_cells_recast; [exact ZPRIV| |].
          - unfold izs_priv_cells. cbn [cells_wf cell_wf]. repeat split. exact L1.
          - unfold izs_priv_cells. cbn [cells_bytes cbytes il_As]. rewrite EMSG, EADL. change (imsg_ptr MSG_NULL) with 0.
            rewrite Ers. reflexivity. }
        change (i_init the_zapi) with zi_init.
        split; [apply IREL_init|]. split.
        { unfold ATY. iinit_red. split; [apply ty16_init|]. split; [apply ty16_init| apply ty32_init]. }
        unfold PATIq. iinit_red. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [right; split; [reflexivity| left; reflexivity]|]. split; [unfold HEAD, FLAGS, HCRC; lia|]. split; [left; reflexivity|]. split; [left; reflexivity|].
        split; [intros i Hi; unfold arr_make in Hi; rewrite arr_len_init in Hi; lia|].
        unfold bk_ok, bkmax. iinit_red. cbn. lia.
    -
      destruct HR as (-> & HP2).
      assert (ENV2 : lx_env m2 st' [] LB (wz (bv_unsigned sp + -32)) tp B lo errv2 canary).
      { apply (lx_env_heap m1 m2 s st' [] [] LB (wz (bv_unsigned sp + -32)) tp B lo errv errv2 canary ENV1 HPRc HP2 MI2); [rewrite E32; exact STK2| exact ERR2| exact AUX2]. }
      eapply evt_mono; [exact (iinit_null lo ra sp gp tp t0'' t1'' t2'' s0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'' s1 x8v (wz 7176) (wz S) F fc m2
                                  FR STK2 ltac:(lia) ltac:(lia) ltac:(lia) MI2)|].
      intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & STK').
      unfold inflateInit_post. exists u0, u1, u2, (wz (-4)), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m'.
      split; [reflexivity|]. split; [|split].
      + unfold lx_post_env. split.
        { exists errv2. eapply (lx_env_munch [(lo, bv_unsigned sp)] m2 m' st' [] LB (wz (bv_unsigned sp + -32)) sp tp B lo errv2 canary HFRAME ENV2 MU' WM' MI' STK'); [lia| |].
          - constructor; [|constructor]. unfold rclient_write_ok; cbn [fst snd]; left; lia.
          - intros a Ha. cbn [outside]. repeat split; lia. }
        split; [exact FRM0|]. split; [|split; assumption].
        eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans; [exact PRES2|].
        apply (lx_pres_of_munch LB (bv_unsigned sp) _ [(lo, bv_unsigned sp)] m2 m' MU' WM').
        intros a (NX & HC). cbn [outside].
        destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb)|]; repeat split; lia.
      + unfold wint, Z_MEM_ERROR. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia. reflexivity.
      + apply (rw_cells_transport usegs [(lo, bv_unsigned sp)] m2 m') in ZS1; [| exact MU'| exact WM'| unfold zs_pub; cbn [app cells_size csize Nat.add disjoint_from]; split; [lia| exact I]].
        destruct (rw_cells_forget usegs m' _ _ ZS1) as (j & Hj). exists j. exact Hj.
  Qed.
End INIT.
End WithCeiling0.
