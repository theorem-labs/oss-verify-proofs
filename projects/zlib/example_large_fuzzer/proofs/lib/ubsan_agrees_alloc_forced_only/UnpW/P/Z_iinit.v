(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Stdio. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTarget. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Target. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZApi ZHarness. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInst.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocP Require Import RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Monad.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Layout Drv_kit F_fwrite Z_kit Zlib_iface Zh_kit Z_img Startup_glue.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_dinit_kit Z_irep Z_ikit Z_iinit_kit Z_ireset2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require F_memset.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateInit1 RefInflateInit_run. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZApiInst. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import ZTaintI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
#[local] Transparent the_zapi.

(* zlib 1.4 (a worker): a worker's 1.4 inflateInit_ walk (example_small template), ported
   at the compress binary's addresses (same code at +0x2ec; malloc / zcalloc / zcfree unchanged). *)
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition PC_II_RET : Z := 0x1d154.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ii_at_malloc (S lo : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (jstate : word) (jrest : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (wz S) (wz 7176) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x20b2c) fc None m' (seg_rom psegs)
    /\ rw_cells psegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk psegs m' lo (bv_unsigned sp + -32)
    /\ rw_cells psegs m' S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 (wz 0); C8 jstate; C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); CB 24 jrest])
    /\ munch [(lo, bv_unsigned sp); (S, S + 112)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Lemma iinit_to_malloc : forall (S lo : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (jmsg jstate : word) (jrest : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x5c000 <= lo ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jrest]) ->
  bv_unsigned sp <= S -> S + 112 < 2^63 ->
  mem_inv psegs m ->
  evt psegs (ii_at_malloc S lo ni ai ti no ao to p1 p2 jstate jrest ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) (wz A_ZVERSION) (wz ZS_SIZEOF) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_INFLATEINIT_) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros STK LO1 LO2 ZS SPS S63 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold zs_pub in ZS. cbn [app] in ZS.
  unfold Z_INFLATEINIT_, A_ZVERSION, ZS_SIZEOF. carve_frame 32%nat STK.
  do 2 zs. br_false. do 2 zs. br_false. do 3 zs. br_false. zs. br_false.
  do 3 zs. br_true. (* 1.4: the frame is carved after the zalloc / zfree checks *)
  do 6 zs. br_false. do 4 zs.
  do 5 zs.
  do 6 zs.
  do 4 zs.
  apply evt_done. unfold ii_at_malloc. do 15 eexists. split; [reflexivity|].
  split; [exact FR|]. split; [exact STK|]. split; [unfold zs_pub, Z_ZCALLOC, Z_ZCFREE; cbn [app]; exact ZS|].
  split; [exact MU|]. split; [exact WM| eassumption].
Qed.

(* [comment removed for export] *)
Lemma iinit_null : forall (lo : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1 x9 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells psegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk psegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 64 -> 0x5c000 <= lo -> bv_unsigned sp < 2^63 ->
  mem_inv psegs m ->
  evt psegs (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (-4)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom psegs)
               /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp))
    (MS (mkR (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_II_RET) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 SP63 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold PC_II_RET. zs. br_true. do 2 zs. do 5 zs.
  release_frame FR STK (bv_unsigned sp).
  do 2 zs.
  apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact STK].
Qed.

(* 1.4: after the zalloc, inflateInit_ zeroes the state past its first 8 bytes (memset(state + 8, 0, 7168)), stores
   strm, mode = HEAD, strm->state and the packed words wrap | reqwrap = 5 | 5 and reqbits | wbits = 15 | 15, and calls
   inflateReset. hz_tail = the head's bytes 8..168 right after the memset, one cell per access width of those stores
   and of inflateReset. *)
Definition hz_tail : list cell :=
  [C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].

Definition ii_block_post14 (S A lo : Z) (ni ai no ao : Z) (p1 p2 jrest : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (S, S + 112); (A, A + 7176)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' S (zs_pub ni ai 0 no ao 0 p1 p2 ++ [C8 (wz 0); C8 (wz A); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
                                                           C4 (wz 0); CB 4 (firstn 4 (skipn 4 jrest)); C8 (wz 1);
                                                           CB 8 (firstn 8 (skipn 8 (skipn 4 (skipn 4 jrest))))])
    /\ rw_cells psegs m' A (ireset14_post S A)
    /\ rw_cells psegs m' (A + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)]
    /\ rw_cells psegs m' (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))]
    /\ rw_cells psegs m' (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))]
    /\ rw_cells psegs m' (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))].

Lemma iinit_block14 : forall (S A lo : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (jstate : word) (jrest junk : list byte)
    (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells psegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk psegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 128 -> 0x5c000 <= lo ->
  rw_cells psegs m S (zs_pub ni ai ti no ao to p1 p2 ++ [C8 (wz 0); C8 jstate; C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); CB 24 jrest]) ->
  rw_cells psegs m A [CB (Z.to_nat 7176) junk] ->
  bv_unsigned sp <= S -> S + 112 < 2^63 -> 0 < A -> A + 7176 <= lo ->
  mem_inv psegs m ->
  evt psegs (ii_block_post14 S A lo ni ai no ao p1 p2 jrest ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR (wz PC_II_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (wz S) (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_II_RET) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 ZS WJ SPS S63 A0 A1 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112); (A, A + 7176)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold zs_pub in ZS. cbn [app] in ZS. unfold Z_ZCALLOC, Z_ZCFREE in ZS.
  (* [the strm's last 24 bytes: data_type (inflateReset stores it), its pad, adler, reserved] *)
  apply (rw_cells_split_CB psegs m S [C8 (wz ni); C4 (wz ai); CB 4 p1; C8 (wz ti); C8 (wz no); C4 (wz ao); CB 4 p2; C8 (wz to); C8 (wz 0); C8 jstate; C8 (wz 107260); C8 (wz 107276); C8 (wz 0)]
           24 jrest [] [4; 4; 8; 8]%nat) in ZS; [|reflexivity]. cbn [app mk_CB_cells] in ZS.
  (* [the fresh block: its first 8 bytes (strm goes there) and the 7168 the memset clears] *)
  assert (LJ : length junk = Z.to_nat 7176) by exact (proj1 (proj1 (proj1 WJ))).
  assert (WJ' : rw_cells psegs m A [CB (length junk) junk]) by (rewrite LJ; exact WJ).
  pose proof (cb_subZ m A junk 8 7168 WJ' ltac:(lia) ltac:(lia) ltac:(rewrite LJ; lia)) as C8r.
  pose proof (cb_subZ m A junk 0 8 WJ' ltac:(lia) ltac:(lia) ltac:(rewrite LJ; lia)) as C8l. rewrite Z.add_0_r in C8l. change (Z.to_nat 8) with 8%nat in C8l.
  clear WJ WJ'.
  assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  unfold PC_II_RET. zs. br_false.
  do 6 zs.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.F_memset.memset_callZ with (D := A + 8) (C := 0) (N := 7168); [exact C8r| eassumption| lia| lia| lia| lia] | post_call segs mm] end.
  change (0 mod 256) with 0 in POST.
  lazymatch type of POST with rw_cells _ ?mm _ _ => rename mm into mz end.
  (* [the cleared bytes: head 8..168, lens, work, codes, tail] *)
  assert (POST' : rw_cells psegs mz (A + 8) [CB (length (repeat (Z_to_bv 8 0) (Z.to_nat 7168))) (repeat (Z_to_bv 8 0) (Z.to_nat 7168))])
    by (rewrite repeat_length; exact POST).
  pose proof (cb_subZ mz (A + 8) _ 0 160 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as HZ.
  pose proof (cb_subZ mz (A + 8) _ 160 640 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZL0.
  pose proof (cb_subZ mz (A + 8) _ 800 576 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZW0.
  pose proof (cb_subZ mz (A + 8) _ 1376 5776 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZC0.
  pose proof (cb_subZ mz (A + 8) _ 7152 16 POST' ltac:(lia) ltac:(lia) ltac:(rewrite repeat_length; lia)) as ZT.
  clear POST POST'.
  rewrite Z.add_0_r in HZ.
  replace (A + 8 + 160) with (A + 168) in ZL0 by lia. replace (A + 8 + 800) with (A + 808) in ZW0 by lia.
  replace (A + 8 + 1376) with (A + 1384) in ZC0 by lia. replace (A + 8 + 7152) with (A + 7160) in ZT by lia.
  assert (HZ8 : rw_cells psegs mz (A + 8) hz_tail).
  { eapply rw_cells_recast; [exact HZ| unfold hz_tail; cbn [cells_wf cell_wf]; repeat split| vm_compute; reflexivity]. }
  assert (ZL : rw_cells psegs mz (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))]).
  { eapply rw_cells_recast; [exact ZL0| cbn [cells_wf cell_wf]; rewrite repeat_length; repeat split| vm_compute; reflexivity]. }
  assert (ZW : rw_cells psegs mz (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))]).
  { eapply rw_cells_recast; [exact ZW0| cbn [cells_wf cell_wf]; rewrite repeat_length; repeat split| vm_compute; reflexivity]. }
  assert (ZC : rw_cells psegs mz (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))]).
  { eapply rw_cells_recast; [exact ZC0| cbn [cells_wf cell_wf]; rewrite repeat_length; repeat split| vm_compute; reflexivity]. }
  assert (GT : rw_cells psegs mz (A + 7160) [C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
  { eapply rw_cells_recast; [exact ZT| cbn [cells_wf cell_wf]; repeat split| vm_compute; reflexivity]. }
  clear HZ ZL0 ZW0 ZC0 ZT.
  unfold hz_tail in HZ8.
  (* [inflateInit_'s stores: strm, mode, strm->state, the zalloc check, wrap | reqwrap, reqbits | wbits; then
      mv a0,a1 and the jal to inflateReset] *)
  do 7 zs. zs. br_false.
  do 8 zs.
  (* [the head as inflateReset reads it] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (GA : rw_cells psegs mm A (ireset14_pre S)) end.
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
      | rewrite E32; lia| exact S63| exact A0| exact A1| eassumption]. }
  intros ms' PO. unfold ireset14_post_st in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STK' & ZS' & GA' & GT').
  rewrite E32 in *. clear ZS GA GT STK.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m' MUc WMc end. clear MUc WMc.
  replace (ret_pc (wz 119224)) with (wz 119224) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  zs. br_true. zs. do 5 zs.
  release_frame FR STK' (bv_unsigned sp).
  do 2 zs.
  apply evt_done. unfold ii_block_post14. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK'|].
  split; [exact ZS'|]. split; [exact GA'|]. split; [exact GT'|]. split; [exact ZL|]. split; [exact ZW| exact ZC].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma le8_mode_last : le8 (wz 16180) = le4 (wz 16180) ++ le4 (wz 0).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_hd_flags : le8 (wz (-4294967296)) = le4 (wz 0) ++ le4 (wz (-1)).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_00 : le8 (wz 0) = le4 (wz 0) ++ le4 (wz 0).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma le8_sane_back : le8 (wz 18446744069414584321) = le4 (wz 1) ++ le4 (wz (-1)).
Proof. rewrite le8_Z, !le4_Z. cbn [Z_to_le_bytes app]. repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.

(* [comment removed for export] *)
(* zlib 1.4: Z_ikit's ired predates r2's two inflate_state fields; this is ired's list plus is_reqwrap / is_reqbits /
   iset_reqwrap / iset_reqbits, so a projection over the new setters reduces here and the kernel never meets
   [is_check (iset_reqbits ..)] at Qed (it took > 300 s there) *)
Local Ltac ired14 := cbn [w_s w_c w_r is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk is_reqwrap is_reqbits ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk iset_reqwrap iset_reqbits icset_input icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out icset_adler icset_data_type icset_msg irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret wset_s wset_c wset_r].

Ltac iinit_red :=
  unfold iinit_of, ireset_s, s_pre, is_of_oracle, lay_ref;
  cbn [lay_mode lay_last lay_wrap lay_havedict lay_flags lay_dmax lay_check lay_total lay_head lay_wbits lay_wsize lay_whave lay_wnext lay_window lay_hold lay_bits
       lay_length lay_offset lay_extra lay_lencode lay_distcode lay_lenbits lay_distbits lay_ncode lay_nlen lay_ndist lay_have lay_next lay_lens lay_work lay_codes
       lay_sane lay_back lay_was il_S il_As il_Aw il_NI il_NO win_addr cp_addr];
  ired14; change (ir2_wrap MAX_WBITS) with 5; change (ir2_wb MAX_WBITS) with 15.

(* [1.4: the oracle reads zeros past byte 8 (the memset), whatever 1.3.1 offset the model reads them at] *)
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

(* [r2's model (zmemzero) builds the fresh state from the zero oracle: its integer cells are 0 by these lemmas, so
    the cell comparisons below stay syntactic (a reflexivity on [wz (init_u32 (fun _ => 0) b i)] blew up at Qed)] *)
Lemma z0_range : forall i : Z, 0 <= (fun _ : Z => 0) i < 256.
Proof. intros i. cbv beta. lia. Qed.
Lemma init_u16_z0 : forall b i, init_u16 (fun _ : Z => 0) b i = 0.
Proof. intros b i. rewrite (init_u16_ole _ z0_range). apply ole_zero. intros k _. reflexivity. Qed.
Lemma init_u32_z0 : forall b i, init_u32 (fun _ : Z => 0) b i = 0.
Proof. intros b i. rewrite (init_u32_ole _ z0_range). apply ole_zero. intros k _. reflexivity. Qed.
Lemma init_u64_z0 : forall b i, init_u64 (fun _ : Z => 0) b i = 0.
Proof. intros b i. rewrite (init_u64_ole _ z0_range). apply ole_zero. intros k _. reflexivity. Qed.

(* [the fresh 1.4 state, field by field (one Qed each, so the kernel checks each piece on its own)] *)
Section IST14.
Variables (m : mem) (S A NI NO : Z) (junk : list byte).
Hypothesis HZ : forall k, 8 <= Z.of_nat k < 7176 -> nth k junk (Z_to_bv 8 0) = Z_to_bv 8 0.

Lemma iist14_A : rw_cells psegs m A (ireset14_post S A) -> isA m (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof.
  intros GA. unfold ireset14_post in GA.
  apply (cells_split8_0 m A [C8 (wz S); C8 (wz 16180); C4 (wz 5); C4 (wz 5); C8 (wz (-4294967296)); C4 (wz 32768); C4 (wz 0);
                            C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 15); C4 (wz 15)]) in GA. cbn [app] in GA.
  unfold isA. eapply rw_cells_recast; [exact GA| |].
    + unfold isA_cells. cbn [cells_wf cell_wf]. repeat split.
    + unfold isA_cells. iinit_red. cbn [win_addr cp_addr il_As il_Aw].
      rewrite ?(izero32 junk HZ), ?(izero64 junk HZ) by lia.
      rewrite ?init_u16_z0, ?init_u32_z0, ?init_u64_z0.
      cbn [cells_bytes cbytes]. unfold HEAD. rewrite le8_mode_last, le8_hd_flags.
      rewrite <- !app_assoc. rewrite !Z.mul_0_r, !Z.add_0_r. reflexivity.
Qed.

Lemma iist14_T : rw_cells psegs m (A + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)] ->
  isT m (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof.
  intros GT. exists (le4 (wz 0)). eapply rw_cells_recast; [exact GT| |].
    + unfold isT_cells. cbn [cells_wf cell_wf]. repeat split; try apply length_le4.
    + unfold isT_cells. iinit_red. rewrite ?(izero32 junk HZ) by lia. rewrite ?init_u16_z0, ?init_u32_z0, ?init_u64_z0.
      cbn [cells_bytes cbytes]. rewrite le8_sane_back.
      rewrite <- !app_assoc. reflexivity.
Qed.

Lemma iist14_lens : rw_cells psegs m (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))] ->
  ilens m (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof.
  intros ZL. unfold ilens, u16arr. iinit_red. apply u8arr_of_rw_cells in ZL.
    (* r2's model (zmemzero) reads the arrays from the zero oracle, so each cell is 0; the template's orc-junk route
       is kept as the first alternative *)
    rewrite (av16_zero _ 320) by (try lia; intros i Hi; unfold iarr_u16_of; rewrite arr_get_init;
                                  first [apply (izero16 junk HZ); lia | apply init_u16_z0]).
    exact ZL.
Qed.

Lemma iist14_work : rw_cells psegs m (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))] ->
  iwork m (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof.
  intros ZW. unfold iwork, u16arr. iinit_red. apply u8arr_of_rw_cells in ZW.
    rewrite (av16_zero _ 288) by (try lia; intros i Hi; unfold iarr_u16_of; rewrite arr_get_init;
                                  first [apply (izero16 junk HZ); lia | apply init_u16_z0]).
    exact ZW.
Qed.

Lemma iist14_codes : rw_cells psegs m (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))] ->
  icodes m (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof.
  intros ZC. unfold icodes, u32arr. iinit_red. apply u8arr_of_rw_cells in ZC. destruct ZC as [ZB ZW']. split.
    + rewrite (av32_zero _ 1444) by (try lia; intros i Hi; unfold iarr_u32_of; rewrite arr_get_init;
                                     first [apply (izero32 junk HZ); lia | apply init_u32_z0]).
      exact ZB.
    + lazymatch goal with |- context [length (av32 ?a ?n)] =>
        replace (4 * Z.of_nat (length (av32 a n)))
          with (Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat 5776)))) by (rewrite av32_length, repeat_length; lia) end.
      exact ZW'.
Qed.

Lemma iist14_win : iwin m (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof. unfold iwin. iinit_red. exact I. Qed.

Lemma iist14_arrs : iarrs (iinit_of (orc junk)).
Proof.
  unfold iarrs. iinit_red. unfold iarr_u16_of, iarr_u32_of. rewrite !arr_len_init. repeat split; try reflexivity.
  intros NE. exfalso. apply NE. reflexivity.
Qed.

Lemma iist14_lay : blk_ok A 7176 -> ilay_ok (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof. intros BOK. unfold ilay_ok. iinit_red. split; [exact BOK|]. intros NE. exfalso. apply NE. reflexivity. Qed.
End IST14.

Lemma iinit_IST14 : forall m S A NI NO (junk : list byte),
  (forall k, 8 <= Z.of_nat k < 7176 -> nth k junk (Z_to_bv 8 0) = Z_to_bv 8 0) ->
  rw_cells psegs m A (ireset14_post S A) ->
  rw_cells psegs m (A + 7160) [C8 (wz 18446744069414584321); C4 (wz 0); C4 (wz 0)] ->
  rw_cells psegs m (A + 168) [CB (Z.to_nat 640) (repeat (Z_to_bv 8 0) (Z.to_nat 640))] ->
  rw_cells psegs m (A + 808) [CB (Z.to_nat 576) (repeat (Z_to_bv 8 0) (Z.to_nat 576))] ->
  rw_cells psegs m (A + 1384) [CB (Z.to_nat 5776) (repeat (Z_to_bv 8 0) (Z.to_nat 5776))] ->
  blk_ok A 7176 ->
  IST m (Z_irep.mkIL S A 0 NI NO) (iinit_of (orc junk)).
Proof.
  intros m S A NI NO junk HZ GA GT ZL ZW ZC BOK.
  constructor;
    first [ eapply iist14_A; eassumption | eapply iist14_T; eassumption | eapply iist14_lens; eassumption
          | eapply iist14_work; eassumption | eapply iist14_codes; eassumption | eapply iist14_win
          | eapply iist14_arrs | eapply iist14_lay; eassumption ].
Qed.

(* [comment removed for export] *)
Lemma zi_init_z : zs_msg (iz_z zi_init) = MSG_NULL /\ zs_adler (iz_z zi_init) = 1 /\ zs_total_in (iz_z zi_init) = 0 /\ zs_total_out (iz_z zi_init) = 0.
Proof.
  unfold zi_init, iz0, iinit0. cbn [iz_z]. rewrite iinit_run_of. cbn [zr_strm zret0]. unfold ireset_z, z_pre.
  change (is_wrap (s_pre HarnessSmall.g0 5%N MAX_WBITS)) with 5. cbn. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
                               STK ltac:(lia) ltac:(lia) ZS SF1 ltac:(lia) MI)|].
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & FR & STK1 & ZS1 & MU1 & WM1 & MI1).
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
    (* [comment removed for export] *)
    assert (AGC : forall A0 n, bv_unsigned sp + -32 <= A0 -> 0 <= n -> A0 + n <= 2^64 -> Z_dview.agree_on A0 (A0 + n) m1 m2).
    { intros A0 n H1 H2 H3 a Ha. apply HPR; [lia|]. left. lia. }
    apply (Z_dview.rw_cells_agree m1 m2) in FR; [|apply AGC; cbn [cells_size csize Nat.add]; lia].
    apply (Z_dview.rw_cells_agree m1 m2) in ZS1; [|apply AGC; unfold zs_pub; cbn [app cells_size csize Nat.add]; lia].
    (* [comment removed for export] *)
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= lo /\ 0 < blk_addr b).
    { intros b Hb. pose proof (HBR _ _ _ b HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    assert (PRES1 : lx_pres LB (bv_unsigned sp) [(S, S + ZS_SIZEOF)] m m1).
    { apply (lx_pres_of_munch LB (bv_unsigned sp) _ [(lo, bv_unsigned sp); (S, S + 112)] m m1 MU1 WM1).
      intros a (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX. cbn [outside].
      destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb)|]; repeat split; lia. }
    assert (PRES2 : lx_pres LB (bv_unsigned sp) [(S, S + ZS_SIZEOF)] m1 m2).
    { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR| lia| auto]. }
    destruct r as [p|].
    - (* [comment removed for export] *)
      destruct HR as (A & junk & -> & RBR & HP2 & WJ & _).
      destruct RBR as (RB1 & RB2 & RB3 & RB4 & RB5).
      assert (BOK : blk_ok A 7176) by (unfold blk_ok; repeat split; try assumption; lia).
      assert (A1 : A + 7176 <= lo) by lia.
      assert (SEPB : forall b, In b LB -> blk_addr b + blk_size b <= A \/ A + 7176 <= blk_addr b).
      { intros b Hb. pose proof (heap_sep st' [(p, A, 7176)] LB m2 (p, A, 7176) b HND HBD HP2 (or_introl eq_refl) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
      assert (ENV2 : lx_env m2 st' [(p, A, 7176)] LB (wz (bv_unsigned sp + -32)) tp B lo errv2 canary).
      { apply (lx_env_heap m1 m2 s st' [] [(p, A, 7176)] LB (wz (bv_unsigned sp + -32)) tp B lo errv errv2 canary ENV1 HPRc HP2 MI2); [rewrite E32; exact STK2| exact ERR2| exact AUX2]. }
      assert (LJ' : length junk = Z.to_nat 7176) by exact (proj1 (proj1 (proj1 WJ))).
      (* 1.4: inflateInit_ zeroes the state past byte 8 and calls inflateReset (iinit_block14); the model state is read
         from jkz = the block's first 8 junk bytes followed by zeros *)
      eapply evt_mono; [exact (iinit_block14 S A lo ni ai ti no ao to p1 p2 jstate jrest junk ra sp gp tp t0'' t1'' t2'' s0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                  t3'' t4'' t5'' t6'' s1 F fc m2 FR STK2 ltac:(lia) ltac:(lia) ZS1 WJ SF1 ltac:(lia) RB1 A1 MI2)|].
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
        { (* [1.4: inflateReset stores data_type = 0; its pad and reserved stay the strm's junk] *)
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
        intros i Hi. unfold arr_make in Hi. rewrite arr_len_init in Hi. lia.
    - (* [comment removed for export] *)
      destruct HR as (-> & HP2).
      assert (ENV2 : lx_env m2 st' [] LB (wz (bv_unsigned sp + -32)) tp B lo errv2 canary).
      { apply (lx_env_heap m1 m2 s st' [] [] LB (wz (bv_unsigned sp + -32)) tp B lo errv errv2 canary ENV1 HPRc HP2 MI2); [rewrite E32; exact STK2| exact ERR2| exact AUX2]. }
      eapply evt_mono; [exact (iinit_null lo ra sp gp tp t0'' t1'' t2'' s0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'' s1 (wz S) F fc m2
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
      + apply (rw_cells_transport psegs [(lo, bv_unsigned sp)] m2 m') in ZS1; [| exact MU'| exact WM'| unfold zs_pub; cbn [app cells_size csize Nat.add disjoint_from]; split; [lia| exact I]].
        destruct (rw_cells_forget psegs m' _ _ ZS1) as (j & Hj). exists j. exact Hj.
  Qed.
End INIT.
End WithCeiling0.
