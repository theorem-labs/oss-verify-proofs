(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.   (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface CJ_tree AShadow CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import Exit SO_base Stdio_iface Drv_base Drv_icpt_defs Drv_dicpt Drv_iface2 Drv_traces CJ_fuzz_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DRV_B_TRUN : Z := cost_malloc (2^26) + 2 * cost_free + 4 * FUZZ_COST (2^26).
(* [comment removed for export] *)
Definition loop_budget (cap : Z) : Z := DRV_B_TRUN + 9 * (2^27 - cap) + 2^19 * (2^26 / cap).
(* [comment removed for export] *)
Definition DRV_B_MAIN : Z := cost_malloc 65536 + loop_budget 65536.

(* [comment removed for export] *)
Definition loop_tokens (k : nat) : nat := (11 - k)%nat.

Section CeilWrap.
Context {ACEIL : Ceil}.

Section Stmts.
  Variables (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface).
  Let ART := CJ_iface.ART AI.
  Let ADRV := Drv_iface2.ADRV AI DI.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition main_two_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (fs : Fs) (lo P1 : Z) (tid : word) (path slack : list byte) (errv : word) (B0 : Z),
    DMOD fs FDS0 mo ->
    ART (bv_unsigned sp + 48) (bv_unsigned sp) [] [] [] B0 m mo g -> DRV_B_MAIN <= B0 -> ADRV DRV_CALLS m mo g ->
    TINV TI 0 [] -> drv_traces_ok TI ->
    ra = wz ASTAGE2_RET -> tp = wz ATP -> a0 = wz 2 -> a1 = wz (bv_unsigned sp + 56) ->
    stk bsegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp + 48 <= 2^47 ->
    sp_window_lo <= bv_unsigned sp + 48 -> bv_unsigned sp mod 16 = 0 ->
    ASTACK_BOTTOM (bv_unsigned sp + 48) <= lo ->                 (* [comment removed for export] *)
    mem_inv bsegs m -> frm0 fc ->
    ADSTAT tid m -> 0 < bv_unsigned tid < 2^22 -> DICPT m ->
    rw_cells bsegs m AERRNO [C4 errv] -> rw_cells bsegs m AINITFLAG [C1 (Z_to_bv 8 0)] ->
    stdout_file m stdout_init -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m ->
    (exists stj, rw_cells bsegs m ARS [CB RSN stj]) ->
    rw_cells bsegs m (bv_unsigned sp + 64) [C8 (wz P1)] ->
    bytes_at bsegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
    path_has_slash path = false -> path <> dotdot_path ->   (* [comment removed for export] *)
    (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 131071 -> bv_unsigned sp + 48 <= P1 ->
    P1 + zlength path + 1 + zlength slack + 16 <= 2^47 ->
    LRZ bsegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (wz AMAIN) fc None m (seg_rom bsegs)) mo g
        (spec_path path fs).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition main_usage_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (fs : Fs) (lo argc P0 : Z) (tid : word) (argv0 slack : list byte) (B0 : Z),
    DMOD fs FDS0 mo ->
    ART (bv_unsigned sp + 48) (bv_unsigned sp) [] [] [] B0 m mo g -> TINV TI 0 [] -> drv_traces_ok TI ->
    ra = wz ASTAGE2_RET -> tp = wz ATP -> a0 = wz argc -> a1 = wz (bv_unsigned sp + 56) ->
    0 <= argc < 2^63 -> argc <> 2 ->
    stk bsegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp + 48 <= 2^47 ->
    bv_unsigned sp mod 16 = 0 ->
    mem_inv bsegs m -> frm0 fc ->
    ADSTAT tid m -> 0 < bv_unsigned tid < 2^22 -> DICPT m ->
    stdout_file m stdout_init -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m ->
    rw_cells bsegs m (bv_unsigned sp + 56) [C8 (wz P0)] ->
    bytes_at bsegs m P0 (argv0 ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) argv0 ->
    (- (P0 + zlength argv0 + 1)) mod 8 <= zlength slack -> zlength argv0 <= 131071 -> bv_unsigned sp + 48 <= P0 ->
    P0 + zlength argv0 + 1 + zlength slack + 16 <= 2^47 ->
    LRZ bsegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (wz AMAIN) fc None m (seg_rom bsegs)) mo g
        (t_die (msg_usage argv0) fs).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Kloop (data : list byte) (fs : Fs) (cap : Z) : TSet := t_body data fs.

Section LoopStmts.
  (* [comment removed for export] *)
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid ra0 : word)
            (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 : word) (q8 q9 q10 q11 : word).
  Let sp0 : Z := bv_unsigned sp + 128.

  (* [comment removed for export] *)
  Definition loop_inv (len cap A : Z) (TRS : list (list Z)) (B np : Z) (junk : list byte)
             (m : word -> option byte) (mo : Model) (g : lghost) : Prop :=
    stk bsegs m lo (bv_unsigned sp) /\ mem_inv bsegs m
    /\ rw_cells bsegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)
    /\ ADSTAT tid m /\ DICPT m /\ (exists e, rw_cells bsegs m AERRNO [C4 e]) /\ rw_cells bsegs m AINITFLAG [C1 (Z_to_bv 8 0)]
    /\ stdout_file m stdout_init /\ stderr_wfile0 m /\ stdin_file m /\ stack_shadow_zero m
    /\ bytes_at bsegs m P1 (path ++ Z_to_bv 8 0 :: slack)
    /\ ART sp0 SPB [(A, cap)] [] TRS B m mo g /\ TINV TI np TRS /\ np = 0 /\ loop_budget cap <= B
    /\ DMOD fs (FDS3 (FdFile path (wz len))) mo /\ fs_lookup fs path = Some data
    /\ rw_cells bsegs m A [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk]
    /\ shadow_ok m A cap
    /\ (exists stj, rw_cells bsegs m ARS [CB RSN stj])
    /\ (exists k : nat, cap = 65536 * 2 ^ (Z.of_nat k) /\ ADRV (loop_tokens k) m mo g)
    /\ 0 <= len <= cap /\ len <= zlength data /\ cap <= 2^26.

  (* [comment removed for export] *)
  Definition loop_regs (len cap A : Z) (m : word -> option byte) (pc : Z) : machine_state -> Prop :=
    fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz len) (wz 3) (wz cap) (wz ARS) s7 q8 q9 q10 q11 t3 t4 t5 t6)
              F (wz pc) fc None m (seg_rom bsegs).

  (* [comment removed for export] *)
  Definition loop_stmt : Prop :=
    forall len cap A TRS B np junk m mo g ms,
      loop_inv len cap A TRS B np junk m mo g -> len < cap -> loop_regs len cap A m 0x81fb0 ms ->
      LRZ bsegs ms mo g (Kloop data fs cap).

  (* [comment removed for export] *)
  Definition post_stmt : Prop :=
    forall cap A TRS B np junk m mo g (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      loop_inv (zlength data) cap A TRS B np junk m mo g -> zlength data < cap ->
      LRZ bsegs (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz (zlength data)) (wz 3) (wz cap) (wz ARS) (wz 0) q8 q9 q10 q11 t3 t4 t5 t6)
                    F (wz 0x81fd8) fc None m (seg_rom bsegs)) mo g
          (t_body data fs).
End LoopStmts.

Lemma Kloop_top : forall data fs cap, t_eq (Kloop data fs cap) (t_body data fs).
Proof. intros data fs cap. apply t_eq_refl. Qed.

Lemma Kloop_nil : forall data fs cap, Kloop data fs cap [].
Proof. intros data fs cap. unfold Kloop. apply t_body_nil. Qed.

(* [comment removed for export] *)
Definition loop_side (sp tp : word) (fc : bv 32) (lo SPB P1 : Z) (tid : word) (path slack : list byte) : Prop :=
  tp = wz ATP /\ lo + 2^22 <= bv_unsigned sp + 80 /\ alloc_ceiling <= lo /\ bv_unsigned sp + 128 <= 2^47 /\ SPB = bv_unsigned sp + 80
  /\ 0 < bv_unsigned tid < 2^22 /\ frm0 fc /\ ~ In (Z_to_bv 8 0) path /\ (- (P1 + zlength path + 1)) mod 8 <= zlength slack
  /\ zlength path <= 131071 /\ bv_unsigned sp + 128 <= P1 /\ P1 + zlength path + 1 + zlength slack + 16 <= 2^47 /\ bv_unsigned sp mod 16 = 0
  /\ sp_window_lo <= bv_unsigned sp + 128 /\ ASTACK_BOTTOM (bv_unsigned sp + 128) <= lo.

(* [comment removed for export] *)
Definition trun_side (sp tp : word) (lo SPB : Z) : Prop :=
  tp = wz ATP /\ lo + 2^22 <= bv_unsigned sp + 80 /\ alloc_ceiling <= lo /\ bv_unsigned sp + 128 <= 2^47 /\ SPB = bv_unsigned sp + 80
  /\ bv_unsigned sp mod 16 = 0 /\ sp_window_lo <= bv_unsigned sp + 128 /\ ASTACK_BOTTOM (bv_unsigned sp + 128) <= lo.

Lemma loop_side_trun : forall sp tp fc lo SPB P1 tid path slack,
  loop_side sp tp fc lo SPB P1 tid path slack -> trun_side sp tp lo SPB.
Proof.
  intros until slack. intros (TP & LO & GT & SPH & SPBE & _ & _ & _ & _ & _ & _ & _ & SPAL & WIN & BOT).
  split; [exact TP|]. split; [exact LO|]. split; [exact GT|]. split; [exact SPH|]. split; [exact SPBE|]. split; [exact SPAL|]. split; [exact WIN| exact BOT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tcalls (cl : Z) (data : list byte) : nat :=
  match Z.to_nat cl with O => 1%nat | _ => S (Z.to_nat (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4)) end.

(* [comment removed for export] *)
Definition lines (j : nat) : list Z := concat (repeat [48; 10] j).
Definition so_after (j : nat) : stdout_st := mkStdout true (lines j) false false.

Section TrunStmt.
  Variables (sp gp tp : word) (fs : Fs) (lo SPB : Z) (tid : word) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word)
            (ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 : word) (A cap : Z).
  Let sp0 : Z := bv_unsigned sp + 128.

  (* [comment removed for export] *)
  Definition trun_ret (st : Z) (so : stdout_st) : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                             (m' : word -> option byte) (e' : word) (LB' : list cblock) (TRS' : list (list Z)) (B' np' : Z),
      ms' = MS (mkR (wz 0x82058) sp gp tp t0 t1 t2 ms0 ms1 (wz st) a1 a2 a3 a4 a5 a6 a7 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (wz 0x82058) fc' None m' (seg_rom bsegs)
      /\ frm0 fc' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' AERRNO [C4 e'] /\ ART sp0 SPB LB' [] TRS' B' m' mo' g' /\ In (A, cap) LB' /\ TINV TI np' TRS' /\ cost_free <= B'
      /\ rw_cells bsegs m' (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)
      /\ ADSTAT tid m' /\ DICPT m' /\ stderr_wfile0 m' /\ stdin_file m' /\ stack_shadow_zero m' /\ stdout_file m' so /\ DMOD fs FDS0 mo'.

  Definition trun_stmt : Prop :=
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (TRS : list (list Z)) (B : Z) (junk data : list byte) (cl : Z) (e : word) (KT : TSet),
      let len := zlength data in
      let plen := len - 6 - cl in
      ART sp0 SPB [(A, cap)] [] TRS B m mo g -> TINV TI 0 TRS -> DRV_B_TRUN <= B -> 4 * FUZZ_NP (2^26) <= NPMAX TI ->
      ADRV 1 m mo g ->
      rw_cells bsegs m A [CB (Z.to_nat len) data; CB (Z.to_nat (cap - len)) junk] -> shadow_ok m A cap ->
      0 <= cl < 32768 -> 6 + cl <= len -> len < 2^26 -> len <= cap ->
      DMOD fs FDS0 mo -> frm0 fc ->
      stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m -> rw_cells bsegs m AERRNO [C4 e] ->
      rw_cells bsegs m AINITFLAG [C1 (Z_to_bv 8 0)] -> ADSTAT tid m -> DICPT m -> stdout_file m stdout_init -> stderr_wfile0 m ->
      stdin_file m -> stack_shadow_zero m ->
      rw_cells bsegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0) ->
      KT [] ->
      (forall ms' mo' g', trun_ret 0 (so_after (tcalls cl data - 1)) ms' mo' g' -> LRZ bsegs ms' mo' g' KT) ->
      LRZ bsegs (MS (mkR (wz 0x82058) sp gp tp t0 t1 t2 ms0 ms1 (wz (A + 2)) (wz cl) (wz (A + 6 + cl)) (wz plen) a4 a5 a6 a7
                         ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ATRUN) fc None m (seg_rom bsegs)) mo g
          (t_emit (W 1 emit_line) KT).
End TrunStmt.
End Stmts.
End CeilWrap.
