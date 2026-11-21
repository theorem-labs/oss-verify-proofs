(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_pure2 Z_updwin_pure Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefUpdWin1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition Z_UPDATEWINDOW : Z := 0x21ac0.
Definition PC_UW_BODY : Z := 0x21b38.     (* [comment removed for export] *)
Definition PC_UW_RET : Z := 0x21b30.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition updwin_post (L : ilay) (s' : inflate_state) (rc : Z) (lo : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (W : list ivl) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz rc) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp) /\ isA m' L s' /\ iwin m' L s'.
Definition PC_UW_COPY : Z := 0x21b44.     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma xor_guard_sub : forall a b, 0 < a -> 0 <= b -> a <> b -> Z.lxor (Z.b2z (0 <? a)) (Z.b2z (Z.lxor a b <? 1)) = 1.
Proof.
  intros a b Ha Hb Hne. rewrite (proj2 (Z.ltb_lt 0 a) Ha).
  assert (NZ : Z.lxor a b <> 0) by (intros E0; apply Hne; apply Z.lxor_eq; exact E0).
  pose proof (Z.lxor_nonneg a b) as NN.
  replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma xor_guard_sub0 : forall a, 0 < a -> Z.lxor (Z.b2z (0 <? a)) (Z.b2z (a <? 1)) = 1.     (* [comment removed for export] *)
Proof. intros a Ha. rewrite (proj2 (Z.ltb_lt 0 a) Ha). replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Ltac gXsub := first [ rewrite xor_guard_sub by lia | rewrite xor_guard_sub0 by lia ]; zs; br_false.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PC_MALLOC : Z := 0x23b0c.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition uw_at_malloc (L : ilay) (copy E lo : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' fj,
    ms' = MS (mkR (wz PC_UW_RET) (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz 32768) a1 a2 a3 a4 a5 a6 a7
                  (wz 1) (wz (il_As L)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz PC_MALLOC) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Lemma updwin_to_malloc : forall (L : ilay) (s : inflate_state) (c : icall) (copy E lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk usegs m lo (bv_unsigned sp) -> izs m L c ->
  isA m L s -> is_window_blk s = None -> is_wbits s = 15 ->
  lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo ->
  mem_inv usegs m ->
  il_S L mod 8 = 0 -> il_As L mod 16 = 0 ->      (* [comment removed for export] *)
  evt usegs (uw_at_malloc L copy E lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (il_S L)) (wz E) (wz copy) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_UPDATEWINDOW) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STK ZS GA HB Hwb LO1 LO2 SPS S63 As0 As1 MI ALS ALA.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  open_isA GA. open_izs ZS.
  unfold Z_UPDATEWINDOW. carve_frame 64%nat STK.
  do 10 zs. zs. al8 (il_S L). gF. zs. gF. zs. al8 (il_As L). gF.       (* [comment removed for export] *)
  do 2 zs. rewrite HB. cbn [win_addr]. zs. br_false.
  zs. rewrite Hwb. zs. gF.                                             (* [comment removed for export] *)
  do 6 zs. do 4 zs.
  apply evt_done. unfold uw_at_malloc. do 16 eexists. split; [reflexivity|].
  split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma updwin_ret_null : forall (fj : list byte) (L : ilay) (s : inflate_state) (copy E lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = None ->
  lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp < 2^63 -> 0 < il_As L -> il_As L + 7176 <= lo ->
  mem_inv usegs m ->
  evt usegs (updwin_post L s 1 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(lo, bv_unsigned sp); (il_As L, il_As L + 168)] m)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz 0) a1 a2 a3 a4 a5 a6 a7 (wz 1) (wz (il_As L)) s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_RET) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros FR STK GA HB LO1 LO2 SP63 As0 As1 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (il_As L, il_As L + 168)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  open_isA GA. rewrite HB in GA. cbn [win_addr] in GA.
  unfold PC_UW_RET. zs. zs. br_true. do 9 zs. release_frame FR STK (bv_unsigned sp). zs.
  apply evt_done. unfold updwin_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact STK|]. split; [unfold isA, isA_cells; rewrite HB; cbn [win_addr]; exact GA|].
  unfold iwin; rewrite HB; exact I.
Qed.

(* [comment removed for export] *)
Definition il_setw (L : ilay) (A : Z) : ilay := mkIL (il_S L) (il_As L) A (il_NI L) (il_NO L).
(* [comment removed for export] *)
Definition s_fresh (s : inflate_state) (wb : ZProg.blk) (junk : list byte) : inflate_state :=
  iset_window (iset_window_blk s (Some wb)) (iarr_u8_of (gwb junk) 0 32768).

