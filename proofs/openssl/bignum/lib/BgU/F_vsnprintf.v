(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim Monad PrintfModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Printf_lib F_memset F_memcpy F_fwritex F_pop_arg F_printf_iface F_printf_core.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import F_printf_snsink F_sn_write F_towrite F_vfprintf Printf_sn.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import PrintfModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bgusegs m mm MU WM end end.
Import ListNotations.
Import ITree.Exc.

Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma rw_cells_recast : forall m A cs cs', rw_cells bgusegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bgusegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells bgusegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells bgusegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.

Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

Definition VSN_FRAME : Z := 304.
Definition VSN_DEPTH : Z := 5856.
Definition VSN_W (lo q D : Z) (dn : nat) : list (Z * Z) := [(lo, q); (D, D + Z.of_nat dn)].

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (D : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom bgusegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk bgusegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells bgusegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

Definition vsnprintf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells bgusegs m D [CB dn junkd] ->
    bytes_at bgusegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> (forall m', munch (VSN_W lo q D dn) m m' -> args_ok 0 0 0 m' lo q 0 slots args) ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    fp_calls (length fmt) fmt args = [] ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk bgusegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv bgusegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt bgusegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b9ff4) fc None m (seg_rom bgusegs)).

Lemma fmt_bytes_at : forall m A f, mem_inv bgusegs m -> ro_bytes_b bgusegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at bgusegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at bgusegs m A _ (ro_cells_image bgusegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
