(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 AsCall AsAuxv ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitSeg ECH_ALibMF ECH_ALibOK ECH_ALibMid ECH_ALibMidA
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C13 ECH_AStmt_C14 ECH_AStmt_C15
  ECH_AC13_small ECH_AC13_store ECH_AC7_newmembuf ECH_AC7_biofreeint ECH_AC7_biofree.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PO_R1 : Z := R_parse_one_OSSL_ECHSTORE_new.                  (* [comment removed for export] *)
Definition PO_R2 : Z := R_parse_one_BIO_new_mem_buf.                     (* [comment removed for export] *)
Definition PO_R3 : Z := R_parse_one_OSSL_ECHSTORE_read_echconfiglist.    (* [comment removed for export] *)
Definition PO_R4 : Z := R_parse_one_OSSL_ECHSTORE_free.                  (* [comment removed for export] *)
Definition ap_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AUXV.
  Context {HCEIL : HeapCeil}.
  Lemma aauxv_wins_of_aimg : forall B X,
    aceil <= B -> Forall in_aimg X -> Forall (fun iv : Z * Z => snd iv <= AAUXV_CELL \/ AAUXV_CELL + 8 <= fst iv) X -> Forall (aauxv_win_ok B) X.
  Proof.
    intros B X HB F1 F2. induction X as [|[lo hi] X IH]; [constructor|].
    inversion F1 as [|iv1 l1 K1 F1']; inversion F2 as [|iv2 l2 K2 F2']; subst. constructor; [| apply IH; assumption].
    apply aauxv_win_ok_low; [exact HB| | exact K2]. unfold in_aimg in K1. cbn in K1. pose proof aceil_facts. unfold AIMG_TOP in K1. lia.
  Qed.
  Lemma aauxv_memflag : forall B, aceil <= B -> Forall (aauxv_win_ok B) memflag_foot.
  Proof.
    intros B HB. apply aauxv_wins_of_aimg; [exact HB| apply aimg_memflag|].
    unfold memflag_foot, A_mem_inited, AAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil].
  Qed.
  Lemma aauxv_ctxph_foot : forall B ph, aceil <= B -> Forall (aauxv_win_ok B) (ctxph_foot ph).
  Proof.
    intros B ph HB. apply aauxv_wins_of_aimg; [exact HB| apply aimg_ctxph_foot|]. apply Forall_ctxph_foot.
    unfold CTX_X, AERRNO_X, ATP, AAUXV_CELL. unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_exlock, A_defctx_exmeth_bio, A_defctx_tlkey, A_defctx_tlkey_once,
      A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_stopped, A_base_inited, A_base_once, A_base_ret,
      A_optsdone, A_optsdone_lock, A_init_lock, A_in_init_config_key, A_load_strings_once, A_load_strings_ret, A_td_tsd, A_td_tsd_used, A_td_cancelbuf,
      A_keys, A_next_key, A_key_lock, A_tsd_main, LIBKEY0.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
  Qed.
  Lemma aauxv_fs_scratch : forall B XS,
    aceil <= B -> Forall (fun iv : Z * Z => AIMG_TOP <= fst iv /\ fst iv <= snd iv <= aceil) XS -> Forall (aauxv_win_ok B) XS.
  Proof.
    intros B XS HB F. eapply Forall_impl; [| exact F]. intros [lo hi] [K1 K2]. cbn [fst snd] in K1, K2.
    apply aauxv_win_ok_low; [exact HB| lia|]. right. unfold AAUXV_CELL, AIMG_TOP in *. cbn. lia.
  Qed.
  Lemma aauxv_CTX_X : forall B, aceil <= B -> Forall (aauxv_win_ok B) CTX_X.
  Proof.
    intros B HB. apply aauxv_wins_of_aimg; [exact HB| apply aimg_CTX_X|].
    unfold CTX_X, AAUXV_CELL. unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_exlock, A_defctx_exmeth_bio, A_defctx_tlkey, A_defctx_tlkey_once,
      A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_stopped, A_base_inited, A_base_once, A_base_ret,
      A_optsdone, A_optsdone_lock, A_init_lock, A_in_init_config_key, A_load_strings_once, A_load_strings_ret, A_td_tsd, A_td_tsd_used, A_td_cancelbuf,
      A_keys, A_next_key, A_key_lock, A_tsd_main, LIBKEY0.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
  Qed.
  Lemma aauxv_ERR_XE : forall B, aceil <= B -> Forall (aauxv_win_ok B) ERR_XE.
  Proof.
    intros B HB. apply aauxv_wins_of_aimg; [exact HB| apply aimg_ERR_XE|].
    unfold ERR_XE, ERRNO_X, ERR_X, ARERRNO, ATP, AAUXV_CELL. unfold A_err_string_once, A_err_string_ret, A_err_string_lock, A_int_error_hash, A_master_once_ret, A_master_once, A_master_key,
      A_defctx_inited, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_stopped, A_base_inited, A_base_once, A_base_ret, A_optsdone, A_optsdone_lock, A_init_lock,
      A_in_init_config_key, A_load_strings_once, A_load_strings_ret, A_td_tsd, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main, LIBKEY0.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
  Qed.
  Lemma aauxv_VDSO_X : forall B, aceil <= B -> Forall (aauxv_win_ok B) VDSO_X.
  Proof. intros B HB. apply aauxv_wins_of_aimg; [exact HB| apply aimg_VDSO_X|]. unfold VDSO_X, A_vdso_func, AAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. Qed.
  Lemma aauxv_errph_foot : forall B LIB m cph eph,
    aceil <= B -> ERRPH_mid LIB m cph eph -> (forall b, In b LIB -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil) ->
    Forall (aauxv_win_ok B) (errph_foot eph).
  Proof.
    intros B LIB m [|x] [|c] HB P HBK; cbn [ERRPH_mid ERRPH errph_foot] in *; try apply Forall_nil; [destruct P|].
    destruct P as [_ CH]. destruct CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    apply Forall_cons; [| apply Forall_nil]. pose proof (HBK _ I5) as [K1 K2]. rewrite Z5 in K2.
    apply aauxv_win_ok_low; [exact HB| exact K2|]. right. cbn [fst]. unfold AAUXV_CELL, AIMG_TOP in *. lia.
  Qed.
End AUXV.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma ap_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 PO_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 a1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                       a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_ECHSTORE_new) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells asegs m1 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_parse_one) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI.
    unfold P_parse_one, P_OSSL_ECHSTORE_new, PO_R1, R_parse_one_OSSL_ECHSTORE_new.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 32%nat ST.
    do 4 st1. do 4 step. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ap_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z),
      0 < A < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 PO_R2) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 s2 s1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_new_mem_buf) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 PO_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PO_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until A. intros AR MI. unfold PO_R1, PO_R2, R_parse_one_OSSL_ECHSTORE_new, R_parse_one_BIO_new_mem_buf, P_BIO_new_mem_buf.
    replace (ret_pc (Z_to_bv 64 0x1ef434)) with (Z_to_bv 64 0x1ef434) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    do 3 step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ap_seg3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      0 < a < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 PO_R3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) s0 (Z_to_bv 64 a) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 PO_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PO_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until a. intros AR MI. unfold PO_R2, PO_R3, R_parse_one_BIO_new_mem_buf, R_parse_one_OSSL_ECHSTORE_read_echconfiglist, P_OSSL_ECHSTORE_read_echconfiglist.
    replace (ret_pc (Z_to_bv 64 0x1ef44c)) with (Z_to_bv 64 0x1ef44c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    do 3 step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ap_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 PO_R4) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_ECHSTORE_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 PO_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PO_R3)) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold PO_R3, PO_R4, R_parse_one_OSSL_ECHSTORE_read_echconfiglist, R_parse_one_OSSL_ECHSTORE_free, P_OSSL_ECHSTORE_free.
    replace (ret_pc (Z_to_bv 64 0x1ef464)) with (Z_to_bv 64 0x1ef464) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ap_seg5 :
    forall (sp gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s2 : word) (s1v : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells asegs m (bv_unsigned sp + -32) (ap_frame s2 s1v s0 ra) ->
      stk asegs m lo (bv_unsigned sp + -32) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1v s1 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free) fc None m (seg_rom asegs)
          /\ stk asegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 PO_R4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PO_R4)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros FR ST CEIL LO MI. unfold PO_R4, R_parse_one_OSSL_ECHSTORE_free, P_BIO_free. unfold ap_frame in FR.
    replace (ret_pc (Z_to_bv 64 0x1ef470)) with (Z_to_bv 64 0x1ef470) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. do 4 step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section COST.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma Cf_nonneg : forall n, 0 <= n -> 0 <= as_Cf H n.
  Proof. pose proof (ah_costs H HH) as (_ & _ & K & _). exact K. Qed.
  Lemma Cf_mono : forall n n', 0 <= n <= n' -> as_Cf H n <= as_Cf H n'.
  Proof. pose proof (ah_costs H HH) as (_ & _ & _ & K & _). exact K. Qed.
  Lemma Cf_super : forall a b, 0 <= a -> 0 <= b -> as_Cf H a + as_Cf H b <= as_Cf H (a + b).
  Proof. pose proof (ah_costs H HH) as (_ & _ & _ & _ & _ & K). exact K. Qed.
  Lemma Cf_arg : forall x a b, x <= as_Cf H a -> a = b -> x <= as_Cf H b.
  Proof. intros x a b K E. subst b. exact K. Qed.
  Lemma Cf_zero : as_Cf H 0 = 0.
  Proof. pose proof (Cf_super 0 0 (Z.le_refl 0) (Z.le_refl 0)) as K. pose proof (Cf_nonneg 0 (Z.le_refl 0)) as K'. rewrite Z.add_0_r in K. lia. Qed.

  Lemma Forall2_In_combine : forall (A B : Type) (R : A -> B -> Prop) (l : list A) (l' : list B) (x : A) (y : B),
    Forall2 R l l' -> In (x, y) (combine l l') -> R x y.
  Proof.
    intros A B R l l' x y F Hin. induction F as [|a b l0 l0' Rab F IH]; [destruct Hin|].
    cbn in Hin. destruct Hin as [E|Hin]; [injection E as <- <-; exact Rab| exact (IH Hin)].
  Qed.
  Lemma ocost_bound : forall P o, Forall (fun b => 0 <= blk_size b) (blocks_of P o) ->
    0 <= lb_bytes (blocks_of P o) /\ ocost H o <= as_Cf H (lb_bytes (blocks_of P o)).
  Proof.
    intros P [[id n]|] F; cbn [blocks_of ocost] in *.
    - pose proof (Forall_inv F) as K. cbn in K. rewrite lb_bytes_cons. cbn [blk_size snd lb_bytes fold_right]. rewrite Z.max_l by lia. split; [lia|]. apply Cf_mono. lia.
    - cbn [lb_bytes fold_right]. rewrite Cf_zero. lia.
  Qed.

  Lemma ecost_sum_bound : forall (X : Type) (f : X -> Z) (g : Z -> X -> list block) (ps : list Z) (xs : list X),
    length xs = length ps ->
    (forall p x, In (p, x) (combine ps xs) -> 0 <= lb_bytes (g p x) /\ f x <= as_Cf H (lb_bytes (g p x))) ->
    0 <= lb_bytes (concat (map (fun pe => g (fst pe) (snd pe)) (combine ps xs)))
    /\ ecost_sum X f xs <= as_Cf H (lb_bytes (concat (map (fun pe => g (fst pe) (snd pe)) (combine ps xs)))).
  Proof.
    intros X f g ps xs. revert ps. induction xs as [|x xs IH]; intros [|p ps] LEN HF; cbn [length] in LEN; try lia.
    - cbn. rewrite Cf_zero. lia.
    - cbn [combine map concat fst snd ecost_sum fold_right]. rewrite lb_bytes_app_s.
      destruct (HF p x ltac:(left; reflexivity)) as [B1 B2].
      destruct (IH ps ltac:(lia) ltac:(intros p' x' Hin; apply HF; right; exact Hin)) as [B3 B4].
      change (fold_right (fun x0 acc => f x0 + acc) 0 xs) with (ecost_sum X f xs).
      split; [lia|]. pose proof (Cf_super _ _ B1 B3). lia.
  Qed.

  Lemma sk_cost_bound : forall P K, Forall (fun b => 0 <= blk_size b) (blocks_SK P K) ->
    0 <= lb_bytes (blocks_SK P K) /\ as_Cf H (Z.max (8 * sk_cap K) 0) + as_Cf H SK_SIZE <= as_Cf H (lb_bytes (blocks_SK P K)).
  Proof.
    intros P K F. unfold blocks_SK in *. rewrite lb_bytes_cons. cbn [blk_size snd].
    destruct (sk_cap K =? 0) eqn:E.
    - apply Z.eqb_eq in E. rewrite E. cbn [lb_bytes fold_right Z.mul Z.max]. rewrite Cf_zero. unfold SK_SIZE. rewrite Z.add_0_r. split; [lia|]. lia.
    - pose proof (Forall_inv (Forall_inv_tail F)) as K2. cbn in K2. rewrite lb_bytes_cons. cbn [blk_size snd lb_bytes fold_right].
      rewrite Z.max_l by lia. unfold SK_SIZE in *. split; [lia|]. pose proof (Cf_super (8 * sk_cap K) 56 ltac:(lia) ltac:(lia)) as K3. eapply (Cf_arg _ _ _ K3). lia.
  Qed.

  Lemma ext_cost_bound : forall LB m p X, EXTobj LB m p X -> Forall (fun b => 0 <= blk_size b) (blocks_EXT p X) ->
    0 <= lb_bytes (blocks_EXT p X) /\ ext_cost H X <= as_Cf H (lb_bytes (blocks_EXT p X)).
  Proof.
    intros LB m p X _ F. unfold blocks_EXT, ext_cost in *. rewrite lb_bytes_cons. cbn [blk_size snd].
    destruct (ocost_bound (ex_val X) (ex_val_o X) (Forall_inv_tail F)) as [B1 B2]. unfold EXT_SIZE in *.
    split; [lia|]. pose proof (Cf_super 16 (lb_bytes (blocks_of (ex_val X) (ex_val_o X))) ltac:(lia) B1). lia.
  Qed.

  Lemma exts_cost_bound : forall LB m P xs, EXTS LB m P xs -> Forall (fun b => 0 <= blk_size b) (blocks_EXTS P xs) ->
    0 <= lb_bytes (blocks_EXTS P xs) /\ exts_cost H xs <= as_Cf H (lb_bytes (blocks_EXTS P xs)).
  Proof.
    intros LB m P [[K es]|] EX F; cbn [blocks_EXTS exts_cost] in *.
    - destruct EX as (_ & _ & LEN & F2). apply Forall_app in F. destruct F as [FS FE].
      destruct (sk_cost_bound P K FS) as [S1 S2]. rewrite lb_bytes_app_s.
      destruct (ecost_sum_bound extrep (ext_cost H) blocks_EXT (sk_elems K) es LEN) as [E1 E2].
      { intros p x Hin. eapply ext_cost_bound with (LB := LB) (m := m).
        - eapply (Forall2_In_combine _ _ _ _ _ _ _ F2 Hin).
        - rewrite Forall_forall in FE. apply Forall_forall. intros b Hb. apply FE. apply in_concat. exists (blocks_EXT p x). split; [| exact Hb].
          apply in_map_iff. exists (p, x). split; [reflexivity| exact Hin]. }
      split; [lia|]. pose proof (Cf_super _ _ S1 E1). lia.
    - cbn [lb_bytes fold_right]. pose proof (Cf_nonneg 0 ltac:(lia)). lia.
  Qed.

  Lemma entry_cost_bound : forall LB m p E, ENTRYobj LB m p E -> Forall (fun b => 0 <= blk_size b) (blocks_ENTRY p E) ->
    0 <= lb_bytes (blocks_ENTRY p E) /\ entry_cost H E <= as_Cf H (lb_bytes (blocks_ENTRY p E)).
  Proof.
    intros LB m p E EO F. unfold blocks_ENTRY, entry_cost in *. rewrite lb_bytes_cons. cbn [blk_size snd].
    pose proof (Forall_inv_tail F) as F'. cbn [blk_size snd] in F'.
    apply Forall_app in F'. destruct F' as [F1 F']. apply Forall_app in F'. destruct F' as [F2 F']. apply Forall_app in F'. destruct F' as [F3 F'].
    apply Forall_app in F'. destruct F' as [F4 F5].
    destruct (ocost_bound _ _ F1) as [A1 A2]. destruct (ocost_bound _ _ F2) as [B1 B2]. destruct (ocost_bound _ _ F3) as [G1 G2]. destruct (ocost_bound _ _ F4) as [D1 D2].
    destruct EO as (_ & _ & _ & _ & _ & _ & EX). destruct (exts_cost_bound _ _ _ _ EX F5) as [X1 X2].
    rewrite !lb_bytes_app_s.
    set (bA := lb_bytes (blocks_of (en_pname E) (en_pname_o E))) in *. set (bB := lb_bytes (blocks_of (en_pub E) (en_pub_o E))) in *.
    set (bC := lb_bytes (blocks_of (en_suites E) (en_suites_o E))) in *. set (bD := lb_bytes (blocks_of (en_encoded E) (en_encoded_o E))) in *.
    set (bX := lb_bytes (blocks_EXTS (en_exts E) (en_exts_o E))) in *.
    unfold ENTRY_SIZE in *. split; [lia|].
    pose proof (Cf_super bD bX D1 X1) as S4.
    pose proof (Cf_super bC (bD + bX) G1 ltac:(lia)) as S3.
    pose proof (Cf_super bB (bC + (bD + bX)) B1 ltac:(lia)) as S2.
    pose proof (Cf_super bA (bB + (bC + (bD + bX))) A1 ltac:(lia)) as S1.
    pose proof (Cf_super 104 (bA + (bB + (bC + (bD + bX)))) ltac:(lia) ltac:(lia)) as S0.
    lia.
  Qed.

  Lemma store_cost_bound : forall LB m st S, STOREobj LB m st S -> Forall (fun b => 0 <= blk_size b) (blocks_STORE st S) ->
    store_cost H S <= as_Cf H (lb_bytes (blocks_STORE st S)).
  Proof.
    intros LB m st S SO F. unfold blocks_STORE, store_cost in *. rewrite lb_bytes_cons. cbn [blk_size snd]. rewrite Cf_zero.
    pose proof (Forall_inv_tail F) as F'. cbn [blk_size snd] in F'. destruct SO as (_ & _ & EN).
    destruct (es_entries_o S) as [[K es]|]; cbn [entries_cost ENTRIES] in *.
    - destruct EN as (_ & _ & LEN & F2). apply Forall_app in F'. destruct F' as [FS FE].
      destruct (sk_cost_bound (es_entries S) K FS) as [S1 S2]. rewrite lb_bytes_app_s.
      destruct (ecost_sum_bound entrep (entry_cost H) blocks_ENTRY (sk_elems K) es LEN) as [E1 E2].
      { intros p x Hin. eapply entry_cost_bound with (LB := LB) (m := m).
        - eapply (Forall2_In_combine _ _ _ _ _ _ _ F2 Hin).
        - rewrite Forall_forall in FE. apply Forall_forall. intros b Hb. apply FE. apply in_concat. exists (blocks_ENTRY p x). split; [| exact Hb].
          apply in_map_iff. exists (p, x). split; [reflexivity| exact Hin]. }
      unfold STORE_SIZE in *. pose proof (Cf_super _ _ S1 E1) as K1.
      assert (NN : 0 <= lb_bytes (blocks_SK (es_entries S) K) + lb_bytes (concat (map (fun pe : Z * entrep => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K) es)))) by (clear - S1 E1; lia).
      pose proof (Cf_super 24 _ ltac:(lia) NN) as K2. lia.
    - cbn [lb_bytes fold_right]. unfold STORE_SIZE. rewrite ?Z.add_0_r, ?Z.add_0_l. lia.
  Qed.
End COST.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_avoid_hi : forall (X : list (Z * Z)) (c A n : Z),
  Forall (fun iv : Z * Z => snd iv <= c) X -> c <= A -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X.
Proof. intros X c A n F LE. eapply Forall_impl; [| exact F]. intros [u w] K. cbn in K |- *. lia. Qed.
Lemma Forall_below_aimg {HCEIL : HeapCeil} : forall X, Forall in_aimg X -> Forall (fun iv : Z * Z => snd iv <= aceil) X.
Proof. intros X F. acb. eapply Forall_impl; [| exact F]. intros [u w] K. unfold in_aimg in K. cbn in K |- *. unfold AIMG_TOP in *. lia. Qed.
Lemma Forall_below_app : forall (X Y : list (Z * Z)) (c : Z),
  Forall (fun iv : Z * Z => snd iv <= c) X -> Forall (fun iv : Z * Z => snd iv <= c) Y -> Forall (fun iv : Z * Z => snd iv <= c) (X ++ Y).
Proof. intros X Y c F G. apply Forall_app. split; assumption. Qed.

(* [comment removed for export] *)
Lemma asegs_find_segment_none_high' : forall a n, 1 <= n -> 12599296 <= a -> find_segment asegs a n = None.
Proof.
  intros a n Hn Ha. unfold asegs, RefMemImage.Ref.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
  cbn [Z.of_N seg_base seg_size RefMemImage.RefMemImage_segment_000 RefMemImage.RefMemImage_segment_001 RefMemImage.RefMemImage_segment_002 RefMemImage.RefMemImage_segment_003
       AsanUbsan.AsanUbsan_segment_000 AsanUbsan.AsanUbsan_segment_001
       AsanUbsan.AsanUbsan_segment_002 AsanUbsan.AsanUbsan_segment_003].
  destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + n) (65536 + 1593344)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 1658880 a); destruct (Z.leb_spec (a + n) (1658880 + 4046848)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 5705728 a); destruct (Z.leb_spec (a + n) (5705728 + 495616)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 6201344 a); destruct (Z.leb_spec (a + n) (6201344 + 6397952)); cbn [andb]; try (exfalso; lia).
  reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_same_raw_hi : forall m m' A cs a,
  rw_cells asegs m A cs -> rw_cells asegs m' A cs -> AIMG_TOP <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Proof.
  intros m m' A cs a [[W1 B1] X1] [[W2 B2] X2] TOP HI Ha.
  pose proof (cells_bytes_length cs W1) as CL.
  destruct B1 as (HA & HL & R1). destruct B2 as (_ & _ & R2). destruct X2 as (_ & _ & WW2).
  split.
  - specialize (R1 (Z.to_nat (a - A)) ltac:(rewrite CL; lia)). specialize (R2 (Z.to_nat (a - A)) ltac:(rewrite CL; lia)).
    rewrite Z2Nat.id in R1, R2 by lia. replace (A + (a - A)) with a in R1, R2 by lia.
    unfold mrd in R1, R2. unfold AIMG_TOP in TOP.
    assert (SR : seg_rom asegs (wa a) = None).
    { unfold seg_rom, memory_read. unfold wa. rewrite unsigned_lit by lia. rewrite asegs_find_segment_none_high' by lia. reflexivity. }
    destruct (m (wa a)) as [b1|]; destruct (m' (wa a)) as [b2|]; rewrite ?SR in R1, R2; congruence.
  - intros _. replace a with (A + (a - A)) by lia. apply WW2. lia.
Qed.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  (* [comment removed for export] *)
  Hypothesis CNX : cnewex_stmt H.
  Hypothesis CFX : cfreeex_stmt H.
  (* [comment removed for export] *)
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).
  Hypothesis RCFG : readcfg_stmt H PF9new PF9free.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let PERM : rheap_perm H := HHx_rheap_perm H HX.

  (* [comment removed for export] *)
  Lemma pf_ok_closed : forall PF site,
    Forall (fun r : Z * list Z => trace_ok (as_TR H) (fst r) (snd r)) (pf_shift site PF) -> pf_ok (as_TR H) PF site [].
  Proof.
    intros PF site F. unfold pf_ok. apply Forall_forall. intros [pc0 p] Hin. cbn [fst snd map].
    unfold pf_shift in F. rewrite Forall_forall in F. exact (F (pc0, p ++ [site]) (in_map (fun pp : Z * list Z => (fst pp, snd pp ++ [site])) PF (pc0, p) Hin)).
  Qed.
  (* [comment removed for export] *)
  Lemma xpres_drop_same : forall LB SP X Y m m',
    xpres H LB SP (X ++ Y) m m' -> (forall q, rin_ivs X q -> m' (wa q) = m (wa q) /\ (wview asegs m (wa q) <> None -> wview asegs m' (wa q) <> None)) ->
    xpres H LB SP Y m m'.
  Proof.
    intros LB SP X Y m m' XP SAME q Hq [HC HY].
    assert (D : rin_ivs X q \/ ~ rin_ivs X q).
    { clear. induction X as [|[lo hi] X IH]; cbn; [right; tauto|]. destruct (Z_le_gt_dec lo q); destruct (Z_lt_ge_dec q hi); destruct IH as [IH|IH]; try (left; lia); try (left; right; exact IH); right; intros [K|K]; [lia| exact (IH K)| lia| exact (IH K)|lia|exact (IH K)]. }
    destruct D as [D|D]; [exact (SAME q D)|]. apply XP; [exact Hq|]. split; [exact HC|].
    intros K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (D K)| exact (HY K)].
  Qed.
  Lemma errph_foot_shape : forall LIB m cph eph, ERRPH_mid LIB m cph eph ->
    errph_foot eph = [] \/ exists c, errph_foot eph = [(blk_addr (ec_es c), blk_addr (ec_es c) + ERRST_SIZE)] /\ In (ec_es c) LIB /\ blk_size (ec_es c) = ERRST_SIZE.
  Proof.
    intros LIB m [|x] [|c] P; cbn [ERRPH_mid ERRPH errph_foot] in *; [left; reflexivity| destruct P| left; reflexivity|].
    right. exists c. destruct P as [_ CH]. destruct CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). split; [reflexivity|]. split; [exact I5| exact Z5].
  Qed.
  Lemma Forall_app_r : forall (A : Type) (P : A -> Prop) (l1 l2 : list A), Forall P (l1 ++ l2) -> Forall P l2.
  Proof. intros A P l1 l2 F. apply Forall_app in F. exact (proj2 F). Qed.

  Lemma parse_one_spec : parse_one_stmt H PF9new PF9free.
  Proof.
    unfold parse_one_stmt. intros until CH.
    intros VIS A0 A1 NR DS DSL DP DH DIN DEMPTY LM SUBL CLO CCL HP KREL BUD BUDC AUX AUXA SPB BHI SPA ST CEIL LO STK0 SSH ERR MI TP AC RL ADDR RFS LFB CHN CHS PFS PCL PFB HAL RAE.
    unfold PARSE_BYTES, PARSE_CNT, PARSE_STACK, PARSE_LF, FR_parse_one, DECODE_BYTES, DECODE_CNT, ERRSTR_BYTES, ERRSTR_CNT, READCFG_LF in *.
    subst a0 a1. pose proof (readcfg_stack_lo M) as RSL. pose proof (ctxph_nonneg H HH (mid_ctx M)) as (PHB & PHC & PHS & PHK). pose proof (errph_nonneg (mid_err M)) as (EHB & EHC).
    assert (NSK : 0 <= NEWMEMBUF_STACK (mid_ctx M)).
    { unfold NEWMEMBUF_STACK, BIONEW_STACK, FR_BIO_new_mem_buf, FR_BIO_new_ex. lia. }
    set (RS := READCFG_STACK M) in *. set (NS := NEWMEMBUF_STACK (mid_ctx M)) in *.
    unfold mid_bytes, mid_cnt in BUD, BUDC.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & CMS & CFS).
    assert (PK0 : 0 <= as_Cm H STORE_SIZE /\ 0 <= NEWMEMBUF_COST H (mid_ctx M) /\ 0 <= READCFG_COST H M /\ 0 <= as_Cf H (STORE_SIZE + 2 ^ 17) /\ 0 <= BIOFREE_COST H).
    { unfold NEWMEMBUF_COST, READCFG_COST, BIOFREE_COST, STORE_SIZE, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, DECODE_CUM_BYTES.
      pose proof (CM0 24 ltac:(lia)). pose proof (CM0 128 ltac:(lia)). pose proof (CM0 32 ltac:(lia)). pose proof (CM0 16 ltac:(lia)). pose proof (CF0 16 ltac:(lia)). pose proof (CM0 (2^23) ltac:(lia)). pose proof (CF0 0 ltac:(lia)).
      pose proof (CF0 32 ltac:(lia)). pose proof (CF0 128 ltac:(lia)). pose proof (CF0 (24 + 2^17) ltac:(lia)). pose proof (CF0 (2^23) ltac:(lia)).
      assert (0 <= errph_cost H (mid_err M)).
      { destruct (mid_err M); cbn [errph_cost]; [| lia]. unfold ERRINIT_COST. pose proof (CM0 ERRINIT_BYTES ltac:(unfold ERRINIT_BYTES; lia)). pose proof (CF0 ERRINIT_BYTES ltac:(unfold ERRINIT_BYTES; lia)). lia. }
      lia. }
    destruct PK0 as (PK1 & PK2 & PK3 & PK4 & PK5). unfold PARSE_COST in HAL. unfold DECODE_BYTES in HAL. unfold READCFG_COST in HAL, PK3.
    (* [comment removed for export] *)
    assert (PFC : forall x, pf_ok (as_TR H) (PF_newmembuf (mid_ctx M)) R_parse_one_BIO_new_mem_buf []
                        /\ pf_ok (as_TR H) (PF_readcfg PF9new PF9free (mid_after_nmb M x)) R_parse_one_OSSL_ECHSTORE_read_echconfiglist []
                        /\ pf_ok (as_TR H) PF_storefree R_parse_one_OSSL_ECHSTORE_free []).
    { intros x0. pose proof (PCL x0) as K. unfold PFC_parse in K. apply Forall_app in K. destruct K as [K1 K]. apply Forall_app in K. destruct K as [K2 K3].
      split; [apply pf_ok_closed; exact K1|]. split; [apply pf_ok_closed; exact K2| apply pf_ok_closed; exact K3]. }
    set (E0 := mid_errblocks M) in *. set (L0 := E0 ++ LB) in *.
    assert (SUB0 : forall b, In b LIB -> In b L0) by (intros b Hb; unfold L0; apply in_or_app; right; apply SUBL; exact Hb).
    assert (SUBE0 : forall b, In b E0 -> In b L0) by (intros b Hb; unfold L0; apply in_or_app; left; exact Hb).
    assert (HB : forall b, In b L0 -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    subst tp. rewrite (unsigned_lit ATP) in ERR by (unfold ATP; lia).
    pose proof LM as (IM0 & MF0 & CP0 & EPm0 & EX0 & VD0 & CL0 & FIT0 & GM0 & GE0 & GX0 & MM0 & MB0 & HT0 & RL0 & ESH0 & EBL0).
    (* [comment removed for export] *)
    set (Bmiss := fun (X : list (Z * Z)) (A0 n0 : Z) => forall q, rin_ivs X q -> ~ (A0 <= q < A0 + n0) /\ ~ (sh A0 <= q < sh A0 + nsh n0)).
    assert (BM_nil : forall A0 n0, Bmiss [] A0 n0) by (intros A0 n0 q K; destruct K).
    assert (BM_app : forall X Y A0 n0, Bmiss X A0 n0 -> Bmiss Y A0 n0 -> Bmiss (X ++ Y) A0 n0).
    { intros X Y A0 n0 DX DY q K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (DX q K)| exact (DY q K)]. }
    assert (SHTOP : sh AIMG_TOP = 0x80178800) by reflexivity.
    assert (BM_img : forall X A0 n0, Forall in_aimg X -> AIMG_TOP <= A0 -> 0 <= n0 -> aapp A0 n0 -> Bmiss X A0 n0).
    { intros X A0 n0 FX P1 P2 P3 q K. pose proof (sh_aapp_range A0 n0 P3 P2) as (S1 & S2 & S3).
      destruct (rin_ivs_In _ _ K) as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as W. unfold in_aimg in W. unfold AIMG_TOP in *. lia. }
    (* [comment removed for export] *)
    assert (BM_blk : forall s' L' m' b b0 lo' hi', as_RHEAP H s' L' m' -> In b L' -> In b0 L' -> blk_id b <> blk_id b0 ->
              blk_addr b <= lo' -> hi' <= blk_addr b + blk_size b -> Bmiss [(lo', hi')] (blk_addr b0) (blk_size b0)).
    { intros s' L' m' b b0 lo' hi' HP' Hb Hb0 NE B1 B2 q K. cbn [rin_ivs fst snd] in K. destruct K as [K|[]].
      pose proof (ah_disj H HH _ _ _ _ _ HP' Hb Hb0 NE) as DJ.
      pose proof (ah_blocks H HH _ _ _ _ HP' Hb) as (_ & _ & Q3 & _ & _ & _ & Q7). pose proof (aapp_not_shadowland _ _ Q7).
      pose proof (ah_blocks H HH _ _ _ _ HP' Hb0) as (_ & _ & R3 & _ & _ & _ & R7). pose proof (sh_aapp_range _ _ R7 R3) as (S1 & S2 & S3).
      unfold ALOWSH_LO, AHI_LO in *. lia. }
    (* [comment removed for export] *)
    assert (BM_xs : forall s' L' m0 mm XS b0, as_RHEAP H s' L' m0 -> In b0 L' -> as_RFS H LF mm -> Forall (fs_scratch H LF) XS -> Bmiss XS (blk_addr b0) (blk_size b0)).
    { intros s' L' m0 mm XS b0 HP' Hb0 RF FXS q K. destruct (rin_ivs_In _ _ K) as (iv & Hiv & R).
      pose proof (fs_scratch_off_block H HH s' L' m0 [b0] LF mm iv q HP' ltac:(intros b [<-|[]]; exact Hb0) RF (proj1 (Forall_forall _ _) FXS iv Hiv) R) as [NBq NSq].
      split; intros Kq; [apply NBq| apply NSq]; exists b0; (split; [left; reflexivity| exact Kq]). }
    (* [comment removed for export] *)
    assert (BX_bytes : forall L SP X mm mm' A0 bs b0, xpres H L SP X mm mm' -> bytes_at asegs mm A0 bs -> In b0 L ->
              blk_addr b0 <= A0 -> A0 + Z.of_nat (length bs) <= blk_addr b0 + blk_size b0 -> Bmiss X (blk_addr b0) (blk_size b0) -> bytes_at asegs mm' A0 bs).
    { intros L SP X mm mm' A0 bs b0 XP BA Hb0 B1 B2 BM. eapply bytes_at_agree; [eapply (magree_of_xpres H); exact XP| exact BA|].
      intros q Hq. unfold in_range in Hq. split; [right; right; left; exists b0; split; [exact Hb0| lia]|]. intros K. exact (proj1 (BM q K) ltac:(lia)). }
    assert (BX_cells : forall L SP X mm mm' A0 cs b0, xpres H L SP X mm mm' -> rw_cells asegs mm A0 cs -> In b0 L ->
              blk_addr b0 <= A0 -> A0 + Z.of_nat (cells_size cs) <= blk_addr b0 + blk_size b0 -> Bmiss X (blk_addr b0) (blk_size b0) -> rw_cells asegs mm' A0 cs).
    { intros L SP X mm mm' A0 cs b0 XP RC Hb0 B1 B2 BM. eapply rw_cells_agree; [eapply (magree_of_xpres H); exact XP| exact RC|].
      intros q Hq. unfold in_range in Hq. split; [right; right; left; exists b0; split; [exact Hb0| lia]|]. intros K. exact (proj1 (BM q K) ltac:(lia)). }
    assert (BX_addr : forall L SP X mm mm' b0, xpres H L SP X mm mm' -> addressable mm (blk_addr b0) (blk_size b0) -> In b0 L ->
              Bmiss X (blk_addr b0) (blk_size b0) -> addressable mm' (blk_addr b0) (blk_size b0)).
    { intros L SP X mm mm' b0 XP AD Hb0 BM. eapply addressable_agreeR; [eapply (magree_of_xpres H); exact XP| | exact AD].
      intros q Hq. split; [right; right; right; left; exists b0; split; [exact Hb0| exact Hq]|]. intros K. exact (proj2 (BM q K) Hq). }
    (* [comment removed for export] *)
    assert (DSX : forall L SP X mm mm', xpres H L SP X mm mm' -> bytes_at asegs mm D ds -> (forall b, In b LB -> In b L) ->
                  (forall pD, In (pD, D, N) LB -> Bmiss X D N) -> bytes_at asegs mm' D ds).
    { intros L SP X mm mm' XP BA SUB DX. destruct (Z.eq_dec N 0) as [N0|N0].
      - destruct ds; [| unfold zlength in DSL; cbn in DSL; lia]. destruct BA as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
      - destruct (DIN ltac:(lia)) as [pD [PIN _]]. unfold zlength in DSL.
        exact (BX_bytes L SP X mm mm' D ds (pD, D, N) XP BA (SUB _ PIN) ltac:(cbn; lia) ltac:(cbn; lia) (DX pD PIN)). }
    assert (ADX : forall L SP X mm mm', xpres H L SP X mm mm' -> (1 <= N -> addressable mm D N) -> (forall b, In b LB -> In b L) ->
                  (forall pD, In (pD, D, N) LB -> Bmiss X D N) -> 1 <= N -> addressable mm' D N).
    { intros L SP X mm mm' XP AD SUB DX N1. destruct (DIN N1) as [pD [PIN _]].
      exact (BX_addr L SP X mm mm' (pD, D, N) XP (AD N1) (SUB _ PIN) (DX pD PIN)). }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply ap_seg1 with (lo := lo); [exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CW1 : Forall (aclient_write_ok H L0) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (AW1 : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)])
      by (constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]).
    assert (SW1 : Forall stack0_ok [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; unfold AHI_LO; lia| constructor]).
    pose proof (ah_fsb H HH _ _ _ HP) as (FSB1 & FSB2 & FSB3 & FSB4).
    assert (FW1 : Forall (afs_write_ok H LF) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [| constructor]. left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. split; lia. }
    assert (HP1 : as_RHEAP H s L0 m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW1]).
    pose proof (aauxv_ok_bounds _ _ AUXA) as ACB.
    assert (AUXA1 : aauxv_ok m1 B) by (eapply aauxv_ok_frame; [exact AUXA| exact MU1| exact WM1| apply Forall_cons; [apply aauxv_win_ok_stack; lia| apply Forall_nil]]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW1]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (XP1 : xpres H L0 (bv_unsigned sp) [] m m1)
      by (eapply (xpres_of_munch H s L0 _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH1 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (ah_RFS_frame H HH); [exact RFS| exact MU1| exact WM1| exact FW1]).
    assert (STK1 : stack0 m1 lo shi) by (eapply stack0_transport; [exact STK0| exact MU1| exact WM1| exact SW1]).
    pose proof (LIBMID_xpres0_any H LIB L0 (bv_unsigned sp) m m1 M LM XP1 SUB0 SUBE0) as LM1.
    pose proof LM1 as (IM1 & MF1 & _ & _ & _ & _ & _ & _ & GM1 & _).
    assert (DS1 : bytes_at asegs m1 D ds) by (eapply DSX; [exact XP1| exact DS| intros b Hb; apply in_or_app; right; exact Hb| intros pD _; apply BM_nil]).
    assert (AD1 : 1 <= N -> addressable m1 D N) by (intros N1; eapply ADX; [exact XP1| exact ADDR| intros b Hb; apply in_or_app; right; exact Hb| intros pD _; apply BM_nil| exact N1]).
    assert (SP16' : (bv_unsigned sp + -32) mod 16 = 0) by (replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SPA; reflexivity).
    clear CW1 AW1 SW1 FW1.
    (* [comment removed for export] *)
    pose proof (astorenew_spec H HH) as SN. unfold storenew_stmt in SN.
    eapply (ah_seq H HH).
    { eapply SN with (lo := lo) (B := B) (LB := L0) (s := s) (v := mid_flag M) (CH := CH); [exact VIS1| reflexivity| reflexivity| ..];
        rewrite ?unsigned_lit by (unfold PO_R1, R_parse_one_OSSL_ECHSTORE_new; lia).
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => unfold STORE_SIZE; clear - BUD PHB EHB; lia
           | |- Z.of_nat (length _) + _ <= _ => clear - BUDC PHC EHC; lia
           | |- _ <= _ - STORENEW_STACK => clear - LO; lia
           | |- forall fp' ra', In (fp', ra') _ -> _ => intros fp' ra' Hin; specialize (CHS _ _ Hin); lia
           | |- pf_ok _ _ _ _ => unfold PO_R1; exact PFS
           | |- _ <= as_AL _ _ => clear - HAL PK1 PK2 PK3 PK4 PK5; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact HP1| exact KREL1| exact AUX1| exact ST1| exact CEIL| exact ERR1| exact MI1| reflexivity| exact SP16'| exact AC1| exact CH1
                       | exact MF1| exact IM1| exact GM1| lia | match goal with |- ?G => idtac "LEFT1:" G end]
           end. }
    clear SN. intros [msF2 mo2] PO. unfold storenew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR & HP2 & SO2 & SSH2 & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite (unsigned_lit ATP) in ERR2 by (unfold ATP; lia).
    pose proof BR as (AP & A16 & _ & ATOP & ACE & AFSB & AAP). unfold STORE_SIZE in ATOP, ACE, AAP.
    assert (AUXA2 : aauxv_ok m2 B) by (eapply aauxv_ok_xpres; [exact AUXA1| exact XP2| lia| apply aauxv_memflag; exact ACB]).
    set (sb := (p, A, STORE_SIZE)) in *. set (L1 := sb :: L0) in *.
    assert (SUB1 : forall b, In b LIB -> In b L1) by (intros b Hb; right; apply SUB0; exact Hb).
    assert (SUBE1 : forall b, In b E0 -> In b L1) by (intros b Hb; right; apply SUBE0; exact Hb).
    assert (HB1 : forall b, In b L1 -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP2 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    pose proof (LIBMID_mf_any H HH _ _ LIB L0 (bv_unsigned sp + -32) m1 m2 M HP1 LM1 XP2 SUB0 SUBE0 MF2) as LM2.
    pose proof LM2 as (_ & _ & CP2 & _ & _ & _ & _ & _ & _ & _ & _ & MM2 & _ & _ & RL2 & _). cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in CP2.
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact FR1| left; cbn; lia|]. unfold memflag_foot, A_mem_inited. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (DS2 : bytes_at asegs m2 D ds) by (eapply DSX; [exact XP2| exact DS1| intros b Hb; apply in_or_app; right; exact Hb| intros pD PIN; pose proof (HB _ (in_or_app _ _ _ (or_intror PIN))) as (P1 & P2 & P3 & P4 & P5 & P6); apply BM_img; [apply aimg_memflag| exact P1| exact P3| exact P6]]).
    assert (AD2 : 1 <= N -> addressable m2 D N) by (intros N1; eapply ADX; [exact XP2| exact AD1| intros b Hb; apply in_or_app; right; exact Hb| intros pD PIN; pose proof (HB _ (in_or_app _ _ _ (or_intror PIN))) as (P1 & P2 & P3 & P4 & P5 & P6); apply BM_img; [apply aimg_memflag| exact P1| exact P3| exact P6]| exact N1]).
    assert (RFS2 : as_RFS H LF m2).
    { eapply (RFS_via_xpres H HH); [exact RFS1| exact XP2|]. unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (STK2 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact XP2| exact STK1| apply stack0_ok_of_aimg; apply aimg_memflag]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply ap_seg2; [lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3.
    (* [comment removed for export] *)
    pose proof (anewmembuf_spec H HH CNX) as NMB. unfold newmembuf_stmt in NMB.
    assert (CHA : as_chain H m2 A []) by (apply (ah_chain_nil H HH); left; lia).
    eapply (ah_seq H HH).
    { eapply NMB with (lo := lo) (B := B) (LB := L1) (s := s2') (ph := mid_ctx M) (buf := D) (len := N) (LF := LF) (CH := []);
        [exact VIS3| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by (unfold PO_R2, R_parse_one_BIO_new_mem_buf; lia).
      all: lazymatch goal with
           | |- lb_bytes _ + _ + _ <= _ => unfold L1; rewrite lb_bytes_cons; cbn [blk_size snd sb]; unfold STORE_SIZE, MEMBIO_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; clear - BUD PHB EHB; lia
           | |- Z.of_nat (length _) + _ + _ <= _ => unfold L1; cbn [length]; clear - BUDC PHC EHC; lia
           | |- _ <= _ - NEWMEMBUF_STACK _ => clear - LO; lia
           | |- CTXPH _ _ _ => eapply (CTXPH_mono LIB L1 SUB1); exact CP2
           | |- forall fp' ra', In (fp', ra') _ -> _ => intros fp' ra' []
           | |- pf_ok _ _ _ _ => unfold PO_R2; exact (proj1 (PFC cx_dummy))
           | |- (length _ + _ <= _)%nat => pose proof (ctxph_frames (mid_ctx M)); destruct (mid_ctx M); cbn [ctxph_frames]; unfold READCFG_MAXLIVE, PARSE_LF, READCFG_LF, AFS_MAXLIVE in *; clear - LFB; lia
           | |- ctxph_sh0 _ _ _ _ => destruct (mid_ctx M); [| exact I]; cbn; rewrite unsigned_lit by lia; eapply stack0_sub; [exact STK2| clear; lia| clear - SSH LO SPR NSK RSL; lia| clear - SPA SPR; Z.div_mod_to_equations; lia]
           | |- ctxph_closed_ok _ _ => exact CCL
           | |- _ <= as_AL _ _ => clear - AL2 HAL PK1 PK2 PK3 PK4 PK5; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- as_chain _ _ _ _ => exact CHA
           | |- _ => first [exact HP2| exact KREL3| exact AUX2| exact ST2| exact CEIL| exact ERR2| exact MI2| reflexivity| exact SP16'| exact AC2
                       | exact MF2| exact IM2| exact GM2| exact MM2| exact RL2| exact RFS2| lia | match goal with |- ?G => idtac "LEFT2:" G end]
           end. }
    clear NMB. intros [msF4 mo4] PO. unfold newmembuf_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv3 & s3' & LA & LB3' & x & a & R & XS3 &
                    VIS4 & PI3 & MP4 & C3F & MM3 & DELTA & ADN3 & CPH3 & KEYS3 & MBO3 & RBUF & RLEN & RPOS & RNRD & RNXT & RPRV & APOS & APART
                    & MSH3 & FXS3 & RFS3 & XP3 & AL3).
    destruct C3F as (KREL4 & MI3 & AC3 & ST3 & ERR3 & AUX3 & HP3x & MF3 & IM3 & GM3 & RL3).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST3, XP3 by lia. rewrite (unsigned_lit ATP) in ERR3 by (unfold ATP; lia).
    pose proof (ctxph_delta_bounds _ _ _ DELTA) as (NB1 & NB2).
    assert (AUXA3 : aauxv_ok m3 B).
    { eapply aauxv_ok_xpres; [exact AUXA2| exact XP3| lia|].
      apply Forall_app; split; [apply aauxv_memflag; exact ACB|]. apply Forall_app; split; [apply aauxv_ctxph_foot; exact ACB|].
      apply aauxv_fs_scratch; [exact ACB| exact (fs_scratch_range_Forall H HH _ _ _ RFS2 FXS3)]. }
    pose proof (membio_blocks_facts a R) as (MBB & MBL).
    set (MB := blocks_MEMBIO a R) in *. set (L2 := MB ++ LA ++ L1) in *.
    set (M2 := mkMID 1 (CtxReady x) (mid_err M) (mid_E M) (mid_vdso M)).
    assert (HP3 : as_RHEAP H s3' L2 m3) by (eapply PERM; [exact HP3x| exact PI3]).
    assert (SUB3x : forall b, In b LB3' -> In b L2) by (intros b Hb; eapply Permutation_in; [exact PI3| exact Hb]).
    assert (HB2 : forall b, In b L2 -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP3 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    assert (ND2 := ah_nodup H HH _ _ _ HP3).
    assert (SUB12 : forall b, In b L1 -> In b L2) by (intros b Hb; unfold L2; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (SUBA2 : forall b, In b (LA ++ LIB) -> In b L2).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [unfold L2; apply in_or_app; right; apply in_or_app; left; exact Hb| apply SUB12; apply SUB1; exact Hb]. }
    pose proof (LIBMID_newmembuf H HH s2' m2 LIB L1 LB3' LA (bv_unsigned sp + -32) XS3 LF m2 m3 _ x HP2 RFS2 FXS3 LM2 XP3 SUB1 SUBE1 CPH3 DELTA KEYS3 MF3) as LM3.
    cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in LM3. change (LIBMID (LA ++ LIB) m3 M2) in LM3.
    pose proof LM3 as (_ & _ & CP3 & EPm3 & _ & _ & _ & _ & _ & GE3 & _ & MM3' & _ & _ & _ & _). cbn [mid_ctx M2] in CP3.
    assert (XSB3 : Forall (fun iv : Z * Z => snd iv <= aceil) XS3).
    { pose proof (fs_scratch_range_Forall H HH _ _ _ RFS2 FXS3) as K. eapply Forall_impl; [| exact K]. intros [u w] Ku. cbn in Ku |- *. lia. }
    assert (XB3 : Forall (fun iv : Z * Z => snd iv <= aceil) (memflag_foot ++ ctxph_foot (mid_ctx M) ++ XS3)).
    { apply Forall_below_app; [apply Forall_below_aimg; apply aimg_memflag|]. apply Forall_below_app; [apply Forall_below_aimg; apply aimg_ctxph_foot| exact XSB3]. }
    assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP3); [exact FR2| left; cbn; lia|]. eapply Forall_avoid_hi; [exact XB3| lia]. }
    (* [comment removed for export] *)
    assert (PAYB3 : forall pD, In (pD, D, N) LB -> Bmiss (memflag_foot ++ ctxph_foot (mid_ctx M) ++ XS3) D N).
    { intros pD PIN. pose proof (HB _ (in_or_app _ _ _ (or_intror PIN))) as (P1 & P2 & P3 & P4 & P5 & P6).
      apply BM_app; [apply BM_img; [apply aimg_memflag| exact P1| exact P3| exact P6]|].
      apply BM_app; [apply BM_img; [apply aimg_ctxph_foot| exact P1| exact P3| exact P6]|].
      exact (BM_xs s2' L1 m2 m2 XS3 (pD, D, N) HP2 ltac:(right; apply in_or_app; right; exact PIN) RFS2 FXS3). }
    assert (DS3 : bytes_at asegs m3 D ds) by (eapply DSX; [exact XP3| exact DS2| intros b Hb; right; apply in_or_app; right; exact Hb| exact PAYB3]).
    assert (AD3 : 1 <= N -> addressable m3 D N) by (intros N1; eapply ADX; [exact XP3| exact AD2| intros b Hb; right; apply in_or_app; right; exact Hb| exact PAYB3| exact N1]).
    assert (STK3 : stack0 m3 lo shi).
    { eapply (stack0_xpres H); [exact XP3| exact STK2|]. apply Forall_app; split; [apply stack0_ok_of_aimg; apply aimg_memflag|].
      apply Forall_app; split; [apply stack0_ok_of_aimg; apply aimg_ctxph_foot|].
      eapply Forall_impl; [| exact FXS3]. intros iv P. exact (fs_scratch_stack0_ok H HH _ _ _ RFS2 P). }
    assert (SBM3 : Bmiss (memflag_foot ++ ctxph_foot (mid_ctx M) ++ XS3) A STORE_SIZE).
    { apply BM_app; [apply BM_img; [apply aimg_memflag| unfold STORE_SIZE; lia| unfold STORE_SIZE; lia| exact AAP]|].
      apply BM_app; [apply BM_img; [apply aimg_ctxph_foot| unfold STORE_SIZE; lia| unfold STORE_SIZE; lia| exact AAP]|].
      exact (BM_xs s2' L1 m2 m2 XS3 sb HP2 (or_introl eq_refl) RFS2 FXS3). }
    assert (SO3 : STOREobj L2 m3 A (store_empty p)).
    { apply STOREobj_empty. apply STOREobj_empty in SO2. destruct SO2 as [SC2 _]. split; [| apply SUB12; left; reflexivity].
      exact (BX_cells L1 _ _ m2 m3 A _ sb XP3 SC2 (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; unfold STORE_SIZE; lia) SBM3). }
    assert (SSH3 : STORE_shad m3 A (store_empty p)).
    { apply STORE_shad_empty. apply STORE_shad_empty in SSH2. destruct SSH2 as [T1 T2]. split; [exact T1|].
      exact (BX_addr L1 _ _ m2 m3 sb XP3 T2 (or_introl eq_refl) SBM3). }
    (* [comment removed for export] *)
    pose proof MBO3 as (_ & _ & _ & _ & BI1x & BI2x & BI3x & BI4x & BR1 & BR2 & BR3 & BR4 & _).
    assert (BI1 : In (mb_id R, a, BIO_SIZE) L2) by (apply SUB3x; exact BI1x). assert (BI2 : In (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) L2) by (apply SUB3x; exact BI2x).
    assert (BI3 : In (mb_bmid R, mb_bm R, BUFMEM_SIZE) L2) by (apply SUB3x; exact BI3x). assert (BI4 : In (mb_rpid R, mb_rp R, BUFMEM_SIZE) L2) by (apply SUB3x; exact BI4x).
    clear BI1x BI2x BI3x BI4x.
    pose proof (MEMBIO_mono H _ _ _ _ _ MBO3 SUB3x) as MBO3'. clear MBO3. rename MBO3' into MBO3.
    pose proof (nd_app MB (LA ++ L1) ND2) as [DJM NDA1]. pose proof (nd_app LA L1 NDA1) as [DJA ND1].
    pose proof (nd_app [sb] L0 ND1) as [DJS ND0]. pose proof (nd_app E0 LB ND0) as [DJE NDB].
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply ap_seg3; [| exact MI3]|].
    { pose proof BR1 as (Q1 & _ & _ & _ & Q4 & _). unfold BIO_SIZE in Q4. lia. }
    intros msF5 mo5 KREL5 MP5 VIS5.
    (* [comment removed for export] *)
    set (LBr := MB ++ LA ++ sb :: LB).
    assert (PI1 : Permutation L2 (E0 ++ LBr)).
    { unfold L2, LBr, L1, L0. change (sb :: E0 ++ LB) with ([sb] ++ E0 ++ LB). change (sb :: LB) with ([sb] ++ LB).
      etransitivity; [apply Permutation_app_head; apply Permutation_app_head; apply Permutation_app_swap_app|].
      etransitivity; [apply Permutation_app_head; apply Permutation_app_swap_app|]. apply Permutation_app_swap_app. }
    assert (HP3r : as_RHEAP H s3' (mid_errblocks M2 ++ LBr) m3) by (cbn [mid_errblocks mid_E M2]; eapply PERM; [exact HP3| exact PI1]).
    assert (SUBr : forall b, In b (LA ++ LIB) -> In b LBr).
    { intros b Hb. unfold LBr. apply in_or_app. right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; apply SUBL; exact Hb]. }
    assert (SUB2r : forall b, In b L2 -> In b (E0 ++ LBr)) by (intros b Hb; eapply Permutation_in; [exact PI1| exact Hb]).
    assert (SUBr2 : forall b, In b (E0 ++ LBr) -> In b L2) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PI1| exact Hb]).
    assert (LBY0 : lb_bytes L0 = lb_bytes E0 + lb_bytes LB) by (unfold L0; apply lb_bytes_app_s).
    assert (LBC0 : length L0 = (length E0 + length LB)%nat) by (unfold L0; apply length_app).
    assert (BYr : lb_bytes (E0 ++ LBr) = MEMBIO_BYTES + lb_bytes LA + STORE_SIZE + lb_bytes E0 + lb_bytes LB).
    { rewrite <- (lb_bytes_perm_s _ _ PI1). unfold L2, L1, L0. rewrite !lb_bytes_app_s, lb_bytes_cons, lb_bytes_app_s. cbn [blk_size snd sb]. lia. }
    assert (CNr : length (E0 ++ LBr) = (4 + (length LA + S (length E0 + length LB)))%nat).
    { rewrite <- (Permutation_length PI1). unfold L2, L1, L0. rewrite !length_app. cbn [length]. rewrite length_app, MBL. reflexivity. }
    assert (NDsm : List.NoDup (map blk_id (sb :: MB))).
    { assert (P : Permutation L2 ((sb :: MB) ++ (LA ++ L0))).
      { unfold L2, L1. change (sb :: MB) with ([sb] ++ MB). change (sb :: L0) with ([sb] ++ L0).
        etransitivity; [apply Permutation_app_head; apply Permutation_app_swap_app| apply (Permutation_app_swap_app MB [sb] (LA ++ L0))]. }
      pose proof (Permutation_NoDup (Permutation_map blk_id P) ND2) as K. rewrite map_app in K. eapply NoDup_app_remove_r. exact K. }
    assert (SEP3 : MEMBIO_sep a R).
    { split; [exact APART|]. rewrite RBUF, RLEN.
      destruct (Z.eq_dec N 0) as [N0|N0].
      - rewrite N0, (DEMPTY N0). unfold P_FUZZ_EMPTY.
        destruct BR1 as (_ & _ & _ & O1 & _). destruct BR2 as (_ & _ & _ & O2 & _). destruct BR3 as (_ & _ & _ & O3 & _). destruct BR4 as (_ & _ & _ & O4 & _).
        unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, AIMG_TOP in *. lia.
      - destruct (DIN ltac:(lia)) as [pD [PIN _]].
        assert (PIN1 : In (pD, D, N) L1) by (right; apply in_or_app; right; exact PIN).
        assert (DJ : forall b, In b MB -> blk_addr b + blk_size b <= D \/ D + N <= blk_addr b).
        { intros b Hb. pose proof (ah_disj H HH _ _ _ b (pD, D, N) HP3 ltac:(unfold L2; apply in_or_app; left; exact Hb) (SUB12 _ PIN1)
                        (DJM _ _ Hb ltac:(apply in_or_app; right; exact PIN1))) as K. cbn [blk_addr blk_size fst snd] in K. lia. }
        pose proof (DJ _ ltac:(left; reflexivity)) as K1. pose proof (DJ _ ltac:(right; left; reflexivity)) as K2.
        pose proof (DJ _ ltac:(right; right; left; reflexivity)) as K3. pose proof (DJ _ ltac:(right; right; right; left; reflexivity)) as K4.
        cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4. lia. }
    assert (BEL3 : MEMBIO_below a R lo).
    { pose proof (HB2 _ BI1) as K1. pose proof (HB2 _ BI2) as K2. pose proof (HB2 _ BI3) as K3. pose proof (HB2 _ BI4) as K4.
      cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4. unfold MEMBIO_below. lia. }
    assert (DJ6 : forall b b', In b (LA ++ LIB) -> In b' (sb :: MB) -> blk_id b <> blk_id b').
    { intros b b' Hb Hb'. apply in_app_or in Hb.
      assert (HbL : In b LIB -> In b L0) by (intros K; unfold L0; apply in_or_app; right; exact (SUBL _ K)).
      destruct Hb' as [<-|Hb'].
      - destruct Hb as [Hb|Hb]; [exact (DJA _ _ Hb (or_introl eq_refl))| apply not_eq_sym; exact (DJS _ _ (or_introl eq_refl) (HbL Hb))].
      - apply not_eq_sym. apply (DJM _ _ Hb'). apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact (HbL Hb)]. }
    assert (DJP : 1 <= N -> exists pD, In (pD, D, N) LBr /\ forall b, In b (LA ++ LIB) -> blk_id b <> pD).
    { intros K. destruct (DIN K) as [pD [PIN PNL]]. exists pD. split; [unfold LBr; apply in_or_app; right; apply in_or_app; right; right; exact PIN|].
      intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (PNL _ Hb)].
      exact (DJA _ _ Hb (or_intror ltac:(unfold L0; apply in_or_app; right; exact PIN))). }
    assert (PSH3 : PAYLOAD_shad m3 R).
    { unfold PAYLOAD_shad. rewrite RBUF, RLEN. destruct (Z.eq_dec N 0) as [N0|N0].
      - rewrite N0, (DEMPTY N0). unfold P_FUZZ_EMPTY. rewrite Z.add_0_r. split; [apply accessible_nil; unfold AAPP_HI; lia|].
        split; [apply ACONST_shvis; [exact AC3| unfold AIMG_LO; lia| lia| unfold AIMG_TOP; lia]|]. unfold in_app_mem. rewrite ASHADOW_BASE_val. lia.
      - destruct (DIN ltac:(lia)) as [pD [PIN _]]. pose proof (HB2 _ (SUB12 _ ltac:(right; apply in_or_app; right; exact PIN))) as PR. cbn [blk_addr blk_size fst snd] in PR.
        destruct PR as (P1 & P2 & P3 & P4 & P5 & P6). pose proof (aapp_bounds D N P6 ltac:(lia)) as (_ & _ & AB3 & _).
        split; [eapply addressable_accessible; [exact (AD3 ltac:(lia))| lia| lia| lia]|].
        split; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HP3 (SUB12 _ ltac:(right; apply in_or_app; right; exact PIN)))|].
        eapply aapp_in_app_mem; [exact P6| lia| lia]. }
    assert (STK3' : stack0 m3 lo (bv_unsigned sp + -32)) by (eapply stack0_sub; [exact STK3| lia| lia| clear - SP16'; Z.div_mod_to_equations; lia]).
    pose proof RCFG as RC. unfold readcfg_stmt in RC.
    eapply (ah_seq H HH).
    { eapply RC with (lo := lo) (B := B) (LIB := LA ++ LIB) (LB := LBr) (M := M2) (x := x) (st := A) (mb := a) (S := store_empty p) (R := R) (ds := ds) (s := s3') (LF := LF) (CH := []);
        [exact VIS5| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by (unfold PO_R3, R_parse_one_OSSL_ECHSTORE_read_echconfiglist; lia).
      all: lazymatch goal with
           | |- STOREobj _ _ _ _ => apply STOREobj_empty; apply STOREobj_empty in SO3; destruct SO3 as [SC3 _]; split; [exact SC3| unfold LBr; apply in_or_app; right; apply in_or_app; right; left; reflexivity]
           | |- _ + STORE_SIZE <= _ => unfold STORE_SIZE; lia
           | |- MEMBIO _ _ _ _ _ => eapply (MEMBIO_frame0 H _ _ aceil); [exact MBO3| intros b Hb; unfold LBr; apply in_or_app; left; exact Hb| apply xpres_refl]
           | |- bytes_at _ _ _ _ => rewrite RBUF; exact DS3
           | |- zlength _ = _ => rewrite RLEN; exact DSL
           | |- 1 <= _ -> exists pD, _ => rewrite RBUF, RLEN; exact DJP
           | |- 1 <= _ -> forall pD, _ => rewrite RBUF, RLEN; cbn [es_id store_empty]; intros K pD Hp EQ; subst pD; unfold LBr, L1, L0 in Hp;
                 apply in_app_or in Hp; destruct Hp as [Hp|Hp]; [exact (DJM _ _ Hp ltac:(apply in_or_app; right; left; reflexivity) eq_refl)|];
                 apply in_app_or in Hp; destruct Hp as [Hp|Hp]; [exact (DJA _ _ Hp ltac:(left; reflexivity) eq_refl)|];
                 destruct Hp as [Hp|Hp]; [| exact (DJS _ _ ltac:(left; reflexivity) ltac:(unfold L0; apply in_or_app; right; exact Hp) eq_refl)];
                 destruct (DIN K) as [pD0 [PIN0 _]];
                 pose proof (ah_disj H HH _ _ _ sb (pD0, D, N) HP3 (SUB12 _ (or_introl eq_refl)) (SUB12 _ (or_intror (in_or_app _ _ _ (or_intror PIN0))))
                               (DJS _ _ ltac:(left; reflexivity) ltac:(unfold L0; apply in_or_app; right; exact PIN0))) as DD;
                 subst sb; injection Hp as E1 E2; cbn [blk_addr blk_size fst snd] in DD; unfold STORE_SIZE in *; clear - DD E1 E2 K; lia
           | |- lb_bytes _ + _ + _ + _ <= _ => unfold M2, mid_bytes; cbn [mid_errblocks mid_ctx mid_err mid_E ctxph_bytes]; change (blocks_ERRST (mid_E M)) with E0; rewrite BYr; unfold MEMBIO_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, STORE_SIZE, DECODE_BYTES, ERRSTR_BYTES; clear - BUD LBY0 NB1 PHB EHB; lia
           | |- Z.of_nat (length _) + _ + _ + _ <= _ => unfold M2, mid_cnt; cbn [mid_errblocks mid_ctx mid_err mid_E ctxph_cnt]; change (blocks_ERRST (mid_E M)) with E0; rewrite CNr; unfold DECODE_CNT, ERRSTR_CNT; clear - BUDC LBC0 NB2 PHC EHC; lia
           | |- _ <= _ - READCFG_STACK _ => pose proof (readcfg_stack_ready M 1 x (mid_E M) (mid_vdso M)) as K; clear - LO RSL NSK K; subst RS NS M2; lia
           | |- CTXPH _ _ _ => eapply (CTXPH_mono (LA ++ LIB) LBr SUBr); exact CP3
           | |- forall fp' ra', In (fp', ra') _ -> _ => intros fp' ra' []
           | |- pf_ok _ _ _ _ => unfold PO_R3; exact (proj1 (proj2 (PFC x)))
           | |- (length _ + _ <= _)%nat => unfold READCFG_LF; clear - LFB; lia
           | |- _ <= as_AL _ _ => unfold M2, READCFG_COST; cbn [mid_err]; clear - AL3 AL2 HAL PK1 PK2 PK3 PK4 PK5; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- as_chain _ _ _ _ => apply (ah_chain_nil H HH); left; lia
           | |- aauxv_ok _ _ => exact AUXA3
           | |- athr_cells _ => exact (ah_thr H HH _ _ _ HP3)
           | |- mid_closed_ok _ _ => exact CLO
           | |- _ => first [exact HP3r| exact KREL5| exact AUX3| exact ST3| exact CEIL| exact ERR3| exact MI3| reflexivity| exact SP16'| exact AC3| exact LM3| exact SUBr
                       | exact RPOS| exact RNRD| exact SEP3| exact BEL3| exact NDsm| exact DJ6| exact SSH3| exact MSH3| exact PSH3| exact STK3'| exact RFS3| exact BHI| lia
                       | match goal with |- ?G => idtac "LEFT3:" G end]
           end. }
    clear RC. intros [msF6 mo6] PO. unfold readcfg_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & errv4 & s4' & rv & M4 & S4 & R4 & LE & NB & XS4 &
                    VIS6 & RV01 & KREL6 & MP6 & MI4 & AC4 & ST4 & STK4 & ERR4 & AUX4 & HP4 & LM4 & STEP4 & NEW4 & CTX4 & SO4 & SSH4 & SID4 & PBS & NBC & NBB & EC4 & EB4
                    & NDS4 & MBO4 & MSH4 & MBEQ & DS4 & FXS4 & RFS4 & THR4 & XP4 & AL4).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST4, STK4, XP4 by lia. rewrite (unsigned_lit ATP) in ERR4 by (unfold ATP; lia).
    set (LB4 := NB ++ LE ++ LBr) in *. set (E4 := mid_errblocks M4) in *. set (F4 := E4 ++ LB4) in *.
    cbn [mid_ctx M2] in CTX4. cbn [mid_err M2] in XP4. unfold M2, READCFG_COST in AL4. cbn [mid_err] in AL4.
    assert (HB4 : forall b, In b F4 -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP4 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    assert (ND4 := ah_nodup H HH _ _ _ HP4).
    pose proof (nd_app E4 LB4 ND4) as [DJ4E ND4L]. pose proof (nd_app NB (LE ++ LBr) ND4L) as [DJ4N ND4M]. pose proof (nd_app LE LBr ND4M) as [DJ4L _].
    pose proof LM4 as (IM4 & MF4 & CP4 & EPm4 & _ & _ & _ & _ & GM4 & GE4 & _ & MM4 & _ & _ & RL4 & _). rewrite CTX4 in CP4.
    assert (F14 : mid_flag M4 = 1) by (destruct STEP4 as [F1 _]; exact F1). rewrite F14 in MF4.
    assert (SUBr4 : forall b, In b LBr -> In b F4) by (intros b Hb; unfold F4, LB4; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (SBIN4 : In sb F4) by (apply SUBr4; unfold LBr; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    assert (BSIN : forall b, In b (blocks_STORE A S4) -> In b F4).
    { intros b Hb. pose proof (Permutation_in _ PBS Hb) as K. cbn [es_id store_empty] in K. destruct K as [<-|K]; [exact SBIN4|].
      unfold F4, LB4. apply in_or_app. right. apply in_or_app. left. exact K. }
    assert (BSIN' : forall b, In b (blocks_STORE A S4) -> In b LB4).
    { intros b Hb. pose proof (Permutation_in _ PBS Hb) as K. cbn [es_id store_empty] in K. destruct K as [<-|K].
      - unfold LB4, LBr. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. left. reflexivity.
      - unfold LB4. apply in_or_app. left. exact K. }
    (* [comment removed for export] *)
    assert (NOTST : forall b, In b (LE ++ MB ++ LA ++ LB) -> ~ In b (blocks_STORE A S4)).
    { intros b Hb K. pose proof (Permutation_in _ PBS K) as K'. cbn [es_id store_empty] in K'.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - destruct K' as [<-|K']; [exact (idsdisj_notin _ _ _ DJ4L Hb ltac:(unfold LBr; apply in_or_app; right; apply in_or_app; right; left; reflexivity))|].
        exact (DJ4N _ _ K' ltac:(apply in_or_app; left; exact Hb) eq_refl).
      - assert (HbLBr : In b (MB ++ LA ++ L1)).
        { apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; apply in_or_app; right; exact Hb]. }
        destruct K' as [<-|K'].
        + apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (DJM _ _ Hb ltac:(apply in_or_app; right; left; reflexivity) eq_refl)|].
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (DJA _ _ Hb ltac:(left; reflexivity) eq_refl)|].
          exact (DJS _ _ ltac:(left; reflexivity) ltac:(unfold L0; apply in_or_app; right; exact Hb) eq_refl).
        + refine (DJ4N _ _ K' _ eq_refl). apply in_or_app. right. unfold LBr.
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; exact Hb]. }
    assert (NOTSTE : forall b, In b E4 -> ~ In b (blocks_STORE A S4)) by (intros b Hb K; exact (DJ4E _ _ Hb (BSIN' _ K) eq_refl)).
    (* [comment removed for export] *)
    assert (XSB4 : Forall (fun iv : Z * Z => snd iv <= aceil) XS4).
    { pose proof (fs_scratch_range_Forall H HH _ _ _ RFS3 FXS4) as K. eapply Forall_impl; [| exact K]. intros [u w] Ku. cbn in Ku |- *. lia. }
    assert (XB4 : Forall (fun iv : Z * Z => snd iv <= aceil) (XS4 ++ [(A, A + STORE_SIZE)] ++ MEMBIO_foot a R ++ ERR_XE ++ VDSO_X ++ errph_foot (mid_err M))).
    { apply Forall_below_app; [exact XSB4|]. apply Forall_below_app; [apply Forall_cons; [cbn [snd]; unfold STORE_SIZE; clear - ACE; lia| apply Forall_nil]|].
      apply Forall_below_app.
      { unfold MEMBIO_foot. destruct BR1 as (_ & _ & _ & _ & Q1 & _). destruct BR3 as (_ & _ & _ & _ & Q3 & _).
        apply Forall_cons; [cbn [snd]; exact Q1|]. apply Forall_cons; [cbn [snd]; exact Q3| apply Forall_nil]. }
      apply Forall_below_app; [apply Forall_below_aimg; apply aimg_ERR_XE|]. apply Forall_below_app; [apply Forall_below_aimg; apply aimg_VDSO_X|].
      eapply errph_foot_below; [exact EPm3| intros b Hb; exact (proj1 (proj2 (HB2 _ (SUBA2 _ Hb))))]. }
    assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact FR3| left; cbn; lia|]. eapply Forall_avoid_hi; [exact XB4| lia]. }
    rewrite RBUF in DS4.
    assert (EFB : forall pD, In (pD, D, N) LB -> Bmiss (errph_foot (mid_err M)) D N).
    { intros pD PIN. destruct (errph_foot_shape _ _ _ _ EPm0) as [E|(c & E & I5 & Z5)]; rewrite E; [apply BM_nil|].
      destruct (Z.eq_dec N 0) as [N0|N0]; [intros q K; rewrite N0; unfold nsh; cbn; lia|].
      destruct (DIN ltac:(lia)) as [pD' [PIN' PNL]].
      refine (BM_blk s3' L2 m3 (ec_es c) (pD, D, N) _ _ HP3 (SUBA2 _ ltac:(apply in_or_app; right; exact I5)) (SUB12 _ ltac:(right; apply in_or_app; right; exact PIN)) _ (Z.le_refl _) ltac:(rewrite Z5; apply Z.le_refl)).
      cbn [blk_id fst snd]. intros EQ. destruct (Z.eq_dec pD pD') as [->|NEQ]; [exact (PNL _ I5 EQ)|]. exfalso.
      pose proof (ah_disj H HH _ _ _ (pD, D, N) (pD', D, N) HP3 (SUB12 _ ltac:(right; apply in_or_app; right; exact PIN)) (SUB12 _ ltac:(right; apply in_or_app; right; exact PIN')) ltac:(cbn; exact NEQ)) as DD.
      cbn [blk_addr blk_size fst snd] in DD. lia. }
    (* [comment removed for export] *)
    assert (BM_cons : forall iv X A0 n0, Bmiss [iv] A0 n0 -> Bmiss X A0 n0 -> Bmiss (iv :: X) A0 n0).
    { intros iv X A0 n0 D1 D2 q K. cbn [rin_ivs] in K. destruct K as [K|K]; [exact (D1 q (or_introl K))| exact (D2 q K)]. }
    assert (XLT : forall X q, Forall (fun iv : Z * Z => snd iv <= aceil) X -> rin_ivs X q -> q < aceil).
    { intros X q FX K. destruct (rin_ivs_In _ _ K) as (iv & Hiv & Riv). pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as W. cbn beta in W. lia. }
    assert (PAYB4 : forall pD, In (pD, D, N) LB -> Bmiss (XS4 ++ [(A, A + STORE_SIZE)] ++ MEMBIO_foot a R ++ ERR_XE ++ VDSO_X ++ errph_foot (mid_err M)) D N).
    { intros pD PIN. pose proof (HB _ (in_or_app _ _ _ (or_intror PIN))) as (P1 & P2 & P3 & P4 & P5 & P6).
      assert (PIN2 : In (pD, D, N) L2) by (apply SUB12; right; apply in_or_app; right; exact PIN).
      assert (NEs : blk_id sb <> pD) by (exact (DJS _ _ (or_introl eq_refl) ltac:(unfold L0; apply in_or_app; right; exact PIN))).
      assert (NE1 : mb_id R <> pD) by (exact (DJM _ _ ltac:(left; reflexivity) ltac:(apply in_or_app; right; right; apply in_or_app; right; exact PIN))).
      assert (NE3 : mb_bmid R <> pD) by (exact (DJM _ _ ltac:(right; right; left; reflexivity) ltac:(apply in_or_app; right; right; apply in_or_app; right; exact PIN))).
      apply BM_app; [exact (BM_xs s3' L2 m3 m3 XS4 (pD, D, N) HP3 PIN2 RFS3 FXS4)|].
      apply BM_app; [exact (BM_blk s3' L2 m3 sb (pD, D, N) A (A + STORE_SIZE) HP3 (SUB12 _ (or_introl eq_refl)) PIN2 NEs (Z.le_refl _) (Z.le_refl _))|].
      apply BM_app.
      { unfold MEMBIO_foot. apply BM_cons; [| apply BM_cons; [| apply BM_nil]].
        - exact (BM_blk s3' L2 m3 (mb_id R, a, BIO_SIZE) (pD, D, N) a (a + BIO_SIZE) HP3 BI1 PIN2 NE1 (Z.le_refl _) (Z.le_refl _)).
        - exact (BM_blk s3' L2 m3 (mb_bmid R, mb_bm R, BUFMEM_SIZE) (pD, D, N) (mb_bm R) (mb_bm R + BUFMEM_SIZE) HP3 BI3 PIN2 NE3 (Z.le_refl _) (Z.le_refl _)). }
      apply BM_app; [apply BM_img; [apply aimg_ERR_XE| exact P1| exact P3| exact P6]|].
      apply BM_app; [apply BM_img; [apply aimg_VDSO_X| exact P1| exact P3| exact P6]|].
      exact (EFB pD PIN). }
    assert (AD4 : 1 <= N -> addressable m4 D N).
    { intros N1. eapply ADX; [exact XP4| exact AD3| intros b Hb; unfold LBr; apply in_or_app; right; apply in_or_app; right; right; exact Hb| exact PAYB4| exact N1]. }
    assert (STK4f : stack0 m4 lo shi).
    { eapply (stack0_xpres H); [exact XP4| exact STK3|].
      apply Forall_app; split; [eapply Forall_impl; [| exact FXS4]; intros iv P; exact (fs_scratch_stack0_ok H HH _ _ _ RFS3 P)|].
      apply Forall_app; split; [apply Forall_cons; [eapply stack0_ok_aapp; [exact AAP| apply Z.le_refl| unfold STORE_SIZE; apply Z.le_refl]| apply Forall_nil]|].
      apply Forall_app; split.
      { unfold MEMBIO_foot. destruct (HB2 _ BI1) as (_ & _ & _ & _ & _ & Q1). destruct (HB2 _ BI3) as (_ & _ & _ & _ & _ & Q3). cbn [blk_addr blk_size fst snd] in Q1, Q3.
        apply Forall_cons; [eapply stack0_ok_aapp; [exact Q1| apply Z.le_refl| apply Z.le_refl]|].
        apply Forall_cons; [eapply stack0_ok_aapp; [exact Q3| apply Z.le_refl| apply Z.le_refl]| apply Forall_nil]. }
      apply Forall_app; split; [apply stack0_ok_of_aimg; apply aimg_ERR_XE|].
      apply Forall_app; split; [apply stack0_ok_of_aimg; apply aimg_VDSO_X|].
      destruct (errph_foot_shape _ _ _ _ EPm0) as [E|(c & E & I5 & Z5)]; rewrite E; [apply Forall_nil|].
      destruct (HB2 _ (SUBA2 _ ltac:(apply in_or_app; right; exact I5))) as (_ & _ & _ & _ & _ & Q5).
      apply Forall_cons; [eapply stack0_ok_aapp; [exact Q5| apply Z.le_refl| rewrite Z5; apply Z.le_refl]| apply Forall_nil]. }
    assert (CH2 : as_chain H m2 (bv_unsigned s0) CH).
    { eapply (chain_via_xpres H HH); [exact CH1| exact XP2| intros fp' ra' IN; pose proof (CHS _ _ IN); lia|].
      intros q K. exact (XLT _ _ (Forall_below_aimg _ aimg_memflag) K). }
    assert (CH3 : as_chain H m3 (bv_unsigned s0) CH).
    { eapply (chain_via_xpres H HH); [exact CH2| exact XP3| intros fp' ra' IN; pose proof (CHS _ _ IN); lia|]. intros q K. exact (XLT _ _ XB3 K). }
    assert (CH4 : as_chain H m4 (bv_unsigned s0) CH).
    { eapply (chain_via_xpres H HH); [exact CH3| exact XP4| intros fp' ra' IN; pose proof (CHS _ _ IN); lia|]. intros q K. exact (XLT _ _ XB4 K). }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply ap_seg4; exact MI4|].
    intros msF7 mo7 KREL7 MP7 VIS7.
    (* [comment removed for export] *)
    assert (FNN : Forall (fun b => 0 <= blk_size b) (blocks_STORE A S4)).
    { apply Forall_forall. intros b Hb. exact (proj1 (proj2 (proj2 (HB4 _ (BSIN _ Hb))))). }
    assert (SCB : store_cost H S4 <= as_Cf H (STORE_SIZE + 2 ^ 17)).
    { etransitivity; [eapply (store_cost_bound H HH); [exact SO4| exact FNN]|].
      apply (Cf_mono H HH). split; [apply lb_bytes_nonneg_s; exact FNN|].
      rewrite (lb_bytes_perm_s _ _ PBS), lb_bytes_cons. cbn [blk_size snd]. unfold DECODE_BYTES in NBB. clear - NBB. unfold STORE_SIZE. lia. }
    pose proof (astorefree_spec H HH) as SF. unfold storefree_stmt, efree_stmt_at in SF.
    eapply (ah_seq H HH).
    { eapply SF with (lo := lo) (B := B) (LB := F4) (s := s4') (p := A) (x := S4) (errv := errv4) (CH := []);
        [exact VIS7| reflexivity| ..]; rewrite ?unsigned_lit by (unfold PO_R4, R_parse_one_OSSL_ECHSTORE_free; lia).
      all: lazymatch goal with
           | |- STOREobj _ _ _ _ => eapply (STOREobj_frame_law H); [exact SO4| exact BSIN| apply xpres_refl| intros b Hb; exact (proj1 (proj2 (HB4 _ (BSIN _ Hb))))]
           | |- _ <= _ - STOREFREE_STACK => clear - LO NSK RSL; lia
           | |- forall fp' ra', In (fp', ra') _ -> _ => intros fp' ra' []
           | |- pf_ok _ _ _ _ => unfold PO_R4; exact (proj2 (proj2 (PFC cx_dummy)))
           | |- _ <= as_AL _ _ => clear - AL4 AL3 AL2 HAL PK1 PK2 PK3 PK4 PK5 SCB; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- as_chain _ _ _ _ => apply (ah_chain_nil H HH); left; lia
           | |- _ => first [exact SSH4| exact NDS4| exact HP4| exact KREL7| exact AUX4| exact ST4| exact CEIL| exact ERR4| exact MI4| reflexivity| exact SP16'| exact AC4
                       | exact IM4| exact GM4| exact GE4| lia | match goal with |- ?G => idtac "LEFT4:" G end]
           end. }
    clear SF. intros [msF8 mo8] PO. unfold efree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m5 & s5' & LB5 &
                    VIS8 & KREL8 & MP8 & MI5 & AC5 & ST5 & ERR5 & AUX5 & PERM5 & HP5 & XP5 & IM5 & GM5 & GE5 & AL5).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST5, XP5 by lia. rewrite (unsigned_lit ATP) in ERR5 by (unfold ATP; lia).
    assert (KEEP5 : forall b, In b (LE ++ MB ++ LA ++ LB) -> In b LB5).
    { intros b Hb. eapply perm_in_rest_s; [exact PERM5| | exact (NOTST _ Hb)].
      unfold F4, LB4, LBr. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb|].
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; exact Hb]. }
    assert (SUB5 : forall b, In b (LE ++ LA ++ LIB) -> In b LB5).
    { intros b Hb. apply KEEP5. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right; apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb]. }
    assert (KEEPE5 : forall b, In b E4 -> In b LB5).
    { intros b Hb. eapply perm_in_rest_s; [exact PERM5| unfold F4; apply in_or_app; left; exact Hb| exact (NOTSTE _ Hb)]. }
    assert (HB5 : forall b, In b LB5 -> AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ 0 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP5 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). repeat split; try assumption; lia. }
    pose proof (LIBMID_xpres0 H (LE ++ LA ++ LIB) LB5 (bv_unsigned sp + -32) m4 m5 M4 x LM4 CTX4 XP5 SUB5 KEEPE5) as LM5.
    pose proof LM5 as (_ & MF5 & CP5 & EPm5 & _ & _ & _ & _ & _ & _ & _ & MM5 & _ & _ & RL5 & _). rewrite CTX4 in CP5. rewrite F14 in MF5.
    assert (FR5 : rw_cells asegs m5 (bv_unsigned sp + -32) (ap_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP5); [exact FR4| left; cbn; lia| apply Forall_nil]. }
    assert (DS5 : bytes_at asegs m5 D ds).
    { eapply DSX; [exact XP5| exact DS4| intros b Hb; apply KEEP5; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb| intros pD _; apply BM_nil]. }
    assert (AD5 : 1 <= N -> addressable m5 D N).
    { intros N1. eapply ADX; [exact XP5| exact AD4| intros b Hb; apply KEEP5; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb| intros pD _; apply BM_nil| exact N1]. }
    assert (STK5 : stack0 m5 lo shi) by (eapply (stack0_xpres H); [exact XP5| exact STK4f| apply Forall_nil]).
    assert (RFS5 : as_RFS H LF m5) by (eapply (RFS_via_xpres H HH); [exact RFS4| exact XP5| apply Forall_nil]).
    assert (CH5 : as_chain H m5 (bv_unsigned s0) CH).
    { eapply (chain_via_xpres H HH); [exact CH4| exact XP5| intros fp' ra' IN; pose proof (CHS _ _ IN); lia|]. intros q []. }
    assert (MBIN5 : forall b, In b (blocks_MEMBIO a R4) -> In b LB5) by (intros b Hb; rewrite MBEQ in Hb; apply KEEP5; apply in_or_app; right; apply in_or_app; left; exact Hb).
    assert (MBO5 : MEMBIO H LB5 m5 a R4) by (eapply (MEMBIO_frame0 H); [exact MBO4| exact MBIN5| exact XP5]).
    assert (MSH5 : MEMBIO_shad m5 a R4).
    { destruct MSH4 as (T1 & T2 & T3 & T4).
      split; [exact (BX_addr LB5 _ _ m4 m5 (mb_id R4, a, BIO_SIZE) XP5 T1 (MBIN5 _ ltac:(left; reflexivity)) (BM_nil _ _))|].
      split; [exact (BX_addr LB5 _ _ m4 m5 (mb_bbid R4, mb_bb R4, BIOBUFMEM_SIZE) XP5 T2 (MBIN5 _ ltac:(right; left; reflexivity)) (BM_nil _ _))|].
      split; [exact (BX_addr LB5 _ _ m4 m5 (mb_bmid R4, mb_bm R4, BUFMEM_SIZE) XP5 T3 (MBIN5 _ ltac:(right; right; left; reflexivity)) (BM_nil _ _))|].
      exact (BX_addr LB5 _ _ m4 m5 (mb_rpid R4, mb_rp R4, BUFMEM_SIZE) XP5 T4 (MBIN5 _ ltac:(right; right; right; left; reflexivity)) (BM_nil _ _)). }
    assert (APART4 : MEMBIO_apart a R4).
    { pose proof MBEQ as MBEQ'. unfold blocks_MEMBIO in MBEQ'. injection MBEQ' as E1 E2 E3 E4' E5 E6 E7. unfold MEMBIO_apart in *. rewrite E3, E5, E7. exact APART. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply ap_seg5 with (lo := lo); [exact FR5| exact ST5| exact CEIL| lia| exact MI5]|].
    intros msF9 mo9 KREL9 MP9 [VIS9 ST5r].
    (* [comment removed for export] *)
    pose proof (abiofree_spec H HH CFX) as BF. unfold biofree_mem_stmt in BF.
    eapply (ah_seq H HH).
    { eapply BF with (lo := lo) (B := B) (LB := LB5) (s := s5') (a := a) (R := R4) (x := x) (errv := errv4) (LF := LF) (CH := CH);
        [exact VIS9| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ATP; lia).
      all: lazymatch goal with
           | |- stack0 _ _ _ => eapply stack0_sub; [exact STK5| clear; lia| clear - SSH SPR LO NSK RSL; lia| clear - SPA SPR; Z.div_mod_to_equations; lia]
           | |- CTXPH _ _ _ => eapply (CTXPH_mono (LE ++ LA ++ LIB) LB5 SUB5); exact CP5
           | |- _ <= _ - BIOFREE_STACK => clear - LO NSK RSL; lia
           | |- forall fp' ra', In (fp', ra') _ -> _ => exact CHS
           | |- pf_ok _ _ _ _ => exact PFB
           | |- (length _ < _)%nat => unfold READCFG_MAXLIVE, AFS_MAXLIVE in *; clear - LFB; lia
           | |- _ <= as_AL _ _ => clear - AL5 AL4 AL3 AL2 HAL PK1 PK2 PK3 PK4 PK5 SCB; lia
           | |- _ mod 2 = 0 => exact RAE
           | |- as_chain _ _ _ _ => exact CH5
           | |- _ => first [exact MBO5| exact APART4| exact MSH5| exact HP5| exact KREL9| exact AUX5| exact SPB| exact SPA| exact ST5r| exact CEIL| exact ERR5| exact MI5| reflexivity| exact AC5
                       | exact MF5| exact IM5| exact GM5| exact MM5| exact RL5| exact RFS5| lia | match goal with |- ?G => idtac "LEFT5:" G end]
           end. }
    clear BF. intros [msF10 mo10] PO. unfold biofree_mem_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m6 & errv6 & s6' & LBr6 & XS6 &
                    VIS10 & MP10 & KREL10 & MI6 & AC6 & ST6 & ERR6 & AUX6 & HP6 & PERM6 & MF6 & IM6 & GM6 & MM6 & RL6 & CP6 & STK6 & FXS6 & RFS6 & XP6 & AL6).
    rewrite MBEQ in PERM6. change (blocks_MEMBIO a R) with MB in PERM6.
    assert (KEEP6 : forall b, In b (LE ++ LA ++ LB) -> In b LBr6).
    { intros b Hb. eapply perm_in_rest_s; [apply Permutation_sym; exact PERM6| |].
      - apply KEEP5. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; right; exact Hb].
      - intros K. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        + exact (DJ4L _ _ Hb ltac:(unfold LBr; apply in_or_app; left; exact K) eq_refl).
        + refine (DJM _ _ K _ eq_refl). apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; apply in_or_app; right; exact Hb]. }
    assert (SUB6 : forall b, In b (LE ++ LA ++ LIB) -> In b LBr6).
    { intros b Hb. apply KEEP6. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb]. }
    assert (KEEPE6 : forall b, In b E4 -> In b LBr6).
    { intros b Hb. eapply perm_in_rest_s; [apply Permutation_sym; exact PERM6| exact (KEEPE5 _ Hb)|].
      intros K. exact (DJ4E _ _ Hb ltac:(unfold LB4, LBr; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact K) eq_refl). }
    (* [comment removed for export] *)
    assert (XP6' : xpres H LBr6 (bv_unsigned sp) XS6 m5 m6).
    { eapply xpres_drop_same; [exact XP6|]. intros q Hq. unfold mutex_foot in Hq. cbn [rin_ivs fst snd] in Hq. destruct Hq as [Hq|[]].
      destruct CP5 as [_ [EX5 _]]. destruct CP6 as [_ [EX6 _]]. destruct EX5 as (I5 & Z5 & _ & MU5). destruct EX6 as (_ & _ & _ & MU6).
      pose proof (HB5 _ (SUB5 _ I5)) as (Q1 & Q2 & _). rewrite Z5 in Q2. unfold MUTEX_SIZE in Q2. pose proof aceil_range as ACR.
      eapply (rw_cells_same_raw_hi m5 m6 _ _ q MU5 MU6); [exact Q1| cbn; lia| cbn; lia]. }
    pose proof (LIBMID_xs H HH s6' m6 (LE ++ LA ++ LIB) LBr6 (bv_unsigned sp) XS6 LF m5 m6 M4 x HP6 RFS5 FXS6 LM5 CTX4 XP6' SUB6 KEEPE6) as LM6.
    assert (STK6f : stack0 m6 lo shi).
    { eapply (stack0_xpres H); [exact XP6'| exact STK5|]. eapply Forall_impl; [| exact FXS6]. intros iv P. exact (fs_scratch_stack0_ok H HH _ _ _ RFS5 P). }
    assert (PAYB6 : forall pD, In (pD, D, N) LB -> Bmiss XS6 D N).
    { intros pD PIN. exact (BM_xs s5' LB5 m5 m5 XS6 (pD, D, N) HP5 (KEEP5 _ ltac:(apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact PIN)) RFS5 FXS6). }
    assert (DS6 : bytes_at asegs m6 D ds) by (eapply DSX; [exact XP6'| exact DS5| intros b Hb; apply KEEP6; apply in_or_app; right; apply in_or_app; right; exact Hb| exact PAYB6]).
    assert (AD6 : 1 <= N -> addressable m6 D N) by (intros N1; eapply ADX; [exact XP6'| exact AD5| intros b Hb; apply KEEP6; apply in_or_app; right; apply in_or_app; right; exact Hb| exact PAYB6| exact N1]).
    (* [comment removed for export] *)
    cbn [es_id store_empty] in PBS. change (p, A, STORE_SIZE) with sb in PBS.
    assert (P5 : Permutation LB5 (E4 ++ LE ++ MB ++ LA ++ LB)).
    { apply (Permutation_app_inv_l (sb :: NB)). transitivity F4.
      - transitivity (blocks_STORE A S4 ++ LB5); [apply Permutation_app_tail; symmetry; exact PBS| exact PERM5].
      - unfold F4, LB4, LBr. apply perm7. }
    assert (P6 : Permutation LBr6 (E4 ++ LE ++ LA ++ LB)).
    { apply (Permutation_app_inv_l MB). transitivity LB5; [symmetry; exact PERM6|]. transitivity (E4 ++ LE ++ MB ++ LA ++ LB); [exact P5| apply perm5]. }
    (* [comment removed for export] *)
    set (BIG := memflag_foot ++ CTX_X ++ ERR_XE ++ VDSO_X ++ errph_foot (mid_err M) ++ (XS3 ++ XS4 ++ XS6)).
    assert (INERR : forall q, rin_ivs AERRNO_X q -> rin_ivs ERR_XE q).
    { intros q K. unfold ERR_XE. apply rin_ivs_app. left. unfold AERRNO_X in K. unfold ERRNO_X, ARERRNO. cbn [rin_ivs fst snd] in K |- *. unfold ATP in *. lia. }
    assert (CTXF : forall q, rin_ivs (ctxph_foot (mid_ctx M)) q -> rin_ivs BIG q).
    { intros q K. apply rin_ivs_ctxph_foot in K. apply rin_ivs_app in K. unfold BIG. apply rin_ivs_app; right. apply rin_ivs_app.
      destruct K as [K|K]; [left; exact K| right]. apply rin_ivs_app; left. exact (INERR q K). }
    assert (DJMB : forall hb, In hb MB -> idsdisj [hb] LB).
    { intros hb Hhb b b' Hb Hb'. destruct Hb as [<-|[]]. apply DJM; [exact Hhb|]. apply in_or_app; right. right. apply in_or_app; right. exact Hb'. }
    assert (SUBLB2 : forall b, In b LB -> In b L2) by (intros b Hb; apply SUB12; right; apply in_or_app; right; exact Hb).
    assert (XP4' : xpres H LB (bv_unsigned sp) (BIG ++ ([(A, A + STORE_SIZE)] ++ MEMBIO_foot a R)) m3 m4).
    { eapply xpres_weaken; [exact XP4| lia| intros b Hb; unfold LBr; apply in_or_app; right; apply in_or_app; right; right; exact Hb|].
      intros q Hq. unfold BIG. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; do 5 (apply rin_ivs_app; right); apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq|].
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq|].
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; right; apply rin_ivs_app; right; exact Hq|].
      apply rin_ivs_app; left. apply rin_ivs_app; right. apply rin_ivs_app; right.
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq|]. apply rin_ivs_app; right.
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq|]. apply rin_ivs_app; right. apply rin_ivs_app; left. exact Hq. }
    assert (XP4'' : xpres H LB (bv_unsigned sp) BIG m3 m4).
    { eapply (xpres_drop_nonclient H); [exact XP4'|]. intros q Hq HC. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq].
      { cbn [rin_ivs fst snd] in Hq. destruct Hq as [Hq|[]].
        pose proof (client_outside_block H HH _ _ _ sb LB (bv_unsigned sp) q HP3 (SUB12 _ (or_introl eq_refl)) SUBLB2
                      ltac:(intros b0 b' Hb0 Hb'; apply DJS; [exact Hb0| unfold L0; apply in_or_app; right; exact Hb']) ltac:(lia) HC) as K.
        cbv delta [sb] in K. cbn [blk_addr blk_size fst snd] in K. unfold STORE_SIZE in *. lia. }
      unfold MEMBIO_foot in Hq. cbn [rin_ivs fst snd] in Hq.
      destruct Hq as [Hq|[Hq|[]]].
      - pose proof (client_outside_block H HH _ _ _ (mb_id R, a, BIO_SIZE) LB (bv_unsigned sp) q HP3 BI1 SUBLB2 (DJMB _ ltac:(left; reflexivity)) ltac:(lia) HC) as K.
        cbn [blk_addr blk_size fst snd] in K. lia.
      - pose proof (client_outside_block H HH _ _ _ (mb_bmid R, mb_bm R, BUFMEM_SIZE) LB (bv_unsigned sp) q HP3 BI3 SUBLB2 (DJMB _ ltac:(right; right; left; reflexivity)) ltac:(lia) HC) as K.
        cbn [blk_addr blk_size fst snd] in K. lia. }
    assert (XPF : xpres H LB (bv_unsigned sp) BIG m m6).
    { eapply xpres_trans; [eapply xpres_weaken; [exact XP1| lia| intros b Hb; unfold L0; apply in_or_app; right; exact Hb| intros q Hq; destruct Hq]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| intros b Hb; unfold L0; apply in_or_app; right; exact Hb| intros q Hq; unfold BIG; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans.
      { eapply xpres_weaken; [exact XP3| lia| intros b Hb; unfold L1, L0; right; apply in_or_app; right; exact Hb|].
        intros q Hq. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [unfold BIG; apply rin_ivs_app; left; exact Hq|].
        apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [exact (CTXF q Hq)|].
        unfold BIG. do 5 (apply rin_ivs_app; right). apply rin_ivs_app; left. exact Hq. }
      eapply xpres_trans; [exact XP4''|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP5| lia| intros b Hb; apply KEEP5; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb| intros q Hq; destruct Hq]|].
      eapply xpres_weaken; [exact XP6'| lia| intros b Hb; apply KEEP6; apply in_or_app; right; apply in_or_app; right; exact Hb|].
      intros q Hq. unfold BIG. do 5 (apply rin_ivs_app; right). apply rin_ivs_app; right. apply rin_ivs_app; right. exact Hq. }
    apply (ah_done H HH). unfold parse_one_post. cbn [cfg_ms cfg_model].
    exists z0, z1, z2, (Z_to_bv 64 1), f1, f2, f3, f4, f5, f6, f7, z3, z4, z5, z6, m6, errv6, s6', M4, (LE ++ LA), (XS3 ++ XS4 ++ XS6).
    split; [exact VIS10|]. split; [exact KREL10|].
    split; [eapply (ah_mpres_trans H HH); [exact MP1| eapply (ah_mpres_trans H HH); [exact MP2| eapply (ah_mpres_trans H HH); [exact MP3| eapply (ah_mpres_trans H HH); [exact MP4|
           eapply (ah_mpres_trans H HH); [exact MP5| eapply (ah_mpres_trans H HH); [exact MP6| eapply (ah_mpres_trans H HH); [exact MP7| eapply (ah_mpres_trans H HH); [exact MP8|
           eapply (ah_mpres_trans H HH); [exact MP9| exact MP10]]]]]]]]]|].
    split; [exact MI6|]. split; [exact AC6|]. split; [exact RL6|]. split; [exact ST6|]. split; [exact STK6f|]. split; [exact ERR6|]. split; [exact AUX6|].
    split; [eapply PERM; [exact HP6|]; rewrite <- ?app_assoc; exact P6|].
    split; [rewrite <- ?app_assoc; exact LM6|].
    split. { unfold mid_step in STEP4 |- *. unfold M2 in STEP4. cbn [mid_flag mid_ctx mid_err mid_vdso] in STEP4. destruct STEP4 as (F1 & C1 & E1 & V1).
             split; [exact F1|]. split; [| split; [exact E1| exact V1]].
             intros b Hb. rewrite CTX4. rewrite Hb in DELTA. cbn [ctxph_delta] in DELTA. destruct DELTA as [-> _]. reflexivity. }
    split. { unfold mid_newlib_ok in NEW4 |- *. unfold M2 in NEW4. cbn [mid_ctx mid_err] in NEW4. destruct NEW4 as (LA2 & LE2 & PN & CN & EN).
             try rewrite CTX4 in CN. cbn in CN. subst LA2. cbn [app] in PN.
             exists LA, LE2. split; [transitivity (LA ++ LE); [apply Permutation_app_comm| apply Permutation_app_head; exact PN]|].
             split; [| exact EN]. rewrite CTX4. clear - DELTA. revert DELTA. destruct (mid_ctx M) as [|b0]; intros DELTA; cbn [ctxph_delta] in DELTA |- *; [exact DELTA|].
             destruct DELTA as [_ E]. exact E. }
    split; [exists x; exact CTX4|].
    split; [exact EC4|]. split; [exact EB4|].
    split; [exact DS6|]. split; [exact AD6|].
    split; [apply Forall_app; split; [exact FXS3| apply Forall_app; split; [exact FXS4| exact FXS6]]|].
    split; [exact RFS6|].
    split; [exact XPF|].
    unfold PARSE_COST, READCFG_COST, DECODE_BYTES. clear - AL2 AL3 AL4 AL5 AL6 SCB PK1 PK2 PK3 PK4 PK5 HAL. lia.
  Qed.
End W.

Print Assumptions parse_one_spec.
