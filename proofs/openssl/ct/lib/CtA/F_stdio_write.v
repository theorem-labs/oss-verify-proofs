(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import FX_Stdio_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros l. unfold to_bytes. apply length_map. Qed.

Lemma to_bytes_zdrop : forall k l, to_bytes (zdrop k l) = skipn (Z.to_nat k) (to_bytes l).
Proof. intros k l. unfold to_bytes, zdrop. rewrite skipn_map. reflexivity. Qed.

Lemma zlength_app' : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros A a b. unfold zlength. rewrite app_length. lia. Qed.

Lemma iov_total_1 : forall a, iov_total [a] = zlength a.
Proof. intros a. unfold iov_total. cbn [concat]. rewrite app_nil_r. reflexivity. Qed.

Lemma iov_total_2 : forall a b, iov_total [a; b] = zlength a + zlength b.
Proof. intros a b. unfold iov_total. cbn [concat]. rewrite app_nil_r. apply zlength_app'. Qed.

Lemma iov_start_cons : forall (b s : list Z), b <> [] -> iov_start b s = [b; s].
Proof. intros b s H. destruct b; [congruence| reflexivity]. Qed.

Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros A l. unfold zlength. lia. Qed.

Lemma bytes_at_skip : forall m A bs k,
  bytes_at ctasegs m A bs -> (k <= length bs)%nat ->
  bytes_at ctasegs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k H Hk. rewrite <- (firstn_skipn k bs) in H.
  apply bytes_at_app in H. destruct H as [_ H]. rewrite firstn_length, Nat.min_l in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply swrap32_small. lia.
Qed.

Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Ltac if_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb ?x ?x) then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv beta iota delta [negb]
  end.

Section StdioWriteProof.
  Context {St : Type}.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (st : St)
            (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
            (buf s : list Z) (S lo : Z) (canary : word).
  Notation usp := (bv_unsigned sp).
  Notation l := (zlength s).
  Notation POST := (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                                    (zlength s) lo canary m0 st).
  (* [comment removed for export] *)
  Notation W := [(usp - 112, usp); (Fp + 32, Fp + 64)].
  Notation WF := [(usp - 112, usp)].

  Hypothesis FD : fd = 1 \/ fd = 2.
  Hypothesis LO : lo <= usp - 112.
  Hypothesis GLO : 0xbcb000 <= lo.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis B0 : 0 <= B.
  Hypothesis BS0 : 0 <= bufsize.
  Hypothesis BUFLE : zlength buf <= bufsize.
  Hypothesis BShi : B + bufsize < 2^64.
  Hypothesis LENS : zlength buf + zlength s <= 2^26.
  Hypothesis S0 : 0 <= S < 2^64.
  Hypothesis Shi : S + zlength s <= 2^64.
  Hypothesis SEPS : s = [] \/ ((S + zlength s <= lo \/ usp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S)).
  Hypothesis SEPB : B + zlength buf <= lo \/ usp <= B.
  Hypothesis BUFB0 : bytes_at ctasegs m0 B (to_bytes buf).
  Hypothesis SRC0 : bytes_at ctasegs m0 S (to_bytes s).
  (* [comment removed for export] *)
  Hypothesis SNIL : S = 0 \/ 0 < zlength s.
  Hypothesis SPHI : usp < 2^64.

  (* [comment removed for export] *)
  Definition src_ok (A : Z) (a : list Z) : Prop :=
    bytes_at ctasegs m0 A (to_bytes a) /\ (a = [] \/ A + zlength a <= lo \/ usp <= A)
    /\ A + zlength a <= UTOP.   (* [comment removed for export] *)

  Lemma src_ok_now : forall m A a, src_ok A a -> munch WF m0 m -> bytes_at ctasegs m A (to_bytes a).
  Proof.
    intros m A a (BA & SEP & _) MU.
    pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_to_bytes in BB.
    destruct SEP as [-> | SEP].
    - apply bytes_at_nil. cbn in BB. lia.
    - eapply bytes_at_transport; [exact BA | exact MU |].
      cbn [disjoint_from]. rewrite length_to_bytes. unfold zlength in SEP. split; [lia | exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma src_ok_now' : forall m A a, src_ok A a -> munch WF m0 m ->
    bytes_at ctasegs m (bv_unsigned (Z_to_bv 64 A)) (to_bytes a).
  Proof.
    intros m A a OK MU. pose proof (bytes_at_bound _ _ _ _ (proj1 OK)) as BB. rewrite length_to_bytes in BB.
    destruct a as [|x a'].
    - apply bytes_at_nil. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 A)) as R. unfold bv_modulus in R. cbn in R. lia.
    - cbn [length] in BB. rewrite unsigned_lit by lia. apply src_ok_now; assumption.
  Qed.

  Lemma src_ok_drop : forall A a k, src_ok A a -> 0 <= k <= zlength a -> src_ok (A + k) (zdrop k a).
  Proof.
    intros A a k (BA & SEP & TOP) Hk. split; [|split].
    - rewrite to_bytes_zdrop. replace (A + k) with (A + Z.of_nat (Z.to_nat k)) by lia.
      apply bytes_at_skip; [exact BA|]. rewrite length_to_bytes. unfold zlength in Hk. lia.
    - destruct SEP as [-> | SEP].
      + left. unfold zdrop. rewrite skipn_nil. reflexivity.
      + right. rewrite zlength_zdrop by lia. lia.
    - rewrite zlength_zdrop by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma src_ok_buf : mem_inv ctasegs m0 -> buf <> [] -> src_ok B buf.
  Proof.
    intros MI NE. split; [exact BUFB0 | split; [right; exact SEPB|]].
    pose proof (bytes_at_below _ _ _ _ MI BUFB0 ltac:(intros E; apply NE; destruct buf; [reflexivity| discriminate])) as T.
    rewrite length_to_bytes in T. unfold zlength. exact T.
  Qed.

  Lemma src_ok_s : mem_inv ctasegs m0 -> src_ok S s.
  Proof.
    intros MI. split; [exact SRC0 | split].
    - destruct SEPS as [E | [H _]]; [left; exact E | right; exact H].
    - destruct s as [|c s'] eqn:Es.
      + unfold zlength, UTOP in *. cbn [length Z.of_nat] in *. lia.
      + pose proof (bytes_at_below _ _ _ _ MI SRC0 ltac:(discriminate)) as T.
        rewrite length_to_bytes in T. unfold zlength. exact T.
  Qed.

  (* [comment removed for export] *)
  Lemma src_ok_top : forall A a, src_ok A a ->
    bv_unsigned (Z_to_bv 64 A) + Z.of_nat (length (to_bytes a)) <= 0x800000000000.
  Proof.
    intros A a (BA & _ & TOP). pose proof (bytes_at_bound _ _ _ _ BA) as BB.
    unfold zlength, UTOP in TOP. rewrite length_to_bytes in *. rewrite unsigned_lit by lia. lia.
  Qed.


  (* [comment removed for export] *)
  Definition frame (j : list byte) (b0 l0 b1 l1 : word) : list cell :=
    [CB 8 j; C8 b0; C8 l0; C8 b1; C8 l1; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition iov_desc (iovs : list (list Z)) (b0 l0 b1 l1 : word) (ptr : Z) : Prop :=
    match iovs with
    | [a] => ptr = usp + -88 /\
             exists A1, b1 = Z_to_bv 64 A1 /\ l1 = Z_to_bv 64 (zlength a) /\ src_ok A1 a
    | [a; b] => ptr = usp + -104 /\
             (exists A0, b0 = Z_to_bv 64 A0 /\ l0 = Z_to_bv 64 (zlength a) /\ src_ok A0 a) /\
             (exists A1, b1 = Z_to_bv 64 A1 /\ l1 = Z_to_bv 64 (zlength b) /\ src_ok A1 b)
    | _ => False
    end.

  (* [comment removed for export] *)
  Lemma frame_iovs2 : forall m j b0 l0 b1 l1,
    rw_cells ctasegs m (usp + -112) (frame j b0 l0 b1 l1) ->
    bytes_at ctasegs m (usp + -104) (iovec_bytes [(b0, l0); (b1, l1)]).
  Proof.
    intros m j b0 l0 b1 l1 [[WF FB] _]. cbn [cells_wf cell_wf frame] in WF. destruct WF as [L8 _].
    cbn [cells_bytes cbytes frame] in FB.
    apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
    cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r, <- app_assoc.
    replace (usp + -104) with (usp + -112 + Z.of_nat 8) by lia.
    apply bytes_at_app in FB as [FB1 FB]. apply bytes_at_app in FB as [FB2 FB].
    apply bytes_at_app in FB as [FB3 FB]. apply bytes_at_app in FB as [FB4 _].
    apply bytes_at_app; split; [exact FB1|]. apply bytes_at_app; split; [exact FB2|].
    apply bytes_at_app; split; [exact FB3| exact FB4].
  Qed.

  Lemma frame_iovs1 : forall m j b0 l0 b1 l1,
    rw_cells ctasegs m (usp + -112) (frame j b0 l0 b1 l1) ->
    bytes_at ctasegs m (usp + -88) (iovec_bytes [(b1, l1)]).
  Proof.
    intros m j b0 l0 b1 l1 FR. pose proof (frame_iovs2 m j b0 l0 b1 l1 FR) as H.
    cbn [iovec_bytes flat_map fst snd] in H |- *. rewrite app_nil_r in H |- *. rewrite <- app_assoc in H.
    apply bytes_at_app in H as [_ H]. apply bytes_at_app in H as [_ H].
    rewrite !length_le8 in H. replace (usp + -104 + Z.of_nat 8 + Z.of_nat 8) with (usp + -88) in H by lia. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_top : forall m j b0 l0 b1 l1 (ptr k : Z),
    rw_cells ctasegs m (usp + -112) (frame j b0 l0 b1 l1) -> mem_inv ctasegs m ->
    usp - 112 <= ptr -> 0 <= k -> ptr + k <= usp ->
    bv_unsigned (Z_to_bv 64 ptr) + k <= 0x800000000000.
  Proof.
    intros m j b0 l0 b1 l1 ptr k FR MI Hp Hk0 Hk.
    pose proof (rw_cells_below _ _ _ _ MI FR ltac:(cbn; lia)) as T. cbn [cells_size csize frame Nat.add length] in T.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB0. unfold UTOP in T.
    rewrite unsigned_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wv_done : forall (raX t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x6 t3 t4 t5 t6 : word)
      (j : list byte) (b0 l0 b1 l1 : word) (m : mem),
    rw_cells ctasegs m (usp + -112) (frame j b0 l0 b1 l1) ->
    rw_cells ctasegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
    ro_cells ctasegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> ro_cells ctasegs m ssp_guard [C8 canary] ->
    stk ctasegs m lo (usp + -112) -> mem_inv ctasegs m -> munch W m0 m -> wmono ctasegs m0 m ->
    evt ctasegs (POST tt st)
      (MS (mkR raX (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7
               x2 x3 x4 (Z_to_bv 64 ssp_guard) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5257e0) fc None m (seg_rom ctasegs)).
  Proof.
    intros until m. intros FR FC GOT GUARD ST MI MU WM.
    unfold frame, file_cells in *. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size csize Nat.add length] in FB.
    do 10 step. if_false.
    do 10 step. release_frame FR ST (bv_unsigned sp).
    unfold stdio_write_post, file_cells. sys_finish.
    - split; [exact GOT | exact GUARD].
    - reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma iov_advance_1 : forall a k, k <= zlength a -> iov_advance [a] k = [zdrop k a].
  Proof.
    intros a k Hk. cbn [iov_advance]. destruct (Z.ltb_spec0 (zlength a) k); [lia| reflexivity].
  Qed.
  Lemma iov_advance_2l : forall a b k, k <= zlength a -> iov_advance [a; b] k = [zdrop k a; b].
  Proof.
    intros a b k Hk. cbn [iov_advance]. destruct (Z.ltb_spec0 (zlength a) k); [lia| reflexivity].
  Qed.
  Lemma iov_advance_2r : forall a b k, zlength a < k -> iov_advance [a; b] k = [zdrop (k - zlength a) b].
  Proof.
    intros a b k Hk. cbn [iov_advance]. destruct (Z.ltb_spec0 (zlength a) k); [reflexivity| lia].
  Qed.

  Lemma iov_total_advance : forall iovs b0 l0 b1 l1 ptr k,
    iov_desc iovs b0 l0 b1 l1 ptr -> 1 <= k < iov_total iovs ->
    iov_total (iov_advance iovs k) = iov_total iovs - k.
  Proof.
    intros iovs b0 l0 b1 l1 ptr k DESC HK.
    destruct iovs as [|a [|b [|? ?]]]; try (exfalso; exact DESC).
    - rewrite iov_total_1 in HK |- *. rewrite iov_advance_1 by lia. rewrite iov_total_1. apply zlength_zdrop. lia.
    - rewrite iov_total_2 in HK |- *. pose proof (zlength_nonneg a). pose proof (zlength_nonneg b).
      destruct (Z.le_gt_cases k (zlength a)) as [LE|GT].
      + rewrite iov_advance_2l by lia. rewrite iov_total_2, zlength_zdrop by lia. lia.
      + rewrite iov_advance_2r by lia. rewrite iov_total_1, zlength_zdrop by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition meminv (m : mem) (j : list byte) (b0 l0 b1 l1 : word) : Prop :=
    rw_cells ctasegs m (usp + -112) (frame j b0 l0 b1 l1) /\
    rw_cells ctasegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) /\
    ro_cells ctasegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells ctasegs m ssp_guard [C8 canary] /\
    stk ctasegs m lo (usp + -112) /\ mem_inv ctasegs m /\ munch W m0 m /\ munch WF m0 m /\ wmono ctasegs m0 m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wv_adv : forall (Q : machine_state -> Prop) (raX t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 t3 t4 t5 t6 : word)
      (j : list byte) (b0 l0 b1 l1 : word) (m : mem) (iovs : list (list Z)) (ptr k : Z),
    meminv m j b0 l0 b1 l1 ->
    iov_desc iovs b0 l0 b1 l1 ptr -> 1 <= k < iov_total iovs -> iov_total iovs <= 2^26 ->
    (forall (a3' a4' a5' : word) (b0' l0' b1' l1' : word) (m' : mem) (ptr' : Z),
        meminv m' j b0' l0' b1' l1' ->
        iov_desc (iov_advance iovs k) b0' l0' b1' l1' ptr' ->
        evt ctasegs Q
          (MS (mkR raX (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 Fp)
                   (Z_to_bv 64 fd) (Z_to_bv 64 ptr') (Z_to_bv 64 (zlength (iov_advance iovs k))) a3' a4' a5' a6 (Z_to_bv 64 66)
                   (Z_to_bv 64 (zlength (iov_advance iovs k))) (Z_to_bv 64 ptr) (Z_to_bv 64 ptr') (Z_to_bv 64 ssp_guard)
                   (Z_to_bv 64 (iov_total (iov_advance iovs k))) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x52585c) fc None m' (seg_rom ctasegs))) ->
    evt ctasegs Q
      (MS (mkR raX (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 Fp)
               (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (zlength iovs)) (Z_to_bv 64 ptr) x4 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 (iov_total iovs))
               s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x52586c) fc None m (seg_rom ctasegs)).
  Proof.
    intros until k. intros (FR & FC & GOT & GUARD & ST & MI & MU & MUF & WM) DESC HK HT K.
    unfold frame, file_cells in *. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size csize Nat.add length] in FB.
    destruct iovs as [|a [|b [|? ?]]]; try (exfalso; exact DESC).
    - (* [comment removed for export] *)
      destruct DESC as (-> & A1 & -> & -> & OKa).
      pose proof (bytes_at_bound _ _ _ _ (proj1 OKa)) as BA. rewrite length_to_bytes in BA.
      rewrite iov_total_1 in HK, HT |- *. unfold zlength in *. cbn [length Z.of_nat Pos.of_succ_nat] in K |- *.
      zstep. if_cases Hc; zify_cond Hc; [exfalso; lia|].
      zstep. zstep.
      replace (Z.of_nat (length a) <? k) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite Z.land_0_l, Z.sub_0_r.
      zstep. zstep. if_cases Hc2; zify_cond Hc2; [| exfalso; lia].
      do 6 zstep. rewrite (sx32_small fd) by lia.
      zstep. zstep. zstep. zstep. zstep. change (bv_swrap 32 (Z.of_nat 1 - 0)) with 1.
      rewrite (iov_advance_1 a k) in K by (unfold zlength; lia).
      pose proof (zlength_zdrop k a ltac:(unfold zlength; lia)) as ZD. unfold zlength in ZD.
      rewrite iov_total_1 in K. unfold zlength in K. rewrite ZD in K.
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in K.
      eapply K.
      + unfold meminv, frame, file_cells, got_ssp, ssp_guard. split_spine; first [hyp_by_addr | assumption].
      + cbn [iov_desc]. split; [reflexivity|]. exists (A1 + k). split; [reflexivity|]. split.
        * unfold zlength. rewrite ZD. reflexivity.
        * apply src_ok_drop; [exact OKa | unfold zlength; lia].
    - (* [comment removed for export] *)
      destruct DESC as (-> & (A0 & -> & -> & OKa) & (A1 & -> & -> & OKb)).
      pose proof (bytes_at_bound _ _ _ _ (proj1 OKa)) as BA. rewrite length_to_bytes in BA.
      pose proof (bytes_at_bound _ _ _ _ (proj1 OKb)) as BB. rewrite length_to_bytes in BB.
      rewrite iov_total_2 in HK, HT |- *. unfold zlength in *. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in K |- *.
      zstep. if_cases Hc; zify_cond Hc; [exfalso; lia|].
      zstep. zstep.
      destruct (Z.le_gt_cases k (Z.of_nat (length a))) as [LE | GT].
      + (* [comment removed for export] *)
        replace (Z.of_nat (length a) <? k) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        rewrite Z.land_0_l, Z.sub_0_r.
        zstep. zstep. if_cases Hc2; zify_cond Hc2; [| exfalso; lia].
        do 6 zstep. rewrite (sx32_small fd) by lia.
        zstep. zstep. zstep. zstep. zstep. change (bv_swrap 32 (Z.of_nat 2 - 0)) with 2.
        pose proof (zlength_zdrop k a ltac:(unfold zlength; lia)) as ZD. unfold zlength in ZD.
        rewrite (iov_advance_2l a b k) in K by (unfold zlength; lia).
        rewrite iov_total_2 in K. unfold zlength in K. rewrite ZD in K.
        cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in K.
        replace (Z.of_nat (length a) - k + Z.of_nat (length b)) with (Z.of_nat (length a) + Z.of_nat (length b) - k) in K by lia.
        eapply K.
        * unfold meminv, frame, file_cells, got_ssp, ssp_guard. split_spine; first [hyp_by_addr | assumption].
        * cbn [iov_desc]. split; [reflexivity|]. split.
          -- exists (A0 + k). split; [reflexivity|]. split; [unfold zlength; rewrite ZD; reflexivity|].
             apply src_ok_drop; [exact OKa | unfold zlength; lia].
          -- exists A1. split; [reflexivity|]. split; [reflexivity|]. exact OKb.
      + (* [comment removed for export] *)
        replace (Z.of_nat (length a) <? k) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        zstep. zstep. zstep. zstep. zstep.
        replace (Z.land 18446744073709551615 (Z.of_nat (length a))) with (Z.of_nat (length a))
          by (change 18446744073709551615 with (2^64 - 1); rewrite zb_land_mask_l by lia; rewrite Z.mod_small by lia; reflexivity).
        zstep. zstep. zstep. zstep. if_cases Hc2; zify_cond Hc2; [exfalso; lia|].
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. rewrite (sx32_small fd) by lia.
        zstep. zstep. zstep. zstep. zstep. change (bv_swrap 32 (Z.of_nat 2 - 1)) with 1.
        pose proof (zlength_zdrop (k - Z.of_nat (length a)) b ltac:(unfold zlength; lia)) as ZD. unfold zlength in ZD.
        rewrite (iov_advance_2r a b k) in K by (unfold zlength; lia).
        rewrite iov_total_1 in K. unfold zlength in K. rewrite ZD in K.
        cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in K.
        replace (Z.of_nat (length b) - (k - Z.of_nat (length a))) with (Z.of_nat (length a) + Z.of_nat (length b) - k) in K |- * by lia.
        eapply K.
        * unfold meminv, frame, file_cells, got_ssp, ssp_guard. split_spine; first [hyp_by_addr | assumption].
        * cbn [iov_desc]. split; [reflexivity|].
          exists (A1 + (k - Z.of_nat (length a))). split; [reflexivity|]. split.
          -- unfold zlength. rewrite ZD. apply f_equal. lia.
          -- apply src_ok_drop; [exact OKb | unfold zlength; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wv_loop : forall fuel (iovs : list (list Z)) (raX t0 t1 t2 a3 a4 a5 a6 x3 t3 t4 t5 t6 : word)
      (j : list byte) (b0 l0 b1 l1 : word) (m : mem) (ptr : Z),
    meminv m j b0 l0 b1 l1 ->
    iov_desc iovs b0 l0 b1 l1 ptr -> iov_total iovs <= 2^26 ->
    implM ctasegs (mloop fuel (wv_body (St:=St) fd) iovs) st POST
      (MS (mkR raX (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 Fp)
               (Z_to_bv 64 fd) (Z_to_bv 64 ptr) (Z_to_bv 64 (zlength iovs)) a3 a4 a5 a6 (Z_to_bv 64 66)
               (Z_to_bv 64 (zlength iovs)) x3 (Z_to_bv 64 ptr) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 (iov_total iovs))
               s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x52585c) fc None m (seg_rom ctasegs)).
  Proof.
    induction fuel as [|fuel IH]; intros until ptr; intros MEM DESC HT.
    { cbn [mloop]. apply implM_unr. }
    apply implM_loop_S. unfold wv_body. apply implM_sysk.
    pose proof MEM as MEM'. destruct MEM' as (FR & FC & GOT & GUARD & ST & MI & MU & MUF & WM).
    pose proof (iov_total iovs) as TOT0.
    assert (TOTNN : 0 <= iov_total iovs) by (apply zlength_nonneg).
    step_ecall. split.
    - (* [comment removed for export] *)
      destruct iovs as [|a [|b [|? ?]]]; try (exfalso; exact DESC).
      + destruct DESC as (-> & A1 & -> & -> & OKa).
        pose proof (bytes_at_bound _ _ _ _ (proj1 OKa)) as BA. rewrite length_to_bytes in BA.
        at_node_red; split_spine; try reflexivity.
        * exact FD.
        * cbn [map length]. lia.
        * cbn [map concat]. rewrite app_nil_r, length_to_bytes. rewrite iov_total_1 in HT. unfold zlength in HT.
          unfold MAX_RW_COUNT. lia.
        * (* [comment removed for export] *)
          eapply (frame_top _ _ _ _ _ _ _ _ FR MI); cbn [map length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]; lia.
        * exists [(Z_to_bv 64 A1, Z_to_bv 64 (zlength a))]. split.
          -- rewrite unsigned_lit by lia. eapply frame_iovs1. exact FR.
          -- constructor; [|constructor]. split; [cbn [snd]; rewrite length_to_bytes; reflexivity|].
             split; [cbn [fst]; apply src_ok_top; exact OKa|].
             cbn [fst]. apply src_ok_now'; [exact OKa | exact MUF].
      + destruct DESC as (-> & (A0 & -> & -> & OKa) & (A1 & -> & -> & OKb)).
        pose proof (bytes_at_bound _ _ _ _ (proj1 OKa)) as BA. rewrite length_to_bytes in BA.
        pose proof (bytes_at_bound _ _ _ _ (proj1 OKb)) as BB. rewrite length_to_bytes in BB.
        at_node_red; split_spine; try reflexivity.
        * exact FD.
        * cbn [map length]. lia.
        * cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes. rewrite iov_total_2 in HT. unfold zlength in HT.
          unfold MAX_RW_COUNT. lia.
        * (* [comment removed for export] *)
          eapply (frame_top _ _ _ _ _ _ _ _ FR MI); cbn [map length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]; lia.
        * exists [(Z_to_bv 64 A0, Z_to_bv 64 (zlength a)); (Z_to_bv 64 A1, Z_to_bv 64 (zlength b))]. split.
          -- rewrite unsigned_lit by lia. eapply frame_iovs2. exact FR.
          -- constructor; [|constructor; [|constructor]].
             ++ split; [cbn [snd]; rewrite length_to_bytes; reflexivity|].
                split; [cbn [fst]; apply src_ok_top; exact OKa|].
                cbn [fst]. apply src_ok_now'; [exact OKa | exact MUF].
             ++ split; [cbn [snd]; rewrite length_to_bytes; reflexivity|].
                split; [cbn [fst]; apply src_ok_top; exact OKb|].
                cbn [fst]. apply src_ok_now'; [exact OKb | exact MUF].
    - (* [comment removed for export] *)
      intros rsp k Hdec. apply dec_writev_Some in Hdec as (-> & Hk & Hk2). cbv beta.
      destruct (Z.eqb_spec k (iov_total iovs)) as [EK|NK].
      + (* [comment removed for export] *)
        apply implM_ret. apply evt_done. unfold eff0. sys_nret.
        step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
        step. step. subst k. if_refl.
        eapply wv_done; [exact FR | exact FC | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
      + (* [comment removed for export] *)
        apply implM_ret. unfold eff0. sys_nret.
        step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
        step. step. if_cases Hq; zify_cond Hq; [exfalso; lia|].
        eapply (wv_adv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j b0 l0 b1 l1 m iovs ptr k MEM DESC ltac:(lia) HT).
        intros a3' a4' a5' b0' l0' b1' l1' m' ptr' MEM2 DESC2.
        apply evt_done. eapply IH; [exact MEM2 | exact DESC2 |].
        rewrite (iov_total_advance iovs b0 l0 b1 l1 ptr k DESC) by lia. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma stdio_write_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rw_cells ctasegs m0 Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
    stk ctasegs m0 lo usp -> ssp_cells m0 canary -> mem_inv ctasegs m0 ->
    implM ctasegs (stdio_writev (St:=St) fd buf s) st POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x52574c) fc None m0 (seg_rom ctasegs)).
  Proof.
    intros until t6. intros FC ST [GOT GUARD] MI.
    (* [comment removed for export] *)
    pose proof (src_ok_s MI) as OKS. pose proof (src_ok_buf MI) as OKB0.
    pose proof (bytes_at_bound _ _ _ _ BUFB0) as BB. rewrite length_to_bytes in BB.
    clear SRC0 BUFB0.
    unfold file_cells in FC. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size csize Nat.add length] in FB.
    pose proof (munch_refl W m0) as MU. pose proof (munch_refl WF m0) as MUF. pose proof (wmono_refl ctasegs m0) as WM.
    unfold zlength in *.
    unfold stdio_writev, WV_FUEL. apply implM_loop_S. unfold wv_body. apply implM_sysk.
    carve_frame 112%nat ST.
    zidle_begin sp 112%Z MUz WMz.
    do 9 zstep.
    zidle_end MUz WMz.
    do 3 zstep. do 13 zstep.
    assert (CASES : buf = [] \/ exists c0 buf', buf = c0 :: buf') by (destruct buf; [left; reflexivity | right; eexists; eexists; reflexivity]).
    destruct CASES as [EB | (c0 & buf' & EB)].
    - (* [comment removed for export] *)
      assert (LB0 : Z.of_nat (length buf) = 0) by (rewrite EB; reflexivity).
      clear OKB0. rewrite EB. cbn [length iov_start].
      replace (B + Z.of_nat 0) with B by lia. rewrite Z.lxor_nilpotent. cbn [Z.b2z Z.ltb].
      replace (B + Z.of_nat (length buf) - B) with 0 in FR by lia.
      zstep. if_refl. zstep. zstep. zstep. rewrite (sx32_small fd) by lia. zstep. zstep. zstep.
      change (Z.b2z (0 <? 0) + 1) with 1.
      replace (B - B + Z.of_nat (length s)) with (iov_total [s]) by (rewrite iov_total_1; unfold zlength; lia).
      assert (DESC : iov_desc [s] (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) (usp + -88)).
      { cbn [iov_desc]. split; [reflexivity|]. exists S. split; [reflexivity|]. split; [reflexivity| exact OKS]. }
      assert (HT : iov_total [s] <= 2^26) by (rewrite iov_total_1; unfold zlength; lia).
      assert (TOTNN : 0 <= iov_total [s]) by (apply zlength_nonneg).
      step_ecall. split.
      + at_node_red; split_spine; try reflexivity.
        * exact FD.
        * cbn [map length]. lia.
        * cbn [map concat]. rewrite app_nil_r, length_to_bytes. unfold MAX_RW_COUNT. lia.
        * eapply (frame_top _ _ _ _ _ _ _ _ FR MI); cbn [map length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]; lia.
        * exists [(Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]. split.
          -- rewrite unsigned_lit by lia. eapply frame_iovs1. exact FR.
          -- constructor; [|constructor]. split; [cbn [snd]; rewrite length_to_bytes; reflexivity|].
             split; [cbn [fst]; apply src_ok_top; exact OKS|].
             cbn [fst]. apply src_ok_now'; [exact OKS | exact MUF].
      + intros rsp k Hdec. apply dec_writev_Some in Hdec as (-> & Hk & Hk2). cbv beta.
        lazymatch type of FR with rw_cells _ ?m1 _ (CB 8 ?j :: _) =>
          assert (MEM : meminv m1 j (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))));
            [unfold meminv, frame, file_cells, got_ssp, ssp_guard; unfold zlength; split_spine; first [hyp_by_addr | assumption] |] end.
        destruct (Z.eqb_spec k (iov_total [s])) as [EK|NK].
        * (* [comment removed for export] *)
          apply implM_ret. apply evt_done. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          step. subst k. if_refl.
          eapply wv_done; [exact FR | unfold zlength; exact FC | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
        * (* [comment removed for export] *)
          apply implM_ret. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          step. if_cases Hq; zify_cond Hq; [| exfalso; lia].
          eapply (wv_adv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [s] (usp + -88) k MEM DESC ltac:(lia) HT).
          intros a3' a4' a5' b0' l0' b1' l1' m' ptr' MEM2 DESC2.
          apply evt_done. eapply wv_loop; [exact MEM2 | exact DESC2 |].
          rewrite (iov_total_advance [s] _ _ _ _ _ k DESC) by lia. lia.
    - (* [comment removed for export] *)
      assert (NE : buf <> []) by (rewrite EB; discriminate).
      pose proof (OKB0 NE) as OKB. clear OKB0.
      assert (NB1 : 1 <= Z.of_nat (length buf)) by (rewrite EB; cbn [length]; lia).
      clear EB c0 buf'. rewrite (iov_start_cons buf s NE).
      set (nb := Z.of_nat (length buf)) in *.
      replace (B + nb - B) with nb in FR by lia.
      replace (0 <? Z.lxor (B + nb) B) with true.
      2:{ symmetry. apply Z.ltb_lt.
          assert (XNZ : Z.lxor (B + nb) B <> 0) by (intros E; apply Z.lxor_eq in E; lia).
          pose proof (Z.lxor_nonneg (B + nb) B). lia. }
      cbn [Z.b2z].
      zstep. if_cases Hb; zify_cond Hb; [exfalso; lia|].
      zstep. zstep. zstep. rewrite (sx32_small fd) by lia. zstep. zstep. zstep. zstep.
      replace (B + nb - B + Z.of_nat (length s)) with (iov_total [buf; s]) by (rewrite iov_total_2; unfold zlength; lia).
      assert (DESC : iov_desc [buf; s] (Z_to_bv 64 B) (Z_to_bv 64 nb) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) (usp + -104)).
      { cbn [iov_desc]. split; [reflexivity|]. split.
        - exists B. split; [reflexivity|]. split; [reflexivity| exact OKB].
        - exists S. split; [reflexivity|]. split; [reflexivity| exact OKS]. }
      assert (HT : iov_total [buf; s] <= 2^26) by (rewrite iov_total_2; unfold zlength; lia).
      assert (TOTNN : 0 <= iov_total [buf; s]) by (apply zlength_nonneg).
      step_ecall. split.
      + at_node_red; split_spine; try reflexivity.
        * exact FD.
        * cbn [map length]. lia.
        * cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes. unfold MAX_RW_COUNT. lia.
        * eapply (frame_top _ _ _ _ _ _ _ _ FR MI); cbn [map length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]; lia.
        * exists [(Z_to_bv 64 B, Z_to_bv 64 nb); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]. split.
          -- rewrite unsigned_lit by lia. eapply frame_iovs2. exact FR.
          -- constructor; [|constructor; [|constructor]].
             ++ split; [cbn [snd]; rewrite length_to_bytes; reflexivity|].
                split; [cbn [fst]; subst nb; apply src_ok_top; exact OKB|].
                cbn [fst]. apply src_ok_now'; [exact OKB | exact MUF].
             ++ split; [cbn [snd]; rewrite length_to_bytes; reflexivity|].
                split; [cbn [fst]; apply src_ok_top; exact OKS|].
                cbn [fst]. apply src_ok_now'; [exact OKS | exact MUF].
      + intros rsp k Hdec. apply dec_writev_Some in Hdec as (-> & Hk & Hk2). cbv beta.
        lazymatch type of FR with rw_cells _ ?m1 _ (CB 8 ?j :: _) =>
          assert (MEM : meminv m1 j (Z_to_bv 64 B) (Z_to_bv 64 nb) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))));
            [unfold meminv, frame, file_cells, got_ssp, ssp_guard; unfold zlength; split_spine; first [hyp_by_addr | assumption] |] end.
        destruct (Z.eqb_spec k (iov_total [buf; s])) as [EK|NK].
        * (* [comment removed for export] *)
          apply implM_ret. apply evt_done. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          step. subst k. if_refl.
          eapply wv_done; [exact FR | unfold zlength; exact FC | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
        * (* [comment removed for export] *)
          apply implM_ret. unfold eff0. sys_nret.
          step. step. step. step. if_cases Hc; zify_cond Hc; [| exfalso; lia]. step.
          step. if_cases Hq; zify_cond Hq; [| exfalso; lia].
          eapply (wv_adv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [buf; s] (usp + -104) k MEM DESC ltac:(lia) HT).
          intros a3' a4' a5' b0' l0' b1' l1' m' ptr' MEM2 DESC2.
          apply evt_done. eapply wv_loop; [exact MEM2 | exact DESC2 |].
          rewrite (iov_total_advance [buf; s] _ _ _ _ _ k DESC) by lia. lia.
  Qed.
End StdioWriteProof.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem stdio_write_proof {St : Type} : @stdio_write_stmt St.
Proof.
  unfold stdio_write_stmt. intros until canary.
  intros FC BUFB SRC -> -> -> FD ST LO GLO SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi LENS S0 Shi SNIL SEPS SEPB.
  pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
  unfold GLOBALS_TOP in GLO. unfold STDIO_WRITE_DEPTH in LO.
  eapply stdio_write_main; try eassumption; lia.
Qed.
