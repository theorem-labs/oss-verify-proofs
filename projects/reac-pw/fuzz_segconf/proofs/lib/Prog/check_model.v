(** The walk of fuzz_segconf's check_model in the plain image (Prog/check_model_c.v), written new for
    reac-pw/fuzz_segconf. strcmp is a premise (strcmp_contract, Prog/strcmp_c.v, 0x1ebf8).

    Code (image 3776ca44d75c):
      0x14848 addi sp,sp,-16; 0x1484c sd ra,8(sp)
      0x14850 lw a2,0x20(a1); seqz a3,a2; addi a1,a1,0x24; addi a3,a3,-1; and a3,a3,a1
      0x14864 beq a0,a3 -> 0x14878; 0x14868 beqz a0 -> abort; 0x1486c beqz a2 -> abort
      0x14870 jal strcmp; 0x14874 bnez a0 -> abort
      0x14878 ld ra,8(sp); addi sp,sp,16; ret; 0x14884 jal abort
    The premise same_text leaves two paths: model_set = 0 and got = NULL (the beq is taken), or model_set = 1 and
    got a C string equal to the model (the beq is taken when got = want + 0x24, else strcmp returns 0). Every branch
    to the abort call is refuted. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec strcmp_c check_model_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Pure facts (no image): shared with check_provenance and the UBSan walks *)

Lemma ck_byte0 : forall b : byte, bv_unsigned b = 0 -> b = Z_to_bv 8 0.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

(** SegModel.strcmp on the values of two NUL-free byte strings is 0 exactly when they are equal (the statement
    of Spec/SegBridge.v's bridge_strcmp; a local copy). *)
Lemma bridge_strcmp : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  SegModel.strcmp (zs sx) (zs sy) = 0 <-> sx = sy.
Proof.
  unfold zs. induction sx as [|x sx IH]; intros [|y sy] NX NY; cbn [map SegModel.strcmp].
  - split; intros; reflexivity.
  - split; [|intros H; discriminate H]. intros H. exfalso. apply NY. cbn [In]. left. apply ck_byte0. lia.
  - split; [|intros H; discriminate H]. intros H. exfalso. apply NX. cbn [In]. left. apply ck_byte0. exact H.
  - assert (X0 : bv_unsigned x <> 0).
    { intros H. apply NX. cbn [In]. left. apply ck_byte0. exact H. }
    assert (NX' : ~ In (Z_to_bv 8 0) sx) by (intros H; apply NX; cbn [In]; right; exact H).
    assert (NY' : ~ In (Z_to_bv 8 0) sy) by (intros H; apply NY; cbn [In]; right; exact H).
    destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E].
    + replace (bv_unsigned x =? 0) with false by (symmetry; apply Z.eqb_neq; exact X0).
      cbn [andb negb]. rewrite (IH sy NX' NY').
      assert (XY : x = y) by (apply bv_eq; exact E). subst y.
      split; [intros ->; reflexivity | intros H; injection H as H; exact H].
    + cbn [andb]. split; [intros H; lia | intros H; injection H as H1 H2; exfalso; apply E; rewrite H1; reflexivity].
Qed.

Lemma ck_firstn_map : forall (f : byte -> Z) n (l : list byte), firstn n (map f l) = map f (firstn n l).
Proof. intros f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma ck_bytes_sub : forall segs m a bs k n, bytes_at segs m a bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros segs m a bs k n H L.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

(** The bytes [off, off + n) of an object at a are at a + off. *)
Lemma ck_fld_at : forall segs m a bs off n, bytes_at segs m a bs -> 0 <= off -> 0 <= n ->
  (Z.to_nat off + Z.to_nat n <= length bs)%nat -> bytes_at segs m (a + off) (fldz off n bs).
Proof.
  intros segs m a bs off n H H0 H1 L. unfold fldz, fld.
  pose proof (ck_bytes_sub segs m a bs (Z.to_nat off) (Z.to_nat n) H L) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

(** A char[cap] field holding s (cstr_enc) holds the bytes of s and their NUL: what strcmp reads. *)
Lemma ck_cstrz : forall segs m a cap s f, bytes_at segs m a f -> cstr_enc cap s f ->
  exists sy, bytes_at segs m a (sy ++ [Z_to_bv 8 0]) /\ zs sy = s /\ ~ In (Z_to_bv 8 0) sy /\
             (length sy < cap)%nat.
Proof.
  intros segs m a cap s f H (Lf & Ls & NZ & Hp).
  set (L := length s) in *.
  assert (Hb : bytes_at segs m a (firstn (S L) f)).
  { rewrite <- (firstn_skipn (S L) f) in H. apply bytes_at_app in H. exact (proj1 H). }
  set (p := firstn (S L) f) in *.
  assert (Lp : length p = S L) by (apply firstn_length_le; lia).
  assert (Ls1 : length (skipn L p) = 1%nat) by (rewrite length_skipn; lia).
  destruct (skipn L p) as [|x [|y r]] eqn:Ex; cbn [length] in Ls1; try lia.
  assert (Ep : p = firstn L p ++ [x]) by (rewrite <- Ex; symmetry; apply firstn_skipn).
  assert (Zp : zs p = s ++ [0]) by (unfold zs, p; rewrite <- ck_firstn_map; exact Hp).
  rewrite Ep in Zp. unfold zs in Zp. rewrite map_app in Zp. cbn [map] in Zp.
  apply app_inj_tail in Zp. destruct Zp as [Zs Zx].
  apply ck_byte0 in Zx. subst x.
  exists (firstn L p). split; [rewrite <- Ep; exact Hb|]. split; [exact Zs|]. split.
  - intros Hin. apply NZ. rewrite <- Zs. exact (in_map bv_unsigned _ _ Hin).
  - rewrite firstn_length_le by lia. lia.
Qed.

(** The values of the two flag words. *)
Lemma ck_le4_1 : le4 (Z_to_bv 64 1) = [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. reflexivity. Qed.
Lemma ck_le4_0 : le4 (Z_to_bv 64 0) = [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. reflexivity. Qed.

Lemma ck_read_all : forall segs m a bs, bytes_at segs m a bs -> ov_read_bytes segs m (wa a) (length bs) = Some bs.
Proof.
  intros segs m a bs H. pose proof (bytes_at_ov_read segs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [skipn Z.of_nat] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Lemma ck_land_ones : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(** UBSan's alignment test `andi x, p, 3`. *)
Lemma ck_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(** After a callee's return: its pc ret_pc of a literal ra is the literal. *)
Ltac ck_fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(** Carry bytes_at H from the entry memory to the current one through the footprint fact MU (munch W m0 m1), for
    a C string (its bytes ++ [NUL]) lying outside W. *)
Ltac ck_transport H :=
  lazymatch type of H with bytes_at ?segs ?m0 _ _ =>
    lazymatch goal with MU : munch ?W m0 ?m1 |- _ =>
      apply (bytes_at_transport segs W m0 m1) in H;
        [| exact MU | cbn [disjoint_from]; rewrite ?length_app; cbn [length]; slia]
    end
  end.

(** ** The walk *)
Theorem check_model_holds : strcmp_contract -> check_model_contract.
Proof.
  intros SC. unfold strcmp_contract, STRCMP in SC.
  unfold check_model_contract, check_model_pre, CHECK_MODEL, CHECK_MODEL_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo o g
    (AL & (bs & BS & ENC) & AP & OC & AO & SAME & (ST & DP & SPA & NR) & MI).
  unfold apart, MSEG_SIZE in AP.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0.
  pose proof (bv_unsigned_in_range 64 a1) as RA1. unfold bv_modulus in RA1. cbn in RA1.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct ENC as (LEN & _ & _ & _ & _ & _ & FM & CM & _ & _ & _).
  pose proof (bytes_at_bound _ _ _ _ BS) as BB.
  pose proof (ck_fld_at rsegs m _ _ MS_MODEL_SET 4 BS ltac:(unfold MS_MODEL_SET; lia) ltac:(lia)
                ltac:(unfold MS_MODEL_SET; rewrite LEN; lia)) as BF.
  pose proof (ck_fld_at rsegs m _ _ MS_MODEL 24 BS ltac:(unfold MS_MODEL; lia) ltac:(lia)
                ltac:(unfold MS_MODEL; rewrite LEN; lia)) as BM0.
  destruct (ck_cstrz rsegs m _ _ _ _ BM0 CM) as (sy & BY & ZY & NY & LY).
  unfold flag_enc in FM. rewrite FM in BF. unfold MS_MODEL_SET in BF. unfold MS_MODEL in BY.
  clear FM BM0 CM.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  revert BF SAME. destruct (ms_model_set g) eqn:EMS; destruct o as [s|]; intros BF SAME;
    cbn [same_text] in SAME; cbv beta iota in BF; try discriminate SAME.
  - (* model_set = 1, got = the C string s, equal to the model *)
    apply Z.eqb_eq in SAME.
    destruct OC as (NZ0 & gx & BGX & ZGX & NIN). subst s.
    assert (NGX : ~ In (Z_to_bv 8 0) gx) by (intros H; apply NIN; exact (in_map bv_unsigned _ _ H)).
    rewrite <- ZY in SAME. apply (proj1 (bridge_strcmp gx sy NGX NY)) in SAME. subst sy.
    unfold apart, zs in AO. rewrite length_map in AO.
    rewrite ck_le4_1 in BF. clear NIN.
    carve_frame 16%nat ST.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M1 end.
    assert (RDF : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned a1 + 32)) 4 =
                  Some [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) by exact (ck_read_all rsegs M1 _ _ BF).
    do 5 zstep.
    replace ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615 by reflexivity.
    rewrite ck_land_ones by lia.
    (* beq a0, a3: taken (got = want + 0x24) to the return *)
    zstep. if_cases K.
    + zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). finish; try exact I.
    + (* beqz a0: got <> NULL *)
      zstep. if_cases K1; [exfalso; zify_cond K1; lia|].
      (* beqz a2: model_set = 1 *)
      zstep. if_false.
      (* jal strcmp(got, want + 0x24) *)
      zstep.
      eapply evt_cut.
      { eapply SC; [exact BGX | exact NGX | rewrite unsigned_lit by lia; exact BY | exact NGX]. }
      intros ms' (r & x11 & x12 & x13 & -> & HR). ck_fix_ret.
      assert (R0 : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r.
      (* bnez a0: strcmp returned 0 *)
      zstep. if_false.
      zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). finish; try exact I.
  - (* model_set = 0, got = NULL *)
    rewrite ck_le4_0 in BF.
    carve_frame 16%nat ST.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M1 end.
    assert (RDF : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned a1 + 32)) 4 =
                  Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) by exact (ck_read_all rsegs M1 _ _ BF).
    do 5 zstep.
    replace ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) with 0 by reflexivity.
    rewrite Z.land_0_l.
    (* beq a0, a3 with a0 = a3 = 0: taken to the return *)
    zstep. if_cases K; [|exfalso; zify_cond K; cbn [ocstrz_at] in OC; lia].
    zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). finish; try exact I.
Qed.
