(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module CJ_minify.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition MINIFY_ENTRY : Z := 0x1397c.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition JT : list byte := map wb
  [68; 53; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 92; 52; 0; 0; 92; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 92; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 92; 52; 0; 0; 216; 52; 0; 0; 128; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 216; 52; 0; 0; 232; 52; 0; 0].

Definition jt_sel (c : Z) : Z :=
  if c =? 0 then 0x3544
  else if (c =? 9) || (c =? 10) || (c =? 13) || (c =? 32) then 0x345c
  else if c =? 34 then 0x3480 else if c =? 47 then 0x34e8 else 0x34d8.

Lemma jt_bytes : forall m, mem_inv psegs m -> bytes_at psegs m 0x10548 JT.
Proof.
  intros m MI.
  pose proof (ro_cells_image psegs m 0x10548 JT MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma byte_list_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  inversion H. f_equal; [apply bv_eq; assumption| apply IH; assumption].
Qed.

Lemma jt_entry : forall c, 0 <= c <= 47 ->
  firstn 4 (skipn (Z.to_nat (Z.shiftl c 2)) JT) = le4 (Z_to_bv 64 (jt_sel c)).
Proof.
  intros c Hc.
  assert (H : exists n, c = Z.of_nat n /\ (n < 48)%nat) by (exists (Z.to_nat c); lia).
  (nelim H 3%nat; intros n -> Hn).
  do 48 (destruct n as [|n]; [apply byte_list_eq; vm_compute; reflexivity|]). lia.
Qed.

Lemma jt_read : forall m c, mem_inv psegs m -> 0 <= c <= 47 ->
  ov_read_bytes psegs m (wa (Z.shiftl c 2 + 0x10548)) 4 = Some (le4 (Z_to_bv 64 (jt_sel c))).
Proof.
  intros m c MI Hc. rewrite Z.add_comm, <- jt_entry by exact Hc.
  apply (bytes_at_read psegs m 0x10548 JT (Z.shiftl c 2) 4 (jt_bytes m MI)).
  - rewrite Z.shiftl_mul_pow2 by lia. lia.
  - change (length JT) with 192%nat. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma jt_sel_default : forall c, c <> 0 -> c <> 9 -> c <> 10 -> c <> 13 -> c <> 32 -> c <> 34 -> c <> 47 ->
  jt_sel c = 0x34d8.
Proof.
  intros. unfold jt_sel.
  repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y); [lia|] end. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sufx (orig buf : list byte) (q : Z) : Prop :=
  length buf = length orig /\ forall x, 0 <= x -> q <= x -> nth_error buf (Z.to_nat x) = nth_error orig (Z.to_nat x).

Lemma sufx_refl : forall orig q, sufx orig orig q.
Proof. intros. split; [reflexivity| intros; reflexivity]. Qed.

Lemma sufx_mono : forall orig buf q q', sufx orig buf q -> q <= q' -> sufx orig buf q'.
Proof. intros orig buf q q' [L H] Hq. split; [exact L|]. intros x H0 Hx. apply H; lia. Qed.

Lemma sufx_upd : forall orig buf q k b,
  sufx orig buf q -> 0 <= k -> (k < q \/ nth_error orig (Z.to_nat k) = Some b) ->
  sufx orig (upd buf (Z.to_nat k) b) q.
Proof.
  intros orig buf q k b [L H] Hk Hb. split; [rewrite upd_length; exact L|].
  intros x H0 Hx. destruct (Z.eq_dec k x) as [<-|NE].
  - destruct Hb as [Hb|Hb]; [lia|]. rewrite Hb.
    destruct (Nat.lt_ge_cases (Z.to_nat k) (length buf)) as [LT|GE].
    + apply nth_error_upd_same. exact LT.
    + exfalso. assert (E : nth_error orig (Z.to_nat k) = None) by (apply nth_error_None; lia). rewrite E in Hb. discriminate.
  - rewrite nth_error_upd_other by lia. apply H; lia.
Qed.

Lemma sufx_nth : forall orig buf q x b,
  sufx orig buf q -> q <= x -> 0 <= x -> nth_error orig (Z.to_nat x) = Some b -> nth_error buf (Z.to_nat x) = Some b.
Proof. intros orig buf q x b [L H] Hx H0 Hb. rewrite H by lia. exact Hb. Qed.

(* [comment removed for export] *)
Lemma mf_store : forall m A buf (k : Z) (b : byte),
  u8arr psegs m A buf -> 0 <= k < Z.of_nat (length buf) ->
  store_ok psegs m (wa (A + k)) 1 = true /\ u8arr psegs (write_to_mem m (wa (A + k)) [b]) A (upd buf (Z.to_nat k) b).
Proof.
  intros m A buf k b ARR Hk. split.
  - eapply u8arr_store_ok; [exact ARR| exact Hk| reflexivity].
  - apply u8arr_write; [exact ARR| exact Hk].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition minify_post (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (n : nat) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(A, A + Z.of_nat n)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ (exists buf', u8arr psegs m' A buf' /\ length buf' = n /\ In (wb 0) buf').

Section Proofs.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (A : Z) (s : list byte).
  Hypothesis NONUL : ~ In (wb 0) s.
  Hypothesis AB : 0 <= A /\ A + Z.of_nat (length s) + 1 <= 2^64.

  Notation len := (Z.of_nat (length s)).
  Notation orig := (s ++ [wb 0]).
  Notation W := [(A, A + Z.of_nat (S (length s)))].
  Notation POST := (minify_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A (S (length s)) m0).
  (* [comment removed for export] *)
  Notation ST pc mm x10 x17 x5 x6 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 (Z_to_bv 64 47) (Z_to_bv 64 34) (Z_to_bv 64 92) (Z_to_bv 64 42)
             (Z_to_bv 64 0x10548) (Z_to_bv 64 10) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  Definition inv (buf : list byte) (m : word -> option byte) (q : Z) : Prop :=
    u8arr psegs m A buf /\ sufx orig buf q /\ munch W m0 m /\ wmono psegs m0 m /\ mem_inv psegs m.

  Lemma orig_length : length orig = S (length s).
  Proof. rewrite length_app. cbn. lia. Qed.

  Lemma orig_nth_lt : forall x, 0 <= x < len -> exists b, nth_error orig (Z.to_nat x) = Some b /\ bv_unsigned b <> 0.
  Proof.
    intros x Hx. destruct (nth_error s (Z.to_nat x)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (wb 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma orig_nth_len : nth_error orig (Z.to_nat len) = Some (wb 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  Lemma orig_nth : forall x, 0 <= x <= len -> exists b, nth_error orig (Z.to_nat x) = Some b /\ (bv_unsigned b = 0 <-> x = len).
  Proof.
    intros x Hx. destruct (Z.eq_dec x len) as [->|NE].
    - exists (wb 0). split; [apply orig_nth_len|]. split; [auto| reflexivity].
    - (nelim (orig_nth_lt x ltac:(lia)) 3%nat; intros b Hb NZ). exists b. split; [exact Hb|]. split; [intros H; exfalso; exact (NZ H)| intros; lia].
  Qed.

  Lemma orig_nth_nz : forall x b, nth_error orig (Z.to_nat x) = Some b -> bv_unsigned b <> 0 -> 0 <= x -> x < len.
  Proof.
    intros x b Hb NZ Hx. destruct (Z.lt_ge_cases x len) as [LT|GE]; [exact LT|]. exfalso.
    destruct (Z.eq_dec x len) as [->|NE].
    - rewrite orig_nth_len in Hb. inversion Hb; subst. apply NZ. reflexivity.
    - assert (E : nth_error orig (Z.to_nat x) = None) by (apply nth_error_None; rewrite orig_length; lia). rewrite E in Hb. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma inv_read : forall buf m q x, inv buf m q -> q <= x -> 0 <= x <= len ->
    exists b, nth_error orig (Z.to_nat x) = Some b /\ (bv_unsigned b = 0 <-> x = len)
      /\ ov_read_bytes psegs m (wa (A + x)) 1 = Some [b] /\ 0 <= bv_unsigned b < 256.
  Proof.
    intros buf m q x (ARR & SX & _) Hq Hx. (nelim (orig_nth x Hx) 3%nat; intros b Hb Hz).
    exists b. split; [exact Hb|]. split; [exact Hz|]. split.
    - eapply u8arr_read; [exact ARR| eapply sufx_nth; [exact SX| exact Hq| lia| exact Hb]| lia| reflexivity].
    - pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac do_store k b tac :=
    lazymatch goal with
    | ARR : u8arr psegs ?m A ?buf |- _ =>
        let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
        destruct (mf_store m A buf k b ARR) as [SOK ARR'];
        [ lia
        | clear ARR; step;
          lazymatch goal with
          | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
              replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa (A + k)) [b])
                by (f_equal; first [tac| unfold wa; f_equal; lia]);
              store_done; rename ARR' into ARR
          end ]
    end.

  Section Head.
    Variable K : nat.
    Hypothesis IH : forall (j i : Z) (buf : list byte) (m : word -> option byte) (x5 x6 : word),
      (Z.to_nat (len - j) < K)%nat -> 0 <= i <= j -> j <= len -> inv buf m j ->
      evt psegs POST (ST 0x139a8 m (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + i)) x5 x6).

    (* [comment removed for export] *)
    Lemma l_adv : forall j i buf m x10 x6,
      (Z.to_nat (len - (j + 1)) < K)%nat -> 0 <= i <= j -> j + 1 <= len -> inv buf m (j + 1) ->
      evt psegs POST (ST 0x13a24 m x10 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + j)) x6).
    Proof.
      intros j i buf m x10 x6 HK Hij Hj INV. (nelimp INV 5%nat; intros ARR _ _ _ MI).
      zstep. zstep. zstep.
      replace (A + j + 1) with (A + (j + 1)) by lia. replace (A + i + 1) with (A + (i + 1)) by lia.
      apply (IH (j + 1) (i + 1) buf m); [exact HK| lia| lia| exact INV].
    Qed.

    (* [comment removed for export] *)
    Lemma l_default : forall j i buf m b x6,
      (Z.to_nat (len - (j + 1)) < K)%nat -> 0 <= i <= j -> j < len -> inv buf m j ->
      nth_error orig (Z.to_nat j) = Some b ->
      evt psegs POST (ST 0x13a20 m (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + j)) x6).
    Proof.
      intros j i buf m b x6 HK Hij Hj INV Hb. (nelimp INV 5%nat; intros ARR SX MU WM MI).
      pose proof (proj1 SX) as L. rewrite orig_length in L.
      do_store i b ltac:(symmetry; apply le1_zxb).
      eapply l_adv; [exact HK| exact Hij| lia|].
      split; [exact ARR|]. split; [| split; [exact MU| split; [exact WM| exact MI]]].
      apply sufx_upd; [eapply sufx_mono; [exact SX| lia]| lia| left; lia].
    Qed.

    (* [comment removed for export] *)
    Ltac rd INV x b :=
      let Hn := fresh "Hn" b in let Hz := fresh "Hz" b in let RD := fresh "RD" in let R := fresh "R" b in
      destruct (inv_read _ _ _ x INV) as (b & Hn & Hz & RD & R); [lia| lia|]. (* [comment removed for export] *)

    Ltac inv_parts INV :=
      lazymatch type of INV with inv _ _ _ =>
        let ARR := fresh "ARR" in let SX := fresh "SX" in let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in
        let Lbuf := fresh "Lbuf" in
        pose proof INV as (ARR & SX & MU & WM & MI); (* [comment removed for export] *)
        pose proof (proj1 SX) as Lbuf; rewrite orig_length in Lbuf
      end.

    (* [comment removed for export] *)
    Ltac mk_inv name q :=
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        lazymatch goal with ARR : u8arr psegs mc A ?buf |- _ =>
          assert (name : inv buf mc q);
          [ split; [exact ARR| split; [| split; [assumption| split; assumption]]] |]
        end end.

    (* [comment removed for export] *)
    Lemma l_ws : forall j i buf m x10 x6,
      (Z.to_nat (len - (j + 1)) < K)%nat -> 0 <= i <= j -> j < len -> inv buf m j ->
      evt psegs POST (ST 0x139a4 m x10 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + j)) x6).
    Proof.
      intros j i buf m x10 x6 HK Hij Hj INV. pose proof INV as (_ & SX & _ & _ & MI). (* [comment removed for export] *)
      zstep. replace (A + j + 1) with (A + (j + 1)) by lia.
      apply (IH (j + 1) i buf m); [exact HK| lia| lia|].
      destruct INV as (ARR & _ & R). split; [exact ARR|]. split; [eapply sufx_mono; [exact SX| lia]| exact R]. (* [comment removed for export] *)
    Qed.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma sl_b8 : forall q o buf m x10 x6,
      (forall buf' m' x10' cb', inv buf' m' (q + 1) -> nth_error orig (Z.to_nat (q + 1)) = Some cb' -> bv_unsigned cb' <> 0 ->
         evt psegs POST (ST 0x139fc m' x10' (Z_to_bv 64 (A + (o + 1))) (Z_to_bv 64 (A + (q + 1))) (Z_to_bv 64 (bv_unsigned cb')))) ->
      (Z.to_nat (len - (q + 1)) < K)%nat -> 0 <= o <= q -> q < len -> inv buf m (q + 1) ->
      evt psegs POST (ST 0x139e8 m x10 (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + q)) x6).
    Proof.
      intros q o buf m x10 x6 CC HK Hoq Hq INV. inv_parts INV.
      rd INV (q + 1) cb.
      zstep. cbv beta. zstep. zstep. zstep. zstep.
      replace (A + q + 1) with (A + (q + 1)) by lia. replace (A + o + 1) with (A + (o + 1)) by lia.
      if_cases Kz; zify_cond Kz.
      - (* [comment removed for export] *)
        apply (IH (q + 1) (o + 1) buf m); [exact HK| lia| lia| exact INV].
      - apply (CC buf m _ cb); [exact INV| exact Hncb| exact Kz].
    Qed.

    (* [comment removed for export] *)
    Lemma sl_cc : forall (kk : nat) q o buf m cb x10,
      (Z.to_nat (len - q) <= kk)%nat -> (Z.to_nat (len - q) <= K)%nat ->
      0 <= o <= q -> q < len -> inv buf m q -> nth_error orig (Z.to_nat q) = Some cb ->
      evt psegs POST (ST 0x139fc m x10 (Z_to_bv 64 (A + o)) (Z_to_bv 64 (A + q)) (Z_to_bv 64 (bv_unsigned cb))).
    Proof.
      induction kk as [|kk IHkk]; intros q o buf m cb x10 Hkk HK Hoq Hq INV Hcb; [lia|].
      inv_parts INV.
      (* [comment removed for export] *)
      do_store o cb ltac:(symmetry; apply le1_zxb).
      mk_inv INV1 q.
      { apply sufx_upd; [exact SX| lia|]. destruct (Z.eq_dec o q) as [->|]; [right; exact Hcb| left; lia]. }
      clear SX INV. inv_parts INV1. clear ARR0 MU0 WM0 MI0.
      rd INV1 q cb1. rewrite Hcb in Hncb1. injection Hncb1 as <-. clear Hzcb1.
      zstep. cbv beta.
      zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        zstep. if_cases Kq; zify_cond Kq.
        + (* [comment removed for export] *)
          do_store o (wb 34) ltac:(apply byte_list_eq; reflexivity).
          mk_inv INV2 (q + 1). { apply sufx_upd; [eapply sufx_mono; [exact SX| lia]| lia| left; lia]. }
          step. eapply (l_adv q o); [lia| lia| lia| exact INV2].
        + (* [comment removed for export] *)
          mk_inv INV2 (q + 1). { eapply sufx_mono; [exact SX| lia]. }
          eapply sl_b8; [| lia| lia| lia| exact INV2].
          intros buf' m' x10' cb' INV' Hcb' NZ'. pose proof (orig_nth_nz _ _ Hcb' NZ' ltac:(lia)). apply (IHkk (q + 1) (o + 1) buf' m' cb'); try assumption; lia.
      - (* [comment removed for export] *)
        rd INV1 (q + 1) c2.
        zstep. cbv beta. zstep. if_cases Kq2; zify_cond Kq2.
        + (* [comment removed for export] *)
          mk_inv INV2 (q + 1). { eapply sufx_mono; [exact SX| lia]. }
          eapply sl_b8; [| lia| lia| lia| exact INV2].
          intros buf' m' x10' cb' INV' Hcb' NZ'. pose proof (orig_nth_nz _ _ Hcb' NZ' ltac:(lia)). apply (IHkk (q + 1) (o + 1) buf' m' cb'); try assumption; lia.
        + (* [comment removed for export] *)
          assert (Ec2 : c2 = wb 34) by (apply bv_eq; rewrite Kq2; reflexivity).
          do_store (o + 1) (wb 34) ltac:(apply byte_list_eq; reflexivity).
          mk_inv INV2 (q + 2).
          { apply sufx_upd; [eapply sufx_mono; [exact SX| lia]| lia|].
            destruct (Z.eq_dec (o + 1) (q + 1)) as [E|NE]; [right; rewrite E, Hnc2, Ec2; reflexivity| left; lia]. }
          zstep. zstep. step.
          replace (A + o + 1) with (A + (o + 1)) by lia. replace (A + q + 1) with (A + (q + 1)) by lia.
          eapply sl_b8; [| lia| lia| lia| replace (q + 1 + 1) with (q + 2) by lia; exact INV2].
          intros buf' m' x10' cb' INV' Hcb' NZ'. pose proof (orig_nth_nz _ _ Hcb' NZ' ltac:(lia)).
          replace (o + 1 + 1) with (o + 2) by lia. replace (q + 1 + 1) with (q + 2) in * by lia.
          apply (IHkk (q + 2) (o + 2) buf' m' cb'); try assumption; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma l_string : forall j i buf m x6,
      (Z.to_nat (len - j) <= K)%nat -> 0 <= i <= j -> j < len -> inv buf m j ->
      nth_error orig (Z.to_nat j) = Some (wb 34) ->
      evt psegs POST (ST 0x139c8 m (Z_to_bv 64 34) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + j)) x6).
    Proof.
      intros j i buf m x6 HK Hij Hj INV Hb. inv_parts INV.
      do_store i (wb 34) ltac:(apply byte_list_eq; reflexivity).
      mk_inv INV1 (j + 1).
      { apply sufx_upd; [eapply sufx_mono; [exact SX| lia]| lia|]. destruct (Z.eq_dec i j) as [->|]; [right; exact Hb| left; lia]. }
      clear SX INV. inv_parts INV1. clear ARR0 MU0 WM0 MI0.
      rd INV1 (j + 1) c1.
      zstep. cbv beta. zstep. zstep. zstep.
      replace (A + j + 1) with (A + (j + 1)) by lia. replace (A + i + 1) with (A + (i + 1)) by lia.
      if_cases Kz; zify_cond Kz.
      - eapply (IH (j + 1) (i + 1)); [lia| lia| lia| exact INV1].
      - zstep. zstep. eapply (sl_cc (Z.to_nat (len - (j + 1))) (j + 1) (i + 1)); [lia| lia| lia| lia| exact INV1| exact Hnc1].
    Qed.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma ol_loop : forall (kk : nat) q i buf m x5 x6,
      (Z.to_nat (len - q) <= kk)%nat -> (Z.to_nat (len - q) < K)%nat ->
      0 <= i <= q -> q <= len -> inv buf m q ->
      evt psegs POST (ST 0x13a44 m (Z_to_bv 64 (A + q)) (Z_to_bv 64 (A + i)) x5 x6).
    Proof.
      induction kk as [|kk IHkk]; intros q i buf m x5 x6 Hkk HK Hiq Hq INV.
      all: inv_parts INV; rd INV q cb.
      all: zstep; cbv beta; zstep; if_cases Kz; zify_cond Kz; [apply (IH q i buf m); [lia| lia| lia| exact INV]|].
      { exfalso. lia. }
      zstep. zstep. replace (A + q + 1) with (A + (q + 1)) by lia.
      assert (INV1 : inv buf m (q + 1)).
      { split; [exact ARR|]. split; [eapply sufx_mono; [exact SX| lia]| split; [exact MU| split; [exact WM| exact MI]]]. }
      if_cases Knl; zify_cond Knl.
      - apply (IHkk (q + 1) i buf m); [lia| lia| lia| lia| exact INV1].
      - step. apply (IH (q + 1) i buf m); [lia| lia| lia| exact INV1].
    Qed.

    (* [comment removed for export] *)
    Lemma ml_loop : forall (kk : nat) q i buf m x5 x6,
      (Z.to_nat (len - q) <= kk)%nat -> (Z.to_nat (len - q) < K)%nat ->
      0 <= i <= q -> q <= len -> inv buf m q ->
      evt psegs POST (ST 0x13a6c m (Z_to_bv 64 (A + q)) (Z_to_bv 64 (A + i)) x5 x6).
    Proof.
      induction kk as [|kk IHkk]; intros q i buf m x5 x6 Hkk HK Hiq Hq INV.
      all: inv_parts INV; rd INV q cb.
      all: zstep; cbv beta; zstep; if_cases Kst; zify_cond Kst.
      1:{ exfalso. lia. }
      1:{ zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|]. step. apply (IH q i buf m); [lia| lia| lia| exact INV]. }
      - rd INV (q + 1) c2.
        zstep. cbv beta. zstep. if_cases Ksl; zify_cond Ksl.
        + (* [comment removed for export] *)
          zstep. step. replace (A + q + 2) with (A + (q + 2)) by lia.
          apply (IH (q + 2) i buf m); [lia| lia| lia|].
          split; [exact ARR|]. split; [eapply sufx_mono; [exact SX| lia]| split; [exact MU| split; [exact WM| exact MI]]].
        + zstep. replace (A + q + 1) with (A + (q + 1)) by lia.
          apply (IHkk (q + 1) i buf m); [lia| lia| lia| lia|].
          split; [exact ARR|]. split; [eapply sufx_mono; [exact SX| lia]| split; [exact MU| split; [exact WM| exact MI]]].
      - zstep. if_cases Kz; zify_cond Kz.
        + zstep. replace (A + q + 1) with (A + (q + 1)) by lia.
          apply (IHkk (q + 1) i buf m); [lia| lia| lia| lia|].
          split; [exact ARR|]. split; [eapply sufx_mono; [exact SX| lia]| split; [exact MU| split; [exact WM| exact MI]]].
        + step. apply (IH q i buf m); [lia| lia| lia| exact INV].
    Qed.

    (* [comment removed for export] *)
    Lemma l_slash : forall j i buf m x6,
      (Z.to_nat (len - j) <= K)%nat -> 0 <= i <= j -> j < len -> inv buf m j ->
      evt psegs POST (ST 0x13a30 m (Z_to_bv 64 47) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + j)) x6).
    Proof.
      intros j i buf m x6 HK Hij Hj INV. inv_parts INV.
      rd INV (j + 1) c1.
      zstep. cbv beta. zstep. if_cases Kst; zify_cond Kst.
      - (* [comment removed for export] *)
        zstep. zstep. replace (A + j + 2) with (A + (j + 2)) by lia.
        apply (ml_loop (Z.to_nat (len - (j + 2))) (j + 2) i buf m); [lia| lia| lia| lia|].
        split; [exact ARR|]. split; [eapply sufx_mono; [exact SX| lia]| split; [exact MU| split; [exact WM| exact MI]]].
      - zstep. replace (A + j + 1) with (A + (j + 1)) by lia. zstep. if_cases Ksl; zify_cond Ksl.
        + (* [comment removed for export] *)
          apply (IH (j + 1) i buf m); [lia| lia| lia|].
          split; [exact ARR|]. split; [eapply sufx_mono; [exact SX| lia]| split; [exact MU| split; [exact WM| exact MI]]].
        + (* [comment removed for export] *)
          zstep. replace (A + j + 2) with (A + (j + 2)) by lia.
          apply (ol_loop (Z.to_nat (len - (j + 2))) (j + 2) i buf m); [lia| lia| lia| lia|].
          split; [exact ARR|]. split; [eapply sufx_mono; [exact SX| lia]| split; [exact MU| split; [exact WM| exact MI]]].
    Qed.

    (* [comment removed for export] *)
    Ltac dispatch :=
      zstep; zstep; step; try rewrite sx32_lit by lia; zstep; step;
      lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity])
      | _ => idtac
      end.

    (* [comment removed for export] *)
    Lemma l_head : forall j i buf m x5 x6,
      (Z.to_nat (len - j) = K) -> 0 <= i <= j -> j <= len -> inv buf m j ->
      evt psegs POST (ST 0x139a8 m (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + i)) x5 x6).
    Proof.
      intros j i buf m x5 x6 HK Hij Hj INV. inv_parts INV.
      rd INV j cb.
      zstep. zstep. cbv beta. zstep. if_cases Kbig; zify_cond Kbig.
      { (* [comment removed for export] *) eapply l_default; [lia| lia| lia| exact INV| exact Hncb]. }
      destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0|N0].
      { (* [comment removed for export] *)
        rewrite E0. dispatch.
        do_store i (wb 0) ltac:(apply byte_list_eq; reflexivity).
        zstep. finish.
        eexists. split; [exact ARR|]. split; [rewrite upd_length; exact Lbuf|].
        eapply nth_error_In. apply nth_error_upd_same. lia. }
      assert (Hjl : j < len) by lia.
      destruct (Z.eq_dec (bv_unsigned cb) 34) as [E34|N34].
      { rewrite E34. dispatch. eapply l_string; [lia| lia| lia| exact INV|]. rewrite Hncb. f_equal. apply bv_eq. rewrite E34. reflexivity. }
      destruct (Z.eq_dec (bv_unsigned cb) 47) as [E47|N47].
      { rewrite E47. dispatch. eapply l_slash; [lia| lia| lia| exact INV]. }
      assert (WS : forall c, c = 9 \/ c = 10 \/ c = 13 \/ c = 32 -> bv_unsigned cb = c ->
                evt psegs POST (ST 0x139b4 m (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + j)) x6)).
      { intros c Hc E. rewrite E. destruct Hc as [->|[->|[->| ->]]]; dispatch; (eapply l_ws; [lia| lia| lia| exact INV]). }
      destruct (Z.eq_dec (bv_unsigned cb) 9) as [E|N9]; [apply (WS 9); [tauto| exact E]|].
      destruct (Z.eq_dec (bv_unsigned cb) 10) as [E|N10]; [apply (WS 10); [tauto| exact E]|].
      destruct (Z.eq_dec (bv_unsigned cb) 13) as [E|N13]; [apply (WS 13); [tauto| exact E]|].
      destruct (Z.eq_dec (bv_unsigned cb) 32) as [E|N32]; [apply (WS 32); [tauto| exact E]|].
      clear WS.
      (* [comment removed for export] *)
      pose proof (jt_read m (bv_unsigned cb) MI ltac:(lia)) as RT.
      rewrite (jt_sel_default (bv_unsigned cb)) in RT by assumption.
      dispatch. eapply l_default; [lia| lia| lia| exact INV| exact Hncb].
    Qed.
  End Head.

  (* [comment removed for export] *)
  Lemma head_all : forall (K : nat) j i buf m x5 x6,
    (Z.to_nat (len - j) = K) -> 0 <= i <= j -> j <= len -> inv buf m j ->
    evt psegs POST (ST 0x139a8 m (Z_to_bv 64 (A + j)) (Z_to_bv 64 (A + i)) x5 x6).
  Proof.
    induction K as [K IHK] using lt_wf_ind. apply l_head.
    intros j i buf m x5 x6 HK Hij Hj INV. eapply (IHK (Z.to_nat (len - j))); [exact HK| reflexivity| exact Hij| exact Hj| exact INV].
  Qed.
End Proofs.

Lemma minify_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (s : list byte),
  a0 = wz A ->
  u8arr psegs m A (s ++ [wb 0]) ->
  ~ In (wb 0) s ->
  mem_inv psegs m ->
  evt psegs (minify_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A (S (length s)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1397c) fc None m (seg_rom psegs)).
Proof.
  intros until s. intros A0 ARR NONUL MI. unfold wz in A0. subst a0.
  pose proof (u8arr_bound _ _ _ _ ARR) as AB. rewrite length_app in AB. cbn [length] in AB.
  assert (AB' : 0 <= A /\ A + Z.of_nat (length s) + 1 <= 2^64) by lia.
  pose proof (munch_refl [(A, A + Z.of_nat (S (length s)))] m) as MU. pose proof (wmono_refl psegs m) as WM.
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    zstep. finish. exists (s ++ [wb 0]). split; [exact ARR|]. split; [rewrite length_app; cbn; lia|]. apply in_or_app. right. left. reflexivity.
  - do 9 zstep.
    eapply evt_eq.
    2:{ eapply (head_all ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A s NONUL AB'
                 (Z.to_nat (Z.of_nat (length s) - 0)) 0 0 (s ++ [wb 0]) m); [reflexivity| lia| lia|].
        split; [exact ARR|]. split; [apply sufx_refl|]. split; [exact MU|]. split; [exact WM| exact MI]. }
    unfold mkR. rewrite Z.add_0_r. reflexivity.
Qed.
End CJ_minify.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pvalue_A.CJ_delete.
Import CJ_minify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaSplit.
(* [comment removed for export] *)
Local Ltac word_eq_tac ::= first [ exact eq_refl
  | lazymatch goal with |- Z_to_bv 64 ?x = Z_to_bv 64 ?y => assert (x <> y) by (clear; lia) end; fail 1
  | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FUZZ_ENTRY : Z := 0x125ec.
Definition FUZZ_STACK : Z := 64 + PARSE_DOC_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nul_split : forall (l : list byte), In (wb 0) l -> exists str rest, l = str ++ wb 0 :: rest /\ ~ In (wb 0) str.
Proof.
  induction l as [|b l IH]; intros Hin; [destruct Hin|].
  destruct (base.decide (b = wb 0)) as [->|NE].
  - exists [], l. split; [reflexivity| intros []].
  - destruct Hin as [E|Hin]; [exfalso; exact (NE E)|]. (nelim (IH Hin) 4%nat; intros str rest -> NN).
    exists (b :: str), rest. split; [reflexivity|]. intros [E|H]; [exact (NE E)| exact (NN H)].
Qed.

(* [comment removed for export] *)
Lemma bytes_exist : forall (m : word -> option byte) (B : Z) (k : nat),
  0 <= B -> B + Z.of_nat k <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat k -> m (wa (B + i)) <> None) ->
  exists bs, length bs = k /\ bytes_at psegs m B bs.
Proof.
  intros m B k HB HK HM. revert B HB HK HM. induction k as [|k IH]; intros B HB HK HM.
  - exists []. split; [reflexivity|]. apply bytes_at_nil. lia.
  - destruct (m (wa B)) as [b|] eqn:Eb.
    2:{ exfalso. apply (HM 0 ltac:(lia)). rewrite Z.add_0_r. exact Eb. }
    destruct (IH (B + 1) ltac:(lia) ltac:(lia)) as (bs & L & BY). (* [comment removed for export] *)
    { intros i Hi. replace (B + 1 + i) with (B + (1 + i)) by lia. apply HM. lia. }
    exists (b :: bs). split; [cbn; lia|].
    change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = O) by lia. subst i.
      cbn. rewrite Z.add_0_r. unfold mrd. rewrite Eb. reflexivity.
    + cbn [length Z.of_nat Pos.of_succ_nat]. exact BY.
Qed.

(* [comment removed for export] *)
Lemma dpres_weaken : forall LB LB' SP SP' m m',
  dpres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> dpres LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL. eapply magree_mono; [exact H|]. cbv beta.
  intros a [Hc Hn]. split; [|exact Hn].
  destruct Hc as [Hc|[Hc|(A & n & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists A, n. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma dpres_of_cj_pres : forall LB SP m m', cj_pres LB SP m m' -> dpres LB SP m m'.
Proof. intros LB SP m m' H a Ha [Hc _]. apply H; assumption. Qed.

(* [comment removed for export] *)
Lemma dpres_rw_cells_stack : forall LB SP m m' A cs,
  dpres LB SP m m' -> rw_cells psegs m A cs -> SP <= A -> alloc_ceiling <= SP -> rw_cells psegs m' A cs.
Proof.
  intros LB SP m m' A cs HP H HS HC. try rewrite alloc_ceiling_eq in HC.
  eapply rw_cells_magree; [exact HP| exact H|]. intros a Ha. split; [left; lia| unfold PGERROR; lia].
Qed.

Lemma dpres_bytes_at_block : forall LB SP m m' D n bs,
  cblock_range D n -> In (D, n) LB ->
  dpres LB SP m m' -> bytes_at psegs m D bs -> Z.of_nat (length bs) <= n -> bytes_at psegs m' D bs.
Proof.
  intros LB SP m m' D n bs HR HD HP BY LEN.
  (nelimp HR 5%nat; intros R1 R2 R3 R4 R5). unfold PIMG_LO, PIMG_HI in R5.
  eapply bytes_at_magree; [exact HP| exact BY|]. intros a Ha. split.
  - right; right. exists D, n. split; [exact HD| lia].
  - unfold PGERROR. lia.
Qed.

(* [comment removed for export] *)
Lemma cj_pres_of_munch : forall LB SP m m' lo hi,
  munch [(lo, hi)] m m' -> wmono psegs m m' ->
  (hi <= lo \/ (hi <= SP /\ (hi <= PDATA_LO \/ PIMG_HI <= lo) /\ forall A n, In (A, n) LB -> A + n <= lo \/ hi <= A)) ->
  cj_pres LB SP m m'.
Proof.
  intros LB SP m m' lo hi MU WM H a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
  destruct H as [H|(H1 & H2 & H3)]; [lia|].
  destruct Hc as [Hs|[[Hd _]|(A & n & Hin & Hr)]]; [lia| lia|]. pose proof (H3 _ _ Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma slack_mod8 : forall P c, P <= c * 8 -> (- P) mod 8 <= c * 8 - P.
Proof.
  intros P c H. replace (c * 8 - P) with (- P + c * 8) by lia.
  rewrite <- (Z.mod_add (- P) c 8) by lia. apply Z.mod_le; lia.
Qed.

(* [comment removed for export] *)
Lemma split4 : forall (data : list byte), (4 <= length data)%nat ->
  data = firstn 4 data ++ skipn 4 data /\ length (firstn 4 data) = 4%nat.
Proof. intros data H. split; [symmetry; apply firstn_skipn| rewrite firstn_length; lia]. Qed.

(* [comment removed for export] *)
Lemma u8arr_mid : forall m A l1 l2 l3,
  u8arr psegs m A (l1 ++ l2 ++ l3) -> u8arr psegs m (A + Z.of_nat (length l1)) l2.
Proof.
  intros m A l1 l2 l3 [BY (W0 & W1 & WR)]. rewrite !length_app in W1, WR.
  apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [BY _].
  split; [exact BY|]. split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + Z.of_nat (length l1) + i) with (A + (Z.of_nat (length l1) + i)) by lia. apply WR. lia.
Qed.

Lemma copy_text_u8arr : forall m C n pre str rest,
  rw_cells psegs m C [CB n (pre ++ str ++ wb 0 :: rest)] -> length pre = 4%nat ->
  u8arr psegs m (C + 4) (str ++ [wb 0]).
Proof.
  intros m C n pre str rest H L. apply u8arr_of_rw_cells in H.
  replace (pre ++ str ++ wb 0 :: rest) with (pre ++ (str ++ [wb 0]) ++ rest) in H by (rewrite <- !app_assoc; reflexivity).
  apply u8arr_mid in H. rewrite L in H. exact H.
Qed.

Section S.
  Variable HI : cj_heap_iface.
  Hypothesis PARSE : parse_wopts_stmt HI.
  Hypothesis PRB : pbuffered_stmt HI.
  Hypothesis PRF : cjprint_stmt HI.
  Hypothesis PRU : cjprintu_stmt HI.

  Definition fuzz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (SPB : Z) (LB : list cblock) (D size : Z) (data : list byte) (lo : Z) (m : word -> option byte)
      : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (errv' : word) (LB' LX : list cblock),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ a0 = wz 0
      /\ frm0 fc' /\ (forall k : bv 5, fp_callee_saved k -> reg_get F' k = reg_get F k)
      /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
      /\ CJST m' /\ rw_cells psegs m' PERRNO [C4 errv']
      /\ LHEAP HI SPB LB' m' mo' /\ Permutation LB' (LB ++ LX)
      /\ dpres LB (bv_unsigned sp) m m'
      /\ (size <= 4 \/ bytes_at psegs m' D data).

  Definition fuzz_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB : list cblock) (D size : Z) (data : list byte) (lo : Z) (errv : word),
      LHEAP HI SPB LB m mo ->
      (size <= 4 \/ (In (D, size) LB /\ bytes_at psegs m D data /\ Z.of_nat (length data) = size)) ->
      0 <= size < 2^26 ->
      CJST m -> rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m ->
      stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - FUZZ_STACK ->
      bv_unsigned sp <= SPB -> SPB < 2^62 -> bv_unsigned sp mod 16 = 0 ->
      frm0 fc -> tp = wz PTP ->
      a0 = wz D -> a1 = wz size ->
      SCPS psegs (fuzz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LB D size data lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz FUZZ_ENTRY) fc None m (seg_rom psegs)) mo.

  (* [comment removed for export] *)
  Ltac slv := (* [comment removed for export] *)
              unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK, PRINT_STACK, PV_STACK, PV_BASE, DELETE_STACK, RMALLOC_STACK in *; lia.

  Section Body.
    (* [comment removed for export] *)
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
              (m0 : word -> option byte) (SPB : Z) (LB : list cblock) (D size : Z) (data : list byte) (lo : Z).
    Hypothesis SPB1 : bv_unsigned sp <= SPB.
    Hypothesis SPB2 : SPB < 2^62.
    Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - FUZZ_STACK.
    Hypothesis TP : tp = wz PTP.
    Hypothesis SZ : 0 <= size < 2^26.

    Notation SPF := (bv_unsigned sp + -64).
    Notation POST := (fuzz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LB D size data lo m0).
    Notation FRAME mm fj := (rw_cells psegs mm (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    (* [comment removed for export] *)
    Notation LST pc Fv fcv mm rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
      (MS (mkR rav (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fv (Z_to_bv 64 pc) fcv None mm (seg_rom psegs)).

    (* [comment removed for export] *)
    Definition linv (LBX : list cblock) (mm : word -> option byte) (mo : Model) (fj : list byte) (Fv : bvmap 5 word) (fcv : bv 32) : Prop :=
      LHEAP HI SPB LBX mm mo /\ stk psegs mm lo SPF /\ FRAME mm fj /\ CJST mm
      /\ (exists e, rw_cells psegs mm PERRNO [C4 e]) /\ mem_inv psegs mm
      /\ dpres LB (bv_unsigned sp) m0 mm /\ frm0 fcv /\ (forall k : bv 5, fp_callee_saved k -> reg_get Fv k = reg_get F k)
      /\ (size <= 4 \/ (cblock_range D size /\ In (D, size) LB /\ bytes_at psegs mm D data /\ Z.of_nat (length data) = size)).

    Lemma SPFeq : bv_unsigned (Z_to_bv 64 SPF) = SPF.
    Proof. apply unsigned_lit. slv. Qed.

    Lemma SPFal : SPF mod 16 = 0.
    Proof. replace SPF with (bv_unsigned sp - 64) by lia. rewrite Zminus_mod, SPAL. reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma fuzz_ret : forall LBX LX mm mo fj Fv fcv rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
      linv LBX mm mo fj Fv fcv -> Permutation LBX (LB ++ LX) ->
      SCPS psegs POST (LST 0x126f8 Fv fcv mm rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31) mo.
    Proof.
      intros until x31. intros (HL & ST & FR & CJ & [e ERR] & MI & PR & FRM & FA & DAT) HP.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      do 10 step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply scps_done. unfold fuzz_post.
      nexists 21%nat. split; [reflexivity|].
      split; [reflexivity|]. split; [exact FRM|]. split; [exact FA|]. split; [exact MI|]. split; [exact ST|].
      split; [exact CJ|]. split; [exact ERR|]. split; [exact HL|]. split; [exact HP|]. split; [exact PR|].
      destruct DAT as [H|(_ & _ & H & _)]; [left; exact H| right; exact H].
    Qed.

    (* [comment removed for export] *)
    Lemma linv_pres_F : forall LBX mm mo fj Fv fcv LBX' mm' mo' e' LBY Fv' fcv',
      linv LBX mm mo fj Fv fcv ->
      cj_pres LBY SPF mm mm' -> (forall b, In b LB -> In b LBY) ->
      LHEAP HI SPB LBX' mm' mo' -> stk psegs mm' lo SPF -> CJST mm' -> rw_cells psegs mm' PERRNO [C4 e'] -> mem_inv psegs mm' ->
      frm0 fcv' -> (forall k : bv 5, fp_callee_saved k -> reg_get Fv' k = reg_get Fv k) ->
      linv LBX' mm' mo' fj Fv' fcv'.
    Proof.
      intros until fcv'. intros (HL & ST & FR & CJ & _ & MI & PR & FRM & FA & DAT) PRS0 HLL HL' ST' CJ' ERR' MI' FRM' FA'.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      assert (PRS : cj_pres LB SPF mm mm') by (eapply cj_pres_weaken; [exact PRS0| lia| exact HLL]).
      split; [exact HL'|]. split; [exact ST'|]. split.
      { eapply cj_pres_rw_cells; [exact PRS| exact FR| left; lia]. }
      split; [exact CJ'|]. split; [exists e'; exact ERR'|]. split; [exact MI'|]. split.
      { eapply dpres_trans; [exact PR|]. apply dpres_of_cj_pres. eapply cj_pres_weaken; [exact PRS| lia| intros b Hb; exact Hb]. }
      split; [exact FRM'|]. split; [intros k Hk; rewrite (FA' k Hk); apply FA; exact Hk|].
      destruct DAT as [H|(HR & HD & BY & LEN)]; [left; exact H| right]. split; [exact HR|]. split; [exact HD|]. split; [|exact LEN].
      eapply dpres_bytes_at_block; [exact HR| exact HD| apply dpres_of_cj_pres; exact PRS| exact BY| lia].
    Qed.

    Lemma linv_pres : forall LBX mm mo fj Fv fcv LBX' mm' mo' e' LBY,
      linv LBX mm mo fj Fv fcv ->
      cj_pres LBY SPF mm mm' -> (forall b, In b LB -> In b LBY) ->
      LHEAP HI SPB LBX' mm' mo' -> stk psegs mm' lo SPF -> CJST mm' -> rw_cells psegs mm' PERRNO [C4 e'] -> mem_inv psegs mm' ->
      linv LBX' mm' mo' fj Fv fcv.
    Proof.
      intros until LBY. intros LI PRS HLL HL' ST' CJ' ERR' MI'. (nelimp LI 10%nat; intros _ _ _ _ _ _ _ FRM _ _).
      eapply linv_pres_F; [exact LI| exact PRS| exact HLL| exact HL'| exact ST'| exact CJ'| exact ERR'| exact MI'| exact FRM| intros; reflexivity].
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_delete : forall LBX mm mo fj Fv fcv (r : Z) (d : nat) (B : list cblock)
        rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
      linv LBX mm mo fj Fv fcv -> Permutation (B ++ LB) LBX -> cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      SCPS psegs POST (LST 0x126f0 Fv fcv mm rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x19 x20 x21 x28 x29 x30 x31) mo.
    Proof.
      intros until x31. intros LI HP CH Hd. (nelimp LI 10%nat; intros HL ST FR CJ [e ERR] MI PR FRM FA DAT).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. step.
      apply evt_done. cbv beta.
      eapply scps_bind.
      { pose proof (cjson_delete_spec HI d) as DEL. unfold delete_spec_at, DELETE_ENTRY, wz in DEL.
        eapply DEL with (lo := lo) (LR := LB) (B := B) (T := CJ_PRINTABLE); rewrite ?E1;
          first [exact HL| exact CH| exact HP| exact CJ| exact ST| exact ERR| exact MI| unfold wz in TP; exact TP| reflexivity| slv]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LR2 -> MI2 ST2 CJ2 ERR2 HL2 HP2 PR2)
.
      rewrite E1 in ST2, PR2.
      replace (ret_pc (Z_to_bv 64 0x126f8)) with (Z_to_bv 64 0x126f8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply fuzz_ret with (LX := []).
      - eapply linv_pres; [exact LI| exact PR2| intros b Hb; exact Hb| exact HL2| exact ST2| exact CJ2| exact ERR2| exact MI2].
      - rewrite app_nil_r. exact HP2.
    Qed.

    Lemma blocks_apart : forall LBX mm mo A n A' n',
      LHEAP HI SPB LBX mm mo -> In (A, n) LBX -> In (A', n') LBX -> A <> A' -> A + n <= A' \/ A' + n' <= A.
    Proof. intros. eapply (lh_blocks_disjoint HI); eauto. Qed.

    (* [comment removed for export] *)
    Lemma fuzz_copy : forall LBX mm mo fj Fv fcv (r : Z) (d : nat) (B : list cblock) (C : Z) (junk pre str rest : list byte)
        rav x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
      linv ((C, size) :: LBX) mm mo fj Fv fcv -> Permutation (B ++ LB) LBX -> cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      rw_cells psegs mm C [CB (Z.to_nat size) junk] -> cblock_range C size -> ~ In C (map fst LBX) ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      SCPS psegs POST (LST 0x126d0 Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) (Z_to_bv 64 C) x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) x19 x20 x21 x28 x29 x30 x31) mo.
    Proof using CEIL LO SPAL SPB1 SPB2 SZ TP.
      intros until x31. intros LI HP CH Hd BLK CR CN SZ4 DEQ LPRE NONUL.
      (nelimp LI 10%nat; intros HL ST FR CJ [e ERR] MI PR FRM FA DAT).
      destruct DAT as [?|(DR & DIN & BY & LEN)]; [exfalso; lia|].
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1.
      (nelimp CR 5%nat; intros C1 C2 C3 C4 C5). try rewrite alloc_ceiling_eq in C4. unfold PIMG_LO, PIMG_HI in C5.
      (nelimp DR 5%nat; intros D1 D2 D3 D4 D5). try rewrite alloc_ceiling_eq in D4. unfold PIMG_LO, PIMG_HI in D5.
      assert (DINX : In (D, size) LBX). { eapply Permutation_in; [exact HP|]. apply in_or_app. right. exact DIN. }
      assert (CND : C <> D). { intros ->. apply CN. apply (in_map fst) in DINX. exact DINX. }
      pose proof (blocks_apart _ _ _ _ _ _ _ HL ltac:(left; reflexivity) ltac:(right; exact DINX) CND) as SEPCD.
      assert (BSEP : forall A' n', In (A', n') B -> C + size <= A' \/ A' + n' <= C).
      { intros A' n' Hin. assert (HinX : In (A', n') LBX) by (eapply Permutation_in; [exact HP|]; apply in_or_app; left; exact Hin).
        eapply (blocks_apart _ _ _ _ _ _ _ HL); [left; reflexivity| right; exact HinX|].
        intros ->. apply CN. apply (in_map fst) in HinX. exact HinX. }
      assert (LSEP : forall A' n', In (A', n') LB -> C + size <= A' \/ A' + n' <= C).
      { intros A' n' Hin. assert (HinX : In (A', n') LBX) by (eapply Permutation_in; [exact HP|]; apply in_or_app; right; exact Hin).
        eapply (blocks_apart _ _ _ _ _ _ _ HL); [left; reflexivity| right; exact HinX|].
        intros ->. apply CN. apply (in_map fst) in HinX. exact HinX. }
      assert (LENN : length data = Z.to_nat size) by lia.
      unfold PERRNO in ERR.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. step. step. step.
      (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (memcpy_spec) with (src := data) (junk := junk); rewrite ?unsigned_lit by lia;
          first [exact BY| exact LENN| exact BLK| lia| exact MI]. }
      cbv beta. intros ms3 PO3.
      (nelim PO3 21%nat; intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m3 -> MU3 WM3 MI3 BLK3 BY3).
      rewrite !unsigned_lit in MU3 by lia. rewrite !unsigned_lit in BLK3 by lia. rewrite !unsigned_lit in BY3 by lia.
      replace (ret_pc (Z_to_bv 64 0x126e0)) with (Z_to_bv 64 0x126e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (rw_cells_transport psegs) in FR; [| exact MU3| exact WM3| cbn; lia].
      eapply (rw_cells_transport psegs) in ERR; [| exact MU3| exact WM3| cbn; lia].
      eapply (stk_transport_disjoint psegs) in ST; [| exact MU3| exact WM3| cbn; lia].
      pose proof (lh_frame HI _ _ _ m3 _ _ HL MU3 WM3 ltac:(constructor; [do 4 right; exists C, size; split; [left; reflexivity| cbn; lia]| constructor])) as HL3.
      pose proof (CJST_frame _ _ m3 CJ MU3 WM3 ltac:(unfold PDATA_LO, PIMG_HI; intros lo' hi' [E2|[]]; inversion E2; subst; lia)) as CJ3.
      pose proof (cj_chain_frame _ _ m3 _ _ _ _ CH MU3 WM3 ltac:(intros A' n' Hin; cbn; split; [pose proof (BSEP A' n' Hin); lia| exact I])) as CH3.
      assert (PR3 : dpres LB (bv_unsigned sp) m0 m3).
      { eapply dpres_trans; [exact PR|]. apply dpres_of_cj_pres. eapply cj_pres_of_munch; [exact MU3| exact WM3|].
        right. split; [lia|]. split; [unfold PDATA_LO, PIMG_HI; lia|]. intros A' n' Hin. pose proof (LSEP A' n' Hin). lia. }
      clear MU3 WM3 MI CJ CH PR HL BLK BY.
      (* [comment removed for export] *)
      zstep. step.
      eapply evt_cut.
      { eapply (minify_spec) with (A := C + 4) (s := str); [reflexivity| | exact NONUL| exact MI3].
        eapply copy_text_u8arr; [| exact LPRE]. rewrite <- DEQ. exact BLK3. }
      cbv beta. intros ms4 PO4.
      (nelim PO4 16%nat; intros t0d t1d a0d a1d a2d a3d a4d a5d a6d a7d m4 -> MU4 WM4 MI4 _).
      replace (ret_pc (Z_to_bv 64 0x126e8)) with (Z_to_bv 64 0x126e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (SL : Z.of_nat (length str) + 5 + Z.of_nat (length rest) = size).
      { rewrite DEQ, !length_app in LEN. cbn [length] in LEN. lia. }
      eapply (rw_cells_transport psegs) in FR; [| exact MU4| exact WM4| cbn; lia].
      eapply (rw_cells_transport psegs) in ERR; [| exact MU4| exact WM4| cbn; lia].
      eapply (stk_transport_disjoint psegs) in ST; [| exact MU4| exact WM4| cbn; lia].
      eapply (bytes_at_transport psegs) in BY3; [| exact MU4| cbn; lia].
      pose proof (lh_frame HI _ _ _ m4 _ _ HL3 MU4 WM4 ltac:(constructor; [do 4 right; exists C, size; split; [left; reflexivity| cbn; lia]| constructor])) as HL4.
      pose proof (CJST_frame _ _ m4 CJ3 MU4 WM4 ltac:(unfold PDATA_LO, PIMG_HI; intros lo' hi' [E2|[]]; inversion E2; subst; lia)) as CJ4.
      pose proof (cj_chain_frame _ _ m4 _ _ _ _ CH3 MU4 WM4 ltac:(intros A' n' Hin; cbn; split; [pose proof (BSEP A' n' Hin); lia| exact I])) as CH4.
      assert (PR4 : dpres LB (bv_unsigned sp) m0 m4).
      { eapply dpres_trans; [exact PR3|]. apply dpres_of_cj_pres. eapply cj_pres_of_munch; [exact MU4| exact WM4|].
        right. split; [lia|]. split; [unfold PDATA_LO, PIMG_HI; lia|]. intros A' n' Hin. pose proof (LSEP A' n' Hin). lia. }
      clear MU4 WM4 MI3 CJ3 CH3 PR3 HL3 BLK3.
      (* [comment removed for export] *)
      step. step.
      replace (Z_to_bv 64 0x151e0) with (wz PFREE) by reflexivity.
      apply evt_done. cbv beta.
      eapply scps_bind.
      { eapply (lh_free HI) with (lo := lo) (A := C) (n := size); rewrite ?E1;
          first [exact HL4| left; reflexivity| exact ST| exact ERR| exact MI4| exact TP| reflexivity| slv]. }
      cbv beta. intros ms5 mo5 PO5.
      (nelim PO5 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m5 -> MI5 ST5 ERR5 PR5 HL5)
.
      rewrite E1 in ST5, PR5. cbn [cb_remove] in PR5, HL5. rewrite Z.eqb_refl in PR5, HL5.
      replace (ret_pc (Z_to_bv 64 0x126f0)) with (Z_to_bv 64 0x126f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply fuzz_delete; [| exact HP| | exact Hd].
      - split; [exact HL5|]. split; [exact ST5|]. split. { eapply cj_pres_rw_cells; [exact PR5| exact FR| left; lia]. }
        split; [eapply CJST_pres; [exact PR5| exact CJ4]|]. split; [exists e; exact ERR5|]. split; [exact MI5|]. split.
        { eapply dpres_trans; [exact PR4|]. apply dpres_of_cj_pres. eapply cj_pres_weaken; [exact PR5| lia|].
          intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. right. exact Hb. }
        split; [exact FRM|]. split; [exact FA|]. right. split; [exact DR|]. split; [exact DIN|]. split; [|exact LEN].
        eapply cj_pres_bytes_at; [exact PR5| exact BY3|]. right; right. exists D, size. split; [exact DINX| lia].
      - eapply cj_chain_pres; [exact CH4| exact PR5|]. intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. left. exact Hb.
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_min : forall LBX mm mo fj Fv fcv (r : Z) (d : nat) (B : list cblock) (b0 : byte) (pre str rest : list byte)
        rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
      linv LBX mm mo fj Fv fcv -> Permutation (B ++ LB) LBX -> cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      SCPS psegs POST (LST 0x126bc Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) (Z_to_bv 64 (bv_unsigned b0)) x20 x21 x28 x29 x30 x31) mo.
    Proof using CEIL LO SPAL SPB1 SPB2 SZ TP.
      intros until x31. intros LI HP CH Hd SZ4 DEQ LPRE NONUL.
      (nelimp LI 10%nat; intros HL ST FR CJ [e ERR] MI PR FRM FA DAT).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1.
      pose proof (bv_unsigned_in_range 8 b0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
      unfold PERRNO in ERR.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. step. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evt_done. cbv beta. eapply fuzz_delete; [exact LI| exact HP| exact CH| exact Hd].
      - step. step.
        replace (Z_to_bv 64 0x15320) with (wz PMALLOC) by reflexivity.
        apply evt_done. cbv beta.
        eapply scps_bind.
        { eapply (lh_malloc HI) with (lo := lo) (n := size); rewrite ?E1;
            first [exact HL| exact ST| exact ERR| exact MI| exact TP| reflexivity| slv]. }
        cbv beta. intros ms2 mo2 PO.
        (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 e2 -> MI2 ST2 ERR2 PR2 RES)
.
        rewrite E1 in ST2, PR2.
        replace (ret_pc (Z_to_bv 64 0x126cc)) with (Z_to_bv 64 0x126cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (LI2 : forall LBY mo', LHEAP HI SPB LBY m2 mo' -> linv LBY m2 mo' fj Fv fcv).
        { intros LBY mo' HLY. eapply linv_pres; [exact LI| exact PR2| | exact HLY| exact ST2| eapply CJST_pres; [exact PR2| exact CJ]| exact ERR2| exact MI2].
          intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. right. exact Hb. }
        assert (CH2 : cj_chain CJ_PRINTABLE m2 d r B).
        { eapply cj_chain_pres; [exact CH| exact PR2|]. intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. left. exact Hb. }
        destruct RES as [[-> HL2]|(C & junk & -> & CR & CN & HL2 & BLK)].
        + (* [comment removed for export] *)
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
          unfold wz. step. if_cases K'; zify_cond K'; [| exfalso; apply K'; reflexivity].
          apply evt_done. cbv beta.
          eapply fuzz_ret with (LX := B); [apply LI2; exact HL2|].
          eapply Permutation_trans; [apply Permutation_sym; exact HP| apply Permutation_app_comm].
        + (nelimp CR 5%nat; intros C1 C2 C3 C4 C5). try rewrite alloc_ceiling_eq in C4.
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
          unfold wz. step. if_cases K'; zify_cond K'; [exfalso; lia|].
          apply evt_done. cbv beta.
          eapply fuzz_copy; [apply LI2; exact HL2| exact HP| exact CH2| exact Hd| exact BLK| exact CR| exact CN| lia| exact DEQ| exact LPRE| exact NONUL].
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_printed : forall LB2 mm mo fj Fv fcv (r : Z) (d : nat) (B : list cblock) (b0 : byte) (pre str rest : list byte) (rp : word)
        rav x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
      linv LB2 mm mo fj Fv fcv ->
      ((rp = wz 0 /\ Permutation (B ++ LB) LB2) \/ (exists q k, rp = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LB) LB2)) ->
      cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      SCPS psegs POST (LST 0x126b4 Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) rp x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) (Z_to_bv 64 (bv_unsigned b0)) x20 x21 x28 x29 x30 x31) mo.
    Proof using CEIL LO SPAL SPB1 SPB2 SZ TP.
      intros until x31. intros LI RES CH Hd SZ4 DEQ LPRE NONUL.
      (nelimp LI 10%nat; intros HL ST FR CJ [e ERR] MI PR FRM FA DAT).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1. unfold PERRNO in ERR.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      destruct RES as [[-> HP2]|(q & k & -> & QNZ & HP2)].
      - unfold wz. step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
        apply evt_done. cbv beta.
        eapply fuzz_min; [exact LI| exact HP2| exact CH| exact Hd| exact SZ4| exact DEQ| exact LPRE| exact NONUL].
      - (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP2)) 5%nat; intros Q1 Q2 Q3 Q4 Q5). try rewrite alloc_ceiling_eq in Q4.
        unfold wz. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        step.
        replace (Z_to_bv 64 0x151e0) with (wz PFREE) by reflexivity.
        apply evt_done. cbv beta.
        eapply scps_bind.
        { eapply (lh_free HI) with (lo := lo) (A := q) (n := k); rewrite ?E1;
            first [exact HL| eapply perm_in_head; exact HP2| exact ST| exact ERR| exact MI| exact TP| reflexivity| slv]. }
        cbv beta. intros ms2 mo2 PO.
        (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MI2 ST2 ERR2 PR2 HL2)
.
        rewrite E1 in ST2, PR2.
        pose proof (perm_cb_remove _ _ _ _ HP2 (lh_nodup HI _ _ _ _ HL)) as HP3.
        replace (ret_pc (Z_to_bv 64 0x126bc)) with (Z_to_bv 64 0x126bc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (INB : forall b, In b (B ++ LB) -> In b (cb_remove q LB2)). { intros b Hb. eapply Permutation_in; [exact HP3| exact Hb]. }
        eapply fuzz_min; [| exact HP3| | exact Hd| exact SZ4| exact DEQ| exact LPRE| exact NONUL].
        + eapply linv_pres; [exact LI| exact PR2| intros b Hb; apply INB; apply in_or_app; right; exact Hb| exact HL2| exact ST2| eapply CJST_pres; [exact PR2| exact CJ]| exact ERR2| exact MI2].
        + eapply cj_chain_pres; [exact CH| exact PR2|]. intros b Hb. apply INB. apply in_or_app. left. exact Hb.
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_print_ret : forall (pc : Z) LB2 mm mo fj Fv fcv (r : Z) (d : nat) (B : list cblock) (b0 : byte) (pre str rest : list byte) (rp : word)
        rav x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
      (pc = 0x12698 \/ pc = 0x126a8 \/ pc = 0x126b4) ->
      linv LB2 mm mo fj Fv fcv ->
      ((rp = wz 0 /\ Permutation (B ++ LB) LB2) \/ (exists q k, rp = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LB) LB2)) ->
      cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      SCPS psegs POST (LST pc Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) rp x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) (Z_to_bv 64 (bv_unsigned b0)) x20 x21 x28 x29 x30 x31) mo.
    Proof using CEIL LO SPAL SPB1 SPB2 SZ TP.
      intros until x31. intros HPC LI RES CH Hd SZ4 DEQ LPRE NONUL. pose proof LI as (HL & _).
      destruct HPC as [-> |[-> | ->]].
      1,2: eapply scps_step_evt; [eapply (lh_mok HI); exact HL|]; step; apply evt_done; cbv beta.
      all: eapply fuzz_printed; [exact LI| exact RES| exact CH| exact Hd| exact SZ4| exact DEQ| exact LPRE| exact NONUL].
    Qed.

    (* [comment removed for export] *)
    Ltac after_print E1 LI HP1 Hd SZ4 DEQ LPRE NONUL retpc :=
      cbv beta; intros ms3 mo3 PO;
      (nelim PO 31%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 m3 e3 LB3 -> MI3 FRM3 FA3 ST3 ERR3 CJ3 PR3 CH3 HL3 RES3)
;
      rewrite E1 in ST3, PR3;
      replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [lia| reflexivity]);
      eapply (fuzz_print_ret retpc);
      [ lia
      | eapply linv_pres_F; [exact LI| exact PR3| intros b Hb; apply in_or_app; right; exact Hb| exact HL3| exact ST3| exact CJ3| exact ERR3| exact MI3| exact FRM3| exact FA3]
      | exact RES3 | exact CH3 | exact Hd | exact SZ4 | exact DEQ | exact LPRE | exact NONUL ].

    (* [comment removed for export] *)
    Lemma fuzz_parsed : forall LB1 mm mo fj Fv fcv (r : Z) (b0 b2 b3 : byte) (pre str rest : list byte)
        rav x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31,
      linv LB1 mm mo fj Fv fcv ->
      ((r = 0 /\ Permutation LB1 LB)
       \/ (r <> 0 /\ exists (B : list cblock) (d : nat) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word),
             cj_chain CJ_PRINTABLE mm d r B /\ (d <= 1001)%nat /\ Permutation LB1 (B ++ LB)
             /\ rw_cells psegs mm r (node_cells 0 (wz 0) ch ty p1 vs vi p2 vd 0))) ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      SCPS psegs POST (LST 0x12674 Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                          x18 (Z_to_bv 64 (bv_unsigned b0)) (Z_to_bv 64 (bv_unsigned b2)) (Z_to_bv 64 (bv_unsigned b3)) x28 x29 x30 x31) mo.
    Proof.
      intros until x31. intros LI RES SZ4 DEQ LPRE NONUL.
      (nelimp LI 10%nat; intros HL ST FR CJ [e ERR] MI PR FRM FA DAT).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPFal as AL. unfold PERRNO in ERR.
      pose proof (bv_unsigned_in_range 8 b2) as Rb2. change (bv_modulus 8) with 256 in Rb2.
      pose proof (bv_unsigned_in_range 8 b3) as Rb3. change (bv_modulus 8) with 256 in Rb3.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      destruct RES as [[-> HP1]|(RNZ & B & d & ch & ty & p1 & vs & vi & p2 & vd & CH & Hd & HP1 & ND)].
      - step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
        apply evt_done. cbv beta.
        eapply fuzz_ret with (LX := []); [exact LI| rewrite app_nil_r; exact HP1].
      - (nelimp (cj_chain_ptr_range _ _ _ _ _ CH) 3%nat; intros R1 R2 R3).
        apply Permutation_sym in HP1.
        step. if_cases K; zify_cond K; [exfalso; exact (RNZ K)|]. clear K.
        step. step. step. if_cases K1; zify_cond K1.
        + (* [comment removed for export] *)
          step. if_cases K2; zify_cond K2.
          * (* [comment removed for export] *)
            step. step.
            apply evt_done. cbv beta. eapply scps_bind.
            { pose proof PRU as X. unfold cjprintu_stmt, print_pre_stmt, CJPRINTU_ENTRY, wz in X.
              eapply X with (lo := lo) (LR := LB) (B := B) (n := d); rewrite ?E1;
                first [exact HL| exact HP1| exact CH| exact RNZ| exact Hd| exact CJ| exact SPB2| exact AL| exact ST| exact ERR| exact MI
                      | exact TP| exact FRM| reflexivity| exact I| slv]. }
            after_print E1 LI HP1 Hd SZ4 DEQ LPRE NONUL 0x126b4.
          * (* [comment removed for export] *)
            step. step.
            apply evt_done. cbv beta. eapply scps_bind.
            { pose proof PRF as X. unfold cjprint_stmt, print_pre_stmt, CJPRINT_ENTRY, wz in X.
              eapply X with (lo := lo) (LR := LB) (B := B) (n := d); rewrite ?E1;
                first [exact HL| exact HP1| exact CH| exact RNZ| exact Hd| exact CJ| exact SPB2| exact AL| exact ST| exact ERR| exact MI
                      | exact TP| exact FRM| reflexivity| exact I| slv]. }
            after_print E1 LI HP1 Hd SZ4 DEQ LPRE NONUL 0x126a8.
        + (* [comment removed for export] *)
          step. step. step. step. step.
          apply evt_done. cbv beta. eapply scps_bind.
          { pose proof PRB as X. unfold pbuffered_stmt, print_pre_stmt, PBUFD_ENTRY, wz in X.
            eapply X with (lo := lo) (LR := LB) (B := B) (n := d); rewrite ?E1;
              first [exact HL| exact HP1| exact CH| exact RNZ| exact Hd| exact CJ| exact SPB2| exact AL| exact ST| exact ERR| exact MI
                    | exact TP| exact FRM| reflexivity| exact I| exists 1; split; [reflexivity| lia]| slv]. }
          after_print E1 LI HP1 Hd SZ4 DEQ LPRE NONUL 0x12698.
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mo : Model) (errv : word),
      LHEAP HI SPB LB m0 mo ->
      (size <= 4 \/ (In (D, size) LB /\ bytes_at psegs m0 D data /\ Z.of_nat (length data) = size)) ->
      CJST m0 -> rw_cells psegs m0 PERRNO [C4 errv] -> mem_inv psegs m0 ->
      stk psegs m0 lo (bv_unsigned sp) -> frm0 fc ->
      SCPS psegs POST
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x125ec) fc None m0 (seg_rom psegs)) mo.
    Proof.
      intros until errv. intros HL PAY CJ ERR MI ST FRM.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold FUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof ST as STc; (nelim STc 3%nat; intros _ SPhi _).
      pose proof SPFeq as E1.
      pose proof CJ as (HK & (ge1 & ge2 & GE) & LC). unfold PHOOKS in HK. unfold PGERROR in GE. unfold PLCONV in LC. unfold PERRNO in ERR.
      pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl psegs m0) as WM.
      assert (BLO : forall A n, In (A, n) LB -> A + n <= bv_unsigned sp - 64).
      { intros A n Hin. (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 64%nat ST.
      do 8 step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      assert (HL1 : LHEAP HI SPB LB m1 mo).
      { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (CJ1 : CJST m1).
      { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' Hin. cbn in Hin. destruct Hin as [E|[]]. inversion E; subst. unfold PDATA_LO, PIMG_HI. lia. }
      assert (PR1 : dpres LB (bv_unsigned sp) m0 m1).
      { apply dpres_of_cj_pres. eapply cj_pres_of_munch; [exact MU| exact WM|]. right. split; [lia|]. split; [unfold PDATA_LO, PIMG_HI; lia|].
        intros A n Hin. pose proof (BLO A n Hin). lia. }
      step. step. step. if_cases K0; zify_cond K0.
      - (* [comment removed for export] *)
        apply evt_done. cbv beta.
        eapply fuzz_ret with (LX := []); [| rewrite app_nil_r; apply Permutation_refl].
        split; [exact HL1|]. split; [exact ST|]. split; [exact FR|]. split; [exact CJ1|]. split; [exists errv; exact ERR|]. split; [exact MI|].
        split; [exact PR1|]. split; [exact FRM|]. split; [intros; reflexivity| left; lia].
      - destruct PAY as [?|(DIN & BY & LEN)]; [exfalso; lia|].
        pose proof (lh_block_range HI _ _ _ _ _ _ HL DIN) as DR. (nelimp DR 5%nat; intros D1 D2 D3 D4 D5). try rewrite alloc_ceiling_eq in D4. unfold PIMG_LO, PIMG_HI in D5.
        eapply (bytes_at_transport psegs) in BY; [| exact MU| cbn; lia].
        clear MU WM.
        step. zstep.
        destruct (nth_error data (Z.to_nat (size - 1))) as [bl|] eqn:Hbl. 2:{ exfalso. apply nth_error_None in Hbl. lia. }
        pose proof (u8ro_read psegs m1 D data (size - 1) bl _ BY Hbl ltac:(lia) eq_refl) as RDl.
        pose proof (bv_unsigned_in_range 8 bl) as Rbl. change (bv_modulus 8) with 256 in Rbl.
        (* [comment removed for export] *)
        assert (RET : forall rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
                  SCPS psegs POST (LST 0x126f8 F fc m1 rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31) mo).
        { intros. eapply fuzz_ret with (LX := []); [| rewrite app_nil_r; apply Permutation_refl].
          split; [exact HL1|]. split; [exact ST|]. split; [exact FR|]. split; [exact CJ1|]. split; [exists errv; exact ERR|]. split; [exact MI|].
          split; [exact PR1|]. split; [exact FRM|]. split; [intros; reflexivity|]. right. split; [exact DR|]. split; [exact DIN|]. split; [exact BY| exact LEN]. }
        zstep. cbv beta. step. if_cases K1; zify_cond K1; [apply evt_done; cbv beta; apply RET|].
        (* [comment removed for export] *)
        destruct (nth_error data 0) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
        destruct (nth_error data 1) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
        destruct (nth_error data 2) as [b2|] eqn:Hb2. 2:{ exfalso. apply nth_error_None in Hb2. lia. }
        destruct (nth_error data 3) as [b3|] eqn:Hb3. 2:{ exfalso. apply nth_error_None in Hb3. lia. }
        pose proof (u8ro_read psegs m1 D data 0 b0 _ BY Hb0 ltac:(lia) eq_refl) as RD0.
        pose proof (u8ro_read psegs m1 D data 1 b1 _ BY Hb1 ltac:(lia) eq_refl) as RD1.
        pose proof (u8ro_read psegs m1 D data 2 b2 _ BY Hb2 ltac:(lia) eq_refl) as RD2.
        pose proof (u8ro_read psegs m1 D data 3 b3 _ BY Hb3 ltac:(lia) eq_refl) as RD3.
        pose proof (bv_unsigned_in_range 8 b0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
        pose proof (bv_unsigned_in_range 8 b1) as Rb1. change (bv_modulus 8) with 256 in Rb1.
        pose proof (bv_unsigned_in_range 8 b2) as Rb2. change (bv_modulus 8) with 256 in Rb2.
        pose proof (bv_unsigned_in_range 8 b3) as Rb3. change (bv_modulus 8) with 256 in Rb3.
        replace (wa (D + 0)) with (wa D) in RD0 by (f_equal; lia).
        zstep. cbv beta. zstep. step. step. if_cases K2; zify_cond K2; [apply evt_done; cbv beta; apply RET|].
        zstep. cbv beta. zstep. step. if_cases K3; zify_cond K3; [apply evt_done; cbv beta; apply RET|].
        zstep. cbv beta. zstep. step. step. if_cases K4; zify_cond K4; [apply evt_done; cbv beta; apply RET|].
        zstep. cbv beta. zstep. step. if_cases K5; zify_cond K5; [apply evt_done; cbv beta; apply RET|].
        zstep. zstep. zstep. step. step.
        (* [comment removed for export] *)
        destruct (split4 data ltac:(lia)) as [DEQ4 LPRE].
        assert (Ebl : bl = wb 0) by (apply bv_eq; rewrite K1; reflexivity).
        assert (INZ : In (wb 0) (skipn 4 data)).
        { rewrite <- Ebl. eapply (nth_error_In _ (Z.to_nat (size - 1) - 4)). rewrite nth_error_skipn, <- Hbl. f_equal. lia. }
        (nelim (nul_split _ INZ) 4%nat; intros str rest EQT NONUL).
        assert (DEQ : data = firstn 4 data ++ str ++ wb 0 :: rest) by (rewrite <- EQT; exact DEQ4).
        assert (SL : 4 + Z.of_nat (length str) + 1 + Z.of_nat (length rest) = size).
        { rewrite DEQ, !length_app, LPRE in LEN. cbn [length] in LEN. lia. }
        set (c := (D + size + 7) / 8).
        assert (Hc : D + size <= c * 8 < D + size + 8) by (subst c; Z.div_mod_to_equations; lia).
        destruct (bytes_exist m1 (D + size) (Z.to_nat (c * 8 - (D + size))) ltac:(lia) ltac:(lia)) as (extra & XL & XB). (* [comment removed for export] *)
        { intros i Hi. apply (lh_block_slack HI _ _ _ _ _ _ i HL1 DIN); [lia| subst c; lia]. }
        assert (BYV : bytes_at psegs m1 (D + 4) (str ++ wb 0 :: rest ++ extra)).
        { assert (B2 : bytes_at psegs m1 D (data ++ extra)). { apply bytes_at_app. split; [exact BY| rewrite LEN; exact XB]. }
          rewrite DEQ, <- app_assoc in B2. apply bytes_at_app in B2. destruct B2 as [_ B2]. rewrite LPRE in B2.
          rewrite <- app_assoc in B2. cbn [app] in B2. exact B2. }
        assert (SLK : (- (D + 4 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length (rest ++ extra))).
        { rewrite length_app. eapply Z.le_trans; [apply (slack_mod8 _ c); lia| lia]. }
        (* [comment removed for export] *)
        apply evt_done. cbv beta.
        eapply scps_bind.
        { pose proof PARSE as X. unfold parse_wopts_stmt, PARSE_WOPTS, wz in X.
          eapply X with (lo := lo) (D := D) (n := size) (str := str) (slack := rest ++ extra) (V := D + 4); rewrite ?E1;
            first [exact HL1| exact DIN| exact BYV| exact NONUL| exact SLK| exact CJ1| exact ERR| exact MI| exact ST| exact CEIL
                  | exact SPB2| exact FRM| exact TP| reflexivity| lia | clear X; slv]. }
        cbv beta. intros ms2 mo2 PO.
        (nelim PO 33%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 r LB' e2 -> A0 FAG FRM2 MI2 ST2 CJ2 ERR2 HL2 BYT DP RES)
.
        unfold wz in A0. subst a0'. rewrite E1 in ST2, DP.
        replace (ret_pc (Z_to_bv 64 0x12674)) with (Z_to_bv 64 0x12674) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply fuzz_parsed with (pre := firstn 4 data) (str := str) (rest := rest); [| exact RES| lia| exact DEQ| exact LPRE| exact NONUL].
        split; [exact HL2|]. split; [exact ST2|]. split.
        { eapply dpres_rw_cells_stack; [exact DP| exact FR| lia| slv]. }
        split; [exact CJ2|]. split; [exists e2; exact ERR2|]. split; [exact MI2|]. split.
        { eapply dpres_trans; [exact PR1|]. eapply dpres_weaken; [exact DP| lia| intros b Hb; exact Hb]. }
        split; [exact FRM2|]. split.
        { intros k Hk. apply FAG; unfold fp_callee_saved in Hk; lia. }
        right. split; [exact DR|]. split; [exact DIN|]. split; [| exact LEN].
        eapply dpres_bytes_at_block; [exact DR| exact DIN| exact DP| exact BY| lia].
    Qed.
  End Body.

  Theorem fuzz_spec : fuzz_stmt.
  Proof.
    unfold fuzz_stmt. intros until errv. intros HL PAY SZ CJ ERR MI ST CEIL LO SPB1 SPB2 SPAL FRM TP A0 A1.
    unfold FUZZ_ENTRY, wz. unfold wz in A0, A1. subst a0 a1.
    eapply fuzz_entry; [exact SPB1| exact SPB2| exact SPAL| exact CEIL| exact LO| exact TP| exact SZ| exact HL| exact PAY| exact CJ| exact ERR| exact MI| exact ST| exact FRM].
  Qed.
End S.


End CeilWrap.
