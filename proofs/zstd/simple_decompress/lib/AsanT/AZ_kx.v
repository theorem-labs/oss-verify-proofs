(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AZ_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma unp_zero_win : forall (m : amem) A8 n, unpoisoned m (8 * A8) (8 * A8 + n) ->
  forall i, 0 <= i < n / 8 -> m (wa (ASHOFF + A8 + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A8 n (H0 & H1 & H) i Hi.
  assert (Hn : 8 * (i + 1) <= n) by (Z.div_mod_to_equations; lia).
  destruct (H (A8 + i) ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Hb & Hg).
  replace (ASHOFF + A8 + i) with (ASHOFF + (A8 + i)) by lia. rewrite Hb. f_equal.
  apply (gran_ok_full _ _ Hg). lia.
Qed.

Lemma areg_zero_win : forall RNG (m : amem) A8 n, areg RNG m (8 * A8) n -> 8 <= n ->
  forall i, 0 <= i < n / 8 -> m (wa (ASHOFF + A8 + i)) = Some (Z_to_bv 8 0).
Proof.
  intros RNG m A8 n AR Hn. destruct (AR ltac:(lia)) as (_ & U & _ & _). exact (unp_zero_win m A8 n U).
Qed.

(* [comment removed for export] *)
Lemma areg_shadow_rng : forall RNG (m : amem) A8 n, areg RNG m (8 * A8) n -> 0 < n -> rng RNG (ASHOFF + A8) ((n + 7) / 8).
Proof.
  intros RNG m A8 n AR Hn. destruct (AR Hn) as (_ & _ & _ & R).
  rewrite shad_div in R. unfold shspan in R. replace (8 * A8 / 8) with A8 in R by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  replace ((8 * A8 + n + 7) / 8 - A8) with ((n + 7) / 8) in R; [exact R|].
  replace (8 * A8 + n + 7) with ((n + 7) + A8 * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma unp_shadow_zero : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n ->
  m (wa (shad p)) = Some (Z_to_bv 8 0).
Proof.
  intros m X n p (H0 & H1 & H) Hp Hg. rewrite shad_div.
  destruct (H (p / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia))
    as (b & Hb & Hok).
  rewrite Hb. f_equal. apply (gran_ok_full _ _ Hok). Z.div_mod_to_equations. lia.
Qed.

Lemma unp_shadow_ok : forall (m : amem) X n p k, unpoisoned m X (X + n) -> X <= p -> 1 <= k -> p + k <= X + n -> p mod 8 + k <= 8 ->
  exists b, m (wa (shad p)) = Some b /\ (sval b = 0 \/ p mod 8 + k <= sval b <= 7).
Proof.
  intros m X n p k (H0 & H1 & H) Hp Hk Hpk H8. rewrite shad_div.
  destruct (H (p / 8) ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (b & Hb & Hok).
  exists b. split; [exact Hb|]. destruct Hok as [Z|Z]; [left; exact Z| right].
  split; [| lia]. assert (Z.min (8 * (p / 8) + 8) (X + n) - 8 * (p / 8) >= p mod 8 + k) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma unp_rd_at : forall (m : amem) A n, unpoisoned m A (A + n) -> 0 < n -> rd_at bsegs m (shad A) (shspan A n).
Proof.
  intros m A n (H0 & H1 & H) Hn. unfold shspan. rewrite shad_div. unfold ASHOFF.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros i Hi. destruct (H (A / 8 + i) ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (b & Hb & _).
  unfold mrd. replace (2147450880 + A / 8 + i) with (ASHOFF + (A / 8 + i)) by (unfold ASHOFF; lia). rewrite Hb. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rdval_sh1 : forall (m : amem) a b, m (wa a) = Some b -> rdval bsegs m (wa a) 1 true = Z_to_bv 64 (sval b).
Proof.
  intros m a b H. unfold rdval. cbn [rdn]. rewrite H. cbn [bytes_le_to_Z]. f_equal.
  unfold extz, sval, bv_signed. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdval_sh0 : forall (m : amem) a sx, m (wa a) = Some (Z_to_bv 8 0) -> rdval bsegs m (wa a) 1 sx = Z_to_bv 64 0.
Proof. intros m a sx H. unfold rdval. cbn [rdn]. rewrite H. destruct sx; reflexivity. Qed.

Lemma sval_range : forall b : byte, -128 <= sval b <= 127.
Proof. intros b. unfold sval. pose proof (bv_signed_in_range 8 b ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R. cbn in R. lia. Qed.

(* [comment removed for export] *)
Lemma unp_shadow_val : forall (m : amem) X n p k, unpoisoned m X (X + n) -> X <= p -> 1 <= k -> p + k <= X + n ->
  (p mod 8 + k <= 8 \/ p - p mod 8 + 8 <= X + n) ->
  exists b, m (wa (shad p)) = Some b /\ (sval b = 0 \/ (p mod 8 + k <= sval b <= 7 /\ X + n < p - p mod 8 + 8)).
Proof.
  intros m X n p k U Hp Hk Hpk Hor.
  destruct (Z_lt_le_dec (X + n) (p - p mod 8 + 8)) as [Hl|Hl].
  - destruct Hor as [H8|H8]; [|lia].
    destruct (unp_shadow_ok m X n p k U Hp Hk Hpk H8) as (b & Hb & [Hz|Hz]).
    + exists b. split; [exact Hb|]. left; exact Hz.
    + exists b. split; [exact Hb|]. right. split; [exact Hz | exact Hl].
  - exists (Z_to_bv 8 0). split; [exact (unp_shadow_zero m X n p U Hp Hl)|]. left. reflexivity.
Qed.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kx_cell_lit :=
  lazymatch goal with
  | |- _ /\ _ /\ _ /\ rdn ?segs ?m (wa ?a) ?w = Some (word_to_le_bytes ?w ?V) =>
      is_Zlit a;         (* [comment removed for export] *)
      split; [lia | split; [lia | split; [lia |]]];
      match goal with
      | H : rw_cells segs m ?A ?cs |- _ =>
          is_Zlit A;     (* [comment removed for export] *)
          let k := eval vm_compute in (a - A) in
          let ok := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 4096)) in
          lazymatch ok with true =>
            replace (wa a) with (wa (A + k)) by (f_equal; vm_compute; reflexivity);
            eapply (kx_word_of_cells segs m A cs k _ w V (proj1 H));
            [ lia | cells_cbv; reflexivity | reflexivity
            | first [ reflexivity
                    | (cbv beta iota delta [cbytes le8 le4 le2 word_to_le_bytes]; f_equal;
                       first [ reflexivity | rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range ]) ] ]
          end
      end
  end.

(* [comment removed for export] *)
Ltac kx_sh_arith :=
  unfold shspan in *; rewrite ?shad_div, ?nshad_div in *; unfold ASHOFF in *; cbn [Z.of_nat] in *;
  rewrite ?Z.mod_small by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac kx_sh_acc H :=
  lazymatch goal with
  | KXA : atoms_ok ?zs ?E |- accP ?E ?RNG (?a, ?n) =>
      let nz := kx_len zs in
      lazymatch type of H with
      | rng RNG ?A0 ?N0 =>
          apply (kx_accP_rng E RNG a n A0 N0 H); [ vm_compute; lia | kx_estarts E zs nz KXA; kx_sh_arith | kx_estarts E zs nz KXA; kx_sh_arith ]
      end
  end.

(* [comment removed for export] *)
Ltac kx_sh_rd H :=
  kx_side_pre;
  lazymatch goal with
  | KXA : atoms_ok ?zs ?E |- rd_ok ?segs ?m ?E ?a ?k =>
      let nz := kx_len zs in
      lazymatch type of H with
      | unpoisoned m ?A (?A + ?n) =>
          eapply (kx_rd_ok segs m E a k _ _ (unp_rd_at m A n H ltac:(lia))); kx_estarts E zs nz KXA; kx_sh_arith
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kx_gen_regF i :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                             ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F ?pc ?fc ?rv ?m ?rom) =>
      let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
      let j := eval vm_compute in (pred i) in
      let xi := kx_nth j xs in
      cut (forall v : word, ltac:(let l' := kx_list_set xs j v in exact (evtF segs RNG Q (MS (mkRl l') F pc fc rv m rom))));
      [ let HH := fresh in intro HH; rewrite mkRl_mkR; exact (HH xi)
      | let v' := fresh "kxv" in intro v'; rewrite <- mkRl_mkR; revert v' ]
  end.
Ltac kx_gen_regsF l :=
  lazymatch l with
  | @nil _ => idtac
  | @cons _ ?i ?t =>
      kx_gen_regsF t; kx_gen_regF i;
      let v := fresh "kxv" in intro v; change kxword in (type of v)
  end.
Ltac kx_tidyF :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      repeat match goal with
      | H : bytes_at segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : u8arr segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : rw_cells segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : ro_cells segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : stk segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : wr_at segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : mem_inv segs ?m' |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : munch _ _ ?m' |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : wmono segs _ ?m' |- _ => lazymatch m' with m => fail | _ => clear H end
      end
  end.
Ltac kx_joinF HJ REGS :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?m0 _) =>
      kx_mem;
      (* [comment removed for export] *)
      repeat match goal with
             | H : reads_ok _ _ _ _ _ |- _ => clear H
             | H : know_ok _ _ _ _ |- _ => clear H
             | H : log_flat _ _ |- _ => clear H
             | H : atoms_ok _ _ |- _ => clear H
             end;
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
          kx_gen_regsF REGS;
          kx_revert_mem m;
          repeat match goal with H : kx_keep _ |- _ => revert H end;
          repeat match goal with
          | |- context [ev ?E ?j] => generalize (ev E j)
          | |- context [edenot ?E ?e] => generalize (edenot E e)
          end;
          repeat match goal with v : kxword |- _ => revert v end;
          exact HJ
      end
  end.
Ltac kx_join_endF := intros; unfold kx_keep in *; kx_tidyF.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kx_sh_simpl_hyp K :=
  rewrite ?Z_to_bv_bv_unsigned in K;
  repeat match type of K with
  | context [Z.land ?P 7] =>
      let E := fresh in
      assert (E : Z.land P 7 = P mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity);
      rewrite E in K; clear E
  end;
  rewrite ?signed_lit_small64 in K by (Z.div_mod_to_equations; lia).

Ltac kx_sh_dead H k :=
  match goal with
  | KB : bv_unsigned (ev ?E ?j) <> 0 |- _ =>
      let HR := fresh "KXSH" in
      kx_read_eq j HR;
      try change (2^64) with 18446744073709551616 in HR;
      lazymatch type of HR with
      | ev E j = rdval ?segs ?m (wa (?P mod 18446744073709551616 / 8 + 2147450880)) 1 true =>
          let PM := fresh in
          assert (PM : P mod 18446744073709551616 = P) by (apply Z.mod_small; lia);
          rewrite PM in HR;
          repeat match goal with
                 | K : context [P mod 18446744073709551616] |- _ => rewrite PM in K
                 end;
          clear PM;
          replace (P / 8 + 2147450880) with (shad P) in HR by (rewrite shad_div; unfold ASHOFF; lia);
          lazymatch type of H with
          | unpoisoned m ?R (?R + ?n) =>
              let b := fresh "sb" in let Hb := fresh "Hsb" in let Hv := fresh "Hsv" in let SR := fresh "SR" in
              destruct (unp_shadow_val m R n P k H ltac:(lia) ltac:(lia) ltac:(lia)
                          ltac:(Z.div_mod_to_equations; lia))
                as (b & Hb & Hv);
              rewrite (rdval_sh1 m _ b Hb) in HR;
              pose proof (sval_range b) as SR;
              exfalso;
              rewrite HR in *;
              repeat match goal with
                     | K : context [Z_to_bv 64 (sval b)] |- _ => progress kx_sh_simpl_hyp K
                     end;
              rewrite Z_to_bv_unsigned in KB; unfold bv_wrap, bv_modulus in KB;
              change (2 ^ Z.of_N 64) with 18446744073709551616 in KB;
              destruct Hv as [Hv|Hv]; [rewrite Hv in KB; apply KB; reflexivity | Z.div_mod_to_equations; lia]
          end
      end
  end.

Ltac kx_sh_dead_any k :=
  lazymatch goal with
  | KXRD : reads_ok _ ?m _ _ _ |- _ => match goal with H : unpoisoned m _ _ |- _ => kx_sh_dead H k end
  end.

Ltac kx_sh_rd_any :=
  lazymatch goal with |- sc_resid _ ?m _ _ => match goal with H : unpoisoned m _ _ |- _ => kx_sh_rd H end end.

(* [comment removed for export] *)
Ltac kx_sh_dead0 H :=
  match goal with
  | KB : bv_unsigned (ev ?E ?j) <> 0 |- _ =>
      let HR := fresh "KXSH" in
      kx_read_eq j HR;
      try change (2^64) with 18446744073709551616 in HR;
      lazymatch type of HR with
      | ev E j = rdval ?segs ?m (wa (?P mod 18446744073709551616 / 8 + 2147450880)) 1 ?sx =>
          rewrite (Z.mod_small P 18446744073709551616) in HR by lia;
          replace (P / 8 + 2147450880) with (shad P) in HR by (rewrite shad_div; unfold ASHOFF; lia);
          lazymatch type of H with
          | unpoisoned m ?R (?R + ?n) =>
              rewrite (rdval_sh0 m (shad P) sx (unp_shadow_zero m R n P H ltac:(lia) ltac:(Z.div_mod_to_equations; lia))) in HR;
              rewrite HR in KB; exfalso; apply KB; reflexivity
          end
      end
  end.
Ltac kx_sh_dead0_any :=
  lazymatch goal with
  | KXRD : reads_ok _ ?m _ _ _ |- _ => match goal with H : unpoisoned m _ _ |- _ => kx_sh_dead0 H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unp_now U MUc H :=
  lazymatch type of MUc with munch _ _ ?mc =>
  lazymatch type of U with unpoisoned _ ?A ?B =>
    assert (H : unpoisoned mc A B)
      by (eapply unpoisoned_munch; [exact U | exact MUc | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
          repeat split; Z.div_mod_to_equations; lia])
  end end.

(* [comment removed for export] *)
Ltac rdb1 B :=
  lazymatch goal with |- _ /\ _ /\ _ /\ rdn ?segs ?mm (wa ?a) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 ?v)) =>
    split; [lia|]; split; [lia|]; split; [lia|];
    lazymatch type of B with bytes_at _ _ ?X _ =>
      replace (wa a) with (wa (X + Z.of_nat 0)) by (f_equal; lia);
      rewrite (bytes_at_rdn segs mm X _ _ 1 B) by (cbn; lia); cbn [skipn firstn word_to_le_bytes Z_to_le_bytes];
      do 2 f_equal; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_small by lia; reflexivity
    end end.


