From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec reac_identity_fw_str_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma z_all_eq : forall (f g : Z -> Z) n, z_all (fun x => f x =? g x) (Z.to_nat n) 0 = true ->
  forall x, 0 <= x < n -> f x = g x.
Proof.
  intros f g n H x Hx. apply Z.eqb_eq. apply (z_all_spec _ _ _ H x). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma reac_identity_fw_str_c2_h : forall v, 0 <= v < 65536 -> Z.shiftr (Z.shiftr v 3 * 8389) 20 = v / 1000.
Proof.
  exact (z_all_eq (fun v => Z.shiftr (Z.shiftr v 3 * 8389) 20) (fun v => v / 1000) 65536
           ltac:(vm_compute; reflexivity)).
Qed.

Lemma reac_identity_fw_str_c2_t : forall v, 0 <= v < 65536 -> (Z.shiftr v 4 <? 625) = (v <? 10000).
Proof.
  intros v Hv. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec (v / 2^4) 625); destruct (Z.ltb_spec v 10000); try reflexivity;
    exfalso; Z.div_mod_to_equations; lia.
Qed.

Lemma reac_identity_fw_str_c2_hd : forall v, 0 <= v < 65536 -> Z.shiftr (Z.shiftr v 4 * 839) 19 = v / 1000 / 10.
Proof.
  exact (z_all_eq (fun v => Z.shiftr (Z.shiftr v 4 * 839) 19) (fun v => v / 1000 / 10) 65536
           ltac:(vm_compute; reflexivity)).
Qed.

Lemma reac_identity_fw_str_c2_f100 : forall f, 0 <= f < 1000 ->
  Z.shiftr (Z.shiftr (Z.shiftl f 48) 50 * 5243) 17 = f / 100.
Proof.
  exact (z_all_eq (fun f => Z.shiftr (Z.shiftr (Z.shiftl f 48) 50 * 5243) 17) (fun f => f / 100) 1000
           ltac:(vm_compute; reflexivity)).
Qed.

Lemma reac_identity_fw_str_c2_f10 : forall f, 0 <= f < 1000 ->
  Z.shiftr (Z.shiftr (Z.shiftl f 48 * 3435986944) 64) 19 = f / 10.
Proof.
  exact (z_all_eq (fun f => Z.shiftr (Z.shiftr (Z.shiftl f 48 * 3435986944) 64) 19) (fun f => f / 10) 1000
           ltac:(vm_compute; reflexivity)).
Qed.

Lemma reac_identity_fw_str_c2_h10 : forall h, 0 <= h < 66 -> Z.shiftr (h * 103) 10 = h / 10.
Proof.
  exact (z_all_eq (fun h => Z.shiftr (h * 103) 10) (fun h => h / 10) 66 ltac:(vm_compute; reflexivity)).
Qed.

Lemma reac_identity_fw_str_c2_fd10 : forall g, 0 <= g < 100 -> Z.shiftr (Z.shiftl (g * 205) 48) 59 = g / 10.
Proof.
  exact (z_all_eq (fun g => Z.shiftr (Z.shiftl (g * 205) 48) 59) (fun g => g / 10) 100
           ltac:(vm_compute; reflexivity)).
Qed.

Lemma lor48 : forall x, 0 <= x < 16 -> Z.lor x 48 = x + 48.
Proof. exact (z_all_eq (fun x => Z.lor x 48) (fun x => x + 48) 16 ltac:(vm_compute; reflexivity)). Qed.

Lemma sub_div_mul : forall a b, 0 < b -> a - a / b * b = a mod b.
Proof. intros a b Hb. rewrite (Z.mod_eq a b) by lia. ring. Qed.

Lemma wtm_app : forall bs bs2 m o k, k = Z.of_nat (length bs) ->
  write_to_mem (write_to_mem m (wa o) bs) (wa (o + k)) bs2 = write_to_mem m (wa o) (bs ++ bs2).
Proof.
  induction bs as [|x bs IH]; intros bs2 m o k ->.
  - cbn [length Z.of_nat app write_to_mem]. rewrite Z.add_0_r. reflexivity.
  - cbn [length app write_to_mem]. rewrite !wa_succ.
    rewrite <- (IH bs2 _ (o + 1) (Z.of_nat (length bs)) eq_refl). do 2 f_equal. lia.
Qed.

Lemma wtm_at : forall m (A : word) o bs, A = wa o -> write_to_mem m A bs = write_to_mem m (wa o) bs.
Proof. intros m A o bs ->. reflexivity. Qed.

Lemma wtm_join : forall bs bs2 m o (A : word), A = wa (o + Z.of_nat (length bs)) ->
  write_to_mem (write_to_mem m (wa o) bs) A bs2 = write_to_mem m (wa o) (bs ++ bs2).
Proof. intros bs bs2 m o A ->. apply wtm_app. reflexivity. Qed.

Lemma fw_fin : forall m o bs, 0 <= o -> o + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa o) bs) o bs /\
  munch [(o, o + Z.of_nat (length bs))] m (write_to_mem m (wa o) bs) /\
  wmono rsegs m (write_to_mem m (wa o) bs).
Proof.
  intros m o bs H1 H2. split; [apply bytes_at_write_same; lia|]. split.
  - apply munch_write; [apply munch_refl | lia | lia | cbn; left; lia].
  - apply wmono_write, wmono_refl.
Qed.

Lemma fw_short : forall v, 0 <= v < 10000 ->
  FW v = [dg (v / 1000 mod 10); Z_to_bv 8 0x2e; dg (v mod 1000 / 100); dg (v mod 1000 / 10 mod 10);
          dg (v mod 1000 mod 10)].
Proof.
  intros v Hv. unfold FW. rewrite (proj2 (Z.leb_gt 10 (v / 1000))) by (Z.div_mod_to_equations; lia).
  reflexivity.
Qed.

Lemma fw_long : forall v, 10000 <= v < 65536 ->
  FW v = [dg (v / 1000 / 10); dg (v / 1000 mod 10); Z_to_bv 8 0x2e; dg (v mod 1000 / 100);
          dg (v mod 1000 / 10 mod 10); dg (v mod 1000 mod 10)].
Proof.
  intros v Hv. unfold FW. rewrite (proj2 (Z.leb_le 10 (v / 1000))) by (Z.div_mod_to_equations; lia).
  reflexivity.
Qed.

Local Ltac rng := rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia.

Local Ltac ul :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by rng end.

Local Ltac norm :=
  repeat first
    [ progress ul
    | rewrite reac_identity_fw_str_c2_h by lia
    | rewrite reac_identity_fw_str_c2_hd by lia
    | rewrite reac_identity_fw_str_c2_f100 by rng
    | rewrite reac_identity_fw_str_c2_f10 by rng
    | rewrite reac_identity_fw_str_c2_h10 by rng
    | rewrite reac_identity_fw_str_c2_fd10 by rng
    | rewrite sub_div_mul by lia
    | match goal with |- context [bv_swrap 32 ?e] =>
        rewrite (bv_swrap_small 32 e) by (change (bv_half_modulus 32) with (2^31); rng) end
    | match goal with |- context [Z.lor ?x 48] => rewrite (lor48 x) by rng end ].

Local Ltac st := step; norm.

Local Ltac br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b;
      [ cbv iota
      | symmetry; unfold_cond; ul; fold_lit_ux; rewrite ?reac_identity_fw_str_c2_t by lia;
        first [ apply Z.eqb_eq; rng | apply Z.eqb_neq; rng | apply Z.ltb_lt; rng | apply Z.ltb_ge; rng ] ]
  end.

Local Ltac refuse :=
  st;
  apply evt_done; cbv beta; do 16 eexists; split; [reflexivity|];
  split; [apply wmono_refl|];
  split; [ intros _; split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity] | reflexivity]
         | intros; exfalso; lia ].

Local Ltac hs o W j :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?M _) =>
    let H := fresh "HS" in
    assert (H : store_ok rsegs M (wa (o + j)) 1 = true)
      by (eapply wr_at_store_ok; [repeat apply wr_at_write; exact W | lia | lia])
  end.

Local Ltac merge o :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem ?m (wa o) ?acc) ?A ?bs) _) =>
      rewrite (wtm_join acc bs m o A) by (unfold wa; f_equal; simpl_sizes; lia)
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?A ?bs) _) =>
      rewrite (wtm_at m A o bs) by (unfold wa; f_equal; lia)
  end.

Local Ltac sto o W j := hs o W j; st; merge o.

Local Ltac tail o W k :=
  do 32 st;
  sto o W (k + 0); sto o W (k + 1); sto o W (k + 2); sto o W (k + 3); sto o W (k + 4); sto o W (k + 5).

Local Ltac byte_eq := unfold dg; ul; first [reflexivity | f_equal; lia].

Local Ltac bytes_eq :=
  lazymatch goal with
  | |- [] = [] => reflexivity
  | |- _ :: _ = _ :: _ => apply (f_equal2 (@cons byte)); [byte_eq | bytes_eq]
  end.

Local Ltac finish v o EFW :=
  st;
  let FB := fresh "FB" in let FM := fresh "FM" in let FWM := fresh "FWM" in
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa o) ?bs) _) =>
      replace bs with (FW v ++ [Z_to_bv 8 0]) by (rewrite EFW; unfold le1; cbn [Z_to_le_bytes app]; bytes_eq);
      pose proof (fw_fin m o (FW v ++ [Z_to_bv 8 0]) ltac:(lia)
                    ltac:(rewrite length_app, EFW; cbn [length]; lia)) as (FB & FM & FWM)
  end;
  apply evt_done; cbv beta; do 16 eexists; split; [reflexivity|];
  split; [exact FWM|]; split; [intros [Hx|Hx]; exfalso; lia|];
  intros _ _; split; [unfold L; rewrite EFW; reflexivity|]; split; [exact FB|];
  replace (o + L v + 1) with (o + Z.of_nat (length (FW v ++ [Z_to_bv 8 0])))
    by (unfold L; rewrite length_app; cbn [length]; lia);
  exact FM.

Theorem reac_identity_fw_str_holds : reac_identity_fw_str_contract.
Proof.
  unfold reac_identity_fw_str_contract, REAC_IDENTITY_FW_STR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v o c
    E0 E1 E2 Hv Ho Hc HW.
  subst a0 a1 a2.
  st. st. st.
  destruct (Z.eq_dec o 0) as [O0|O0].
  { br true. refuse. }
  br false. st. st.
  destruct (Z.ltb_spec c 8) as [C8|C8].
  { br true. refuse. }
  br false.
  specialize (HW O0 C8). pose proof HW as (Wo & Wn & _).
  do 11 st.
  destruct (Z.ltb_spec v 10000) as [V|V].
  - br true. st.
    pose proof (fw_short v ltac:(lia)) as EFW.
    tail o HW 0. finish v o EFW.
  - br false. do 4 st. sto o HW 0. st. st.
    pose proof (fw_long v ltac:(lia)) as EFW.
    tail o HW 1. finish v o EFW.
Qed.
