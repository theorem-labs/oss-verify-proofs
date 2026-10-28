(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Arr Image SFModel Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Str_memcmp Str_memmove Fz_W4_defs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W3_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac relf FR ST hi :=
  eapply stk_release in FR; [| exact ST| lia]; clear ST; rename FR into ST; cbn [cells_size csize Nat.add] in ST;
  lazymatch type of ST with stk _ _ _ ?hi' => replace hi' with hi in ST by lia end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation CTYPE_TABLE := (0x3a8f8)%Z (only parsing).
Definition ctype_table : list byte := Eval vm_compute in (match image_bytes usegs 0x3a8f8 256 with Some bs => bs | None => [] end).
Lemma ctype_table_len : length ctype_table = 256%nat.
Proof. reflexivity. Qed.
Lemma ctype_table_at : forall m, mem_inv usegs m -> bytes_at usegs m CTYPE_TABLE ctype_table.
Proof.
  intros m HI.
  assert (RO : ro_cells usegs m CTYPE_TABLE [CB 256 ctype_table])
    by (apply (ro_cells_image usegs m CTYPE_TABLE ctype_table HI); [vm_compute; reflexivity | lia | cbn; lia]).
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition ctype_post (ra sp gp tp t0 t1 t2 a1 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (r : Z) (a2' a3' a4' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ (r = 0 \/ r = 1) /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp).

Lemma ctype_check_proof : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c mask lo : Z),
  a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 mask -> 0 <= c < 256 -> 0 <= mask < 2 ^ 32 ->
  stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (ctype_post ra sp gp tp t0 t1 t2 a1 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xeb090) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros -> -> Hc Hm ST LO0 SLO MI.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 3 zstep. zstep.
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    do 3 zstep. relf FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold ctype_post. exists 0. do 4 eexists. split; [reflexivity|]. split; [left; reflexivity|].
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia. auto.
  - do 3 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      lazymatch goal with H : mem_inv usegs mX |- _ =>
        pose proof (bytes_at_read usegs mX CTYPE_TABLE ctype_table (2 * c) 2 (ctype_table_at mX H) ltac:(lia) ltac:(rewrite ctype_table_len; lia)) as RD end end.
    rewrite (Z.shiftl_mul_pow2 c 1) by lia. change (2 ^ 1) with 2.
    replace (wa (CTYPE_TABLE + 2 * c)) with (Z_to_bv 64 (CTYPE_TABLE + c * 2)) in RD by (unfold wa; f_equal; lia).
    zstep. zstep. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
    zstep. zstep. rewrite (Z.shiftl_mul_pow2 c 1) by lia. change (2 ^ 1) with 2. zstep. clear RD. do 3 zstep. do 2 zstep. relf FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold ctype_post.
    lazymatch goal with |- context [Z_to_bv 64 (Z.b2z ?b)] => exists (Z.b2z b); do 4 eexists; split; [reflexivity|]; split; [destruct b; cbn [Z.b2z]; [right| left]; reflexivity|] end.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia. auto.
Qed.


(* [comment removed for export] *)
Lemma memcmp_walk_some : forall k l r, (k <= length l)%nat -> (k <= length r)%nat -> exists v, memcmp_walk l r k = Some v.
Proof.
  induction k as [|k IH]; intros l r Hl Hr; [exists 0; reflexivity|].
  destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|]. cbn [memcmp_walk].
  destruct (bv_unsigned a =? bv_unsigned b)%Z; [apply IH; cbn in Hl, Hr; lia| eexists; reflexivity].
Qed.

(* [comment removed for export] *)
Definition bom_lit : list byte := Eval vm_compute in (match image_bytes usegs 0x58794 3 with Some bs => bs | None => [] end).
Lemma bom_lit_at : forall m, mem_inv usegs m -> bytes_at usegs m 0x58794 bom_lit.
Proof.
  intros m HI.
  assert (RO : ro_cells usegs m 0x58794 [CB 3 bom_lit]) by (apply (ro_cells_image usegs m 0x58794 bom_lit HI); [vm_compute; reflexivity | lia | cbn; lia]).
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma swrap32_small : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma san_signed_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z H. rewrite ZBridge.zb_signed, unsigned_lit by lia. replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Proofs.
  Context {CE__ : Ceiling}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB len flags fcall lo : Z) (bs0 : list byte).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 112, bv_unsigned sp); (LB, LB + 256)]%Z.
  Hypothesis AB : 0 < LB /\ LB + 256 <= alloc_ceiling /\ 1 <= len <= 254 /\ 0 <= flags < 2 ^ 32 /\ 0 <= fcall < 2 ^ 32
                  /\ alloc_ceiling <= lo /\ lo <= SP - 112 /\ SP < 2 ^ 64 /\ alloc_ceiling < 2 ^ 63.
  Notation POST := (sanitize_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB len lo bs0 m).
  (* [comment removed for export] *)
  Notation ST pc mm xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 y3 y4 y5 y6 y7 y8 y9 y10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -96)) gp tp x5 x6 x7 sp (Z_to_bv 64 LB) x10 x11 x12 x13 x14 x15 x16 x17 y2 y3 y4 y5 y6 y7 y8 y9 y10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition INVb (mX : mem) (bs : list byte) : Prop :=
    u8arr usegs mX LB bs /\ length bs = 256%nat
    /\ rw_cells usegs mX (SP + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ stk usegs mX lo (SP + -96)
    /\ mem_inv usegs mX /\ munch W m mX /\ wmono usegs m mX.
  Ltac open_inv H := destruct H as (DST & LBS & FR & ST & MI & MU & WM).

  Lemma invb_store_ok : forall mX bs k a, INVb mX bs -> 0 <= k <= 255 -> a = wa (LB + k) -> store_ok usegs mX a 1 = true.
  Proof. intros mX bs k a I Hk Ha; open_inv I. eapply (u8arr_store_ok usegs mX LB bs k a DST); [rewrite LBS; lia | exact Ha]. Qed.

  Lemma invb_store : forall mX bs k a b, INVb mX bs -> 0 <= k <= 255 -> a = wa (LB + k) -> INVb (write_to_mem mX a [b]) (upd bs (Z.to_nat k) b).
  Proof.
    intros mX bs k a b I Hk Ha. pose proof (invb_store_ok mX bs k a I Hk Ha) as SOK. open_inv I. subst a.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - apply (u8arr_write usegs mX LB bs k b DST). rewrite LBS. lia.
    - rewrite upd_length. exact LBS.
    - apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [length cells_size csize Nat.add]; lia].
    - apply stk_write; [exact ST | lia | cbn [length]; lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | cbn [length]; lia |]. cbn [inside length]. right. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma invb_call : forall mX mX' bs, INVb mX bs -> munch [(SP + -96 - 16, SP + -96)]%Z mX mX' -> wmono usegs mX mX' -> mem_inv usegs mX' -> stk usegs mX' lo (SP + -96) ->
    INVb mX' bs.
  Proof.
    intros mX mX' bs I MU' WM' MI' ST'; open_inv I.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply u8arr_transport; [exact DST| exact MU'| exact WM'|]. rewrite LBS. cbn [disjoint_from]. lia.
    - exact LBS.
    - eapply rw_cells_transport; [exact FR| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. lia.
    - exact ST'.
    - exact MI'.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp. cbn [outside]. intros a Ha. lia.
    - eapply wmono_trans; [exact WM| exact WM'].
  Qed.

  (* [comment removed for export] *)
  Ltac stb I k ADDR :=
    lazymatch type of I with INVb ?mX ?bs =>
      let SOK := fresh "SOK" in
      pose proof (invb_store_ok mX bs k (Z_to_bv 64 ADDR) I ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      zstep; clear SOK;
      rewrite t_le1_word;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?b]) _) =>
        let I2 := fresh "I" in
        pose proof (invb_store mX bs k (Z_to_bv 64 ADDR) b I ltac:(lia) ltac:(unfold wa; f_equal; lia)) as I2;
        let m2 := fresh "m" in
        remember (write_to_mem mX (Z_to_bv 64 ADDR) [b]) as m2 eqn:Em; clear Em;
        clear I; try clear mX; rename I2 into I
      end
    end.

  (* [comment removed for export] *)
  Ltac ldb I k ADDR b Hb :=
    lazymatch type of I with INVb ?mX ?bs =>
      destruct (nth_error bs (Z.to_nat k)) as [b|] eqn:Hb;
      [| exfalso; apply nth_error_None in Hb; pose proof I as (_ & ? & _); lia];
      let RD := fresh "RD" in
      pose proof (u8arr_read usegs mX LB bs k b (Z_to_bv 64 ADDR) ltac:(pose proof I as (? & _); assumption) Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      zstep; clear RD
    end.

  (* [comment removed for export] *)
  Lemma san_tail : forall mX bs i xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 y4 y5 y6 y7 y8 y9 y10 x28 x29 x30 x31,
    INVb mX bs -> 0 <= i <= len ->
    evt usegs POST (ST 0x188a6c mX xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 (Z_to_bv 64 i) y4 y5 y6 y7 y8 y9 y10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I Hi.
    zstep. rewrite (swrap32_small (i + 1)) by lia.
    zstep. if_cases KS; zify_cond KS. { exfalso. rewrite !san_signed_small in KS by lia. lia. }
    zstep. zstep. ubs_if. do 5 zstep.
    replace (Z.lxor i 9223372036854775808) with (i + 2 ^ 63) by (change 9223372036854775808 with (2 ^ 63); rewrite ZBridge.zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia).
    replace (i + LB <? LB) with false by (symmetry; apply Z.ltb_ge; lia). replace (i + 2 ^ 63 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
    change (Z.lxor (Z.lxor 0 0) 1) with 1. ubs_if.
    zstep. zstep. stb I i (i + LB).
    zstep. ubs_if. do 5 zstep.
    replace (Z.lxor (i + 1) 9223372036854775808) with (i + 1 + 2 ^ 63) by (change 9223372036854775808 with (2 ^ 63); rewrite ZBridge.zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia).
    replace (i + 1 + LB <? LB) with false by (symmetry; apply Z.ltb_ge; lia). replace (i + 1 + 2 ^ 63 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
    change (Z.lxor (Z.lxor 0 0) 1) with 1. ubs_if.
    stb I (i + 1) (i + 1 + LB).
    open_inv I. do 12 zstep. relf FR ST (bv_unsigned sp). zstep. zstep.
    rewrite !unsigned_lit in DST, LBS by lia. change (10 mod 256) with 10 in DST, LBS. change (0 mod 256) with 0 in DST, LBS.
    apply evt_done. unfold sanitize_post. do 14 eexists. exists (i + 1). do 2 eexists.
    split; [reflexivity|]. split; [lia|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact LBS|].
    split; [pose proof (rw_cells_of_u8arr usegs _ _ _ DST) as X; rewrite LBS in X; exact X|].
    rewrite upd_length in LBS. rewrite upd_length in LBS.
    replace (Z.to_nat (i + 1 - 1)) with (Z.to_nat i) by lia.
    split; [rewrite nth_error_upd_other by lia; apply nth_error_upd_same; rewrite LBS; lia| apply nth_error_upd_same; rewrite upd_length, LBS; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma san_eay : forall (k : nat) j clen mX bs xra x5 x6 x7 x10 x13 x14 x15 x16 x17 y3 y4 y5 y6 y7 y8 y9 y10 x28 x29 x30 x31,
    INVb mX bs -> j = Z.of_nat k -> j <= clen -> clen <= len -> nth_error bs (Z.to_nat clen) = Some (Z_to_bv 8 0) ->
    evt usegs POST (ST 0x1889e4 mX xra x5 x6 x7 x10 (Z_to_bv 64 1) (Z_to_bv 64 32) x13 x14 x15 x16 x17 (Z_to_bv 64 j) y3 y4 y5 y6 y7 y8 y9 y10 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I Hj Hjc Hcl NUL.
    - subst j. change (Z.of_nat 0) with 0. zstep. zstep. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
      zstep. zstep. zstep. replace (LB <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
      if_cases KN; zify_cond KN. { exfalso. rewrite ?unsigned_lit in KN by lia. lia. }
      zstep. ubs_if. zstep. ldb I 0 (LB + 0) b Hb. cbv beta.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        assert (C0 : 0 < clen).
        { destruct (Z.eq_dec clen 0) as [E|]; [| lia]. exfalso. rewrite E in NUL. cbn [Z.to_nat] in NUL. rewrite NUL in Hb. inversion Hb; subst. change (bv_unsigned (Z_to_bv 8 0)) with 0 in K0. lia. }
        zstep. zstep. th_if_lit. eapply san_tail; [exact I| lia].
      + zstep. zstep. th_if_lit. zstep. zstep. zstep. th_if_lit. eapply san_tail; [exact I| lia].
    - zstep. zstep. if_cases KO; zify_cond KO. { exfalso. clear IH. rewrite ?unsigned_lit in KO by lia. lia. }
      zstep. zstep. zstep. replace (LB + j <? 1) with false by (symmetry; apply Z.ltb_ge; clear IH; lia). cbn [Z.b2z Z.lxor].
      if_cases KN; zify_cond KN. { exfalso. clear IH. rewrite ?unsigned_lit in KN by lia. lia. }
      zstep. ubs_if. zstep. ldb I j (LB + j) b Hb. cbv beta.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. if_cases K0; zify_cond K0.
      + assert (C0 : j < clen).
        { destruct (Z.eq_dec j clen) as [E|]; [| lia]. exfalso. rewrite <- E in NUL. rewrite NUL in Hb. inversion Hb; subst. change (bv_unsigned (Z_to_bv 8 0)) with 0 in K0. lia. }
        zstep. rewrite (swrap32_small (j + 1)) by lia. zstep.
        if_cases KS; zify_cond KS. 2: { exfalso. clear IH. rewrite !san_signed_small in KS by lia. lia. }
        eapply san_tail; [exact I| lia].
      + zstep. rewrite (swrap32_small (j + -1)) by lia. zstep.
        if_cases K1; zify_cond K1. 2: { exfalso. clear IH. rewrite ?san_signed_small in K1 by lia. change (bv_signed (Z_to_bv 64 0)) with 0 in K1. lia. }
        replace (j + -1) with (Z.of_nat k) by (clear IH; lia). eapply IH; [exact I| reflexivity| | exact Hcl| exact NUL]. clear IH; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac call_ctype I :=
    lazymatch type of I with INVb ?mX ?bs =>
      eapply evt_cut;
      [ eapply ctype_check_proof; [reflexivity| reflexivity| | | rewrite unsigned_lit by lia; pose proof I as (_ & _ & _ & ? & _); eassumption| | rewrite unsigned_lit by lia| pose proof I as (_ & _ & _ & _ & ? & _); assumption]; lia
      | let ms' := fresh "ms'" in let PO := fresh "PO" in let I2 := fresh "I" in
        intros ms' PO; unfold ctype_post in PO; rewrite !unsigned_lit in PO by lia;
        destruct PO as (?r & ? & ? & ? & ?mY & -> & ?Hr & MU' & WM' & MI' & ST');
        pose proof (invb_call _ _ _ I MU' WM' MI' ST') as I2; clear I MU' WM' MI' ST'; rename I2 into I; th_ret_lit ]
    end.

  (* [comment removed for export] *)
  Lemma san_b64 : forall (k : nat) i P rem clen mX bs xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y10 x28 x29 x30 x31,
    INVb mX bs -> 0 <= i -> i + Z.of_nat (S k) = clen -> clen <= len -> P = LB + i -> rem = Z.of_nat (S k) ->
    evt usegs POST (ST 0x188a28 mX xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 i) (Z_to_bv 64 rem)
                       (Z_to_bv 64 1) (Z_to_bv 64 10) (Z_to_bv 64 13) (Z_to_bv 64 P) (Z_to_bv 64 P) y10 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I Hi Hk Hcl -> ->.
    - change (Z.of_nat 1) with 1 in *.
      zstep. zstep. replace (LB + i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
      ubs_if. zstep. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
      zstep. ubs_if.
      ldb I i (LB + i) b Hb. cbv beta. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. zstep. call_ctype I.
      zstep. if_cases K0; zify_cond K0. { eapply san_tail; [exact I| lia]. }
      ldb I i (LB + i) b2 Hb2. cbv beta. rewrite Hb in Hb2. assert (Eb : b2 = b) by congruence. subst b2. clear Hb2.
      zstep. if_cases K1; zify_cond K1. { eapply san_tail; [exact I| lia]. }
      zstep. if_cases K2; zify_cond K2. { eapply san_tail; [exact I| lia]. }
      do 5 zstep. rewrite (swrap32_small (i + 1)) by lia. th_if_lit.
      zstep. eapply san_tail; [exact I| lia].
    - zstep. zstep. replace (LB + i <? 1) with false by (symmetry; apply Z.ltb_ge; clear IH; lia). cbn [Z.b2z Z.lxor].
      ubs_if. zstep. if_cases KO; zify_cond KO. { exfalso. clear IH. rewrite ?unsigned_lit in KO by lia. lia. }
      zstep. ubs_if.
      ldb I i (LB + i) b Hb. cbv beta. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. zstep. call_ctype I.
      zstep. if_cases K0; zify_cond K0. { eapply san_tail; [exact I| lia]. }
      ldb I i (LB + i) b2 Hb2. cbv beta. rewrite Hb in Hb2. assert (Eb : b2 = b) by congruence. subst b2. clear Hb2.
      zstep. if_cases K1; zify_cond K1. { eapply san_tail; [exact I| lia]. }
      zstep. if_cases K2; zify_cond K2. { eapply san_tail; [exact I| lia]. }
      do 5 zstep. rewrite (swrap32_small (i + 1)) by (clear IH; lia). if_cases K3; zify_cond K3. 2: { exfalso. clear IH. lia. }
      eapply IH; [exact I| clear IH; lia| clear IH; lia| exact Hcl| clear IH; lia| clear IH; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma san_dflt : forall (k : nat) i P rem clen mX bs xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    INVb mX bs -> 0 <= i -> i + Z.of_nat (S k) = clen -> clen <= len -> P = LB + i -> rem = Z.of_nat (S k) ->
    evt usegs POST (ST 0x188994 mX xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 i) (Z_to_bv 64 rem)
                       (Z_to_bv 64 1) (Z_to_bv 64 10) (Z_to_bv 64 13) (Z_to_bv 64 32) (Z_to_bv 64 P) (Z_to_bv 64 P) x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I Hi Hk Hcl -> ->.
    - change (Z.of_nat 1) with 1 in *.
      (* [comment removed for export] *)
      assert (J : forall mZ bsZ x10 x12 x13 x14, INVb mZ bsZ ->
        evt usegs POST (ST 0x1889c4 mZ (Z_to_bv 64 0x1889bc) x5 x6 x7 x10 (Z_to_bv 64 64) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 i) (Z_to_bv 64 1)
                           (Z_to_bv 64 1) (Z_to_bv 64 10) (Z_to_bv 64 13) (Z_to_bv 64 32) (Z_to_bv 64 (LB + i)) (Z_to_bv 64 (LB + i)) x28 x29 x30 x31)).
      { intros mZ bsZ y10 y12 y13 y14 IZ. zstep. rewrite (swrap32_small (i + 1)) by lia. do 4 zstep. th_if_lit. zstep. eapply san_tail; [exact IZ| lia]. }
      zstep. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
      zstep. zstep. zstep. replace (LB + i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
      if_cases KN; zify_cond KN. { exfalso. rewrite ?unsigned_lit in KN by lia. lia. }
      zstep. ubs_if.
      ldb I i (LB + i) b Hb. cbv beta. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. if_cases K1; zify_cond K1. { eapply san_tail; [exact I| lia]. }
      zstep. if_cases K2; zify_cond K2. { eapply san_tail; [exact I| lia]. }
      zstep. zstep. call_ctype I.
      zstep. if_cases K0; zify_cond K0. { eapply J; exact I. }
      stb I i (LB + i). eapply J; exact I.
    - assert (J : forall mZ bsZ x10 x12 x13 x14, INVb mZ bsZ ->
        evt usegs POST (ST 0x1889c4 mZ (Z_to_bv 64 0x1889bc) x5 x6 x7 x10 (Z_to_bv 64 64) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 i) (Z_to_bv 64 (Z.of_nat (S (S k))))
                           (Z_to_bv 64 1) (Z_to_bv 64 10) (Z_to_bv 64 13) (Z_to_bv 64 32) (Z_to_bv 64 (LB + i)) (Z_to_bv 64 (LB + i)) x28 x29 x30 x31)).
      { intros mZ bsZ y10 y12 y13 y14 IZ. zstep. rewrite (swrap32_small (i + 1)) by lia. do 4 zstep. if_cases K3; zify_cond K3. { exfalso. clear IH. lia. }
        zstep. eapply IH; [exact IZ| clear IH; lia| clear IH; lia| exact Hcl| clear IH; lia| clear IH; lia]. }
      zstep. if_cases KO; zify_cond KO. { exfalso. clear IH J. rewrite ?unsigned_lit in KO by lia. lia. }
      zstep. zstep. zstep. replace (LB + i <? 1) with false by (symmetry; apply Z.ltb_ge; clear IH J; lia). cbn [Z.b2z Z.lxor].
      if_cases KN; zify_cond KN. { exfalso. clear IH J. rewrite ?unsigned_lit in KN by lia. lia. }
      zstep. ubs_if.
      ldb I i (LB + i) b Hb. cbv beta. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. if_cases K1; zify_cond K1. { eapply san_tail; [exact I| lia]. }
      zstep. if_cases K2; zify_cond K2. { eapply san_tail; [exact I| lia]. }
      zstep. zstep. call_ctype I.
      zstep. if_cases K0; zify_cond K0. { eapply J; exact I. }
      stb I i (LB + i). eapply J; exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma san_dispatch : forall clen mX bs xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y4 y5 y6 y7 y8 y9 y10 x28 x29 x30 x31,
    INVb mX bs -> 1 <= clen <= len -> nth_error bs (Z.to_nat clen) = Some (Z_to_bv 8 0) ->
    evt usegs POST (ST 0x188960 mX xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 flags) y4 y5 y6 y7 y8 y9 y10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I Hcl NUL.
    zstep. zstep. if_cases KE; zify_cond KE.
    - zstep. zstep. replace (0 <? LB) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      eapply (san_eay (Z.to_nat clen) clen clen); [exact I| lia| lia| lia| exact NUL].
    - do 8 zstep. replace (0 <? LB) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      replace (Z.land clen 4294967295) with clen by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones, Z.mod_small by lia; lia).
      if_cases KB; zify_cond KB.
      + zstep. zstep. eapply (san_b64 (Z.to_nat (clen - 1)) 0 LB clen clen); [exact I| lia| lia| lia| lia| lia].
      + zstep. zstep. zstep. eapply (san_dflt (Z.to_nat (clen - 1)) 0 LB clen clen); [exact I| lia| lia| lia| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma san_entry : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
    u8arr usegs m LB bs0 -> length bs0 = 256%nat -> nth_error bs0 (Z.to_nat len) = Some (Z_to_bv 8 0) -> stk usegs m lo SP -> mem_inv usegs m ->
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LB) (Z_to_bv 64 len) (Z_to_bv 64 flags) (Z_to_bv 64 fcall) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1888c0) fc None m (seg_rom usegs)).
  Proof.
    intros until t6. intros DST0 LBS0 NUL0 ST0 MI0.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST0. do 12 zstep. do 4 zstep.
    pose proof (conj DST0 (conj LBS0 (conj FR (conj ST0 (conj MI0 (conj MU WM)))))) as I. clear DST0 FR ST0 MU WM.
    zstep. if_cases KF; zify_cond KF. { eapply (san_dispatch len); [exact I| lia| exact NUL0]. }
    zstep. zstep. if_cases K4; zify_cond K4. { eapply (san_dispatch len); [exact I| lia| exact NUL0]. }
    do 5 zstep. zstep.
    destruct (memcmp_walk_some 3 bs0 bom_lit ltac:(rewrite LBS0; lia) ltac:(cbn; lia)) as [v Hv].
    eapply evt_cut.
    { eapply bcmp_proof; [exact MI0| rewrite unsigned_lit by lia; exact (proj1 (proj1 I))| rewrite unsigned_lit by lia; apply bom_lit_at; exact MI0
        | rewrite unsigned_lit by lia; exact Hv]. }
    intros ms' PO. destruct PO as (? & ? & ? & ? & ->). th_ret_lit.
    zstep. if_cases KV; zify_cond KV. { eapply (san_dispatch len); [exact I| lia| exact NUL0]. }
    zstep. zstep. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
    do 4 zstep. rewrite (swrap32_small (len + -3)) by lia.
    destruct I as (DST & _ & FR & ST & MI & MU & WM).
    eapply evt_cut.
    { eapply memmove_fwd_proof with (bs := bs0) (off := 3);
        [rewrite unsigned_lit by lia; apply rw_cells_of_u8arr; exact DST| rewrite !unsigned_lit by lia; lia| lia
        | rewrite unsigned_lit by lia; rewrite LBS0; lia| rewrite unsigned_lit by lia; lia| exact MI]. }
    cbv beta. intros ms' PO. unfold memmove_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU2 & WM2 & MI2 & DST2). th_ret_lit.
    rewrite LBS0 in DST2. apply u8arr_of_rw_cells in DST2.
    assert (I : INVb m2 (mv_cur (Z.to_nat 3) bs0 (Z.to_nat (len + -3)))).
    { split; [exact DST2|]. split; [rewrite mv_cur_length; rewrite LBS0; lia|].
      split; [eapply rw_cells_transport; [exact FR| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
      split; [eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2| cbn [disjoint_from]; lia]|].
      split; [exact MI2|]. split; [| eapply wmono_trans; [exact WM| exact WM2]].
      eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros a Ha. lia. }
    clear DST FR ST MI MU WM MU2 WM2 MI2 DST2.
    zstep. ubs_if. zstep. zstep. rewrite (ZBridge.zb_lxor_ones LB) by lia.
    if_cases KX; zify_cond KX. { exfalso. rewrite ?unsigned_lit in KX by lia. lia. }
    zstep. stb I (len + -3) (LB + (len + -3)).
    eapply (san_dispatch (len + -3)); [exact I| lia|].
    rewrite nth_error_upd_same; [| rewrite mv_cur_length; rewrite LBS0; lia]. rewrite unsigned_lit by lia. reflexivity.
  Qed.
End Proofs.

Theorem sanitize_line_proof {CE : Ceiling} : sanitize_line_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LB len flags fcall lo bs -> -> -> -> HLB HLBC HL HF HC LBS BUF NUL ST LO SLO MI.
  unfold SAN_STACK, FZ_SANITIZE in *. unfold ceil_window in CEIL_RANGE__.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2 ^ 64) in SPR.
  eapply san_entry; [lia| apply u8arr_of_rw_cells in BUF; exact BUF| exact LBS| exact NUL| exact ST| exact MI].
Qed.
