(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan AsanNodesFX AsanPGVal AsanPGValSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import AX2 AX2S APC AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module PORT.
  Definition msteps := OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps.
  Definition rdn := OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn.
  Definition getr := OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.getr.
  Definition mkst := OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.mkst.
  Definition frame_mod := OSSVerify.Proofs.coturn.FuzzStunClient.lib.Frame.frame_mod.
  Definition mem_grows := OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.mem_grows.
End PORT.

Lemma port_rdn_eq : PORT.rdn = rdn.
Proof. reflexivity. Qed.
Lemma port_getr_eq : PORT.getr = getr.
Proof. reflexivity. Qed.
Lemma port_mkst_eq : PORT.mkst = mkst.
Proof. reflexivity. Qed.
Lemma port_mem_grows_eq : PORT.mem_grows = mem_grows.
Proof. reflexivity. Qed.

Lemma msteps_of_port : forall segs a b, PORT.msteps segs a b -> msteps segs a b.
Proof.
  intros segs a b H. induction H as [ms | ms ms' ms'' Hsvc Hstep Hrest IH].
  - apply mst_refl.
  - eapply mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srl3_div8 : forall (x y : word), bv_unsigned y mod 64 = 3 ->
  Sem.alu64 ALU_SRL x y = Z_to_bv 64 (bv_unsigned x / 8).
Proof.
  intros x y Hy. rewrite alu_srl. unfold v_srl. rewrite Hy. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma u_add_small : forall (x : word) (c : Z),
  0 <= c -> bv_unsigned x + c < 2 ^ 64 ->
  bv_unsigned (Sem.alu64 ALU_ADD x (Z_to_bv 64 c)) = bv_unsigned x + c.
Proof.
  intros x c Hc Hs. pose proof (u64_range x). rewrite alu_add. unfold v_add.
  rewrite (u_lit64 c). unfold two64. rewrite (Z.mod_small c) by lia.
  rewrite u_lit64. unfold two64. apply Z.mod_small. lia.
Qed.

Section Helpers.
Variable SEGS : list Segment.
Hypothesis SEGS_wr : segs_wr_ok SEGS.

#[using="Type"] Lemma u_add_nowrap : forall (x y : word),
  bv_unsigned x + bv_unsigned y < 2 ^ 64 ->
  bv_unsigned (Sem.alu64 ALU_ADD x y) = bv_unsigned x + bv_unsigned y.
Proof.
  intros x y H. pose proof (u64_range x). pose proof (u64_range y). rewrite alu_add. unfold v_add.
  rewrite u_lit64. unfold two64. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma u_sub_lit : forall (x : word) (c : Z), 0 <= c <= bv_unsigned x ->
  bv_unsigned (Sem.alu64 ALU_ADD x (Z_to_bv 64 (- c))) = bv_unsigned x - c.
Proof.
  intros x c Hc. pose proof (u64_range x). rewrite alu_add. unfold v_add.
  rewrite (u_lit64 (- c)). unfold two64.
  destruct (Z.eq_dec c 0) as [->|Hnz].
  { rewrite Z.mod_0_l by lia. rewrite u_lit64. unfold two64. rewrite Z.mod_small; lia. }
  replace ((- c) mod 2 ^ 64) with (2 ^ 64 - c).
  2: { replace (-c) with ((2^64 - c) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small; lia. }
  replace (bv_unsigned x + (2 ^ 64 - c)) with ((bv_unsigned x - c) + 1 * 2 ^ 64) by lia.
  rewrite u_lit64. unfold two64. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
#[using="SEGS_wr"] Lemma store_ok_readable : forall M (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  store_ok SEGS M (Z_to_bv 64 a) n = true ->
  forall i, 0 <= i < Z.of_nat n -> exists b, rdn SEGS M (Z_to_bv 64 (a + i)) 1 = Some [b].
Proof.
  intros M a n Ha Hn Hst i Hi.
  pose proof (store_ok_all SEGS M n (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; lia) Hst (Z_to_bv 64 (a + i))
                ltac:(rewrite !u64_lit by lia; lia)) as W.
  assert (Hst1 : store_ok SEGS M (Z_to_bv 64 (a + i)) 1 = true).
  { apply store_ok_of_all; [rewrite u64_lit by lia; cbn; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. cbn in Hx.
    replace x with (Z_to_bv 64 (a + i)); [exact W|]. apply bv_eq. rewrite u64_lit by lia. lia. }
  destruct (store_ok_rdn SEGS SEGS_wr 1 M (Z_to_bv 64 (a + i)) ltac:(rewrite u64_lit by lia; cbn; lia) Hst1) as (bs & Hrd & Hlen).
  destruct bs as [|b [|? ?]]; try discriminate. exists b. exact Hrd.
Qed.
End Helpers.

Lemma w2b1 : forall w : word, word_to_le_bytes 1 w = [Z_to_bv 8 (bv_unsigned w)].
Proof. intros. reflexivity. Qed.

Lemma zbv8_mod64 : forall v, Z_to_bv 8 (v mod 2 ^ 64) = Z_to_bv 8 v.
Proof.
  intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 56). reflexivity.
Qed.

Lemma estart_lit0 : forall E a, estart E (SA (ELit 0) a) = a.
Proof. intros. unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. Qed.

Lemma mod64_diff_zero : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> (a - b) mod 2 ^ 64 = 0 -> a = b.
Proof.
  intros a b Ha Hb H. apply Znumtheory.Zmod_divide in H; [|lia]. destruct H as [q Hq].
  assert (q = 0) by nia. subst q. lia.
Qed.

Lemma mod_of_align : forall e k x, (2 ^ e | x)%Z -> 0 <= k <= e -> x mod 2 ^ k = 0.
Proof.
  intros e k x [q Hq] Hk. rewrite Hq. replace e with ((e - k) + k) by lia. rewrite Z.pow_add_r by lia.
  rewrite Z.mul_assoc. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Hypothesis SEGS_wr : segs_wr_ok SEGS.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.
Variable P : FAParams.
Hypothesis FCA : F_contract_asan SEGS P.

Hypothesis SHADOW_ok : shadow_ok A.
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma unlin_nowrap_val : forall E M k c ts, know_ok SEGS E M k -> lin_nowrap_l k c ts = true ->
  bv_unsigned (edenot E (unlin (c, ts))) = c + tden E ts.
Proof.
  intros E M k c ts HK H. unfold lin_nowrap_l in H.
  destruct (lin_range (erange k) c ts) as [[lo hi]|] eqn:Hlr; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  pose proof (lin_range_sound E (erange k) (fun a0 lo0 hi0 Ha => erange_sound SEGS E M k a0 lo0 hi0 HK Ha) _ _ _ _ Hlr) as HR.
  pose proof (unlin_sound E (c, ts)) as [q Hq']. unfold lden, AX2S.uE in Hq'. cbn [fst snd] in Hq'.
  pose proof (u64_range (edenot E (unlin (c, ts)))) as Hu. clear - Hq' Hu HR H1 H2. nia.
Qed.

#[using="Type"] Lemma estart_of_split : forall E e b k m,
  split_lit e = (b, k) -> 0 <= estart E (SA b k) -> estart E (SA b k) + m <= 2 ^ 64 -> 0 < m ->
  estart E (SA b k) = bv_unsigned (edenot E e).
Proof.
  intros E e b k m Hs G0 G1 Gm. pose proof (w_split_lit_denot E e b k Hs) as D.
  apply (f_equal bv_unsigned) in D. rewrite u_lit64 in D. unfold two64 in D.
  unfold estart in *. cbn [a_base a_off] in *. rewrite Z.mod_small in D by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="SHADOW_ok"] Lemma u_shadow_expr : forall E M k b,
  know_ok SEGS E M k -> bv_unsigned (edenot E b) / 8 + shadow_off A < 2 ^ 64 ->
  bv_unsigned (edenot E (eadd (mkSrl k b 3) (ELit (shadow_off A)))) = bv_unsigned (edenot E b) / 8 + shadow_off A.
Proof.
  intros E M k b HK Hb. pose proof SHADOW_ok as SO. unfold shadow_ok in SO. pose proof (u64_range (edenot E b)) as Rb.
  unfold eadd. rewrite mkAlu_denot. cbn [edenot].
  rewrite (mkSrl_denot SEGS E M k b 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)).
  rewrite (srl3_div8 (edenot E b) (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity).
  assert (0 <= bv_unsigned (edenot E b) / 8) by (apply Z.div_pos; lia).
  rewrite (u_add_small (Z_to_bv 64 (bv_unsigned (edenot E b) / 8)) (shadow_off A)); rewrite ?u64_lit; lia.
Qed.

#[using="Type"] Lemma u_srl3 : forall E M k ne, know_ok SEGS E M k ->
  bv_unsigned (edenot E (mkSrl k ne 3)) = bv_unsigned (edenot E ne) / 8.
Proof.
  intros E M k ne HK. pose proof (u64_range (edenot E ne)) as R.
  rewrite (mkSrl_denot SEGS E M k ne 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)).
  rewrite (srl3_div8 (edenot E ne) (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity).
  assert (0 <= bv_unsigned (edenot E ne) / 8) by (apply Z.div_pos; lia).
  assert (bv_unsigned (edenot E ne) / 8 < 2 ^ 64) by (apply Z.div_lt_upper_bound; lia).
  rewrite u64_lit by lia. reflexivity.
Qed.

#[using="SHADOW_ok"] Lemma shadow_of_den : forall E M k b n sb sk sn m,
  know_ok SEGS E M k -> shadow_of A k b n = (sb, sk, sn) ->
  0 <= estart E (SA sb sk) -> estart E (SA sb sk) + m <= 2 ^ 64 -> 0 < m ->
  bv_unsigned (edenot E b) / 8 + shadow_off A < 2 ^ 64 ->
  estart E (SA sb sk) = shadow_off A + bv_unsigned (edenot E b) / 8 /\ elenZ E sn = bv_unsigned (edenot E n) / 8.
Proof.
  intros E M k b n sb sk sn m HK Hsh G0 G1 Gm Hb. unfold shadow_of in Hsh.
  destruct (split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hs. injection Hsh as Esn Esk Esb. subst sb' sk' sn.
  split.
  - rewrite (estart_of_split E _ sb sk m Hs G0 G1 Gm). rewrite (u_shadow_expr E M k b HK Hb). lia.
  - unfold elenZ. apply (u_srl3 E M k n HK).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma cell_is_sound : forall E M k b off w v,
  know_ok SEGS E M k -> (1 <= w <= 8)%nat -> FN.cell_is SEGS k b off w v = true ->
  rdn SEGS M (Z_to_bv 64 (estart E (SA b off))) w = Some (word_to_le_bytes w (Z_to_bv 64 v))
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + Z.of_nat w <= 2 ^ 64.
Proof.
  intros E M k b off w v HK Hw H. unfold FN.cell_is in H. apply andb_prop in H as [Hfl H].
  destruct (know_lookup SEGS k b off w false [] []) as [e sc hs|sc hs|] eqn:HL; try discriminate.
  destruct sc; [|discriminate].
  destruct (erange k e) as [[lo hi]|] eqn:Her; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst lo hi.
  pose proof (erange_sound SEGS E M k e v v HK Her) as Hv.
  destruct (flat_x_sound SEGS E M k b off (ELit (Z.of_nat w)) HK Hfl) as (Clo & Chi & _).
  cbn [edenot] in Chi. rewrite u64_lit in Chi by lia.
  destruct (lookup_piece SEGS E M k b off w e hs HK Hw HL ltac:(unfold flat; lia)) as (bs & Hrd & Hlen & Hbs).
  split; [|lia]. rewrite Hrd, <- Hbs. do 2 f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E e)). f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cell_expr_sound : forall E M k b off e,
  know_ok SEGS E M k -> FN.cell_expr SEGS k b off = Some e ->
  rdn SEGS M (Z_to_bv 64 (estart E (SA b off))) 8 = Some (word_to_le_bytes 8 (edenot E e))
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + 8 <= 2 ^ 64.
Proof.
  intros E M k b off e HK H. unfold FN.cell_expr in H.
  destruct (flat_x k b off (ELit 8)) eqn:Hfl; [|discriminate].
  destruct (know_lookup SEGS k b off 8 false [] []) as [e' sc hs|sc hs|] eqn:HL; try discriminate.
  destruct sc; [|discriminate]. injection H as ->.
  destruct (flat_x_sound SEGS E M k b off (ELit 8) HK Hfl) as (Clo & Chi & _).
  cbn [edenot] in Chi. rewrite u64_lit in Chi by lia.
  destruct (lookup_piece SEGS E M k b off 8 e hs HK ltac:(lia) HL ltac:(unfold flat; lia)) as (bs & Hrd & Hlen & Hbs).
  split; [|lia]. rewrite Hrd, <- Hbs. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="SEGS_wr"] Lemma rw_lit_sound : forall E M k b off n,
  know_ok SEGS E M k -> 0 < n -> FN.rw_lit k b off n = true ->
  store_ok SEGS M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
  /\ (forall i, 0 <= i < n -> store_ok SEGS M (Z_to_bv 64 (estart E (SA b off) + i)) 1 = true)
  /\ (forall i, 0 <= i < n -> exists bt, rdn SEGS M (Z_to_bv 64 (estart E (SA b off) + i)) 1 = Some [bt])
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
  intros E M k b off n HK Hn H. unfold FN.rw_lit in H. apply andb_prop in H as [Hw Hfl].
  destruct (kwritable_sound SEGS E M k k b off n HK HK Hw ltac:(lia)) as (Hst & Hlo & Hhi).
  set (s := estart E (SA b off)) in *.
  assert (RD : forall i, 0 <= i < n -> exists bt, rdn SEGS M (Z_to_bv 64 (s + i)) 1 = Some [bt]).
  { intros i Hi. eapply (store_ok_readable SEGS SEGS_wr M s (Z.to_nat n)); try lia. exact Hst. }
  repeat split; try lia; try exact Hst; try exact RD.
  intros i Hi. apply store_ok_of_all; [rewrite u64_lit by lia; cbn; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia. cbn in Hx.
  apply (store_ok_all SEGS M (Z.to_nat n) (Z_to_bv 64 s) ltac:(rewrite u64_lit by lia; lia) Hst).
  rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="SEGS_wr"] Lemma rw_x_sound : forall E M k b off ne,
  know_ok SEGS E M k -> FN.rw_x k b off ne = true ->
  (forall i, 0 <= i < elenZ E ne -> store_ok SEGS M (Z_to_bv 64 (estart E (SA b off) + i)) 1 = true)
  /\ (forall i, 0 <= i < elenZ E ne -> exists bt, rdn SEGS M (Z_to_bv 64 (estart E (SA b off) + i)) 1 = Some [bt])
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E ne <= 2 ^ 64 /\ 0 < elenZ E ne.
Proof.
  intros E M k b off ne HK H. unfold FN.rw_x in H. apply andb_prop in H as [Hw Hfl].
  destruct (kwritable_x_sound SEGS E M k k b off ne HK HK Hw) as (Hst & Hlo & Hhi).
  destruct (flat_x_sound SEGS E M k b off ne HK Hfl) as (_ & _ & Hpos). fold (elenZ E ne) in Hpos.
  set (s := estart E (SA b off)) in *.
  pose proof (u64_range (edenot E ne)) as Rn. fold (elenZ E ne) in Rn.
  pose proof (Hst (Z.to_nat (elenZ E ne)) ltac:(lia)) as HstN.
  assert (RD : forall i, 0 <= i < elenZ E ne -> exists bt, rdn SEGS M (Z_to_bv 64 (s + i)) 1 = Some [bt]).
  { intros i Hi. eapply (store_ok_readable SEGS SEGS_wr M s (Z.to_nat (elenZ E ne))); try lia. exact HstN. }
  repeat split; try lia; try exact RD.
  intros i Hi. apply store_ok_of_all; [rewrite u64_lit by lia; cbn; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia. cbn in Hx.
  apply (store_ok_all SEGS M (Z.to_nat (elenZ E ne)) (Z_to_bv 64 s) ltac:(rewrite u64_lit by lia; lia) HstN).
  rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zero_lit_sound : forall E M k b off n,
  know_ok SEGS E M k -> 0 < n < 2 ^ 64 -> FN.zero_lit k b off n = true ->
  (forall i, 0 <= i < n -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0))
  /\ (forall i, 0 <= i < n -> rdn SEGS M (Z_to_bv 64 (estart E (SA b off) + i)) 1 = Some [Z_to_bv 8 0])
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
  intros E M k b off n HK Hn H. unfold FN.zero_lit in H. apply andb_prop in H as [Hz Hfl].
  destruct (kzero_x_sound SEGS E M k k b off (ELit n) HK HK Hz) as (Zb & Hlo & Hhi).
  replace (elenZ E (ELit n)) with n in Zb, Hhi by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  repeat split; try lia; try exact Zb.
  intros i Hi. cbn [rdn]. rewrite (Zb i Hi). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma apart_all_sound : forall E M k ws b off w,
  know_ok SEGS E M k -> FN.apart_all k ws b off w = true ->
  Forall (fun r => let '(wb, wk, wn) := r in
            estart E (SA b off) + elenZ E (ELit w) <= estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= estart E (SA b off)) ws.
Proof.
  intros E M k ws b off w HK H. unfold FN.apart_all in H. apply Forall_forall. intros [[wb wk] wn] Hin.
  pose proof (proj1 (forallb_forall _ _) H _ Hin) as Hr. cbn beta iota in Hr.
  exact (ranges_apart_x_sound SEGS E M k b off (ELit w) wb wk wn HK Hr).
Qed.

(* [comment removed for export] *)
Definition inr (E : env) (r : expr * Z * expr) (x : word) : bool :=
  let '(b, off, n) := r in
  (Z.leb (estart E (SA b off)) (bv_unsigned x) && Z.ltb (bv_unsigned x) (estart E (SA b off) + elenZ E n))%bool.

#[using="Type"] Lemma havoc1_sound : forall E M M' k b off n,
  know_ok SEGS E M k ->
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E n <= bv_unsigned x -> M' x = M x) ->
  mem_grows M M' ->
  know_ok SEGS E M' (FN.havoc1 k b off n).
Proof.
  intros E M M' k b off n HK Hout Hg. unfold FN.havoc1.
  assert (G : know_ok SEGS E M' (kn_havocK k b off n)) by (eapply w_know_ok_havocK; eassumption).   (* [comment removed for export] *)
  destruct b as [z| | | | | | |]; try exact G. destruct z; try exact G.
  destruct n as [len| | | | | | |]; try exact G.
  eapply w_know_ok_havocK; [apply kimg_cut_sound; exact HK | exact Hout | exact Hg].
Qed.

#[using="Type"] Lemma havocs_sound : forall E ws M M' k,
  know_ok SEGS E M k ->
  mem_grows M M' ->
  (forall x : word, forallb (fun r => negb (inr E r x)) ws = true -> M' x = M x) ->
  know_ok SEGS E M' (FN.havocs k ws).
Proof.
  intros E ws. induction ws as [|[[b off] n] ws IH]; intros M M' k HK Hg Hout.
  - cbn [FN.havocs]. assert (EM : M' = M) by (apply functional_extensionality; intros x; apply Hout; reflexivity). rewrite EM. exact HK.
  - cbn [FN.havocs].
    set (M1 := fun x : word => if inr E (b, off, n) x then M' x else M x).
    assert (Hg1 : mem_grows M M1).
    { intros x Hx. unfold M1. destruct (inr E (b, off, n) x); [apply Hg; exact Hx | exact Hx]. }
    apply (IH M1 M').
    + apply (havoc1_sound E M M1 k b off n HK); [|exact Hg1].
      intros x Hx. unfold M1, inr. destruct (Z.leb_spec (estart E (SA b off)) (bv_unsigned x)); [|reflexivity].
      destruct (Z.ltb_spec (bv_unsigned x) (estart E (SA b off) + elenZ E n)); [lia | reflexivity].
    + intros x Hx. unfold M1 in Hx |- *. destruct (inr E (b, off, n) x); [exact Hx | apply Hg; exact Hx].
    + intros x Hx. unfold M1. destruct (inr E (b, off, n) x) eqn:Hi; [reflexivity|].
      apply Hout. cbn [forallb]. rewrite Hi. exact Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kept_of_ekeeps : forall R R', ekeeps R R' -> kept_ok R R'.
Proof.
  intros R R' HE r Hr0 Hnc. apply HE.
  pose proof (reg_of_ridx r (ridx r) eq_refl) as Hr.
  assert (Hlt : (ridx r < 32)%nat).
  { unfold ridx. pose proof (bv_unsigned_in_range 5 r) as X. change (bv_modulus 5) with 32 in X. lia. }
  assert (Hnz : ridx r <> 0%nat).
  { intros H0. apply Hr0. rewrite Hr, H0. apply bv_eq. reflexivity. }
  rewrite Hr. unfold caller_saved in Hnc.
  set (n := ridx r) in *. clearbody n.
  do 32 (destruct n as [|n]; [ first [ exfalso; apply Hnc; cbn; tauto
                                     | exfalso; apply Hnz; reflexivity
                                     | unfold ekept; cbn;
                                       repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end ] |]).
  exfalso. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zero_kept : forall (M M' : word -> option byte) (x : word),
  M x = Some (Z_to_bv 8 0) -> mem_grows M M' ->
  rdn SEGS M' x 1 = Some [Z_to_bv 8 0] -> M' x = M x.
Proof.
  intros M M' x H0 Hg Hr. rewrite H0. cbn [rdn] in Hr.
  destruct (M' x) as [b'|] eqn:Hm'.
  - injection Hr as Hb. rewrite Hb. reflexivity.
  - exfalso. apply (Hg x); [rewrite H0; discriminate | exact Hm'].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mk_ctx_inv : forall cs c, FN.mk_ctx SEGS A P cs = Some c ->
  let k := kn cs in
  pc cs = fa_entry P
  /\ ret_lit cs = Some (fa_ret P) /\ FN.c_ret c = fa_ret P
  /\ reg_lit cs 4 = Some (fa_tp P)
  /\ FN.c_sp c = reg cs 2 /\ FN.c_data c = reg cs 10 /\ FN.c_ne c = reg cs 11
  /\ split_lit (reg cs 2) = (FN.c_spb c, FN.c_spk c)
  /\ split_lit (reg cs 10) = (FN.c_db c, FN.c_dk c)
  /\ FN.cell_expr SEGS k (ELit 0) (fa_tp P) = Some (FN.c_efs c)
  /\ FN.cell_expr SEGS k (ELit 0) (fa_tp P + 0x8) = Some (FN.c_edb c)
  /\ FN.cell_expr SEGS k (ELit 0) (fa_tsd P) = Some (FN.c_ectx c)
  /\ split_lit (FN.c_efs c) = (FN.c_fsb c, FN.c_fsk c)
  /\ split_lit (FN.c_edb c) = (FN.c_dbb c, FN.c_dbk c)
  /\ split_lit (FN.c_ectx c) = (FN.c_cxb c, FN.c_cxk c)
  /\ FN.cell_expr SEGS k (FN.c_cxb c) (FN.c_cxk c + 0x98) = Some (FN.c_ethr c)
  /\ split_lit (FN.c_ethr c) = (FN.c_thb c, FN.c_thk c)
  /\ xlo k (reg cs 11) = Some (FN.c_nlo c) /\ xhi k (reg cs 11) = Some (FN.c_nhi c)
  /\ xlo k (reg cs 10) = Some (FN.c_dlo c) /\ xhi k (reg cs 10) = Some (FN.c_dhi c)
  /\ xlo k (reg cs 2) = Some (FN.c_splo c) /\ xhi k (reg cs 2) = Some (FN.c_sphi c)
  /\ xlo k (FN.c_efs c) = Some (FN.c_flo c) /\ xhi k (FN.c_efs c) = Some (FN.c_fhi c)
  /\ FN.c_shf c = shadow_of A k (eaddz (reg cs 2) (- fa_frame P)) (ELit (fa_frame P))
  /\ FN.c_shs c = shadow_of A k (eaddz (FN.c_efs c) FS_FRAMES) (ELit FS_FRAMES_LEN)
  /\ FN.c_shd c = split_lit (eadd (mkSrl k (reg cs 10) 3) (ELit (shadow_off A)))
  /\ FN.c_ws c = [ (FN.c_spb c, FN.c_spk c - fa_frame P, ELit (fa_frame P))
                 ; (FN.c_fsb c, FN.c_fsk c, ELit FS_HINTS)
                 ; (FN.c_fsb c, FN.c_fsk c + FS_FRAMES, ELit FS_FRAMES_LEN)
                 ; (fst (fst (FN.c_shs c)), snd (fst (FN.c_shs c)), snd (FN.c_shs c))
                 ; (ELit 0, fa_prng P, ELit 8)
                 ; (ELit 0, fa_errno P, ELit 4) ]
  /\ FN.c_wall c = [ (FN.c_spb c, FN.c_spk c - fa_frame P, ELit (fa_frame P))
                   ; (fst (fst (FN.c_shf c)), snd (fst (FN.c_shf c)), snd (FN.c_shf c))
                   ; (FN.c_fsb c, FN.c_fsk c, ELit FS_HINTS)
                   ; (FN.c_fsb c, FN.c_fsk c + FS_FLAGS, ELit FS_FLAGS_LEN)
                   ; (FN.c_fsb c, FN.c_fsk c + FS_FRAMES, ELit FS_FRAMES_LEN)
                   ; (fst (fst (FN.c_shs c)), snd (fst (FN.c_shs c)), snd (FN.c_shs c))
                   ; (ELit 0, fa_prng P, ELit 8)
                   ; (ELit 0, fa_errno P, ELit 4)
                   ; (FN.c_spb c, FN.c_spk c, ELit 16)
                   ; (fst (fst (FN.c_shf c)), snd (fst (FN.c_shf c)) + fa_frame P / 8, ELit 2) ].
Proof.
  intros cs c H. unfold FN.mk_ctx in H.
  destruct (Z.eqb (pc cs) (fa_entry P)) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 4) as [tp|] eqn:Htp; [|discriminate].
  destruct (Z.eqb ret (fa_ret P) && Z.eqb tp (fa_tp P))%bool eqn:Hrt; [|discriminate]. cbn [negb] in H.
  apply andb_prop in Hrt as [Hr1 Hr2]. apply Z.eqb_eq in Hr1. apply Z.eqb_eq in Hr2. subst ret tp.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hssp.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hsd.
  destruct (FN.cell_expr SEGS (kn cs) (ELit 0) (fa_tp P)) as [efs|] eqn:Hefs; [|discriminate].
  destruct (FN.cell_expr SEGS (kn cs) (ELit 0) (fa_tp P + 0x8)) as [edb|] eqn:Hedb; [|discriminate].
  destruct (FN.cell_expr SEGS (kn cs) (ELit 0) (fa_tsd P)) as [ectx|] eqn:Hectx; [|discriminate].
  destruct (split_lit efs) as [fsb fsk] eqn:Hsfs.
  destruct (split_lit edb) as [dbb dbk] eqn:Hsdb.
  destruct (split_lit ectx) as [cxb cxk] eqn:Hscx.
  destruct (FN.cell_expr SEGS (kn cs) cxb (cxk + 0x98)) as [ethr|] eqn:Hethr; [|discriminate].
  destruct (split_lit ethr) as [thb thk] eqn:Hsth.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:E1; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:E2; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [dlo|] eqn:E3; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:E4; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:E5; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:E6; [|discriminate].
  destruct (xlo (kn cs) efs) as [flo|] eqn:E7; [|discriminate].
  destruct (xhi (kn cs) efs) as [fhi|] eqn:E8; [|discriminate].
  injection H as <-. cbn.
  repeat split; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Tst (b : bool) : Prop := b = true.
Ltac hideT := repeat match goal with H : ?b = true |- _ => change (b = true) with (Tst b) in H end.
(* [comment removed for export] *)
Definition Hid (P : Prop) : Prop := P.
#[using="SEGS_wx SEGS_in_hull HULL_ok SEGS_wr argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FCA SHADOW_ok"] Theorem node_F_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (FN.node_F SEGS A nx0 P).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  rewrite FN.node_F_eq in Hn. (* [comment removed for export] *) unfold FN.node_F_ref in Hn.
  destruct (FN.mk_ctx SEGS A P cs) as [c|] eqn:Hctx; [|discriminate].
  destruct (forallb (fun b : bool => b) (FN.tests SEGS A nx0 P cs c)) eqn:Htests; [|discriminate].
  pose proof (mk_ctx_inv cs c Hctx) as CTX. cbv zeta in CTX.
  destruct CTX as (Hpc & Hret & Hcret & Htp & Hcsp & Hcdata & Hcne & Hssp & Hsd & Hefs & Hedb & Hectx & Hsfs & Hsdb & Hscx
                   & Hethr & Hsth & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & Hshf & Hshs & Hshd & Hws & Hwall).
  (* [comment removed for export] *)
  set (fr := fa_frame P) in *.
  set (sp := reg cs 2) in *. set (data := reg cs 10) in *. set (ne := reg cs 11) in *.
  set (spb := FN.c_spb c) in *. set (spk := FN.c_spk c) in *. set (db := FN.c_db c) in *. set (dk := FN.c_dk c) in *.
  set (efs := FN.c_efs c) in *. set (fsb := FN.c_fsb c) in *. set (fsk := FN.c_fsk c) in *.
  set (edb := FN.c_edb c) in *. set (dbb := FN.c_dbb c) in *. set (dbk := FN.c_dbk c) in *.
  set (ectx := FN.c_ectx c) in *. set (cxb := FN.c_cxb c) in *. set (cxk := FN.c_cxk c) in *.
  set (ethr := FN.c_ethr c) in *. set (thb := FN.c_thb c) in *. set (thk := FN.c_thk c) in *.
  set (nlo := FN.c_nlo c) in *. set (nhi := FN.c_nhi c) in *. set (dlo := FN.c_dlo c) in *. set (dhi := FN.c_dhi c) in *.
  set (splo := FN.c_splo c) in *. set (sphi := FN.c_sphi c) in *. set (flo := FN.c_flo c) in *. set (fhi := FN.c_fhi c) in *.
  (* [comment removed for export] *)
  unfold FN.tests in Htests.
  destruct (FN.c_shf c) as [[shfb shfk] shfn] eqn:Dshf. destruct (FN.c_shs c) as [[shsb shsk] shsn] eqn:Dshs.
  destruct (FN.c_shd c) as [shdb shdk] eqn:Dshd.
  cbn [forallb fst snd] in Htests.
  rewrite ?Hcsp, ?Hcdata, ?Hcne in Htests.
  fold fr sp data ne spb spk db dk efs fsb fsk edb dbb dbk ectx cxb cxk ethr thb thk nlo nhi dlo dhi splo sphi flo fhi in Htests.
  apply andb_prop in Htests as [T0 Htests]. apply andb_prop in Htests as [T1 Htests]. apply andb_prop in Htests as [T2 Htests].
  apply andb_prop in Htests as [T3 Htests]. apply andb_prop in Htests as [T4 Htests]. apply andb_prop in Htests as [T5 Htests].
  apply andb_prop in Htests as [T6 Htests]. apply andb_prop in Htests as [T7 Htests]. apply andb_prop in Htests as [T8 Htests].
  apply andb_prop in Htests as [T9 Htests]. apply andb_prop in Htests as [T10 Htests]. apply andb_prop in Htests as [T11 Htests].
  apply andb_prop in Htests as [T12 Htests]. apply andb_prop in Htests as [T13 Htests]. apply andb_prop in Htests as [T14 Htests].
  apply andb_prop in Htests as [T15 Htests]. apply andb_prop in Htests as [T16 Htests]. apply andb_prop in Htests as [T17 Htests].
  apply andb_prop in Htests as [T18 Htests]. apply andb_prop in Htests as [T19 Htests]. apply andb_prop in Htests as [T20 Htests].
  apply andb_prop in Htests as [T21 Htests]. apply andb_prop in Htests as [T22 Htests]. apply andb_prop in Htests as [T23 Htests].
  apply andb_prop in Htests as [T24 Htests]. apply andb_prop in Htests as [T25 Htests]. apply andb_prop in Htests as [T26 Htests].
  apply andb_prop in Htests as [T27 Htests]. apply andb_prop in Htests as [T28 Htests]. apply andb_prop in Htests as [T29 Htests].
  apply andb_prop in Htests as [T30 Htests]. apply andb_prop in Htests as [T31 Htests]. apply andb_prop in Htests as [T32 Htests].
  apply andb_prop in Htests as [T33 Htests]. apply andb_prop in Htests as [T34 Htests]. apply andb_prop in Htests as [T35 _].
  rewrite ?Hcsp, ?Hcdata, ?Hcne in *.
  hideT.
  (* [comment removed for export] *)
  apply andb_prop in T1 as [T1 T1d]. apply andb_prop in T1 as [T1 T1c]. apply andb_prop in T1 as [T1a T1b].
  apply Z.eqb_eq in T1a. apply Z.eqb_eq in T1b. apply Z.ltb_lt in T1c. apply Z.ltb_lt in T1d.
  apply andb_prop in T2 as [T2a T2b]. apply Z.leb_le in T2a. apply Z.ltb_lt in T2b.
  apply Z.leb_le in T3. (* [comment removed for export] *) apply Z.leb_le in T5. apply Z.leb_le in T7.
  apply andb_prop in T8 as [T8a T8b]. apply Z.leb_le in T8a. apply Z.leb_le in T8b.
  apply andb_prop in T9 as [T9 T9c]. apply andb_prop in T9 as [T9a T9b]. apply Z.leb_le in T9a. apply Z.leb_le in T9c.
  (* [comment removed for export] *)
  unfold F_SPLO, F_SPHI, HIGHMEM_LO, VA_HI, FS_LEN in *.
  (* [comment removed for export] *)
  destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model (fa_ret P) HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  destruct (w_reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 4 (fa_tp P) HC ltac:(lia) Htp) as [R4 Htpr].
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  fold sp in R2. fold data in R10. fold ne in R11.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) in R4 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
  set (spw := edenot E sp) in *. set (dataw := edenot E data) in *. set (nw := edenot E ne) in *.
  set (usp := bv_unsigned spw). set (ud := bv_unsigned dataw). set (n := bv_unsigned nw).
  pose proof (u64_range spw) as Rsp. pose proof (u64_range dataw) as Rd. pose proof (u64_range nw) as Rn.
  fold usp in Rsp. fold ud in Rd. fold n in Rn.
  (* [comment removed for export] *)
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN E1) as Bnlo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN E2) as Bnhi.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN E3) as Bdlo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN E4) as Bdhi.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN E5) as Bsplo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN E6) as Bsphi.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN E7) as Bflo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN E8) as Bfhi.
  fold spw usp dataw ud nw n in Bnlo, Bnhi, Bdlo, Bdhi, Bsplo, Bsphi.
  set (fsw := edenot E efs) in *. set (fs := bv_unsigned fsw). fold fs in Bflo, Bfhi. pose proof (u64_range fsw) as Rfs. fold fs in Rfs.
  (* [comment removed for export] *)
  destruct (ealign_sound SEGS E M (kn cs) data HKN) as [_ ALd]. fold dataw ud in ALd.
  destruct (ealign_sound SEGS E M (kn cs) sp HKN) as [_ ALs]. fold spw usp in ALs.
  destruct (ealign_sound SEGS E M (kn cs) efs HKN) as [_ ALf]. fold fsw fs in ALf.
  assert (Hud16 : ud mod 16 = 0) by (change 16 with (2 ^ 4); eapply mod_of_align; [exact ALd | lia]).
  assert (Husp16 : usp mod 16 = 0) by (change 16 with (2 ^ 4); eapply mod_of_align; [exact ALs | lia]).
  assert (Hfs4096 : fs mod 4096 = 0) by (change 4096 with (2 ^ 12); eapply mod_of_align; [exact ALf | lia]).
  (* [comment removed for export] *)
  set (ctx := estart E (SA cxb cxk)). set (thr := estart E (SA thb thk)). set (dbv := estart E (SA dbb dbk)).
  (* [comment removed for export] *)
  assert (P1 : getr R 1 = Z_to_bv 64 (fa_ret P)) by exact R1.
  assert (P2 : getr R 2 = spw) by exact R2.
  assert (P4 : getr R 4 = Z_to_bv 64 (fa_tp P)) by exact R4.
  assert (P10 : getr R 10 = dataw) by exact R10.
  assert (P11 : getr R 11 = Z_to_bv 64 n) by (rewrite R11; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Pn : 0 <= n < fa_nmax P) by lia.
  assert (Pd0 : ud <> 0) by lia.
  assert (Pd63 : ud + n < 2 ^ 63).
  { unfold Tst in T4. apply orb_prop in T4 as [T4|T4].
    - apply Z.ltb_lt in T4. lia.
    - pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN T4) as L4. cbn [xt_den] in L4.
      rewrite edenot_lit, u_small in L4 by lia. fold dataw nw in L4. fold ud n in L4. lia. }
  (* [comment removed for export] *)
  assert (PdH : 0 < n -> Hid (ud + n <= 0x7fff7000 \/ 0x10007fff8000 <= ud) /\ ud + n <= 2 ^ 47 - 64).
  { intros Hn0. destruct (Z.eqb_spec nhi 0); [lia|]. cbn [orb] in T6.
    apply andb_prop in T6 as [T6 T6c]. apply andb_prop in T6 as [T6a T6b].
    apply Z.leb_le in T6a. split.
    - unfold Hid. apply orb_prop in T6b as [T6b|T6b]; [apply Z.leb_le in T6b; right; lia|].
      pose proof (off_band_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model data 0 ne HC T6b) as OB.
      unfold estart, elenZ in OB. cbn [a_base a_off] in OB. rewrite Z.add_0_r in OB. fold dataw nw in OB. fold ud n in OB.
      specialize (OB ltac:(lia)). unfold LOWTOP, KHI, TOPMAX, STK in *. lia.
    - apply orb_prop in T6c as [T6c|T6c]; [apply Z.leb_le in T6c; lia|].
      pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN T6c) as L6. cbn [xt_den] in L6.
      rewrite edenot_lit, u_small in L6 by lia. fold dataw nw in L6. fold ud n in L6. lia. }
  assert (Psp : 0x7fff80000000 - 4096 <= usp) by lia.
  assert (Psp2 : usp + 16 <= 0x800000000000) by lia.
  (* [comment removed for export] *)
  assert (Pfs1 : Hid (fs + 11571200 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)).
  { unfold Hid. unfold Tst in T9b. apply orb_prop in T9b as [Hx|Hx]; [apply Z.leb_le in Hx; right; lia|].
    pose proof (off_band_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model efs 0 (ELit 11571200) HC Hx) as OB.
    unfold estart, elenZ in OB. cbn [a_base a_off edenot] in OB. rewrite Z.add_0_r in OB. fold fsw fs in OB.
    rewrite u64_lit in OB by lia. specialize (OB ltac:(lia)). unfold LOWTOP, KHI, TOPMAX, STK in *. lia. }
  clear T6 T9b.   (* [comment removed for export] *)
  assert (Pfs2 : fs + 11571200 <= 2 ^ 47) by lia.
  assert (Pimg : fa_imgend P <= fs) by (unfold Tst in T35; apply Z.leb_le in T35; lia).   (* [comment removed for export] *)
  assert (PD1 : ud + n + 4096 <= usp - fr \/ usp + 4112 <= ud).
  { left. unfold Tst in T10. apply orb_prop in T10 as [T10|T10].
    - apply Z.leb_le in T10. lia.
    - pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN T10) as L10. cbn [xt_den] in L10.
      fold spw dataw nw in L10. fold usp ud n in L10. lia. }
  assert (PD2 : fs + 11571200 + 4096 <= usp - fr \/ usp + 4112 <= fs).
  { left. unfold Tst in T11. apply orb_prop in T11 as [T11|T11].
    - apply Z.leb_le in T11. lia.
    - pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN T11) as L11. cbn [xt_den] in L11.
      change (edenot E (ELit 11571200)) with (Z_to_bv 64 11571200) in L11. rewrite u64_lit in L11 by lia.
      fold spw fsw in L11. fold usp fs in L11. lia. }
  (* [comment removed for export] *)
  destruct (rw_lit_sound E M (kn cs) spb (spk - fr) (fr + 16) HKN ltac:(lia) T16) as (W1st & W1st1 & W1rd & W1lo & W1hi).   (* [comment removed for export] *)
  assert (Husp_eq : usp = estart E (SA spb spk)).
  { pose proof (w_split_lit_denot E sp spb spk Hssp) as D. fold spw in D. apply (f_equal bv_unsigned) in D. fold usp in D.
    unfold estart in W1lo, W1hi |- *. cbn [a_base a_off] in W1lo, W1hi |- *.
    rewrite u_lit64 in D. unfold two64 in D.
    destruct (Z.eq_dec (bv_unsigned (edenot E spb) + spk) (2 ^ 64)) as [EQ|NE].
    - exfalso. rewrite EQ in D. rewrite Z.mod_same in D by lia. lia.
    - rewrite Z.mod_small in D by lia. exact D. }
  destruct (rw_lit_sound E M (kn cs) fsb fsk FS_HINTS HKN ltac:(unfold FS_HINTS; lia) T20) as (W3st & W3st1 & W3rd & W3lo & W3hi).
  unfold FS_HINTS in W3st, W3st1, W3rd, W3hi.
  assert (Hfs_eq : fs = estart E (SA fsb fsk)).
  { unfold fs, fsw. apply (u_of_split E efs fsb fsk Hsfs). lia. }
  assert (Hud_eq : nhi <> 0 -> ud = estart E (SA db dk) /\ FN.rw_x (kn cs) db dk ne = true).
  { intros Hnz. destruct (Z.eqb_spec nhi 0); [lia|]. cbn [orb] in T13.
    destruct (rw_x_sound E M (kn cs) db dk ne HKN T13) as (_ & _ & Dlo & Dhi & Dpos).
    split; [|exact T13]. unfold ud, dataw. apply (u_of_split E data db dk Hsd). lia. }
  assert (PD3 : fs + 11571200 + 4096 <= ud \/ ud + n <= fs).
  { apply Bool.orb_prop in T12. destruct T12 as [T12|T12].
    - apply Bool.orb_prop in T12. destruct T12 as [T12|T12]; apply Z.leb_le in T12; lia.
    - apply andb_prop in T12 as [T12 Hap]. apply andb_prop in T12 as [T12a T12b].
      apply Z.leb_le in T12a. apply Bool.negb_true_iff in T12b. apply Z.eqb_neq in T12b.
      destruct (Hud_eq T12b) as [Hud _].
      pose proof (ranges_apart_x_sound SEGS E M (kn cs) db (dk - 4096) (eaddz ne 4096) fsb fsk (ELit 11571200) HKN Hap) as X.
      assert (L1 : elenZ E (eaddz ne 4096) = n + 4096).
      { unfold elenZ, eaddz. rewrite mkAlu_denot. cbn [edenot]. fold nw. rewrite (u_add_small nw 4096) by lia. reflexivity. }
      assert (L2 : elenZ E (ELit 11571200) = 11571200) by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
      rewrite L1, L2 in X. rewrite Hfs_eq, Hud. unfold estart in X |- *. cbn [a_base a_off] in X |- *. lia. }
  assert (Hsh : shadow_off A = fa_shoff P) by exact T1a.
  pose proof SHADOW_ok as SO. unfold shadow_ok in SO.
  assert (Hud8 : 0 <= ud / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Husp8 : 0 <= (usp - fr) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hfs8 : 0 <= (fs + FS_FRAMES) / 8 < 2 ^ 61) by (unfold FS_FRAMES; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hn8 : 0 <= n / 8 <= n /\ n / 8 < 2 ^ 61) by (repeat split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hfr8 : 0 < fr / 8 /\ 8 * (fr / 8) = fr).
  { clear - T1b T1c. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  hideT.
  (* [comment removed for export] *)
  assert (P_rd : readable SEGS M ud n).
  { unfold readable. intros i Hi. destruct (Z.eq_dec nhi 0) as [Z0|NZ]; [lia|].
    destruct (Hud_eq NZ) as [Hud T13']. destruct (rw_x_sound E M (kn cs) db dk ne HKN T13') as (_ & RD & _ & _ & _).
    unfold elenZ in RD. fold nw n in RD. rewrite Hud. apply RD. lia. }
  (* [comment removed for export] *)
  assert (Eud : bv_unsigned (edenot E data) = ud) by reflexivity.
  assert (P_dsh : 0 < n -> forall g, 0 <= 8 * g < n ->
            rdn SEGS M (Z_to_bv 64 (shadow P ud + g)) 1 = Some [Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)]).
  { intros Hn0 g Hg. unfold shadow. destruct (Z.eqb_spec nhi 0) as [Z0|NZ]; [lia|]. cbn [orb] in T14.
    apply andb_prop in T14 as [Tz Tp].
    destruct (Z.leb_spec (8 * g + 8) n) as [FULLG|PART].
    - (* [comment removed for export] *)
      destruct (Z.ltb_spec nhi 8) as [S8|L8]; [clear - S8 Hg FULLG Bnhi; lia|]. cbn [orb] in Tz.
      destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) shdb shdk (mkSrl (kn cs) ne 3) HKN HKN Tz) as (Zb & Zlo & Zhi).
      assert (Ln : elenZ E (mkSrl (kn cs) ne 3) = n / 8) by (unfold elenZ; rewrite (u_srl3 E M (kn cs) ne HKN); reflexivity).
      rewrite Ln in Zb, Zhi.
      assert (Hg8 : 0 <= g < n / 8).
      { split; [lia|]. pose proof (Z.div_le_lower_bound n 8 (g + 1) ltac:(lia) ltac:(lia)). lia. }
      symmetry in Hshd.
      pose proof (estart_of_split E _ shdb shdk (n / 8) Hshd Zlo Zhi ltac:(lia)) as Esh.
      rewrite (u_shadow_expr E M (kn cs) data HKN ltac:(rewrite Eud; clear - Hud8 SO; lia)) in Esh. rewrite Eud, Hsh in Esh.
      replace (fa_shoff P + ud / 8 + g) with (estart E (SA shdb shdk) + g) by lia. apply rdn1_overlay. apply Zb. exact Hg8.
    - (* [comment removed for export] *)
      assert (Hgq : g = n / 8).
      { pose proof (Z.div_le_lower_bound n 8 g ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound n 8 (g + 1) ltac:(lia) ltac:(lia)). lia. }
      unfold FN.partial_ok in Tp. rewrite ?Hcdata, ?Hcne, ?Hsh in Tp. apply Bool.orb_prop in Tp. destruct Tp as [Tal|Tp].
      { exfalso. apply Z.leb_le in Tal. destruct (ealign_sound SEGS E M (kn cs) ne HKN) as [_ ALn]. fold nw n in ALn.
        pose proof (mod_of_align _ 3 _ ALn ltac:(lia)) as M8. change (2 ^ 3) with 8 in M8.
        rewrite (Z.mod_eq n 8) in M8 by lia. lia. }
      destruct (split_lit (eadd (eadd (mkSrl (kn cs) data 3) (ELit (fa_shoff P))) (mkSrl (kn cs) ne 3))) as [pb pk] eqn:Hsp.
      apply andb_prop in Tp as [Pfl Tp].
      destruct (know_lookup SEGS (kn cs) pb pk 1 false [] []) as [e sc hs|sc hs|] eqn:HL; try discriminate.
      destruct sc; [|discriminate].
      destruct (flat_x_sound SEGS E M (kn cs) pb pk (ELit 1) HKN Pfl) as (Plo & Phi & _).
      cbn [edenot] in Phi. rewrite u64_lit in Phi by lia.
      destruct (lookup_piece SEGS E M (kn cs) pb pk 1 e hs HKN ltac:(lia) HL ltac:(unfold flat; lia)) as (bs & Hrd & Hlen & Hbs).
      pose proof (estart_of_split E _ pb pk 1 Hsp Plo Phi ltac:(lia)) as Epb.
      unfold eadd at 1 in Epb. rewrite mkAlu_denot in Epb.
      pose proof (u_shadow_expr E M (kn cs) data HKN ltac:(rewrite Eud; clear - Hud8 SO; lia)) as UX. rewrite Eud, Hsh in UX.
      pose proof (u_srl3 E M (kn cs) ne HKN) as UY. fold nw n in UY.
      rewrite (u_add_nowrap _ _ ltac:(rewrite UX, UY; clear - Hud8 Hn8 SO Hsh; lia)) in Epb. rewrite UX, UY in Epb.
      replace (fa_shoff P + ud / 8 + g) with (estart E (SA pb pk)) by (clear - Epb Hgq; lia).
      rewrite Hrd, <- Hbs, w2b1. do 2 f_equal.
      (* [comment removed for export] *)
      pose proof (u64_range (edenot E e)) as Re.
      pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as M8.
      assert (He8 : bv_unsigned (edenot E e) = n mod 8).
      { unfold n, nw. apply (partial_val_ok_sound SEGS E M (kn cs)); [exact HKN | exact Tp |]. fold nw n.
        rewrite (Z.mod_eq n 8) by lia. clear - Hg Hgq PART M8. lia. }
      rewrite He8. f_equal. rewrite (Z.mod_eq n 8) by lia. lia. }
  assert (P_dm : 0 < n -> readable SEGS M (shadow P ud - 2) (n / 8 + 6)).
  { intros Hn0. unfold readable, shadow. intros i Hi. destruct (Z.eqb_spec nhi 0) as [Z0|NZ]; [lia|]. cbn [orb] in T15.
    destruct (rw_x_sound E M (kn cs) shdb (shdk - 2) _ HKN T15) as (_ & RD & Mlo & Mhi & Mpos).
    assert (Ln : elenZ E (eaddz (mkSrl (kn cs) ne 3) 6) = n / 8 + 6).
    { unfold elenZ, eaddz. rewrite mkAlu_denot. cbn [edenot].
      rewrite (u_add_small _ 6); rewrite ?(u_srl3 E M (kn cs) ne HKN); fold nw n; lia. }
    rewrite Ln in RD, Mhi.
    symmetry in Hshd.
    assert (Esh : estart E (SA shdb shdk) = fa_shoff P + ud / 8).
    { pose proof (estart_of_split E _ shdb shdk (n / 8 + 4) Hshd) as X.
      unfold estart in X, Mlo, Mhi |- *. cbn [a_base a_off] in X, Mlo, Mhi |- *.
      rewrite (u_shadow_expr E M (kn cs) data HKN ltac:(rewrite Eud; clear - Hud8 SO; lia)) in X. rewrite Eud, Hsh in X. clear - X Mlo Mhi Hn8 SO Hsh Hud8. lia. }
    unfold estart in Esh, RD. cbn [a_base a_off] in Esh, RD.
    replace (fa_shoff P + ud / 8 - 2 + i) with (bv_unsigned (edenot E shdb) + (shdk - 2) + i) by (clear - Esh; lia).
    apply RD. lia. }
  assert (P_dm2 : 0 < n -> readable SEGS M (rd8 (shadow P ud)) (rd8 (shadow P (ud + n - 1)) + 8 - rd8 (shadow P ud))).
  { intros Hn0. unfold readable, rd8, shadow. intros i Hi. destruct (Z.eqb_spec nhi 0) as [Z0|NZ]; [lia|]. cbn [orb] in T33.
    apply Bool.orb_prop in T33 as [T33|T33].
    2:{ (* [comment removed for export] *)
    destruct (FN.shd_split (kn cs) shdb) as [[Bb tb]|] eqn:Hsp; [|discriminate].
    destruct (xhi (kn cs) tb) as [th|] eqn:Hth; [|discriminate].
    apply andb_prop in T33 as [Tth T33]. apply Z.ltb_lt in Tth. unfold two64 in Tth.
    unfold FN.shd_split in Hsp.
    destruct (lsplit_divc 8 (snd (lin_of shdb))) as [dts rts] eqn:Hls.
    match type of Hsp with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection Hsp as <- <-.
    apply andb_prop in Hc as [Hc Hn3]. apply andb_prop in Hc as [Hc Hn2]. apply andb_prop in Hc as [Hal Hn1]. apply Z.leb_le in Hal.
    set (cc := fst (lin_of shdb)) in *.
    pose proof (lin_nowrap_sound SEGS E M (kn cs) shdb HKN Hn1) as Hval. fold cc in Hval.
    destruct (lsplit_divc_sound E _ _ _ _ Hls) as [_ Hsum]. rewrite Hsum in Hval.
    pose proof (unlin_nowrap_val E M (kn cs) (cc - cc mod 8) dts HKN Hn2) as HuB.
    pose proof (unlin_nowrap_val E M (kn cs) (cc mod 8) rts HKN Hn3) as Hut.
    set (Bx := unlin (cc - cc mod 8, dts)) in *. set (tx := unlin (cc mod 8, rts)) in *.
    destruct (ealign_sound SEGS E M (kn cs) Bx HKN) as [_ ALb].
    pose proof (mod_of_align _ 3 _ ALb ltac:(clear - Hal; lia)) as B8. change (2 ^ 3) with 8 in B8.
    pose proof (xhi_sound SEGS E M (kn cs) tx th HKN Hth) as Tx.
    pose proof (u64_range (edenot E tx)) as Rt. pose proof (u64_range (edenot E Bx)) as RB. pose proof (u64_range (edenot E shdb)) as Rs.
    set (uB := bv_unsigned (edenot E Bx)) in *. set (ut := bv_unsigned (edenot E tx)) in *.
    assert (Hsplit : bv_unsigned (edenot E shdb) = uB + ut) by (clear - Hval HuB Hut; lia).
    pose proof (u_srl3 E M (kn cs) ne HKN) as UY. fold nw n in UY.
    assert (Ln : elenZ E (eaddz (eadd tx (mkSrl (kn cs) ne 3)) (9 + shdk mod 8)) = ut + n / 8 + (9 + shdk mod 8)).
    { pose proof (Z.mod_pos_bound shdk 8 ltac:(reflexivity)) as Mk.
      assert (Hn8' : n / 8 <= nhi / 8) by (apply Z.div_le_mono; [reflexivity | clear - Bnhi; lia]).
      assert (NW : bv_unsigned (edenot E tx) + bv_unsigned (edenot E (mkSrl (kn cs) ne 3)) < 2 ^ 64).
      { rewrite UY. fold ut. clear - Tx Tth Hn8' Rn Mk. lia. }
      unfold elenZ, eaddz, eadd. rewrite !mkAlu_denot. cbn [edenot].
      rewrite (u_add_small _ (9 + shdk mod 8)).
      - rewrite (u_add_nowrap _ _ NW). rewrite UY. fold ut. reflexivity.
      - clear - Mk; lia.
      - rewrite (u_add_nowrap _ _ NW). rewrite UY. fold ut. clear - Tx Tth Hn8' Rn Mk. lia. }
    destruct (rw_x_sound E M (kn cs) Bx (shdk - shdk mod 8) _ HKN T33) as (_ & RD & Mlo & Mhi & Mpos).
    rewrite Ln in RD, Mhi.
    symmetry in Hshd.
    assert (Esh : bv_unsigned (edenot E shdb) + shdk = fa_shoff P + ud / 8).
    { pose proof (estart_of_split E _ shdb shdk (n / 8 + 9) Hshd) as X.
      unfold estart in X, Mlo, Mhi |- *. cbn [a_base a_off] in X, Mlo, Mhi |- *.
      rewrite (u_shadow_expr E M (kn cs) data HKN ltac:(rewrite Eud; clear - Hud8 SO; lia)) in X. rewrite Eud, Hsh in X.
      pose proof (Z.mod_pos_bound shdk 8 ltac:(reflexivity)) as Mk. clear - X Mlo Mhi Hn8 SO Hsh Hud8 Mk Hsplit Tx Rt. lia. }
    unfold estart in RD. cbn [a_base a_off] in RD.
    assert (Hq : (ud + n - 1) / 8 <= ud / 8 + n / 8).
    { clear - Hn0 Rd Hud16. pose proof (Z.div_mod ud 16 ltac:(lia)) as Dm. set (q := ud / 16) in *.
      assert (Equd : ud = 2 * q * 8) by lia.
      assert (E8 : ud / 8 = 2 * q) by (rewrite Equd; apply Z.div_mul; lia).
      rewrite E8. replace (ud + n - 1) with (2 * q * 8 + (n - 1)) by lia. rewrite Z.div_add_l by lia.
      pose proof (Z.div_le_mono (n - 1) n 8 ltac:(lia) ltac:(lia)). lia. }
    pose proof (Z.mod_pos_bound (fa_shoff P + ud / 8) 8 ltac:(reflexivity)) as Mu.
    pose proof (Z.mod_pos_bound (fa_shoff P + (ud + n - 1) / 8) 8 ltac:(reflexivity)) as Mq.
    pose proof (Z.mod_pos_bound shdk 8 ltac:(reflexivity)) as Mk.
    pose proof (Z.mod_pos_bound (ut + shdk) 8 ltac:(reflexivity)) as Mts.
    (* [comment removed for export] *)
    assert (Hmod : (fa_shoff P + ud / 8) mod 8 = (ut + shdk) mod 8).
    { rewrite <- Esh, Hsplit. replace (uB + ut + shdk) with (ut + shdk + uB) by ring.
      rewrite Z.add_mod by discriminate. rewrite B8, Z.add_0_r. apply Z.mod_mod. discriminate. }
    assert (Hmono : shdk - shdk mod 8 <= ut + shdk - (ut + shdk) mod 8).
    { pose proof (Z.div_mod shdk 8 ltac:(discriminate)) as D1. pose proof (Z.div_mod (ut + shdk) 8 ltac:(discriminate)) as D2.
      assert (Hut0 : 0 <= ut) by (clear - Rt; lia).
      pose proof (Z.div_le_mono shdk (ut + shdk) 8 ltac:(reflexivity) ltac:(clear - Hut0; lia)) as D3. clear - D1 D2 D3. lia. }
    replace (fa_shoff P + ud / 8 - (fa_shoff P + ud / 8) mod 8 + i)
      with (uB + (shdk - shdk mod 8) + ((ut + shdk - (ut + shdk) mod 8) - (shdk - shdk mod 8) + i)) by (rewrite Hmod, <- Esh, Hsplit; ring).
    apply RD. clear - Hi Hq Mq Mu Mk Mts Hmod Hmono Esh Hsplit. lia. }
    apply Bool.orb_prop in T33 as [T33|T33].
    2:{ (* [comment removed for export] *)
    destruct (rw_x_sound E M (kn cs) shdb (shdk - 7) _ HKN T33) as (_ & RD & Mlo & Mhi & Mpos).
    assert (Ln : elenZ E (eaddz (mkSrl (kn cs) ne 3) 16) = n / 8 + 16).
    { unfold elenZ, eaddz. rewrite mkAlu_denot. cbn [edenot].
      rewrite (u_add_small _ 16); rewrite ?(u_srl3 E M (kn cs) ne HKN); fold nw n; clear - Hn8 Rn; lia. }
    rewrite Ln in RD, Mhi.
    symmetry in Hshd.
    assert (Esh : estart E (SA shdb shdk) = fa_shoff P + ud / 8).
    { pose proof (estart_of_split E _ shdb shdk (n / 8 + 9) Hshd) as X.
      unfold estart in X, Mlo, Mhi |- *. cbn [a_base a_off] in X, Mlo, Mhi |- *.
      rewrite (u_shadow_expr E M (kn cs) data HKN ltac:(rewrite Eud; clear - Hud8 SO; lia)) in X. rewrite Eud, Hsh in X. clear - X Mlo Mhi Hn8 SO Hsh Hud8. lia. }
    unfold estart in Esh, RD. cbn [a_base a_off] in Esh, RD.
    set (ub := bv_unsigned (edenot E shdb)) in *.
    assert (Hq : (ud + n - 1) / 8 <= ud / 8 + n / 8).
    { clear - Hn0 Rd Hud16. pose proof (Z.div_mod ud 16 ltac:(lia)) as Dm. set (q := ud / 16) in *.
      assert (Equd : ud = 2 * q * 8) by lia.
      assert (E8 : ud / 8 = 2 * q) by (rewrite Equd; apply Z.div_mul; lia).
      rewrite E8. replace (ud + n - 1) with (2 * q * 8 + (n - 1)) by lia. rewrite Z.div_add_l by lia.
      pose proof (Z.div_le_mono (n - 1) n 8 ltac:(lia) ltac:(lia)). lia. }
    pose proof (Z.mod_pos_bound (fa_shoff P + ud / 8) 8 ltac:(lia)) as Mu.
    pose proof (Z.mod_pos_bound (fa_shoff P + (ud + n - 1) / 8) 8 ltac:(lia)) as Mq.
    replace (fa_shoff P + ud / 8 - (fa_shoff P + ud / 8) mod 8 + i)
      with (ub + (shdk - 7) + (7 - (fa_shoff P + ud / 8) mod 8 + i)) by (clear - Esh; lia).
    apply RD. clear - Hi Hq Mq Mu. lia. }
    apply andb_prop in T33 as [Tal T33]. apply Z.leb_le in Tal.
    destruct (rw_x_sound E M (kn cs) shdb (shdk - shdk mod 8) _ HKN T33) as (_ & RD & Mlo & Mhi & Mpos).
    pose proof (Z.mod_pos_bound shdk 8 ltac:(lia)) as Mk.
    assert (Ln : elenZ E (eaddz (mkSrl (kn cs) ne 3) (9 + shdk mod 8)) = n / 8 + (9 + shdk mod 8)).
    { unfold elenZ, eaddz. rewrite mkAlu_denot. cbn [edenot].
      rewrite (u_add_small _ (9 + shdk mod 8)); rewrite ?(u_srl3 E M (kn cs) ne HKN); fold nw n; clear - Mk Hn8 Rn; lia. }
    rewrite Ln in RD, Mhi.
    symmetry in Hshd.
    assert (Esh : estart E (SA shdb shdk) = fa_shoff P + ud / 8).
    { pose proof (estart_of_split E _ shdb shdk (n / 8 + 9) Hshd) as X.
      unfold estart in X, Mlo, Mhi |- *. cbn [a_base a_off] in X, Mlo, Mhi |- *.
      rewrite (u_shadow_expr E M (kn cs) data HKN ltac:(rewrite Eud; clear - Hud8 SO; lia)) in X. rewrite Eud, Hsh in X. clear - X Mlo Mhi Hn8 SO Hsh Hud8 Mk. lia. }
    (* [comment removed for export] *)
    destruct (ealign_sound SEGS E M (kn cs) shdb HKN) as [_ ALb].
    pose proof (mod_of_align _ 3 _ ALb ltac:(lia)) as B8. change (2 ^ 3) with 8 in B8.
    unfold estart in Esh, RD. cbn [a_base a_off] in Esh, RD.
    set (ub := bv_unsigned (edenot E shdb)) in *.
    assert (Hm : (fa_shoff P + ud / 8) mod 8 = shdk mod 8).
    { rewrite <- Esh. rewrite Z.add_mod by lia. fold ub in B8 |- *. rewrite B8, Z.add_0_l. apply Z.mod_mod. lia. }
    assert (Hq : (ud + n - 1) / 8 <= ud / 8 + n / 8).
    { clear - Hn0 Rd Hud16. pose proof (Z.div_mod ud 16 ltac:(lia)) as Dm. set (q := ud / 16) in *.
      assert (Equd : ud = 2 * q * 8) by lia.
      assert (E8 : ud / 8 = 2 * q) by (rewrite Equd; apply Z.div_mul; lia).
      rewrite E8. replace (ud + n - 1) with (2 * q * 8 + (n - 1)) by lia. rewrite Z.div_add_l by lia.
      pose proof (Z.div_le_mono (n - 1) n 8 ltac:(lia) ltac:(lia)). lia. }
    pose proof (Z.mod_pos_bound (fa_shoff P + (ud + n - 1) / 8) 8 ltac:(lia)) as Mq.
    replace (fa_shoff P + ud / 8 - (fa_shoff P + ud / 8) mod 8 + i) with (ub + (shdk - shdk mod 8) + i) by (clear - Esh Hm; lia).
    apply RD. clear - Hi Hm Hq Mq Mk. lia. }
  hideT.
  (* [comment removed for export] *)
  assert (Esp : estart E (SA spb (spk - fr)) = usp - fr) by (clear - Husp_eq; unfold estart in Husp_eq |- *; cbn [a_base a_off] in Husp_eq |- *; lia).
  rewrite Esp in W1st, W1st1, W1rd.
  assert (P_fw : writable SEGS M (usp - fr) (fr + 16)) by (unfold writable; exact W1st1).   (* [comment removed for export] *)
  assert (P_fr16 : readable SEGS M usp 16).
  { unfold readable. intros i Hi. replace (usp + i) with (usp - fr + (fr + i)) by ring. apply W1rd. clear - Hi Hfr8. lia. }
  apply andb_prop in T17 as [T17 T17w]. apply andb_prop in T17 as [T17z T17f].
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) shfb shfk shfn HKN HKN T17z) as (F2z & F2lo & F2hi).
  destruct (flat_x_sound SEGS E M (kn cs) shfb shfk shfn HKN T17f) as (_ & _ & F2pos). fold (elenZ E shfn) in F2pos.
  symmetry in Hshf.
  assert (Uspm : bv_unsigned (edenot E (eaddz sp (- fr))) = usp - fr).
  { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. fold spw. apply u_sub_lit. fold usp. lia. }
  destruct (shadow_of_den E M (kn cs) (eaddz sp (- fr)) (ELit fr) shfb shfk shfn (elenZ E shfn) HKN Hshf F2lo F2hi F2pos
              ltac:(rewrite Uspm; lia)) as [Eshf Lshf].
  rewrite Uspm, Hsh in Eshf. cbn [edenot] in Lshf. rewrite (u64_lit fr) in Lshf by lia.
  rewrite Lshf in F2z, F2hi, F2pos.
  assert (P_fz : zeroes SEGS M (shadow P (usp - fr)) (fr / 8)).
  { unfold zeroes, shadow. intros i Hi. replace (fa_shoff P + (usp - fr) / 8 + i) with (estart E (SA shfb shfk) + i) by lia.
    apply rdn1_overlay. apply F2z. exact Hi. }
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) shfb shfk (ELit (fr / 8 + 2)) HKN HKN T17w) as (F2st & F2wlo & F2whi).
  assert (EL2 : elenZ E (ELit (fr / 8 + 2)) = fr / 8 + 2) by (unfold elenZ; cbn [edenot]; apply u64_lit; clear - Hfr8 W1lo W1hi; lia).
  rewrite EL2 in F2st, F2whi.
  assert (P_fsw : writable SEGS M (shadow P (usp - fr)) (fr / 8 + 2)).   (* [comment removed for export] *)
  { unfold writable, shadow. intros i Hi. rewrite <- Eshf.
    generalize (F2st (Z.to_nat (fr / 8 + 2)) ltac:(clear - Hfr8; lia)). clear - F2lo F2hi F2wlo F2whi Hi Hfr8. intros ST.
    apply store_ok_of_all; [rewrite u64_lit by lia; cbn; lia|]. intros x Hx. rewrite u64_lit in Hx by lia. cbn in Hx.
    apply (store_ok_all SEGS M (Z.to_nat (fr / 8 + 2)) (Z_to_bv 64 (estart E (SA shfb shfk))) ltac:(rewrite u64_lit by lia; lia) ST).
    rewrite u64_lit by lia. lia. }
  destruct (rw_lit_sound E M (kn cs) shfb (shfk - 8) 8 HKN ltac:(lia) T18) as (_ & _ & F3rd & _ & _).
  destruct (rw_lit_sound E M (kn cs) shfb (shfk + fr / 8) 10 HKN ltac:(lia) T19) as (_ & _ & F4rd & _ & _).   (* [comment removed for export] *)
  assert (P_fm1 : readable SEGS M (shadow P (usp - fr) - 8) 8).
  { unfold readable, shadow. intros i Hi. unfold estart in Eshf, F3rd. cbn [a_base a_off] in Eshf, F3rd.
    replace (fa_shoff P + (usp - fr) / 8 - 8 + i) with (bv_unsigned (edenot E shfb) + (shfk - 8) + i) by lia. apply F3rd. lia. }
  assert (Hq8 : (usp - fr) / 8 + fr / 8 = usp / 8).
  { clear - T1b T1c Husp16 Psp. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (P_fm2 : readable SEGS M (shadow P usp) 10).
  { unfold readable, shadow. intros i Hi. unfold estart in Eshf, F4rd. cbn [a_base a_off] in Eshf, F4rd.
    replace (fa_shoff P + usp / 8 + i) with (bv_unsigned (edenot E shfb) + (shfk + fr / 8) + i) by lia. apply F4rd. lia. }
  hideT.
  (* [comment removed for export] *)
  assert (Efs : forall o, estart E (SA fsb (fsk + o)) = fs + o) by (intros o; rewrite Hfs_eq; unfold estart; cbn [a_base a_off]; lia).
  assert (P_s1 : readable SEGS M fs FS_HINTS).
  { unfold readable, FS_HINTS. intros i Hi. rewrite Hfs_eq. apply W3rd. exact Hi. }
  assert (P_s2 : writable SEGS M fs FS_HINTS).
  { unfold writable, FS_HINTS. intros i Hi. rewrite Hfs_eq. apply W3st1. exact Hi. }
  destruct (cell_is_sound E M (kn cs) fsb (fsk + FS_SSL) 8 20 HKN ltac:(lia) T21) as (S3rd & _ & _). rewrite Efs in S3rd.
  assert (P_s3 : cell SEGS M (fs + FS_SSL) 8 20) by exact S3rd.
  destruct (cell_is_sound E M (kn cs) fsb (fsk + FS_NEEDSGC) 1 0 HKN ltac:(lia) T22) as (S4rd & _ & _). rewrite Efs in S4rd.
  assert (P_s4 : cell SEGS M (fs + FS_NEEDSGC) 1 0) by exact S4rd.
  apply andb_prop in T23 as [T23z T23w].
  destruct (zero_lit_sound E M (kn cs) fsb (fsk + FS_FLAGS) FS_FLAGS_LEN HKN ltac:(unfold FS_FLAGS_LEN; lia) T23z) as (S5z & S5rd & _ & _).
  rewrite Efs in S5z, S5rd.
  assert (P_s5 : zeroes SEGS M (fs + FS_FLAGS) FS_FLAGS_LEN) by (unfold zeroes; exact S5rd).
  destruct (rw_lit_sound E M (kn cs) fsb (fsk + FS_FLAGS) FS_FLAGS_LEN HKN ltac:(unfold FS_FLAGS_LEN; lia) T23w) as (_ & S6st & _ & _ & _).
  rewrite Efs in S6st.
  assert (P_s6 : writable SEGS M (fs + FS_FLAGS) FS_FLAGS_LEN) by (unfold writable; exact S6st).
  destruct (rw_lit_sound E M (kn cs) fsb (fsk + FS_FRAMES) FS_FRAMES_LEN HKN ltac:(unfold FS_FRAMES_LEN; lia) T24) as (_ & S7st & S7rd & _ & _).
  rewrite Efs in S7st, S7rd.
  assert (P_s7 : readable SEGS M (fs + FS_FRAMES) FS_FRAMES_LEN) by (unfold readable; exact S7rd).
  assert (P_s8 : writable SEGS M (fs + FS_FRAMES) FS_FRAMES_LEN) by (unfold writable; exact S7st).
  destruct (rw_lit_sound E M (kn cs) shsb (shsk - 8) (FS_FRAMES_LEN / 8 + 16) HKN ltac:(unfold FS_FRAMES_LEN; cbn; lia) T25) as (_ & S9st & S9rd & S9lo & S9hi).
  symmetry in Hshs.
  assert (Ufsm : bv_unsigned (edenot E (eaddz efs FS_FRAMES)) = fs + FS_FRAMES).
  { unfold eaddz, FS_FRAMES. rewrite mkAlu_denot. cbn [edenot]. fold fsw. rewrite (u_add_small fsw 36864); fold fs; lia. }
  destruct (shadow_of_den E M (kn cs) (eaddz efs FS_FRAMES) (ELit FS_FRAMES_LEN) shsb shsk shsn (FS_FRAMES_LEN / 8 + 8) HKN Hshs) as [Eshs Lshs].
  { clear - S9lo. unfold estart in *. cbn [a_base a_off] in *. lia. }
  { clear - S9hi. unfold estart, FS_FRAMES_LEN in *. cbn [a_base a_off] in *. cbn. lia. }
  { unfold FS_FRAMES_LEN. cbn. lia. }
  { rewrite Ufsm. clear - Hfs8 SO. lia. }
  rewrite Ufsm, Hsh in Eshs. cbn [edenot] in Lshs. rewrite u64_lit in Lshs by (unfold FS_FRAMES_LEN; cbn; lia).
  assert (P_s9 : readable SEGS M (shadow P (fs + FS_FRAMES) - 8) (FS_FRAMES_LEN / 8 + 16)).
  { unfold readable, shadow. intros i Hi. unfold estart in Eshs, S9rd. cbn [a_base a_off] in Eshs, S9rd.
    replace (fa_shoff P + (fs + FS_FRAMES) / 8 - 8 + i) with (bv_unsigned (edenot E shsb) + (shsk - 8) + i) by (clear - Eshs; lia).
    apply S9rd. exact Hi. }
  assert (P_s10 : writable SEGS M (shadow P (fs + FS_FRAMES)) (FS_FRAMES_LEN / 8)).
  { unfold writable, shadow. intros i Hi. unfold estart in Eshs, S9st. cbn [a_base a_off] in Eshs, S9st.
    replace (fa_shoff P + (fs + FS_FRAMES) / 8 + i) with (bv_unsigned (edenot E shsb) + (shsk - 8) + (i + 8)) by (clear - Eshs; lia).
    apply S9st. clear - Hi. unfold FS_FRAMES_LEN in *. cbn in *. lia. }
  hideT.
  (* [comment removed for export] *)
  destruct (cell_expr_sound E M (kn cs) (ELit 0) (fa_tp P) efs HKN Hefs) as (T1rd & _ & _). rewrite estart_lit0 in T1rd.
  assert (P_t1 : cell SEGS M (fa_tp P) 8 fs).
  { unfold cell. refine (eq_trans T1rd _). do 2 f_equal. fold fsw. unfold fs. symmetry. apply Z_to_bv_bv_unsigned. }
  destruct (cell_expr_sound E M (kn cs) (ELit 0) (fa_tp P + 0x8) edb HKN Hedb) as (T2rd & _ & _). rewrite estart_lit0 in T2rd.
  assert (P_t2 : cell SEGS M (fa_tp P + 0x8) 8 dbv).
  { unfold cell. refine (eq_trans T2rd _). do 2 f_equal. unfold dbv.
    rewrite (w_split_lit_denot E edb dbb dbk Hsdb). reflexivity. }
  destruct (cell_is_sound E M (kn cs) dbb (dbk + 0x18) 8 (fa_tp P) HKN ltac:(lia) T26) as (T3rd & _ & _).
  assert (P_t3 : cell SEGS M (dbv + 0x18) 8 (fa_tp P)).
  { unfold cell. unfold dbv. unfold estart in T3rd |- *. cbn [a_base a_off] in T3rd |- *.
    replace (bv_unsigned (edenot E dbb) + dbk + 24) with (bv_unsigned (edenot E dbb) + (dbk + 24)) by lia. exact T3rd. }
  destruct (cell_expr_sound E M (kn cs) (ELit 0) (fa_tsd P) ectx HKN Hectx) as (T4rd & _ & _). rewrite estart_lit0 in T4rd.
  assert (P_t4 : cell SEGS M (fa_tsd P) 8 ctx).
  { unfold cell. refine (eq_trans T4rd _). do 2 f_equal. unfold ctx.
    rewrite (w_split_lit_denot E ectx cxb cxk Hscx). reflexivity. }
  destruct (cell_expr_sound E M (kn cs) cxb (cxk + 0x98) ethr HKN Hethr) as (T5rd & _ & _).
  assert (P_t5 : cell SEGS M (ctx + 0x98) 8 thr).
  { unfold cell. unfold ctx, thr. unfold estart in T5rd |- *. cbn [a_base a_off] in T5rd |- *.
    replace (bv_unsigned (edenot E cxb) + cxk + 152) with (bv_unsigned (edenot E cxb) + (cxk + 152)) by lia. refine (eq_trans T5rd _).
    do 2 f_equal. rewrite (w_split_lit_denot E ethr thb thk Hsth). reflexivity. }
  destruct (rw_lit_sound E M (kn cs) thb (thk + 0x30) 16 HKN ltac:(lia) T27) as (_ & _ & T6rd & _ & _).
  assert (P_t6 : readable SEGS M (thr + 0x30) 16).
  { unfold readable. intros i Hi. unfold thr. unfold estart in T6rd |- *. cbn [a_base a_off] in T6rd |- *.
    replace (bv_unsigned (edenot E thb) + thk + 48 + i) with (bv_unsigned (edenot E thb) + (thk + 48) + i) by lia. apply T6rd. exact Hi. }
  (* [comment removed for export] *)
  unfold FN.chain_ok in T34. fold edb ectx ethr dbb dbk cxb cxk thb thk in T34.
  apply andb_prop in T34 as [T34 T34x]. apply andb_prop in T34 as [T34 T34c]. apply andb_prop in T34 as [T34a T34b].
  destruct (flat_x_sound SEGS E M (kn cs) dbb dbk (ELit 32) HKN T34a) as (Fdb1 & Fdb2 & _).
  destruct (flat_x_sound SEGS E M (kn cs) cxb cxk (ELit 160) HKN T34b) as (Fcx1 & Fcx2 & _).
  destruct (flat_x_sound SEGS E M (kn cs) thb thk (ELit 64) HKN T34c) as (Fth1 & Fth2 & _).
  cbn [edenot] in Fdb2, Fcx2, Fth2. rewrite u64_lit in Fdb2 by lia. rewrite u64_lit in Fcx2 by lia. rewrite u64_lit in Fth2 by lia.
  fold dbv in Fdb1, Fdb2. fold ctx in Fcx1, Fcx2. fold thr in Fth1, Fth2.
  destruct (xlo (kn cs) edb) as [dblo|] eqn:Xdb; [|cbn in T34x; discriminate].
  destruct (xlo (kn cs) ectx) as [cxlo|] eqn:Xcx; [|cbn in T34x; discriminate].
  destruct (xlo (kn cs) ethr) as [thlo|] eqn:Xth; [|cbn in T34x; discriminate].
  apply andb_prop in T34x as [T34x T34h]. apply andb_prop in T34x as [T34f T34g].
  apply Z.leb_le in T34f. apply Z.leb_le in T34g. apply Z.leb_le in T34h.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Xdb) as Bdb. pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Xcx) as Bcx.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Xth) as Bth.
  rewrite (w_split_lit_denot E edb dbb dbk Hsdb) in Bdb. rewrite (w_split_lit_denot E ectx cxb cxk Hscx) in Bcx.
  rewrite (w_split_lit_denot E ethr thb thk Hsth) in Bth.
  change (bv_unsigned (edenot E dbb) + dbk) with dbv in Bdb. change (bv_unsigned (edenot E cxb) + cxk) with ctx in Bcx.
  change (bv_unsigned (edenot E thb) + thk) with thr in Bth.
  rewrite u64_lit in Bdb by (clear - Fdb1 Fdb2; lia). rewrite u64_lit in Bcx by (clear - Fcx1 Fcx2; lia).
  rewrite u64_lit in Bth by (clear - Fth1 Fth2; lia).
  assert (P_t7 : ctx <> 0) by (clear - Bcx T34g; lia).
  assert (P_t8 : thr <> 0) by (clear - Bth T34h; lia).
  assert (P_t9 : 0 < dbv) by (clear - Bdb T34f; lia).
  assert (P_t10 : dbv + 32 <= 2 ^ 64) by (clear - Fdb2; lia).
  assert (P_t11 : 0 <= ctx) by (clear - Fcx1; lia).
  assert (P_t12 : ctx + 160 <= 2 ^ 64) by (clear - Fcx2; lia).
  assert (P_t13 : 0 <= thr) by (clear - Fth1; lia).
  assert (P_t14 : thr + 64 <= 2 ^ 64) by (clear - Fth2; lia).
  hideT.
  (* [comment removed for export] *)
  apply andb_prop in T28 as [T28 T28c]. apply andb_prop in T28 as [T28a T28b].
  assert (Lfr : elenZ E (ELit fr) = fr) by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (L88 : elenZ E (ELit FS_HINTS) = FS_HINTS) by (unfold elenZ, FS_HINTS; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (Lfl : elenZ E (ELit FS_FLAGS_LEN) = FS_FLAGS_LEN) by (unfold elenZ, FS_FLAGS_LEN; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (Lfr2 : elenZ E (ELit FS_FRAMES_LEN) = FS_FRAMES_LEN) by (unfold elenZ, FS_FRAMES_LEN; cbn [edenot]; rewrite u64_lit by (cbn; lia); reflexivity).
  assert (L8 : elenZ E (ELit 8) = 8) by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (L4 : elenZ E (ELit 4) = 4) by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (L16 : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  apply andb_prop in T32 as [T32a T32b].
  destruct (rw_lit_sound E M (kn cs) (ELit 0) (fa_prng P) 8 HKN ltac:(lia) T32a) as (_ & W7st & W7rd & W7lo & W7hi). rewrite estart_lit0 in W7st, W7rd, W7lo, W7hi.
  destruct (rw_lit_sound E M (kn cs) (ELit 0) (fa_errno P) 4 HKN ltac:(lia) T32b) as (_ & W8st & W8rd & W8lo & W8hi). rewrite estart_lit0 in W8st, W8rd, W8lo, W8hi.
  assert (APW : forall b off w, FN.apart_all (kn cs) (FN.c_wall c) b off w = true -> 0 <= w < 2 ^ 64 ->
            apart_writes P usp fs (estart E (SA b off)) w).
  { intros b off w Hap Hw. pose proof (apart_all_sound E M (kn cs) _ b off w HKN Hap) as AP. rewrite Hwall in AP.
    cbn [fst snd] in AP.
    apply Forall_cons_iff in AP as [A1 AP]. apply Forall_cons_iff in AP as [A2 AP]. apply Forall_cons_iff in AP as [A3 AP].
    apply Forall_cons_iff in AP as [A4 AP]. apply Forall_cons_iff in AP as [A5 AP]. apply Forall_cons_iff in AP as [A6 AP].
    apply Forall_cons_iff in AP as [A7 AP]. apply Forall_cons_iff in AP as [A8 AP].
    apply Forall_cons_iff in AP as [A9 AP]. apply Forall_cons_iff in AP as [A10 _].   (* [comment removed for export] *)
    assert (Lw : elenZ E (ELit w) = w) by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    assert (L2 : elenZ E (ELit 2) = 2) by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    rewrite Lw, Lfr, Esp in A1. rewrite Lw, Lshf, Eshf in A2. rewrite Lw, L88, <- Hfs_eq in A3. rewrite Lw, Lfl, Efs in A4.
    rewrite Lw, Lfr2, Efs in A5. rewrite Lw, Lshs, Eshs in A6. rewrite Lw, L8, estart_lit0 in A7. rewrite Lw, L4, estart_lit0 in A8.
    rewrite Lw, L16, <- Husp_eq in A9.
    assert (E10 : estart E (SA shfb (shfk + fr / 8)) = fa_shoff P + usp / 8).
    { clear - Eshf Hq8. unfold estart in *. cbn [a_base a_off] in *. lia. }
    rewrite Lw, L2, E10 in A10.
    unfold apart_writes, FA_writes, shadow. fold fr.
    apply Forall_app. split.
    - apply Forall_cons; [clear - A1; cbn [fst snd]; lia|]. apply Forall_cons; [clear - A2; cbn [fst snd]; lia|].
      apply Forall_cons; [clear - A3; cbn [fst snd]; lia|]. apply Forall_cons; [clear - A4; cbn [fst snd]; lia|].
      apply Forall_cons; [clear - A5; cbn [fst snd]; lia|]. apply Forall_cons; [clear - A6; cbn [fst snd]; lia|].
      apply Forall_cons; [clear - A7; cbn [fst snd]; lia|]. apply Forall_cons; [clear - A8; cbn [fst snd]; lia|].
      apply Forall_nil.
    - apply Forall_cons; [clear - A9; cbn [fst snd]; lia|]. apply Forall_cons; [clear - A10; cbn [fst snd]; lia|].
      apply Forall_nil. }
  assert (P_a1 : apart_writes P usp fs (dbv + 0x18) 8).
  { replace (dbv + 0x18) with (estart E (SA dbb (dbk + 0x18))) by (unfold dbv, estart; cbn [a_base a_off]; lia). apply APW; [exact T28a | lia]. }
  assert (P_a2 : apart_writes P usp fs (ctx + 0x98) 8).
  { replace (ctx + 0x98) with (estart E (SA cxb (cxk + 0x98))) by (unfold ctx, estart; cbn [a_base a_off]; lia). apply APW; [exact T28b | lia]. }
  assert (P_a3 : apart_writes P usp fs (thr + 0x30) 16).
  { replace (thr + 0x30) with (estart E (SA thb (thk + 0x30))) by (unfold thr, estart; cbn [a_base a_off]; lia). apply APW; [exact T28c | lia]. }
  hideT.
  (* [comment removed for export] *)
  assert (P_c1 : Forall (fun c => cell SEGS M (fst (fst c)) (snd (fst c)) (snd c)) (fa_kcells P)).
  { apply Forall_forall. intros [[a w] v] Hin. cbn [fst snd].
    pose proof (proj1 (forallb_forall _ _) T29 _ Hin) as KC. unfold FN.kcell_ok in KC.
    apply andb_prop in KC as [KC KCc]. apply andb_prop in KC as [KC KCa]. apply andb_prop in KC as [KC1 KC2].
    apply Z.leb_le in KC1. apply Z.leb_le in KC2. apply Z.leb_le in KCa.
    destruct (cell_is_sound E M (kn cs) (ELit 0) a (Z.to_nat w) v HKN ltac:(lia) KCc) as (Crd & _ & _).
    rewrite estart_lit0 in Crd. unfold cell. exact Crd. }
  assert (P_c2 : Forall (fun r => filled SEGS M (fst (fst r)) (snd (fst r)) (snd r)) (fa_gsh P)).
  { apply Forall_forall. intros [[a cnt] v] Hin. cbn [fst snd].
    pose proof (proj1 (forallb_forall _ _) T30 _ Hin) as G. unfold FN.gsh_ok in G.
    apply andb_prop in G as [G Gall]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
    apply Z.ltb_lt in G1. apply Z.leb_le in G2. apply Z.ltb_lt in G3. unfold two64 in G3.
    unfold filled. intros i Hi.
    assert (Hin2 : In (Z.to_nat i) (seq 0 (Z.to_nat cnt))) by (apply in_seq; lia).
    pose proof (proj1 (forallb_forall _ _) Gall _ Hin2) as Gi. cbn beta in Gi.
    destruct (cell_is_sound E M (kn cs) (ELit 0) (a + Z.of_nat (Z.to_nat i)) 1 v HKN ltac:(lia) Gi) as (Crd & _ & _).
    rewrite estart_lit0 in Crd. rewrite Z2Nat.id in Crd by lia. refine (eq_trans Crd _).
    rewrite w2b1. rewrite u_lit64. unfold two64. rewrite zbv8_mod64. reflexivity. }
  assert (P_c3 : Forall (fun r => pristine M (fst r) (snd r)) (fa_pristine P)).
  { apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
    pose proof (proj1 (forallb_forall _ _) T31 _ Hin) as PR. unfold FN.pristine_ok in PR. cbn [fst snd] in PR.
    apply andb_prop in PR as [PR PRc]. apply andb_prop in PR as [PR1 PR2].
    unfold pristine. intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a).
    apply (img_cov_sound SEGS E M (kn cs) lo hi HKN PRc). exact Ha. }
  assert (P_w1 : readable SEGS M (fa_prng P) 8) by (unfold readable; exact W7rd).
  assert (P_w2 : writable SEGS M (fa_prng P) 8) by (unfold writable; exact W7st).
  assert (P_w3 : readable SEGS M (fa_errno P) 4) by (unfold readable; exact W8rd).
  assert (P_w4 : writable SEGS M (fa_errno P) 4) by (unfold writable; exact W8st).
  hideT.
  (* [comment removed for export] *)
  pose proof (FCA R M (seg_rom SEGS) spw dataw n fs ctx thr dbv) as F0.
  specialize (F0 P1 P2 P4 P10 P11 Pn Pd0 Pd63 Hud16 PdH Husp16 Psp Psp2 Hfs4096 Pfs1 Pfs2 Pimg PD1 PD2 PD3
                 P_rd P_dsh P_dm P_dm2 P_fw P_fr16 P_fz P_fsw P_fm1 P_fm2
                 P_s1 P_s2 P_s3 P_s4 P_s5 P_s6 P_s7 P_s8 P_s9 P_s10
                 P_t1 P_t2 P_t3 P_t4 P_t5 P_t6 P_t7 P_t8 P_t9 P_t10 P_t11 P_t12 P_t13 P_t14
                 P_a1 P_a2 P_a3 P_c1 P_c2 P_c3 P_w1 P_w2 P_w3 P_w4).
  destruct F0 as (regs' & mem' & MS & EK & A0 & FM & Z1 & Z2).
  destruct FM as [Hout Hgrows]. fold usp in Z1, Z2, Hout. fold fr in Z1, Z2, Hout.
  (* [comment removed for export] *)
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs cs' E R FULL model TT (fa_ret P) (Some (ELit 0)) _ regs' mem' HC Hn).
  - rewrite Hpc. exact (msteps_of_port _ _ _ MS).
  - apply kept_of_ekeeps. exact EK.
  - cbn [edenot]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). exact A0.
  - (* [comment removed for export] *)
    apply (havocs_sound E (FN.c_ws c) M mem' (kn cs) HKN); [exact Hgrows|].
    intros x Hx. rewrite Hws in Hx. cbn [forallb inr fst snd negb andb] in Hx.
    set (ux := bv_unsigned x) in *. pose proof (u64_range x) as Rx. fold ux in Rx.
    assert (Xeq : x = Z_to_bv 64 ux) by (symmetry; apply Z_to_bv_bv_unsigned).
    (* [comment removed for export] *)
    assert (NIN : forall lo len, (negb ((lo <=? ux) && (ux <? lo + len)))%bool = true -> ~ (lo <= ux < lo + len)).
    { intros lo len Hb Hc. destruct (Z.leb_spec lo ux); destruct (Z.ltb_spec ux (lo + len)); cbn in Hb; try discriminate; lia. }
    rewrite Esp, Lfr, <- Hfs_eq, L88, Efs, Lfr2, Eshs, Lshs, !estart_lit0, L8, L4 in Hx.
    apply andb_prop in Hx as [N1 Hx]. apply andb_prop in Hx as [N2 Hx]. apply andb_prop in Hx as [N3 Hx].
    apply andb_prop in Hx as [N4 Hx]. apply andb_prop in Hx as [N5 Hx]. apply andb_prop in Hx as [N6 _].
    apply NIN in N1. apply NIN in N2. apply NIN in N3. apply NIN in N4. apply NIN in N5. apply NIN in N6.
    assert (C2 : (fa_shoff P + (usp - fr) / 8 <= ux < fa_shoff P + (usp - fr) / 8 + fr / 8)
                 \/ ~ (fa_shoff P + (usp - fr) / 8 <= ux < fa_shoff P + (usp - fr) / 8 + fr / 8)) by (clear; lia).
    destruct C2 as [[W2a W2b]|OUT2].
    { (* [comment removed for export] *)
      apply (zero_kept M mem' x); [| exact Hgrows |].
      - rewrite Xeq. replace ux with (estart E (SA shfb shfk) + (ux - estart E (SA shfb shfk))) by lia. apply F2z. clear - W2a W2b Eshf. lia.
      - rewrite Xeq. replace ux with (shadow P (usp - fr) + (ux - shadow P (usp - fr))) by lia.
        apply Z1. unfold shadow. clear - W2a W2b. lia. }
    assert (C4 : (fs + FS_FLAGS <= ux < fs + FS_FLAGS + FS_FLAGS_LEN) \/ ~ (fs + FS_FLAGS <= ux < fs + FS_FLAGS + FS_FLAGS_LEN)) by (clear; lia).
    destruct C4 as [[W4a W4b]|OUT4].
    { (* [comment removed for export] *)
      apply (zero_kept M mem' x); [| exact Hgrows |].
      - rewrite Xeq. replace ux with (fs + FS_FLAGS + (ux - (fs + FS_FLAGS))) by lia. apply S5z. clear - W4a W4b. lia.
      - rewrite Xeq. replace ux with (fs + FS_FLAGS + (ux - (fs + FS_FLAGS))) by lia. apply Z2. clear - W4a W4b. lia. }
    apply Hout. unfold FA_footprint, FA_writes, shadow. cbn [map fst snd OSSVerify.Proofs.coturn.FuzzStunClient.lib.Frame.outside].
    unfold OSSVerify.Proofs.coturn.FuzzStunClient.lib.Frame.in_rng. fold fr ux.
    rewrite !u64_lit by (clear - Psp Psp2 T1c T1d Husp8 SO Hsh Rfs Pfs2 Hfs8 W7lo W7hi W8lo W8hi Hfr8; unfold FS_FLAGS, FS_FRAMES, FS_FRAMES_LEN in *; lia).
    clear - N1 N2 N3 N4 N5 N6 OUT2 OUT4 Hfr8. unfold FS_HINTS, FS_FLAGS, FS_FLAGS_LEN, FS_FRAMES, FS_FRAMES_LEN in *. lia.
  - intros E' R' FULL' model' Hag HC' Hfs. exact (Hk E' R' FULL' model' Hag HC' Hfs).
Qed.


End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Table.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Hypothesis SEGS_wr : segs_wr_ok SEGS.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.
Variable P : FAParams.
Hypothesis FCA : F_contract_asan SEGS P.
Hypothesis SHADOW_ok : shadow_ok A.

#[using="SEGS_wx SEGS_in_hull HULL_ok SEGS_wr argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FCA SHADOW_ok"] Theorem fn_xn_sound : ext_stmt SEGS A nx0 LIMIT (FN.xn SEGS A nx0 P) SINV argH FS0.
Proof.
  intros id args. unfold FN.xn.
  do 102 (destruct id as [|id]; [intros cs cs' E R FULL model T _ _ H; discriminate H|]).
  destruct id as [|id]; [|intros cs cs' E R FULL model T _ _ H; discriminate H].
  destruct args as [|? ?]; [|intros cs cs' E R FULL model T _ _ H; discriminate H].
  exact (node_F_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SEGS_wr SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0 P FCA SHADOW_ok).
Qed.
End Table.

(* [comment removed for export] *)
