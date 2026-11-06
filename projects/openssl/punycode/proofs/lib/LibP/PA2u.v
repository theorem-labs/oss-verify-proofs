(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit HasZero StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibP Require Import PCode PImg PStrlen PStrchr PStrncmp PMemcpy PWpacket PWpMemcpy PWpPut PDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_a2u stops := wp_go 0x1e09b8 168%nat C_a2ulabel_eq C_a2ulabel stops.

(* [comment removed for export] *)
Lemma first_stop : forall (P : Z -> bool) (m : nat) k z, z - k = Z.of_nat m -> P z = true ->
  exists r, k <= r <= z /\ P r = true /\ forall j, k <= j < r -> P j = false.
Proof.
  intros P m. induction m as [|m IH]; intros k z Hm Hz.
  - exists z. split; [lia|]. split; [exact Hz | intros j Hj; lia].
  - destruct (P k) eqn:Ek.
    + exists k. split; [lia|]. split; [exact Ek | intros j Hj; lia].
    + destruct (IH (k + 1) z ltac:(lia) Hz) as (r & Hr & HPr & Hb).
      exists r. split; [lia|]. split; [exact HPr|].
      intros j Hj. destruct (Z.eq_dec j k) as [->|]; [exact Ek | apply Hb; lia].
Qed.

(* [comment removed for export] *)
Definition KSL : list nat :=
  [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Definition a2u_FP (S out : Z) (x : word) : Prop :=
  inr x (S - 2384) 168 \/ inr x (S - 2200) 16 \/ inr x (S - 2160) 2048 \/ inr x out 16.

(* [comment removed for export] *)
Definition XN (i : Z) : byte :=
  if Z.eqb i 0 then Z_to_bv 8 120 else if Z.eqb i 1 then Z_to_bv 8 110 else Z_to_bv 8 45.

Lemma xn_loads : forall M, img_ok M 0x1e151 0x1e156 ->
  forall i, 0 <= i < 4 -> load_ok PSEGS M (W (0x1e151 + i)) 1 (W (bv_unsigned (XN i))).
Proof.
  intros M Hi i Hr.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [->|[->|[->| ->]]] by lia;
    (eapply (load_img PSEGS M 0x1e151 0x1e156); [exact Hi | lia | lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity]).
Qed.

Lemma xn_nz : forall i, 0 <= i < 4 -> bv_unsigned (XN i) <> 0.
Proof.
  intros i Hr. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [->|[->|[->| ->]]] by lia; vm_compute; discriminate.
Qed.

Lemma xn_not_stop : forall i, 0 <= i < 4 -> bv_unsigned (XN i) <> 0 /\ bv_unsigned (XN i) <> 46.
Proof.
  intros i Hr. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [->|[->|[->| ->]]] by lia; split; vm_compute; discriminate.
Qed.

Section A2u.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (S b len N out sb : Z) (eb : word) (B : Z -> byte).
Hypothesis HB : bytes_at M b N B.
Hypothesis Hb : 0 < b /\ b + N < 2 ^ 63.
Hypothesis Hlen : 0 <= len < 2 ^ 31 /\ len < N.
Hypothesis HBlen : bv_unsigned (B len) = 0.
Hypothesis Hslack : (b + len) / 8 * 8 + 8 <= b + N.
Hypothesis HP0 : pkt_at M (S - 2216) out 0 16 sb eb.
Hypothesis Hsb : 0 < sb < 2 ^ 64.
Hypothesis Heb : (bv_unsigned eb mod 2 ^ 8) mod 2 = 0.
Hypothesis Hi1 : img_ok M 0x3a658 0x3a660.
Hypothesis Hi2 : img_ok M 0x3a690 0x3a698.
Hypothesis Hi3 : img_ok M 0x1e151 0x1e156.
Hypothesis HS : P_IMG_END <= S - 2384 /\ S < 2 ^ 63.
Hypothesis Hw1 : wr_ok PSEGS M (S - 2384) 168.
Hypothesis Hw2 : wr_ok PSEGS M (S - 2200) 16.
Hypothesis Hw3 : wr_ok PSEGS M (S - 2160) 2048.
Hypothesis Hout : P_IMG_END <= out /\ out + 16 < 2 ^ 63.
Hypothesis Hwo : wr_ok PSEGS M out 16.
Hypothesis Hdo : out + 16 <= S - 2384 \/ S <= out.
Hypothesis Hdb : b + N <= S - 2384 \/ S <= b.
Hypothesis Hdbo : b + N <= out \/ out + 16 <= b.

Variable l0 : regfile.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSL l0 l' ->
  rget l' 2 = W (S - 2240) -> rget l' 8 = W S ->
  unch M M' (a2u_FP S out) -> mem_grows M M' ->
  reach PSEGS rom (Z_to_bv 64 0x1e0c08) l' M' Post.

(* [comment removed for export] *)
Definition LM (M' : mem) (wr : Z) : Prop :=
  pkt_at M' (S - 2216) out wr 16 sb eb /\ 0 <= wr <= 16 /\ unch M M' (a2u_FP S out) /\ mem_grows M M'.

Lemma LM_wf : forall wr, 0 <= wr <= 16 -> pkt_wf (S - 2216) out wr 16 sb eb.
Proof. intros wr Hwr. unfold pkt_wf, P_IMG_END in *. repeat split; try lia; exact Heb. Qed.

Lemma LM_bytes : forall M' wr, LM M' wr -> bytes_at M' b N B.
Proof.
  intros M' wr (_ & _ & HU & _). unfold P_IMG_END in *.
  eapply bytes_at_unch; [exact HU | lia | lia | | exact HB]. intros x Hx. unfold a2u_FP, inr in *. lia.
Qed.

Lemma LM_img : forall M' wr lo hi, LM M' wr -> 0 <= lo -> hi <= P_IMG_END -> img_ok M lo hi -> img_ok M' lo hi.
Proof.
  intros M' wr lo hi (_ & _ & HU & _) Hlo Hhi Hi. unfold P_IMG_END in *.
  eapply img_unch; [exact HU | lia | lia | | exact Hi]. intros x Hx. unfold a2u_FP, inr in *. lia.
Qed.

Lemma LM_wr : forall M' wr a n, LM M' wr -> wr_ok PSEGS M a n -> wr_ok PSEGS M' a n.
Proof. intros M' wr a n (_ & _ & _ & HG) Hw. eapply wr_ok_grows; eassumption. Qed.

Lemma LM_next : forall M' M'' wr wr' (P : word -> Prop), LM M' wr ->
  unch M' M'' P -> (forall x, P x -> a2u_FP S out x) -> mem_grows M' M'' ->
  pkt_at M'' (S - 2216) out wr' 16 sb eb -> 0 <= wr' <= 16 -> LM M'' wr'.
Proof.
  intros M' M'' wr wr' P (_ & _ & HU & HG) HU' HP HG' Hpk Hwr'. unfold LM.
  split; [exact Hpk|]. split; [lia|]. split.
  - eapply unch_trans; [exact HU|]. eapply unch_weaken; [exact HU' | exact HP].
  - eapply mem_grows_trans; eassumption.
Qed.

(* [comment removed for export] *)
Definition lstable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSL l0 l /\ rget l 2 = W (S - 2240) /\ rget l 8 = W S
  /\ rget l 9 = W 0x1e151 /\ rget l 22 = W (S - 2226) /\ rget l 25 = W (S - 2226) /\ rget l 23 = W 512.

Ltac open_ls H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H8 & ?H9 & ?H22 & ?H25 & ?H23);
  regs_open l Hl.

Ltac prove_ls Hse :=
  unfold lstable; split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|];
  cbn [rget lget]; repeat split; reflexivity.

(* [comment removed for export] *)
Lemma exit_blk : forall l M' wr, LM M' wr -> length l = 32%nat -> same_except KSL l0 l ->
  rget l 2 = W (S - 2240) -> rget l 8 = W S -> reach PSEGS rom (Z_to_bv 64 0x1e0c08) l M' Post.
Proof. intros l M' wr (_ & _ & HU & HG) Hl Hse H2 H8. apply K; assumption. Qed.

(* [comment removed for export] *)
Lemma err_exit : forall l M' wr, LM M' wr -> lstable l -> reach PSEGS rom (Z_to_bv 64 0x1e0be8) l M' Post.
Proof.
  intros l M' wr HLM Hst. open_ls Hst l. subst.
  wp_a2u [0x1e0c08].
  eapply exit_blk; [exact HLM | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma LM_call : forall M' wr, LM M' wr ->
  pkt_wf (S - 2216) out wr 16 sb eb /\ wr_ok PSEGS M' (S - 2384) 168 /\ wr_ok PSEGS M' (S - 2200) 16
  /\ wr_ok PSEGS M' (S - 2160) 2048 /\ wr_ok PSEGS M' out 16.
Proof.
  intros M' wr HLM. pose proof HLM as (_ & Hwr & _ & _).
  split; [apply LM_wf; exact Hwr|]. repeat split; eapply LM_wr; eassumption.
Qed.

(* [comment removed for export] *)
Lemma LM_frame : forall M' M'' wr (P : word -> Prop), LM M' wr -> unch M' M'' P -> mem_grows M' M'' ->
  (forall x, P x -> a2u_FP S out x) -> (forall x, inr x (S - 2216) 56 -> ~ P x) -> LM M'' wr.
Proof.
  intros M' M'' wr P HLM HU' HG' HP Hpk. pose proof HLM as (Hp & Hwr & _ & _). unfold P_IMG_END in *.
  eapply LM_next; [exact HLM | exact HU' | exact HP | exact HG' | | exact Hwr].
  eapply pkt_at_unch; [exact HU' | lia | lia | exact Hpk | exact Hp].
Qed.

Lemma LM_store : forall M' wr a bs, LM M' wr -> 0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall x, inr x a (Z.of_nat (length bs)) -> inr x (S - 2384) 168) -> LM (wbytes M' (W a) bs) wr.
Proof.
  intros M' wr a bs HLM Ha Hn Hin.
  eapply (LM_frame M' _ wr (fun x => inr x a (Z.of_nat (length bs)))); [exact HLM | | apply wbytes_grows | | ].
  - apply unch_store; [apply unch_refl | exact Ha | exact Hn | intros x Hx; exact Hx].
  - intros x Hx. left. apply Hin, Hx.
  - intros x Hx Hx2. apply Hin in Hx2. unfold inr in *. lia.
Qed.

Lemma LM_rd_block : forall M' wr, LM M' wr -> rd_ok M' b N.
Proof. intros M' wr HLM. eapply bytes_at_rd_ok. eapply LM_bytes. exact HLM. Qed.

Section Label.
(* [comment removed for export] *)
Variable k : Z.
Hypothesis Hk : 0 <= k <= len.
Hypothesis Khead : forall k' l M' wr', k < k' <= len -> LM M' wr' -> lstable l -> rget l 19 = W (b + k') ->
  reach PSEGS rom (Z_to_bv 64 0x1e0a44) l M' Post.

(* [comment removed for export] *)
Lemma after_label : forall l M' wr tmpv r, LM M' wr -> lstable l -> rget l 18 = W tmpv ->
  tmpv = 0 \/ (tmpv = b + r /\ k <= r < len) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0bbc) l M' Post.
Proof.
  intros l M' wr tmpv r HLM Hst H18 Htmp.
  destruct (LM_call _ _ HLM) as (HW & Hw1' & Hw2' & Hw3' & Hwo'). pose proof HLM as (HP & Hwr & HU & HG).
  unfold P_IMG_END in *. open_ls Hst l. subst.
  wp_a2u (@nil Z). rewrite ?addi_W.
  assert (Hdec : pb_ok wr 16 \/ ~ pb_ok wr 16) by (unfold pb_ok; lia).
  split; intros Hbr.
  - (* [comment removed for export] *)
    eapply (put_byte_cps rom Post M' (S - 2216) out wr 16 sb (S - 2240) eb (W 0) HP HW);
      [ lia | eapply wr_ok_sub; [exact Hw1' | lia | lia] | exact Hwo' | replace (S - 2216 + 16) with (S - 2200) by lia; exact Hw2'
      | lia | reflexivity | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity |].
    intros l' M'' wr' Hl' Hse' Hy Hn HP' HU' HG'. cbn [rget lget].
    replace (v_jalr (Z_to_bv 64 1969148) 0) with (Z_to_bv 64 0x1e0bfc) by reflexivity.
    assert (HLM' : LM M'' wr').
    { eapply LM_next; [exact HLM | exact HU' | | exact HG' | exact HP' |].
      - intros x Hx. unfold FR_pb, a2u_FP, inr in *. lia.
      - destruct Hdec as [Hd|Hd]; [rewrite (Hy Hd); unfold pb_ok in Hd; lia | rewrite (Hn Hd); lia]. }
    regs_open l' Hl'. se_subst Hse'. clear Hse'.
    wp_a2u [0x1e0c08].
    eapply exit_blk; [exact HLM' | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity | reflexivity].
  - (* [comment removed for export] *)
    destruct Htmp as [->|[-> Hr]]; [exfalso; apply Hbr; reflexivity|]. clear Hbr.
    eapply (put_byte_cps rom Post M' (S - 2216) out wr 16 sb (S - 2240) eb (W 46) HP HW);
      [ lia | eapply wr_ok_sub; [exact Hw1' | lia | lia] | exact Hwo' | replace (S - 2216 + 16) with (S - 2200) by lia; exact Hw2'
      | lia | reflexivity | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity |].
    intros l' M'' wr' Hl' Hse' Hy Hn HP' HU' HG'. cbn [rget lget].
    replace (v_jalr (Z_to_bv 64 1969108) 0) with (Z_to_bv 64 0x1e0bd4) by reflexivity.
    assert (HLM' : LM M'' wr').
    { eapply LM_next; [exact HLM | exact HU' | | exact HG' | exact HP' |].
      - intros x Hx. unfold FR_pb, a2u_FP, inr in *. lia.
      - destruct Hdec as [Hd|Hd]; [rewrite (Hy Hd); unfold pb_ok in Hd; lia | rewrite (Hn Hd); lia]. }
    regs_open l' Hl'. se_subst Hse'. clear Hse'.
    wp_a2u [0x1e0a44]. rewrite ?addi_W.
    eapply (Khead (r + 1)); [lia | exact HLM' | prove_ls Hse | cbn [rget lget]; f_equal; lia].
Qed.

(* [comment removed for export] *)
Lemma plain_label : forall l M' wr tmpv r, LM M' wr -> lstable l -> k <= r <= len ->
  rget l 19 = W (b + k) -> rget l 20 = W (r - k) -> rget l 18 = W tmpv ->
  tmpv = 0 \/ (tmpv = b + r /\ k <= r < len) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0a80) l M' Post.
Proof.
  intros l M' wr tmpv r HLM Hst Hr H19 H20 H18 Htmp.
  destruct (LM_call _ _ HLM) as (HW & Hw1' & Hw2' & Hw3' & Hwo'). pose proof HLM as (HP & Hwr & HU & HG).
  pose proof (LM_rd_block _ _ HLM) as Hrdb.
  unfold P_IMG_END in *. open_ls Hst l. subst.
  wp_a2u (@nil Z). rewrite ?addi_W.
  assert (Hdec : wm_ok wr 16 (r - k) \/ ~ wm_ok wr 16 (r - k)) by (unfold wm_ok; lia).
  eapply (wmemcpy_cps rom Post M' (S - 2216) out wr 16 sb (S - 2240) (b + k) (r - k) eb HP HW);
    [ lia | lia | eapply wr_ok_sub; [exact Hw1' | lia | lia] | lia | lia
    | eapply rd_ok_sub; [exact Hrdb | lia | lia] | exact Hwo'
    | replace (S - 2216 + 16) with (S - 2200) by lia; exact Hw2' | lia
    | reflexivity | reflexivity | cbn [rget lget]; f_equal; lia | reflexivity | reflexivity |].
  intros l' M'' wr' Hl' Hse' Hy Hn HP' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1968788) 0) with (Z_to_bv 64 0x1e0a94) by reflexivity.
  assert (HLM' : LM M'' wr').
  { eapply LM_next; [exact HLM | exact HU' | | exact HG' | exact HP' |].
    - intros x Hx. unfold FR_wm, a2u_FP, inr in *. lia.
    - destruct Hdec as [Hd|Hd]; [rewrite (Hy Hd); unfold wm_ok in Hd; lia | rewrite (Hn Hd); lia]. }
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  wp_a2u [0x1e0bbc].
  eapply (after_label _ _ wr' tmpv r); [exact HLM' | prove_ls Hse | reflexivity | exact Htmp].
Qed.

(* [comment removed for export] *)
Section Utf.
Variables (w : Z) (tmpv r : Z).
Hypothesis Hw : 0 < w <= 512.
Hypothesis Htmp : tmpv = 0 \/ (tmpv = b + r /\ k <= r < len).

Section UtfIter.
Variable i : Z.
Hypothesis Hi : 0 <= i < w.
Hypothesis Kf1 : forall l M' wr, i + 1 < w -> LM M' wr -> lstable l -> rget l 18 = W tmpv ->
  rget l 19 = W (w - (i + 1)) -> rget l 20 = W (S - 2160 + 4 * (i + 1)) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0ad8) l M' Post.

(* [comment removed for export] *)
Lemma utf_put : forall l M' wr u, LM M' wr -> lstable l -> 1 <= u <= 4 -> rget l 12 = W u ->
  rget l 18 = W tmpv -> rget l 19 = W (w - i) -> rget l 20 = W (S - 2160 + 4 * i) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0b88) l M' Post.
Proof.
  intros l M' wr u HLM Hst Hu H12 H18 H19 H20.
  destruct (LM_call _ _ HLM) as (_ & Hw1' & _ & _ & _).
  unfold P_IMG_END in *. open_ls Hst l. subst.
  wp_a2u (@nil Z). rewrite ?add_W, ?addi_W.
  split; [eapply wr_ok_store; [exact Hw1' | lia | lia]|].
  match goal with |- reach _ _ _ _ ?Mx _ => set (M2 := Mx) end.
  assert (HLM2 : LM M2 wr).
  { unfold M2. apply LM_store; [exact HLM | lia | rewrite length_N_to_le_bytes; lia|].
    intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold inr in *. lia. }
  clearbody M2.
  destruct (LM_call _ _ HLM2) as (HW & Hw1'' & Hw2'' & Hw3'' & Hwo''). pose proof HLM2 as (HP & Hwr & HU & HG).
  assert (Hdec : wm_ok wr 16 u \/ ~ wm_ok wr 16 u) by (unfold wm_ok; lia).
  eapply (wmemcpy_cps rom Post M2 (S - 2216) out wr 16 sb (S - 2240) (S - 2226) u eb HP HW);
    [ lia | lia | eapply wr_ok_sub; [exact Hw1'' | lia | lia] | lia | lia
    | eapply rd_ok_sub; [apply (wr_ok_rd_ok M2 (S - 2384) 168 Hw1''); unfold P_IMG_END; lia | lia | lia] | exact Hwo''
    | replace (S - 2216 + 16) with (S - 2200) by lia; exact Hw2'' | lia
    | reflexivity | reflexivity | cbn [rget lget]; f_equal; lia | cbn [rget lget]; f_equal; lia | reflexivity |].
  intros l' M'' wr' Hl' Hse' Hy Hn HP' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1969060) 0) with (Z_to_bv 64 0x1e0ba4) by reflexivity.
  assert (HLM' : LM M'' wr').
  { eapply LM_next; [exact HLM2 | exact HU' | | exact HG' | exact HP' |].
    - intros x Hx. unfold FR_wm, a2u_FP, inr in *. lia.
    - destruct Hdec as [Hd|Hd]; [rewrite (Hy Hd); unfold wm_ok in Hd; lia | rewrite (Hn Hd); lia]. }
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  wp_a2u [0x1e0ad8; 0x1e0bbc]. rewrite ?addi_W. rewrite Wu by lia.
  split; intros Hbr.
  - eapply Kf1; [lia | exact HLM' | prove_ls Hse | reflexivity | ..]; cbn [rget lget]; f_equal; lia.
  - eapply (after_label _ _ wr' tmpv r); [exact HLM' | prove_ls Hse | reflexivity | exact Htmp].
Qed.

(* [comment removed for export] *)
Lemma utf_cp : forall l M' wr, LM M' wr -> lstable l ->
  rget l 18 = W tmpv -> rget l 19 = W (w - i) -> rget l 20 = W (S - 2160 + 4 * i) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0ad8) l M' Post.
Proof.
  intros l M' wr HLM Hst H18 H19 H20.
  destruct (LM_call _ _ HLM) as (_ & Hw1' & _ & Hw3' & _).
  unfold P_IMG_END in *. open_ls Hst l. subst.
  wp_a2u [0x1e0b88; 0x1e0be8].
  assert (exists v, load_ok PSEGS M' (W (S - 2160 + 4 * i)) 4 v) as [v Hv].
  { eapply load_rd; [apply (wr_ok_rd_ok M' (S - 2160) 2048 Hw3'); unfold P_IMG_END; lia | lia..]. }
  exists v. split; [exact Hv|]. clear Hv. rewrite ?addi_W.
  repeat (first [ split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact Hw1']; solve_grows | lia | lia]|]
                | split; intros ?Hbr ]);
    first [ eapply err_exit; [ | prove_ls Hse]
          | eapply utf_put; [ | prove_ls Hse | | reflexivity | reflexivity | reflexivity | reflexivity] ];
    try lia;
    repeat (apply LM_store; [ | lia | rewrite length_N_to_le_bytes; lia
                            | intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold inr in *; lia]);
    exact HLM.
Qed.

End UtfIter.

Lemma utf_loop : forall m i l M' wr, w - i = Z.of_nat m -> 0 <= i < w -> LM M' wr -> lstable l ->
  rget l 18 = W tmpv -> rget l 19 = W (w - i) -> rget l 20 = W (S - 2160 + 4 * i) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0ad8) l M' Post.
Proof.
  induction m as [m IH] using lt_wf_ind; intros i l M' wr Hm Hi HLM Hst H18 H19 H20.
  apply (utf_cp i Hi) with (wr := wr); try assumption.
  intros l2 M2 wr2 Hlt HLM2 Hst2 H18' H19' H20'.
  eapply (IH (Z.to_nat (w - (i + 1)))) with (i := i + 1); try eassumption; lia.
Qed.
End Utf.

(* [comment removed for export] *)
Lemma puny_label : forall l M' wr tmpv r, LM M' wr -> lstable l -> k + 4 <= r <= len ->
  rget l 19 = W (b + k) -> rget l 20 = W (r - k) -> rget l 18 = W tmpv ->
  tmpv = 0 \/ (tmpv = b + r /\ k <= r < len) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0aa4) l M' Post.
Proof.
  intros l M' wr tmpv r HLM Hst Hr H19 H20 H18 Htmp.
  destruct (LM_call _ _ HLM) as (_ & Hw1' & _ & _ & _).
  unfold P_IMG_END in *. open_ls Hst l. subst.
  wp_a2u (@nil Z). rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Hw1' | lia | lia]|].
  match goal with |- reach _ _ _ _ ?Mx _ => set (M2 := Mx) end.
  assert (Cq : cell PSEGS M2 (S - 2226 + 6) 4 (W 512)) by (unfold M2; apply cell_store_same; lia).
  assert (HLM2 : LM M2 wr).
  { unfold M2. apply LM_store; [exact HLM | lia | rewrite length_N_to_le_bytes; lia|].
    intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold inr in *. lia. }
  clearbody M2.
  destruct (LM_call _ _ HLM2) as (_ & Hw1'' & _ & Hw3'' & _).
  pose proof (LM_rd_block _ _ HLM2) as Hrdb.
  replace (Z_to_bv 64 1967752) with (Z_to_bv 64 0x1e0688) by reflexivity.
  eapply (decode_cps rom Post M2 (S - 2240) (b + k + 4) (r - k + -4) (S + -2048 + -112) (S + -2048 + -172) 512);
    [ lia | lia | eapply rd_ok_sub; [exact Hrdb | lia | lia] | lia
    | replace (S + -2048 + -172) with (S - 2226 + 6) by lia; exact Cq
    | unfold P_IMG_END; lia | eapply wr_ok_sub; [exact Hw1'' | lia | lia]
    | unfold P_IMG_END; lia | eapply wr_ok_sub; [exact Hw3'' | lia | lia]
    | unfold P_IMG_END; lia | eapply wr_ok_sub; [exact Hw1'' | lia | lia]
    | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M3 Hl' Hse' Ha0 Hwc HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1968836) 0) with (Z_to_bv 64 0x1e0ac4) by reflexivity.
  assert (HLM3 : LM M3 wr).
  { eapply LM_frame; [exact HLM2 | exact HU' | exact HG' | | ].
    - intros x Hx. unfold dec_FP, a2u_FP, inr in *. lia.
    - intros x Hx Hx2. unfold dec_FP, inr in *. lia. }
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  destruct Ha0 as [Ea0|Ea0]; match type of Ea0 with ?x = _ => subst x end.
  - (* [comment removed for export] *)
    wp_a2u [0x1e0be8]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    split; intros Hbr; [clear Hbr | exfalso; lia].
    eapply err_exit; [exact HLM3 | prove_ls Hse].
  - destruct (Hwc eq_refl) as (wv & Hwv & Cw). clear Hwc.
    wp_a2u [0x1e0be8; 0x1e0ad8; 0x1e0bbc]. change (bv_unsigned (Z_to_bv 64 1)) with 1.
    split; intros Hbr; [exfalso; lia|]. clear Hbr.
    rewrite ?addi_W.
    eexists. split; [apply load_cell; [replace (S - 2226 + 6) with (S + -2048 + -172) by lia; exact Cw | lia]|].
    rewrite (Wu wv) by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small wv) by lia.
    rewrite Wu by lia. split; intros Hbr.
    + eapply (after_label _ _ wr tmpv r); [exact HLM3 | prove_ls Hse | reflexivity | exact Htmp].
    + eapply (utf_loop wv tmpv r ltac:(lia) Htmp (Z.to_nat (wv - 0)) 0);
        [ lia | lia | exact HLM3 | prove_ls Hse | reflexivity | ..]; cbn [rget lget]; f_equal; lia.
Qed.

(* [comment removed for export] *)
Section Stops.
Variables (r z : Z).
Hypothesis Hrz : k <= r <= z /\ z <= len.
Hypothesis HBz : bv_unsigned (B z) = 0.
Hypothesis HBnz : forall j, k <= j < z -> bv_unsigned (B j) <> 0.
Hypothesis HBr : bv_unsigned (B r) = 0 \/ bv_unsigned (B r) = 46.
Hypothesis HBn : forall j, k <= j < r -> bv_unsigned (B j) <> 0 /\ bv_unsigned (B j) <> 46.

Lemma slack_le : forall t, k <= t <= len -> (b + t) / 8 * 8 + 8 <= b + N.
Proof.
  intros t Ht. assert ((b + t) / 8 <= (b + len) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma prefix_test : forall l M' wr tmpv, LM M' wr -> lstable l ->
  rget l 19 = W (b + k) -> rget l 20 = W (r - k) -> rget l 18 = W tmpv ->
  tmpv = 0 \/ (tmpv = b + r /\ k <= r < len) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0a6c) l M' Post.
Proof.
  intros l M' wr tmpv HLM Hst H19 H20 H18 Htmp.
  pose proof (LM_bytes _ _ HLM) as HB'.
  assert (Hi3' : img_ok M' 0x1e151 0x1e156) by (eapply LM_img; [exact HLM | lia | unfold P_IMG_END; lia | exact Hi3]).
  unfold P_IMG_END in *. open_ls Hst l. subst.
  wp_a2u (@nil Z).
  replace (Z_to_bv 64 2584376) with (Z_to_bv 64 0x276f38) by reflexivity.
  eapply (strncmp_cps rom Post M' b N B k z 0x1e151 4 XN);
    [ exact HB' | lia | lia | lia | lia | exact HBz | exact HBnz | lia | lia
    | apply xn_loads; exact Hi3' | apply xn_nz | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' Hl' Hse' Heq. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1968764) 0) with (Z_to_bv 64 0x1e0a7c) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  wp_a2u [0x1e0aa4; 0x1e0a80]. split; intros Hbr.
  - (* [comment removed for export] *)
    specialize (Heq Hbr).
    assert (Hr4 : k + 4 <= r).
    { destruct (Z_lt_le_dec r (k + 4)); [|assumption]. exfalso.
      pose proof (Heq (r - k) ltac:(lia)) as E. replace (k + (r - k)) with r in E by lia.
      destruct (xn_not_stop (r - k) ltac:(lia)) as [N0 N46]. rewrite <- E in N0, N46. destruct HBr; contradiction. }
    eapply (puny_label _ _ wr tmpv r); [exact HLM | prove_ls Hse | lia | reflexivity | reflexivity | reflexivity | exact Htmp].
  - clear Hbr Heq.
    eapply (plain_label _ _ wr tmpv r); [exact HLM | prove_ls Hse | lia | reflexivity | reflexivity | reflexivity | exact Htmp].
Qed.

Lemma r_is_z : bv_unsigned (B r) = 0 -> r = z.
Proof.
  intros H0. destruct (Z.eq_dec r z) as [E|E]; [exact E|]. exfalso. apply (HBnz r); [lia | exact H0].
Qed.

(* [comment removed for export] *)
Lemma head : forall l M' wr, LM M' wr -> lstable l -> rget l 19 = W (b + k) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0a44) l M' Post.
Proof.
  intros l M' wr HLM Hst H19.
  pose proof (LM_bytes _ _ HLM) as HB'.
  destruct (LM_call _ _ HLM) as (_ & Hw1' & _ & _ & _).
  assert (Hi1' : img_ok M' 0x3a658 0x3a660) by (eapply LM_img; [exact HLM | lia | unfold P_IMG_END; lia | exact Hi1]).
  assert (Hi2' : img_ok M' 0x3a690 0x3a698) by (eapply LM_img; [exact HLM | lia | unfold P_IMG_END; lia | exact Hi2]).
  pose proof (slack_le r ltac:(lia)) as Hslr. pose proof (slack_le z ltac:(lia)) as Hslz.
  unfold P_IMG_END in *. open_ls Hst l. subst.
  wp_a2u (@nil Z).
  replace (Z_to_bv 64 2583228) with (Z_to_bv 64 0x276abc) by reflexivity.
  eapply (strchr_cps rom Post M' b N B k r 46 (S - 2240));
    [ exact HB' | lia | lia | lia | lia | lia | exact HBr | exact HBn | exact Hslr | exact Hi1' | exact Hi2'
    | lia | lia | eapply wr_ok_sub; [exact Hw1' | lia | lia] | lia
    | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M'' Hl' Hse' H10' HU' HG'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1968720) 0) with (Z_to_bv 64 0x1e0a50) by reflexivity.
  assert (HLM' : LM M'' wr).
  { eapply LM_frame; [exact HLM | exact HU' | exact HG' | | ].
    - intros x Hx. unfold FR2, a2u_FP, inr in *. lia.
    - intros x Hx Hx2. unfold FR2, inr in *. lia. }
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  destruct (Z.eqb_spec (bv_unsigned (B r)) 46) as [E46|E46]; match type of H10' with ?x = _ => subst x end.
  - (* [comment removed for export] *)
    assert (Hrl : r < len).
    { destruct (Z.eq_dec r len) as [E|E]; [|lia]. exfalso. rewrite E, HBlen in E46. discriminate E46. }
    wp_a2u [0x1e0a6c]. rewrite Wu by lia. split; intros Hbr; [exfalso; lia|]. clear Hbr.
    rewrite ?sub_W.
    eapply (prefix_test _ _ wr (b + r)); [exact HLM' | prove_ls Hse | reflexivity | | reflexivity | right; split; [reflexivity | lia]].
    cbn [rget lget]. f_equal. lia.
  - (* [comment removed for export] *)
    assert (Er : r = z) by (apply r_is_z; destruct HBr; [assumption | contradiction]).
    pose proof (LM_bytes _ _ HLM') as HB''.
    assert (Hi1'' : img_ok M'' 0x3a658 0x3a660) by (eapply LM_img; [exact HLM' | lia | unfold P_IMG_END; lia | exact Hi1]).
    assert (Hi2'' : img_ok M'' 0x3a690 0x3a698) by (eapply LM_img; [exact HLM' | lia | unfold P_IMG_END; lia | exact Hi2]).
    wp_a2u (@nil Z). change (bv_unsigned (Z_to_bv 64 0)) with 0. split; intros Hbr; [clear Hbr | exfalso; lia].
    replace (Z_to_bv 64 2584232) with (Z_to_bv 64 0x276ea8) by reflexivity.
    eapply (strlen_cps rom Post M'' b N B k z);
      [ exact HB'' | lia | lia | lia | lia | exact HBz | exact HBnz | exact Hslz | exact Hi1'' | exact Hi2''
      | reflexivity | reflexivity |].
    intros l3 Hl3 Hse3 H10''. cbn [rget lget].
    replace (v_jalr (Z_to_bv 64 1968744) 0) with (Z_to_bv 64 0x1e0a68) by reflexivity.
    regs_open l3 Hl3. se_subst Hse3. clear Hse3. match type of H10'' with ?x = _ => subst x end.
    wp_a2u [0x1e0a6c].
    eapply (prefix_test _ _ wr 0); [exact HLM' | prove_ls Hse | reflexivity | | reflexivity | left; reflexivity].
    cbn [rget lget]. f_equal. lia.
Qed.

End Stops.

(* [comment removed for export] *)
Lemma label : forall l M' wr, LM M' wr -> lstable l -> rget l 19 = W (b + k) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0a44) l M' Post.
Proof.
  intros l M' wr HLM Hst H19.
  set (Pz := fun j => Z.eqb (bv_unsigned (B j)) 0).
  set (Pr := fun j => Z.eqb (bv_unsigned (B j)) 0 || Z.eqb (bv_unsigned (B j)) 46).
  destruct (first_stop Pz (Z.to_nat (len - k)) k len ltac:(lia)) as (z & Hz & HPz & Hzb).
  { unfold Pz. rewrite HBlen. reflexivity. }
  destruct (first_stop Pr (Z.to_nat (z - k)) k z ltac:(lia)) as (r & Hr & HPr & Hrb).
  { unfold Pr. unfold Pz in HPz. rewrite HPz. reflexivity. }
  unfold Pz in HPz, Hzb. unfold Pr in HPr, Hrb.
  apply (head r z) with (wr := wr); try assumption.
  - lia.
  - apply Z.eqb_eq. exact HPz.
  - intros j Hj. apply Z.eqb_neq. apply Hzb. exact Hj.
  - apply orb_true_iff in HPr. destruct HPr as [E|E]; apply Z.eqb_eq in E; [left | right]; exact E.
  - intros j Hj. specialize (Hrb j Hj). apply orb_false_iff in Hrb as [E1 E2].
    split; apply Z.eqb_neq; assumption.
Qed.

End Label.

(* [comment removed for export] *)
Lemma labels : forall m k l M' wr, len - k = Z.of_nat m -> 0 <= k <= len -> LM M' wr -> lstable l ->
  rget l 19 = W (b + k) -> reach PSEGS rom (Z_to_bv 64 0x1e0a44) l M' Post.
Proof.
  induction m as [m IH] using lt_wf_ind; intros k l M' wr Hm Hk HLM Hst H19.
  eapply label with (k := k) (wr := wr); try assumption.
  intros k' l2 M2 wr2 Hk' HLM2 Hst2 H19'.
  eapply (IH (Z.to_nat (len - k'))) with (k := k'); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma region_body : forall l, l = l0 -> length l = 32%nat ->
  rget l 2 = W (S - 2240) -> rget l 8 = W S -> rget l 19 = W b ->
  reach PSEGS rom (Z_to_bv 64 0x1e0a18) l M Post.
Proof.
  intros l El Hl H2 H8 H19.
  assert (Hse : same_except KSL l0 l) by (rewrite El; apply same_except_refl). clear El.
  assert (HLM : LM M 0) by (unfold LM; split; [exact HP0|]; split; [lia|]; split; [apply unch_refl | apply mem_grows_refl]).
  regs_open l Hl. subst.
  wp_a2u [0x1e0a44]. rewrite ?addi_W.
  eapply (labels (Z.to_nat (len - 0)) 0); [lia | lia | exact HLM | | cbn [rget lget]; f_equal; lia].
  unfold lstable; split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|].
  cbn [rget lget]. repeat split; try reflexivity; f_equal; lia.
Qed.

End A2u.

(* [comment removed for export] *)
Theorem a2u_loop_cps : forall rom Post M S b len N out sb eb B l,
  bytes_at M b N B -> 0 < b /\ b + N < 2 ^ 63 -> 0 <= len < 2 ^ 31 /\ len < N ->
  bv_unsigned (B len) = 0 -> (b + len) / 8 * 8 + 8 <= b + N ->
  pkt_at M (S - 2216) out 0 16 sb eb -> 0 < sb < 2 ^ 64 -> (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 ->
  img_ok M 0x3a658 0x3a660 -> img_ok M 0x3a690 0x3a698 -> img_ok M 0x1e151 0x1e156 ->
  P_IMG_END <= S - 2384 /\ S < 2 ^ 63 ->
  wr_ok PSEGS M (S - 2384) 168 -> wr_ok PSEGS M (S - 2200) 16 -> wr_ok PSEGS M (S - 2160) 2048 ->
  P_IMG_END <= out /\ out + 16 < 2 ^ 63 -> wr_ok PSEGS M out 16 ->
  (out + 16 <= S - 2384 \/ S <= out) -> (b + N <= S - 2384 \/ S <= b) -> (b + N <= out \/ out + 16 <= b) ->
  length l = 32%nat -> rget l 2 = W (S - 2240) -> rget l 8 = W S -> rget l 19 = W b ->
  (forall l' M', length l' = 32%nat -> same_except KSL l l' ->
     rget l' 2 = W (S - 2240) -> rget l' 8 = W S ->
     unch M M' (a2u_FP S out) -> mem_grows M M' ->
     reach PSEGS rom (Z_to_bv 64 0x1e0c08) l' M' Post) ->
  reach PSEGS rom (Z_to_bv 64 0x1e0a18) l M Post.
Proof.
  intros rom Post M S b len N out sb eb B l; intros.
  eapply (region_body rom Post M S b len N out sb eb B) with (l0 := l); eauto.
Qed.
