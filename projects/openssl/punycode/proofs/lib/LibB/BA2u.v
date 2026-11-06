(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit HasZero StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow ACheck ASaves ABridge.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BCode2 BRt BImg BIface BWpacket BWpMemcpy BWpPut BDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_a2u stops := wp_go 0x4312f4 376%nat C_a2ulabel_eq C_a2ulabel stops.

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
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Definition a2u_FP (fs L FB6 out : Z) (x : word) : Prop :=
  inr x (L - 2400) 2464 \/ inr x (FB6 + 32) 2048 \/ inr x (FB6 + 2224) 16 \/ inr x (FB6 + 2304) 4
  \/ inr x (FB6 + 2320) 6 \/ inr x (sha FB6 + 288) 3 \/ inr x out 16 \/ ring_FP fs x.

(* [comment removed for export] *)
Definition a2u_sep (fs L FB6 out b N : Z) : Prop :=
  (L + 64 <= fs \/ fs + FS_SIZE <= L - 2400) /\ (L + 64 <= FB6 \/ FB6 + 2400 <= L - 2400)
  /\ (L + 64 <= out \/ out + 16 <= L - 2400) /\ (L + 64 <= b \/ b + N <= L - 2400)
  /\ (out + 16 <= FB6 \/ FB6 + 2400 <= out) /\ (out + 16 <= fs \/ fs + 1085440 <= out)
  /\ (FB6 + 2400 <= fs \/ fs + 1085440 <= FB6) /\ (b + N <= fs \/ fs + 1085440 <= b)
  /\ (b + N <= out \/ out + 16 <= b) /\ (b + N <= FB6 \/ FB6 + 2400 <= b)
  /\ (L + 64 <= SB \/ HIMEM_BEG <= L - 2400).

(* [comment removed for export] *)
Definition XNB : Z := 0xc2ee0.
Definition XN (i : Z) : byte :=
  if Z.eqb i 0 then Z_to_bv 8 120 else if Z.eqb i 1 then Z_to_bv 8 110 else Z_to_bv 8 45.

Lemma xn_loads : forall M, img_ok M 0xc2ee0 0xc2ee5 ->
  forall i, 0 <= i < 4 -> load_ok BSEGS M (W (0xc2ee0 + i)) 1 (W (bv_unsigned (XN i))).
Proof.
  intros M Hi i Hr.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [->|[->|[->| ->]]] by lia;
    (eapply (load_img BSEGS M 0xc2ee0 0xc2ee5); [exact Hi | lia | lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity]).
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
Variables (RTX : mem -> Prop) (RTXD : word -> Prop) (RSEP : Z -> Z -> Prop) (fs : Z).
Hypothesis IF : rt_iface RTX RTXD RSEP fs.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (L FB6 b len N out sb : Z) (eb : word) (B : Z -> byte).
(* [comment removed for export] *)
Hypothesis HB : bytes_at M b N B.
Hypothesis Hb : 0 < b /\ b + N < 2 ^ 63.
Hypothesis Hlen : 0 <= len < 2 ^ 31 /\ len < N.
Hypothesis HBlen : bv_unsigned (B len) = 0.
Hypothesis Hslack : (b + len) / 8 * 8 + 8 <= b + N.
Hypothesis Hbsh : memrange b N /\ addr_ok M b (len + 1) /\ shw_ok M b (len + 1).
(* [comment removed for export] *)
Hypothesis HP0 : pkt_at M (FB6 + 2208) out 0 16 sb eb.
Hypothesis Hsb : 0 < sb < 2 ^ 64.
Hypothesis Heb : (bv_unsigned eb mod 2 ^ 8) mod 2 = 0.
(* [comment removed for export] *)
Hypothesis Hrt : rt_ok M.
Hypothesis Hrtx : RTX M.
Hypothesis Huar : uar_on M.
Hypothesis Hgot : cell BSEGS M 0x5e2590 8 (W 0x273608) /\ cell BSEGS M 0x5e2598 8 (W 0x273870).   (* [comment removed for export] *)
Hypothesis Hxn : img_ok M 0xc2ee0 0xc2ee5.
Hypothesis Hxnsh : M (W (sha XNB)) = Some (Z_to_bv 8 5) /\ shw_ok M XNB 4.
(* [comment removed for export] *)
Hypothesis Hfs : fs_wf fs.
Hypothesis Hring : ring_idle M fs.
Hypothesis Hrwr : ring_wr M fs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis HFB6 : FB6 mod 64 = 0 /\ (B_IMG_END <= FB6 /\ (FB6 + 4096 <= SB \/ HIMEM_BEG <= FB6)) /\ FB6 + 4096 <= HIMEM_END.
Hypothesis Hsh6 : zeros M (sha FB6 + 276) 7 /\ zeros M (sha FB6 + 4) 256 /\ rd_ok M (sha FB6) 296
                  /\ wr_ok BSEGS M (sha FB6 + 288) 3.
Hypothesis Hw6 : wr_ok BSEGS M (FB6 + 32) 2048 /\ wr_ok BSEGS M (FB6 + 2224) 16 /\ wr_ok BSEGS M (FB6 + 2304) 4
                 /\ wr_ok BSEGS M (FB6 + 2320) 6.
(* [comment removed for export] *)
Hypothesis Hout : B_IMG_END <= out /\ memrange out 16 /\ addr_ok M out 16 /\ shw_ok M out 16 /\ wr_ok BSEGS M out 16.
(* [comment removed for export] *)
Hypothesis HL : B_IMG_END <= L - 2400 /\ L + 64 < 2 ^ 63 /\ L mod 32 = 0.
Hypothesis HwL : wr_ok BSEGS M (L - 2400) 2464.
Hypothesis Hsep : a2u_sep fs L FB6 out b N.
Hypothesis Hs_rtxd : forall x, a2u_FP fs L FB6 out x -> ~ RTXD x.
Hypothesis Hrsep : RSEP (L - 2400) 2400.

Variable l0 : regfile.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSL l0 l' ->
  cell BSEGS M' (L + 24) 8 (rget l0 27) -> cell BSEGS M' (L + 32) 8 (rget l0 25) -> cell BSEGS M' (L + 40) 8 (rget l0 20) ->
  ring_idle M' fs -> unch M M' (a2u_FP fs L FB6 out) -> mem_grows M M' ->
  reach BSEGS rom (W 0x431800) l' M' Post.

Let pk := FB6 + 2208.
Let FP := a2u_FP fs L FB6 out.

(* [comment removed for export] *)
Lemma nums : 0 < out /\ out + 24 <= HIMEM_END /\ 0 < b /\ b + N + 8 <= HIMEM_END
  /\ (B_IMG_END <= fs /\ (fs + FS_SIZE <= SB \/ HIMEM_BEG <= fs))
  /\ fs + FS_SIZE <= HIMEM_END /\ fs mod 8 = 0 /\ FB6 mod 8 = 0 /\ B_IMG_END <= L - 2400.
Proof.
  destruct Hout as (O1 & [_ O2] & _). destruct Hbsh as ([_ B2] & _). destruct Hfs as (F1 & F2 & F3).
  destruct HFB6 as (A1 & A2 & A3). destruct HL as (L1 & _). destruct Hb as (B0 & _).
  assert (FB6 mod 8 = 0).
  { pose proof (Z.div_mod FB6 64 ltac:(lia)) as Hd. rewrite A1 in Hd. rewrite Hd.
    replace (64 * (FB6 / 64) + 0) with (0 + (8 * (FB6 / 64)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  clear - O1 O2 B2 B0 F1 F2 F3 H L1. unfold B_IMG_END, LOMEM_END, HIMEM_BEG, HIMEM_END, SB, FS_SIZE in *. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma FP_app : forall y, FP y -> B_IMG_END <= bv_unsigned y.
Proof.
  destruct HL as (L1 & _). destruct Hout as (O1 & _). destruct HFB6 as (_ & A2 & A3). destruct Hfs as (F1 & F2 & _).
  pose proof (sha_range (fs + 36864) ltac:(unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *; lia)) as Hr.
  pose proof (sha_range FB6 ltac:(unfold HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *; lia)) as Hr6.
  clear - L1 O1 A2 F1 Hr Hr6.
  intros y Hy. unfold FP, a2u_FP, ring_FP, inr, B_IMG_END, SB, HIMEM_BEG, FS_SIZE in *. lia.
Qed.

Lemma ring_sha_range : SB <= sha (fs + 36864) /\ sha (fs + 36864) + 131072 <= HIMEM_BEG.
Proof.
  destruct Hfs as (F1 & F2 & _). unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *.
  assert (Hq : (fs + 36864) / 8 <= 17592185913344) by (apply Z.div_le_upper_bound; lia).
  assert (Hq0 : 0 <= (fs + 36864) / 8) by (apply Z.div_pos; lia).
  unfold sha, SB. lia.
Qed.

Lemma f6_sha_range : SB <= sha FB6 /\ sha FB6 + 512 <= HIMEM_BEG.
Proof.
  destruct HFB6 as (_ & A2 & A3). unfold HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *.
  assert (Hq : FB6 / 8 <= 17592186043904) by (apply Z.div_le_upper_bound; lia).
  assert (Hq0 : 0 <= FB6 / 8) by (apply Z.div_pos; lia).
  unfold sha, SB. lia.
Qed.

(* [comment removed for export] *)
Lemma FP_sha : forall x, 0 <= x < HIMEM_END -> (x < fs + 36864 \/ fs + 1085440 <= x) ->
  (x < FB6 + 2304 \/ FB6 + 2328 <= x) -> ~ FP (W (sha x)).
Proof.
  intros x Hx Hor H6 HF.
  pose proof (sha_range x Hx) as Hr. pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  destruct HFB6 as (_ & A2 & A3). destruct Hout as (_ & [_ O2] & _).
  pose proof Hsep as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S11).
  assert (Hu : bv_unsigned (W (sha x)) = sha x) by (apply Wu; clear - Hr; unfold SB, HIMEM_BEG, B_IMG_END, FS_SIZE in *; lia).
  assert (Hq : fs + 36864 = 8 * ((fs + 36864) / 8)).
  { clear - N7. pose proof (Z.div_mod (fs + 36864) 8 ltac:(lia)) as Hd. replace ((fs + 36864) mod 8) with 0 in Hd; [lia|].
    symmetry. replace (fs + 36864) with (fs + 4608 * 8) by lia. rewrite Z.mod_add by lia. exact N7. }
  assert (Hq6 : FB6 = 8 * (FB6 / 8)) by (clear - N8; pose proof (Z.div_mod FB6 8 ltac:(lia)) as Hd; lia).
  assert (Hn1 : ~ (sha (fs + 36864) <= sha x < sha (fs + 36864) + 131072)).
  { clear - Hor Hq Hx. unfold sha. set (q := (fs + 36864) / 8) in *. clearbody q. destruct Hor as [Hlt|Hge].
    - assert (x / 8 < q) by (apply Z.div_lt_upper_bound; lia). lia.
    - assert (q + 131072 <= x / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  assert (Hn2 : ~ (sha FB6 + 288 <= sha x < sha FB6 + 288 + 3)).
  { clear - H6 Hq6 Hx. unfold sha. set (q := FB6 / 8) in *. clearbody q. destruct H6 as [Hlt|Hge].
    - assert (x / 8 < q + 288) by (apply Z.div_lt_upper_bound; lia). lia.
    - assert (q + 291 <= x / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  clear - HF Hr Hu O2 S11 N5 A2 Hn1 Hn2.
  unfold FP, a2u_FP, ring_FP, inr in HF. rewrite Hu in HF. unfold SB, LOMEM_END, HIMEM_BEG, HIMEM_END, B_IMG_END, FS_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
Definition spills (M' : mem) : Prop :=
  cell BSEGS M' (L + 24) 8 (rget l0 27) /\ cell BSEGS M' (L + 32) 8 (rget l0 25) /\ cell BSEGS M' (L + 40) 8 (rget l0 20)
  /\ cell BSEGS M' (L + 48) 8 (W XNB) /\ cell BSEGS M' (L + 56) 8 (W (FB6 + 32)).

(* [comment removed for export] *)
Definition LM (M' : mem) (wr : Z) : Prop :=
  pkt_at M' pk out wr 16 sb eb /\ 0 <= wr <= 16 /\ ring_idle M' fs /\ spills M'
  /\ unch M M' FP /\ mem_grows M M'.

Lemma LM_wf : forall wr, 0 <= wr <= 16 -> pkt_wf pk out wr 16 sb eb.
Proof.
  intros wr Hwr. pose proof nums as (N1 & N2 & _). destruct HFB6 as (_ & A2 & A3). subst pk.
  unfold pkt_wf, memrange, B_IMG_END, LOMEM_END, HIMEM_BEG, HIMEM_END, SB, FS_SIZE in *. repeat split; try lia; exact Heb.
Qed.

(* [comment removed for export] *)
Lemma LM_rt : forall M' wr, LM M' wr -> rt_ok M' /\ RTX M' /\ uar_on M'
  /\ (cell BSEGS M' 0x5e2590 8 (W 0x273608) /\ cell BSEGS M' 0x5e2598 8 (W 0x273870))
  /\ img_ok M' 0xc2ee0 0xc2ee5.
Proof.
  intros M' wr (_ & _ & _ & _ & HU & _).
  split; [|split; [|split; [|split]]].
  - eapply rt_ok_unch; [exact HU | apply FP_app | exact Hrt].
  - eapply (if_unch _ _ _ _ IF); [exact Hrtx | exact HU |]. intros x Hx. split; [apply FP_app, Hx | apply Hs_rtxd, Hx].
  - eapply uar_on_unch; [exact HU | apply FP_app | exact Huar].
  - destruct Hgot as (G1 & G2).
    split; (eapply cell_unch; [exact HU | lia | (cbn; lia) | | eassumption]);
      intros x Hx HF; apply FP_app in HF; unfold inr, B_IMG_END in *; cbn in Hx; lia.
  - eapply img_unch; [exact HU | lia | lia | | exact Hxn]. intros x Hx HF. apply FP_app in HF. unfold inr, B_IMG_END in *. lia.
Qed.

Lemma sep_b : (b + N <= fs + 36864 \/ fs + 1085440 <= b) /\ (b + N <= FB6 + 2304 \/ FB6 + 2328 <= b).
Proof. pose proof Hsep as (_ & _ & _ & _ & _ & _ & _ & S8 & _ & S10 & _). clear - S8 S10. lia. Qed.

Lemma sep_out : (out + 16 <= fs + 36864 \/ fs + 1085440 <= out) /\ (out + 16 <= FB6 + 2304 \/ FB6 + 2328 <= out).
Proof. pose proof Hsep as (_ & _ & _ & _ & S5 & S6 & _). clear - S5 S6. lia. Qed.

Lemma sep_f6 : (FB6 + 2400 <= fs + 36864 \/ fs + 1085440 <= FB6).
Proof. pose proof Hsep as (_ & _ & _ & _ & _ & _ & S7 & _). clear - S7. lia. Qed.

(* [comment removed for export] *)
Lemma LM_shb : forall M' wr x, LM M' wr -> 0 <= x < HIMEM_END -> (x < fs + 36864 \/ fs + 1085440 <= x) ->
  (x < FB6 + 2304 \/ FB6 + 2328 <= x) -> M' (W (sha x)) = M (W (sha x)).
Proof. intros M' wr x (_ & _ & _ & _ & HU & _) Hx H1 H2. apply HU. apply FP_sha; assumption. Qed.

Lemma LM_str : forall M' wr, LM M' wr -> bytes_at M' b N B /\ addr_ok M' b (len + 1) /\ shw_ok M' b (len + 1).
Proof.
  intros M' wr HLM. pose proof HLM as (_ & _ & _ & _ & HU & HG). destruct Hbsh as (Bm & Bo & Bs).
  pose proof nums as (N1 & N2 & N3 & N4 & _). destruct sep_b as (Sb1 & Sb2). destruct Hlen as (Hl1 & Hl2). destruct Hb as (Hb1 & Hb2).
  split; [|split].
  - eapply bytes_at_unch; [exact HU | lia | lia | | exact HB].
    pose proof Hsep as (_ & _ & _ & S4 & _ & _ & _ & S8 & S9 & S10 & _). destruct Bm as [_ Bm].
    pose proof ring_sha_range as Hr. pose proof f6_sha_range as Hr6.
    clear - S4 S8 S9 S10 Hr Hr6 Bm.
    intros x Hx HF. unfold FP, a2u_FP, ring_FP, inr, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END in *. lia.
  - intros x Hx. destruct (Bo x Hx) as (s & Hs & Hc). exists s. split; [|exact Hc].
    rewrite (LM_shb M' wr x HLM); [exact Hs | destruct Bm as [_ Bm]; unfold LOMEM_END, HIMEM_END in *; lia | lia | lia].
  - unfold shw_ok in *. eapply rd_ok_grows; [exact HG | exact Bs].
Qed.

(* [comment removed for export] *)
Lemma LM_f6 : forall M' wr, LM M' wr ->
  sh0 M' pk 56 /\ addr_ok M' (FB6 + 32) 2048 /\ shw_ok M' (FB6 + 32) 2048 /\ rd_ok M' (sha FB6) 296.
Proof.
  intros M' wr HLM. pose proof HLM as (_ & _ & _ & _ & HU & HG).
  destruct Hsh6 as (Z1 & Z2 & R1 & _). pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  destruct HFB6 as (_ & A2 & A3). pose proof sep_f6 as S7. unfold HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *.
  assert (Hrd : rd_ok M' (sha FB6) 296) by (eapply rd_ok_grows; [exact HG | exact R1]).
  assert (Zpk : zeros M' (sha pk) (56 / 8)).
  { unfold pk. replace (FB6 + 2208) with (FB6 + 8 * 276) by lia. rewrite sha_add8. change (56 / 8) with 7.
    intros i Hi. replace (sha FB6 + 276 + i) with (sha (FB6 + 8 * (276 + i))) by (rewrite sha_add8; lia).
    rewrite (LM_shb M' wr _ HLM); [rewrite sha_add8; replace (sha FB6 + (276 + i)) with (sha FB6 + 276 + i) by lia; apply Z1; lia
                                   | unfold HIMEM_END; lia | lia | lia]. }
  assert (Zbuf : zeros M' (sha (FB6 + 32)) (2048 / 8)).
  { replace (FB6 + 32) with (FB6 + 8 * 4) by lia. rewrite sha_add8. change (2048 / 8) with 256.
    intros i Hi. replace (sha FB6 + 4 + i) with (sha (FB6 + 8 * (4 + i))) by (rewrite sha_add8; lia).
    rewrite (LM_shb M' wr _ HLM); [rewrite sha_add8; replace (sha FB6 + (4 + i)) with (sha FB6 + 4 + i) by lia; apply Z2; lia
                                   | unfold HIMEM_END; lia | lia | lia]. }
  split; [|split; [|split]].
  - apply sh0_of_zeros; [unfold pk; lia | unfold pk; replace (FB6 + 2208) with (FB6 + 276 * 8) by lia; rewrite Z.mod_add by lia; exact N8
                        | lia | reflexivity | exact Zpk].
  - apply (addr_ok_of_chunk M' (FB6 + 32) 2048 (Z_to_bv 8 0)); [lia | lia
      | replace (FB6 + 32) with (FB6 + 4 * 8) by lia; rewrite Z.mod_add by lia; exact N8 | exact Zbuf
      | intros Hne; exfalso; apply Hne; reflexivity].
  - unfold shw_ok. eapply rd_ok_sub; [exact Hrd | |].
    + replace (FB6 + 32) with (FB6 + 8 * 4) by lia. rewrite sha_add8.
      pose proof (Z.div_mod (sha FB6 + 4) 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (sha FB6 + 4) 8 ltac:(lia)) as Hm.
      assert (Hs8 : sha FB6 mod 8 = 0).
      { destruct HFB6 as (A1 & _). unfold sha, SB. pose proof (Z.div_mod FB6 64 ltac:(lia)) as Hd6. rewrite A1 in Hd6.
        replace FB6 with (0 + (8 * (FB6 / 64)) * 8) by lia. rewrite Z.div_add by lia.
        replace (0 / 8 + 8 * (FB6 / 64) + 2147450880) with (0 + (FB6 / 64 + 268431360) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
      assert ((sha FB6 + 4) mod 8 = 4).
      { pose proof (Z.div_mod (sha FB6) 8 ltac:(lia)) as Hd8. rewrite Hs8 in Hd8.
        replace (sha FB6 + 4) with (4 + (sha FB6 / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
      lia.
    + replace (FB6 + 32) with (FB6 + 8 * 4) by lia. replace (FB6 + 8 * 4 + 2048 - 1) with (FB6 + 2079) by lia.
      rewrite sha_add8.
      assert (E : sha (FB6 + 2079) = sha FB6 + 259).
      { unfold sha. pose proof (Z.div_mod FB6 8 ltac:(lia)) as Hd. rewrite N8 in Hd.
        replace (FB6 + 2079) with (7 + (FB6 / 8 + 259) * 8) by lia. rewrite Z.div_add by lia. rewrite (Z.div_small 7) by lia. lia. }
      rewrite E.
      pose proof (Z.div_mod (sha FB6 + 259) 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (sha FB6 + 259) 8 ltac:(lia)) as Hm.
      pose proof (Z.div_mod (sha FB6 + 4) 8 ltac:(lia)) as Hd4. pose proof (Z.mod_pos_bound (sha FB6 + 4) 8 ltac:(lia)) as Hm4.
      lia.
  - exact Hrd.
Qed.

Lemma LM_out : forall M' wr, LM M' wr -> addr_ok M' out 16 /\ shw_ok M' out 16.
Proof.
  intros M' wr HLM. pose proof HLM as (_ & _ & _ & _ & HU & HG). destruct Hout as (_ & Om & Oa & Os & _).
  destruct sep_out as (S1 & S2). pose proof nums as (N1 & N2 & _).
  split.
  - intros x Hx. destruct (Oa x Hx) as (s & Hs & Hc). exists s. split; [|exact Hc].
    rewrite (LM_shb M' wr x HLM); [exact Hs | lia | lia | lia].
  - unfold shw_ok in *. eapply rd_ok_grows; [exact HG | exact Os].
Qed.

Lemma LM_xn : forall M' wr, LM M' wr -> addr_ok M' XNB 4 /\ shw_ok M' XNB 4.
Proof.
  intros M' wr HLM. pose proof HLM as (_ & _ & _ & _ & HU & HG). destruct Hxnsh as (X1 & X2).
  pose proof nums as (_ & _ & _ & _ & N5 & _). destruct HFB6 as (_ & A2 & _).
  split.
  - eapply addr_ok_sub; [apply (addr_ok_partial M' XNB 5 (Z_to_bv 8 5)); [unfold XNB; lia | reflexivity | lia | | reflexivity] | lia | lia].
    rewrite (LM_shb M' wr XNB HLM); [exact X1 | unfold XNB, HIMEM_END; lia | unfold XNB, HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia | unfold XNB, HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia].
  - unfold shw_ok in *. eapply rd_ok_grows; [exact HG | exact X2].
Qed.

Lemma LM_wr : forall M' wr, LM M' wr -> ring_wr M' fs /\ wr_ok BSEGS M' (L - 2400) 2464 /\ wr_ok BSEGS M' out 16
  /\ wr_ok BSEGS M' (FB6 + 32) 2048 /\ wr_ok BSEGS M' (pk + 16) 16 /\ wr_ok BSEGS M' (FB6 + 2304) 4
  /\ wr_ok BSEGS M' (FB6 + 2320) 6 /\ wr_ok BSEGS M' (sha FB6 + 288) 3.
Proof.
  intros M' wr (_ & _ & _ & _ & _ & HG). destruct Hw6 as (W1 & W2 & W3 & W4). destruct Hsh6 as (_ & _ & _ & W5).
  destruct Hout as (_ & _ & _ & _ & W6).
  split; [eapply ring_wr_grows; [exact HG | exact Hrwr]|].
  unfold pk. replace (FB6 + 2208 + 16) with (FB6 + 2224) by lia.
  repeat split; eapply wr_ok_grows; eassumption.
Qed.

(* [comment removed for export] *)
Definition FPI (x : word) : Prop :=
  inr x (L - 2400) 2400 \/ inr x (FB6 + 32) 2048 \/ inr x (FB6 + 2304) 4 \/ inr x (FB6 + 2320) 6
  \/ inr x (sha FB6 + 288) 3.

Lemma FPI_FP : forall x, FPI x -> FP x.
Proof. intros x Hx. unfold FPI, FP, a2u_FP in *. unfold inr in *. lia. Qed.

Lemma FPI_apart : forall x, FPI x -> ~ inr x pk 56 /\ ~ inr x (L + 24) 40 /\ ~ inr x fs 8 /\ ~ inr x (fs + 4096) 16384.
Proof.
  pose proof Hsep as (S1 & S2 & _ & _ & _ & _ & S7 & _ & _ & _ & S11). pose proof f6_sha_range as (R1 & R2).
  destruct Hfs as (F1 & F2 & _). destruct HFB6 as (_ & A2 & A3).
  clear - S1 S2 S7 S11 R1 R2 F1 F2 A2 A3.
  intros x Hx. unfold FPI, pk, inr, SB, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END in *. lia.
Qed.

Lemma ring_idle_unch : forall M' M'' (P : word -> Prop), ring_idle M' fs -> unch M' M'' P ->
  (forall x, P x -> ~ inr x fs 8 /\ ~ inr x (fs + 4096) 16384) -> ring_idle M'' fs.
Proof.
  intros M' M'' P ((h & Hh & Ch) & Hz) HU HP. destruct Hfs as (F1 & F2 & _). unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *.
  split.
  - exists h. split; [exact Hh|]. eapply cell_unch; [exact HU | lia | (cbn; lia) | | exact Ch].
    intros x Hx HPx. destruct (HP x HPx) as [H1 _]. apply H1. exact Hx.
  - eapply zeros_grows_unch; [exact HU | lia | lia | | exact Hz]. intros x Hx HPx. destruct (HP x HPx) as [_ H2]. apply H2. exact Hx.
Qed.

Lemma spills_unch : forall M' M'' (P : word -> Prop), spills M' -> unch M' M'' P ->
  (forall x, P x -> ~ inr x (L + 24) 40) -> spills M''.
Proof.
  intros M' M'' P (C1 & C2 & C3 & C4 & C5) HU HP. destruct HL as (L1 & L2 & _). unfold B_IMG_END in *.
  unfold spills. repeat split; (eapply cell_unch; [exact HU | lia | (cbn; lia) | | eassumption]);
    intros x Hx HPx; apply (HP x HPx); cbn in Hx; unfold inr in *; lia.
Qed.

(* [comment removed for export] *)
Lemma LM_frame : forall M' M'' wr (P : word -> Prop), LM M' wr -> unch M' M'' P -> mem_grows M' M'' ->
  (forall x, P x -> FPI x) -> LM M'' wr.
Proof.
  intros M' M'' wr P (Hp & Hwr & Hri & Hsp & HU & HG) HU' HG' HP.
  destruct HFB6 as (_ & A2 & A3). unfold HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *.
  split; [|split; [exact Hwr|split; [|split; [|split]]]].
  - eapply pkt_at_unch; [exact HU' | unfold pk; lia | unfold pk; lia | | exact Hp].
    intros x Hx HPx. destruct (FPI_apart x (HP x HPx)) as (H1 & _). apply H1. exact Hx.
  - eapply ring_idle_unch; [exact Hri | exact HU' |]. intros x HPx. destruct (FPI_apart x (HP x HPx)) as (_ & _ & H3 & H4). auto.
  - eapply spills_unch; [exact Hsp | exact HU' |]. intros x HPx. destruct (FPI_apart x (HP x HPx)) as (_ & H2 & _). exact H2.
  - eapply unch_trans; [exact HU|]. eapply unch_weaken; [exact HU'|]. intros x Hx. apply FPI_FP, HP, Hx.
  - eapply mem_grows_trans; eassumption.
Qed.

Lemma LM_store : forall M' wr a bs, LM M' wr -> 0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall x, inr x a (Z.of_nat (length bs)) -> FPI x) -> LM (wbytes M' (W a) bs) wr.
Proof.
  intros M' wr a bs HLM Ha Hn Hin.
  eapply (LM_frame M' _ wr (fun x => inr x a (Z.of_nat (length bs)))); [exact HLM | | apply wbytes_grows | exact Hin].
  apply unch_store; [apply unch_refl | exact Ha | exact Hn | intros x Hx; exact Hx].
Qed.

(* [comment removed for export] *)
Lemma LM_next : forall M' M'' wr wr', LM M' wr -> unch M' M'' (FR_wm fs L out 16 pk) -> mem_grows M' M'' ->
  pkt_at M'' pk out wr' 16 sb eb -> 0 <= wr' <= 16 -> ring_idle M'' fs -> LM M'' wr'.
Proof.
  intros M' M'' wr wr' (_ & _ & _ & Hsp & HU & HG) HU' HG' Hp' Hwr' Hri'.
  split; [exact Hp'|]. split; [exact Hwr'|]. split; [exact Hri'|]. split; [|split].
  - eapply spills_unch; [exact Hsp | exact HU' |].
    pose proof Hsep as (S1 & S2 & S3 & _ & _ & _ & _ & _ & _ & _ & S11). pose proof ring_sha_range as (R1 & R2).
    destruct Hfs as (F1 & F2 & _). clear - S1 S2 S3 S11 R1 R2 F1 F2.
    intros x Hx. unfold FR_wm, ring_FP, pk, inr, SB, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END in *. lia.
  - eapply unch_trans; [exact HU|]. eapply unch_weaken; [exact HU'|].
    clear. intros x Hx. unfold FR_wm, FP, a2u_FP, pk, inr in *. replace (FB6 + 2208 + 16) with (FB6 + 2224) in Hx by lia.
    destruct Hx as [H|[H|[H|H]]]; [left; lia | do 6 right; left; exact H | do 2 right; left; exact H | do 7 right; exact H].
  - eapply mem_grows_trans; eassumption.
Qed.

Hypothesis H0tp : rget l0 4 = W TP.

Lemma img_ok_sub : forall M' lo hi lo' hi', img_ok M' lo hi -> lo <= lo' -> hi' <= hi -> img_ok M' lo' hi'.
Proof. intros M' lo hi lo' hi' H H1 H2 i Hi. apply H. lia. Qed.

Lemma sep_pb : pb_sep fs L pk out 16.
Proof.
  pose proof Hsep as (S1 & S2 & S3 & _ & S5 & S6 & S7 & _ & _ & _ & S11). clear - S1 S2 S3 S5 S6 S7 S11.
  unfold pb_sep, pk, FS_SIZE in *. repeat split; lia.
Qed.

Lemma sep_wm_b : forall k n, 0 <= k -> 0 <= n -> k + n <= N -> wm_sep fs L pk out 16 (b + k) n.
Proof.
  intros k n Hk Hn Hkn.
  pose proof Hsep as (S1 & S2 & S3 & _ & S5 & S6 & S7 & S8 & S9 & _ & S11). clear - S1 S2 S3 S5 S6 S7 S8 S9 S11 Hk Hn Hkn.
  unfold wm_sep, pk, FS_SIZE in *. repeat split; lia.
Qed.

Lemma sep_wm_seed : forall n, 0 <= n <= 6 -> wm_sep fs L pk out 16 (FB6 + 2320) n.
Proof.
  intros n Hn.
  pose proof Hsep as (S1 & S2 & S3 & _ & S5 & S6 & S7 & _ & _ & _ & S11). clear - S1 S2 S3 S5 S6 S7 S11 Hn.
  unfold wm_sep, pk, FS_SIZE in *. repeat split; lia.
Qed.

Lemma FRwm_rtxd : forall x, FR_wm fs L out 16 pk x -> ~ RTXD x.
Proof.
  intros x Hx. apply Hs_rtxd. unfold FR_wm, a2u_FP, pk in *. replace (FB6 + 2208 + 16) with (FB6 + 2224) in Hx by lia.
  destruct Hx as [H|[H|[H|H]]]; [left; unfold inr in *; lia | do 6 right; left; exact H | do 2 right; left; exact H | do 7 right; exact H].
Qed.

Lemma out_facts : forall M' wr, LM M' wr ->
  B_IMG_END <= out /\ memrange out 16 /\ addr_ok M' out 16 /\ (0 < 16 -> shw_ok M' out 16) /\ wr_ok BSEGS M' out 16.
Proof.
  intros M' wr HLM. destruct (LM_out _ _ HLM) as (Oa & Os). destruct (LM_wr _ _ HLM) as (_ & _ & Wo & _).
  destruct Hout as (O1 & O2 & _).
  split; [exact O1|]. split; [exact O2|]. split; [exact Oa|]. split; [intros _; exact Os | exact Wo].
Qed.

Lemma stk_facts : B_IMG_END <= L - 2400 /\ L < 2 ^ 63 /\ L mod 32 = 0.
Proof. destruct HL as (L1 & L2 & L3). repeat split; try assumption; lia. Qed.

(* [comment removed for export] *)
Definition lstable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSL l0 l /\ rget l 2 = W L /\ rget l 4 = W TP /\ rget l 9 = W L /\ rget l 18 = W SB
  /\ rget l 19 = W (sha FB6) /\ rget l 21 = W pk /\ rget l 22 = W (FB6 + 2320) /\ rget l 24 = W (FB6 + 2304).

Ltac open_ls H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H4 & ?H9 & ?H18 & ?H19 & ?H21 & ?H22 & ?H24);
  regs_open l Hl.

Ltac prove_ls Hse :=
  unfold lstable; split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|];
  cbn [rget lget]; repeat split; reflexivity.

(* [comment removed for export] *)
Lemma exit_blk : forall l M' wr, LM M' wr -> length l = 32%nat -> same_except KSL l0 l ->
  reach BSEGS rom (W 0x431800) l M' Post.
Proof.
  intros l M' wr (_ & _ & Hri & (C1 & C2 & C3 & _) & HU & HG) Hl Hse. apply K; assumption.
Qed.

(* [comment removed for export] *)
Lemma err_exit2 : forall l M' wr, LM M' wr -> lstable l -> reach BSEGS rom (W 0x4317f4) l M' Post.
Proof.
  intros l M' wr HLM Hst. destruct (LM_wr _ _ HLM) as (_ & _ & _ & _ & _ & _ & _ & Wsh).
  pose proof f6_sha_range as (R1 & R2). unfold SB, HIMEM_BEG, B_IMG_END, FS_SIZE in *.
  open_ls Hst l. subst.
  wp_a2u [0x431800]. rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Wsh | lia | cbn; lia]|].
  eapply exit_blk; [ | reflexivity | eapply same_except_trans; [exact Hse | same_ex]].
  apply LM_store; [exact HLM | lia | cbn; lia |]. intros x Hx. cbn in Hx. unfold FPI, inr in *. lia.
Qed.

Lemma err_exit1 : forall l M' wr, LM M' wr -> lstable l -> reach BSEGS rom (W 0x4317bc) l M' Post.
Proof.
  intros l M' wr HLM Hst. destruct (LM_wr _ _ HLM) as (_ & _ & _ & _ & _ & _ & Wsd & Wsh).
  pose proof f6_sha_range as (R1 & R2). destruct HFB6 as (A1 & A2 & A3). unfold SB, HIMEM_BEG, HIMEM_END, B_IMG_END, FS_SIZE in *.
  pose proof Hst as Hst'. open_ls Hst l. subst.
  wp_a2u [0x4317f4; 0x4318c4]. rewrite ?addi_W.
  change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
  change (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613.
  change (bv_unsigned (Z_to_bv 64 (-4))) with 18446744073709551612.
  rewrite ?(Wu (FB6 + 2320)) by lia.
  split; [eapply wr_ok_store; [exact Wsd | lia | cbn; lia]|].
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact Wsd]; solve_grows | lia | cbn; lia]|].
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact Wsd]; solve_grows | lia | cbn; lia]|].
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact Wsh]; solve_grows | lia | cbn; lia]|].
  eapply err_exit2; [ | prove_ls Hse].
  repeat (apply LM_store; [ | lia | cbn; lia | intros x Hx; cbn in Hx; unfold FPI, inr in *; lia]). exact HLM.
Qed.

Lemma pk_al : pk mod 8 = 0.
Proof.
  pose proof nums as (_ & _ & _ & _ & _ & _ & _ & N8 & _). unfold pk.
  replace (FB6 + 2208) with (FB6 + 276 * 8) by lia. rewrite Z.mod_add by lia. exact N8.
Qed.

(* [comment removed for export] *)
Lemma bufsize_keep : forall M' M'' v, unch M' M'' (FR_wm fs L out 16 pk) ->
  cell BSEGS M' (FB6 + 2304) 4 v -> cell BSEGS M'' (FB6 + 2304) 4 v.
Proof.
  intros M' M'' v HU HC.
  pose proof Hsep as (_ & S2 & _ & _ & S5 & _ & S7 & _). pose proof ring_sha_range as (R1 & R2).
  destruct HFB6 as (_ & A2 & A3). destruct Hfs as (F1 & F2 & _).
  eapply cell_unch; [exact HU | unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia | (cbn; unfold HIMEM_END in *; lia) | | exact HC].
  clear - S2 S5 S7 R1 R2 A2 A3 F1 F2.
  intros x Hx HF. cbn in Hx. unfold FR_wm, ring_FP, pk, inr, SB, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END in *. lia.
Qed.

(* [comment removed for export] *)
Lemma put_call : forall l M' wr (val : word), LM M' wr -> length l = 32%nat ->
  rget l 2 = W L -> rget l 4 = W TP -> rget l 10 = W pk -> rget l 11 = val -> rget l 12 = W 1 ->
  (forall l' M'' wr', length l' = 32%nat -> same_except KSC l l' -> LM M'' wr' ->
     reach BSEGS rom (v_jalr (rget l 1) 0) l' M'' Post) ->
  reach BSEGS rom (W 0x273608) l M' Post.
Proof.
  intros l M' wr val HLM Hl H2 H4 H10 H11 H12 Kc.
  destruct (LM_rt _ _ HLM) as (Hrt' & Hrtx' & Huar' & Hgot' & _).
  destruct (LM_f6 _ _ HLM) as (Hshpk & _). destruct (LM_wr _ _ HLM) as (Hrw & WL & _ & _ & Wpk & _).
  pose proof HLM as (HP & Hwr & ((h & Hh & Chint) & Hz) & _).
  eapply (put_byte_cps RTX RTXD RSEP fs IF rom Post M' pk out wr 16 sb L h eb val l);
    [ exact Hrt' | exact Hrtx' | exact Huar' | exact (proj1 Hgot') | exact Hfs | exact Hh | exact Chint
    | exact Hz | exact Hrw | exact HP | apply LM_wf; exact Hwr | exact pk_al | lia | exact Hshpk | exact Wpk | exact stk_facts
    | eapply wr_ok_sub; [exact WL | lia | lia] | exact (out_facts _ _ HLM) | exact sep_pb | exact FRwm_rtxd | exact Hrsep
    | exact Hl | exact H2 | exact H4 | exact H10 | exact H11 | exact H12 | ].
  intros l' M'' wr' Hl' Hse' Hy Hn HP' Hri' HU' HG'.
  apply (Kc l' M'' wr' Hl' Hse').
  eapply LM_next; [exact HLM | exact HU' | exact HG' | exact HP' | | exact Hri'].
  assert (Hdec : pb_ok wr 16 \/ ~ pb_ok wr 16) by (unfold pb_ok; lia).
  destruct Hdec as [Hd|Hd]; [rewrite (Hy Hd); unfold pb_ok in Hd; lia | rewrite (Hn Hd); lia].
Qed.

(* [comment removed for export] *)
Lemma wm_call : forall l M' wr src n, LM M' wr -> length l = 32%nat ->
  rget l 2 = W L -> rget l 4 = W TP -> rget l 10 = W pk -> rget l 11 = W src -> rget l 12 = W n ->
  0 <= n < 2 ^ 62 -> memrange src n /\ addr_ok M' src n /\ (0 < n -> shw_ok M' src n) /\ rd_ok M' src n ->
  wm_sep fs L pk out 16 src n ->
  (forall l' M'' wr', length l' = 32%nat -> same_except KSC l l' -> LM M'' wr' ->
     (forall v, cell BSEGS M' (FB6 + 2304) 4 v -> cell BSEGS M'' (FB6 + 2304) 4 v) ->
     reach BSEGS rom (v_jalr (rget l 1) 0) l' M'' Post) ->
  reach BSEGS rom (W 0x273870) l M' Post.
Proof.
  intros l M' wr src n HLM Hl H2 H4 H10 H11 H12 Hn Hsrc Hsp Kc.
  destruct (LM_rt _ _ HLM) as (Hrt' & Hrtx' & Huar' & Hgot' & _).
  destruct (LM_f6 _ _ HLM) as (Hshpk & _). destruct (LM_wr _ _ HLM) as (Hrw & WL & _ & _ & Wpk & _).
  pose proof HLM as (HP & Hwr & ((h & Hh & Chint) & Hz) & _).
  eapply (wmemcpy_cps RTX RTXD RSEP fs IF rom Post M' pk out wr 16 sb L src n h eb l);
    [ exact Hrt' | exact Hrtx' | exact Huar' | exact (proj2 Hgot') | exact Hfs | exact Hh | exact Chint
    | exact Hz | exact Hrw | exact HP | apply LM_wf; exact Hwr | exact pk_al | lia | exact Hshpk | exact Wpk | exact stk_facts
    | eapply wr_ok_sub; [exact WL | lia | lia] | exact Hn | exact Hsrc | exact (out_facts _ _ HLM) | exact Hsp
    | exact FRwm_rtxd | exact Hrsep
    | exact Hl | exact H2 | exact H4 | exact H10 | exact H11 | exact H12 | ].
  intros l' M'' wr' Hl' Hse' Hy Hno HP' Hri' HU' HG'.
  apply (Kc l' M'' wr' Hl' Hse'); [|intros v Hv; eapply bufsize_keep; [exact HU' | exact Hv]].
  eapply LM_next; [exact HLM | exact HU' | exact HG' | exact HP' | | exact Hri'].
  assert (Hdec : wm_ok wr 16 n \/ ~ wm_ok wr 16 n) by (unfold wm_ok; lia).
  destruct Hdec as [Hd|Hd]; [rewrite (Hy Hd); unfold wm_ok in Hd; lia | rewrite (Hno Hd); lia].
Qed.

Ltac fix_jalr target :=
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) ?i) _ _ _ =>
    replace (v_jalr (Z_to_bv 64 x) i) with (W target) by reflexivity end.

Section Label.
(* [comment removed for export] *)
Variable k : Z.
Hypothesis Hk : 0 <= k <= len.
Hypothesis Khead : forall k' l M' wr', k < k' <= len -> LM M' wr' -> lstable l -> rget l 25 = W XNB ->
  rget l 26 = W (b + k') -> reach BSEGS rom (W 0x431520) l M' Post.

(* [comment removed for export] *)
Lemma final_blk : forall l M' wr, LM M' wr -> lstable l -> reach BSEGS rom (W 0x431798) l M' Post.
Proof.
  intros l M' wr HLM Hst. open_ls Hst l. subst.
  wp_a2u (@nil Z).
  fix_jalr 0x273608.
  eapply (put_call _ M' wr (W 0)); [exact HLM | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M'' wr' Hl' Hse' HLM'. cbn [rget lget].
  fix_jalr 0x4317ac.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  wp_a2u [0x431800].
  eapply exit_blk; [exact HLM' | reflexivity | eapply same_except_trans; [exact Hse | same_ex]].
Qed.

(* [comment removed for export] *)
Lemma dot_blk : forall l M' wr r, LM M' wr -> lstable l -> rget l 25 = W XNB -> rget l 27 = W (b + r) ->
  k <= r < len -> reach BSEGS rom (W 0x431768) l M' Post.
Proof.
  intros l M' wr r HLM Hst H25 H27 Hr. pose proof Hb as (Hb1 & Hb2). pose proof Hlen as (Hl1 & Hl2).
  open_ls Hst l. subst.
  wp_a2u (@nil Z).
  fix_jalr 0x273608.
  eapply (put_call _ M' wr (W 46)); [exact HLM | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l' M'' wr' Hl' Hse' HLM'. cbn [rget lget].
  fix_jalr 0x43177c.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  wp_a2u [0x431520; 0x4318c4]. rewrite ?addi_W.
  change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615. rewrite ?(Wu (b + r)) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  eapply (Khead (r + 1)); [lia | exact HLM' | prove_ls Hse | reflexivity | cbn [rget lget]; f_equal; lia].
Qed.

(* [comment removed for export] *)
Lemma after_plain : forall l M' wr tmpv r, LM M' wr -> lstable l -> rget l 25 = W XNB -> rget l 27 = W tmpv ->
  tmpv = 0 \/ (tmpv = b + r /\ k <= r < len) -> reach BSEGS rom (W 0x431588) l M' Post.
Proof.
  intros l M' wr tmpv r HLM Hst H25 H27 Htmp. pose proof Hb as (Hb1 & Hb2). pose proof Hlen as (Hl1 & Hl2).
  pose proof Hst as Hst'. open_ls Hst l. subst.
  wp_a2u [0x431798; 0x431768].
  split; intros Hbr.
  - eapply final_blk; [exact HLM | exact Hst'].
  - destruct Htmp as [->|[-> Hr]]; [exfalso; apply Hbr; reflexivity|].
    eapply (dot_blk _ _ wr r); [exact HLM | exact Hst' | reflexivity | reflexivity | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma after_puny : forall l M' wr tmpv r, LM M' wr -> lstable l -> rget l 27 = W tmpv ->
  tmpv = 0 \/ (tmpv = b + r /\ k <= r < len) -> reach BSEGS rom (W 0x431758) l M' Post.
Proof.
  intros l M' wr tmpv r HLM Hst H27 Htmp. pose proof Hb as (Hb1 & Hb2). pose proof Hlen as (Hl1 & Hl2).
  destruct (LM_wr _ _ HLM) as (_ & _ & _ & _ & _ & _ & _ & Wsh).
  pose proof f6_sha_range as (R1 & R2). unfold SB, HIMEM_BEG, B_IMG_END, FS_SIZE in *.
  destruct HL as (L1 & L2 & _). unfold B_IMG_END in *.
  open_ls Hst l. subst.
  wp_a2u [0x431798; 0x431768]. rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Wsh | lia | cbn; lia]|].
  match goal with |- exists v, load_ok _ ?Mx _ _ _ /\ _ => assert (HLM2 : LM Mx wr) end.
  { apply LM_store; [exact HLM | lia | cbn; lia |]. intros x Hx. cbn in Hx. unfold FPI, inr in *. lia. }
  match goal with |- exists v, load_ok _ ?Mx _ _ _ /\ _ => set (M2 := Mx) in * end. clearbody M2.
  pose proof HLM2 as (_ & _ & _ & (_ & _ & _ & C48' & _) & _).
  eexists. split; [apply load_cell8; exact C48'|].
  split; intros Hbr.
  - eapply final_blk; [exact HLM2 | prove_ls Hse].
  - destruct Htmp as [->|[-> Hr]]; [exfalso; apply Hbr; reflexivity|].
    eapply (dot_blk _ _ wr r); [exact HLM2 | prove_ls Hse | reflexivity | reflexivity | exact Hr].
Qed.

Lemma memrange_sub0 : forall a n a' n', memrange a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> memrange a' n'.
Proof. intros a n a' n' Hm H1 H2 H3. clear - Hm H1 H2 H3. destruct Hm as [Hn Hm]. split; [exact H2|]. lia. Qed.

(* [comment removed for export] *)
Lemma str_src : forall M' wr t, LM M' wr -> k <= t <= len ->
  memrange (b + k) (t - k) /\ addr_ok M' (b + k) (t - k) /\ (0 < t - k -> shw_ok M' (b + k) (t - k)) /\ rd_ok M' (b + k) (t - k).
Proof.
  intros M' wr t HLM Ht. destruct (LM_str _ _ HLM) as (HB' & Ba & Bs). destruct Hbsh as (Bm & _). destruct Hlen as (Hl1 & Hl2).
  split; [eapply memrange_sub0; [exact Bm | lia | lia | lia]|].
  split; [eapply addr_ok_sub; [exact Ba | lia | lia]|].
  split; [intros Hp; eapply shw_ok_sub; [exact Bs | lia | lia | lia]|].
  eapply rd_ok_sub; [eapply bytes_at_rd_ok; exact HB' | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma plain_label : forall l M' wr tmpv r, LM M' wr -> lstable l -> k <= r <= len -> rget l 25 = W XNB ->
  rget l 26 = W (b + k) -> rget l 20 = W (r - k) -> rget l 27 = W tmpv ->
  tmpv = 0 \/ (tmpv = b + r /\ k <= r < len) ->
  reach BSEGS rom (W 0x431568) l M' Post.
Proof.
  intros l M' wr tmpv r HLM Hst Hr H25 H26 H20 H27 Htmp. destruct Hlen as (Hl1 & Hl2).
  open_ls Hst l. subst.
  wp_a2u (@nil Z).
  fix_jalr 0x273870.
  eapply (wm_call _ M' wr (b + k) (r - k)); [exact HLM | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | lia | eapply str_src; [exact HLM | lia] | apply sep_wm_b; lia |].
  intros l' M'' wr' Hl' Hse' HLM' _. cbn [rget lget].
  fix_jalr 0x43157c.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  wp_a2u [0x431588].
  eapply (after_plain _ _ wr' tmpv r); [exact HLM' | prove_ls Hse | reflexivity | reflexivity | exact Htmp].
Qed.

Lemma load1_val : forall (Mx : mem) a u, Mx (W a) = Some (Z_to_bv 8 u) -> 0 <= u < 256 -> load_ok BSEGS Mx (W a) 1 (W u).
Proof.
  intros Mx a u H Hu. clear - H Hu. exists [Z_to_bv 8 u]. split; [cbn [rdn]; rewrite H; reflexivity|].
  rewrite bytes_le_1. rewrite Z_to_bv_unsigned. rewrite Wu by lia. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma byte_keep : forall (Mx : mem) a b0 bs v, Mx (W a) = Some v -> 0 <= a < 2 ^ 64 -> 0 <= b0 ->
  b0 + Z.of_nat (length bs) < 2 ^ 64 -> (a < b0 \/ b0 + Z.of_nat (length bs) <= a) ->
  (wbytes Mx (W b0) bs) (W a) = Some v.
Proof.
  intros Mx a b0 bs v H Ha Hb0 Hbn Hd. clear - H Ha Hb0 Hbn Hd. rewrite wbytes_out; [exact H | exact Hb0 | exact Hbn |].
  unfold inr. rewrite Wu by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma seed_src : forall M' wr u, LM M' wr -> M' (W (sha FB6 + 290)) = Some (Z_to_bv 8 6) -> 0 <= u <= 6 ->
  memrange (FB6 + 2320) u /\ addr_ok M' (FB6 + 2320) u /\ (0 < u -> shw_ok M' (FB6 + 2320) u) /\ rd_ok M' (FB6 + 2320) u.
Proof.
  intros M' wr u HLM H6 Hu. destruct (LM_f6 _ _ HLM) as (_ & _ & _ & Hrd). destruct (LM_wr _ _ HLM) as (_ & _ & _ & _ & _ & _ & Wsd & _).
  pose proof nums as (_ & _ & _ & _ & _ & _ & _ & N8 & _). destruct HFB6 as (A1 & A2 & A3).
  assert (Hs8 : sha FB6 mod 8 = 0).
  { clear - A1. unfold sha, SB. pose proof (Z.div_mod FB6 64 ltac:(lia)) as Hd6. rewrite A1 in Hd6.
    replace FB6 with (0 + (8 * (FB6 / 64)) * 8) by lia. rewrite Z.div_add by lia.
    replace (0 / 8 + 8 * (FB6 / 64) + 2147450880) with (0 + (FB6 / 64 + 268431360) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  assert (Esh : sha (FB6 + 2320) = sha FB6 + 290) by (replace (FB6 + 2320) with (FB6 + 8 * 290) by lia; apply sha_add8).
  unfold HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *.
  split; [split; [lia | unfold LOMEM_END, HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *; lia]|].
  split; [eapply addr_ok_sub; [apply (addr_ok_partial M' (FB6 + 2320) 6 (Z_to_bv 8 6)); [lia | | lia | rewrite Esh; exact H6 | reflexivity] | lia | lia]|].
  { replace (FB6 + 2320) with (FB6 + 290 * 8) by lia. rewrite Z.mod_add by lia. exact N8. }
  split.
  - intros Hp. unfold shw_ok. eapply rd_ok_sub; [exact Hrd | |].
    + rewrite Esh. pose proof (Z.div_mod (sha FB6) 8 ltac:(lia)) as Hd. rewrite Hs8 in Hd.
      replace (sha FB6 + 290) with (2 + (sha FB6 / 8 + 36) * 8) by lia. rewrite Z.div_add by lia. rewrite (Z.div_small 2) by lia. lia.
    + assert (E2 : sha (FB6 + 2320 + u - 1) = sha FB6 + 290).
      { unfold sha. pose proof (Z.div_mod FB6 8 ltac:(lia)) as Hd. rewrite N8 in Hd.
        replace (FB6 + 2320 + u - 1) with ((u - 1) + (FB6 / 8 + 290) * 8) by lia. rewrite Z.div_add by lia.
        rewrite (Z.div_small (u - 1)) by lia. lia. }
      rewrite E2, Esh. pose proof (Z.div_mod (sha FB6) 8 ltac:(lia)) as Hd. rewrite Hs8 in Hd.
      replace (sha FB6 + 290) with (2 + (sha FB6 / 8 + 36) * 8) by lia. rewrite Z.div_add by lia. rewrite (Z.div_small 2) by lia. lia.
  - eapply rd_ok_sub; [apply (wr_ok_rd_ok M' (FB6 + 2320) 6 Wsd); unfold B_IMG_END; lia | lia | lia].
Qed.

(* [comment removed for export] *)
Section Utf.
Variables (w : Z) (tmpv r : Z).
Hypothesis Hw : 0 < w <= 512.
Hypothesis Htmp : tmpv = 0 \/ (tmpv = b + r /\ k <= r < len).

Section UtfIter.
Variable i : Z.
Hypothesis Hi : 0 <= i < w.
Hypothesis Kf1 : forall l M' wr, i + 1 < w -> LM M' wr -> lstable l -> cell BSEGS M' (FB6 + 2304) 4 (W w) ->
  rget l 27 = W tmpv -> rget l 20 = W (i + 1) -> rget l 26 = W (FB6 + 32 + 4 * (i + 1)) ->
  rget l 25 = W (FB6 + 32 + 4 * (i + 1)) ->
  reach BSEGS rom (W 0x4315d0) l M' Post.

(* [comment removed for export] *)
Lemma utf_put : forall l M' wr u, LM M' wr -> lstable l -> 1 <= u <= 4 -> M' (W (sha FB6 + 290)) = Some (Z_to_bv 8 6) ->
  cell BSEGS M' (FB6 + 2304) 4 (W w) ->
  rget l 12 = W u -> rget l 27 = W tmpv -> rget l 20 = W i ->
  rget l 26 = W (FB6 + 32 + 4 * i) -> rget l 25 = W (FB6 + 32 + 4 * i) ->
  reach BSEGS rom (W 0x43170c) l M' Post.
Proof.
  intros l M' wr u HLM Hst Hu H6 Cw H12 H27 H20 H26 H25.
  destruct HFB6 as (A1 & A2 & A3). pose proof f6_sha_range as (R1 & R2). unfold SB, HIMEM_BEG, HIMEM_END, B_IMG_END, FS_SIZE in *.
  open_ls Hst l. subst.
  wp_a2u (@nil Z).
  fix_jalr 0x273870.
  eapply (wm_call _ M' wr (FB6 + 2320) u); [exact HLM | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | lia | eapply seed_src; [exact HLM | exact H6 | lia] | apply sep_wm_seed; lia |].
  intros l' M'' wr' Hl' Hse' HLM' Hkeep. cbn [rget lget].
  fix_jalr 0x43171c.
  pose proof (Hkeep _ Cw) as Cw'.
  destruct (LM_wr _ _ HLM') as (_ & _ & _ & _ & _ & _ & _ & Wsh').
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  wp_a2u [0x4315d0; 0x431758]. rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Wsh' | lia | cbn; lia]|].
  match goal with |- exists v, load_ok _ ?Mx _ _ _ /\ _ => assert (HLM3 : LM Mx wr') end.
  { apply LM_store; [exact HLM' | lia | cbn; lia |]. intros x Hx. cbn in Hx. unfold FPI, inr in *. lia. }
  match goal with |- exists v, load_ok _ ?Mx _ _ _ /\ _ => assert (Cw3 : cell BSEGS Mx (FB6 + 2304) 4 (W w)) end.
  { apply cell_store_other; [lia | lia | lia | cbn; lia | cbn; lia | exact Cw']. }
  match goal with |- exists v, load_ok _ ?Mx _ _ _ /\ _ => set (M3 := Mx) in * end. clearbody M3.
  eexists. split; [apply load_cell; [exact Cw3 | lia]|].
  rewrite (Wu w) by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small w) by lia.
  rewrite ?(Wu (i + 1)), ?(Wu w) by lia.
  split; intros Hbr.
  - eapply Kf1; [lia | exact HLM3 | prove_ls Hse | exact Cw3 | reflexivity | ..]; cbn [rget lget]; f_equal; lia.
  - eapply (after_puny _ _ wr' tmpv r); [exact HLM3 | prove_ls Hse | reflexivity | exact Htmp].
Qed.

(* [comment removed for export] *)
Lemma utf_enc : forall l M' wr, LM M' wr -> lstable l -> M' (W (sha FB6 + 290)) = Some (Z_to_bv 8 6) ->
  cell BSEGS M' (FB6 + 2304) 4 (W w) ->
  rget l 27 = W tmpv -> rget l 20 = W i -> rget l 26 = W (FB6 + 32 + 4 * i) -> rget l 25 = W (FB6 + 32 + 4 * i) ->
  reach BSEGS rom (W 0x4315f0) l M' Post.
Proof.
  intros l M' wr HLM Hst H6 Cw H27 H20 H26 H25.
  destruct (LM_wr _ _ HLM) as (_ & _ & _ & Wbuf & _ & _ & Wsd & _).
  destruct HFB6 as (A1 & A2 & A3). pose proof f6_sha_range as (R1 & R2). destruct HL as (L1 & L2 & _).
  unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END, FS_SIZE in *.
  open_ls Hst l. subst.
  wp_a2u [0x43170c; 0x4317bc; 0x4318c4].
  assert (exists v, load_ok BSEGS M' (W (FB6 + 32 + 4 * i)) 4 v) as [v Hv].
  { eapply load_rd; [apply (wr_ok_rd_ok M' (FB6 + 32) 2048 Wbuf); unfold B_IMG_END; lia | lia..]. }
  exists v. split; [exact Hv|]. clear Hv. rewrite ?addi_W.
  change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
  change (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613.
  change (bv_unsigned (Z_to_bv 64 (-4))) with 18446744073709551612.
  change (bv_unsigned (Z_to_bv 64 (-5))) with 18446744073709551611.
  rewrite ?(Wu (FB6 + 2320)) by lia.
  repeat (first [ split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact Wsd]; solve_grows | lia | cbn; lia]|]
                | split; intros ?Hbr; try (exfalso; lia) ]).
  - eapply err_exit1; [exact HLM | prove_ls Hse].
  - match goal with |- reach _ _ _ _ ?Mx _ =>
      assert (HLMx : LM Mx wr) by (repeat (apply LM_store; [ | lia | cbn; lia | intros x Hx; cbn in Hx; unfold FPI, inr in *; lia]); exact HLM);
      assert (H6x : Mx (W (sha FB6 + 290)) = Some (Z_to_bv 8 6)) by (repeat (apply byte_keep; [ | lia | lia | cbn; lia | cbn; lia]); exact H6);
      assert (Cwx : cell BSEGS Mx (FB6 + 2304) 4 (W w)) by (repeat (apply cell_store_other; [lia | lia | lia | cbn; lia | cbn; lia | ]); exact Cw);
      set (M2 := Mx) in *; clearbody M2 end.
    eapply (utf_put _ M2 wr 4); [exact HLMx | prove_ls Hse | lia | exact H6x | exact Cwx | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
  - match goal with |- reach _ _ _ _ ?Mx _ =>
      assert (HLMx : LM Mx wr) by (repeat (apply LM_store; [ | lia | cbn; lia | intros x Hx; cbn in Hx; unfold FPI, inr in *; lia]); exact HLM);
      assert (H6x : Mx (W (sha FB6 + 290)) = Some (Z_to_bv 8 6)) by (repeat (apply byte_keep; [ | lia | lia | cbn; lia | cbn; lia]); exact H6);
      assert (Cwx : cell BSEGS Mx (FB6 + 2304) 4 (W w)) by (repeat (apply cell_store_other; [lia | lia | lia | cbn; lia | cbn; lia | ]); exact Cw);
      set (M2 := Mx) in *; clearbody M2 end.
    eapply (utf_put _ M2 wr 3); [exact HLMx | prove_ls Hse | lia | exact H6x | exact Cwx | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
  - match goal with |- reach _ _ _ _ ?Mx _ =>
      assert (HLMx : LM Mx wr) by (repeat (apply LM_store; [ | lia | cbn; lia | intros x Hx; cbn in Hx; unfold FPI, inr in *; lia]); exact HLM);
      assert (H6x : Mx (W (sha FB6 + 290)) = Some (Z_to_bv 8 6)) by (repeat (apply byte_keep; [ | lia | lia | cbn; lia | cbn; lia]); exact H6);
      assert (Cwx : cell BSEGS Mx (FB6 + 2304) 4 (W w)) by (repeat (apply cell_store_other; [lia | lia | lia | cbn; lia | cbn; lia | ]); exact Cw);
      set (M2 := Mx) in *; clearbody M2 end.
    eapply (utf_put _ M2 wr 2); [exact HLMx | prove_ls Hse | lia | exact H6x | exact Cwx | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
  - match goal with |- reach _ _ _ _ ?Mx _ =>
      assert (HLMx : LM Mx wr) by (repeat (apply LM_store; [ | lia | cbn; lia | intros x Hx; cbn in Hx; unfold FPI, inr in *; lia]); exact HLM);
      assert (H6x : Mx (W (sha FB6 + 290)) = Some (Z_to_bv 8 6)) by (repeat (apply byte_keep; [ | lia | lia | cbn; lia | cbn; lia]); exact H6);
      assert (Cwx : cell BSEGS Mx (FB6 + 2304) 4 (W w)) by (repeat (apply cell_store_other; [lia | lia | lia | cbn; lia | cbn; lia | ]); exact Cw);
      set (M2 := Mx) in *; clearbody M2 end.
    eapply (utf_put _ M2 wr 1); [exact HLMx | prove_ls Hse | lia | exact H6x | exact Cwx | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.
(* [comment removed for export] *)
Lemma utf_cp : forall l M' wr, LM M' wr -> lstable l -> cell BSEGS M' (FB6 + 2304) 4 (W w) ->
  rget l 27 = W tmpv -> rget l 20 = W i -> rget l 26 = W (FB6 + 32 + 4 * i) -> rget l 25 = W (FB6 + 32 + 4 * i) ->
  reach BSEGS rom (W 0x4315d0) l M' Post.
Proof.
  intros l M' wr HLM Hst Cw H27 H20 H26 H25.
  destruct (LM_wr _ _ HLM) as (_ & _ & _ & _ & _ & _ & _ & Wsh).
  destruct HFB6 as (A1 & A2 & A3). pose proof f6_sha_range as (R1 & R2).
  unfold SB, HIMEM_BEG, HIMEM_END, B_IMG_END, FS_SIZE in *.
  open_ls Hst l. subst.
  wp_a2u [0x4315f0; 0x4318c8; 0x4318c4]. rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Wsh | lia | cbn; lia]|].
  rewrite ?(Wu i), ?(Wu 512) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  match goal with |- exists v, load_ok _ ?Mx _ _ _ /\ _ =>
    assert (HLM2 : LM Mx wr) by (apply LM_store; [exact HLM | lia | cbn; lia | intros x Hx; cbn in Hx; unfold FPI, inr in *; lia]);
    assert (H62 : Mx (W (sha FB6 + 290)) = Some (Z_to_bv 8 6))
      by (change (word_to_le_bytes 1 (Z_to_bv 64 6)) with [Z_to_bv 8 6]; cbn [wbytes]; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity);
    assert (Cw2 : cell BSEGS Mx (FB6 + 2304) 4 (W w)) by (apply cell_store_other; [lia | lia | lia | cbn; lia | cbn; lia | exact Cw]);
    set (M2 := Mx) in *; clearbody M2 end.
  destruct (LM_f6 _ _ HLM2) as (_ & Hbok & _ & _).
  destruct (sh_load_k BSEGS M2 (FB6 + 32 + 4 * i) 4 ltac:(eapply addr_ok_sub; [exact Hbok | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound (FB6 + 32 + 4 * i) 8 ltac:(lia)) as Hm8.
  rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?addi_W.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  split; [intros Hnz; split; [intros Hbad; exfalso; lia | intros _] | intros _];
    (eapply utf_enc; [exact HLM2 | prove_ls Hse | exact H62 | exact Cw2 | reflexivity | reflexivity | reflexivity | reflexivity]).
Qed.

End UtfIter.

Lemma utf_loop : forall m i l M' wr, w - i = Z.of_nat m -> 0 <= i < w -> LM M' wr -> lstable l ->
  cell BSEGS M' (FB6 + 2304) 4 (W w) ->
  rget l 27 = W tmpv -> rget l 20 = W i -> rget l 26 = W (FB6 + 32 + 4 * i) -> rget l 25 = W (FB6 + 32 + 4 * i) ->
  reach BSEGS rom (W 0x4315d0) l M' Post.
Proof.
  induction m as [m IH] using lt_wf_ind; intros i l M' wr Hm Hi HLM Hst Cw H27 H20 H26 H25.
  apply (utf_cp i Hi) with (wr := wr); try assumption.
  intros l2 M2 wr2 Hlt HLM2 Hst2 Cw2 H27' H20' H26' H25'.
  eapply (IH (Z.to_nat (w - (i + 1)))) with (i := i + 1); try eassumption; lia.
Qed.
End Utf.

Lemma dec_nums : (L <= SB \/ HIMEM_BEG <= L - 2400) /\ (FB6 + 32 + 4 * 512 <= L - 2400 \/ L <= FB6 + 32)
  /\ (FB6 + 2304 + 4 <= L - 2400 \/ L <= FB6 + 2304).
Proof. pose proof Hsep as (_ & S2 & _ & _ & _ & _ & _ & _ & _ & _ & S11). clear - S2 S11. lia. Qed.
(* [comment removed for export] *)
Lemma puny_label : forall l M' wr tmpv r, LM M' wr -> lstable l -> k + 4 <= r <= len ->
  rget l 26 = W (b + k) -> rget l 20 = W (r - k) -> rget l 27 = W tmpv ->
  tmpv = 0 \/ (tmpv = b + r /\ k <= r < len) ->
  reach BSEGS rom (W 0x431590) l M' Post.
Proof.
  intros l M' wr tmpv r HLM Hst Hr H26 H20 H27 Htmp.
  destruct (LM_wr _ _ HLM) as (_ & _ & _ & _ & _ & Wq & _ & Wsh).
  destruct HFB6 as (A1 & A2 & A3). pose proof f6_sha_range as (R1 & R2). destruct Hlen as (Hl1 & Hl2).
  pose proof Hb as (Hb1 & Hb2).
  pose proof nums as (_ & _ & _ & _ & _ & _ & _ & N8 & _).
  assert (N4 : FB6 mod 4 = 0).
  { pose proof (Z.div_mod FB6 64 ltac:(lia)) as Hd. rewrite A1 in Hd. rewrite Hd.
    replace (64 * (FB6 / 64) + 0) with (0 + (16 * (FB6 / 64)) * 4) by lia. rewrite Z.mod_add by lia. reflexivity. }
  unfold SB, HIMEM_BEG, HIMEM_END, B_IMG_END, FS_SIZE in A2, A3, R1, R2.
  open_ls Hst l. subst.
  wp_a2u [0x4315a4]. rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Wsh | lia | cbn; lia]|].
  split; [eapply wr_ok_store; [eapply wr_ok_grows; [apply wbytes_grows | exact Wq] | lia | cbn; lia]|].
  match goal with |- reach _ _ _ _ ?Mx _ =>
    assert (HLM2 : LM Mx wr) by (repeat (apply LM_store; [ | lia | cbn; lia | intros x Hx; cbn in Hx; unfold FPI, inr in *; lia]); exact HLM);
    assert (H42 : Mx (W (sha FB6 + 288)) = Some (Z_to_bv 8 4))
      by (apply byte_keep; [ | lia | lia | cbn; lia | cbn; lia];
          change (word_to_le_bytes 1 (Z_to_bv 64 4)) with [Z_to_bv 8 4]; cbn [wbytes]; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity);
    assert (Cq : cell BSEGS Mx (FB6 + 2304) 4 (W 512)) by (apply cell_store_same; cbn; lia);
    set (M2 := Mx) in *; clearbody M2 end.
  destruct (LM_rt _ _ HLM2) as (Hrt2 & _). destruct (LM_f6 _ _ HLM2) as (_ & Hbok & Hbsw & _).
  destruct (LM_wr _ _ HLM2) as (_ & WL2 & _ & Wbuf2 & _ & Wq2 & _ & _).
  pose proof HLM2 as (_ & _ & _ & (_ & _ & _ & _ & C56) & _).
  destruct (str_src M2 wr r HLM2 ltac:(lia)) as (Sm & Sa & _ & Sr).
  destruct dec_nums as (D1 & D2 & D3). destruct stk_facts as (K1 & K2 & _). destruct HL as (L1 & L2 & _).
  unfold B_IMG_END in L1, K1.
  wp_a2u [0x4318c4]. rewrite ?addi_W. rewrite ?(Wu 4), ?(Wu (b + k + 4)) by lia.
  split; intros Hbr; [exfalso; lia|]. clear Hbr.
  eexists. split; [apply load_cell8; exact C56|].
  eapply (decode_cps rom Post M2 L (b + k + 4) (r - k + -4) (FB6 + 32) (FB6 + 2304) 512);
    [ exact Hrt2 | lia | eapply memrange_sub0; [exact Sm | lia | lia | lia]
    | eapply addr_ok_sub; [exact Sa | lia | lia] | eapply rd_ok_sub; [exact Sr | lia | lia] | lia | exact Cq
    | unfold B_IMG_END; lia | exact D1 | eapply wr_ok_sub; [exact WL2 | lia | lia]
    | unfold B_IMG_END; lia | split; [lia | unfold LOMEM_END, HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *; lia] | exact Hbok | intros _; exact Hbsw | exact Wbuf2
    | unfold B_IMG_END; lia | split; [lia | unfold LOMEM_END, HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *; lia]
    | apply (addr_ok_partial M2 (FB6 + 2304) 4 (Z_to_bv 8 4)); [lia | | lia | | reflexivity]
    | exact Wq2 | exact D2 | exact D3
    | right; lia
    | replace (FB6 + 32) with (FB6 + 8 * 4) by lia; rewrite Z.mod_add by lia; exact N4
    | replace (FB6 + 2304) with (FB6 + 576 * 4) by lia; rewrite Z.mod_add by lia; exact N4
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
  { replace (FB6 + 2304) with (FB6 + 288 * 8) by lia. rewrite Z.mod_add by lia. exact N8. }
  { replace (FB6 + 2304) with (FB6 + 8 * 288) by lia. rewrite sha_add8. exact H42. }
  intros l' M3 Hl' Hse' Ha0 Hwc HU' HG'. cbn [rget lget].
  fix_jalr 0x4315b8.
  assert (HLM3 : LM M3 wr).
  { eapply LM_frame; [exact HLM2 | exact HU' | exact HG' |].
    clear. intros x Hx. unfold dec_FP, FPI, inr in *. lia. }
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  destruct Ha0 as [Ea0|Ea0]; match type of Ea0 with ?x = _ => subst x end.
  - (* [comment removed for export] *)
    wp_a2u [0x4317f4; 0x4315bc]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    split; intros Hbr; [clear Hbr | exfalso; lia].
    eapply err_exit2; [exact HLM3 | prove_ls Hse].
  - destruct (Hwc eq_refl) as (wv & Hwv & Cw). clear Hwc.
    pose proof HLM3 as (_ & _ & _ & (_ & _ & _ & _ & C56') & _).
    wp_a2u [0x4317f4; 0x4315d0; 0x431758]. change (bv_unsigned (Z_to_bv 64 1)) with 1.
    split; intros Hbr; [exfalso; lia|]. clear Hbr.
    rewrite ?addi_W.
    eexists. split; [apply load_cell; [exact Cw | lia]|].
    rewrite (Wu wv) by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small wv) by lia.
    rewrite lw_W by lia. rewrite ?(Wu wv) by lia.
    split; intros Hbr.
    + eapply (after_puny _ _ wr tmpv r); [exact HLM3 | prove_ls Hse | reflexivity | exact Htmp].
    + eexists. split; [apply load_cell8; exact C56'|].
      eapply (utf_loop wv tmpv r ltac:(lia) Htmp (Z.to_nat (wv - 0)) 0);
        [ lia | lia | exact HLM3 | prove_ls Hse | exact Cw | reflexivity | ..]; cbn [rget lget]; f_equal; lia.
Qed.

Lemma ic_nums : (L <= SB \/ HIMEM_BEG <= L - 2224) /\ (L <= SB \/ HIMEM_BEG <= L - 2256)
  /\ (b + N <= L - 2224 \/ L <= b) /\ (b + N <= L - 2256 \/ L <= b) /\ (XNB + 4 <= L - 2256 \/ L <= XNB).
Proof.
  pose proof Hsep as (_ & _ & _ & S4 & _ & _ & _ & _ & _ & _ & S11). destruct HL as (L1 & _).
  clear - S4 S11 L1. unfold XNB, B_IMG_END in *. lia.
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
  intros t Ht. clear - Ht Hslack Hk. assert ((b + t) / 8 <= (b + len) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma str_chk : forall M' wr t n, LM M' wr -> k <= t <= len -> 0 < n <= t - k + 1 ->
  memrange (b + k) n /\ addr_ok M' (b + k) n /\ shw_ok M' (b + k) n.
Proof.
  intros M' wr t n HLM Ht Hn. destruct (LM_str _ _ HLM) as (_ & Ba & Bs). destruct Hbsh as (Bm & _). destruct Hlen as (Hl1 & Hl2).
  split; [eapply memrange_sub0; [exact Bm | lia | lia | lia]|].
  split; [eapply addr_ok_sub; [exact Ba | lia | lia] | eapply shw_ok_sub; [exact Bs | lia | lia | lia]].
Qed.

(* [comment removed for export] *)
Lemma prefix_test : forall l M' wr tmpv, LM M' wr -> lstable l -> rget l 25 = W XNB ->
  rget l 26 = W (b + k) -> rget l 20 = W (r - k) -> rget l 27 = W tmpv ->
  tmpv = 0 \/ (tmpv = b + r /\ k <= r < len) ->
  reach BSEGS rom (W 0x431550) l M' Post.
Proof.
  intros l M' wr tmpv HLM Hst H25 H26 H20 H27 Htmp.
  destruct (LM_str _ _ HLM) as (HB' & _). destruct (LM_rt _ _ HLM) as (Hrt' & Hrtx' & _ & _ & Hxn').
  destruct (LM_xn _ _ HLM) as (Xa & Xs). destruct (LM_wr _ _ HLM) as (_ & WL & _).
  destruct ic_nums as (_ & I2 & _ & I4 & I5). destruct HL as (L1 & L2 & _). destruct Hlen as (Hl1 & Hl2).
  destruct (str_chk M' wr z (Z.min (z - k + 1) 4) HLM ltac:(lia) ltac:(lia)) as (Sm & Sa & Ss).
  open_ls Hst l. subst.
  wp_a2u (@nil Z). rewrite ?addi_W.
  fix_jalr 0x1a74e0.
  eapply (if_strncmp _ _ _ _ IF rom Post M' b N B k z XNB 4 XN L);
    [ exact Hrt' | exact Hrtx' | exact HB' | exact Hb | lia | lia | exact HBz | exact HBnz | lia | unfold XNB; lia
    | apply xn_loads; exact Hxn' | apply xn_nz | exact Sm | exact Sa | exact Ss
    | unfold XNB; split; [lia | left; unfold LOMEM_END; lia] | exact Xa | exact Xs
    | unfold B_IMG_END in *; lia | exact I2 | eapply wr_ok_sub; [exact WL | lia | lia] | exact I4 | exact I5
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
  intros l' M'' Hl' Hse' Heq HU' HG'. cbn [rget lget].
  fix_jalr 0x431564.
  assert (HLM' : LM M'' wr).
  { eapply LM_frame; [exact HLM | exact HU' | exact HG' |]. clear. intros x Hx. unfold FPI, inr in *. lia. }
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  wp_a2u [0x431590; 0x431568]. split; intros Hbr.
  - (* [comment removed for export] *)
    specialize (Heq Hbr).
    assert (Hr4 : k + 4 <= r).
    { destruct (Z_lt_le_dec r (k + 4)); [|assumption]. exfalso.
      pose proof (Heq (r - k) ltac:(lia)) as E. replace (k + (r - k)) with r in E by lia.
      destruct (xn_not_stop (r - k) ltac:(lia)) as [N0 N46]. rewrite <- E in N0, N46. destruct HBr; contradiction. }
    eapply (puny_label _ _ wr tmpv r); [exact HLM' | prove_ls Hse | lia | reflexivity | reflexivity | reflexivity | exact Htmp].
  - clear Hbr Heq.
    eapply (plain_label _ _ wr tmpv r); [exact HLM' | prove_ls Hse | lia | reflexivity | reflexivity | reflexivity | reflexivity | exact Htmp].
Qed.

Lemma r_is_z : bv_unsigned (B r) = 0 -> r = z.
Proof.
  intros H0. destruct (Z.eq_dec r z) as [E|E]; [exact E|]. exfalso. apply (HBnz r); [lia | exact H0].
Qed.

(* [comment removed for export] *)
Lemma head : forall l M' wr, LM M' wr -> lstable l -> rget l 25 = W XNB -> rget l 26 = W (b + k) ->
  reach BSEGS rom (W 0x431520) l M' Post.
Proof.
  intros l M' wr HLM Hst H25 H26.
  destruct (LM_str _ _ HLM) as (HB' & _). destruct (LM_rt _ _ HLM) as (Hrt' & Hrtx' & _).
  destruct (LM_wr _ _ HLM) as (_ & WL & _).
  destruct ic_nums as (I1 & _ & I3 & _). destruct HL as (L1 & L2 & _). pose proof Hlen as (Hl1 & Hl2). pose proof Hb as (Hb1 & Hb2).
  pose proof (slack_le r ltac:(lia)) as Hslr. pose proof (slack_le z ltac:(lia)) as Hslz.
  destruct (str_chk M' wr r (r - k + 1) HLM ltac:(lia) ltac:(lia)) as (Sm & Sa & Ss).
  open_ls Hst l. subst.
  wp_a2u (@nil Z).
  fix_jalr 0x1a74e4.
  eapply (if_strchr _ _ _ _ IF rom Post M' b N B k r 46 L);
    [ exact Hrt' | exact Hrtx' | exact HB' | exact Hb | lia | lia | lia | lia | exact HBr | exact HBn | exact Hslr
    | exact Sm | exact Sa | exact Ss | unfold B_IMG_END in *; lia | exact I1 | eapply wr_ok_sub; [exact WL | lia | lia] | exact I3
    | reflexivity | reflexivity | reflexivity | reflexivity | ].
  intros l' M'' Hl' Hse' H10' HU' HG'. cbn [rget lget].
  fix_jalr 0x431530.
  assert (HLM' : LM M'' wr).
  { eapply LM_frame; [exact HLM | exact HU' | exact HG' |]. clear. intros x Hx. unfold FPI, inr in *. lia. }
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  destruct (Z.eqb_spec (bv_unsigned (B r)) 46) as [E46|E46]; match type of H10' with ?x = _ => subst x end.
  - (* [comment removed for export] *)
    assert (Hrl : r < len).
    { destruct (Z.eq_dec r len) as [E|E]; [|lia]. exfalso. rewrite E, HBlen in E46. discriminate E46. }
    wp_a2u [0x431550; 0x431540]. rewrite Wu by lia. split; intros Hbr; [exfalso; lia|]. clear Hbr.
    rewrite ?sub_W.
    eapply (prefix_test _ _ wr (b + r)); [exact HLM' | prove_ls Hse | reflexivity | reflexivity | | reflexivity | right; split; [reflexivity | lia]].
    cbn [rget lget]. f_equal. lia.
  - (* [comment removed for export] *)
    assert (Er : r = z) by (apply r_is_z; destruct HBr; [assumption | contradiction]).
    destruct (LM_str _ _ HLM') as (HB'' & _). destruct (LM_rt _ _ HLM') as (Hrt'' & Hrtx'' & _).
    destruct (LM_wr _ _ HLM') as (_ & WL' & _).
    destruct (str_chk M'' wr z (z - k + 1) HLM' ltac:(lia) ltac:(lia)) as (Sm' & Sa' & Ss').
    wp_a2u (@nil Z). change (bv_unsigned (Z_to_bv 64 0)) with 0. split; intros Hbr; [clear Hbr | exfalso; lia].
    fix_jalr 0x1a74d4.
    eapply (if_strlen _ _ _ _ IF rom Post M'' b N B k z L);
      [ exact Hrt'' | exact Hrtx'' | exact HB'' | exact Hb | lia | lia | lia | exact HBz | exact HBnz | exact Hslz
      | exact Sm' | exact Sa' | exact Ss' | unfold B_IMG_END in *; lia | exact I1 | eapply wr_ok_sub; [exact WL' | lia | lia] | exact I3
      | reflexivity | reflexivity | reflexivity | ].
    intros l3 M3 Hl3 Hse3 H10'' HU3 HG3. cbn [rget lget].
    fix_jalr 0x43154c.
    assert (HLM3 : LM M3 wr).
    { eapply LM_frame; [exact HLM' | exact HU3 | exact HG3 |]. clear. intros x Hx. unfold FPI, inr in *. lia. }
    regs_open l3 Hl3. se_subst Hse3. clear Hse3. match type of H10'' with ?x = _ => subst x end.
    wp_a2u [0x431550].
    eapply (prefix_test _ _ wr 0); [exact HLM3 | prove_ls Hse | reflexivity | reflexivity | | reflexivity | left; reflexivity].
    cbn [rget lget]. f_equal. lia.
Qed.

End Stops.

(* [comment removed for export] *)
Lemma label : forall l M' wr, LM M' wr -> lstable l -> rget l 25 = W XNB -> rget l 26 = W (b + k) ->
  reach BSEGS rom (W 0x431520) l M' Post.
Proof.
  intros l M' wr HLM Hst H25 H26.
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
  rget l 25 = W XNB -> rget l 26 = W (b + k) -> reach BSEGS rom (W 0x431520) l M' Post.
Proof.
  induction m as [m IH] using lt_wf_ind; intros k l M' wr Hm Hk HLM Hst H25 H26.
  eapply label with (k := k) (wr := wr); try assumption.
  intros k' l2 M2 wr2 Hk' HLM2 Hst2 H25' H26'.
  eapply (IH (Z.to_nat (len - k'))) with (k := k'); try eassumption; lia.
Qed.

Lemma entry_nums : (forall x, inr x L 64 -> ~ inr x pk 56 /\ ~ inr x fs 8 /\ ~ inr x (fs + 4096) 16384).
Proof.
  pose proof Hsep as (S1 & S2 & _). destruct Hfs as (F1 & F2 & _). clear - S1 S2 F1 F2.
  intros x Hx. unfold pk, inr, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *. lia.
Qed.

(* [comment removed for export] *)
Lemma region_body : forall l, l = l0 -> length l = 32%nat ->
  rget l 2 = W L -> rget l 9 = W L -> rget l 18 = W SB -> rget l 19 = W (sha FB6) -> rget l 21 = W pk ->
  rget l 25 = W FB6 -> rget l 26 = W b ->
  reach BSEGS rom (W 0x4314f4) l M Post.
Proof.
  intros l El Hl H2 H9 H18 H19 H21 H25 H26.
  assert (Hse : same_except KSL l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0tp as H4. rewrite <- El in H4.
  assert (E27 : rget l0 27 = rget l 27) by (rewrite El; reflexivity).
  assert (E25 : rget l0 25 = W FB6) by (rewrite <- El; exact H25).
  assert (E20 : rget l0 20 = rget l 20) by (rewrite El; reflexivity). clear El.
  destruct HL as (L1 & L2 & _). unfold B_IMG_END in L1.
  regs_open l Hl. cbn [rget lget] in E27, E20. subst sp tp s1 s2 s3 s5 s9 s10.
  wp_a2u [0x431520]. rewrite ?addi_W.
  repeat (split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact HwL]; solve_grows | lia | cbn; lia]|]).

  change (799900 + -1468) with XNB.
  set (SL := [(24, s11); (40, s4); (32, W FB6); (56, W (FB6 + 32)); (48, W XNB)] : list (Z * word)).
  match goal with |- reach _ _ _ _ ?Mx _ => replace Mx with (saves M L SL) by reflexivity end.
  assert (HSL : slots_ok 64 SL = true) by reflexivity.
  assert (HU1 : unch M (saves M L SL) (fun x => inr x L 64)).
  { apply (saves_unch SL M M L 64); [lia | lia | exact HSL | intros x Hx; exact Hx | apply unch_refl]. }
  assert (HG1 : mem_grows M (saves M L SL)) by apply saves_grows.
  assert (Hsp1 : spills (saves M L SL)).
  { unfold spills. cbn [rget]. cbn [rget] in E25. rewrite E27, E25, E20.
    repeat split; (apply (saves_cell BSEGS SL M L 64); [lia | lia | exact HSL | unfold SL; in_list]). }
  set (M1 := saves M L SL) in *.
  clearbody M1.
  assert (HLM : LM M1 0).
  { pose proof entry_nums as En. destruct HFB6 as (_ & A2 & A3). unfold HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *.
    split; [|split; [lia|split; [|split; [exact Hsp1|split]]]].
    - eapply pkt_at_unch; [exact HU1 | unfold pk; lia | unfold pk; lia | | exact HP0].
      intros x Hx HPx. destruct (En x HPx) as (E1 & _). apply E1. exact Hx.
    - eapply ring_idle_unch; [exact Hring | exact HU1 |]. intros x HPx. destruct (En x HPx) as (_ & E2 & E3). auto.
    - eapply unch_weaken; [exact HU1|]. clear. intros x Hx. left. unfold inr in *. lia.
    - exact HG1. }
  eapply (labels (Z.to_nat (len - 0)) 0); [lia | destruct Hlen; lia | exact HLM | | reflexivity
                                          | cbn [rget lget]; f_equal; lia].
  unfold lstable; split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|].
  cbn [rget lget]. repeat split; try reflexivity; f_equal; unfold pk; lia.
Qed.

End A2u.

(* [comment removed for export] *)
Theorem a2u_loop_cps : forall RTX RTXD RSEP fs, rt_iface RTX RTXD RSEP fs ->
  forall rom Post M L FB6 b len N out sb (eb : word) (B : Z -> byte) l,
  bytes_at M b N B -> 0 < b /\ b + N < 2 ^ 63 -> 0 <= len < 2 ^ 31 /\ len < N ->
  bv_unsigned (B len) = 0 -> (b + len) / 8 * 8 + 8 <= b + N ->
  memrange b N /\ addr_ok M b (len + 1) /\ shw_ok M b (len + 1) ->
  pkt_at M (FB6 + 2208) out 0 16 sb eb -> 0 < sb < 2 ^ 64 -> (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 ->
  rt_ok M -> RTX M -> uar_on M -> cell BSEGS M 0x5e2590 8 (W 0x273608) /\ cell BSEGS M 0x5e2598 8 (W 0x273870) ->
  img_ok M 0xc2ee0 0xc2ee5 ->
  M (W (sha XNB)) = Some (Z_to_bv 8 5) /\ shw_ok M XNB 4 ->
  fs_wf fs -> ring_idle M fs -> ring_wr M fs ->
  FB6 mod 64 = 0 /\ (B_IMG_END <= FB6 /\ (FB6 + 4096 <= SB \/ HIMEM_BEG <= FB6)) /\ FB6 + 4096 <= HIMEM_END ->
  zeros M (sha FB6 + 276) 7 /\ zeros M (sha FB6 + 4) 256 /\ rd_ok M (sha FB6) 296 /\ wr_ok BSEGS M (sha FB6 + 288) 3 ->
  wr_ok BSEGS M (FB6 + 32) 2048 /\ wr_ok BSEGS M (FB6 + 2224) 16 /\ wr_ok BSEGS M (FB6 + 2304) 4
    /\ wr_ok BSEGS M (FB6 + 2320) 6 ->
  B_IMG_END <= out /\ memrange out 16 /\ addr_ok M out 16 /\ shw_ok M out 16 /\ wr_ok BSEGS M out 16 ->
  B_IMG_END <= L - 2400 /\ L + 64 < 2 ^ 63 /\ L mod 32 = 0 -> wr_ok BSEGS M (L - 2400) 2464 ->
  a2u_sep fs L FB6 out b N -> (forall x, a2u_FP fs L FB6 out x -> ~ RTXD x) -> RSEP (L - 2400) 2400 ->
  length l = 32%nat -> rget l 2 = W L -> rget l 4 = W TP -> rget l 9 = W L -> rget l 18 = W SB ->
  rget l 19 = W (sha FB6) -> rget l 21 = W (FB6 + 2208) -> rget l 25 = W FB6 -> rget l 26 = W b ->
  (forall l' M', length l' = 32%nat -> same_except KSL l l' ->
     cell BSEGS M' (L + 24) 8 (rget l 27) -> cell BSEGS M' (L + 32) 8 (rget l 25) -> cell BSEGS M' (L + 40) 8 (rget l 20) ->
     ring_idle M' fs -> unch M M' (a2u_FP fs L FB6 out) -> mem_grows M M' ->
     reach BSEGS rom (W 0x431800) l' M' Post) ->
  reach BSEGS rom (W 0x4314f4) l M Post.
Proof.
  intros RTX RTXD RSEP fs IF rom Post M L FB6 b len N out sb eb B l; intros.
  eapply (region_body RTX RTXD RSEP fs IF rom Post M L FB6 b len N out sb eb B) with (l0 := l); eauto.
Qed.

Print Assumptions a2u_loop_cps.

