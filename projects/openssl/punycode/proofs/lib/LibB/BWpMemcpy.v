(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow ACheck ASaves.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BCode2 BRt BImg BIface BWpacket.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_wm stops := wp_go 0x273870 118%nat C_wp_memcpy_eq C_wp_memcpy stops.

(* [comment removed for export] *)
Definition KSI_wm : list nat :=
  [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%nat.
Definition WM_SLOTS : list (nat * Z) :=
  [(1%nat, 88); (8%nat, 80); (9%nat, 72); (18%nat, 64); (19%nat, 56); (20%nat, 48); (21%nat, 40);
   (22%nat, 32); (23%nat, 24); (24%nat, 16); (25%nat, 8)].

(* [comment removed for export] *)
Definition FR_wm (fs spv out mx pk : Z) (x : word) : Prop :=
  inr x (spv - 2400) 2400 \/ inr x out mx \/ inr x (pk + 16) 16 \/ ring_FP fs x.
Definition wm_ok (wr mx len : Z) : Prop := len <> 0 /\ len <= mx - wr.

(* [comment removed for export] *)
Definition wm_sep (fs spv pk out mx src len : Z) : Prop :=
  (spv <= fs \/ fs + FS_SIZE <= spv - 2400) /\ (spv <= pk \/ pk + 56 <= spv - 2400)
  /\ (spv <= out \/ out + mx <= spv - 2400) /\ (out + mx <= pk \/ pk + 56 <= out)
  /\ (out + mx <= fs \/ fs + 1085440 <= out) /\ (pk + 56 <= fs \/ fs + 1085440 <= pk)
  /\ (src + len <= fs \/ fs + 1085440 <= src) /\ (out + mx <= src \/ src + len <= out)
  /\ (spv <= SB \/ HIMEM_BEG <= spv - 2400).

Section WMemcpy.
Variables (RTX : mem -> Prop) (RTXD : word -> Prop) (RSEP : Z -> Z -> Prop) (fs : Z).
Hypothesis IF : rt_iface RTX RTXD RSEP fs.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pk out wr mx sb spv src len h k FB : Z) (eb : word).
Hypothesis Hk : k = h mod 16384.
Hypothesis HFB : FB = fs + 36864 + 64 * k.
Hypothesis Hrt : rt_ok M.
Hypothesis Hrtx : RTX M.
Hypothesis Huar : uar_on M.
Hypothesis Hgot : cell BSEGS M 0x5e2598 8 (W 0x273870).   (* [comment removed for export] *)
Hypothesis Hfs : fs_wf fs.
Hypothesis Hh : 0 <= h < 2 ^ 64.
Hypothesis Hhint : cell BSEGS M fs 8 (W h).
Hypothesis Hflags : zeros M (fs + 4096) 16384.
Hypothesis Hrwr : ring_wr M fs.
Hypothesis HP : pkt_at M pk out wr mx sb eb.
Hypothesis HW : pkt_wf pk out wr mx sb eb.
Hypothesis Hpk8 : pk mod 8 = 0.
Hypothesis Hmx : mx < 32.
Hypothesis Hsh : sh0 M pk 56.
Hypothesis Hwpk : wr_ok BSEGS M (pk + 16) 16.
Hypothesis Hsp : B_IMG_END <= spv - 2400 /\ spv < 2 ^ 63 /\ spv mod 32 = 0.
Hypothesis Hfr : wr_ok BSEGS M (spv - 2400) 2400.
Hypothesis Hlen : 0 <= len < 2 ^ 62.
Hypothesis Hsrc : memrange src len /\ addr_ok M src len /\ (0 < len -> shw_ok M src len) /\ rd_ok M src len.
Hypothesis Hout : B_IMG_END <= out /\ memrange out mx /\ addr_ok M out mx /\ (0 < mx -> shw_ok M out mx)
                  /\ wr_ok BSEGS M out mx.
(* [comment removed for export] *)
Hypothesis Hsep : wm_sep fs spv pk out mx src len.
Hypothesis Hs_rtxd : forall x, FR_wm fs spv out mx pk x -> ~ RTXD x.
Hypothesis Hrsep : RSEP (spv - 2400) 2400.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W spv.
Hypothesis H0tp : rget l0 4 = W TP.
Hypothesis K : forall l' M' wr', length l' = 32%nat -> same_except KSC l0 l' ->
  (wm_ok wr mx len -> wr' = wr + len) -> (~ wm_ok wr mx len -> wr' = wr) ->
  pkt_at M' pk out wr' mx sb eb -> ring_idle M' fs ->
  unch M M' (FR_wm fs spv out mx pk) -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Lemma kb : 0 <= k < 16384.
Proof. rewrite Hk. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Lemma memrange_nums : forall a n, memrange a n -> 0 <= n /\ 0 <= a /\ a + n + 8 <= HIMEM_END.
Proof. intros a n [Hn Hm]. unfold LOMEM_END, HIMEM_BEG, HIMEM_END, B_IMG_END, SB, FS_SIZE in *. lia. Qed.

Lemma nums_FB : fs + 36864 <= FB /\ FB + 64 <= fs + 1085440 /\ FB mod 8 = 0 /\ fs + FS_SIZE <= HIMEM_END
  /\ (B_IMG_END <= fs /\ (fs + FS_SIZE <= SB \/ HIMEM_BEG <= fs)).
Proof.
  destruct Hfs as (F1 & F2 & F3). pose proof kb as Hkb. clear - F1 F2 F3 Hkb HFB.
  assert (FB mod 8 = 0).
  { rewrite HFB. replace (fs + 36864 + 64 * k) with (fs + (4608 + 8 * k) * 8) by lia. rewrite Z.mod_add by lia. exact F3. }
  unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *. lia.
Qed.

Lemma nums : 0 <= pk /\ pk + 64 <= HIMEM_END /\ 0 <= out /\ out + mx + 8 <= HIMEM_END /\ 0 <= src
  /\ src + len + 8 <= HIMEM_END /\ fs + 36864 <= FB /\ FB + 64 <= fs + 1085440 /\ FB mod 8 = 0
  /\ fs + FS_SIZE <= HIMEM_END /\ 0 <= mx /\ (B_IMG_END <= fs /\ (fs + FS_SIZE <= SB \/ HIMEM_BEG <= fs)).
Proof.
  destruct HW as (_ & Hm1 & _). destruct Hout as (_ & Hm2 & _). destruct Hsrc as (Hm3 & _).
  apply memrange_nums in Hm1, Hm2, Hm3. pose proof nums_FB as (B1 & B2 & B3 & B4 & B5).
  clear - Hm1 Hm2 Hm3 B1 B2 B3 B4 B5. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma FR_app : forall y, FR_wm fs spv out mx pk y -> B_IMG_END <= bv_unsigned y.
Proof.
  destruct Hsp as (S1 & _). destruct Hout as (O1 & _). destruct HW as (P1 & _).
  destruct Hfs as (F1 & F2 & _).
  pose proof (sha_range (fs + 36864) ltac:(unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *; lia)) as Hr.
  clear - S1 O1 P1 F1 Hr.
  intros y Hy. unfold FR_wm, ring_FP, inr, B_IMG_END, SB, HIMEM_BEG, FS_SIZE in *. lia.
Qed.

Definition saved (M2 : mem) : Prop :=
  forall r off, In (r, off) WM_SLOTS -> cell BSEGS M2 (spv + -96 + off) 8 (rget l0 r).

(* [comment removed for export] *)
Section AfterMalloc.
Variable M1 : mem.
Hypothesis HU1 : unch M M1 (fun x => inr x (spv - 2400) 2400 \/ inr x fs 8 \/ inr x (fs + 4096 + k) 1
                                     \/ inr x (FB + 24) 8 \/ inr x (FB + 56) 8 \/ inr x (sha FB) 8).
Hypothesis HG1 : mem_grows M M1.
Hypothesis Hsv1 : saved M1.
Hypothesis C56 : cell BSEGS M1 (FB + 56) 8 (W (fs + 4096 + k)).
Hypothesis Chint : cell BSEGS M1 fs 8 (W (h + 1)).

Definition FPA (x : word) : Prop :=
  inr x (spv - 2400) 2312 \/ inr x out mx \/ inr x (pk + 16) 16 \/ inr x FB 56 \/ inr x (sha FB) 8.

Definition WI (M2 : mem) : Prop := unch M1 M2 FPA /\ mem_grows M1 M2.

Lemma WI_refl : WI M1.
Proof. split; [apply unch_refl | apply mem_grows_refl]. Qed.

Lemma shaFB : sha FB = sha (fs + 36864) + 8 * k.
Proof. rewrite HFB. apply sha_frame. Qed.

Lemma shaFB_range : SB <= sha FB /\ sha FB + 8 <= HIMEM_BEG.
Proof.
  pose proof nums_FB as (N1 & N2 & N3 & N4 & N5). destruct Hfs as (F1 & F2 & _).
  pose proof (sha_range FB ltac:(unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *; lia)) as Hr1.
  pose proof (sha_range (FB + 63) ltac:(unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *; lia)) as Hr2.
  assert (E : sha (FB + 63) = sha FB + 7).
  { clear - N3. unfold sha. pose proof (Z.div_mod FB 8 ltac:(lia)) as Hd. rewrite N3 in Hd.
    replace (FB + 63) with (7 + (FB / 8 + 7) * 8) by lia. rewrite Z.div_add by lia.
    rewrite (Z.div_small 7) by lia. lia. }
  clear - Hr1 Hr2 E. lia.
Qed.

(* [comment removed for export] *)
Lemma sepA_total : forall x, FPA x -> FR_wm fs spv out mx pk x.
Proof.
  clear - HFB Hk Hh. intros x Hx. pose proof shaFB as Es. assert (Hkb : 0 <= k < 16384) by (rewrite Hk; apply Z.mod_pos_bound; lia).
  unfold FPA, FR_wm, ring_FP in *.
  destruct Hx as [H|[H|[H|[H|H]]]]; [left | right; left; exact H | right; right; left; exact H
    | right; right; right; right; right; left | right; right; right; right; right; right]; unfold inr in *; lia.
Qed.

Lemma sepM_total : forall x,
  (inr x (spv - 2400) 2400 \/ inr x fs 8 \/ inr x (fs + 4096 + k) 1 \/ inr x (FB + 24) 8 \/ inr x (FB + 56) 8
   \/ inr x (sha FB) 8) -> FR_wm fs spv out mx pk x.
Proof.
  clear - HFB Hk Hh. intros x Hx. pose proof shaFB as Es. assert (Hkb : 0 <= k < 16384) by (rewrite Hk; apply Z.mod_pos_bound; lia).
  unfold FR_wm, ring_FP in *.
  destruct Hx as [H|[H|[H|[H|[H|H]]]]]; [left; exact H | right; right; right; left; exact H
    | right; right; right; right; left | right; right; right; right; right; left
    | right; right; right; right; right; left | right; right; right; right; right; right]; unfold inr in *; lia.
Qed.

(* [comment removed for export] *)
Lemma WI_total : forall M2, WI M2 -> unch M M2 (FR_wm fs spv out mx pk) /\ mem_grows M M2.
Proof.
  intros M2 [HU HG]. split; [|eapply mem_grows_trans; eassumption].
  eapply unch_trans; [eapply unch_weaken; [exact HU1 | exact sepM_total] | eapply unch_weaken; [exact HU | exact sepA_total]].
Qed.

Lemma WI_step : forall M2 M3 (P : word -> Prop), WI M2 -> unch M2 M3 P -> mem_grows M2 M3 ->
  (forall x, P x -> FPA x) -> WI M3.
Proof.
  intros M2 M3 P [HU HG] HU' HG' HPs. split; [|eapply mem_grows_trans; eassumption].
  eapply unch_trans; [exact HU|]. eapply unch_weaken; [exact HU' | exact HPs].
Qed.

(* [comment removed for export] *)
Lemma sepA_saves : forall x, inr x (spv - 88) 88 -> ~ FPA x.
Proof.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12). pose proof shaFB_range as Hsr.
  destruct Hsp as (S1 & S2 & _). pose proof Hsep as (Hs_win_fs & Hs_win_pk & Hs_win_out & Hs_out_pk & Hs_out_ring & Hs_pk_ring & Hs_src_ring & Hs_src_out & S3). destruct Hfs as (F1 & _).
  clear - N7 N8 Hsr S1 S2 S3 F1 Hs_win_fs Hs_win_pk Hs_win_out.
  intros x Hx HF. unfold FPA, inr, B_IMG_END, SB, HIMEM_BEG, FS_SIZE in *. lia.
Qed.

Lemma sepA_ring : forall x, (inr x (FB + 56) 8 \/ inr x fs 8 \/ inr x (fs + 4096) 16384) -> ~ FPA x.
Proof.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12). pose proof shaFB_range as Hsr.
  destruct Hsp as (S1 & S2 & _). pose proof Hsep as (Hs_win_fs & Hs_win_pk & Hs_win_out & Hs_out_pk & Hs_out_ring & Hs_pk_ring & Hs_src_ring & Hs_src_out & S3). destruct Hfs as (F1 & _). pose proof kb as Hkb.
  clear - N7 N8 Hsr S1 S2 S3 F1 Hs_win_fs Hs_out_ring Hs_pk_ring HFB Hkb.
  intros x Hx HF. unfold FPA, inr, B_IMG_END, SB, HIMEM_BEG, FS_SIZE in *. lia.
Qed.

Lemma WI_saved : forall M2, WI M2 -> saved M2.
Proof.
  intros M2 [HU _] r off Hin. destruct Hsp as (S1 & S2 & _). unfold B_IMG_END in *.
  eapply cell_unch; [exact HU | | | | apply Hsv1; exact Hin];
    unfold WM_SLOTS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-|]);
    try contradiction; try lia; intros x Hx; apply sepA_saves; unfold inr in *; cbn in Hx; lia.
Qed.

Lemma WI_c56 : forall M2, WI M2 -> cell BSEGS M2 (FB + 56) 8 (W (fs + 4096 + k)) /\ cell BSEGS M2 fs 8 (W (h + 1)).
Proof.
  intros M2 [HU _]. pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12).
  destruct Hfs as (F1 & F2 & _). unfold HIMEM_END, HIMEM_BEG, FS_SIZE, B_IMG_END, SB in *.
  split; (eapply cell_unch; [exact HU | lia | (cbn; lia) | | eassumption]);
    intros x Hx; apply sepA_ring; cbn in Hx; [left | right; left]; exact Hx.
Qed.

Lemma WI_rt : forall M2, WI M2 -> rt_ok M2 /\ RTX M2 /\ uar_on M2.
Proof.
  intros M2 HWI. destruct (WI_total _ HWI) as [HU _].
  split; [|split].
  - eapply rt_ok_unch; [exact HU | apply FR_app | exact Hrt].
  - eapply (if_unch _ _ _ _ IF); [exact Hrtx | exact HU |]. intros x Hx. split; [apply FR_app, Hx | apply Hs_rtxd, Hx].
  - eapply uar_on_unch; [exact HU | apply FR_app | exact Huar].
Qed.

Lemma WI_wr : forall M2, WI M2 ->
  wr_ok BSEGS M2 (spv - 2400) 2400 /\ wr_ok BSEGS M2 FB 64 /\ wr_ok BSEGS M2 (sha FB) 8
  /\ wr_ok BSEGS M2 (fs + 4096 + k) 1 /\ wr_ok BSEGS M2 out mx /\ wr_ok BSEGS M2 (pk + 16) 16.
Proof.
  intros M2 HWI. destruct (WI_total _ HWI) as [_ HG]. destruct Hrwr as (R1 & R2 & R3 & R4).
  destruct Hout as (_ & _ & _ & _ & O5). pose proof kb as Hkb. pose proof shaFB as Es.
  repeat split; (eapply wr_ok_grows; [exact HG|]);
    first [ exact Hfr | exact O5 | exact Hwpk
          | eapply wr_ok_sub; [exact R3 | lia | lia] | eapply wr_ok_sub; [exact R4 | lia | lia]
          | eapply wr_ok_sub; [exact R2 | lia | lia] ].
Qed.

Lemma store1_zero_hit : forall (Mx : mem) a,
  (wbytes Mx (W a) (word_to_le_bytes 1 (Z_to_bv 64 0))) (W a) = Some (Z_to_bv 8 0).
Proof.
  intros Mx a. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. cbn [wbytes].
  unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sepM_flags : forall i, 0 <= i < 16384 -> i <> k ->
  ~ (inr (W (fs + 4096 + i)) (spv - 2400) 2400 \/ inr (W (fs + 4096 + i)) fs 8 \/ inr (W (fs + 4096 + i)) (fs + 4096 + k) 1
     \/ inr (W (fs + 4096 + i)) (FB + 24) 8 \/ inr (W (fs + 4096 + i)) (FB + 56) 8 \/ inr (W (fs + 4096 + i)) (sha FB) 8).
Proof.
  intros i Hi Hne. pose proof nums_FB as (N1 & N2 & N3 & N4 & N5). pose proof shaFB_range as Hsr. pose proof kb as Hkb.
  destruct Hsp as (S1 & S2 & _). pose proof Hsep as (Hs_win_fs & Hs_win_pk & Hs_win_out & Hs_out_pk & Hs_out_ring & Hs_pk_ring & Hs_src_ring & Hs_src_out & S3).
  assert (Hu : bv_unsigned (W (fs + 4096 + i)) = fs + 4096 + i) by (apply Wu; unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *; lia).
  clear - Hu Hi Hne N1 N2 N4 N5 Hsr Hkb S1 S2 S3 Hs_win_fs.
  unfold inr. rewrite Hu. unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END, FS_SIZE in *. lia.
Qed.

Lemma flags_idle : forall M2, WI M2 ->
  zeros (wbytes M2 (W (fs + 4096 + k)) (word_to_le_bytes 1 (Z_to_bv 64 0))) (fs + 4096) 16384.
Proof.
  intros M2 [HU _] i Hi. pose proof nums_FB as (N1 & N2 & N3 & N4 & N5). pose proof kb as Hkb.
  assert (Hr : 0 <= fs + 4096 + i < 2 ^ 64) by (unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *; lia).
  destruct (Z.eq_dec i k) as [->|Hne]; [apply store1_zero_hit|].
  rewrite wbytes_out; [ | unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia | cbn; unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *; lia
                      | unfold inr; rewrite Wu by lia; cbn; lia ].
  rewrite HU; [rewrite HU1; [apply Hflags; lia | apply sepM_flags; lia]|].
  apply sepA_ring. right. right. unfold inr. rewrite Wu by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma WI_store : forall M2 a bs, WI M2 -> 0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall x, inr x a (Z.of_nat (length bs)) -> FPA x) -> WI (wbytes M2 (W a) bs).
Proof.
  intros M2 a bs HWI Ha Hn HF. eapply (WI_step M2 _ (fun x => inr x a (Z.of_nat (length bs)))); [exact HWI | | apply wbytes_grows | exact HF].
  apply unch_store; [apply unch_refl | exact Ha | exact Hn | intros x Hx; exact Hx].
Qed.

Ltac solve_WI HWI :=
  repeat (apply WI_store; [ | lia | rewrite ?length_N_to_le_bytes; lia
                          | let x := fresh "x" in let Hx := fresh "Hx" in
                            intros x Hx; rewrite ?length_N_to_le_bytes in Hx; unfold FPA, inr in *; lia ]);
  exact HWI.

(* [comment removed for export] *)
Definition FPE (x : word) : Prop := inr x FB 8 \/ inr x (sha FB) 8 \/ inr x (fs + 4096 + k) 1.
Lemma pkt_FPE : forall M2 M3 wr', unch M2 M3 FPE -> pkt_at M2 pk out wr' mx sb eb -> pkt_at M3 pk out wr' mx sb eb.
Proof.
  intros M2 M3 wr' HU HP2.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12).
  pose proof shaFB_range as (Hs1 & Hs2). pose proof kb as Hkb. destruct HW as (P1 & [_ P2] & _).
  pose proof Hsep as (_ & _ & _ & _ & _ & Hs_pk_ring & _).
  clear - HU HP2 N1 N2 N7 N8 N12 Hs1 Hs2 Hkb P1 P2 Hs_pk_ring.
  eapply pkt_at_unch; [exact HU | lia | unfold HIMEM_END in *; lia | | exact HP2].
  intros x Hx HF. unfold FPE, inr, B_IMG_END, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, FS_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma FR_sha : forall x, 0 <= x < HIMEM_END -> (x < fs + 36864 \/ fs + 1085440 <= x) ->
  ~ FR_wm fs spv out mx pk (W (sha x)).
Proof.
  intros x Hx Hout_ring HF.
  pose proof (sha_range x Hx) as Hr. destruct Hfs as (F1 & F2 & F3).
  destruct HW as (_ & [_ P2] & _). destruct Hout as (_ & [_ O2] & _).
  pose proof Hsep as (_ & _ & _ & _ & _ & _ & _ & _ & S3).
  assert (Hu : bv_unsigned (W (sha x)) = sha x) by (apply Wu; unfold SB, HIMEM_BEG, B_IMG_END, FS_SIZE in *; lia).
  assert (Hq : fs + 36864 = 8 * ((fs + 36864) / 8)).
  { pose proof (Z.div_mod (fs + 36864) 8 ltac:(lia)) as Hd. replace ((fs + 36864) mod 8) with 0 in Hd; [lia|].
    symmetry. replace (fs + 36864) with (fs + 4608 * 8) by lia. rewrite Z.mod_add by lia. exact F3. }
  assert (Hnsh : ~ (sha (fs + 36864) <= sha x < sha (fs + 36864) + 131072)).
  { unfold sha. set (q := (fs + 36864) / 8) in *. clearbody q. destruct Hout_ring as [Hlt|Hge].
    - assert (x / 8 < q) by (apply Z.div_lt_upper_bound; lia). lia.
    - assert (q + 131072 <= x / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  clear - HF Hr Hu P2 O2 S3 F1 Hnsh.
  unfold FR_wm, ring_FP, inr in HF. rewrite Hu in HF. unfold SB, LOMEM_END, HIMEM_BEG, HIMEM_END, B_IMG_END, FS_SIZE in *. lia.
Qed.

Lemma sh_FR : forall M2 x, unch M M2 (FR_wm fs spv out mx pk) -> 0 <= x < HIMEM_END ->
  (x < fs + 36864 \/ fs + 1085440 <= x) -> M2 (W (sha x)) = M (W (sha x)).
Proof. intros M2 x HU Hx Ho. apply HU. apply FR_sha; assumption. Qed.

Lemma addr_ok_FR : forall M2 a n, unch M M2 (FR_wm fs spv out mx pk) -> memrange a n ->
  (a + n <= fs + 36864 \/ fs + 1085440 <= a) -> addr_ok M a n -> addr_ok M2 a n.
Proof.
  intros M2 a n HU Hm Ho H x Hx. destruct (H x Hx) as (s & Hs & Hc). exists s. split; [|exact Hc].
  rewrite (sh_FR M2 x HU); [exact Hs | | lia].
  apply memrange_nums in Hm. lia.
Qed.

Lemma sh0_FR : forall M2 a n, unch M M2 (FR_wm fs spv out mx pk) -> memrange a n ->
  (a + n <= fs + 36864 \/ fs + 1085440 <= a) -> sh0 M a n -> sh0 M2 a n.
Proof.
  intros M2 a n HU Hm Ho H x Hx. rewrite (sh_FR M2 x HU); [apply H, Hx | | lia].
  apply memrange_nums in Hm. lia.
Qed.

Lemma memrange_sub : forall a n a' n', memrange a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> memrange a' n'.
Proof. intros a n a' n' [Hn Hm] H1 H2 H3. split; [exact H2|]. lia. Qed.

Lemma sh0_store_app : forall M2 a n b bs, sh0 M2 a n -> 0 <= a -> a + n <= HIMEM_END ->
  0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 -> (b + Z.of_nat (length bs) <= SB \/ HIMEM_BEG <= b) ->
  sh0 (wbytes M2 (W b) bs) a n.
Proof.
  intros M2 a n b bs H Ha Hn Hb Hbn Hz. eapply (sh0_unch M2 _ (fun x => inr x b (Z.of_nat (length bs)))); [ | exact Ha | exact Hn | | exact H].
  - apply unch_store; [apply unch_refl | exact Hb | exact Hbn | intros x Hx; exact Hx].
  - intros y Hy. unfold inr in Hy. lia.
Qed.

Lemma WI_sh0 : forall M2, WI M2 -> sh0 M2 pk 56.
Proof.
  intros M2 HWI. destruct (WI_total _ HWI) as (HUt & _).
  destruct HW as (_ & P2 & _). pose proof Hsep as (_ & _ & _ & _ & _ & Hs_pk_ring & _).
  apply (sh0_FR M2 pk 56 HUt P2); [lia | exact Hsh].
Qed.

(* [comment removed for export] *)
Definition stableB (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSI_wm l0 l /\ rget l 8 = W spv /\ rget l 18 = W FB
  /\ rget l 24 = W (sha FB) /\ rget l 25 = W FB.

(* [comment removed for export] *)
Lemma wm_exit3 : forall l2 M2 wr', saved M2 -> length l2 = 32%nat -> same_except KSI_wm l0 l2 -> rget l2 8 = W spv ->
  (wm_ok wr mx len -> wr' = wr + len) -> (~ wm_ok wr mx len -> wr' = wr) ->
  pkt_at M2 pk out wr' mx sb eb -> ring_idle M2 fs -> unch M M2 (FR_wm fs spv out mx pk) -> mem_grows M M2 ->
  reach BSEGS rom (W 0x273a0c) l2 M2 Post.
Proof.
  intros l2 M2 wr' Hsv Hl Hse H8 Hy Hn HP2 Hri HU2 HG2.
  pose proof (Hsv 1%nat 88 ltac:(unfold WM_SLOTS; in_list)) as Csv1. pose proof (Hsv 8%nat 80 ltac:(unfold WM_SLOTS; in_list)) as Csv8.
  pose proof (Hsv 9%nat 72 ltac:(unfold WM_SLOTS; in_list)) as Csv9. pose proof (Hsv 18%nat 64 ltac:(unfold WM_SLOTS; in_list)) as Csv18.
  pose proof (Hsv 19%nat 56 ltac:(unfold WM_SLOTS; in_list)) as Csv19. pose proof (Hsv 20%nat 48 ltac:(unfold WM_SLOTS; in_list)) as Csv20.
  pose proof (Hsv 21%nat 40 ltac:(unfold WM_SLOTS; in_list)) as Csv21. pose proof (Hsv 22%nat 32 ltac:(unfold WM_SLOTS; in_list)) as Csv22.
  pose proof (Hsv 23%nat 24 ltac:(unfold WM_SLOTS; in_list)) as Csv23. pose proof (Hsv 24%nat 16 ltac:(unfold WM_SLOTS; in_list)) as Csv24.
  pose proof (Hsv 25%nat 8 ltac:(unfold WM_SLOTS; in_list)) as Csv25.
  clear Hsv. destruct Hsp as (S1 & S2 & _). unfold B_IMG_END in *.
  regs_open l2 Hl. subst s0.
  wp_wm (@nil Z). mem_auto.
  apply (K _ _ wr'); [reflexivity | | exact Hy | exact Hn | exact HP2 | exact Hri | exact HU2 | exact HG2].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma WI_release : forall M4, WI M4 ->
  let M5 := wbytes M4 (W (fs + 4096 + k)) (word_to_le_bytes 1 (Z_to_bv 64 0)) in
  saved M5 /\ ring_idle M5 fs /\ unch M M5 (FR_wm fs spv out mx pk) /\ mem_grows M M5 /\ unch M4 M5 FPE.
Proof.
  intros M4 HWI M5. pose proof (flags_idle _ HWI) as Hz. fold M5 in Hz.
  pose proof (WI_saved _ HWI) as Hsv. destruct (WI_c56 _ HWI) as (_ & Chint'). destruct (WI_total _ HWI) as (HU & HG).
  pose proof nums_FB as (N1 & N2 & N3 & N4 & N5). pose proof kb as Hkb. destruct Hsp as (S1 & S2 & _).
  pose proof Hsep as (Hs_win_fs & _).
  assert (HU5 : unch M4 M5 (fun x => inr x (fs + 4096 + k) 1)).
  { unfold M5. clear - N4 N5 Hkb.
    apply unch_store; [apply unch_refl | unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia | cbn; unfold HIMEM_END, FS_SIZE in *; lia | intros x Hx; exact Hx]. }
  split; [|split; [|split; [|split]]].
  - intros r off Hin. pose proof (Hsv r off Hin) as Hc.
    assert (Ho : 8 <= off <= 88).
    { unfold WM_SLOTS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). contradiction. }
    clear - HU5 Hc Ho S1 S2 N4 N5 Hkb Hs_win_fs.
    eapply cell_unch; [exact HU5 | unfold B_IMG_END in *; lia | (cbn; lia) | | exact Hc].
    intros x Hx Hx2. cbn in Hx. unfold inr, B_IMG_END, HIMEM_BEG, HIMEM_END, FS_SIZE, SB in *. lia.
  - split; [|exact Hz]. exists ((h + 1) mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|].
    replace (W ((h + 1) mod 2 ^ 64)) with (W (h + 1)) by (apply W_eq_mod; rewrite Z.mod_mod by lia; reflexivity).
    clear - HU5 Chint' N4 N5 Hkb.
    eapply cell_unch; [exact HU5 | unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia | (cbn; unfold HIMEM_END, FS_SIZE in *; lia) | | exact Chint'].
    intros x Hx Hx2. cbn in Hx. unfold inr in *. lia.
  - eapply unch_trans; [exact HU|]. eapply unch_weaken; [exact HU5|]. clear - Hkb.
    intros x Hx. unfold FR_wm, ring_FP. right. right. right. right. left. unfold inr in *. lia.
  - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  - eapply unch_weaken; [exact HU5|]. intros x Hx. unfold FPE. right. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma wm_epi : forall l2 M2 wr', WI M2 -> stableB l2 ->
  (wm_ok wr mx len -> wr' = wr + len) -> (~ wm_ok wr mx len -> wr' = wr) ->
  pkt_at M2 pk out wr' mx sb eb ->
  reach BSEGS rom (W 0x2739a4) l2 M2 Post.
Proof.
  intros l2 M2 wr' HWI (Hl & Hse & H8 & H18 & H24 & H25) Hy Hn HP2.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12).
  pose proof shaFB_range as (Hs1 & Hs2). pose proof kb as Hkb.
  destruct (WI_wr _ HWI) as (W1 & W2 & W3 & W4 & W5 & W6).
  regs_open l2 Hl. subst s0 s2 s8 s9.
  wp_wm [0x2739b8]. rewrite ?addi_W.
  assert (E1 : v_addiw (Z_to_bv 64 1172320256) 1550 = W 0x45e0360e) by (apply bv_eq; reflexivity). rewrite E1. clear E1.
  unfold SB, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END in *.
  mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ =>
    assert (HWI3 : WI Mx) by solve_WI HWI;
    assert (HU3 : unch M2 Mx FPE) by (solve_unch ltac:(unfold FPE, inr in *; lia));
    set (M3 := Mx) in * end.
  clearbody M3.
  destruct (WI_wr _ HWI3) as (W1' & W2' & W3' & W4' & W5' & W6'). clear W1 W2 W3 W4 W5 W6.
  wp_wm [0x2739e0; 0x2739ec]. rewrite ?addi_W.
  rewrite (Wu FB) by lia. split; intros Hb; [exfalso; lia|]. clear Hb.
  mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ =>
    assert (HWI4 : WI Mx) by solve_WI HWI3;
    assert (HU4 : unch M3 Mx FPE) by (solve_unch ltac:(unfold FPE, inr in *; lia));
    set (M4 := Mx) in * end.
  clearbody M4.
  destruct (WI_c56 _ HWI4) as (C56' & _).
  destruct (WI_wr _ HWI4) as (_ & _ & _ & W4'' & _ & _).
  wp_wm [0x273a0c]. rewrite ?addi_W.
  eexists. split; [apply load_cell8; exact C56'|].
  split; [eapply wr_ok_store; [exact W4'' | lia | cbn; lia]|].
  destruct (WI_release _ HWI4) as (Hsv5 & Hri5 & HU5 & HG5 & HUE5).
  eapply (wm_exit3 _ _ wr'); [exact Hsv5 | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity
    | exact Hy | exact Hn | | exact Hri5 | exact HU5 | exact HG5].
  eapply pkt_FPE; [|exact HP2]. eapply unch_trans; [exact HU3|]. eapply unch_trans; [exact HU4 | exact HUE5].
Qed.

(* [comment removed for export] *)
Lemma wm_call_nums : rb_ok wr mx len ->
  (out + wr + len <= src \/ src + len <= out + wr)
  /\ (B_IMG_END <= spv + -96 - 2224 /\ spv + -96 < 2 ^ 63)
  /\ (spv + -96 <= SB \/ HIMEM_BEG <= spv + -96 - 2224)
  /\ (out + wr + len <= spv + -96 - 2224 \/ spv + -96 <= out + wr)
  /\ (src + len <= fs + 36864 \/ fs + 1085440 <= src)
  /\ (out + mx <= fs + 36864 \/ fs + 1085440 <= out).
Proof.
  intros (Hln0 & Hroom). destruct Hsp as (Sp1 & Sp2 & Sp3). destruct HW as (_ & _ & _ & _ & Hwr & _).
  pose proof Hsep as (Hs_win_fs & Hs_win_pk & Hs_win_out & Hs_out_pk & Hs_out_ring & Hs_pk_ring & Hs_src_ring & Hs_src_out & Hs_win_sh).
  clear - Hln0 Hroom Sp1 Sp2 Hwr Hlen Hs_win_out Hs_out_ring Hs_src_ring Hs_src_out Hs_win_sh.
  unfold B_IMG_END in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma wm_after_alloc : forall l2 M2 wr', WI M2 -> stableB l2 -> rget l2 2 = W (spv + -96) ->
  rget l2 19 = W len -> rget l2 20 = W src -> rget l2 22 = W 1 -> rget l2 23 = W (FB + 32) ->
  pkt_at M2 pk out wr' mx sb eb ->
  (rb_ok wr mx len -> rget l2 10 = W 1 /\ wr' = wr + len /\ cell BSEGS M2 (FB + 32) 8 (W (out + wr))) ->
  (~ rb_ok wr mx len -> rget l2 10 = W 0 /\ wr' = wr) ->
  reach BSEGS rom (W 0x273984) l2 M2 Post.
Proof.
  intros l2 M2 wr' HWI Hst H2 H19 H20 H22 H23 HP2 Hok Hno.
  assert (Hdec : rb_ok wr mx len \/ ~ rb_ok wr mx len) by (unfold rb_ok; lia).
  destruct Hdec as [Hy|Hn].
  2:{ destruct (Hno Hn) as (H10 & ->). pose proof Hst as (Hl & Hse & H8 & H18 & H24 & H25).
      regs_open l2 Hl. subst a0 s0 s2 s8 s9.
      wp_wm [0x2739a4; 0x273988]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      split; intros Hb; [|exfalso; apply Hb; reflexivity]. clear Hb.
      apply (wm_epi _ _ wr); [exact HWI | | intros [Hy1 Hy2]; exfalso; apply Hn; split; assumption | reflexivity | exact HP2].
      split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex]|]. cbn [rget lget]. repeat split; reflexivity. }
  destruct (Hok Hy) as (H10 & -> & Cab). clear Hok Hno. pose proof Hst as (Hl & Hse & H8 & H18 & H24 & H25).
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12).
  pose proof HW as (Hpk0 & Hmr & Hout0 & Hout2 & Hwr & Hsb & Heb).
  destruct Hy as (Hlen0 & Hroom).
  destruct (WI_rt _ HWI) as (Hrt3 & Hrtx3 & _).
  destruct (WI_total _ HWI) as (HUt3 & HGt3).
  destruct (WI_wr _ HWI) as (W1' & _ & _ & _ & W5' & _).
  pose proof Hsrc as (Sm & Sa & Ss & Sr). pose proof Hout as (O1 & O2 & O3 & O4 & O5).
  destruct (wm_call_nums (conj Hlen0 Hroom)) as (D1 & D2 & D3 & D4 & D5 & D6).
  unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END, FS_SIZE in N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11, N12, Hpk0.
  regs_open l2 Hl. subst a0 sp s0 s2 s3 s4 s6 s7 s8 s9.
  wp_wm [0x2739a4; 0x2739a0].
  change (bv_unsigned (Z_to_bv 64 1)) with 1. split; intros Hb; [exfalso; lia|]. clear Hb.
  eexists. split; [apply load_cell8; exact Cab|].
  rewrite (Wu (out + wr)) by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  eapply (if_amemcpy _ _ _ _ IF rom Post M2 (out + wr) src len (spv + -96));
    [ exact Hrt3 | exact Hrtx3 | lia | exact Sm
    | eapply memrange_sub; [exact O2 | lia | lia | lia]
    | eapply addr_ok_FR; [exact HUt3 | exact Sm | exact D5 | exact Sa]
    | eapply addr_ok_sub; [eapply addr_ok_FR; [exact HUt3 | exact O2 | exact D6 | exact O3] | lia | lia]
    | intros Hlp; unfold shw_ok; eapply rd_ok_grows; [exact HGt3 | apply Ss; lia]
    | intros Hlp; eapply shw_ok_sub; [unfold shw_ok; eapply rd_ok_grows; [exact HGt3 | apply O4; lia] | lia | lia | lia]
    | eapply rd_ok_grows; [exact HGt3 | exact Sr]
    | eapply wr_ok_sub; [exact W5' | lia | lia]
    | unfold B_IMG_END in *; lia | exact D1 | exact D2 | exact D3
    | eapply wr_ok_sub; [exact W1' | lia | lia]
    | exact D4 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
  intros l' M' Hl' Hse' HU' HG'. cbn [rget lget].
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) 0) _ _ _ =>
    replace (v_jalr (Z_to_bv 64 x) 0) with (W 0x27399c) by reflexivity end.
  regs_open l' Hl'. se_subst Hse'. clear Hse'.
  assert (HWI4 : WI M').
  { eapply (WI_step M2 M'); [exact HWI | exact HU' | exact HG' |]. clear - Hlen0 Hroom Hwr Hlen. intros x Hx. unfold FPA, inr in *. lia. }
  assert (HP4 : pkt_at M' pk out (wr + len) mx sb eb).
  { pose proof Hsep as (_ & Hs_win_pk & _ & Hs_out_pk & _).
    eapply pkt_at_unch; [exact HU' | lia | lia | | exact HP2].
    clear - Hs_win_pk Hs_out_pk Hlen0 Hroom Hwr Hlen. intros x Hx Hx2. unfold inr in *. lia. }
  wp_wm [0x2739a4].
  apply (wm_epi _ _ (wr + len)); [exact HWI4 | | reflexivity | intros Hn; exfalso; apply Hn; split; assumption | exact HP4].
  split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex]|]. cbn [rget lget]. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wm_al_nums :
  (B_IMG_END <= spv + -96 - 128 /\ spv + -96 < 2 ^ 63 /\ (spv + -96 <= SB \/ HIMEM_BEG <= spv + -96 - 128)
    /\ (pk + 56 <= spv + -96 - 128 \/ spv + -96 <= pk) /\ (FB + 32 + 8 <= spv + -96 - 128 \/ spv + -96 <= FB + 32))
  /\ (B_IMG_END <= FB + 32 /\ memrange (FB + 32) 8 /\ (FB + 32 + 8 <= pk \/ pk + 56 <= FB + 32) /\ (FB + 32) mod 8 = 0).
Proof.
  destruct Hsp as (Sp1 & Sp2 & Sp3). pose proof nums_FB as (N1 & N2 & N3 & N4 & N5).
  pose proof Hsep as (Hs_win_fs & Hs_win_pk & Hs_win_out & Hs_out_pk & Hs_out_ring & Hs_pk_ring & Hs_src_ring & Hs_src_out & Hs_win_sh).
  assert (H8 : (FB + 32) mod 8 = 0).
  { clear - N3. replace (FB + 32) with (FB + 4 * 8) by lia. rewrite Z.mod_add by lia. exact N3. }
  clear - Sp1 Sp2 N1 N2 N4 N5 Hs_win_fs Hs_win_pk Hs_pk_ring Hs_win_sh H8.
  unfold memrange, B_IMG_END, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, FS_SIZE in *. repeat split; try lia; exact H8.
Qed.

(* [comment removed for export] *)
Lemma sh0_local : forall M2, M2 (W (sha FB + 4)) = Some (Z_to_bv 8 0) -> sh0 M2 (FB + 32) 8.
Proof.
  intros M2 H x Hx. pose proof nums_FB as (_ & _ & N3 & _).
  replace (sha x) with (sha FB + 4); [exact H|]. unfold sha.
  pose proof (Z.div_mod FB 8 ltac:(lia)) as Hd. rewrite N3 in Hd.
  replace x with ((x - FB - 32) + (FB / 8 + 4) * 8) by lia. rewrite Z.div_add by lia.
  rewrite (Z.div_small (x - FB - 32)) by lia. lia.
Qed.

Lemma byte_store_other : forall (Mx : mem) a b bs v, Mx (W a) = Some v -> 0 <= a < 2 ^ 64 -> 0 <= b ->
  b + Z.of_nat (length bs) < 2 ^ 64 -> (a < b \/ b + Z.of_nat (length bs) <= a) ->
  (wbytes Mx (W b) bs) (W a) = Some v.
Proof.
  intros Mx a b bs v H Ha Hb Hbn Hd. rewrite wbytes_out; [exact H | exact Hb | exact Hbn |].
  unfold inr. rewrite Wu by lia. lia.
Qed.

Lemma pkt_M1 : pkt_at M1 pk out wr mx sb eb.
Proof.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12).
  pose proof shaFB_range as (Hs1 & Hs2). pose proof kb as Hkb. destruct HW as (P1 & [_ P2] & _).
  pose proof Hsep as (_ & Hs_win_pk & _ & _ & _ & Hs_pk_ring & _).
  eapply pkt_at_unch; [exact HU1 | lia | unfold HIMEM_END in *; lia | | exact HP].
  clear - N1 N2 N7 N8 N12 Hs1 Hs2 Hkb P1 P2 Hs_win_pk Hs_pk_ring HFB.
  intros x Hx HF. unfold inr, B_IMG_END, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, FS_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
Definition FPH (x : word) : Prop := inr x (spv - 96) 8 \/ inr x FB 24 \/ inr x (sha FB) 8.
Lemma pkt_FPH : forall M2 M3, unch M2 M3 FPH -> pkt_at M2 pk out wr mx sb eb -> pkt_at M3 pk out wr mx sb eb.
Proof.
  intros M2 M3 HU HP2.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12).
  pose proof shaFB_range as (Hs1 & Hs2). destruct HW as (P1 & [_ P2] & _).
  pose proof Hsep as (_ & Hs_win_pk & _ & _ & _ & Hs_pk_ring & _).
  eapply pkt_at_unch; [exact HU | lia | unfold HIMEM_END in *; lia | | exact HP2].
  clear - N1 N2 N7 N8 N12 Hs1 Hs2 P1 P2 Hs_win_pk Hs_pk_ring.
  intros x Hx HF. unfold FPH, inr, B_IMG_END, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, FS_SIZE in *. lia.
Qed.

Lemma WI_got : forall M2, WI M2 -> cell BSEGS M2 0x5e2598 8 (W 0x273870).
Proof.
  intros M2 HWI. destruct (WI_total _ HWI) as (HUt & _).
  eapply cell_unch; [exact HUt | lia | (cbn; lia) | | exact Hgot].
  intros x Hx HF. apply FR_app in HF. unfold inr, B_IMG_END in *. lia.
Qed.

(* [comment removed for export] *)
Lemma wm_after_malloc : forall l2, length l2 = 32%nat -> same_except KSI_wm l0 l2 ->
  rget l2 2 = W (spv + -96) -> rget l2 8 = W spv -> rget l2 9 = W (spv + -96) -> rget l2 10 = W FB ->
  rget l2 19 = W len -> rget l2 20 = W src -> rget l2 21 = W pk -> rget l2 24 = W SB ->
  reach BSEGS rom (W 0x2738e0) l2 M1 Post.
Proof.
  intros l2 Hl Hse H2 H8 H9 H10 H19 H20 H21 H24.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12).
  pose proof shaFB_range as (Hs1 & Hs2). pose proof kb as Hkb.
  pose proof WI_refl as HWI1. pose proof pkt_M1 as HP1.
  destruct (WI_wr _ HWI1) as (W1 & W2 & W3 & W4 & W5 & W6).
  destruct Hsp as (Sp1 & Sp2 & Sp3).
  unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END, FS_SIZE in N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11, N12, Hs1, Hs2, Sp1.
  regs_open l2 Hl. subst sp s0 s1 a0 s3 s4 s5 s8.
  wp_wm [0x2738f4; 0x273914]. rewrite (Wu FB) by lia.
  split; intros Hb; [|exfalso; lia]. clear Hb.
  rewrite ?addi_W. mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ =>
    assert (HWI2 : WI Mx) by solve_WI HWI1;
    assert (HU2 : unch M1 Mx FPH) by (solve_unch ltac:(unfold FPH, inr in *; lia));
    set (M2 := Mx) in * end.
  clearbody M2. clear W1 W2 W3 W4 W5 W6.
  destruct (WI_wr _ HWI2) as (W1 & W2 & W3 & W4 & W5 & W6). pose proof (WI_got _ HWI2) as Hgot2.
  wp_wm [0x273948]. rewrite ?addi_W.
  rewrite (sha_addr_r FB) by lia. rewrite ?addi_W.
  exists (W 0x273870). split.
  { apply load_cell8. exact Hgot2. }
  assert (E1 : v_addiw (Z_to_bv 64 1102417920) (-1357) = W 0x41b58ab3) by (apply bv_eq; reflexivity). rewrite E1. clear E1.
  mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ =>
    assert (HWI3 : WI Mx) by solve_WI HWI2;
    assert (HU3 : unch M2 Mx FPH) by (solve_unch ltac:(unfold FPH, inr in *; lia));
    assert (Hz3 : Mx (W (sha FB + 4)) = Some (Z_to_bv 8 0)) by apply store1_zero_hit;
    set (M3 := Mx) in * end.
  clearbody M3. clear W1 W2 W3 W4 W5 W6 Hgot2.
  destruct (WI_wr _ HWI3) as (W1 & W2 & W3 & W4 & W5 & W6).
  wp_wm [0x273968]. rewrite ?addi_W. mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ =>
    assert (HWI4 : WI Mx) by solve_WI HWI3;
    assert (HU4 : unch M3 Mx FPH) by (solve_unch ltac:(unfold FPH, inr in *; lia));
    assert (Hz4 : Mx (W (sha FB + 4)) = Some (Z_to_bv 8 0))
      by (repeat (apply byte_store_other; [ | lia | lia | cbn; lia | cbn; lia]); exact Hz3);
    set (M4 := Mx) in * end.
  clearbody M4. clear W1 W2 W3 W4 W5 W6.
  assert (HP4 : pkt_at M4 pk out wr mx sb eb).
  { eapply pkt_FPH; [|exact HP1]. eapply unch_trans; [exact HU2|]. eapply unch_trans; [exact HU3 | exact HU4]. }
  clear HU2 HU3 HU4 HWI2 HWI3 Hz3.
  wp_wm [0x2739a4]. rewrite (Wu len) by lia. rewrite ?addi_W.
  split; intros Hb.
  { apply (wm_epi _ _ wr); [exact HWI4 | | intros [Hy1 Hy2]; exfalso; lia | reflexivity | exact HP4].
    split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex]|]. cbn [rget lget]. repeat split; reflexivity. }
  destruct (WI_rt _ HWI4) as (Hrt4 & _ & _). pose proof (WI_sh0 _ HWI4) as Hsh4.
  destruct (WI_wr _ HWI4) as (W1 & W2 & W3 & W4 & W5 & W6).
  destruct wm_al_nums as (R1 & R2).
  match goal with |- reach _ _ (Z_to_bv 64 ?x) _ _ _ => replace (Z_to_bv 64 x) with (Z_to_bv 64 0x272074) by reflexivity end.
  eapply (alloc_cps rom Post M4 pk out wr mx sb (spv + -96) len (FB + 32) eb Hrt4 HP4 HW Hpk8 Hsh4 R1);
    [ eapply wr_ok_sub; [exact W1 | lia | lia] | exact Hlen | exact R2
    | apply sh0_local; exact Hz4 | eapply wr_ok_sub; [exact W2 | lia | lia] | exact W6
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
  intros l' M' wr' Hl' Hse' Hok Hno HP' HU' HG'. cbn [rget lget].
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) 0) _ _ _ =>
    replace (v_jalr (Z_to_bv 64 x) 0) with (W 0x273984) by reflexivity end.
  assert (HWI5 : WI M').
  { eapply (WI_step M4 M'); [exact HWI4 | exact HU' | exact HG' |]. clear. intros x Hx. unfold FR_al, FPA, inr in *. lia. }
  regs_open l' Hl'. se_subst Hse'.
  apply (wm_after_alloc _ _ wr'); [exact HWI5 | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
                          | exact HP' | exact Hok | exact Hno].
  split; [reflexivity|]. split; [|cbn [rget lget]; repeat split; reflexivity].
  eapply same_except_call; [ | exact Hse' | ]; [eapply same_except_trans; [exact Hse | same_ex] |].
  unfold KS_al, KSI_wm. subset_tac.
Qed.

End AfterMalloc.

(* [comment removed for export] *)
Definition SL_wm : list (Z * word) :=
  [(0, W 0); (88, rget l0 1); (80, rget l0 8); (72, rget l0 9); (64, rget l0 18); (56, rget l0 19); (48, rget l0 20);
   (40, rget l0 21); (32, rget l0 22); (24, rget l0 23); (16, rget l0 24); (8, rget l0 25)].

Lemma wm_win_nums : (fs + FS_SIZE <= spv + -96 - 208 \/ spv + -96 <= fs)
  /\ (spv + -96 <= SB \/ HIMEM_BEG <= spv + -96 - 208)
  /\ (forall x, inr x (spv - 2400) 2400 -> ~ inr x fs FS_SIZE /\ B_IMG_END <= bv_unsigned x)
  /\ (forall x, inr x (spv - 88) 88 ->
        ~ (inr x (spv + -96 - 208) 208 \/ inr x fs 8 \/ inr x (fs + 4096 + k) 1 \/ inr x (FB + 24) 8
           \/ inr x (FB + 56) 8 \/ inr x (sha FB) 8)).
Proof.
  destruct Hsp as (Sp1 & Sp2 & Sp3). pose proof nums_FB as (NF1 & NF2 & NF3 & NF4 & NF5).
  pose proof shaFB_range as (Hs1 & Hs2). pose proof kb as Hkb.
  pose proof Hsep as (Hs_win_fs & _ & _ & _ & _ & _ & _ & _ & Hs_win_sh).
  clear - Sp1 Sp2 Hs_win_fs Hs_win_sh NF1 NF2 NF4 NF5 Hs1 Hs2 Hkb.
  unfold inr, B_IMG_END, SB, HIMEM_BEG, HIMEM_END, FS_SIZE in *.
  split; [lia|]. split; [lia|]. split; intros x Hx; lia.
Qed.

Lemma wmemcpy_body : forall l, l = l0 -> rget l 10 = W pk -> rget l 11 = W src -> rget l 12 = W len ->
  reach BSEGS rom (W 0x273870) l M Post.
Proof.
  intros l El H10 H11 H12. pose proof Hl0 as Hl. rewrite <- El in Hl.
  assert (Hse : same_except KSI_wm l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2. pose proof H0tp as H4. rewrite <- El in H4.
  assert (HSLe : SL_wm = SL_wm) by reflexivity. unfold SL_wm at 1 in HSLe. rewrite <- El in HSLe. clear El.
  destruct Hsp as (Sp1 & Sp2 & Sp3). destruct wm_win_nums as (Q1 & Q2 & Q3 & Q4).
  unfold B_IMG_END in Sp1.
  regs_open l Hl. subst sp tp a0 a1 a2. cbn [rget lget] in HSLe.
  wp_wm [0x2738a4]. mem_auto.
  assert (HSL : slots_ok 96 SL_wm = true) by reflexivity.
  match goal with |- reach _ _ _ _ ?Mx _ => replace Mx with (saves M (spv + -96) SL_wm)
    by (rewrite <- HSLe; cbn [saves]; replace (spv + -96 + 0) with (spv + -96) by lia; reflexivity) end.
  set (M0s := saves M (spv + -96) SL_wm) in *.
  assert (HUs : unch M M0s (fun x => inr x (spv - 2400) 2400)).
  { apply (saves_unch SL_wm M M (spv + -96) 96); [lia | lia | exact HSL | | apply unch_refl]. intros x Hx. unfold inr in *. lia. }
  assert (HGs : mem_grows M M0s) by apply saves_grows.
  assert (Hsvs : forall off v, In (off, v) SL_wm -> cell BSEGS M0s (spv + -96 + off) 8 v).
  { intros off v Hin. apply (saves_cell BSEGS SL_wm M (spv + -96) 96); [lia | lia | exact HSL | exact Hin]. }
  clearbody M0s. clear HSLe HSL.
  assert (Hrt0 : rt_ok M0s). { eapply rt_ok_unch; [exact HUs | | exact Hrt]. intros y Hy. apply (Q3 y Hy). }
  assert (Hrtx0 : RTX M0s).
  { eapply (if_unch _ _ _ _ IF); [exact Hrtx | exact HUs |]. intros x Hx. split; [apply (Q3 x Hx) | apply Hs_rtxd; left; exact Hx]. }
  assert (Huar0 : uar_on M0s). { eapply uar_on_unch; [exact HUs | | exact Huar]. intros y Hy. apply (Q3 y Hy). }
  pose proof nums_FB as (NF1 & NF2 & NF3 & NF4 & NF5).
  assert (Hhint0 : cell BSEGS M0s fs 8 (W h)).
  { eapply cell_unch; [exact HUs | unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia | (cbn; unfold HIMEM_END, FS_SIZE in *; lia) | | exact Hhint].
    intros x Hx Hx2. destruct (Q3 x Hx2) as [Hq _]. apply Hq. cbn in Hx. unfold inr, FS_SIZE in *. lia. }
  assert (Hflags0 : zeros M0s (fs + 4096) 16384).
  { eapply zeros_grows_unch; [exact HUs | unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia | unfold HIMEM_END, FS_SIZE in *; lia | | exact Hflags].
    intros x Hx Hx2. destruct (Q3 x Hx2) as [Hq _]. apply Hq. unfold inr, FS_SIZE in *. lia. }
  pose proof (ring_wr_grows _ _ _ HGs Hrwr) as (Rw1 & Rw2 & Rw3 & Rw4).
  pose proof Hrt0 as (G1 & G2 & _). pose proof Huar0 as (U1 & U2).
  unfold G_SB, C_SB, G_UAR, C_UAR in *.
  wp_wm [0x2738e8]. rewrite ?addi_W. mem_auto.
  eexists. split; [apply load_cell; [exact U2 | lia]|]. mem_auto.
  change (v_lw (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) mod 2 ^ (8 * Z.of_nat 4)))) with (W 1).
  change (bv_unsigned (W 1)) with 1.
  assert (Hal : (spv + -96) mod 32 = 0).
  { replace (spv + -96) with (spv + (-3) * 32) by lia. rewrite Z.mod_add by lia. exact Sp3. }
  rewrite (andi_m32_aligned (spv + -96)) by (lia || exact Hal).
  replace (spv + -96 + 96) with spv by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  match goal with |- reach _ _ (Z_to_bv 64 ?x) _ _ _ => replace (Z_to_bv 64 x) with (W 0x1a1328) by reflexivity end.
  destruct Hfs as (Fs1 & Fs2 & Fs3).
  eapply (if_malloc0 _ _ _ _ IF rom Post M0s h (spv + -96));
    [ exact Hrt0 | exact Hrtx0 | exact Hhint0 | exact Hh | exact Hflags0 | split; [exact Fs1 | exact Fs2]
    | exact Rw1 | exact Rw2 | exact Rw3 | exact Rw4 | unfold B_IMG_END; lia | exact Q2
    | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HGs | exact Hfr] | lia | lia]
    | eapply (if_sep_sub _ _ _ _ IF); [exact Hrsep | lia | lia] | exact Q1
    | reflexivity | reflexivity | reflexivity | ].
  intros l' M' k0 FB0 Hl' Hse' H10' Ch' Cf' C24' C56' Hz' HU' HG'. subst k0 FB0.
  rewrite <- Hk in *. rewrite <- HFB in *. cbn [rget lget].
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) 0) _ _ _ => replace (v_jalr (Z_to_bv 64 x) 0) with (W 0x2738e0) by reflexivity end.
  assert (Hsv' : saved M').
  { intros r off Hin.
    assert (Hin2 : In (off, rget l0 r) SL_wm /\ 8 <= off <= 88).
    { unfold WM_SLOTS in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; split; [unfold SL_wm; in_list | lia]|]). contradiction. }
    destruct Hin2 as (Hin2 & Ho).
    eapply cell_unch; [exact HU' | lia | (cbn; lia) | | apply Hsvs; exact Hin2].
    intros x Hx. apply Q4. cbn in Hx. unfold inr in *. lia. }
  assert (HU1' : unch M M' (fun x => inr x (spv - 2400) 2400 \/ inr x fs 8 \/ inr x (fs + 4096 + k) 1
                                     \/ inr x (FB + 24) 8 \/ inr x (FB + 56) 8 \/ inr x (sha FB) 8)).
  { eapply unch_trans; [eapply unch_weaken; [exact HUs|] | eapply unch_weaken; [exact HU'|]].
    - intros x Hx. left. exact Hx.
    - intros x Hx. cbv beta in Hx. destruct Hx as [Hx|Hx]; [left; unfold inr in *; lia | right; exact Hx]. }
  regs_open l' Hl'. se_subst Hse'. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  eapply (wm_after_malloc M' HU1' (mem_grows_trans _ _ _ HGs HG') Hsv' C56' Ch');
    [reflexivity | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
  eapply same_except_call; [ | exact Hse' | ]; [eapply same_except_trans; [exact Hse | same_ex] |].
  unfold KSC, KSI_wm. subset_tac.
Qed.

End WMemcpy.

Theorem wmemcpy_cps : forall RTX RTXD RSEP fs, rt_iface RTX RTXD RSEP fs ->
  forall rom Post M pk out wr mx sb spv src len h (eb : word) l,
  rt_ok M -> RTX M -> uar_on M -> cell BSEGS M 0x5e2598 8 (W 0x273870) -> fs_wf fs ->
  0 <= h < 2 ^ 64 -> cell BSEGS M fs 8 (W h) -> zeros M (fs + 4096) 16384 -> ring_wr M fs ->
  pkt_at M pk out wr mx sb eb -> pkt_wf pk out wr mx sb eb -> pk mod 8 = 0 -> mx < 32 -> sh0 M pk 56 -> wr_ok BSEGS M (pk + 16) 16 ->
  B_IMG_END <= spv - 2400 /\ spv < 2 ^ 63 /\ spv mod 32 = 0 -> wr_ok BSEGS M (spv - 2400) 2400 ->
  0 <= len < 2 ^ 62 ->
  memrange src len /\ addr_ok M src len /\ (0 < len -> shw_ok M src len) /\ rd_ok M src len ->
  B_IMG_END <= out /\ memrange out mx /\ addr_ok M out mx /\ (0 < mx -> shw_ok M out mx) /\ wr_ok BSEGS M out mx ->
  wm_sep fs spv pk out mx src len ->
  (forall x, FR_wm fs spv out mx pk x -> ~ RTXD x) -> RSEP (spv - 2400) 2400 ->
  length l = 32%nat -> rget l 2 = W spv -> rget l 4 = W TP ->
  rget l 10 = W pk -> rget l 11 = W src -> rget l 12 = W len ->
  (forall l' M' wr', length l' = 32%nat -> same_except KSC l l' ->
     (wm_ok wr mx len -> wr' = wr + len) -> (~ wm_ok wr mx len -> wr' = wr) ->
     pkt_at M' pk out wr' mx sb eb -> ring_idle M' fs ->
     unch M M' (FR_wm fs spv out mx pk) -> mem_grows M M' ->
     reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (W 0x273870) l M Post.
Proof.
  intros RTX RTXD RSEP fs IF rom Post M pk out wr mx sb spv src len h eb l; intros.
  eapply (wmemcpy_body RTX RTXD RSEP fs IF rom Post M pk out wr mx sb spv src len h (h mod 16384)
            (fs + 36864 + 64 * (h mod 16384)) eb) with (l0 := l); eauto.
Qed.


Print Assumptions wmemcpy_cps.
