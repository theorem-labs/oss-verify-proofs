(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): HEAD, [0x13cac, 0x13d64)
   up to LOOP at turn 0, and [0x13efc, 0x13f04) to TAIL (plain binary;
   fuzz_segconf.c:649-663), as V01_Inv.v_head_stmt states it from memset's and memcpy's contracts.
   The run (sp = S - 208, s0 = m, s3 = tab, s6 = cap, s10 = m + 0x2000):
   - 0x13cac `beqz s3` and 0x13cb4 `beqz a0` are not taken (4096 <= tab, mt: v01_geo); s2 = mt.
   - 0x13ccc memset(tab + 18 cap, 0x5a, 18) (memset_contract at 0x1e930): tab's zero cell is split at tab + 18 cap
     (v01h_split2); the guard entry tab[cap] reads 0x5a (guard_at).
   - 0x13cd0 .. 0x13cdc: a1 = 0, a0 = flags & 1 (8(sp)), `sw zero,0x3c(sp)`.
   - 0x13ce0 `beqz a0`, 0x13ce4 `beqz s6`: flags & 1 = 0 or cap = 0 go to JOIN with SegModel.vlan_init = [] (a1 = 0);
     else memcpy(tab, "enp1s0", 7) and memcpy(mt, "enp1s0", 7) (memcpy_contract at 0x1e52c; the source 0x10539 is
     .rodata: on a mem_inv memory its 7 bytes read seg_rom (v01h_enp_at), and it lies in a reserved segment, so it
     is apart from tab and mt, whose bytes are in no reserved segment: v01h_enp_apart), `sh 33,0x10(tab)`,
     `sw 33,0x10(mt)`, a1 = 1, `sw 1,0x3c(sp)`: vlan_init = [(S_enp, 33)] (rvlan_enc / mvlan_enc in V01HeadPure).
   - JOIN 0x13d28 (v01h_join): `sd s2,0x20(sp)`; s4 = `lw 0(s10)` = m->n (mconf_enc's u32 at MC_N, sign-extended);
     m->n = 0: 0x13efc `sd zero,0x18(sp)`, s6 = a1, TAIL with V01_RES = (0, tab0); else 0x13d34 .. 0x13d60 (s2 = 0,
     0x18(sp) = 0, s9 = -m, s11 = -10, s8 = 4094, 0x28(sp) = 2^50 + 3, s1 = m, s6 = a1) to LOOP at turn 0.
   [V01HeadPure] holds the lemmas that name no address of the image and no register.
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec seg_cuts memset_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import V01_Inv.
Import ListNotations.
Open Scope Z_scope.

Module V01HeadPure.

(* The payload's cap and flags bytes. *)
Lemma cap_rng : forall inp, 0 <= seg_cap inp < 40.
Proof.
  intros inp. unfold seg_cap, seg_pay, SegModel.decode.
  destruct (SegModel.fuzz_u8 (seg_in inp)) as [b0 i1]. destruct (SegModel.fuzz_u8 i1) as [fl i2].
  destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [SegModel.p_cap]. apply Z.mod_pos_bound. lia.
Qed.

Lemma zs_byte_ok : forall bs : list byte, Forall SegModel.byte_ok (zs bs).
Proof.
  intros bs. unfold zs. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _).
  unfold SegModel.byte_ok. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  exact R.
Qed.

Lemma flags_rng : forall inp, 0 <= seg_flags inp < 256.
Proof.
  intros inp. unfold seg_flags, seg_pay, SegModel.decode.
  pose proof (SegModel.u8_ok (seg_in inp) (zs_byte_ok inp)) as Hu. revert Hu.
  destruct (SegModel.fuzz_u8 (seg_in inp)) as [b0 i1]. cbn [fst snd]. intros [_ H1].
  pose proof (SegModel.u8_ok i1 H1) as Hu. revert Hu.
  destruct (SegModel.fuzz_u8 i1) as [fl i2]. cbn [fst snd]. intros [Hf _].
  destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [SegModel.p_flags]. exact Hf.
Qed.

(* SegModel.vlan_init (H:656-661): one entry ("enp1s0", 33) when flags & 1 and cap > 0, else none. *)
Lemma vlan_init_one : forall p, Z.land (p_flags p) 1 <> 0 -> 0 < p_cap p -> vlan_init p = [(S_enp, 33)].
Proof.
  intros p H1 H2. unfold vlan_init. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity.
Qed.

Lemma vlan_init_nil : forall p, Z.land (p_flags p) 1 = 0 \/ p_cap p <= 0 -> vlan_init p = [].
Proof.
  intros p [H|H]; unfold vlan_init.
  - rewrite (proj2 (Z.eqb_eq _ _) H). reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _) H), andb_false_r. reflexivity.
Qed.

Lemma tab0_one : forall inp, Z.land (seg_flags inp) 1 <> 0 -> 0 < seg_cap inp -> seg_tab0 inp = [(S_enp, 33)].
Proof. intros inp H1 H2. exact (vlan_init_one (seg_pay inp) H1 H2). Qed.

Lemma tab0_nil : forall inp, Z.land (seg_flags inp) 1 = 0 \/ seg_cap inp <= 0 -> seg_tab0 inp = [].
Proof. intros inp H. exact (vlan_init_nil (seg_pay inp) H). Qed.

Lemma n0_rng : forall inp, 0 <= Z.of_nat (length (seg_tab0 inp)) <= seg_cap inp.
Proof.
  intros inp. unfold seg_tab0. split; [lia|].
  apply vlan_init_len. exact (proj1 (cap_rng inp)).
Qed.

(* m_declared over no segment. *)
Lemma decl_nil : forall mc tab cap, mc_seg mc = [] -> m_declared mc tab cap = (0, tab).
Proof. intros mc tab cap H. unfold m_declared. rewrite H. reflexivity. Qed.

(* "enp1s0" and its NUL, the 7 bytes the harness copies (H:657, H:659). *)
Definition ENP : list byte := zb (S_enp ++ [0]).

Lemma enp_len : length ENP = 7%nat.
Proof. reflexivity. Qed.

Lemma firstn_zs : forall n (l : list byte), firstn n (zs l) = zs (firstn n l).
Proof. unfold zs. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma enp_cstr : forall f, length f = 16%nat -> firstn 7 f = ENP -> cstr_enc 16 S_enp f.
Proof.
  intros f Hl Hf. split; [exact Hl|]. split; [apply Nat.ltb_lt; vm_compute; reflexivity|]. split.
  - intros H. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H.
  - change (S (length S_enp)) with 7%nat. rewrite firstn_zs, Hf. vm_compute. reflexivity.
Qed.

(* The table entries ("enp1s0", 33): struct reac_declared_vlan (18 bytes) and struct mvlan (20 bytes). *)
Lemma rvlan_enp : rvlan_enc (S_enp, 33) (ENP ++ repeat ZERO 9 ++ le2 (Z_to_bv 64 33)).
Proof.
  unfold rvlan_enc. cbn [fst snd].
  split; [reflexivity|]. split; [apply enp_cstr; reflexivity|]. split; [lia | reflexivity].
Qed.

Lemma mvlan_enp : mvlan_enc (S_enp, 33) (ENP ++ repeat ZERO 9 ++ le4 (Z_to_bv 64 33)).
Proof.
  unfold mvlan_enc, u32_enc. cbn [fst snd].
  split; [reflexivity|]. split; [apply enp_cstr; reflexivity|]. split; [lia | reflexivity].
Qed.

Lemma rtab_enp : rtab_enc [(S_enp, 33)] (ENP ++ repeat ZERO 9 ++ le2 (Z_to_bv 64 33)).
Proof.
  split; [reflexivity|]. intros i Hi. destruct i as [|i].
  - exact rvlan_enp.
  - exfalso. cbn [length] in Hi. apply Nat.succ_lt_mono in Hi. exact (Nat.nlt_0_r _ Hi).
Qed.

Lemma mtab_enp : mtab_enc [(S_enp, 33)] (ENP ++ repeat ZERO 9 ++ le4 (Z_to_bv 64 33)).
Proof.
  split; [reflexivity|]. intros i Hi. destruct i as [|i].
  - exact mvlan_enp.
  - exfalso. cbn [length] in Hi. apply Nat.succ_lt_mono in Hi. exact (Nat.nlt_0_r _ Hi).
Qed.

Lemma rtab_nil : rtab_enc [] [].
Proof. split; [reflexivity|]. intros i Hi. exfalso. exact (Nat.nlt_0_r _ Hi). Qed.

Lemma mtab_nil : mtab_enc [] [].
Proof. split; [reflexivity|]. intros i Hi. exfalso. exact (Nat.nlt_0_r _ Hi). Qed.

End V01HeadPure.

Import V01HeadPure.

Lemma v01h_n0 : forall inp, 0 <= v_n0 inp <= seg_cap inp.
Proof. intros inp. exact (n0_rng inp). Qed.

(* ---- Words ---- *)
Lemma v01h_weq : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

Ltac v1_weq :=
  first [ reflexivity
        | f_equal; lia
        | apply v01h_weq; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Lemma v01h_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite MState.unsigned_lit by lia.
  rewrite bv_swrap_small; [reflexivity|]. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

(* Branch tactics (check_segments' CsPure.cs_ntk / cs_tkn): not taken / taken. *)
Ltac v1_ntk := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ exfalso; zify_cond K;
        try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
               ?Z.eqb_neq in K);
        lia
      | clear K ]
  end.
Ltac v1_tkn := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ clear K
      | exfalso; zify_cond K;
        try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
               ?Z.eqb_neq in K);
        lia ]
  end.

(* ---- Cells and bytes ---- *)
Lemma v01h_cb_iff : forall m A n bs, rw_cells rsegs m A [CB n bs] <->
  length bs = n /\ bytes_at rsegs m A bs /\ wr_at rsegs m A (Z.of_nat n).
Proof.
  intros m A n bs. unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma v01h_wr_lo : forall m a n k, wr_at rsegs m a n -> 0 <= k <= n -> wr_at rsegs m a k.
Proof. intros m a n k (H1 & H2 & H) Hk. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

Lemma v01h_wr_hi : forall m a n k, wr_at rsegs m a n -> 0 <= k <= n -> wr_at rsegs m (a + k) (n - k).
Proof.
  intros m a n k (H1 & H2 & H) Hk. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma v01h_split2 : forall m A A1 a r N, N = (a + r)%nat -> A1 = A + Z.of_nat a ->
  rw_cells rsegs m A [CB N (repeat ZERO N)] ->
  rw_cells rsegs m A [CB a (repeat ZERO a)] /\ rw_cells rsegs m A1 [CB r (repeat ZERO r)].
Proof.
  intros m A A1 a r N HN HA H. subst N A1. apply v01h_cb_iff in H as (_ & Hb & Hw).
  rewrite repeat_app in Hb. apply bytes_at_app in Hb as [Hb1 Hb2]. rewrite repeat_length in Hb2.
  split; apply v01h_cb_iff; (split; [apply repeat_length|]).
  - split; [exact Hb1|]. apply (v01h_wr_lo m A (Z.of_nat (a + r))); [exact Hw | lia].
  - split; [exact Hb2|]. replace (Z.of_nat r) with (Z.of_nat (a + r) - Z.of_nat a) by lia.
    apply v01h_wr_hi; [exact Hw | lia].
Qed.

Lemma v01h_split4 : forall m A A1 A2 A3 a b c r N, N = (a + b + c + r)%nat ->
  A1 = A + Z.of_nat a -> A2 = A1 + Z.of_nat b -> A3 = A2 + Z.of_nat c ->
  rw_cells rsegs m A [CB N (repeat ZERO N)] ->
  rw_cells rsegs m A [CB a (repeat ZERO a)] /\ rw_cells rsegs m A1 [CB b (repeat ZERO b)] /\
  rw_cells rsegs m A2 [CB c (repeat ZERO c)] /\ rw_cells rsegs m A3 [CB r (repeat ZERO r)].
Proof.
  intros m A A1 A2 A3 a b c r N HN H1 H2 H3 H.
  destruct (v01h_split2 m A A1 a (b + c + r) N ltac:(lia) H1 H) as [Ha H'].
  destruct (v01h_split2 m A1 A2 b (c + r) (b + c + r) ltac:(lia) H2 H') as [Hb H''].
  destruct (v01h_split2 m A2 A3 c r (c + r) ltac:(lia) H3 H'') as [Hc Hr].
  auto.
Qed.

Lemma v01h_rw_eq : forall m A A' n n' bs, rw_cells rsegs m A [CB n bs] -> A = A' -> n = n' ->
  rw_cells rsegs m A' [CB n' bs].
Proof. intros; subst; assumption. Qed.

Lemma v01h_rwz_eq : forall m A A' n n', rw_cells rsegs m A [CB n (repeat ZERO n)] -> A = A' -> n = n' ->
  rw_cells rsegs m A' [CB n' (repeat ZERO n')].
Proof. intros; subst; assumption. Qed.

Lemma v01h_rw_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs H. apply v01h_cb_iff in H. tauto. Qed.

Lemma v01h_rw_c2 : forall m A v, rw_cells rsegs m A [C2 v] -> bytes_at rsegs m A (le2 v).
Proof. intros m A v [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma v01h_rw_c4 : forall m A v, rw_cells rsegs m A [C4 v] -> bytes_at rsegs m A (le4 v).
Proof. intros m A v [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma v01h_ba_eq : forall m a a' bs, bytes_at rsegs m a bs -> a = a' -> bytes_at rsegs m a' bs.
Proof. intros; subst; assumption. Qed.

Lemma v01h_bytes3 : forall m A A1 A2 b1 b2 b3, bytes_at rsegs m A b1 -> bytes_at rsegs m A1 b2 ->
  bytes_at rsegs m A2 b3 -> A1 = A + Z.of_nat (length b1) -> A2 = A1 + Z.of_nat (length b2) ->
  bytes_at rsegs m A (b1 ++ b2 ++ b3).
Proof.
  intros m A A1 A2 b1 b2 b3 H1 H2 H3 E1 E2. subst A1 A2.
  apply bytes_at_app. split; [exact H1|]. apply bytes_at_app. split; [exact H2 | exact H3].
Qed.

(* A u32 field at offset k of a block as a 4-byte read-only cell (CsPure.cs_rd4 in cell form). *)
Lemma v01h_rd4 : forall m a bs k v, bytes_at rsegs m a bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  u32_enc v (fldz k 4 bs) -> ro_cells rsegs m (a + k) [C4 (Z_to_bv 64 v)].
Proof.
  intros m a bs k v H Hk Hl (_ & E). split; [exact (conj I I)|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r, <- E. unfold fldz, fld. change (Z.to_nat 4) with 4%nat.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia. rewrite Z2Nat.id in H by lia.
  rewrite <- (firstn_skipn 4 (skipn (Z.to_nat k) bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(* Main's frame cells. *)
Lemma v01h_frame : forall S m w00 w08 w10 w18 w20 w28 w30 w38 w3c v10 v18 v20 v28 v30 v3c,
  rw_cells rsegs m (S - 208) [C8 w00; C8 w08; C8 w10; C8 w18; C8 w20; C8 w28; C8 w30; C4 w38; C4 w3c] ->
  w10 = v10 -> w18 = v18 -> w20 = v20 -> w28 = v28 -> w30 = v30 -> w3c = v3c ->
  v01_frame S w00 w08 v10 v18 v20 v28 v30 w38 v3c m.
Proof. intros; subst; assumption. Qed.

(* ---- "enp1s0" in .rodata ---- *)
Lemma v01h_enp_ro : ro_bytes_b rsegs 0x10539 ENP = true.
Proof. vm_compute. reflexivity. Qed.

Lemma v01h_enp_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10539 ENP.
Proof.
  intros m H. apply (ro_bytes_at rsegs m 0x10539 ENP H); [lia | rewrite enp_len; lia |].
  apply ro_bytes_b_sound. exact v01h_enp_ro.
Qed.

(* One reserved segment of the image covers [0x10539, 0x10540). *)
Lemma v01h_enp_resv : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x10539) &&
    (0x10540 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

(* A block in no reserved segment is apart from those 7 bytes. *)
Lemma v01h_enp_apart : forall a n, blk_noimg rsegs a n -> 7 <= n -> 0x10539 + 7 <= a \/ a + 7 <= 0x10539.
Proof.
  intros a n Hn H7.
  pose proof v01h_enp_resv as R. apply existsb_exists in R as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct (Z_le_gt_dec (0x10539 + 7) a) as [Ha|Ha]; [left; exact Ha|].
  destruct (Z_le_gt_dec (a + 7) 0x10539) as [Hb|Hb]; [right; exact Hb|].
  exfalso. apply (Hn (Z.max 0 (0x10539 - a)) ltac:(lia) s Hs). lia.
Qed.

(* ---- The memory invariants across a run that writes only the stack window ---- *)
Lemma v01h_mem_frame : forall inp S c mm tab mt m0 m m', v01_geo inp S c mm tab mt ->
  v01_mem inp S tab mt m0 m -> munch [(S - 65536, S - 104)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (S - 65536) (S - 208) -> v01_mem inp S tab mt m0 m'.
Proof.
  intros inp S c mm tab mt m0 m m' G (MU & WM & _ & _ & (bs & HB & HE) & (fr & HF) & HG) MU' WM' MI' ST'.
  pose proof G as (_ & G2 & G3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G13 & G14 & _).
  pose proof (cap_rng inp) as Hcap. pose proof (v01h_n0 inp) as Hn0.
  unfold TAB_N, RVLAN_SIZE in G14. unfold guard_at in *. unfold v_n0, v_cap, RVLAN_SIZE in *.
  split; [|split; [|split; [exact MI'|split; [exact ST'|]]]].
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU'].
    unfold sub_fp, v01_W. cbn [outside]. intros x (Hx & _). split; [exact Hx | exact I].
  - eapply wmono_trans; [exact WM | exact WM'].
  - split; [|split].
    + exists bs. split; [|exact HE]. apply (bytes_at_transport rsegs [(S - 65536, S - 104)] m m' tab bs HB MU').
      destruct HE as (L & _). rewrite L. cbn [disjoint_from]. split; [lia | exact I].
    + exists fr. apply (rw_cells_transport rsegs [(S - 65536, S - 104)] m m' _ _ HF MU' WM').
      cbn [disjoint_from cells_size csize]. split; [lia | exact I].
    + apply (bytes_at_transport rsegs [(S - 65536, S - 104)] m m' _ _ HG MU').
      cbn [disjoint_from]. unfold GUARD_BYTES. rewrite repeat_length. split; [lia | exact I].
Qed.

Lemma v01h_mt_frame : forall inp S c mm tab mt T m m', v01_geo inp S c mm tab mt ->
  v01_mt inp mt T m -> munch [(S - 65536, S - 104)] m m' -> wmono rsegs m m' -> v01_mt inp mt T m'.
Proof.
  intros inp S c mm tab mt T m m' G (HL & (bs & HB & HE) & (fr & HF)) MU' WM'.
  pose proof G as (_ & G2 & G3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G17 & G18 & _).
  pose proof (cap_rng inp) as Hcap.
  unfold MT_N, MVLAN_SIZE in G18. unfold v_cap, MVLAN_SIZE in *.
  split; [exact HL|]. split.
  - exists bs. split; [|exact HE]. apply (bytes_at_transport rsegs [(S - 65536, S - 104)] m m' mt bs HB MU').
    destruct HE as (L & _). rewrite L. cbn [disjoint_from]. split; [lia | exact I].
  - exists fr. apply (rw_cells_transport rsegs [(S - 65536, S - 104)] m m' _ _ HF MU' WM').
    cbn [disjoint_from cells_size csize]. split; [lia | exact I].
Qed.

(* ---- The memory invariants at JOIN from the cells HEAD leaves ---- *)
Lemma v01h_mem_nil : forall inp S tab mt m0 m, v_tab0 inp = [] ->
  munch [(S - 65536, S - 104); (mt, mt + 20 * (seg_cap inp + 1)); (tab, tab + 18 * (seg_cap inp + 1))] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m (S - 65536) (S - 208) ->
  rw_cells rsegs m tab [CB (Z.to_nat (18 * seg_cap inp)) (repeat ZERO (Z.to_nat (18 * seg_cap inp)))] ->
  rw_cells rsegs m (tab + 18 * seg_cap inp) [CB 18 GUARD_BYTES] ->
  v01_mem inp S tab mt m0 m.
Proof.
  intros inp S tab mt m0 m HT MU WM MI ST TB GD.
  pose proof (rw_cells_bound rsegs m tab _ TB) as Btab. pose proof (cap_rng inp) as Hcap.
  unfold v01_mem, v01_W, TAB_N, MT_N, v_n0, v_cap, guard_at, RVLAN_SIZE, MVLAN_SIZE. rewrite HT.
  cbn [length Z.of_nat].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exists []; split; [apply bytes_at_nil; lia | exact rtab_nil]|].
  split; [eexists; eapply v01h_rw_eq; [exact TB | lia | lia] | exact (v01h_rw_bytes _ _ _ _ GD)].
Qed.

Lemma v01h_mt_nil : forall inp mt m, v_tab0 inp = [] ->
  rw_cells rsegs m mt [CB (Z.to_nat (20 * (seg_cap inp + 1))) (repeat ZERO (Z.to_nat (20 * (seg_cap inp + 1))))] ->
  v01_mt inp mt (v_tab0 inp) m.
Proof.
  intros inp mt m HT MT. pose proof (rw_cells_bound rsegs m mt _ MT) as Bmt. pose proof (cap_rng inp) as Hcap.
  unfold v01_mt, v_cap, MVLAN_SIZE. rewrite HT. cbn [length Z.of_nat].
  split; [lia|]. split; [exists []; split; [apply bytes_at_nil; lia | exact mtab_nil]|].
  eexists; eapply v01h_rw_eq; [exact MT | lia | lia].
Qed.

Lemma v01h_mem_one : forall inp S tab mt m0 m, v_tab0 inp = [(S_enp, 33)] -> 1 <= seg_cap inp ->
  munch [(S - 65536, S - 104); (mt, mt + 20 * (seg_cap inp + 1)); (tab, tab + 18 * (seg_cap inp + 1))] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m (S - 65536) (S - 208) ->
  rw_cells rsegs m tab [CB 7 ENP] -> rw_cells rsegs m (tab + 7) [CB 9 (repeat ZERO 9)] ->
  rw_cells rsegs m (tab + 16) [C2 (Z_to_bv 64 33)] ->
  rw_cells rsegs m (tab + 18)
    [CB (Z.to_nat (18 * seg_cap inp) - 18) (repeat ZERO (Z.to_nat (18 * seg_cap inp) - 18))] ->
  rw_cells rsegs m (tab + 18 * seg_cap inp) [CB 18 GUARD_BYTES] ->
  v01_mem inp S tab mt m0 m.
Proof.
  intros inp S tab mt m0 m HT Hc MU WM MI ST E1 E2 E3 E4 GD.
  unfold v01_mem, v01_W, TAB_N, MT_N, v_n0, v_cap, guard_at, RVLAN_SIZE, MVLAN_SIZE. rewrite HT.
  cbn [length Z.of_nat Pos.of_succ_nat].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split.
  { exists (ENP ++ repeat ZERO 9 ++ le2 (Z_to_bv 64 33)). split; [|exact rtab_enp].
    apply (v01h_bytes3 m tab (tab + 7) (tab + 16)).
    - exact (v01h_rw_bytes _ _ _ _ E1).
    - exact (v01h_rw_bytes _ _ _ _ E2).
    - exact (v01h_rw_c2 _ _ _ E3).
    - rewrite enp_len. lia.
    - rewrite repeat_length. lia. }
  split; [eexists; eapply v01h_rw_eq; [exact E4 | lia | lia] | exact (v01h_rw_bytes _ _ _ _ GD)].
Qed.

Lemma v01h_mt_one : forall inp mt m, v_tab0 inp = [(S_enp, 33)] -> 1 <= seg_cap inp ->
  rw_cells rsegs m mt [CB 7 ENP] -> rw_cells rsegs m (mt + 7) [CB 9 (repeat ZERO 9)] ->
  rw_cells rsegs m (mt + 16) [C4 (Z_to_bv 64 33)] ->
  rw_cells rsegs m (mt + 20)
    [CB (Z.to_nat (20 * (seg_cap inp + 1)) - 20) (repeat ZERO (Z.to_nat (20 * (seg_cap inp + 1)) - 20))] ->
  v01_mt inp mt (v_tab0 inp) m.
Proof.
  intros inp mt m HT Hc E1 E2 E3 E4. unfold v01_mt, v_cap, MVLAN_SIZE. rewrite HT.
  cbn [length Z.of_nat Pos.of_succ_nat].
  split; [lia|]. split.
  { exists (ENP ++ repeat ZERO 9 ++ le4 (Z_to_bv 64 33)). split; [|exact mtab_enp].
    apply (v01h_bytes3 m mt (mt + 7) (mt + 16)).
    - exact (v01h_rw_bytes _ _ _ _ E1).
    - exact (v01h_rw_bytes _ _ _ _ E2).
    - exact (v01h_rw_c4 _ _ _ E3).
    - rewrite enp_len. lia.
    - rewrite repeat_length. lia. }
  eexists; eapply v01h_rw_eq; [exact E4 | lia | lia].
Qed.

(* ---- The continuations in register-equation form ---- *)
Lemma v01h_kloop0 : forall inp S c mm tab mt m0 gp tp F fc Q, K_loop inp S c mm tab mt m0 gp tp F fc Q ->
  forall T added m (ra x2 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 s5 x22 s7 x24 x25 x26 x27 t3 t4 t5
                    t6 : word),
  v01_loop_mem inp S c tab mt m0 0 0 T added m ->
  x2 = Z_to_bv 64 (S - 208) -> x8 = Z_to_bv 64 mm -> x9 = Z_to_bv 64 (mm + 256 * Z.of_nat 0) ->
  x18 = Z_to_bv 64 (Z.of_nat 0) -> x19 = Z_to_bv 64 tab -> x20 = Z_to_bv 64 (v_nsegs inp) ->
  x22 = Z_to_bv 64 (Z.of_nat (length T)) -> x24 = Z_to_bv 64 4094 ->
  x25 = Z_to_bv 64 (- (mm + 256 * Z.of_nat 0)) -> x26 = Z_to_bv 64 (mm + 0x2000) -> x27 = Z_to_bv 64 (-10) ->
  evt rsegs Q (MS (mkR ra x2 gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 s5 x22 s7 x24 x25 x26 x27
                       t3 t4 t5 t6) F (Z_to_bv 64 0x13d64) fc None m (seg_rom rsegs)).
Proof.
  intros inp S c mm tab mt m0 gp tp F fc Q KL T added m ra x2 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
    s5 x22 s7 x24 x25 x26 x27 t3 t4 t5 t6 HM E2 E8 E9 E18 E19 E20 E22 E24 E25 E26 E27.
  subst x2 x8 x9 x18 x19 x20 x22 x24 x25 x26 x27.
  exact (KL 0%nat T added ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 m HM).
Qed.

Lemma v01h_ktail0 : forall inp S c mm tab mt m0 gp tp F fc Q, K_tail inp S c mm tab mt m0 gp tp F fc Q ->
  forall m (ra x2 t0 t1 t2 x8 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 x19 s4 s5 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  v01_tail_mem inp S c tab mt m0 m ->
  x2 = Z_to_bv 64 (S - 208) -> x8 = Z_to_bv 64 mm -> x19 = Z_to_bv 64 tab ->
  x22 = Z_to_bv 64 (Z.of_nat (length (snd (V01_RES inp)))) ->
  evt rsegs Q (MS (mkR ra x2 gp tp t0 t1 t2 x8 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 x19 s4 s5 x22 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x13f04) fc None m (seg_rom rsegs)).
Proof.
  intros inp S c mm tab mt m0 gp tp F fc Q KT m ra x2 t0 t1 t2 x8 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 x19 s4 s5 x22 s7
    s8 s9 s10 s11 t3 t4 t5 t6 HM E2 E8 E19 E22.
  subst x2 x8 x19 x22.
  exact (KT ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 m HM).
Qed.

(* ---- JOIN 0x13d28 .. 0x13d64 / 0x13f04 ---- *)
Lemma v01h_join : forall (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop),
  v01_geo inp S c mm tab mt -> v01_base inp c mm m0 ->
  K_loop inp S c mm tab mt m0 gp tp F fc Q -> K_tail inp S c mm tab mt m0 gp tp F fc Q ->
  forall (ra x2 t0 t1 t2 x8 s1 a0 x11 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 x26 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (w00 w08 w18 w20 w28 w38 w3c : word) (vb : list byte),
  rw_cells rsegs m (S - 208)
    [C8 w00; C8 w08; C8 (Z_to_bv 64 (v_cap inp)); C8 w18; C8 w20; C8 w28; C8 (Z_to_bv 64 c); C4 w38; C4 w3c] ->
  rw_cells rsegs m (S - 208 + 64) [CB 20 vb] ->
  v01_mem inp S tab mt m0 m -> v01_mt inp mt (v_tab0 inp) m ->
  x2 = Z_to_bv 64 (S - 208) -> x8 = Z_to_bv 64 mm -> x11 = Z_to_bv 64 (v_n0 inp) -> x18 = Z_to_bv 64 mt ->
  x19 = Z_to_bv 64 tab -> x26 = Z_to_bv 64 (mm + 0x2000) -> w3c = Z_to_bv 64 (v_n0 inp) ->
  evt rsegs Q (MS (mkR ra x2 gp tp t0 t1 t2 x8 s1 a0 x11 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 x26 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x13d28) fc None m (seg_rom rsegs)).
Proof.
  intros inp S c mm tab mt m0 gp tp F fc Q G B KL KT ra x2 t0 t1 t2 x8 s1 a0 x11 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5
    s6 s7 s8 s9 x26 s11 t3 t4 t5 t6 m w00 w08 w18 w20 w28 w38 w3c vb FR VB VM VT E2 E8 E11 E18 E19 E26 E3c.
  subst x2 x8 x11 x18 x19 x26 w3c.
  pose proof G as (_ & G2 & G3 & _ & _ & _ & _ & _ & G9 & G10 & _ & _ & G13 & G14 & _ & _ & G17 & G18 & _ & _ &
                   _ & _ & _ & G24 & G25 & _).
  pose proof (cap_rng inp) as Hcap. pose proof (v01h_n0 inp) as Hn0.
  unfold TAB_N, MT_N, RVLAN_SIZE, MVLAN_SIZE, SEG_M_SIZE in G10, G14, G18, G24, G25.
  unfold apart in G24, G25.
  unfold v_cap in FR.
  (* m->n at m + 0x2000, from mconf_at m0 m, kept by the run so far (m is apart from v01_W) *)
  pose proof B as (_ & (bsm & BM & EM) & _ & _).
  pose proof EM as (LM & L32 & _ & UN & _). unfold SEG_M_SIZE in LM.
  pose proof VM as (MU0 & _ & MI & ST & _).
  assert (BM' : bytes_at rsegs m mm bsm).
  { apply (bytes_at_transport rsegs (v01_W inp S tab mt) m0 m mm bsm BM MU0).
    unfold v01_W, TAB_N, MT_N, RVLAN_SIZE, MVLAN_SIZE. cbn [disjoint_from]. rewrite LM.
    split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (RN : ro_cells rsegs m (mm + 8192) [C4 (Z_to_bv 64 (v_nsegs inp))]).
  { apply (v01h_rd4 m mm bsm 8192 (v_nsegs inp) BM'); [lia | lia | exact UN]. }
  assert (Hn32 : 0 <= v_nsegs inp <= 32) by (unfold v_nsegs, v_segs; lia).
  clear MU0 BM BM' EM LM UN B.
  pose proof (munch_refl [(S - 65536, S - 104)] m) as MUs.
  pose proof (wmono_refl rsegs m) as WMs.
  (* 0x13d28 sd s2,0x20(sp) *)
  zstep.
  (* 0x13d2c lw s4,0(s10) *)
  zstep.
  rewrite (v01h_sx32 (v_nsegs inp)) by lia.
  (* 0x13d30 blez s4 *)
  zstep.
  destruct (Z.eq_dec (v_nsegs inp) 0) as [N0 | N0].
  - (* m->n = 0: 0x13efc sd zero,0x18(sp); 0x13f00 mv s6,a1; TAIL *)
    v1_tkn.
    zstep. zstep.
    assert (Hseg : v_segs inp = []).
    { destruct (v_segs inp) as [|g l] eqn:E; [reflexivity|]. exfalso.
      unfold v_nsegs in N0. rewrite E in N0. cbn [length] in N0. rewrite Nat2Z.inj_succ in N0.
      unfold Z.succ in N0. lia. }
    assert (ER : V01_RES inp = (0, v_tab0 inp)).
    { unfold V01_RES. apply decl_nil. exact Hseg. }
    eapply (v01h_ktail0 inp S c mm tab mt m0 gp tp F fc Q KT).
    + unfold v01_tail_mem. rewrite ER. cbn [fst snd].
      split; [exact (v01h_mem_frame inp S c mm tab mt m0 m _ G VM MUs WMs MI ST)|].
      split; [exact (v01h_mt_frame inp S c mm tab mt (v_tab0 inp) m _ G VT MUs WMs)|].
      exists w00, w08, w28, w38. eapply v01h_frame; [exact FR | v1_weq ..].
    + v1_weq.
    + v1_weq.
    + v1_weq.
    + rewrite ER. cbn [snd]. v1_weq.
  - (* m->n > 0: 0x13d34 .. 0x13d60; LOOP at turn 0 *)
    assert (Np : 0 < v_nsegs inp) by lia.
    v1_ntk.
    do 12 zstep.
    eapply (v01h_kloop0 inp S c mm tab mt m0 gp tp F fc Q KL (v_tab0 inp) 0).
    + split.
      { destruct (v_segs inp) as [|g l] eqn:E; [exfalso; apply N0; unfold v_nsegs; rewrite E; reflexivity|].
        cbn [length]. apply Nat.lt_0_succ. }
      split; [split; [unfold v_n0; apply Z.add_0_l | reflexivity]|].
      split; [exact (v01h_mem_frame inp S c mm tab mt m0 m _ G VM MUs WMs MI ST)|].
      split; [exact (v01h_mt_frame inp S c mm tab mt (v_tab0 inp) m _ G VT MUs WMs)|].
      split; [exists w00, w08, w38; eapply v01h_frame; [exact FR | v1_weq ..]|].
      exists vb. exact VB.
    + v1_weq.
    + v1_weq.
    + v1_weq.
    + v1_weq.
    + v1_weq.
    + v1_weq.
    + v1_weq.
    + v1_weq.
    + v1_weq.
    + v1_weq.
    + v1_weq.
Qed.

(* ---- Transport across a callee: the cells, the stack, the write set and wmono ---- *)
Ltac v1_dj := cbn [disjoint_from cells_size csize]; simpl_sizes; split; [lia | exact I].

Ltac v1_tr MU1 WM1 :=
  lazymatch type of MU1 with munch ?W ?m ?m1 =>
  repeat match goal with
  | H : rw_cells rsegs m ?A ?cs |- _ =>
      apply (rw_cells_transport rsegs W m m1 A cs) in H; [ | exact MU1 | exact WM1 | v1_dj ]
  | H : stk rsegs m ?lo ?hi |- _ =>
      apply (stk_transport_disjoint rsegs W m m1 lo hi) in H; [ | exact MU1 | exact WM1 | v1_dj ]
  | H : munch ?Wq ?mq m |- _ =>
      apply (munch_trans Wq mq m m1) in H;
      [ | apply (munch_weaken W Wq m m1); [ unfold sub_fp; cbn [outside]; intros ? ?; split; [lia | exact I]
                                          | exact MU1 ] ]
  | H : wmono rsegs ?mq m |- _ => apply (wmono_trans rsegs mq m m1) in H; [ | exact WM1 ]
  end
  end; clear MU1 WM1.

Ltac v1_eq HT :=
  first [ reflexivity | (unfold v_n0; rewrite HT; reflexivity) | v1_weq ].

(* ---- HEAD 0x13cac .. 0x13d28 ---- *)
Lemma v01_head : memset_contract -> memcpy_contract -> v01_head_stmt.
Proof.
  intros MSC MCC. unfold v01_head_stmt.
  intros inp S c mm tab mt m gp tp F fc Q ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s9 s11 t3 t4 t5 t6
    G B P KL KT.
  pose proof G as (_ & G2 & G3 & _ & _ & _ & _ & _ & G9 & G10 & _ & _ & G13 & G14 & _ & G16 & G17 & G18 & _ & G20 &
                   _ & _ & _ & _ & _ & G26).
  destruct P as (MI & ST & (w00 & w18 & w20 & w28 & w38 & w3c & FR) & (vb & VB) & TB & MTB).
  pose proof (cap_rng inp) as Hcap. pose proof (flags_rng inp) as Hfl.
  unfold v01_frame in FR. unfold v_cap in *.
  unfold TAB_N, MT_N, RVLAN_SIZE, MVLAN_SIZE, SEG_M_SIZE in G10, G14, G16, G18, G20, G26, TB, MTB.
  pose proof (v01h_enp_apart tab _ G16 ltac:(lia)) as APt.
  pose proof (v01h_enp_apart mt _ G20 ltac:(lia)) as APm.
  clear G16 G20.
  unfold apart in G26.
  pose proof (munch_refl [(S - 65536, S - 104); (mt, mt + 20 * (seg_cap inp + 1));
                          (tab, tab + 18 * (seg_cap inp + 1))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* tab: its entries [tab, tab + 18 cap) and the guard entry tab[cap] *)
  destruct (v01h_split2 m tab (tab + 18 * seg_cap inp) (Z.to_nat (18 * seg_cap inp)) 18
              (Z.to_nat (18 * (seg_cap inp + 1))) ltac:(lia) ltac:(lia) TB) as [TB1 GD].
  clear TB.
  unfold vst.
  (* 0x13cac beqz s3 *)
  zstep. v1_ntk.
  (* 0x13cb0 mv s2,a0 *)
  zstep.
  (* 0x13cb4 beqz a0 *)
  zstep. v1_ntk.
  (* 0x13cb8 li a0,18; 0x13cbc mul a0,s6,a0; 0x13cc0 add a0,s3,a0; 0x13cc4 li a1,0x5a; 0x13cc8 li a2,18 *)
  do 5 zstep.
  (* 0x13ccc jal memset *)
  zstep.
  eapply evt_cut.
  { eapply MSC; [|assumption].
    eapply v01h_rwz_eq; [exact GD | rewrite MState.unsigned_lit by lia; lia | reflexivity]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU1 & WM1 & MI1 & GD1).
  rewrite !MState.unsigned_lit in MU1, GD1 by lia.
  change (Z.to_nat 18) with 18%nat in GD1. change (90 mod 256) with 90 in GD1.
  pose proof (v01h_rw_eq _ _ (tab + 18 * seg_cap inp) _ 18%nat _ GD1 ltac:(lia) eq_refl) as GD2.
  clear GD GD1. rename GD2 into GD1.
  v1_tr MU1 WM1.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13cd0 mv a1,zero; 0x13cd4 ld a0,8(sp); 0x13cd8 andi a0,a0,1; 0x13cdc sw zero,0x3c(sp) *)
  do 4 zstep.
  (* 0x13ce0 beqz a0; 0x13ce4 beqz s6 *)
  zstep.
  destruct (Z.eq_dec (Z.land (seg_flags inp) 1) 0) as [L0 | L0];
    [ v1_tkn
    | v1_ntk; zstep; destruct (Z.eq_dec (seg_cap inp) 0) as [C0 | C0]; [v1_tkn | v1_ntk] ].
  3: {
  (* flags & 1 and cap > 0: the entry ("enp1s0", 33) in tab[0] and mt[0] *)
  assert (Hc1 : 1 <= seg_cap inp) by lia.
  assert (HT : v_tab0 inp = [(S_enp, 33)]) by (apply tab0_one; [exact L0 | lia]).
  destruct (v01h_split4 _ tab (tab + 7) (tab + 16) (tab + 18) 7 9 2 (Z.to_nat (18 * seg_cap inp) - 18)
              (Z.to_nat (18 * seg_cap inp)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) TB1) as (T1 & T2 & T3 & T4).
  clear TB1.
  destruct (v01h_split4 _ mt (mt + 7) (mt + 16) (mt + 20) 7 9 4 (Z.to_nat (20 * (seg_cap inp + 1)) - 20)
              (Z.to_nat (20 * (seg_cap inp + 1))) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) MTB)
    as (M1 & M2 & M3 & M4).
  clear MTB.
  (* 0x13ce8 auipc a0; 0x13cec addi s5,a0,-0x7af; 0x13cf0 li a2,7; 0x13cf4 mv a0,s3; 0x13cf8 mv a1,s5 *)
  do 5 zstep.
  (* 0x13cfc jal memcpy (tab, "enp1s0", 7) *)
  zstep.
  eapply evt_cut.
  { eapply MCC with (src := ENP).
    - eapply v01h_ba_eq; [apply v01h_enp_at; eassumption | reflexivity].
    - reflexivity.
    - eapply v01h_rwz_eq; [exact T1 | rewrite MState.unsigned_lit by lia; lia | reflexivity].
    - rewrite !MState.unsigned_lit by lia. lia.
    - assumption. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU3 & WM3 & MI3 & E1 & _).
  rewrite !MState.unsigned_lit in MU3, E1 by lia. change (Z.to_nat 7) with 7%nat in E1.
  clear T1.
  v1_tr MU3 WM3.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13d00 li s1,33; 0x13d04 sh s1,0x10(s3) *)
  zstep. zstep.
  (* 0x13d08 li a2,7; 0x13d0c mv a0,s2; 0x13d10 mv a1,s5 *)
  do 3 zstep.
  (* 0x13d14 jal memcpy (mt, "enp1s0", 7) *)
  zstep.
  eapply evt_cut.
  { eapply MCC with (src := ENP).
    - eapply v01h_ba_eq; [apply v01h_enp_at; eassumption | reflexivity].
    - reflexivity.
    - eapply v01h_rwz_eq; [exact M1 | rewrite MState.unsigned_lit by lia; lia | reflexivity].
    - rewrite !MState.unsigned_lit by lia. lia.
    - assumption. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU5 & WM5 & MI5 & E2 & _).
  rewrite !MState.unsigned_lit in MU5, E2 by lia. change (Z.to_nat 7) with 7%nat in E2.
  clear M1.
  v1_tr MU5 WM5.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13d18 sw s1,0x10(s2); 0x13d1c li a0,1; 0x13d20 li a1,1; 0x13d24 sw a0,0x3c(sp) *)
  do 4 zstep.
  (* JOIN *)
  eapply (v01h_join inp S c mm tab mt m gp tp F fc Q G B KL KT).
  - eassumption.
  - eassumption.
  - apply (v01h_mem_one inp S tab mt m _ HT Hc1); assumption.
  - apply (v01h_mt_one inp mt _ HT Hc1); assumption.
  - v1_eq HT.
  - v1_eq HT.
  - v1_eq HT.
  - v1_eq HT.
  - v1_eq HT.
  - v1_eq HT.
  - v1_eq HT.
  }
  (* flags & 1 = 0, or cap = 0: no entry *)
  all: assert (HT : v_tab0 inp = []) by (apply tab0_nil; lia).
  all: eapply (v01h_join inp S c mm tab mt m gp tp F fc Q G B KL KT);
         [ eassumption | eassumption
         | apply (v01h_mem_nil inp S tab mt m _ HT); assumption
         | apply (v01h_mt_nil inp mt _ HT); assumption
         | v1_eq HT .. ].
Qed.
