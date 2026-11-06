(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits AxMalloc MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS
                        MngGM AXG_ntfm AXG_ntfg AXG_nQ AXG_nD AXG_tam AXG_as1 AXG_as2 AXG_as4 AxTry AXF_efbz AXF_mcc.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_spsz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_spsz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint span_done (f : nat) (sp size : Z) : bool :=
  match f with
  | O => false
  | S f' => if Z.lxor sp (sp + size - 1) <? 4096 then span_done f' (sp + size) size else true
  end.

Definition span_chk (sc : Z) : bool := forall_from (fun a => span_done 300 (16 + class_size sc * (a + 2)) (class_size sc)) 0 32.

Lemma span_chk_all : forall_from span_chk 1 47 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma span_done_inst : forall sc a, 1 <= sc <= 47 -> 0 <= a <= 31 -> span_done 300 (16 + class_size sc * (a + 2)) (class_size sc) = true.
Proof.
  intros sc a Hs Ha. pose proof (forall_from_ok _ _ _ span_chk_all sc ltac:(cbn; lia)) as H1. unfold span_chk in H1.
  exact (forall_from_ok _ _ _ H1 a ltac:(cbn; lia)).
Qed.

Lemma bits_lt : forall x n, 0 <= x -> 0 <= n -> (forall j, n <= j -> Z.testbit x j = false) -> x < 2^n.
Proof.
  intros x n Hx Hn Hb. destruct (Z.eq_dec x 0) as [->|Hnz]; [apply Z.pow_pos_nonneg; lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia.
  destruct (Z.lt_ge_cases (Z.log2 x) n) as [Hl|Hg]; [exact Hl|]. exfalso.
  pose proof (Z.bit_log2 x ltac:(lia)) as Hbit. rewrite Hb in Hbit by lia. discriminate.
Qed.

Lemma lxor_small : forall a b, 0 <= a < 2^28 -> 0 <= b < 2^28 -> 0 <= Z.lxor a b < 2^28.
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|]. apply bits_lt; [apply Z.lxor_nonneg; lia | lia |].
  intros j Hj. rewrite Z.lxor_spec.
  assert (A : Z.testbit a j = false).
  { destruct (Z.eq_dec a 0) as [->|Ha0]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|].
    assert (Z.log2 a < 28) by (apply Z.log2_lt_pow2; lia). lia. }
  assert (B : Z.testbit b j = false).
  { destruct (Z.eq_dec b 0) as [->|Hb0]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|].
    assert (Z.log2 b < 28) by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite A, B. reflexivity.
Qed.

Section SPAN.
Context {fx : FPState}.

Ltac spiscs Z32 Z35 :=
  repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite u_xor64, Z32, Z35.

(* [comment removed for export] *)
#[using="Type"] Lemma span_run : forall f c sp size (R : bvmap 5 word) m rom,
  span_done f sp size = true ->
  getr R 5 = wa sp -> getr R 14 = wa (c - 1) -> getr R 15 = wa size -> getr R 16 = wa (sp + size - 1) -> getr R 17 = wa 4096 ->
  1 <= c -> c + Z.of_nat f <= 2^28 -> 16 <= size <= 2^20 -> 0 <= sp -> sp + (Z.of_nat f + 1) * size <= 2^28 ->
  exists R', msteps SEGS (mkst R (wa 0x5280c) m rom) (mkst R' (wa 0x52820) m rom) /\ getr R' 14 = wa (span_loop f c sp size) /\
    (forall k, In k [1;2;3;4;7;8;9;10;11;12;13;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%nat ->
       getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction f as [|f IH]; intros c sp size R m rom Hd R5 R14 R15 R16 R17 Hc Hcf Hsz Hsp Hspf; [discriminate|].
  cbn [span_done] in Hd. cbn [span_loop].
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spiz.spi_pre R m sp (c - 1) size (sp + size - 1)).
  { constructor; try assumption; clear - Hc Hcf Hsz Hsp Hspf; lia. }
  assert (XR : 0 <= Z.lxor (sp + size - 1) sp < 2^28) by (apply lxor_small; clear - Hc Hcf Hsz Hsp Hspf; lia).
  set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spiz.VALS_spi sp (c - 1) size (sp + size - 1))).
  assert (Z32 : bv_unsigned (ev E 32) = sp) by (apply zatom; [reflexivity | reflexivity | clear - Hc Hcf Hsz Hsp Hspf; lia]).
  assert (Z35 : bv_unsigned (ev E 35) = sp + size - 1) by (apply zatom; [reflexivity | reflexivity | clear - Hc Hcf Hsz Hsp Hspf; lia]).
  destruct (Z.lxor sp (sp + size - 1) <? 4096) eqn:Ec.
  - destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spiz.spi_pspl R m rom sp (c - 1) size (sp + size - 1) P) as (R1 & M1 & Q5 & Q14 & Q15 & Q16 & Q17 & Qk).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spi.RES_pspl fst snd]. fold E. spiscs Z32 Z35. rewrite br_lt_z by (clear - XR; lia). rewrite Z.lxor_comm. exact Ec. }
    destruct (IH (c + 1) (sp + size) size R1 m rom Hd) as (R2 & M2 & Q & K2).
    + exact Q5.
    + rewrite Q14. f_equal. ring.
    + exact Q15.
    + rewrite Q16. f_equal. ring.
    + exact Q17.
    + clear - Hc. lia.
    + clear - Hcf. lia.
    + exact Hsz.
    + clear - Hsp Hsz. lia.
    + clear - Hspf Hsz. lia.
    + exists R2. split; [exact (msteps_trans SEGS _ _ _ M1 M2)|]. split; [exact Q|].
      intros k Hk. rewrite (K2 k Hk). apply Qk. exact Hk.
  - destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spiz.spi_pspx R m rom sp (c - 1) size (sp + size - 1) P) as (R1 & M1 & Q5 & Q14 & Q15 & Q16 & Q17 & Qk).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spi.RES_pspx fst snd]. fold E. spiscs Z32 Z35. rewrite br_lt_z by (clear - XR; lia). rewrite Z.lxor_comm. rewrite Ec. reflexivity. }
    exists R1. split; [exact M1|]. split; [rewrite Q14; f_equal; ring|]. exact Qk.
Qed.

End SPAN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mb_tab : forall am, 0 <= am_last am <= 31 -> 0 <= am_sc am < 64 -> 0 <= am_maplen am -> meta_bits am <= 2^63-1 ->
  Z.land (Z.shiftr (meta_bits am) 5 mod 2^64) 126 = 2 * am_sc am.
Proof.
  intros am Hl Hs Hm HW. assert (W0 : 0 <= meta_bits am) by (apply meta_bits_nonneg; lia).
  rewrite TB1_SCW by lia. rewrite mb_scw by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rx_aidx_cell : forall L s m EXC q a, repr_x L s (bview SEGS m) EXC -> EXC_ok s EXC -> KS s -> MT s q = Some (MUsed a) ->
  cell_holds L (bview SEGS m) (if am_maplen a =? 0 then MCell (LMem (padd (am_mem a) 8)) 1 (VLo5 (am_aidx a)) else MCell (LMem (padd (am_mem a) 8)) 4 (VZ (am_aidx a))).
Proof.
  intros L s m EXC q a HR HEO HK Hq. pose proof HR as (_ & HPW & _).
  set (c := if am_maplen a =? 0 then MCell (LMem (padd (am_mem a) 8)) 1 (VLo5 (am_aidx a)) else MCell (LMem (padd (am_mem a) 8)) 4 (VZ (am_aidx a))).
  assert (Hc : In c (gpart s)) by (apply (group_in_gpart s q a c Hq (proj1 HK)); right; left; reflexivity).
  assert (Hw : mc_w c <> 8%nat) by (unfold c; destruct (am_maplen a =? 0); cbn; lia).
  assert (Hci : In c (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact Hc).
  exact (repr_x_holds L s _ EXC c HR Hci (not_exc_group L s EXC c HPW HEO Hc Hw)).
Qed.

Lemma span_loop_le : forall f c sp sz, span_loop f c sp sz <= c + Z.of_nat f.
Proof.
  induction f as [|f IH]; intros c sp sz; cbn [span_loop]; [lia|].
  destruct (Z.lxor sp (sp + sz - 1) <? 4096); [specialize (IH (c + 1) (sp + sz) sz); lia | lia].
Qed.

Definition units_chk (sc : Z) : bool := (1 <=? znth sc size_classes) && (znth sc size_classes <=? 8191).
Lemma units_chk_all : forall_from units_chk 0 48 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma units_range : forall sc, 0 <= sc < 48 -> 1 <= znth sc size_classes <= 8191.
Proof.
  intros sc Hs. pose proof (forall_from_ok _ _ _ units_chk_all sc ltac:(cbn; lia)) as H. unfold units_chk in H.
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma le_byte_lo : forall z, 0 <= z < 256 -> le_byte z 4 0 = z.
Proof. intros z Hz. unfold le_byte. cbn [Z.of_nat]. rewrite Z.shiftr_0_r, !Z.mod_small by (cbn; lia). reflexivity. Qed.
Lemma le_byte_hi : forall z k, 0 <= z < 256 -> (1 <= k < 4)%nat -> le_byte z 4 k = 0.
Proof.
  intros z k Hz Hk. unfold le_byte. rewrite (Z.mod_small z) by (cbn; lia). rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small; [reflexivity|]. split; [lia|]. apply (Z.lt_le_trans _ 256); [lia|].
  change 256 with (2^8). apply Z.pow_le_mono_r; lia.
Qed.

Lemma span_cnt_T : forall l cnt1, cnt1 < l + 1 -> (if l + 1 <? cnt1 then l + 1 else cnt1) = cnt1.
Proof. intros l cnt1 H. replace (l + 1 <? cnt1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma span_cnt_F : forall l cnt1, l + 1 <= cnt1 -> (if l + 1 <? cnt1 then l + 1 else cnt1) = l + 1.
Proof. intros l cnt1 H. destruct (l + 1 <? cnt1) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. lia. Qed.

Section SPANSEG.
Context {fx : FPState}.

Ltac reg_via K k T := match goal with |- getr ?R ?r = _ => replace r with (Z_to_bv 5 (Z.of_nat k)) by (apply bv_eq; reflexivity) end;
  rewrite (K k ltac:(cbn [In]; memb)); litr2 T; reflexivity.

#[using="Type"] Theorem seg_span : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m2 am2,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m2)) -> getr R 13 = wa (ext_Z true 0 4 (am_freed am2)) -> getr R 14 = wa 2 -> 0 <= sc < 48 ->
  MT s m2 = Some (MUsed am2) -> Z.land (am_freed am2) (ones (am_aidx am2)) = 0 -> am_next am2 = Some m2 -> am_avail am2 = 0 ->
  0 <= am_freed am2 <= 2^32-1 -> 0 <= am_aidx am2 <= 31 -> 0 <= am_last am2 <= 31 -> 1 <= am_sc am2 <= 47 -> 0 < am_maplen am2 ->
  meta_bits am2 <= 2^63-1 ->
  exists R' m', msteps SEGS (mkst R (wa 0x523e4) m rom) (mkst R' (wa 0x52418) m' rom) /\
    ta_m2 sc m2 s = ta_fin m2 (set_meta s m2 (MUsed (am_set_aidx (span_cnt am2 - 1) am2))) /\
    NC L [] [] (set_meta s m2 (MUsed (am_set_aidx (span_cnt am2 - 1) am2))) m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L (set_meta s m2 (MUsed (am_set_aidx (span_cnt am2 - 1) am2))) s /\
    mem_grows m m' /\ FRM L s sp0 K m m' /\ getr R' 10 = wa (loc_addr L (LMem m2)) /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m2 am2 N F R10 R13 R14 Rsc M2 Hmask Hnx Hav Rfr Rai Rl Rs Rm RW.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO. pose proof HR as (_ & HPW & _).
  assert (K2 : In m2 (keys s)) by (eapply MT_keys; exact M2).
  set (G2 := loc_addr L (LMem m2)) in *.
  destruct (HMP m2 K2) as (G2a & G2b & G2c & G2d). fold G2 in G2a, G2b, G2c, G2d.
  set (MEM := loc_addr L (LMem (am_mem am2))) in *.
  assert (RMEM : 1 <= MEM /\ MEM + 8 <= sp0 - K).
  { set (CH := MCell (LMem (am_mem am2)) 8 (VP m2)).
    assert (CHi : In CH (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; apply (group_in_gpart s m2 am2 CH M2 (proj1 HK)); left; reflexivity).
    pose proof (HC CH CHi) as (P1 & P2 & _). unfold CH in P1, P2. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in P1, P2. fold MEM in P1, P2.
    clear - P1 P2. lia. }
  set (aidx := am_aidx am2) in *. set (last := am_last am2) in *. set (sc2 := am_sc am2) in *.
  (* [comment removed for export] *)
  assert (Eml : (am_maplen am2 =? 0) = false) by (apply Z.eqb_neq; lia).
  set (CI := MCell (LMem (padd (am_mem am2) 8)) 4 (VZ aidx)).
  assert (CIg : In CI (gpart s)).
  { apply (group_in_gpart s m2 am2 CI M2 (proj1 HK)). right. left. unfold CI. cbn [group_cells]. rewrite Eml. reflexivity. }
  assert (CIi : In CI (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact CIg).
  assert (HCI : cell_holds L (bview SEGS m) CI) by (exact (repr_x_holds L s _ [] CI HR CIi (not_exc_group L s [] CI HPW HEO CIg ltac:(unfold CI; cbn; lia)))).
  assert (ECI : loc_addr L (mc_loc CI) = MEM + 8) by (unfold CI; cbn [mc_loc]; rewrite loc_padd; reflexivity).
  pose proof (HC CI CIi) as (I1 & I2 & I3). rewrite ECI in I1, I2, I3. unfold CI in I2, I3. cbn [mc_w Z.of_nat Pos.of_succ_nat] in I2, I3.
  pose proof (gpart_vs_msc L s m2 _ CI HPW HK M2 CIg ltac:(unfold CI; cbn; lia)) as DIG. rewrite ECI in DIG. unfold CI in DIG. cbn [mc_w Z.of_nat Pos.of_succ_nat] in DIG. fold G2 in DIG.
  assert (MI4 : rdn SEGS m (wa (MEM + 8)) 4 = Some (word_to_le_bytes 4 (wa aidx))).
  { pose proof (holds_rdn SEGS L m CI HCI ltac:(intros z E; discriminate) ltac:(cbn; lia)) as H. rewrite ECI in H. exact H. }
  assert (MI1 : rdn SEGS m (wa (MEM + 8)) 1 = Some (word_to_le_bytes 1 (wa aidx))).
  { pose proof (rdn_slice SEGS m 4 (wa (MEM + 8)) _ 0 1 MI4 ltac:(lia)) as E. rewrite word_add_0 in E. rewrite E. reflexivity. }
  assert (HCIb : forall k, (k < 4)%nat -> bview SEGS m (MEM + 8 + Z.of_nat k) = Some (le_byte aidx 4 k)).
  { intros k Hk. pose proof HCI as H. unfold CI, cell_holds in H. cbn [mc_loc mc_w mc_val sval_num] in H. rewrite loc_padd in H. fold MEM in H. exact (H k Hk). }
  assert (WI : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (MEM + 8 + d)) k = true).
  { apply (store_ok_of_bytes SEGS m (MEM + 8) 1). intros j Hj. assert (j = 0) as -> by lia. rewrite Z.add_0_r.
    pose proof (HCIb 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E.
    exact (proj1 (proj2 (bview_some SEGS m _ _ E))). }
  (* [comment removed for export] *)
  set (W := meta_bits am2).
  assert (RW0 : 0 <= W) by (apply meta_bits_nonneg; lia).
  set (units := znth sc2 size_classes).
  assert (Runits : 1 <= units <= 8191) by (apply units_range; lia).
  assert (Esize : class_size sc2 = 16 * units) by reflexivity.
  assert (Ehb : Z.land aidx 31 = aidx) by (apply landx31; lia).
  destruct Henv as (Mgot & Mtab & Mcan).
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_m2cz.m2c_pre R m sc G2 (am_freed am2) MEM aidx).
  { pose proof F as [R2 R8 R18 R20 R21 R22 R23 Rsp Asp Rsc' Rreq Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Rs8 Rs9 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7 Ms8 Ms9 Mcan' Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G2a G2b Hsp2 HK1; lia); try (clear - RMEM Hsp2 HK1; lia); try (clear - Rai; lia).
    - exact (rx_mem L s m [] HR HEO HK m2 am2 M2).
    - pose proof (rx_next L s m [] HR HEO HK m2 am2 M2) as E. rewrite Hnx in E. exact E. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_m2cz.m2c_pm2c R m rom sc G2 (am_freed am2) MEM aidx P1) as (R1 & Hms1 & Q10 & Q11 & Q12 & Q13 & Q21 & Qk1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_m2c.RES_pm2c fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_m2cz.VALS_m2c sc G2 (am_freed am2) MEM aidx)).
    assert (Z34 : bv_unsigned (ev E 34) = am_freed am2) by (apply zatom; [reflexivity | reflexivity | clear - Rfr; lia]).
    assert (Z36 : bv_unsigned (ev E 36) = aidx) by (apply zatom; [reflexivity | reflexivity | clear - Rai; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
      rewrite ?br_eq_z, ?br_ne_z; litmods; rewrite ?(Z.mod_small (am_freed am2) (2^64)), ?(Z.mod_small aidx (2^64)) by (clear - Rfr Rai; lia).
    pose proof (m2_cond (am_freed am2) aidx ltac:(clear - Rfr; lia) ltac:(clear - Rai; lia)) as C. change (0 mod 2^64) with 0 in C. rewrite C.
    rewrite Ehb. apply negb_false_iff. apply Z.eqb_eq. exact Hmask. }
  assert (P2 : AXF_spsz.sps_pre R1 m G2 MEM aidx W units).
  { constructor; try assumption; try (clear - G2a G2b Hsp2 HK1; lia); try (clear - RMEM Hsp2 HK1; lia); try (clear - Rai; lia); try (clear - RW RW0; lia).
    all: try (clear - Runits; lia).
    - exact (rx_bits L s m [] HR HEO HK m2 am2 M2).
    - unfold W. rewrite mb_tab by lia. replace (2 * am_sc am2 + 98984) with (98984 + 2 * am_sc am2) by ring. apply Mtab. lia. }
  destruct (AXF_spsz.sps_psps R1 m rom G2 MEM aidx W units P2 ltac:(constructor)) as (R2 & Hms2 & T5 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & Tk).
  set (size := class_size sc2). set (c0 := aidx + 2). set (sp := 16 + size * c0).
  assert (Rsize : 16 <= size <= 131056) by (unfold size; rewrite Esize; lia).
  destruct (span_run 300 c0 sp size R2 m rom) as (R3 & Hms3 & S14 & Sk).
  { apply span_done_inst; lia. }
  { rewrite T5, Ehb. f_equal; try (unfold sp, c0, size; rewrite Esize; ring). }
  { rewrite T14, Ehb. f_equal; try (unfold c0; ring). }
  { rewrite T15. f_equal; try (unfold size; rewrite Esize; reflexivity). }
  { rewrite T16, Ehb. f_equal; try (unfold sp, c0, size; rewrite Esize; ring). }
  { exact T17. }
  { unfold c0. lia. }
  { unfold c0. cbn [Z.of_nat]. clear - Rai. lia. }
  { unfold size in *. rewrite Esize in *. clear - Runits. lia. }
  { unfold sp, c0. clear - Rsize Rai. nia. }
  { unfold sp, c0. cbn [Z.of_nat]. clear - Rsize Rai. nia. }
  set (cnt1 := span_loop 300 c0 sp size) in *.
  assert (Rcnt : c0 <= cnt1 <= c0 + 300) by (split; [apply span_loop_ge | pose proof (span_loop_le 300%nat c0 sp size) as H; cbn [Z.of_nat] in H; exact H]).
  assert (Espan : span_cnt am2 = if last + 1 <? cnt1 then last + 1 else cnt1) by reflexivity.
  assert (K3 : forall k, In k [10;11;12;13]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr R2 (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. apply Sk. clear - Hk. cbn [In] in *. tauto. }
  assert (P3 : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spez.spe_pre R3 m G2 MEM aidx W cnt1).
  { constructor; try assumption; try (clear - G2a G2b Hsp2 HK1; lia); try (clear - RMEM Hsp2 HK1; lia); try (clear - Rai; lia); try (clear - RW RW0; lia).
    all: try (unfold c0 in Rcnt; clear - Rcnt Rai; lia).
    - reg_via K3 10%nat T10.
    - reg_via K3 11%nat T11.
    - reg_via K3 12%nat T12.
    - reg_via K3 13%nat T13.
    - pose proof (rx_avail L s m [] HR HEO HK m2 am2 M2) as E. rewrite Hav in E. exact E.
    - clear - DIG. lia. }
  assert (Hl31 : Z.land W 31 = last) by (unfold W; apply mb_land31; lia).
  set (E3 := Ez R3 (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spez.VALS_spe G2 MEM aidx W cnt1)).
  assert (Z35 : bv_unsigned (ev E3 35) = W) by (apply zatom; [reflexivity | reflexivity | clear - RW RW0; lia]).
  assert (Z36 : bv_unsigned (ev E3 36) = cnt1) by (apply zatom; [reflexivity | reflexivity | unfold c0 in Rcnt; clear - Rcnt Rai; lia]).
  set (aidx' := span_cnt am2 - 1).
  set (am2' := am_set_aidx aidx' am2).
  set (s' := set_meta s m2 (MUsed am2')).
  assert (Raidx' : 0 <= aidx' <= last).
  { unfold aidx'. rewrite Espan. destruct (last + 1 <? cnt1) eqn:Ec; [lia|]. apply Z.ltb_ge in Ec. unfold c0 in Rcnt. lia. }
  (* [comment removed for export] *)
  assert (RUN : exists R4 v, msteps SEGS (mkst R (wa 0x523e4) m rom) (mkst R4 (wa 0x52418) (wbytes m (wa (MEM + 8)) (word_to_le_bytes 1 (wa v))) rom) /\
                  v = aidx' /\ getr R4 10 = wa G2 /\
                  (forall k, In k [1;2;3;4;8;9;18;19;20;22;23;24;25;26;27]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
                  getr R4 21 = wa (8 * sc + 614184)).
  { assert (K123 : forall k, In k [1;2;3;4;7;8;9;18;19;20;22;23;24;25;26;27;28;29;30;31]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
    { intros k Hk. rewrite (Sk k ltac:(clear - Hk; cbn [In] in *; intuition lia)). rewrite (Tk k ltac:(clear - Hk; cbn [In] in *; intuition lia)).
      apply Qk1. clear - Hk. cbn [In] in *. intuition lia. }
    assert (R3_21 : getr R3 21 = wa (8 * sc + 614184)).
    { match goal with |- getr ?R ?r = _ => replace r with (Z_to_bv 5 (Z.of_nat 21)) by (apply bv_eq; reflexivity) end.
      rewrite (Sk 21%nat ltac:(cbn [In]; memb)), (Tk 21%nat ltac:(cbn [In]; memb)). litr2 Q21. reflexivity. }
    destruct (Z_lt_le_dec cnt1 (last + 1)) as [Lt|Ge].
    - destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spez.spe_pspt R3 m rom G2 MEM aidx W cnt1 P3) as (R4 & Hms4 & U10 & _ & _ & _ & _ & Uk).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spe.RES_pspt fst snd]. fold E3.
        repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z35, ?Z36;
          rewrite ?br_ltu_z; litmods; rewrite ?(Z.mod_small W) by (clear - RW RW0; lia).
        rewrite Hl31. rewrite !Z.mod_small by (unfold c0 in Rcnt; clear - Rcnt Rl Rai; lia). apply Z.ltb_lt. exact Lt. }
      exists R4, (32 * Z.shiftr aidx 5 + Z.land ((cnt1 + -1) mod 2^64) 31). split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 (msteps_trans SEGS _ _ _ Hms3 Hms4)))|].
      split.
      { rewrite (Z.shiftr_div_pow2 aidx 5) by lia. rewrite Z.div_small by (change (2^5) with 32; lia).
        rewrite Z.mod_small by (unfold c0 in Rcnt; lia). unfold aidx'. rewrite Espan, span_cnt_T by exact Lt.
        change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by (change (2^5) with 32; unfold c0 in Rcnt; lia). ring. }
      split; [exact U10|]. split.
      + intros k Hk. rewrite (Uk k ltac:(clear - Hk; cbn [In] in *; intuition lia)). apply K123. clear - Hk. cbn [In] in *. intuition lia.
      + reg_via Uk 21%nat R3_21.
    - destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spez.spe_pspf R3 m rom G2 MEM aidx W cnt1 P3) as (R4 & Hms4 & U10 & _ & _ & _ & _ & Uk).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_spe.RES_pspf fst snd]. fold E3.
        repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z35, ?Z36;
          rewrite ?br_ltu_z; litmods; rewrite ?(Z.mod_small W) by (clear - RW RW0; lia).
        rewrite Hl31. rewrite !Z.mod_small by (unfold c0 in Rcnt; clear - Rcnt Rl Rai; lia). apply Z.ltb_ge. exact Ge. }
      exists R4, (32 * Z.shiftr aidx 5 + Z.land W 31). split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 (msteps_trans SEGS _ _ _ Hms3 Hms4)))|].
      split.
      { rewrite (Z.shiftr_div_pow2 aidx 5) by lia. rewrite Z.div_small by (change (2^5) with 32; lia).
        rewrite Hl31. unfold aidx'. rewrite Espan, span_cnt_F by exact Ge. ring. }
      split; [exact U10|]. split.
      + intros k Hk. rewrite (Uk k ltac:(clear - Hk; cbn [In] in *; intuition lia)). apply K123. clear - Hk. cbn [In] in *. intuition lia.
      + reg_via Uk 21%nat R3_21. }
  destruct RUN as (R4 & v & Hms & Ev & R4_10 & K4 & R4_21). subst v.
  set (m' := wbytes m (wa (MEM + 8)) (word_to_le_bytes 1 (wa aidx'))) in *.
  assert (MOUT : forall x, 0 <= x < 2^64 -> x <> MEM + 8 -> m' (wa x) = m (wa x)).
  { intros x Hx Hne. unfold m'. rewrite MngWb.wbytes_out by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by lia; lia). reflexivity. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply wbytes_grows).
  assert (HKs' : KS s') by (apply KS_set_meta; [exact HK | exact K2]).
  assert (Ks' : keys s' = keys s) by (apply keys_set_meta; exact K2).
  assert (Ms' : MT s' m2 = Some (MUsed am2')) by apply MT_set_same.
  assert (HRS : RS L s' s).
  { apply (RS_set_used L s m2 am2 am2' HK M2). unfold group_cells. change (am_maplen am2') with (am_maplen am2). change (am_mem am2') with (am_mem am2).
    rewrite Eml. reflexivity. }
  set (CI' := MCell (LMem (padd (am_mem am2) 8)) 4 (VZ aidx')).
  assert (ECI' : loc_addr L (mc_loc CI') = MEM + 8) by (unfold CI'; cbn [mc_loc]; rewrite loc_padd; reflexivity).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CI']).
  { constructor; [|constructor]. unfold cell_holds. rewrite ECI'. cbn [CI' mc_val mc_w sval_num]. intros k Hk.
    destruct (Nat.eq_dec k 0) as [->|Hk0].
    - rewrite Z.add_0_r. rewrite (bview_some_byte SEGS m' (MEM + 8) (nth 0 (word_to_le_bytes 1 (wa aidx')) (Z_to_bv 8 0)) ltac:(clear - RMEM Hsp2 HK1; lia)
         ltac:(unfold m'; apply wbytes_at_wa0; cbn [length word_to_le_bytes Z_to_le_bytes]; lia)).
      f_equal. rewrite le_byte_lo by lia. cbn [word_to_le_bytes Z_to_le_bytes nth]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 8) with 256. rewrite u_wa_small by lia. apply Z.mod_small. lia.
    - rewrite (bview_ext SEGS m m') by (apply MOUT; [clear - RMEM Hsp2 HK1 Hk; lia | lia]).
      rewrite (HCIb k Hk). rewrite !le_byte_hi by lia. reflexivity. }
  assert (REPR : repr_x L s' (bview SEGS m') []).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') [] [CI'] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. destruct (cov_setm s m2 am2 am2' c HK M2 Hc) as [H|[H|H]]; [left; exact H | |].
      + left. apply (In_image_used s m2 am2 c HK M2). left. exact H.
      + unfold group_cells in H. change (am_maplen am2') with (am_maplen am2) in H. change (am_mem am2') with (am_mem am2) in H.
        change (am_aidx am2') with aidx' in H. rewrite Eml in H.
        destruct H as [<-|[<-|H]].
        * left. apply (In_image_used s m2 am2 _ HK M2). right. unfold group_cells. left. reflexivity.
        * right. left. reflexivity.
        * left. apply (In_image_used s m2 am2 _ HK M2). right. unfold group_cells. right. right. exact H.
    - intros c [<-|[]]. apply (In_image_used s' m2 am2' _ HKs' Ms'). right. unfold group_cells. change (am_maplen am2') with (am_maplen am2).
      change (am_mem am2') with (am_mem am2). change (am_aidx am2') with aidx'. rewrite Eml. right. left. reflexivity.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (Z.eq_dec a (MEM + 8)) as [->|Hne]; [|exfalso; exact (Ha' (MOUT a Ra Hne))].
      exists CI'. split; [left; reflexivity|]. unfold in_rng, cell_range. rewrite ECI'. cbn [CI' mc_w Z.of_nat Pos.of_succ_nat fst snd]. lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (Z.eq_dec x (MEM + 8)) as [->|H]; [|exfalso; exact (Hne (MOUT x Hx H))].
    exists CI. split; [exact CIi|]. split; [unfold wide; right; cbn; lia|]. unfold in_rng, cell_range. rewrite ECI. cbn [CI mc_w Z.of_nat Pos.of_succ_nat fst snd]. lia. }
  exists R4, m'. split; [exact Hms|]. split; [exact (ta_m2c s sc m2 am2 M2 Hmask Hnx)|].
  split; [exact (NC_next L [] [] s s' m m' sp0 K N REPR HRS HKs' ltac:(intros x []) Hgrow FR Ks')|].
  split.
  { apply (as_frame_move R R4 m m'); [exact F | | |].
    - apply (keeps21 R R4 m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F); [|exact R4_21].
      intros k Hk. apply K4. clear - Hk. cbn [In] in *. intuition lia.
    - intros x Hx. apply MOUT; [clear - Hx Hsp1 Hsp2 HK1; lia | clear - Hx RMEM Hsp1 HK1; lia].
    - intros x Hx. apply MOUT; [clear - Hx; lia | clear - Hx I3 I1 I2; lia]. }
  split; [exact HRS|]. split; [exact Hgrow|]. split; [exact FR|]. split; [exact R4_10|].
  intros k Hk. apply K4. clear - Hk. cbn [In] in *. intuition lia.
Qed.

End SPANSEG.
