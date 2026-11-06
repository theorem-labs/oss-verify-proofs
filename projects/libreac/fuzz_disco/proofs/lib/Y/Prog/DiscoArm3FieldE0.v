(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_push.v, with its module paths and module names changed; 616 of its 666 lines of code are new or changed and 1541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldMDA2.v, with its module paths and module names changed; 832 of its 923 lines of code are new or changed and 575 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YC85 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition E0_CNT : nat := 563%nat.
Definition e0_srx (r : nat) : sv := match r with 27%nat => SOff AT_SH 0 | _ => a3f_srx 0 r end.
Definition e0_sr : list sv := map e0_srx (seq 0 32).
Definition e0_acs : list YP09.chunk := [YP09.mkChunk 360 (CVal 8 (SOff E0_CNT 0))].
Definition e0_fcs : list YP09.chunk := [YP09.mkChunk 2544 (CVal 4 (SOff E0_CNT 0))].
Definition e0_fa : list (nat * afact) := [(E0_CNT, mkAF 0 8 0)].
Definition e0_G : facts := d_facts e0_fa [].
Definition e0_rs1 : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ e0_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ e0_fcs);
   fshadow_region AT_SH DFRAME_CLASS 208 212 (dsh_chunks dsh_ser);
   got_regionP; bcell_regionP 32].

Lemma e0_subregion : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.
Lemma e0_subrefl : forall r, subregion r r.
Proof. intros [b lo hi wlo whi cs]. apply e0_subregion. lia. Qed.
Lemma e0_submem1 : submem e0_rs1 (d_kregions dsh_ser e0_acs e0_fcs ++ []).
Proof.
  unfold e0_rs1, d_kregions, fshadow_region. rewrite app_nil_r.
  apply submem_keep; [apply e0_subrefl|].
  apply submem_keep; [apply e0_subregion; lia|].
  apply submem_keep; [apply e0_subregion; lia|].
  apply submem_keep; [apply e0_subregion; unfold DFRAME_SH; lia|].
  apply submem_keep; [apply e0_subrefl|].
  apply submem_keep; [apply e0_subrefl|].
  apply submem_nil.
Qed.
Lemma e0_wf1 : regions_wf e0_rs1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma e0_kwf1 : regions_wf (d_kregions dsh_ser e0_acs e0_fcs ++ []) = true. Proof. vm_compute. reflexivity. Qed.
Lemma e0_awr1 : forall E STK sp0 FP bl0 blc ly (own : list (Z * Z)) cid pos,
  bv_unsigned (ew E AT_SH) = shadow_addr (frame_addr ly cid pos) -> In (cid, pos) own ->
  512 <= fs_frame_bytes cid / 8 ->
  awr_ok E e0_rs1 STK sp0 FP bl0 blc ly own.
Proof.
  intros E STK sp0 FP bl0 blc ly own cid pos Hb Hin Hsz. unfold e0_rs1, fshadow_region.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ AT_SH); [reflexivity | exact Hb | | ].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists cid, pos. split; [exact Hin|]. right. unfold in_zr. cbn [fst snd]. lia.
  - apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
    apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|]. apply awr_ok_nil.
Qed.

Lemma e0_dsh2_check :
  forallb (fun k => Z.eqb (dsh_ser2 (Z.of_nat k))
    (if (208 <=? Z.of_nat k) && (Z.of_nat k <? 212) then 0 else dsh_ser (Z.of_nat k))) (seq 0 384) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma e0_dsh2_eq : forall k, 0 <= k < 384 ->
  dsh_ser2 k = if (208 <=? k) && (k <? 212) then 0 else dsh_ser k.
Proof.
  intros k Hk. pose proof e0_dsh2_check as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat k) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply Z.eqb_eq in H. exact H.
Qed.
Lemma e0_dsh2_used : forall k, 208 <= k < 212 -> dsh_ser2 k = 0.
Proof.
  intros k Hk. rewrite (e0_dsh2_eq k ltac:(lia)).
  replace ((208 <=? k) && (k <? 212)) with true;
    [reflexivity | symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia].
Qed.
Lemma e0_dsh2 : forall k, 0 <= k < 384 -> ~ (208 <= k < 212) -> dsh_ser2 k = dsh_ser k.
Proof.
  intros k Hk Hn. rewrite (e0_dsh2_eq k Hk).
  destruct ((208 <=? k) && (k <? 212)) eqn:Eb; [|reflexivity].
  exfalso. apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
Lemma e0_inw1 : forall E a, in_wrange E e0_rs1 a ->
  base_val E (Some AT_SH) + 208 <= a < base_val E (Some AT_SH) + 212.
Proof.
  intros E a (r & Hin & Hr). unfold e0_rs1 in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold got_regionP, bcell_regionP, fshadow_region in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma e0_slot_chk : forallb (fun c => ((0 <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? 472)) &&
  ((YP09.c_off c + YP09.c_len c <=? 360) || (376 <=? YP09.c_off c))) dslot_chunks = true.
Proof. vm_compute. reflexivity. Qed.
Lemma e0_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.
Lemma e0_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length].
    rewrite length_app, IHl, e0_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.
Lemma e0_used0 : a3f_used 0 = repeat 0 32.
Proof. vm_compute. reflexivity. Qed.

Definition e0_G2 (lo hi : Z) : facts := d_facts [(E0_CNT, mkAF lo hi 0)] [].
Definition e0_rs3 : smem := [YP09.mkRegion (Some AT_A) 0 472 360 376 e0_acs].
Lemma e0_submem3 : submem e0_rs3 (d_kregions dsh_ser2 e0_acs [] ++ []).
Proof.
  unfold e0_rs3, d_kregions. rewrite app_nil_r.
  apply submem_drop. apply submem_keep.
  { unfold subregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|].
    intros c Hc. apply in_or_app. right. exact Hc. }
  apply submem_drop. apply submem_drop. apply submem_drop. apply submem_drop. apply submem_nil.
Qed.
Lemma e0_wf3 : regions_wf e0_rs3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma e0_kwf3 : regions_wf (d_kregions dsh_ser2 e0_acs [] ++ []) = true. Proof. vm_compute. reflexivity. Qed.
Lemma e0_inw3 : forall E cs a, in_wrange E [YP09.mkRegion (Some AT_A) 0 472 360 376 cs] a ->
  base_val E (Some AT_A) + 360 <= a < base_val E (Some AT_A) + 376.
Proof.
  intros E cs a (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.
Lemma e0_awr3 : forall E STK sp0 FP bl0 blc ly own a,
  bv_unsigned (ew E AT_A) = a -> sp0 - STK <= a + 360 -> a + 376 <= sp0 ->
  awr_ok E e0_rs3 STK sp0 FP bl0 blc ly own.
Proof.
  intros E STK sp0 FP bl0 blc ly own a Ha H1 H2. unfold e0_rs3.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ AT_A (a - sp0)); [reflexivity | lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma e0_env_reg : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  ew (d_env cx E (a3f_vals regs ++ ex)) a = getr regs r.
Proof.
  intros cx E regs ex r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite d_env_x by (unfold a3f_vals; rewrite length_app, length_map, length_seq; lia).
  unfold a3f_vals. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
  rewrite (nth_indep _ _ ((fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) 0%nat))
    by (rewrite length_map, length_seq; lia).
  pose proof (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) 0%nat
    (Z.to_nat (bv_unsigned r))) as Hm.
  cbv beta in Hm |- *. rewrite Hm, seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma e0_chunk_z : forall E (m : word -> option byte) base o,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk o (CVal 1 (SLit 0))) ->
  option_map (fun b : byte => bv_unsigned b) (mbyte SEGS m (base + o)) = Some 0.
Proof.
  intros E m base o H. destruct (H 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. rewrite Z.add_0_r in Hb2. rewrite Hb2.
  injection Hb1 as <-. cbn [option_map]. f_equal.
Qed.
Lemma e0_byte_of_aview : forall (Hh : word -> bool) (m : word -> option byte) a v,
  aview SEGS Hh m a = Some v -> mbyte SEGS (mrestrict Hh m) a = Some (Z_to_bv 8 v).
Proof.
  intros Hh m a v Hv. unfold aview in Hv.
  destruct (mbyte SEGS (mrestrict Hh m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma e0_rok : forall E (m m' : word -> option byte) nn b lo hi wlo whi cs,
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = b ->
  (forall c, In c cs -> forall i, 0 <= i < YP09.c_len c ->
     mbyte SEGS m' (b + YP09.c_off c + i) = mbyte SEGS m (b + YP09.c_off c + i)) ->
  (forall o, wlo <= o < whi -> writable_at SEGS m' (b + o)) ->
  region_ok SEGS E m' (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
  intros E m m' nn b lo hi wlo whi cs HR Hb HK HW.
  unfold region_ok in HR |- *.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR |- *.
  rewrite Hb in HR |- *. destruct HR as (H1 & H2 & _ & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact HW|].
  apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) H4 c Hc) as Hck.
  intros i Hi. destruct (Hck i Hi) as (bb & Hcb & Hmb). exists bb. split; [exact Hcb|].
  rewrite (HK c Hc i Hi). exact Hmb.
Qed.

Lemma e0_rok_range : forall E (m m' : word -> option byte) nn b lo hi wlo whi cs,
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = b ->
  (forall a, b + lo <= a < b + hi -> mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall o, wlo <= o < whi -> writable_at SEGS m' (b + o)) ->
  forallb (fun c => (lo <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? hi)) cs = true ->
  region_ok SEGS E m' (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
  intros E m m' nn b lo hi wlo whi cs HR Hb HK HW HC.
  apply (e0_rok E m m' nn b lo hi wlo whi cs HR Hb); [|exact HW].
  intros c Hc i Hi.
  pose proof (proj1 (forallb_forall _ _) HC c Hc) as Hin. cbn beta in Hin.
  apply andb_prop in Hin as [Hin1 Hin2]. apply Z.leb_le in Hin1. apply Z.leb_le in Hin2.
  apply HK. lia.
Qed.

Lemma e0_frame_keep : forall cx h (shf shf' : Z -> Z) (W : world SEGS) (m m' : word -> option byte) (E : env),
  d_E cx E ->
  bv_unsigned (ew E AT_STK) = d_S cx -> bv_unsigned (ew E AT_A) = d_A cx ->
  bv_unsigned (ew E AT_F) = d_FB cx -> bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx) ->
  0 <= shadow_addr (d_FB cx) -> shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8 <= 2 ^ 64 ->
  Forall (region_ok SEGS E (rd W m)) (d_regions cx shf) ->
  rdword (aview SEGS (w_H W) m) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  d_hslots cx h W m ->
  d_shadow cx shf' W m' ->
  (forall a, d_S cx - 104 <= a < d_S cx -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, d_A cx <= a < d_A cx + 472 -> ~ (d_A cx + 360 <= a < d_A cx + 376) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, d_FB cx <= a < d_FB cx + 24 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, d_FB cx + fs_frame_bytes DFRAME_CLASS - 8 <= a < d_FB cx + fs_frame_bytes DFRAME_CLASS ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall o, 0 <= o < 472 -> apresent (w_H W) m' (d_A cx + o)) ->
  (forall o, 0 <= o < DFRAME_SIZE -> apresent (w_H W) m' (d_FB cx + o)) ->
  (forall o, 0 <= o < DFRAME_SH -> apresent (w_H W) m' (shadow_addr (d_FB cx) + o)) ->
  Forall (region_ok SEGS E (rd W m')) (d_regions cx shf') /\
  rdword (aview SEGS (w_H W) m') (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) /\
  d_hslots cx h W m'.
Proof.
  intros cx h shf shf' W m m' E HE BS BA BF BSH SH1 SH2 HREG HFLAG HHS HSH K1 K2 K3 K4 P1 P2 P3.
  pose proof HREG as HR. cbn [d_regions] in HR.
  pose proof (Forall_inv HR) as RSTK. apply Forall_inv_tail in HR.
  pose proof (Forall_inv HR) as RA. apply Forall_inv_tail in HR.
  pose proof (Forall_inv HR) as RF.
  split.
  { cbn [d_regions].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    - eapply (e0_rok_range E _ _ AT_STK (d_S cx)); [exact RSTK | exact BS | | intros o Ho; lia |].
      + intros a Ha. apply (mbyte_of_aview SEGS). apply K1. lia.
      + vm_compute. reflexivity.
    - eapply (e0_rok E _ _ AT_A (d_A cx)); [exact RA | exact BA | |].
      + intros c Hc i Hi.
        pose proof (proj1 (forallb_forall _ _) e0_slot_chk c Hc) as Hin. cbn beta in Hin.
        apply andb_prop in Hin as [Hin1 Hin2]. apply andb_prop in Hin1 as [Hin0 Hin1].
        apply Z.leb_le in Hin0. apply Z.leb_le in Hin1. apply orb_true_iff in Hin2.
        apply (mbyte_of_aview SEGS). apply K2; [lia|].
        destruct Hin2 as [Hin2|Hin2]; apply Z.leb_le in Hin2; lia.
      + intros o Ho. apply (apresent_writable SEGS). apply P1. exact Ho.
    - eapply (e0_rok E _ _ AT_F (d_FB cx)); [exact RF | exact BF | |].
      + intros c Hc i Hi. cbn [In] in Hc.
        destruct Hc as [<-|[<-|[<-|[]]]];
          cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in Hi |- *;
          apply (mbyte_of_aview SEGS); apply K3; lia.
      + intros o Ho. apply (apresent_writable SEGS). apply P2. exact Ho.
    - unfold region_ok, fshadow_region. cbv beta zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite BSH.
      split; [lia|]. split; [lia|]. split.
      + intros o Ho. apply (apresent_writable SEGS). apply P3. exact Ho.
      + apply dsh_chunks_ok. intros kk Hkk. pose proof (HSH kk Hkk) as X.
        split; [exact (aview_range _ _ _ _ _ X)|]. unfold aview in X.
        destruct (mbyte SEGS (rd W m') (shadow_addr (d_FB cx) + kk)) as [b|] eqn:Eb; [|discriminate X].
        cbn [option_map] in X. injection X as <-. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { transitivity (rdword (aview SEGS (w_H W) m) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8)); [|exact HFLAG].
    apply rdword_ext. intros kk Hkk. apply K4. lia. }
  assert (KV : forall off v, 120 <= off -> off + 8 <= 384 -> off + 8 <= 360 \/ 376 <= off ->
    val_mem SEGS (rd W m) (d_A cx + off) 8 v -> val_mem SEGS (rd W m') (d_A cx + off) 8 v).
  { intros off v H1 H2 H3 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact Hv].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply K2; lia. }
  destruct HHS as (Q184 & Q120 & Q136 & Q376 & Q280 & Q232 & Q264).
  split; [apply (KV 184); [lia | lia | lia | exact Q184]|].
  split; [apply (KV 120); [lia | lia | lia | exact Q120]|].
  split; [apply (KV 136); [lia | lia | lia | exact Q136]|].
  split; [apply (KV 376); [lia | lia | lia | exact Q376]|].
  split; [apply (KV 280); [lia | lia | lia | exact Q280]|].
  split; [apply (KV 232); [lia | lia | lia | exact Q232]|].
  apply (KV 264); [lia | lia | lia | exact Q264].
Qed.

Section h.
Variable B : asyms.

Lemma e0_regs_ok : forall cx E regs ex, d_E cx E -> d_rL B cx regs ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) e0_sr regs.
Proof.
  intros cx E regs ex HE HL.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & _ & HSH). unfold AT_A in HA60. unfold AT_SH in HSH.
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | rewrite HA60, Z.add_0_r, Z_to_bv_bv_unsigned;
      first [ rewrite <- Hsp; unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity | exact H9 ]
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H8; unfold w64, d_S, spZ;
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
    | exact H18
    | exact H20
    | rewrite HSH, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H27
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (e0_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis DBRT : d_body_rt_stmt B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).

Theorem a3f_e0 : seg_e0_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad W c (HFROM & HD).
destruct HD as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R27) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & H360 & HVP & HOO).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFSpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *.
destruct (proj1 (Z.mod_divide (d_FB cx) 32 ltac:(lia)) GF32) as (qf & EQF).
assert (ESHA : shadow_addr (d_FB cx) = 2147450880 + 4 * qf).
{ unfold shadow_addr, SHADOW_OFF. rewrite EQF. replace (qf * 32) with (4 * qf * 8) by lia.
  rewrite Z.div_mul by lia. reflexivity. }
assert (HSHlo : 2147450880 <= shadow_addr (d_FB cx)) by lia.
assert (HSHhi : shadow_addr (d_FB cx) + 512 < 17594333495296) by lia.
assert (HSHSTK : shadow_addr (d_FB cx) + 512 < d_A cx - 4096) by lia.
assert (HFBSH : d_FB cx + 4096 <= shadow_addr (d_FB cx) \/ shadow_addr (d_FB cx) + 512 <= d_FB cx).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
  destruct GFapp as (Hg1 & [Hg2 | (Hg2 & Hg3)]); [left; lia | right; lia]. }
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
assert (ES2 : bv_unsigned (ew E AT_STK) = d_S cx)
  by (change AT_STK with 2%nat; rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (EA : bv_unsigned (ew E AT_A) = d_A cx) by (rewrite E60; unfold w64; apply unsigned_lit_small; lia).
assert (EFv : bv_unsigned (ew E AT_F) = d_FB cx) by (rewrite EF; unfold w64; apply unsigned_lit_small; lia).
assert (ESHv : bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx))
  by (rewrite ESH; unfold w64; apply unsigned_lit_small; lia).
set (vals := a3f_vals regs ++ [Z_to_bv 64 count]).
assert (Lv : length vals = 33%nat)
  by (unfold vals, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (ECNT : ew (d_env cx E vals) E0_CNT = Z_to_bv 64 count)
  by (unfold E0_CNT; exact (d_env_x cx E vals 32 ltac:(rewrite Lv; lia))).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
  by (intros nn Hnn; apply d_env_old; exact Hnn).
assert (U60 : bv_unsigned (ew (d_env cx E vals) AT_A) = d_A cx)
  by (rewrite EO by (unfold AT_FL, AT_A; lia); rewrite E60; apply unsigned_lit_small; lia).
assert (U516 : bv_unsigned (ew (d_env cx E vals) AT_F) = d_FB cx)
  by (rewrite EO by (unfold AT_FL, AT_F; lia); rewrite EF; apply unsigned_lit_small; lia).
assert (U529 : bv_unsigned (ew (d_env cx E vals) AT_SH) = shadow_addr (d_FB cx)).
{ rewrite EO by (unfold AT_FL, AT_SH; lia). rewrite ESH. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.div_le_upper_bound (d_FB cx) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
assert (UCNT : bv_unsigned (ew (d_env cx E vals) E0_CNT) = count)
  by (rewrite ECNT; apply unsigned_lit_small; lia).
assert (HVC : val_mem SEGS (rd W mem3) (d_obj cx OT + 384) 4 count).
{ rewrite Ec. rewrite <- (ReacDiscoTableAge.ta_n_val T1 HLT1 (proj1 HTOK1)).
  apply (ReacDiscoTableAge.ta_vm_of_ga (rd W mem3) (d_obj cx OT) T1 384 4 HGT ltac:(lia)).
  rewrite HLT1. cbn [Z.of_nat]. lia. }
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) e0_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 360 8%N (SOff E0_CNT 0) count).
  - cbn [sv_denot]. rewrite UCNT, Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact H360. }
assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) e0_fcs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) 2544 4%N (SOff E0_CNT 0) count).
  - cbn [sv_denot]. rewrite UCNT, Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (unfold d_obj, dobj_off; lia). exact HVC. }
assert (HGf : facts_ok (d_env cx E vals) e0_G).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals e0_fa [] HCTX HE); [|exact I].
  cbn [e0_fa atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite UCNT, Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (DSEAT LAWS PAL fq cx dsh_ser ly3 S3 W regs mem3 md3 k E R12_OFF e0_sr vals e0_acs e0_fcs []
  e0_G HCTX HE HREG HFLAG (e0_regs_ok cx E regs [Z_to_bv 64 count] HE HRL) HGf Hacs Hfcs
  (Forall_nil _) I (Forall_nil _) e0_kwf1) as HS0.
pose proof (st_ok_pi_submem _ _ _ e0_rs1 HS0 e0_submem1 e0_wf1) as HS.
clear HS0. cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HS.
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))).
pose proof (SRr_run_pi_AJ (fx := fq) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fq) (PI := PI) B LAWS) as RUNC.
unfold cfg_at, w64.
paj_run_shc RUNP RUNC HS HJ.
{ apply (e0_awr1 _ _ _ _ _ _ _ _ DFRAME_CLASS (c_fpos cx)).
  - rewrite U529, EFA3. reflexivity.
  - left. reflexivity.
  - change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (U529n : bv_unsigned (ew (d_env cx E vals) 529%nat) = shadow_addr (d_FB cx))
  by (change 529%nat with AT_SH; exact U529).
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hna. apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia.
  intros Hw. apply e0_inw1 in Hw.
  change (base_val (d_env cx E vals) (Some AT_SH)) with (bv_unsigned (ew (d_env cx E vals) AT_SH)) in Hw.
  rewrite U529 in Hw. lia. }
assert (SH0 : forall kk, 208 <= kk < 212 -> aview SEGS (w_H W) (ms_mem ms) (shadow_addr (d_FB cx) + kk) = Some 0).
{ pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HMOK & _).
  lazymatch type of HMOK with Forall ?P ?rs => let rs' := eval vm_compute in rs in change (Forall P rs') in HMOK end.
  apply Forall_inv_tail in HMOK. apply Forall_inv_tail in HMOK. apply Forall_inv_tail in HMOK.
  pose proof (Forall_inv HMOK) as RSH.
  destruct RSH as (_ & _ & _ & HCH). cbn [YP09.r_base YP09.r_chunks base_val restrict ms_mem] in HCH.
  rewrite U529n in HCH.
  pose proof (e0_chunk_z _ _ _ _ (Forall_inv HCH)) as B211. apply Forall_inv_tail in HCH.
  pose proof (e0_chunk_z _ _ _ _ (Forall_inv HCH)) as B210. apply Forall_inv_tail in HCH.
  pose proof (e0_chunk_z _ _ _ _ (Forall_inv HCH)) as B209. apply Forall_inv_tail in HCH.
  pose proof (e0_chunk_z _ _ _ _ (Forall_inv HCH)) as B208.
  intros kk Hkk. unfold aview.
  assert (Hk4 : kk = 208 \/ kk = 209 \/ kk = 210 \/ kk = 211) by lia.
  destruct Hk4 as [-> | [-> | [-> | ->]]]; assumption. }
assert (HSHD1 : d_shadow cx dsh_ser2 W (ms_mem ms)).
{ intros kk Hkk. unfold DFRAME_SH in Hkk.
  destruct (Z.le_gt_cases 208 kk) as [Hlo|Hlo]; [destruct (Z.lt_ge_cases kk 212) as [Hhi|Hhi]|].
  - rewrite (SH0 kk ltac:(lia)). rewrite (e0_dsh2_used kk ltac:(lia)). reflexivity.
  - rewrite KM1 by lia. rewrite (HSHD kk ltac:(unfold DFRAME_SH; lia)).
    f_equal. symmetry. apply e0_dsh2; lia.
  - rewrite KM1 by lia. rewrite (HSHD kk ltac:(unfold DFRAME_SH; lia)).
    f_equal. symmetry. apply e0_dsh2; lia. }
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
assert (X3 : ew (d_env cx E vals) 534 = getr regs 3)
  by exact (e0_env_reg cx E regs [Z_to_bv 64 count] (3%bv : bv 5) 534%nat eq_refl).
assert (X4 : ew (d_env cx E vals) 535 = getr regs 4)
  by exact (e0_env_reg cx E regs [Z_to_bv 64 count] (4%bv : bv 5) 535%nat eq_refl).
assert (X18 : ew (d_env cx E vals) 549 = getr regs 18)
  by exact (e0_env_reg cx E regs [Z_to_bv 64 count] (18%bv : bv 5) 549%nat eq_refl).
assert (X20 : ew (d_env cx E vals) 551 = getr regs 20)
  by exact (e0_env_reg cx E regs [Z_to_bv 64 count] (20%bv : bv 5) 551%nat eq_refl).
assert (X24 : ew (d_env cx E vals) 555 = getr regs 24)
  by exact (e0_env_reg cx E regs [Z_to_bv 64 count] (24%bv : bv 5) 555%nat eq_refl).
assert (U516n : bv_unsigned (ew (d_env cx E vals) 516%nat) = d_FB cx)
  by (change 516%nat with AT_F; exact U516).
assert (U60n : bv_unsigned (ew (d_env cx E vals) 60%nat) = d_A cx)
  by (change 60%nat with AT_A; exact U60).
assert (U2n : bv_unsigned (ew (d_env cx E vals) 2%nat) = d_S cx)
  by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA AS___asan_memset) (AMEMSET fq) W (ms_regs ms) (ms_mem ms)
    LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k
    (d_obj cx OUSED) 0 32 (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 7584)) HJ).
  - rewrite Q10, U516n. unfold w64, d_obj, dobj_off. f_equal; lia.
  - rewrite Q11. reflexivity.
  - rewrite Q12. reflexivity.
  - lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold spZ. rewrite Q2. replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) by lia. exact U60n.
  - apply (proj2 (Z.mod_divide (d_A cx - d_S cx) 16 ltac:(lia))).
    exists (2 * ((d_S cx - MFRAME) / 32) - d_S cx / 16).
    unfold d_A. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as D. rewrite GS16 in D.
    set (x := (d_S cx - MFRAME) / 32) in *. set (y := d_S cx / 16) in *. clearbody x y. lia.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - rewrite Q3, X3. exact Rgp.
  - rewrite Q4, X4. exact Rtp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. unfold d_obj, dobj_off in Ha. split.
    + right. right. right. exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
    + unfold ESTACK. lia.
  - unfold amem_range, d_obj, dobj_off.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
    destruct GFapp as (Hg1 & [Hg2 | (Hg2 & Hg3)]); [left; lia | right; split; lia].
  - intros x Hx. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr.
    assert (HD : SHADOW_OFF + x / 8 = shadow_addr (d_FB cx) + (x / 8 - 4 * qf))
      by (rewrite ESHA; unfold SHADOW_OFF; lia).
    rewrite HD. apply SH0. unfold d_obj, dobj_off in Hx. rewrite EQF in Hx. lia.
  - intros _ s Hs.
    assert (Hhull : shadow_addr (d_FB cx) + 200 <= s < shadow_addr (d_FB cx) + 220).
    { unfold d_obj, dobj_off, shadow_addr, SHADOW_OFF in Hs |- *. rewrite EQF in Hs |- *. lia. }
    replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
    rewrite (HSHD1 (s - shadow_addr (d_FB cx)) ltac:(unfold DFRAME_SH; lia)). discriminate.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Hset & Hkeep & Hpres2 & Hsame).
assert (HPR2 : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem2 a).
{ intros a Ha. apply Hpres2. eapply apresent_grows; [exact HG | exact Ha]. }
assert (KM2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) ->
  ~ (d_obj cx OUSED <= a < d_obj cx OUSED + 32) -> ~ (d_A cx - 4096 <= a < d_A cx) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha H1 H2 H3. rewrite (Hkeep a Ha H2 ltac:(unfold ESTACK; lia)). exact (KM1 a Ha H1). }
assert (HNSH : forall a, d_FB cx <= a < d_FB cx + 4096 ->
  ~ (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212))
  by (destruct HFBSH as [HF1|HF1]; intros a Ha; lia).
assert (HSHD2 : d_shadow cx dsh_ser2 W mem2).
{ intros kk Hkk. unfold DFRAME_SH in Hkk.
  rewrite (Hkeep (shadow_addr (d_FB cx) + kk) ltac:(lia) ltac:(unfold d_obj, dobj_off; lia)
    ltac:(unfold ESTACK; lia)).
  exact (HSHD1 kk ltac:(unfold DFRAME_SH; lia)). }
assert (HHS3 : d_hslots cx h W mem3) by exact (d_hslots_of_frame cx h dsh_ser W mem3 HFRM).
assert (KSTK : forall a, d_S cx - 104 <= a < d_S cx -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KM2; unfold d_obj, dobj_off; lia. }
assert (KASL : forall a, d_A cx <= a < d_A cx + 472 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KM2; unfold d_obj, dobj_off; lia. }
assert (KFH : forall a, d_FB cx <= a < d_FB cx + 24 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KM2; unfold d_obj, dobj_off; lia. }
assert (KFL : forall a, d_FB cx + fs_frame_bytes DFRAME_CLASS - 8 <= a < d_FB cx + fs_frame_bytes DFRAME_CLASS ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha.
  apply KM2; unfold d_obj, dobj_off; lia. }
assert (PA1 : forall o, 0 <= o < 472 -> apresent (w_H W) mem2 (d_A cx + o))
  by (intros o Ho; apply HPR2; apply GSTKpres; unfold LLVMF_STK; lia).
assert (PA2 : forall o, 0 <= o < DFRAME_SIZE -> apresent (w_H W) mem2 (d_FB cx + o))
  by (intros o Ho; apply HPR2; apply GFpres; unfold DFRAME_SIZE in Ho; lia).
assert (PA3 : forall o, 0 <= o < DFRAME_SH -> apresent (w_H W) mem2 (shadow_addr (d_FB cx) + o))
  by (intros o Ho; apply HPR2; apply GFSpres; unfold DFRAME_SH in Ho; lia).
destruct (e0_frame_keep cx h dsh_ser dsh_ser2 W mem3 mem2 E HE ES2 EA EFv ESHv
  ltac:(lia) ltac:(change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia)
  HREG HFLAG HHS3 HSHD2 KSTK (fun a Ha _ => KASL a Ha) KFH KFL PA1 PA2 PA3) as (HREG2 & HFLAG2 & HHS2).
assert (HCTX2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem2 md2 k) by exact (conj HBASE (conj HJ2 HFR)).
assert (U2w : ew (d_env cx E vals) 2 = w64 (d_S cx))
  by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (U60w : ew (d_env cx E vals) 60%nat = w64 (d_A cx))
  by (rewrite EO by (unfold AT_FL; lia); exact E60).
assert (U32w : ew (d_env cx E vals) 32 = w64 SHADOW_OFF)
  by (rewrite EO by (unfold AT_FL; lia); exact E32).
assert (USHw : ew (d_env cx E vals) 529%nat = w64 (shadow_addr (d_FB cx)))
  by (rewrite EO by (unfold AT_FL; lia); exact ESH).
assert (P2' : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (P3' : getr regs2 3 = getr (ms_regs ms) 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
assert (P4' : getr regs2 4 = getr (ms_regs ms) 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
assert (P8' : getr regs2 8 = getr (ms_regs ms) 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
assert (P9' : getr regs2 9 = getr (ms_regs ms) 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
assert (P18' : getr regs2 18 = getr (ms_regs ms) 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
assert (P19' : getr regs2 19 = getr (ms_regs ms) 19) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
assert (P20' : getr regs2 20 = getr (ms_regs ms) 20) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
assert (P24' : getr regs2 24 = getr (ms_regs ms) 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
assert (P27' : getr regs2 27 = getr (ms_regs ms) 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
assert (HRL2 : d_rL B cx regs2).
{ split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - unfold spZ. rewrite P2', Q2. exact U60n.
  - rewrite P3', Q3, X3. exact Rgp.
  - rewrite P4', Q4, X4. exact Rtp.
  - rewrite P8', Q8, U2w. reflexivity.
  - rewrite P9', Q9, U60w. reflexivity.
  - rewrite P19', Q19, U32w. reflexivity.
  - rewrite P18', Q18. unfold w64, WS_MASK. reflexivity.
  - rewrite P20', Q20. reflexivity.
  - rewrite P27', Q27, USHw. reflexivity. }
assert (H360b : val_mem SEGS (rd W mem2) (d_A cx + 360) 8 count).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem2); [|exact H360].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KASL. lia. }
set (vals2 := a3f_vals regs2 ++ [Z_to_bv 64 count]).
assert (Lv2 : length vals2 = 33%nat)
  by (unfold vals2, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (ECNT2 : ew (d_env cx E vals2) E0_CNT = Z_to_bv 64 count)
  by (unfold E0_CNT; exact (d_env_x cx E vals2 32 ltac:(rewrite Lv2; lia))).
assert (UCNT2 : bv_unsigned (ew (d_env cx E vals2) E0_CNT) = count)
  by (rewrite ECNT2; apply unsigned_lit_small; lia).
assert (Hacs3 : Forall (YP09.chunk_ok SEGS (d_env cx E vals2) (rd W mem2) (d_A cx)) e0_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 360 8%N (SOff E0_CNT 0) count).
  - cbn [sv_denot]. rewrite UCNT2, Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact H360b. }
assert (SEAT : forall lo hi, lo <= count <= hi -> 0 <= lo ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals2) (mkSS 7584 e0_sr e0_rs3 None (e0_G2 lo hi))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs2 (Z_to_bv 64 (BASE + 7584)) mem2 (YK11.seg_rom SEGS)))).
{ intros lo hi Hlh Hlo.
  assert (HGf2 : facts_ok (d_env cx E vals2) (e0_G2 lo hi)).
  { apply (DFACTS LAWS cx ly3 S3 W mem2 md2 k E vals2 [(E0_CNT, mkAF lo hi 0)] [] HCTX2 HE); [|exact I].
    cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UCNT2, Z.pow_0_r, Z.mod_1_r. lia. }
  pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs2 mem2 md2 k E 7584 e0_sr vals2 e0_acs [] []
    (e0_G2 lo hi) HCTX2 HE HREG2 HFLAG2 (e0_regs_ok cx E regs2 [Z_to_bv 64 count] HE HRL2) HGf2
    Hacs3 (Forall_nil _) (Forall_nil _) I (Forall_nil _) e0_kwf3) as HT0.
  exact (st_ok_pi_submem _ _ _ e0_rs3 HT0 e0_submem3 e0_wf3). }
assert (HEI2 : img_env VAL A_LIM (d_env cx E vals2))
  by exact (proj1 (proj2 (proj2 (d_E_env cx E vals2 HE)))).
assert (W60 : bv_unsigned (ew (d_env cx E vals2) AT_A) = d_A cx)
  by (rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact EA).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PI := PI) B LAWS) as RUNTOP.
rename ms into msa. rename mat into mata. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym (proj1 HBLK))). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 buf (Z.max (slot_ser_defs.ser_cap op) 1)
  DFRAME_CLASS (c_fpos cx) HAR3 Hinb HFin3) as HSEPb.
unfold zdisjoint, in_zr in HSEPb. cbn [fst snd] in HSEPb. rewrite EFA3 in HSEPb.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HSEPb.
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (LOO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296)
  by (rewrite (e0_objs_len buf vpad os HVP Lo6), Los; lia).
assert (HhA : in_app h (req_size HUNT_SIZE)).
{ assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym (proj1 HBLK))). apply in_or_app. right. left. reflexivity. }
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin))))). }
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hc. pose proof HBASE as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hrol : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low;
    [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (Hroi : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_img_range;
    [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (HOF : d_FB cx + 4096 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= d_FB cx)
  by (destruct HOFFF as [HO|HO]; [left|right]; exact HO).
assert (NOTRD : forall a, (d_obj cx OUSED <= a < d_obj cx OUSED + 32) \/
  (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) -> ~ d_rdset B cx h a).
{ intros a Ha Hrd.
  pose proof HGEO as (_ & _ & _ & _ & _ & _ & Hhfb & Hinp).
  pose proof HCAN as (_ & _ & Hcimg).
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hhfb, Hinp.
  assert (HhS : h + 480 <= 2147446784 \/ 17594333495296 <= h).
  { change (req_size HUNT_SIZE) with 480 in HhA.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HhA. clear - HhA. lia. }
  unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size in Hrd. unfold d_obj, dobj_off in Ha.
  unfold HUNT_SIZE in Hrd, Hhfb.
  destruct Hrd as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
  - clear - Ha Hr HFBSH. lia.
  - clear - Ha Hr HFBSH. lia.
  - clear - Ha Hr HFBSH. lia.
  - clear - Ha Hr HFBSH. lia.
  - clear - Ha Hr Hhfb HhS HSHlo HSHhi. lia.
  - specialize (HpA Hc). specialize (Hinp Hc).
    pose proof (req_size_pos (c_n cx) ltac:(clear - Hc; lia)) as (_ & Hrqp).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HpA.
    destruct Hinp as (_ & _ & Hinf & _).
    assert (HpS : c_p cx + c_n cx <= 2147446784 \/ 17594333495296 <= c_p cx)
      by (clear - HpA Hrqp; lia).
    clear - Ha Hr Hinf HpS HSHlo HSHhi. lia.
  - pose proof (Hrol a (proj1 Hr)) as Hl. pose proof (Hroi a (proj1 Hr)) as Hm.
    clear - Ha Hl Hm HOF C5 HSHlo. lia.
  - pose proof (Hcimg a Hr) as Himg. pose proof (pa_segs_low a Himg) as Hl. pose proof (pa_img_range a Himg) as Hm.
    clear - Ha Hl Hm HOF C5 HSHlo. lia. }
assert (LAND : forall m4 : word -> option byte,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 360 <= a < d_A cx + 376) ->
     aview SEGS (w_H W) m4 a = aview SEGS (w_H W) mem2 a) ->
  mem_grows (rd W mem2) (rd W m4) ->
  d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W m4 /\
  d_sp1 cx i n now W m4 /\ d_sp0 cx i now W m4 /\ a3_tab cx now T0 T1 W m4 /\ a3_buf op T1 now buf W m4 /\
  garr8 SEGS (rd W m4) (d_obj cx OO) (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)) /\
  garr8 SEGS (rd W m4) (d_obj cx OUSED) (a3f_used 0)).
{ intros m4 K4 G4.
  assert (K43 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 360 <= a < d_A cx + 376) ->
    ~ (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) ->
    ~ (d_obj cx OUSED <= a < d_obj cx OUSED + 32) -> ~ (d_A cx - 4096 <= a < d_A cx) ->
    aview SEGS (w_H W) m4 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha H1 H2 H3 H4. rewrite (K4 a Ha H1). exact (KM2 a Ha H2 H3 H4). }
  assert (HSH4 : d_shadow cx dsh_ser2 W m4).
  { intros kk Hkk. unfold DFRAME_SH in Hkk.
    rewrite (K4 (shadow_addr (d_FB cx) + kk) ltac:(lia) ltac:(lia)).
    exact (HSHD2 kk ltac:(unfold DFRAME_SH; lia)). }
  assert (P4 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m4 a)
    by (intros a Ha; eapply apresent_grows; [exact G4 | exact Ha]).
  destruct (e0_frame_keep cx h dsh_ser2 dsh_ser2 W mem2 m4 E HE ES2 EA EFv ESHv
    ltac:(lia) ltac:(change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia)
    HREG2 HFLAG2 HHS2 HSH4
    ltac:(intros a Ha; apply K4; lia)
    ltac:(intros a Ha Hna; apply K4; lia)
    ltac:(intros a Ha; apply K4; lia)
    ltac:(intros a Ha; change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha; apply K4; lia)
    ltac:(intros o Ho; apply P4; apply PA1; exact Ho)
    ltac:(intros o Ho; apply P4; apply PA2; exact Ho)
    ltac:(intros o Ho; apply P4; apply PA3; exact Ho)) as (HREG4 & HFLAG4 & HHS4).
  assert (HFR4 : d_frame cx h dsh_ser2 W m4).
  { exists E. split; [exact HE|]. split; [exact HREG4|]. split; [exact HFLAG4|]. exact HHS4. }
  assert (KV4 : forall off (nn : nat) v, 0 <= off -> off + Z.of_nat nn <= 360 ->
    val_mem SEGS (rd W mem3) (d_A cx + off) nn v -> val_mem SEGS (rd W m4) (d_A cx + off) nn v).
  { intros off nn v H0 H1 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 m4); [|exact Hv].
    intros kk Hkk. apply K43; unfold d_obj, dobj_off; lia. }
  assert (KG4 : forall a l, garr8 SEGS (rd W mem3) a l ->
    (forall x, a <= x < a + Z.of_nat (length l) -> 0 <= x < 2 ^ 64 /\ ~ (d_A cx - 4096 <= x < d_A cx + 376) /\
       ~ (shadow_addr (d_FB cx) + 208 <= x < shadow_addr (d_FB cx) + 212) /\
       ~ (d_obj cx OUSED <= x < d_obj cx OUSED + 32)) ->
    garr8 SEGS (rd W m4) a l).
  { intros a l Hg Hx. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|].
    intros x Hxr. destruct (Hx x Hxr) as (Xa & Xb & Xc & Xd). apply (mbyte_of_aview SEGS). apply K43; lia. }
  split.
  { apply (DBRT cx h n n (a3_xb buf op) dsh_ser dsh_ser2 ly3 S3 W mem3 m4 (d_S cx - LLVMF_STK) (d_S cx)
      (fun a => (d_A cx - 4096 <= a < d_A cx + 376) \/ (d_obj cx OUSED <= a < d_obj cx OUSED + 32) \/
                (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212)) HBODY).
    - lia.
    - lia.
    - intros a [Ha | Ha]; [left; unfold LLVMF_STK; lia | right; apply NOTRD; exact Ha].
    - intros a Ha Hna. apply K43; lia.
    - intros a _ Hpr. apply P4. apply HPR2. exact Hpr.
    - exact HFR4.
    - exact HSH4.
    - lia. }
  pose proof HSP1 as ((H208 & H320) & H192 & H200).
  pose proof HSP0 as (H208' & H320').
  split.
  { split; [split|split].
    - apply KV4; [lia | cbn [Z.of_nat]; lia | exact H208].
    - apply KV4; [lia | cbn [Z.of_nat]; lia | exact H320].
    - apply KV4; [lia | cbn [Z.of_nat]; lia | exact H192].
    - apply KV4; [lia | cbn [Z.of_nat]; lia | exact H200]. }
  split.
  { split; [apply KV4; [lia | cbn [Z.of_nat]; lia | exact H208'] | apply KV4; [lia | cbn [Z.of_nat]; lia | exact H320']]. }
  split.
  { split; [exact (proj1 HTAB)|]. apply KG4; [exact HGT|].
    intros x Hx. rewrite length_map, HLT1 in Hx. unfold d_obj, dobj_off in Hx |- *. cbn [Z.of_nat] in Hx. lia. }
  split.
  { split; [exact Hr2|]. apply KG4; [exact HGB|].
    intros x Hx. rewrite Lb in Hx. unfold d_obj, dobj_off.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. lia. }
  split.
  { apply KG4; [exact HOO|].
    intros x Hx. rewrite length_map in Hx. unfold d_obj, dobj_off in Hx |- *. lia. }
  rewrite e0_used0. intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
  intros kk Hkk. assert (Ekk : kk = 0%nat) by lia. subst kk.
  cbn [Z.of_nat]. rewrite Z.add_0_r. replace (le_byte 0 1 0) with 0 by reflexivity.
  apply e0_byte_of_aview. rewrite K4 by (unfold d_obj, dobj_off; lia).
  rewrite (Hset (Z.of_nat j) ltac:(lia)). reflexivity. }
assert (REGS : forall R : bvmap 5 word,
  getr R 2 = ew (d_env cx E vals2) 60 -> getr R 3 = ew (d_env cx E vals2) 534 ->
  getr R 4 = ew (d_env cx E vals2) 535 -> getr R 8 = ew (d_env cx E vals2) 2 ->
  getr R 9 = ew (d_env cx E vals2) 60 -> getr R 18 = Z_to_bv 64 4294977024 ->
  getr R 19 = ew (d_env cx E vals2) 32 -> getr R 20 = Z_to_bv 64 32 ->
  getr R 24 = ew (d_env cx E vals2) 555 -> getr R 27 = ew (d_env cx E vals2) 529 ->
  d_rL B cx R /\ getr R 24 = w64 buf /\ getr R 27 = w64 (shadow_addr (d_FB cx))).
{ intros R G2 G3 G4 G8 G9 G18 G19 G20 G24 G27.
  pose proof HRL2 as (L2 & L3 & L4 & L8 & L9 & L19 & L18 & L20 & L27).
  assert (Y3 : ew (d_env cx E vals2) 534 = getr regs2 3)
    by exact (e0_env_reg cx E regs2 [Z_to_bv 64 count] (3%bv : bv 5) 534%nat eq_refl).
  assert (Y4 : ew (d_env cx E vals2) 535 = getr regs2 4)
    by exact (e0_env_reg cx E regs2 [Z_to_bv 64 count] (4%bv : bv 5) 535%nat eq_refl).
  assert (Y24 : ew (d_env cx E vals2) 555 = getr regs2 24)
    by exact (e0_env_reg cx E regs2 [Z_to_bv 64 count] (24%bv : bv 5) 555%nat eq_refl).
  assert (Z2 : ew (d_env cx E vals2) 2 = w64 (d_S cx))
    by (rewrite d_env_old by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
        unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Z60 : ew (d_env cx E vals2) 60%nat = w64 (d_A cx))
    by (rewrite d_env_old by (unfold AT_FL; lia); exact E60).
  assert (Z32 : ew (d_env cx E vals2) 32 = w64 SHADOW_OFF)
    by (rewrite d_env_old by (unfold AT_FL; lia); exact E32).
  assert (Z529 : ew (d_env cx E vals2) 529%nat = w64 (shadow_addr (d_FB cx)))
    by (rewrite d_env_old by (unfold AT_FL; lia); exact ESH).
  split; [|split].
  - split; [unfold spZ; rewrite G2, Z60; unfold w64; apply unsigned_lit_small; lia|].
    split; [rewrite G3, Y3; exact L3|]. split; [rewrite G4, Y4; exact L4|].
    split; [rewrite G8, Z2; reflexivity|]. split; [rewrite G9, Z60; reflexivity|].
    split; [rewrite G19, Z32; reflexivity|]. split; [rewrite G18; unfold w64, WS_MASK; reflexivity|].
    split; [rewrite G20; reflexivity|]. rewrite G27, Z529. reflexivity.
  - rewrite G24, Y24, P24', Q24, X24. exact R24.
  - rewrite G27, Z529. reflexivity. }
assert (FIN14 : forall (ms4 : machine_state) md4,
  ms4 = YK11.mkst (fx := fq) (ms_regs ms4) (Z_to_bv 64 (BASE + R14_OFF)) (ms_mem ms4) (YK11.seg_rom SEGS) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms4) md4 k ->
  d_rL B cx (ms_regs ms4) -> getr (ms_regs ms4) 24 = w64 buf ->
  getr (ms_regs ms4) 27 = w64 (shadow_addr (d_FB cx)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 360 <= a < d_A cx + 376) ->
     aview SEGS (w_H W) (ms_mem ms4) a = aview SEGS (w_H W) mem2 a) ->
  mem_grows (rd W mem2) (rd W (ms_mem ms4)) ->
  r14_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W (mkCfg ms4 md4)).
{ intros ms4 md4 Ems4 HJ4 HRL4 R244 R274 K4 G4.
  destruct (LAND (ms_mem ms4) K4 G4) as (HB4 & HSP14 & HSP04 & HTAB4 & _).
  rewrite Ems4. unfold r14_in. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms4), (ms_mem ms4), md4, k, acc.
  split; [reflexivity|].
  split; [exact HFRM0|].
  split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split; [exact HRL4|]. split; [split; [exact R274 | exact R244]|].
  split; [split; [exact HSP14 | exact HTAB4]|]. split; [exact HSP04 | exact HB4]. }
assert (FINPH : 1 <= count -> forall (ms4 : machine_state) md4,
  ms4 = YK11.mkst (fx := fq) (ms_regs ms4) (Z_to_bv 64 (BASE + PH_OFF)) (ms_mem ms4) (YK11.seg_rom SEGS) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms4) md4 k ->
  d_rL B cx (ms_regs ms4) -> getr (ms_regs ms4) 24 = w64 buf ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 360 <= a < d_A cx + 376) ->
     aview SEGS (w_H W) (ms_mem ms4) a = aview SEGS (w_H W) mem2 a) ->
  mem_grows (rd W mem2) (rd W (ms_mem ms4)) ->
  val_mem SEGS (rd W (ms_mem ms4)) (d_A cx + 368) 8 0 ->
  val_mem SEGS (rd W (ms_mem ms4)) (d_A cx + 360) 8 count ->
  f_ph B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 0 W (mkCfg ms4 md4)).
{ intros Hc1 ms4 md4 Ems4 HJ4 HRL4 R244 K4 G4 V368 V360.
  destruct (LAND (ms_mem ms4) K4 G4) as (HB4 & HSP14 & HSP04 & HTAB4 & HBUF4 & HOO4 & HUS4).
  rewrite Ems4. unfold f_ph, a3f_st. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms4), (ms_mem ms4), md4, k, acc.
  split; [reflexivity|].
  split; [exact HFRM0|].
  split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split; [exact HRL4|]. split; [split; [exact R244 | exact I]|].
  split; [|split; [exact HSP04 | exact HB4]].
  split; [exact HSP14|]. split; [exact HTAB4|]. split; [exact HBUF4|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO4|].
  split; [split; [lia | split; [exact V368 | exact V360]] | exact HUS4]. }
assert (Hc3 : count = 0 \/ 1 <= count <= 7 \/ count = 8) by lia.
destruct Hc3 as [Ec0 | [Hc17 | Ec8]].
- pose proof (SEAT 0 0 ltac:(lia) ltac:(lia)) as HT.
  paj_run_to_shc RUNTOP HT HJ2 R14_OFF.
  { apply (e0_awr3 _ _ _ _ _ _ _ _ (d_A cx)); [exact W60 | unfold LLVMF_STK; lia | lia]. }
  rename ms into ms5. rename mat into mat5. rename HF into HF5. rename HFr into HFr5. rename HG into HG5.
  prreg HT (10%bv : bv 5) Q10b.
  lazymatch type of HT with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    pose proof (ast_ok_pi_set_reg_fp Ex ssx msx (10%bv : bv 5) (SLit 0) HT ltac:(vm_compute; reflexivity)
      ltac:(cbn [sv_denot ms_regs restrict]; rewrite Q10b; change 563%nat with E0_CNT;
            rewrite ECNT2, Ec0; reflexivity)) as HT3 end.
  clear HT. rename HT3 into HT. norm_ss HT.
  paj_run_to_shc RUNTOP HT HJ2 R14_OFF.
  { apply (e0_awr3 _ _ _ _ _ _ _ _ (d_A cx)); [exact W60 | unfold LLVMF_STK; lia | lia]. }
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 360 <= a < d_A cx + 376) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a).
  { intros a Ha Hna. transitivity (aview SEGS (w_H W) (ms_mem ms5) a).
    - apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia.
      intros Hw. apply e0_inw3 in Hw.
      change (base_val (d_env cx E vals2) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals2) AT_A)) in Hw.
      rewrite W60 in Hw. lia.
    - apply (aview_eq_of SEGS). apply HFr5. rewrite unsigned_lit_small by lia.
      intros Hw. apply e0_inw3 in Hw.
      change (base_val (d_env cx E vals2) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals2) AT_A)) in Hw.
      rewrite W60 in Hw. lia. }
  assert (G4 : mem_grows (rd W mem2) (rd W (ms_mem ms))) by (intros x Hx; apply HG; apply HG5; exact Hx).
  prreg HT (2%bv : bv 5) S2. prreg HT (3%bv : bv 5) S3'. prreg HT (4%bv : bv 5) S4.
  prreg HT (8%bv : bv 5) S8. prreg HT (9%bv : bv 5) S9. prreg HT (18%bv : bv 5) S18.
  prreg HT (19%bv : bv 5) S19. prreg HT (20%bv : bv 5) S20. prreg HT (24%bv : bv 5) S24.
  prreg HT (27%bv : bv 5) S27.
  destruct (REGS (ms_regs ms) S2 S3' S4 S8 S9 S18 S19 S20 S24 S27) as (HRL4 & R244 & R274).
  apply SRr_ret. cbv beta. left.
  exact (FIN14 ms _ (st_ok_pi_restrict_mkst _ _ _ _ HT eq_refl) HJ2 HRL4 R244 R274 K4 G4).
- pose proof (SEAT 1 7 ltac:(lia) ltac:(lia)) as HT.
  paj_run_to_shc RUNTOP HT HJ2 PH_OFF.
  { apply (e0_awr3 _ _ _ _ _ _ _ _ (d_A cx)); [exact W60 | unfold LLVMF_STK; lia | lia]. }
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 360 <= a < d_A cx + 376) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a).
  { intros a Ha Hna. apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia.
    intros Hw. apply e0_inw3 in Hw.
    change (base_val (d_env cx E vals2) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals2) AT_A)) in Hw.
    rewrite W60 in Hw. lia. }
  prreg HT (2%bv : bv 5) S2. prreg HT (3%bv : bv 5) S3'. prreg HT (4%bv : bv 5) S4.
  prreg HT (8%bv : bv 5) S8. prreg HT (9%bv : bv 5) S9. prreg HT (18%bv : bv 5) S18.
  prreg HT (19%bv : bv 5) S19. prreg HT (20%bv : bv 5) S20. prreg HT (24%bv : bv 5) S24.
  prreg HT (27%bv : bv 5) S27.
  destruct (REGS (ms_regs ms) S2 S3' S4 S8 S9 S18 S19 S20 S24 S27) as (HRL4 & R244 & _).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HT eq_refl) as RA. cbn [ms_mem restrict] in RA.
  assert (V368 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 368) 8 0)
    by exact (field_of_region (d_env cx E vals2) _ AT_A (d_A cx) _ 0 472 360 376 368 8%N _ 0 RA W60
      ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (V360 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 360) 8 count)
    by exact (field_of_region (d_env cx E vals2) _ AT_A (d_A cx) _ 0 472 360 376 360 8%N _ count RA W60
      ltac:(cbn [In]; right; left; reflexivity)
      ltac:(cbn [sv_denot]; change 563%nat with E0_CNT; rewrite UCNT2, Z.add_0_r; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)).
  apply SRr_ret. cbv beta. right.
  exact (FINPH ltac:(lia) ms _ (st_ok_pi_restrict_mkst _ _ _ _ HT eq_refl) HJ2 HRL4 R244 K4 HG V368 V360).
- pose proof (SEAT 8 8 ltac:(lia) ltac:(lia)) as HT.
  paj_run_to_shc RUNTOP HT HJ2 PH_OFF.
  { apply (e0_awr3 _ _ _ _ _ _ _ _ (d_A cx)); [exact W60 | unfold LLVMF_STK; lia | lia]. }
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 360 <= a < d_A cx + 376) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a).
  { intros a Ha Hna. apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia.
    intros Hw. apply e0_inw3 in Hw.
    change (base_val (d_env cx E vals2) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals2) AT_A)) in Hw.
    rewrite W60 in Hw. lia. }
  prreg HT (2%bv : bv 5) S2. prreg HT (3%bv : bv 5) S3'. prreg HT (4%bv : bv 5) S4.
  prreg HT (8%bv : bv 5) S8. prreg HT (9%bv : bv 5) S9. prreg HT (18%bv : bv 5) S18.
  prreg HT (19%bv : bv 5) S19. prreg HT (20%bv : bv 5) S20. prreg HT (24%bv : bv 5) S24.
  prreg HT (27%bv : bv 5) S27.
  destruct (REGS (ms_regs ms) S2 S3' S4 S8 S9 S18 S19 S20 S24 S27) as (HRL4 & R244 & _).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HT eq_refl) as RA. cbn [ms_mem restrict] in RA.
  assert (V368 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 368) 8 0)
    by exact (field_of_region (d_env cx E vals2) _ AT_A (d_A cx) _ 0 472 360 376 368 8%N _ 0 RA W60
      ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (V360 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 360) 8 count)
    by exact (field_of_region (d_env cx E vals2) _ AT_A (d_A cx) _ 0 472 360 376 360 8%N _ count RA W60
      ltac:(cbn [In]; right; left; reflexivity)
      ltac:(rewrite Ec8; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)).
  apply SRr_ret. cbv beta. right.
  exact (FINPH ltac:(lia) ms _ (st_ok_pi_restrict_mkst _ _ _ _ HT eq_refl) HJ2 HRL4 R244 K4 HG V368 V360).
Qed.
End h.
End f.
End d.
