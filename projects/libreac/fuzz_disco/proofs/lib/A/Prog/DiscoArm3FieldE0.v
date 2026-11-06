(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 568 of its 627 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntClsCuts.v, with its module names changed; 1003 of its 1072 lines of code are new or changed and 558 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC45 YC85 YC88 YC81 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt DiscoEntSeat DiscoRo DiscoEntBodyStmt DiscoEntBody FindEntry.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacBoxName ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoArm3FieldCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition e0_sr : list sv := SLit 0 :: atom_regs 531 8 ++ SOff 60 0 :: atom_regs 540 22.
Definition e0_sr3 : list sv :=
  SLit 0 :: atom_regs 531 8 ++ SOff 60 0 :: atom_regs 540 11 ++ SOff 562 0 :: atom_regs 552 10.
Definition e0_fcs : list YP09.chunk := [YP09.mkChunk 2544 (CVal 4 (SOff 562 0))].
Definition e0_acs3 : list YP09.chunk := [YP09.mkChunk 344 (CVal 8 (SOff 563 0))].
Definition e0_G : facts := d_facts [(562%nat, mkAF 0 8 0)] [].
Definition e0_sh1 : list YP09.chunk := Eval vm_compute in dsh_chunks dsh_ser.
Definition e0_sh2 : list YP09.chunk := Eval vm_compute in dsh_chunks dsh_ser2.
Definition e0_rs1 : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ []);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ e0_fcs);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 208 212 e0_sh1;
   got_regionP; bcell_regionP 32].
Definition e0_rs3 : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 336 376 (dslot_chunks ++ e0_acs3);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ []);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 0 0 e0_sh2;
   got_regionP; bcell_regionP 32].

Lemma e0_subregion : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.
Lemma e0_sh1_eq : e0_sh1 = dsh_chunks dsh_ser. Proof. vm_compute. reflexivity. Qed.
Lemma e0_sh2_eq : e0_sh2 = dsh_chunks dsh_ser2. Proof. vm_compute. reflexivity. Qed.
Lemma e0_subrefl : forall r, subregion r r.
Proof. intros [b lo hi wlo whi cs]. apply e0_subregion. lia. Qed.
Lemma e0_submem1 : submem e0_rs1 (d_kregions dsh_ser [] e0_fcs ++ []).
Proof.
  unfold e0_rs1, d_kregions, fshadow_region. rewrite app_nil_r, e0_sh1_eq.
  apply submem_keep; [apply e0_subrefl|].
  apply submem_keep; [apply e0_subregion; lia|].
  apply submem_keep; [apply e0_subregion; lia|].
  apply submem_keep; [apply e0_subregion; unfold DFRAME_SH; lia|].
  apply submem_keep; [apply e0_subrefl|].
  apply submem_keep; [apply e0_subrefl|].
  apply submem_nil.
Qed.
Lemma e0_submem3 : submem e0_rs3 (d_kregions dsh_ser2 e0_acs3 [] ++ []).
Proof.
  unfold e0_rs3, d_kregions, fshadow_region. rewrite app_nil_r, e0_sh2_eq.
  apply submem_keep; [apply e0_subrefl|].
  apply submem_keep; [apply e0_subregion; lia|].
  apply submem_keep; [apply e0_subregion; lia|].
  apply submem_keep; [apply e0_subregion; lia|].
  apply submem_keep; [apply e0_subrefl|].
  apply submem_keep; [apply e0_subrefl|].
  apply submem_nil.
Qed.
Lemma e0_wf1 : regions_wf e0_rs1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma e0_wf3 : regions_wf e0_rs3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma e0_kwf1 : regions_wf (d_kregions dsh_ser [] e0_fcs ++ []) = true. Proof. vm_compute. reflexivity. Qed.
Lemma e0_kwf3 : regions_wf (d_kregions dsh_ser2 e0_acs3 [] ++ []) = true. Proof. vm_compute. reflexivity. Qed.
Lemma e0_inw1 : forall E a, in_wrange E e0_rs1 a ->
  base_val E (Some AT_SH) + 208 <= a < base_val E (Some AT_SH) + 212.
Proof.
  intros E a (r & Hin & Hr). unfold e0_rs1 in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold got_regionP, bcell_regionP in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma e0_inw3 : forall E a, in_wrange E e0_rs3 a ->
  base_val E (Some AT_A) + 336 <= a < base_val E (Some AT_A) + 376.
Proof.
  intros E a (r & Hin & Hr). unfold e0_rs3 in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold got_regionP, bcell_regionP in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma e0_awr1 : forall E STK sp0 FP bl0 blc ly (own : list (Z * Z)) cid pos,
  bv_unsigned (ew E AT_SH) = shadow_addr (frame_addr ly cid pos) -> In (cid, pos) own ->
  512 <= fs_frame_bytes cid / 8 ->
  awr_ok E e0_rs1 STK sp0 FP bl0 blc ly own.
Proof.
  intros E STK sp0 FP bl0 blc ly own cid pos Hb Hin Hsz. unfold e0_rs1.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ AT_SH); [reflexivity | exact Hb | | ].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists cid, pos. split; [exact Hin|]. right. unfold in_zr. cbn [fst snd]. lia.
  - apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
    apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|]. apply awr_ok_nil.
Qed.
Lemma e0_awr3 : forall E STK sp0 FP bl0 blc ly own a,
  bv_unsigned (ew E AT_A) = a -> sp0 - STK <= a + 336 -> a + 376 <= sp0 ->
  awr_ok E e0_rs3 STK sp0 FP bl0 blc ly own.
Proof.
  intros E STK sp0 FP bl0 blc ly own a Ha H1 H2. unfold e0_rs3.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ AT_A (a - sp0)); [reflexivity | lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|]. apply awr_ok_nil.
Qed.
Lemma e0_soff : forall E n z b, bv_unsigned (ew E n) = b -> sv_denot E (SOff n z) = Z_to_bv 64 (b + z).
Proof. intros E n z b Hb. cbn [sv_denot]. rewrite Hb. reflexivity. Qed.
Lemma e0_sextw : forall (x : word) c, bv_unsigned x mod 2 ^ 32 = c -> 0 <= c < 2 ^ 31 ->
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 0))) = Z_to_bv 64 c.
Proof.
  intros x c Hx Hc. rewrite sext64_lit. f_equal.
  cbn [alu32 alu]. rewrite low32_lit.
  unfold bv_signed. rewrite bv_add_unsigned, low32_unsigned, !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.add_0_r. Z.div_mod_to_equations. lia.
Qed.
Lemma e0_vis : forall segs (H : word -> bool) m a, apresent H m a -> aview segs H m a <> None.
Proof.
  intros segs H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn [option_map]. discriminate.
Qed.
Lemma e0_dsh2 : forall k, ~ (208 <= k < 212) -> dsh_ser2 k = dsh_ser k.
Proof.
  intros k Hk. unfold dsh_ser2, dsh_ser, dsh, dobjs. cbn [dsh_look live_ser live_ser2].
  destruct (dsh_in OCUR k); [reflexivity|]. destruct (dsh_in OO k); [reflexivity|].
  destruct (dsh_in OUSED k) eqn:EU; [|reflexivity].
  exfalso. unfold dsh_in, dobj_off, dobj_size in EU. apply andb_prop in EU as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn in E1, E2. lia.
Qed.
Lemma e0_dsh2_used : forall k, 208 <= k < 212 -> dsh_ser2 k = 0.
Proof.
  intros k Hk. assert (Hk4 : k = 208 \/ k = 209 \/ k = 210 \/ k = 211) by lia.
  destruct Hk4 as [ -> | [ -> | [ -> | -> ] ] ]; vm_compute; reflexivity.
Qed.
Lemma e0_used0 : a3f_used 0 = repeat 0 32.
Proof. vm_compute. reflexivity. Qed.
Lemma e0_rep_nth : forall (j : nat), (j < 32)%nat -> nth j (repeat 0 32) 0 = 0.
Proof. intros j Hj. apply nth_repeat. Qed.
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

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma e0_x : forall cx E (R : bvmap 5 word) (c d : word) (j : nat), (j < 31)%nat ->
  ew (d_env cx E (map (getr R) (tl all_regs) ++ [c; d])) (AT_X + j) = getr R (nth j (tl all_regs) 0%bv).
Proof.
  intros cx E R c d j Hj. rewrite d_env_x by (rewrite length_app, length_map; cbn; lia).
  rewrite app_nth1 by (rewrite length_map; cbn; lia).
  rewrite (nth_indep _ _ (getr R 0%bv)) by (rewrite length_map; cbn; lia).
  apply map_nth.
Qed.
Lemma e0_atom : forall cx E (R : bvmap 5 word) (c d : word) (j : nat), (j < 31)%nat ->
  sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ [c; d])) (SOff (AT_X + j) 0) = getr R (nth j (tl all_regs) 0%bv).
Proof.
  intros cx E R c d j Hj. cbn [sv_denot]. rewrite e0_x by exact Hj. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma e0_c : forall cx E (R : bvmap 5 word) (c d : word),
  ew (d_env cx E (map (getr R) (tl all_regs) ++ [c; d])) 562 = c.
Proof.
  intros cx E R c d. change (562%nat) with (AT_X + 31)%nat.
  rewrite d_env_x by (rewrite length_app, length_map; cbn; lia).
  rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map. cbn. reflexivity.
Qed.
Lemma e0_d : forall cx E (R : bvmap 5 word) (c d : word),
  ew (d_env cx E (map (getr R) (tl all_regs) ++ [c; d])) 563 = d.
Proof.
  intros cx E R c d. change (563%nat) with (AT_X + 32)%nat.
  rewrite d_env_x by (rewrite length_app, length_map; cbn; lia).
  rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map. cbn. reflexivity.
Qed.
Lemma e0_regs_ok : forall cx E (R : bvmap 5 word) (c d : word),
  getr R 9 = w64 (d_A cx) -> ew E AT_A = w64 (d_A cx) -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs) ++ [c; d])) e0_sr R.
Proof.
  intros cx E R c d R9 E60 HA.
  assert (S60 : sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ [c; d])) (SOff 60 0) = w64 (d_A cx)).
  { cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite E60.
    unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity | rewrite S60; exact R9 ]).
Qed.
Lemma e0_regs_ok3 : forall cx E (R : bvmap 5 word) (c d : word),
  getr R 9 = w64 (d_A cx) -> getr R 21 = c -> ew E AT_A = w64 (d_A cx) -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs) ++ [c; d])) e0_sr3 R.
Proof.
  intros cx E R c d R9 R21 E60 HA.
  assert (S60 : sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ [c; d])) (SOff 60 0) = w64 (d_A cx)).
  { cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite E60.
    unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  assert (S562 : sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ [c; d])) (SOff 562 0) = c).
  { cbn [sv_denot]. rewrite (e0_c cx E R c d), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
  regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity | rewrite S60; exact R9 | rewrite S562; exact R21 ]).
Qed.
Lemma e0_aview_byte : forall (H : word -> bool) (m : word -> option byte) a v,
  mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
  intros H m a v Hm Hv. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma e0_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> IMG_LO <= a < IMG_TOP.
Proof.
  intros a [ (s & Hs & _ & Hr) | Hr ]; apply pa_img_range; [exists s; split; [exact Hs | exact Hr] | apply pa_relro_img; exact Hr].
Qed.
Lemma e0_frame_aview : forall (E : env) (rs : smem) (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> ~ in_wrange E rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' a HF Hn Ha. unfold aview, mbyte.
  rewrite (HF (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hn)). reflexivity.
Qed.
Lemma e0_rok : forall E (m m' : word -> option byte) nn b lo hi wlo whi cs clo chi,
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = b ->
  (forall a, b + clo <= a < b + chi -> mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall o, wlo <= o < whi -> writable_at SEGS m' (b + o)) ->
  forallb (fun c => (clo <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? chi)) cs = true ->
  region_ok SEGS E m' (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
  intros E m m' nn b lo hi wlo whi cs clo chi HR Hb HK HW HC.
  unfold region_ok in HR |- *.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR |- *.
  rewrite Hb in HR |- *. destruct HR as (H1 & H2 & _ & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact HW|].
  apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) H4 c Hc) as Hck.
  pose proof (proj1 (forallb_forall _ _) HC c Hc) as Hin. cbn beta in Hin.
  apply andb_prop in Hin as [Hin1 Hin2]. apply Z.leb_le in Hin1. apply Z.leb_le in Hin2.
  intros i Hi. destruct (Hck i Hi) as (bb & Hcb & Hmb). exists bb. split; [exact Hcb|].
  rewrite HK by lia. exact Hmb.
Qed.
Lemma e0_mbyte_kept : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview SEGS H m' a = aview SEGS H m a -> mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof. intros H m m' a Ha. exact (mbyte_of_aview SEGS H H m m' a Ha). Qed.
Lemma e0_rdword_ext : forall (H : word -> bool) (m m' : word -> option byte) a v,
  (forall x, a <= x < a + 8 -> aview SEGS H m' x = aview SEGS H m x) ->
  rdword (aview SEGS H m) a = Some v -> rdword (aview SEGS H m') a = Some v.
Proof.
  intros H m m' a v HK HV. unfold rdword in HV |- *.
  rewrite (HK a ltac:(lia)), (HK (a + 1) ltac:(lia)), (HK (a + 2) ltac:(lia)), (HK (a + 3) ltac:(lia)),
    (HK (a + 4) ltac:(lia)), (HK (a + 5) ltac:(lia)), (HK (a + 6) ltac:(lia)), (HK (a + 7) ltac:(lia)).
  exact HV.
Qed.
Lemma e0_mbyte_of_aview : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> 0 <= v < 256 /\ mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
  intros H m a v Hv. destruct (aview_byte SEGS H m a v Hv) as (b & Hm & Hvb & Hr).
  split; [exact Hr|]. rewrite Hm, Hvb, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma e0_garr8_keep : forall (H : word -> bool) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS H m' x = aview SEGS H m x) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
  intros H m m' a l HK HG j Hj. destruct (HG j Hj) as (HV & HB). split; [|exact HB].
  eapply (val_mem_kept SEGS H H m m'); [|exact HV].
  intros kk Hkk. cbn [Z.of_nat] in Hkk. apply HK. lia.
Qed.
Lemma e0_zero_garr8 : forall (H : word -> bool) (m : word -> option byte) a (l : list Z),
  (forall x, 0 <= x < Z.of_nat (length l) -> aview SEGS H m (a + x) = Some 0) ->
  (forall j, (j < length l)%nat -> nth j l 0 = 0) ->
  garr8 SEGS (mrestrict H m) a l.
Proof.
  intros H m a l HK HZ j Hj. rewrite (HZ j Hj). split; [|lia].
  exact (proj1 (YC88.val_mem1_of_aview SEGS H m _ 0 (HK (Z.of_nat j) ltac:(lia)))).
Qed.
Lemma e0_rl_of : forall (B : asyms) cx (R R' : bvmap 5 word),
  getr R' 2 = getr R 2 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 -> getr R' 8 = getr R 8 ->
  getr R' 9 = w64 (d_A cx) -> getr R' 18 = getr R 18 -> getr R' 20 = getr R 20 -> getr R' 25 = getr R 25 ->
  d_rL B cx R -> d_rL B cx R'.
Proof.
  intros B cx R R' H2 H3 H4 H8 H9 H18 H20 H25 (Hsp & Hgp & Htp & Hs0 & Hs1 & Hs2 & Hs4 & Hs9).
  unfold d_rL. split; [unfold spZ in Hsp |- *; rewrite H2; exact Hsp|].
  split; [rewrite H3; exact Hgp|]. split; [rewrite H4; exact Htp|]. split; [rewrite H8; exact Hs0|].
  split; [exact H9|]. split; [rewrite H18; exact Hs2|]. split; [rewrite H20; exact Hs4|].
  rewrite H25; exact Hs9.
Qed.
Lemma e0_beq0 : forall E k c, ew E k = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 ->
  (branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = true <-> c = 0).
Proof.
  intros E k c Hk Hc. rewrite branch_eq_U, U_SOff, U_lit by lia. rewrite Hk, Z.add_0_r.
  rewrite unsigned_lit_small by lia. rewrite YP0m.zcanon_small by lia. apply Z.eqb_eq.
Qed.
Lemma e0_bltu : forall E k c m, ew E k = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  (branch_taken BC_LTU (sv_denot E (SOff k 0)) (sv_denot E (SLit m)) = true <-> c < m).
Proof.
  intros E k c m Hk Hc Hm. rewrite branch_ltu_U, U_SOff, U_lit by lia. rewrite Hk, Z.add_0_r.
  rewrite unsigned_lit_small by lia. rewrite YP0m.zcanon_small by lia. apply Z.ltb_lt.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis MT_TRIV : MT = ameter_triv.

Theorem a3f_e0 : seg_e0_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad W c (HFROM & HD).
destruct HD as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R21 & R26) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (a3f_count T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof (ReacDiscoTableAge.age_val (rd W mem3) T1 (d_obj cx OT) 384 4 HGT ltac:(lia) ltac:(rewrite HLT1; lia)) as HTN.
rewrite (ReacDiscoTableAge.u_of_n T1 HLT1 ltac:(lia)), <- Ec in HTN.
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & Hgeo & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
pose proof HSP1 as ((H232 & H344) & H224 & H248).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_lt as Hceil0. pose proof alloc_ceiling_value as (Hceil1 & _).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (LOO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296).
{ rewrite (e0_objs_len buf vpad os HVP Lo6), Los. lia. }
assert (Hinh : In (h, slot_inv.HUNT_SIZE) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. right. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 h slot_inv.HUNT_SIZE DFRAME_CLASS (c_fpos cx) HAR3 Hinh HFin3) as HSEPh.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 buf (Z.max (slot_ser_defs.ser_cap op) 1)
  DFRAME_CLASS (c_fpos cx) HAR3 Hinb HFin3) as HSEPb.
unfold zdisjoint, in_zr in HSEPh, HSEPb. cbn [fst snd] in HSEPh, HSEPb.
rewrite EFA3 in HSEPh, HSEPb. change (fs_frame_bytes DFRAME_CLASS) with 4096 in HSEPh, HSEPb.
pose proof HBASE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & Hpn & _).
assert (HINP0 : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)).
{ intros Hpos. apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app].
  right. right. destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia | exact Hin]. }
destruct (proj1 (Z.mod_divide (d_FB cx) 32 ltac:(lia)) GF32) as (qf & EQF).
destruct (proj1 (Z.mod_divide (d_A cx) 32 ltac:(lia)) GA32) as (qa & EQA).
destruct (proj1 (Z.mod_divide (d_S cx) 16 ltac:(lia)) GS16) as (qs & EQS).
clear GF32 GA32 GS16.
assert (ESHA : shadow_addr (d_FB cx) = 2147450880 + 4 * qf).
{ unfold shadow_addr, SHADOW_OFF. rewrite EQF. replace (qf * 32) with (4 * qf * 8) by lia.
  rewrite Z.div_mul by lia. reflexivity. }
assert (SHA : forall z, 0 <= z -> shadow_addr (d_FB cx + z) = shadow_addr (d_FB cx) + z / 8).
{ intros z Hz. rewrite ESHA. unfold shadow_addr, SHADOW_OFF. rewrite EQF.
  replace (qf * 32 + z) with (4 * qf * 8 + z) by lia. rewrite Z.div_add_l by lia. lia. }
assert (HSHlo : 2147450880 <= shadow_addr (d_FB cx)) by lia.
assert (HSHhi : shadow_addr (d_FB cx) + 512 < 17594333495296) by lia.
assert (HFBSH : d_FB cx + 4096 <= shadow_addr (d_FB cx) \/ shadow_addr (d_FB cx) + 512 <= d_FB cx).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
  destruct GFapp as (Hg1 & [Hg2 | (Hg2 & Hg3)]); [left; lia | right; lia]. }
assert (NOTRD : forall a, (d_FB cx + 1664 <= a < d_FB cx + 1696) \/
  (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) -> ~ d_rdset B cx h a).
{ intros a Ha Hrd.
  assert (HFBo : (d_FB cx <= a < d_FB cx + 4096) \/ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512)) by lia.
  unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size in Hrd.
  destruct Hrd as [HT|[HG|[HL|[HU|[HHh|[HIn|[HRo|HCn]]]]]]];
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hhapp, Hbapp.
  - lia.
  - lia.
  - lia.
  - lia.
  - change (req_size slot_inv.HUNT_SIZE) with 480 in HSEPh, Hhapp. change slot_inv.HUNT_SIZE with 480 in HHh. lia.
  - destruct HIn as (Hpos & HIn).
    pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 (HINP0 Hpos)) as (_ & Hp4096 & Hpceil & Hpapp & _).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) DFRAME_CLASS (c_fpos cx)
      HAR3 (HINP0 Hpos) HFin3) as HSEPp.
    unfold zdisjoint, in_zr in HSEPp. cbn [fst snd] in HSEPp. rewrite EFA3 in HSEPp.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in HSEPp.
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrqp).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp. lia.
  - destruct HRo as (HRo & _ & _). pose proof (e0_roP_img a HRo) as Hro. unfold off_img, IMG_LO, IMG_TOP in HOFFF, Hro.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in HOFFF. lia.
  - unfold AE2k.FF_canary in HCn. unfold off_img, IMG_LO, IMG_TOP in HOFFF.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in HOFFF. lia. }

remember (map (getr regs) (tl all_regs) ++ [Z_to_bv 64 count; Z_to_bv 64 now]) as V1 eqn:HV1.
pose proof (d_E_env cx E V1 HE) as HE1.
pose proof HE1 as (_ & _ & HEI1 & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E V1) 60) = d_A cx).
{ rewrite (E60' : ew (d_env cx E V1) 60 = w64 (d_A cx)). unfold w64. apply unsigned_lit_small. lia. }
assert (U516 : bv_unsigned (ew (d_env cx E V1) 516) = d_FB cx).
{ rewrite (EF' : ew (d_env cx E V1) 516 = w64 (d_FB cx)). unfold w64. apply unsigned_lit_small. lia. }
assert (U529 : bv_unsigned (ew (d_env cx E V1) 529) = shadow_addr (d_FB cx)).
{ rewrite (ESH' : ew (d_env cx E V1) 529 = w64 (shadow_addr (d_FB cx))). unfold w64. apply unsigned_lit_small. lia. }
assert (E562 : ew (d_env cx E V1) 562 = Z_to_bv 64 count) by (rewrite HV1; apply e0_c).
assert (Hregs1 : regs_ok (d_env cx E V1) e0_sr regs) by (rewrite HV1; apply (e0_regs_ok cx E regs); [exact Rs1 | exact E60 | lia]).
assert (HG1 : facts_ok (d_env cx E V1) e0_G).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E V1 [(562%nat, mkAF 0 8 0)] [] HCTX HE); [|exact I].
  cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E562, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (Hfcs1 : Forall (YP09.chunk_ok SEGS (d_env cx E V1) (rd W mem3) (d_FB cx)) e0_fcs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) 2544 4%N (SOff 562 0) count).
  - cbn [sv_denot]. rewrite E562, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (unfold d_obj, dobj_off; lia). exact HTN. }
pose proof (DSEAT LAWS PAL fq cx dsh_ser ly3 S3 W regs mem3 md3 k E R12_OFF e0_sr V1 [] e0_fcs [] e0_G
  HCTX HE HREG HFLAG Hregs1 HG1 (Forall_nil _) Hfcs1 (Forall_nil _) I (Forall_nil _) e0_kwf1) as HS0.
pose proof (st_ok_pi_submem _ _ _ e0_rs1 HS0 e0_submem1 e0_wf1) as HS.
clear HS0. cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HS.
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
assert (HAWR1 : forall bl0 blc, awr_ok (d_env cx E V1) e0_rs1 LLVMF_STK (d_S cx) [] bl0 blc ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ intros bl0 blc. apply (e0_awr1 _ _ _ _ _ _ _ _ DFRAME_CLASS (c_fpos cx)).
  - change AT_SH with 529%nat. rewrite U529, EFA3. reflexivity.
  - left. reflexivity.
  - change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) ->
  ~ in_wrange (d_env cx E V1) e0_rs1 a).
{ intros a Ha Hna Hw. apply e0_inw1 in Hw. change (base_val (d_env cx E V1) (Some AT_SH)) with (bv_unsigned (ew (d_env cx E V1) 529)) in Hw.
  rewrite U529 in Hw. lia. }
unfold cfg_at, w64.
paj_run_to_shc RUNTOP HS HJ 7448.
{ apply HAWR1. }
rename HF into HFa. rename HFr into HFra. rename HG into HGa.
prreg HS (21%bv : bv 5) Q21.
change (ew (d_env cx E V1) 551) with (ew (d_env cx E V1) (AT_X + 20)) in Q21.
rewrite HV1, e0_x in Q21 by lia.
change (nth 20 (tl all_regs) 0%bv) with (21%bv : bv 5) in Q21.
rewrite (e0_sextw (getr regs 21) count R21 ltac:(lia)) in Q21.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ex ssx msx (21%bv : bv 5) (SOff 562 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot]; rewrite E562, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact Q21)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
paj_run_shc RUNP RUNC HS HJ.
{ apply HAWR1. }
rename HF into HFc. rename HFr into HFrc. rename HG into HGc.

prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (1%bv : bv 5) Q1. prreg HS (9%bv : bv 5) Q9. prreg HS (21%bv : bv 5) Q21b.
assert (ESH529 : ew (d_env cx E V1) 529 = w64 (shadow_addr (d_FB cx))) by exact ESH'.
assert (EA60n : ew (d_env cx E V1) 60 = w64 (d_A cx)) by exact E60'.
assert (EF516 : ew (d_env cx E V1) 516 = w64 (d_FB cx)) by exact EF'.
prreg HS (2%bv : bv 5) Q2.
change (ew (d_env cx E V1) 532) with (ew (d_env cx E V1) (AT_X + 1)) in Q2.
rewrite HV1, e0_x in Q2 by lia. change (nth 1 (tl all_regs) 0%bv) with (2%bv : bv 5) in Q2.
prreg HS (3%bv : bv 5) Q3.
change (ew (d_env cx E V1) 533) with (ew (d_env cx E V1) (AT_X + 2)) in Q3.
rewrite HV1, e0_x in Q3 by lia. change (nth 2 (tl all_regs) 0%bv) with (3%bv : bv 5) in Q3.
prreg HS (4%bv : bv 5) Q4.
change (ew (d_env cx E V1) 534) with (ew (d_env cx E V1) (AT_X + 3)) in Q4.
rewrite HV1, e0_x in Q4 by lia. change (nth 3 (tl all_regs) 0%bv) with (4%bv : bv 5) in Q4.
prreg HS (8%bv : bv 5) Q8.
change (ew (d_env cx E V1) 538) with (ew (d_env cx E V1) (AT_X + 7)) in Q8.
rewrite HV1, e0_x in Q8 by lia. change (nth 7 (tl all_regs) 0%bv) with (8%bv : bv 5) in Q8.
prreg HS (18%bv : bv 5) Q18.
change (ew (d_env cx E V1) 548) with (ew (d_env cx E V1) (AT_X + 17)) in Q18.
rewrite HV1, e0_x in Q18 by lia. change (nth 17 (tl all_regs) 0%bv) with (18%bv : bv 5) in Q18.
prreg HS (20%bv : bv 5) Q20.
change (ew (d_env cx E V1) 550) with (ew (d_env cx E V1) (AT_X + 19)) in Q20.
rewrite HV1, e0_x in Q20 by lia. change (nth 19 (tl all_regs) 0%bv) with (20%bv : bv 5) in Q20.
prreg HS (25%bv : bv 5) Q25.
change (ew (d_env cx E V1) 555) with (ew (d_env cx E V1) (AT_X + 24)) in Q25.
rewrite HV1, e0_x in Q25 by lia. change (nth 24 (tl all_regs) 0%bv) with (25%bv : bv 5) in Q25.
prreg HS (26%bv : bv 5) Q26.
change (ew (d_env cx E V1) 556) with (ew (d_env cx E V1) (AT_X + 25)) in Q26.
rewrite HV1, e0_x in Q26 by lia. change (nth 25 (tl all_regs) 0%bv) with (26%bv : bv 5) in Q26.
prreg HS (19%bv : bv 5) Q19. rewrite ESH529 in Q19.
rewrite EF516 in Q10. unfold w64 in Q10. rewrite unsigned_lit_small in Q10 by lia.
rewrite EA60n in Q9. rewrite E562 in Q21b.
pose proof (st_ok_region_nth (d_env cx E V1) _ _ 3%nat _ HS ltac:(vm_compute; reflexivity)) as R529.
cbn [ms_mem restrict] in R529.
lazymatch type of R529 with region_ok _ _ _ ?r =>
  pose proof (sh_region_bytes SEGS (d_env cx E V1) (rd W (ms_mem ms0)) dsh_ser2 r ltac:(vm_compute; reflexivity) R529) as SHB end.
cbn [YP09.r_base base_val] in SHB. rewrite U529 in SHB.
assert (SH0 : forall z, 0 <= z < 384 -> aview SEGS (w_H W) (ms_mem ms0) (shadow_addr (d_FB cx) + z) = Some (dsh_ser2 z)).
{ intros z Hz. destruct (SHB z ltac:(unfold DFRAME_SH; lia)) as (Hr & Hm). exact (e0_aview_byte _ _ _ _ Hm Hr). }
assert (PRS0 : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Ha. apply (apresent_grows _ _ _ _ HGc). apply (apresent_grows _ _ _ _ HGa). exact Ha. }
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hna. rewrite (e0_frame_aview _ _ (w_H W) (ms_mem ms) (ms_mem ms0) a HFrc (KW1 a Ha Hna) Ha).
  exact (e0_frame_aview _ _ (w_H W) mem3 (ms_mem ms) a HFra (KW1 a Ha Hna) Ha). }
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA DS___asan_memset) (AMEMSET fq) W (ms_regs ms0) (ms_mem ms0)
    LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k
    (d_FB cx + 1664) 0 32 (d_A cx - d_S cx) _ HJ).
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Q2. fold (spZ regs). rewrite Rsp. lia.
  - rewrite EQA, EQS. replace (qa * 32 - qs * 16) with ((2 * qa - qs) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - rewrite Q3. exact Rgp.
  - rewrite Q4. exact Rtp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros aa Haa. split; [exact (proj1 (HAWRF aa ltac:(unfold DFRAME_SIZE; lia)))|].
    unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
    destruct GFapp as (Hg1 & [Hg2 | (Hg2 & Hg3)]); [left | right]; lia.
  - intros xx Hxx. exists 0. split; [|left; reflexivity].
    change (shadow_of_addr SHADOW_OFF xx) with (shadow_addr xx).
    replace xx with (d_FB cx + (xx - d_FB cx)) by lia. rewrite SHA by lia.
    assert (Hz1 : 208 <= (xx - d_FB cx) / 8) by (apply Z.div_le_lower_bound; lia).
    assert (Hz2 : (xx - d_FB cx) / 8 < 212) by (apply Z.div_lt_upper_bound; lia).
    rewrite SH0 by lia. rewrite e0_dsh2_used by lia. reflexivity.
  - intros _. intros s Hs. apply (e0_vis SEGS). apply PRS0.
    replace (d_FB cx + 1664 + 32 - 1) with (d_FB cx + 1695) in Hs by lia.
    rewrite !SHA in Hs by lia. change (1664 / 8) with 208 in Hs. change (1695 / 8) with 211 in Hs.
    pose proof (Z.mul_succ_div_gt (shadow_addr (d_FB cx) + 208) 8 ltac:(lia)) as M1.
    pose proof (Z.mul_div_le (shadow_addr (d_FB cx) + 211) 8 ltac:(lia)) as M2.
    replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
    apply GFsh. lia.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & HSET & HKEEP & HPRES & HMAT).

assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (d_A cx - 4096 <= a < d_A cx) -> ~ (d_FB cx + 1664 <= a < d_FB cx + 1696) ->
  ~ (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha H1 H2 H3.
  rewrite (HKEEP a Ha ltac:(intros Hc; apply H2; lia) ltac:(unfold ESTACK; lia)). exact (KEEP0 a Ha H3). }
assert (PRS2 : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem2 a)
  by (intros a Ha; apply HPRES; apply PRS0; exact Ha).
assert (SH2 : forall z, 0 <= z < 384 -> aview SEGS (w_H W) mem2 (shadow_addr (d_FB cx) + z) = Some (dsh_ser2 z)).
{ intros z Hz. rewrite (HKEEP (shadow_addr (d_FB cx) + z) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)).
  exact (SH0 z Hz). }
assert (ES2 : bv_unsigned (ew E AT_STK) = d_S cx)
  by (change AT_STK with 2%nat; rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (EA60 : bv_unsigned (ew E AT_A) = d_A cx) by (rewrite E60; unfold w64; apply unsigned_lit_small; lia).
assert (EA516 : bv_unsigned (ew E AT_F) = d_FB cx) by (rewrite EF; unfold w64; apply unsigned_lit_small; lia).
assert (EA529 : bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx))
  by (rewrite ESH; unfold w64; apply unsigned_lit_small; lia).
pose proof (Forall_inv HREG) as RG2. pose proof (Forall_inv_tail HREG) as HREGt.
pose proof (Forall_inv HREGt) as RG60. pose proof (Forall_inv_tail HREGt) as HREGt2.
pose proof (Forall_inv HREGt2) as RG516.
assert (HREG2 : Forall (region_ok SEGS E (rd W mem2)) (d_regions cx dsh_ser2)).
{ unfold d_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons]].
    + apply (e0_rok E (rd W mem3) (rd W mem2) AT_STK (d_S cx) _ _ _ _ _ (-104) 0 RG2 ES2);
        [ intros a Ha; apply e0_mbyte_kept; apply KEEP2; lia
        | intros o Ho; lia
        | vm_compute; reflexivity ].
    + apply (e0_rok E (rd W mem3) (rd W mem2) AT_A (d_A cx) _ _ _ _ _ 16 424 RG60 EA60);
        [ intros a Ha; apply e0_mbyte_kept; apply KEEP2; lia
        | intros o Ho; apply (apresent_writable SEGS); apply PRS2; apply GSTK; unfold LLVMF_STK; lia
        | vm_compute; reflexivity ].
    + apply (e0_rok E (rd W mem3) (rd W mem2) AT_F (d_FB cx) _ _ _ _ _ 0 24 RG516 EA516);
        [ intros a Ha; apply e0_mbyte_kept; apply KEEP2; lia
        | intros o Ho; apply (apresent_writable SEGS); apply PRS2; apply GFpres; unfold DFRAME_SIZE in Ho; lia
        | vm_compute; reflexivity ].
    + apply Forall_cons; [|apply Forall_nil]. unfold fshadow_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EA529.
      change (fs_frame_bytes DFRAME_CLASS / 8) with 512.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply PRS2. apply GFsh. unfold DFRAME_SH in Ho. lia.
      * apply dsh_chunks_ok. intros kk Hkk. apply e0_mbyte_of_aview. apply SH2. unfold DFRAME_SH in Hkk. lia. }
assert (HFLAG2 : rdword (aview SEGS (w_H W) mem2) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
  Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))).
{ apply (e0_rdword_ext (w_H W) mem3 mem2); [|exact HFLAG].
  intros x Hx. apply KEEP2; change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hx; lia. }
assert (H216b : val_mem SEGS (rd W mem2) (d_A cx + 216) 8 h).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem2); [|exact H216].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KEEP2; lia. }
assert (H152b : val_mem SEGS (rd W mem2) (d_A cx + 152) 8 (h + 440)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem2); [|exact H152].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KEEP2; lia. }
assert (HSHD2 : d_shadow cx dsh_ser2 W mem2) by (intros kk Hkk; apply SH2; unfold DFRAME_SH in Hkk; lia).
assert (V344 : val_mem SEGS (rd W mem2) (d_A cx + 344) 8 now).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem2); [|exact H344].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KEEP2; lia. }
assert (P9 : getr regs2 9 = w64 (d_A cx))
  by (transitivity (getr (ms_regs ms0) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact Q9]).
assert (P21 : getr regs2 21 = Z_to_bv 64 count)
  by (transitivity (getr (ms_regs ms0) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact Q21b]).
assert (P2 : getr regs2 2 = getr regs 2)
  by (transitivity (getr (ms_regs ms0) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact Q2]).
assert (P3 : getr regs2 3 = getr regs 3)
  by (transitivity (getr (ms_regs ms0) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact Q3]).
assert (P4 : getr regs2 4 = getr regs 4)
  by (transitivity (getr (ms_regs ms0) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact Q4]).
assert (P8 : getr regs2 8 = getr regs 8)
  by (transitivity (getr (ms_regs ms0) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact Q8]).
assert (P18 : getr regs2 18 = getr regs 18)
  by (transitivity (getr (ms_regs ms0) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact Q18]).
assert (P20 : getr regs2 20 = getr regs 20)
  by (transitivity (getr (ms_regs ms0) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact Q20]).
assert (P25 : getr regs2 25 = getr regs 25)
  by (transitivity (getr (ms_regs ms0) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact Q25]).
assert (P26 : getr regs2 26 = getr regs 26)
  by (transitivity (getr (ms_regs ms0) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact Q26]).
assert (P19 : getr regs2 19 = w64 (shadow_addr (d_FB cx)))
  by (transitivity (getr (ms_regs ms0) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact Q19]).
remember (map (getr regs2) (tl all_regs) ++ [Z_to_bv 64 count; Z_to_bv 64 now]) as V3 eqn:HV3.
pose proof (d_E_env cx E V3 HE) as HE3.
pose proof HE3 as (_ & _ & HEI3 & E60'' & EF'' & ESH'').
assert (U60b : bv_unsigned (ew (d_env cx E V3) 60) = d_A cx).
{ rewrite (E60'' : ew (d_env cx E V3) 60 = w64 (d_A cx)). unfold w64. apply unsigned_lit_small. lia. }
assert (U516b : bv_unsigned (ew (d_env cx E V3) 516) = d_FB cx).
{ rewrite (EF'' : ew (d_env cx E V3) 516 = w64 (d_FB cx)). unfold w64. apply unsigned_lit_small. lia. }
assert (U529b : bv_unsigned (ew (d_env cx E V3) 529) = shadow_addr (d_FB cx)).
{ rewrite (ESH'' : ew (d_env cx E V3) 529 = w64 (shadow_addr (d_FB cx))). unfold w64. apply unsigned_lit_small. lia. }
assert (E562b : ew (d_env cx E V3) 562 = Z_to_bv 64 count) by (rewrite HV3; apply e0_c).
assert (E563b : ew (d_env cx E V3) 563 = Z_to_bv 64 now) by (rewrite HV3; apply e0_d).
assert (HCTX2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem2 md2 k) by exact (conj HBASE (conj HJ2 HFR)).
assert (Hregs3 : regs_ok (d_env cx E V3) e0_sr3 regs2)
  by (rewrite HV3; apply (e0_regs_ok3 cx E regs2); [exact P9 | exact P21 | exact E60 | lia]).
assert (HG3 : facts_ok (d_env cx E V3) e0_G).
{ apply (DFACTS LAWS cx ly3 S3 W mem2 md2 k E V3 [(562%nat, mkAF 0 8 0)] [] HCTX2 HE); [|exact I].
  cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E562b, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (Hacs3 : Forall (YP09.chunk_ok SEGS (d_env cx E V3) (rd W mem2) (d_A cx)) e0_acs3).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 344 8%N (SOff 563 0) now).
  - cbn [sv_denot]. rewrite E563b, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact V344. }
pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs2 mem2 md2 k E 7500 e0_sr3 V3 e0_acs3 [] [] e0_G
  HCTX2 HE HREG2 HFLAG2 Hregs3 HG3 Hacs3 (Forall_nil _)
  (Forall_nil _) I (Forall_nil _) e0_kwf3) as HT0.
pose proof (st_ok_pi_submem _ _ _ e0_rs3 HT0 e0_submem3 e0_wf3) as HT.
clear HT0. cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HT.

assert (UA3 : bv_unsigned (ew (d_env cx E V3) AT_A) = d_A cx) by exact U60b.
assert (HAWR3 : forall bl0 blc, awr_ok (d_env cx E V3) e0_rs3 LLVMF_STK (d_S cx) [] bl0 blc ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ intros bl0 blc. apply (e0_awr3 _ _ _ _ _ _ _ _ (d_A cx)); [exact UA3 | unfold LLVMF_STK; lia | lia]. }
assert (KW3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 336 <= a < d_A cx + 376) ->
  ~ in_wrange (d_env cx E V3) e0_rs3 a).
{ intros a Ha Hna Hw. apply e0_inw3 in Hw.
  change (base_val (d_env cx E V3) (Some AT_A)) with (bv_unsigned (ew (d_env cx E V3) AT_A)) in Hw.
  rewrite UA3 in Hw. lia. }
assert (POSTB : forall (msF : machine_state) (matF : list word) (ssF : sstate),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E V3) ssF (restrict (w_H W) msF) ->
  ss_pc ssF = PH_OFF -> ss_resv ssF = None -> d_land_chk dsh_ser2 (ss_mem ssF) = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem msF) (with_vm_backing (m_vm_lazy md2) matF md2) k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 336 <= a < d_A cx + 376) ->
     aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msF) a) ->
  d_rL B cx (ms_regs msF) -> getr (ms_regs msF) 26 = w64 buf -> getr (ms_regs msF) 22 = w64 (d_obj cx OT) ->
  val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 336) 8 count ->
  val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 368) 8 0 ->
  val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 344) 8 now ->
  0 < count ->
  SRr SEGS W (mkCfg msF (with_vm_backing (m_vm_lazy md2) matF md2))
    (fun W' c' => r14_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c' \/
       f_ph B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 0 W' c')).
{ intros msF matF ssF HSF HpcF HrvF HchkF HJF HFrF HGF HrLF R26F R22F V336F V368F V344F Hcpos.
  pose proof HFrF as KEEPF.
  assert (KALL : forall a, 0 <= a < 2 ^ 64 ->
    ~ (d_A cx - 4096 <= a < d_A cx + 376) -> ~ (d_FB cx + 1664 <= a < d_FB cx + 1696) ->
    ~ (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) ->
    aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha H1 H2 H3. rewrite (KEEPF a Ha ltac:(lia)). apply KEEP2; [exact Ha | lia | exact H2 | exact H3]. }
  assert (PRESF : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem msF) a)
    by (intros a Ha; apply HGF; apply PRS2; exact Ha).
  assert (H216F : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 216) 8 h).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem2 (ms_mem msF)); [|exact H216b].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KEEPF; lia. }
  assert (H152F : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 152) 8 (h + 440)).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem2 (ms_mem msF)); [|exact H152b].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KEEPF; lia. }
  assert (HCTXF : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msF)
    (with_vm_backing (m_vm_lazy md2) matF md2) k) by exact (conj HBASE (conj HJF HFR)).
  pose proof (DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W (with_vm_backing (m_vm_lazy md2) matF md2) k
    (d_env cx E V3) ssF msF HCTXF HE3 (d_env_fl cx E V3) HSF HchkF H216F H152F) as (HFRMF & HSHDF).
  assert (HBODYF : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W (ms_mem msF)).
  { apply (d_body_rt B cx h n n (a3_xb buf op) dsh_ser dsh_ser2 ly3 S3 W mem3 (ms_mem msF)
      (d_A cx - 4096) (d_A cx + 376)
      (fun a => (d_A cx - 4096 <= a < d_A cx + 376) \/ (d_FB cx + 1664 <= a < d_FB cx + 1696) \/
                (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212)) HBODY).
    - unfold LLVMF_STK. lia.
    - lia.
    - intros a [Ha | Ha]; [left; exact Ha | right; apply NOTRD; exact Ha].
    - intros a Ha Hna. apply KALL; [exact Ha | intros Hc; apply Hna; left; exact Hc
        | intros Hc; apply Hna; right; left; exact Hc | intros Hc; apply Hna; right; right; exact Hc].
    - intros a _ Ha. exact (PRESF a Ha).
    - exact HFRMF.
    - exact HSHDF.
    - lia. }
  assert (KG : forall a l (Lz : Z), Z.of_nat (length l) = Lz -> 0 <= a -> a + Lz <= 2 ^ 64 ->
    (a + Lz <= d_A cx - 4096 \/ d_A cx + 376 <= a) ->
    (a + Lz <= d_FB cx + 1664 \/ d_FB cx + 1696 <= a) ->
    (a + Lz <= shadow_addr (d_FB cx) + 208 \/ shadow_addr (d_FB cx) + 212 <= a) ->
    garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem msF)) a l).
  { intros a l Lz HL H0 H1 H2 H3 H4 Hg. apply (e0_garr8_keep (w_H W) mem3 (ms_mem msF)); [|exact Hg].
    intros x Hx. rewrite HL in Hx. apply KALL; lia. }
  assert (KV : forall a v, 0 <= a -> a + 8 <= d_A cx + 336 -> d_A cx <= a ->
    val_mem SEGS (rd W mem3) a 8 v -> val_mem SEGS (rd W (ms_mem msF)) a 8 v).
  { intros a v H0 H1 H2 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem msF)); [|exact Hv].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
    rewrite (KEEPF (a + kk) ltac:(lia) ltac:(lia)). apply KEEP2; lia. }
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HSF HrvF). rewrite HpcF.
  apply SRr_ret. right.
  unfold f_ph, a3f_st. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy md2) matF md2), k, acc.
  split; [reflexivity|]. split; [assumption|]. split; [exact HBASE|]. split; [exact HJF|]. split; [exact HFR|]. split; [exact Hk|].
  split; [pose proof HJF as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
  split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split; [exact HrLF|].
  split; [cbv beta; split; [exact R26F | exact R22F]|].
  split.
  { cbv beta. split; [split; [split|split]|].
    - apply KV; [lia | lia | lia | exact H232].
    - exact V344F.
    - apply KV; [lia | lia | lia | exact H224].
    - apply KV; [lia | lia | lia | exact H248].
    - split; [split; [exact (proj1 HTAB)|]|].
      + refine (KG _ _ 400 ltac:(rewrite length_map, HLT1; reflexivity) _ _ _ _ _ HGT);
          unfold d_obj, dobj_off; lia.
      + split; [split; [exact Hr2|]|].
        * refine (KG _ _ (a3_r T1 now + 1) Lb _ _ _ _ _ HGB);
            unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp; lia.
        * split; [exact HJR|]. split; [exact HVP|]. split.
          -- refine (KG _ _ (Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)))
               ltac:(rewrite length_map; reflexivity) _ _ _ _ _ HOO); unfold d_obj, dobj_off; lia.
          -- split.
             ++ split; [lia|]. split; [exact V368F | exact V336F].
             ++ rewrite e0_used0. apply (e0_zero_garr8 (w_H W) (ms_mem msF)).
                ** intros x Hx. rewrite repeat_length in Hx.
                   rewrite (KEEPF (d_obj cx OUSED + x) ltac:(unfold d_obj, dobj_off; lia)
                     ltac:(unfold d_obj, dobj_off; lia)).
                   replace (d_obj cx OUSED + x) with (d_FB cx + 1664 + x) by (unfold d_obj, dobj_off; lia).
                   rewrite (HSET x ltac:(lia)). reflexivity.
                ** intros j Hj. rewrite repeat_length in Hj. apply e0_rep_nth. exact Hj. }
  split; [split; [apply KV; [lia | lia | lia | exact H232] | exact V344F]|].
  exact HBODYF. }

assert (POSTA : forall (msF : machine_state) (matF : list word) (ssF : sstate),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E V3) ssF (restrict (w_H W) msF) ->
  ss_pc ssF = R14_OFF -> ss_resv ssF = None -> d_land_chk dsh_ser2 (ss_mem ssF) = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem msF) (with_vm_backing (m_vm_lazy md2) matF md2) k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 336 <= a < d_A cx + 376) ->
     aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msF) a) ->
  d_rL B cx (ms_regs msF) -> getr (ms_regs msF) 26 = w64 buf ->
  getr (ms_regs msF) 10 = w64 (shadow_addr (d_FB cx)) ->
  val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 344) 8 now ->
  SRr SEGS W (mkCfg msF (with_vm_backing (m_vm_lazy md2) matF md2))
    (fun W' c' => r14_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf W' c' \/
       f_ph B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 0 W' c')).
{ intros msF matF ssF HSF HpcF HrvF HchkF HJF HFrF HGF HrLF R26F R10F V344F.
  pose proof HFrF as KEEPF.
  assert (KALL : forall a, 0 <= a < 2 ^ 64 ->
    ~ (d_A cx - 4096 <= a < d_A cx + 376) -> ~ (d_FB cx + 1664 <= a < d_FB cx + 1696) ->
    ~ (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212) ->
    aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha H1 H2 H3. rewrite (KEEPF a Ha ltac:(lia)). apply KEEP2; [exact Ha | lia | exact H2 | exact H3]. }
  assert (PRESF : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem msF) a)
    by (intros a Ha; apply HGF; apply PRS2; exact Ha).
  assert (H216F : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 216) 8 h).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem2 (ms_mem msF)); [|exact H216b].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KEEPF; lia. }
  assert (H152F : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 152) 8 (h + 440)).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem2 (ms_mem msF)); [|exact H152b].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KEEPF; lia. }
  assert (HCTXF : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msF)
    (with_vm_backing (m_vm_lazy md2) matF md2) k) by exact (conj HBASE (conj HJF HFR)).
  pose proof (DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W (with_vm_backing (m_vm_lazy md2) matF md2) k
    (d_env cx E V3) ssF msF HCTXF HE3 (d_env_fl cx E V3) HSF HchkF H216F H152F) as (HFRMF & HSHDF).
  assert (HBODYF : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W (ms_mem msF)).
  { apply (d_body_rt B cx h n n (a3_xb buf op) dsh_ser dsh_ser2 ly3 S3 W mem3 (ms_mem msF)
      (d_A cx - 4096) (d_A cx + 376)
      (fun a => (d_A cx - 4096 <= a < d_A cx + 376) \/ (d_FB cx + 1664 <= a < d_FB cx + 1696) \/
                (shadow_addr (d_FB cx) + 208 <= a < shadow_addr (d_FB cx) + 212)) HBODY).
    - unfold LLVMF_STK. lia.
    - lia.
    - intros a [Ha | Ha]; [left; exact Ha | right; apply NOTRD; exact Ha].
    - intros a Ha Hna. apply KALL; [exact Ha | intros Hc; apply Hna; left; exact Hc
        | intros Hc; apply Hna; right; left; exact Hc | intros Hc; apply Hna; right; right; exact Hc].
    - intros a _ Ha. exact (PRESF a Ha).
    - exact HFRMF.
    - exact HSHDF.
    - lia. }
  assert (KV : forall a v, 0 <= a -> a + 8 <= d_A cx + 336 -> d_A cx <= a ->
    val_mem SEGS (rd W mem3) a 8 v -> val_mem SEGS (rd W (ms_mem msF)) a 8 v).
  { intros a v H0 H1 H2 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem msF)); [|exact Hv].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
    rewrite (KEEPF (a + kk) ltac:(lia) ltac:(lia)). apply KEEP2; lia. }
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HSF HrvF). rewrite HpcF.
  apply SRr_ret. left.
  unfold r14_in. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy md2) matF md2), k, acc.
  split; [reflexivity|]. split; [assumption|]. split; [exact HBASE|]. split; [exact HJF|]. split; [exact HFR|]. split; [exact Hk|].
  split; [pose proof HJF as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
  split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split; [exact HrLF|].
  split; [cbv beta; split; [exact R10F | exact R26F]|].
  split.
  { cbv beta. split.
    - split; [split; [apply KV; [lia | lia | lia | exact H232] | exact V344F]|].
      split; [apply KV; [lia | lia | lia | exact H224] | apply KV; [lia | lia | lia | exact H248]].
    - split; [exact (proj1 HTAB)|].
      refine (e0_garr8_keep (w_H W) mem3 (ms_mem msF) _ _ _ HGT).
      intros x Hx. rewrite length_map, HLT1 in Hx. change (Z.of_nat 400) with 400 in Hx.
      apply KALL; unfold d_obj, dobj_off in *; lia. }
  split; [split; [apply KV; [lia | lia | lia | exact H232] | exact V344F]|].
  exact HBODYF. }

assert (FK : forall (rs : smem) (ma mb : word -> option byte),
  frame_of (d_env cx E V3) rs (rd W ma) (rd W mb) ->
  (forall a, in_wrange (d_env cx E V3) rs a -> d_A cx + 336 <= a < d_A cx + 376) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 336 <= a < d_A cx + 376) ->
  aview SEGS (w_H W) mb a = aview SEGS (w_H W) ma a).
{ intros rs ma mb HFx Hinw a Ha Hna. apply (e0_frame_aview _ rs (w_H W) ma mb a HFx); [|exact Ha].
  intros Hw. exact (Hna (Hinw a Hw)). }
assert (INW : forall a, in_wrange (d_env cx E V3) e0_rs3 a -> d_A cx + 336 <= a < d_A cx + 376).
{ intros a Hw. apply e0_inw3 in Hw.
  change (base_val (d_env cx E V3) (Some AT_A)) with (bv_unsigned (ew (d_env cx E V3) AT_A)) in Hw.
  rewrite UA3 in Hw. exact Hw. }
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at, w64.
paj_run_to_shc RUNTOP HT HJ2 PH_OFF.
{ apply HAWR3. }
rename HF into HFb. rename HFr into HFrb. rename HG into HGb.
psrr_branch_pi RUNP BR HT.

{ assert (Hc0 : count = 0) by (apply (proj1 (e0_beq0 (d_env cx E V3) 562 count E562b ltac:(lia))); exact Hc).
  paj_run_to_shc RUNTOP HT HJ2 R14_OFF.
  { apply HAWR3. }
  prreg HT (2%bv : bv 5) q2.
  change (ew (d_env cx E V3) 532) with (ew (d_env cx E V3) (AT_X + 1)) in q2.
  rewrite HV3, e0_x in q2 by lia. change (nth 1 (tl all_regs) 0%bv) with (2%bv : bv 5) in q2.
  rewrite P2 in q2.
  prreg HT (3%bv : bv 5) q3.
  change (ew (d_env cx E V3) 533) with (ew (d_env cx E V3) (AT_X + 2)) in q3.
  rewrite HV3, e0_x in q3 by lia. change (nth 2 (tl all_regs) 0%bv) with (3%bv : bv 5) in q3.
  rewrite P3 in q3.
  prreg HT (4%bv : bv 5) q4.
  change (ew (d_env cx E V3) 534) with (ew (d_env cx E V3) (AT_X + 3)) in q4.
  rewrite HV3, e0_x in q4 by lia. change (nth 3 (tl all_regs) 0%bv) with (4%bv : bv 5) in q4.
  rewrite P4 in q4.
  prreg HT (8%bv : bv 5) q8.
  change (ew (d_env cx E V3) 538) with (ew (d_env cx E V3) (AT_X + 7)) in q8.
  rewrite HV3, e0_x in q8 by lia. change (nth 7 (tl all_regs) 0%bv) with (8%bv : bv 5) in q8.
  rewrite P8 in q8.
  prreg HT (18%bv : bv 5) q18.
  change (ew (d_env cx E V3) 548) with (ew (d_env cx E V3) (AT_X + 17)) in q18.
  rewrite HV3, e0_x in q18 by lia. change (nth 17 (tl all_regs) 0%bv) with (18%bv : bv 5) in q18.
  rewrite P18 in q18.
  prreg HT (20%bv : bv 5) q20.
  change (ew (d_env cx E V3) 550) with (ew (d_env cx E V3) (AT_X + 19)) in q20.
  rewrite HV3, e0_x in q20 by lia. change (nth 19 (tl all_regs) 0%bv) with (20%bv : bv 5) in q20.
  rewrite P20 in q20.
  prreg HT (25%bv : bv 5) q25.
  change (ew (d_env cx E V3) 555) with (ew (d_env cx E V3) (AT_X + 24)) in q25.
  rewrite HV3, e0_x in q25 by lia. change (nth 24 (tl all_regs) 0%bv) with (25%bv : bv 5) in q25.
  rewrite P25 in q25.
  prreg HT (26%bv : bv 5) q26.
  change (ew (d_env cx E V3) 556) with (ew (d_env cx E V3) (AT_X + 25)) in q26.
  rewrite HV3, e0_x in q26 by lia. change (nth 25 (tl all_regs) 0%bv) with (26%bv : bv 5) in q26.
  rewrite P26 in q26.
  prreg HT (9%bv : bv 5) q9.
  rewrite (E60'' : ew (d_env cx E V3) 60 = w64 (d_A cx)) in q9.
  assert (RL : d_rL B cx (ms_regs ms2)) by (apply (e0_rl_of B cx regs); assumption).
  prreg HT (10%bv : bv 5) q10.
  change (ew (d_env cx E V3) 549) with (ew (d_env cx E V3) (AT_X + 18)) in q10.
  rewrite HV3, e0_x in q10 by lia. change (nth 18 (tl all_regs) 0%bv) with (19%bv : bv 5) in q10.
  rewrite P19 in q10.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HT ltac:(vm_compute; reflexivity)) as RA.
  cbn [ms_mem restrict] in RA.
  pose proof (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ 344 8%N (SOff 563 0) now RA UA3
    ltac:(apply (nth_error_In _ 29%nat); vm_compute; reflexivity)
    ltac:(rewrite (e0_soff (d_env cx E V3) 563 0 now ltac:(rewrite E563b; apply unsigned_lit_small; lia)); f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V344F.
  apply (POSTA ms2 mat2 _ HT eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ2).
  - intros a Ha Hna.
    rewrite (FK _ (ms_mem ms1) (ms_mem ms2) HFr ltac:(intros aa Hw; apply INW; exact Hw) a Ha Hna).
    exact (FK _ mem2 (ms_mem ms1) HFrb ltac:(intros aa Hw; apply INW; exact Hw) a Ha Hna).
  - intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HGb). exact Ha.
  - exact RL.
  - rewrite q26. exact R26.
  - exact q10.
  - exact V344F. }

{ assert (Hc0 : count <> 0).
  { intros Hz. pose proof (proj2 (e0_beq0 (d_env cx E V3) 562 count E562b ltac:(lia)) Hz) as Ht.
    rewrite Ht in Hc. discriminate Hc. }
  paj_run_to_shc RUNTOP HT HJ2 PH_OFF.
  { apply HAWR3. }
  rename HF into HFd. rename HFr into HFrd. rename HG into HGd.
  clear Hc.
  psrr_branch_pi RUNP BR HT.
  { assert (Hlt : count < 8) by (apply (proj1 (e0_bltu (d_env cx E V3) 562 count 8 E562b ltac:(lia) ltac:(lia))); exact Hc).
  paj_run_to_shc RUNTOP HT HJ2 PH_OFF.
    { apply HAWR3. }
    prreg HT (2%bv : bv 5) q2.
    change (ew (d_env cx E V3) 532) with (ew (d_env cx E V3) (AT_X + 1)) in q2.
    rewrite HV3, e0_x in q2 by lia. change (nth 1 (tl all_regs) 0%bv) with (2%bv : bv 5) in q2.
    rewrite P2 in q2.
    prreg HT (3%bv : bv 5) q3.
    change (ew (d_env cx E V3) 533) with (ew (d_env cx E V3) (AT_X + 2)) in q3.
    rewrite HV3, e0_x in q3 by lia. change (nth 2 (tl all_regs) 0%bv) with (3%bv : bv 5) in q3.
    rewrite P3 in q3.
    prreg HT (4%bv : bv 5) q4.
    change (ew (d_env cx E V3) 534) with (ew (d_env cx E V3) (AT_X + 3)) in q4.
    rewrite HV3, e0_x in q4 by lia. change (nth 3 (tl all_regs) 0%bv) with (4%bv : bv 5) in q4.
    rewrite P4 in q4.
    prreg HT (8%bv : bv 5) q8.
    change (ew (d_env cx E V3) 538) with (ew (d_env cx E V3) (AT_X + 7)) in q8.
    rewrite HV3, e0_x in q8 by lia. change (nth 7 (tl all_regs) 0%bv) with (8%bv : bv 5) in q8.
    rewrite P8 in q8.
    prreg HT (18%bv : bv 5) q18.
    change (ew (d_env cx E V3) 548) with (ew (d_env cx E V3) (AT_X + 17)) in q18.
    rewrite HV3, e0_x in q18 by lia. change (nth 17 (tl all_regs) 0%bv) with (18%bv : bv 5) in q18.
    rewrite P18 in q18.
    prreg HT (20%bv : bv 5) q20.
    change (ew (d_env cx E V3) 550) with (ew (d_env cx E V3) (AT_X + 19)) in q20.
    rewrite HV3, e0_x in q20 by lia. change (nth 19 (tl all_regs) 0%bv) with (20%bv : bv 5) in q20.
    rewrite P20 in q20.
    prreg HT (25%bv : bv 5) q25.
    change (ew (d_env cx E V3) 555) with (ew (d_env cx E V3) (AT_X + 24)) in q25.
    rewrite HV3, e0_x in q25 by lia. change (nth 24 (tl all_regs) 0%bv) with (25%bv : bv 5) in q25.
    rewrite P25 in q25.
    prreg HT (26%bv : bv 5) q26.
    change (ew (d_env cx E V3) 556) with (ew (d_env cx E V3) (AT_X + 25)) in q26.
    rewrite HV3, e0_x in q26 by lia. change (nth 25 (tl all_regs) 0%bv) with (26%bv : bv 5) in q26.
    rewrite P26 in q26.
    prreg HT (9%bv : bv 5) q9.
    rewrite (E60'' : ew (d_env cx E V3) 60 = w64 (d_A cx)) in q9.
    assert (RL : d_rL B cx (ms_regs ms3)) by (apply (e0_rl_of B cx regs); assumption).
    prreg HT (22%bv : bv 5) q22.
    rewrite U516b in q22.
    pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HT ltac:(vm_compute; reflexivity)) as RA.
    cbn [ms_mem restrict] in RA.
    pose proof (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ 344 8%N (SOff 563 0) now RA UA3
      ltac:(apply (nth_error_In _ 31%nat); vm_compute; reflexivity)
      ltac:(rewrite (e0_soff (d_env cx E V3) 563 0 now ltac:(rewrite E563b; apply unsigned_lit_small; lia)); f_equal; lia)
      ltac:(cbn; lia) ltac:(cbn; lia)) as V344F.
    pose proof (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ 368 8%N (SLit 0) 0 RA UA3
      ltac:(apply (nth_error_In _ 1%nat); vm_compute; reflexivity) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)) as V368F.
    pose proof (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ 336 8%N (SOff 562 0) count RA UA3
      ltac:(apply (nth_error_In _ 0%nat); vm_compute; reflexivity)
      ltac:(rewrite (e0_soff (d_env cx E V3) 562 0 count ltac:(rewrite E562b; apply unsigned_lit_small; lia)); f_equal; lia)
      ltac:(cbn; lia) ltac:(cbn; lia)) as V336F.
    apply (POSTB ms3 mat3 _ HT eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ2).
    - intros a Ha Hna.
      rewrite (FK _ (ms_mem ms2) (ms_mem ms3) HFr ltac:(intros aa Hw; apply INW; exact Hw) a Ha Hna).
      rewrite (FK _ (ms_mem ms1) (ms_mem ms2) HFrd ltac:(intros aa Hw; apply INW; exact Hw) a Ha Hna).
      exact (FK _ mem2 (ms_mem ms1) HFrb ltac:(intros aa Hw; apply INW; exact Hw) a Ha Hna).
    - intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HGd).
      apply (apresent_grows _ _ _ _ HGb). exact Ha.
    - exact RL.
    - rewrite q26. exact R26.
    - rewrite q22. unfold w64, d_obj, dobj_off. first [reflexivity | f_equal; lia].
    - exact V336F.
    - exact V368F.
    - exact V344F.
    - lia. }

  { assert (Hc8e : count = 8).
    { assert (Hn8 : ~ count < 8).
      { intros Hl. pose proof (proj2 (e0_bltu (d_env cx E V3) 562 count 8 E562b ltac:(lia) ltac:(lia)) Hl) as Ht.
        rewrite Ht in Hc. discriminate Hc. }
      lia. }
  paj_run_to_shc RUNTOP HT HJ2 PH_OFF.
    { apply HAWR3. }
    prreg HT (2%bv : bv 5) q2.
    change (ew (d_env cx E V3) 532) with (ew (d_env cx E V3) (AT_X + 1)) in q2.
    rewrite HV3, e0_x in q2 by lia. change (nth 1 (tl all_regs) 0%bv) with (2%bv : bv 5) in q2.
    rewrite P2 in q2.
    prreg HT (3%bv : bv 5) q3.
    change (ew (d_env cx E V3) 533) with (ew (d_env cx E V3) (AT_X + 2)) in q3.
    rewrite HV3, e0_x in q3 by lia. change (nth 2 (tl all_regs) 0%bv) with (3%bv : bv 5) in q3.
    rewrite P3 in q3.
    prreg HT (4%bv : bv 5) q4.
    change (ew (d_env cx E V3) 534) with (ew (d_env cx E V3) (AT_X + 3)) in q4.
    rewrite HV3, e0_x in q4 by lia. change (nth 3 (tl all_regs) 0%bv) with (4%bv : bv 5) in q4.
    rewrite P4 in q4.
    prreg HT (8%bv : bv 5) q8.
    change (ew (d_env cx E V3) 538) with (ew (d_env cx E V3) (AT_X + 7)) in q8.
    rewrite HV3, e0_x in q8 by lia. change (nth 7 (tl all_regs) 0%bv) with (8%bv : bv 5) in q8.
    rewrite P8 in q8.
    prreg HT (18%bv : bv 5) q18.
    change (ew (d_env cx E V3) 548) with (ew (d_env cx E V3) (AT_X + 17)) in q18.
    rewrite HV3, e0_x in q18 by lia. change (nth 17 (tl all_regs) 0%bv) with (18%bv : bv 5) in q18.
    rewrite P18 in q18.
    prreg HT (20%bv : bv 5) q20.
    change (ew (d_env cx E V3) 550) with (ew (d_env cx E V3) (AT_X + 19)) in q20.
    rewrite HV3, e0_x in q20 by lia. change (nth 19 (tl all_regs) 0%bv) with (20%bv : bv 5) in q20.
    rewrite P20 in q20.
    prreg HT (25%bv : bv 5) q25.
    change (ew (d_env cx E V3) 555) with (ew (d_env cx E V3) (AT_X + 24)) in q25.
    rewrite HV3, e0_x in q25 by lia. change (nth 24 (tl all_regs) 0%bv) with (25%bv : bv 5) in q25.
    rewrite P25 in q25.
    prreg HT (26%bv : bv 5) q26.
    change (ew (d_env cx E V3) 556) with (ew (d_env cx E V3) (AT_X + 25)) in q26.
    rewrite HV3, e0_x in q26 by lia. change (nth 25 (tl all_regs) 0%bv) with (26%bv : bv 5) in q26.
    rewrite P26 in q26.
    prreg HT (9%bv : bv 5) q9.
    rewrite (E60'' : ew (d_env cx E V3) 60 = w64 (d_A cx)) in q9.
    assert (RL : d_rL B cx (ms_regs ms3)) by (apply (e0_rl_of B cx regs); assumption).
    prreg HT (22%bv : bv 5) q22.
    rewrite U516b in q22.
    pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HT ltac:(vm_compute; reflexivity)) as RA.
    cbn [ms_mem restrict] in RA.
    pose proof (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ 344 8%N (SOff 563 0) now RA UA3
      ltac:(apply (nth_error_In _ 31%nat); vm_compute; reflexivity)
      ltac:(rewrite (e0_soff (d_env cx E V3) 563 0 now ltac:(rewrite E563b; apply unsigned_lit_small; lia)); f_equal; lia)
      ltac:(cbn; lia) ltac:(cbn; lia)) as V344F.
    pose proof (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ 368 8%N (SLit 0) 0 RA UA3
      ltac:(apply (nth_error_In _ 1%nat); vm_compute; reflexivity) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)) as V368F.
    pose proof (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ 336 8%N (SLit 8) count RA UA3
      ltac:(apply (nth_error_In _ 0%nat); vm_compute; reflexivity)
      ltac:(rewrite Hc8e; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as V336F.
    apply (POSTB ms3 mat3 _ HT eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ2).
    - intros a Ha Hna.
      rewrite (FK _ (ms_mem ms2) (ms_mem ms3) HFr ltac:(intros aa Hw; apply INW; exact Hw) a Ha Hna).
      rewrite (FK _ (ms_mem ms1) (ms_mem ms2) HFrd ltac:(intros aa Hw; apply INW; exact Hw) a Ha Hna).
      exact (FK _ mem2 (ms_mem ms1) HFrb ltac:(intros aa Hw; apply INW; exact Hw) a Ha Hna).
    - intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HGd).
      apply (apresent_grows _ _ _ _ HGb). exact Ha.
    - exact RL.
    - rewrite q26. exact R26.
    - rewrite q22. unfold w64, d_obj, dobj_off. first [reflexivity | f_equal; lia].
    - exact V336F.
    - exact V368F.
    - exact V344F.
    - lia. }
}
Qed.
End h.
End f.
End d.
