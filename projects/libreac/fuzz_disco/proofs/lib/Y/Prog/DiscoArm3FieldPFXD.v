(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_push.v, with its module paths and module names changed; 616 of its 666 lines of code are new or changed and 1541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldMDA2.v, with its module names changed; 980 of its 1061 lines of code are new or changed and 585 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnShared SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFXKit DiscoArm3FieldCall.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel ReacDiscoTableAge DiscoArm3FieldPH.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_Pq slot_ser_P3 disco_box_name_model tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition PFXDR_OFF : Z := 0x2064.

Definition pfxd_acs (p : Z) : list YP09.chunk := [YP09.mkChunk 352 (CVal 8 (SOff 529 (271 + 6 * p)))].
Definition pfxd_fcs (p : Z) : list YP09.chunk :=
  [YP09.mkChunk (2173 + 48 * p) (CVal 1 (SOff 563 0)); YP09.mkChunk (2174 + 48 * p) (CVal 1 (SOff 564 0))].
Definition pfxd_fa : list (nat * afact) := [(563%nat, mkAF 0 255 0); (564%nat, mkAF 0 255 0)].
Definition pfxd_vals (regs : bvmap 5 word) (T : list byte) (p : Z) : list word :=
  a3f_vals regs ++ [Z_to_bv 64 (disco_table_c.din_of T p); Z_to_bv 64 (disco_table_c.dout_of T p)].
Definition pfxd_T (a b : Z) : list Z := disco_json_text.dec a ++ [120] ++ disco_json_text.dec b.
Definition pfxd_srB (p : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set (a3f_sr (-16)) (10%bv : bv 5) (SLit 0)) (21%bv : bv 5) (SOff 529 (271 + 6 * p)))
    (25%bv : bv 5) (SOff 516 (2174 + 48 * p))) (26%bv : bv 5) (SOff 516 (2173 + 48 * p)).
Definition pfxd_rsB (p : Z) : smem := map (fun r => set_window r 0 0) (d_kregions dsh_md (pfxd_acs p) (pfxd_fcs p)).
Definition pfxd_ssB (p : Z) : sstate := mkSS BNR_OFF (pfxd_srB p) (pfxd_rsB p) None (d_facts pfxd_fa []).
Definition pfxd_rsA : smem := map (fun r => set_window r 0 0) (d_kregions dsh_md [] []).
Definition pfxd_ssA : sstate :=
  mkSS BNR_OFF (sr_set (a3f_sr (-16)) (10%bv : bv 5) (SLit 18446744073709551615)) pfxd_rsA None (d_facts pfxd_fa []).
Definition pfxd_rsP : smem := [YP09.mkRegion (Some 9%nat) 240 248 0 0 [YP09.mkChunk 240 (CVal 8 (SOff 33 0))]].
Definition pfxd_finB (p : Z) : list sv :=
  [SLit 0; SOff A_TEXT 8292; SOff 60 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0; SOff 2 0;
   SOff 60 0; SOff 516 2000; SLit 24; SOff (A_OBJ 14) 0; SOff 563 0; SOff 564 0; SOff 546 0; SOff 547 0; SOff 548 0;
   SLit WS_MASK; SOff 32 0; SLit 32; SOff 529 (271 + 6 * p); SOff 553 0; SOff 554 0; SOff 555 0;
   SOff 516 (2174 + 48 * p); SOff 516 (2173 + 48 * p); SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0; SOff 562 0].
Definition pfxd_finA : list sv :=
  [SLit 0; SOff 532 0; SOff 60 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0; SOff 2 0;
   SOff 60 0; SLit 18446744073709551615; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0; SOff 546 0; SOff 547 0;
   SOff 548 0; SLit WS_MASK; SOff 32 0; SLit 32; SOff 552 0; SOff 553 0; SOff 554 0; SOff 555 0; SOff 556 0;
   SOff 557 0; SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0; SOff 562 0].

Ltac pfxd_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Ltac pfxd_emem HF :=
  apply functional_extensionality; let x := fresh "x" in intros x; apply HF;
  let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros (r & Hr & Hw);
  lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia|]); destruct Hr.

Lemma pfxd_sw : forall r, subregion (set_window r 0 0) r.
Proof.
  intros r. unfold subregion, set_window.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc; exact Hc.
Qed.

Lemma pfxd_narrow : forall (l x : smem), submem (map (fun r => set_window r 0 0) l) (l ++ x).
Proof.
  induction l as [|r l IH]; intros x; cbn [map app]; [apply submem_nil|].
  apply submem_keep; [apply pfxd_sw | apply IH].
Qed.

Lemma pfxd_subw : forall b lo hi wlo whi (cs cs' : list YP09.chunk),
  (forall c, In c cs' -> In c cs) ->
  subregion (set_window (YP09.mkRegion b lo hi wlo whi cs') 0 0) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi cs cs' Hc. unfold subregion, set_window.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. exact Hc.
Qed.

Lemma pfxd_narrowA : forall acs fcs,
  submem (map (fun r => set_window r 0 0) (d_kregions dsh_md [] [])) (d_kregions dsh_md acs fcs ++ []).
Proof.
  intros acs fcs. unfold d_kregions. cbn [map app].
  apply submem_keep; [apply pfxd_sw|].
  apply submem_keep.
  { apply pfxd_subw. intros c Hc. rewrite app_nil_r in Hc. apply in_or_app. left. exact Hc. }
  apply submem_keep.
  { apply pfxd_subw. intros c Hc. rewrite app_nil_r in Hc. apply in_or_app. left. exact Hc. }
  apply submem_keep; [apply pfxd_sw|]. apply submem_keep; [apply pfxd_sw|]. apply submem_keep; [apply pfxd_sw|].
  apply submem_nil.
Qed.

Lemma pfxd_kwf : forall p, 0 <= p < 8 ->
  regions_wf (d_kregions dsh_md (pfxd_acs p) (pfxd_fcs p) ++ []) = true.
Proof.
  intros p Hp. assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma pfxd_nwf : forall p, 0 <= p < 8 -> regions_wf (pfxd_rsB p) = true.
Proof.
  intros p Hp. assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma pfxd_awf : regions_wf pfxd_rsA = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pfxd_pwf : regions_wf pfxd_rsP = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pfxd_chunk_in : forall r c, In c (YP09.r_chunks r) -> region_wf r = true ->
  YP09.r_lo r <= YP09.c_off c /\ YP09.c_off c + c_len c <= YP09.r_hi r.
Proof.
  intros r c Hin Hwf. unfold region_wf in Hwf. apply andb_prop in Hwf as [_ Hcs].
  pose proof (proj1 (forallb_forall _ _) Hcs c Hin) as X. unfold chunk_inside in X.
  apply andb_prop in X as [X _]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

Lemma pfxd_rdword : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  assert (H0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma pfxd_text : forall a b, 0 <= a <= 40 -> 0 <= b <= 40 ->
  pf_text [Pd; PLit 120; Pd] [AInt a; AInt b] = Some (pfxd_T a b).
Proof.
  intros a b Ha Hb. unfold pfxd_T. cbn [pf_text option_map]. rewrite app_nil_r.
  rewrite (tj_lemmas.dec_pfdec a) by lia. rewrite (tj_lemmas.dec_pfdec b) by lia. reflexivity.
Qed.

Lemma pfxd_dec : forall v, 0 <= v <= 40 -> (length (disco_json_text.dec v) <= 2)%nat.
Proof.
  intros v Hv. destruct (disco_json_lemmas.dec_spec v) as (_ & _ & _ & L).
  { split; [lia|]. apply (Z.le_lt_trans _ 40); [lia | reflexivity]. }
  exact (L 2 ltac:(lia) ltac:(apply (Z.le_lt_trans _ 40); [lia | reflexivity])).
Qed.

Lemma pfxd_T_len : forall a b, 0 <= a <= 40 -> 0 <= b <= 40 -> (length (pfxd_T a b) <= 5)%nat.
Proof.
  intros a b Ha Hb. unfold pfxd_T. rewrite !length_app. cbn [length].
  pose proof (pfxd_dec a Ha). pose proof (pfxd_dec b Hb). lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {POV : PAObjVal lib_both3_0_listing (PI := PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pfxd_env_reg : forall (cx : dcx) (E : env) (regs : bvmap 5 word) (T : list byte) (p : Z) (r : bv 5) (a : nat),
  a = (AT_X + Z.to_nat (bv_unsigned r))%nat -> ew (d_env cx E (pfxd_vals regs T p)) a = getr regs r.
Proof.
  intros cx E regs T p r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold pfxd_vals.
  rewrite d_env_x by (unfold a3f_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia).
  rewrite app_nth1 by (unfold a3f_vals; rewrite length_map, length_seq; lia).
  unfold a3f_vals.
  set (f := fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))).
  rewrite (nth_indep _ (Z_to_bv 64 0) (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. unfold f. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma pfxd_e563 : forall (cx : dcx) (E : env) (regs : bvmap 5 word) (T : list byte) (p : Z),
  ew (d_env cx E (pfxd_vals regs T p)) 563 = Z_to_bv 64 (disco_table_c.din_of T p).
Proof.
  intros cx E regs T p. change 563%nat with (AT_X + 32)%nat.
  rewrite d_env_x by (unfold pfxd_vals, a3f_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia).
  unfold pfxd_vals. rewrite app_nth2 by (unfold a3f_vals; rewrite length_map, length_seq; lia).
  unfold a3f_vals. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma pfxd_e564 : forall (cx : dcx) (E : env) (regs : bvmap 5 word) (T : list byte) (p : Z),
  ew (d_env cx E (pfxd_vals regs T p)) 564 = Z_to_bv 64 (disco_table_c.dout_of T p).
Proof.
  intros cx E regs T p. change 564%nat with (AT_X + 33)%nat.
  rewrite d_env_x by (unfold pfxd_vals, a3f_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia).
  unfold pfxd_vals. rewrite app_nth2 by (unfold a3f_vals; rewrite length_map, length_seq; lia).
  unfold a3f_vals. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma pfxd_regs_ok : forall (cx : dcx) (E : env) (so : Z) (regs : bvmap 5 word) (T : list byte) (p : Z),
  d_E cx E -> 0 <= d_A cx < 2 ^ 64 -> spZ regs = d_A cx + so ->
  getr regs 8 = w64 (d_S cx) -> getr regs 9 = w64 (d_A cx) -> getr regs 19 = w64 SHADOW_OFF ->
  getr regs 18 = w64 WS_MASK -> getr regs 20 = w64 32 ->
  regs_ok (d_env cx E (pfxd_vals regs T p)) (a3f_sr so) regs.
Proof.
  intros cx E so regs T p HE HA Hsp H8 H9 H19 H18 H20.
  pose proof (d_E_env cx E (pfxd_vals regs T p) HE) as (HER & H32 & _ & HA60 & _ & _).
  unfold AT_A in HA60.
  assert (UA : bv_unsigned (ew (d_env cx E (pfxd_vals regs T p)) 60) = d_A cx).
  { rewrite HA60. unfold w64. apply unsigned_lit_small. exact HA. }
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<- | Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | rewrite UA; first [ rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned
                        | rewrite Z.add_0_r; exact H9 ]
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H8; unfold w64, d_S, spZ;
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
    | exact H18
    | exact H20
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (pfxd_env_reg cx E regs T p x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Lemma pfxd_region_tr : forall (E : env) H (m m' : word -> option byte) (r : YP09.region),
  region_ok SEGS E (mrestrict H m) r ->
  (forall c i, In c (YP09.r_chunks r) -> 0 <= i < c_len c ->
     aview SEGS H m' (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     aview SEGS H m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  (forall a, apresent H m a -> apresent H m' a) ->
  region_ok SEGS E (mrestrict H m') r.
Proof.
  intros E H m m' r (B1 & B2 & Wr & C) Hc Hp. split; [exact B1|]. split; [exact B2|]. split.
  - intros o Ho. apply (writable_kept H m m'); [apply Hp | exact (Wr o Ho)].
  - apply Forall_forall. intros c Hin i Hi. destruct (proj1 (Forall_forall _ _) C c Hin i Hi) as (b & Hb1 & Hb2).
    exists b. split; [exact Hb1|]. rewrite (mbyte_of_aview SEGS H H m m' _ (Hc c i Hin Hi)). exact Hb2.
Qed.

Lemma pfxd_frame_tr : forall (cx : dcx) h shf (W : world SEGS) (m m' : word -> option byte) (K : Z -> Prop),
  d_frame cx h shf W m ->
  (forall a, K a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  (forall a, d_S cx - 104 <= a < d_S cx -> K a) ->
  (forall a, d_A cx <= a < d_A cx + 472 -> K a) ->
  (forall a, d_FB cx <= a < d_FB cx + 24 -> K a) ->
  (forall a, d_FB cx + 4088 <= a < d_FB cx + 4096 -> K a) ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384 -> K a) ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 47 ->
  d_frame cx h shf W m'.
Proof.
  intros cx h shf W m m' K (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264)
    HK Hp K2 K60 K516 KFL KSH HA HF.
  exists E. split; [exact HE|].
  pose proof HE as (EE & _ & _ & E60 & EF & ESH).
  assert (B2 : base_val E (Some AT_STK) = d_S cx).
  { cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (B60 : base_val E (Some AT_A) = d_A cx).
  { cbn [base_val]. rewrite E60. unfold w64. apply unsigned_lit_small. lia. }
  assert (B516 : base_val E (Some AT_F) = d_FB cx).
  { cbn [base_val]. rewrite EF. unfold w64. apply unsigned_lit_small. lia. }
  assert (B529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
  { cbn [base_val]. rewrite ESH. unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
  unfold d_regions in HREG |- *.
  apply Forall_cons_iff in HREG as [R2 HREG]. apply Forall_cons_iff in HREG as [R60 HREG].
  apply Forall_cons_iff in HREG as [R516 HREG]. apply Forall_cons_iff in HREG as [R529 _].
  split.
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    - apply (pfxd_region_tr E (w_H W) m m' _ R2); [|exact Hp]. intros c i Hin Hi. apply HK.
      pose proof (pfxd_chunk_in _ c Hin ltac:(vm_compute; reflexivity)) as Hc.
      cbn [YP09.r_lo YP09.r_hi YP09.r_base] in Hc |- *. rewrite B2. apply K2. lia.
    - apply (pfxd_region_tr E (w_H W) m m' _ R60); [|exact Hp]. intros c i Hin Hi. apply HK.
      pose proof (pfxd_chunk_in _ c Hin ltac:(vm_compute; reflexivity)) as Hc.
      cbn [YP09.r_lo YP09.r_hi YP09.r_base] in Hc |- *. rewrite B60. apply K60. lia.
    - apply (pfxd_region_tr E (w_H W) m m' _ R516); [|exact Hp]. intros c i Hin Hi. apply HK.
      cbn [YP09.r_chunks YP09.r_base In] in Hin |- *. rewrite B516.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn in Hi |- *; apply K516; lia.
    - apply (pfxd_region_tr E (w_H W) m m' _ R529); [|exact Hp]. intros c i Hin Hi. apply HK.
      unfold fshadow_region in Hin |- *. cbn [YP09.r_chunks YP09.r_base] in Hin |- *. rewrite B529.
      unfold dsh_chunks in Hin. apply in_map_iff in Hin as (kk & <- & Hkk). apply in_seq in Hkk.
      change (Z.to_nat DFRAME_SH) with 384%nat in Hkk. cbn in Hi |- *. apply KSH. lia. }
  assert (KVM : forall off v, 0 <= off -> off + 8 <= 472 ->
    val_mem SEGS (rd W m) (d_A cx + off) 8 v -> val_mem SEGS (rd W m') (d_A cx + off) 8 v).
  { intros off v H0 H1 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact Hv].
    intros kk Hkk. apply HK. apply K60. change (Z.of_nat 8) with 8 in Hkk. lia. }
  split.
  { rewrite <- HFLAG. apply pfxd_rdword. intros i Hi. apply HK. apply KFL.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  split; [apply KVM; [lia | lia | exact V184]|].
  split; [apply KVM; [lia | lia | exact V120]|].
  split; [apply KVM; [lia | lia | exact V136]|].
  split; [apply KVM; [lia | lia | exact V376]|].
  split; [apply KVM; [lia | lia | exact V280]|].
  split; [apply KVM; [lia | lia | exact V232]|].
  apply KVM; [lia | lia | exact V264].
Qed.

Lemma pfxd_shadow_tr : forall (cx : dcx) shf (W : world SEGS) (m m' : word -> option byte) (K : Z -> Prop),
  d_shadow cx shf W m ->
  (forall a, K a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384 -> K a) ->
  d_shadow cx shf W m'.
Proof.
  intros cx shf W m m' K HS HK KSH kk Hkk. rewrite HK by (apply KSH; unfold DFRAME_SH in Hkk; lia).
  exact (HS kk Hkk).
Qed.

Lemma pfxd_garr8_text : forall (W : world SEGS) (m : word -> option byte) d (T : list Z),
  (forall i, 0 <= i < Z.of_nat (length T) -> aview SEGS (w_H W) m (d + i) = Some (nth (Z.to_nat i) T 0)) ->
  aview SEGS (w_H W) m (d + Z.of_nat (length T)) = Some 0 ->
  garr8 SEGS (rd W m) d (T ++ [0]).
Proof.
  intros W m d T Hb Hz jj Hjj. rewrite length_app in Hjj. cbn [length] in Hjj.
  destruct (Nat.lt_ge_cases jj (length T)) as [Hl|Hl].
  - rewrite app_nth1 by exact Hl.
    pose proof (Hb (Z.of_nat jj) ltac:(lia)) as Hv. rewrite Nat2Z.id in Hv.
    exact (YC88.val_mem1_of_aview SEGS (w_H W) m _ _ Hv).
  - assert (jj = length T) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    exact (YC88.val_mem1_of_aview SEGS (w_H W) m _ _ Hz).
Qed.

Lemma pfxd_ra_frame : forall (cx : dcx) shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= d_FB cx -> 0 <= lo -> lo + len <= 3072 ->
  (forall k, lo / 8 <= k < (lo + len + 7) / 8 -> shf k = 0) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + lo) len.
Proof.
  intros cx shf W m lo len HSH H8 HF0 Hlo Hhi Hz x Hx. exists 0. split; [|left; reflexivity].
  assert (Ex : shadow_of_addr SHADOW_OFF x = shadow_addr (d_FB cx) + (x - d_FB cx) / 8)
    by (unfold shadow_of_addr, shadow_addr; lia).
  rewrite Ex. rewrite HSH by (unfold DFRAME_SH; lia). f_equal. apply Hz. lia.
Qed.

Lemma pfxd_hull_frame : forall (cx : dcx) shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= d_FB cx -> 64 <= lo -> 0 < len -> lo + len + 64 <= 3072 ->
  shadow_hull_vis (aview SEGS (w_H W) m) (d_FB cx + lo) len.
Proof.
  intros cx shf W m lo len HSH H8 HF0 Hlo Hn Hhi s Hs. unfold shadow_addr in Hs.
  replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
  rewrite HSH; [discriminate|]. unfold shadow_addr, DFRAME_SH. lia.
Qed.

Lemma pfxd_offimg : forall b n a, off_img b n -> in_img SEGS a -> b <= a < b + n -> False.
Proof.
  intros b n a Hoff Hi Ha. pose proof (pa_img_range a Hi) as Hr. unfold off_img in Hoff. lia.
Qed.

Lemma pfxd_roimg : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hg)].
Qed.

Lemma pfxd_sh13 : forall (cx : dcx) p, d_FB cx mod 8 = 0 ->
  shadow_addr (d_FB cx) + (271 + 6 * p) = shadow_addr (d_obj cx OT + 48 * p + 13).
Proof.
  intros cx p H8. change (d_obj cx OT) with (d_FB cx + 2160). unfold shadow_addr.
  pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)) as D. rewrite H8 in D.
  replace (d_FB cx + 2160 + 48 * p + 13) with ((d_FB cx / 8 + (271 + 6 * p)) * 8 + 5) by lia.
  rewrite Z.div_add_l by lia. change (5 / 8) with 0. lia.
Qed.

Lemma pfxd_sh14 : forall (cx : dcx) p, d_FB cx mod 8 = 0 ->
  shadow_addr (d_FB cx) + (271 + 6 * p) = shadow_addr (d_obj cx OT + 48 * p + 14).
Proof.
  intros cx p H8. change (d_obj cx OT) with (d_FB cx + 2160). unfold shadow_addr.
  pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)) as D. rewrite H8 in D.
  replace (d_FB cx + 2160 + 48 * p + 14) with ((d_FB cx / 8 + (271 + 6 * p)) * 8 + 6) by lia.
  rewrite Z.div_add_l by lia. change (6 / 8) with 0. lia.
Qed.

Lemma pfxd_shr : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 64.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF. lia. Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis ASNPRINTF : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi FF_got_canary FF_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi snp_cr (SIGMA AS___interceptor_trampoline_snprintf).
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis DBRT : d_body_rt_stmt B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis KGOT : ak_can_got tfib_K = FF_got_canary.
Hypothesis SNPRO : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis SNPUN : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Definition pfxd_runB_stmt (p : Z) : Prop :=
  forall (fq : YK11.FPState) (W : world SEGS) (E : env) (ms : machine_state) (mdc : Model)
    STK sp0 FP ly S W0 mem md own lyc Sc k (Q : world SEGS -> config -> Prop),
  img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E (pfxd_ssB p) (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  (forall (R : bvmap 5 word) (mat' : list word),
     (forall r, getr R r = sv_denot E (sr_get (pfxd_finB p) r)) ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     SRr SEGS W (mkCfg (YK11.mkst (fx := fq) R (Z_to_bv 64 (SIGMA AS___interceptor_trampoline_snprintf)) (ms_mem ms)
       (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.

Definition pfxd_runA_stmt : Prop :=
  forall (fq : YK11.FPState) (W : world SEGS) (E : env) (ms : machine_state) (mdc : Model)
    STK sp0 FP ly S W0 mem md own lyc Sc k (Q : world SEGS -> config -> Prop),
  img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E pfxd_ssA (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  (forall (R : bvmap 5 word) (mat' : list word),
     (forall r, getr R r = sv_denot E (sr_get pfxd_finA r)) ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     SRr SEGS W (mkCfg (YK11.mkst (fx := fq) R (Z_to_bv 64 (BASE + MD_OFF)) (ms_mem ms)
       (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.

Lemma pfxd_runB_0 : pfxd_runB_stmt 0.
Proof.
  intros fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ KP.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [pfxd_awr|].
  lazymatch type of HS with
  | YP0l.st_ok _ _ ?st (restrict _ ?m1) =>
      assert (Emem : ms_mem m1 = ms_mem ms) by pfxd_emem HF;
      assert (Hsr : ss_regs st = pfxd_finB 0) by (vm_compute; reflexivity);
      pmkst HS; rewrite Emem in HJ |- *;
      apply (KP (ms_regs m1));
      [ intros r; rewrite (st_ok_restrict_reg SEGS _ _ _ _ r HS), Hsr; reflexivity | exact HJ ]
  end.
Qed.

Lemma pfxd_runB_1 : pfxd_runB_stmt 1.
Proof.
  intros fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ KP.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [pfxd_awr|].
  lazymatch type of HS with
  | YP0l.st_ok _ _ ?st (restrict _ ?m1) =>
      assert (Emem : ms_mem m1 = ms_mem ms) by pfxd_emem HF;
      assert (Hsr : ss_regs st = pfxd_finB 1) by (vm_compute; reflexivity);
      pmkst HS; rewrite Emem in HJ |- *;
      apply (KP (ms_regs m1));
      [ intros r; rewrite (st_ok_restrict_reg SEGS _ _ _ _ r HS), Hsr; reflexivity | exact HJ ]
  end.
Qed.

Lemma pfxd_runB_2 : pfxd_runB_stmt 2.
Proof.
  intros fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ KP.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [pfxd_awr|].
  lazymatch type of HS with
  | YP0l.st_ok _ _ ?st (restrict _ ?m1) =>
      assert (Emem : ms_mem m1 = ms_mem ms) by pfxd_emem HF;
      assert (Hsr : ss_regs st = pfxd_finB 2) by (vm_compute; reflexivity);
      pmkst HS; rewrite Emem in HJ |- *;
      apply (KP (ms_regs m1));
      [ intros r; rewrite (st_ok_restrict_reg SEGS _ _ _ _ r HS), Hsr; reflexivity | exact HJ ]
  end.
Qed.

Lemma pfxd_runB_3 : pfxd_runB_stmt 3.
Proof.
  intros fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ KP.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [pfxd_awr|].
  lazymatch type of HS with
  | YP0l.st_ok _ _ ?st (restrict _ ?m1) =>
      assert (Emem : ms_mem m1 = ms_mem ms) by pfxd_emem HF;
      assert (Hsr : ss_regs st = pfxd_finB 3) by (vm_compute; reflexivity);
      pmkst HS; rewrite Emem in HJ |- *;
      apply (KP (ms_regs m1));
      [ intros r; rewrite (st_ok_restrict_reg SEGS _ _ _ _ r HS), Hsr; reflexivity | exact HJ ]
  end.
Qed.

Lemma pfxd_runB_4 : pfxd_runB_stmt 4.
Proof.
  intros fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ KP.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [pfxd_awr|].
  lazymatch type of HS with
  | YP0l.st_ok _ _ ?st (restrict _ ?m1) =>
      assert (Emem : ms_mem m1 = ms_mem ms) by pfxd_emem HF;
      assert (Hsr : ss_regs st = pfxd_finB 4) by (vm_compute; reflexivity);
      pmkst HS; rewrite Emem in HJ |- *;
      apply (KP (ms_regs m1));
      [ intros r; rewrite (st_ok_restrict_reg SEGS _ _ _ _ r HS), Hsr; reflexivity | exact HJ ]
  end.
Qed.

Lemma pfxd_runB_5 : pfxd_runB_stmt 5.
Proof.
  intros fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ KP.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [pfxd_awr|].
  lazymatch type of HS with
  | YP0l.st_ok _ _ ?st (restrict _ ?m1) =>
      assert (Emem : ms_mem m1 = ms_mem ms) by pfxd_emem HF;
      assert (Hsr : ss_regs st = pfxd_finB 5) by (vm_compute; reflexivity);
      pmkst HS; rewrite Emem in HJ |- *;
      apply (KP (ms_regs m1));
      [ intros r; rewrite (st_ok_restrict_reg SEGS _ _ _ _ r HS), Hsr; reflexivity | exact HJ ]
  end.
Qed.

Lemma pfxd_runB_6 : pfxd_runB_stmt 6.
Proof.
  intros fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ KP.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [pfxd_awr|].
  lazymatch type of HS with
  | YP0l.st_ok _ _ ?st (restrict _ ?m1) =>
      assert (Emem : ms_mem m1 = ms_mem ms) by pfxd_emem HF;
      assert (Hsr : ss_regs st = pfxd_finB 6) by (vm_compute; reflexivity);
      pmkst HS; rewrite Emem in HJ |- *;
      apply (KP (ms_regs m1));
      [ intros r; rewrite (st_ok_restrict_reg SEGS _ _ _ _ r HS), Hsr; reflexivity | exact HJ ]
  end.
Qed.

Lemma pfxd_runB_7 : pfxd_runB_stmt 7.
Proof.
  intros fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ KP.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [pfxd_awr|].
  lazymatch type of HS with
  | YP0l.st_ok _ _ ?st (restrict _ ?m1) =>
      assert (Emem : ms_mem m1 = ms_mem ms) by pfxd_emem HF;
      assert (Hsr : ss_regs st = pfxd_finB 7) by (vm_compute; reflexivity);
      pmkst HS; rewrite Emem in HJ |- *;
      apply (KP (ms_regs m1));
      [ intros r; rewrite (st_ok_restrict_reg SEGS _ _ _ _ r HS), Hsr; reflexivity | exact HJ ]
  end.
Qed.

Lemma pfxd_runA : pfxd_runA_stmt.
Proof.
  intros fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ KP.
  pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) MD_OFF; [pfxd_awr|].
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?st (restrict _ ?m1) =>
      assert (Emem : ms_mem m1 = ms_mem ms) by pfxd_emem HF;
      assert (Hsr : ss_regs st = pfxd_finA) by (vm_compute; reflexivity);
      pmkst HS; rewrite Emem in HJ |- *;
      apply (KP (ms_regs m1));
      [ intros r; rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS), Hsr; reflexivity | exact HJ ]
  end.
Qed.

Lemma pfxd_runB : forall p, 0 <= p < 8 -> pfxd_runB_stmt p.
Proof.
  intros p Hp. assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    [exact pfxd_runB_0 | exact pfxd_runB_1 | exact pfxd_runB_2 | exact pfxd_runB_3 |
     exact pfxd_runB_4 | exact pfxd_runB_5 | exact pfxd_runB_6 | exact pfxd_runB_7].
Qed.

Theorem a3f_pfxd : forall p, 0 <= p < 8 -> seg_pfd_p_spec B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp8 cx h i n now op W0 c0 T0 T1 buf count os vpad W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & R24 & (HBR & R10) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY).
destruct HY as (HPYK & Hhd & H352 & HWID & HTOKc).
pose proof HPYK as (HSL & H408 & HUSED).
pose proof HSL as (Hp & H368 & H360).
pose proof HBR as (R21 & R22 & R23 & R25 & R26 & R27).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof HTOK1 as (_ & _ & _ & HT4).
destruct (HT4 p ltac:(lia)) as (Hhd01 & Hhd40 & _).
assert (Hhd1 : disco_table_c.hd_of T1 p = 1) by lia.
destruct (Hhd40 Hhd1) as (Hdi40 & Hdo40).
assert (Rdi : 0 <= disco_table_c.din_of T1 p < 256) by exact (slot_ser_Pq.u1_range T1 (48 * p + 13)).
assert (Rdo : 0 <= disco_table_c.dout_of T1 p < 256) by exact (slot_ser_Pq.u1_range T1 (48 * p + 14)).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof HCAN as (HCv & HCr & HCi).
pose proof DCAN as (AIL & KCAN).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as (Hceil0 & _).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HOFF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
assert (HFB8 : d_FB cx mod 8 = 0) by (pose proof (Z.div_mod (d_FB cx) 32 ltac:(lia)); lia).
assert (A1 : (d_A cx - d_S cx) mod 16 = 0).
{ pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
  rewrite GA32 in DA. rewrite GS16 in DS.
  replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult. }
clear GA32 GS16 GF32.
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
assert (U60E : bv_unsigned (ew E AT_A) = d_A cx) by (rewrite E60; unfold w64; apply unsigned_lit_small; lia).
assert (U516E : bv_unsigned (ew E AT_F) = d_FB cx) by (rewrite EF; unfold w64; apply unsigned_lit_small; lia).
pose proof (d_E_env cx E (pfxd_vals regs T1 p) HE) as HE'.
pose proof HE' as (EE' & E32' & HEI' & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E (pfxd_vals regs T1 p)) 60) = d_A cx).
{ rewrite (E60' : ew _ 60 = _). unfold w64. apply unsigned_lit_small. lia. }
assert (U516 : bv_unsigned (ew (d_env cx E (pfxd_vals regs T1 p)) 516) = d_FB cx).
{ rewrite (EF' : ew _ 516 = _). unfold w64. apply unsigned_lit_small. lia. }
assert (U529 : bv_unsigned (ew (d_env cx E (pfxd_vals regs T1 p)) 529) = shadow_addr (d_FB cx)).
{ rewrite (ESH' : ew _ 529 = _). unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
assert (Hregs : regs_ok (d_env cx E (pfxd_vals regs T1 p)) (a3f_sr (-16)) regs)
  by (apply pfxd_regs_ok; [exact HE | lia | exact Rsp | exact R8 | exact R9 | exact R19 | exact R18 | exact R20]).
assert (HGf : facts_ok (d_env cx E (pfxd_vals regs T1 p)) (d_facts pfxd_fa [])).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (pfxd_vals regs T1 p) pfxd_fa [] HCTX HE); [|exact I].
  cbn [pfxd_fa atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite pfxd_e563, pfxd_e564. rewrite !unsigned_lit_small by lia. rewrite Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia. }
assert (HTB : forall kk (nn : nat), 0 <= kk -> (Z.to_nat kk + nn <= 400)%nat ->
  val_mem SEGS (rd W mem3) (d_obj cx OT + kk) nn (disco_table_c.u_at T1 kk nn)).
{ intros kk nn Hk0 Hkn. unfold disco_table_c.u_at.
  apply (ReacDiscoTableAge.ta_vm_of_ga (rd W mem3) (d_obj cx OT) T1 kk nn HGT Hk0). rewrite HLT1. lia. }
assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E (pfxd_vals regs T1 p)) (rd W mem3) (d_FB cx)) (pfxd_fcs p)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS _ _ (d_FB cx) (2173 + 48 * p) 1%N (SOff 563 0) (disco_table_c.din_of T1 p)).
    + cbn [sv_denot]. rewrite pfxd_e563, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + cbn [N.to_nat]. unfold disco_table_c.din_of.
      replace (d_FB cx + (2173 + 48 * p)) with (d_obj cx OT + (48 * p + 13)) by (unfold d_obj, dobj_off; lia).
      apply HTB; lia.
  - apply (chunk_ok_val SEGS _ _ (d_FB cx) (2174 + 48 * p) 1%N (SOff 564 0) (disco_table_c.dout_of T1 p)).
    + cbn [sv_denot]. rewrite pfxd_e564, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + cbn [N.to_nat]. unfold disco_table_c.dout_of.
      replace (d_FB cx + (2174 + 48 * p)) with (d_obj cx OT + (48 * p + 14)) by (unfold d_obj, dobj_off; lia).
      apply HTB; lia. }
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E (pfxd_vals regs T1 p)) (rd W mem3) (d_A cx)) (pfxd_acs p)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 352 8%N (SOff 529 (271 + 6 * p)) (shadow_addr (d_obj cx OT + 48 * p + 14))).
  - cbn [sv_denot]. rewrite U529, (pfxd_sh14 cx p HFB8). reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply pfxd_shr. unfold d_obj, dobj_off. lia.
  - cbn. lia.
  - exact H352. }
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E BNR_OFF (a3f_sr (-16)) (pfxd_vals regs T1 p)
  (pfxd_acs p) (pfxd_fcs p) [] (d_facts pfxd_fa []) HCTX HE HREG HFLAG Hregs HGf Hacs Hfcs (Forall_nil _) I
  (Forall_nil _) (pfxd_kwf p Hp8)) as HS0.
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
pose proof HSP1 as ((H208 & H320) & H192 & H200).
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (_ & Hb4096 & Hbceil & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (LO : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))) <= 1296).
{ rewrite length_map, (DiscoArm3FieldPH.ph_objs_len buf vpad os HVP Lo6), Los. lia. }
assert (LU : length (a3f_used (p + 1)) = 32%nat) by (unfold a3f_used; reflexivity).
unfold cfg_at, w64.

destruct (Z.eqb_spec (a3f_bnret T1 p) 0) as [Hb0 | Hb1].
- assert (HMB : a3f_model T1 p =
    (disco_box_name_model.bn_TK (disco_box_name_model.bn_NM (a3f_fam T1 p) [] (disco_table_c.din_of T1 p)
       (disco_table_c.dout_of T1 p)), pfxd_T (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p)))
    by (unfold a3f_model, a3f_ent, pfxd_T, a3f_fam; exact (slot_ser_P3.model_bn T1 p Hhd1 Hb0)).
  destruct (slot_ser_P3.bn_ret0 (a3f_fam T1 p) [] (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p) Hb0)
    as (Bi & Bo & Bz).
  destruct (disco_box_name_model.bn_c17 (a3f_fam T1 p) (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p)
    Bi Bo Bz) as (_ & _ & Ltk & _).
  pose proof (HTOKc Hb0) as HTOK3.
  pose proof (pfxd_T_len (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p) ltac:(lia) ltac:(lia)) as LT.
  assert (POSTB : forall (R : bvmap 5 word) (mat1 : list word),
    getr R 1 = Z_to_bv 64 (BASE + PFXDR_OFF) -> spZ R = d_A cx ->
    getr R 3 = w64 (as_gp B) -> getr R 4 = w64 (as_tp B) -> getr R 8 = w64 (d_S cx) -> getr R 9 = w64 (d_A cx) ->
    getr R 10 = w64 (d_obj cx OWID) -> getr R 11 = w64 24 -> getr R 12 = w64 (VAL (A_OBJ 14)) ->
    getr R 13 = w64 (disco_table_c.din_of T1 p) -> getr R 14 = w64 (disco_table_c.dout_of T1 p) ->
    getr R 18 = w64 WS_MASK -> getr R 19 = w64 SHADOW_OFF -> getr R 20 = w64 32 ->
    getr R 22 = w64 (d_obj cx OT + 48 * p) -> getr R 24 = w64 buf -> getr R 27 = w64 (shadow_addr (d_FB cx)) ->
    ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 (with_vm_backing (m_vm_lazy md3) mat1 md3) k ->
    SRr SEGS W (mkCfg (YK11.mkst (fx := fq) R (Z_to_bv 64 (SIGMA AS___interceptor_trampoline_snprintf)) mem3
      (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md3) mat1 md3))
      (fun W' c' => exists mp, f_md B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W' c')).
  { intros R mat1 Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q18 Q19 Q20 Q22 Q24 Q27 HJ1.
    set (md1 := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
    assert (HDC : dimg_consts W mem3) by exact (DCRO LAWS DROH ly3 S3 W mem3 md3 HAR3 HIMG).
    pose proof HDC as (_ & _ & _ & HSTR & _).
    pose proof HSTR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HSC14 & _) & _).
    pose proof HSC14 as (Hc14 & HG14 & Hf14 & Hf63 & Hl32 & HAM14 & HRA14 & HHV14 & _ & HIM14).
    assert (HSN : SNPRINTF_STK = 11776) by reflexivity.
    assert (A2 : d_A cx - d_S cx <= 0) by lia.
    assert (A3 : SNPRINTF_STK - (d_A cx - d_S cx) <= LLVMF_STK) by (rewrite HSN; unfold LLVMF_STK; lia).
    assert (Hsp0 : spZ R = d_S cx + (d_A cx - d_S cx)) by lia.
    assert (A6 : YK0s.ret_ok (getr R 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [unfold PFXDR_OFF; lia | reflexivity]).
    assert (A7 : snp_ctx W mem3 (spZ R) (d_obj cx OWID) 24).
    { apply (snp_ctx_ok B W mem3 (spZ R) (d_obj cx OWID) 24 SNPRO SNPUN HIMG
        (snp_can_of B tfib_K AIL KGOT KCAN ly3 S3 W mem3 md3 (c_canary cx) HAR3 HCv HCr)).
      - rewrite Q2, HSN. unfold off_img, IMG_LO, IMG_TOP. lia.
      - unfold off_img in HOFF |- *. unfold d_obj, dobj_off. lia. }
    pose proof (pa_img_range _ (HIM14 (VAL (A_OBJ 14)) ltac:(cbn [length Z.of_nat]; lia))) as I0.
    pose proof (pa_img_range _ (HIM14 (VAL (A_OBJ 14) + 5) ltac:(cbn [length Z.of_nat]; lia))) as I5.
    unfold IMG_LO, IMG_TOP in I0, I5.
    assert (A8 : SnShared.fmt_at (aview SEGS (w_H W) mem3) (SnShared.snp_out SNPRINTF_STK (spZ R) (d_obj cx OWID) 24)
      (VAL (A_OBJ 14)) a3f_fmt_wid).
    { unfold SnShared.fmt_at, a3f_fmt_wid. split; [exact Hf14|]. split.
      { intros ii Hii. cbn [length Z.of_nat] in Hii.
        destruct (HG14 (Z.to_nat ii) ltac:(rewrite length_app; cbn [length]; lia)) as (Hv & Hr).
        rewrite Z2Nat.id in Hv by lia. exact (aview_of_val_mem1 SEGS (w_H W) mem3 _ _ Hv Hr). }
      split.
      { unfold SnShared.snp_out. rewrite Q2, HSN. cbn [length Z.of_nat].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
          unfold d_obj, dobj_off; unfold off_img in HOFF; unfold IMG_LO, IMG_TOP in HOFF; lia. }
      split; [exact HAM14|]. split; [exact HRA14 | exact HHV14]. }
    assert (A9 : pf_parse a3f_fmt_wid = Some [Pd; PLit 120; Pd]) by (vm_compute; reflexivity).
    assert (A10 : Forall pf_disco_piece [Pd; PLit 120; Pd])
      by (repeat (apply Forall_cons; [exact I|]); apply Forall_nil).
    assert (V14 : VAL (A_OBJ 14) = 0x20fe0)
      by (rewrite (pa_obj_val (PI := PI) 14%nat) by (unfold tfib_nobj; lia); reflexivity).
    assert (A10l : disco_fmt_lo <= VAL (A_OBJ 14)) by (rewrite V14; unfold disco_fmt_lo; lia).
    assert (A10h : VAL (A_OBJ 14) + Z.of_nat (length a3f_fmt_wid) + 1 <= disco_fmt_hi)
      by (rewrite V14; unfold a3f_fmt_wid, disco_fmt_hi; cbn [length Z.of_nat]; lia).
    assert (A10n : a3f_fmt_wid <> []) by (unfold a3f_fmt_wid; discriminate).
    assert (A11 : SnShared.va_words R (aview SEGS (w_H W) mem3) (spZ R) [] (map (argZ R) [3; 4; 5; 6; 7])).
    { unfold SnShared.va_words. split; [rewrite app_nil_r; reflexivity|]. intros i0 Hi0. cbn in Hi0. lia. }
    assert (A12 : spZ R + 8 * Z.of_nat (length (@nil Z)) <= 2 ^ 47).
    { cbn [length Z.of_nat]. rewrite Q2.
      pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HS1 & HS2 & _) & _).
      lia. }
    assert (A13 : Forall (zdisjoint (spZ R, 8 * Z.of_nat (length (@nil Z))))
      (SnShared.snp_out SNPRINTF_STK (spZ R) (d_obj cx OWID) 24)).
    { unfold SnShared.snp_out. rewrite Q2, HSN. cbn [length Z.of_nat].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
        unfold d_obj, dobj_off; lia. }
    assert (G3 : argZ R 3 = disco_table_c.din_of T1 p).
    { unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite Q13. unfold w64. apply unsigned_lit_small. lia. }
    assert (G4 : argZ R 4 = disco_table_c.dout_of T1 p).
    { unfold argZ. replace (Z_to_bv 5 (10 + 4)) with (14%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite Q14. unfold w64. apply unsigned_lit_small. lia. }
    assert (A14 : SnShared.pf_args_asan (aview SEGS (w_H W) mem3)
      (SnShared.snp_out SNPRINTF_STK (spZ R) (d_obj cx OWID) 24)
      (map (argZ R) [3; 4; 5; 6; 7]) [AInt (disco_table_c.din_of T1 p); AInt (disco_table_c.dout_of T1 p)]).
    { cbn [map SnShared.pf_args_asan SnShared.pf_arg_asan]. rewrite G3, G4.
      split; [split; [lia | reflexivity]|]. split; [split; [lia | reflexivity] | exact I]. }
    assert (A14m : SnFF.pf_args_amem (map (argZ R) [3; 4; 5; 6; 7])
      [AInt (disco_table_c.din_of T1 p); AInt (disco_table_c.dout_of T1 p)]) by exact I.
    assert (HTt : pf_text [Pd; PLit 120; Pd] [AInt (disco_table_c.din_of T1 p); AInt (disco_table_c.dout_of T1 p)] =
      Some (pfxd_T (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p))) by (apply pfxd_text; lia).
    assert (A16 : 1 <= 24 < 2 ^ 31) by lia.
    assert (A17 : Z.of_nat (length (pfxd_T (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p))) < 2 ^ 31 - 1)
      by lia.
    assert (A18 : 0 < d_obj cx OWID) by (unfold d_obj, dobj_off; lia).
    assert (A19 : d_obj cx OWID + 24 <= 2 ^ 63) by (unfold d_obj, dobj_off; lia).
    assert (A20 : pairwise zdisjoint (SnShared.snp_out SNPRINTF_STK (spZ R) (d_obj cx OWID) 24)).
    { unfold SnShared.snp_out. rewrite Q2, HSN. cbn [pairwise].
      split; [apply Forall_cons; [|apply Forall_nil]; unfold zdisjoint; cbn [fst snd]; unfold d_obj, dobj_off; lia|].
      split; [apply Forall_nil | exact I]. }
    assert (A21 : forall a, d_obj cx OWID <= a < d_obj cx OWID + 24 ->
      awr_byte LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
        [(DFRAME_CLASS, c_fpos cx)] a /\ ~ (spZ R - SNPRINTF_STK <= a < spZ R)).
    { intros a Ha. unfold d_obj, dobj_off in Ha.
      split; [exact (proj1 (HAWRF a ltac:(unfold DFRAME_SIZE; lia))) | rewrite Q2, HSN; lia]. }
    assert (A22 : amem_range (d_obj cx OWID) (24 + 8)).
    { unfold amem_range, d_obj, dobj_off. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *. lia. }
    assert (A23 : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF (d_obj cx OWID) 24).
    { change (d_obj cx OWID) with (d_FB cx + 2000).
      apply (pfxd_ra_frame cx dsh_md W mem3 2000 24 HSHD); [exact HFB8 | lia | lia | lia |].
      intros kk Hkk. change (2000 / 8) with 250 in Hkk. change ((2000 + 24 + 7) / 8) with 253 in Hkk.
      assert (Hk3 : kk = 250 \/ kk = 251 \/ kk = 252) by lia.
      destruct Hk3 as [-> | [-> | ->]]; vm_compute; reflexivity. }
    assert (A24 : shadow_hull_vis (aview SEGS (w_H W) mem3) (d_obj cx OWID) 24).
    { change (d_obj cx OWID) with (d_FB cx + 2000).
      apply (pfxd_hull_frame cx dsh_md W mem3 2000 24 HSHD); [exact HFB8 | lia | lia | lia | lia]. }
    eapply SRr_bind.
    { exact (aj_snprintf_at B LAWS ASNPRINTF fq W R mem3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md1 k (d_obj cx OWID) 24 (VAL (A_OBJ 14)) a3f_fmt_wid
        [Pd; PLit 120; Pd] [] (map (argZ R) [3; 4; 5; 6; 7])
        [AInt (disco_table_c.din_of T1 p); AInt (disco_table_c.dout_of T1 p)]
        (pfxd_T (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p)) (d_A cx - d_S cx)
        HJ1 HFRM0 Q10 Q11 Q12 Hsp0 A1 A2 A3 Q3 Q4 A6 A7 A8 A9 A10 A10l A10h A10n A11 A12 A13 A14 A14m HTt
        A16 A17 A18 A19 A20 A21 A22 A23 A24 HIMG). }
    cbv beta. intros W2 c2 _ (-> & fx2 & regs2 & mem2 & md2 & -> & HFRMc & _ & HJ2 & HP2 & Hsame & Hres & Heff & Hz & Hfr2 & Hpres2).
    clear dependent fq. rename fx2 into fq. rename HFRMc into HFRM0.
    pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
    rewrite Z.min_l in Heff, Hz by lia.
    assert (HOWID2 : garr8 SEGS (rd W mem2) (d_obj cx OWID)
      (pfxd_T (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p) ++ [0]))
      by exact (pfxd_garr8_text W mem2 (d_obj cx OWID) _ Heff Hz).
    assert (KU : forall a, 0 <= a < 2 ^ 64 -> ~ (d_obj cx OWID <= a < d_obj cx OWID + 24) ->
      ~ (d_A cx - 11776 <= a < d_A cx) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
    { intros a Ha H1 H2. apply Hfr2; [exact Ha | lia | rewrite Q2, HSN; exact H2]. }
    pose (K := fun a : Z => 0 <= a < 2 ^ 64 /\ ~ (d_obj cx OWID <= a < d_obj cx OWID + 24) /\
      ~ (d_A cx - 11776 <= a < d_A cx)).
    assert (HK : forall a, K a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
    { intros a (Ha & H1 & H2). exact (KU a Ha H1 H2). }
    assert (KR : forall lo hi, 0 <= lo -> hi <= 2 ^ 64 -> (hi <= d_obj cx OWID \/ d_obj cx OWID + 24 <= lo) ->
      (hi <= d_A cx - 11776 \/ d_A cx <= lo) -> forall a, lo <= a < hi -> K a).
    { intros lo hi H1 H2 H3 H4 a Ha. unfold K. clear - H1 H2 H3 H4 Ha. lia. }
    assert (Eow : d_obj cx OWID = d_FB cx + 2000) by reflexivity.
    assert (Hsh : shadow_addr (d_FB cx) = 2147450880 + d_FB cx / 8) by reflexivity.
    assert (HFRM2 : d_frame cx h dsh_md W mem2).
    { apply (pfxd_frame_tr cx h dsh_md W mem3 mem2 K HFRM HK Hpres2); try (apply KR; rewrite ?Eow, ?Hsh; lia); lia. }
    assert (HSHD2 : d_shadow cx dsh_md W mem2).
    { apply (pfxd_shadow_tr cx dsh_md W mem3 mem2 K HSHD HK). apply KR; rewrite ?Eow, ?Hsh; lia. }
    assert (HBODY2 : d_body B cx h n (a3_xb buf op) dsh_md ly3 S3 W mem2).
    { apply (DBRT cx h n n (a3_xb buf op) dsh_md dsh_md ly3 S3 W mem3 mem2 (d_A cx - 11776) (d_A cx)
        (fun a => (d_A cx - 11776 <= a < d_A cx) \/ d_objr cx OWID a) HBODY).
      - unfold LLVMF_STK. lia.
      - lia.
      - intros a [Ha|Ha]; [left; exact Ha|right].
        unfold d_objr in Ha. rewrite Eow in Ha. cbn [dobj_size] in Ha.
        pose proof HGEO as (_ & _ & Hh0 & Hhc & _ & _ & Hhf & Hinp).
        change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hhf, Hinp. unfold HUNT_SIZE in Hhf, Hhc.
        unfold d_rdset, d_objr. intros [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
        + unfold d_obj, dobj_off, dobj_size in Hr. lia.
        + unfold d_obj, dobj_off, dobj_size in Hr. lia.
        + unfold d_obj, dobj_off, dobj_size in Hr. lia.
        + unfold d_obj, dobj_off, dobj_size in Hr. lia.
        + unfold HUNT_SIZE in Hr. lia.
        + destruct Hr as (Hcn & Hr). destruct (Hinp Hcn) as (_ & _ & Hpf & _). lia.
        + assert (Hro : in_roP SEGS pa_relro_lo pa_relro_hi a) by (first [exact Hr | exact (proj1 Hr)]).
          exact (pfxd_offimg (d_FB cx) 4096 a HOFF (pfxd_roimg a Hro) ltac:(lia)).
        + exact (pfxd_offimg (d_FB cx) 4096 a HOFF (HCi a Hr) ltac:(lia)).
      - intros a Ha HnR. apply KU; [exact Ha | |].
        + intros Hd. apply HnR. right. unfold d_objr. cbn [dobj_size]. exact Hd.
        + intros Hw. apply HnR. left. exact Hw.
      - intros a _ Hpa. exact (Hpres2 a Hpa).
      - exact HFRM2.
      - exact HSHD2.
      - lia. }
    assert (KV : forall off v, 0 <= off -> off + 8 <= 472 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
      val_mem SEGS (rd W mem2) (d_A cx + off) 8 v).
    { intros off v H0 H1 Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem2); [|exact Hv].
      intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KU; unfold d_obj, dobj_off; lia. }
    assert (KG : forall a L, 0 <= a -> a + Z.of_nat (length L) <= 2 ^ 64 ->
      (a + Z.of_nat (length L) <= d_obj cx OWID \/ d_obj cx OWID + 24 <= a) ->
      (a + Z.of_nat (length L) <= d_A cx - 11776 \/ d_A cx <= a) ->
      garr8 SEGS (rd W mem3) a L -> garr8 SEGS (rd W mem2) a L).
    { intros a L H0 H1 H2 H3 Hg. apply (YC88.garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem2 a L); [|exact Hg].
      intros x Hx. apply KU; lia. }
    assert (V240 : val_mem SEGS (rd W mem2) (d_A cx + 240) 8 (d_obj cx OTOK)).
    { apply KV; [lia | lia |].
      pose proof HREG as HR. unfold d_regions in HR. pose proof (Forall_inv (Forall_inv_tail HR)) as RA.
      exact (field_of_region E _ AT_A (d_A cx) _ _ _ _ _ 240 8%N (SOff AT_F 1856) (d_obj cx OTOK) RA U60E
        ltac:(unfold dslot_chunks; cbn [map fst snd In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot]; rewrite U516E; unfold d_obj, dobj_off; reflexivity)
        ltac:(cbn [Z.of_N]; unfold d_obj, dobj_off; lia) ltac:(cbn [Z.of_N]; lia)). }
    rewrite Q1.
    remember (Eimg (Ereg regs2 [Z_to_bv 64 SB; Z_to_bv 64 (d_obj cx OTOK)])) as E0 eqn:HE0.
    assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
    assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs2 r)
      by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
    assert (E33 : ew E0 33 = Z_to_bv 64 (d_obj cx OTOK)).
    { rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
    assert (P2 : getr regs2 2 = getr R 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
    assert (P3 : getr regs2 3 = getr R 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
    assert (P4 : getr regs2 4 = getr R 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
    assert (P8 : getr regs2 8 = getr R 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
    assert (P9 : getr regs2 9 = getr R 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
    assert (P18 : getr regs2 18 = getr R 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
    assert (P19 : getr regs2 19 = getr R 19) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
    assert (P20 : getr regs2 20 = getr R 20) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
    assert (P22 : getr regs2 22 = getr R 22) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
    assert (P24 : getr regs2 24 = getr R 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
    assert (P27 : getr regs2 27 = getr R 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
    assert (U9 : bv_unsigned (ew E0 9) = d_A cx).
    { rewrite (EE0 9%nat 9%bv eq_refl), P9, Q9. unfold w64. apply unsigned_lit_small. lia. }
    assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 (mkSS PFXDR_OFF sr_atoms pfxd_rsP None (mkFacts [] [] []))
      (restrict (w_H W) (YK11.mkst (fx := fq) regs2 (Z_to_bv 64 (BASE + PFXDR_OFF)) mem2 (YK11.seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - rewrite HE0. apply regs_ok_Eimg_Ereg.
      - exact pfxd_pwf.
      - unfold pfxd_rsP. apply Forall_cons; [|apply Forall_nil].
        unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E0 _ (d_A cx) 240 8%N (SOff 33 0) (d_obj cx OTOK)).
        + cbn [sv_denot]. rewrite E33, unsigned_lit_small by (unfold d_obj, dobj_off; lia). rewrite Z.add_0_r. reflexivity.
        + cbn [Z.of_N]. unfold d_obj, dobj_off. lia.
        + cbn. lia.
        + exact V240.
      - unfold pfxd_rsP. split; exact I.
      - split; [exact I | split; exact I]. }
    reshok_bx HS 32%nat.
    paj_run_to_tok RUNTO HS HJ2 SHOK Bspan MD_OFF; [pfxd_awr|].
    assert (Emem2 : ms_mem ms = mem2) by pfxd_emem HF.
    pmkst HS. rewrite Emem2 in HJ2 |- *.
    prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4.
    prreg HS (8%bv : bv 5) Z8. prreg HS (9%bv : bv 5) Z9. prreg HS (18%bv : bv 5) Z18.
    prreg HS (19%bv : bv 5) Z19. prreg HS (20%bv : bv 5) Z20. prreg HS (22%bv : bv 5) Z22.
    prreg HS (23%bv : bv 5) Z23. prreg HS (24%bv : bv 5) Z24. prreg HS (27%bv : bv 5) Z27.
    apply SRr_ret. exists (d_obj cx OTOK).
    unfold f_md, a3f_st. split; [exact Hfrom|].
    unfold d_arm_at_pf, d_at.
    exists fq, ly3, S3, (ms_regs ms), mem2, (with_vm_backing (m_vm_lazy md2) mat md2), k, acc.
    split; [unfold cfg_at, w64; reflexivity|].
    split; [exact HFRM0|].
    split; [exact HBASE|]. split; [exact HJ2|]. split; [exact HFR|]. split; [exact Hk|].
    split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
    split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
    split.
    { unfold d_rL.
      split; [unfold spZ; rewrite Z2, (EE0 2%nat 2%bv eq_refl), P2; exact Q2|].
      split; [rewrite Z3, (EE0 3%nat 3%bv eq_refl), P3; exact Q3|].
      split; [rewrite Z4, (EE0 4%nat 4%bv eq_refl), P4; exact Q4|].
      split; [rewrite Z8, (EE0 8%nat 8%bv eq_refl), P8; exact Q8|].
      split; [rewrite Z9, (EE0 9%nat 9%bv eq_refl), P9; exact Q9|].
      split; [rewrite Z19, (EE0 19%nat 19%bv eq_refl), P19; exact Q19|].
      split; [rewrite Z18, (EE0 18%nat 18%bv eq_refl), P18; exact Q18|].
      split; [rewrite Z20, (EE0 20%nat 20%bv eq_refl), P20; exact Q20|].
      rewrite Z27, (EE0 27%nat 27%bv eq_refl), P27; exact Q27. }
    split.
    { cbv beta. split; [rewrite Z24, (EE0 24%nat 24%bv eq_refl), P24; exact Q24|].
      split; [rewrite Z23, E33; reflexivity|].
      rewrite Z22, (EE0 22%nat 22%bv eq_refl), P22; exact Q22. }
    split.
    { cbv beta. split.
      { split; [split; apply KV; first [lia | assumption] |].
        split; apply KV; first [lia | assumption]. }
      split.
      { split; [exact (proj1 HTAB)|].
        apply KG; [unfold d_obj, dobj_off; lia | | | | exact HGT];
          rewrite length_map, HLT1; change (Z.of_nat 400) with 400; unfold d_obj, dobj_off; lia. }
      split.
      { split; [exact Hr2|].
        pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 buf (Z.max (slot_ser_defs.ser_cap op) 1) DFRAME_CLASS
          (c_fpos cx) HAR3 Hinb HFin3) as HSEP.
        unfold zdisjoint in HSEP. cbn [fst snd] in HSEP. rewrite EFA3 in HSEP.
        change (fs_frame_bytes DFRAME_CLASS) with 4096 in HSEP.
        apply KG; [lia | | | | exact HGB]; rewrite Lb; unfold d_obj, dobj_off; lia. }
      split; [exact HJR|]. split; [exact HVP|]. split.
      { apply KG; [unfold d_obj, dobj_off; lia | | | | exact HOO]; unfold d_obj, dobj_off; lia. }
      split; [split; [exact Hp|]; split; apply KV; first [lia | assumption] |].
      split; [apply KV; first [lia | assumption] |].
      split.
      { apply KG; [unfold d_obj, dobj_off; lia | | | | exact HUSED]; rewrite LU;
          change (Z.of_nat 32) with 32; unfold d_obj, dobj_off; lia. }
      rewrite HMB. cbn [fst snd]. split; [exact HOWID2|].
      right. split; [reflexivity|].
      apply KG; [unfold d_obj, dobj_off; lia | | | | exact HTOK3]; rewrite length_app; cbn [length];
        unfold d_obj, dobj_off; lia. }
    split; [split; apply KV; first [lia | assumption] |].
    exact HBODY2. }
  try rewrite (proj2 (Z.eqb_eq _ _) Hb0) in R10.
  assert (V10 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit 0) = getr regs 10)
    by (rewrite R10; reflexivity).
  assert (V21 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 529 (271 + 6 * p)) = getr regs 21).
  { cbn [sv_denot]. rewrite U529, R21, (pfxd_sh13 cx p HFB8). reflexivity. }
  assert (V25 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 516 (2174 + 48 * p)) = getr regs 25).
  { cbn [sv_denot]. rewrite U516, R25. unfold w64, d_obj, dobj_off. f_equal. lia. }
  assert (V26 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 516 (2173 + 48 * p)) = getr regs 26).
  { cbn [sv_denot]. rewrite U516, R26. unfold w64, d_obj, dobj_off. f_equal. lia. }
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (10%bv : bv 5) _ HS0 eq_refl V10) as HS1.
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (21%bv : bv 5) _ HS1 eq_refl V21) as HS2.
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (25%bv : bv 5) _ HS2 eq_refl V25) as HS3.
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (26%bv : bv 5) _ HS3 eq_refl V26) as HS4.
  pose proof (st_ok_pi_submem _ _ _ (pfxd_rsB p) HS4 (pfxd_narrow _ _) (pfxd_nwf p Hp8)) as HS.
  clear HS0 HS1 HS2 HS3 HS4.
  pose proof (pfxd_runB p Hp8) as RUNB. unfold pfxd_runB_stmt in RUNB.
  eapply RUNB; [exact HEI' | exact HS | exact HJ |].
  clear RUNB. intros R mat QR HJ1.
  apply (POSTB R mat);
    [ transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff A_TEXT 8292)); [exact (QR (1%bv : bv 5))|];
      rewrite (codeptr_val _ 8292 HEI'); reflexivity
    | unfold spZ; transitivity (bv_unsigned (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 60 0)));
        [rewrite (QR (2%bv : bv 5)); reflexivity|]; cbn [sv_denot]; rewrite U60, Z.add_0_r; apply unsigned_lit_small; lia
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 534 0)); [exact (QR (3%bv : bv 5))|];
      cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 3%bv 534 eq_refl); exact Rgp
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 535 0)); [exact (QR (4%bv : bv 5))|];
      cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 4%bv 535 eq_refl); exact Rtp
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 2 0)); [exact (QR (8%bv : bv 5))|];
      cbn [sv_denot]; rewrite d_env_old by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r;
      unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 60 0)); [exact (QR (9%bv : bv 5))|];
      cbn [sv_denot]; rewrite U60, Z.add_0_r; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 516 2000)); [exact (QR (10%bv : bv 5))|];
      cbn [sv_denot]; rewrite U516; unfold w64, d_obj, dobj_off; f_equal; lia
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit 24)); [exact (QR (11%bv : bv 5))|]; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff (A_OBJ 14) 0)); [exact (QR (12%bv : bv 5))|];
      cbn [sv_denot]; rewrite (img_env_atomP _ (A_OBJ 14) HEI' ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 563 0)); [exact (QR (13%bv : bv 5))|];
      cbn [sv_denot]; rewrite pfxd_e563, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 564 0)); [exact (QR (14%bv : bv 5))|];
      cbn [sv_denot]; rewrite pfxd_e564, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit WS_MASK)); [exact (QR (18%bv : bv 5))|]; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 32 0)); [exact (QR (19%bv : bv 5))|];
      cbn [sv_denot]; rewrite (E32' : ew _ 32 = _), Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit 32)); [exact (QR (20%bv : bv 5))|]; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 553 0)); [exact (QR (22%bv : bv 5))|];
      cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 22%bv 553 eq_refl); exact R22
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 555 0)); [exact (QR (24%bv : bv 5))|];
      cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 24%bv 555 eq_refl); exact R24
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 558 0)); [exact (QR (27%bv : bv 5))|];
      cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 27%bv 558 eq_refl); exact R27
    | exact HJ1 ].

- assert (HMA : a3f_model T1 p = (disco_json_text.s_unknown, disco_json_text.s_0x0))
    by (unfold a3f_model, a3f_ent; exact (slot_ser_P3.model_nobn T1 p Hhd1 Hb1)).
  try rewrite (proj2 (Z.eqb_neq _ _) Hb1) in R10.
  assert (V10 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit 18446744073709551615) = getr regs 10)
    by (rewrite R10; cbn [sv_denot]; unfold w64; apply bv_eq; reflexivity).
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (10%bv : bv 5) _ HS0 eq_refl V10) as HS1.
  pose proof (st_ok_pi_submem _ _ _ pfxd_rsA HS1 (pfxd_narrowA _ _) pfxd_awf) as HS.
  clear HS0 HS1.
  pose proof pfxd_runA as RUNA. unfold pfxd_runA_stmt in RUNA.
  eapply RUNA; [exact HEI' | exact HS | exact HJ |].
  clear RUNA. intros R mat QR HJ1.
  apply SRr_ret. exists (VAL (A_OBJ 11)).
  unfold f_md, a3f_st. split; [exact Hfrom|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, R, mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc.
  split; [reflexivity|]. split; [exact HFRM0|]. split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|].
  split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { unfold d_rL.
    split.
    { unfold spZ. transitivity (bv_unsigned (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 60 0)));
        [rewrite (QR (2%bv : bv 5)); reflexivity|]. cbn [sv_denot]. rewrite U60, Z.add_0_r. apply unsigned_lit_small. lia. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 534 0)); [exact (QR (3%bv : bv 5))|].
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 3%bv 534 eq_refl). exact Rgp. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 535 0)); [exact (QR (4%bv : bv 5))|].
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 4%bv 535 eq_refl). exact Rtp. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 2 0)); [exact (QR (8%bv : bv 5))|].
      cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r.
      unfold w64, d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 60 0)); [exact (QR (9%bv : bv 5))|].
      cbn [sv_denot]. rewrite U60, Z.add_0_r. reflexivity. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 32 0)); [exact (QR (19%bv : bv 5))|].
      cbn [sv_denot]. rewrite (E32' : ew _ 32 = _), Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit WS_MASK)); [exact (QR (18%bv : bv 5))|]. reflexivity. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit 32)); [exact (QR (20%bv : bv 5))|]. reflexivity. }
    transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 558 0)); [exact (QR (27%bv : bv 5))|].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 27%bv 558 eq_refl). exact R27. }
  split.
  { cbv beta.
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 555 0)); [exact (QR (24%bv : bv 5))|].
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 24%bv 555 eq_refl). exact R24. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 554 0)); [exact (QR (23%bv : bv 5))|].
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 23%bv 554 eq_refl). exact R23. }
    transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 553 0)); [exact (QR (22%bv : bv 5))|].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 22%bv 553 eq_refl). exact R22. }
  split.
  { cbv beta. split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
    split; [exact HVP|]. split; [exact HOO|].
    split; [exact HSL|]. split; [exact H408|]. split; [exact HUSED|].
    rewrite HMA. cbn [fst snd]. split; [exact HWID | left; split; reflexivity]. }
  split; [exact HSP0 | exact HBODY].
Qed.

Lemma a3f_pfxd_0 : seg_pfd_p_spec B MT XM_LIB RLO RHI tfib_K 0.
Proof. exact (a3f_pfxd 0 ltac:(lia)). Qed.

Lemma a3f_pfxd_1 : seg_pfd_p_spec B MT XM_LIB RLO RHI tfib_K 1.
Proof. exact (a3f_pfxd 1 ltac:(lia)). Qed.

Lemma a3f_pfxd_2 : seg_pfd_p_spec B MT XM_LIB RLO RHI tfib_K 2.
Proof. exact (a3f_pfxd 2 ltac:(lia)). Qed.

Lemma a3f_pfxd_3 : seg_pfd_p_spec B MT XM_LIB RLO RHI tfib_K 3.
Proof. exact (a3f_pfxd 3 ltac:(lia)). Qed.

Lemma a3f_pfxd_4 : seg_pfd_p_spec B MT XM_LIB RLO RHI tfib_K 4.
Proof. exact (a3f_pfxd 4 ltac:(lia)). Qed.

Lemma a3f_pfxd_5 : seg_pfd_p_spec B MT XM_LIB RLO RHI tfib_K 5.
Proof. exact (a3f_pfxd 5 ltac:(lia)). Qed.

Lemma a3f_pfxd_6 : seg_pfd_p_spec B MT XM_LIB RLO RHI tfib_K 6.
Proof. exact (a3f_pfxd 6 ltac:(lia)). Qed.

Lemma a3f_pfxd_7 : seg_pfd_p_spec B MT XM_LIB RLO RHI tfib_K 7.
Proof. exact (a3f_pfxd 7 ltac:(lia)). Qed.

End h.
End f.
End d.
