(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module names changed; 960 of its 998 lines of code are new or changed and 7 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC45 YC81 YC88 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt DiscoEntSeat DiscoRo DiscoEntBodyStmt DiscoEntBody.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacBoxName ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb disco_box_name_model slot_ser_P3 slot_ser_Pq tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoArm3FieldCut DiscoArm3FieldCall DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoArm3FieldPH.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition PFXDR_OFF : Z := 0x20c4.

Definition pfxd_fcs (p : Z) : list YP09.chunk :=
  [YP09.mkChunk (2173 + 48 * p) (CVal 1 (SOff 563 0)); YP09.mkChunk (2174 + 48 * p) (CVal 1 (SOff 564 0))].
Definition pfxd_fa : list (nat * afact) := [(563%nat, mkAF 0 255 0); (564%nat, mkAF 0 255 0)].
Definition pfxd_vals (regs : bvmap 5 word) (T : list byte) (p : Z) : list word :=
  a3f_vals regs ++ [Z_to_bv 64 (disco_table_c.din_of T p); Z_to_bv 64 (disco_table_c.dout_of T p)].
Definition pfxd_T (a b : Z) : list Z := disco_json_text.dec a ++ [120] ++ disco_json_text.dec b.
Definition pfxd_srB (p : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (a3f_sr (-16)) (10%bv : bv 5) (SLit 0)) (19%bv : bv 5) (SOff 516 (2174 + 48 * p)))
    (21%bv : bv 5) (SOff 529 (271 + 6 * p))) (23%bv : bv 5) (SOff 516 (2173 + 48 * p))) (27%bv : bv 5) (SOff 529 (271 + 6 * p)).
Definition pfxd_rsB (p : Z) : smem := map (fun r => set_window r 0 0) (d_kregions dsh_md [] (pfxd_fcs p)).
Definition pfxd_ssB (p : Z) : sstate := mkSS BNR_OFF (pfxd_srB p) (pfxd_rsB p) None (d_facts pfxd_fa []).
Definition pfxd_finB (p : Z) : list sv :=
  [SLit 0; SOff A_TEXT 8388; SOff 60 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0; SOff 2 0;
   SOff 60 0; SOff 516 2000; SLit 24; SOff (A_OBJ 14) 0; SOff 563 0; SOff 564 0; SOff 546 0; SOff 547 0; SOff 548 0;
   SOff 32 0; SOff 516 (2174 + 48 * p); SLit WS_MASK; SOff 529 (271 + 6 * p); SOff 553 0; SOff 516 (2173 + 48 * p);
   SOff 555 0; SLit 32; SOff 557 0; SOff 529 (271 + 6 * p); SOff 559 0; SOff 560 0; SOff 561 0; SOff 562 0].
Definition pfxd_finA : list sv :=
  [SLit 0; SOff 532 0; SOff 60 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0; SOff 2 0;
   SOff 60 0; SLit 18446744073709551615; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0; SOff 546 0; SOff 547 0;
   SOff 548 0; SOff 32 0; SOff 550 0; SLit WS_MASK; SOff 552 0; SOff 553 0; SOff 554 0; SOff 555 0; SLit 32;
   SOff 557 0; SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0; SOff 562 0].
Definition pfxd_rsA : smem := map (fun r => set_window r 0 0) (d_kregions dsh_md [] []).
Definition pfxd_ssA : sstate :=
  mkSS BNR_OFF (sr_set (a3f_sr (-16)) (10%bv : bv 5) (SLit 18446744073709551615)) pfxd_rsA None (d_facts pfxd_fa []).

Ltac pfxd_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Ltac pfxd_emem HF :=
  apply functional_extensionality; let x := fresh "x" in intros x; apply HF;
  let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros (r & Hr & Hw); vm_compute in Hr;
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

Lemma pfxd_narrowA : forall fcs,
  submem (map (fun r => set_window r 0 0) (d_kregions dsh_md [] [])) (d_kregions dsh_md [] fcs ++ []).
Proof.
  intros fcs. unfold d_kregions. cbn [map app].
  apply submem_keep; [apply pfxd_sw|].
  apply submem_keep; [apply pfxd_sw|].
  apply submem_keep.
  { unfold subregion, set_window. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
    intros c Hc. rewrite app_nil_r in Hc. apply in_or_app. left. exact Hc. }
  apply submem_keep; [apply pfxd_sw|]. apply submem_keep; [apply pfxd_sw|]. apply submem_keep; [apply pfxd_sw|].
  apply submem_nil.
Qed.

Lemma pfxd_kwf : forall p, 0 <= p < 8 -> regions_wf (d_kregions dsh_md [] (pfxd_fcs p) ++ []) = true.
Proof.
  intros p Hp. assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma pfxd_nwf : forall p, 0 <= p < 8 ->
  regions_wf (map (fun r => set_window r 0 0) (d_kregions dsh_md [] (pfxd_fcs p))) = true.
Proof.
  intros p Hp. assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma pfxd_cin : forall r c, region_wf r = true -> In c (YP09.r_chunks r) ->
  YP09.r_lo r <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= YP09.r_hi r.
Proof.
  intros r c Hw Hc. apply region_wf_facts in Hw as (_ & _ & Hw).
  pose proof (proj1 (forallb_forall _ _) Hw c Hc) as H. unfold chunk_inside in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
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

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
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

Lemma pfxd_soff : forall (E : env) (n : nat) (z b : Z),
  bv_unsigned (ew E n) = b -> sv_denot E (SOff n z) = Z_to_bv 64 (b + z).
Proof. intros E n z b Hb. cbn [sv_denot]. rewrite Hb. reflexivity. Qed.

Lemma pfxd_regs_ok : forall (cx : dcx) (E : env) (so : Z) (regs : bvmap 5 word) (T : list byte) (p : Z),
  d_E cx E -> 0 <= d_A cx < 2 ^ 64 -> spZ regs = d_A cx + so ->
  getr regs 8 = w64 (d_S cx) -> getr regs 9 = w64 (d_A cx) -> getr regs 18 = w64 SHADOW_OFF ->
  getr regs 20 = w64 WS_MASK -> getr regs 25 = w64 32 ->
  regs_ok (d_env cx E (pfxd_vals regs T p)) (a3f_sr so) regs.
Proof.
  intros cx E so regs T p HE HA Hsp H8 H9 H18 H20 H25.
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
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r; exact H8
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18
    | exact H20
    | exact H25
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (pfxd_env_reg cx E regs T p x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Lemma pfxd_rok : forall E (m m' : word -> option byte) r,
  region_ok SEGS E m r ->
  (forall c i, In c (YP09.r_chunks r) -> 0 <= i < YP09.c_len c ->
     mbyte SEGS m' (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     mbyte SEGS m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E m' r.
Proof.
  intros E m m' r HR Hc Hw. unfold region_ok in HR |- *. cbv zeta in HR |- *.
  destruct HR as (H1 & H2 & _ & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact Hw|].
  rewrite Forall_forall in H4 |- *. intros c Hin i Hi.
  destruct (H4 c Hin i Hi) as (b & Hb & Hm). exists b. split; [exact Hb|].
  rewrite Hc; [exact Hm | exact Hin | exact Hi].
Qed.

Lemma pfxd_rok_ext : forall E (m m' : word -> option byte) r,
  region_ok SEGS E m r -> region_wf r = true ->
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E m' r.
Proof.
  intros E m m' r HR Hwf He Hw. apply (pfxd_rok E m m' r HR); [|exact Hw].
  intros c i Hc Hi. pose proof (pfxd_cin r c Hwf Hc) as Hci. apply He. lia.
Qed.

Lemma pfxd_frame_kept : forall (cx : dcx) h shf (W W' : world SEGS) (m m' : word -> option byte),
  0 <= d_A cx -> d_A cx + 472 <= 2 ^ 64 -> 0 <= d_FB cx -> d_FB cx + 4096 <= 2 ^ 47 ->
  d_frame cx h shf W m ->
  (forall a, (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) \/ (d_FB cx <= a < d_FB cx + 24) \/
     (d_FB cx + 4088 <= a < d_FB cx + 4096) \/ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  (forall a, (d_A cx <= a < d_A cx + 472) \/ (d_FB cx <= a < d_FB cx + 3072) \/
     (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) -> apresent (w_H W') m' a) ->
  d_frame cx h shf W' m'.
Proof.
  intros cx h shf W W' m m' HA0 HA1 HF0 HF1 (E & HE & HR & Hfl & H216 & H152) Hk Hp.
  pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
  assert (B2 : base_val E (Some AT_STK) = d_S cx).
  { unfold base_val, AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (BA : base_val E (Some AT_A) = d_A cx).
  { unfold base_val. rewrite E60. unfold w64. apply unsigned_lit_small. lia. }
  assert (BF : base_val E (Some AT_F) = d_FB cx).
  { unfold base_val. rewrite EF. unfold w64. apply unsigned_lit_small. lia. }
  assert (BS : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
  { unfold base_val. rewrite ESH. unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
  assert (KB : forall a, (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) \/
     (d_FB cx <= a < d_FB cx + 24) \/ (d_FB cx + 4088 <= a < d_FB cx + 4096) \/
     (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
     mbyte SEGS (mrestrict (w_H W') m') a = mbyte SEGS (mrestrict (w_H W) m) a)
    by (intros a Ha; apply (mbyte_of_aview SEGS); apply Hk; exact Ha).
  assert (PW : forall a, (d_A cx <= a < d_A cx + 472) \/ (d_FB cx <= a < d_FB cx + 3072) \/
     (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) -> writable_at SEGS (mrestrict (w_H W') m') a)
    by (intros a Ha; apply (apresent_writable SEGS); apply Hp; exact Ha).
  exists E. split; [exact HE|]. split.
  - unfold d_regions in HR |- *.
    pose proof (Forall_inv HR) as R1. apply Forall_inv_tail in HR.
    pose proof (Forall_inv HR) as R2. apply Forall_inv_tail in HR.
    pose proof (Forall_inv HR) as R3. apply Forall_inv_tail in HR.
    pose proof (Forall_inv HR) as R4.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (pfxd_rok_ext E _ _ _ R1 ltac:(vm_compute; reflexivity)).
      * cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2. intros a Ha. apply KB. left. lia.
      * cbn [YP09.r_wlo YP09.r_whi]. intros o Ho. lia.
    + apply (pfxd_rok_ext E _ _ _ R2 ltac:(vm_compute; reflexivity)).
      * cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BA. intros a Ha. apply KB. right; left. lia.
      * cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite BA. intros o Ho. apply PW. left. lia.
    + apply (pfxd_rok E _ _ _ R3).
      * intros c i Hc Hi.
        assert (WF3 : region_wf (YP09.mkRegion (Some AT_F) 0 24 0 0
          [YP09.mkChunk 0 (CVal 8 (SLit MAGIC_LIVE)); YP09.mkChunk 8 (CVal 8 (SOff (A_OBJ 2) 0));
           YP09.mkChunk 16 (CVal 8 (SOff (A_OBJ 3) 0))]) = true) by (vm_compute; reflexivity).
        pose proof (pfxd_cin _ c WF3 Hc) as Hci.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi] in Hci |- *. rewrite BF. apply KB. right; right; left. lia.
      * cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite BF. intros o Ho. apply PW. right; left.
        unfold DFRAME_SIZE in Ho. lia.
    + apply (pfxd_rok_ext E _ _ _ R4 ltac:(vm_compute; reflexivity)).
      * unfold fshadow_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BS.
        change (fs_frame_bytes DFRAME_CLASS / 8) with 512. intros a Ha. apply KB. right; right; right; right. lia.
      * unfold fshadow_region. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite BS. intros o Ho. apply PW.
        right; right. unfold DFRAME_SH in Ho. lia.
  - split.
    { rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W') m')); [exact Hfl|].
      intros kk Hkk. apply Hk. right; right; right; left. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
    split.
    + eapply (val_mem_kept SEGS (w_H W) (w_H W') m m'); [|exact H216].
      intros kk Hkk. apply Hk. right; left. change (Z.of_nat 8) with 8 in Hkk. lia.
    + eapply (val_mem_kept SEGS (w_H W) (w_H W') m m'); [|exact H152].
      intros kk Hkk. apply Hk. right; left. change (Z.of_nat 8) with 8 in Hkk. lia.
Qed.

Lemma pfxd_aview_garr8 : forall H (m : word -> option byte) a L j,
  garr8 SEGS (mrestrict H m) a L -> (j < length L)%nat -> aview SEGS H m (a + Z.of_nat j) = Some (nth j L 0).
Proof.
  intros H m a L j HG Hj. unfold aview. rewrite (garr8_mbyte SEGS (mrestrict H m) a L j HG Hj). cbn [option_map].
  destruct (HG j Hj) as [_ Hr]. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma pfxd_garr8_text : forall H (m : word -> option byte) d (T : list Z),
  (forall i, 0 <= i < Z.of_nat (length T) -> aview SEGS H m (d + i) = Some (nth (Z.to_nat i) T 0)) ->
  aview SEGS H m (d + Z.of_nat (length T)) = Some 0 ->
  garr8 SEGS (mrestrict H m) d (T ++ [0]).
Proof.
  intros H m d T HT H0 j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j (length T)) as [Hl | Hg].
  - rewrite app_nth1 by exact Hl.
    pose proof (HT (Z.of_nat j) ltac:(lia)) as Hv. rewrite Nat2Z.id in Hv.
    exact (val_mem1_of_aview SEGS H m (d + Z.of_nat j) (nth j T 0) Hv).
  - assert (Ej : j = length T) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    exact (val_mem1_of_aview SEGS H m (d + Z.of_nat (length T)) 0 H0).
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
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi AE2k.FF_got_canary AE2k.FF_canary YImgTop.IMG_LO YImgTop.IMG_TOP
    disco_fmt_lo disco_fmt_hi snp_cr (SIGMA DS___interceptor_trampoline_snprintf).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis SNPRO : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis SNPUN : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis DAIL : asink_img_laws SEGS B tfib_K.
Hypothesis DKCAN : ak_can_got tfib_K = AE2k.FF_got_canary /\ ak_canary tfib_K = AE2k.FF_canary.

Definition pfxd_runB_stmt (p : Z) : Prop :=
  forall (fq : YK11.FPState) (W : world SEGS) (E : env) (ms : machine_state) (mdc : Model)
    STK sp0 FP ly S W0 mem md own lyc Sc k (Q : world SEGS -> config -> Prop),
  img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E (pfxd_ssB p) (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  (forall (R : bvmap 5 word) (mat' : list word),
     (forall r, getr R r = sv_denot E (sr_get (pfxd_finB p) r)) ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     SRr SEGS W (mkCfg (YK11.mkst (fx := fq) R (Z_to_bv 64 (SIGMA DS___interceptor_trampoline_snprintf)) (ms_mem ms)
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
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & R26 & (HBR & R10) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY).
destruct HY as (HPYK & Hhd & HWID & HTOKc).
pose proof HPYK as (HSL & H392 & H408 & HUSED).
pose proof HSL as (Hp & H368 & H336).
pose proof HBR as (R19 & R21 & R22 & R23 & R24 & R27).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (a3f_count T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof HTOK1 as (_ & _ & _ & HT4).
destruct (HT4 p ltac:(lia)) as (Hhd01 & Hhd40 & _).
assert (Hhd1 : disco_table_c.hd_of T1 p = 1) by lia.
destruct (Hhd40 Hhd1) as (Hdi40 & Hdo40).
assert (Rdi : 0 <= disco_table_c.din_of T1 p < 256) by exact (slot_ser_Pq.u1_range T1 (48 * p + 13)).
assert (Rdo : 0 <= disco_table_c.dout_of T1 p < 256) by exact (slot_ser_Pq.u1_range T1 (48 * p + 14)).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof ASAN_CEIL_range as Hceil. unfold ASAN_CEIL in Hceil.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
pose proof (d_E_env cx E (pfxd_vals regs T1 p) HE) as HE'.
pose proof HE' as (EE' & E32' & HEI' & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E (pfxd_vals regs T1 p)) 60) = d_A cx).
{ rewrite (E60' : ew _ 60 = _). unfold w64. apply unsigned_lit_small. lia. }
assert (U516 : bv_unsigned (ew (d_env cx E (pfxd_vals regs T1 p)) 516) = d_FB cx).
{ rewrite (EF' : ew _ 516 = _). unfold w64. apply unsigned_lit_small. lia. }
assert (U529 : bv_unsigned (ew (d_env cx E (pfxd_vals regs T1 p)) 529) = shadow_addr (d_FB cx)).
{ rewrite (ESH' : ew _ 529 = _). unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
assert (SHB : 0 <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 <= alloc_ceiling)
  by (unfold shadow_addr, SHADOW_OFF; lia).
assert (SHX : shadow_addr (d_FB cx) + 512 <= d_FB cx \/ d_FB cx + 4096 <= shadow_addr (d_FB cx)).
{ unfold in_app, kLowShadowBeg, kHighMemBeg in GFapp. unfold shadow_addr, SHADOW_OFF.
  destruct GFapp as (_ & [G | [G _]]); [right | left]; lia. }
assert (Hregs : regs_ok (d_env cx E (pfxd_vals regs T1 p)) (a3f_sr (-16)) regs)
  by (apply pfxd_regs_ok; [exact HE | lia | exact Rsp | exact R8 | exact R9 | exact R18 | exact R20 | exact R25]).
assert (HGf : facts_ok (d_env cx E (pfxd_vals regs T1 p)) (d_facts pfxd_fa [])).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (pfxd_vals regs T1 p) pfxd_fa [] HCTX HE); [|exact I].
  cbn [pfxd_fa atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite pfxd_e563, pfxd_e564. rewrite !unsigned_lit_small by lia. rewrite Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia. }
assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E (pfxd_vals regs T1 p)) (rd W mem3) (d_FB cx)) (pfxd_fcs p)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS _ _ (d_FB cx) (2173 + 48 * p) 1%N (SOff 563 0) (disco_table_c.din_of T1 p)).
    + cbn [sv_denot]. rewrite pfxd_e563, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + replace (d_FB cx + (2173 + 48 * p)) with (d_obj cx OT + (48 * p + 13)) by (unfold d_obj, dobj_off; lia).
      exact (ReacDiscoTableAge.age_val (rd W mem3) T1 (d_obj cx OT) (48 * p + 13) 1 HGT ltac:(lia)
        ltac:(rewrite HLT1; lia)).
  - apply (chunk_ok_val SEGS _ _ (d_FB cx) (2174 + 48 * p) 1%N (SOff 564 0) (disco_table_c.dout_of T1 p)).
    + cbn [sv_denot]. rewrite pfxd_e564, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + replace (d_FB cx + (2174 + 48 * p)) with (d_obj cx OT + (48 * p + 14)) by (unfold d_obj, dobj_off; lia).
      exact (ReacDiscoTableAge.age_val (rd W mem3) T1 (d_obj cx OT) (48 * p + 14) 1 HGT ltac:(lia)
        ltac:(rewrite HLT1; lia)). }
assert (U32 : bv_unsigned (ew (d_env cx E (pfxd_vals regs T1 p)) 32) = SHADOW_OFF)
  by (rewrite (E32' : ew _ 32 = _); unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E BNR_OFF (a3f_sr (-16)) (pfxd_vals regs T1 p) []
  (pfxd_fcs p) [] (d_facts pfxd_fa []) HCTX HE HREG HFLAG Hregs HGf (Forall_nil _) Hfcs (Forall_nil _) I (Forall_nil _)
  (pfxd_kwf p Hp8)) as HS0.
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
    getr R 18 = w64 SHADOW_OFF -> getr R 20 = w64 WS_MASK -> getr R 24 = w64 (d_obj cx OT + 48 * p) ->
    getr R 25 = w64 32 -> getr R 26 = w64 buf ->
    ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 (with_vm_backing (m_vm_lazy md3) mat1 md3) k ->
    SRr SEGS W (mkCfg (YK11.mkst (fx := fq) R (Z_to_bv 64 (SIGMA DS___interceptor_trampoline_snprintf)) mem3
      (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md3) mat1 md3))
      (fun W' c' => exists mp, f_md B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W' c')).
  { intros R mat1 Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q18 Q20 Q24 Q25 Q26 HJ1.
    set (md1 := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
    pose proof (DiscoEntBody.can_got_rdword B tfib_K ly3 S3 W mem3 md1 DAIL (proj1 DKCAN) (proj2 DKCAN) (proj1 HJ1)) as HG1.
    pose proof (DiscoEntBody.can_rdword cx W mem3 HCAN) as HG2.
    pose proof (DCRO LAWS (conj DRO (conj GM (HV))) ly3 S3 W mem3 md1 (proj1 HJ1) HIMG) as HCONST.
    destruct HCONST as (_ & _ & _ & HSTR & _).
    destruct HSTR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HSC14 & _) & _).
    destruct HSC14 as (Hc14 & HG14 & Hf14 & Hf63 & Hl32 & HAM14 & HRA14 & HHV14 & _ & HIM14).
    assert (HSN : SNPRINTF_STK = 11776) by reflexivity.
    assert (A1 : (d_A cx - d_S cx) mod 16 = 0) by lia.
    assert (A2 : d_A cx - d_S cx <= 0) by lia.
    assert (A3 : SNPRINTF_STK - (d_A cx - d_S cx) <= LLVMF_STK) by (rewrite HSN; unfold LLVMF_STK; lia).
    assert (Hsp0 : spZ R = d_S cx + (d_A cx - d_S cx)) by lia.
    assert (A6 : YK0s.ret_ok (getr R 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [unfold PFXDR_OFF; lia | reflexivity]).
    assert (A7 : snp_ctx W mem3 (spZ R) (d_obj cx OWID) 24).
    { apply (snp_ctx_ok B W mem3 (spZ R) (d_obj cx OWID) 24 SNPRO SNPUN HIMG (ex_intro _ (c_canary cx) (conj HG1 HG2))).
      - rewrite Q2, HSN. unfold off_img, IMG_LO, IMG_TOP. lia.
      - unfold off_img in GFoff |- *. unfold d_obj, dobj_off. lia. }
    assert (A8 : fmt_at (aview SEGS (w_H W) mem3) (snp_out SNPRINTF_STK (spZ R) (d_obj cx OWID) 24)
      (VAL (A_OBJ 14)) a3f_fmt_wid).
    { pose proof (pa_img_range _ (HIM14 (VAL (A_OBJ 14)) ltac:(simpl; lia))) as I0.
      pose proof (pa_img_range _ (HIM14 (VAL (A_OBJ 14) + 5) ltac:(simpl; lia))) as I5.
      unfold IMG_LO, IMG_TOP in I0, I5.
      unfold fmt_at, a3f_fmt_wid. split; [exact Hf14|]. split.
      { intros i0 Hi0. simpl in Hi0.
        pose proof (pfxd_aview_garr8 (w_H W) mem3 _ _ (Z.to_nat i0) HG14 ltac:(simpl; lia)) as Hv.
        rewrite Z2Nat.id in Hv by lia. exact Hv. }
      split.
      { unfold snp_out. rewrite Q2, HSN.
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
          simpl; unfold d_obj, dobj_off; unfold off_img in GFoff; unfold IMG_LO, IMG_TOP in GFoff; lia. }
      split; [exact HAM14|]. split; [exact HRA14 | exact HHV14]. }
    assert (A9 : pf_parse a3f_fmt_wid = Some [Pd; PLit 120; Pd]) by (vm_compute; reflexivity).
    assert (A10 : Forall pf_disco_piece [Pd; PLit 120; Pd])
      by (repeat (apply Forall_cons; [exact I|]); apply Forall_nil).
    assert (A11 : va_words R (aview SEGS (w_H W) mem3) (spZ R) [] (map (argZ R) [3; 4; 5; 6; 7])).
    { unfold va_words. split; [rewrite app_nil_r; reflexivity|]. intros i0 Hi0. cbn in Hi0. lia. }
    assert (A12 : spZ R + 8 * Z.of_nat (length (@nil Z)) <= d_S cx) by (cbn [length Z.of_nat]; rewrite Q2; lia).
    assert (A13 : Forall (zdisjoint (spZ R, 8 * Z.of_nat (length (@nil Z))))
      (snp_out SNPRINTF_STK (spZ R) (d_obj cx OWID) 24)).
    { unfold snp_out. rewrite Q2, HSN. cbn [length Z.of_nat].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
        unfold d_obj, dobj_off; lia. }
    assert (G3 : argZ R 3 = disco_table_c.din_of T1 p).
    { unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite Q13. unfold w64. apply unsigned_lit_small. lia. }
    assert (G4 : argZ R 4 = disco_table_c.dout_of T1 p).
    { unfold argZ. replace (Z_to_bv 5 (10 + 4)) with (14%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite Q14. unfold w64. apply unsigned_lit_small. lia. }
    assert (A14 : pf_args_asan (aview SEGS (w_H W) mem3) (snp_out SNPRINTF_STK (spZ R) (d_obj cx OWID) 24)
      (map (argZ R) [3; 4; 5; 6; 7]) [AInt (disco_table_c.din_of T1 p); AInt (disco_table_c.dout_of T1 p)]).
    { cbn [map pf_args_asan pf_arg_asan]. rewrite G3, G4.
      split; [split; [lia | reflexivity]|]. split; [split; [lia | reflexivity] | exact I]. }
    assert (HTt : pf_text [Pd; PLit 120; Pd] [AInt (disco_table_c.din_of T1 p); AInt (disco_table_c.dout_of T1 p)] =
      Some (pfxd_T (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p))) by (apply pfxd_text; lia).
    assert (A16 : 1 <= 24 < 2 ^ 31) by lia.
    assert (A17 : Z.of_nat (length (pfxd_T (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p))) < 2 ^ 31 - 1)
      by lia.
    assert (A18 : 0 < d_obj cx OWID) by (unfold d_obj, dobj_off; lia).
    assert (A19 : d_obj cx OWID + 24 <= 2 ^ 63) by (unfold d_obj, dobj_off; lia).
    assert (A20 : pairwise zdisjoint (snp_out SNPRINTF_STK (spZ R) (d_obj cx OWID) 24)).
    { unfold snp_out. rewrite Q2, HSN. cbn [pairwise].
      split; [apply Forall_cons; [|apply Forall_nil]; unfold zdisjoint; cbn [fst snd]; unfold d_obj, dobj_off; lia|].
      split; [apply Forall_nil | exact I]. }
    assert (A21 : forall a, d_obj cx OWID <= a < d_obj cx OWID + 24 ->
      awr_byte LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
        [(DFRAME_CLASS, c_fpos cx)] a /\ ~ (spZ R - SNPRINTF_STK <= a < spZ R)).
    { intros a Ha. unfold d_obj, dobj_off in Ha.
      split; [exact (proj1 (HAWRF a ltac:(unfold DFRAME_SIZE; lia))) | rewrite Q2, HSN; lia]. }
    assert (A22 : amem_range (d_obj cx OWID) (24 + 8)).
    { unfold amem_range, d_obj, dobj_off. unfold in_app in GFapp.
      unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *. lia. }
    assert (A23 : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF (d_obj cx OWID) 24).
    { change (d_obj cx OWID) with (d_FB cx + 2000).
      apply (pfxd_ra_frame cx dsh_md W mem3 2000 24 HSHD); [lia | lia | lia | lia |].
      intros kk Hkk. assert (Hk3 : kk = 250 \/ kk = 251 \/ kk = 252) by lia.
      destruct Hk3 as [-> | [-> | ->]]; vm_compute; reflexivity. }
    assert (A24 : shadow_hull_vis (aview SEGS (w_H W) mem3) (d_obj cx OWID) 24).
    { change (d_obj cx OWID) with (d_FB cx + 2000).
      apply (pfxd_hull_frame cx dsh_md W mem3 2000 24 HSHD); lia. }
    assert (Vf14 : VAL (A_OBJ 14) = 0x20fe0) by exact (pa_obj_val 14 ltac:(vm_compute; lia)).
    assert (A25 : disco_fmt_lo <= VAL (A_OBJ 14)) by (rewrite Vf14; unfold disco_fmt_lo; lia).
    assert (A26 : VAL (A_OBJ 14) + Z.of_nat (length a3f_fmt_wid) + 1 <= disco_fmt_hi)
      by (rewrite Vf14; unfold disco_fmt_hi; change (length a3f_fmt_wid) with 5%nat; lia).
    assert (A27 : a3f_fmt_wid <> []) by (unfold a3f_fmt_wid; discriminate).
    eapply SRr_bind.
    { exact (aj_snprintf_at B LAWS ASNPRINTF fq W R mem3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md1 k (d_obj cx OWID) 24 (VAL (A_OBJ 14)) a3f_fmt_wid
        [Pd; PLit 120; Pd] [] (map (argZ R) [3; 4; 5; 6; 7])
        [AInt (disco_table_c.din_of T1 p); AInt (disco_table_c.dout_of T1 p)]
        (pfxd_T (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p)) (d_A cx - d_S cx)
        HJ1 Q10 Q11 Q12 Hsp0 A1 A2 A3 Q3 Q4 A6 A7 A8 A9 A10 A11 A12 A13 A14 HTt A16 A17 A18 A19 A20 A21 A22 A23 A24
        A25 A26 A27 I I Hfrm0 HIMG). }
    cbv beta. intros W2 c2 _ (-> & fq2 & regs2 & mem2 & md2 & -> & Hfrm2 & HJ2 & HP2 & Hsame & Hres & Heff & Hz & Hfr2 & Hpres2).
    rewrite Z.min_l in Heff, Hz by lia.
    assert (HOWID2 : garr8 SEGS (rd W mem2) (d_obj cx OWID)
      (pfxd_T (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p) ++ [0]))
      by exact (pfxd_garr8_text (w_H W) mem2 (d_obj cx OWID) _ Heff Hz).
    assert (KU : forall a, 0 <= a < 2 ^ 64 -> ~ (d_obj cx OWID <= a < d_obj cx OWID + 24) ->
      ~ (d_A cx - 11776 <= a < d_A cx) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
    { intros a Ha H1 H2. apply Hfr2; [exact Ha | lia | rewrite Q2, HSN; exact H2]. }
    assert (HCTX2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem2 md2 k) by exact (conj HBASE (conj HJ2 HFR)).
    pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem2 md2 k HCTX2)
      as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres2 & GFsh2 & GSTK2 & _ & _ & _ & _).
    assert (HFRM2 : d_frame cx h dsh_md W mem2).
    { apply (pfxd_frame_kept cx h dsh_md W W mem3 mem2); [lia | lia | lia | lia | exact HFRM | |].
      - intros a Ha. apply KU; destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]]; unfold d_obj, dobj_off; lia.
      - intros a [Ha | [Ha | Ha]].
        + apply GSTK2. unfold LLVMF_STK. lia.
        + apply GFpres2. lia.
        + replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia. apply GFsh2. lia. }
    assert (HSHD2 : d_shadow cx dsh_md W mem2).
    { intros kk Hkk. unfold DFRAME_SH in Hkk.
      rewrite (KU (shadow_addr (d_FB cx) + kk)) by (unfold d_obj, dobj_off; lia).
      apply HSHD. unfold DFRAME_SH. lia. }
    assert (HBODY2 : d_body B cx h n (a3_xb buf op) dsh_md ly3 S3 W mem2).
    { apply (d_body_rt B cx h n n (a3_xb buf op) dsh_md dsh_md ly3 S3 W mem3 mem2 (d_A cx - 11776) (d_A cx)
        (fun a => d_objr cx OWID a \/ (d_A cx - 11776 <= a < d_A cx)) HBODY).
      - unfold LLVMF_STK. lia.
      - lia.
      - intros a [Ha | Ha]; [right | left; exact Ha].
        unfold d_objr, d_obj, dobj_off, dobj_size in Ha.
        pose proof HGEO as (_ & _ & _ & _ & _ & _ & G7 & G8).
        change (fs_frame_bytes DFRAME_CLASS) with 4096 in G7, G8.
        unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size.
        intros [X | [X | [X | [X | [X | [X | [X | X]]]]]]];
          [ lia | lia | lia | lia
          | destruct G7 as [G7 | G7]; lia
          | destruct X as (Xn & X); destruct (G8 Xn) as (_ & _ & G9 & _); destruct G9 as [G9 | G9]; lia
          | destruct X as (X & _);
            exact (off_img_not_img (d_FB cx) (fs_frame_bytes DFRAME_CLASS) a HOFF
              ltac:(change (fs_frame_bytes DFRAME_CLASS) with 4096; lia) (in_roP_img a X))
          | exact (off_img_not_img (d_FB cx) (fs_frame_bytes DFRAME_CLASS) a HOFF
              ltac:(change (fs_frame_bytes DFRAME_CLASS) with 4096; lia) (proj2 (proj2 HCAN) a X)) ].
      - intros a Ha Hna. apply KU; [exact Ha | intros Hx; apply Hna; left; exact Hx | intros Hx; apply Hna; right; exact Hx].
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
    { intros a L H0 H1 H2 H3 Hg. apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem2 a L); [|exact Hg].
      intros x Hx. apply KU; lia. }
    rewrite Q1.
    pose proof HFRM2 as (E2 & HE2 & HREG2 & HFLAG2 & _ & _).
    pose proof HE2 as (EE2 & _).
    assert (P2 : getr regs2 2 = getr R 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
    assert (P3 : getr regs2 3 = getr R 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
    assert (P4 : getr regs2 4 = getr R 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
    assert (P8 : getr regs2 8 = getr R 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
    assert (P9 : getr regs2 9 = getr R 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
    assert (P18 : getr regs2 18 = getr R 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
    assert (P20 : getr regs2 20 = getr R 20) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
    assert (P24 : getr regs2 24 = getr R 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
    assert (P25 : getr regs2 25 = getr R 25) by exact (HP2 25 ltac:(unfold acallee_saved; lia)).
    assert (P26 : getr regs2 26 = getr R 26) by exact (HP2 26 ltac:(unfold acallee_saved; lia)).
    assert (Hregs2 : regs_ok (d_env cx E2 (a3f_vals regs2)) (a3f_sr 0) regs2).
    { apply (a3f_regs_ok cx E2 0 regs2 HE2); [lia | | | | | |].
      - unfold spZ. rewrite P2. fold (spZ R). lia.
      - rewrite P8. exact Q8.
      - rewrite P9. exact Q9.
      - rewrite P18. exact Q18.
      - rewrite P20. exact Q20.
      - rewrite P25. exact Q25. }
    pose proof (DSEAT LAWS PAL fq2 cx dsh_md ly3 S3 W regs2 mem2 md2 k E2 PFXDR_OFF (a3f_sr 0) (a3f_vals regs2) [] [] []
      (d_facts [] []) HCTX2 HE2 HREG2 HFLAG2 Hregs2
      (DFACTS LAWS cx ly3 S3 W mem2 md2 k E2 (a3f_vals regs2) [] [] HCTX2 HE2 I I)
      (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS2.
    pose proof (st_ok_pi_submem _ _ _ (map (fun r => set_window r 0 0) (d_kregions dsh_md [] [])) HS2
      (pfxd_narrow _ _) ltac:(vm_compute; reflexivity)) as HS3.
    clear HS2. cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HS3.
    pose proof (d_E_env cx E2 (a3f_vals regs2) HE2) as (_ & E32b & HEIb & E60b & EFb & _).
    assert (U60b : bv_unsigned (ew (d_env cx E2 (a3f_vals regs2)) 60) = d_A cx).
    { rewrite (E60b : ew _ 60 = _). unfold w64. apply unsigned_lit_small. lia. }
    assert (U516b : bv_unsigned (ew (d_env cx E2 (a3f_vals regs2)) 516) = d_FB cx).
    { rewrite (EFb : ew _ 516 = _). unfold w64. apply unsigned_lit_small. lia. }
    reshok_bx HS3 32%nat.
    pose proof (paj_run_to (fx := fq2) (PI := PI) B LAWS) as RUNTO.
    paj_run_to_tok RUNTO HS3 HJ2 SHOK Bspan MD_OFF; [pfxd_awr|].
    assert (Emem2 : ms_mem ms = mem2) by pfxd_emem HF.
    pmkst HS3. rewrite Emem2 in HJ2 |- *.
    pose proof (fun r => st_ok_pi_restrict_reg (w_H W) (d_env cx E2 (a3f_vals regs2)) _ ms r HS3) as QR.
    assert (U32b : bv_unsigned (ew (d_env cx E2 (a3f_vals regs2)) 32) = SHADOW_OFF)
      by (rewrite (E32b : ew _ 32 = _); unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
    pose proof HSP1 as ((H232 & H344) & H224 & H248).
    pose proof HBUF as (Hr2 & HGB).
    pose proof HBLK as (HPerm0 & _).
    assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
    pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & _).
    pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 buf (Z.max (slot_ser_defs.ser_cap op) 1) DFRAME_CLASS
      (c_fpos cx) HAR3 Hinb HFin3) as HSEP.
    unfold zdisjoint in HSEP. cbn [fst snd] in HSEP. rewrite EFA3 in HSEP.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in HSEP.
    assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
      by (unfold a3_r; rewrite length_app; cbn [length]; lia).
    pose proof (DiscoArm3FieldPH.ph_objs_len buf vpad os HVP Lo6) as LO.
    apply SRr_ret. exists (d_obj cx OTOK).
    unfold f_md, a3f_st. split; [exact Hfrom|].
    unfold d_arm_at_pf, d_at.
    exists fq2, ly3, S3, (ms_regs ms), mem2, (with_vm_backing (m_vm_lazy md2) mat md2), k, acc.
    split; [reflexivity|]. split; [exact Hfrm2|].
    split; [exact HBASE|]. split; [exact HJ2|]. split; [exact HFR|]. split; [exact Hk|].
    split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
    split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
    split.
    { unfold d_rL.
      split.
      { unfold spZ. transitivity (bv_unsigned (sv_denot (d_env cx E2 (a3f_vals regs2)) (SOff 60 0)));
          [rewrite (QR (2%bv : bv 5)); reflexivity|].
        cbn [sv_denot]. rewrite U60b, Z.add_0_r. apply unsigned_lit_small. lia. }
      split.
      { transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SOff 534 0)); [exact (QR (3%bv : bv 5))|].
        cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (a3f_env_reg cx E2 regs2 3%bv 534 eq_refl), P3; exact Q3. }
      split.
      { transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SOff 535 0)); [exact (QR (4%bv : bv 5))|].
        cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (a3f_env_reg cx E2 regs2 4%bv 535 eq_refl), P4; exact Q4. }
      split.
      { transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SOff 2 0)); [exact (QR (8%bv : bv 5))|].
        cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). rewrite (EE2 2%nat 2%bv eq_refl), Z.add_0_r.
        unfold w64, d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
      split.
      { transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SOff 60 0)); [exact (QR (9%bv : bv 5))|].
        cbn [sv_denot]. rewrite U60b, Z.add_0_r. reflexivity. }
      split.
      { transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SOff 32 0)); [exact (QR (18%bv : bv 5))|].
        cbn [sv_denot]. rewrite U32b, Z.add_0_r. reflexivity. }
      split.
      { transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SLit WS_MASK)); [exact (QR (20%bv : bv 5))|].
        reflexivity. }
      transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SLit 32)); [exact (QR (25%bv : bv 5))|].
      reflexivity. }
    split.
    { cbv beta. split.
      { transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SOff 557 0)); [exact (QR (26%bv : bv 5))|].
        cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (a3f_env_reg cx E2 regs2 26%bv 557 eq_refl), P26; exact Q26. }
      split.
      { transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SOff 516 1856)); [exact (QR (22%bv : bv 5))|].
        cbn [sv_denot]. rewrite U516b. unfold w64, d_obj, dobj_off. f_equal; lia. }
      transitivity (sv_denot (d_env cx E2 (a3f_vals regs2)) (SOff 555 0)); [exact (QR (24%bv : bv 5))|].
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (a3f_env_reg cx E2 regs2 24%bv 555 eq_refl), P24; exact Q24. }
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
        apply KG; [lia | | | | exact HGB]; rewrite Lb; unfold d_obj, dobj_off; lia. }
      split; [exact HJR|]. split; [exact HVP|]. split.
      { apply KG; [unfold d_obj, dobj_off; lia | | | | exact HOO]; rewrite length_map, LO, Los;
          unfold d_obj, dobj_off; lia. }
      split; [split; [exact Hp|]; split; apply KV; first [lia | assumption] |].
      split; [apply KV; first [lia | assumption] |].
      split; [apply KV; first [lia | assumption] |].
      split.
      { apply KG; [unfold d_obj, dobj_off; lia | | | | exact HUSED]; rewrite (a3f_used_bytes (p + 1)) by lia;
          change (Z.of_nat 32) with 32; unfold d_obj, dobj_off; lia. }
      rewrite HMB. cbn [fst snd]. split; [exact HOWID2|].
      right. split; [reflexivity|].
      apply KG; [unfold d_obj, dobj_off; lia | | | | exact HTOK3]; rewrite length_app; cbn [length];
        unfold d_obj, dobj_off; lia. }
    split; [split; apply KV; first [lia | assumption] |].
    exact HBODY2. }
  assert (V10 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit 0) = getr regs 10).
  { rewrite R10. cbn [sv_denot]. unfold w64. apply bv_eq. vm_compute. reflexivity. }
  assert (V19 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 516 (2174 + 48 * p)) = getr regs 19).
  { cbn [sv_denot]. rewrite U516, R19. unfold w64, d_obj, dobj_off. f_equal. lia. }
  assert (V23 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 516 (2173 + 48 * p)) = getr regs 23).
  { cbn [sv_denot]. rewrite U516, R23. unfold w64, d_obj, dobj_off. f_equal. lia. }
  assert (V21 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 529 (271 + 6 * p)) = getr regs 21).
  { cbn [sv_denot]. rewrite U529, R21. unfold w64, shadow_addr, d_obj, dobj_off. f_equal. lia. }
  assert (V27 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 529 (271 + 6 * p)) = getr regs 27).
  { cbn [sv_denot]. rewrite U529, R27. unfold w64, shadow_addr, d_obj, dobj_off. f_equal. lia. }
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (10%bv : bv 5) _ HS0 eq_refl V10) as HS1.
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (19%bv : bv 5) _ HS1 eq_refl V19) as HS2.
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (21%bv : bv 5) _ HS2 eq_refl V21) as HS3.
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (23%bv : bv 5) _ HS3 eq_refl V23) as HS4.
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (27%bv : bv 5) _ HS4 eq_refl V27) as HS5.
  pose proof (st_ok_pi_submem _ _ _ (pfxd_rsB p) HS5 (pfxd_narrow _ _) (pfxd_nwf p Hp8)) as HS.
  clear HS0 HS1 HS2 HS3 HS4 HS5.
  pose proof (pfxd_runB p Hp8) as RUNB. unfold pfxd_runB_stmt in RUNB.
  eapply RUNB; [exact HEI' | exact HS | exact HJ |].
  clear RUNB. intros R mat QR HJ1.
  apply (POSTB R mat);
    [ transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff A_TEXT 8388)); [exact (QR (1%bv : bv 5))|];
      rewrite (codeptr_val _ 8388 HEI'); reflexivity
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
      cbn [sv_denot]; rewrite (HEI' (A_OBJ 14) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 563 0)); [exact (QR (13%bv : bv 5))|];
      cbn [sv_denot]; rewrite pfxd_e563, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 564 0)); [exact (QR (14%bv : bv 5))|];
      cbn [sv_denot]; rewrite pfxd_e564, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 32 0)); [exact (QR (18%bv : bv 5))|];
      cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit WS_MASK)); [exact (QR (20%bv : bv 5))|]; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 555 0)); [exact (QR (24%bv : bv 5))|];
      cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 24%bv 555 eq_refl); exact R24
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit 32)); [exact (QR (25%bv : bv 5))|]; reflexivity
    | transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 557 0)); [exact (QR (26%bv : bv 5))|];
      cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 26%bv 557 eq_refl); exact R26
    | exact HJ1 ].
- assert (HMA : a3f_model T1 p = (disco_json_text.s_unknown, disco_json_text.s_0x0))
    by (unfold a3f_model, a3f_ent; exact (slot_ser_P3.model_nobn T1 p Hhd1 Hb1)).
  assert (V10 : sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit 18446744073709551615) = getr regs 10).
  { rewrite R10. cbn [sv_denot]. unfold w64. apply bv_eq. vm_compute. reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (10%bv : bv 5) _ HS0 eq_refl V10) as HS1.
  pose proof (st_ok_pi_submem _ _ _ pfxd_rsA HS1 (pfxd_narrowA _) ltac:(vm_compute; reflexivity)) as HS.
  clear HS0 HS1.
  pose proof pfxd_runA as RUNA. unfold pfxd_runA_stmt in RUNA.
  eapply RUNA; [exact HEI' | exact HS | exact HJ |].
  clear RUNA. intros R mat QR HJ1.
  apply SRr_ret. exists (VAL (A_OBJ 11)).
  unfold f_md, a3f_st. split; [exact Hfrom|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, R, mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc.
  split; [reflexivity|]. split; [exact Hfrm0|].
  split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
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
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 32 0)); [exact (QR (18%bv : bv 5))|].
      cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit WS_MASK)); [exact (QR (20%bv : bv 5))|]. reflexivity. }
    transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SLit 32)); [exact (QR (25%bv : bv 5))|]. reflexivity. }
  split.
  { cbv beta.
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 557 0)); [exact (QR (26%bv : bv 5))|].
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 26%bv 557 eq_refl). exact R26. }
    split.
    { transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 553 0)); [exact (QR (22%bv : bv 5))|].
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 22%bv 553 eq_refl). exact R22. }
    transitivity (sv_denot (d_env cx E (pfxd_vals regs T1 p)) (SOff 555 0)); [exact (QR (24%bv : bv 5))|].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (pfxd_env_reg cx E regs T1 p 24%bv 555 eq_refl). exact R24. }
  split.
  { cbv beta. split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
    split; [exact HVP|]. split; [exact HOO|].
    split; [exact HSL|]. split; [exact H392|]. split; [exact H408|]. split; [exact HUSED|].
    rewrite HMA. cbn [fst snd]. split; [exact HWID | left; split; reflexivity]. }
  split; [exact HSP0 | exact HBODY].
Qed.

End h.
End f.
End d.
