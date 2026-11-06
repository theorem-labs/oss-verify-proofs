(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 470 of its 537 lines of code are new or changed and 429 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3JsonC2Tk.v, with its module paths and module names changed; 129 of its 211 lines of code are new or changed and 455 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YC1i YC88 YI67 YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_age_c slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition jk_sx (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0
  | 19%nat => SOff 32 0 | 27%nat => SOff AT_SH 0
  | _ => SOff (AT_X + r) 0
  end.
Definition jk_sr : list sv := map jk_sx (seq 0 32).
Definition jk_vals (regs : bvmap 5 word) (ex : list word) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ ex.

Lemma jk_lnot : forall x, 0 <= x < 2 ^ 64 -> w64 (Z.lnot x) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
  intros x Hx. assert (Hl : Z.lnot x = - x - 1) by (unfold Z.lnot, Z.pred; lia).
  unfold w64. rewrite Hl. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  replace (2 ^ 64 - 1 - x) with ((- x - 1) + 1 * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma jk_nowin : forall (E : env) (rs : smem) (a : Z),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> ~ in_wrange E rs a.
Proof.
  intros E rs a Hf (r & Hin & Hr). rewrite forallb_forall in Hf.
  pose proof (Hf r Hin) as Hq. apply Z.leb_le in Hq. lia.
Qed.

Lemma jk_apres_grow : forall (Hh : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict Hh m) (mrestrict Hh m') -> apresent Hh m a -> apresent Hh m' a.
Proof.
  intros Hh m m' a HG (Hh0 & b & Hb). split; [exact Hh0|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh0, Hb in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. exact (HG ltac:(discriminate) eq_refl).
Qed.

Lemma jk_nth_app : forall (l : list Z) (x : Z), 0 <= x < jlen l -> nth (Z.to_nat x) (l ++ [0]) 0 = jbyte l x.
Proof.
  intros l x Hx. unfold jbyte, jlen in *. rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma jk_in : forall (c : YP09.chunk) l, existsb (chunk_eqb c) l = true -> In c l.
Proof.
  intros c l H. apply existsb_exists in H as (x & Hx & He). apply chunk_eqb_eq in He. subst x. exact Hx.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma jk_mbyte_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a,
  d_kept P W m W' m' -> 0 <= a < 2 ^ 64 -> ~ P a -> mbyte SEGS (rd W' m') a = mbyte SEGS (rd W m) a.
Proof.
  intros P W m W' m' a HK Ha HP. pose proof (HK a Ha HP) as E. unfold aview in E.
  destruct (mbyte SEGS (rd W' m') a) as [b1|] eqn:E1; destruct (mbyte SEGS (rd W m) a) as [b2|] eqn:E2;
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma jk_val_mem_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a nb v,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat nb -> ~ P x) ->
  val_mem SEGS (rd W m) a nb v -> val_mem SEGS (rd W' m') a nb v.
Proof.
  intros P W m W' m' a nb v HK H0 H1 HP Hv k Hk.
  rewrite (jk_mbyte_kept P W m W' m'); [exact (Hv k Hk) | exact HK | lia |].
  apply HP. lia.
Qed.

Lemma jk_garr8_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a l,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length l) -> ~ P x) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
  intros P W m W' m' a l HK H0 H1 HP Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (jk_val_mem_kept P W m W' m'); [exact HK | lia | lia | | exact Hv].
  intros x Hx. apply HP. lia.
Qed.

Lemma jk_den : forall (E : env) (q : nat) v d, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff q d) = Z_to_bv 64 (v + d).
Proof. intros E q v d Hq Hv. cbn [sv_denot]. rewrite Hq, unsigned_lit_small by lia. reflexivity. Qed.

Lemma jk_den0 : forall (E : env) (q : nat) v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff q 0) = Z_to_bv 64 v.
Proof. intros E q v Hq Hv. cbn [sv_denot]. rewrite Hq, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. Qed.

Lemma jk_byte : forall (W : world SEGS) m (a : Z) (l : list Z) (jx : Z),
  garr8 SEGS (rd W m) a l -> 0 <= jx < Z.of_nat (length l) ->
  val_mem SEGS (rd W m) (a + jx) 1 (nth (Z.to_nat jx) l 0) /\ 0 <= nth (Z.to_nat jx) l 0 < 256.
Proof.
  intros W m a l jx Hg Hj.
  assert (Hn : (Z.to_nat jx < length l)%nat) by lia.
  destruct (Hg (Z.to_nat jx) Hn) as [Hv Hr]. rewrite Z2Nat.id in Hv by lia. split; assumption.
Qed.

Lemma jk_region_kept : forall E (m m' : word -> option byte) r,
  region_ok SEGS E m r -> region_wf r = true ->
  (forall x, base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
     mbyte SEGS m' x = mbyte SEGS m x) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E m' r.
Proof.
  intros E m m' r (H1 & H2 & H3 & H4) Hwf Hrd Hwr.
  apply region_wf_facts in Hwf as (_ & _ & Hci).
  split; [exact H1|]. split; [exact H2|]. split; [exact Hwr|].
  rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
  destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
  pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
  rewrite Hrd by lia. exact Hb2.
Qed.

Lemma jk_x : forall cx E regs ex j, (j < 32)%nat ->
  ew (d_env cx E (jk_vals regs ex)) (AT_X + j) = getr regs (Z_to_bv 5 (Z.of_nat j)).
Proof.
  intros cx E regs ex j Hj.
  rewrite d_env_x by (unfold jk_vals; rewrite length_app, length_map, length_seq; lia).
  unfold jk_vals. rewrite app_nth1 by (rewrite length_map, length_seq; exact Hj).
  set (f := fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))).
  transitivity (nth j (map f (seq 0 32)) (f 0%nat)).
  - apply nth_indep. rewrite length_map, length_seq. exact Hj.
  - rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma jk_xe : forall cx E regs ex j, (j < length ex)%nat ->
  ew (d_env cx E (jk_vals regs ex)) (AT_X + (32 + j)) = nth j ex (Z_to_bv 64 0).
Proof.
  intros cx E regs ex j Hj.
  rewrite d_env_x by (unfold jk_vals; rewrite length_app, length_map, length_seq; lia).
  unfold jk_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
  rewrite length_map, length_seq. f_equal. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma jk_regs_ok : forall cx E regs ex, d_E cx E -> d_rL B cx regs ->
  regs_ok (d_env cx E (jk_vals regs ex)) jk_sr regs.
Proof.
  intros cx E regs ex HE HL.
  destruct HE as (HER & H32 & _ & HA60 & _ & HSH).
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx))
    by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
  { rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  apply regs_ok_by_cases. intros r Hr.
  cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: try (rewrite getr_zero; reflexivity).
  all: rewrite Z.add_0_r; unfold d_env.
  all: first
    [ rewrite ew_havoc_old by (cbv; lia);
      first [ change AT_A with 60%nat in HA60; rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
            | change AT_STK with 2%nat; rewrite HS2, Z_to_bv_bv_unsigned; exact H8
            | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
            | change AT_SH with 529%nat in HSH; rewrite HSH; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H27 ]
    | unfold havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth jk_vals map seq app Nat.add AT_X AT_FL];
      match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
        let y := eval vm_compute in x in change x with y end;
      rewrite Z_to_bv_bv_unsigned; reflexivity ].
Qed.

Lemma jk_shent : forall ly S (W : world SEGS) mem md (E : env) (q : nat) (bp len lo hi : Z),
  AR SEGS B ly S W mem md -> In (bp, len) (ablocks B ly S) ->
  U E (SOff 32 0) = SHADOW_OFF -> 0 <= lo <= hi ->
  bp <= U E (SOff q 0) + lo -> U E (SOff q 0) + hi <= bp + req_size len ->
  shent_ok SEGS (SOff 32 0) E (rd W mem) (mkSHE q lo hi).
Proof.
  intros ly S W mem md E q bp len lo hi HAR Hin HB Hlh Hlo Hhi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
  eapply (shent_ok_of_range SEGS (w_H W) mem E (SOff 32 0) q bp (req_size len) (U E (SOff q 0)) lo hi).
  - exact (range_addressable_of_block SEGS B LAWS ly S W mem md bp len bp (req_size len) HAR Hin
             ltac:(lia) ltac:(lia)).
  - exact HB.
  - reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

Lemma jk_fin : forall (T0 T1 : list byte) now removed,
  reac_disco_table_age_c.age_post T0 now T1 removed -> 0 <= now < 2 ^ 64 ->
  exists fin, jfin_ok T1 now fin.
Proof.
  intros T0 T1 now removed HP Hnow.
  destruct HP as (LT & _ & _ & _ & _ & _ & TOK & _).
  destruct (jtext_facts T1 now LT TOK Hnow) as (os & HJ & Hn & Hws & Hl & Hinb).
  exists (disco_table_c.n_of T1, os). split; [exact HJ|]. split; [exact Hn|].
  split; [exact Hws|]. split; [exact Hl | exact Hinb].
Qed.

End h.
End f.
End d.
