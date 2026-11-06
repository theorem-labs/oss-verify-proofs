(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module names changed; 493 of its 540 lines of code are new or changed and 449 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3JsonC3.v; 380 of its 432 lines of code are new or changed and 488 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC81 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
JsonScalar DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonJs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb slot_ser_J2 slot_ser_Pq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition c1_fa : list (nat * afact) :=
  [(10%nat, mkAF 0 969 0); (18%nat, mkAF SB SB 0); (22%nat, mkAF 2 969 0); (25%nat, mkAF 32 32 0);
   (26%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF 4096 140737479966720 0); (34%nat, mkAF 33 255 0)].
Definition c1_cs : list acond :=
  [mkAC BC_LTU (SOff 10 0) (SOff 22 0); mkAC BC_LTU (SOff 10 1) (SOff 22 0)].
Definition c1_al : list (sv * sv) := [(SAlu ALU_ADD (SOff 26 0) (SOff 10 0), SOff 33 0)].
Definition c1_G : facts := mkFacts c1_fa c1_cs c1_al.
Definition c1_rA : YP09.region := YP09.mkRegion (Some 9%nat) 464 468 0 0 [YP09.mkChunk 464 (CVal 4 (SLit 1))].
Definition c1_rB : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 58)); YP09.mkChunk 1 (CVal 1 (SOff 34 0))].
Definition c1_ss : sstate := mkSS PAIR_OFF sr_atoms [c1_rA; c1_rB] None c1_G.
Definition c1_SH : list shent := [mkSHE 33 0 2].
Definition c1_Bx : sv := SOff 18 0.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma c1_byte : forall (W : world SEGS) m (bufv : Z) (l : list Z) (x : Z),
  garr8 SEGS (rd W m) bufv (l ++ [0]) -> 0 <= x < jlen l ->
  val_mem SEGS (rd W m) (bufv + x) 1 (jbyte l x) /\ 0 <= jbyte l x < 256.
Proof.
  intros W m bufv l x Hg Hx. unfold jlen in Hx.
  assert (Hn : (Z.to_nat x < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  destruct (Hg (Z.to_nat x) Hn) as [Hv Hr].
  rewrite app_nth1 in Hv, Hr by lia.
  rewrite Z2Nat.id in Hv by lia. unfold jbyte. split; [exact Hv | exact Hr].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis JSC : jsc_step_stmt B MT XM_LIB RLO RHI tfib_K.

Lemma c1_shent : forall ly S (W : world SEGS) mem md E (m : nat) p nn q lo hi,
  AR SEGS B ly S W mem md -> In (p, nn) (ablocks B ly S) ->
  U E c1_Bx = SHADOW_OFF -> U E (SOff m 0) = q -> p <= q + lo -> lo <= hi -> q + hi <= p + req_size nn ->
  shent_ok SEGS c1_Bx E (rd W mem) (mkSHE m lo hi).
Proof.
  intros ly S W mem md E m p nn q lo hi HAR Hin HB Hm Hlo Hlh Hhi.
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
  rewrite <- (aview_rd_of SEGS).
  destruct (al_shadow _ _ LAWS ly S W mem md p nn HAR Hin) as [Hbs _].
  destruct (al_blocks _ _ LAWS ly S W mem md p nn HAR Hin) as (_ & _ & _ & Happ & _).
  split.
  - destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
    eapply block_shadow_range; [exact Hbs | lia | lia].
  - intros a Ha. cbn [Z.min Z.max] in Ha.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Lemma c1_jcut_mono : forall cx h i n now op W0 c0 T0 T1 buf pc shf R R' X X' W c,
  (forall regs, R regs -> R' regs) -> (forall W1 m, X W1 m -> X' W1 m) ->
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf pc shf R X W c ->
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf pc shf R' X' W c.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf pc shf R R' X X' W c HR HX (HF & HAT).
  destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & accm & Hc & HCSR & HB & HJ & HFR & Hk & Hnev & HMO & Hacc &
    Hi & Hn & Hnow & HRL & (A22 & A26 & AR) & (B1 & B2 & B3 & BX) & HSP0 & HBODY).
  split; [exact HF|]. exists fq, ly3, S3, regs, mem3, md3, k, accm.
  split; [exact Hc|]. split; [exact HCSR|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact HRL|].
  split; [split; [exact A22 | split; [exact A26 | exact (HR regs AR)]]|].
  split; [split; [exact B1 | split; [exact B2 | split; [exact B3 | exact (HX W mem3 BX)]]]|].
  split; [exact HSP0 | exact HBODY].
Qed.

Definition c1_R (cx : dcx) (T1 : list byte) (now count : Z) : bvmap 5 word -> Prop :=
  fun regs => getr regs 19 = w64 (- a3_r T1 now) /\ getr regs 23 = w64 (jcur cx count) /\
    getr regs 24 = w64 (jcur cx count + 24) /\ getr regs 27 = w64 (jcur cx count + 48).

Definition c1_X (cx : dcx) (T1 : list byte) (now buf : Z) (fin : Z * list jobj) (ip j2 kk ks kl vk vs vl : Z)
  (cur c2 : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
  : world SEGS -> (word -> option byte) -> Prop :=
  fun W m => jfin_ok T1 now fin /\ 0 <= ip < j2 /\ 0 <= count /\ length acc = Z.to_nat count /\
    kk = 1 /\ 1 <= vk <= 3 /\
    jslot_upd (a3_text T1 now) (kk, ks, kl) (vk, vs, vl) cur = Some c2 /\
    jpairs_cont (a3_text T1 now) fin (json_ws (a3_text T1 now) j2) c2 count acc /\
    length cur = 6%nat /\ Forall (slot_ser_tokb.tok_inb (a3_text T1 now)) cur /\
    slot_ser_tokb.tok_inb (a3_text T1 now) (kk, ks, kl) /\
    slot_ser_tokb.tok_inb (a3_text T1 now) (vk, vs, vl) /\
    jmem cx buf count vpad (acc ++ [cur]) W m /\
    val_mem SEGS (rd W m) (d_A cx + 392) 8 (jcur cx count + 72) /\
    val_mem SEGS (rd W m) (d_A cx + 336) 8 (jcur cx count + 96) /\
    val_mem SEGS (rd W m) (d_A cx + 280) 8 (jcur cx count + 120) /\
    val_mem SEGS (rd W m) (d_A cx + 448) 8 (buf + ks) /\ val_mem SEGS (rd W m) (d_A cx + 456) 8 kl /\
    val_mem SEGS (rd W m) (d_A cx + 464) 4 kk.

Lemma c1_Rkeep : forall cx T1 now count rg rg', aregs_preserved rg rg' ->
  c1_R cx T1 now count rg -> c1_R cx T1 now count rg'.
Proof.
  intros cx T1 now count rg rg' HP (A19 & A23 & A24 & A27). unfold c1_R.
  assert (P19 : getr rg' 19 = getr rg 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
  assert (P23 : getr rg' 23 = getr rg 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
  assert (P24 : getr rg' 24 = getr rg 24) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
  assert (P27 : getr rg' 27 = getr rg 27) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
  rewrite P19, P23, P24, P27.
  split; [exact A19|]. split; [exact A23|]. split; [exact A24 | exact A27].
Qed.

Lemma c1_count_le : forall T1 now fin c2 j2 count acc,
  jfin_ok T1 now fin ->
  jpairs_cont (a3_text T1 now) fin (json_ws (a3_text T1 now) j2) c2 count acc -> count <= 7.
Proof.
  intros T1 now fin c2 j2 count acc (_ & Hfin & _) (f & i2 & c' & _ & HA).
  pose proof (jobjs_after_count (a3_text T1 now) fin i2 count acc c' HA). lia.
Qed.

Lemma c1_Xkeep : forall cx T1 now buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad W1 m1 W2 m2,
  c1_X cx T1 now buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad W1 m1 ->
  jsc_kept cx 424 W1 m1 W2 m2 ->
  c1_X cx T1 now buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad W2 m2.
Proof.
  intros cx T1 now buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad W1 m1 W2 m2 HX HK.
  destruct HK as (GF0 & GFA & GAS & GS & HKP).
  pose proof HX as (HFIN & Hip & Hc0 & Hla & Hkk & Hvk & Hupd & Hcont & Hlc & Htc & Htk & Htv & HMEM &
    V392 & V336 & V280 & V448 & V456 & V464).
  pose proof (c1_count_le T1 now fin c2 j2 count acc HFIN Hcont) as Hc7.
  destruct HMEM as (M408 & M368 & Lvpad & Gvpad & GOO & HAall).
  assert (GAlo : 16512 <= d_A cx) by (unfold TJSON_SCALAR_STK, ESTACK in *; lia).
  assert (HLoo : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur]))) = 144 * (count + 1)).
  { rewrite (slot_ser_Pq.objs_len buf vpad (acc ++ [cur]) Lvpad HAall).
    rewrite length_app. cbn [length]. rewrite Hla.
    rewrite Nat2Z.inj_mul, Nat2Z.inj_add, Z2Nat.id by exact Hc0.
    change (Z.of_nat 144) with 144. change (Z.of_nat 1) with 1. reflexivity. }
  assert (KV : forall off nb v, 0 <= off -> off + Z.of_nat nb <= 472 -> (off + Z.of_nat nb <= 424 \/ 444 <= off) ->
    val_mem SEGS (rd W1 m1) (d_A cx + off) nb v -> val_mem SEGS (rd W2 m2) (d_A cx + off) nb v).
  { intros off nb v H0 H1 H2 Hv.
    eapply (jsc_val_mem_kept _ W1 m1 W2 m2); [exact HKP | lia | lia | | exact Hv].
    intros x Hx [HQ | HQ]; destruct H2 as [H2 | H2]; unfold TJSON_SCALAR_STK, ESTACK in *; lia. }
  split; [exact HFIN|]. split; [exact Hip|]. split; [exact Hc0|]. split; [exact Hla|].
  split; [exact Hkk|]. split; [exact Hvk|]. split; [exact Hupd|]. split; [exact Hcont|].
  split; [exact Hlc|]. split; [exact Htc|]. split; [exact Htk|]. split; [exact Htv|].
  split.
  { split; [apply (KV 408 8%nat); [lia | lia | lia | exact M408]|].
    split; [apply (KV 368 8%nat); [lia | lia | lia | exact M368]|].
    split; [exact Lvpad|].
    split.
    { eapply (jsc_garr8_kept _ W1 m1 W2 m2); [exact HKP | lia | rewrite length_map, Lvpad; lia | | exact Gvpad].
      intros x Hx [HQ | HQ]; rewrite length_map, Lvpad in Hx;
        unfold TJSON_SCALAR_STK, ESTACK in *; lia. }
    split; [| exact HAall].
    eapply (jsc_garr8_kept _ W1 m1 W2 m2); [exact HKP | | | | exact GOO].
    - unfold d_obj, dobj_off. lia.
    - rewrite length_map, HLoo. unfold d_obj, dobj_off. unfold TJSON_SCALAR_STK, ESTACK in *. lia.
    - rewrite length_map, HLoo. intros x Hx [HQ | HQ]; unfold d_obj, dobj_off in Hx;
        unfold TJSON_SCALAR_STK, ESTACK in *; lia. }
  split; [apply (KV 392 8%nat); [lia | lia | lia | exact V392]|].
  split; [apply (KV 336 8%nat); [lia | lia | lia | exact V336]|].
  split; [apply (KV 280 8%nat); [lia | lia | lia | exact V280]|].
  split; [apply (KV 448 8%nat); [lia | lia | lia | exact V448]|].
  split; [apply (KV 456 8%nat); [lia | lia | lia | exact V456]|].
  apply (KV 464 4%nat); [lia | lia | lia | exact V464].
Qed.

Lemma c1_step : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (fin : Z * list jobj) (ip j kk ks kl : Z) (cur : jobj) (count : Z) (acc : list jobj) (vpad : list byte)
  (j2 vk vs vl : Z) (c2 : jobj) (W : world SEGS) (c : config),
  jpair_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c ->
  kk = 1 -> 0 <= j -> at_byte (a3_text T1 now) j 58 = true ->
  jscalar (a3_text T1 now) (j + 1) = Some (j2, vk, vs, vl) ->
  1 <= vk <= 3 -> ip < j2 ->
  jslot_upd (a3_text T1 now) (kk, ks, kl) (vk, vs, vl) cur = Some c2 ->
  jpairs_cont (a3_text T1 now) fin (json_ws (a3_text T1 now) j2) c2 count acc ->
  slot_ser_tokb.tok_inb (a3_text T1 now) (kk, ks, kl) ->
  slot_ser_tokb.tok_inb (a3_text T1 now) (vk, vs, vl) ->
  SRr SEGS W c (jsc_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf dsh_scr VAL_OFF (j + 1) 424
    (c1_R cx T1 now count) (c1_X cx T1 now buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad)).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad j2 vk vs vl c2 W c
  HP Hkk Hj0 Hcolon Hjs Hvkb Hipj2 Hupd Hcont Htk Htv.
destruct HP as (HFROM & HAT).
destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & accm & -> & HCSR & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R22 & R26 & R10 & R19 & R23 & R24 & R27) & (HSP1 & HTAB & HBUF & HXp) & HSP0 & HBODY).
destruct HXp as (HFIN & Hip0 & Hcount0 & Hlenacc & Hjsk & Hpf & Hlencur & Hcurtok & HMEM & V392 & V336 & V280 &
  V448 & V456 & V464).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HFIN as (HJR & Hfin8 & Hnows & Hlen969 & Hinb).
pose proof HBUF as (Hr2 & Hgbuf).
pose proof ASAN_CEIL_range as (Hceil0 & _). unfold ASAN_CEIL in Hceil0.
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
destruct (at_byte_true _ _ _ Hcolon) as (Hjlt & Hjb).
pose proof (jscalar_in (a3_text T1 now) (j + 1) j2 vk vs vl Hjs) as Hj1lt.
assert (Hj1r : j + 2 <= a3_r T1 now) by (unfold a3_r, jlen in *; lia).
pose proof (jno_ws_byte (a3_text T1 now) (j + 1) Hnows ltac:(unfold jlen, a3_r in *; lia)) as HV.
pose proof HBODY as (Tb & Gb & Lkb & Hbt & HFRM & HSHD & HOBJ & HBLK & _).
pose proof HBLK as (HPerm0 & _ & _ & _).
assert (Hinbuf : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof HJ as (HAR3 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0) as [Eq | Eq]; lia. }
rewrite Hreq in Hbceil, Hbapp.
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GWpres & _ & _ & _ & _).
unfold LLVMF_STK in GSlo.
pose proof (d_A_range cx ltac:(unfold MFRAME; lia)) as (GA1 & GA32). unfold MFRAME in GA1.
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (buf + j); Z_to_bv 64 (jbyte (a3_text T1 now) (j + 1))]))
  as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (E33 : ew E0 33 = Z_to_bv 64 (buf + j)).
{ rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 33%nat with (32 + 1)%nat.
  rewrite ew_Ereg_extra. reflexivity. }
assert (E34 : ew E0 34 = Z_to_bv 64 (jbyte (a3_text T1 now) (j + 1))).
{ rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 34%nat with (32 + 2)%nat.
  rewrite ew_Ereg_extra. reflexivity. }
assert (U9 : bv_unsigned (ew E0 9) = d_A cx).
{ rewrite (EE0 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. lia. }
assert (U10 : bv_unsigned (ew E0 10) = j).
{ rewrite (EE0 10%nat 10%bv eq_refl), R10. unfold w64. apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew E0 18) = SHADOW_OFF).
{ rewrite (EE0 18%nat 18%bv eq_refl), Rs2. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U22 : bv_unsigned (ew E0 22) = a3_r T1 now).
{ rewrite (EE0 22%nat 22%bv eq_refl), R22. unfold w64. apply unsigned_lit_small. lia. }
assert (U25 : bv_unsigned (ew E0 25) = 32).
{ rewrite (EE0 25%nat 25%bv eq_refl), Rs9. unfold w64. apply unsigned_lit_small. lia. }
assert (U26 : bv_unsigned (ew E0 26) = buf).
{ rewrite (EE0 26%nat 26%bv eq_refl), R26. unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E0 33) = buf + j) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E0 34) = jbyte (a3_text T1 now) (j + 1))
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (HG : facts_ok E0 c1_G).
{ split; [|split].
  - unfold c1_G, c1_fa. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U18, U22, U25, U26, U33, U34. rewrite Z.pow_0_r. rewrite !Z.mod_1_r.
    unfold SB, SHADOW_OFF in *.
    repeat split; try lia.
  - unfold c1_G, c1_cs. cbn [f_conds conds_ok].
    split; [|split; [|exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b];
      rewrite branch_ltu_U, !U_SOff, U10, U22;
      rewrite !zcanon_id by (unfold M64; lia); apply Z.ltb_lt; lia.
  - unfold c1_G, c1_al. cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite (U_add_off_atom E0 26 0 10 0 ltac:(unfold M64; lia) ltac:(unfold M64; lia)).
    rewrite U_SOff, U26, U10, U33. rewrite zcanon_id by (unfold M64; lia). lia. }
destruct (c1_byte W mem3 buf (a3_text T1 now) j Hgbuf ltac:(unfold jlen, a3_r in *; lia)) as (Hvj & _).
destruct (c1_byte W mem3 buf (a3_text T1 now) (j + 1) Hgbuf ltac:(unfold jlen, a3_r in *; lia)) as (Hvj1 & _).
rewrite Hjb in Hvj.
assert (HRA : region_ok SEGS E0 (rd W mem3) c1_rA).
{ unfold c1_rA, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E0 _ (d_A cx) 464 4 (SLit 1) 1).
  - cbn [sv_denot]. reflexivity.
  - lia.
  - lia.
  - cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite <- Hkk. exact V464. }
assert (HRB : region_ok SEGS E0 (rd W mem3) c1_rB).
{ unfold c1_rB, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS E0 _ (buf + j) 0 1 (SLit 58) 58).
    + cbn [sv_denot]. reflexivity.
    + lia.
    + lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact Hvj.
  - apply (chunk_ok_val SEGS E0 _ (buf + j) 1 1 (SOff 34 0) (jbyte (a3_text T1 now) (j + 1))).
    + cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
    + lia.
    + lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
      replace (buf + j + 1) with (buf + (j + 1)) by lia. exact Hvj1. }
assert (HPD : pairwise_disjoint E0 [c1_rA; c1_rB]).
{ cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c1_rA, c1_rB.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33.
  split; [split; [right; lia | exact I] | split; [exact I | exact I]]. }
assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 c1_ss
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PAIR_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold c1_ss. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HRA | constructor; [exact HRB | constructor]].
  - exact HPD.
  - exact HG. }
assert (SHOK : sh_ok SEGS c1_Bx c1_SH E0 (rd W mem3)).
{ unfold c1_SH. constructor; [|constructor].
  apply (c1_shent ly3 S3 W mem3 md3 E0 33%nat buf (Z.max (slot_ser_defs.ser_cap op) 1) (buf + j) 0 2
    HAR3 Hinbuf).
  - unfold c1_Bx. rewrite U_SOff, U18, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
  - rewrite U_SOff, U33, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  - lia.
  - lia.
  - rewrite Hreq. lia. }
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?a ?b ?cc ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' a b cc d e f g) end.
  intros a (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
assert (Emem : ms_mem ms = mem3).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Hr).
  cbn [In] in Hin. unfold c1_ss in Hin. cbn [ss_mem] in Hin.
  destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val c1_rA c1_rB] in Hr; lia. }
pmkst HS.
rewrite Emem. rewrite Emem in HJ.
rewrite pa_sigma_json_scalar.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite (EE0 2%nat 2%bv eq_refl) in Q2. rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
rewrite (EE0 4%nat 4%bv eq_refl) in Q4. rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
rewrite (EE0 9%nat 9%bv eq_refl) in Q9. rewrite (EE0 18%nat 18%bv eq_refl) in Q18.
rewrite (EE0 19%nat 19%bv eq_refl) in Q19. rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
rewrite (EE0 22%nat 22%bv eq_refl) in Q22. rewrite (EE0 23%nat 23%bv eq_refl) in Q23.
rewrite (EE0 24%nat 24%bv eq_refl) in Q24. rewrite (EE0 25%nat 25%bv eq_refl) in Q25.
rewrite (EE0 26%nat 26%bv eq_refl) in Q10. rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
rewrite (EE0 27%nat 27%bv eq_refl) in Q27. rewrite (EE0 22%nat 22%bv eq_refl) in Q12.
rewrite U10 in Q11. rewrite U9 in Q13.
apply SRr_ret.
unfold jsc_in, jcut.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, accm.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact HCSR|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite Q2; exact Rsp|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
  split; [rewrite Q9; exact Rs1|]. split; [rewrite Q18; exact Rs2|]. split; [rewrite Q20; exact Rs4|].
  rewrite Q25; exact Rs9. }
split.
{ split; [rewrite Q22; exact R22|]. split; [rewrite Q26; exact R26|].
  split; [unfold w64, VAL_OFF; exact Q1|].
  split; [rewrite Q10; exact R26|].
  split; [unfold w64; exact Q11|].
  split; [rewrite Q12; exact R22|].
  split; [unfold w64; exact Q13|].
  unfold c1_R.
  split; [rewrite Q19; exact R19|]. split; [rewrite Q23; exact R23|]. split; [rewrite Q24; exact R24|].
  rewrite Q27; exact R27. }
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
  unfold c1_X.
  split; [exact HFIN|]. split; [lia|]. split; [exact Hcount0|]. split; [exact Hlenacc|].
  split; [exact Hkk|]. split; [exact Hvkb|]. split; [exact Hupd|]. split; [exact Hcont|].
  split; [exact Hlencur|]. split; [exact Hcurtok|]. split; [exact Htk|]. split; [exact Htv|].
  split; [exact HMEM|].
  split; [exact V392|]. split; [exact V336|]. split; [exact V280|].
  split; [exact V448|]. split; [exact V456 | exact V464]. }
split; [exact HSP0 | exact HBODY].
Qed.

Theorem a3j_C1 : jseg_C1 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad W c HP.
destruct (jcut_x B MT XM_LIB RLO RHI tfib_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (m & HX).
destruct HX as (HFIN & Hip0 & Hcount0 & Hlenacc & Hjsk & Hpf & Hlencur & Hcurtok & HMEM & V392 & V336 & V280 &
  V448 & V456 & V464).
pose proof HFIN as (HJR & Hfin8 & Hnows & Hlen969 & Hinb).
destruct (jpairs_from_step (a3_text T1 now) fin ip cur count acc Hpf)
  as (j' & kk' & ks' & kl' & j2 & vk & vs & vl & c2 & E1 & Ekk & Ecol & E4 & E5 & Econt).
rewrite Hjsk in E1. injection E1 as <- <- <- <-.
pose proof (jscalar_lt (a3_text T1 now) ip j kk ks kl ltac:(lia) Hjsk) as Hipj.
assert (Hj0 : 0 <= j) by lia.
rewrite (json_ws_id (a3_text T1 now) j Hnows Hj0) in Ecol, E4.
rewrite (json_ws_id (a3_text T1 now) (j + 1) Hnows ltac:(lia)) in E4.
pose proof (jscalar_lt (a3_text T1 now) (j + 1) j2 vk vs vl ltac:(lia) E4) as Hj1j2.
pose proof (slot_ser_J2.jscalar_kind (a3_text T1 now) (j + 1) j2 vk vs vl E4) as Hvkb.
pose proof (slot_ser_tokb.jscalar_bnd (a3_text T1 now) ip j kk ks kl Hjsk ltac:(lia)) as (Bks & Bkl & Bkb & _).
pose proof (slot_ser_tokb.jscalar_bnd (a3_text T1 now) (j + 1) j2 vk vs vl E4 ltac:(lia)) as (Bvs & Bvl & Bvb & _).
assert (Htk : slot_ser_tokb.tok_inb (a3_text T1 now) (kk, ks, kl))
  by (right; cbn [fst snd]; lia).
assert (Htv : slot_ser_tokb.tok_inb (a3_text T1 now) (vk, vs, vl))
  by (right; cbn [fst snd]; lia).
eapply SRr_bind.
{ exact (c1_step cx h i n now op W0 c0 T0 T1 buf fin ip j kk ks kl cur count acc vpad j2 vk vs vl c2 W c
    HP Ekk Hj0 Ecol E4 Hvkb ltac:(lia) E5 Econt Htk Htv). }
intros W1 c1 _ Hin.
eapply SRr_mono.
{ exact (JSC cx h i n now op W0 c0 T0 T1 buf dsh_scr VAL_OFF (j + 1) 424 j2 vk vs vl
    (c1_R cx T1 now count) (c1_X cx T1 now buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad) W1 c1
    ltac:(unfold VAL_OFF; lia) ltac:(unfold VAL_OFF; reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(lia)
    ltac:(lia) E4 (fun rg rg' Hpr Hr => c1_Rkeep cx T1 now count rg rg' Hpr Hr)
    (fun W3 m3 W4 m4 Hx Hk => c1_Xkeep cx T1 now buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad
       W3 m3 W4 m4 Hx Hk) Hin). }
intros W2 c3 _ Hout.
exists j2, vk, vs, vl, c2.
unfold jval_in.
refine (c1_jcut_mono cx h i n now op W0 c0 T0 T1 buf VAL_OFF dsh_scr _ _ _ _ W2 c3 _ _ Hout).
- intros rg (G10 & G19 & G23 & G24 & G27). exact (conj G10 (conj G19 (conj G23 (conj G24 G27)))).
- intros W4 m4 (HXc & A424 & A432 & A440).
  destruct HXc as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 &
    K17 & K18 & K19).
  replace (d_A cx + 424 + 8) with (d_A cx + 432) in A432 by lia.
  replace (d_A cx + 424 + 16) with (d_A cx + 440) in A440 by lia.
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
  split; [exact K5|]. split; [exact K6|]. split; [exact K7|]. split; [exact K8|].
  split; [exact K9|]. split; [exact K10|]. split; [exact K11|]. split; [exact K12|].
  split; [exact K13|]. split; [exact K14|]. split; [exact K15|]. split; [exact K16|].
  split; [exact K17|]. split; [exact K18|]. split; [exact K19|].
  split; [exact A424|]. split; [exact A432 | exact A440].
Qed.

End h.
End f.
End d.
