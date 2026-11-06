(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 329 of its 381 lines of code are new or changed and 444 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i DiscoACjr ACj1 DiscoACja YC85s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoArm3 DiscoArm3JsonCut DiscoArm3JsonADefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition ja1_sx (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0
  | 18%nat => SOff 32 0
  | _ => SOff (AT_X + r) 0
  end.
Definition ja1_sr : list sv := map ja1_sx (seq 0 32).
Definition ja1_vals (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32).
Definition ja1_rs0 : smem := [YP09.mkRegion (Some AT_A) 0 472 0 0 dslot_chunks].

Lemma ja1_rs0_sub : forall pc sr G,
  submem ja1_rs0 (ss_mem (ss_d pc sr dsh_loop [] [] [] G)).
Proof.
intros pc sr G. unfold ja1_rs0. cbn [ss_d ss_mem d_kregions app].
apply submem_drop. apply submem_keep.
{ unfold subregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
  intros c Hc. rewrite app_nil_r. exact Hc. }
apply submem_nil.
Qed.

Lemma ja1_dsh_check :
  forallb (fun k => Z.eqb (dsh_ser (Z.of_nat k))
    (if (30 <=? Z.of_nat k) && (Z.of_nat k <? 192) then 0 else dsh_loop (Z.of_nat k))) (seq 0 384) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ja1_dsh : forall k, 0 <= k < 384 -> dsh_ser k = if (30 <=? k) && (k <? 192) then 0 else dsh_loop k.
Proof.
intros k Hk. pose proof ja1_dsh_check as H. rewrite forallb_forall in H.
specialize (H (Z.to_nat k) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply Z.eqb_eq in H. exact H.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ja1_apres_grow : forall (Hh : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict Hh m) (mrestrict Hh m') -> apresent Hh m a -> apresent Hh m' a.
Proof.
intros Hh m m' a HG (Hh0 & b & Hb). split; [exact Hh0|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh0, Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
exfalso. exact (HG ltac:(discriminate) eq_refl).
Qed.

Lemma ja1_region_kept : forall E (m m' : word -> option byte) r,
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

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis ASS00 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_00) 0.

Lemma ja1_regs_ok : forall cx E regs, d_E cx E -> d_rL B cx regs ->
  regs_ok (d_env cx E (ja1_vals regs)) ja1_sr regs.
Proof.
intros cx E regs HE HL.
destruct HE as (HER & H32 & _ & HA60 & _ & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
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
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | unfold havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth ja1_vals map seq Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ].
Qed.

Theorem a3j_A_S1 : jA_S1_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf W c [HFROM HAT].
destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HCSR & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & (R22 & R26) & (Hsp1 & Htab & Hbuf) & Hsp0 & Hbody).
pose proof Hbody as (T & G & Lk & H & Hframe & Hshadow & Hobjs & Hblocks & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (DSEAT LAWS PAL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E R10_OFF ja1_sr (ja1_vals regs) [] [] []
  (d_facts [] []) HCTX HdE Hregs Hflag (ja1_regs_ok cx E regs HdE HrL)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (ja1_vals regs) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ ja1_rs0 HS0 (ja1_rs0_sub _ _ _) ltac:(vm_compute; reflexivity)) as HS.
clear HS0.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF0 & GFc & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTKpres & GAR & GFin & GEFA & GEFL).
pose proof HdE as (HER & HE32 & HEIE & HE60 & HE516 & HE529).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA2).
assert (HSHr : kLowMemEnd <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 <= kHighShadowEnd).
{ pose proof (YCbq.shadow_addr_bounds (d_FB cx) ltac:(lia)) as Q1.
  pose proof (YCbq.shadow_addr_bounds (d_FB cx + 4096) ltac:(lia)) as Q2.
  pose proof (YCbq.shadow_range_end (d_FB cx) 4096 ltac:(lia)) as Q3. change (4096 / 8) with 512 in Q3. lia. }
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
remember (d_env cx E (ja1_vals regs)) as E1 eqn:HE1 in HS.
assert (E1sh : ew E1 529 = Z_to_bv 64 (shadow_addr (d_FB cx))).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE529. }
assert (E1a : ew E1 60 = Z_to_bv 64 (d_A cx)).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE60. }
assert (E1s : ew E1 2 = Z_to_bv 64 (d_S cx)).
{ rewrite HE1, d_env_old by (cbv; lia). rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (E132 : ew E1 32 = Z_to_bv 64 SHADOW_OFF).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE32. }
assert (E1x : forall j, (j < 32)%nat -> ew E1 (AT_X + j) = getr regs (Z_to_bv 5 (Z.of_nat j))).
{ intros j Hj. rewrite HE1, d_env_x by (unfold ja1_vals; rewrite length_map, length_seq; exact Hj).
  unfold ja1_vals. set (f := fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))).
  transitivity (nth j (map f (seq 0 32)) (f 0%nat)).
  - apply nth_indep. rewrite length_map, length_seq. exact Hj.
  - rewrite map_nth, seq_nth by exact Hj. reflexivity. }
assert (X3 : ew E1 534 = getr regs 3) by exact (E1x 3%nat ltac:(lia)).
assert (X4 : ew E1 535 = getr regs 4) by exact (E1x 4%nat ltac:(lia)).
assert (X20 : ew E1 551 = getr regs 20) by exact (E1x 20%nat ltac:(lia)).
assert (X22 : ew E1 553 = getr regs 22) by exact (E1x 22%nat ltac:(lia)).
assert (X25 : ew E1 556 = getr regs 25) by exact (E1x 25%nat ltac:(lia)).
assert (X26 : ew E1 557 = getr regs 26) by exact (E1x 26%nat ltac:(lia)).
clear E1x.
assert (HEI : img_env VAL A_LIM E1).
{ rewrite HE1. unfold d_env. apply img_env_havoc_hi; [exact HEIE | cbv; lia]. }
norm_ss HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E1
  (mrestrict (w_H W) (ms_mem (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + R10_OFF)) mem3 (YK11.seg_rom SEGS)))))
  by (unfold sh_ok; apply Forall_nil).
pose proof (paj_run (fx := fq) B LAWS) as RUN.
unfold cfg_at. change (w64 (BASE + R10_OFF)) with (Z_to_bv 64 (BASE + R10_OFF)).
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
prreg HS (18%bv : bv 5) Rs2. prreg HS (20%bv : bv 5) Rs4. prreg HS (22%bv : bv 5) Rs6.
prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10.
assert (HK1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hw).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
pmkst HS.
eapply SRr_bind.
{ eapply (aj_set_shadow_atS (fx := fq) SEGS B LAWS pa_segs_low (SIGMA DS___asan_set_shadow_00) 0 (ASS00 fq)
    W (ms_regs ms) (ms_mem ms) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k DFRAME_CLASS (c_fpos cx) (shadow_addr (d_FB cx) + 30) 162
    (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 2940)) HJ).
  - left; reflexivity.
  - rewrite Ra0, E1sh, unsigned_lit_small by lia. reflexivity.
  - rewrite Ra1. reflexivity.
  - lia.
  - rewrite GEFA. lia.
  - rewrite GEFA. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - unfold spZ. rewrite Rsp, E1a, unsigned_lit_small by lia. lia.
  - unfold d_A, MFRAME. lia.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - rewrite Rgp, X3. exact (proj1 (proj2 HrL)).
  - rewrite Rtp, X4. exact (proj1 (proj2 (proj2 HrL))).
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & H00 & Hkeep4 & Hpres4 & _).
assert (HPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem4 a)
  by (intros a Ha; apply Hpres4; exact (ja1_apres_grow _ _ _ _ HG Ha)).
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ d_fsh cx a -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hn'. unfold d_fsh in Hn'. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Hn'.
  rewrite Hkeep4 by (first [exact Ha | lia]). apply HK1. exact Ha. }
assert (HNF : forall x, (d_FB cx <= x < d_FB cx + 4096) \/ (d_S cx - 32768 <= x < d_S cx) ->
  0 <= x < 2 ^ 64 /\ ~ d_fsh cx x).
{ intros x Hx. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. zlia. }
assert (HKF : forall x, (d_FB cx <= x < d_FB cx + 4096) \/ (d_S cx - 32768 <= x < d_S cx) ->
  aview SEGS (w_H W) mem4 x = aview SEGS (w_H W) mem3 x)
  by (intros x Hx; destruct (HNF x Hx) as (Hx1 & Hx2); exact (HK x Hx1 Hx2)).
assert (HAPP : forall p len a, in_app p len -> p <= a < p + len -> 0 <= a < 2 ^ 64 /\ ~ d_fsh cx a).
{ intros p len a Hp Ha. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. zlia. }
assert (HSH4 : d_shadow cx dsh_ser W mem4).
{ intros kk Hkk. unfold DFRAME_SH in Hkk. rewrite ja1_dsh by lia.
  destruct (Z.leb_spec 30 kk); destruct (Z.ltb_spec kk 192); cbn [andb].
  all: first
   [ pose proof (H00 (kk - 30) ltac:(lia)) as X;
     replace (shadow_addr (d_FB cx) + 30 + (kk - 30)) with (shadow_addr (d_FB cx) + kk) in X by lia; exact X
   | rewrite Hkeep4 by lia; rewrite HK1 by lia; exact (Hshadow kk ltac:(unfold DFRAME_SH; lia)) ]. }
assert (HFR4 : d_frame cx h dsh_ser W mem4).
{ exists E. split; [exact HdE|].
  pose proof Hregs as HR. cbn [d_regions] in HR.
  pose proof (Forall_inv HR) as RSTK. apply Forall_inv_tail in HR.
  pose proof (Forall_inv HR) as RA. apply Forall_inv_tail in HR.
  pose proof (Forall_inv HR) as RF.
  assert (BS : base_val E (Some AT_STK) = d_S cx)
    by (cbn [base_val]; change AT_STK with 2%nat; rewrite (HER 2%nat 2%bv eq_refl); reflexivity).
  assert (BA : base_val E (Some AT_A) = d_A cx)
    by (cbn [base_val]; rewrite HE60; apply unsigned_lit_small; lia).
  assert (BF : base_val E (Some AT_F) = d_FB cx)
    by (cbn [base_val]; rewrite HE516; apply unsigned_lit_small; lia).
  assert (BSH : base_val E (Some AT_SH) = shadow_addr (d_FB cx))
    by (cbn [base_val]; rewrite HE529; apply unsigned_lit_small; lia).
  split.
  { cbn [d_regions].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    - eapply ja1_region_kept; [exact RSTK | vm_compute; reflexivity | |].
      + cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BS. intros x Hx.
        apply (mbyte_of_aview SEGS). apply HKF. right. lia.
      + cbn [YP09.r_wlo YP09.r_whi]. intros o Ho. lia.
    - eapply ja1_region_kept; [exact RA | vm_compute; reflexivity | |].
      + cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BA. intros x Hx.
        apply (mbyte_of_aview SEGS). apply HKF. right. lia.
      + cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite BA. intros o Ho.
        apply (apresent_writable SEGS). apply HPR. apply GSTKpres. unfold LLVMF_STK. lia.
    - eapply ja1_region_kept; [exact RF | vm_compute; reflexivity | |].
      + cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BF. intros x Hx.
        apply (mbyte_of_aview SEGS). apply HKF. left. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hx. lia.
      + cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite BF. intros o Ho.
        apply (apresent_writable SEGS). apply HPR. apply GFpres. unfold DFRAME_SIZE in Ho. lia.
    - unfold region_ok, fshadow_region. cbv beta zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BSH.
      change (fs_frame_bytes DFRAME_CLASS / 8) with 512.
      split; [lia|]. split; [lia|]. split.
      + intros o Ho. apply (apresent_writable SEGS). apply HPR. apply GSHpres. unfold DFRAME_SH in Ho. lia.
      + apply dsh_chunks_ok. intros kk Hkk. pose proof (HSH4 kk Hkk) as X.
        split; [exact (aview_range _ _ _ _ _ X)|]. unfold aview in X.
        destruct (mbyte SEGS (rd W mem4) (shadow_addr (d_FB cx) + kk)) as [b|] eqn:Eb; [|discriminate X].
        cbn [option_map] in X. injection X as <-. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { transitivity (rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8)); [|exact Hflag].
    apply rdword_ext. intros kk Hkk. apply HKF. left. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  split.
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact Hh216].
    intros kk Hkk. cbn in Hkk. apply HKF. right. lia.
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact Hh152].
    intros kk Hkk. cbn in Hkk. apply HKF. right. lia. }
assert (HVM : forall off v, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W mem4) (d_A cx + off) 8 v).
{ intros off v Ho1 Ho2 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact Hv].
  intros kk Hkk. cbn in Hkk. apply HKF. right. lia. }
assert (HSP0 : d_sp0 cx i now W mem4).
{ destruct Hsp0 as (Q1 & Q2). split; apply HVM; first [lia | assumption]. }
assert (HbA : in_app buf (req_size (Z.max (slot_ser_defs.ser_cap op) 1))).
{ destruct Hblocks as (HPm & _).
  assert (Hin : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPm)). unfold a3_xb. cbn [app]. left. reflexivity. }
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ GAR Hin))))). }
assert (HhA : in_app h (req_size HUNT_SIZE)).
{ destruct Hblocks as (HPm & _).
  assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. right. left. reflexivity. }
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ GAR Hin))))). }
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hc. pose proof Hbase as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low;
    [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (HBODY4 : d_body B cx h n (a3_xb buf op) dsh_ser ly3 S3 W mem4).
{ apply (d_body_rt B cx h n n (a3_xb buf op) dsh_loop dsh_ser ly3 S3 W mem3 mem4 (d_S cx) (d_S cx) (d_fsh cx) Hbody).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right. intros Hr. unfold d_fsh in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
    unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size in Hr.
    change (req_size HUNT_SIZE) with 480 in HhA. unfold HUNT_SIZE in Hr.
    destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [(Hr & _) | Hr]]]]]]].
    + zlia.
    + zlia.
    + zlia.
    + zlia.
    + zlia.
    + specialize (HpA Hc).
      replace (req_size (c_n cx)) with (c_n cx) in HpA by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
      zlia.
    + specialize (Hro a Hr). zlia.
    + unfold AE2k.FF_canary in Hr. zlia.
  - exact HK.
  - intros a _ Ha. exact (HPR a Ha).
  - exact HFR4.
  - exact HSH4.
  - lia. }
apply SRr_ret. unfold jA_c1, jcut. cbv beta. split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, regs4, mem4, md4, k, acc.
split; [unfold cfg_at, w64, JA_RET1; reflexivity|].
split; [exact HCSR|]. split; [exact Hbase|]. split; [exact HJ4|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
assert (P2 : getr regs4 2 = getr (ms_regs ms) 2) by exact (HP4 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs4 3 = getr (ms_regs ms) 3) by exact (HP4 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs4 4 = getr (ms_regs ms) 4) by exact (HP4 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs4 8 = getr (ms_regs ms) 8) by exact (HP4 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs4 9 = getr (ms_regs ms) 9) by exact (HP4 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs4 18 = getr (ms_regs ms) 18) by exact (HP4 18 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs4 20 = getr (ms_regs ms) 20) by exact (HP4 20 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs4 22 = getr (ms_regs ms) 22) by exact (HP4 22 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs4 25 = getr (ms_regs ms) 25) by exact (HP4 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs4 26 = getr (ms_regs ms) 26) by exact (HP4 26 ltac:(unfold acallee_saved; lia)).
pose proof HrL as (L2 & L3 & L4 & L8 & L9 & L18 & L20 & L25).
split.
{ split; [unfold spZ; rewrite P2, Rsp, E1a; apply unsigned_lit_small; lia|].
  split; [rewrite P3, Rgp, X3; exact L3|].
  split; [rewrite P4, Rtp, X4; exact L4|].
  split; [rewrite P8, Rs0, E1s; reflexivity|].
  split; [rewrite P9, Rs1, E1a; reflexivity|].
  split; [rewrite P18, Rs2, E132; reflexivity|].
  split; [rewrite P20, Rs4, X20; exact L20|].
  rewrite P25, Rs9, X25; exact L25. }
split.
{ split; [rewrite P22, Rs6, X22; exact R22|]. split; [rewrite P26, Rs10, X26; exact R26 | exact I]. }
split.
{ split.
  { destruct Hsp1 as (_ & Q224 & Q248). split; [exact HSP0|]. split; apply HVM; first [lia | assumption]. }
  split.
  { destruct Htab as (Hage & HT1). split; [exact Hage|].
    destruct Hage as (removed & Hm & Hpost). pose proof (proj1 Hpost) as HL1.
    apply (garr8_frame SEGS (rd W mem3) (rd W mem4) (d_obj cx OT) _ HT1).
    intros a Ha. rewrite length_map, HL1 in Ha.
    apply (mbyte_of_aview SEGS). apply HKF. left. unfold d_obj, dobj_off in Ha. lia. }
  split; [|exact I].
  destruct Hbuf as (Hr & Hb). split; [exact Hr|].
  apply (garr8_frame SEGS (rd W mem3) (rd W mem4) buf _ Hb).
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. unfold a3_r in Hr.
  replace (req_size (Z.max (slot_ser_defs.ser_cap op) 1)) with (Z.max (slot_ser_defs.ser_cap op) 1) in HbA
    by (unfold req_size; destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia).
  destruct (HAPP buf (Z.max (slot_ser_defs.ser_cap op) 1) a HbA ltac:(lia)) as (Ha1 & Ha2).
  apply (mbyte_of_aview SEGS). exact (HK a Ha1 Ha2). }
split; [exact HSP0|].
exact HBODY4.
Qed.

End h.
End f.
End d.
