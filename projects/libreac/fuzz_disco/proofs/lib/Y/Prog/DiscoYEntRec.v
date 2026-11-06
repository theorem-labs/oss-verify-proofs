(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 365 of its 397 lines of code are new or changed and 37 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntLatch.v, with its module paths and numbers changed; 913 of its 1003 lines of code are new or changed and 307 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC81 YC85 YC1g YC1h YC4b YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntRecCuts DiscoYEntSeat
DiscoYEntRecHead DiscoYEntRecArm DiscoYEntRecCopy.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition C1_OFF : Z := 0xd68.

Definition yb_sr : list sv :=
  [SLit 0; SOff 546 0; SOff AT_A 0; SOff 3 0; SOff 4 0; SOff 547 0; SOff 548 0; SOff 549 0;
   SOff AT_STK 0; SOff AT_A 0; SOff 550 0; SOff 536 0; SOff 537 0; SOff 551 0; SOff 552 0; SOff 553 0;
   SOff 554 0; SOff 555 0; SLit WS_MASK; SOff 32 0; SLit 32; SOff 531 0; SLit 1; SOff 535 0;
   SOff 538 0; SOff 539 0; SOff 532 0; SOff AT_SH 0; SOff 556 0; SOff 557 0; SOff 558 0; SOff 559 0].

Definition yb_acs : list YP09.chunk :=
  [YP09.mkChunk 208 (CVal 8 (SOff 531 0)); YP09.mkChunk 320 (CVal 8 (SOff 532 0));
   YP09.mkChunk 360 (CVal 8 (SOff 533 0)); YP09.mkChunk 352 (CVal 8 (SOff 534 0));
   YP09.mkChunk 184 (CVal 8 (SOff 540 0)); YP09.mkChunk 120 (CVal 8 (SOff 541 0));
   YP09.mkChunk 136 (CVal 8 (SLit 0));
   YP09.mkChunk 376 (CVal 8 (SOff 542 0)); YP09.mkChunk 280 (CVal 8 (SOff 543 0));
   YP09.mkChunk 232 (CVal 8 (SOff 544 0)); YP09.mkChunk 264 (CVal 8 (SOff 545 0))].

Definition yc_sr : list sv :=
  [SLit 0; SOff 545 0; SOff AT_A 0; SOff 3 0; SOff 4 0; SOff 546 0; SOff 547 0; SOff 548 0;
   SOff AT_STK 0; SOff AT_A 0; SOff 549 0; SOff 536 0; SOff 550 0; SOff 551 0; SOff 552 0; SOff 553 0;
   SOff 554 0; SOff 555 0; SLit WS_MASK; SOff 32 0; SLit 32; SOff 531 0; SLit 1; SOff 535 0;
   SOff 537 0; SOff 538 0; SOff 532 0; SOff AT_SH 0; SOff 556 0; SOff 557 0; SOff 558 0; SOff 559 0].

Definition yc_acs : list YP09.chunk :=
  [YP09.mkChunk 208 (CVal 8 (SOff 531 0)); YP09.mkChunk 320 (CVal 8 (SOff 532 0));
   YP09.mkChunk 360 (CVal 8 (SOff 533 0)); YP09.mkChunk 352 (CVal 8 (SOff 534 0));
   YP09.mkChunk 184 (CVal 8 (SOff 539 0)); YP09.mkChunk 120 (CVal 8 (SOff 540 0));
   YP09.mkChunk 136 (CVal 8 (SLit 0));
   YP09.mkChunk 376 (CVal 8 (SOff 541 0)); YP09.mkChunk 280 (CVal 8 (SOff 542 0));
   YP09.mkChunk 232 (CVal 8 (SOff 543 0)); YP09.mkChunk 264 (CVal 8 (SOff 544 0))].

Ltac yr_ro HS bn :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let idx := idx_of_base rs bn in let idx := eval vm_compute in idx in
let r := eval vm_compute in (nth idx rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx idx r (set_window r 0 0) HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0
     (st_ok_pi_region_nth Ex ssx msx idx r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.

Lemma y_den_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v <-. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Ltac yr_meq MEQ :=
  repeat match goal with
  | HFx : frame_of _ _ _ _ |- _ =>
      let M := fresh "M" in
      pose proof (y_frame_eq _ _ _ _ HFx ltac:(vm_compute; reflexivity)) as M;
      cbn [ms_mem mkst] in M; clear HFx
  end;
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msf; cfg_model := _ |} _ =>
  lazymatch goal with HBD : d_body _ _ _ _ _ _ _ _ _ ?m0 |- _ =>
  assert (MEQ : forall x, ms_mem msf x = m0 x)
    by (intros x; repeat match goal with Mx : forall x, ms_mem _ x = _ |- _ => rewrite Mx; clear Mx end;
        reflexivity)
  end end.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Definition yb_vals (cx : dcx) (h i n now op : Z) (regs : bvmap 5 word) : list word :=
  [w64 i; w64 now; w64 op; w64 (if op <? 128 then op else op - 256); w64 (op mod 4);
   w64 (rdb (rest_of (c_pl cx) n) 0); w64 (256 * rdb (rest_of (c_pl cx) n) 1);
   w64 (rec_rem n); w64 (d_cur cx (rec_rem n));
   w64 h; w64 (h + 440); w64 (dnot (d_obj cx OG)); w64 (dnot (d_obj cx OT)); w64 (dnot (d_obj cx OO));
   w64 (dnot (d_obj cx OUSED));
   getr regs 1; getr regs 5; getr regs 6; getr regs 7; getr regs 10; getr regs 13; getr regs 14;
   getr regs 15; getr regs 16; getr regs 17; getr regs 28; getr regs 29; getr regs 30; getr regs 31].

Definition yc_vals (cx : dcx) (h i n now op : Z) (regs : bvmap 5 word) : list word :=
  [w64 i; w64 now; w64 op; w64 (if op <? 128 then op else op - 256); w64 (op mod 4);
   w64 (rec_len (rest_of (c_pl cx) n) n);
   w64 (rec_rem n); w64 (d_cur cx (rec_rem n));
   w64 h; w64 (h + 440); w64 (dnot (d_obj cx OG)); w64 (dnot (d_obj cx OT)); w64 (dnot (d_obj cx OO));
   w64 (dnot (d_obj cx OUSED));
   getr regs 1; getr regs 5; getr regs 6; getr regs 7; getr regs 10; getr regs 12; getr regs 13; getr regs 14;
   getr regs 15; getr regs 16; getr regs 17; getr regs 28; getr regs 29; getr regs 30; getr regs 31].

Lemma y_slot_atom : forall (E : env) (cx : dcx) (W : world SEGS) m lo hi wlo whi cs od (q : nat) v,
  region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 60%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 60) = d_A cx ->
  In (YP09.mkChunk od (CVal 8 (SOff q 0))) cs -> ew E q = w64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (rd W m) (d_A cx + od) 8 v.
Proof.
intros E cx W m lo hi wlo whi cs od q v HR HA Hin Hq Hv.
exact (field_of_region E _ 60%nat (d_A cx) cs lo hi wlo whi od 8%N (SOff q 0) v HR HA Hin
  ltac:(rewrite sv_denot_SOff0, Hq; reflexivity)
  ltac:(cbn [Z.of_N]; change (8 * 8) with 64; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.

Lemma y_slot_lit : forall (E : env) (cx : dcx) (W : world SEGS) m lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 60%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 60) = d_A cx ->
  In (YP09.mkChunk od (CVal 8 (SLit v))) cs -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (rd W m) (d_A cx + od) 8 v.
Proof.
intros E cx W m lo hi wlo whi cs od v HR HA Hin Hv.
exact (field_of_region E _ 60%nat (d_A cx) cs lo hi wlo whi od 8%N (SLit v) v HR HA Hin
  ltac:(rewrite denot_lit_U, U_SLit; f_equal; apply zcanon_id; unfold M64; lia)
  ltac:(cbn [Z.of_N]; change (8 * 8) with 64; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.

Lemma y_rok_move : forall (E : env) (W3 W4 : world SEGS) m3 m4 (r : YP09.region),
  region_wf r = true ->
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> apresent (w_H W4) m4 (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E (mrestrict (w_H W3) m3) r -> region_ok SEGS E (mrestrict (w_H W4) m4) r.
Proof.
intros E W3 W4 m3 m4 r Hwf HAV HPR (H1 & H2 & H3 & H4).
unfold region_wf in Hwf. apply andb_prop in Hwf as [Hwf Hch]. apply andb_prop in Hwf as [Hlh _].
apply Z.leb_le in Hlh. rewrite forallb_forall in Hch.
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply (apresent_writable SEGS). exact (HPR o Ho).
- apply Forall_forall. intros c Hc.
  pose proof (Hch c Hc) as Hci. unfold chunk_inside in Hci.
  apply andb_prop in Hci as [Hci Hcl]. apply andb_prop in Hci as [Hc1 Hc2].
  apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. apply Z.leb_le in Hcl.
  pose proof (proj1 (Forall_forall _ _) H4 c Hc) as HcOK.
  intros j Hj. destruct (HcOK j Hj) as (b & Hb & Hm).
  exists b. split; [exact Hb|].
  erewrite (mbyte_of_aview SEGS); [exact Hm | ].
  unfold YP09.c_len in Hcl.
  first [ apply HAV; lia | symmetry; apply HAV; lia ].
Qed.

Lemma y_val_move : forall (W3 W4 : world SEGS) m3 m4 a q v,
  (forall x, a <= x < a + Z.of_nat q -> aview SEGS (w_H W4) m4 x = aview SEGS (w_H W3) m3 x) ->
  val_mem SEGS (mrestrict (w_H W3) m3) a q v -> val_mem SEGS (mrestrict (w_H W4) m4) a q v.
Proof.
intros W3 W4 m3 m4 a q v HAV Hv j Hj.
erewrite (mbyte_of_aview SEGS); [exact (Hv j Hj) | ].
first [ apply HAV; lia | symmetry; apply HAV; lia ].
Qed.

Lemma y_frame_move : forall (cx : dcx) h shf (W3 W4 : world SEGS) m3 m4,
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 64 -> 0 <= shadow_addr (d_FB cx) < 2 ^ 64 ->
  0 <= d_S cx < 2 ^ 64 -> d_A cx + 472 <= d_S cx -> d_S cx - LLVMF_STK <= d_A cx ->
  (forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
     aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  (forall a, d_S cx - LLVMF_STK <= a < d_S cx -> apresent (w_H W4) m4 a) ->
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> apresent (w_H W4) m4 a) ->
  (forall j, 0 <= j < 512 -> apresent (w_H W4) m4 (shadow_addr (d_FB cx) + j)) ->
  d_frame cx h shf W3 m3 -> d_frame cx h shf W4 m4.
Proof.
intros cx h shf W3 W4 m3 m4 RA RFB RSH RS HA1 HA2 KS KF KH PS PF PH
  (E & HE & HRG & HFL & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
assert (U2 : base_val E (Some AT_STK) = d_S cx)
  by (cbn [base_val]; unfold AT_STK; rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U60 : base_val E (Some AT_A) = d_A cx)
  by (cbn [base_val]; unfold AT_A; rewrite E60; unfold w64; apply unsigned_lit_small; exact RA).
assert (U516 : base_val E (Some AT_F) = d_FB cx)
  by (cbn [base_val]; unfold AT_F; rewrite E516; unfold w64; apply unsigned_lit_small; exact RFB).
assert (U529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx))
  by (cbn [base_val]; unfold AT_SH; rewrite E529; unfold w64; apply unsigned_lit_small; exact RSH).
assert (KA : forall a, d_A cx <= a < d_A cx + 472 ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) by (intros a Ha; apply KS; lia).
unfold d_regions in HRG.
pose proof (Forall_inv HRG) as R1. apply Forall_inv_tail in HRG.
pose proof (Forall_inv HRG) as R2. apply Forall_inv_tail in HRG.
pose proof (Forall_inv HRG) as R3. apply Forall_inv_tail in HRG.
pose proof (Forall_inv HRG) as R4. clear HRG.
exists E. split; [exact HE|]. split.
- unfold d_regions. repeat apply Forall_cons; try apply Forall_nil.
  + eapply (y_rok_move E W3 W4 m3 m4);
      [ vm_compute; reflexivity
      | cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite U2; intros a Ha; apply KS;
        clear - Ha HA1 HA2; lia
      | cbn [YP09.r_wlo YP09.r_whi]; intros o Ho; lia
      | exact R1 ].
  + eapply (y_rok_move E W3 W4 m3 m4);
      [ vm_compute; reflexivity
      | cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite U60; intros a Ha; apply KA; lia
      | cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite U60; intros o Ho; apply PS;
        clear - Ho HA1 HA2; lia
      | exact R2 ].
  + eapply (y_rok_move E W3 W4 m3 m4);
      [ vm_compute; reflexivity
      | cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite U516; intros a Ha; apply KF;
        change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha; lia
      | cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite U516; intros o Ho; apply PF;
        unfold DFRAME_SIZE in Ho; lia
      | exact R3 ].
  + eapply (y_rok_move E W3 W4 m3 m4);
      [ vm_compute; reflexivity
      | unfold fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite U529; intros a Ha; apply KH;
        change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha; lia
      | unfold fshadow_region; cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite U529; intros o Ho;
        replace (shadow_addr (d_FB cx) + o) with (shadow_addr (d_FB cx) + o) by reflexivity;
        apply PH; unfold DFRAME_SH in Ho; lia
      | exact R4 ].
- split.
  + rewrite (rdword_ext (aview SEGS (w_H W3) m3) (aview SEGS (w_H W4) m4)); [exact HFL|].
    intros j Hj. apply KF. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  + repeat split;
      (apply (y_val_move W3 W4 m3 m4); [intros x Hx; apply KA; cbn [Z.of_nat] in Hx; lia | assumption]).
Qed.

Lemma y_val_ext : forall (W : world SEGS) (m m' : word -> option byte) a q v,
  (forall x, m' x = m x) -> val_mem SEGS (rd W m) a q v -> val_mem SEGS (rd W m') a q v.
Proof.
intros W m m' a q v HM Hv j Hj. rewrite (y_mbyte_ext SEGS (w_H W) m m' HM). exact (Hv j Hj).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DUNIV : duniv_ok B.
Hypothesis AMALLOC : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B.
Hypothesis BMALLOC : d_body_malloc_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DRO : d_ro_hyps B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis AMEMCPY : forall fq : YK11.FPState,
  aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).

Lemma y_chain : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  bad_next (d_S cx) (ly_top ly3) (s0Z (c_regs cx)) = true \/
  fpchain (rdword (aview SEGS (w_H W3) mem3)) (s0Z (c_regs cx)) (ly_top ly3) [].
Proof.
intros cx ly3 S3 W3 mem3 md3 k (HB & HJ & HFR).
destruct HB as (HPRE & _).
destruct HPRE as (HAFN & _).
destruct HAFN as (HAR0 & _ & _ & _ & _ & Hstk & _ & Hch & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly3 & _ & _ & _ & _ & _ & _ & Hkeep & _).
destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
rewrite Etop. change (spZ (c_regs cx)) with (d_S cx) in *.
pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hs0r.
change (bv_unsigned (getr (c_regs cx) 8)) with (s0Z (c_regs cx)) in Hs0r.
destruct Hch as [(Hv & _) | (Hv1 & Hv2 & Hv3 & Hfp & _)].
- left. unfold bad_next. destruct Hv as [Hv | [Hv | Hv]].
  + apply Bool.orb_true_iff; left; apply Bool.orb_true_iff; left; apply Z.leb_le.
    unfold LLVMF_STK in *. lia.
  + apply Bool.orb_true_iff; left; apply Bool.orb_true_iff; right; apply Z.leb_le. lia.
  + apply Bool.orb_true_iff; right. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hv.
- right. cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hr2). exists r. split; [|exact Hr2].
  rewrite <- Hr. apply rdword_ext. intros kk Hkk. apply Hkeep; unfold LLVMF_STK in *; lia.
Qed.

Definition yb_c1 (cx : dcx) (h i n now op : Z) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx C1_OFF (EV_HEAD i) (ACC_HEAD MT i)
    (fun regs ly3 S3 W3 mem3 md3 =>
       0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ 0 <= op < 256 /\ op mod 4 <> 3 /\
       d_rL B cx regs /\ getr regs 22 = w64 1 /\ getr regs 21 = w64 i /\ getr regs 26 = w64 now /\
       getr regs 23 = w64 (op mod 4) /\
       getr regs 11 = w64 (rec_len (rest_of (c_pl cx) n) n) /\
       getr regs 24 = w64 (rec_rem n) /\ getr regs 25 = w64 (d_cur cx (rec_rem n)) /\
       d_sp0 cx i now W3 mem3 /\ d_spOP cx op W3 mem3 /\
       d_body B cx h n [] dsh_loop ly3 S3 W3 mem3).

Lemma y_rec_bounds : forall (R : list byte) (n : Z), 0 <= n ->
  0 <= rec_want R <= REC_MAX /\ 0 <= rec_rem n <= n /\ 0 <= rec_len R n <= rec_rem n /\
  rec_len R n <= REC_MAX /\ rec_rem n + rec_take n = n /\ 0 <= rec_take n <= 2.
Proof.
intros R n Hn.
pose proof (bv_unsigned_in_range 8 (nth 0 R (Z_to_bv 8 0))) as G0.
pose proof (bv_unsigned_in_range 8 (nth 1 R (Z_to_bv 8 0))) as G1.
change (bv_modulus 8) with 256 in G0, G1.
unfold rec_len, rec_want, rec_rem, rec_take, rdb, REC_MAX in *.
repeat split; lia.
Qed.

Lemma y_cur_bound : forall (cx : dcx) (m : Z),
  d_base B MT XM_LIB RLO RHI tfib_K cx -> 0 <= m <= c_n cx ->
  0 <= d_cur cx m <= alloc_ceiling + A_EMPTY.
Proof.
intros cx m (HPRE & _) Hm.
pose proof asan_consts as (C1 & _).
pose proof HPRE as (HAFN & _ & _ & _ & HINdisj & _). pose proof (proj1 HAFN) as HAR0.
unfold d_cur.
destruct HINdisj as [(Hn0 & Hp0) | (Hr & Hinb)].
- rewrite Hn0, Hp0 in *. unfold A_EMPTY in *. lia.
- destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) HAR0 Hinb)
    as (_ & H4096 & Hc & _).
  assert (Hrq : req_size (c_n cx) = c_n cx)
    by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); [lia | reflexivity]).
  rewrite Hrq in Hc. unfold A_EMPTY. lia.
Qed.

Lemma yb_c1_ok : forall (fq : YK11.FPState) (cx : dcx) (h i n now op : Z) ly3 S3 (W : world SEGS)
  mem3 md' k acc (E : env) (ss : sstate) (ms : machine_state),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 -> 0 <= op < 256 -> op mod 4 <> 3 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = C1_OFF ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 -> (forall x, ms_mem ms x = mem3 x) ->
  d_sp0 cx i now W mem3 -> d_spOP cx op W mem3 ->
  d_rL B cx (ms_regs ms) -> getr (ms_regs ms) 22 = w64 1 -> getr (ms_regs ms) 21 = w64 i ->
  getr (ms_regs ms) 26 = w64 now -> getr (ms_regs ms) 23 = w64 (op mod 4) ->
  getr (ms_regs ms) 11 = w64 (rec_len (rest_of (c_pl cx) n) n) ->
  getr (ms_regs ms) 24 = w64 (rec_rem n) -> getr (ms_regs ms) 25 = w64 (d_cur cx (rec_rem n)) ->
  yb_c1 cx h i n now op W (mkCfg ms md').
Proof.
intros fq cx h i n now op ly3 S3 W mem3 md' k acc E ss ms HFQ HB HJ HFR Hk Hev Hmo Hacc
  Ri Rn Rnow Rop Ropm HS Hrv Hpc HBD MEQ HSP HOP HRL H22 H21 H26 H23 H11 H24 H25.
pose proof (y_body_ext B BRT cx h n [] dsh_loop ly3 S3 W mem3 (ms_mem ms)
  ltac:(intros x; rewrite MEQ; reflexivity) HBD) as HBD'.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
pose proof HSP as (VS1 & VS2). pose proof HOP as (VO1 & VO2).
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFQ|].
split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Ri|]. split; [exact Rn|]. split; [exact Rnow|]. split; [exact Rop|]. split; [exact Ropm|].
split; [exact HRL|]. split; [exact H22|]. split; [exact H21|]. split; [exact H26|]. split; [exact H23|].
split; [exact H11|]. split; [exact H24|]. split; [exact H25|].
split; [split; [exact (y_val_ext W mem3 (ms_mem ms) _ _ _ ltac:(intros x; rewrite MEQ; reflexivity) VS1)
               | exact (y_val_ext W mem3 (ms_mem ms) _ _ _ ltac:(intros x; rewrite MEQ; reflexivity) VS2)]|].
split; [split; [exact (y_val_ext W mem3 (ms_mem ms) _ _ _ ltac:(intros x; rewrite MEQ; reflexivity) VO1)
               | exact (y_val_ext W mem3 (ms_mem ms) _ _ _ ltac:(intros x; rewrite MEQ; reflexivity) VO2)]|].
exact HBD'.
Qed.

Theorem yb_s1 : forall cx h i n now op (W : world SEGS) (c : config),
  yr_join B MT XM_LIB RLO RHI tfib_K cx h i n now op W c ->
  SRr SEGS W c (yb_c1 cx h i n now op).
Proof.
intros cx h i n now op W c Hpre.
destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFQ & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
  Ri & Rn & Rnow & Rop & Ropm & HR & H22 & H21 & H26 & H23 & H11 & H12 & H24 & H25 & HSP & HOP & HBD).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
pose proof asan_consts as (C1 & _).
pose proof HB as (HPRE & _).
pose proof HPRE as (HAFN & _ & _ & _ & HINdisj & _).
pose proof HAFN as (_ & _ & _ & Hgp0 & Htp0 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (c_regs cx)) with (d_S cx) in Hslo, Hshi.
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTK & HWR).
pose proof HFRM as (E & HE & HRG & HFL & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
pose proof HR as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
pose proof HSP as (V208 & V320).
pose proof HOP as (V360 & V352).
pose proof HGEO as (HFB0 & HFBc & Hh0 & HhC & HcS & Hlen & Hdisj & Hin).
pose proof HINP as (Rnm & HINPg & HINPo).
assert (Rcn : 0 <= c_n cx < 2 ^ 26)
  by (clear - HINdisj Hlen; destruct HINdisj as [(Hn0 & _) | (Hr & _)]; lia).
destruct (y_rec_bounds (rest_of (c_pl cx) n) n Rn) as (Hw1 & Hr1 & Hl1 & Hl2 & Hrt & Htk).
assert (Hb0 : 0 <= rdb (rest_of (c_pl cx) n) 0 < 256)
  by (unfold rdb; pose proof (bv_unsigned_in_range 8 (nth 0 (rest_of (c_pl cx) n) (Z_to_bv 8 0)));
      change (bv_modulus 8) with 256 in *; lia).
assert (Hb1 : 0 <= rdb (rest_of (c_pl cx) n) 1 < 256)
  by (unfold rdb; pose proof (bv_unsigned_in_range 8 (nth 1 (rest_of (c_pl cx) n) (Z_to_bv 8 0)));
      change (bv_modulus 8) with 256 in *; lia).
pose proof (y_cur_bound cx (rec_rem n) HB ltac:(clear - Hr1 Rnm Rcn; lia)) as Rcur.
pose proof (y_A_range (d_S cx) ltac:(clear - C1 Hceil Hslo; unfold MFRAME, LLVMF_STK in *; lia)) as HAr.
change (32 * ((d_S cx - MFRAME) / 32)) with (d_A cx) in HAr.
assert (RA : 0 <= d_A cx < 2 ^ 64) by (clear - C1 Hceil Hslo Hshi H47 HAr; unfold MFRAME, LLVMF_STK in *; lia).
pose proof (y_E_env cx E (yb_vals cx h i n now op regs) HE) as HEd.
pose proof HEd as (_ & _ & HEI' & _).
set (Ed := d_env cx E (yb_vals cx h i n now op regs)) in *.
assert (AO : forall q, (q < AT_FL)%nat -> ew Ed q = ew E q) by (intros q Hq; apply y_env_old; exact Hq).
assert (AX : forall j, (j < 29)%nat -> ew Ed (AT_X + j) = nth j (yb_vals cx h i n now op regs) (Z_to_bv 64 0))
  by (intros j Hj; apply y_env_x; cbn [length yb_vals]; lia).
assert (D60 : sv_denot Ed (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot Ed (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D3 : sv_denot Ed (SOff 3 0) = w64 (as_gp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 3%nat 3%bv eq_refl); exact Hgp0).
assert (D4 : sv_denot Ed (SOff 4 0) = w64 (as_tp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 4%nat 4%bv eq_refl); exact Htp0).
assert (D32 : sv_denot Ed (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E32).
assert (D529 : sv_denot Ed (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E529).
assert (DX : forall j q, q = (AT_X + j)%nat -> (j < 29)%nat ->
  sv_denot Ed (SOff q 0) = nth j (yb_vals cx h i n now op regs) (Z_to_bv 64 0))
  by (intros j q -> Hj; rewrite sv_denot_SOff0; exact (AX j Hj)).
assert (E536 : ew Ed 536 = Z_to_bv 64 (rdb (rest_of (c_pl cx) n) 0))
  by (change 536%nat with (AT_X + 5)%nat; rewrite (AX 5%nat ltac:(lia)); cbn [yb_vals nth]; reflexivity).
assert (E537 : ew Ed 537 = Z_to_bv 64 (256 * rdb (rest_of (c_pl cx) n) 1))
  by (change 537%nat with (AT_X + 6)%nat; rewrite (AX 6%nat ltac:(lia)); cbn [yb_vals nth]; reflexivity).
assert (E538 : ew Ed 538 = Z_to_bv 64 (rec_rem n))
  by (change 538%nat with (AT_X + 7)%nat; rewrite (AX 7%nat ltac:(lia)); cbn [yb_vals nth]; reflexivity).
assert (E539 : ew Ed 539 = Z_to_bv 64 (d_cur cx (rec_rem n)))
  by (change 539%nat with (AT_X + 8)%nat; rewrite (AX 8%nat ltac:(lia)); cbn [yb_vals nth]; reflexivity).
assert (HROK : regs_ok Ed yb_sr regs).
{ apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
  repeat (destruct Hz as [<-|Hz];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
      lazymatch goal with
      | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
      | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H18 | exact H20 | exact H22 ]
      | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
          first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
      | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
      | |- _ = sv_denot _ (SOff 3 0) => rewrite D3; exact Hgp
      | |- _ = sv_denot _ (SOff 4 0) => rewrite D4; exact Htp
      | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H19
      | |- _ = sv_denot _ (SOff 529 0) => rewrite D529; exact H27
      | |- _ = sv_denot _ (SOff ?q 0) =>
          let j := eval vm_compute in (q - 531)%nat in
          rewrite (DX j q eq_refl ltac:(lia)); cbn [nth yb_vals]; first [reflexivity | assumption]
      end
    | ]).
  destruct Hz. }
assert (HFB4 : d_FB cx + 4096 <= alloc_ceiling)
  by (change (fs_frame_bytes DFRAME_CLASS) with 4096 in HFBc; exact HFBc).
assert (HFACTS : facts_ok Ed (d_facts [] []))
  by exact (FACTS LAWS cx ly3 S3 W mem3 md3 k E (yb_vals cx h i n now op regs) [] [] HC HE I I).
assert (HACS : Forall (YP09.chunk_ok SEGS Ed (rd W mem3) (d_A cx)) yb_acs).
{ unfold yb_acs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ i);
      [rewrite (DX 0%nat 531%nat eq_refl ltac:(lia)); reflexivity
      | cbn; clear - Ri; unfold MAX_OPS in Ri; lia | lia | exact V208].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ now);
      [rewrite (DX 1%nat 532%nat eq_refl ltac:(lia)); reflexivity | cbn; clear - Rnow; lia | lia | exact V320].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ op);
      [rewrite (DX 2%nat 533%nat eq_refl ltac:(lia)); reflexivity | cbn; clear - Rop; lia | lia | exact V360].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ ((if op <? 128 then op else op - 256) mod 2 ^ 64));
      [rewrite (DX 3%nat 534%nat eq_refl ltac:(lia)); cbn [nth yb_vals]; unfold w64; symmetry; apply y_Z_to_bv_mod64
      | cbn; apply Z.mod_pos_bound; lia | lia | apply y_val_mem_mod64; exact V352].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ h);
      [rewrite (DX 9%nat 540%nat eq_refl ltac:(lia)); reflexivity
      | cbn; clear - Hh0 HhC C1; unfold HUNT_SIZE in *; lia | lia | exact V184].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (h + 440));
      [rewrite (DX 10%nat 541%nat eq_refl ltac:(lia)); reflexivity
      | cbn; clear - Hh0 HhC C1; unfold HUNT_SIZE in *; lia | lia | exact V120].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ 0); [reflexivity | cbn; lia | lia | exact V136].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OG)));
      [rewrite (DX 11%nat 542%nat eq_refl ltac:(lia)); reflexivity
      | cbn; unfold dnot, d_obj, dobj_off; clear - HFB0 HFB4 C1; lia | lia | exact V376].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OT)));
      [rewrite (DX 12%nat 543%nat eq_refl ltac:(lia)); reflexivity
      | cbn; unfold dnot, d_obj, dobj_off; clear - HFB0 HFB4 C1; lia | lia | exact V280].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OO)));
      [rewrite (DX 13%nat 544%nat eq_refl ltac:(lia)); reflexivity
      | cbn; unfold dnot, d_obj, dobj_off; clear - HFB0 HFB4 C1; lia | lia | exact V232].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OUSED)));
      [rewrite (DX 14%nat 545%nat eq_refl ltac:(lia)); reflexivity
      | cbn; unfold dnot, d_obj, dobj_off; clear - HFB0 HFB4 C1; lia | lia | exact V264]. }
pose proof (SEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E JOIN_OFF yb_sr
  (yb_vals cx h i n now op regs) yb_acs [] [] (d_facts [] []) HC HE HRG HFL HROK HFACTS HACS
  (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + JOIN_OFF)) with (Z_to_bv 64 (BASE + JOIN_OFF)).
unfold ss_d in HS. fold Ed in HS.
yr_ro HS 60%nat. yr_ro HS 516%nat. yr_ro HS 529%nat.
assert (Uor : U Ed (SAlu ALU_OR (SOff 537 0) (SOff 536 0)) = rec_want (rest_of (c_pl cx) n)).
{ rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom Ed 537%nat (256 * rdb (rest_of (c_pl cx) n) 1) E537 ltac:(clear - Hb1; lia)).
  rewrite (U_atom Ed 536%nat (rdb (rest_of (c_pl cx) n) 0) E536 ltac:(clear - Hb0; lia)).
  rewrite y_lor_byte by (clear - Hb0 Hb1; lia).
  unfold rec_want. apply zcanon_id. unfold M64. clear - Hb0 Hb1. lia. }
assert (Rnb64 : 0 <= rec_rem n < 2 ^ 64) by (clear - Hr1 Rn Rnm Rcn; lia).
assert (Rcur64 : 0 <= d_cur cx (rec_rem n) < 2 ^ 64)
  by (unfold A_EMPTY in Rcur; clear - Rcur C1; lia).
assert (Unb : U Ed (SOff 538 0) = rec_rem n) by exact (U_atom Ed 538%nat _ E538 Rnb64).
assert (Ucur : U Ed (SOff 539 0) = d_cur cx (rec_rem n)) by exact (U_atom Ed 539%nat _ E539 Rcur64).
pose proof (U_not Ed 539%nat (d_cur cx (rec_rem n)) E539 Rcur64) as Unot.
paj_run_to_sh RUNTO HS HJ 0xd54; [awr_ok_tac | ].
psrr_branch_pi RUNP BR HS.
- rewrite branch_ltu_U, Uor, Unb in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_sh RUNTO HS HJ 0xd60; [awr_ok_tac | ].
  psrr_branch_pi RUNP BR HS.
  2: { exfalso. rewrite branch_geu_U, Unot, Uor in Hc0.
       apply Bool.negb_false_iff, Z.ltb_lt in Hc0. unfold REC_MAX in Hw1. unfold A_EMPTY in Rcur.
       clear - Hc0 Rcur C1 Hw1. lia. }
  paj_run_to_sh RUNTO HS HJ C1_OFF; [awr_ok_tac | ].
  yr_meq MEQ. apply SRr_ret.
  apply (yb_c1_ok fq cx h i n now op ly3 S3 W mem3 _ k acc _ _ _ HFQ HB HJ HFR Hk Hev Hmo Hacc
    Ri Rn Rnow Rop Ropm HS eq_refl eq_refl HBD MEQ HSP HOP).
  + yr_rg HS (2%bv : bv 5) Q2; yr_rg HS (3%bv : bv 5) Q3; yr_rg HS (4%bv : bv 5) Q4;
    yr_rg HS (8%bv : bv 5) Q8; yr_rg HS (9%bv : bv 5) Q9; yr_rg HS (19%bv : bv 5) Q19;
    yr_rg HS (18%bv : bv 5) Q18; yr_rg HS (20%bv : bv 5) Q20; yr_rg HS (27%bv : bv 5) Q27;
    unfold d_rL;
    split; [unfold spZ; rewrite Q2, D60; unfold w64; apply unsigned_lit_small; exact RA|];
    split; [rewrite Q3; exact D3|]; split; [rewrite Q4; exact D4|]; split; [rewrite Q8; exact D2|];
    split; [rewrite Q9; exact D60|]; split; [rewrite Q19; exact D32|];
    split; [rewrite Q18; reflexivity|]; split; [rewrite Q20; reflexivity|]; rewrite Q27; exact D529.
  + yr_rg HS (22%bv : bv 5) Q22. rewrite Q22. reflexivity.
  + yr_rg HS (21%bv : bv 5) Q21. rewrite Q21, (DX 0%nat 531%nat eq_refl ltac:(lia)). reflexivity.
  + yr_rg HS (26%bv : bv 5) Q26. rewrite Q26, (DX 1%nat 532%nat eq_refl ltac:(lia)). reflexivity.
  + yr_rg HS (23%bv : bv 5) Q23. rewrite Q23, (DX 4%nat 535%nat eq_refl ltac:(lia)). reflexivity.
  + yr_rg HS (11%bv : bv 5) Q11. rewrite Q11, (y_den_of_U Ed _ _ Uor).
    unfold w64. f_equal. unfold rec_len. symmetry. apply Z.min_l. lia.
  + yr_rg HS (24%bv : bv 5) Q24. rewrite Q24, (DX 7%nat 538%nat eq_refl ltac:(lia)). reflexivity.
  + yr_rg HS (25%bv : bv 5) Q25. rewrite Q25, (DX 8%nat 539%nat eq_refl ltac:(lia)). reflexivity.
- rewrite branch_ltu_U, Uor, Unb in Hc. apply Z.ltb_ge in Hc.
  paj_run_to_sh RUNTO HS HJ 0xd60; [awr_ok_tac | ].
  psrr_branch_pi RUNP BR HS.
  2: { exfalso. rewrite branch_geu_U, Unot, Unb in Hc0.
       apply Bool.negb_false_iff, Z.ltb_lt in Hc0. unfold A_EMPTY in Rcur.
       clear - Hc0 Rcur C1 Hr1 Rn Rnm Rcn. lia. }
  paj_run_to_sh RUNTO HS HJ C1_OFF; [awr_ok_tac | ].
  yr_meq MEQ. apply SRr_ret.
  apply (yb_c1_ok fq cx h i n now op ly3 S3 W mem3 _ k acc _ _ _ HFQ HB HJ HFR Hk Hev Hmo Hacc
    Ri Rn Rnow Rop Ropm HS eq_refl eq_refl HBD MEQ HSP HOP).
  + yr_rg HS (2%bv : bv 5) Q2; yr_rg HS (3%bv : bv 5) Q3; yr_rg HS (4%bv : bv 5) Q4;
    yr_rg HS (8%bv : bv 5) Q8; yr_rg HS (9%bv : bv 5) Q9; yr_rg HS (19%bv : bv 5) Q19;
    yr_rg HS (18%bv : bv 5) Q18; yr_rg HS (20%bv : bv 5) Q20; yr_rg HS (27%bv : bv 5) Q27;
    unfold d_rL;
    split; [unfold spZ; rewrite Q2, D60; unfold w64; apply unsigned_lit_small; exact RA|];
    split; [rewrite Q3; exact D3|]; split; [rewrite Q4; exact D4|]; split; [rewrite Q8; exact D2|];
    split; [rewrite Q9; exact D60|]; split; [rewrite Q19; exact D32|];
    split; [rewrite Q18; reflexivity|]; split; [rewrite Q20; reflexivity|]; rewrite Q27; exact D529.
  + yr_rg HS (22%bv : bv 5) Q22. rewrite Q22. reflexivity.
  + yr_rg HS (21%bv : bv 5) Q21. rewrite Q21, (DX 0%nat 531%nat eq_refl ltac:(lia)). reflexivity.
  + yr_rg HS (26%bv : bv 5) Q26. rewrite Q26, (DX 1%nat 532%nat eq_refl ltac:(lia)). reflexivity.
  + yr_rg HS (23%bv : bv 5) Q23. rewrite Q23, (DX 4%nat 535%nat eq_refl ltac:(lia)). reflexivity.
  + yr_rg HS (11%bv : bv 5) Q11. rewrite Q11, (DX 7%nat 538%nat eq_refl ltac:(lia)).
    cbn [yb_vals nth]. unfold w64. f_equal. unfold rec_len. symmetry. apply Z.min_r. lia.
  + yr_rg HS (24%bv : bv 5) Q24. rewrite Q24, (DX 7%nat 538%nat eq_refl ltac:(lia)). reflexivity.
  + yr_rg HS (25%bv : bv 5) Q25. rewrite Q25, (DX 8%nat 539%nat eq_refl ltac:(lia)). reflexivity.
Qed.

Theorem yb_s2a : forall cx h i n now op (W : world SEGS) (c : config),
  yb_c1 cx h i n now op W c ->
  SRr SEGS W c (fun W' c' => exists fr,
    yr_c2 B MT XM_LIB RLO RHI tfib_K cx h i n now op fr (rec_len (rest_of (c_pl cx) n) n) W' c').
Proof.
intros cx h i n now op W c Hpre.
destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFQ & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
  Ri & Rn & Rnow & Rop & Ropm & HR & H22 & H21 & H26 & H23 & H11 & H24 & H25 & HSP & HOP & HBD).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
pose proof asan_consts as (C1 & _).
pose proof HB as (HPRE & _).
pose proof HPRE as (HAFN & _ & _ & _ & HINdisj & _).
pose proof HAFN as (_ & _ & _ & Hgp0 & Htp0 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (c_regs cx)) with (d_S cx) in Hslo, Hshi.
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTK & HWR).
pose proof HFRM as (E & HE & HRG & HFL & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
pose proof HR as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
pose proof HSP as (V208 & V320).
pose proof HOP as (V360 & V352).
pose proof HGEO as (HFB0 & HFBc & Hh0 & HhC & HcS & Hlen & Hdisj & Hin).
pose proof HINP as (Rnm & HINPg & HINPo).
assert (Rcn : 0 <= c_n cx < 2 ^ 26)
  by (clear - HINdisj Hlen; destruct HINdisj as [(Hn0 & _) | (Hr & _)]; lia).
destruct (y_rec_bounds (rest_of (c_pl cx) n) n Rn) as (Hw1 & Hr1 & Hl1 & Hl2 & Hrt & Htk).
assert (Hb0 : 0 <= rdb (rest_of (c_pl cx) n) 0 < 256)
  by (unfold rdb; pose proof (bv_unsigned_in_range 8 (nth 0 (rest_of (c_pl cx) n) (Z_to_bv 8 0)));
      change (bv_modulus 8) with 256 in *; lia).
assert (Hb1 : 0 <= rdb (rest_of (c_pl cx) n) 1 < 256)
  by (unfold rdb; pose proof (bv_unsigned_in_range 8 (nth 1 (rest_of (c_pl cx) n) (Z_to_bv 8 0)));
      change (bv_modulus 8) with 256 in *; lia).
pose proof (y_cur_bound cx (rec_rem n) HB ltac:(clear - Hr1 Rnm Rcn; lia)) as Rcur.
pose proof (y_A_range (d_S cx) ltac:(clear - C1 Hceil Hslo; unfold MFRAME, LLVMF_STK in *; lia)) as HAr.
change (32 * ((d_S cx - MFRAME) / 32)) with (d_A cx) in HAr.
assert (HAmod : d_A cx mod 32 = 0) by (unfold d_A; rewrite Z.mul_comm; apply Z_mod_mult).
assert (RA : 0 <= d_A cx < 2 ^ 64) by (clear - C1 Hceil Hslo Hshi H47 HAr; unfold MFRAME, LLVMF_STK in *; lia).
pose proof (y_E_env cx E (yc_vals cx h i n now op regs) HE) as HEd.
pose proof HEd as (_ & _ & HEI' & _).
set (Ed := d_env cx E (yc_vals cx h i n now op regs)) in *.
assert (AO : forall q, (q < AT_FL)%nat -> ew Ed q = ew E q) by (intros q Hq; apply y_env_old; exact Hq).
assert (AX : forall j, (j < 29)%nat -> ew Ed (AT_X + j) = nth j (yc_vals cx h i n now op regs) (Z_to_bv 64 0))
  by (intros j Hj; apply y_env_x; cbn [length yc_vals]; lia).
assert (D60 : sv_denot Ed (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot Ed (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D3 : sv_denot Ed (SOff 3 0) = w64 (as_gp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 3%nat 3%bv eq_refl); exact Hgp0).
assert (D4 : sv_denot Ed (SOff 4 0) = w64 (as_tp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 4%nat 4%bv eq_refl); exact Htp0).
assert (D32 : sv_denot Ed (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E32).
assert (D529 : sv_denot Ed (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E529).
assert (DX : forall j q, q = (AT_X + j)%nat -> (j < 29)%nat ->
  sv_denot Ed (SOff q 0) = nth j (yc_vals cx h i n now op regs) (Z_to_bv 64 0))
  by (intros j q -> Hj; rewrite sv_denot_SOff0; exact (AX j Hj)).
assert (E536 : ew Ed 536 = Z_to_bv 64 (rec_len (rest_of (c_pl cx) n) n))
  by (change 536%nat with (AT_X + 5)%nat; rewrite (AX 5%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E537 : ew Ed 537 = Z_to_bv 64 (rec_rem n))
  by (change 537%nat with (AT_X + 6)%nat; rewrite (AX 6%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E538 : ew Ed 538 = Z_to_bv 64 (d_cur cx (rec_rem n)))
  by (change 538%nat with (AT_X + 7)%nat; rewrite (AX 7%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (HROK : regs_ok Ed yc_sr regs).
{ apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
  repeat (destruct Hz as [<-|Hz];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
      lazymatch goal with
      | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
      | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H18 | exact H20 | exact H22 ]
      | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
          first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
      | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
      | |- _ = sv_denot _ (SOff 3 0) => rewrite D3; exact Hgp
      | |- _ = sv_denot _ (SOff 4 0) => rewrite D4; exact Htp
      | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H19
      | |- _ = sv_denot _ (SOff 529 0) => rewrite D529; exact H27
      | |- _ = sv_denot _ (SOff ?q 0) =>
          let j := eval vm_compute in (q - 531)%nat in
          rewrite (DX j q eq_refl ltac:(lia)); cbn [nth yc_vals]; first [reflexivity | assumption]
      end
    | ]).
  destruct Hz. }
assert (HFB4 : d_FB cx + 4096 <= alloc_ceiling)
  by (change (fs_frame_bytes DFRAME_CLASS) with 4096 in HFBc; exact HFBc).
assert (HFACTS : facts_ok Ed (d_facts [] []))
  by exact (FACTS LAWS cx ly3 S3 W mem3 md3 k E (yc_vals cx h i n now op regs) [] [] HC HE I I).
assert (HACS : Forall (YP09.chunk_ok SEGS Ed (rd W mem3) (d_A cx)) yc_acs).
{ unfold yc_acs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ i);
      [rewrite (DX 0%nat 531%nat eq_refl ltac:(lia)); reflexivity
      | cbn; clear - Ri; unfold MAX_OPS in Ri; lia | lia | exact V208].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ now);
      [rewrite (DX 1%nat 532%nat eq_refl ltac:(lia)); reflexivity | cbn; clear - Rnow; lia | lia | exact V320].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ op);
      [rewrite (DX 2%nat 533%nat eq_refl ltac:(lia)); reflexivity | cbn; clear - Rop; lia | lia | exact V360].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ ((if op <? 128 then op else op - 256) mod 2 ^ 64));
      [rewrite (DX 3%nat 534%nat eq_refl ltac:(lia)); cbn [nth yc_vals]; unfold w64; symmetry; apply y_Z_to_bv_mod64
      | cbn; apply Z.mod_pos_bound; lia | lia | apply y_val_mem_mod64; exact V352].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ h);
      [rewrite (DX 8%nat 539%nat eq_refl ltac:(lia)); reflexivity
      | cbn; clear - Hh0 HhC C1; unfold HUNT_SIZE in *; lia | lia | exact V184].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (h + 440));
      [rewrite (DX 9%nat 540%nat eq_refl ltac:(lia)); reflexivity
      | cbn; clear - Hh0 HhC C1; unfold HUNT_SIZE in *; lia | lia | exact V120].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ 0); [reflexivity | cbn; lia | lia | exact V136].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OG)));
      [rewrite (DX 10%nat 541%nat eq_refl ltac:(lia)); reflexivity
      | cbn; unfold dnot, d_obj, dobj_off; clear - HFB0 HFB4 C1; lia | lia | exact V376].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OT)));
      [rewrite (DX 11%nat 542%nat eq_refl ltac:(lia)); reflexivity
      | cbn; unfold dnot, d_obj, dobj_off; clear - HFB0 HFB4 C1; lia | lia | exact V280].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OO)));
      [rewrite (DX 12%nat 543%nat eq_refl ltac:(lia)); reflexivity
      | cbn; unfold dnot, d_obj, dobj_off; clear - HFB0 HFB4 C1; lia | lia | exact V232].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OUSED)));
      [rewrite (DX 13%nat 544%nat eq_refl ltac:(lia)); reflexivity
      | cbn; unfold dnot, d_obj, dobj_off; clear - HFB0 HFB4 C1; lia | lia | exact V264]. }
pose proof (SEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E C1_OFF yc_sr
  (yc_vals cx h i n now op regs) yc_acs [] [] (d_facts [] []) HC HE HRG HFL HROK HFACTS HACS
  (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNC.
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + C1_OFF)) with (Z_to_bv 64 (BASE + C1_OFF)).
unfold ss_d in HS. fold Ed in HS.
yr_ro HS 516%nat. yr_ro HS 529%nat.
assert (A60 : bv_unsigned (ew Ed 60) = d_A cx)
  by (rewrite (AO 60%nat ltac:(unfold AT_FL; lia)), E60; unfold w64; apply unsigned_lit_small; exact RA).
assert (RFB : 0 <= d_FB cx < 2 ^ 64) by (clear - HFB0 HFB4 C1; lia).
assert (RSH : 0 <= shadow_addr (d_FB cx) < 2 ^ 64)
  by (unfold shadow_addr; apply y_shaddr_range; exact RFB).
assert (A516 : bv_unsigned (ew Ed 516) = d_FB cx)
  by (rewrite (AO 516%nat ltac:(unfold AT_FL; lia)), E516; unfold w64; apply unsigned_lit_small; exact RFB).
assert (A529 : bv_unsigned (ew Ed 529) = shadow_addr (d_FB cx))
  by (rewrite (AO 529%nat ltac:(unfold AT_FL; lia)), E529; unfold w64; apply unsigned_lit_small; exact RSH).
destruct (y_geom B LAWS MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k HC) as
  (GS16 & GSlo & GShi & GFB0 & GFBc & GFBapp & GFBimg & GFBmod & GFpres & GSHpres & GWpres & GAR & Gfin & GEFB & GEFL).
paj_run_to_sh RUNTO HS HJ 0xd70.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end.
  eapply (y_awr Ed cx ly3);
    [ vm_compute; reflexivity | exact A60 | exact A516 | exact A529
    | clear - HAr; unfold MFRAME in *; lia | clear - HAr; unfold MFRAME, LLVMF_STK in *; lia | exact GEFB ]. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hna. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros (rr & Hrin & Hrr).
  lazymatch type of Hrin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hrin end.
  cbn [In] in Hrin.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx end; try contradiction; subst rr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr;
  rewrite ?A60, ?A516, ?A529 in Hrr; lia. }
assert (E539h : ew Ed 539 = w64 h)
  by (change 539%nat with (AT_X + 8)%nat; rewrite (AX 8%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E540h : ew Ed 540 = w64 (h + 440))
  by (change 540%nat with (AT_X + 9)%nat; rewrite (AX 9%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E541g : ew Ed 541 = w64 (dnot (d_obj cx OG)))
  by (change 541%nat with (AT_X + 10)%nat; rewrite (AX 10%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E542t : ew Ed 542 = w64 (dnot (d_obj cx OT)))
  by (change 542%nat with (AT_X + 11)%nat; rewrite (AX 11%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E543o : ew Ed 543 = w64 (dnot (d_obj cx OO)))
  by (change 543%nat with (AT_X + 12)%nat; rewrite (AX 12%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E544u : ew Ed 544 = w64 (dnot (d_obj cx OUSED)))
  by (change 544%nat with (AT_X + 13)%nat; rewrite (AX 13%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (Rh64 : 0 <= h < 2 ^ 64) by (clear - Hh0 HhC C1; unfold HUNT_SIZE in *; lia).
assert (Rh440 : 0 <= h + 440 < 2 ^ 64) by (clear - Hh0 HhC C1; unfold HUNT_SIZE in *; lia).
assert (Rdn : forall o, 0 <= dnot (d_obj cx o) < 2 ^ 64).
{ intros o. unfold dnot, d_obj. destruct o; cbn [dobj_off]; clear - HFB0 HFB4 C1; lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as RA1 end.
cbn [ms_mem restrict] in RA1.
pose proof (y_slot_atom Ed cx W (ms_mem ms) _ _ _ _ _ 184 539%nat h RA1 A60
  ltac:(clear; cbn; tauto) E539h Rh64) as W184.
pose proof (y_slot_atom Ed cx W (ms_mem ms) _ _ _ _ _ 120 540%nat (h + 440) RA1 A60
  ltac:(clear; cbn; tauto) E540h Rh440) as W120.
pose proof (y_slot_lit Ed cx W (ms_mem ms) _ _ _ _ _ 136 0 RA1 A60
  ltac:(clear; cbn; tauto) ltac:(clear; lia)) as W136.
pose proof (y_slot_atom Ed cx W (ms_mem ms) _ _ _ _ _ 376 541%nat (dnot (d_obj cx OG)) RA1 A60
  ltac:(clear; cbn; tauto) E541g (Rdn OG)) as W376.
pose proof (y_slot_atom Ed cx W (ms_mem ms) _ _ _ _ _ 280 542%nat (dnot (d_obj cx OT)) RA1 A60
  ltac:(clear; cbn; tauto) E542t (Rdn OT)) as W280.
pose proof (y_slot_atom Ed cx W (ms_mem ms) _ _ _ _ _ 232 543%nat (dnot (d_obj cx OO)) RA1 A60
  ltac:(clear; cbn; tauto) E543o (Rdn OO)) as W232.
pose proof (y_slot_atom Ed cx W (ms_mem ms) _ _ _ _ _ 264 544%nat (dnot (d_obj cx OUSED)) RA1 A60
  ltac:(clear; cbn; tauto) E544u (Rdn OUSED)) as W264.
assert (HCt : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms)
  (with_vm_backing (m_vm_lazy md3) mat md3) k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
destruct (LAND LAWS FFL fq cx h dsh_loop ly3 S3 W _ k Ed _ ms HCt HEd
  (d_env_fl cx E (yc_vals cx h i n now op regs)) HS ltac:(vm_compute; reflexivity)
  W184 W120 W136 W376 W280 W232 W264) as (HFRM4 & HSHD4).
assert (HBD4 : d_body B cx h n [] dsh_loop ly3 S3 W (ms_mem ms)).
{ apply (BRT cx h n n [] dsh_loop dsh_loop ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx + 472)
    (fun a => d_A cx <= a < d_A cx + 472) HBD);
  [ clear - HAr; unfold MFRAME, LLVMF_STK in *; lia
  | clear - HAr; unfold MFRAME in *; lia
  | intros a Ha; left; exact Ha
  | exact KEEP
  | intros a _ Hp; exact (apresent_grows (w_H W) mem3 (ms_mem ms) a HG Hp)
  | exact HFRM4 | exact HSHD4 | lia ]. }
rename ms into ms1. rename mat into mat1. rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
yr_ro HS 60%nat.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end.
  eapply (y_awr Ed cx ly3);
    [ vm_compute; reflexivity | exact A60 | exact A516 | exact A529
    | clear - HAr; unfold MFRAME in *; lia | clear - HAr; unfold MFRAME, LLVMF_STK in *; lia | exact GEFB ]. }
pose proof (y_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MC.
cbn [ms_mem mkst] in MC.
pose proof (y_frame_ext cx h dsh_loop W (ms_mem ms1) (ms_mem ms) MC HFRM4) as HFRM5.
pose proof (y_shadow_ext cx dsh_loop W (ms_mem ms1) (ms_mem ms) MC HSHD4) as HSHD5.
pose proof (y_body_ext B BRT cx h n [] dsh_loop ly3 S3 W (ms_mem ms1) (ms_mem ms) MC HBD4) as HBD5.
rewrite (pal_malloc B TL) in HS. pmkst HS.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & Hfrs0 & Hnev0 & Hbb0 & _).
assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 (rec_len (rest_of (c_pl cx) n) n)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in
    change (sr_get sr r) with v end.
  rewrite sv_denot_SOff0, E536. reflexivity. }
assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + 0xd74)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in
    change (sr_get sr r) with v end.
  exact (codeptr_val _ 0xd74 HEI'). }
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS). rewrite (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (Hsp2 : spZ (ms_regs ms) = d_A cx)
  by (unfold spZ; rewrite (RG 2%bv ltac:(cbv; tauto)); exact Hsp).
assert (RS64 : 0 <= d_S cx < 2 ^ 64) by (unfold LLVMF_STK in GSlo; clear - GSlo GShi C1; lia).
assert (Hs02 : s0Z (ms_regs ms) = d_S cx).
{ unfold s0Z. rewrite (RG 8%bv ltac:(cbv; tauto)), H8. unfold w64. apply unsigned_lit_small. exact RS64. }
assert (Hra2 : raZ (ms_regs ms) = BASE + 0xd74).
{ unfold raZ. rewrite R1. apply unsigned_lit_small. pose proof pa_B_ok. pose proof pa_base_lo. lia. }
assert (USP2 : bv_unsigned (ew Ed 2) = d_S cx)
  by (rewrite (AO 2%nat ltac:(unfold AT_FL; lia)), (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E1v : ew Ed 1 = Z_to_bv 64 RA_LLVMF).
{ rewrite (AO 1%nat ltac:(unfold AT_FL; lia)), (EE 1%nat 1%bv eq_refl).
  pose proof (proj1 (proj2 HPRE)) as Hra0. unfold raZ in Hra0. rewrite <- Hra0.
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (E8v : ew Ed 8 = Z_to_bv 64 (s0Z (c_regs cx))).
{ rewrite (AO 8%nat ltac:(unfold AT_FL; lia)), (EE 8%nat 8%bv eq_refl). unfold s0Z.
  symmetry. apply Z_to_bv_bv_unsigned. }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as RSV end.
cbn [ms_mem restrict] in RSV.
assert (HRD8 : rdword (aview SEGS (w_H W) (ms_mem ms)) (d_S cx - 8) = Some RA_LLVMF).
{ apply rdword_of_val_mem; [| unfold RA_LLVMF; lia].
  replace (d_S cx - 8) with (d_S cx + (-8)) by lia.
  apply (field_of_region Ed _ 2%nat (d_S cx) _ (-104) 0 0 0 (-8) 8%N (SOff 1 0) RA_LLVMF RSV USP2
    ltac:(clear; cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite E1v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold RA_LLVMF; lia) ltac:(clear; cbn; lia)). }
assert (HRD16 : rdword (aview SEGS (w_H W) (ms_mem ms)) (d_S cx - 16) = Some (s0Z (c_regs cx))).
{ apply rdword_of_val_mem; [| unfold s0Z; apply bv_unsigned_in_range].
  replace (d_S cx - 16) with (d_S cx + (-16)) by lia.
  apply (field_of_region Ed _ 2%nat (d_S cx) _ (-104) 0 0 0 (-16) 8%N (SOff 8 0) (s0Z (c_regs cx)) RSV USP2
    ltac:(clear; cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite E8v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr (c_regs cx) 8)))
    ltac:(clear; cbn; lia)). }
clear RSV.
assert (HCt2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms)
  (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat1 md3)) mat
     (with_vm_backing (m_vm_lazy md3) mat1 md3)) k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
pose proof (y_chain cx ly3 S3 W (ms_mem ms) _ k HCt2) as HCH.
destruct (d_call_chain B MT XM_LIB RLO RHI tfib_K (pc_malloc_ra0 (as_code B)) 0xd74 cx ly3 S3 W
  (ms_mem ms) _ k (ms_regs ms) (s0Z (c_regs cx)) HCt2
  (proj2 (pal_rt_below B TL)) ltac:(clear; lia)
  ltac:(pose proof pa_base_lo as HBL; clear - HBL; try unfold IMG_LO in HBL; lia)
  ltac:(apply DUNIV; unfold d_sites; do 8 right; left; reflexivity)
  ltac:(apply DUNIV; unfold d_sites; do 2 right; left; reflexivity)
  Hsp2 Hs02 ltac:(clear - HAr; unfold MFRAME in *; lia) Hra2 HRD8 HRD16 HCH) as (ch & Hchp & Htr).
pose proof HBD4 as (T4 & G4 & Lk4 & H4 & _ & _ & _ & HBLK4 & _).
pose proof HBLK4 as (_ & _ & Hbb4 & _).
eapply SRr_bind.
{ eapply (aj_malloc_at04 (fx := fq) SEGS B LAWS pa_segs_low (pal_env B TL) ML (AMALLOC fq) W
    (ms_regs ms) (ms_mem ms) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k (rec_len (rest_of (c_pl cx) n) n) (d_A cx - d_S cx)
    (Z_to_bv 64 (BASE + 0xd74)) ch HJ).
  - exact R10.
  - unfold MALLOC_MAX. clear - Hl1 Hl2 Hr1 Rn. unfold REC_MAX in Hl2. lia.
  - clear - Hbb4 Hbb0 Hl1 Hl2 Hr1 Rn. unfold REC_MAX in Hl2. unfold HUNT_SIZE, LIVE_LIB in *. cbn [fold_right] in Hbb4. lia.
  - rewrite Hsp2. lia.
  - clear - GS16 HAmod. lia.
  - clear - HAr; unfold MFRAME in *; lia.
  - clear - HAr; unfold ASTACK, LLVMF_STK, MFRAME in *; lia.
  - rewrite (RG 3%bv ltac:(cbv; tauto)). exact Hgp.
  - rewrite (RG 4%bv ltac:(cbv; tauto)). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [pose proof pa_base_lo as HBL; clear - HBL; try unfold IMG_LO in HBL; lia | reflexivity].
  - clear - Hev Hnev0 Ri. unfold EV_HEAD, EV_PRO, EV_ITER, EV_LIB, MAX_OPS in *. lia.
  - exact Hchp.
  - exact Htr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & Hr4096 & Eab2 & HK).
apply SRr_ret. exists res.
assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 (k + 1))
  by (split; [exact HB | split; [exact HJ2 | rewrite Hfrs2; exact HFR]]).
destruct (y_geom B LAWS MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 (k + 1) HC2) as
  (_ & _ & _ & _ & _ & _ & _ & _ & GFpres2 & GSHpres2 & GWpres2 & GAR2 & Gfin2 & GEFB2 & _).
assert (Hnew : In (res, rec_len (rest_of (c_pl cx) n) n) (ablocks B ly2 S2))
  by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ DFRAME_CLASS (c_fpos cx) GAR2 Hnew Gfin2) as Hsbf.
unfold zdisjoint in Hsbf. cbn [fst snd] in Hsbf. rewrite GEFB2 in Hsbf.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsbf.
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KA2 : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha. apply K1; [clear - Ha HAr GSlo GShi C1; unfold MFRAME, LLVMF_STK in *; lia
  | clear - Ha; unfold ASTACK; lia]. }
assert (KF2 : forall a, d_FB cx <= a < d_FB cx + 4096 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Gfin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite GEFB.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - cbn beta. clear - Ha Hsbf. lia. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res (rec_len (rest_of (c_pl cx) n) n) GAR2 Hnew)
  as (_ & _ & Hcei2 & Hia2 & _).
assert (KH2 : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Gfin).
  - right. unfold in_zr. cbn [fst snd]. rewrite GEFB.
    change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - cbn beta. clear - Ha Hia2 GFB0 HFB4 C1.
    unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
assert (HFRM2 : d_frame cx h dsh_loop W2 mem2).
{ apply (y_frame_move cx h dsh_loop W W2 (ms_mem ms) mem2 RA RFB RSH RS64
    ltac:(clear - HAr; unfold MFRAME in *; lia) ltac:(clear - HAr; unfold MFRAME, LLVMF_STK in *; lia)
    KA2 KF2 KH2 GWpres2 GFpres2 GSHpres2 HFRM5). }
assert (HSHD2 : d_shadow cx dsh_loop W2 mem2)
  by (intros j Hj; rewrite (KH2 (shadow_addr (d_FB cx) + j) ltac:(unfold DFRAME_SH in Hj; lia));
      exact (HSHD5 j Hj)).
assert (Hdi : forall a, res <= a < res + req_size (rec_len (rest_of (c_pl cx) n) n) ->
  d_inxb [(res, rec_len (rest_of (c_pl cx) n) n)] a)
  by (intros a Ha; exists res, (rec_len (rest_of (c_pl cx) n) n); split; [left; reflexivity | exact Ha]).
assert (HK' : acall_kept SEGS B ly3 S3 W (ms_mem ms) W2 mem2
  (d_S cx + (d_A cx - d_S cx) - ASTACK) (d_S cx + (d_A cx - d_S cx))
  (d_inxb [(res, rec_len (rest_of (c_pl cx) n) n)])).
{ split; [exact K1|]. split.
  - intros b m j Hb Hj Hne. exact (K2 b m j Hb Hj (fun Hc2 => Hne (Hdi _ Hc2))).
  - split; [exact K3|]. split.
    + intros cid pos a Hf Hz Hne. exact (K4 cid pos a Hf Hz (fun Hc2 => Hne (Hdi _ Hc2))).
    + split; [exact K5 | exact K6]. }
assert (HBD2 : d_body B cx h n [(res, rec_len (rest_of (c_pl cx) n) n)] dsh_loop ly2 S2 W2 mem2).
{ pose proof (BMALLOC LAWS DRO DCAN cx h n [] dsh_loop dsh_loop ly3 S3 W (ms_mem ms) _ k ly2 S2 W2 mem2 md2 (k + 1)
    (d_S cx + (d_A cx - d_S cx) - ASTACK) (d_S cx + (d_A cx - d_S cx))
    [(res, rec_len (rest_of (c_pl cx) n) n)] HBD5
    (conj HB HJ) (conj HB HJ2) ltac:(clear; cbn; lia)
    ltac:(clear - HAr; unfold ASTACK, MFRAME, LLVMF_STK in *; lia)
    ltac:(clear - HAr; unfold MFRAME in *; lia) Eab2
    ltac:(apply Forall_cons; [cbn [fst snd]; exact (blk_off_imgP B _ _ _ _ _ _ _ GAR2 Hnew) | apply Forall_nil])
    HK' HFRM2 HSHD2) as HB2. cbn [app] in HB2. exact HB2. }
assert (Rlen64 : 0 <= rec_len (rest_of (c_pl cx) n) n < 2 ^ 64)
  by (clear - Hl1 Hl2 Hr1 Rn; unfold REC_MAX in Hl2; lia).
assert (Rop64 : 0 <= op < 2 ^ 64) by (clear - Rop; lia).
assert (Ri64 : 0 <= i < 2 ^ 64) by (clear - Ri; unfold MAX_OPS in Ri; lia).
assert (Rsop : 0 <= (if op <? 128 then op else op - 256) mod 2 ^ 64 < 2 ^ 64)
  by (apply Z.mod_pos_bound; lia).
assert (E531 : ew Ed 531 = w64 i)
  by (change 531%nat with (AT_X + 0)%nat; rewrite (AX 0%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E532 : ew Ed 532 = w64 now)
  by (change 532%nat with (AT_X + 1)%nat; rewrite (AX 1%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E533 : ew Ed 533 = w64 op)
  by (change 533%nat with (AT_X + 2)%nat; rewrite (AX 2%nat ltac:(lia)); cbn [yc_vals nth]; reflexivity).
assert (E534 : ew Ed 534 = w64 ((if op <? 128 then op else op - 256) mod 2 ^ 64)).
{ change 534%nat with (AT_X + 3)%nat; rewrite (AX 3%nat ltac:(lia)); cbn [yc_vals nth].
  unfold w64. symmetry. apply y_Z_to_bv_mod64. }
pose proof (y_slot_atom Ed cx W (ms_mem ms1) _ _ _ _ _ 408 536%nat _ RA1 A60
  ltac:(clear; cbn; tauto) E536 Rlen64) as W408.
pose proof (y_slot_atom Ed cx W (ms_mem ms1) _ _ _ _ _ 208 531%nat i RA1 A60
  ltac:(clear; cbn; tauto) E531 Ri64) as W208.
pose proof (y_slot_atom Ed cx W (ms_mem ms1) _ _ _ _ _ 320 532%nat now RA1 A60
  ltac:(clear; cbn; tauto) E532 Rnow) as W320.
pose proof (y_slot_atom Ed cx W (ms_mem ms1) _ _ _ _ _ 360 533%nat op RA1 A60
  ltac:(clear; cbn; tauto) E533 Rop64) as W360.
pose proof (y_slot_atom Ed cx W (ms_mem ms1) _ _ _ _ _ 352 534%nat _ RA1 A60
  ltac:(clear; cbn; tauto) E534 Rsop) as W352.
assert (MV : forall a v, d_A cx <= a -> a + 8 <= d_S cx ->
  val_mem SEGS (rd W (ms_mem ms1)) a 8 v -> val_mem SEGS (rd W2 mem2) a 8 v).
{ intros a v Ha1 Ha2 Hv.
  apply (y_val_move W W2 (ms_mem ms) mem2); [intros x Hx; apply KA2; cbn [Z.of_nat] in Hx; lia|].
  exact (y_val_ext W (ms_mem ms1) (ms_mem ms) a 8 v MC Hv). }
assert (RP : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr regs2 r = getr regs r).
{ intros r Hr. rewrite <- (RG r Hr). cbv [In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [ match goal with |- getr _ ?rr = _ => let z := eval vm_compute in (bv_unsigned rr) in
        exact (HP2 z ltac:(unfold acallee_saved; lia)) end | ]).
  destruct Hr. }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
exists fq, ly2, S2, regs2, mem2, md2, (k + 1), 0.
split; [unfold cfg_at; reflexivity|].
split; [exact HFQ|].
split; [exact HB|]. split; [exact HJ2|]. split; [rewrite Hfrs2; exact HFR|].
split; [clear - Hk; lia|].
split; [clear - Hnev2 Hev Hk; unfold EV_HEAD in *; lia|].
split; [rewrite MT_TRIV; exact I|].
split; [unfold ACC_HEAD, ACC_PRO, ACC_ITER; rewrite MT_TRIV; cbn [mo_malloc mo_free ameter_triv]; lia|].
split; [exact Ri|]. split; [exact Rn|]. split; [exact Rnow|]. split; [exact Rop|]. split; [exact Ropm|].
split; [exact Hr4096|]. split; [clear - Hl1 Hl2; lia|]. split; [exact (proj2 Hl1)|].
split; [clear - Hr1 Rnm Rcn; lia|]. split; [clear - Hr1 Rnm; lia|].
split.
{ destruct HR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q19 & Q18 & Q20 & Q27).
  unfold d_rL, spZ.
  rewrite !RP by (cbv; tauto).
  repeat split; assumption. }
split; [rewrite (RP 22%bv ltac:(cbv; tauto)); exact H22|].
split; [rewrite (RP 21%bv ltac:(cbv; tauto)); exact H21|].
split; [rewrite (RP 26%bv ltac:(cbv; tauto)); exact H26|].
split; [rewrite (RP 23%bv ltac:(cbv; tauto)); exact H23|].
split; [exact Ha0|].
split; [rewrite (RP 24%bv ltac:(cbv; tauto)); exact H24|].
split; [rewrite (RP 25%bv ltac:(cbv; tauto)); exact H25|].
split; [apply MV; [clear - HAr; lia | clear - HAr; unfold MFRAME in *; lia | exact W408]|].
split; [split; apply MV; [clear - HAr; lia | clear - HAr; unfold MFRAME in *; lia | exact W208
                          | clear - HAr; lia | clear - HAr; unfold MFRAME in *; lia | exact W320]|].
split; [split; [apply MV; [clear - HAr; lia | clear - HAr; unfold MFRAME in *; lia | exact W360]
               | apply y_val_mem_unmod64; apply MV;
                 [clear - HAr; lia | clear - HAr; unfold MFRAME in *; lia | exact W352]]|].
exact HBD2.
Qed.


Theorem pb_rec : rec_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold rec_spec. intros cx h i n now op W c Hin.
assert (S2B : yr_s2b_stmt B MT XM_LIB RLO RHI tfib_K) by (apply pb_rec_copy; assumption).
pose proof (yr_pb_head B LAWS MT XM_LIB RLO RHI tfib_K TL SEAT FACTS BRT) as HEAD.
pose proof (yr_pb_arm B LAWS TL MT XM_LIB RLO RHI tfib_K SEAT FACTS BRT) as ARM.
eapply SRr_bind; [exact (HEAD cx h i n now op W c Hin) |].
intros W1 c1 _ HJ1.
eapply SRr_bind; [exact (yb_s1 cx h i n now op W1 c1 HJ1) |].
intros W2 c2 _ HC1.
eapply SRr_bind; [exact (yb_s2a cx h i n now op W2 c2 HC1) |].
intros W3 c3 _ (fr & HC2).
eapply SRr_bind; [exact (S2B cx h i n now op fr _ W3 c3 HC2) |].
intros W4 c4 _ HM.
eapply SRr_bind; [exact (ARM cx h i n now op (rec_rem n) fr _ W4 c4 HM) |].
intros W5 c5 _ HA. apply SRr_ret.
exists (rec_rem n), fr, (rec_len (rest_of (c_pl cx) n) n).
split; [reflexivity|]. split; [reflexivity|]. exact HA.
Qed.

End h.
End f.
End d.
