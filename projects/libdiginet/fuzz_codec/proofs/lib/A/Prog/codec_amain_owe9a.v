(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module names changed; 414 of its 469 lines of code are new or changed and 578 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owel.v, with its module names changed; 578 of its 651 lines of code are new or changed and 396 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe9_lib.v; 746 of its 788 lines of code are new or changed and 609 lines of the source are left out. *)
(* Segment OWE9 (SCRIBBLE, owe_pc 9 = 0x8230c .. CHK 0x8273c) of the image-A walk of LLVMFuzzerTestOneInput
   (lib/A/Prog/codec_amain_inv.v seg_owe 9), for the Control|24 desk (chars = 4): the k.a range test, the four
   seven-bit checks with their E_RANGE tails, pl at F + 32 marked usable and filled, __asan_memcpy(pl + 2,
   k.bytes, 4) and __asan_memcpy(want + 4, pl, 6) through CPgWalkIntr's cw_intrin_call, the want fields, pl
   marked unusable, to CHK. The tactics are shared with codec_amain_owe9b.v (ProControl). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkIntr CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_owel codec_amain_owex codec_amain_owe9_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Ltac o9_unf := repeat (first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]).
Ltac o9_unf_in H := repeat (first [rewrite ew_ewset_other in H by lia | rewrite ew_havoc_old in H by lia]).
Ltac o9_den En := rewrite (am_den_off _ _ _ 0 En) by lia; rewrite Z.add_0_r; reflexivity.
Ltac o9_dis :=
  lazymatch goal with |- all_disjoint ?Ev ?r ?rs =>
    let r' := eval vm_compute in r in let rs' := eval vm_compute in rs in
    change (all_disjoint Ev r' rs') end;
  cbn [all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; o9_unf;
  repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- context [bv_unsigned (ew _ ?n)] => rewrite U end;
  try (unfold shadow_addr, SHADOW_OFF, SB in * ); try (unfold A_GOT_shadow, A_shadow_glob in * );
  try appn; repeat split; lia.

Ltac o9_submem :=
  repeat first
  [ apply submem_nil
  | apply submem_keep;
    [ unfold subregion; cbn; repeat split;
      first [ reflexivity | lia | (left; lia) | (right; split; lia)
            | (let cc := fresh in let Hc := fresh in intros cc Hc; cbn [In] in Hc |- *; tauto) ] | ]
  | apply submem_drop ].

Ltac o9_awr :=
  idtac;
  let U2 := lazymatch goal with H : bv_unsigned (ew _ 2) = _ |- _ => H end in
  let sp1 := lazymatch type of U2 with _ = ?s => s end in
  let U33 := lazymatch goal with H : bv_unsigned (ew _ 33) = FA _ _ |- _ => H end in
  let pos := lazymatch type of U33 with _ = FA _ ?p => p end in
  let U34 := lazymatch goal with H : bv_unsigned (ew _ 34) = shadow_addr (FA _ _) |- _ => H end in
  let EFA := lazymatch goal with H : frame_addr _ 3 _ = FA _ _ |- _ => H end in
  let spz := lazymatch goal with |- awr_ok _ _ _ ?s _ _ _ _ _ => s end in
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ spz _ _ _ _ _ 2%nat (sp1 - spz));
    [reflexivity | o9_unf; rewrite U2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 3 pos 33%nat);
    [reflexivity | o9_unf; rewrite EFA; exact U33 | left; reflexivity | cbn [YP09.r_wlo]; lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 3) with 512; lia |]
  | eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 pos 34%nat);
    [reflexivity | o9_unf; rewrite EFA; exact U34 | left; reflexivity | cbn [YP09.r_wlo]; lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 3 / 8) with 64; lia |] ].

Ltac o9_kwr zone :=
  idtac;
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; o9_unf_in Hb;
      repeat match goal with U : bv_unsigned (ew _ ?n) = _, Hb' : context [bv_unsigned (ew _ ?n)] |- _ =>
        rewrite U in Hb' end;
      unfold zone; lia | ]);
  destruct Hr.

Ltac o9_keep z := cw_keep ltac:(o9_kwr z);
  lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => repeat (rewrite wvb_collapse in HJx) end.

Ltac o9_fix En := repeat (first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]); exact En.
Ltac o9_sb kk Hkd j := unfold owe_kZ; rewrite Hkd; apply owe9_rng_s;
  apply (o9_sb_false (kz_bytes kk) _ j); [vm_compute; lia | lia | lia | lia].

Ltac o9_err why U33 HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE KE :=
  cw_run_to o9_awr 0x8273c;
  cw_keep ltac:(o9_kwr owe_zone);
  lazymatch goal with HSx : st_ok _ _ _ _ |- _ =>
    let Ems := fresh "Ems" in
    pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HSx eq_refl) as Ems;
    rewrite Ems in HSx; rewrite Ems; clear Ems;
    let Hrw := fresh "Hrw" in let Hrl := fresh "Hrl" in
    owe_region HSx 6%nat Hrw; owe_region HSx 7%nat Hrl;
    rewrite restrict_mkst_fx in Hrw, Hrl; cbn [ms_mem] in Hrw, Hrl;
    unfold am_frame_region in Hrw, Hrl;
    let Uc := fresh "Uc" in
    lazymatch type of HSx with st_ok _ ?Ec _ _ =>
      lazymatch type of U33 with _ = ?Fv =>
        assert (Uc : bv_unsigned (ew Ec 33) = Fv) by (o9_unf; exact U33) end end;
    let V1 := fresh "V1" in let V2 := fresh "V2" in let V3 := fresh "V3" in let V4 := fresh "V4" in
    pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 316 4 _ Hrw Uc ltac:(owe_in) ltac:(lia)) as V1;
    pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 344 8 _ Hrl Uc ltac:(owe_in) ltac:(lia)) as V2;
    pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 352 4 _ Hrl Uc ltac:(owe_in) ltac:(lia)) as V3;
    pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 356 4 _ Hrl Uc ltac:(owe_in) ltac:(lia)) as V4;
    eapply o9_err_fin;
    [ assumption | exact HJ0 | exact Hfr | exact Hk | exact Hmo | exact HC | exact Hops | exact Hcur | exact Hkat
    | exact Hrec | exact Hrc | eassumption | exact HSx | env_agree_chain HAE
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | exact KE
    | apply (owe_vm _ _ 4 _ _ V1); vm_compute; reflexivity
    | apply (owe_vm _ _ 8 _ _ V2); vm_compute; reflexivity
    | apply (owe_vm _ _ 4 _ _ V3); vm_compute; reflexivity
    | apply (owe_vm _ _ 4 _ _ V4); vm_compute; reflexivity
    | why ]
  end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy 0x51998.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.

Lemma o9_walk_c24 : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 ->
rec_okZ k (Some c24) -> kz_kind k = 9 -> kz_rc k = fst (enc_kZ k (Some c24)) ->
kz_want_rc k = 0 -> kz_want_len k = 0 -> kz_want_key k = 0 -> kz_want_display k = 0 ->
getr regs2 23 = w64 (kz_desk k) ->
SRr tfibsegs W2 (cfg_at tfibsegs (owe_pc 9) regs2 mem2 md2) (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof using TL LAWS AMEMCPY GM IV ROB.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hkind Hrc Hwrc Hwl Hwk Hwd R23.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof Hrec as (_ & Hpd & Hrdr & _).
destruct (pd_range_A _ _ _ Hpd) as (_ & Hdv & Rdev & Rstr & Rchr & Rctr).
pose proof (owe_desk_range _ _ _ Hpd) as Hdr.
pose proof Hrdr as (Ra & Rb & Rcc & Rdl & Rlen & Rby & Rn & _).
pose proof Hkat as ((Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gby & Vn & Vrc & Gbef & Gout & Vwrc & Gwant &
  Vwl & Vwk & Vwd) & Hwf).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
unfold AM_HI in Hchi. change (fs_frame_bytes 3) with 512 in Hfceil.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HC as (Hpre & _ & R2 & _).
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 kj Hpre HJ) as HRO.
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
assert (D2 : 512 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia).
assert (D1 : FA g pos / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
assert (D3 : 8 * (FA g pos / 8) <= FA g pos) by (apply Z.mul_div_le; lia).
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44)
  by (unfold shadow_addr, SHADOW_OFF, SB; lia).
assert (Hfsh : FA g pos + 512 <= shadow_addr (FA g pos) \/ shadow_addr (FA g pos) + 64 <= FA g pos).
{ unfold in_app in Happ. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  destruct Happ as (_ & [Hlow | (Hh1 & Hh2)]); [left; lia|].
  right. assert (D4 : 2199291686912 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (Hap : FA g pos + 512 <= kz_desk k + 8 \/ kz_desk k + 8 + 4 <= FA g pos + 0).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos (kz_desk k + 8) 4 0 512 HAR Hin) as G.
  rewrite EFA in G. change (fs_frame_bytes 3) with 512 in G. apply G; lia. }
assert (Hgot : FA g pos + 512 <= A_GOT_shadow \/ A_GOT_shadow + 8 <= FA g pos + 0).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos A_GOT_shadow 8 0 512 HAR Hin) as G.
  rewrite EFA in G. change (fs_frame_bytes 3) with 512 in G. unfold A_GOT_shadow in *. apply G; lia. }
assert (Hbc : FA g pos + 512 <= A_shadow_glob \/ A_shadow_glob + 8 <= FA g pos + 0).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos A_shadow_glob 8 0 512 HAR Hin) as G.
  rewrite EFA in G. change (fs_frame_bytes 3) with 512 in G. unfold A_shadow_glob in *. apply G; lia. }
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof HC as (_ & Hsp1e & _).
(* the bytes of k.bytes *)
assert (BY : forall j, (j < 8)%nat ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + (216 + Z.of_nat j)) 1 (nth j (kz_bytes k) 0) /\
  0 <= nth j (kz_bytes k) 0 < 256).
{ intros j Hj. destruct (Gby j ltac:(rewrite Rlen; lia)) as [G1 G2]. split; [|exact G2].
  replace (FA g pos + (216 + Z.of_nat j)) with (FA g pos + 176 + 40 + Z.of_nat j) by lia. exact G1. }
pose proof (BY 0%nat ltac:(lia)) as (V216 & Q0). pose proof (BY 1%nat ltac:(lia)) as (V217 & Q1).
pose proof (BY 2%nat ltac:(lia)) as (V218 & Q2). pose proof (BY 3%nat ltac:(lia)) as (V219 & Q3).
pose proof (BY 4%nat ltac:(lia)) as (V220 & Q4). pose proof (BY 5%nat ltac:(lia)) as (V221 & Q5).
pose proof (BY 6%nat ltac:(lia)) as (V222 & Q6). pose proof (BY 7%nat ltac:(lia)) as (V223 & Q7).
(* the environment *)
set (ys := o9_ys k).
remember (am_env g pos c regs2 ys) as E eqn:HEE.
assert (HAE : env_agree 37 (am_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (kz_a k)) by (subst E; exact (am_ew_y g pos c regs2 ys 0)).
assert (E38 : ew E 38 = Z_to_bv 64 (nth 0 (kz_bytes k) 0)) by (subst E; exact (am_ew_y g pos c regs2 ys 1)).
assert (E39 : ew E 39 = Z_to_bv 64 (nth 1 (kz_bytes k) 0)) by (subst E; exact (am_ew_y g pos c regs2 ys 2)).
assert (E40 : ew E 40 = Z_to_bv 64 (nth 2 (kz_bytes k) 0)) by (subst E; exact (am_ew_y g pos c regs2 ys 3)).
assert (E41 : ew E 41 = Z_to_bv 64 (nth 3 (kz_bytes k) 0)) by (subst E; exact (am_ew_y g pos c regs2 ys 4)).
assert (E42 : ew E 42 = Z_to_bv 64 (nth 4 (kz_bytes k) 0)) by (subst E; exact (am_ew_y g pos c regs2 ys 5)).
assert (E43 : ew E 43 = Z_to_bv 64 (nth 5 (kz_bytes k) 0)) by (subst E; exact (am_ew_y g pos c regs2 ys 6)).
assert (E44 : ew E 44 = Z_to_bv 64 (nth 6 (kz_bytes k) 0)) by (subst E; exact (am_ew_y g pos c regs2 ys 7)).
assert (E45 : ew E 45 = Z_to_bv 64 (nth 7 (kz_bytes k) 0)) by (subst E; exact (am_ew_y g pos c regs2 ys 8)).
assert (E23 : ew E 23 = Z_to_bv 64 (kz_desk k))
  by (subst E; rewrite (am_ew_reg g pos c regs2 ys 23 23%bv eq_refl), R23; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; exact (am_ew_F g pos c regs2 ys)).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (subst E; exact (am_ew_SH g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (am_ew_SB g pos c regs2 ys)).
assert (Eq2 : ew E 2 = Z_to_bv 64 sp1)
  by (subst E; rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp1)
  by (subst E; rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = FA g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (FA g pos))
  by (rewrite E34; apply unsigned_lit_small; unfold SB in Hsh; lia).
assert (U23 : bv_unsigned (ew E 23) = kz_desk k) by (rewrite E23; apply unsigned_lit_small; lia).
(* the start state *)
assert (HRS : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) (o9_rs c24)).
{ unfold o9_rs. repeat apply Forall_cons; try apply Forall_nil.
  - unfold o9_rk. rewrite HEE.
    apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 200 224 200 200
      _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite <- HEE. repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 200 4 (SOff 37 0) (kz_a k)); [o9_den E37 | cbn; lia | cbn; lia |].
      replace (FA g pos + 200) with (FA g pos + 176 + 24) by lia. exact Va.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 216 1 (SOff 38 0) (nth 0 (kz_bytes k) 0));
      [o9_den E38 | cbn; lia | cbn; lia |].
      replace (FA g pos + 216) with (FA g pos + (216 + Z.of_nat 0)) by lia. exact V216.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 217 1 (SOff 39 0) (nth 1 (kz_bytes k) 0));
      [o9_den E39 | cbn; lia | cbn; lia |].
      replace (FA g pos + 217) with (FA g pos + (216 + Z.of_nat 1)) by lia. exact V217.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 218 1 (SOff 40 0) (nth 2 (kz_bytes k) 0));
      [o9_den E40 | cbn; lia | cbn; lia |].
      replace (FA g pos + 218) with (FA g pos + (216 + Z.of_nat 2)) by lia. exact V218.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 219 1 (SOff 41 0) (nth 3 (kz_bytes k) 0));
      [o9_den E41 | cbn; lia | cbn; lia |].
      replace (FA g pos + 219) with (FA g pos + (216 + Z.of_nat 3)) by lia. exact V219.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 220 1 (SOff 42 0) (nth 4 (kz_bytes k) 0));
      [o9_den E42 | cbn; lia | cbn; lia |].
      replace (FA g pos + 220) with (FA g pos + (216 + Z.of_nat 4)) by lia. exact V220.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 221 1 (SOff 43 0) (nth 5 (kz_bytes k) 0));
      [o9_den E43 | cbn; lia | cbn; lia |].
      replace (FA g pos + 221) with (FA g pos + (216 + Z.of_nat 5)) by lia. exact V221.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 222 1 (SOff 44 0) (nth 6 (kz_bytes k) 0));
      [o9_den E44 | cbn; lia | cbn; lia |].
      replace (FA g pos + 222) with (FA g pos + (216 + Z.of_nat 6)) by lia. exact V222.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 223 1 (SOff 45 0) (nth 7 (kz_bytes k) 0));
      [o9_den E45 | cbn; lia | cbn; lia |].
      replace (FA g pos + 223) with (FA g pos + (216 + Z.of_nat 7)) by lia. exact V223.
  - unfold o9_rr. subst E.
    apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 316 320 316 320
      _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val tfibsegs _ _ (FA g pos) 316 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    replace (FA g pos + 316) with (FA g pos + 176 + 140) by lia. rewrite <- Hwrc. exact Vwrc.
  - unfold o9_rf. subst E.
    apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 344 360 344 360
      _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val tfibsegs _ _ (FA g pos) 344 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia. rewrite <- Hwl. exact Vwl.
    + apply (chunk_ok_val tfibsegs _ _ (FA g pos) 352 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia. rewrite <- Hwk. exact Vwk.
    + apply (chunk_ok_val tfibsegs _ _ (FA g pos) 356 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia. rewrite <- Hwd. exact Vwd.
  - unfold o9_rg.
    apply (owe_desk_region_ok B TL E W2 mem2 (kz_p k) (kz_desk k) c24 _ HRO Hpd U23).
    intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth desk_bytesZ sv_denot]; try reflexivity. lia. }
assert (HPD : pairwise_disjoint E (o9_rs c24)).
{ unfold o9_rs, o9_rk, o9_rr, o9_rf, o9_rg, owe_desk_region, am_frame_region.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33, U23. repeat split; lia. }
assert (HAP : Forall (fun r => all_disjoint E r am_regs) (o9_rs c24)).
{ unfold o9_rs. rewrite HEE. repeat apply Forall_cons; try apply Forall_nil.
  - exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 200 224 200 200 _
      HJ Hfr HC ltac:(lia) ltac:(lia)).
  - exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 316 320 316 320 _
      HJ Hfr HC ltac:(lia) ltac:(lia)).
  - exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 344 360 344 360 _
      HJ Hfr HC ltac:(lia) ltac:(lia)).
  - rewrite <- HEE. exact (owe_desk_apart_base E _ (kz_desk k) sp1 U23 Hdr U2 ltac:(lia)). }
assert (HAF : atoms_ok E o9_AF).
{ unfold o9_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E23, E37, E38, E39, E40, E41, E42, E43, E44, E45.
  rewrite !unsigned_lit_small by (pose proof (BY 0%nat ltac:(lia)); pose proof (BY 1%nat ltac:(lia));
    pose proof (BY 2%nat ltac:(lia)); pose proof (BY 3%nat ltac:(lia)); pose proof (BY 4%nat ltac:(lia));
    pose proof (BY 5%nat ltac:(lia)); pose proof (BY 6%nat ltac:(lia)); pose proof (BY 7%nat ltac:(lia)); lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  pose proof (BY 0%nat ltac:(lia)); pose proof (BY 1%nat ltac:(lia)); pose proof (BY 2%nat ltac:(lia));
  pose proof (BY 3%nat ltac:(lia)); pose proof (BY 4%nat ltac:(lia)); pose proof (BY 5%nat ltac:(lia));
  pose proof (BY 6%nat ltac:(lia)); pose proof (BY 7%nat ltac:(lia)).
  destruct Hdv as [Hd1 | Hd1]; rewrite Hd1; repeat split; first [reflexivity | lia]. }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 9) ys (o9_rs c24) o9_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity)) as HS.
rewrite <- HEE in HS. specialize (HS HRS HPD HAP HAF).
assert (SHOK : sh_ok tfibsegs CW_Bx o9_SH E (mrestrict (w_H W2) mem2)).
{ unfold o9_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p k) (kz_desk k) c24 GM IV HAR Hpd E23 E32).
  - subst E. exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 0 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof (owe_U_sx32 E 37 (kz_a k) E37 ltac:(lia)) as Ua.
unfold cfg_at. change (w64 (owe_pc 9)) with (Z_to_bv 64 0x8230c).
cw_keep_j0 HJ HJ0.
(* 0x8230c-0x82314: lw s8,24(s6); li a0,127; bltu a0,s8 *)
cw_run o9_awr. o9_keep owe_zone.
cw_branch Hb1.
all: rewrite branch_ltu_U, U_lit, Ua in Hb1 by lia.
{ (* 127 < a: the E_RANGE tail *)
  apply Z.ltb_lt in Hb1.
  assert (Ha : 127 < kz_a k) by (destruct (Z.ltb_spec (kz_a k) (2 ^ 31)); lia).
  o9_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe9_rng_a; lia) U33 HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE KE. }
apply Z.ltb_ge in Hb1.
assert (Ha : kz_a k <= 127) by (destruct (Z.ltb_spec (kz_a k) (2 ^ 31)); lia).
(* 0x82318-0x82364: the desk's chars (4), then the four bytes' seven-bit checks *)
cw_run o9_awr. o9_keep owe_zone.
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (F0 : ew Ec 38 = Z_to_bv 64 (nth 0 (kz_bytes k) 0)) by (o9_fix E38) end.
cw_branch Hb. all: rewrite (o9_br_sx8 _ _ _ F0 ltac:(lia)) in Hb. clear F0.
{ apply Z.ltb_lt in Hb.
  o9_err ltac:(o9_sb k Hkind 0%nat) U33 HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE KE. }
apply Z.ltb_ge in Hb. rename Hb into Hby0.
cw_run o9_awr. o9_keep owe_zone.
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (F1 : ew Ec 39 = Z_to_bv 64 (nth 1 (kz_bytes k) 0)) by (o9_fix E39) end.
cw_branch Hb. all: rewrite (o9_br_sx8 _ _ _ F1 ltac:(lia)) in Hb. clear F1.
{ apply Z.ltb_lt in Hb.
  o9_err ltac:(o9_sb k Hkind 1%nat) U33 HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE KE. }
apply Z.ltb_ge in Hb. rename Hb into Hby1.
cw_run o9_awr. o9_keep owe_zone.
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (F2 : ew Ec 40 = Z_to_bv 64 (nth 2 (kz_bytes k) 0)) by (o9_fix E40) end.
cw_branch Hb. all: rewrite (o9_br_sx8 _ _ _ F2 ltac:(lia)) in Hb. clear F2.
{ apply Z.ltb_lt in Hb.
  o9_err ltac:(o9_sb k Hkind 2%nat) U33 HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE KE. }
apply Z.ltb_ge in Hb. rename Hb into Hby2.
cw_run o9_awr. o9_keep owe_zone.
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (F3 : ew Ec 41 = Z_to_bv 64 (nth 3 (kz_bytes k) 0)) by (o9_fix E41) end.
cw_branch Hb. all: rewrite (o9_br_sx8 _ _ _ F3 ltac:(lia)) in Hb. clear F3.
{ apply Z.ltb_lt in Hb.
  o9_err ltac:(o9_sb k Hkind 3%nat) U33 HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE KE. }
apply Z.ltb_ge in Hb. rename Hb into Hby3.
(* 0x82358-0x82368: the loop is done, to 0x8284c *)
cw_run_to o9_awr 0x8284c. o9_keep owe_zone.
(* ---- 0x8284c-0x82898: s3 spilled, pl marked usable and filled, __asan_memcpy(pl + 2, k.bytes, 4) ---- *)
pose proof (o9_widen _ _ _ g pos sp1 4 ltac:(lia) KE) as KE2. clear KE. rename KE2 into KE.
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (Uc2 : bv_unsigned (ew Ec 2) = sp1) by (o9_unf; exact U2);
  assert (Uc33 : bv_unsigned (ew Ec 33) = FA g pos) by (o9_unf; exact U33);
  assert (Uc34 : bv_unsigned (ew Ec 34) = shadow_addr (FA g pos)) by (o9_unf; exact U34);
  assert (Uc23 : bv_unsigned (ew Ec 23) = kz_desk k) by (o9_unf; exact U23) end.
pose proof (o9_add_region _ _ _ o9_rsp HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_mem restrict]; eapply o9_swin_ok;
        [ exact Uc2 | intros aa Haa; eapply o9_jpres; [eassumption | lia] | lia | lia | lia ])
  ltac:(o9_dis)) as HSn. clear HS. rename HSn into HS.
pose proof (o9_add_region _ _ _ o9_rpl HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_mem restrict]; unfold o9_rpl; eapply (o9_fwin_ok B LAWS);
        [ lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (proj1 HJx) end
        | exact Hin | rewrite EFA; exact Uc33 | lia | lia | lia | lia | lia ])
  ltac:(o9_dis)) as HSn. clear HS. rename HSn into HS.
pose proof (o9_add_region _ _ _ o9_rsh HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_mem restrict]; unfold o9_rsh; eapply (o9_shwin_ok B LAWS);
        [ lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (proj1 HJx) end
        | exact Hin | rewrite EFA; exact Uc34 | lia | lia | lia ])
  ltac:(o9_dis)) as HSn. clear HS. rename HSn into HS.
clear Uc2 Uc33 Uc34 Uc23.
aj_run_to_sh tfibtbl_lib_ok HS HJ 0x51998.
{ o9_awr. }
o9_keep o9_zone.
(* the shadow bytes of pl and the payload's first two bytes, read off the regions the run wrote *)
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (Ec2 : ew Ec 2 = Z_to_bv 64 sp1) by (o9_unf; exact Eq2);
  assert (Ec33 : ew Ec 33 = Z_to_bv 64 (FA g pos)) by (o9_unf; exact E33);
  assert (Ec34 : ew Ec 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (o9_unf; exact E34);
  assert (Ec37 : ew Ec 37 = Z_to_bv 64 (kz_a k)) by (o9_unf; exact E37) end.
assert (Uc33 : bv_unsigned (ew _ 33) = FA g pos) by (rewrite Ec33; apply unsigned_lit_small; lia).
assert (Uc34 : bv_unsigned (ew _ 34) = shadow_addr (FA g pos))
  by (rewrite Ec34; apply unsigned_lit_small; unfold SB in Hsh; lia).
owe_region HS 0%nat Hr0. owe_region HS 1%nat Hr1.
cbn [ms_mem restrict] in Hr0, Hr1.
pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 4 (SLit 0) Hr0
  ltac:(cbn [YP09.r_base base_val]; exact Uc34) ltac:(owe_in)) as SH4.
pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 5 (SLit 2) Hr0
  ltac:(cbn [YP09.r_base base_val]; exact Uc34) ltac:(owe_in)) as SH5.
pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 32 (SExt true 32 (SOff 37 0)) Hr1
  ltac:(cbn [YP09.r_base base_val]; exact Uc33) ltac:(owe_in)) as PL0.
pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 33 (SLit 0) Hr1
  ltac:(cbn [YP09.r_base base_val]; exact Uc33) ltac:(owe_in)) as PL1.
change (bv_unsigned (sv_denot _ (SLit 0)) mod 256) with 0 in SH4, PL1.
change (bv_unsigned (sv_denot _ (SLit 2)) mod 256) with 2 in SH5.
pose proof HC as (_ & _ & _ & _ & _ & R3g & R4t & _).
assert (Eg3 : ew E 3 = w64 (as_gp B))
  by (subst E; rewrite (am_ew_reg g pos c regs2 ys 3 3%bv eq_refl); exact R3g).
assert (Eg4 : ew E 4 = w64 (as_tp B))
  by (subst E; rewrite (am_ew_reg g pos c regs2 ys 4 4%bv eq_refl); exact R4t).
lazymatch goal with HSp : st_ok _ ?Ecur _ (restrict _ ?msv) |- _ =>
  assert (Ez2 : ew Ecur 2 = Z_to_bv 64 sp1) by (o9_unf; exact Eq2);
  assert (Ez33 : ew Ecur 33 = Z_to_bv 64 (FA g pos)) by (o9_unf; exact E33);
  assert (Ez3 : ew Ecur 3 = w64 (as_gp B)) by (o9_unf; exact Eg3);
  assert (Ez4 : ew Ecur 4 = w64 (as_tp B)) by (o9_unf; exact Eg4);
  assert (Hsp2 : spZ (ms_regs msv) = sp1) by
    (unfold spZ; rewrite (o9_getr_off0 _ _ _ _ 2%bv 2 _ HS ltac:(vm_compute; reflexivity) Ez2);
     apply unsigned_lit_small; lia);
  assert (Ha0 : getr (ms_regs msv) 10%bv = w64 (FA g pos + 34)) by
    (exact (o9_getr_off _ _ _ _ 10%bv 33 34 (FA g pos) HS ltac:(vm_compute; reflexivity) Ez33
              ltac:(lia) ltac:(lia)));
  assert (Ha1 : getr (ms_regs msv) 11%bv = w64 (FA g pos + 216)) by
    (exact (o9_getr_off _ _ _ _ 11%bv 33 216 (FA g pos) HS ltac:(vm_compute; reflexivity) Ez33
              ltac:(lia) ltac:(lia)));
  assert (Ha2 : getr (ms_regs msv) 12%bv = w64 4) by
    (exact (o9_getr_lit _ _ _ _ 12%bv 4 HS ltac:(vm_compute; reflexivity) ltac:(lia)));
  assert (Hgp : getr (ms_regs msv) 3%bv = w64 (as_gp B)) by
    (exact (o9_getr_off0 _ _ _ _ 3%bv 3 _ HS ltac:(vm_compute; reflexivity) Ez3));
  assert (Htp : getr (ms_regs msv) 4%bv = w64 (as_tp B)) by
    (exact (o9_getr_off0 _ _ _ _ 4%bv 4 _ HS ltac:(vm_compute; reflexivity) Ez4));
  assert (SHk : forall i, 0 <= i < 56 -> i <> 4 -> i <> 5 ->
    aview tfibsegs (w_H W2) (ms_mem msv) (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0))
  by (intros i Hi H4 H5; rewrite KE;
      [ exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia
      | revert Hfsh Hsh; unfold o9_zone, shadow_addr, SHADOW_OFF, SB; appn; lia ]) end.
lazymatch goal with HSp : st_ok _ _ _ (restrict _ ?msv) |- _ =>
  assert (BV : forall j, (j < 8)%nat ->
    aview tfibsegs (w_H W2) (ms_mem msv) (FA g pos + 216 + Z.of_nat j) = Some (nth j (kz_bytes k) 0)) by
  (intros j Hj; rewrite KE;
   [ apply (aview_of_val_mem1 tfibsegs (w_H W2) mem2);
     [ replace (FA g pos + 216 + Z.of_nat j) with (FA g pos + (216 + Z.of_nat j)) by lia;
       exact (proj1 (BY j Hj)) | exact (proj2 (BY j Hj)) ]
   | lia | unfold o9_zone; lia ]) end.
(* 0x82898 __asan_memcpy(pl + 2, k.bytes, chars) *)
lazymatch goal with
| HSp : st_ok _ ?Ecur ?ssp (restrict _ ?msv) |- SRr _ _ (mkCfg _ ?mdv) _ =>
  let rsv := eval vm_compute in
    (o9_closew (nth 0 (ss_mem ssp) (YP09.mkRegion None 0 0 0 0 []))
     :: o9_plo (nth 1 (ss_mem ssp) (YP09.mkRegion None 0 0 0 0 []))
     :: o9_fix_wins (skipn 2%nat (ss_mem ssp))) in
  apply (cw_intrin_call B LAWS OCpy 0x51998 AMEMCPY W2 Ecur ssp msv mdv LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 kj
    (FA g pos + 34) (FA g pos + 216) 4 0x8289c 64%nat rsv)
end.
{ exact HS. }
{ vm_compute; reflexivity. }
{ vm_compute; reflexivity. }
{ eassumption. }
{ exact Ha0. }
{ exact Ha1. }
{ exact Ha2. }
{ lia. }
{ lia. }
{ lia. }
{ rewrite Hsp2. unfold ESTACK. lia. }
{ rewrite Hsp2. lia. }
{ rewrite Hsp2, Hsp1e.
  replace (32 * ((e_sp0 g - 288) / 32)) with ((2 * ((e_sp0 g - 288) / 32)) * 16) by lia.
  apply Z.mod_mul. lia. }
{ exact Hsp016. }
{ exact Hgp. }
{ exact Htp. }
{ vm_compute; reflexivity. }
{ lia. }
{ unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. }
{ intros aa Haa. split.
  - right. right. right. exists 3, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
  - rewrite Hsp2. unfold ESTACK. lia. }
{ unfold amem_range in *. appn. lia. }
{ apply (range_addressable_sub _ _ (FA g pos + 32) 10); [|lia|lia].
  apply (o9_ra_pl W2 _ (FA g pos)); [exact Hf64 | lia | exact SH4 | exact SH5]. }
{ intros _. eapply (o9_hull B LAWS); [exact (proj1 HJ) | exact Hin | lia | lia | lia]. }
{ split; [lia|]. split; [lia|]. split.
  - intros aa Haa. split.
    + eapply (o9_frame_rd B LAWS ly2 S2 W2 _ _ pos (FA g pos + 216) 4);
      [exact (proj1 HJ) | exact Hin | rewrite EFA; lia | rewrite EFA; lia | exact Haa].
    + rewrite Hsp2. unfold ESTACK. lia.
  - split; [lia|]. split; [unfold amem_range in *; appn; lia|]. split.
    + replace 4 with (220 - 216) by lia.
      apply (o9_ra_zero W2 _ (FA g pos) 216 220); [exact Hf64 | lia | lia | lia |].
      intros j Hj. change (216 / 8) with 27 in Hj. change ((220 - 1) / 8) with 27 in Hj.
      assert (Ej : j = 27) by lia. subst j. rewrite (SHk 27 ltac:(lia) ltac:(lia) ltac:(lia)).
      vm_compute. reflexivity.
    + intros _. eapply (o9_hull B LAWS); [exact (proj1 HJ) | exact Hin | lia | lia | lia]. }
{ vm_compute; reflexivity. }
{ vm_compute; reflexivity. }
{ vm_compute; reflexivity. }
{ vm_compute; reflexivity. }
{ o9_submem. }
{ repeat apply Forall_cons; try apply Forall_nil;
  (split; [ intros aa Haa; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Haa; o9_unf_in Haa;
            rewrite ?U2, ?U33, ?U23, ?U34 in Haa; rewrite Hsp2;
            unfold A_GOT_shadow, A_shadow_glob, ESTACK, shadow_addr, SHADOW_OFF, SB in *; appn; split; lia
          | cbn; lia ]). }
intros regsA memA mdA HJA HPA Ha0A HeffA HfrA HpresA HSMA HSA.
clear HS. rename HSA into HS. clear HJ. rename HJA into HJ.
assert (KEA : forall a, 0 <= a < 2 ^ 64 -> ~ o9_zone g pos sp1 4 a ->
  aview tfibsegs (w_H W2) memA a = aview tfibsegs (w_H W2) mem2 a).
{ intros aq Hq Hz. rewrite (HfrA aq Hq ltac:(unfold o9_zone in Hz; lia)
    ltac:(rewrite Hsp2; unfold o9_zone, ESTACK in *; lia)).
  apply KE; [exact Hq | exact Hz]. }
clear KE. rename KEA into KE.
assert (SHkA : forall j, 22 <= j <= 44 ->
  aview tfibsegs (w_H W2) memA (shadow_addr (FA g pos) + j) = Some 0).
{ intros j Hj. rewrite KE; [| unfold shadow_addr, SHADOW_OFF; lia
  | revert Hfsh Hsh; unfold o9_zone, shadow_addr, SHADOW_OFF, SB; appn; lia ].
  rewrite (HSH j ltac:(lia)). f_equal.
  pose proof amain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _).
  apply (Hk23 0 (Z.to_nat j)). lia. }
lazymatch goal with HSp : st_ok _ ?Ecur _ (restrict _ ?msv) |- _ =>
  assert (Ew33 : ew Ecur 33 = Z_to_bv 64 (FA g pos)) by (o9_unf; exact E33);
  assert (Ew32 : ew Ecur 32 = Z_to_bv 64 SB) by (o9_unf; exact E32);
  assert (Ew23 : ew Ecur 23 = Z_to_bv 64 (kz_desk k)) by (o9_unf; exact E23);
  assert (Ew2 : ew Ecur 2 = Z_to_bv 64 sp1) by (o9_unf; exact Eq2);
  assert (Uw33 : bv_unsigned (ew Ecur 33) = FA g pos) by (rewrite Ew33; apply unsigned_lit_small; lia);
  assert (Uw2 : bv_unsigned (ew Ecur 2) = sp1) by (rewrite Ew2; apply unsigned_lit_small; lia);
  assert (Uw23 : bv_unsigned (ew Ecur 23) = kz_desk k) by (rewrite Ew23; apply unsigned_lit_small; lia)
end.
pose proof (o9_add_region _ _ _ o9_rw HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_mem restrict]; unfold o9_rw; eapply (o9_fwin_ok B LAWS);
        [ exact (proj1 HJ) | exact Hin | rewrite EFA; exact Uw33 | lia | lia | lia | lia | lia ])
  ltac:(o9_dis)) as HSn. clear HS. rename HSn into HS.
pose proof (o9_add_region _ _ _ (o9_rb 4) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_mem restrict]; unfold o9_rb; eapply (o9_fwin_ok B LAWS);
        [ exact (proj1 HJ) | exact Hin | rewrite EFA; exact Uw33 | lia | lia | lia | lia | lia ])
  ltac:(o9_dis)) as HSn. clear HS. rename HSn into HS.
clear SHOK.
lazymatch goal with HSp : st_ok _ ?Ecur _ _ |- _ =>
  assert (SHOK : sh_ok tfibsegs CW_Bx o9_SH Ecur (mrestrict (w_H W2) memA)) by
    (unfold o9_SH; apply Forall_cons;
     [ exact (owe_desk_shent B ly2 S2 W2 memA mdA Ecur (kz_p k) (kz_desk k) c24 GM IV (proj1 HJ) Hpd Ew23 Ew32)
     | apply Forall_cons;
       [ exact (o9_shk W2 memA Ecur (FA g pos) Hf64 ltac:(lia) ltac:(lia) Happ SHkA Ew33 Ew32)
       | apply Forall_nil ] ]) end.
(* 0x8289c-0x828d4: the desk's device byte, want[0 .. 4), then __asan_memcpy(want + 4, pl, chars + 2) *)
clear Uc33 Uc34 Uw2 Uw33 Uw23.
cw_run o9_awr.
(* the payload is not written after the first copy: its bytes are the copied ones at the second call *)
lazymatch goal with HFx : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
  pose proof (cw_kept_run (o9_zc g pos sp1) _ _ _ m1 m1 m2 (fun _ _ _ => eq_refl) HFx) as KPC;
  lazymatch type of KPC with ?P -> _ =>
    assert (KWc : P) by (o9_kwr o9_zc); specialize (KPC KWc); clear KWc end;
  assert (PLC : forall i, 0 <= i < 4 ->
    aview tfibsegs (w_H W2) m2 (FA g pos + 34 + i) = Some (nth (Z.to_nat i) (kz_bytes k) 0)) by
    (intros i Hi; rewrite (KPC (FA g pos + 34 + i) ltac:(lia) ltac:(unfold o9_zc; lia));
     rewrite (HeffA i ltac:(lia));
     replace (FA g pos + 216 + i) with (FA g pos + 216 + Z.of_nat (Z.to_nat i)) by lia;
     exact (BV (Z.to_nat i) ltac:(lia)));
  clear KPC end.
cw_keep ltac:(o9_kwr o9_zone).
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  repeat (rewrite wvb_collapse in HJx) end.
(* the state at the second call *)
clear Ew33 Ew32 Ew23 Ew2 Hsp2 Ha0 Ha1 Ha2 Hgp Htp.
lazymatch goal with HSp : st_ok _ ?Ecur _ (restrict _ ?msv) |- _ =>
  assert (Ex2 : ew Ecur 2 = Z_to_bv 64 sp1) by (o9_unf; exact Eq2);
  assert (Ex33 : ew Ecur 33 = Z_to_bv 64 (FA g pos)) by (o9_unf; exact E33);
  assert (Ex34 : ew Ecur 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (o9_unf; exact E34);
  assert (Ex32 : ew Ecur 32 = Z_to_bv 64 SB) by (o9_unf; exact E32);
  assert (Ex23 : ew Ecur 23 = Z_to_bv 64 (kz_desk k)) by (o9_unf; exact E23);
  assert (Ex37 : ew Ecur 37 = Z_to_bv 64 (kz_a k)) by (o9_unf; exact E37);
  assert (Ux34 : bv_unsigned (ew Ecur 34) = shadow_addr (FA g pos))
    by (rewrite Ex34; apply unsigned_lit_small; unfold SB in Hsh; lia);
  assert (Hsp2 : spZ (ms_regs msv) = sp1) by
    (unfold spZ; rewrite (o9_getr_off0 _ _ _ _ 2%bv 2 _ HS ltac:(vm_compute; reflexivity) Ex2);
     apply unsigned_lit_small; lia);
  assert (Ha0 : getr (ms_regs msv) 10%bv = w64 (FA g pos + 324)) by
    (exact (o9_getr_off _ _ _ _ 10%bv 33 324 (FA g pos) HS ltac:(vm_compute; reflexivity) Ex33
              ltac:(lia) ltac:(lia)));
  assert (Ha1 : getr (ms_regs msv) 11%bv = w64 (FA g pos + 32)) by
    (exact (o9_getr_off _ _ _ _ 11%bv 33 32 (FA g pos) HS ltac:(vm_compute; reflexivity) Ex33
              ltac:(lia) ltac:(lia)));
  assert (Ha2 : getr (ms_regs msv) 12%bv = w64 6) by
    (exact (o9_getr_lit _ _ _ _ 12%bv 6 HS ltac:(vm_compute; reflexivity) ltac:(lia)));
  assert (Hgp : getr (ms_regs msv) 3%bv = w64 (as_gp B)) by
    (exact (o9_getr_off0 _ _ _ _ 3%bv 3 _ HS ltac:(vm_compute; reflexivity) ltac:(o9_unf; exact Eg3)));
  assert (Htp : getr (ms_regs msv) 4%bv = w64 (as_tp B)) by
    (exact (o9_getr_off0 _ _ _ _ 4%bv 4 _ HS ltac:(vm_compute; reflexivity) ltac:(o9_unf; exact Eg4)));
  assert (SHkB : forall j, 22 <= j <= 44 ->
    aview tfibsegs (w_H W2) (ms_mem msv) (shadow_addr (FA g pos) + j) = Some 0) by
    (intros j Hj; rewrite KE;
     [ rewrite (HSH j ltac:(lia)); f_equal;
       pose proof amain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _);
       apply (Hk23 0 (Z.to_nat j)); lia
     | unfold shadow_addr, SHADOW_OFF; lia
     | revert Hfsh Hsh; unfold o9_zone, shadow_addr, SHADOW_OFF, SB; appn; lia ]) end.
owe_region HS 2%nat Hs0. owe_region HS 3%nat Hs1.
cbn [ms_mem restrict] in Hs0, Hs1.
lazymatch goal with HSp : st_ok _ ?Ecur _ _ |- _ =>
  assert (Ux33 : bv_unsigned (ew Ecur 33) = FA g pos) by (rewrite Ex33; apply unsigned_lit_small; lia) end.
pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 4 (SLit 0) Hs0
  ltac:(cbn [YP09.r_base base_val]; exact Ux34) ltac:(owe_in)) as SX4.
pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 5 (SLit 2) Hs0
  ltac:(cbn [YP09.r_base base_val]; exact Ux34) ltac:(owe_in)) as SX5.
pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 32 (SExt true 32 (SOff 37 0)) Hs1
  ltac:(cbn [YP09.r_base base_val]; exact Ux33) ltac:(owe_in)) as PX0.
pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 33 (SLit 0) Hs1
  ltac:(cbn [YP09.r_base base_val]; exact Ux33) ltac:(owe_in)) as PX1.
change (bv_unsigned (sv_denot _ (SLit 0)) mod 256) with 0 in SX4, PX1.
change (bv_unsigned (sv_denot _ (SLit 2)) mod 256) with 2 in SX5.
(* 0x828d4 __asan_memcpy(want + 4, pl, chars + 2) *)
lazymatch goal with
| HSp : st_ok _ ?Ecur ?ssp (restrict _ ?msv) |- SRr _ _ (mkCfg _ ?mdv) _ =>
  let rsv := eval vm_compute in (o9_fix_wins (ss_mem ssp)) in
  apply (cw_intrin_call B LAWS OCpy 0x51998 AMEMCPY W2 Ecur ssp msv mdv LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 kj
    (FA g pos + 324) (FA g pos + 32) 6 0x828d8 128%nat rsv)
end.
{ exact HS. }
{ vm_compute; reflexivity. }
{ vm_compute; reflexivity. }
{ eassumption. }
{ exact Ha0. }
{ exact Ha1. }
{ exact Ha2. }
{ lia. }
{ lia. }
{ lia. }
{ rewrite Hsp2. unfold ESTACK. lia. }
{ rewrite Hsp2. lia. }
{ rewrite Hsp2, Hsp1e.
  replace (32 * ((e_sp0 g - 288) / 32)) with ((2 * ((e_sp0 g - 288) / 32)) * 16) by lia.
  apply Z.mod_mul. lia. }
{ exact Hsp016. }
{ exact Hgp. }
{ exact Htp. }
{ vm_compute; reflexivity. }
{ lia. }
{ unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. }
{ intros aa Haa. split.
  - right. right. right. exists 3, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
  - rewrite Hsp2. unfold ESTACK. lia. }
{ unfold amem_range in *. appn. lia. }
{ replace 6 with (330 - 324) by lia.
  apply (o9_ra_zero W2 _ (FA g pos) 324 330); [exact Hf64 | lia | lia | lia |].
  intros j Hj. change (324 / 8) with 40 in Hj. change ((330 - 1) / 8) with 41 in Hj.
  apply SHkB. lia. }
{ intros _. eapply (o9_hull B LAWS); [exact (proj1 HJ) | exact Hin | lia | lia | lia]. }
{ split; [lia|]. split; [lia|]. split.
  - intros aa Haa. split.
    + eapply (o9_frame_rd B LAWS ly2 S2 W2 _ _ pos (FA g pos + 32) 6);
      [exact (proj1 HJ) | exact Hin | rewrite EFA; lia | rewrite EFA; lia | exact Haa].
    + rewrite Hsp2. unfold ESTACK. lia.
  - split; [lia|]. split; [unfold amem_range in *; appn; lia|]. split.
    + apply (range_addressable_sub _ _ (FA g pos + 32) 10); [|lia|lia].
      apply (o9_ra_pl W2 _ (FA g pos)); [exact Hf64 | lia | exact SX4 | exact SX5].
    + intros _. eapply (o9_hull B LAWS); [exact (proj1 HJ) | exact Hin | lia | lia | lia]. }
{ vm_compute; reflexivity. }
{ vm_compute; reflexivity. }
{ vm_compute; reflexivity. }
{ vm_compute; reflexivity. }
{ o9_submem. }
{ repeat apply Forall_cons; try apply Forall_nil;
  (split; [ intros aa Haa; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Haa; o9_unf_in Haa;
            rewrite ?U2, ?U33, ?U23, ?U34 in Haa; rewrite Hsp2;
            unfold A_GOT_shadow, A_shadow_glob, ESTACK, shadow_addr, SHADOW_OFF, SB in *; appn; split; lia
          | cbn; lia ]). }
intros regsB memB mdB HJB HPB Ha0B HeffB HfrB HpresB HSMB HSB.
clear HS. rename HSB into HS. clear HJ. rename HJB into HJ.
assert (KEB : forall a, 0 <= a < 2 ^ 64 -> ~ o9_zone g pos sp1 4 a ->
  aview tfibsegs (w_H W2) memB a = aview tfibsegs (w_H W2) mem2 a).
{ intros aq Hq Hz. rewrite (HfrB aq Hq ltac:(unfold o9_zone in Hz; lia)
    ltac:(rewrite Hsp2; unfold o9_zone, ESTACK in *; lia)).
  apply KE; [exact Hq | exact Hz]. }
clear KE. rename KEB into KE.
(* want[4 .. 10) now holds the payload *)
assert (WB : forall i, 0 <= i < 6 ->
  aview tfibsegs (w_H W2) memB (FA g pos + 324 + i) =
  Some (nth (Z.to_nat i) ([u8 (kz_a k); 0] ++ firstn 4 (kz_bytes k)) 0)).
{ intros i Hi. rewrite (HeffB i ltac:(lia)).
  assert (Ei : i = 0 \/ i = 1 \/ 2 <= i < 6) by lia.
  destruct Ei as [-> | [-> | Hi2]].
  - rewrite Z.add_0_r, PX0, (o9_sx_u8 _ 37 (kz_a k) Ex37 ltac:(lia)). reflexivity.
  - replace (FA g pos + 32 + 1) with (FA g pos + 33) by lia. rewrite PX1. reflexivity.
  - replace (FA g pos + 32 + i) with (FA g pos + 34 + (i - 2)) by lia.
    rewrite (PLC (i - 2) ltac:(lia)). f_equal.
    replace (Z.to_nat i) with (2 + Z.to_nat (i - 2))%nat by lia. cbn [nth app].
    symmetry. apply (o9_nth_firstn (kz_bytes k) 4 (Z.to_nat (i - 2))). lia. }
(* 0x828d8-0x82914: the last want byte, want_len, want_key, want_display *)
clear Ex2 Ex33 Ex34 Ex32 Ex23 Ux34 Ux33 Hsp2 Ha0 Ha1 Ha2 Hgp Htp.
clear SHOK.
lazymatch goal with HSp : st_ok _ ?Ecur _ (restrict _ ?msv) |- _ =>
  assert (Ey33 : ew Ecur 33 = Z_to_bv 64 (FA g pos)) by (o9_unf; exact E33);
  assert (Ey32 : ew Ecur 32 = Z_to_bv 64 SB) by (o9_unf; exact E32);
  assert (Ey23 : ew Ecur 23 = Z_to_bv 64 (kz_desk k)) by (o9_unf; exact E23);
  assert (Ey34 : ew Ecur 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (o9_unf; exact E34);
  assert (Uy33 : bv_unsigned (ew Ecur 33) = FA g pos) by (rewrite Ey33; apply unsigned_lit_small; lia);
  assert (Uy34 : bv_unsigned (ew Ecur 34) = shadow_addr (FA g pos))
    by (rewrite Ey34; apply unsigned_lit_small; unfold SB in Hsh; lia);
  assert (SHkC : forall j, 22 <= j <= 44 ->
    aview tfibsegs (w_H W2) (ms_mem msv) (shadow_addr (FA g pos) + j) = Some 0) by
    (intros j Hj; rewrite KE;
     [ rewrite (HSH j ltac:(lia)); f_equal;
       pose proof amain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _);
       apply (Hk23 0 (Z.to_nat j)); lia
     | unfold shadow_addr, SHADOW_OFF; lia
     | revert Hfsh Hsh; unfold o9_zone, shadow_addr, SHADOW_OFF, SB; appn; lia ]);
  assert (SHOK : sh_ok tfibsegs CW_Bx o9_SH Ecur (mrestrict (w_H W2) memB)) by
    (unfold o9_SH; apply Forall_cons;
     [ exact (owe_desk_shent B ly2 S2 W2 memB mdB Ecur (kz_p k) (kz_desk k) c24 GM IV (proj1 HJ) Hpd Ey23 Ey32)
     | apply Forall_cons;
       [ exact (o9_shk W2 memB Ecur (FA g pos) Hf64 ltac:(lia) ltac:(lia) Happ SHkC Ey33 Ey32)
       | apply Forall_nil ] ]) end.
cw_run_to o9_awr 0x82918.
lazymatch goal with HFx : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
  pose proof (cw_kept_run (o9_zd g pos sp1 4) _ _ _ m1 m1 m2 (fun _ _ _ => eq_refl) HFx) as KD;
  lazymatch type of KD with ?P -> _ =>
    assert (KWd : P) by (o9_kwr o9_zd); specialize (KD KWd); clear KWd end;
  assert (WD1 : forall i, 0 <= i < 6 ->
    aview tfibsegs (w_H W2) m2 (FA g pos + 324 + i) = aview tfibsegs (w_H W2) m1 (FA g pos + 324 + i)) by
    (intros i Hi; apply (KD (FA g pos + 324 + i)); [lia | unfold o9_zd; revert Hfsh Hsh;
     unfold shadow_addr, SHADOW_OFF, SB; appn; lia]);
  clear KD end.
cw_keep ltac:(o9_kwr o9_zone).
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  repeat (rewrite wvb_collapse in HJx) end.
(* 0x82918-0x82928: pl marked unusable again, s9 and s3 restored, to CHK *)
lazymatch goal with HSp : st_ok _ _ ?ssp _ |- _ =>
  let rsv := eval vm_compute in (firstn 2%nat (ss_mem ssp) ++ skipn 3%nat (ss_mem ssp)) in
  pose proof (o9_drop _ _ _ rsv HS ltac:(o9_submem) ltac:(vm_compute; reflexivity)) as HSn end.
clear HS. rename HSn into HS.
lazymatch goal with HSp : st_ok _ ?Ecur _ _ |- _ =>
  assert (Uz34 : bv_unsigned (ew Ecur 34) = shadow_addr (FA g pos)) by (o9_unf; exact U34) end.
pose proof (o9_add_region _ _ _ o9_rsh HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_mem restrict]; unfold o9_rsh; eapply (o9_shwin_ok B LAWS);
        [ exact (proj1 HJ) | exact Hin | rewrite EFA; exact Uz34 | lia | lia | lia ])
  ltac:(o9_dis)) as HSn. clear HS. rename HSn into HS.
clear Uz34 Uy33 Uy34.
aj_run_to_sh tfibtbl_lib_ok HS HJ 0x8273c.
{ o9_awr. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
  pose proof (cw_kept_run (o9_zd g pos sp1 4) _ _ _ m1 m1 m2 (fun _ _ _ => eq_refl) HFx) as KD;
  lazymatch type of KD with ?P -> _ =>
    assert (KWd : P) by (o9_kwr o9_zd); specialize (KD KWd); clear KWd end;
  assert (WD2 : forall i, 0 <= i < 6 ->
    aview tfibsegs (w_H W2) m2 (FA g pos + 324 + i) = aview tfibsegs (w_H W2) m1 (FA g pos + 324 + i)) by
    (intros i Hi; apply (KD (FA g pos + 324 + i)); [lia | unfold o9_zd; revert Hfsh Hsh;
     unfold shadow_addr, SHADOW_OFF, SB; appn; lia]);
  clear KD end.
cw_keep ltac:(o9_kwr o9_zone).
(* the end at CHK: the bytes and fields the regions hold *)
lazymatch goal with HSp : st_ok _ ?Ecur _ _ |- _ =>
  assert (Uf33 : bv_unsigned (ew Ecur 33) = FA g pos) by (o9_unf; exact U33);
  assert (Uf34 : bv_unsigned (ew Ecur 34) = shadow_addr (FA g pos)) by (o9_unf; exact U34);
  assert (Ef37 : ew Ecur 37 = Z_to_bv 64 (kz_a k)) by (o9_unf; exact E37) end.
owe_region HS 0%nat Hf0. owe_region HS 1%nat Hf1. owe_region HS 2%nat Hf2.
owe_region HS 11%nat Hf11. owe_region HS 12%nat Hf12.
cbn [ms_mem restrict] in Hf0, Hf1, Hf2, Hf11, Hf12.
pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 4 (SLit 18446744073709551608) Hf0
  ltac:(cbn [YP09.r_base base_val]; exact Uf34) ltac:(owe_in)) as F4.
pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 5 (SLit 18446744073709551608) Hf0
  ltac:(cbn [YP09.r_base base_val]; exact Uf34) ltac:(owe_in)) as F5.
pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 330 (SLit 18446744073709551607) Hf1
  ltac:(cbn [YP09.r_base base_val]; exact Uf33) ltac:(owe_in)) as F330.
pose proof (o9_chunk_aview2 _ W2 _ _ (FA g pos) 320 5104 Hf2
  ltac:(cbn [YP09.r_base base_val]; exact Uf33) ltac:(owe_in) ltac:(lia)) as (F320 & F321).
pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 322 (SLit 1) Hf2
  ltac:(cbn [YP09.r_base base_val]; exact Uf33) ltac:(owe_in)) as F322.
pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 323 (SLit 64) Hf2
  ltac:(cbn [YP09.r_base base_val]; exact Uf33) ltac:(owe_in)) as F323.
change (bv_unsigned (sv_denot _ (SLit 18446744073709551608)) mod 256) with 248 in F4, F5.
change (bv_unsigned (sv_denot _ (SLit 18446744073709551607)) mod 256) with 247 in F330.
change (bv_unsigned (sv_denot _ (SLit 1)) mod 256) with 1 in F322.
change (bv_unsigned (sv_denot _ (SLit 64)) mod 256) with 64 in F323.
change (5104 mod 256) with 240 in F320. change (5104 / 256) with 19 in F321.
try (unfold am_frame_region in Hf11, Hf12).
pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 316 4 _ Hf11 Uf33 ltac:(owe_in) ltac:(lia)) as Vr.
pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 344 8 _ Hf12 Uf33 ltac:(owe_in) ltac:(lia)) as Vl.
pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 352 4 _ Hf12 Uf33 ltac:(owe_in) ltac:(lia)) as Vk.
pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 356 4 _ Hf12 Uf33 ltac:(owe_in) ltac:(lia)) as Vd.
lazymatch goal with HSp : st_ok _ _ _ (restrict _ ?msv) |- _ =>
  assert (GB : garr8 tfibsegs (mrestrict (w_H W2) (ms_mem msv)) (FA g pos + 320) (o9_bs c24 k)) end.
{ apply o9_garr_of_aview; [|exact (o9_bs_rng c24 k Hrec)].
  intros j Hj. rewrite (o9_bs_lenN c24 k Rlen ltac:(cbn; lia)) in Hj.
  change (Z.to_nat (d_chars c24)) with 4%nat in Hj.
  assert (Ej : (j < 4)%nat \/ (4 <= j < 10)%nat \/ j = 10%nat) by lia.
  destruct Ej as [Hj4 | [Hj10 | ->]].
  - destruct j as [|[|[|[|j]]]]; [| | | | lia].
    + replace (FA g pos + 320 + Z.of_nat 0) with (FA g pos + 320) by lia. exact F320.
    + replace (FA g pos + 320 + Z.of_nat 1) with (FA g pos + 320 + 1) by lia. exact F321.
    + replace (FA g pos + 320 + Z.of_nat 2) with (FA g pos + 322) by lia. exact F322.
    + replace (FA g pos + 320 + Z.of_nat 3) with (FA g pos + 323) by lia. exact F323.
  - rewrite (o9_bs_nth_mid c24 k j ltac:(cbn; lia) Rlen ltac:(cbn; lia)).
    change (Z.to_nat (d_chars c24)) with 4%nat.
    replace (FA g pos + 320 + Z.of_nat j) with (FA g pos + 324 + Z.of_nat (j - 4)) by lia.
    rewrite (WD2 (Z.of_nat (j - 4)) ltac:(lia)), (WD1 (Z.of_nat (j - 4)) ltac:(lia)),
      (WB (Z.of_nat (j - 4)) ltac:(lia)).
    rewrite Nat2Z.id. reflexivity.
  - pose proof (o9_bs_nth_last c24 k Rlen ltac:(cbn; lia)) as HL.
    change (6 + Z.to_nat (d_chars c24))%nat with 10%nat in HL. rewrite HL.
    replace (FA g pos + 320 + Z.of_nat 10) with (FA g pos + 330) by lia. exact F330. }
eapply (o9_ok_fin B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k c24);
  [ exact HJ0 | exact Hfr | exact Hk | exact Hmo | exact HC | exact Hops | exact Hcur | exact Hkat
  | exact Hrec | exact Hrc | exact Hkind | cbn; lia | exact HJ | exact HS
  | vm_compute; reflexivity | vm_compute; reflexivity | env_agree_chain HAE
  | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; repeat (first [left; reflexivity | right])
  | exact KE | exact F4 | exact F5 | exact GB
  | apply (owe_vm _ _ 4 _ _ Vr); vm_compute; reflexivity
  | apply (owe_vm _ _ 8 _ _ Vl); vm_compute; reflexivity
  | apply (owe_vm _ _ 4 _ _ Vk); rewrite (o9_key_den _ 37 (kz_a k) Ef37 ltac:(lia));
    change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32);
    apply Z.mod_mod; lia
  | apply (owe_vm _ _ 4 _ _ Vd); vm_compute; reflexivity
  | exact Ha
  | intros j Hj; change (Z.to_nat (d_chars c24)) with 4%nat in Hj;
    destruct j as [|[|[|[|j]]]]; [exact Hby0 | exact Hby1 | exact Hby2 | exact Hby3 | lia] ].
Qed.
End b.
End a.
