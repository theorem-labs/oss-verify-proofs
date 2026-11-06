(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths and module names changed; 18 of its 49 lines of code are new or changed and 192 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe9.v, with its module paths and module names changed; 563 of its 597 lines of code are new or changed and 15 lines of the source are left out. *)
(* Segment OWE9 (SCRIBBLE) of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_owe 9),
   for the Control|24 desk (chars = 4): it is the image-A walk of lib/A/Prog/codec_amain_owe9a.v at image B.
     0x8293c a = k.a; a > 127 -> 0x82dc8 (want_rc = -11)
     0x82948 / 0x82950 the UBSan tests of the desk pointer (NULL, not 8-aligned; decided from its atom fact)
     0x82954 s8 = desk + 10, s9 its shadow byte's address, the check of desk + 10; a2 = chars (4)
     0x8297c the seven-bit test of k.bytes[0 .. 4) (the UBSan test of a0, the check of a0's byte, lb, bltz -> 0x82dc8)
     0x82ef0 pl marked usable (shadow bytes 6, 7 = 00 02), pl = [a, 0, ..., 0] at F + 48 (0x82f2c: the UBSan
             overflow test of pl, decided), the checked copy of k.bytes[0 .. 4) to pl + 2 (0x82f38)
     0x82f3c the checks of desk + 8 and desk + 10, owe_sysex(k, dev, 0x40, pl, chars + 2) (0x82f70,
             lib/AU/Prog/codec_bmain_owebl.v bm_owe_sysex_at, with the cut facts from codec_bmain_oweb_9l.v o9_callst)
     0x82f74 the end (codec_bmain_oweb_9z.v o9_after).
   The error paths end in lib/AU/Prog/codec_bmain_oweb_11.v o11_err_end. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgSatU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkKeptU CPgWalkCallU CPgWalkFrameU CPgWalkIntrU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_headl codec_bmain_encl codec_bmain_owel codec_bmain_owebl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_oweb_10l codec_bmain_oweb_11l codec_bmain_oweb_11.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_oweb_9l codec_bmain_oweb_9z.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy BM_asan_memcpy.
Hypothesis OSX : cdcU_owe_sysex_specX tfibsegs B MT BM_owe_sysex.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Local Notation rd W mem := (mrestrict (w_H W) mem).

Ltac o9_den En := rewrite (bm_den_off _ _ _ 0 En) by lia; rewrite Z.add_0_r; reflexivity.
Ltac o9_dis :=
  lazymatch goal with |- all_disjoint ?Ev ?r ?rs =>
    let r' := eval vm_compute in r in let rs' := eval vm_compute in rs in
    change (all_disjoint Ev r' rs') end;
  cbn [all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; o9_unf;
  repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- context [bv_unsigned (ew _ ?n)] => rewrite U end;
  try (unfold shadow_addr, SHADOW_OFF, SB in * ); try (unfold A_GOT_shadow, A_shadow_glob in * );
  repeat split; lia.
(* an error path at CHK: codec_bmain_oweb_11.v's o11_err_end with the code's literal v and the code's equation Hf *)
Ltac o9_close v Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE :=
  lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
    eapply (o11_err_end B MT K XM_LIB LAWS _ _ _ _ _ _ _ _ _ _ _ _ (o9_ys _) _ _ Ev ssv msv _ v) end;
    [exact HJ0 | exact Hfr | exact Hkj | exact Hmo | exact HC | exact Hops | exact Hcur | exact Hkat | exact Hrec
    | exact Hrc | exact Hwl | exact Hwk | exact Hwd | exact HJ | env_agree_chain HAE | exact HS | reflexivity
    | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | | | | | ];
    [ intros a Ha Hz; apply KE; [exact Ha | intros Hw; apply Hz; unfold o9_zone, o11_zerr in *; lia]
    | rewrite ?Hf; unfold E_RANGE; lia | rewrite ?Hf; unfold E_RANGE; lia | lia | rewrite ?Hf; reflexivity ].
Ltac o9_rreg HS r Q :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS) end.

Lemma o9_walk_c24 : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 ->
rec_okZ k (Some c24) -> kz_kind k = 9 -> kz_rc k = fst (enc_kZ k (Some c24)) ->
kz_want_rc k = 0 -> kz_want_len k = 0 -> kz_want_key k = 0 -> kz_want_display k = 0 ->
getr regs2 22 = w64 (kz_desk k) ->
SRr tfibsegs W2 (cfg_at tfibsegs (owe_pc 9) regs2 mem2 md2) (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hkind Hrc Hwrc Hwl Hwk Hwd R22.
assert (Hk0 : kj = 0) by (unfold EV_LIB in Hk; lia). subst kj.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof Hrec as (_ & Hpd & Hrdr & _).
destruct (pd_range_B _ _ _ Hpd) as (_ & Hdv & Rdev & Rstr & Rchr & Rctr).
pose proof (owe_desk_range _ _ _ Hpd) as Hdr.
pose proof Hrdr as (Ra & Rb & Rcc & Rdl & Rlen & Rby & Rn & _).
pose proof Hkat as ((Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gby & Vn & Vrc & Gbef & Gout & Vwrc & Gwant &
  Vwl & Vwk & Vwd) & Hwf).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
unfold BM_HI in Hchi. change (fs_frame_bytes 3) with 512 in Hfceil.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HC as (Hpre & _ & R2 & _).
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 0 Hpre HJ) as HRO.
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as Happ.
assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos) by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
assert (D44 : FA g pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (Hfsh : FA g pos + 512 <= shadow_addr (FA g pos) \/ shadow_addr (FA g pos) + 64 <= FA g pos).
{ pose proof Happ as Happ'. unfold in_app in Happ'.
  unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  destruct Happ' as (_ & [Hlow | (Hh1 & Hh2)]); [left; lia|].
  right. assert (D4 : 2199291686912 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (Hapd : FA g pos + 512 <= kz_desk k + 8 \/ kz_desk k + 8 + 4 <= FA g pos + 0).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos (kz_desk k + 8) 4 0 512 HAR Hin) as G.
  rewrite EFA in G. change (fs_frame_bytes 3) with 512 in G. apply G; lia. }
assert (Hgot : FA g pos + 512 <= A_GOT_shadow \/ A_GOT_shadow + 8 <= FA g pos + 0).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos A_GOT_shadow 8 0 512 HAR Hin) as G.
  rewrite EFA in G. change (fs_frame_bytes 3) with 512 in G. unfold A_GOT_shadow in *. apply G; lia. }
assert (Hbc : FA g pos + 512 <= A_shadow_glob \/ A_shadow_glob + 8 <= FA g pos + 0).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos A_shadow_glob 8 0 512 HAR Hin) as G.
  rewrite EFA in G. change (fs_frame_bytes 3) with 512 in G. unfold A_shadow_glob in *. apply G; lia. }
pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof bmain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _).
assert (BY : forall j, (j < 8)%nat ->
  val_mem tfibsegs (rd W2 mem2) (FA g pos + (232 + Z.of_nat j)) 1 (nth j (kz_bytes k) 0) /\
  0 <= nth j (kz_bytes k) 0 < 256).
{ intros j Hj. destruct (Gby j ltac:(rewrite Rlen; lia)) as [G1 G2]. split; [|exact G2].
  replace (FA g pos + (232 + Z.of_nat j)) with (FA g pos + 192 + 40 + Z.of_nat j) by lia. exact G1. }
pose proof (BY 0%nat ltac:(lia)) as (V232 & Q0).
pose proof (BY 1%nat ltac:(lia)) as (V233 & Q1).
pose proof (BY 2%nat ltac:(lia)) as (V234 & Q2).
pose proof (BY 3%nat ltac:(lia)) as (V235 & Q3).
pose proof (BY 4%nat ltac:(lia)) as (V236 & Q4).
pose proof (BY 5%nat ltac:(lia)) as (V237 & Q5).
pose proof (BY 6%nat ltac:(lia)) as (V238 & Q6).
pose proof (BY 7%nat ltac:(lia)) as (V239 & Q7).
set (ys := o9_ys k).
set (E := bm_env g pos c regs2 ys).
assert (E37 : ew E 37 = Z_to_bv 64 (kz_a k)) by exact (bm_ew_y g pos c regs2 ys 0).
assert (E38 : ew E 38 = Z_to_bv 64 (nth 0 (kz_bytes k) 0)) by exact (bm_ew_y g pos c regs2 ys 1).
assert (E39 : ew E 39 = Z_to_bv 64 (nth 1 (kz_bytes k) 0)) by exact (bm_ew_y g pos c regs2 ys 2).
assert (E40 : ew E 40 = Z_to_bv 64 (nth 2 (kz_bytes k) 0)) by exact (bm_ew_y g pos c regs2 ys 3).
assert (E41 : ew E 41 = Z_to_bv 64 (nth 3 (kz_bytes k) 0)) by exact (bm_ew_y g pos c regs2 ys 4).
assert (E42 : ew E 42 = Z_to_bv 64 (nth 4 (kz_bytes k) 0)) by exact (bm_ew_y g pos c regs2 ys 5).
assert (E43 : ew E 43 = Z_to_bv 64 (nth 5 (kz_bytes k) 0)) by exact (bm_ew_y g pos c regs2 ys 6).
assert (E44 : ew E 44 = Z_to_bv 64 (nth 6 (kz_bytes k) 0)) by exact (bm_ew_y g pos c regs2 ys 7).
assert (E45 : ew E 45 = Z_to_bv 64 (nth 7 (kz_bytes k) 0)) by exact (bm_ew_y g pos c regs2 ys 8).
assert (E22 : ew E 22 = Z_to_bv 64 (kz_desk k)) by (unfold E; rewrite (bm_ew_reg g pos c regs2 ys 22 22%bv eq_refl), R22; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by exact (bm_ew_F g pos c regs2 ys).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by exact (bm_ew_SH g pos c regs2 ys).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (bm_ew_SB g pos c regs2 ys).
assert (Eq2 : ew E 2 = Z_to_bv 64 sp1) by (unfold E; rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite Eq2; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = FA g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (FA g pos))
  by (rewrite E34; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (U22 : bv_unsigned (ew E 22) = kz_desk k) by (rewrite E22; apply unsigned_lit_small; lia).
(* the start state *)
assert (HRS : Forall (region_ok tfibsegs E (rd W2 mem2)) (o9_rs c24)).
{ unfold o9_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - unfold o9_rr.
    apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 c ys);
      [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ (FA g pos) 332 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. rewrite Hwrc in Vwrc. replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia.
    exact Vwrc.
  - unfold o9_rk.
    apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 c ys);
      [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ].
    apply Forall_cons; [|].
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 216 4 (SOff 37 0) (kz_a k)); [o9_den E37 | cbn; lia | cbn; lia |].
      change (N.to_nat 4) with 4%nat. replace (FA g pos + 216) with (FA g pos + 192 + 24) by lia. exact Va. }
    apply Forall_cons; [|].
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 232 1 (SOff 38 0) (nth 0 (kz_bytes k) 0)); [o9_den E38 | cbn; lia | cbn; lia |].
      change (N.to_nat 1) with 1%nat. replace (FA g pos + 232) with (FA g pos + (232 + Z.of_nat 0)) by lia. exact V232. }
    apply Forall_cons; [|].
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 233 1 (SOff 39 0) (nth 1 (kz_bytes k) 0)); [o9_den E39 | cbn; lia | cbn; lia |].
      change (N.to_nat 1) with 1%nat. replace (FA g pos + 233) with (FA g pos + (232 + Z.of_nat 1)) by lia. exact V233. }
    apply Forall_cons; [|].
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 234 1 (SOff 40 0) (nth 2 (kz_bytes k) 0)); [o9_den E40 | cbn; lia | cbn; lia |].
      change (N.to_nat 1) with 1%nat. replace (FA g pos + 234) with (FA g pos + (232 + Z.of_nat 2)) by lia. exact V234. }
    apply Forall_cons; [|].
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 235 1 (SOff 41 0) (nth 3 (kz_bytes k) 0)); [o9_den E41 | cbn; lia | cbn; lia |].
      change (N.to_nat 1) with 1%nat. replace (FA g pos + 235) with (FA g pos + (232 + Z.of_nat 3)) by lia. exact V235. }
    apply Forall_cons; [|].
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 236 1 (SOff 42 0) (nth 4 (kz_bytes k) 0)); [o9_den E42 | cbn; lia | cbn; lia |].
      change (N.to_nat 1) with 1%nat. replace (FA g pos + 236) with (FA g pos + (232 + Z.of_nat 4)) by lia. exact V236. }
    apply Forall_cons; [|].
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 237 1 (SOff 43 0) (nth 5 (kz_bytes k) 0)); [o9_den E43 | cbn; lia | cbn; lia |].
      change (N.to_nat 1) with 1%nat. replace (FA g pos + 237) with (FA g pos + (232 + Z.of_nat 5)) by lia. exact V237. }
    apply Forall_cons; [|].
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 238 1 (SOff 44 0) (nth 6 (kz_bytes k) 0)); [o9_den E44 | cbn; lia | cbn; lia |].
      change (N.to_nat 1) with 1%nat. replace (FA g pos + 238) with (FA g pos + (232 + Z.of_nat 6)) by lia. exact V238. }
    apply Forall_cons; [|].
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 239 1 (SOff 45 0) (nth 7 (kz_bytes k) 0)); [o9_den E45 | cbn; lia | cbn; lia |].
      change (N.to_nat 1) with 1%nat. replace (FA g pos + 239) with (FA g pos + (232 + Z.of_nat 7)) by lia. exact V239. }
    apply Forall_nil.
  - unfold o9_rg.
    apply (owe_desk_region_ok B TL E W2 mem2 (kz_p k) (kz_desk k) c24 _ HRO Hpd U22).
    intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth desk_bytesZ sv_denot]; try reflexivity. lia. }
assert (HPD : pairwise_disjoint E (o9_rs c24)).
{ unfold o9_rs, o9_rr, o9_rk, o9_rg, owe_desk_region, bm_frame_region.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33, U22.
  pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos (kz_desk k + 8) 4 216 376 HAR Hin) as AP.
  rewrite EFA in AP. change (fs_frame_bytes 3) with 512 in AP. specialize (AP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  repeat split; lia. }
assert (HAP : Forall (fun r => all_disjoint E r bm_regs) (o9_rs c24)).
{ unfold o9_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  3: { unfold o9_rg. apply (owe_desk_apart_base E _ (kz_desk k) sp1 U22 Hdr U2 ltac:(lia)). }
  all: unfold o9_rr, o9_rk;
  apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 c ys);
  [exact HJ | exact Hfr | exact HC | lia | lia]. }
assert (HAF : atoms_ok E o9_AF).
{ unfold o9_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U22, E37, E38, E39, E40, E41, E42, E43, E44, E45.
  rewrite !unsigned_lit_small by lia.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  destruct Hdv as [Hd1 | Hd1]; rewrite Hd1; repeat split; first [reflexivity | lia]. }
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 0 c (owe_pc 9) ys (o9_rs c24) o9_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) HRS HPD HAP HAF) as HS.
fold E in HS.
assert (HAE : env_agree 37 (bm_env g pos c regs2 ys) E) by apply env_agree_refl.
assert (SHOK : sh_ok tfibsegs CW_Bx o9_SH E (rd W2 mem2)).
{ unfold o9_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p k) (kz_desk k) c24 GM IV HAR Hpd E22 E32).
  - exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 0 c ys HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o11_zerr (FA g pos) sp1 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof (owe_U_sx32 E 37 (kz_a k) E37 ltac:(lia)) as Ua.
assert (Hkj : 0 <= 0 <= EV_LIB) by (unfold EV_LIB; lia).
unfold cfg_at. change (w64 (owe_pc 9)) with (Z_to_bv 64 0x8293c).
cw_keep_j0 HJ HJ0.
(* 0x8293c-0x82944: lw a1,24(s7); li a0,127; bltu a0,a1 *)
cw_run o9_awr. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
cw_branch Hb1.
all: rewrite branch_ltu_U, U_lit, Ua in Hb1 by lia.
{ (* 127 < a: the E_RANGE tail *)
  apply Z.ltb_lt in Hb1.
  assert (Ha7 : 127 < kz_a k) by (destruct (Z.ltb_spec (kz_a k) (2 ^ 31)); lia).
  cw_run_to o9_awr PC_CHK. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
  assert (Hf : fst (owe_kZ k (Some c24)) = E_RANGE) by (unfold owe_kZ; rewrite Hkind; apply owe9_rng_a; lia).
  o9_close 18446744073709551605 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE. }
apply Z.ltb_ge in Hb1.
assert (Ha7 : kz_a k <= 127) by (destruct (Z.ltb_spec (kz_a k) (2 ^ 31)); lia).
(* 0x82948-0x82994: the desk's tests, chars, and the seven-bit test of each byte *)
cw_run o9_awr. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (F0 : ew Ec 38 = Z_to_bv 64 (nth 0 (kz_bytes k) 0)) by (o9_unf; exact E38) end.
cw_branch Hb. all: rewrite (o11_lt_byte _ _ _ F0 ltac:(lia)) in Hb. clear F0.
{ apply Z.leb_le in Hb.
  cw_run_to o9_awr PC_CHK. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
  assert (Hf : fst (owe_kZ k (Some c24)) = E_RANGE).
  { unfold owe_kZ. rewrite Hkind. apply owe9_rng_s.
    apply (o11_sb_false (kz_bytes k) (d_chars c24) 0); [cbn; lia | rewrite Rlen; cbn; lia | exact Hb | exact (proj2 Q0)]. }
  o9_close 18446744073709551605 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE. }
apply Z.leb_gt in Hb. rename Hb into Hby0.
cw_run o9_awr. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (F1 : ew Ec 39 = Z_to_bv 64 (nth 1 (kz_bytes k) 0)) by (o9_unf; exact E39) end.
cw_branch Hb. all: rewrite (o11_lt_byte _ _ _ F1 ltac:(lia)) in Hb. clear F1.
{ apply Z.leb_le in Hb.
  cw_run_to o9_awr PC_CHK. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
  assert (Hf : fst (owe_kZ k (Some c24)) = E_RANGE).
  { unfold owe_kZ. rewrite Hkind. apply owe9_rng_s.
    apply (o11_sb_false (kz_bytes k) (d_chars c24) 1); [cbn; lia | rewrite Rlen; cbn; lia | exact Hb | exact (proj2 Q1)]. }
  o9_close 18446744073709551605 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE. }
apply Z.leb_gt in Hb. rename Hb into Hby1.
cw_run o9_awr. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (F2 : ew Ec 40 = Z_to_bv 64 (nth 2 (kz_bytes k) 0)) by (o9_unf; exact E40) end.
cw_branch Hb. all: rewrite (o11_lt_byte _ _ _ F2 ltac:(lia)) in Hb. clear F2.
{ apply Z.leb_le in Hb.
  cw_run_to o9_awr PC_CHK. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
  assert (Hf : fst (owe_kZ k (Some c24)) = E_RANGE).
  { unfold owe_kZ. rewrite Hkind. apply owe9_rng_s.
    apply (o11_sb_false (kz_bytes k) (d_chars c24) 2); [cbn; lia | rewrite Rlen; cbn; lia | exact Hb | exact (proj2 Q2)]. }
  o9_close 18446744073709551605 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE. }
apply Z.leb_gt in Hb. rename Hb into Hby2.
cw_run o9_awr. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (F3 : ew Ec 41 = Z_to_bv 64 (nth 3 (kz_bytes k) 0)) by (o9_unf; exact E41) end.
cw_branch Hb. all: rewrite (o11_lt_byte _ _ _ F3 ltac:(lia)) in Hb. clear F3.
{ apply Z.leb_le in Hb.
  cw_run_to o9_awr PC_CHK. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
  assert (Hf : fst (owe_kZ k (Some c24)) = E_RANGE).
  { unfold owe_kZ. rewrite Hkind. apply owe9_rng_s.
    apply (o11_sb_false (kz_bytes k) (d_chars c24) 3); [cbn; lia | rewrite Rlen; cbn; lia | exact Hb | exact (proj2 Q3)]. }
  o9_close 18446744073709551605 Hf HJ0 Hfr Hkj Hmo HC Hops Hcur Hkat Hrec Hrc Hwl Hwk Hwd HJ HAE HS KE. }
apply Z.leb_gt in Hb. rename Hb into Hby3.
(* 0x82998-0x829a8: the loop is done, to 0x82ef0 *)
cw_run_to o9_awr 0x82ef0. cw_keep ltac:(o9_kwr o11_zerr). repeat (rewrite wvb_collapse in * ).
assert (Hall : forall l, 0 <= l < d_chars c24 -> nth (Z.to_nat l) (kz_bytes k) 0 < 128).
{ intros l Hl. cbn in Hl.
  assert (El : l = 0 \/ l = 1 \/ l = 2 \/ l = 3) by lia.
  destruct El as [-> | [-> | [-> | ->]]].
  - exact Hby0. 
  - exact Hby1. 
  - exact Hby2. 
  - exact Hby3. }
(* ---- 0x82ef0-0x82f38: pl marked usable and filled, the checked copy of k.bytes[0 .. chars) to pl + 2 ---- *)
lazymatch goal with KE : forall a, _ -> ~ o11_zerr _ _ a -> aview _ ?Hh ?m a = _ |- _ =>
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ o9_zone g pos sp1 a -> aview tfibsegs Hh m a = aview tfibsegs (w_H W2) mem2 a)
  by (intros a' Ha' Hz; apply KE; [exact Ha' | intros Hw; apply Hz; unfold o9_zone, o11_zerr in *; lia]) end.
clear KE. rename KE2 into KE.
lazymatch goal with HSp : st_ok _ ?Ec _ _ |- _ =>
  assert (Uc2 : bv_unsigned (ew Ec 2) = sp1) by (o9_unf; exact U2);
  assert (Uc33 : bv_unsigned (ew Ec 33) = FA g pos) by (o9_unf; exact U33);
  assert (Uc34 : bv_unsigned (ew Ec 34) = shadow_addr (FA g pos)) by (o9_unf; exact U34);
  assert (Uc22 : bv_unsigned (ew Ec 22) = kz_desk k) by (o9_unf; exact U22) end.
pose proof (o9_add_region _ _ _ o9_rpl HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_mem restrict]; unfold o9_rpl; eapply (o10_fwin_ok B LAWS);
        [ lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (proj1 HJx) end
        | exact Hin | rewrite EFA; exact Uc33 | lia | lia | lia | lia ])
  ltac:(o9_dis)) as HSn. clear HS. rename HSn into HS.
pose proof (o9_add_region _ _ _ o9_rsh HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_mem restrict]; unfold o9_rsh; eapply (o9_shwin_ok B LAWS);
        [ lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (proj1 HJx) end
        | exact Hin | rewrite EFA; exact Uc34 | lia | lia | lia ])
  ltac:(o9_dis)) as HSn. clear HS. rename HSn into HS.
clear Uc2 Uc33 Uc34 Uc22.
aj_run_to_sh tfibtbl_lib_ok HS HJ 0x51ae8.
{ o9_awr. }
cw_keep ltac:(o9_kwr o9_zone). repeat (rewrite wvb_collapse in * ).
(* the state at the checked copy (0x51ae8): a0 = pl + 2, a1 = k.bytes, a2 = chars, ra = 0x82f3c *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- _ => rename msv into msC end.
lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
  assert (Ec2 : ew Ec 2 = Z_to_bv 64 sp1) by (o9_unf; exact Eq2);
  assert (Ec33 : ew Ec 33 = Z_to_bv 64 (FA g pos)) by (o9_unf; exact E33);
  assert (Ec34 : ew Ec 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (o9_unf; exact E34);
  assert (Ec37 : ew Ec 37 = Z_to_bv 64 (kz_a k)) by (o9_unf; exact E37) end.
assert (Uc33 : bv_unsigned (ew _ 33) = FA g pos) by (rewrite Ec33; apply unsigned_lit_small; lia).
assert (Uc34 : bv_unsigned (ew _ 34) = shadow_addr (FA g pos))
  by (rewrite Ec34; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
o9_region HS 0%nat Hr0. o9_region HS 1%nat Hr1.
change (ms_mem (restrict (w_H W2) msC)) with (mrestrict (w_H W2) (ms_mem msC)) in Hr0, Hr1.
pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 6 (SLit 0) Hr0
  ltac:(cbn [YP09.r_base base_val]; exact Uc34) ltac:(o9_in)) as SH6.
pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 7 (SLit 2) Hr0
  ltac:(cbn [YP09.r_base base_val]; exact Uc34) ltac:(o9_in)) as SH7.
change (bv_unsigned (sv_denot _ (SLit 0)) mod 256) with 0 in SH6.
change (bv_unsigned (sv_denot _ (SLit 2)) mod 256) with 2 in SH7.
pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 48 (SExt true 32 (SOff 37 0)) Hr1
  ltac:(cbn [YP09.r_base base_val]; exact Uc33) ltac:(o9_in)) as PL0.
pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 49 (SLit 0) Hr1
  ltac:(cbn [YP09.r_base base_val]; exact Uc33) ltac:(o9_in)) as PL1.
change (bv_unsigned (sv_denot _ (SLit 0)) mod 256) with 0 in PL1.
rewrite (o9_sx_u8 _ 37 (kz_a k) Ec37 ltac:(lia)) in PL0.
pose proof HC as (_ & _ & _ & _ & _ & R3g & R4t & _).
o9_rreg HS (10%bv : bv 5) Ga0. o9_rreg HS (11%bv : bv 5) Ga1. o9_rreg HS (12%bv : bv 5) Ga2.
o9_rreg HS (2%bv : bv 5) Gsp. o9_rreg HS (3%bv : bv 5) Ggp. o9_rreg HS (4%bv : bv 5) Gtp.
rewrite (bm_den_off _ 33 (FA g pos) 50 Ec33) in Ga0 by lia.
rewrite (bm_den_off _ 33 (FA g pos) 232 Ec33) in Ga1 by lia.
cbn [sv_denot] in Ga2.
rewrite (bm_den_off _ 2 sp1 0 Ec2), Z.add_0_r in Gsp by lia.
assert (Hspc : spZ (ms_regs msC) = sp1) by (unfold spZ; rewrite Gsp; apply unsigned_lit_small; lia).
assert (G3 : getr (ms_regs msC) 3 = w64 (as_gp B)).
{ rewrite Ggp. cbn [sv_denot]. o9_unf. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold E. rewrite (bm_ew_reg g pos c regs2 ys 3 3%bv eq_refl). exact R3g. }
assert (G4 : getr (ms_regs msC) 4 = w64 (as_tp B)).
{ rewrite Gtp. cbn [sv_denot]. o9_unf. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold E. rewrite (bm_ew_reg g pos c regs2 ys 4 4%bv eq_refl). exact R4t. }
assert (Hes : ESTACK = 4096) by reflexivity.
assert (SHk : forall j, 24 <= j <= 46 ->
  aview tfibsegs (w_H W2) (ms_mem msC) (shadow_addr (FA g pos) + j) = Some 0).
{ intros j Hj. rewrite KE; [| unfold shadow_addr, SHADOW_OFF; lia | unfold o9_zone, shadow_addr, SHADOW_OFF in *; lia].
  rewrite (HSH j ltac:(lia)). f_equal. apply (Hk23 0 (Z.to_nat j)). lia. }
assert (BV : forall j, (j < 8)%nat ->
  aview tfibsegs (w_H W2) (ms_mem msC) (FA g pos + 232 + Z.of_nat j) = Some (nth j (kz_bytes k) 0)).
{ intros j Hj. rewrite KE; [| lia | unfold o9_zone, shadow_addr, SHADOW_OFF in *; lia].
  apply (aview_of_val_mem1 tfibsegs (w_H W2) mem2); [|exact (proj2 (BY j Hj))].
  replace (FA g pos + 232 + Z.of_nat j) with (FA g pos + (232 + Z.of_nat j)) by lia. exact (proj1 (BY j Hj)). }
(* 0x82f38 the checked copy (pl + 2, k.bytes, chars) *)
lazymatch goal with
| HSp : st_ok _ ?Ecur ?ssp (restrict _ msC) |- SRr _ _ (mkCfg _ ?mdv) _ =>
  let rsv := eval vm_compute in
    (o9_closew (nth 0 (ss_mem ssp) (YP09.mkRegion None 0 0 0 0 []))
     :: o9_plo (nth 1 (ss_mem ssp) (YP09.mkRegion None 0 0 0 0 []))
     :: o9_fix_wins (skipn 2%nat (ss_mem ssp))) in
  let kk := eval vm_compute in (run_K 50 (SOff 32 0) o9_SH ssp) in
  eapply (cw_intrin_call B LAWS OCpy BM_asan_memcpy AMEMCPY W2 Ecur ssp msC mdv LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
    (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 0 (FA g pos + 50) (FA g pos + 232) 4 0x82f3c kk rsv _ HSp)
end.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact HJ.
- exact Ga0.
- exact Ga1.
- exact Ga2.
- lia.
- lia.
- lia.
- rewrite Hspc, Hes. lia.
- rewrite Hspc. lia.
- rewrite Hspc. pose proof (Z.div_mod sp1 32 ltac:(lia)) as DM. rewrite Hsp32, Z.add_0_r in DM.
  rewrite DM. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult.
- exact Hsp016.
- exact G3.
- exact G4.
- vm_compute. reflexivity.
- lia.
- apply ret_ok_even. vm_compute. reflexivity.
- intros a Ha'. split.
  + right; right; right. exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
  + rewrite Hspc, Hes. lia.
- unfold amem_range in *. appn. lia.
- apply (range_addressable_sub _ _ (FA g pos + 48) 10); [|lia|lia].
  apply (o9_ra_pl W2 _ (FA g pos)); [exact Hf64 | lia | exact SH6 | exact SH7].
- intros _. eapply (o9_hull B LAWS); [exact (proj1 HJ) | exact Hin | lia | lia | lia].
- cbv beta iota. split; [lia|]. split; [lia|]. split.
  { intros a Ha'. split.
    - eapply (o9_frame_rd B LAWS ly2 S2 W2 _ _ pos (FA g pos + 232) 4);
      [exact (proj1 HJ) | exact Hin | rewrite EFA; lia | rewrite EFA; lia | exact Ha'].
    - rewrite Hspc, Hes. lia. }
  split; [lia|]. split; [unfold amem_range in *; appn; lia|]. split.
  + replace 4 with ((232 + 4) - 232) by lia.
    apply (o9_ra_zero W2 _ (FA g pos) 232 (232 + 4)); [exact Hf64 | lia | lia | lia |].
    intros j Hj. apply SHk. change (232 / 8) with 29 in Hj. change ((232 + 4 - 1) / 8) with 29 in Hj. lia.
  + intros _. eapply (o9_hull B LAWS); [exact (proj1 HJ) | exact Hin | lia | lia | lia].
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- lazymatch goal with |- submem ?a ?b =>
    let a' := eval vm_compute in a in let b' := eval vm_compute in b in change (submem a' b') end.
  submem_to.
- repeat apply Forall_cons; try apply Forall_nil;
  (split; [ intros a Ha'; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha'; o9_unf_in Ha';
            repeat match goal with U : bv_unsigned (ew _ ?n) = _, H' : context [bv_unsigned (ew _ ?n)] |- _ =>
              rewrite U in H' end;
            rewrite Hspc, Hes; unfold A_GOT_shadow, A_shadow_glob, shadow_addr, SHADOW_OFF in *; split; lia
          | cbn; lia ]).
- (* 0x82f3c: the state after the copy *)
  intros regsA memA mdA HJA HPA HdA HcpA HkpA HprA HsmA HSA.
  cbv beta iota in HcpA. rewrite Hspc, Hes in HkpA.
  clear HS SHOK HJ. rename HSA into HS. rename HJA into HJ.
  assert (KEA : forall a, 0 <= a < 2 ^ 64 -> ~ o9_zone g pos sp1 a ->
    aview tfibsegs (w_H W2) memA a = aview tfibsegs (w_H W2) mem2 a).
  { intros aq Hq Hz. rewrite (HkpA aq Hq ltac:(unfold o9_zone in Hz; lia) ltac:(unfold o9_zone in Hz; lia)).
    apply KE; [exact Hq | exact Hz]. }
  clear KE. rename KEA into KE.
  assert (PLC : forall i, 0 <= i < 4 ->
    aview tfibsegs (w_H W2) memA (FA g pos + 50 + i) = Some (nth (Z.to_nat i) (kz_bytes k) 0)).
  { intros i Hi. rewrite (HcpA i Hi).
    replace (FA g pos + 232 + i) with (FA g pos + 232 + Z.of_nat (Z.to_nat i)) by lia. exact (BV (Z.to_nat i) ltac:(lia)). }
  lazymatch goal with HSp : st_ok _ ?Ecur _ _ |- _ =>
    assert (Ew33 : ew Ecur 33 = Z_to_bv 64 (FA g pos)) by (o9_unf; exact E33);
    assert (Ew34 : ew Ecur 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (o9_unf; exact E34);
    assert (Ew32 : ew Ecur 32 = Z_to_bv 64 SB) by (o9_unf; exact E32);
    assert (Ew22 : ew Ecur 22 = Z_to_bv 64 (kz_desk k)) by (o9_unf; exact E22);
    assert (Ew2 : ew Ecur 2 = Z_to_bv 64 sp1) by (o9_unf; exact Eq2) end.
  assert (Uw2 : bv_unsigned (ew _ 2) = sp1) by (rewrite Ew2; apply unsigned_lit_small; lia).
  assert (Uw33 : bv_unsigned (ew _ 33) = FA g pos) by (rewrite Ew33; apply unsigned_lit_small; lia).
  assert (Uw34 : bv_unsigned (ew _ 34) = shadow_addr (FA g pos))
    by (rewrite Ew34; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
  assert (Uw22 : bv_unsigned (ew _ 22) = kz_desk k) by (rewrite Ew22; apply unsigned_lit_small; lia).
  (* pl's first two bytes and its two shadow bytes, from the regions the copy kept *)
  o9_region HS 0%nat Hq0. o9_region HS 1%nat Hq1.
  change (ms_mem (restrict (w_H W2) _)) with (mrestrict (w_H W2) memA) in Hq0, Hq1.
  pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 6 (SLit 0) Hq0
    ltac:(cbn [YP09.r_base base_val]; exact Uw34) ltac:(o9_in)) as SA6.
  pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 7 (SLit 2) Hq0
    ltac:(cbn [YP09.r_base base_val]; exact Uw34) ltac:(o9_in)) as SA7.
  change (bv_unsigned (sv_denot _ (SLit 0)) mod 256) with 0 in SA6.
  change (bv_unsigned (sv_denot _ (SLit 2)) mod 256) with 2 in SA7.
  pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 48 (SExt true 32 (SOff 37 0)) Hq1
    ltac:(cbn [YP09.r_base base_val]; exact Uw33) ltac:(o9_in)) as PA0.
  pose proof (o9_chunk_aview _ W2 _ _ (FA g pos) 49 (SLit 0) Hq1
    ltac:(cbn [YP09.r_base base_val]; exact Uw33) ltac:(o9_in)) as PA1.
  change (bv_unsigned (sv_denot _ (SLit 0)) mod 256) with 0 in PA1.
  lazymatch goal with HSp : st_ok _ ?Ecur _ _ |- _ =>
    assert (Ew37 : ew Ecur 37 = Z_to_bv 64 (kz_a k)) by (o9_unf; exact E37) end.
  rewrite (o9_sx_u8 _ 37 (kz_a k) Ew37 ltac:(lia)) in PA0.
  clear Hq0 Hq1.
  assert (SHkA : forall j, 24 <= j <= 46 ->
    aview tfibsegs (w_H W2) memA (shadow_addr (FA g pos) + j) = Some 0).
  { intros j Hj. rewrite KE; [| unfold shadow_addr, SHADOW_OFF; lia | unfold o9_zone, shadow_addr, SHADOW_OFF in *; lia].
    rewrite (HSH j ltac:(lia)). f_equal. apply (Hk23 0 (Z.to_nat j)). lia. }
  lazymatch goal with HSp : st_ok _ ?Ecur _ _ |- _ =>
    assert (SHOK : sh_ok tfibsegs CW_Bx o9_SH Ecur (rd W2 memA)) by
      (unfold o9_SH; apply Forall_cons;
       [ exact (owe_desk_shent B ly2 S2 W2 memA mdA Ecur (kz_p k) (kz_desk k) c24 GM IV (proj1 HJ) Hpd Ew22 Ew32)
       | apply Forall_cons;
         [ exact (o9_shk W2 memA Ecur (FA g pos) Hf64 ltac:(lia) Happ SHkA Ew33 Ew32)
         | apply Forall_nil ] ]) end.
  (* 0x82f3c-0x82f70: the checks of desk + 8 and desk + 10, owe_sysex's arguments, jal *)
  clear Uw2 Uw33 Uw34 Uw22.
  cw_run_to o9_awr 0x84e8c.
  lazymatch goal with HFx : _ _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (cw_kept_run (o9_zc g pos sp1) _ _ _ m1 m1 m2 (fun _ _ _ => eq_refl) HFx) as KPC;
    lazymatch type of KPC with ?P -> _ =>
      assert (KWc : P) by (o9_kwr o9_zc); specialize (KPC KWc); clear KWc end;
    assert (PLK : forall i, 0 <= i < 10 ->
      aview tfibsegs (w_H W2) m2 (FA g pos + 48 + i) = aview tfibsegs (w_H W2) m1 (FA g pos + 48 + i))
      by (intros i Hi; apply KPC; [lia | unfold o9_zc, shadow_addr, SHADOW_OFF in *; lia]);
    clear KPC end.
  cw_keep ltac:(o9_kwr o9_zone). repeat (rewrite wvb_collapse in * ).
  (* the state at owe_sysex's entry 0x84e8c *)
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- _ => rename msv into msc end.
  lazymatch goal with HSp : st_ok _ ?Ecur _ _ |- _ =>
    assert (Ex33 : ew Ecur 33 = Z_to_bv 64 (FA g pos)) by (o9_unf; exact E33);
    assert (Ex34 : ew Ecur 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (o9_unf; exact E34) end.
  assert (Ux33 : bv_unsigned (ew _ 33) = FA g pos) by (rewrite Ex33; apply unsigned_lit_small; lia).
  assert (Ux34 : bv_unsigned (ew _ 34) = shadow_addr (FA g pos))
    by (rewrite Ex34; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
  o9_region HS 0%nat Hs0. o9_region HS 7%nat Hs7.
  change (ms_mem (restrict (w_H W2) msc)) with (mrestrict (w_H W2) (ms_mem msc)) in Hs0, Hs7.
  pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 6 (SLit 0) Hs0
    ltac:(cbn [YP09.r_base base_val]; exact Ux34) ltac:(o9_in)) as SC6.
  pose proof (o9_chunk_aview _ W2 _ _ (shadow_addr (FA g pos)) 7 (SLit 2) Hs0
    ltac:(cbn [YP09.r_base base_val]; exact Ux34) ltac:(o9_in)) as SC7.
  change (bv_unsigned (sv_denot _ (SLit 0)) mod 256) with 0 in SC6.
  change (bv_unsigned (sv_denot _ (SLit 2)) mod 256) with 2 in SC7.
  unfold bm_frame_region in Hs7.
  pose proof (field_of_region _ _ 33 (FA g pos) _ 332 336 332 336 332 4 (SLit 0) 0 Hs7 Ux33 ltac:(o9_in) eq_refl
    ltac:(cbn; lia) ltac:(lia)) as V332c.
  change (N.to_nat 4) with 4%nat in V332c.
  o9_rreg HS (1%bv : bv 5) Gbra. o9_rreg HS (10%bv : bv 5) Gb0. o9_rreg HS (11%bv : bv 5) Gb1.
  o9_rreg HS (12%bv : bv 5) Gb2. o9_rreg HS (13%bv : bv 5) Gb3. o9_rreg HS (14%bv : bv 5) Gb4.
  rewrite (bm_den_off _ 33 (FA g pos) 192 Ex33) in Gb0 by lia.
  rewrite (bm_den_off _ 33 (FA g pos) 48 Ex33) in Gb3 by lia.
  assert (Gb1' : getr (ms_regs msc) 11 = w64 (d_dev c24)) by (rewrite Gb1; reflexivity).
  assert (Gb2' : getr (ms_regs msc) 12 = w64 64) by (rewrite Gb2; reflexivity).
  assert (Gb4' : getr (ms_regs msc) 14 = w64 (4 + 2)) by (rewrite Gb4; reflexivity).
  assert (Gbra' : getr (ms_regs msc) 1 = w64 0x82f74) by (rewrite Gbra; reflexivity).
  set (s9v := bv_unsigned (getr (ms_regs msc) 25)).
  assert (H25 : getr (ms_regs msc) 25 = w64 s9v) by (unfold s9v, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (KK : forall x, FA g pos + 192 <= x < FA g pos + 376 ->
    aview tfibsegs (w_H W2) (ms_mem msc) x = aview tfibsegs (w_H W2) mem2 x).
  { intros x Hx.
    destruct (Z_lt_le_dec x (FA g pos + 332)) as [Hlo | Hlo];
      [|destruct (Z_lt_le_dec x (FA g pos + 336)) as [Hhi | Hhi]].
    - apply KE; [lia | unfold o9_zone, shadow_addr, SHADOW_OFF in *; lia].
    - apply (o11_same _ _ _ (FA g pos + 332) 4 0 V332c); [|cbn; lia].
      rewrite Hwrc in Vwrc. replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia. exact Vwrc.
    - apply KE; [lia | unfold o9_zone, shadow_addr, SHADOW_OFF in *; lia]. }
  assert (KZ : forall a, bm_keepzone g pos sp1 a ->
    aview tfibsegs (w_H W2) (ms_mem msc) a = aview tfibsegs (w_H W2) mem2 a).
  { intros a Ha'. unfold bm_keepzone in Ha'. apply KE; [unfold BM_HI in *; lia|].
    unfold o9_zone, shadow_addr, SHADOW_OFF in *. lia. }
  assert (KSH : forall i, 0 <= i < 60 ->
    aview tfibsegs (w_H W2) (ms_mem msc) (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) o9_shS 0)).
  { intros i Hi.
    destruct (Z.eq_dec i 6) as [-> | H6]; [rewrite SC6; reflexivity|].
    destruct (Z.eq_dec i 7) as [-> | H7]; [rewrite SC7; reflexivity|].
    rewrite KE; [| unfold shadow_addr, SHADOW_OFF; lia | unfold o9_zone, shadow_addr, SHADOW_OFF in *; lia].
    rewrite (HSH i Hi). f_equal. symmetry. apply o9_shS_other; lia. }
  lazymatch goal with HSp : st_ok _ ?Ecur _ (restrict _ msc) |- _ =>
    assert (HAEc : env_agree 37 (bm_env g pos c regs2 ys) Ecur) by env_agree_chain HAE end.
  destruct (o9_callst B MT K XM_LIB LAWS g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 0 ys _ _ msc _ o9_shS s9v
    HJ0 Hfr HC Hops Hcur Hkat HJ HAEc HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) H25
    ltac:(vm_compute; o9_in) KZ KK KSH) as (HCc & Hopsc & Hcurc & Hkatc).
  (* owe_sysex(k, dev, 0x40, pl, chars + 2) *)
  set (bs := o9_pl c24 k).
  assert (Lbs : Z.of_nat (length bs) = 4 + 2) by (unfold bs, o9_pl; rewrite length_app, length_firstn, Rlen; cbn; lia).
  assert (Fbs : Forall (fun x => 0 <= x < 256) bs).
  { unfold bs, o9_pl. apply Forall_app. split; [apply Forall_cons; [lia | apply Forall_cons; [lia | apply Forall_nil]]|].
    apply Forall_forall. intros x Hx. apply In_nth with (d := 0) in Hx as (j & Hj & <-).
    rewrite length_firstn, Rlen in Hj. cbn in Hj. rewrite o9_nth_firstn by (cbn; lia). exact (proj2 (BY j ltac:(lia))). }
  assert (Hspec : owe_kZ k (Some c24) = (0, (fst (owe_sx (d_dev c24) 64 bs), KEY 7 (kz_a k), snd (owe_sx (d_dev c24) 64 bs)))).
  { unfold owe_kZ. rewrite Hkind. unfold bs, o9_pl. apply o9_ok; [lia|].
    apply (o11_sb_true (kz_bytes k) (d_chars c24)); [cbn; lia | rewrite Rlen; cbn; lia | exact Rby | exact Hall]. }
  assert (Fx : Forall (fun x => 0 <= x < 256) (fst (owe_sx (d_dev c24) 64 bs))).
  { unfold owe_sx. cbn [fst]. apply Forall_app. split; [|apply Forall_app; split; [exact Fbs|]].
    - repeat (apply Forall_cons; [first [lia | unfold u8; apply Z.mod_pos_bound; lia] |]). apply Forall_nil.
    - apply Forall_cons; [lia | apply Forall_nil]. }
  assert (BSc : block_shadow (aview tfibsegs (w_H W2) (ms_mem msc)) SHADOW_OFF (FA g pos + 48) 10).
  { apply bm_block_shadow; [exact Hf64 | lia | reflexivity | lia |].
    intros i Hi. change ((10 + 7) / 8) with 2 in Hi. change (48 / 8) with 6. change (10 / 8) with 1.
    change (10 mod 8) with 2.
    destruct (Z.eq_dec i 0) as [-> | H0]; [rewrite Z.add_0_r; exact SC6|].
    assert (Ei : i = 1) by lia. subst i. exact SC7. }
  pose proof HJ as (HARc & _).
  pose proof satU_T_main_owe_sysex as HT1. pose proof satU_T_main_fits as HT2.
  eapply cpw_call with (P := inv_chk B MT K XM_LIB g pos sp1 ops);
    [exact HS | reflexivity | | intros W' c' HP; apply SRr_ret; exact HP].
  cbn [ss_pc].
  apply (bm_owe_sysex_at B MT K XM_LIB LAWS MTL OSX (inv_chk B MT K XM_LIB g pos sp1 ops) g pos sp1 o9_shS s9v
    ly2 S2 W2 (ms_regs msc) (ms_mem msc) _ c k (d_dev c24) 64 (FA g pos + 48) bs 0x82f74 HJ Hfr Hmo HCc Hcurc Hkatc).
  + exact o9_shS_k.
  + exact Gb0.
  + split; [cbn; lia | exact Gb1'].
  + split; [lia | exact Gb2'].
  + exact Gb3.
  + rewrite Lbs. exact Gb4'.
  + apply Nat2Z.inj_le. rewrite Lbs. cbn. lia.
  + rewrite Lbs.
    exact (satU_main_pl_rd tfibsegs B LAWS ly2 S2 W2 (ms_mem msc) _ sp1 TB_owe_sysex pos (FA g pos) LLVMF_STK (e_sp0 g)
      48 10 48 (4 + 2) HARc Hin EFA Hf64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) BSc ltac:(lia) ltac:(lia)).
  + intros _. split; [lia|]. split; [|left; rewrite Lbs; lia].
    apply o9_garr_of_aview; [|exact Fbs].
    intros j Hj. rewrite <- Nat2Z.id in Hj. assert (Hj' : (j < 4 + 2)%nat) by lia.
    destruct j as [|[|j]].
    * rewrite Z.add_0_r. rewrite <- (Z.add_0_r (FA g pos + 48)). rewrite (PLK 0 ltac:(lia)). rewrite Z.add_0_r.
      exact PA0.
    * replace (FA g pos + 48 + Z.of_nat 1) with (FA g pos + 48 + 1) by lia. rewrite (PLK 1 ltac:(lia)).
      replace (FA g pos + 48 + 1) with (FA g pos + 49) by lia. exact PA1.
    * replace (FA g pos + 48 + Z.of_nat (S (S j))) with (FA g pos + 48 + (2 + Z.of_nat j)) by lia.
      rewrite (PLK (2 + Z.of_nat j) ltac:(lia)).
      replace (FA g pos + 48 + (2 + Z.of_nat j)) with (FA g pos + 50 + Z.of_nat j) by lia.
      rewrite (PLC (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id.
      unfold bs, o9_pl. cbn [nth app]. rewrite o9_nth_firstn by (cbn; lia). reflexivity.
  + exact Gbra'.
  + apply ret_ok_even. vm_compute. reflexivity.
  + lia.
  + (* owe_sysex returned to 0x82f74 *)
    intros W3 ly3 S3 regs3 mem3 md3 HJ3 Hfr3 Hmo3 HC3 Hcur3 HPR Hk3 KF.
    destruct (owe_sx (d_dev c24) 64 bs) as [wsx dsx] eqn:Esx.
    try rewrite Esx in Hspec; try rewrite Esx in Hk3; try rewrite Esx in Fx.
    cbn [fst snd] in Hspec, Fx. cbv beta iota in Hk3.
    assert (Hops3 : ops_at ops regs3).
    { destruct Hopsc as (Ho1 & Ho2). split; [exact Ho1|].
      assert (HPR20 : getr regs3 20 = getr (ms_regs msc) 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
      rewrite HPR20. exact Ho2. }
    exact (o9_after B MT K XM_LIB TL LAWS g pos sp1 ops c k (Some c24) s9v ly3 S3 W3 regs3 mem3 md3 wsx dsx
      HJ3 Hfr3 Hmo3 HC3 Hops3 Hcur3 Hk3 Hrec Hrc Hwrc ltac:(lia) Hspec Fx).
Qed.


End b.
End a.
