(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the TAIL segment of sup_chain's walk on plugin-hostd/fuzz_command's ASan+UBSan
   build (fuzz_command.asan-ubsan), from the loop exit BASE + SCB_LEXIT = 0x8c444 to the return 0x8c558, against the
   interface lib/B/Prog/sup_chain_d.v (scb_lctx, scb_inv) and the helpers lib/B/Prog/sup_chain_aux.v. Statement from
   a Theorem Labs lane 707acd856cb (lib/B/Prog/sup_chain_c.v, tsup_chain_spec). The block bookkeeping of the post is the pure lemma
   scb4_final_blocks; the release segment 0x8c47c .. 0x8c558 is scb4_rel; scb_tail composes the four calls with both.

   The code: ld s2,8(s1) (the slot); arg_s(slot, list) 0x8c450; free(list) 0x8c458; rec_shape_of("chain", 5)
   0x8c468; answer(slot, shape, 1) 0x8c478 with this call's class-1 frame still live; then the inline release
   0x8c47c .. 0x8c4e4 (the magic 0x45e0360e at F, f5 at the frame's 16 shadow bytes, the flag byte through the word
   at F + 120), the epilogue (the saved registers back, sp := s0 - 192 + 192) and `ret`. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_chain_s4.v, with its module paths, module names and numbers changed; 312 of its 339 lines of code are new or changed and 2024 lines of the source are left out. *)
(* Segment EXIT of the image-B walk of LLVMFuzzerTestOneInput (fuzz_codec.asan-ubsan 0x83530-0x836b4): seg_exit of
   lib/AU/Prog/codec_bmain_inv.v.
   Phase 1, from the EXIT cut (bm_entry0 with the spills only, then the frame's first word and its shadow as regions):
     0x83530 / 0x83534 s4 = a5 = F (spills 80 / 72); 0x83538-0x83558 text's nine shadow bytes 10 .. 18 set to 0xf8;
     0x8355c-0x83564 F[0] = 0x45e0360e (the frame retired); 0x83568 beqz s4 decided (F >= 4096, so the machine-stack
     release 0x83584-0x83670 is not run); 0x8356c-0x83574 a1 = 64, a0 = s2 = shadow_addr F, the call of the shadow
     fill with 0xf5 (aset_shadow_realizes at 0x54ab0, in journal form by codec_bmain_exit_rt.bx_set_shadow_at).
   Phase 2, at the return 0x83578, a new state over the call's registers: the flag byte (atom 34), the flag word at
   F + 504 (on s4) and the thirteen saved words below sp0 (on s0, atoms 35 .. 47 = the entry's ra, s0, s1, s2 .. s11).
     0x83578-0x8357c the flag byte cleared through the word at F + 504 (YCem.aj_flag_store_sh: the frame leaves the
     journal's own frames), 0x83580 j, 0x83674-0x836b4 a0 = 0, the thirteen restores, sp = sp0, ret to the entry's ra.
   The range holds no UBSan trap edge (codec_bmain_inv.v's trap lists have no pc in 0x83530-0x836b4). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YG0p.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YO09 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkKeptU CPgWalkFrameU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_exit_rt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* lib/Reusable/YCbq.v's appn (the zones unfolded) *)
Ltac bx_appn := unfold app_addr, in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd,
  kHighShadowEnd, kImgLo in *.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ================================ small facts ================================ *)
(* the frame's bytes are application memory, its shadow is in the shadow zone: the two are apart *)
Lemma bx_sh_apart : forall F, in_app F 512 -> F + 512 <= shadow_addr F \/ shadow_addr F + 64 <= F.
Proof.
intros F Ha. unfold shadow_addr, SHADOW_OFF. bx_appn.
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M. lia.
Qed.
Lemma bx_den_x : forall regs xs j, sv_denot (Ereg regs (cw_extra xs)) (SOff (33 + j) 0) = Z_to_bv 64 (nth j xs 0).
Proof. intros regs xs j. rewrite sv_denot_SOff0. apply cw_ew_x. Qed.
Lemma bx_unsigned_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.
(* a saved word as an 8-byte chunk of an extra atom *)
Lemma bx_sv_chunk : forall regs xs m base off j v,
nth j xs 0 = v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs (Ereg regs (cw_extra xs)) m base (YP09.mkChunk off (CVal 8 (SOff (33 + j) 0))).
Proof.
intros regs xs m base off j v Hj Hv Hm.
apply (chunk_ok_val tfibsegs _ m base off 8 (SOff (33 + j) 0) v).
- rewrite bx_den_x, Hj. reflexivity.
- change (8 * Z.of_N 8) with 64. lia.
- cbn. lia.
- exact Hm.
Qed.

(* ================================ the state at the return of the shadow fill ================================ *)
Definition bx_rfl : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition bx_rfw : YP09.region := YP09.mkRegion (Some 20%nat) 504 512 0 0 [YP09.mkChunk 504 (CVal 8 (SOff 34 0))].
Definition bx_saves : list YP09.chunk :=
[YP09.mkChunk (-8) (CVal 8 (SOff 35 0)); YP09.mkChunk (-16) (CVal 8 (SOff 36 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 37 0)); YP09.mkChunk (-32) (CVal 8 (SOff 38 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 39 0)); YP09.mkChunk (-48) (CVal 8 (SOff 40 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 41 0)); YP09.mkChunk (-64) (CVal 8 (SOff 42 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 43 0)); YP09.mkChunk (-80) (CVal 8 (SOff 44 0));
 YP09.mkChunk (-88) (CVal 8 (SOff 45 0)); YP09.mkChunk (-96) (CVal 8 (SOff 46 0));
 YP09.mkChunk (-104) (CVal 8 (SOff 47 0))].
Definition bx_rsv : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 bx_saves.
Definition bx_xs (R : bvmap 5 word) (F FL : Z) : list Z :=
[F; FL; bv_unsigned (getr R 1); bv_unsigned (getr R 8); bv_unsigned (getr R 9);
 bv_unsigned (getr R 18); bv_unsigned (getr R 19); bv_unsigned (getr R 20); bv_unsigned (getr R 21);
 bv_unsigned (getr R 22); bv_unsigned (getr R 23); bv_unsigned (getr R 24); bv_unsigned (getr R 25);
 bv_unsigned (getr R 26); bv_unsigned (getr R 27)].

(* the zone phase 1 writes: the frame's first word and text's nine shadow bytes *)
Ltac bx_kwr U33 U34 :=
  idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
      rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia; rewrite ?U33, ?U34 in Hb; lia | ]);
  destruct Hr.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ASSF5 : aset_shadow_realizes tfibsegs B BM_set_shadow_f5 0xf5.

Theorem seg_exit_holds : seg_exit B MT K XM_LIB.
Proof using MTF TL LAWS ML ASF FFL ASSF5.
unfold seg_exit.
intros g pos sp1 W2 c2 HX.
destruct HX as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & HMLE & HC & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & _).
pose proof HC as (Hpre & Hsp1 & R2 & R9 & R8 & R3 & R4 & R21 & R18 & R27 & R23 & R25 & R19 & R26 & HF64 &
  V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 & V128 & V136 & V144 & V152 &
  S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & VFL & HSH & HIN & HPERM).
pose proof Hpre as Hpre0. unfold e_pre, codec_lib_pre_x in Hpre0.
destruct Hpre0 as (HFN & Hra & _).
pose proof HFN as (_ & Hret & Hra4 & Hgp & Htp & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (FS512 : fs_frame_bytes 3 = 512) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HJ as (HAR & Hly & _).
assert (EFL : flag_addr ly2 3 pos = flag_addr (e_ly g) 3 pos).
{ unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA, FS512 in Happ.
pose proof (bx_sh_apart (FA g pos) Happ) as Hsep.
destruct (FFL ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & HFLo & _ & HFL4096 & _ & HFLc).
set (F := FA g pos) in *.
set (FL := flag_addr ly2 3 pos) in *.
rewrite <- EFL in VFL.
assert (HshF : SB + 512 <= shadow_addr F <= SB + 2 ^ 44).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF. split; [apply Z.add_le_mono_l; apply Z.div_le_lower_bound; lia|].
  apply Z.add_le_mono_l. apply Z.div_le_upper_bound; [lia|]. unfold BM_HI in Hchi. lia. }
unfold SB in HshF.
(* ---- phase 1: the state at EXIT ---- *)
pose proof (bm_entry0 B MT K XM_LIB TL LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 k PC_EXIT [] [] []
  HJ Hfr HC eq_refl (Forall_nil _) I (Forall_nil _) I) as HS0.
remember (bm_env g pos 0 regs2 []) as E eqn:HEE in HS0.
assert (E33 : ew E 33 = Z_to_bv 64 F) by (subst E; exact (bm_ew_F g pos 0 regs2 [])).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr F)) by (subst E; exact (bm_ew_SH g pos 0 regs2 [])).
assert (U33 : bv_unsigned (ew E 33) = F) by (rewrite E33; apply unsigned_lit_small; unfold BM_HI in Hchi; lia).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr F) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E2 : ew E 2 = getr regs2 2) by (subst E; exact (bm_ew_reg g pos 0 regs2 [] 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs2 3) by (subst E; exact (bm_ew_reg g pos 0 regs2 [] 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs2 4) by (subst E; exact (bm_ew_reg g pos 0 regs2 [] 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs2 8) by (subst E; exact (bm_ew_reg g pos 0 regs2 [] 8 8%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
(* keep the spills only, then add text's shadow window and the frame's first word *)
lazymatch type of HS0 with st_ok _ ?Ev ?ssv ?msv =>
  let l := eval vm_compute in (ss_mem ssv) in
  let r4 := eval vm_compute in (nth 3 l got_region) in
  assert (HS1 : st_ok tfibsegs Ev (mkSS (ss_pc ssv) (ss_regs ssv) [r4] (ss_resv ssv) (ss_facts ssv)) msv)
  by (apply (st_ok_submem tfibsegs Ev ssv msv [r4] HS0); [change (submem [r4] l); submem_to | reflexivity])
end.
clear HS0.
pose proof (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 k 0 [] 0 8 0 8 []
  HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _)) as HRfh.
pose proof (bm_shadow_region_ok B MT K XM_LIB LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 k 0 [] 10 19
  HJ Hfr HC ltac:(lia) ltac:(lia)) as HRsh.
rewrite <- HEE in HRfh, HRsh. clear HEE.
pose proof (ast_ok_add_region tfibsegs E _ _ (bm_frame_region 0 8 0 8 []) HS1 eq_refl HRfh
  ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, bm_frame_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U33, B2; split; [lia | exact I])) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. clear HS1.
pose proof (ast_ok_add_region tfibsegs E _ _ (bm_shadow_region 10 19 (shm SH_F8)) HS2 eq_refl HRsh
  ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, bm_shadow_region, bm_frame_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U33, U34, B2;
        split; [lia | split; [lia | exact I]])) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS. clear HS2 HRfh HRsh.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ ((F <= a < F + 8) \/ (shadow_addr F + 10 <= a < shadow_addr F + 19)) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
unfold cfg_at. change (w64 PC_EXIT) with (Z_to_bv 64 PC_EXIT).
(* 0x83530 .. jal 0x54ab0 *)
(* the run writes the frame's shadow, so it is the shadow engine's (YCem), not the token layer's *)
aj_run_to_sh tfibtbl_lib_ok HS HJ 0x54ab0.
{ cw_awrA.
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end.
  eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 pos 34%nat);
  [ reflexivity | rewrite U34, EFA; reflexivity | left; reflexivity | cbn; lia
  | cbn [YP09.r_whi]; change (fs_frame_bytes 3 / 8) with 64; lia |].
  eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 3 pos 33%nat);
  [ reflexivity | rewrite U33, EFA; reflexivity | left; reflexivity | cbn; lia
  | cbn [YP09.r_whi]; rewrite FS512; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
cw_ajA HJ.
cw_keep ltac:(bx_kwr U33 U34).
(* the registers at the call *)
rreg HS (1%bv : bv 5) Gra. rreg HS (2%bv : bv 5) Gsp. rreg HS (3%bv : bv 5) Ggp. rreg HS (4%bv : bv 5) Gtp.
rreg HS (8%bv : bv 5) Gs0. rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (20%bv : bv 5) Gs4.
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Gsp, Ggp, Gtp, Gs0, Ga0, Gs4.
rewrite E2, R2 in Gsp. rewrite E3, R3 in Ggp. rewrite E4, R4 in Gtp. rewrite E8, R8 in Gs0.
rewrite E34 in Ga0. rewrite E33 in Gs4.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
eapply SRr_bind.
{ eapply (bx_set_shadow_at tfibsegs B LAWS tfib_segs_low BM_set_shadow_f5 0xf5 ASSF5 W2 (ms_regs ms) (ms_mem ms)
    LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 _ k 3 pos
    (shadow_addr F) 64 (sp1 - e_sp0 g) (Z_to_bv 64 0x83578) HJ).
  - left. reflexivity.
  - exact Ga0.
  - exact Ga1.
  - lia.
  - rewrite EFA. lia.
  - rewrite EFA, FS512. change (512 / 8) with 64. lia.
  - unfold spZ. rewrite Gsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2.
    rewrite Hsp32, Z.add_0_r in D1. rewrite Hsp016, Z.add_0_r in D2.
    replace (sp1 - e_sp0 g) with ((2 * (sp1 / 32) - e_sp0 g / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold ESTACK. lia.
  - exact Ggp.
  - exact Gtp.
  - exact Gra.
  - apply ret_ok_even. vm_compute. reflexivity. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HAR3 & Hf5 & Hkept3).
(* ---- phase 2: the state at 0x83578 ---- *)
lazymatch type of Gs0 with getr ?rgT _ = _ =>
  assert (P8 : getr regs3 8 = w64 (e_sp0 g))
    by (transitivity (getr rgT 8); [exact (HP3 8 ltac:(unfold acallee_saved; lia)) | exact Gs0]);
  assert (P20 : getr regs3 20 = Z_to_bv 64 F)
    by (transitivity (getr rgT 20); [exact (HP3 20 ltac:(unfold acallee_saved; lia)) | exact Gs4]);
  assert (P3 : getr regs3 3 = w64 (as_gp B))
    by (transitivity (getr rgT 3); [exact (HP3 3 ltac:(unfold acallee_saved; lia)) | exact Ggp]);
  assert (P4 : getr regs3 4 = w64 (as_tp B))
    by (transitivity (getr rgT 4); [exact (HP3 4 ltac:(unfold acallee_saved; lia)) | exact Gtp]) end.
(* the bytes phase 2 reads, kept from the EXIT cut through phase 1 and the fill *)
assert (KK : forall x, (F + 504 <= x < F + 512 \/ e_sp0 g - 104 <= x < e_sp0 g) ->
  aview tfibsegs (w_H W2) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. rewrite (Hkept3 x ltac:(unfold BM_HI in Hchi; lia) ltac:(lia)).
  apply KE; [unfold BM_HI in Hchi; lia | lia]. }
assert (VK : forall a v, (forall x, a <= x < a + 8 -> F + 504 <= x < F + 512 \/ e_sp0 g - 104 <= x < e_sp0 g) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem3) a 8 v).
{ intros a v Ha Hv. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3 a 8 v); [|exact Hv].
  intros x Hx. apply KK. apply Ha. cbn in Hx. lia. }
destruct (FFL ly2 S2 W2 mem3 md3 3 pos HAR3 Hin) as (HFLp3 & _).
fold FL in HFLp3.
destruct (al_frames _ _ LAWS ly2 S2 W2 mem3 md3 3 pos HAR3 Hin) as (_ & _ & Hfb3 & _).
rewrite EFA, FS512 in Hfb3.
assert (HFLa : F + 512 <= FL \/ FL + 1 <= F + 504).
{ apply (cw_flag_apart B ly2 S2 FL (F + 504) (F + 512) HFLo).
  intros a Ha. exact (proj2 (Hfb3 a ltac:(lia))). }
set (xs2 := bx_xs (e_regs g) F FL).
set (E5 := Ereg regs3 (cw_extra xs2)).
assert (X34 : ew E5 34 = Z_to_bv 64 FL) by exact (cw_ew_x regs3 xs2 1).
assert (U34' : bv_unsigned (ew E5 34) = FL) by (rewrite X34; apply unsigned_lit_small; lia).
assert (U20' : bv_unsigned (ew E5 20) = F).
{ unfold E5. rewrite (ew_Ereg_nat regs3 _ 20 20%bv eq_refl), P20. apply unsigned_lit_small. unfold BM_HI in Hchi. lia. }
assert (U8' : bv_unsigned (ew E5 8) = e_sp0 g).
{ unfold E5. rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), P8. unfold w64. apply unsigned_lit_small. lia. }
assert (HS5 : st_ok tfibsegs E5 (mkSS 0x83578 sr_atoms [bx_rfl; bx_rfw; bx_rsv] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 0x83578) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, bx_rfl. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      fold E5. rewrite U34'. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable tfibsegs). replace (FL + o) with FL by lia. exact HFLp3.
    + unfold region_ok, bx_rfw. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      fold E5. rewrite U20'. unfold BM_HI in Hchi.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (bx_sv_chunk regs3 xs2 _ F 504 1 FL); [reflexivity | lia |].
      apply VK; [intros x Hx; lia | exact VFL].
    + unfold region_ok, bx_rsv. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      fold E5. rewrite U8'.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold bx_saves.
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
        let j := eval vm_compute in (n - 33)%nat in
        change n with (33 + j)%nat; eapply (bx_sv_chunk regs3 xs2 _ _ off j);
        [reflexivity | apply bx_unsigned_range | apply VK; [intros x Hx; lia|]] end;
      lazymatch goal with |- val_mem _ _ (e_sp0 g + ?o) _ _ =>
        replace (e_sp0 g + o) with (e_sp0 g - - o) by lia; cbn [Z.opp] end;
      assumption.
  - apply pairwise_disjoint_of_extents.
    unfold bx_rfl, bx_rfw, bx_rsv, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E5. rewrite U34', U20', U8'.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold BM_HI in Hchi. repeat split; lia.
  - split; [exact I|]. split; exact I. }
(* the atoms of the restores, for the final registers *)
assert (XR1 : ew E5 35 = getr (e_regs g) 1)
  by (unfold E5, xs2; change 35%nat with (33 + 2)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR8 : ew E5 36 = getr (e_regs g) 8)
  by (unfold E5, xs2; change 36%nat with (33 + 3)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR9 : ew E5 37 = getr (e_regs g) 9)
  by (unfold E5, xs2; change 37%nat with (33 + 4)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR18 : ew E5 38 = getr (e_regs g) 18)
  by (unfold E5, xs2; change 38%nat with (33 + 5)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR19 : ew E5 39 = getr (e_regs g) 19)
  by (unfold E5, xs2; change 39%nat with (33 + 6)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR20 : ew E5 40 = getr (e_regs g) 20)
  by (unfold E5, xs2; change 40%nat with (33 + 7)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR21 : ew E5 41 = getr (e_regs g) 21)
  by (unfold E5, xs2; change 41%nat with (33 + 8)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR22 : ew E5 42 = getr (e_regs g) 22)
  by (unfold E5, xs2; change 42%nat with (33 + 9)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR23 : ew E5 43 = getr (e_regs g) 23)
  by (unfold E5, xs2; change 43%nat with (33 + 10)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR24 : ew E5 44 = getr (e_regs g) 24)
  by (unfold E5, xs2; change 44%nat with (33 + 11)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR25 : ew E5 45 = getr (e_regs g) 25)
  by (unfold E5, xs2; change 45%nat with (33 + 12)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR26 : ew E5 46 = getr (e_regs g) 26)
  by (unfold E5, xs2; change 46%nat with (33 + 13)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR27 : ew E5 47 = getr (e_regs g) 27)
  by (unfold E5, xs2; change 47%nat with (33 + 14)%nat; rewrite cw_ew_x; cbn [nth bx_xs]; apply Z_to_bv_bv_unsigned).
assert (XR2 : ew E5 8 = getr (e_regs g) 2).
{ unfold E5. rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), P8. unfold w64, e_sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (XR3 : ew E5 3 = getr (e_regs g) 3).
{ unfold E5. rewrite (ew_Ereg_nat regs3 _ 3 3%bv eq_refl), P3. symmetry. exact Hgp. }
assert (XR4 : ew E5 4 = getr (e_regs g) 4).
{ unfold E5. rewrite (ew_Ereg_nat regs3 _ 4 4%bv eq_refl), P4. symmetry. exact Htp. }
clearbody E5 xs2.
clear HS KE Hkept3 HP3 Gra Gsp Ggp Gtp Gs0 Ga0 Ga1 Gs4 HJ.
rename HJ3 into HJ.
unfold YK0s.ret_ok in Hret.
(* 0x83578 .. ret: the flag byte cleared, a0 = 0, the restores; the kit's flag-store step takes the frame-flag law in
   lib/AU/YCbqU.v's form *)
pose proof (ffl_U_of_A B FFL) as FFLU.
aj_run_flag_sh tfibtbl_lib_ok HS5 HJ.
- lia.
- intros a (r & Hr & Hb).
  cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; unfold bx_rfl, bx_rfw, bx_rsv in Hb;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
  + right. rewrite U34' in Hb. fold FL. lia.
  + lia.
  + lia.
- intros msr HSr. fold FL.
  lazymatch type of HSr with st_ok _ ?Ex ?ssx _ =>
    pose proof (st_ok_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR end.
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region _ (ms_mem msr) n FL cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
      ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact U34')
      ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end.
  pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0. exact V0.
- (* the run's end: aj_run_flag_sh has introduced the state at `ret` (HS5) and the journal without the frame (HJ) *)
  cw_ajA HJ.
  eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W2 E5); [exact HS5 | reflexivity | vm_compute; reflexivity |].
  intros mat2.
  rreg HS5 (1%bv : bv 5) F1. rreg HS5 (10%bv : bv 5) F10.
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in F1.
  red.
  lazymatch goal with |- exists _ _ _ _ _ _, {| cfg_ms := mkst (ms_regs ?msf) _ _ _; cfg_model := ?mdf |} = _ /\ _ =>
    exists ly2, (stack_free_state 3 pos S2), (ms_regs msf), (ms_mem msf), mdf, k end.
  split.
  { unfold cfg_at. rewrite F1, XR1, Hret. unfold raZ in Hra. unfold w64. rewrite <- Hra, Z_to_bv_bv_unsigned. reflexivity. }
  split; [eapply (ajournal_materialize tfibsegs B LAWS tfib_segs_low); exact HJ|].
  split; [lia|].
  split.
  { apply aregs_preserved_eqs;
    lazymatch goal with |- getr _ ?r = getr _ _ => let R := fresh "R" in rreg HS5 r R; rewrite R; clear R end;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    first [ exact XR2 | exact XR3 | exact XR4 | exact XR8 | exact XR9 | exact XR18 | exact XR19 | exact XR20
          | exact XR21 | exact XR22 | exact XR23 | exact XR24 | exact XR25 | exact XR26 | exact XR27 ]. }
  split; [rewrite F10; reflexivity|].
  split; [exact (cw_perm_release B ly2 S2 (e_ly g) (e_S g) 3 pos HPERM)|].
  exact (cw_mo_le_release MT MTF (e_S g) S2 3 pos 0 HMLE).
Qed.
End b.
End a.
