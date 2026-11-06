(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, with its module paths and module names changed; 118 of its 153 lines of code are new or changed and 205 lines of the source are left out. *)
(* The exit of diginet_scribble_encode at image A, from the block 0x85fe8 (ss_scrX) every path reaches:
     0x85fe8-0x85ff0  F[0] := 0x45e0360e (the frame header retired)
     0x85ff4          beqz s2: not taken, s2 = F >= 4096 (the real-stack release 0x86028-0x86044 is not reached)
     0x85ff8-0x86018  the frame's 8 shadow bytes := 0xf5
     0x8601c-0x86020  ld a1,56(s2); sb zero,0(a1): the flag byte cleared, the frame released (aj_flag_store)
     0x86048-0x86084  sp = s0 - 128, ra and s0-s11 back from the save area, sp += 128, ret.
   The run's writes are the frame, its shadow and its flag byte (fresh for the call state: cw_fresh_frame_j) and
   nothing else, so the walk's kept invariant (tcj_kept) and the 32 bytes of out carry to the return. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkKept CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_encode_A_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Lemma sce_exit : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k (regs : bvmap 5 word)
(out : Z) (before : list Z) (R : Z * option cmd) pos sp1 ly3 S3 (W3 : world tfibsegs) ms3 md3 E3,
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_scribble ->
spZ regs - 144 <= sp1 <= spZ regs - 128 ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) ly3 S3 W3 (ms_mem ms3) md3 k ->
~ In (0, pos) (frames Sc) ->
Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) -> mo_le MT Sc S3 0 -> same_io mdc md3 ->
env_agree 32 (Ereg regs (cw_extra [])) E3 ->
ew E3 70 = Z_to_bv 64 sp1 -> ew E3 75 = Z_to_bv 64 (frame_addr lyc 0 pos) ->
ew E3 87 = Z_to_bv 64 (flag_addr lyc 0 pos) -> ew E3 88 = Z_to_bv 64 (SB + frame_addr lyc 0 pos / 8) ->
ew E3 600 = Z_to_bv 64 (fst R) ->
tdst_ok B lyc Sc out 32 -> out + 32 <= spZ regs - T_scribble ->
tcj_kept tfibsegs B T_scribble lyc Sc W memc W3 (ms_mem ms3) (spZ regs) (cenc_wr out) ->
garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) out (cmd_outZ before (snd R)) -> length (cmd_outZ before (snd R)) = 32%nat ->
st_ok tfibsegs E3 ss_scrX (restrict (w_H W3) ms3) ->
SRr tfibsegs W3 (mkCfg ms3 md3)
(cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T_scribble (cenc_wr out) lyc Sc W memc mdc
  (cenc_res tfibsegs out before R)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs out before R pos sp1 ly3 S3 W3 ms3 md3 E3
HE Hsp1 HJ3 Hnin HP3 HM3 HIO3 HAE E70 E75 E87 E88 E600 Hout Hout2 KT3 HRES HL32 HS.
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_scribble HE
  ltac:(unfold T_scribble, T_sysex, ESTACK; lia)) as (Hceil0 & H47 & H46 & _ & Hpres0).
unfold T_scribble, T_sysex, ESTACK in Hwlo, Hceil0, H46, Hpres0, Hout2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _).
assert (Hfr3 : frames S3 = (0, pos) :: frames Sc) by (rewrite Hfrs3, Hfrs0; reflexivity).
assert (Hin3 : In (0, pos) (frames S3)) by (rewrite Hfr3; left; reflexivity).
assert (Efa : forall c p, frame_addr ly3 c p = frame_addr lyc c p).
{ intros c p. unfold frame_addr. destruct Hly0 as (_ & _ & _ & _ & _ & EF & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  rewrite EF, EF3. reflexivity. }
assert (Efl : flag_addr ly3 0 pos = flag_addr lyc 0 pos).
{ unfold flag_addr. destruct Hly0 as (_ & _ & _ & _ & _ & EF & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  rewrite EF, EF3. reflexivity. }
destruct (FFL ly3 S3 W3 (ms_mem ms3) md3 0 pos HAR3 Hin3) as (HFLp & HFLo & _ & (HFL0 & _ & HFLc)).
rewrite Efl in HFLp, HFLo, HFL0, HFLc.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR3 Hin3) as (_ & _ & HFb & HFs).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 0 pos HAR3 Hin3) as (HF4096 & HFceil & _).
rewrite Efa in HFb, HFs, HF4096, HFceil.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
set (sp := spZ regs) in *.
assert (AG : forall n, (n < 32)%nat -> ew E3 n = ew (Ereg regs (cw_extra [])) n) by (intros n Hn; exact (proj1 HAE n Hn)).
assert (B2 : bv_unsigned (ew (Ereg regs (cw_extra [])) 2) = sp) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E1 : ew E3 1 = getr regs 1) by (rewrite (AG 1%nat) by lia; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (HSF : 0 <= shadow_addr F < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia));
  pose proof (Z.div_le_upper_bound F 8 F ltac:(lia) ltac:(lia)); lia).
assert (HSB : shadow_addr F = SB + F / 8) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity).
assert (HSB2 : 0 <= SB + F / 8 < 2 ^ 64) by (rewrite <- HSB; exact HSF).
assert (HSB' : shadow_addr F = 2147450880 + F / 8) by (rewrite HSB; reflexivity).
assert (HF8 : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
(* the flag byte as a region in front: FL is the runtime's own, the frame, its shadow and the stack are not *)
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (ast_ok_add_region tfibsegs Ev ssv msv (cw_flag_region 87) HS eq_refl
  (cw_flag_region_ok B FFL Ev 87 ly3 S3 W3 (ms_mem ms3) md3 0 pos HAR3 Hin3 ltac:(rewrite Efl; exact E87))
  ltac:(cbn [ss_mem ss_scrX all_disjoint]; unfold cw_flag_region, extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E87, E88, E75, (AG 2%nat) by lia; rewrite B2;
    rewrite !unsigned_lit_small by lia;
    split; [pose proof (cw_flag_apart B ly3 S3 FL (shadow_addr F) (shadow_addr F + 8) HFLo
             ltac:(intros a Ha; replace a with (shadow_addr F + (a - shadow_addr F)) by lia; exact (proj2 (HFs (a - shadow_addr F) ltac:(lia)))));
           lia|];
    split; [pose proof (cw_flag_apart B ly3 S3 FL F (F + 64) HFLo ltac:(intros a Ha; exact (proj2 (HFb a Ha)))); lia|];
    split; [lia | exact I])) as HS1 end.
clear HS. rename HS1 into HS. norm_ss HS. pose proof HJ3 as HJ3p.
(* the release run, to `ret` *)
aj_run_flag_sh tfibtbl_lib_ok HS HJ3;
[ lia
| eapply (cw_awrf_flag_front _ _ _ _ _ _ _ _ _ _ 87%nat);
  [ reflexivity | rewrite E87, unsigned_lit_small by lia; exact (eq_sym Efl) | cbn; lia | cbn; lia |];
  sce_awr AG sp sp1 pos
| flag0 E87 Efl
| ].
lazymatch goal with HFr : frame_of ?Ev ?rs (mrestrict _ (ms_mem ms3)) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
(* every byte the release run wrote: the flag byte, the frame's shadow, the frame (all fresh), or the save area *)
assert (HXc : forall a, in_wrange Ev rs a ->
  (sp - 4304 <= a < sp) \/ cw_fresh B lyc Sc a);
[ intros a (r & Hr & Hb);
  lazymatch type of Hr with In _ ?rl => let rl' := eval vm_compute in rl in change (In r rl') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; revert Hb; evalE AG; intros Hb;
      first
      [ left; lia
      | right; eapply (cw_fresh_frame_j B LAWS FFL); [exact HJ0 | exact HJ3p | exact HP3 |];
        unfold frame_rng, in_zr; cbn [fst snd]; fold F; fold FL;
        try change (fs_frame_bytes 0 / 8) with 8; try change (fs_frame_bytes 0) with 64;
        first [ left; lia | right; left; lia | right; right; lia ] ]
    | ]);
  destruct Hr
| ];
(* the kept invariant at the return *)
assert (KK : tcj_kept tfibsegs B T_scribble lyc Sc W memc W3 m2 sp (cenc_wr out));
[ apply (cw_kept_step B LAWS T_scribble lyc Sc W memc mdc W3 (ms_mem ms3) m2 sp (cenc_wr out) (in_wrange Ev rs));
  [ unfold T_scribble, T_sysex, ESTACK; lia | exact HAR0 | exact KT3
  | intros a Ha Hx; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
    rewrite unsigned_lit_small by exact Ha; exact Hx
  | intros a Hx; destruct (HXc a Hx) as [Hw | Hw]; [left; unfold T_scribble, T_sysex, ESTACK; lia | right; right; exact Hw]
  | intros a Hp; eapply apresent_grows; [exact HG | exact Hp] ]
| ];
(* the 32 bytes of out are not written by the run *)
assert (HRES2 : garr8 tfibsegs (mrestrict (w_H W3) m2) out (cmd_outZ before (snd R)));
[ intros j Hj; destruct (HRES j Hj) as (Hv & Hb); split; [|exact Hb];
  apply (cw_val_mem_kept (w_H W3) (w_H W3) (ms_mem ms3) m2 _ 1 _); [|exact Hv];
  intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx;
  assert (Hxo : out <= x < out + 32) by (rewrite HL32 in Hj; lia);
  unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 x)); [reflexivity|];
  rewrite unsigned_lit_small by (pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc out 32 x HAR0 Hout Hxo); lia);
  intros Hw; destruct (HXc x Hw) as [Hw' | (_ & _ & Hfb & Hff)];
  [ pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc out 32 x HAR0 Hout Hxo); lia
  | destruct (Hout x Hxo) as [(bb & m & Hinb & Hrb) | (cid & ps & Hinf & Hrf)];
    [ exact (Hfb bb m (x - bb) Hinb ltac:(lia) ltac:(lia))
    | exact (proj1 (Hff cid ps Hinf) Hrf) ] ]
| ] end.
cw_frame_leaf ltac:(idtac; exact KK)
  ltac:(idtac; unfold cenc_res; split;
    [ rewrite R10; cbn [sv_denot]; rewrite E600, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact HRES2 ]).
Qed.
End d.
End b.
