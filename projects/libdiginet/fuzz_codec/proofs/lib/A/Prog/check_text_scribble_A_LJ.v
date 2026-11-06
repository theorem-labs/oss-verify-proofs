(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, with its module paths changed; 260 of its 281 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_text_scribble_A_LB.v, with its addresses changed; 364 of its 464 lines of code are new or changed and 181 lines of the source are left out. *)
(* The inlined owed_scribble_text loop of check_text_scribble at image A: 0x83918-0x83958, the store of the
   turn's byte into the frame's want array and the two tests that end the turn. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36 AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall CPgWalkIntr check_text_scribble_A
check_text_scribble_A_LD.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Ltac ctl_show HS := lazymatch type of HS with st_ok _ ?E ?ss _ => let v := eval vm_compute in ss in idtac "ST" v end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Lemma ctl_join_holds :
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q,
ctl_pre B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 ->
cts_pad_cont B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch n tb S2 fpos SP1 E0 Q ->
ctl_head B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q ->
ctl_join B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 (Datatypes.S fuel) Q.
Proof using TL LAWS ML.
unfold ctl_join, ctl_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q
  HPRE PAD HEAD EZ msZ mdZ o i pre cv st HS HAT E417 E418 E460 E461
  Ho Hfuel Hi Hcv Hst Hilen HFLD Hplen HMOD HWANT.
destruct HPRE as (HE & H10 & H11 & H12 & Hn & Hstr & Hoq & Hoch & Hdst & Hdisj & EE & E32
  & Hfin2 & Hfrs2 & Eab & HSP1 & HSP1al).
red in HAT. destruct HAT as (AG & E33 & E38 & E60 & E61 & HJ & KT & HIO).
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HJ0) as HAR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble HE
  ltac:(unfold T_check_text_scribble, ESTACK; lia)) as (Hceil & H47 & H46 & _ & Hpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_check_text_scribble, ESTACK in *.
pose proof (proj1 HJ) as HAR2.
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 fpos) in *.
assert (HF8a : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8b : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (HZfr : forall a, F <= a < F + 64 -> cw_fresh B lyc Sc a).
{ intros a Ha. apply (cw_fresh_own B LAWS lyc Sc lyc S2 W (ms_mem msZ) mdZ 0 fpos a HAR2 Hfrs2
    ltac:(rewrite Eab; apply Permutation_refl) ltac:(intros; reflexivity)).
  left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
assert (B2 : spZ regs = bv_unsigned (ew E0 2)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HFLu : 0 <= ctl_FLu lyc fpos < 2 ^ 64) by (unfold ctl_FLu; apply u64_range).
assert (Htf : forall x, q <= x < q + Z.of_nat (length tb) -> ~ (F <= x < F + 64)).
{ intros x Hx Hinn. destruct (HZfr x Hinn) as (_ & _ & Hblk & Hfrm).
  destruct Hoq as [(bb & mm & Hb & Hlo & Hhi) | (cid & pos & Hb & Hlo & Hhi)].
  - exact (Hblk bb mm (x - bb) Hb ltac:(lia) ltac:(lia)).
  - destruct (Hfrm cid pos Hb) as (Hzz & _).
    exact (Hzz ltac:(unfold in_zr, frame_rng; cbn [fst snd]; lia)). }
assert (HF8m : F mod 8 = 0)
  by (destruct (proj1 (Z.mod_divide F 64 ltac:(lia)) HF64) as (kk & Hkk);
      replace F with (kk * 8 * 8) by lia; apply Z_mod_mult).
assert (HFam : amem_range F 64).
{ clear - HFapp C1 C2 C3 C4 C5.
  unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd, ASAN_CEIL in *. lia. }
assert (HFd8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
assert (HFS : F + 64 <= shadow_addr F \/ shadow_addr F + 8 <= F).
{ unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
  destruct HFapp as (_ & [Hl | Hh]); [left | right]; lia. }
pose proof Hstr as (Hq0 & Hgtb & Hin0 & Hcrd).
pose proof Hcrd as (Hcq0 & Hcqhi & Hcrdb & Hcra & Hchull & Hcam & Hcwin).
pose proof Hdst as (Hch0 & Hchhi & Htd & Htwr & Hchra0 & Hchhull0 & Hcham & Hchwin).
unfold coff_win in Hcwin, Hchwin.
destruct (cts_cstring tb Hin0) as (Hzl & Hz0 & Hnz).
assert (Hi16 : i + st <= 16)
  by (pose proof (ctl_i_small tb (Z.to_nat n) (o + 1) (i + st) (pre ++ [cv]) HMOD); lia).
pose proof HJ as HJn. clear HJ. rename HJn into HJ.
assert (SHOK : sh_ok tfibsegs CW_Bx [] EZ (mrestrict (w_H W) (ms_mem msZ))) by constructor.
assert (HWK : forall a, F + 32 <= a < F + 40 ->
  aview tfibsegs (w_H W) (ms_mem msZ) a = aview tfibsegs (w_H W) (ms_mem msZ) a) by (intros; reflexivity).
ctl_ufacts SP1 (spZ regs) E33 AG B2.
(* 0x83918 add a0,s6,a1: the want slot's address, pinned to atom 462 *)
cw_run_to ctl_awr 0x8391c.
ctl_wkeep F. ctl_keep F HZfr.
ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (U38c : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
  assert (U61c : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia) end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (F + 32 + o))
    (ctl_denot_of_U Ev _ _ (ctl_add_off Ev 38 32 417 F o E38 E417
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) R10 end.
ctl_pin (10%bv : bv 5) 462%nat.
ctl_rebase.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E462 : ew Ev 462 = Z_to_bv 64 (F + 32 + o)) by (rewrite ctl_ew_h0; exact R10) end.
ctl_ufacts SP1 (spZ regs) E33 AG B2.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (U462c : bv_unsigned (ew Ev 462) = F + 32 + o) by (rewrite E462; apply unsigned_lit_small; lia);
  assert (U61d : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
  assert (E32v : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
(* the want array's zero shadow byte: its eight bytes are marked usable *)
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
  pose proof (ctl_sh4_of (w_H W) Ev ssx msx F HS ltac:(vm_compute; reflexivity) U61d) as HSH4;
  assert (HRAw : range_addressable (aview tfibsegs (w_H W) (ms_mem msx)) SHADOW_OFF (F + 32) 8)
    by (apply (ctl_want_ra (w_H W) (ms_mem msx) F 8 HSH4 HF64 ltac:(lia) ltac:(lia))) end.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 462%nat (mkAF 1 (2 ^ 47 - 2) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E462, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; repeat split; first [lia | apply Z.mod_1_r])) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
repeat match goal with Hsh : sh_ok _ _ _ _ _ |- _ => clear Hsh end.
lazymatch goal with HSx : st_ok _ ?Ev _ (restrict (w_H W) ?ms3) |- _ =>
  assert (Hwe : shent_ok tfibsegs CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) (mkSHE 462 0 1))
    by (apply (cw_shent_ra W (ms_mem ms3) Ev 462 (F + 32 + o) 1);
        [ intros x Hx; apply HRAw; lia
        | clear - HFam Ho Hn; unfold amem_range in *; lia
        | lia | lia | lia | exact E462 | exact E32v ]);
  shok_auto_with SHOK CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) [mkSHE 462 0 1] ltac:(exact Hwe) end.
(* 0x8391c-0x83928: the store's instrumented check, paid by that entry *)
cw_run_to ctl_awr 0x8392c.
ctl_wkeep F. ctl_keep F HZfr.
ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
repeat match goal with
| Hu : bv_unsigned (ew _ 38) = _ |- _ => clear Hu
| Hu : bv_unsigned (ew _ 61) = _ |- _ => clear Hu
| Hu : bv_unsigned (ew _ 462) = _ |- _ => clear Hu
end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (U38c : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
  assert (U61c : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
  assert (U462c : bv_unsigned (ew Ev 462) = F + 32 + o) by (rewrite E462; apply unsigned_lit_small; lia) end.
(* the want slot as a one-byte region the walk may write *)
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly4 ?S4 _ ?m4 ?md4 _ |- _ =>
  destruct (al_frames _ _ LAWS ly4 S4 W m4 md4 0 fpos (proj1 HJx) Hfin2) as (_ & _ & HFpres & _) end.
change (fs_frame_bytes 0) with 64 in HFpres. fold F in HFpres.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv (YP09.mkRegion (Some 462%nat) 0 1 0 1 []) HS eq_refl
    ltac:(unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite U462c; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros oo Hoo; apply (apresent_writable tfibsegs);
          exact (proj1 (HFpres (F + 32 + o + oo) ltac:(lia))))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite U462c, U61c, U38c, U33, U2; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
(* 0x8392c sb a5,0(a0): the one byte the turn writes *)
aj_run_to_sh tfibtbl_lib_ok HS HJ 0x83930.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly' own') end.
  eapply (cw_awr_ok_cons_frame_off _ _ _ _ _ _ _ _ _ _ 0 fpos 462%nat (32 + o));
  [reflexivity | rewrite U462c; fold F; lia | left; reflexivity
  | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (fs_frame_bytes 0) with 64; lia |].
  ctl_awr. }
ctl_rebase.
(* the want bytes before the slot are kept, and the slot now holds the turn's byte *)
lazymatch goal with
| HFrw : frame_of ?Ev ?rs (mrestrict ?Hh ?ma) (mrestrict ?Hh ?mb) |- _ =>
  assert (HWp : forall j, 0 <= j < o ->
            aview tfibsegs Hh mb (F + 32 + j) = aview tfibsegs Hh ma (F + 32 + j));
  [ intros j Hj; unfold aview, mbyte;
    rewrite (HFrw (Z_to_bv 64 (F + 32 + j))); [reflexivity|];
    rewrite unsigned_lit_small by lia;
    let rr := fresh "rr" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
    intros (rr & Hin & Hb); cbv beta in Hb;
    lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hin end;
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
       repeat match goal with Hh2 : bv_unsigned (ew _ ?m) = _ |- _ =>
         lazymatch type of Hb with context [bv_unsigned (ew _ m)] => rewrite Hh2 in Hb end end;
       lia |]); destruct Hin
  | ] end.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
  pose proof (cts_chunk1 (w_H W) Ev ssx msx 0%nat
    (YP09.mkRegion (Some 462%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 460 0))]) 0%nat 0 (SOff 460 0) cv HS
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    (ctl_byte_of Ev 460 cv E460 Hcv)) as VST;
  cbn [base_val YP09.r_base] in VST; rewrite U462c, Z.add_0_r in VST end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HWANT2 : YI00.garr8 tfibsegs (mrestrict (w_H W) (ms_mem msx)) (F + 32) (pre ++ [cv]));
  [ intros jj Hjj; rewrite length_app, Hplen in Hjj; cbn [length] in Hjj;
    destruct (Nat.lt_ge_cases jj (Z.to_nat o)) as [Hlt | Hge];
    [ rewrite app_nth1 by lia; destruct (HWANT jj ltac:(lia)) as (Hvv & Hrr); split; [|exact Hrr];
      apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msZ)); [|exact Hvv];
      intros y Hy; rewrite <- (HWK y ltac:(lia));
      replace y with (F + 32 + (y - (F + 32))) by lia; apply HWp; lia
    | replace jj with (Z.to_nat o) by lia; rewrite app_nth2 by lia;
      rewrite Hplen, Nat.sub_diag; cbn [nth]; split; [|exact Hcv];
      replace (F + 32 + Z.of_nat (Z.to_nat o)) with (F + 32 + o) by lia; exact VST ]
  | ] end.
ctl_keep F HZfr.
clear HWANT HWK. rename HWANT2 into HWANT.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HWK : forall a, F + 32 <= a < F + 40 ->
    aview tfibsegs (w_H W) (ms_mem msx) a = aview tfibsegs (w_H W) (ms_mem msx) a) by (intros; reflexivity) end.
(* the want slot's region goes again: the token runs take no open write window *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs' := eval vm_compute in (tl (ss_mem ssx)) in
  let HS1 := fresh "HS1" in
  pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to)
    ltac:(vm_compute; reflexivity)) as HS1;
  clear HS; rename HS1 into HS; norm_ss HS end.
ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
repeat match goal with Hsh : sh_ok _ _ _ _ _ |- _ => clear Hsh end.
lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H W) ?msx) =>
  assert (SHOK : sh_ok tfibsegs CW_Bx [] Ev (mrestrict (w_H W) (ms_mem msx))) by constructor end.
(* 0x83930 add s10,a6,s10: the text bytes used after this turn *)
cw_run_to ctl_awr 0x83934.
ctl_wkeep F. ctl_keep F HZfr. ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (i + 0 + st))
    (ctl_denot_of_U Ev _ _ (ctl_add_off Ev 418 0 461 i st E418 E461
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) R26 end.
replace (i + 0 + st) with (st + i) in R26 by lia.
ctl_pin (26%bv : bv 5) 465%nat.
ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E465 : ew Ev 465 = Z_to_bv 64 (st + i)) by (rewrite ctl_ew_h0; exact R26) end.
(* 0x83934 add a0,s5,s10: the next text byte's address, in atom 463, and its byte in atom 464 *)
set (c3 := nth (Z.to_nat (i + st)) tb 0) in *.
assert (Hqhi : q + (st + i) <= 2 ^ 47 - 2)
  by (clear - Hcam Hilen Hzl Hcq0 Hi Hst C3 C4 C5; unfold amem_range in *; lia).
assert (Hamx : amem_range (q + (st + i)) 1)
  by (clear - Hcam Hilen Hzl Hcq0 Hi Hst; unfold amem_range in *; lia).
ctl_shok0.
cw_run_to ctl_awr 0x83938.
ctl_wkeep F. ctl_keep F HZfr. ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly4 ?S4 _ ?m4 ?md4 _ |- _ =>
  destruct (ctl_text_at B LAWS lyc Sc W memc mdc ly4 S4 m4 md4 (spZ regs) q ch tb (Z.to_nat (i + st))
    HAR (proj1 HJx) ltac:(rewrite Eab; intros bb mm Hb; exact Hb) ltac:(intros cid pos; reflexivity)
    Hstr Hoq Hcham Hch0 Hdisj KT ltac:(lia)) as (HRAq & HVq & Hc38) end.
replace (q + Z.of_nat (Z.to_nat (i + st))) with (q + (st + i)) in HVq by lia.
replace (q + Z.of_nat (Z.to_nat (i + st))) with (q + (st + i)) in HVq by lia.
fold c3 in HVq, Hc38.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E10v : ew Ev 10 = Z_to_bv 64 q)
    by (rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10);
  rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (q + 0 + (st + i)))
    (ctl_denot_of_U Ev _ _ (ctl_add_off Ev 10 0 465 q (st + i) E10v E465
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) R10b end.
replace (q + 0 + (st + i)) with (q + (st + i)) in R10b by lia.
ctl_pin (10%bv : bv 5) 463%nat.
ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E463 : ew Ev 463 = Z_to_bv 64 (q + (st + i))) by (rewrite ctl_ew_h0; exact R10b) end.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 463%nat (mkAF 1 (2 ^ 47 - 2) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E463, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; repeat split; first [lia | apply Z.mod_1_r])) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_havoc_win tfibsegs 464%nat Ev ssx msx [Z_to_bv 64 c3] HS
    ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E464 : ew Ev 464 = Z_to_bv 64 c3) by (rewrite ctl_ew_h0; reflexivity);
  assert (U38d : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
  assert (U61e : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
  assert (E32w : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (Hxoff2 : q + (st + i) + 1 <= F \/ F + 64 <= q + (st + i))
  by (pose proof (Htf (q + (st + i)) ltac:(lia)); lia).
assert (Hxsh2 : q + (st + i) + 1 <= shadow_addr F \/ shadow_addr F + 8 <= q + (st + i))
  by (pose proof (ctl_text_off_fsh (q + (st + i)) F ltac:(lia) HF8m HFam Hamx ltac:(lia)); lia).
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv
    (YP09.mkRegion (Some 463%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 464 0))]) HS eq_refl
    ltac:(unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite E463, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
          split; [intros oo Hoo; lia|];
          apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val tfibsegs Ev _ (q + (st + i)) 0 1 (SOff 464 0) c3);
          [rewrite sv_denot_SOff0, E464; reflexivity | cbn; lia | cbn; lia |];
          rewrite Z.add_0_r; exact (AE36.val_mem1_of_aview (w_H W) _ _ _ HVq))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite E463, unsigned_lit_small by lia;
          rewrite U61e, U38d, U33, U2; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
repeat match goal with Hsh : sh_ok _ _ _ _ _ |- _ => clear Hsh end.
lazymatch goal with HSx : st_ok _ ?Ev _ (restrict (w_H W) ?ms3) |- _ =>
  assert (Hte : shent_ok tfibsegs CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) (mkSHE 463 0 1))
    by (apply (cw_shent_ra W (ms_mem ms3) Ev 463 (q + (st + i)) 1);
        [ intros x Hx; apply HRAq; lia | exact Hamx | lia | lia | lia | exact E463 | exact E32w ]);
  shok_auto_with SHOK CW_Bx Ev (mrestrict (w_H W) (ms_mem ms3)) [mkSHE 463 0 1] ltac:(exact Hte) end.
(* 0x83938-0x8394c: the next byte's check, its load and the slot count; stop at 0x83950 beqz a5 *)
cw_run ctl_awr.
ctl_wkeep F. ctl_keep F HZfr. ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
(* the text byte's region goes, the flag byte's region comes back, and the turn's slot count, text
   index and text byte go into the atoms 417, 418 and 419 *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs' := eval vm_compute in (tl (ss_mem ssx)) in
  let HS1 := fresh "HS1" in
  pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to)
    ltac:(vm_compute; reflexivity)) as HS1;
  clear HS; rename HS1 into HS; norm_ss HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (U60f : bv_unsigned (ew Ev 60) = ctl_FLu lyc fpos) by (rewrite E60; reflexivity);
  assert (U38e : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
  assert (U61f : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia) end.
pose proof HFLD as HFLD2. destruct HFLD2 as (FD1 & FD2 & FD3 & FD4).
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv (YP09.mkRegion (Some 60%nat) 0 1 0 0 []) HS eq_refl
    ltac:(unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite U60f; split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia | apply Forall_nil])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite U60f, U61f, U38e, U33, U2; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx cts_rec_atoms [] [] HS
    ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (o + 1))
    (ctl_denot_of_U Ev _ _ (U_atom_off Ev 417 o 1 E417 ltac:(lia) ltac:(lia))) R11;
  rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (st + i))
    (ctl_denot_of_U Ev _ _ (U_atom Ev 465 (st + i) E465 ltac:(lia))) R26b;
  rreg_by HS (15%bv : bv 5) (Z_to_bv 64 c3)
    (ctl_denot_of_U Ev _ _ (ctl_zext8 Ev 464 c3 E464 Hc38)) R15 end.
ctl_lit (11%bv : bv 5).
ctl_lit (15%bv : bv 5).
ctl_pin (11%bv : bv 5) 417%nat.
ctl_pin (26%bv : bv 5) 418%nat.
ctl_pin (15%bv : bv 5) 419%nat.
ctl_rebase.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E417n : ew Ev 417 = Z_to_bv 64 (o + 1))
    by (repeat first [ solve [rewrite ctl_ew_h0; exact R11] | rewrite ew_havoc_old by (cbn; lia) ];
        rewrite ctl_ew_h0; exact R11);
  assert (E418n : ew Ev 418 = Z_to_bv 64 (st + i))
    by (repeat first [ solve [rewrite ctl_ew_h0; exact R26b] | rewrite ew_havoc_old by (cbn; lia) ];
        rewrite ctl_ew_h0; exact R26b);
  assert (E419n : ew Ev 419 = Z_to_bv 64 c3)
    by (repeat first [ solve [rewrite ctl_ew_h0; exact R15] | rewrite ew_havoc_old by (cbn; lia) ];
        rewrite ctl_ew_h0; exact R15) end.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 417%nat (mkAF 0 8 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E417n, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; repeat split; first [lia | apply Z.mod_1_r])) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 419%nat (mkAF 0 255 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E419n, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; repeat split; first [lia | apply Z.mod_1_r])) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
ctl_shok0. ctl_ufacts SP1 (spZ regs) E33 AG B2.
(* 0x83950 beqz a5: the next text byte decides *)
cw_run ctl_awr.
ctl_wkeep F. ctl_keep F HZfr. ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
cw_branch Hz.
all: rewrite branch_eq_U in Hz.
all: lazymatch type of Hz with context [U ?Ecur (SOff 419 0)] =>
     let Hx := fresh "Hx" in
     assert (Hx : ew Ecur 419 = Z_to_bv 64 c3)
       by (repeat first [ solve [exact E419n]
                        | rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia) ]; exact E419n);
     rewrite (U_atom Ecur 419 c3 Hx ltac:(lia)) in Hz;
     rewrite (U_lit Ecur 0 ltac:(lia)) in Hz; clear Hx end.
- (* the text is done: the pad of want takes over *)
  assert (Hz0e : c3 = 0) by (apply Z.eqb_eq in Hz; exact Hz).
  assert (Hiend : i + st = Z.of_nat (length (cts_cstr tb))).
  { destruct (Z_lt_le_dec (i + st) (Z.of_nat (length (cts_cstr tb)))) as [Hh|Hh]; [exfalso | lia].
    apply (Hnz (Z.to_nat (i + st)) ltac:(lia)). exact Hz0e. }
  cw_run_to ctl_awr 0x83984.
  ctl_wkeep F. ctl_keep F HZfr.
  cw_join_win HS cts_ss_pad 420%nat cts_deadP_bv ltac:(idtac).
  ctl_rebase.
  destruct (cts_model_end tb (Z.to_nat n) (o + 1) (i + st) (pre ++ [cv]) Hin0 HMOD
              ltac:(lia) ltac:(lia) ltac:(right; lia)) as (HMf & HMs).
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      eapply (PAD Ev msx mdx (o + 1) (i + st) (pre ++ [cv])) end end.
  1: exact HS.
  1: constructor.
  1: exact AG. 1: exact E33. 1: exact E38. 1: exact E60. 1: exact E61.
  1: exact E417n. 1: (replace (i + st) with (st + i) by lia; exact E418n).
  1: eassumption. 1: exact KT. 1: (eapply same_io_trans; [exact HIO | cpw_io]).
  1: lia. 1: lia. 1: (rewrite length_app, Hplen; cbn [length]; lia).
  1: exact HMf. 1: exact HMs.
  1: (intros jj Hjj; destruct (HWANT jj Hjj) as (Hvv & Hrr); split; [|exact Hrr];
        lazymatch type of HWK with forall a, _ -> aview _ _ _ a = aview _ _ ?m0 a =>
          apply (cw_val_mem_kept (w_H W) (w_H W) m0) end; [| exact Hvv];
        intros y Hy; apply HWK; rewrite length_app, Hplen in Hjj; cbn [length] in Hjj; fold F; lia).
- (* the text goes on: the slot count decides *)
  assert (Hz0e : c3 <> 0) by (apply Z.eqb_neq in Hz; exact Hz).
  assert (Hilt2 : i + st < Z.of_nat (length (cts_cstr tb))).
  { destruct (Z_lt_le_dec (i + st) (Z.of_nat (length (cts_cstr tb)))) as [Hh|Hh]; [exact Hh | exfalso].
    apply Hz0e. change c3 with (nth (Z.to_nat (i + st)) tb 0).
    replace (Z.to_nat (i + st)) with (length (cts_cstr tb)) by lia. exact Hz0. }
  cw_run ctl_awr.
  ctl_wkeep F. ctl_keep F HZfr. ctl_rebase. ctl_ufacts SP1 (spZ regs) E33 AG B2.
  cw_branch Hb2.
  all: rewrite branch_geu_U in Hb2.
  all: lazymatch type of Hb2 with context [U ?Ecur (SOff 417 0)] =>
       let Hx := fresh "Hx" in let Hy := fresh "Hy" in
       assert (Hx : ew Ecur 417 = Z_to_bv 64 (o + 1))
         by (repeat first [ solve [exact E417n]
                          | rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia) ]; exact E417n);
       assert (Hy : ew Ecur 12 = Z_to_bv 64 n)
         by (rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12);
       rewrite (U_atom Ecur 417 (o + 1) Hx ltac:(lia)) in Hb2;
       rewrite (U_atom Ecur 12 n Hy ltac:(lia)) in Hb2; clear Hx Hy end.
  + (* the slots are full: the pad of want takes over *)
    assert (Hoend : o + 1 = n) by (apply negb_true_iff, Z.ltb_ge in Hb2; lia).
    cw_run_to ctl_awr 0x83984.
    ctl_wkeep F. ctl_keep F HZfr.
    cw_join_win HS cts_ss_pad 420%nat cts_deadP_bv ltac:(idtac).
    ctl_rebase.
    destruct (cts_model_end tb (Z.to_nat n) (o + 1) (i + st) (pre ++ [cv]) Hin0 HMOD
                ltac:(lia) ltac:(lia) ltac:(left; lia)) as (HMf & HMs).
    lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        eapply (PAD Ev msx mdx (o + 1) (i + st) (pre ++ [cv])) end end.
    1: exact HS.
    1: constructor.
    1: exact AG. 1: exact E33. 1: exact E38. 1: exact E60. 1: exact E61.
    1: exact E417n. 1: (replace (i + st) with (st + i) by lia; exact E418n).
    1: eassumption. 1: exact KT. 1: (eapply same_io_trans; [exact HIO | cpw_io]).
    1: lia. 1: lia. 1: (rewrite length_app, Hplen; cbn [length]; lia).
    1: exact HMf. 1: exact HMs.
    1: (intros jj Hjj; destruct (HWANT jj Hjj) as (Hvv & Hrr); split; [|exact Hrr];
        lazymatch type of HWK with forall a, _ -> aview _ _ _ a = aview _ _ ?m0 a =>
          apply (cw_val_mem_kept (w_H W) (w_H W) m0) end; [| exact Hvv];
        intros y Hy; apply HWK; rewrite length_app, Hplen in Hjj; cbn [length] in Hjj; fold F; lia).
  + (* another slot and another text byte: the loop head again *)
    assert (Holt : o + 1 < n) by (apply negb_false_iff, Z.ltb_lt in Hb2; lia).
    cw_run_to ctl_awr 0x838d0.
    ctl_wkeep F. ctl_keep F HZfr.
    cw_join_win HS cts_ss_lp 440%nat cts_deadL_bv ltac:(idtac).
    ctl_rebase.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        eapply (HEAD Ev msx mdx (o + 1) (i + st) (pre ++ [cv])) end end.
    1: exact HS.
    1: (red; split; [exact AG|]; split; [exact E33|]; split; [exact E38|]; split; [exact E60|];
        split; [exact E61|]; split; [eassumption|];
        split; [exact KT | eapply same_io_trans; [exact HIO | cpw_io]]).
    1: exact E417n. 1: (replace (i + st) with (st + i) by lia; exact E418n). 1: exact E419n.
    1: lia. 1: lia. 1: lia. 1: (rewrite length_app, Hplen; cbn [length]; lia). 1: exact HMOD.
    1: (intros jj Hjj; destruct (HWANT jj Hjj) as (Hvv & Hrr); split; [|exact Hrr];
        lazymatch type of HWK with forall a, _ -> aview _ _ _ a = aview _ _ ?m0 a =>
          apply (cw_val_mem_kept (w_H W) (w_H W) m0) end; [| exact Hvv];
        intros y Hy; apply HWK; rewrite length_app, Hplen in Hjj; cbn [length] in Hjj; fold F; lia).
Qed.
End d.
End b.
