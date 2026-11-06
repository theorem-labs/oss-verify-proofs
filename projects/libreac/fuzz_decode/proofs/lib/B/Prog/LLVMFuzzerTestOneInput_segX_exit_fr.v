(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_exit_fr: the two frees of image B's LLVMFuzzerTestOneInput exit group, from +0xab8 to
   +0xac8 (the re-poison after them is segX_exit_rp.v):
     +0xab8 mv a0, s7; +0xabc jal free          free #2: the upstream buffer
     +0xac0 mv a0, s11; +0xac4 jal free         free #3: the payload copy
   Each free is a two-instruction symbolic run to the call (the Pa engine's PTS_call), the statement's
   afree04_rule (lib/Reusable/YC5d.v:76) at the listing's trampoline, and the frame invariant carried across the
   call (ex_core_kept / ex_acall_keep of segX_exit_defs.v); the form is cgif's call stages (proofs/cgif/
   cgif_file_fuzzer/lib/A/ACf2.v rt_C_aux's free, ACf1.v rt_Bend_aux's call sites) and boxreg's ReadName.v call
   idiom (a working branch lib/A/Prog/ReadName.v:841-935). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa
  DecodeBPaLib DecodeBImg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_exit_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the
   plain ones (YM03.v:179-180 lf_lia_orig / lf_nia_orig). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Open Scope Z_scope.

Section fr. Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation base cx :=
  (@dec_b_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx).

Lemma fr_base_eq : decodeb_val A_TEXT = DEC_A_LLVMF.
Proof. vm_compute. reflexivity. Qed.

Section f. Context {fx : YK11.FPState}.

Ltac fr_rg HS r :=
  lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict ?H ?msx) =>
    rewrite (st_ok_restrict_reg sg H Ex ssx msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e end.

(* The free itself, at the trampoline: afree04_rule, then the frame invariant and the cut-point facts carried
   across the call (ex_acall_keep, ex_core_kept). *)
Lemma fr_free_call :
  pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free ->
  dec_llvmf_utraces RA_LLVMF B -> AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc dec_B_sink_head segs B MT) ->
  forall X (cx : dctx) (W : world segs) regs regsT mem md ly S k bl pa n spent rest (R : bvmap 5 word -> Prop),
  X = 0xab8 \/ X = 0xac0 ->
  base cx ->
  dec_b_core B cx ly S W regs mem md k -> 0 <= k <= 17 ->
  Permutation (ablocks B ly S) (ablocks B (d_ly cx) (d_S cx) ++ bl ++ [(pa, n)]) ->
  mo_le MT (d_S cx) S spent -> 0 <= rest -> mo_ok MT S (mo_free MT + rest) ->
  dec_b_frs cx (aview segs (w_H W) mem) -> dec_b_fsh cx (aview segs (w_H W) mem) 0 4 ->
  R regs -> (forall r r', R r -> aregs_preserved r r' -> R r') ->
  aregs_preserved regs regsT -> YK11.getr regsT 10 = w64 pa ->
  YK11.getr regsT 1 = w64 (DEC_A_LLVMF + (X + 8)) ->
  frm_zero (@fp_csr fx) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) mem (YK11.seg_rom segs)) md)
    (ex_fr B MT (X + 8) (k + 1) bl (spent + mo_free MT) rest R cx).
Proof.
intros HPCF HUTR LAWS MTL AFREE X cx W regs regsT mem md ly S k bl pa n spent rest R HX HB Hcore Hk Hperm Hmle
  Hrest Hmok Hfrs Hfsh HR HRp HP0 Ra0 Rra Hfz.
pose proof decodeb_segs_low as Hsegs.
destruct (ex_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx HB)
  as (Hret0 & Hra0 & Hgp0 & Htp0 & Hstk0 & Hch0 & Hpn & Hnlen & Hfr0 & Hnev0 & Hlive0 & _ & _ & _ & Hra40).
pose proof Hcore as (HJ & Hfrm & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnevk & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk00 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
assert (SHV : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (EB : DEC_A_LLVMF = 524464) by reflexivity.
pose proof (ex_achain B cx ly S W regs mem md k Hch0 Hstk0 Hra40 Hcore) as Hach.
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrm; left; reflexivity).
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
assert (Hinb : In (pa, n) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; right. left; reflexivity. }
assert (Hnb : ~ In (pa, n) (ablocks B (d_ly cx) (d_S cx))).
{ intros Hb. apply (ex_perm_twice B LAWS ly S W mem md (ablocks B (d_ly cx) (d_S cx)) (bl ++ [(pa, n)]) (pa, n) HAR Hperm Hb).
  apply in_or_app; right; left; reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ pa n HAR Hinb) as (_ & Hb4096 & Hbceil & Hbapp & _).
assert (Rg : forall r, acallee_saved r -> YK11.getr regsT (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) by exact HP0.
assert (Rg2 : YK11.getr regsT 2 = YK11.getr regs 2) by exact (Rg 2 ltac:(unfold acallee_saved; lia)).
assert (Rg3 : YK11.getr regsT 3 = YK11.getr regs 3) by exact (Rg 3 ltac:(unfold acallee_saved; lia)).
assert (Rg4 : YK11.getr regsT 4 = YK11.getr regs 4) by exact (Rg 4 ltac:(unfold acallee_saved; lia)).
assert (Rg8 : YK11.getr regsT 8 = YK11.getr regs 8) by exact (Rg 8 ltac:(unfold acallee_saved; lia)).
assert (Rg9 : YK11.getr regsT 9 = YK11.getr regs 9) by exact (Rg 9 ltac:(unfold acallee_saved; lia)).
assert (Rsp : spZ regsT = d_sp1 cx) by (unfold spZ in *; rewrite <- Hsp, Rg2; reflexivity).
assert (Rs0 : s0Z regsT = d_sp0 cx).
{ unfold s0Z. rewrite Rg8, Hs0. unfold w64. apply unsigned_lit_small. lia. }
assert (Rraz : raZ regsT = DEC_A_LLVMF + (X + 8)).
{ unfold raZ. rewrite Rra. unfold w64. apply unsigned_lit_small. destruct HX as [-> | ->]; rewrite EB; lia. }
eapply SRr_bind.
{ eapply (AFREE fx W regsT mem DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S md k pa n (d_sp1 cx - d_sp0 cx) (YK11.getr regsT 1) (ex_ch cx) HJ Hinb Ra0).
  - lia.
  - rewrite Z.mod_divide in Hsp0al, Hsp1al by lia. rewrite Z.mod_divide by lia.
    destruct Hsp0al as [q0 Hq0]. destruct Hsp1al as [q1 Hq1]. exists (2 * q1 - q0). lia.
  - lia.
  - unfold ASTACK. lia.
  - rewrite Rg3. exact Hgp.
  - rewrite Rg4. exact Htp.
  - reflexivity.
  - rewrite Rra. unfold w64. rewrite <- fr_base_eq.
    apply (ret_ok_codeptr_v (PI := PI_decodeb)); destruct HX as [-> | ->]; first [lia | reflexivity].
  - unfold DEC_EV_LIB in Hnev0. lia.
  - apply (achain_chain_pre ly _ (d_sp1 cx) (d_sp0 cx) (ex_ch cx) regsT Hach); [lia | exact Rs0 | rewrite Rraz; destruct HX as [-> | ->]; lia].
  - rewrite call_trace_of_spine. unfold ex_ch.
    assert (HinR : In (raZ regsT) DEC_LLVMF_RA_FREE).
    { rewrite Rraz. unfold DEC_LLVMF_RA_FREE. cbn [map In]. destruct HX as [-> | ->]; [right; left | right; right; left]; reflexivity. }
    destruct (Z.ltb_spec (d_sp0 cx + 16) (ly_top (d_ly cx))); cbn [spine map fst snd].
    + destruct (HUTR [RA_LLVMF] ltac:(right; left; reflexivity)) as [_ HF2].
      pose proof (HF2 _ HinR) as HT. unfold dec_utrace in HT. rewrite Hra0. exact HT.
    + destruct (HUTR [] ltac:(left; reflexivity)) as [_ HF2].
      pose proof (HF2 _ HinR) as HT. unfold dec_utrace in HT. exact HT.
  - intros Hb. exfalso. exact (Hnb Hb).
  - apply (mo_ok_le MT MTL S (mo_free MT) (mo_free MT + rest) Hmok). lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & (l1 & l2 & Hbl1 & Hbl2) & Hfr2 & HK & Hmle2).
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx)) with (d_sp1 cx) in HK by lia.
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HnF : forall a, d_F cx <= a < d_F cx + 64 -> ~ (pa <= a < pa + req_size n)).
{ pose proof (sep_block_frame segs B LAWS ly S W mem md pa n DEC_FCLASS (d_fpos cx) HAR Hinb Hin0) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes DEC_FCLASS) with 64 in Hd. lia. }
assert (HnS : forall a, d_SH cx <= a < d_SH cx + 8 -> ~ (pa <= a < pa + req_size n)).
{ intros a Ha Hpa. unfold d_SH, shadow_addr in Ha.
  pose proof (Z.div_pos (d_F cx) 8 ltac:(lia) ltac:(lia)).
  destruct (frames_bounds segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (_ & Hfb & _).
  rewrite EFA in Hfb. change (fs_frame_bytes DEC_FCLASS) with 64 in Hfb.
  assert (d_F cx / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. rewrite SHV in Ha. cbn in *. lia. }
destruct (ex_acall_keep B LAWS cx ly S W regs mem md k W2 mem2 _ _ _ Hcore HK ltac:(lia) HnF HnS) as (Ksp & KF & KS).
assert (Hne : forall x, In x (ablocks B (d_ly cx) (d_S cx)) -> x <> (pa, n)) by (intros x Hx ->; exact (Hnb Hx)).
assert (HP2 : YK11.getr regs2 2 = YK11.getr regsT 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (HP3 : YK11.getr regs2 3 = YK11.getr regsT 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (HP4 : YK11.getr regs2 4 = YK11.getr regsT 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (HP8 : YK11.getr regs2 8 = YK11.getr regsT 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (HP9 : YK11.getr regs2 9 = YK11.getr regsT 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
apply SRr_ret. unfold ex_fr. cbv beta. exists fx, ly2, S2, regs2, mem2, md2.
split. { rewrite Rra. reflexivity. }
split; [exact Hfz|].
split.
{ apply (ex_core_kept B cx ly S W regs mem md k ly2 S2 W2 regs2 mem2 md2 (k + 1) Hcore HJ2).
  - rewrite Hfr2. exact Hfrm.
  - rewrite HP8. exact Rg8.
  - rewrite HP9. exact Rg9.
  - unfold spZ. rewrite HP2, Rg2. reflexivity.
  - rewrite HP3. exact Rg3.
  - rewrite HP4. exact Rg4.
  - intros a Ha. apply Ksp. lia.
  - intros a Ha. exact (proj1 (KF a Ha)).
  - intros a Ha. exact (proj2 (KF a Ha)).
  - intros Hn0. pose proof (Hpay Hn0) as Hp. rewrite Hbl1 in Hp. rewrite Hbl2.
    destruct Hpn as [[Hn00 _] | [_ Hinp]]; [lia|].
    apply in_app_or in Hp as [Hp | [Hp | Hp]]; [apply in_or_app; left; exact Hp | | apply in_or_app; right; exact Hp].
    exfalso. exact (Hne _ Hinp (eq_sym Hp)).
  - intros i Hi. rewrite <- Hnlen in Hi.
    destruct Hpn as [[Hn00 _] | [Hnpos Hinp]]; [lia|].
    pose proof (Hpay (proj1 Hnpos)) as Hp.
    pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrq.
    apply (K2 (d_p cx) (d_n cx) i Hp ltac:(lia)).
    pose proof (sep_blocks segs B LAWS ly S W mem md (d_p cx) (d_n cx) pa n HAR Hp Hinb (Hne _ Hinp)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split.
{ rewrite Hbl2.
  assert (P1 : Permutation (l1 ++ (pa, n) :: l2) ((ablocks B (d_ly cx) (d_S cx) ++ bl) ++ (pa, n) :: [])).
  { rewrite <- Hbl1, <- app_assoc. exact Hperm. }
  pose proof (Permutation_app_inv _ _ _ _ _ P1) as P2. rewrite app_nil_r in P2. exact P2. }
split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmle Hmle2)|].
split; [exact (mo_ok_step MT MTL S S2 (mo_free MT) rest Hmok Hmle2)|].
split.
{ unfold dec_b_frs, dec_b_slot in *. destruct Hfrs as (Q0 & Q8 & Q16).
  split; [|split]; [rewrite <- Q0 | rewrite <- Q8 | rewrite <- Q16]; apply rdword_ext; intros j Hj; apply Ksp; lia. }
split.
{ unfold dec_b_fsh in *. destruct Hfsh as (L0 & L4 & L5 & L6).
  split; [intros i Hi; rewrite KS by lia; exact (L0 i Hi)|].
  split; [rewrite KS by lia; exact L4|]. split; [rewrite KS by lia; exact L5|].
  intros i Hi; rewrite KS by lia; exact (L6 i Hi). }
exact (HRp regsT regs2 (HRp regs regsT HR HP0) HP).
Qed.

(* One free of the group: `mv a0, sN; jal free` at DEC_A_LLVMF + X, for (X, N) = (0xab8, s7) or (0xac0, s11). *)
Lemma fr_free_at :
  pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free ->
  dec_llvmf_utraces RA_LLVMF B -> AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc dec_B_sink_head segs B MT) ->
  forall X N (cx : dctx) (W : world segs) regs mem md ly S k bl pa n spent rest (R : bvmap 5 word -> Prop),
  (X = 0xab8 /\ N = 23) \/ (X = 0xac0 /\ N = 27) ->
  base cx ->
  dec_b_core B cx ly S W regs mem md k -> 0 <= k <= 17 ->
  Permutation (ablocks B ly S) (ablocks B (d_ly cx) (d_S cx) ++ bl ++ [(pa, n)]) ->
  mo_le MT (d_S cx) S spent -> 0 <= rest -> mo_ok MT S (mo_free MT + rest) ->
  dec_b_frs cx (aview segs (w_H W) mem) -> dec_b_fsh cx (aview segs (w_H W) mem) 0 4 ->
  R regs -> (forall r, R r -> YK11.getr r (Z_to_bv 5 N) = w64 pa) ->
  (forall r r', R r -> aregs_preserved r r' -> R r') ->
  frm_zero (@fp_csr fx) ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (DEC_A_LLVMF + X)) mem (YK11.seg_rom segs)) md)
    (ex_fr B MT (X + 8) (k + 1) bl (spent + mo_free MT) rest R cx).
Proof.
intros HPCF HUTR LAWS MTL AFREE X N cx W regs mem md ly S k bl pa n spent rest R HXN HB Hcore Hk Hperm Hmle Hrest
  Hmok Hfrs Hfsh HR HRa0 HRp Hfz.
pose proof decodeb_segs_low as Hsegs. pose proof decodeb_wx as Hwx.
destruct (ex_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx HB)
  as (Hret0 & Hra0 & Hgp0 & Htp0 & Hstk0 & Hch0 & Hpn & Hnlen & Hfr0 & Hnev0 & Hlive0 & _ & _ & _ & Hra40).
pose proof Hcore as (HJ & Hfrm & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnevk & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk00 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
pose proof (ex_achain B cx ly S W regs mem md k Hch0 Hstk0 Hra40 Hcore) as Hach.
set (E := Eimg (Ereg regs [])).
assert (HS : st_ok_pi segs decodeb_val E (mkSS X sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (decodeb_val A_TEXT + X)) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (PI := PI_decodeb)).
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok segs (SOff 18 0) [] E (mrestrict (w_H W) mem)) by constructor.
assert (HEI : img_env decodeb_val A_LIM E) by (exact (Eimg_env (PI := PI_decodeb) (Ereg regs []))).
pose proof (paj_run (SK := dec_B_sink_head) (PI := PI_decodeb) B LAWS) as RUN.
change (w64 (DEC_A_LLVMF + X)) with (Z_to_bv 64 (DEC_A_LLVMF + X)). rewrite <- fr_base_eq.
destruct HXN as [[-> ->] | [-> ->]].
all: paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
(* back at the call: memory untouched (no region), callee-saved registers the entry's, a0 = the block, ra *)
all: assert (Emem : ms_mem ms = mem)
       by (apply functional_extensionality; intros x; apply HF; intros (r & Hr & _); destruct Hr).
all: rewrite Emem in HJ.
all: pose proof (ex_core_md B cx ly S W regs mem md k mem _ Hcore HJ eq_refl) as Hcore'.
all: pmkst HS.
all: rewrite Emem.
all: change (pa_sigma DB___interceptor_trampoline_free) with (decodeb_sigma DB___interceptor_trampoline_free).
all: rewrite <- HPCF.
all: lazymatch goal with |- context [ex_fr _ _ (?x + 8)] =>
       apply (fr_free_call HPCF HUTR LAWS MTL AFREE x cx W regs (ms_regs ms) mem _ ly S k bl pa n spent rest R
         ltac:(lia) HB Hcore' Hk Hperm Hmle Hrest Hmok Hfrs Hfsh HR HRp) end.
all: try exact Hfz.
all: try (apply (aregs_preserved_of_st_ok segs (w_H W) E _ ms regs [] HS);
       [ split; [intros nn Hnn; cbv delta [E]; symmetry; apply Eimg_low; unfold A_TEXT; lia | reflexivity]
       | vm_compute; reflexivity ]).
all: try (fr_rg HS (10%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r; cbv delta [E];
       rewrite Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_lt by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
       rewrite Z_to_bv_bv_unsigned; apply HRa0; exact HR).
all: try (fr_rg HS (1%bv : bv 5); rewrite (codeptr_val (PI := PI_decodeb) E _ HEI); unfold w64; rewrite fr_base_eq;
       reflexivity).
all: lazymatch goal with
  | |- aregs_preserved _ _ =>
    apply (aregs_preserved_of_st_ok segs (w_H W) E _ ms regs [] HS);
       [ split; [intros nn Hnn; cbv delta [E]; apply Eimg_low; unfold A_TEXT; lia | reflexivity]
       | vm_compute; reflexivity ]
  | |- _ => fr_rg HS (1%bv : bv 5); rewrite (codeptr_val (PI := PI_decodeb) E _ HEI); unfold w64; f_equal; vm_compute;
       reflexivity
  end.
Qed.
End f.
End fr.
