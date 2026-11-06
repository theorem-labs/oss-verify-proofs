(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_cmp_tail: the end of image B's LLVMFuzzerTestOneInput cmp segment (llvm_b_cmp_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), from the call of free #1 to llvm_b_st_840:
     +0x830 ld a0, 88(s1); +0x834 jal free           free #1: the decode buffer (both paths reach +0x830)
     +0x838 mv a0, s6;     +0x83c jal reac_upstream_channels
   The free is the statement's afree04_rule (lib/Reusable/YC5d.v:76) at the listing's trampoline, as the exit group's
   fr_free_call (lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_fr.v, working copy) applies it; the leaf is the
   statement's dec_leaf_at reac_upstream_channels through a Theorem Labs lane's per-leaf instance
   dec_leafb_upstream_channels (lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v, a14 727ce5de258), whose read-only
   multiplier is dec_crt_cells' own row; the two instructions between them are a Pa run to the leaf's PTS_call
   (exit_fr's fr_free_at form). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs reac_upstream_channels_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_cmp_defs
  LLVMFuzzerTestOneInput_segX_cmp_kit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_upstream_channels_cg LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_leafb.
Import ListNotations.
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_channels_cg.

Section t. Context {rc : YM05.RunCeil}.
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

Lemma cm_base_eq : decodeb_val A_TEXT = DEC_A_LLVMF.
Proof. vm_compute. reflexivity. Qed.

Section f. Context {fx : YK11.FPState}.

Ltac cm_rg HS r :=
  lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict ?H ?msx) =>
    rewrite (st_ok_restrict_reg sg H Ex ssx msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e end.

(* +0x834 .. +0x840: free #1, the two-instruction run to the leaf, and reac_upstream_channels. *)
Lemma cm_tail :
  pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free ->
  dec_llvmf_utraces RA_LLVMF B -> dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc dec_B_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LUpChannels.dec_reac_upstream_channels_cg) fx') ->
  forall (cx : dctx) (W : world segs) ly S regs mem md out res mode nch ns,
  base cx -> rom_view segs (d_W cx) (d_mem cx) -> frm_zero (@fp_csr fx) ->
  dec_b_core B cx ly S W regs mem md dec_ev_6f0 ->
  Permutation (ablocks B ly S) (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++
                                [(out, dec_b_olen nch ns)]) ->
  4096 <= res ->
  mo_le MT (d_S cx) S (dec_spent_6f0 MT (d_n cx)) -> mo_ok MT S (dec_rest_6f0 MT) ->
  cm_mem cx out res mode nch ns W mem ->
  YK11.getr regs 10 = w64 out -> YK11.getr regs 1 = w64 (DEC_A_LLVMF + 0x838) ->
  YK11.getr regs 22 = w64 (dec_b_len (d_n cx)) -> YK11.getr regs 27 = w64 res ->
  SRr segs W (mkCfg (YK11.mkst regs (Z_to_bv 64 (pc_wrap_free (as_code B))) mem (YK11.seg_rom segs)) md)
    (llvm_b_st_840 B MT cx).
Proof.
intros HPCF HUTR HCELLS HROS HRNE LAWS MTL AFREE LUC cx W ly S regs mem md out res mode nch ns HB HROMcx Hfz Hcore
  Hperm Hres4 Hmle Hmok HMEM Ra0 Rra R22 R27.
pose proof decodeb_segs_low as Hsegs. pose proof decodeb_wx as Hwx.
destruct (cm_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx HB)
  as (Hret0 & Hra0 & Hgp0 & Htp0 & Hstk0 & Hch0 & Hpn & Hnlen & Hfr0 & Hnev0 & Hlive0 & Hra40).
pose proof Hcore as (HJ & Hfrm & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnevk & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk00 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
assert (SHV : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (EB : DEC_A_LLVMF = 524464) by reflexivity.
set (len := dec_b_len (d_n cx)) in *.
set (olen := dec_b_olen nch ns) in *.
assert (Hlen : 0 <= len < 67108864).
{ unfold len, dec_b_len. destruct Hpn as [[-> _] | [Hn _]]; lia. }
pose proof (cm_achain B cx ly S W regs mem md dec_ev_6f0 Hch0 Hstk0 Hra40 Hcore) as Hach.
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrm; left; reflexivity).
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
assert (Hinb : In (out, olen) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; right. left; reflexivity. }
assert (Hinr : In (res, len) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; left. left; reflexivity. }
assert (Hnb : ~ In (out, olen) (ablocks B (d_ly cx) (d_S cx))).
{ intros Hb. apply (cm_perm_twice B LAWS ly S W mem md (ablocks B (d_ly cx) (d_S cx)) ([(res, len)] ++ [(out, olen)])
    (out, olen) HAR Hperm Hb).
  apply in_or_app; right; left; reflexivity. }
assert (Hro : (res, len) <> (out, olen)).
{ intros Heq. apply (cm_perm_twice B LAWS ly S W mem md ((ablocks B (d_ly cx) (d_S cx)) ++ [(res, len)]) [(out, olen)]
    (out, olen) HAR ltac:(rewrite <- app_assoc; exact Hperm)); [|left; reflexivity].
  apply in_or_app; right; left; exact Heq. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hinb) as (_ & Hb4096 & Hbceil & Hbapp & _).
assert (Rsp : spZ regs = d_sp1 cx) by exact Hsp.
assert (Rs0 : s0Z regs = d_sp0 cx).
{ unfold s0Z. rewrite Hs0. unfold w64. apply unsigned_lit_small. lia. }
assert (Rraz : raZ regs = DEC_A_LLVMF + 0x838).
{ unfold raZ. rewrite Rra. unfold w64. apply unsigned_lit_small. rewrite EB. lia. }
(* ---- free #1 ---- *)
eapply SRr_bind.
{ eapply (AFREE fx W regs mem DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S md dec_ev_6f0 out olen (d_sp1 cx - d_sp0 cx) (YK11.getr regs 1) (cm_ch cx)
    HJ Hinb Ra0).
  - lia.
  - rewrite Z.mod_divide in Hsp0al, Hsp1al by lia. rewrite Z.mod_divide by lia.
    destruct Hsp0al as [q0 Hq0]. destruct Hsp1al as [q1 Hq1]. exists (2 * q1 - q0). lia.
  - lia.
  - unfold ASTACK. lia.
  - exact Hgp.
  - exact Htp.
  - reflexivity.
  - rewrite Rra. unfold w64. rewrite <- cm_base_eq.
    apply (ret_ok_codeptr_v (PI := PI_decodeb)); first [lia | reflexivity].
  - unfold DEC_EV_LIB, dec_ev_6f0 in *. lia.
  - apply (achain_chain_pre ly _ (d_sp1 cx) (d_sp0 cx) (cm_ch cx) regs Hach); [lia | exact Rs0 | rewrite Rraz; lia].
  - apply (cm_trace_in RA_LLVMF cx regs (pc_free_ra0 (as_code B)) (as_universe B) (DEC_A_LLVMF + 0x838) Hra0 Rraz).
    intros sp Hsp'. destruct (HUTR sp Hsp') as [_ HF2]. apply HF2.
    unfold DEC_LLVMF_RA_FREE. cbn [map In]. left; reflexivity.
  - intros Hb. exfalso. exact (Hnb Hb).
  - apply (mo_ok_le MT MTL S (mo_free MT) (dec_rest_6f0 MT) Hmok). unfold dec_rest_6f0.
    pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(lia)). pose proof (mo_free_nonneg MT MTL).
    unfold dec_rest_840, dec_rest_96c, dec_crt_cost_max. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & (l1 & l2 & Hbl1 & Hbl2) & Hfr2 & HK & Hmle2).
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx)) with (d_sp1 cx) in HK by lia.
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HnF : forall a, d_F cx <= a < d_F cx + 64 -> ~ (out <= a < out + req_size olen)).
{ pose proof (sep_block_frame segs B LAWS ly S W mem md out olen DEC_FCLASS (d_fpos cx) HAR Hinb Hin0) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes DEC_FCLASS) with 64 in Hd. lia. }
assert (HnS : forall a, d_SH cx <= a < d_SH cx + 8 -> ~ (out <= a < out + req_size olen)).
{ intros a Ha Hpa. unfold d_SH, shadow_addr in Ha.
  pose proof (Z.div_pos (d_F cx) 8 ltac:(lia) ltac:(lia)).
  destruct (frames_bounds segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (_ & Hfb & _).
  rewrite EFA in Hfb. change (fs_frame_bytes DEC_FCLASS) with 64 in Hfb.
  assert (d_F cx / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. rewrite SHV in Ha. cbn in *. lia. }
destruct (cm_acall_keep B LAWS cx ly S W regs mem md dec_ev_6f0 W2 mem2 _ _ _ Hcore HK ltac:(lia) HnF HnS)
  as (Ksp & KF & KS).
assert (Hne : forall x, In x (ablocks B (d_ly cx) (d_S cx)) -> x <> (out, olen)) by (intros x Hx ->; exact (Hnb Hx)).
assert (HP2 : YK11.getr regs2 2 = YK11.getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (HP3 : YK11.getr regs2 3 = YK11.getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (HP4 : YK11.getr regs2 4 = YK11.getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (HP8 : YK11.getr regs2 8 = YK11.getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (HP9 : YK11.getr regs2 9 = YK11.getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (HP22 : YK11.getr regs2 22 = YK11.getr regs 22) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
assert (HP27 : YK11.getr regs2 27 = YK11.getr regs 27) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
(* the frame invariant and the memory clauses after the free *)
assert (Hcore2 : dec_b_core B cx ly2 S2 W2 regs2 mem2 md2 dec_ev_840).
{ apply (cm_core_kept B cx ly S W regs mem md dec_ev_6f0 ly2 S2 W2 regs2 mem2 md2 dec_ev_840 Hcore HJ2).
  - rewrite Hfr2. exact Hfrm.
  - exact HP8.
  - exact HP9.
  - unfold spZ. rewrite HP2. reflexivity.
  - exact HP3.
  - exact HP4.
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
    pose proof (sep_blocks segs B LAWS ly S W mem md (d_p cx) (d_n cx) out olen HAR Hp Hinb (Hne _ Hinp)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
pose proof Hcore2 as (HJ2' & _). pose proof HJ2' as (HAR2 & _).
assert (HMEM2 : cm_mem cx out res mode nch ns W2 mem2).
{ apply (cm_mem_kept B cx ly S W mem md ly2 S2 W2 mem2 md2 out res mode nch ns HCELLS HAR HAR2
    (cm_rom_rd B cx _ _ _ _ _ _ _ _ HROS HRNE HROMcx HJ) (cm_rom_rd B cx _ _ _ _ _ _ _ _ HROS HRNE HROMcx HJ2')).
  - intros a Ha _. apply Ksp. lia.
  - intros a Ha. exact (proj1 (KF a Ha)).
  - exact KS.
  - intros i Hi.
    assert (Hbl : Z.of_nat (length (d_body cx)) <= len).
    { unfold len, d_body, dec_b_len, dec_b_u. rewrite length_skipn.
      lia. }
    pose proof (req_size_pos len ltac:(lia)) as Hrq.
    apply (K2 res len i Hinr ltac:(lia)).
    pose proof (sep_blocks segs B LAWS ly S W mem md res len out olen HAR Hinr Hinb Hro) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - exact HMEM. }
assert (Hperm2 : Permutation (ablocks B ly2 S2) (ablocks B (d_ly cx) (d_S cx) ++ [(res, len)])).
{ rewrite Hbl2.
  assert (P1 : Permutation (l1 ++ (out, olen) :: l2) ((ablocks B (d_ly cx) (d_S cx) ++ [(res, len)]) ++ (out, olen) :: [])).
  { rewrite <- Hbl1, <- app_assoc. exact Hperm. }
  pose proof (Permutation_app_inv _ _ _ _ _ P1) as P2. rewrite app_nil_r in P2. exact P2. }
assert (Hmle3 : mo_le MT (d_S cx) S2 (dec_spent_840 MT (d_n cx))).
{ unfold dec_spent_840. exact (mo_le_trans MT MTL _ _ _ _ _ Hmle Hmle2). }
assert (Hmok3 : mo_ok MT S2 (dec_rest_840 MT)).
{ unfold dec_rest_6f0 in Hmok. exact (mo_ok_step MT MTL S S2 (mo_free MT) (dec_rest_840 MT) Hmok Hmle2). }
(* ---- +0x838 .. +0x83c: the run to the leaf ---- *)
rewrite Rra.
change (w64 (DEC_A_LLVMF + 0x838)) with (Z_to_bv 64 (DEC_A_LLVMF + 0x838)). rewrite <- cm_base_eq.
set (E := Eimg (Ereg regs2 [])).
assert (HS : st_ok_pi segs decodeb_val E (mkSS 0x838 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (decodeb_val A_TEXT + 0x838)) mem2 (seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (PI := PI_decodeb)).
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok segs (SOff 18 0) [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env decodeb_val A_LIM E) by (exact (Eimg_env (PI := PI_decodeb) (Ereg regs2 []))).
pose proof (paj_run (SK := dec_B_sink_head) (PI := PI_decodeb) B LAWS) as RUN.
paj_run_tok RUN HS HJ2 SHOK cm_Bspan; [apply awr_ok_nil |].
assert (Emem : ms_mem ms = mem2)
  by (apply functional_extensionality; intros x; apply HF; intros (r & Hr & _); destruct Hr).
rewrite Emem in HJ2.
assert (HPT : aregs_preserved regs2 (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E _ ms regs2 [] HS);
    [ split; [intros nn Hnn; cbv delta [E]; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia | reflexivity]
    | vm_compute; reflexivity ]. }
assert (Ta0 : YK11.getr (ms_regs ms) 10 = w64 len).
{ cm_rg HS (10%bv : bv 5). cbn [sv_denot]. rewrite Z.add_0_r. cbv delta [E].
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_lt by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  rewrite Z_to_bv_bv_unsigned. etransitivity; [exact HP22 | exact R22]. }
assert (Tra : YK11.getr (ms_regs ms) 1 = w64 (DEC_A_LLVMF + 0x840)).
{ cm_rg HS (1%bv : bv 5). rewrite (codeptr_val (PI := PI_decodeb) E _ HEI). unfold w64.
  f_equal; vm_compute; reflexivity. }
pmkst HS. rewrite Emem.
change (pa_sigma DB_reac_upstream_channels) with (decodeb_sigma DB_reac_upstream_channels).
assert (EPC : decodeb_sigma DB_reac_upstream_channels = REAC_UPSTREAM_CHANNELS) by (vm_compute; reflexivity).
rewrite EPC.
assert (TP2 : YK11.getr (ms_regs ms) 2 = YK11.getr regs 2) by (rewrite <- HP2; exact (HPT 2 ltac:(unfold acallee_saved; lia))).
assert (TP3 : YK11.getr (ms_regs ms) 3 = YK11.getr regs 3) by (rewrite <- HP3; exact (HPT 3 ltac:(unfold acallee_saved; lia))).
assert (TP4 : YK11.getr (ms_regs ms) 4 = YK11.getr regs 4) by (rewrite <- HP4; exact (HPT 4 ltac:(unfold acallee_saved; lia))).
(* ---- reac_upstream_channels ---- *)
eapply SRr_mono.
{ apply (@dec_leafb_upstream_channels fx rc dec_B_sink_head B LAWS HCELLS LUC W2 (ms_regs ms) mem2 DEC_LLVMF_STK
    (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 _ dec_ev_840
    (d_sp1 cx - d_sp0 cx) HJ2).
  - assert (Tsp : spZ (ms_regs ms) = d_sp1 cx) by (unfold spZ in *; rewrite TP2; exact Rsp). lia.
  - rewrite Z.mod_divide in Hsp0al, Hsp1al by lia. rewrite Z.mod_divide by lia.
    destruct Hsp0al as [q0 Hq0]. destruct Hsp1al as [q1 Hq1]. exists (2 * q1 - q0). lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite Tra. unfold w64. rewrite <- cm_base_eq.
    apply (ret_ok_codeptr_v (PI := PI_decodeb)); first [lia | reflexivity].
  - rewrite TP3. exact Hgp.
  - rewrite TP4. exact Htp. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3' & Hres3 & Heff3 & Hgr3 & ->).
(* ---- the state at +0x840 ---- *)
assert (U3 : forall r, acallee_saved r -> YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (HPT r Hr). exact (HP3' r Hr). }
unfold llvm_b_st_840. exists fx, ly2, S2, regs3, mem2, md3, res, mode, nch, ns.
split. { rewrite Tra. reflexivity. }
split; [exact Hfz|].
split.
{ apply (cm_core_kept B cx ly2 S2 W2 regs2 mem2 md2 dec_ev_840 ly2 S2 W2 regs3 mem2 md3 dec_ev_840 Hcore2 HJ3).
  - pose proof Hcore2 as (_ & Hfr3 & _). exact Hfr3.
  - exact (U3 8 ltac:(unfold acallee_saved; lia)).
  - exact (U3 9 ltac:(unfold acallee_saved; lia)).
  - assert (Q2 : YK11.getr regs3 2 = YK11.getr regs2 2) by exact (U3 2 ltac:(unfold acallee_saved; lia)).
    unfold spZ. rewrite Q2. reflexivity.
  - exact (U3 3 ltac:(unfold acallee_saved; lia)).
  - exact (U3 4 ltac:(unfold acallee_saved; lia)).
  - intros a Ha. reflexivity.
  - intros a Ha. reflexivity.
  - pose proof Hcore2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFp2 & _). exact HFp2.
  - pose proof Hcore2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPy2 & _). exact HPy2.
  - intros i Hi. reflexivity. }
split; [exact Hperm2|].
split; [exact Hres4|].
split; [exact Hmle3|]. split; [exact Hmok3|].
destruct HMEM2 as (Mfrs & Mfsh & Mmode & Mg & M24 & M32 & M40 & M56 & M64 & M72 & M80 & M88 & M112).
split; [exact Mfrs|].
split.
{ rewrite Hres3. assert (Ta0' : bv_unsigned (YK11.getr (ms_regs ms) 10) = len)
    by (rewrite Ta0; unfold w64; apply unsigned_lit_small; lia).
  rewrite Ta0'. reflexivity. }
assert (Q22 : YK11.getr regs3 22 = YK11.getr regs2 22) by exact (U3 22 ltac:(unfold acallee_saved; lia)).
assert (Q27 : YK11.getr regs3 27 = YK11.getr regs2 27) by exact (U3 27 ltac:(unfold acallee_saved; lia)).
split; [rewrite Q22, HP22; exact R22|].
split; [rewrite Q27, HP27; exact R27|].
split; [exact Mmode|]. split; [exact Mfsh|]. split; [exact Mg|].
split; [exact M24|]. split; [exact M32|]. split; [exact M40|]. split; [exact M80 | exact M112].
Qed.
End f.
End t.
