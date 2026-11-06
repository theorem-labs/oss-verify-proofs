(* Part M1 of segment M of check_text_scribble's walk in image B (check_text_scribble_B_mi.v): from the memset 0x83ff4
   (bs_cut .. PC_M) through __asan_memset (ch, 0xa5, 24) (the runtime's contract, lib/AU/Prog/CPgWalkIntrU.v
   cw_intrin_call) and 0x84004 .. 0x84010 to the entry of diginet_scribble_text (bs_cut .. PC_C1). The memset writes
   the record (the call's write set) and its stack below sp1; the save area, the frame, its shadow and want are none
   of these. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YE2y.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkIntrU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_f check_text_scribble_B_mi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MSET : aintrin_realizes tfibsegs B OSet B_MEMSET.

Theorem bsm1_holds : forall g pos W2 c2, bs_pre B g -> bs_now B g -> bs_cut B MT g pos PC_M (P_M g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (bs_cut B MT g pos PC_C1 (P_C1 g pos)).
Proof.
intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (R26 & R20 & Hwg).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & R27 & _).
pose proof Hpre as (HE & _ & _ & _ & Hoch & _ & (Hch0 & Hchn & Hchtd & Hchtw & _ & _ & Hcham & Hchwin) & _ & _ & _ & Hn & _).
pose proof HE as (_ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 (proj1 HE)) as HARc.
destruct (bs_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (bs_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as (_ & Hchra2 & Hchhull2 & _).
unfold TB_check_text_scribble, ESTACK in Hceil, Hwin, H46.
assert (Hsp1m : bs_sp1 g mod 16 = 0).
{ pose proof (Z.div_mod (bs_sp1 g) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D. rewrite D.
  replace (32 * (bs_sp1 g / 32)) with ((2 * (bs_sp1 g / 32)) * 16) by lia. apply Z_mod_mult. }
(* the state at 0x83ff4: no memory, the registers as atoms *)
set (E := Ereg regs2 (cw_extra [])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (HS : st_ok tfibsegs E (mkSS PC_M sr_atoms [] None (mkFacts [(32%nat, mkAF SB SB 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_M) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite cw_ew_SB, unsigned_lit_small by (unfold SB; lia). unfold SB. split; [|exact I]. split; [lia|].
    split; [reflexivity | lia]. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 (bs_q g)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E26 : ew E 26 = w64 (snd (bs_owe g))) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 PC_M) with (Z_to_bv 64 PC_M).
cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) B_MEMSET.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem2) (mrestrict _ ?m1), HG : mem_grows _ _ |- _ =>
  assert (KA1 : forall a, aview tfibsegs (w_H W2) m1 a = aview tfibsegs (w_H W2) mem2 a)
    by (intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity | intros (r & Hr & _); destruct Hr]);
  assert (KP1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m1 a)
    by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp))
end.
clear_frames. cw_norm_model.
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict (w_H ?Wx) ?msv) |- _ =>
  rreg HS (10%bv : bv 5) Ra0; rreg HS (11%bv : bv 5) Ra1; rreg HS (12%bv : bv 5) Ra2; rreg HS (2%bv : bv 5) Rsp;
  rreg HS (3%bv : bv 5) Rgp; rreg HS (4%bv : bv 5) Rtp;
  assert (Esp : spZ (ms_regs msv) = bs_sp1 g)
    by (unfold spZ at 1; rewrite Rsp; rewrite ?sv_denot_SOff0; ewpeel; rewrite (EE 2%nat 2%bv eq_refl), R2;
        apply unsigned_lit_small; lia);
  let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
  eapply (cw_intrin_call B LAWS OSet B_MEMSET MSET Wx Ev ssv msv _ (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g)
    (bs_W0 g) (bs_mem0 g) (bs_md0 g) ((0, pos) :: bs_own g) ly2 S2 (bs_k g) (bs_ch g) 165 24 0x84004 kk [] _ HS
    eq_refl eq_refl HJ);
  [ rewrite Ra0, ?sv_denot_SOff0; ewpeel; rewrite (EE 20%nat 20%bv eq_refl); exact R20
  | rewrite Ra1; reflexivity
  | rewrite Ra2; reflexivity
  | lia | lia | lia
  | rewrite Esp; unfold ESTACK; lia
  | rewrite Esp; lia
  | rewrite Esp; exact Hsp1m
  | exact Hsp0al
  | rewrite Rgp, ?sv_denot_SOff0; ewpeel; rewrite (EE 3%nat 3%bv eq_refl), R3; exact Hgp
  | rewrite Rtp, ?sv_denot_SOff0; ewpeel; rewrite (EE 4%nat 4%bv eq_refl), R4; exact Htp
  | vm_compute; reflexivity
  | lia
  | apply ret_ok_even; vm_compute; reflexivity
  | intros a Ha; destruct (Hchtw a Ha) as (Haw & _ & _ & _);
    pose proof (cj_dst_byte tfibsegs B LAWS (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) (bs_mdc g) (bs_ch g) 24 a HARc
      Hchtd Ha) as (Hb1 & _);
    split;
    [ apply (bsm_awr_mono _ _ _ _ _ _ _ _ _ _ _ Haw);
      [ intros bb mm Hin; exact (Permutation_in _ (Permutation_sym HP) Hin) | apply incl_tl, incl_refl | exact Efa ]
    | rewrite Esp; unfold ESTACK, coff_win, TB_check_text_scribble in *; lia ]
  | exact Hcham
  | intros x Hx; destruct (Hchra2 x Hx) as (s & Hs & Hok); exists s; rewrite KA1; split; assumption
  | intros _ s Hs; rewrite KA1; exact (Hchhull2 s Hs)
  | exact I
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | cbn [ss_mem]; submem_to
  | apply Forall_nil
  | ] end.
intros regs3 mem3 md3 HJm HPm3 Ha0m Hset Hkeptm Hpresm Hsbm HSm.
pose proof (same_io_materialized _ _ Hsbm) as HIOm. clear Hsbm.
rewrite Esp in Hkeptm. unfold ESTACK in Hkeptm.
clear HS. rename HSm into HS. clear HJ. rename HJm into HJ.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (SHOK2 : sh_ok tfibsegs CW_Bx [] Ev (mrestrict (w_H W2) mem3)) by constructor end.
clear SHOK. rename SHOK2 into SHOK.
(* 0x84004 .. 0x84010: a0 = q, a1 = ch, a2 = n, jal diginet_scribble_text *)
cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) PC_C1.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem3) (mrestrict _ ?m4), HG : mem_grows _ _ |- _ =>
  assert (KA2 : forall a, aview tfibsegs (w_H W2) m4 a = aview tfibsegs (w_H W2) mem3 a)
    by (intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity | intros (r & Hr & _); destruct Hr]);
  assert (KP2 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) m4 a)
    by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp))
end.
clear_frames. cw_norm_model.
(* the bytes of the walk's own frame and of its shadow are fresh for the call state *)
assert (HFR : forall a, (bs_F g pos <= a < bs_F g pos + 64) \/ (SB + bs_F g pos / 8 <= a < SB + bs_F g pos / 8 + 8) ->
  cw_fresh B (bs_lyc g) (bs_Sc g) a).
{ intros a Ha. apply (cw_fresh_own B LAWS (bs_lyc g) (bs_Sc g) ly2 S2 W2 mem2 md2 0 pos a HAR2 Hfr HP Efa).
  assert (HSB : shadow_addr (bs_F g pos) = SB + bs_F g pos / 8)
    by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity).
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. fold (bs_F g pos). rewrite HSB.
  change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. destruct Ha; [left | right]; lia. }
assert (HRF : forall a, bs_ch g <= a < bs_ch g + 24 -> cw_fresh B (bs_lyc g) (bs_Sc g) a -> False)
  by (intros a Ha Hf; exact (bsl_apart B (bs_lyc g) (bs_Sc g) (bs_ch g) 24 a Hoch Hf a Ha eq_refl)).
assert (HF8 : 0 <= bs_F g pos / 8 <= bs_F g pos) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8b : bs_F g pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
(* everything but the record and the memset's stack is as at 0x83ff4 *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- _ =>
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (bs_ch g <= a < bs_ch g + 24) -> ~ (bs_sp1 g - 4096 <= a < bs_sp1 g) ->
    aview tfibsegs (w_H W2) (ms_mem msv) a = aview tfibsegs (w_H W2) mem2 a)
    by (intros a Ha H1 H2; rewrite KA2, (Hkeptm a Ha H1 H2); exact (KA1 a));
  assert (KPALL : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msv) a)
    by (intros a Hp; exact (KP2 a (Hpresm a (KP1 a Hp))))
end.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- _ =>
  assert (KREC : forall i, 0 <= i < 24 -> val_mem tfibsegs (rd W2 (ms_mem msv)) (bs_ch g + i) 1 165)
    by (intros i Hi; apply YE2y.val_mem1_of_aview; rewrite KA2, (Hset i Hi); reflexivity);
  (* the frame, its shadow and the save area are none of the written bytes *)
  assert (KOFF : forall a, (bs_sp g - 96 <= a < bs_sp g) \/ (bs_F g pos <= a < bs_F g pos + 64) \/
    (SB + bs_F g pos / 8 <= a < SB + bs_F g pos / 8 + 8) ->
    aview tfibsegs (w_H W2) (ms_mem msv) a = aview tfibsegs (w_H W2) mem2 a)
    by (intros a Ha; apply KALL;
        [ unfold SB in *; lia
        | intros Hr; destruct Ha as [Ha | Ha];
          [ unfold coff_win, TB_check_text_scribble, ESTACK in Hchwin; lia | exact (HRF a Hr (HFR a Ha)) ]
        | unfold SB in *; lia ])
end.
apply SRr_ret.
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md4] =>
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Hms;
  exists ly2, S2, (ms_regs msv), (ms_mem msv), md4;
  split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|]
end.
split; [exact HJ|].
split.
{ apply (cw_kept_step B LAWS TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) (bs_mdc g) W2 mem2
    (ms_mem ms0) (bs_sp g) (bs_wr g) (fun a => (bs_ch g <= a < bs_ch g + 24) \/ (bs_sp1 g - 4096 <= a < bs_sp1 g)));
  [ unfold TB_check_text_scribble, ESTACK; lia | exact HARc | exact HK
  | intros a Ha Hx; apply KALL; [exact Ha | intros H; apply Hx; left; exact H | intros H; apply Hx; right; exact H]
  | intros a [Ha | Ha]; [right; left; split; [exact Ha|]; intros Him;
      exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ a HARc Hchtd Ha Him)
    | left; unfold TB_check_text_scribble, ESTACK; lia]
  | exact KPALL ]. }
split; [exact HP|]. split; [exact Hni|].
lazymatch type of HIOm with same_io ?mA _ =>
  assert (HIO1 : same_io (bs_mdc g) mA) by (eapply same_io_trans; [exact Hio | kio]) end.
split; [eapply same_io_trans; [exact (same_io_trans _ _ _ HIO1 HIOm) | kio]|].
split; [exact Hmo|].
split.
{ apply (bsm_common_keep g pos regs2 mem2 W2 _ _ W2 HC);
  [ bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
  | bs_rfin | bs_rfin | bs_rfin | exact KOFF ]. }
split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
split.
{ intros j Hj. rewrite repeat_length in Hj. rewrite (bsf_nth_repeat 24 j 165 0 Hj).
  split; [exact (KREC (Z.of_nat j) ltac:(lia)) | lia]. }
pose proof (bsf_owe_len (Z.to_nat (bs_n g)) (bs_tb g)) as HOL.
assert (HwL : Z.of_nat (length (fst (bs_owe g))) = bs_n g)
  by (unfold bs_owe, owed_scribble_text_spec; rewrite HOL; lia).
apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Hwg].
intros a Ha. rewrite HwL in Ha. apply KALL.
- lia.
- intros Hr. apply (HRF a Hr). apply (bs_fresh B LAWS g pos ly2 S2 W2 mem2 md2 a Hpre HJ0 HP). unfold bs_zv. lia.
- lia.
Qed.
End s.
