From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRop_iface V23LeptCmap2 V23LeptRop V23LeptRop2Segs V23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptRopGSpec V23LeptRop2Gset V23LeptRop2WC V23LeptRopGenSetup.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenPre.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem rg_gen_pre_W : rg_gen_pre.
Proof.
  unfold rg_gen_pre.
  intros C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy op tv ret ENTRY
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh Ld Ld0 Ld00 Ls Hop JTv Eent Htv0 Htv2 NW NH AR1 AR2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 240 <= s)%Z) by exact Hlo.
  pose proof SHd as (_ & Hdpw & Hdph & Ewd & Hszd). pose proof SHs as (_ & Hspw & Hsph & Ews & Hszs).
  pose proof (wpl_bits dpixw 1 ltac:(lia) ltac:(lia)) as WBd. rewrite <- Ewd in WBd.
  pose proof (wpl_bits spixw 1 ltac:(lia) ltac:(lia)) as WBs. rewrite <- Ews in WBs.
  pose proof (wpl_of_range dpixw 1 ltac:(lia) ltac:(left; reflexivity)) as Hwd. rewrite <- Ewd in Hwd.
  pose proof (wpl_of_range spixw 1 ltac:(lia) ltac:(left; reflexivity)) as Hws. rewrite <- Ews in Hws.
  set (nd := (4 * (dwpl * dpixh))%Z) in *. set (ns := (4 * (swpl * spixh))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; assert (1 * 1 <= dwpl * dpixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  assert (Hns : (0 < ns)%Z) by (subst ns; assert (1 * 1 <= swpl * spixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datas) ns CK HW Ls Hns) as [Gs TOPs]. rewrite u_Z2bv in Gs, TOPs by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & AL16d & _). rewrite u_Z2bv in AL16d by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ls) as (_ & AL16s & _). rewrite u_Z2bv in AL16s by lia.
  pose proof (mod16_mod4 _ AL16d) as AL4d. pose proof (mod16_mod4 _ AL16s) as AL4s.
  pose proof (clip_facts dx sx dw dpixw spixw ltac:(lia) ltac:(lia) NW) as (CX1 & CX2 & CX3 & CX4 & CX5).
  pose proof (clip_facts dy sy dh dpixh spixh ltac:(lia) ltac:(lia) NH) as (CY1 & CY2 & CY3 & CY4 & CY5).
  assert (Hop' : (1 <= op <= 14)%Z) by lia.
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true)
    by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  destruct (rl_clip_run al_rom regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKf Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy H2 H1 H10 H11 H12 H13 H14 H15 H16 H17 NW NH)
    as (r1 & S1 & D1 & D2 & D5 & D6 & D7 & D8 & D9 & D11 & D12 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26
        & D27 & D28 & D29 & D30 & D31 & AG1).
  carry AG1 H10 (10 : reg) D10. carry AG1 H14 (14 : reg) D14. carry AG1 H16 (16 : reg) D16.
  set (DH := clip_w dy sy dh dpixh spixh) in *.
  set (M1 := wbytes (RLF m s ret regs) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 DH))) in *.
  assert (GR1 : mem_grows m M1).
  { subst M1. unfold RLF. repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl. }
  assert (OUT1 : forall a : word, ~ (s - 240 <= u a < s)%Z -> M1 a = m a).
  { intros a Ha. subst M1. rewrite wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). apply RLF_outside; lia. }
  assert (SOK240 : store_ok SEGS M1 (Z_to_bv 64 (s - 240)) 240 = true).
  { eapply store_ok_mono; [exact GR1 | apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]]. }
  assert (JT1 : rdn SEGS M1 (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv)).
  { transitivity (rdn SEGS m (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4).
    - apply rdn_ext; unfold RG_JT; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT1. lia.
    - rewrite <- p16_segs. rewrite (W_rdn_ro C A m md (RG_JT + 4 * (op - 1)) 4 HW) by (unfold RG_JT; cbn; lia).
      rewrite p16_segs. exact JTv. }
  assert (DH1 : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 DH))).
  { subst M1. apply rdn_wbytes_hit8; unorm; lia. }
  assert (RLD : RLC_D = RG_P0) by (apply bv_eq; reflexivity).
  assert (EP : Z_to_bv 64 PC_rasteropLow = RLC_P) by (apply bv_eq; reflexivity).
  rewrite RLD in S1.
  destruct (rg_setup_W al_rom r1 M1 s datad dpixh datas spixh dwpl swpl (clip_d dx sx) (clip_s dx sx)
              (clip_w dx sx dw dpixw spixw) (clip_d dy sy) (clip_s dy sy) DH op tv
              (clip_s dy sy) sy dpixh dy (clip_d dy sy + clip_w2 dy sy dh - dpixh)%Z spixh
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AL4d ltac:(lia) ltac:(lia) AL4s
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              CX1 CX2 NW ltac:(lia) ltac:(lia) CY1 CY2 NH ltac:(lia) ltac:(lia) AR1 AR2
              Hop' Htv0 Htv2 JT1
              ltac:(unfold clip_s; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold clip_d, clip_w2; lia) ltac:(lia)
              ltac:(subst DH; unfold clip_w, clip_w3, clip_w2, clip_d, clip_s; lia)
              SOK240 DH1 D2 D1 D26 D23 D16 D18 D28 D6 D5 D7 D8 D9 D10 D11 D13 D14 D19 D24 D25 D27)
    as (r2 & MB & dxb & sls & nfw & psf & pdf & psF & pdF & psl & pdl & fw & f6 & f7 & nofull & nolast & f3 &
        S2 & OUT2 & GR2 & K3 & K4 & GEO & CELLS & REGS).
  exists r2, MB, dxb, sls, nfw, psf, pdf, psF, pdF, psl, pdl, fw, f6, f7, nofull, nolast, f3.
  split; [rewrite EP, <- Eent; eapply msteps_trans; [exact S1 | exact S2] |].
  split; [intros a Ha; rewrite OUT2 by lia; apply OUT1; exact Ha |].
  split; [eapply mem_grows_trans; [exact GR1 | exact GR2] |].
  split.
  { apply (rlcells_frame (RLF m s ret regs)); [lia | lia | apply rlcells_RLF; lia |].
    intros x Hx. rewrite OUT2 by lia. subst M1. apply wbytes_outside; zlen; rewrite ?u_Z2bv by lia; lia. }
  split; [rewrite K3; apply AG1; notin_list |].
  split; [rewrite K4; apply AG1; notin_list |].
  split; [exact GEO |]. split; [exact CELLS | exact REGS].
Qed.

End GenPre.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
