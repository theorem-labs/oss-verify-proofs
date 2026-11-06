(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceMeter PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceCloseSpec.

(* The return slot of the fclose call, 0x81d94 = the function + 0x48 (lib/A: 0x81ecc = + 0x3c). *)
Definition CL_RET_FCLOSE : Z := Eval compute in (AF_pcap_source_close + 72).
Lemma CL_RET_FCLOSE_eq : CL_RET_FCLOSE = AF_pcap_source_close + 72.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section d.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the stream predicates read only their footprint: the PAImg instances of lib/A's image-generic lemmas
   (Section fr of lib/A/Prog/PcapSourceClose.v) ---------------------------------------------------------------- *)
Definition vm_frame := AC.vm_frame_segs SEGS.
Definition asource_none_frame := AC.asource_none_frame_segs SEGS.
Definition asource_at_frame := AC.asource_at_frame_segs SEGS.

Lemma ra_frame : forall (rd rd' : Z -> option Z) a n,
  range_addressable rd SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n HR Hk x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite Hk by exact Hx. split; [exact Hs | exact Ho]. Qed.

Section e.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.

(* ---- the walk ------------------------------------------------------------ *)
Definition SB_CL : Z := 0x7fff8000.
Definition CBx : sv := SOff 32 0.
Definition CLspan : Z * Z := (SB_CL, SB_CL + 2 ^ 44 - 1).
Definition ps_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition cl_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32; ps_region].
Definition cl_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SB_CL SB_CL 0)] [] [].
Definition ss_cl : sstate := mkSS AF_pcap_source_close sr_atoms cl_regions None cl_facts.
Definition cl_SH : list shent := [mkSHE 10 0 8].
Definition cl_extra (f : Z) : list word := map (Z_to_bv 64) [SB_CL; f].

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable ra_fc1 ra_fc2 : Z.
(* Discharged by the asan-ubsan instance of a Theorem Labs lane's fclose walk (lib/A/Stdio/WFclose.v; a Theorem Labs lane's lib/B twin). Its
   data-buffer premise In (b, |C|) (a working branch a55f5f4a671) comes from the f <> 0 live-block fact Hinb. *)
Hypothesis AFCLOSE : afclose_source_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fclose) ra_fc1 ra_fc2
  pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
Hypothesis ASIL : asource_img_laws SK SEGS B K.
Hypothesis FM : asrc_file_meter SK SEGS B MT.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).

(* The stream's environment lies in the image (asil_env). *)
Lemma src_env_img : forall a, asrc_env_addr K a -> 0x10000 <= a < pcap_img_end.
Proof. intros a Ha. exact (pa_img_range a (proj1 (asil_env _ _ _ _ ASIL a Ha))). Qed.

(* The meta invariant across a run that writes only [sp - 32, sp) and [ps, ps + 8). *)
Lemma src_meta_inv_frame : forall lyc Sc W memc mdc mm mdq M sp ps cid pos,
  AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc Sc W mm mdq -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= ps -> ps + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  alloc_ceiling + 32 <= sp -> ly_stk_lo lyc <= sp - 32 -> sp <= ly_stk_hi lyc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((sp - 32 <= a < sp) \/ (ps <= a < ps + 8)) ->
     aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
  asrc_meta_inv SEGS K lyc (rdW W memc) M -> asrc_meta_inv SEGS K lyc (rdW W mm) M.
Proof.
intros lyc Sc W memc mdc mm mdq M sp ps cid pos HAR HAR2 Hin Hfa1 Hfa2 Hc32 Hlo Hhi UN (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & _).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfimg.
split; [exact HX|]. split; [exact Himg|]. split; [exact (asrc_meta_ptr_of_AR SK SEGS B K ASIL _ _ _ _ _ HAR2)|]. split.
- eapply vm_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
  destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & _ & _ & _).
  pose proof (pa_segs_low x Hi) as Hx1. pose proof (pa_img_range x Hi) as Hx2. unfold pcap_img_end, YImgTop.IMG_TOP in Hx2.
  apply UN; [lia | intros [H|H]; lia].
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
  intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_of_aview SEGS).
  destruct (AR_extra_law_ok SEGS B lyc Sc W memc mdc a HAR
    ltac:(apply Exists_exists; exists (M, AMETA_SIZE); split; [exact HX | unfold in_zr; cbn [fst snd]; lia]))
    as (_ & _ & Hfr & Hstk & _ & _ & Happ).
  destruct (Hfr cid pos Hin) as [Hnf _].
  unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ.
  apply UN; [lia | intros [H|H]; [apply Hstk; lia | apply Hnf; lia]].
Qed.

Lemma shent_ps_ok : forall Ex (m : word -> option byte) ps,
  U Ex CBx = SHADOW_OFF -> U Ex (SOff 10 0) = ps ->
  (4096 <= ps /\ (ps + 8 <= kLowShadowBeg \/ kHighMemBeg <= ps)) ->
  range_addressable (YCbn.rd_of SEGS m) SHADOW_OFF ps 8 ->
  sh_ok SEGS CBx cl_SH Ex m.
Proof.
intros Ex m ps HB Hq Hz HR. unfold sh_ok, cl_SH. apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq. split.
- rewrite Z.add_0_r. exact HR.
- intros a Ha. cbn in Ha. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma cl_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ps f cid pos,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 ps ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - AC.TPCAP_SOURCE_CLOSE_STK -> spZ regs <= sp0 ->
  In (cid, pos) own -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= ps -> ps + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid -> ps mod 8 = 0 ->
  val_mem SEGS (rdW W memc) ps 8 f -> 0 <= f < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps 8 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (cl_extra f))) ss_cl
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pcap_source_close)) memc (seg_rom SEGS))) /\
  sh_ok SEGS CBx cl_SH (Eimg (Ereg regs (cl_extra f))) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps f cid pos
  HJ H10 Hal16 Hwlo Hwhi Hown Hin Hfa1 Hfa2 Hps8 Hfv Hf64 Hsh.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HTS : AC.TPCAP_SOURCE_CLOSE_STK = 16560) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 15 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
set (E := Eimg (Ereg regs (cl_extra f))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cl_extra f)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ps) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_CL) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 15) = Z_to_bv 64 (VAL (A_OBJ 15))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = ps) by (rewrite E10; apply unsigned_lit_small; unfold in_app in Hfapp; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HPS : forall a, ps <= a < ps + 8 -> apresent (w_H W) memc a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
  right. right. right. exists cid, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd]. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_cl. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cl_regions, stack_region, got_regionP, bcell_regionP, ps_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * fold E. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 15) 0) (VAL (A_OBJ 15)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 15)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * fold E. rewrite (VB (A_OBJ 15) (VAL (A_OBJ 15)) Ecell) by (pose proof (pa_val_range (A_OBJ 15)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 15)) 0 8 CBx SB_CL);
      [cbn [sv_denot CBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_CL; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * fold E. rewrite (VB 10%nat ps E10) by (unfold in_app in Hfapp; lia).
      split; [lia|]. split; [unfold in_app in Hfapp; lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply HPS. lia. }
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ ps 0 8 (SOff 33 0) f);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Hfv.
  + apply pairwise_disjoint_of_extents.
    unfold cl_regions, stack_region, got_regionP, bcell_regionP, ps_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    fold E. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 15) (VAL (A_OBJ 15)) Ecell) by (pose proof (pa_val_range (A_OBJ 15)); lia).
    rewrite (VB 10%nat ps E10) by (unfold in_app in Hfapp; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, in_app, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    revert Hslo Hshi H47 Hceil C1 C3 HTS Hstk0 HcellR HgcD HgotR Hfa1 Hfa2 Hf4096 Hfceil Hfapp Hfimg Hwlo Hwhi.
    clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, U10, E32, !unsigned_lit_small by (unfold SB_CL; lia).
    try change (2 ^ 4) with 16. try change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    unfold in_app in Hfapp.
    revert Hslo Hshi H47 Hceil C1 C3 HTS Hstk0 Hal16 Hps8 Hfa1 Hfa2 Hf4096 Hfceil Hfapp Hwlo Hwhi.
    clear. unfold SB_CL. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- apply (shent_ps_ok _ _ ps).
  + unfold CBx. rewrite (U_atom _ 32 SB_CL E32) by (unfold SB_CL; lia). reflexivity.
  + rewrite (U_atom _ 10 ps E10) by (unfold in_app in Hfapp; lia). reflexivity.
  + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + rewrite <- (aview_rd_of SEGS). exact Hsh.
Qed.

Ltac cl_awr spv sp0v Usp U10 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spv - sp0v);
    [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | exact U10 | cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha |] ].

Ltac cl_frame_kept HF spv psv Usp U10 UN :=
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (spv - 32 <= a < spv) \/ (psv <= a < psv + 8)) HF
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?Usp, ?U10 in HrrW; lia|]);
          destruct HinW)) as UN.

Lemma asource_at_disj : forall m f b C p, asource_at SEGS K m f b C p ->
  f + SRC_FILE_BLOCK <= b \/ b + Z.of_nat (length C) <= f.
Proof.
intros m f b C p (Wn & cpos & fl & md & H). cbv zeta in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd).
exact Hd.
Qed.

(* The kept clauses of a run that writes only the function's own frame [sp - 32, sp) and the field [ps, ps + 8). *)
Lemma tclose_kept_nocall : forall lyc Sc W memc mdc memF sp ps cid pos (Ek : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= ps -> ps + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  alloc_ceiling + AC.TPCAP_SOURCE_CLOSE_STK <= sp ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((sp - 32 <= a < sp) \/ (ps <= a < ps + 8)) ->
     aview SEGS (w_H W) memF a = aview SEGS (w_H W) memc a) ->
  (forall a, sp - AC.TPCAP_SOURCE_CLOSE_STK <= a < sp -> apresent (w_H W) memF a) ->
  (forall a, ps <= a < ps + 8 -> Ek a) ->
  AC.tclose_kept SK SEGS B lyc Sc W memc W memF (sp - AC.TPCAP_SOURCE_CLOSE_STK) sp Ek.
Proof.
intros lyc Sc W memc mdc memF sp ps cid pos Ek HAR Hin Hfa1 Hfa2 Hsp UN Hpw HEk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfimg.
assert (HTS : AC.TPCAP_SOURCE_CLOSE_STK = 16560) by reflexivity.
assert (K1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - AC.TPCAP_SOURCE_CLOSE_STK <= a < sp) ->
  aview SEGS (w_H W) memF a = aview SEGS (w_H W) memc a).
{ intros a Ha Hn. apply UN; [lia|]. intros [H|H]; lia. }
split; [exact K1|]. split; [|split; [|split; [|split]]].
- intros b0 m0 i Hb Hi HnE. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & Hb4096 & Hbceil & _).
  apply UN; [lia|]. intros [H|H]; [lia | apply HnE; apply HEk; exact H].
- intros a Hi Hno He Hof. pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hr2.
  unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
  apply UN; [lia|]. intros [H|H]; lia.
- intros cid' pos' a Hin' Hr HnE.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid' pos' HAR Hin') as (Hg4096 & Hgceil & Hgapp).
  pose proof (fs_frame_bytes_nonneg cid') as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid' pos') ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid' pos' + fs_frame_bytes cid') ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid' pos') (fs_frame_bytes cid') Hnn) as Hse.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  apply UN; [destruct Hr; lia|]. intros [H|H]; [destruct Hr; lia | apply HnE; apply HEk; exact H].
- intros a Ha Hn Hp. eapply (apresent_transfer SEGS); [lia | intros Him; pose proof (pa_segs_low a Him); lia | apply K1; [exact Ha | exact Hn] | exact Hp].
- exact Hpw.
Qed.

(* The same across the fclose call: the run before it, fclose's journal, and the run after it. *)
Lemma tclose_kept_call : forall lyc Sc W memc mdc mm mdq ly2 S2 W2 mem2 md2 memF sp ps cid pos f (Ek : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= ps -> ps + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  alloc_ceiling + AC.TPCAP_SOURCE_CLOSE_STK <= sp ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) ->
  Permutation (ablocks B lyc Sc) ((f, SRC_FILE_BLOCK) :: ablocks B ly2 S2) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((sp - 32 <= a < sp) \/ (ps <= a < ps + 8)) ->
     aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
  ajournal SEGS B PFCLOSE_STK (sp - 32) (asource_fp f) lyc Sc W mm mdq [] ly2 S2 W2 mem2 md2 2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((sp - 32 <= a < sp) \/ (ps <= a < ps + 8)) ->
     aview SEGS (w_H W2) memF a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, sp - AC.TPCAP_SOURCE_CLOSE_STK <= a < sp -> apresent (w_H W2) memF a) ->
  (forall a, ps <= a < ps + 8 -> Ek a) -> (forall a, f <= a < f + req_size SRC_FILE_BLOCK -> Ek a) ->
  AC.tclose_kept SK SEGS B lyc Sc W memc W2 memF (sp - AC.TPCAP_SOURCE_CLOSE_STK) sp Ek.
Proof.
intros lyc Sc W memc mdc mm mdq ly2 S2 W2 mem2 md2 memF sp ps cid pos f Ek HAR Hin Hfa1 Hfa2 Hsp Hinf HPm UNa HJ1 UNb
  Hpw HEp HEf.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : AC.TPCAP_SOURCE_CLOSE_STK = 16560) by reflexivity. assert (HAS : PFCLOSE_STK = 16528) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfimg.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK HAR Hinf) as (_ & Hff4096 & Hffceil & Hfia & _).
change (req_size SRC_FILE_BLOCK) with 1304 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfia.
assert (K1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - AC.TPCAP_SOURCE_CLOSE_STK <= a < sp) ->
  aview SEGS (w_H W2) memF a = aview SEGS (w_H W) memc a).
{ intros a Ha Hn.
  transitivity (aview SEGS (w_H W2) mem2 a); [apply UNb; [lia | intros [H|H]; lia]|].
  transitivity (aview SEGS (w_H W) mm a); [apply G1; lia|].
  apply UNa; [lia | intros [H|H]; lia]. }
split; [exact K1|]. split; [|split; [|split; [|split]]].
- intros b0 m0 i Hb Hi HnE. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & Hb4096 & Hbceil & _).
  assert (Hne : (b0, m0) <> (f, SRC_FILE_BLOCK)).
  { intros Heq. injection Heq as -> ->. apply HnE. apply HEf. change (req_size SRC_FILE_BLOCK) with 1304 in *. lia. }
  assert (Hb2 : In (b0, m0) (ablocks B ly2 S2)).
  { destruct (Permutation_in _ HPm Hb) as [H|H]; [congruence | exact H]. }
  transitivity (aview SEGS (w_H W2) mem2 (b0 + i)); [apply UNb; [lia | intros [H|H]; [lia | apply HnE; apply HEp; exact H]]|].
  transitivity (aview SEGS (w_H W) mm (b0 + i)).
  { apply (G2 b0 m0 i Hb Hb2 Hi). intros Hf. destruct (AC.in_asource_fp f _ Hf) as [H|H]; [|lia].
    apply HnE. apply HEf. change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in H. lia. }
  apply UNa; [lia | intros [H|H]; [lia | apply HnE; apply HEp; exact H]].
- intros a Hi Hno He Hof. pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hr2.
  unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
  transitivity (aview SEGS (w_H W2) mem2 a); [apply UNb; [lia | intros [H|H]; lia]|].
  transitivity (aview SEGS (w_H W) mm a); [apply (G3 a Hi Hno He); apply fp_spares_off; exact Hof|].
  apply UNa; [lia | intros [H|H]; lia].
- intros cid' pos' a Hin' Hr HnE.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid' pos' HAR Hin') as (Hg4096 & Hgceil & Hgapp).
  pose proof (fs_frame_bytes_nonneg cid') as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid' pos') ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid' pos' + fs_frame_bytes cid') ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid' pos') (fs_frame_bytes cid') Hnn) as Hse.
  pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK cid' pos' HAR Hinf Hin') as Dff.
  unfold zdisjoint in Dff. cbn [fst snd] in Dff. change (req_size SRC_FILE_BLOCK) with 1304 in Dff.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  transitivity (aview SEGS (w_H W2) mem2 a);
    [apply UNb; [destruct Hr; lia | intros [H|H]; [destruct Hr; lia | apply HnE; apply HEp; exact H]]|].
  transitivity (aview SEGS (w_H W) mm a).
  { apply (G4 cid' pos' a Hin'); [unfold frame_rng, in_zr; cbn [fst snd]; exact Hr|].
    intros Hf. destruct (AC.in_asource_fp f _ Hf) as [H|H]; unfold SRC_FILE_BLOCK in H; destruct Hr; lia. }
  apply UNa; [destruct Hr; lia | intros [H|H]; [destruct Hr; lia | apply HnE; apply HEp; exact H]].
- intros a Ha Hn Hp. eapply (apresent_transfer SEGS); [lia | intros Him; pose proof (pa_segs_low a Him); lia | apply K1; [exact Ha | exact Hn] | exact Hp].
- exact Hpw.
Qed.

Theorem pb_pcap_source_closeX :
  AC.tpcap_source_close_specX SK SEGS pa_relro_lo pa_relro_hi B K MT (BASE + AF_pcap_source_close).
Proof.
unfold AC.tpcap_source_close_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps f b M p C cid pos
  HJ HROD Hraw Hra4 Hgp Htp H10 Hal16 Hwlo Hwhi Hown Hfa1 Hfa2 [Hps0 Hps8] Hfv Hf64 Hsh Hstream Hev.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HTS : AC.TPCAP_SOURCE_CLOSE_STK = 16560) by reflexivity.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfimg.
pose proof (frame_al64 SEGS B lyc Sc W memc mdc cid pos HAR Hin) as (Hfa64 & Hfb64 & Hfb).
assert (Hsp_hi : alloc_ceiling + AC.TPCAP_SOURCE_CLOSE_STK <= spZ regs) by lia.
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
destruct (cl_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps f cid pos
  HJ H10 Hal16 Hwlo Hwhi Hown Hin Hfa1 Hfa2 Hps8 Hfv Hf64 Hsh) as [HS SHOK].
remember (Eimg (Ereg regs (cl_extra f))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cl_extra f)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ps) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_CL) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs (cl_extra f)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hps64 : 0 <= ps < 2 ^ 64) by (unfold in_app in Hfapp; lia).
assert (U10 : bv_unsigned (ew E 10) = ps) by (rewrite E10; apply unsigned_lit_small; exact Hps64).
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_pcap_source_close)) with (Z_to_bv 64 (BASE + AF_pcap_source_close)).
(* The frame, the three saves, the two UBSan guards (0x81d5c ps null, 0x81d68 ps & 7: both decided not taken by the
   run, from atom 10's facts that cl_entry proves), the shadow base, the first shadow check and the load of ps->f, up
   to its test. *)
paj_run_tok RUN HS HJ SHOK CLspan;
  [ cl_awr (spZ regs) sp0 Usp U10; right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia] |].
cl_frame_kept HFr (spZ regs) ps Usp U10 UN1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK CLspan.
- (* f = 0: no call and no store; the epilogue *)
  rewrite branch_eq_U, (U_atom E 33 f E33 Hf64), U_lit in Hc by lia. apply Z.eqb_eq in Hc. subst f.
  paj_run_tok RUN HS HJ SHOK CLspan;
    [ cl_awr (spZ regs) sp0 Usp U10; right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia] |].
  cl_frame_kept HFr (spZ regs) ps Usp U10 UN2. clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 32 <= a < spZ regs) \/ (ps <= a < ps + 8)) ->
              aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)) end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3;
    cbn [ms_mem restrict mkst] in HR3 end.
  pose proof (field_of_region E _ 10%nat ps _ _ _ _ _ 0 8%N (SOff 33 0) 0 HR3 U10 ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vps.
  rewrite Z.add_0_r in Vps. change (N.to_nat 8) with 8%nat in Vps.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    prreg HS (1%bv : bv 5) R1;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    unfold AC.tpcap_source_close_post;
    exists lyc, Sc, (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite R1, E1, Hraw; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); eapply ajournal_mono_k; [exact HJ | unfold AC.EV_CLOSE; lia]|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (cl_extra 0) HS); [exact HAE | vm_compute; reflexivity]|];
    split; [reflexivity|];
    split; [cbn [Z.eqb]; eapply (asfm_k0 _ _ _ _ FM);
            eapply (ajournal_sub_init SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k 0 sp0 [] 0 HJ);
            [lia | reflexivity | lia | lia | lia]|];
    split; [repeat rewrite (proj1 (AC.wvb_fds_fs _ _ _)); reflexivity|];
    split; [repeat rewrite (proj2 (AC.wvb_fds_fs _ _ _)); reflexivity|];
    split; [cbn [AC.tclose_fblk Z.eqb app]; apply Permutation_refl|];
    split; [exact Vps|];
    split; [| intros Hf0; exfalso; apply Hf0; reflexivity];
    apply (tclose_kept_nocall lyc Sc W memc mdc (ms_mem msc) (spZ regs) ps cid pos); 
    [ exact HAR | exact Hin | exact Hfa1 | exact Hfa2 | exact Hsp_hi | exact UN
    | intros a Ha; apply Hpres1; lia | intros a Ha; left; exact Ha ]
  end.
- (* f <> 0: the call of fclose, the second shadow check, ps->f = NULL and the epilogue *)
  rewrite branch_eq_U, (U_atom E 33 f E33 Hf64), U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hf0.
  destruct (Hstream Hf0) as (Hinf & Hinb & HSRC & HMETA & HFPinc).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK HAR Hinf) as (_ & Hff4096 & Hffceil & Hfia & _).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) HAR Hinb) as (_ & Hb4096 & Hbceil & Hbia & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfia, Hbia.
  pose proof (req_size_pos (Z.of_nat (length C)) ltac:(lia)) as [_ Hreqb].
  change (req_size SRC_FILE_BLOCK) with 1304 in Hffceil, Hfia.
  pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK cid pos HAR Hinf Hin) as Dff.
  unfold zdisjoint in Dff. cbn [fst snd] in Dff. change (req_size SRC_FILE_BLOCK) with 1304 in Dff.
  pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc b (Z.of_nat (length C)) cid pos HAR Hinb Hin) as Dbf.
  unfold zdisjoint in Dbf. cbn [fst snd] in Dbf.
  pose proof (asource_at_disj _ _ _ _ _ HSRC) as Dfb.
  destruct (in_split _ _ Hinf) as (l1 & l2 & El).
  assert (HPf : Permutation (ablocks B lyc Sc) ((f, SRC_FILE_BLOCK) :: l1 ++ l2))
    by (rewrite El; apply Permutation_sym; apply Permutation_middle).
  paj_run_tok RUN HS HJ SHOK CLspan;
    [ cl_awr (spZ regs) sp0 Usp U10; right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia] |].
  cl_frame_kept HFr (spZ regs) ps Usp U10 UN2. clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UNa : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 32 <= a < spZ regs) \/ (ps <= a < ps + 8)) ->
              aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)) end.
  clear UN1 UN2.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  assert (HEVf : st_nev Sc + 2 <= EV_MAX) by (unfold AC.EV_CLOSE in Hev; lia).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, E3; exact Hgp);
    assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, E4; exact Htp);
    assert (Qsp : spZ rg = sp0 + (spZ regs - 32 - sp0))
      by (unfold spZ at 1; rewrite Q2, Usp, unsigned_lit_small by lia; lia);
    assert (Q10' : getr rg 10 = Z_to_bv 64 f) by (rewrite Q10, E33; reflexivity);
    assert (Qs0 : achain lyc (aview SEGS (w_H W) mm) (sp0 + (spZ regs - 32 - sp0)) (s0Z rg) [])
      by (apply achain_low; unfold s0Z; rewrite Q8, E10, unsigned_lit_small by lia; lia);
    assert (HSRCc : asource_at SEGS K (rdW W mm) f b C p)
      by (apply (asource_at_frame K (rdW W memc) (rdW W mm) f b C p); [| exact HSRC];
          intros a Ha; apply (mbyte_of_aview SEGS); unfold SRC_FILE_BLOCK in Ha;
          destruct Ha as [Ha | [Ha | Ha]];
          [ apply UNa; [lia | intros [H|H]; lia]
          | apply UNa; [lia | intros [H|H]; lia]
          | pose proof (src_env_img a Ha) as Hk; apply UNa; [lia | intros [H|H]; lia] ]);
    assert (HRODc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mm))
      by (intros a Hro Ho He;
          assert (Hi : in_img SEGS a) by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]);
          pose proof (pa_img_range a Hi) as Hr1; pose proof (pa_segs_low a Hi) as Hr2;
          rewrite (UNa a) by (lia || (intros [H|H]; lia)); exact (HROD a Hro Ho He));
    assert (HMETAc : asrc_meta_inv SEGS K lyc (rdW W mm) M)
      by (pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _);
          eapply (src_meta_inv_frame lyc Sc W memc mdc mm _ M (spZ regs) ps cid pos HAR (proj1 HJ) Hin Hfa1 Hfa2);
          [ lia | rewrite Eslo; lia | rewrite Eshi; lia | exact UNa | exact HMETA ])
  end.
  (* The callee's stack: its astk_ok follows from the caller's journal (afn_pre_at): PFCLOSE_STK - o <= STK with
     o = spZ regs - 32 - sp0, and ly_bot + STK < sp0 + ASTACK gives ly_bot + PFCLOSE_STK < (spZ regs - 32) + ASTACK. *)
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  eapply SRr_bind;
  [ eapply (cl_callS B LAWS W rg mm _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdq k PFCLOSE_STK
      (asource_fp f) 2 (spZ regs - 32 - sp0) (Z_to_bv 64 (BASE + (symaddr ((Symbols.AsanUbsan.s_pcap_source_close + 0x48) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z))) []
      (fun ly3 S3 W3 regs3 mem3 md3 => getr regs3 10 = Z_to_bv 64 0 /\ Permutation (ablocks B ly3 S3) (l1 ++ l2) /\
         frames S3 = frames Sc /\ asource_none SEGS K (rdW W3 mem3) /\ garr8 SEGS (rdW W3 mem3) b C /\
         m_fds md3 = m_fds mdq /\ m_fs md3 = m_fs mdq) HJ Qsp);
    [ replace (spZ regs - 32 - sp0) with ((spZ regs / 16 - 2 - sp0 / 16) * 16)
        by (pose proof (Z_div_mod_eq_full (spZ regs) 16); pose proof (Z_div_mod_eq_full sp0 16); lia);
      apply Z.mod_mul; lia
    | lia | unfold PFCLOSE_STK; lia | unfold PFCLOSE_STK; lia
    | exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [lia | reflexivity]
    | rewrite unsigned_lit_small by lia; lia
    | exact Qs0
    | intros HPRE1; eapply SRr_mono;
      [ eapply (AFCLOSE W lyc Sc rg mm mdq [] f b M C p (l1 ++ l2) HPRE1 Q10' HPf HSRCc Hinb HMETAc
          ltac:(intros a Ha Ho He; exact (HRODc a Ha Ho He)) HEVf HUfc1 HUfc2)
      | cbv beta; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & Ha0 & HPm & Hfr3 & HSN & HGB & HFD & HFS);
        exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity|];
        split; [exact HJ1|]; split; [exact HP|];
        exact (conj Ha0 (conj HPm (conj Hfr3 (conj HSN (conj HGB (conj HFD HFS)))))) ]
    | exact HFPinc ]
  | ] end.
  cbv beta. intros W2 c2 Hwle2
    (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & Ha02 & HPerm2 & Hfrs2 & HSN2 & HGB2 & HFD2 & HFS2).
  replace (sp0 + (spZ regs - 32 - sp0)) with (spZ regs - 32) in HJc2 by lia.
  assert (HPm2 : Permutation (ablocks B lyc Sc) ((f, SRC_FILE_BLOCK) :: ablocks B ly2 S2)).
  { eapply Permutation_trans; [exact HPf|]. apply perm_skip. apply Permutation_sym. exact HPerm2. }
  pose proof HJc2 as (HAR2 & Hly2 & _).
  assert (Efa : forall c q, frame_addr ly2 c q = frame_addr lyc c q).
  { intros c q. unfold frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact Hin).
  assert (HPS2 : forall a, ps <= a < ps + 8 -> apresent (w_H W2) mem2 a).
  { intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 _)).
    right. right. right. exists cid, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd]. rewrite Efa. lia. }
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 3]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
      + apply (mbyte_of_aview SEGS). pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
        apply G1; unfold PFCLOSE_STK; lia.
      + intros _. apply (apresent_writable SEGS). apply Hpres2. lia.
    - eapply region_kept_frame_sub; [exact HJc2 | exact U10 | exact Hin | lia | lia | |].
      + intros a Ha Hf. destruct (AC.in_asource_fp f a Hf) as [H|H]; unfold SRC_FILE_BLOCK in H; lia.
      + intros a Ha. apply HPS2. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
  assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAE' : env_agree 32 (Ereg regs (cl_extra f)) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
  clear HE'.
  assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
  assert (U10' : bv_unsigned (ew E' 10) = ps) by (rewrite OLD by lia; exact U10).
  assert (E1' : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
  assert (E32' : ew E' 32 = Z_to_bv 64 SB_CL) by (rewrite OLD by lia; exact E32).
  assert (E10' : ew E' 10 = Z_to_bv 64 ps) by (rewrite OLD by lia; exact E10).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  assert (SHOK3 : sh_ok SEGS CBx cl_SH E' (mrestrict (w_H W2) mem2)).
  { apply (shent_ps_ok _ _ ps).
    + unfold CBx. rewrite (U_atom _ 32 SB_CL E32') by (unfold SB_CL; lia). reflexivity.
    + rewrite (U_atom _ 10 ps E10') by lia. reflexivity.
    + unfold kLowShadowBeg, kHighMemBeg. lia.
    + rewrite <- (aview_rd_of SEGS). apply (ra_frame (aview SEGS (w_H W) memc)); [exact Hsh|].
      intros x Hx. unfold shadow_of_addr.
      pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
      assert (Hx8 : x / 8 = ps / 8) by (apply AC.div8_in; [exact Hps8 | exact Hx]).
      pose proof (Z_div_mod_eq_full ps 8) as Eps. rewrite Hps8, Z.add_0_r in Eps.
      destruct (AC.div8_of_mul64 _ Hfa64) as [Efa8 Efa64].
      destruct (AC.div8_of_mul64 _ Hfb64) as [Efb8 Efb64].
      rewrite Hx8.
      rewrite (G4 cid pos (SHADOW_OFF + ps / 8) Hin).
      * apply UNa; [unfold SHADOW_OFF; lia | unfold SHADOW_OFF; intros [H|H]; lia].
      * right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Efa8, Efb8. unfold SHADOW_OFF. lia.
      * intros Hf. destruct (AC.in_asource_fp f _ Hf) as [H|H]; unfold SRC_FILE_BLOCK, SHADOW_OFF in H; lia. }
  clear SHOK.
  (* The second shadow check, ps->f = NULL, the restores and the return. *)
  paj_run_tok RUN HS HJ2 SHOK3 CLspan;
    [ cl_awr (spZ regs) sp0 Usp' U10'; right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; rewrite Efa; lia] |].
  cl_frame_kept HFr (spZ regs) ps Usp' U10' UN3. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth E' ssx (restrict _ msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRp;
    cbn [ms_mem restrict mkst] in HRp end.
  pose proof (field_of_region E' _ 10%nat ps _ _ _ _ _ 0 8%N (SLit 0) 0 HRp U10' ltac:(cbn; tauto)
    ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vps.
  rewrite Z.add_0_r in Vps. change (N.to_nat 8) with 8%nat in Vps.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  assert (Hb2 : In (b, Z.of_nat (length C)) (ablocks B ly2 S2)).
  { destruct (Permutation_in _ HPm2 Hinb) as [H|H]; [|exact H]. injection H as -> HlC.
    unfold SRC_FILE_BLOCK in *. lia. }
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 _ _ _ b (Z.of_nat (length C)) cid pos HAR2 Hb2 Hin2) as Dbf2.
  unfold zdisjoint in Dbf2. cbn [fst snd] in Dbf2. rewrite Efa in Dbf2.
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    prreg HS (1%bv : bv 5) R1;
    eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    unfold AC.tpcap_source_close_post;
    exists ly2, S2, (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite R1, E1', Hraw; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs (cl_extra f) HS); [exact HAE' | vm_compute; reflexivity]|];
    split; [exact Hfrs2|];
    split; [destruct (Z.eqb_spec f 0) as [H|H]; [contradiction|];
            eapply (asfm_close _ _ _ _ FM); [exact HJc2 | exact HPf | exact HPerm2]|];
    split; [repeat rewrite (proj1 (AC.wvb_fds_fs _ _ _)); rewrite HFD2; repeat rewrite (proj1 (AC.wvb_fds_fs _ _ _)); reflexivity|];
    split; [repeat rewrite (proj2 (AC.wvb_fds_fs _ _ _)); rewrite HFS2; repeat rewrite (proj2 (AC.wvb_fds_fs _ _ _)); reflexivity|];
    split; [unfold AC.tclose_fblk; destruct (Z.eqb_spec f 0) as [H|H]; [contradiction | exact HPm2]|];
    split; [exact Vps|];
    split;
    [ eapply (tclose_kept_call lyc Sc W memc mdc _ _ ly2 S2 W2 mem2 md2 (ms_mem msc) (spZ regs) ps cid pos f);
      [ exact HAR | exact Hin | exact Hfa1 | exact Hfa2 | exact Hsp_hi | exact Hinf | exact HPm2 | exact UNa | exact HJc2
      | exact UN3 | intros a Ha; apply Hpres3; lia | intros a Ha; left; exact Ha
      | intros a Ha; right; split; [exact Hf0 | exact Ha] ]
    | intros _; split;
      [ apply (asource_none_frame K (rdW W2 mem2)); [| exact HSN2];
        intros a Ha; pose proof (src_env_img a Ha) as Hk; apply (mbyte_of_aview SEGS); apply UN3; [lia | intros [H|H]; lia]
      | apply (garr8_frame SEGS (rdW W2 mem2) _ _ _ HGB2);
        intros a Ha; apply (mbyte_of_aview SEGS); apply UN3; [lia | intros [H|H]; lia] ] ]
  end.
Qed.

End e.
End d.
End b.

(* The sink-head instance is explicit on every exported theorem (a Theorem Labs lane, 21:57Z): the only global sink_head instance in
   this closure is the plain build's (lib/Reusable/YI5b.v src0_sink_head), so a caller must name this image's head
   instead of obtaining an instance by inference. The statement's own Arguments are lib/A's. *)
Arguments pb_pcap_source_closeX {fx rc} SK {PI}.
Arguments tclose_kept_nocall {rc} SK {PI}.
Arguments tclose_kept_call {rc} SK {PI}.
Arguments src_meta_inv_frame {rc} SK {PI}.
Arguments src_env_img {rc} SK {PI}.
Arguments cl_entry {fx rc} SK {PI}.

(* GUARD: SK must stay explicit. SK is passed by position; were it implicit again, the positional SK
   would land on the next argument and this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pb_pcap_source_closeX (fx:=fx) (rc:=rc) SK (PI:=PI)).
