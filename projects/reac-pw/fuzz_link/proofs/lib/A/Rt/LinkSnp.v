(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): link_snprintf, link's ONE snprintf contract
   (LinkSnpDef.v asnprintf_link_realizes, closed at link's instance as LinkSnpInst.v link_asnprintf_contract) at the
   trampoline LA_W_SNPRINTF 0x43088 (__interceptor_trampoline_snprintf -> ___interceptor_snprintf 0x46f20 ->
   ___interceptor_vsnprintf 0x46b30 -> musl vsnprintf 0x9a50c -> ___interceptor_vfprintf 0x46a7c -> musl vfprintf
   0x973e0 / printf_core 0x97590 -> sn_write 0x9a5d8), for its three call sites (remember 0x89ea8, LLVMFuzzerTestOneInput
   0x839c4 and 0x82b14).

   It is the port of the released disco chain at link's family and instance (LinkSnpPort.v
   link_snprintf_fm_PcapB: SnShared.sh_asnprintf_realizes at PcapB, FMsnprintfFmI.FF_fmP pf_link_piece, the canary cells
   FM_GOT_canary 0xa2658 / FM_canary 0x651c50, the image window [IMG_LO, IMG_TOP), the constants FMsnprintfCr.fm_cr,
   PC_snprintf 0x43088), with the chain's statements generalized in place by this sub-lane (the placement arm "between
   the stack-guard .got word and the guard", and the presence exception at the destination's in-image bytes), at the
   window LINK_SNP_STK = 2 * ESTACK = 8192 >= fm_glue_img + GXA_VF_DEPTH = 8160. Its premises are rebuilt from what
   the contract holds:
   - consts_view over fm_cr: LinkSnpRom.lsr_fm_cr_consts, from AR (in ecall_pre) and arodata_okP;
   - fm_cr and the canary cells miss the window and the destination (lsn_cr_out, lsn_gc_out, lsn_gv_out): every range
     of fm_cr lies in [0x10000, 0xa1000) (FMsnprintfCr.fm_cr_in_image) and the canary cells at 0xa2658 / 0x651c50; the
     window lies above kHighMemBeg <= ly_stk_lo (layout_ok's lo_top); the destination lies off the image (above
     IMG_TOP or below IMG_LO) or between the stack-guard .got word and the guard (link_snp_place);
   - the family: FF_link is FF_fmP pf_link_piece with SnFF's copy of pf_args_amem (lsn_FF);
   - pairwise disjointness of the window and the destination, and dest_ok: the contract's per-byte destination
     facts with K = 8192 >= ESTACK and its ownership premise;
   - the placement: link_snp_place's two off-image arms give the chain's first arm (off [IMG_LO, IMG_TOP)), its span
     arm the chain's second.
   The post's presence clause: the chain's exception `d <= a < d + w /\ in_img tfibsegs a` lies inside the contract's
   `d <= a < d + w /\ IMG_LO <= a < IMG_TOP` (ACeh.tfib_img_range).
   link_snprintf_journal_PcapB is LinkSnpJ.link_snprintf_journal (the call as one step of the caller's journal) at
   link's instance with this contract given, for the walks of the three callers.
   Proves function wrapper_snprintf at 0x43088 (PORT of libreac/fuzz_disco's released chain, rule 24 CONFIRM by
   a Theorem Labs lane; the statement generalized in place, see the commit). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m FMH_Base.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AD2l ACeh FMsnprintfFm FMsnprintfCr FMsnprintfFmI RT_pf_sh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkPfPiece LinkSnpDef LinkSnpInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkSnpRom LinkSnpPort LinkSnpJ.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI16.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the family ---- *)
Lemma lsn_args_amem : forall args ws, SnFF.pf_args_amem ws args -> RT_pf_sh.pf_args_amem ws args.
Proof.
induction args as [|x args IH]; intros ws H; [destruct ws; exact I|].
destruct ws as [|w ws]; [destruct x; exact I|].
destruct x; cbn in H |- *; try exact (IH ws H).
destruct H as [H1 H2]. exact (conj H1 (IH ws H2)).
Qed.

Lemma lsn_FF : forall rd rs f ws T, FF_link rd rs f ws T -> FMsnprintfFmI.FF_fmP pf_link_piece rd rs f ws T.
Proof.
intros rd rs f ws T (fmt & ps & args & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
exists fmt, ps, args.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
  (lsn_args_amem args ws H11))))))))))).
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- what lies apart from the window and the destination ---- *)
Lemma lsn_win_high : forall B ly S W regs mem md K,
  ecall_pre tfibsegs B ly S W regs mem md -> ly_stk_lo ly + K <= spZ regs -> 0 <= K ->
  YG0f.kHighMemBeg <= spZ regs - K.
Proof.
intros B ly S W regs mem md K HE HK HK0.
destruct HE as ((M & _) & _). apply am_layout in M. apply lo_top in M. lia.
Qed.

Lemma lsn_cr_out : forall B ly S W regs mem md K d w,
  ecall_pre tfibsegs B ly S W regs mem md -> ly_stk_lo ly + K <= spZ regs -> 0 <= K ->
  link_snp_place d w ->
  Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d w)) FMsnprintfCr.fm_cr.
Proof.
intros B ly S W regs mem md K d w HE HK HK0 HP.
pose proof (lsn_win_high B ly S W regs mem md K HE HK HK0) as HW.
apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) FMsnprintfCr.fm_cr_in_image r Hr) as Hb. cbv beta in Hb.
unfold link_snp_place, YImgTop.IMG_TOP, YImgTop.IMG_LO, LA_GOT_GUARD, LA_GUARD in HP. unfold YG0f.kHighMemBeg in HW.
unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd]; lia.
Qed.

Lemma lsn_gc_out : forall B ly S W regs mem md K d w,
  ecall_pre tfibsegs B ly S W regs mem md -> ly_stk_lo ly + K <= spZ regs -> 0 <= K ->
  link_snp_place d w ->
  Forall (zdisjoint (FM_GOT_canary, 8)) (snp_out K (spZ regs) d w).
Proof.
intros B ly S W regs mem md K d w HE HK HK0 HP.
pose proof (lsn_win_high B ly S W regs mem md K HE HK HK0) as HW.
unfold link_snp_place, YImgTop.IMG_TOP, YImgTop.IMG_LO, LA_GOT_GUARD, LA_GUARD in HP. unfold YG0f.kHighMemBeg in HW.
unfold snp_out, FM_GOT_canary. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold zdisjoint; cbn [fst snd]; lia.
Qed.

Lemma lsn_gv_out : forall B ly S W regs mem md K d w,
  ecall_pre tfibsegs B ly S W regs mem md -> ly_stk_lo ly + K <= spZ regs -> 0 <= K ->
  link_snp_place d w ->
  Forall (zdisjoint (FM_canary, 8)) (snp_out K (spZ regs) d w).
Proof.
intros B ly S W regs mem md K d w HE HK HK0 HP.
pose proof (lsn_win_high B ly S W regs mem md K HE HK HK0) as HW.
unfold link_snp_place, YImgTop.IMG_TOP, YImgTop.IMG_LO, LA_GOT_GUARD, LA_GUARD in HP. unfold YG0f.kHighMemBeg in HW.
unfold snp_out, FM_canary. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold zdisjoint; cbn [fst snd]; lia.
Qed.

(* ---- the window and the destination are apart: no destination byte lies in the window, and w >= 1 ---- *)
Lemma lsn_pairwise : forall K sp d w, 1 <= w -> 1 <= K ->
  (forall a, d <= a < d + w -> ~ (sp - K <= a < sp)) ->
  pairwise zdisjoint (snp_out K sp d w).
Proof.
intros K sp d w Hw HK Hout. apply (proj2 (pairwise_snp K sp d w)). unfold zdisjoint. cbn [fst snd].
destruct (Z_le_gt_dec (sp - K + K) d) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (d + w) (sp - K)) as [L2|L2]; [right; exact L2|].
exfalso. destruct (Z_le_gt_dec d (sp - K)) as [L3|L3].
- apply (Hout (sp - K)); lia.
- apply (Hout d); lia.
Qed.

(* ---- the top ---- *)
Theorem link_snprintf : link_asnprintf_contract.
Proof.
unfold link_asnprintf_contract, asnprintf_link_realizes, sh_asnprintf_link_realizes.
intros ly S W regs mem md d n f xs ws T cval HE HRO HK HWIN HPRE HNO HFRM.
destruct HPRE as (R10 & R11 & R12 & HGC & HGV & HVA & HXS & HDX & HFF & Hn & HT & Hd0 & Hdw & HWR & HAMR &
  HRAD & HSHV & HPL & HRT).
pose proof (LinkSnpDef.sn_len_pos (n - 1) T) as Hw1.
assert (HK0 : 0 <= LINK_SNP_STK) by (unfold LINK_SNP_STK, ESTACK; lia).
assert (HKE : ESTACK <= LINK_SNP_STK) by (unfold LINK_SNP_STK, ESTACK; lia).
assert (HK1 : 1 <= LINK_SNP_STK) by (unfold LINK_SNP_STK, ESTACK; lia).
assert (TOP : sh_asnprintf_realizes tfibsegs AD2l.PcapB (FMsnprintfFmI.FF_fmP pf_link_piece) LINK_SNP_STK
  FM_GOT_canary FM_canary YImgTop.IMG_LO YImgTop.IMG_TOP FMsnprintfCr.fm_cr PC_snprintf).
{ apply LinkSnpPort.link_snprintf_fm_PcapB. apply Z.leb_le. vm_compute. reflexivity. }
eapply SRr_mono.
{ refine (TOP ly S W regs mem md d n f xs ws T cval HE HK HWIN R10 R11 R12
    (LinkSnpRom.lsr_fm_cr_consts AD2l.PcapB AD2l.PcapB_syms ly S W mem md PCAP_RLO PCAP_RHI (proj1 HE) HRO)
    FMsnprintfCr.fm_cr_bounds
    (lsn_cr_out AD2l.PcapB ly S W regs mem md LINK_SNP_STK d (sn_len (n - 1) T) HE HK HK0 HPL)
    HGC HGV ltac:(unfold FM_GOT_canary; lia) ltac:(unfold FM_GOT_canary; lia)
    ltac:(unfold FM_canary; lia) ltac:(unfold FM_canary; lia)
    (lsn_gc_out AD2l.PcapB ly S W regs mem md LINK_SNP_STK d (sn_len (n - 1) T) HE HK HK0 HPL)
    (lsn_gv_out AD2l.PcapB ly S W regs mem md LINK_SNP_STK d (sn_len (n - 1) T) HE HK HK0 HPL)
    HVA HXS HDX (lsn_FF _ _ _ _ _ HFF) Hn HT Hd0 Hdw
    (lsn_pairwise LINK_SNP_STK (spZ regs) d (sn_len (n - 1) T) Hw1 HK1 (fun a Ha => proj2 (HWR a Ha)))
    _ HAMR HRAD HSHV _ HFRM).
  - (* dest_ok: writable, not the runtime's, outside the ESTACK window (inside the K window) *)
    intros a Ha. destruct (HWR a Ha) as [Hwr Hout]. split; [exact Hwr|]. split; [exact (HNO a Ha)|].
    intros X. apply Hout. lia.
  - (* the placement *)
    unfold link_snp_place in HPL. unfold zdisjoint, FM_GOT_canary, FM_canary, LA_GOT_GUARD, LA_GUARD in *.
    cbn [fst snd]. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia. }
cbv beta. intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hfp & Hfrm & HAR & Hpres & Hsame & Ha0 & Hby & Hkept & Hoff).
split; [reflexivity|]. exists fx', regs', mem', md'.
split; [reflexivity|].
split; [exact Hfp|]. split; [exact Hfrm|]. split; [exact HAR|]. split; [exact Hpres|].
split; [exact Hsame|]. split; [exact Ha0|]. split; [exact Hby|]. split; [exact Hkept|].
intros a Ha Hp Hx. apply (Hoff a Ha Hp). intros (Hd & Hi). apply Hx. split; [exact Hd|].
pose proof (ACeh.tfib_img_range a Hi) as R. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP.
cbv [pcap_img_end YImgTop.IMG_TOP] in R. lia.
Qed.

(* ---- the journal step at link's instance: LinkSnpJ.link_snprintf_journal at tfibsegs / PcapB / the relro window,
   its laws (YG0q.AR_laws_ok), its image bound (ACeh.tfib_segs_low) and its contract (link_snprintf) given; only
   the sink head SK stays a parameter ---- *)
Definition link_snprintf_journal_PcapB (SK : YI16.sink_head) :=
  LinkSnpJ.link_snprintf_journal SK tfibsegs AD2l.PcapB (YG0q.AR_laws_ok tfibsegs AD2l.PcapB) ACeh.tfib_segs_low
    PCAP_RLO PCAP_RHI link_snprintf.

End s.
