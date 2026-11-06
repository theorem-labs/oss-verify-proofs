From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge Cells.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel bcmp_c bcmp pcap_source_struct
  pcap_source_struct_next pcap_source_next_c pcap_source_next_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PGlue PInvCF PSROcf PContractCF PCut PImg PSteps
  PWalkDef PWalk PSegL2 PSegL3.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

Lemma gl_eq1 : forall (mem m0 m' : word -> option byte) lo hi, ro_agree rsegs mem ->
  munch [(lo, hi)] (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> mbyte rsegs m' x = mbyte rsegs mem x.
Proof.
  intros mem m0 m' lo hi HRO MU HR x Hx Hn.
  rewrite (mbyte_rel rsegs m' m0 x HR).
  rewrite (mbyte_rel rsegs mem (normalize rsegs mem) x (mem_rel_normalize rsegs mem HRO)).
  unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
  cbn [outside]. rewrite (unsigned_lit x Hx). split; [exact Hn | exact I].
Qed.

Lemma gl_rw : forall (m m' : word -> option byte) a cs,
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i) /\
     writable_at rsegs m' (a + i)) ->
  rw_cells rsegs m a cs -> rw_cells rsegs m' a cs.
Proof.
  intros m m' a cs H [[Hwf Hb] (Hw1 & Hw2 & _)].
  split; [split; [exact Hwf|]|].
  - apply (ss_bytes_mbyte rsegs m m' a (cells_bytes cs)); [|exact Hb].
    intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf. exact (proj1 (H i Hi)).
  - split; [exact Hw1|]. split; [exact Hw2|]. intros i Hi. exact (proj2 (H i Hi)).
Qed.

Lemma gl_norm_rw : forall (mem : word -> option byte) a cs, ro_agree rsegs mem -> rw_cells rsegs mem a cs ->
  SS_TOP <= a -> rw_cells rsegs (normalize rsegs mem) a cs.
Proof.
  intros mem a cs HRO H Ha. pose proof H as [_ (W0 & W1 & _)].
  apply (RoAdapt.rw_cells_norm rsegs mem a cs HRO H).
  intros i Hi. unfold wa. apply ss_ro_false. lia.
Qed.

Lemma gl_u8arr : forall (m : word -> option byte) a k, 0 <= a -> a + k <= 2 ^ 64 -> 0 <= k ->
  (forall i, 0 <= i < k -> writable_at rsegs m (a + i) /\ present m (a + i)) ->
  Arr.u8arr rsegs m a (ss_rd_list m a (Z.to_nat k)).
Proof.
  intros m a k Ha Hk Hk0 H. split.
  - split; [exact Ha|]. split; [rewrite ss_rd_list_len; lia|].
    intros j Hj. rewrite ss_rd_list_len in Hj. rewrite ss_rd_list_nth by exact Hj.
    destruct (H (Z.of_nat j) ltac:(lia)) as [_ [v Hv]]. unfold mrd, wa. rewrite Hv. reflexivity.
  - split; [exact Ha|]. split; [rewrite ss_rd_list_len; lia|].
    intros j Hj. rewrite ss_rd_list_len in Hj. exact (proj1 (H j ltac:(lia))).
Qed.

Section GL.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis HMALCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B (APIf rc).
Hypothesis HFREECF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Hypothesis HNEXTCF : forall fx : YK11.FPState, @pcap_source_next_contract_cf fx.

Lemma gl_win : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  forall a, g_S g - SLOT_K <= a < g_S g -> writable_at rsegs mem a.
Proof.
  intros g km hb L A regs mem md HF a Ha.
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HW).
  rewrite <- (sg_segs B APIf ra empty FF). exact (HW a Ha).
Qed.

Lemma seg_L_cf : forall i p, 0 <= i ->
  Hcut_cf B APIf ra (fun g => Inv_KL2 B APIf ra empty (i + 1) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g)
    (fun g => oKL2 (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g) ->
  Hcut_cf B APIf ra (Inv_K4 B APIf ra empty i p) (oK4 p).
Proof.
  intros i p _ HX g c HCAP (b & h & buf & km & HC).
  apply (cut_open_cf B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1c8)%Z) km (hb_bhu g b h buf) (P_K4 g i p b h buf) c (oK4 p g)
    (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP HPr.
  destruct HPr as (H9 & H18 & H20 & H21 & H22 & H24 & H25 & H27 & Hi0 & Hip & KQ & H12 & HFST & HGOOD &
    (HSTD & HGRD & (fl & mdv & HERR)) & HQ0 & HQB & HQ8 & HOFL & HMSTL & (pad & HPS) & H16 & HTS & HBUF).
  pose proof (ss_fr_bnd B APIf ra empty FF g km _ L A regs mem md HF) as (HSP & HM16 & HSK & HS47 & HRO).
  pose proof (ss_fr_stk B APIf ra empty FF g km _ L A regs mem md HF) as HSTK.
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  assert (HFB : (symaddr ImgPages.Plain.top) + 65536 - 160 <= fsp g /\ fsp g + 160 <= 2 ^ 47)
    by (unfold fsp, SLOT_FRAME, SS_TOP in *; lia).
  assert (USP : bv_unsigned (getr regs 2) = fsp g) by (rewrite HSP; apply unsigned_lit; lia).
  assert (HN26 : Z.of_nat (length (gF g)) < 2 ^ 26).
  { pose proof HF as (HGV & _). pose proof HGV as (Hn & _). unfold g_n in Hn. revert Hn. unfold gF.
    destruct (g_in g) as [|d l]; cbn [tl length]; intros; lia. }
  destruct (PWalk.kind_fit (gsw g) (gF g) (gcap g) (gq g p) KQ) as (_ & _ & EP & HPL & HI1).
  unfold flen in HPL.
  assert (HQG : p <= gq g p) by apply PWalk.psn_q_ge.
  destruct (mstl_frame _ _ _ _ _ _ _ HMSTL) as (cs & Hcs & HCS & HBF & _ & Hh0 & HMK).
  pose proof (gcap_range g) as (GC1 & GC2).
  assert (M24 : (fsp g + 24) mod 8 = 0) by (clear - HM16; Z.div_mod_to_equations; lia).
  assert (M32 : (fsp g + 32) mod 8 = 0) by (clear - HM16; Z.div_mod_to_equations; lia).
  assert (NQ0 : bytes_at rsegs (normalize rsegs mem) (symaddr Symbols.Plain.s_g_file_len) (le8 (wz (Z.of_nat (length (gF g))))))
    by exact (bytes_at_normalize rsegs mem _ _ HRO HQ0).
  assert (NB : bytes_at rsegs (normalize rsegs mem) b (gF g)) by exact (bytes_at_normalize rsegs mem _ _ HRO HBF).
  assert (NBUF : bytes_at rsegs (normalize rsegs mem) buf (rec_bytes (gsw g) (gF g) (gq g p)))
    by exact (bytes_at_normalize rsegs mem _ _ HRO HBUF).
  pose proof (gl_norm_rw mem _ _ HRO HPS ltac:(unfold SS_TOP; lia)) as NPS.
  pose proof (gl_norm_rw mem _ _ HRO H16 ltac:(unfold SS_TOP; lia)) as N16.
  pose proof (gl_norm_rw mem _ _ HRO HTS ltac:(unfold SS_TOP; lia)) as NTS.
  pose proof (mem_inv_normalize rsegs mem) as NMI.
  assert (NST : stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (fsp g + 160))
    by (replace (fsp g + 160) with (g_S g) by (unfold fsp, SLOT_FRAME; lia); exact HSTK).
  assert (NSK : skips (gsw g) (gF g) (gcap g) p (gq g p)) by (apply PWalk.psn_q_skips; lia).
  assert (EO : oK4 p g = psn_out h (gsw g) (gF g) (gcap g) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) ++
                         oKL2 (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g).
  { unfold oK4, oKL2, wrest, psn_out.
    replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (PWalk.walk_unfold_len (gsw g) (gF g) (gcap g) (pos_of (gsw g) (gF g) (gcap g) (gq g p))) by lia.
    rewrite <- app_assoc. reflexivity. }
  rewrite EO.
  apply (ss_mid_o_cf B APIf ra empty FF g km (hb_bhu g b h buf) L A regs mem md (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1c8)%Z))
    (QL (getr regs 2) (getr regs 3) (getr regs 4) (@fp_regs fx') (@fp_csr fx') (normalize rsegs mem)
        (g_S g - SLOT_K) (fsp g) (gcap g) buf b (gfirst g) (gq g p + 16 + incl (gsw g) (gF g) (gq g p)) i)
    _ (Post_o B APIf ra g) HF HP).
  - rewrite ss_mkR_of.
    eapply (pcap_L_x bcmp_holds) with (sw := gsw g) (Fc := gF g) (pad := pad) (lo := g_S g - SLOT_K)
      (sp_h := fsp g) (cap := gcap g) (buf := buf) (b := b) (p := p) (i := i) (Q := gq g p)
      (swz := gswz g) (h := h).
    all: first [ exact USP | eassumption | reflexivity | exact (gswz_01 g) | lia ].
  - intros ms (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 &
      x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m1 & -> & -> & -> & -> & -> &
      -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & MU & WM & _ & _ & _).
    do 3 eexists. split; [reflexivity|].
    split.
    + exists [(fsp g + 24, fsp g + 32)]. split; [exact MU|]. split; [exact WM|].
      intros x Hx O. left.
      apply (ss_fp1 g (fsp g + 24) (fsp g + 32) x); [unfold fsp, SLOT_FRAME; lia | unfold fsp, SLOT_FRAME; lia
        | exact Hx | exact O].
    + split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ XR HR HF'.
    destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 &
      x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m1 & EMS & E1 & E2 & E3 &
      E4 & E9 & E10 & E11 & E12 & E13 & E18 & E19 & E20 & E21 & E22 & E24 & E25 & E27 & MU & WM & _ & _ & TS1).
    injection EMS as ER Epc Em. subst R pc' m0'.
    subst x1 x2 x3 x4 x9 x10 x11 x12 x13 x18 x19 x20 x21 x22 x24 x25 x27.
    assert (G1 : getr regs' 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x440)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    assert (G9 : getr regs' 9 = wz (gcap g)) by (rewrite (ss_getr_eqv _ _ 9 XR); reflexivity).
    assert (G10 : getr regs' 10 = wz (fsp g + 32)) by (rewrite (ss_getr_eqv _ _ 10 XR); reflexivity).
    assert (G11 : getr regs' 11 = wz buf) by (rewrite (ss_getr_eqv _ _ 11 XR); reflexivity).
    assert (G12 : getr regs' 12 = wz (gcap g)) by (rewrite (ss_getr_eqv _ _ 12 XR); reflexivity).
    assert (G13 : getr regs' 13 = wz (fsp g + 24)) by (rewrite (ss_getr_eqv _ _ 13 XR); reflexivity).
    assert (G18 : getr regs' 18 = wz buf) by (rewrite (ss_getr_eqv _ _ 18 XR); reflexivity).
    assert (G19 : getr regs' 19 = wz (gfirst g)) by (rewrite (ss_getr_eqv _ _ 19 XR); reflexivity).
    assert (G20 : getr regs' 20 = wz b) by (rewrite (ss_getr_eqv _ _ 20 XR); reflexivity).
    assert (G21 : getr regs' 21 = wz 0xff00) by (rewrite (ss_getr_eqv _ _ 21 XR); reflexivity).
    assert (G22 : getr regs' 22 = wz (symaddr Symbols.Plain.s_g_file_len)) by (rewrite (ss_getr_eqv _ _ 22 XR); reflexivity).
    assert (G24 : getr regs' 24 = wz (gq g p + 16 + incl (gsw g) (gF g) (gq g p)))
      by (rewrite (ss_getr_eqv _ _ 24 XR); reflexivity).
    assert (G25 : getr regs' 25 = wz (i + 1)) by (rewrite (ss_getr_eqv _ _ 25 XR); reflexivity).
    assert (G27 : getr regs' 27 = wz (1000000 * 2 ^ 32)) by (rewrite (ss_getr_eqv _ _ 27 XR); reflexivity).
    pose proof (gl_eq1 mem m1 m' (fsp g + 24) (fsp g + 32) HRO MU HR) as EQ1.
    pose proof (gl_win _ _ _ _ _ _ _ _ HF') as WIN'.
    assert (HPS' : rw_cells rsegs m' (fsp g + 32)
      (ps_cells (wz h) (wz (gswz g)) (wz (orig (gsw g) (gF g) (gq g p)))
        (if tagged (gsw g) (gF g) (gq g p) then wz 1 else wz 0)
        (if tagged (gsw g) (gF g) (gq g p) then wz (rec_vid (gF g) (gq g p)) else wz 0) pad)).
    { apply (gl_rw mem m' _ _); [|exact HPS]. intros k Hk. cbn [cells_size csize ps_cells] in Hk.
      split; [apply EQ1; lia | apply WIN'; unfold fsp, SLOT_FRAME in *; lia]. }
    pose proof (RoAdapt.rw_cells_back rsegs m' m1 _ _ HR TS1) as HTS'.
    assert (HMSTL' : mstl m' h b (gF g) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) (wz 0) (wz 0)).
    { apply HMK.
      - apply (gl_rw mem m' h cs); [|exact HCS]. intros k Hk. rewrite Hcs in Hk.
        assert (IH : in_hb (hb_bhu g b h buf) (h + k))
          by (exists h, 1304; split; [unfold hb_bhu; cbn [In]; right; left; reflexivity | lia]).
        destruct (ss_hb_low B APIf ra empty FF g km _ L A regs' m' md (h + k) HF' HP IH) as (L1 & L2).
        destruct (ss_hb_blk B APIf ra empty FF g km (hb_bhu g b h buf) L A regs' m' md h 1304 HF' HP
          ltac:(unfold hb_bhu; cbn [In]; right; left; reflexivity)) as (HWH & _).
        destruct (HWH k ltac:(lia)) as (W & _).
        rewrite (sg_segs B APIf ra empty FF) in W.
        split; [apply EQ1; unfold fsp, SLOT_FRAME in *; lia | exact W].
      - apply (ss_bytes_mbyte rsegs mem m' b (gF g)); [|exact HBF]. intros k Hk.
        assert (IH : in_hb (hb_bhu g b h buf) (b + k))
          by (exists b, (gn g); split; [unfold hb_bhu; cbn [In]; left; reflexivity | unfold gn; lia]).
        destruct (ss_hb_low B APIf ra empty FF g km _ L A regs' m' md (b + k) HF' HP IH) as (L1 & L2).
        apply EQ1; unfold fsp, SLOT_FRAME in *; lia. }
    assert (HERR' : errf m' fl mdv).
    { apply (PImg.errf_keep B APIf ra empty FF mem m' fl mdv HERR). intros k Hk.
      rewrite (sg_segs B APIf ra empty FF). apply EQ1; unfold A_STDERR; lia. }
    assert (HSTD' : stdio_ok m').
    { apply (ss_stdio_keep B APIf ra empty FF L A mem m' md (FR_MR B APIf ra empty g km _ L A regs' m' md HF') HSTD).
      intros a Ha. rewrite (sg_segs B APIf ra empty FF). apply EQ1; unfold A_LIBC, A_OFL_LOCK in *; lia. }
    destruct (ss_hb_blk B APIf ra empty FF g km (hb_bhu g b h buf) L A regs' m' md buf (gbn g) HF' HP
      ltac:(unfold hb_bhu; cbn [In]; right; right; left; reflexivity)) as (HWB & HB4 & HBC & _).
    assert (HBJ : Arr.u8arr rsegs m' buf (ss_rd_list m' buf (Z.to_nat (gbn g)))).
    { apply gl_u8arr; [lia | lia | lia |]. intros k Hk. destruct (HWB k Hk) as (W & Pr & _).
      rewrite (sg_segs B APIf ra empty FF) in W. split; [exact W | exact Pr]. }
    assert (HBN : Z.of_nat (length (ss_rd_list m' buf (Z.to_nat (gbn g)))) = Z.max (gcap g) 1)
      by (rewrite ss_rd_list_len; unfold gbn in *; lia).
    eapply (ps_next_step_cf (fx:=fx') B APIf ra empty FF (HNEXTCF fx') g km (hb_bhu g b h buf) [(b, gn g); (h, 1304)]
      L A regs' m' md (fsp g + 32) buf (gcap g) (fsp g + 24) h (gswz g) b
      (pos_of (gsw g) (gF g) (gcap g) (gq g p)) fl mdv
      (wz (orig (gsw g) (gF g) (gq g p))) (if tagged (gsw g) (gF g) (gq g p) then wz 1 else wz 0)
      (if tagged (gsw g) (gF g) (gq g p) then wz (rec_vid (gF g) (gq g p)) else wz 0) (wz 0) (wz 0) (wz (-1)) pad
      (ss_rd_list m' buf (Z.to_nat (gbn g))) (gF g) (oKL2 (pos_of (gsw g) (gF g) (gcap g) (gq g p)) g)
      (Post_o B APIf ra g) HF' HP Hfrm).
    + rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + exact G10.
    + exact G11.
    + exact G12.
    + exact G13.
    + lia.
    + unfold fsp, SLOT_FRAME; lia.
    + exact M32.
    + exact HPS'.
    + unfold hb_bhu, gbn. apply Permutation_sym.
      exact (Permutation_cons_append [(b, gn g); (h, 1304)] (buf, Z.max (gcap g) 1)).
    + exact HBJ.
    + exact HBN.
    + lia.
    + intros _. split; [lia|]. split; [unfold fsp, SLOT_FRAME; lia|]. split; [exact M24|].
      split; [left; lia | exact HTS'].
    + intros _. split; [right; left; reflexivity|]. split; [left; reflexivity|].
      split; [exact HMSTL'|]. split; [exact (gswz_01 g) | exact HN26].
    + exact HERR'.
    + intros regs2 mem2 Ft fc2 mdv2 Hfc2 _ HF2 HRP2 HSTK2 _ HIMG2 HSTDI HERR2 HGRD2 _ HOP2.
      rewrite G1. apply (HX g _ HCAP). exists b, h, buf, km.
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc2) g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x440)%Z) km (hb_bhu g b h buf)
        (P_KL2 g (i + 1) (pos_of (gsw g) (gF g) (gcap g) (gq g p)) b h buf) L A regs2 mem2 md Hfc2 HF2 HP).
      rewrite (sg_segs B APIf ra empty FF) in HSTK2, HIMG2.
      assert (EQS : forall x, fsp g <= x < fsp g + 24 -> mbyte rsegs mem2 x = mbyte rsegs mem x).
      { intros x Hx. rewrite (HSTK2 x ltac:(unfold fsp, SLOT_FRAME in *; lia) ltac:(lia) ltac:(lia)).
        apply EQ1; lia. }
      assert (EQG : forall x, (symaddr Symbols.Plain.s_g_file_len) <= x < (symaddr Symbols.Plain.s_environ) -> mbyte rsegs mem2 x = mbyte rsegs mem x).
      { intros x Hx. rewrite (HIMG2 x ltac:(apply img_w_iff; right; left; lia) ltac:(unfold A_STDERR; lia)).
        apply EQ1; lia. }
      assert (EQO : forall x, A_OFL_HEAD <= x < A_OFL_HEAD + 8 -> mbyte rsegs mem2 x = mbyte rsegs mem x).
      { intros x Hx.
        rewrite (HIMG2 x ltac:(apply img_w_iff; right; right; lia) ltac:(unfold A_STDERR, A_OFL_HEAD in *; lia)).
        apply EQ1; unfold A_OFL_HEAD in *; lia. }
      pose proof (gl_win _ _ _ _ _ _ _ _ HF2) as WIN2.
      split; [transitivity (getr regs' 9); [exact (HRP2 9 ltac:(unfold callee_saved; lia)) | exact G9]|].
      split; [transitivity (getr regs' 18); [exact (HRP2 18 ltac:(unfold callee_saved; lia)) | exact G18]|].
      split; [transitivity (getr regs' 19); [exact (HRP2 19 ltac:(unfold callee_saved; lia)) | exact G19]|].
      split; [transitivity (getr regs' 20); [exact (HRP2 20 ltac:(unfold callee_saved; lia)) | exact G20]|].
      split; [transitivity (getr regs' 21); [exact (HRP2 21 ltac:(unfold callee_saved; lia)) | exact G21]|].
      split; [transitivity (getr regs' 22); [exact (HRP2 22 ltac:(unfold callee_saved; lia)) | exact G22]|].
      split; [transitivity (getr regs' 24); [exact (HRP2 24 ltac:(unfold callee_saved; lia)) |
        rewrite G24, EP; reflexivity]|].
      split; [transitivity (getr regs' 25); [exact (HRP2 25 ltac:(unfold callee_saved; lia)) | exact G25]|].
      split; [transitivity (getr regs' 27); [exact (HRP2 27 ltac:(unfold callee_saved; lia)) | exact G27]|].
      split; [exact (PWalk.walk_pos_step (gsw g) (gF g) (gcap g) p i Hip KQ)|].
      split; [rewrite EP; unfold gn; lia|].
      split; [exact HGOOD|].
      split; [split; [exact (HSTDI HSTD')|]; split; [exact HGRD2 | exists fl, mdv2; exact HERR2]|].
      split.
      { unfold q64. apply (ss_bytes_mbyte rsegs mem mem2); [|exact HQ0]. intros k Hk.
        rewrite length_le8 in Hk. apply EQG. lia. }
      split.
      { unfold q64. apply (ss_bytes_mbyte rsegs mem mem2); [|exact HQB]. intros k Hk.
        rewrite length_le8 in Hk. apply EQG. lia. }
      split.
      { unfold q64. apply (ss_bytes_mbyte rsegs mem mem2); [|exact HQ8]. intros k Hk.
        rewrite length_le8 in Hk. apply EQS. lia. }
      split.
      { unfold ofl_one in *. apply (gl_rw mem mem2 _ _); [|exact HOFL]. intros k Hk.
        cbn [cells_size csize] in Hk.
        split; [apply EQO; lia | exact (proj1 (img_w_wr mem2 (A_OFL_HEAD + k) ltac:(apply img_w_iff; right; right; lia)))]. }
      split.
      { apply (gl_rw mem mem2 _ _); [|exact H16]. intros k Hk. cbn [cells_size csize] in Hk.
        split; [apply EQS; lia | apply WIN2; unfold fsp, SLOT_FRAME in *; lia]. }
      exists (wz (orig (gsw g) (gF g) (gq g p))), (if tagged (gsw g) (gF g) (gq g p) then wz 1 else wz 0),
        (if tagged (gsw g) (gF g) (gq g p) then wz (rec_vid (gF g) (gq g p)) else wz 0), (wz (-1)), pad,
        (ss_rd_list m' buf (Z.to_nat (gbn g))).
      split; [exact HBN | exact (HOP2 ltac:(lia))].
Qed.

End GL.
