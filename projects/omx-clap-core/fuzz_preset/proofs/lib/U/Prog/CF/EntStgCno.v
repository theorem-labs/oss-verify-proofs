From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YL0b YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c fuzz_alloc_live_c fuzz_alloc_count_c fuzz_alloc_peak_reset_c EntSegA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_c EntryDefs EntrySR EntBase EntGlue EntBig EntStg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require fuzz_alloc_ran_out_reset_c fuzz_alloc_most_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The check_no_overread stage of the #102 ubsan entry (check_no_overread 0x13868 called at 0x1376c, ra 0x13770), the
   walk on to parse_noting (0x13a38, ra 0x13798: ent_segB1), and the entry's start (EntBig.ent_start) into it.
   check_no_overread's contract (CF/check_no_overread_c.v) takes the two flag bytes 0 (ent_flags) and returns a0 = 0
   with both still 0. Ledger cells by LedgerCells' names; their numerals come from the names (the abbreviations below). *)
Local Abbreviation LIVEv := ltac:(let v := eval cbv in Ledger.G_LIVE in exact v) (only parsing).
Local Abbreviation PEAKv := ltac:(let v := eval cbv in Ledger.G_PEAK in exact v) (only parsing).
Local Abbreviation COUNTv := ltac:(let v := eval cbv in Ledger.G_COUNT in exact v) (only parsing).

Lemma ents1_peak_ro : forall a : word, Ledger.G_PEAK <= bv_unsigned a < Ledger.G_PEAK + 8 -> EMem.ro_addr rsegs a = false.
Proof.
  intros a Ha. unfold EMem.ro_addr.
  assert (E : bv_unsigned a = Ledger.G_PEAK \/ bv_unsigned a = Ledger.G_PEAK + 1 \/ bv_unsigned a = Ledger.G_PEAK + 2 \/
              bv_unsigned a = Ledger.G_PEAK + 3 \/ bv_unsigned a = Ledger.G_PEAK + 4 \/ bv_unsigned a = Ledger.G_PEAK + 5 \/
              bv_unsigned a = Ledger.G_PEAK + 6 \/ bv_unsigned a = Ledger.G_PEAK + 7) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; vm_compute; reflexivity.
Qed.

Lemma ents1_cno_W : forall a, cno_writes a -> ent_W a.
Proof. intros a [H|H]; [left; exact H | right; left; exact H]. Qed.

Lemma ents1_ns : forall lo hi x, ~ EFrame.outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x Hn.
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [exfalso; apply Hn; apply outside_one; lia|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [lia | exfalso; apply Hn; apply outside_one; lia].
Qed.

Lemma ents1_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity. Qed.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis CNO : forall fx' : YK11.FPState, @check_no_overread_contract fx' rc B API F.
Hypothesis HLIVE : fuzz_alloc_live_contract.
Hypothesis HCOUNT : fuzz_alloc_count_contract.
Hypothesis HRESET : fuzz_alloc_peak_reset_contract.
Hypothesis HRST : fuzz_alloc_ran_out_reset_c.fuzz_alloc_ran_out_reset_contract.
Hypothesis HMOST : fuzz_alloc_most_c.fuzz_alloc_most_contract.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Theorem stg_cno_holds : stg_pjp_st (fx := fx) B API F -> stg_cno_st (fx := fx) B API F.
Proof.
  intros NEXT. unfold stg_cno_st.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md peak
    ENT INV R1 RK R8 R9 R10 R11 R21 FL HEMP HE0 ROOM HN.
  pose proof RK as (R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof FL as (FLR & FLO).
  pose proof ENT as (PREW & SYMS & SINKS & RAE & SLK & RO0 & TS & FRM0 & LED0 & CNT & HJ & RES0).
  pose proof PREW as (PRE & HNL & BLK & _).
  pose proof PRE as (MR0 & WF0 & BD0 & INIT0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & R10' & R11' & PAY & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & PAY0 & _).
  pose proof RS as (MRc & WFc & BDc & INc & KBc & _).
  pose proof alloc_ceiling_val as HCV.
  pose proof alloc_ceiling_lt as HCL.
  assert (HK : SLOT_K = 14704) by reflexivity.
  assert (HCK : 112 + CNO_K <= SLOT_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (HCK0 : 0 <= CNO_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (HSP : spZ regs = spZ regs0 - 112) by (unfold spZ at 1; rewrite R2; apply ents1_uns; lia).
  assert (RET : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  pose proof (ent_env_mid B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    fx1 L A mem md [] peak cnt0 b0 regs CNO_K ENT INV HSP R4 RET HCK0 ltac:(lia)) as REN.
  assert (PR : 0 < p /\ p + n < 2 ^ 62 /\ (0 < n -> In (p, n) (blocks L0 A0))).
  { destruct PAY as [(Hn0 & ->) | (Hn0 & q & Hq & Eq)].
    - split; [lia|]. split; [lia | intros; lia].
    - pose proof (rg_blk_of B API HSEG AX FG L0 A0 q n Hq) as Hb. rewrite Eq in Hb.
      destruct (rg_blk B API HSEG AX FG L0 A0 mem0 md0 p n 0 MR0 Hb ltac:(lia)) as (_ & H1 & H2 & _).
      split; [lia|]. split; [lia | intros; exact Hb]. }
  destruct PR as (HP0 & HP1 & HPB).
  assert (PB : EMem.bytes_at (ms_segs B) mem p pl).
  { split; [lia|]. split; [lia|]. intros i Hi.
    change (EMem.mrd (ms_segs B) mem (EMem.wa (p + Z.of_nat i))) with (mbyte (ms_segs B) mem (p + Z.of_nat i)).
    rewrite (PAY0 (Z.of_nat i)) by lia. rewrite (BLK (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity. }
  assert (HCN : Z.of_nat j <= 3) by lia.
  assert (HNE : pl <> [] -> 0 < n) by (intros Hne; rewrite HNL; destruct pl; [contradiction | cbn [length]; lia]).
  eapply SR_bind.
  { apply (CNO fx1 L A regs mem md [] peak cnt0 b0 p pl REN LED ltac:(lia) R10);
      [rewrite <- HNL; exact R11 | exact HN | exact PB | | exact RES | exact (proj1 (ROOM HN)) | exact FLR | exact FLO].
    intros Hne. exists p, n. split; [|lia].
    apply KBc; [apply HPB, HNE, Hne | apply HNE, Hne | intros []]. }
  intros c' (fx' & L' & A' & regs' & mem' & md' & peak' & E1 & E2 & E3 & -> & FRM' & RP & RD' & INIT' & LED' & PK &
             PB' & _ & D1 & D2 & D3 & RES' & A0' & GR' & GO').
  rewrite R1.
  set (cnt1 := cnt0 + 3 * Z.of_nat (ncalls jr_strtod (zb pl))) in *.
  pose proof RP as (MR' & WF' & BD' & _ & _ & _ & _ & UB' & PA' & RR' & _).
  pose proof (rstep_of_rpost B API HSEG AX FG CNO_K L A regs mem md cno_writes (fun _ _ => False)
    L' A' regs' mem' md' RP) as ST1.
  rewrite HSP in ST1.
  pose proof ST1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WR1).
  pose proof LED' as ((WL & WP & WC & WFL) & HPK & HC & HFL & _).
  cbn [lsum] in WL, HPK.
  assert (G2' : getr regs' 2 = Z_to_bv 64 (spZ regs0 - 112))
    by (etransitivity; [apply (RR' 2); unfold callee_saved; lia | exact R2]).
  assert (BL : EMem.bytes_at rsegs mem' LIVEv (EMem.le8 (Z_to_bv 64 0))).
  { rewrite <- HSEG. apply (word_mem_le8 (ms_segs B) mem' LIVEv 0); [exact WL | lia | lia | lia]. }
  assert (BC : EMem.bytes_at rsegs mem' COUNTv (EMem.le8 (Z_to_bv 64 cnt1))).
  { rewrite <- HSEG. apply (word_mem_le8 (ms_segs B) mem' COUNTv cnt1); [exact WC | lia | lia | lia]. }
  assert (HWG : forall m x, LIVEv <= x < LIVEv + 24 -> wview rsegs m (Z_to_bv 64 x) <> None).
  { intros m x Hx. apply (seg_win_wview rsegs LIVEv 24 m x); [vm_compute; reflexivity | lia | exact Hx]. }
  assert (WP8 : EMem.wr_at rsegs mem' PEAKv 8).
  { split; [lia|]. split; [lia|]. intros i Hi. apply HWG. lia. }
  destruct (kb_md B API L' A' mem' md' MR') as (Hh & Hz).
  eapply (ent_kA B HSEG fx' regs' _ mem' md' _ _ Hh Hz).
  { unfold rmk. rewrite G2', A0'.
    exact (ent_segB1 HLIVE HCOUNT HRESET (getr regs' 1) (getr regs' 3) (getr regs' 4) (getr regs' 5) (getr regs' 6)
      (getr regs' 7) (getr regs' 8) (getr regs' 9) (getr regs' 11) (getr regs' 12) (getr regs' 13)
      (getr regs' 14) (getr regs' 15) (getr regs' 16) (getr regs' 17) (getr regs' 18) (getr regs' 19) (getr regs' 20)
      (getr regs' 21) (getr regs' 22) (getr regs' 23) (getr regs' 24) (getr regs' 25) (getr regs' 26) (getr regs' 27)
      (getr regs' 28) (getr regs' 29) (getr regs' 30) (getr regs' 31) (@fp_regs fx') (@fp_csr fx') mem'
      (spZ regs0 - 112) (Z_to_bv 64 0) (Z_to_bv 64 cnt1) BL BC WP8). }
  { intros ms' (m' & _ & _ & _ & _ & _ & E). eexists _, _, _. exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  destruct HQ as (m1 & MU & WM & BP1 & BL1 & BC1 & E).
  ent_inj E R pc' mem1.
  assert (OUTW : forall x, 0 <= x < 2 ^ 64 -> (x < PEAKv \/ PEAKv + 8 <= x) ->
    0 <= x < 2 ^ 64 /\ EFrame.outside [(PEAKv, PEAKv + 8)] x).
  { intros x Hx Ho. split; [exact Hx | apply outside_one; exact Ho]. }
  assert (LED1 : ledger B L' A' m1 [] 0 cnt1 (2 ^ 64 - 1)).
  { rewrite <- HSEG in BP1, BL1, BC1.
    pose proof (bytes_at_le8_word (ms_segs B) m1 _ _ BP1) as W1.
    pose proof (bytes_at_le8_word (ms_segs B) m1 _ _ BL1) as W2.
    pose proof (bytes_at_le8_word (ms_segs B) m1 _ _ BC1) as W3.
    rewrite ents1_uns in W1 by lia. rewrite ents1_uns in W2 by lia. rewrite ents1_uns in W3 by lia.
    unfold ledger, alloc_words.
    split; [|split; [cbn [lsum]; lia | split; [lia | split; [lia | split; constructor]]]].
    split; [exact W2|]. split; [exact W1|]. split; [exact W3|].
    apply (kb_word_munch (ms_segs B) mem' m1 [(PEAKv, PEAKv + 8)] Ledger.G_FAIL (2 ^ 64 - 1) WFL MU).
    intros k Hk. apply OUTW; unfold Ledger.G_FAIL; lia. }
  assert (RA1 : ro_agree (ms_segs B) m1).
  { intros a Ha. pose proof (proj1 RD' a Ha) as H0.
    destruct (kb_outside_dec [(PEAKv, PEAKv + 8)] (bv_unsigned a)) as [Ho|Hn].
    - unfold EMem.mrd in *. rewrite (MU a Ho). exact H0.
    - exfalso. pose proof (ents1_ns _ _ _ Hn) as Hr. rewrite HSEG in Ha.
      rewrite (ents1_peak_ro a Hr) in Ha. discriminate. }
  assert (ST2 : rstep B API CNO_K (spZ regs0 - 112) alloc_statics (fun _ => False) L' A' mem' md' L' A' m1 md').
  { apply (rstep_of_munch B API HSEG AX FG CNO_K (spZ regs0 - 112) alloc_statics (fun _ => False) L' A' mem' m1 md'
      [(PEAKv, PEAKv + 8)] MR' WF' BD' WR1 MU); [rewrite HSEG; exact WM | |].
    - intros x Hx Hn. right. pose proof (ents1_ns _ _ _ Hn) as Hr.
      unfold alloc_statics, Ledger.G_LIVE, Ledger.G_PEAK, Ledger.G_COUNT, Ledger.G_FAIL. lia.
    - intros x Hx Hob. destruct (kb_outside_dec [(PEAKv, PEAKv + 8)] x) as [Ho|Hn]; [exact Ho|exfalso].
      pose proof (ents1_ns _ _ _ Hn) as Hr.
      assert (Hs : alloc_statics x)
        by (unfold alloc_statics, Ledger.G_LIVE, Ledger.G_PEAK, Ledger.G_COUNT, Ledger.G_FAIL; lia).
      destruct (statics_img B API HSEG AX FG x Hs) as (Himg & Hno).
      destruct Hob as [Ho | (q & k & Hb & Hq)].
      + exact (Hno L' A' mem' md' MR' Ho).
      + destruct (rg_blk_in B API HSEG AX FG L' A' q k Hb) as (q' & Hq' & Eq).
        apply (ax_blocks_img AX L' A' mem' md' q' k (x - q) MR' Hq'); [lia|].
        rewrite Eq. replace (q + (x - q)) with x by lia. exact Himg. }
  assert (ST : rstep B API CNO_K (spZ regs0 - 112) (fun x => cno_writes x \/ alloc_statics x)
                 (fun a : Z => exists k : Z, (fun _ _ : Z => False) a k) L A mem md L' A' m1 md').
  { apply (rstep_seq B API HSEG AX FG CNO_K (spZ regs0 - 112) cno_writes alloc_statics
      (fun a : Z => exists k : Z, (fun _ _ : Z => False) a k) (fun _ => False) L A mem md L' A' mem' md' L' A' m1 md'
      ST1 ST2).
    intros a k _ _ _ H. exact H. }
  assert (INV1 : ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx' L' A' m1 md' [] 0 cnt1 (ent_b1 F b0 pl E1 E2 E3)).
  { apply (ent_after B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md [] peak
      cnt0 b0 CNO_K _ _ fx' L' A' m1 md' [] 0 cnt1 (ent_b1 F b0 pl E1 E2 E3) ENT INV ST HCK0 ltac:(lia));
      [| | | | exact RA1 | exact FRM' | exact LED1 | exact RES'].
    - intros a [H|H]; left; [exact (ents1_cno_W a H) | left; exact H].
    - intros a Ha [H|H]; [pose proof (ent_W_lo a (ents1_cno_W a H)) | pose proof (ent_statics_lo a H)]; lia.
    - intros a k _ _ (n' & []).
    - intros a k Hin _. destruct (rg_blk_in B API HSEG AX FG L A a k Hin) as (q0 & Hq0 & <-).
      assert (Hq1 : In (q0, k) (user_blocks A')) by (apply UB'; [exact Hq0 | intros []]).
      rewrite <- (PA' q0 k Hq0 Hq1). exact (rg_blk_of B API HSEG AX FG L' A' q0 k Hq1). }
  assert (Q3 : getr regs1 3 = getr regs' 3) by (rewrite HGr; reflexivity).
  assert (Q4 : getr regs1 4 = getr regs' 4) by (rewrite HGr; reflexivity).
  assert (Q8 : getr regs1 8 = getr regs' 8) by (rewrite HGr; reflexivity).
  assert (Q9 : getr regs1 9 = getr regs' 9) by (rewrite HGr; reflexivity).
  assert (Q10 : getr regs1 10 = getr regs' 9) by (rewrite HGr; reflexivity).
  assert (Q11 : getr regs1 11 = getr regs' 8) by (rewrite HGr; reflexivity).
  assert (K3 : getr regs1 3 = getr regs 3)
    by (transitivity (getr regs' 3); [rewrite HGr; reflexivity | apply (RR' 3); unfold callee_saved; lia]).
  assert (K4 : getr regs1 4 = getr regs 4)
    by (transitivity (getr regs' 4); [rewrite HGr; reflexivity | apply (RR' 4); unfold callee_saved; lia]).
  assert (K8 : getr regs1 8 = getr regs 8)
    by (transitivity (getr regs' 8); [rewrite HGr; reflexivity | apply (RR' 8); unfold callee_saved; lia]).
  assert (K9 : getr regs1 9 = getr regs 9)
    by (transitivity (getr regs' 9); [rewrite HGr; reflexivity | apply (RR' 9); unfold callee_saved; lia]).
  assert (K21 : getr regs1 21 = getr regs 21)
    by (transitivity (getr regs' 21); [rewrite HGr; reflexivity | apply (RR' 21); unfold callee_saved; lia]).
  assert (K22 : getr regs1 22 = getr regs 22)
    by (transitivity (getr regs' 22); [rewrite HGr; reflexivity | apply (RR' 22); unfold callee_saved; lia]).
  assert (K23 : getr regs1 23 = getr regs 23)
    by (transitivity (getr regs' 23); [rewrite HGr; reflexivity | apply (RR' 23); unfold callee_saved; lia]).
  assert (K24 : getr regs1 24 = getr regs 24)
    by (transitivity (getr regs' 24); [rewrite HGr; reflexivity | apply (RR' 24); unfold callee_saved; lia]).
  assert (K25 : getr regs1 25 = getr regs 25)
    by (transitivity (getr regs' 25); [rewrite HGr; reflexivity | apply (RR' 25); unfold callee_saved; lia]).
  assert (K26 : getr regs1 26 = getr regs 26)
    by (transitivity (getr regs' 26); [rewrite HGr; reflexivity | apply (RR' 26); unfold callee_saved; lia]).
  assert (K27 : getr regs1 27 = getr regs 27)
    by (transitivity (getr regs' 27); [rewrite HGr; reflexivity | apply (RR' 27); unfold callee_saved; lia]).
  assert (FL1 : ent_flags (ms_segs B) m1).
  { unfold ent_flags. rewrite HSEG in GR', GO' |- *.
    split; [apply (EFrame.bytes_at_transport rsegs [(PEAKv, PEAKv + 8)] mem' m1 _ _ GR' MU) |
            apply (EFrame.bytes_at_transport rsegs [(PEAKv, PEAKv + 8)] mem' m1 _ _ GO' MU)];
      cbn [EFrame.disjoint_from]; rewrite EMem.length_le1;
      unfold fuzz_alloc_ran_out_c.G_RAN_OUT, GL_OWN_RAN_OUT; (split; [lia | exact I]). }
  apply (NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A' regs1 m1 md' E1 E2 E3 ENT INV1).
  - rewrite HGr. reflexivity.
  - split; [rewrite HGr; reflexivity|].
    split; [rewrite K3; exact R3|]. split; [rewrite K4; exact R4|].
    split; [rewrite K22; exact R22|]. split; [rewrite K23; exact R23|].
    split; [rewrite K24; exact R24|]. split; [rewrite K25; exact R25|].
    split; [rewrite K26; exact R26 | rewrite K27; exact R27].
  - rewrite K8. exact R8.
  - rewrite K9. exact R9.
  - rewrite Q10, <- Q9, K9. exact R9.
  - rewrite Q11, <- Q8, K8. exact R8.
  - rewrite HGr. reflexivity.
  - rewrite HGr. reflexivity.
  - rewrite HGr. reflexivity.
  - rewrite K21. exact R21.
  - exact FL1.
  - exact HEMP.
  - exact HE0.
  - exact ROOM.
  - exact HN.
  - exact (conj D1 (conj D2 D3)).
Qed.

Theorem entry_start : stg_cno_st (fx := fx) B API F -> forall ra empty stk,
  slot_syms B -> slot_globals B -> slot_sinks B -> ra mod 2 = 0 -> 0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  SLOT_K <= stk ->
  forall (j : nat) L A regs mem md p n pl (peak cnt : Z) (b0 : rf_R F),
    (j < 4)%nat ->
    lib_pre_w B API stk empty L A regs mem md ra p n pl ->
    G_img_c B frame_RELRO mem -> ro_agree (ms_segs B) mem -> spZ regs <= TASK_SIZE -> frm_zero fp_csr ->
    ledger B L A mem [] peak cnt (2 ^ 64 - 1) -> cnt <= Z.of_nat j * 2 ^ 60 ->
    rf_ok F A b0 -> entry_rooms F b0 cnt pl -> ent_n pl <= 0x300000 ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 LLVMFUZZERTESTONEINPUT) mem (seg_rom (ms_segs B))) md)
      (ent_sr_post B API F stk j L A regs mem md ra p n pl cnt b0).
Proof.
  intros STG ra empty stk SYMS _ SINKS RAE HEMP HE0 SLK j L A regs mem md p n pl peak cnt b0 HJ PREW _ RO TS FRM LED
    CNT RES ROOM HN.
  assert (ENT : ent_pre (fx := fx) B API F stk empty j L A regs mem md ra p n pl peak cnt b0)
    by exact (conj PREW (conj SYMS (conj SINKS (conj RAE (conj SLK (conj RO (conj TS (conj FRM (conj LED (conj CNT
      (conj HJ RES))))))))))).
  pose proof PREW as (PRE & _).
  pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R10 & R11 & _).
  apply (ent_start B API F HSEG FA HRST HMOST stk empty j L A regs mem md ra p n pl peak cnt b0 _ ENT HN).
  intros regs1 mem1 INV FL G1 G2 G3 G4 G22 G23 G24 G25 G26 G27 G8 G9 G10 G11 G21.
  apply (STG stk empty j L A regs mem md ra p n pl peak cnt b0 fx L A regs1 mem1 md peak ENT INV).
  - exact G1.
  - unfold ent_rk. repeat split; assumption.
  - rewrite G8. exact R11.
  - rewrite G9. exact R10.
  - rewrite G10. exact R10.
  - rewrite G11. exact R11.
  - exact G21.
  - exact FL.
  - exact HEMP.
  - exact HE0.
  - exact ROOM.
  - exact HN.
Qed.

Theorem entry_sr_of_cno : stg_cno_st (fx := fx) B API F -> forall ra empty stk,
  entry_sr_contract (fx := fx) B API F ra empty stk.
Proof.
  intros STG ra empty stk SYMS GLOB SINKS RAE HEMP HE0 SLK j L A regs mem md p n pl peak cnt b0 HJ PREW GI RO TS FRM
    LED CNT RES ROOM.
  destruct (Z_le_gt_dec (ent_n pl) 0x300000) as [Hs|Hb].
  - exact (entry_start STG ra empty stk SYMS GLOB SINKS RAE HEMP HE0 SLK j L A regs mem md p n pl peak cnt b0 HJ PREW
      GI RO TS FRM LED CNT RES ROOM Hs).
  - exact (entry_big B API F HSEG FA ra empty stk SYMS GLOB SINKS RAE HEMP SLK j L A regs mem md p n pl peak cnt b0 HJ
      PREW GI RO TS FRM LED CNT RES ltac:(lia)).
Qed.

End C.
