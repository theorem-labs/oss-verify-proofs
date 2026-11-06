From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01 YL0g YL0b YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c check_no_overread_c
fuzz_alloc_live_c fuzz_alloc_count_c fuzz_alloc_peak_reset_c EntSegA EntryDefs EntrySR EntBase EntGlue EntBig EntStg
EntStgD.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require fuzz_alloc_ran_out_c fuzz_alloc_ran_out_reset_c
  fuzz_alloc_most_c.
Import ListNotations.
Local Open Scope Z_scope.

(* The check_no_overread stage of LLVMFuzzerTestOneInput on the #102 plain pin (fuzz_preset.c:812-813 of #102,
   `if (check_no_overread(data, size)) return 0;`, plain 0x13778 called at 0x1367c).  Under cno_room and the two zero flag
   bytes the call returns a0 = 0 (check_no_overread_c), so the branch at 0x13680 falls through into EntSegA.ent_segB1:
   live = fuzz_alloc_live(), count = fuzz_alloc_count(), fuzz_alloc_peak_reset(), the arguments of parse_noting.
   The entry itself (the prologue, the size test, g_own_ran_out = 0, fuzz_alloc_ran_out_reset(), fuzz_alloc_most(...)) is
   EntBig.ent_start; entry_sr_of_cno joins it, EntBig.entry_big and this stage. *)

(* g_peak (8 bytes, LedgerCells.GL_PEAK) lies in a writable segment *)
Lemma ents1_peak_ro : forall a : word, G_PEAK <= bv_unsigned a < G_PEAK + 8 -> EMem.ro_addr rsegs a = false.
Proof.
  intros a Ha. unfold EMem.ro_addr. unfold G_PEAK in Ha.
  assert (E : bv_unsigned a = 0x347b8 \/ bv_unsigned a = 0x347b9 \/ bv_unsigned a = 0x347ba \/
              bv_unsigned a = 0x347bb \/ bv_unsigned a = 0x347bc \/ bv_unsigned a = 0x347bd \/
              bv_unsigned a = 0x347be \/ bv_unsigned a = 0x347bf) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; vm_compute; reflexivity.
Qed.

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

(* check_no_overread (0x13778) called at 0x1367c (stg_cno_st), on to the call of parse_noting *)
Theorem stg_cno_holds : stg_pjp_st (fx := fx) B API F -> stg_cno_st (fx := fx) B API F.
Proof.
  intros NEXT. unfold stg_cno_st.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md peak
    ENT INV R1 RK R8 R9 R10 R11 R21 FLG HEMP HE0 ROOM HN.
  pose proof RK as (R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof FLG as (FR & FO).
  pose proof ENT as (PREW & SYMS & SINKS & RAE & SLK & RO0 & TS & FRM0 & LED0 & CNT & HJ & RES0).
  pose proof PREW as (PRE & HNL & BLK & _).
  pose proof PRE as (MR0 & WF0 & BD0 & INIT0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & R10' & R11' & PAY & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & PAY0 & _).
  pose proof RS as (MRc & WFc & BDc & INc & KBc & _).
  pose proof alloc_ceiling_val as HCV.
  pose proof alloc_ceiling_lt as HCL.
  assert (HK : SLOT_K = 14176) by reflexivity.
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
      [rewrite <- HNL; exact R11 | exact HN | exact PB | | exact RES | exact (proj1 (ROOM HN)) | exact FR | exact FO].
    intros Hne. exists p, n. split; [|lia].
    apply KBc; [apply HPB, HNE, Hne | apply HNE, Hne | intros []]. }
  intros c' (fx' & L' & A' & regs' & mem' & md' & peak' & E1 & E2 & E3 & -> & FRM' & RP & RD' & INIT' & LED' & PK &
             PB' & _ & D1 & D2 & D3 & RES' & A0' & FR' & FO').
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
  assert (BL : EMem.bytes_at rsegs mem' G_LIVE (EMem.le8 (Z_to_bv 64 0))).
  { rewrite <- HSEG. apply (word_mem_le8 (ms_segs B) mem' G_LIVE 0); [exact WL | lia | unfold G_LIVE; lia | unfold G_LIVE; lia]. }
  assert (BC : EMem.bytes_at rsegs mem' G_COUNT (EMem.le8 (Z_to_bv 64 cnt1))).
  { rewrite <- HSEG. apply (word_mem_le8 (ms_segs B) mem' G_COUNT cnt1);
      [exact WC | lia | unfold G_COUNT; lia | unfold G_COUNT; lia]. }
  assert (HWG : forall m x, G_LIVE <= x < G_LIVE + 24 -> wview rsegs m (Z_to_bv 64 x) <> None).
  { intros m x Hx. apply (seg_win_wview rsegs G_LIVE 24 m x); [vm_compute; reflexivity | lia | exact Hx]. }
  assert (WP8 : EMem.wr_at rsegs mem' G_PEAK 8).
  { unfold G_PEAK. split; [lia|]. split; [lia|]. intros i Hi. apply HWG. unfold G_LIVE. lia. }
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
  assert (OUTW : forall x, 0 <= x < 2 ^ 64 -> (x < G_PEAK \/ G_PEAK + 8 <= x) ->
    0 <= x < 2 ^ 64 /\ EFrame.outside [(G_PEAK, G_PEAK + 8)] x).
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
    apply (kb_word_munch (ms_segs B) mem' m1 [(G_PEAK, G_PEAK + 8)] Ledger.G_FAIL (2 ^ 64 - 1) WFL MU).
    intros k Hk. apply OUTW; unfold Ledger.G_FAIL, G_PEAK; lia. }
  assert (RA1 : ro_agree (ms_segs B) m1).
  { intros a Ha. pose proof (proj1 RD' a Ha) as H0.
    destruct (kb_outside_dec [(G_PEAK, G_PEAK + 8)] (bv_unsigned a)) as [Ho|Hn].
    - unfold EMem.mrd in *. rewrite (MU a Ho). exact H0.
    - exfalso. pose proof (ents1_ns _ _ _ Hn) as Hr. rewrite HSEG in Ha.
      rewrite (ents1_peak_ro a Hr) in Ha. discriminate. }
  assert (ST2 : rstep B API CNO_K (spZ regs0 - 112) alloc_statics (fun _ => False) L' A' mem' md' L' A' m1 md').
  { apply (rstep_of_munch B API HSEG AX FG CNO_K (spZ regs0 - 112) alloc_statics (fun _ => False) L' A' mem' m1 md'
      [(G_PEAK, G_PEAK + 8)] MR' WF' BD' WR1 MU); [rewrite HSEG; exact WM | |].
    - intros x Hx Hn. right. pose proof (ents1_ns _ _ _ Hn) as Hr.
      unfold alloc_statics, Ledger.G_LIVE, Ledger.G_PEAK, Ledger.G_COUNT, Ledger.G_FAIL. unfold G_PEAK in Hr. lia.
    - intros x Hx Hob. destruct (kb_outside_dec [(G_PEAK, G_PEAK + 8)] x) as [Ho|Hn]; [exact Ho|exfalso].
      pose proof (ents1_ns _ _ _ Hn) as Hr.
      assert (Hs : alloc_statics x)
        by (unfold alloc_statics, Ledger.G_LIVE, Ledger.G_PEAK, Ledger.G_COUNT, Ledger.G_FAIL; unfold G_PEAK in Hr; lia).
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
    - intros a [[H|H]|H]; left; [left; exact H | right; left; exact H | left; exact H].
    - intros a Ha [[H|H]|H]; [pose proof (ent_statics_lo a H) | unfold fuzz_alloc_ran_out_c.G_RAN_OUT in H |
        pose proof (ent_statics_lo a H)]; lia.
    - intros a k _ _ (n' & []).
    - intros a k Hin _. destruct (rg_blk_in B API HSEG AX FG L A a k Hin) as (q0 & Hq0 & <-).
      assert (Hq1 : In (q0, k) (user_blocks A')) by (apply UB'; [exact Hq0 | intros []]).
      rewrite <- (PA' q0 k Hq0 Hq1). exact (rg_blk_of B API HSEG AX FG L' A' q0 k Hq1). }
  assert (FLG1 : ent_flags (ms_segs B) m1).
  { rewrite HSEG in FR', FO' |- *.
    apply (ents_flags_munch rsegs [(G_PEAK, G_PEAK + 8)] mem' m1 (conj FR' FO') MU);
      cbn [EFrame.disjoint_from]; unfold fuzz_alloc_ran_out_c.G_RAN_OUT, GL_OWN_RAN_OUT, G_PEAK;
      (split; [left; lia | exact I]). }
  assert (Q3 : getr regs1 3 = getr regs' 3) by (rewrite HGr; reflexivity).
  assert (Q4 : getr regs1 4 = getr regs' 4) by (rewrite HGr; reflexivity).
  assert (Q8 : getr regs1 8 = getr regs' 8) by (rewrite HGr; reflexivity).
  assert (Q9 : getr regs1 9 = getr regs' 9) by (rewrite HGr; reflexivity).
  assert (Q10 : getr regs1 10 = getr regs' 9) by (rewrite HGr; reflexivity).
  assert (Q11 : getr regs1 11 = getr regs' 8) by (rewrite HGr; reflexivity).
  assert (Q21 : getr regs1 21 = getr regs' 21) by (rewrite HGr; reflexivity).
  assert (Q22 : getr regs1 22 = getr regs' 22) by (rewrite HGr; reflexivity).
  assert (Q23 : getr regs1 23 = getr regs' 23) by (rewrite HGr; reflexivity).
  assert (Q24 : getr regs1 24 = getr regs' 24) by (rewrite HGr; reflexivity).
  assert (Q25 : getr regs1 25 = getr regs' 25) by (rewrite HGr; reflexivity).
  assert (Q26 : getr regs1 26 = getr regs' 26) by (rewrite HGr; reflexivity).
  assert (Q27 : getr regs1 27 = getr regs' 27) by (rewrite HGr; reflexivity).
  assert (P3 : getr regs' 3 = getr regs 3) by (apply (RR' 3); unfold callee_saved; lia).
  assert (P4 : getr regs' 4 = getr regs 4) by (apply (RR' 4); unfold callee_saved; lia).
  assert (P8 : getr regs' 8 = getr regs 8) by (apply (RR' 8); unfold callee_saved; lia).
  assert (P9 : getr regs' 9 = getr regs 9) by (apply (RR' 9); unfold callee_saved; lia).
  assert (P21 : getr regs' 21 = getr regs 21) by (apply (RR' 21); unfold callee_saved; lia).
  assert (P22 : getr regs' 22 = getr regs 22) by (apply (RR' 22); unfold callee_saved; lia).
  assert (P23 : getr regs' 23 = getr regs 23) by (apply (RR' 23); unfold callee_saved; lia).
  assert (P24 : getr regs' 24 = getr regs 24) by (apply (RR' 24); unfold callee_saved; lia).
  assert (P25 : getr regs' 25 = getr regs 25) by (apply (RR' 25); unfold callee_saved; lia).
  assert (P26 : getr regs' 26 = getr regs 26) by (apply (RR' 26); unfold callee_saved; lia).
  assert (P27 : getr regs' 27 = getr regs 27) by (apply (RR' 27); unfold callee_saved; lia).
  apply (NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A' regs1 m1 md' E1 E2 E3 ENT INV1).
  - rewrite HGr. reflexivity.
  - split; [rewrite HGr; reflexivity|].
    split; [rewrite Q3, P3; exact R3|]. split; [rewrite Q4, P4; exact R4|].
    split; [rewrite Q22, P22; exact R22|]. split; [rewrite Q23, P23; exact R23|].
    split; [rewrite Q24, P24; exact R24|]. split; [rewrite Q25, P25; exact R25|].
    split; [rewrite Q26, P26; exact R26 | rewrite Q27, P27; exact R27].
  - rewrite Q8, P8. exact R8.
  - rewrite Q9, P9. exact R9.
  - rewrite Q10, P9. exact R9.
  - rewrite Q11, P8. exact R8.
  - rewrite HGr. reflexivity.
  - rewrite HGr. reflexivity.
  - rewrite HGr. reflexivity.
  - rewrite Q21, P21. exact R21.
  - exact FLG1.
  - exact HEMP.
  - exact HE0.
  - exact ROOM.
  - exact HN.
  - exact (conj D1 (conj D2 D3)).
Qed.

(* The whole entry from 0x13628 (entry_sr_contract): a file over PRESET_FILE_MAX_BYTES returns 0 at once
   (EntBig.entry_big); otherwise EntBig.ent_start reaches the check_no_overread call with the frame and the two zero
   flag bytes that stg_cno_st asks for.  The only place that cites EntBig. *)
Theorem entry_sr_of_cno : stg_cno_st (fx := fx) B API F -> forall ra empty stk,
  entry_sr_contract (fx := fx) B API F ra empty stk.
Proof.
  intros STG ra empty stk SYMS GLOB SINKS RAE HEMP HE0 SLK j L A regs mem md p n pl peak cnt b0 HJ PREW GI RO TS FRM
    LED CNT RES ROOM.
  destruct (Z_le_gt_dec (ent_n pl) 0x300000) as [HN|Hb].
  2: exact (entry_big B API F HSEG FA ra empty stk SYMS GLOB SINKS RAE HEMP SLK j L A regs mem md p n pl peak cnt b0 HJ
       PREW GI RO TS FRM LED CNT RES ltac:(lia)).
  assert (ENT : ent_pre (fx := fx) B API F stk empty j L A regs mem md ra p n pl peak cnt b0)
    by exact (conj PREW (conj SYMS (conj SINKS (conj RAE (conj SLK (conj RO (conj TS (conj FRM (conj LED (conj CNT
      (conj HJ RES))))))))))).
  pose proof PREW as (PRE & _).
  pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R10 & R11 & _).
  apply (ent_start B API F HSEG FA HRST HMOST stk empty j L A regs mem md ra p n pl peak cnt b0 _ ENT HN).
  intros regs1 mem1 INV FLG Q1 Q2 Q3 Q4 Q22 Q23 Q24 Q25 Q26 Q27 Q8 Q9 Q10 Q11 Q21.
  apply (STG stk empty j L A regs mem md ra p n pl peak cnt b0 fx L A regs1 mem1 md peak ENT INV Q1).
  - exact (conj Q2 (conj Q3 (conj Q4 (conj Q22 (conj Q23 (conj Q24 (conj Q25 (conj Q26 Q27)))))))).
  - rewrite Q8. exact R11.
  - rewrite Q9. exact R10.
  - rewrite Q10. exact R10.
  - rewrite Q11. exact R11.
  - exact Q21.
  - exact FLG.
  - exact HEMP.
  - exact HE0.
  - exact ROOM.
  - exact HN.
Qed.

End C.
