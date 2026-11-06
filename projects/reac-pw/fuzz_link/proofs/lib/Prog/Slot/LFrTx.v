(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: its text_buf and text_of calls at the SR
   level (S-FR item 6, part 2), from a CUT at the callee's entry to a CUT at the return address.
   - lfr_text_buf: text_buf(cap) at 0x14fb0 (op_read: kc at 0x13e4c, ra 0x13e50; ac at 0x13e58, ra 0x13e5c); cap = 0
     answers NULL and nothing changes, else a fresh block of cap + 1 bytes (the cap bytes and the guard byte, all
     0x5a) joins the slot's heap blocks.
   - lfr_text_of: text_of(cursor, own) at 0x15aa8 (op_decide 0x13aa4 / 0x13ab4: a0 = sp+0x40, a1 = sp+0x78 /
     sp+0x50; op_write 0x13fb4: a1 = sp+0x78); the answer is a C string with its slack bytes up to the next
     multiple of 8 (the word loads of the deciders and of strlen read them, a Theorem Labs lane's al_ok), either in .rodata
     (own = 0) or the fresh block *own (own <> 0, which joins hb).
   The callee contracts are Section hypotheses: TBUF is lib/Prog/text_buf_c.v text_buf_contract and TOF is
   lib/Prog/text_of_c.v text_of_contract, both as they stand (with AMEND-slot items 11, 12 and 13: the old blocks
   kept, the init flag, the footprint of the block's real size, and the table arm's string with strlen's slack in
   .rodata, `s + |t| + 8 <= A_RO_END`). The frame step is LFrTxA.ltx_call over LFrCall.lfr_call. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import text_buf_c text_of_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrCall LFrRun LFrAl LFrTxA.
Import ListNotations.
Local Open Scope Z_scope.

Section TX.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.
Local Notation segs := (ms_segs B).
Local Notation MR := (aa_MR API).

Hypothesis TBUF : forall fx' : YK11.FPState, @text_buf_contract fx' rc B API.
Hypothesis TOF : forall fx' : YK11.FPState, @text_of_contract fx' rc B API.

Ltac ltx_unf := unfold apart, apart_gnl, SLOT_STACK_Z, A_G_NL, NK_SIZE, A_LONG_ALIAS, A_ERRNO, A_TP, ERRNO_TP_OFF,
  A_RO_LO, A_RO_END, SLOT_STACK, SLOT_FRAME, LF_TOP, TASK_SIZE, A_TEXTS, TEXTS_N in *.

(* ==========================================================================
   1. text_buf
   ========================================================================== *)

Lemma lfr_text_buf : forall g hb T cap ra (P : machine_state -> Prop) (P' : Z -> machine_state -> Prop) c,
  0 <= cap < 40 -> lroom_hb hb -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  CUT B API g TEXT_BUF hb T P c ->
  (forall ms, P ms -> getr (ms_regs ms) 1 = Z_to_bv 64 ra /\
     getr (ms_regs ms) 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME) /\ getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\
     getr (ms_regs ms) 10 = Z_to_bv 64 cap) ->
  (forall R F fc m regs' m' r,
     P (MS R F (Z_to_bv 64 TEXT_BUF) fc None m (seg_rom rsegs)) ->
     regs_preserved R regs' -> getr regs' 10 = Z_to_bv 64 r ->
     lcarry (lkeep B g hb) m m' -> lpost_mem g m' ->
     (cap = 0 -> r = 0) ->
     (cap <> 0 -> r <> 0 /\ lfresh B g hb r (cap + 1) /\ tbuf_at m' r cap (repeat (zb GUARD_BYTE) (Z.to_nat cap))) ->
     P' r (MS regs' F (Z_to_bv 64 ra) fc None m' (seg_rom rsegs))) ->
  SR (ms_segs B) c (fun c' => exists r, CUT B API g ra (opt_hb r (cap + 1) hb) T (P' r) c').
Proof.
  intros g hb T cap ra P P' c Hcap Hroom Hra Hra2 HCUT HPR HK.
  pose proof (ltx_segs B API FF) as SEG.
  apply (cut_open B API g TEXT_BUF hb T P c _ HCUT).
  intros fx' L A regs mem md Hfz HF Heqv.
  destruct (lc_rep P fx' regs TEXT_BUF mem Heqv) as (R & HPc & HR).
  destruct (HPR _ HPc) as (G1 & G2 & G4 & G10). cbn [ms_regs MState.MS] in G1, G2, G4, G10.
  assert (R1 : YK11.getr regs 1 = Z_to_bv 64 ra) by (rewrite (lc_getr R regs 1 HR); exact G1).
  assert (R2 : YK11.getr regs 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME)) by (rewrite (lc_getr R regs 2 HR); exact G2).
  assert (R4 : YK11.getr regs 4 = Z_to_bv 64 A_TP) by (rewrite (lc_getr R regs 4 HR); exact G4).
  assert (R10 : YK11.getr regs 10 = Z_to_bv 64 cap) by (rewrite (lc_getr R regs 10 HR); exact G10).
  assert (B1 : getr regs 1 = Z_to_bv 64 ra) by exact R1.
  assert (HKb : 0 <= TEXT_BUF_K <= SLOT_STACK - SLOT_FRAME)
    by (unfold TEXT_BUF_K, ALLOC_STACK, SLOT_STACK, SLOT_FRAME; lia).
  destruct (la_pre B API FF g hb T L A regs mem md ra TEXT_BUF_K HF Hra Hra2 HKb R1 R2 R4) as (HSP & PRE).
  pose proof HF as (HGV & HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & HRS & _).
  pose proof (@lc_ceil rc) as [HC1 HC2]. unfold LF_TOP in HC1.
  pose proof (TBUF fx' L A regs mem md (sb_hb (lg_b g) hb) cap SEG PRE HRO R10 Hcap HRS
    (lroom B API g hb (cap + 1) HGV Hroom ltac:(lia))) as HSR.
  eapply SR_mono; [exact HSR|].
  intros c' (L' & A' & regs' & mem' & md' & Ec & HC & HRO' & H0 & H1).
  set (r := bv_unsigned (getr regs' 10)) in *.
  assert (E10 : getr regs' 10 = Z_to_bv 64 r) by (unfold r; symmetry; apply Z_to_bv_bv_unsigned).
  assert (HROr' : ro_agree rsegs mem') by (rewrite <- SEG; exact HRO').
  assert (HCE : call_post_k B MR TEXT_BUF_K L A regs mem md (fun a => (r <= a < r + (cap + 1)) \/ (fun _ : Z => False) a)
    L' A' regs' mem' md').
  { refine (ltx_post_E B API TEXT_BUF_K L A regs mem md _ _ L' A' regs' mem' md' _ HC).
    intros a Ha. left. cbv beta in Ha. lia. }
  assert (HR0 : r = 0 -> 0 <= cap + 1 <= 4096 /\ L' = L /\ A' = A).
  { intros Hr. destruct (Z.eq_dec cap 0) as [Hc|Hc].
    - destruct (H0 Hc) as (_ & EL & EA & _). split; [lia | split; assumption].
    - exfalso. destruct (H1 Hc) as (Hn & _). apply Hn. rewrite E10. f_equal. exact Hr. }
  assert (HR1 : r <> 0 -> 1 <= cap + 1 /\ fresh_block B r (cap + 1) /\
     (exists b1 b2, blocks L' A' = b1 ++ (r, cap + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
     res_ok_slots A' (sb_malloc (sb_hb (lg_b g) hb) (cap + 1)) /\
     (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\ st_init_done A' = true).
  { intros Hr. destruct (Z.eq_dec cap 0) as [Hc|Hc].
    - exfalso. destruct (H0 Hc) as (E0 & _). apply Hr. unfold r. rewrite E0. apply MState.unsigned_lit. lia.
    - destruct (H1 Hc) as (_ & Hfb & Hl & Hres & Hinc & Hst & _).
      split; [lia|]. split; [exact Hfb|]. split; [exact Hl|]. split; [exact Hres|].
      split; [exact Hinc | exact Hst]. }
  destruct (ltx_call B API FF g hb T L A mem md regs TEXT_BUF_K (fun _ => False) r (cap + 1) L' A' regs' mem' md'
    HF HSP HKb HCE (fun a H => False_ind _ H) (fun a => or_intror (fun H => H)) (fun a H => False_ind _ H)
    HRO' HR0 HR1) as (HLF & HLC & HPM & HFR).
  exists r. rewrite Ec, B1.
  apply (cut_close B API fx' g ra (opt_hb r (cap + 1) hb) T (P' r) L' A' regs' mem' md' Hfz HLF).
  apply lc_eqv_self. unfold lcanon.
  pose proof HC as (_ & _ & _ & _ & _ & RP & _).
  apply (HK R (@fp_regs fx') (@fp_csr fx') (normalize_cj rsegs mem) regs' (normalize_cj rsegs mem') r HPc).
  - exact (lc_rp R regs regs' HR RP).
  - exact E10.
  - intros x Hx. exact (HLC x (conj Hx (fun H => H))).
  - exact HPM.
  - intros Hc. destruct (H0 Hc) as (E0 & _). unfold r. rewrite E0. apply MState.unsigned_lit. lia.
  - intros Hc. destruct (H1 Hc) as (Hn & Hfb & _ & _ & _ & _ & Htb).
    assert (Hr : r <> 0) by (intros Hr; apply Hn; rewrite E10; f_equal; exact Hr).
    split; [exact Hr|]. split; [exact (HFR Hr)|].
    destruct Hfb as (Hr4 & Hrc & Hni).
    unfold tbuf_at in *. apply ltx_rw_norm; [exact HROr' | | | exact Htb].
    + cbn [cells_size csize]. unfold TASK_SIZE. lia.
    + intros i Hi. cbn [cells_size csize] in Hi.
      apply (ltx_cj_out B API FF); [unfold TASK_SIZE; lia|]. apply Hni. lia.
Qed.

(* ==========================================================================
   2. text_of
   ========================================================================== *)

Lemma lfr_text_of : forall g hb T ra pcur pown (P : machine_state -> Prop)
    (P' : Z -> Z -> machine_state -> Prop) c,
  lroom_hb hb -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  lg_S g - SLOT_FRAME <= pcur -> pcur + 16 <= lg_S g -> lg_S g - SLOT_FRAME <= pown -> pown + 8 <= lg_S g ->
  (pown + 8 <= pcur \/ pcur + 16 <= pown) ->
  CUT B API g TEXT_OF hb T P c ->
  (forall ms, P ms -> getr (ms_regs ms) 1 = Z_to_bv 64 ra /\
     getr (ms_regs ms) 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME) /\ getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\
     getr (ms_regs ms) 10 = Z_to_bv 64 pcur /\ getr (ms_regs ms) 11 = Z_to_bv 64 pown /\
     exists c0 c1 : word,
       rw_cells rsegs (ms_mem ms) pcur [C8 c0; C8 c1] /\ (exists w, rw_cells rsegs (ms_mem ms) pown [C8 w]) /\
       (exists inp, bytes_at rsegs (ms_mem ms) (bv_unsigned c0) inp /\ Z.of_nat (length inp) = bv_unsigned c1) /\
       0 < lg_n g /\ lg_p g <= bv_unsigned c0 /\ bv_unsigned c0 + bv_unsigned c1 <= lg_p g + lg_n g) ->
  (forall R F fc m regs' m' (c0 c1 : word) own k s t sl,
     P (MS R F (Z_to_bv 64 TEXT_OF) fc None m (seg_rom rsegs)) ->
     rw_cells rsegs m pcur [C8 c0; C8 c1] ->
     regs_preserved R regs' -> getr regs' 10 = Z_to_bv 64 s -> s <> 0 ->
     lcarry (fun x => lkeep B g hb x /\ ~ (pcur <= x < pcur + 16) /\ ~ (pown <= x < pown + 8)) m m' ->
     lpost_mem g m' ->
     cstr_at m' s t -> Z.of_nat (length t) < 320 ->
     bytes_at rsegs m' (s + Z.of_nat (length t) + 1) sl ->
     Z.of_nat (length sl) = (- (s + Z.of_nat (length t) + 1)) mod 8 ->
     apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) (lg_S g - SLOT_STACK_Z) SLOT_STACK_Z ->
     apart_gnl s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) ->
     apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) A_LONG_ALIAS 304 ->
     apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) A_ERRNO 4 ->
     (forall a n, In (a, n) hb -> 0 < n -> apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) a n) ->
     rw_cells rsegs m' pown [C8 (Z_to_bv 64 own)] ->
     (exists adv, 0 <= adv <= bv_unsigned c1 /\
        rw_cells rsegs m' pcur [C8 (Z_to_bv 64 (bv_unsigned c0 + adv)); C8 (Z_to_bv 64 (bv_unsigned c1 - adv))]) ->
     (own = 0 -> k = 0 /\ A_RO_LO <= s /\ s + Z.of_nat (length t) + 1 <= A_RO_END) ->
     (own <> 0 -> own = s /\ 1 <= k <= 320 /\ Z.of_nat (length t) + 1 <= k /\ lfresh B g hb own k) ->
     P' own k (MS regs' F (Z_to_bv 64 ra) fc None m' (seg_rom rsegs))) ->
  SR (ms_segs B) c (fun c' => exists own k, CUT B API g ra (opt_hb own k hb) T (P' own k) c').
Proof.
  intros g hb T ra pcur pown P P' c Hroom Hra Hra2 Hq1 Hq2 Ho1 Ho2 Hco HCUT HPR HK.
  pose proof (ltx_segs B API FF) as SEG.
  apply (cut_open B API g TEXT_OF hb T P c _ HCUT).
  intros fx' L A regs mem md Hfz HF Heqv.
  destruct (lc_rep P fx' regs TEXT_OF mem Heqv) as (R & HPc & HR).
  destruct (HPR _ HPc) as (G1 & G2 & G4 & G10 & G11 & c0 & c1 & Hcur & (w & Hown) & (inp & Hinp & Hlen) & Hn0
    & Hp1 & Hp2).
  cbn [ms_regs ms_mem MState.MS] in G1, G2, G4, G10, G11, Hcur, Hown, Hinp.
  assert (R1 : YK11.getr regs 1 = Z_to_bv 64 ra) by (rewrite (lc_getr R regs 1 HR); exact G1).
  assert (R2 : YK11.getr regs 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME)) by (rewrite (lc_getr R regs 2 HR); exact G2).
  assert (R4 : YK11.getr regs 4 = Z_to_bv 64 A_TP) by (rewrite (lc_getr R regs 4 HR); exact G4).
  assert (R10 : YK11.getr regs 10 = Z_to_bv 64 pcur) by (rewrite (lc_getr R regs 10 HR); exact G10).
  assert (R11 : YK11.getr regs 11 = Z_to_bv 64 pown) by (rewrite (lc_getr R regs 11 HR); exact G11).
  assert (B1 : getr regs 1 = Z_to_bv 64 ra) by exact R1.
  assert (B10 : getr regs 10 = Z_to_bv 64 pcur) by exact R10.
  assert (B11 : getr regs 11 = Z_to_bv 64 pown) by exact R11.
  assert (HKo : 0 <= TEXT_OF_K <= SLOT_STACK - SLOT_FRAME)
    by (unfold TEXT_OF_K, ALLOC_STACK, SLOT_STACK, SLOT_FRAME; lia).
  destruct (la_pre B API FF g hb T L A regs mem md ra TEXT_OF_K HF Hra Hra2 HKo R1 R2 R4) as (HSP & PRE).
  pose proof HF as (HGV & HM & _ & _ & HID & _ & _ & _ & _ & _ & _ & _ & HRO & HRS & HP & _).
  destruct (lc_gv B API g HGV) as (HS & HS16 & HS47 & HM0 & _).
  pose proof (@lc_ceil rc) as [HC1 HC2].
  assert (HROr : ro_agree rsegs mem) by (rewrite <- SEG; exact HRO).
  assert (U10 : bv_unsigned (Z_to_bv 64 pcur) = pcur) by (apply MState.unsigned_lit; ltx_unf; lia).
  assert (U11 : bv_unsigned (Z_to_bv 64 pown) = pown) by (apply MState.unsigned_lit; ltx_unf; lia).
  destruct (ltx_payload B API g HGV Hn0) as (Hpin & Hp4 & Hpc).
  assert (Hpin' : In (lg_p g, lg_n g) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hpin).
  pose proof (TOF fx' L A regs mem md (sb_hb (lg_b g) hb) c0 c1 SEG PRE HRO) as HT.
  rewrite B10, B11, U10, U11 in HT.
  eapply SR_mono.
  { apply HT.
    - exact (ltx_rw_raw mem pcur _ HROr Hcur).
    - exists w. exact (ltx_rw_raw mem pown _ HROr Hown).
    - ltx_unf. lia.
    - ltx_unf. lia.
    - ltx_unf. lia.
    - ltx_unf. lia.
    - exact HRS.
    - exact (lroom B API g hb 320 HGV Hroom ltac:(lia)).
    - exact HID.
    - exists inp. split; [exact (bytes_at_rel_cj rsegs mem _ _ _ (mem_rel_cj_normalize rsegs mem HROr) Hinp)|].
      split; [exact Hlen|]. split; left; ltx_unf; lia.
    - intros _. destruct (proj1 (blocks_In L A _ _) Hpin') as (q & Eq & Hq).
      exists q, (lg_n g). split; [exact Hq|]. rewrite Eq. lia.
    - exact Hco.
    - unfold apart_frame. rewrite HSP. right. lia.
    - unfold apart_frame. rewrite HSP. right. lia.
    - exact (ltx_texts_img B API FF g hb T L A mem md HF).
    - right. ltx_unf. lia.
    - right. ltx_unf. lia. }
  intros c' (L' & A' & regs' & mem' & md' & own & s & t & k & Ec & HC & HRO' & H10 & Hs0 & Hcs & Htl & Hpw
    & (adv & Hadv & Hcur') & Hown0 & Hown1).
  assert (HROr' : ro_agree rsegs mem') by (rewrite <- SEG; exact HRO').
  (* the frame step *)
  assert (P1 : forall a, (fun a => (pcur <= a < pcur + 16) \/ (pown <= a < pown + 8)) a ->
             lg_S g - SLOT_FRAME <= a < lg_S g).
  { intros a Ha. cbv beta in Ha. lia. }
  assert (P2 : forall a, (fun a => (pcur <= a < pcur + 16) \/ (pown <= a < pown + 8)) a ->
             writable_at segs mem' a).
  { intros a [Ha|Ha]; rewrite SEG.
    - pose proof Hcur' as (_ & _ & _ & Hw). cbn [cells_size csize] in Hw.
      pose proof (Hw (a - pcur) ltac:(lia)) as W. replace (pcur + (a - pcur)) with a in W by lia. exact W.
    - pose proof (ltx_wr_hi mem' pown _ (Z.to_nat (a - pown)) Hpw ltac:(ltx_unf; lia)
        ltac:(rewrite Mem.length_le8; lia)) as W.
      rewrite Z2Nat.id in W by lia. replace (pown + (a - pown)) with a in W by lia. exact W. }
  assert (P3 : own = 0 -> 0 <= k <= 4096 /\ L' = L /\ A' = A).
  { intros Ho. destruct (Hown0 Ho) as (Hk0 & EL & EA & _). split; [lia | split; assumption]. }
  assert (P4 : own <> 0 -> 1 <= k /\ fresh_block B own k /\
     (exists b1 b2, blocks L' A' = b1 ++ (own, k) :: b2 /\ blocks L A = b1 ++ b2) /\
     res_ok_slots A' (sb_malloc (sb_hb (lg_b g) hb) k) /\
     (forall q k', In (q, k') (user_blocks A) -> In (q, k') (user_blocks A')) /\ st_init_done A' = true).
  { intros Ho. destruct (Hown1 Ho) as (_ & Hk & Hfb & _ & Hl & Hres & Hinc & Hst).
    split; [lia|]. split; [exact Hfb|]. split; [exact Hl|]. split; [exact Hres|].
    split; [exact Hinc | exact Hst]. }
  destruct (ltx_call B API FF g hb T L A mem md regs TEXT_OF_K
    (fun a => (pcur <= a < pcur + 16) \/ (pown <= a < pown + 8)) own k L' A' regs' mem' md'
    HF HSP HKo HC P1 (fun a => ltx_dec2 a pcur 16 pown 8) P2 HRO' P3 P4) as (HLF & HLC & HPM & HFR).
  (* the answer: its string, its slack up to the next multiple of 8, and where they lie *)
  assert (HE0 : 1 <= s /\ s + Z.of_nat (length t) + 1 <= YM05.alloc_ceiling).
  { destruct (Z.eq_dec own 0) as [Ho|Ho].
    - destruct (Hown0 Ho) as (_ & _ & _ & _ & Hlo & Hhi). ltx_unf. lia.
    - destruct (Hown1 Ho) as (Eos & _ & (Hf4 & Hfc & _) & Htk & _). subst own. lia. }
  assert (Hcsn : cstr_at (normalize_cj rsegs mem') s t).
  { destruct Hcs as [Hb Hnz]. split; [|exact Hnz].
    apply (bytes_at_normalize_cj_low rsegs mem'); [exact HROr' | | exact Hb].
    rewrite length_app. cbn [length]. unfold TASK_SIZE. lia. }
  assert (SL : exists sl, bytes_at rsegs (normalize_cj rsegs mem') (s + Z.of_nat (length t) + 1) sl /\
     Z.of_nat (length sl) = (- (s + Z.of_nat (length t) + 1)) mod 8 /\
     apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) (lg_S g - SLOT_STACK_Z) SLOT_STACK_Z /\
     apart_gnl s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) /\
     apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) A_LONG_ALIAS 304 /\
     apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) A_ERRNO 4 /\
     (forall a n, In (a, n) hb -> 0 < n -> apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) a n)).
  { remember (s + Z.of_nat (length t) + 1) as e0 eqn:Ee0.
    pose proof (ltx_rup e0) as Hrup. pose proof (ltx_rup_bnd e0) as Hrb.
    pose proof (Z.mod_pos_bound (- e0) 8 ltac:(lia)) as Hmb.
    assert (Hfin : forall sl : list byte, length sl = Z.to_nat ((- e0) mod 8) ->
      Z.of_nat (length sl) = (- e0) mod 8 /\ s + (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) = 8 * ((e0 + 7) / 8)).
    { intros sl Hl. rewrite Hl, Z2Nat.id by lia. split; [reflexivity | lia]. }
    destruct (Z.eq_dec own 0) as [Ho|Ho].
    - (* a .rodata text: the bytes after its NUL up to the next multiple of 8 are .rodata's *)
      destruct (Hown0 Ho) as (_ & _ & _ & _ & Hlo & Hhi).
      assert (Hbe : forall i, (i < Z.to_nat ((- e0) mod 8))%nat ->
        exists b, Mem.mrd rsegs (normalize_cj rsegs mem') (Z_to_bv 64 (e0 + Z.of_nat i)) = Some b).
      { intros i Hi. destruct (ltx_ro_ok (e0 + Z.of_nat i) ltac:(ltx_unf; lia)) as (Hro & b & Hbb).
        exists b. unfold Mem.mrd, normalize_cj. cbv beta. rewrite (cj_drop_ro rsegs _ Hro). exact Hbb. }
      destruct (ltx_bytes_ex (Z.to_nat ((- e0) mod 8)) (normalize_cj rsegs mem') e0 ltac:(lia) ltac:(ltx_unf; lia)
        Hbe) as (sl & Hsl & Hb).
      exists sl. destruct (Hfin sl Hsl) as (Hl8 & HE8).
      split; [exact Hb|]. split; [exact Hl8|].
      split; [ltx_unf; left; lia|]. split; [ltx_unf; left; lia|].
      split; [ltx_unf; left; lia|]. split; [ltx_unf; left; lia|].
      intros a n Ha Hn.
      assert (Ha' : In (a, n) (blocks L A))
        by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Ha).
      assert (HIA : forall y, a <= y < a + n -> ~ in_img B y).
      { intros y Hy. destruct (lc_blk B API FF L A mem md a n (y - a) HM Ha' ltac:(lia)) as (_ & _ & _ & _ & Hni).
        replace (a + (y - a)) with y in Hni by lia. exact Hni. }
      assert (HIB : forall y, s <= y < 8 * ((e0 + 7) / 8) -> in_img B y).
      { intros y Hy. apply (ltx_ro_img B API FF y ltac:(ltx_unf; lia)).
        exact (proj1 (ltx_ro_ok y ltac:(ltx_unf; lia))). }
      destruct (ltx_apart_img B a (a + n) s (8 * ((e0 + 7) / 8)) ltac:(lia) ltac:(lia) HIA HIB) as [D|D].
      + unfold apart. right. lia.
      + unfold apart. left. lia.
    - (* the fresh block: its bytes, then the allocator's slack up to the next multiple of 8 *)
      destruct (Hown1 Ho) as (Eos & Hk & Hfb & Htk & (b1 & b2 & Eb1 & Eb2) & _).
      pose proof Hfb as (Hf4 & Hfc & Hfni).
      pose proof HC as (HM' & _).
      assert (Hin' : In (own, k) (blocks L' A')) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
      destruct (lc_fa B API FF fx') as (_ & _ & _ & _ & _ & Hslack & _).
      assert (HE8 : 8 * ((e0 + 7) / 8) <= 8 * ((own + k + 7) / 8)) by (apply ltx_rup_mono; lia).
      pose proof (ltx_rup_bnd (own + k)) as Hrb2.
      assert (HNI : forall y, own <= y < 8 * ((own + k + 7) / 8) -> ~ in_img B y /\ present mem' y).
      { intros y Hy. destruct (Z_lt_ge_dec y (own + k)) as [Hy2|Hy2].
        - split.
          + replace y with (own + (y - own)) by lia. apply Hfni. lia.
          + destruct (lc_blk B API FF L' A' mem' md' own k (y - own) HM' Hin' ltac:(lia)) as (Hpr & _).
            replace (own + (y - own)) with y in Hpr by lia. exact Hpr.
        - split.
          + apply (ltx_slack_noimg B API FF own k y ltac:(lia) Hfni). lia.
          + exact (Hslack L' A' mem' md' own k y HM' Hin' ltac:(lia)). }
      assert (Hbe : forall i, (i < Z.to_nat ((- e0) mod 8))%nat ->
        exists b, Mem.mrd rsegs (normalize_cj rsegs mem') (Z_to_bv 64 (e0 + Z.of_nat i)) = Some b).
      { intros i Hi. destruct (HNI (e0 + Z.of_nat i) ltac:(lia)) as (Hni & b & Hpb).
        exists b. unfold Mem.mrd, normalize_cj. cbv beta.
        rewrite (ltx_cj_out B API FF (e0 + Z.of_nat i) ltac:(unfold TASK_SIZE; lia) Hni). rewrite Hpb. reflexivity. }
      destruct (ltx_bytes_ex (Z.to_nat ((- e0) mod 8)) (normalize_cj rsegs mem') e0 ltac:(lia) ltac:(lia) Hbe)
        as (sl & Hsl & Hb).
      exists sl. destruct (Hfin sl Hsl) as (Hl8 & HE).
      split; [exact Hb|]. split; [exact Hl8|].
      assert (HAP : forall X n, 0 < n -> 0x21000 <= X -> X + n <= LF_TOP ->
                apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) X n).
      { intros X n Hn HX1 HX2. unfold apart.
        assert (HIA : forall y, own <= y < 8 * ((e0 + 7) / 8) -> ~ in_img B y)
          by (intros y Hy; exact (proj1 (HNI y ltac:(lia)))).
        assert (HIB : forall y, X <= y < X + n -> in_img B y)
          by (intros y Hy; exact (lfr_img_rng B API FF _ _ ltx_hi_chk y ltac:(lia))).
        destruct (ltx_apart_img B own (8 * ((e0 + 7) / 8)) X (X + n) ltac:(lia) ltac:(lia) HIA HIB) as [D|D].
        - left. lia.
        - right. lia. }
        split.
        { unfold apart. left.
          assert (Hal : (lg_S g - SLOT_STACK_Z) mod 8 = 0)
            by (clear - HS16; unfold SLOT_STACK_Z; Z.div_mod_to_equations; lia).
          pose proof (ltx_rup_le (own + k) (lg_S g - SLOT_STACK_Z) ltac:(unfold SLOT_STACK, SLOT_STACK_Z in *; lia) Hal).
          lia. }
        split; [exact (HAP A_G_NL NK_SIZE ltac:(ltx_unf; lia) ltac:(ltx_unf; lia) ltac:(ltx_unf; lia))|].
        split; [exact (HAP A_LONG_ALIAS 304 ltac:(lia) ltac:(ltx_unf; lia) ltac:(ltx_unf; lia))|].
        split; [exact (HAP A_ERRNO 4 ltac:(lia) ltac:(ltx_unf; lia) ltac:(ltx_unf; lia))|].
        intros a n Ha Hn.
        destruct (HFR Ho) as (_ & _ & _ & _ & Hhb & _).
        assert (Ha' : In (a, n) (blocks L A))
          by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Ha).
        destruct (proj1 (blocks_In L A a n) Ha') as (q & Eq & Hq).
        pose proof (mr_blocks_aligned B MR (aa_laws API) L A mem md q n HM Hq) as Hal. rewrite Eq in Hal.
        unfold apart. destruct (Hhb a n Ha) as [D|D].
        * left. pose proof (ltx_rup_le (own + k) a D ltac:(clear - Hal; Z.div_mod_to_equations; lia)). lia.
        * right. lia. }
  destruct SL as (sl & Hsl & Hsll & A1 & A2 & A3 & A4 & A5).
  exists own, k. rewrite Ec, B1.
  apply (cut_close B API fx' g ra (opt_hb own k hb) T (P' own k) L' A' regs' mem' md' Hfz HLF).
  apply lc_eqv_self. unfold lcanon.
  pose proof HC as (_ & _ & _ & _ & _ & RP & _).
  apply (HK R (@fp_regs fx') (@fp_csr fx') (normalize_cj rsegs mem) regs' (normalize_cj rsegs mem') c0 c1 own k s t sl
    HPc Hcur).
  - exact (lc_rp R regs regs' HR RP).
  - exact H10.
  - exact Hs0.
  - intros x (Hk & Hn1 & Hn2). apply HLC. split; [exact Hk | intros [H|H]; contradiction].
  - exact HPM.
  - exact Hcsn.
  - exact Htl.
  - exact Hsl.
  - exact Hsll.
  - exact A1.
  - exact A2.
  - exact A3.
  - exact A4.
  - exact A5.
  - apply (ltx_rw_win B API FF g (opt_hb own k hb) T L' A' mem' md' pown _ HLF);
      [unfold SLOT_STACK, SLOT_FRAME in *; lia | cbn [cells_size csize]; lia |].
    split; [split; exact I|].
    change (cells_bytes [C8 (Z_to_bv 64 own)]) with (le8 (Z_to_bv 64 own) ++ []). rewrite app_nil_r.
    apply (bytes_at_normalize_cj_low rsegs mem'); [exact HROr' | rewrite Mem.length_le8; ltx_unf; lia | exact Hpw].
  - exists adv. split; [exact Hadv|].
    apply ltx_rw_norm; [exact HROr' | cbn [cells_size csize]; ltx_unf; lia | | exact Hcur'].
    intros i Hi. cbn [cells_size csize] in Hi. apply ltx_cj_hi. ltx_unf. lia.
  - intros Ho. destruct (Hown0 Ho) as (Hk0 & _ & _ & _ & Hlo & Hhi).
    split; [exact Hk0|]. split; [exact Hlo|]. ltx_unf. lia.
  - intros Ho. destruct (Hown1 Ho) as (Eos & Hk & _ & Htk & _).
    split; [exact Eos|]. split; [exact Hk|]. split; [exact Htk | exact (HFR Ho)].
Qed.

End TX.
