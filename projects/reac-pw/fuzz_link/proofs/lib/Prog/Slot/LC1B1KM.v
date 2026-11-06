(* The slot LLVMFuzzerTestOneInput, plain image, op_write arm, segment B1: the call of kernel at 0x13fc0
   (entry 0x14190, ra 0x13fc4, kernel_c.v, leaf K 4416), a0 = sp + 0x40 (the input cursor).
   - c1b1_kpre: kernel's Pre from the loop memory at text_of's return (lh_mem, the cursor cells);
   - c1b1_kpost: kernel's Post and its footprint (its frame, g_nl below NK_OPEN, long_alias's 301 bytes, the
     cursor's 16) give the loop memory again, with the cursor moved on and nk_next = 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call LC1B1Lib.
Local Open Scope Z_scope.

Lemma c1b1_kpre : forall E i P N kbs mbs gbs m regs,
  lenv_ok E -> lh_mem E i P N kbs mbs gbs m ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] ->
  mem_inv rsegs m ->
  spZ regs = e_S E - SLOT_FRAME -> arg regs 0 = e_S E - SLOT_FRAME + FO_P ->
  c1b1_kP regs m.
Proof.
  intros E i P N kbs mbs gbs m regs HE HL HC MI HSP HA0.
  destruct (c1b1_lenv E HE) as (S1 & S2 & _ & _ & _ & _ & _ & _ & _ & L1 & P1 & P2 & P3 & _).
  destruct (c1b1_lh_split _ _ _ _ _ _ _ _ HL) as (ST & _ & NK & NW & IT & _ & _ & _ & _ & LA & _ & _ & _ & _ & K).
  destruct ST as (_ & _ & _ & _ & _ & _ & TX & IP & _ & PL & LS & _ & _).
  destruct K as (k & Hk & EP & EN).
  assert (UP : bv_unsigned (wz P) = P) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (wz N) = N) by (apply unsigned_lit; lia).
  unfold c1b1_kP. cbv beta.
  exists kbs, (wz P), (wz N).
  unfold kernel_apart, frame_apart_gnl, apart_frame, apart_gnl. rewrite HSP, HA0, UP, UN.
  clear HL.
  unfold SLOT_FRAME, FO_P, A_G_NL, NK_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE, A_TEXTS, TEXTS_N in *.
  split; [exact NK|].
  split; [lia|].
  split; [exact NW|].
  split; [exact HC|].
  split; [lia|].
  split; [lia|].
  split.
  { exists (skipn (Z.to_nat k) (e_pl E)). split.
    - rewrite <- (firstn_skipn (Z.to_nat k) (e_pl E)) in PL. apply bytes_at_app in PL. destruct PL as [_ PL].
      rewrite length_firstn in PL.
      replace (e_p0 E + Z.of_nat (Nat.min (Z.to_nat k) (length (e_pl E)))) with P in PL by lia. exact PL.
    - rewrite length_skipn. lia. }
  split; [lia|].
  split; [lia|].
  split.
  { intros j Hj. destruct (c1b1_texts m MI TX j Hj) as (p & s & sl & U & B & NZ & SLK & LS' & B1 & B2).
    exists p, s, sl. refine (conj U (conj _ (conj B (conj NZ (conj SLK (conj LS' _)))))); lia. }
  split.
  { destruct LA as [la LA]. destruct LS as (sl & LSB & LSL). exists la, sl. exact (conj LA (conj LSB LSL)). }
  split; [lia|].
  split; [lia|].
  intros tab j nm ix p IT2 Hn U.
  destruct (c1b1_ifname m kbs tab j nm ix p IT IP IT2 Hn U) as (Hj & Ep & Enm & _).
  pose proof (c1b1_link_bnd j Hj) as B. rewrite <- Enm in B.
  destruct (c1b1_wz_eq p _ Ep ltac:(lia)) as [q Hq].
  lia.
Qed.

Lemma c1b1_kpost : forall E i P N kbs mbs gbs m m' own s t sl regs regs' m0 sp0,
  lenv_ok E -> lh_mem E i P N kbs mbs gbs m ->
  rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] ->
  bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) ->
  al_ok E m s t sl -> MemNorm.task_mem rsegs m -> seg_fp (e_S E) (c1_hp E) m0 m ->
  sp0 = e_S E - SLOT_FRAME -> arg regs 0 = e_S E - SLOT_FRAME + FO_P ->
  c1b1_kQ regs m regs' m' ->
  munch ((sp0 - 4416, sp0) :: c1b1_kW regs m) m m' -> wmono rsegs m m' ->
  exists P' N' kbs', lh_mem E i P' N' kbs' mbs gbs m' /\ nk_next kbs' = 0 /\ 0 <= N' /\
    rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_P) [C8 (wz P'); C8 (wz N')] /\
    bytes_at rsegs m' (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) /\
    al_ok E m' s t sl /\ MemNorm.task_mem rsegs m' /\ seg_fp (e_S E) (c1_hp E) m0 m'.
Proof.
  intros E i P N kbs mbs gbs m m' own s t sl regs regs' m0 sp0 HE HL HC HO HA HT HF Esp HA0 PO MU WM.
  subst sp0.
  destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & M3 & _ & _ & _ & _ & L1 & P1 & P2 & P3 & _).
  destruct (c1b1_lh_split _ _ _ _ _ _ _ _ HL)
    as (ST & _ & NK & NW & IT & O1 & O2 & O3 & O4 & _ & MD & MW & KW & MA & K).
  destruct K as (k & Hk & EP & EN).
  unfold c1b1_kQ in PO. cbv beta in PO.
  destruct (PO kbs NK)
    as (kbs' & NK' & NW' & NX & _ & _ & _ & _ & EO1 & EO2 & EO3 & EO4 & EO5 & EO6 & EO7 & IT' & CU & LA').
  rewrite HA0 in CU.
  destruct (CU (wz P) (wz N) HC) as (adv & Hadv & HC').
  assert (UP : bv_unsigned (wz P) = P) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (wz N) = N) by (apply unsigned_lit; lia).
  rewrite UP in HC'. rewrite UN in Hadv, HC'.
  unfold c1b1_kW in MU. cbv beta in MU. rewrite HA0 in MU.
  lazymatch type of MU with munch ?W _ _ => assert (WK : c1b1_wok E W) end.
  { intros x Hx HO'. cbn [outside] in HO'. unfold c1b1_al.
    unfold SLOT_FRAME, FO_P, A_G_NL, NK_CHUNK, NK_OPEN, A_LONG_ALIAS, LONG_ALIAS_SIZE in *. lia. }
  exists (P + adv), (N - adv), kbs'.
  refine (conj _ (conj NX (conj _ (conj HC' (conj _ (conj _ (conj _ _))))))).
  - apply c1b1_lh_join.
    + exact (c1b1_static_tr E gbs m m' _ HE ST MU WM WK).
    + exists (N - adv). exact HC'.
    + exact NK'.
    + exact NW'.
    + exact (IT' link_tab IT).
    + rewrite EO1. exact O1.
    + rewrite EO4. exact O2.
    + rewrite EO2, EO3. exact O3.
    + rewrite EO2. exact O4.
    + exact LA'.
    + destruct MD as [MDu MDl]. split; [|exact MDl].
      eapply c1b1_u8_tr; [exact MDu | exact MU | exact WM |]. rewrite MDl.
      intros x Hx. cbn [outside].
      unfold MD_SIZE, SLOT_FRAME, FO_P, A_G_NL, NK_CHUNK, NK_OPEN, A_LONG_ALIAS, LONG_ALIAS_SIZE in *. lia.
    + exact MW.
    + exact KW.
    + exact MA.
    + exists (k + adv). lia.
  - lia.
  - exact (c1b1_own_tr E m m' _ own HE HO MU WK).
  - exact (c1b1_alok_tr E m m' _ s t sl HA MU WK).
  - exact (c1b1_task E _ m m' HE HT MU WK).
  - exact (c1b1_segfp E _ m0 m m' HF MU WM WK).
Qed.
