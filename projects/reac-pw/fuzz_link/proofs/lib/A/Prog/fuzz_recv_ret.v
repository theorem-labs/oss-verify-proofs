(* fuzz_recv on image A: the epilogue +0x23c (a0 := s2, the restores of ra and s0..s9 from the frame, sp += 96,
   ret) from a machine state that satisfies rv_inv, and the contract's apost at the ret: RV_RET of
   lib/A/Prog/fuzz_recv_defs.v. Every exit of fuzz_recv goes through +0x23c, so this file is the only place the walk
   builds the apost.
   - ashadow_kept_run2: LinkWalk.v ashadow_kept_run for bytes E below SHADOW_OFF or in high memory (the buffer can
     be in high memory: amem_range);
   - apost_leaf2: LinkWalk.v apost_leaf (EV = 0) with that E;
   - rv_ret_ok: the run of the fresh state ss_rt to the `ret` (+0x270), then the apost at the write set and errno
     (LinkWalkErrno.v apost_errno). The run writes no byte (the frame region has no write window), so the memory
     at the ret is the memory at +0x23c.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkErrno fuzz_recv_c fuzz_recv_defs fuzz_recv_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).

(* The shadow of every heap block the call keeps, for a run that writes only its window (above the ceiling) and
   bytes E below SHADOW_OFF or at or above kHighMemBeg: the shadow byte of a heap byte is in
   [SHADOW_OFF, kHighMemBeg) and below the ceiling. *)
Lemma ashadow_kept_run2 : forall lyc Sc ly2 S2 W memc mdc W2 mem2 slo shi (E : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  alloc_ceiling <= slo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall x, E x -> x < SHADOW_OFF \/ kHighMemBeg <= x) ->
  ashadow_kept SEGS B lyc Sc ly2 S2 W memc W2 mem2.
Proof.
  intros lyc Sc ly2 S2 W memc mdc W2 mem2 slo shi E HAR Hceil UN HE b m a Hin _ Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
  assert (Ha0 : 0 <= a <= alloc_ceiling) by lia.
  assert (Hd0 : 0 <= a / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : a / 8 < 0x100000000000) by (apply Z.div_lt_upper_bound; lia).
  assert (Hs : 0x7fff8000 <= shadow_addr a < 0x10007fff8000) by (unfold shadow_addr, SHADOW_OFF; lia).
  apply UN.
  - lia.
  - lia.
  - intros HEa. destruct (HE _ HEa) as [Hx|Hx]; unfold SHADOW_OFF, kHighMemBeg in Hx; lia.
Qed.

(* LinkWalk.v apost_leaf at EV = 0, with the write set E below SHADOW_OFF or in high memory *)
Lemma apost_leaf2 : forall (K : Z) (E : Z -> Prop) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regs2 : bvmap 5 word) mem2 md2
    (Q : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  sp0 - STK <= spZ regs - K -> spZ regs - K <= spZ regs ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> ~ E a ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem2 a) ->
  (forall x, E x -> x < SHADOW_OFF \/ kHighMemBeg <= x) ->
  Q lyc Sc W regs2 mem2 md2 ->
  apost SK SEGS B K 0 E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
  intros K E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 Q
    HJ HJ2 Hlo Hwin Hfds Hfs HP UN Hgrow Hpw HE HQ.
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & _).
  assert (Hc : alloc_ceiling <= sp0 - STK) by lia. clear Hceil Hslo.
  exists lyc, Sc, regs2, mem2, md2.
  split; [reflexivity|].
  split; [rewrite Z.add_0_r; exact HJ2|].
  split; [exact HP|]. split; [reflexivity|].
  split; [exact Hfds|]. split; [exact Hfs|].
  split.
  { eapply akept_run;
      first [ exact LAWS | exact pa_segs_low | exact HAR | lia | exact UN | exact Hgrow | exact Hpw ]. }
  split; [exact (ashadow_kept_run2 lyc Sc lyc Sc W memc mdc W mem2 (spZ regs - K) (spZ regs) E HAR
                   ltac:(lia) UN HE)|].
  exact HQ.
Qed.

Variable c : rvc.
Hypothesis HC : rv_call SK B c.

(* THE EPILOGUE +0x23c and the apost *)
Lemma rv_ret_ok : RV_RET SK B c.
Proof using All.
  intros regs mem md HI H19 HQ.
  unfold rv_goal.
  pose proof HC as ((HJ0 & HGX & _ & Hret & _) & _).
  unfold YK0s.ret_ok in Hret.
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR & _).
  pose proof HI as (HJ & Hfd & Hfs & Hsp & Hgp & Htp & H26 & H27 & _ & UN & PR).
  destruct (rv_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & H16 & HXO).
  destruct (rv_pre_facts SK B TL c HC) as (Hb0 & Hlen & Hamr & Hbg & Hbf & Hef & Heg & He0 & He1).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (pal_env B TL) as ENV.
  (* the atoms 32..42: the entry ra, s0, s1, s2..s9 *)
  pose proof (rv_E_ext c regs) as EX.
  assert (X0 : ew (rv_E c regs) 32 = getr (c_regs0 c) 1) by exact (EX 0%nat ltac:(lia)).
  assert (X1 : ew (rv_E c regs) 33 = getr (c_regs0 c) 8) by exact (EX 1%nat ltac:(lia)).
  assert (X2 : ew (rv_E c regs) 34 = getr (c_regs0 c) 9) by exact (EX 2%nat ltac:(lia)).
  assert (X3 : ew (rv_E c regs) 35 = getr (c_regs0 c) 18) by exact (EX 3%nat ltac:(lia)).
  assert (X4 : ew (rv_E c regs) 36 = getr (c_regs0 c) 19) by exact (EX 4%nat ltac:(lia)).
  assert (X5 : ew (rv_E c regs) 37 = getr (c_regs0 c) 20) by exact (EX 5%nat ltac:(lia)).
  assert (X6 : ew (rv_E c regs) 38 = getr (c_regs0 c) 21) by exact (EX 6%nat ltac:(lia)).
  assert (X7 : ew (rv_E c regs) 39 = getr (c_regs0 c) 22) by exact (EX 7%nat ltac:(lia)).
  assert (X8 : ew (rv_E c regs) 40 = getr (c_regs0 c) 23) by exact (EX 8%nat ltac:(lia)).
  assert (X9 : ew (rv_E c regs) 41 = getr (c_regs0 c) 24) by exact (EX 9%nat ltac:(lia)).
  assert (X10 : ew (rv_E c regs) 42 = getr (c_regs0 c) 25) by exact (EX 10%nat ltac:(lia)).
  clear EX.
  (* the fresh state ss_rt *)
  pose proof (rv_st_ok SK B c HC regs mem md RV_RT [] [] HI H19 eq_refl (Forall_nil _)
    ltac:(cbn; first [exact I | constructor]) ltac:(cbn; first [exact I | constructor])
    ltac:(cbn; first [exact I | constructor])) as HS.
  pose proof (rv_E_env c regs) as HEI.
  assert (SHOK : sh_ok SEGS rv_Bx [] (rv_E c regs) (mrestrict (w_H (c_W c)) mem)) by constructor.
  pose proof (paj_run_xe SK B LAWS ENV ERRF (c_G c) HGX (c_XO c) (c_OUT c)) as RUN.
  (* +0x23c .. +0x270: a0 := s2, the restores, sp += 96; the run stops at the ret *)
  paj_run_tok RUN HS HJ SHOK rv_span.
  - (* the frame region has no write window *)
    intros a (r & Hin & Hr). unfold rv_ss in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<-|[]].
    unfold rv_fr in Hr. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
  - lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
    (* the run wrote no byte *)
    assert (Hm : ms_mem ms1 = mem).
    { eapply frame_of_read_only; [|exact HF]. vm_compute. reflexivity. }
    rewrite Hm in HJ.
    prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
    prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
    prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
    prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26.
    prreg HS (27%bv : bv 5) R27.
    (* the callee-saved registers: sp = entry sp, gp / tp / s10 / s11 as at the call, s0..s9 from the frame *)
    assert (HP : aregs_preserved (c_regs0 c) (ms_regs ms1)).
    { assert (ZB : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> getr (ms_regs ms1) rr = getr (c_regs0 c) rr ->
                     getr (ms_regs ms1) (Z_to_bv 5 z) = getr (c_regs0 c) (Z_to_bv 5 z))
        by (intros rr z -> Hq; exact Hq).
      intros r Hr. unfold acallee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      clear Hr.
      destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]]].
      - apply (ZB 2%bv 2 ltac:(apply bv_eq; reflexivity)).
        rewrite R2, (rv_E_reg c regs 2 2%bv), Hsp by (lia || reflexivity). unfold w64.
        rewrite unsigned_lit_small by (unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *; lia).
        rewrite Z.sub_add. unfold rv_sp, spZ. apply Z_to_bv_bv_unsigned.
      - apply (ZB 3%bv 3 ltac:(apply bv_eq; reflexivity)).
        rewrite R3, (rv_E_reg c regs 3 3%bv) by (lia || reflexivity). exact Hgp.
      - apply (ZB 4%bv 4 ltac:(apply bv_eq; reflexivity)).
        rewrite R4, (rv_E_reg c regs 4 4%bv) by (lia || reflexivity). exact Htp.
      - apply (ZB 8%bv 8 ltac:(apply bv_eq; reflexivity)). rewrite R8, X1. reflexivity.
      - apply (ZB 9%bv 9 ltac:(apply bv_eq; reflexivity)). rewrite R9, X2. reflexivity.
      - apply (ZB 18%bv 18 ltac:(apply bv_eq; reflexivity)). rewrite R18, X3. reflexivity.
      - apply (ZB 19%bv 19 ltac:(apply bv_eq; reflexivity)). rewrite R19, X4. reflexivity.
      - apply (ZB 20%bv 20 ltac:(apply bv_eq; reflexivity)). rewrite R20, X5. reflexivity.
      - apply (ZB 21%bv 21 ltac:(apply bv_eq; reflexivity)). rewrite R21, X6. reflexivity.
      - apply (ZB 22%bv 22 ltac:(apply bv_eq; reflexivity)). rewrite R22, X7. reflexivity.
      - apply (ZB 23%bv 23 ltac:(apply bv_eq; reflexivity)). rewrite R23, X8. reflexivity.
      - apply (ZB 24%bv 24 ltac:(apply bv_eq; reflexivity)). rewrite R24, X9. reflexivity.
      - apply (ZB 25%bv 25 ltac:(apply bv_eq; reflexivity)). rewrite R25, X10. reflexivity.
      - apply (ZB 26%bv 26 ltac:(apply bv_eq; reflexivity)).
        rewrite R26, (rv_E_reg c regs 26 26%bv) by (lia || reflexivity). exact H26.
      - apply (ZB 27%bv 27 ltac:(apply bv_eq; reflexivity)).
        rewrite R27, (rv_E_reg c regs 27 27%bv) by (lia || reflexivity). exact H27. }
    (* a0 = s2 *)
    assert (HA0 : getr (ms_regs ms1) 10 = getr regs 18).
    { rewrite R10. apply (rv_E_reg c regs 18 18%bv); [lia | reflexivity]. }
    clear R2 R3 R4 R8 R9 R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10.
    (* the ret: pc := ra = the entry ra *)
    eapply (paj_ret_at (PL := PL_link) (PI := PI) (c_W c) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    rewrite R1, X0, Hret, Hm.
    (* the apost at the write set and errno, then without errno *)
    eapply (apost_errno SK SEGS B LAWS ENV); [exact HAR|].
    eapply apost_leaf2.
    + exact HJ0.
    + apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low). exact HJ.
    + unfold rv_sp in Hlo. exact Hlo.
    + unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK. lia.
    + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
    + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
    + exact HP.
    + (* the bytes outside the frame window: rv_ewr is inside the write set and errno *)
      intros a Ha Hw HE. apply UN; [exact Ha | exact Hw |].
      intros Hr. apply HE. unfold rv_ewr in Hr. destruct Hr as [Hr|[Hr|[Hr|Hr]]].
      * left. exists (LA_G_NL + NK_NEXT, LA_G_NL + NK_MISUSE + 4).
        split; [left; reflexivity | cbn [fst snd]; unfold NK_NEXT, NK_MISUSE in *; lia].
      * left. exists (LA_G_NL + NK_NEXT, LA_G_NL + NK_MISUSE + 4).
        split; [left; reflexivity | cbn [fst snd]; unfold NK_NEXT, NK_MISUSE in *; lia].
      * left. exists (aarg (c_regs0 c) 1, aarg (c_regs0 c) 1 + aarg (c_regs0 c) 2).
        split; [right; left; reflexivity | cbn [fst snd]; unfold rv_buf, rv_len in Hr; lia].
      * right. exact Hr.
    + exact PR.
    + (* the frame window is present: the journal's stack window holds it *)
      pose proof HJ as (_ & HXO2 & (memS & HJi & _) & _).
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
      intros a Ha. apply Hpres. unfold rv_sp in Hlo, Hhi. clear - Ha Hlo Hhi HXO2. lia.
    + (* the write set and errno: g_nl (low), the buffer (amem_range), errno (low) *)
      intros x [((lo, hi) & Hin & Hx) | Hx].
      * destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; cbn [fst snd] in Hx.
        -- left. unfold LA_G_NL, NK_NEXT, NK_MISUSE, SHADOW_OFF in *. lia.
        -- unfold amem_range, rv_buf, rv_len in Hamr. unfold kLowMemEnd, SHADOW_OFF in *.
           destruct Hamr as [Hq|Hq]; [left; lia | right; lia].
      * left. unfold aerrno in Hx. unfold kLowMemEnd, SHADOW_OFF in *. lia.
    + (* Q: the allocator state and the blocks as at the call, and fuzz_recv_apost *)
      cbv beta. split; [destruct (c_Sc c); reflexivity|]. split; [apply Permutation_refl|].
      exact (HQ (ms_regs ms1) HA0).
Qed.
End w.

Print Assumptions rv_ret_ok.
