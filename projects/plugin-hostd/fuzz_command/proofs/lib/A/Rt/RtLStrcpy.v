(* The strcpy entry of fuzz_command.asan at its trampoline 0x451d8 (`j 0x4c760`, the image's objdump listing, line
   18794), lifted from the committed body walk to our runtime contract (RtString.v astrcpy_realizes):
   - the trampoline: A/Bz/A/I_tramp.v tramp_strcpy;
   - the interceptor and musl's strcpy under it: A/Bz/A/I_strcpyw.v iscpy_spec, its two Section hypotheses
     discharged by A/Bz/A/R_isPoisoned.v rip_proof (the range check) and A/Prog/strcpy_wrap_sc.v sc_proof (musl's
     strcpy body); depth 2,224 bytes (ISTRCPY_DEPTH), inside the contract's ESTACK window;
   - the bridge: the walk runs on the cleaned store (RtBzClean.bz_run_clean); its premises come from the contract
     through RtBzAdapt (strings with the word loop's slack, range checks, the stack window) and RtBzPre (the
     runtime's fixed cells); its end state gives art_post with the write set [d, d + |s| + 1) through
     RtBzAdaptP.art_post_clean. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YK1b YP03 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import
RtDefs RtBzHBase RtBzHStr RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtBzStr RtString.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strcpyw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_tramp.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strcpy_wrap_sc.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module SCW := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strcpyw.
Module TRP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_tramp.
Module RIP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.R_isPoisoned.
Module SCP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strcpy_wrap_sc.

(* ---- arithmetic ---- *)

(* the rounded end is the end of the string with its terminator and the slack after it *)
Lemma aword_end_succ : forall p k, RtString.aword_end p (k + 1) = p + k + 1 + (7 - (p + k) mod 8).
Proof.
  intros p k. unfold RtString.aword_end. replace (p + (k + 1)) with (p + k + 1) by lia.
  rewrite mod_neg_succ. lia.
Qed.

(* ---- the destination as the walk reads it ---- *)

Section d. Context {fx : YK11.FPState}.

Lemma tfib_segs_readable : forall sg, In sg tfibsegs -> seg_readable sg = true.
Proof.
  assert (H : forallb seg_readable tfibsegs = true) by (vm_compute; reflexivity).
  intros sg Hin. exact (proj1 (forallb_forall _ _) H sg Hin).
Qed.

(* a byte the store may be written at is a byte the walks' reader finds: every writable segment of the image is
   readable *)
Lemma mrd_of_writable : forall (m : word -> option byte) a,
  writable_at tfibsegs m a -> BM.mrd BI.asegs m (Z_to_bv 64 a) <> None.
Proof.
  intros m a HW. unfold writable_at, wview in HW. unfold BM.mrd, BPE.seg_rom, memory_read.
  change BI.asegs with tfibsegs. change (Z.of_N 1) with 1.
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  destruct (find_segment tfibsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:F; [|exfalso; exact (HW eq_refl)].
  destruct (seg_writable sg) eqn:Wr; [|exfalso; exact (HW eq_refl)].
  pose proof (YK04.find_segment_some_spec _ _ _ _ F) as (Hin & _ & _).
  rewrite (tfib_segs_readable sg Hin). change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) as [c|];
    [cbn; discriminate | exfalso; exact (HW eq_refl)].
Qed.

End d.

(* a destination byte is not dropped by the cleaning: above the low band no segment covers it, and in the low band
   it is not a read-only image byte *)
Lemma dst_dc : forall a, 0 <= a < 2 ^ 47 -> (a < kLowMemEnd -> ~ in_rom tfibsegs a) -> Dc (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hro. pose proof (u64z a ltac:(lia)) as Eu.
  destruct (Z_lt_le_dec a kLowMemEnd) as [L|L].
  - apply Dc_false; [| rewrite Eu; unfold BM.UTOP; lia].
    destruct (BM.ro_addr BI.asegs (Z_to_bv 64 a)) eqn:E; [|reflexivity].
    exfalso. apply (Hro L). rewrite <- Eu. exact (RtBzStr.ro_addr_in_rom _ E).
  - apply Dc_above. rewrite Eu. unfold TFIB_IMG_END, BM.UTOP, kLowMemEnd in *. lia.
Qed.

(* bytes that are present and writable are a block of cells the walk may write *)
Lemma rw_cb_of_present : forall (m : word -> option byte) (d : Z) (n : nat),
  0 <= d -> d + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> BM.mrd BI.asegs m (BM.wa (d + Z.of_nat i)) <> None /\
                           wview BI.asegs m (BM.wa (d + Z.of_nat i)) <> None) ->
  exists junk, BS.rw_cells BI.asegs m d [BC.CB n junk].
Proof.
  intros m d n Hd Hn H.
  exists (map (fun j => match BM.mrd BI.asegs m (BM.wa (d + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end)
             (seq 0 n)).
  split; [split|].
  - cbn [BC.cells_wf BC.cell_wf]. split; [rewrite length_map, length_seq; reflexivity | exact I].
  - cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
    split; [exact Hd|]. split; [rewrite length_map, length_seq; exact Hn|].
    intros i Hi. rewrite length_map, length_seq in Hi.
    rewrite nth_error_map, nth_error_seq.
    replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    cbn [option_map Nat.add].
    destruct (BM.mrd BI.asegs m (BM.wa (d + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
    exfalso. exact (proj1 (H i Hi) E).
  - split; [exact Hd|]. split; [cbn [BC.cells_size BC.csize]; lia|].
    intros i Hi. cbn [BC.cells_size BC.csize] in Hi.
    specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. exact (proj2 H).
Qed.

(* the walk's stack window is above the image, so every byte it leaves there is in the store *)
Lemma win_present : forall (m : word -> option byte) lo hi, BF.stk BI.asegs m lo hi -> TFIB_IMG_END <= lo ->
  forall a, lo <= a < hi -> m (Z_to_bv 64 a) <> None.
Proof.
  intros m lo hi (Hlo & Hhi & ST) Himg a Ha.
  destruct (ST a ltac:(lia)) as (_ & b & Hb). unfold BM.mrd, BM.wa in Hb.
  destruct (m (Z_to_bv 64 a)) as [c|] eqn:E; [discriminate|].
  assert (HN : BPE.seg_rom BI.asegs (Z_to_bv 64 a) = None) by exact (seg_rom_none_high a ltac:(lia)).
  rewrite HN in Hb. discriminate.
Qed.

(* ---- the strcpy interceptor's fixed cells (Bz I_strcpyw.v:33 icells_cp, and the init flag) ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : CmdBSyms B.

Lemma icells_cp_of_ARm : forall ly S H mem, ARm B ly S (aview tfibsegs H mem) -> SCW.icells_cp (mrestrict H mem).
Proof.
  intros ly S H mem M. unfold SCW.icells_cp.
  split; [|split].
  - apply (ro_c8 B TB ly S H mem 0xa8250 0x9f1cc M); [vm_compute; reflexivity | lia | lia | lia].
  - apply (ro_c8 B TB ly S H mem 0xa63e8 0xae8b8 M); [vm_compute; reflexivity | lia | lia | lia].
  - apply (ro_c1 B TB ly S H mem 0xae8d5 1 M); [vm_compute; reflexivity | lia | lia | lia].
Qed.

Lemma flag_of_ARm : forall ly S H mem, ARm B ly S (aview tfibsegs H mem) ->
  BS.rw_cells BI.asegs (mrestrict H mem) 0xb1d98 [BC.C1 (Z_to_bv 8 1)].
Proof.
  intros ly S H mem M. apply rw_of_ro; [|vm_compute; reflexivity].
  apply (ro_c1 B TB ly S H mem 0xb1d98 1 M); [vm_compute; reflexivity | lia | lia | lia].
Qed.

(* on the cleaned store: each cell lies below 2^47 and holds the bytes it held; the flag's byte is writable in the
   image (decided) *)
Local Ltac roc RE H :=
  apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | exact H].

Lemma icells_cp_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> SCW.icells_cp (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. destruct (icells_cp_of_ARm ly S H mem M) as (C1 & C2 & C3).
  split; [|split].
  - roc RE C1.
  - roc RE C2.
  - roc RE C3.
Qed.

Lemma flag_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) ->
  BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict H mem)) 0xb1d98 [BC.C1 (Z_to_bv 8 1)].
Proof.
  intros ly S H mem RE M.
  apply (RtBzClean.rw_cells_clean _ _ _ RE);
    [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity | exact (flag_of_ARm ly S H mem M)].
Qed.

End k.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.

Theorem cmd_strcpy : RtString.astrcpy_realizes tfibsegs B 0x451d8.
Proof.
  unfold RtString.astrcpy_realizes.
  intros ly S W regs mem md d x s HPRE G10 G11 Hd0 Hx0 SX RD AMx WR AMd HRO TAIL HSEP HROM.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _).
  unfold astr_len in *.
  pose proof RD as (_ & _ & Hn & _).
  pose proof WR as (_ & _ & _ & HWa & _).
  assert (Hx47 : x + Z.of_nat (length s) + 8 <= 2 ^ 47 - 1)
    by (clear - AMx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMx; lia).
  assert (Hd47 : d + Z.of_nat (length s) + 8 <= 2 ^ 47 - 1)
    by (clear - AMd; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMd; lia).
  (* the read-only views and the cleaned store *)
  pose proof (rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  (* the stack: the contract's window, cleaned, cut to the walk's depth *)
  destruct (stk_of_stk_pre B ESTACK ly S W regs mem md HPRE ltac:(unfold ESTACK; lia)) as (ST0 & HC0 & HCs & Hsp47).
  assert (HIMG : TFIB_IMG_END <= spZ regs - ESTACK) by (clear - HC0 HCs; unfold TFIB_IMG_END; lia).
  assert (STc : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - ESTACK) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - ESTACK) (spZ regs));
      [exact HIMG | unfold BM.UTOP; lia | exact ST0]. }
  destruct (BF.stk_split BI.asegs _ _ (spZ regs - 2224) _ STc ltac:(unfold ESTACK; lia)) as (_ & ST).
  assert (HIMG2 : TFIB_IMG_END <= spZ regs - 2224) by (clear - HIMG; unfold ESTACK in HIMG; lia).
  (* the source with the word loop's slack *)
  destruct (bz_str_slack W mem x s SX TAIL ltac:(lia) ltac:(unfold astr_len; lia)) as (BYm & PAD).
  unfold astr_len in BYm, PAD.
  set (sl := tail_bytes W mem (x + Z.of_nat (length s))) in *.
  pose proof (tail_bytes_length W mem (x + Z.of_nat (length s))) as SLL. fold sl in SLL.
  assert (SL7 : Z.of_nat (length sl) <= 7)
    by (clear - SLL; pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)); lia).
  assert (BY : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x (s ++ Z_to_bv 8 0 :: sl)).
  { apply (bytes_at_clean _ x _ RE); [|exact BYm].
    rewrite length_app. cbn [length]. clear - SL7 Hx47. unfold BM.UTOP. lia. }
  (* the separation the walk states over source + slack *)
  assert (OV : d + Z.of_nat (length s) + 1 <= x \/ x + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= d).
  { clear - HSEP SLL. rewrite aword_end_succ in HSEP. rewrite SLL. lia. }
  clear HSEP.
  (* the range checks *)
  assert (CKx : BQ.chk_ok (clean (mrestrict (w_H W) mem)) x (Z.of_nat (length s) + 1)).
  { apply (chk_ok_clean _ x _ RE); [lia | lia |].
    exact (chk_of_read ESTACK W regs mem x (Z.of_nat (length s) + 1) (Z.of_nat (length s) + 1) (Z.of_nat (length s))
             RD AMx ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (CKd : BQ.chk_ok (clean (mrestrict (w_H W) mem)) d (Z.of_nat (length s) + 1)).
  { apply (chk_ok_clean _ d _ RE); [lia | lia |].
    exact (chk_of_write B ESTACK ly S W regs mem d (Z.of_nat (length s) + 1) (Z.of_nat (length s) + 1)
             (Z.of_nat (length s)) WR AMd ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* both strings are apart from the walk's stack window *)
  pose proof (sep_of_read ESTACK W regs mem x (Z.of_nat (length s) + 1) ltac:(unfold ESTACK; lia) ltac:(lia) RD)
    as SEPx.
  pose proof (sep_of_write B ESTACK ly S W regs mem d (Z.of_nat (length s) + 1) ltac:(unfold ESTACK; lia)
                ltac:(lia) WR) as SEPd.
  (* the destination: present and writable bytes of the cleaned store *)
  assert (DSTb : forall i, (i < length s + 1)%nat ->
     BM.mrd BI.asegs (clean (mrestrict (w_H W) mem)) (BM.wa (d + Z.of_nat i)) <> None /\
     wview BI.asegs (clean (mrestrict (w_H W) mem)) (BM.wa (d + Z.of_nat i)) <> None).
  { intros i Hi.
    destruct (HWa (d + Z.of_nat i) ltac:(lia)) as (HW & _ & _).
    assert (DC : Dc (Z_to_bv 64 (d + Z.of_nat i)) = false).
    { apply dst_dc; [lia | intros Hlow; exact (HRO (d + Z.of_nat i) ltac:(lia) Hlow)]. }
    unfold BM.wa. rewrite (mrd_clean_nd _ _ DC), (wview_clean_nd _ _ DC).
    split; [exact (mrd_of_writable _ _ HW) | exact HW]. }
  destruct (rw_cb_of_present (clean (mrestrict (w_H W) mem)) d (length s + 1) ltac:(lia) ltac:(lia) DSTb)
    as (junk & DST).
  (* the runtime's fixed cells *)
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_cp_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ICP.
  pose proof (flag_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as FLG.
  (* the run *)
  eapply (bz_run_clean B TB W 0x451d8 regs mem md _ _ (romN_of_rt B W mem HROM)
            (rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - apply evt_grows. apply bz_canon. apply TRP.tramp_strcpy.
    apply (SCW.iscpy_spec RIP.rip_proof SCP.sc_proof
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (* the 31 registers *)
             _ _ _ (* F fc m *)
             d x s sl junk (spZ regs - 2224)).
    + exact G10.
    + exact G11.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
    + unfold R_m2s.kHighShadowEnd. clear - HC0 HCs. unfold ESTACK in HCs. lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). exact Hsp47.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact BY.
    + exact (proj2 SX).
    + exact PAD.
    + exact DST.
    + exact OV.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). clear - SEPx SL7. unfold ESTACK in SEPx. lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). clear - SEPd. unfold ESTACK in SEPd. lia.
    + exact CKx.
    + exact CKd.
    + exact M2S.
    + exact FLG.
    + exact ICP.
    + exact MI.
  - intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Emsc & MU & _ & _ & ST' & CPY).
    apply (art_post_clean B LAWS ESTACK 2224 ly S W regs mem md _ _ msc ms' model' HPRE); subst msc.
    + unfold ESTACK. lia.
    + exact Hcl.
    + exact Heqv.
    + exact Hsbm.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + (* outside the window and the destination the store is the caller's *)
      intros xw Hx HEx. change (m' xw = clean (mrestrict (w_H W) mem) xw).
      apply MU. cbn [BF.outside]. split; [exact HEx | split; [exact Hx | exact I]].
    + (* every byte of the window is in the store *)
      exact (win_present m' _ _ ST' HIMG2).
    + exact GROW.
    + (* the destination: unowned, in range, not dropped, not hidden *)
      intros a Ha. cbv beta in Ha.
      destruct (HWa a ltac:(lia)) as (HW & Hown & _).
      split; [exact Hown|]. split; [lia|]. split.
      * apply dst_dc; [lia | intros Hlow; exact (HRO a Ha Hlow)].
      * exact (wH_false_of_writable W mem a HW).
    + (* the answer and the copied bytes *)
      intros regs' mem' HR _ HEv. split.
      * rewrite HR. reflexivity.
      * intros i Hi.
        rewrite length_app in Hi. cbn [length] in Hi.
        rewrite (HEv (d + Z.of_nat i)) by (cbv beta; lia).
        destruct CPY as ((_ & BYc) & _). cbn [BC.cells_bytes BC.cbytes] in BYc. rewrite app_nil_r in BYc.
        destruct BYc as (_ & _ & BYc).
        assert (Hi' : (i < length (s ++ [Z_to_bv 8 0]))%nat) by (rewrite length_app; cbn [length]; lia).
        transitivity (option_map (fun b : byte => bv_unsigned b) (nth_error (s ++ [Z_to_bv 8 0]) i));
          [f_equal; exact (BYc i Hi') |].
        rewrite (nth_error_nth' (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) Hi'). reflexivity.
Qed.

End s.
