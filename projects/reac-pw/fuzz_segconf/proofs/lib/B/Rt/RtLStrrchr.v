(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLStrrchr.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* Interface row 11 of reac-pw/fuzz_segconf's ASan+UBSan image B (provenance/evidence/interceptors/INTERFACE-A-interceptors.md):
   the strrchr wrapper at its 4-byte jump PC_strrchr = 0x43ab8 (lib/A/Rt/SegRtPC.v), lifted from the relocated Bz walk to
   the accepted contract text RtSeg.astrrchr_realizes (lib/A/Rt/RtSeg.v).
   - the walk: lib/A/Bz/A/I_strrchr.v istrrchr_spec (relocated from plugin-hostd/fuzz_reply a0dcb5cdc736; the code it
     walks is the same in both images): the jump 0x43ab8, the wrapper 0x45e50 (the init gate, internal_strlen, the
     range check of len + 1 bytes), then REAL(strrchr) = musl strrchr 0x9b678, which calls the strlen wrapper through
     its jump 0x43a98 and tail-calls musl memrchr 0x9afa4 over len + 1 bytes; depth 4400 bytes, inside the contract's
     2 * ESTACK window. Its two Section hypotheses are met by R_isPoisoned.rip_proof (the range check's slow arm) and
     wrap_kit_sl.sl_proof (musl strlen under the strlen wrapper).
   - the glue, as fuzz_command's RtLStrcpy.v / RtLStrncmpR.v: the walk runs on the cleaned store
     (RtBzClean.bz_run_clean); its premises come from the contract through RtBzAdapt (the string with the word loop's
     slack, the range check, the stack window) and RtBzPre (the runtime's fixed cells, rows of the per-binary record's
     constant table); its end state gives art_post with no write set (RtBzAdaptP.art_post_ro_clean).
   - the answer: the walk's rchr_res (the last index below len + 1 holding c) is RtSeg's last_at, and both are
     SegModel.strrchr (lib/Spec/SegModel.v) on a NUL-free string. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YK1b YP03 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import
RtDefs RtBzHBase RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg SegRtPC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strrchr.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strlen.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.wrap_kit_sl.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module SRW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strrchr.
Module SNW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strnlenw.
Module SLW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strlen.
Module RIP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Module PSL := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.wrap_kit_sl.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.

(* ---- lists ---- *)

Lemma nth_skipn_add : forall (A : Type) (l : list A) (n k : nat) (d : A),
  nth k (skipn n l) d = nth (n + k) l d.
Proof.
  intros A l n. revert l. induction n as [|n IH]; intros l k d; [reflexivity|].
  destruct l as [|a l]; [destruct k; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

(* an element of [skipn n l] is [l] at an index from n on *)
Lemma in_skipn_nth : forall (A : Type) (l : list A) (n : nat) (d y : A),
  In y (skipn n l) -> exists k, (n <= k < length l)%nat /\ nth k l d = y.
Proof.
  intros A l n d y Hy. apply (In_nth _ _ d) in Hy as (k & Hk & Ek).
  rewrite length_skipn in Hk. rewrite nth_skipn_add in Ek.
  exists (n + k)%nat. split; [lia | exact Ek].
Qed.

(* the element of [l] at an index from n on is in [skipn n l] *)
Lemma nth_in_skipn : forall (A : Type) (l : list A) (n k : nat) (d : A),
  (n <= k < length l)%nat -> In (nth k l d) (skipn n l).
Proof.
  intros A l n k d Hk. replace k with (n + (k - n))%nat by lia. rewrite <- nth_skipn_add.
  apply nth_In. rewrite length_skipn. lia.
Qed.

(* ---- last_at (RtSeg.v) has at most one witness ---- *)

Lemma last_at_unique : forall (l : list Z) c j1 j2, RtSeg.last_at l c j1 -> RtSeg.last_at l c j2 -> j1 = j2.
Proof.
  intros l c j1 j2 (L1 & N1 & A1) (L2 & N2 & A2).
  destruct (Nat.lt_trichotomy j1 j2) as [H|[H|H]]; [|exact H|].
  - exfalso. apply A1. rewrite <- N2. apply nth_in_skipn. lia.
  - exfalso. apply A2. rewrite <- N1. apply nth_in_skipn. lia.
Qed.

(* ---- SegModel.strrchr is last_at ---- *)

(* the accumulator of SegModel.last_idx: what it ends with, from the index i on *)
Lemma last_idx_inv : forall c (l : list Z) (i : nat) (acc : option nat),
  (forall j, SM.last_idx c l i acc = Some j ->
     (acc = Some j /\ ~ In c l) \/
     ((i <= j < i + length l)%nat /\ nth (j - i) l 0 = c /\ ~ In c (skipn (S (j - i)) l))) /\
  (SM.last_idx c l i acc = None -> acc = None /\ ~ In c l).
Proof.
  intros c l. induction l as [|b l IH]; intros i acc.
  - cbn [SM.last_idx]. split.
    + intros j E. left. split; [exact E | intros []].
    + intros E. split; [exact E | intros []].
  - cbn [SM.last_idx]. destruct (Z.eqb_spec b c) as [Eb|Eb].
    + (* b is c: the accumulator becomes Some i *)
      destruct (IH (S i) (Some i)) as (HS & HN). split.
      * intros j E. right. destruct (HS j E) as [(Ea & Nl)|(Hr & Hn & Ha)].
        -- injection Ea as <-. replace (i - i)%nat with O by lia. cbn [nth skipn length].
           split; [lia|]. split; [exact Eb | exact Nl].
        -- replace (j - i)%nat with (S (j - S i)) by lia. cbn [nth skipn length].
           split; [lia|]. split; [exact Hn | exact Ha].
      * intros E. destruct (HN E) as (Ea & _). discriminate Ea.
    + destruct (IH (S i) acc) as (HS & HN). split.
      * intros j E. destruct (HS j E) as [(Ea & Nl)|(Hr & Hn & Ha)].
        -- left. split; [exact Ea|]. intros [Hb|Hl]; [exact (Eb Hb) | exact (Nl Hl)].
        -- right. replace (j - i)%nat with (S (j - S i)) by lia. cbn [nth skipn length].
           split; [lia|]. split; [exact Hn | exact Ha].
      * intros E. destruct (HN E) as (Ea & Nl).
        split; [exact Ea|]. intros [Hb|Hl]; [exact (Eb Hb) | exact (Nl Hl)].
Qed.

Lemma last_idx_last_at : forall c (l : list Z) j, SM.last_idx c l 0 None = Some j -> RtSeg.last_at l c j.
Proof.
  intros c l j E. destruct (proj1 (last_idx_inv c l 0 None) j E) as [(Ea & _)|(Hr & Hn & Ha)];
    [discriminate Ea|].
  rewrite Nat.sub_0_r in Hn, Ha. split; [lia|]. split; [exact Hn | exact Ha].
Qed.

Lemma last_idx_none : forall c (l : list Z), SM.last_idx c l 0 None = None -> ~ In c l.
Proof. intros c l E. exact (proj2 (proj2 (last_idx_inv c l 0 None) E)). Qed.

(* on a NUL-free string SegModel.strrchr names the last index of c, and None exactly when c does not occur *)
Theorem strrchr_last_at : forall (l : list Z) c j, SM.nulfree l ->
  SM.strrchr l c = Some j <-> RtSeg.last_at l c j.
Proof.
  intros l c j Hn. unfold SM.strrchr. rewrite (SM.cut_nul_id l Hn). split.
  - exact (last_idx_last_at c l j).
  - intros HL. destruct (SM.last_idx c l 0 None) as [j'|] eqn:E.
    + f_equal. exact (last_at_unique l c j' j (last_idx_last_at c l j' E) HL).
    + exfalso. destruct HL as (Hj & Hv & _). apply (last_idx_none c l E). rewrite <- Hv. apply nth_In. exact Hj.
Qed.

Theorem strrchr_none : forall (l : list Z) c, SM.nulfree l ->
  SM.strrchr l c = None <-> ~ In c l.
Proof.
  intros l c Hn. unfold SM.strrchr. rewrite (SM.cut_nul_id l Hn). split.
  - exact (last_idx_none c l).
  - intros HN. destruct (SM.last_idx c l 0 None) as [j|] eqn:E; [|reflexivity].
    exfalso. destruct (last_idx_last_at c l j E) as (Hj & Hv & _). apply HN. rewrite <- Hv. apply nth_In. exact Hj.
Qed.

(* the byte values of a C string hold no 0 *)
Lemma nulfree_zs : forall s : list byte, ~ In (Z_to_bv 8 0) s -> SM.nulfree (map (fun b : byte => bv_unsigned b) s).
Proof.
  intros s HN. unfold SM.nulfree. intros Hin. apply in_map_iff in Hin as (b & Eb & Hb). apply HN.
  replace (Z_to_bv 8 0) with b; [exact Hb | apply bv_eq; rewrite Eb; reflexivity].
Qed.

(* ---- the walk's answer (I_strrchr.v rchr_res) is last_at ---- *)

Lemma rchr_idx_spec : forall (bs : list byte) c (j : nat), (j <= length bs)%nat ->
  (SRW.rchr_idx c bs j = None -> forall k, (k < j)%nat -> bv_unsigned (nth k bs (Z_to_bv 8 0)) <> c) /\
  (forall i, SRW.rchr_idx c bs j = Some i ->
     (i < j)%nat /\ bv_unsigned (nth i bs (Z_to_bv 8 0)) = c /\
     forall k, (i < k < j)%nat -> bv_unsigned (nth k bs (Z_to_bv 8 0)) <> c).
Proof.
  intros bs c j. induction j as [|j IH]; intros Hj.
  - cbn [SRW.rchr_idx]. split; [intros _ k Hk; lia | intros i E; discriminate E].
  - destruct (IH ltac:(lia)) as (HN & HS).
    destruct (nth_error bs j) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
    assert (Nb : nth j bs (Z_to_bv 8 0) = b) by (apply nth_error_nth; exact Eb).
    cbn [SRW.rchr_idx]. rewrite Eb.
    destruct (Z.eqb_spec (bv_unsigned b) c) as [Ec|Ec].
    + split; [intros E; discriminate E|].
      intros i E. injection E as <-. split; [lia|]. split; [rewrite Nb; exact Ec | intros k Hk; lia].
    + split.
      * intros E k Hk. destruct (Nat.eq_dec k j) as [->|Hkj]; [rewrite Nb; exact Ec | exact (HN E k ltac:(lia))].
      * intros i E. destruct (HS i E) as (Hi & Hv & Ha). split; [lia|]. split; [exact Hv|].
        intros k Hk. destruct (Nat.eq_dec k j) as [->|Hkj]; [rewrite Nb; exact Ec | exact (Ha k ltac:(lia))].
Qed.

(* with c <> 0 the walk never answers the terminator: its answer is 0 when c is not in the string, else x plus
   the last index of c *)
Theorem rchr_res_last_at : forall x c (s : list byte), 0 < c < 256 ->
  (SRW.rchr_res x c (s ++ [Z_to_bv 8 0]) (S (length s)) = 0 /\
     ~ In c (map (fun b : byte => bv_unsigned b) s)) \/
  (exists j, RtSeg.last_at (map (fun b : byte => bv_unsigned b) s) c j /\
     SRW.rchr_res x c (s ++ [Z_to_bv 8 0]) (S (length s)) = x + Z.of_nat j).
Proof.
  intros x c s Hc.
  assert (L : (S (length s) <= length (s ++ [Z_to_bv 8 0]))%nat) by (rewrite length_app; cbn [length]; lia).
  (* below the terminator the byte list is the string *)
  assert (Ek : forall k, (k < length s)%nat -> nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = nth k s (Z_to_bv 8 0))
    by (intros k Hk; apply app_nth1; exact Hk).
  assert (EZ : forall k, nth k (map (fun b : byte => bv_unsigned b) s) 0 = bv_unsigned (nth k s (Z_to_bv 8 0))).
  { intros k. exact (map_nth (fun b : byte => bv_unsigned b) s (Z_to_bv 8 0) k). }
  unfold SRW.rchr_res.
  destruct (SRW.rchr_idx c (s ++ [Z_to_bv 8 0]) (S (length s))) as [i|] eqn:E;
    destruct (rchr_idx_spec (s ++ [Z_to_bv 8 0]) c (S (length s)) L) as (HN & HS).
  - destruct (HS i E) as (Hi & Hv & Ha).
    (* the terminator holds 0, not c *)
    assert (Hil : (i < length s)%nat).
    { destruct (Nat.eq_dec i (length s)) as [->|Hne]; [|lia]. exfalso.
      rewrite app_nth2, Nat.sub_diag in Hv by lia. cbn [nth] in Hv. change (bv_unsigned (Z_to_bv 8 0)) with 0 in Hv.
      lia. }
    right. exists i. split; [|reflexivity].
    split; [rewrite length_map; exact Hil|]. split; [rewrite EZ, <- (Ek i Hil); exact Hv|].
    intros Hin. apply (in_skipn_nth _ _ (S i) 0 c) in Hin as (k & Hk & Ekv).
    rewrite length_map in Hk. rewrite EZ, <- (Ek k ltac:(lia)) in Ekv.
    exact (Ha k ltac:(lia) Ekv).
  - left. split; [reflexivity|]. intros Hin.
    apply (In_nth _ _ 0) in Hin as (k & Hk & Ekv). rewrite length_map in Hk.
    rewrite EZ, <- (Ek k Hk) in Ekv. exact (HN E k ltac:(lia) Ekv).
Qed.

(* ---- the wrapper's fixed cells, rows of the record's constant table (A/AF0m.v) ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : SegBSyms B.

Local Ltac c8 M := eapply (ro_c8 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M := eapply (ro_c1 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac roc RE H :=
  apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | exact H].
Local Ltac rwc RE H :=
  apply (RtBzClean.rw_cells_clean _ _ _ RE);
  [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity | exact H].

(* the strnlen / strlen wrappers' shared cells (I_strnlenw.v icells_sn): the common-flags and shadow-offset pointer
   words, the shadow offset, the "initialised" flag (writable) and the strlen flag byte *)
Lemma icells_sn_of_ARm : forall ly S H mem, ARm B ly S (aview tfibsegs H mem) -> SNW.icells_sn (mrestrict H mem).
Proof.
  intros ly S H mem M. unfold SNW.icells_sn.
  split; [c8 M|]. split; [c8 M|]. split; [c8 M|].
  split; [apply rw_of_ro; [c1 M | vm_compute; reflexivity] | c1 M].
Qed.

Lemma icells_sn_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> SNW.icells_sn (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. destruct (icells_sn_of_ARm ly S H mem M) as (C1 & C2 & C3 & C4 & C5).
  split; [roc RE C1|]. split; [roc RE C2|]. split; [roc RE C3|]. split; [rwc RE C4 | roc RE C5].
Qed.

(* REAL(strlen) (I_strlen.v icells_sl) *)
Lemma icells_sl_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> SLW.icells_sl (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. unfold SLW.icells_sl.
  assert (C : SLW.icells_sl (mrestrict H mem)) by (unfold SLW.icells_sl; c8 M).
  roc RE C.
Qed.

(* the strchr-family flag byte (common flags + 0xfd) and REAL(strrchr) (I_strrchr.v icells_srr) *)
Lemma icells_srr_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> SRW.icells_srr (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M.
  assert (C : SRW.icells_srr (mrestrict H mem)) by (unfold SRW.icells_srr; split; [c1 M | c8 M]).
  unfold SRW.icells_srr in *. destruct C as (C1 & C2). split; [roc RE C1 | roc RE C2].
Qed.

End k.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

Theorem seg_strrchr : RtSeg.astrrchr_realizes tfibsegs B SegRtPC.PC_strrchr.
Proof.
  unfold RtSeg.astrrchr_realizes, SegRtPC.PC_strrchr.
  intros ly S W regs mem md x c s HPRE G10 G11 Hc Hx SX RD AMx TAIL HROM.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _).
  unfold astr_len in *.
  pose proof RD as (_ & _ & Hn & _).
  assert (Hx47 : x + Z.of_nat (length s) + 8 <= 2 ^ 47 - 1)
    by (clear - AMx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMx; lia).
  (* the read-only views and the cleaned store *)
  pose proof (rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  (* the stack: the contract's window, cleaned *)
  destruct (stk_of_stk_pre B (2 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (HIMG : TFIB_IMG_END <= spZ regs - 2 * ESTACK) by (clear - HC0 HCs; unfold TFIB_IMG_END; lia).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 2 * ESTACK) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - 2 * ESTACK) (spZ regs));
      [exact HIMG | unfold BM.UTOP; lia | exact ST0]. }
  (* the string with the word loop's slack *)
  destruct (bz_str_slack W mem x s SX TAIL ltac:(lia) ltac:(unfold astr_len; lia)) as (BYm & PAD).
  unfold astr_len in BYm, PAD.
  set (sl := tail_bytes W mem (x + Z.of_nat (length s))) in *.
  pose proof (tail_bytes_length W mem (x + Z.of_nat (length s))) as SLL. fold sl in SLL.
  assert (SL7 : Z.of_nat (length sl) <= 7)
    by (clear - SLL; pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)); lia).
  assert (BY : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x (s ++ Z_to_bv 8 0 :: sl)).
  { apply (bytes_at_clean _ x _ RE); [|exact BYm].
    rewrite length_app. cbn [length]. clear - SL7 Hx47. unfold BM.UTOP. lia. }
  (* the range check over the string and its NUL *)
  assert (CK : BQ.chk_ok (clean (mrestrict (w_H W) mem)) x (Z.of_nat (length s) + 1)).
  { apply (chk_ok_clean _ x _ RE); [lia | lia |].
    exact (chk_of_read (2 * ESTACK) W regs mem x (Z.of_nat (length s) + 1) (Z.of_nat (length s) + 1)
             (Z.of_nat (length s)) RD AMx ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* the string and its slack are apart from the walk's stack window *)
  pose proof (sep_of_read (2 * ESTACK) W regs mem x (Z.of_nat (length s) + 1) ltac:(unfold ESTACK; lia)
                ltac:(lia) RD) as SEPx.
  (* the runtime's fixed cells *)
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_sn_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ISN.
  pose proof (icells_sl_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ISL.
  pose proof (icells_srr_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ISR.
  (* the run: the jump, the wrapper, musl strrchr, the strlen wrapper, musl memrchr *)
  eapply (bz_run_clean B TB W 0x43ab8 regs mem md _ _ (romN_of_rt B W mem HROM)
            (rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - apply evt_grows. apply bz_canon.
    apply (SRW.istrrchr_spec RIP.rip_proof PSL.sl_proof
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (* the 31 registers *)
             _ _ _ (* F fc m *)
             x c s sl (spZ regs - 2 * ESTACK)).
    + exact G10.
    + exact G11.
    + lia.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold ESTACK. lia.
    + unfold BR.kHighShadowEnd. clear - HC0 HCs. lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
    + lia.
    + lia.
    + lia.
    + exact BY.
    + exact (proj2 SX).
    + exact PAD.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). clear - SEPx SL7. unfold ESTACK in SEPx. lia.
    + exact CK.
    + exact M2S.
    + exact ISN.
    + exact ISL.
    + exact ISR.
    + exact MI.
  - (* the post: the window is the only change, and the answer *)
    intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & _
                    & _ & ST').
    destruct (bz_window (clean (mrestrict (w_H W) mem)) m' (spZ regs) 4400 (spZ regs - 2 * ESTACK) MU ST')
      as (MO & MN); [unfold ESTACK; lia | exact HIMG |].
    apply (art_post_ro_clean B LAWS (2 * ESTACK) 4400 ly S W regs mem md _ _ ms' model' HPRE
             ltac:(unfold ESTACK; lia) Hcl Heqv Hsbm
             eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(keep_regs) MO MN GROW).
    intros regs' mem' HR _.
    assert (A10 : getr regs' 10%bv
                  = Z_to_bv 64 (SRW.rchr_res x c (s ++ [Z_to_bv 8 0]) (Datatypes.S (length s))))
      by (rewrite (HR 10%bv); reflexivity).
    rewrite A10.
    destruct (rchr_res_last_at x c s Hc) as [(E0 & NI)|(j & HL & Ej)].
    + left. split; [rewrite E0; reflexivity | exact NI].
    + right. exists j. split; [exact HL | rewrite Ej; reflexivity].
Qed.

(* the same answer in SegModel's words (lib/Spec/SegModel.v strrchr), for a caller that states its program
   against the model *)
Corollary seg_strrchr_model : forall x c (s : list byte), 0 < c < 256 -> ~ In (Z_to_bv 8 0) s ->
  forall v, ((v = 0 /\ ~ In c (map (fun b : byte => bv_unsigned b) s)) \/
             (exists j, RtSeg.last_at (map (fun b : byte => bv_unsigned b) s) c j /\ v = x + Z.of_nat j)) <->
            v = match SM.strrchr (map (fun b : byte => bv_unsigned b) s) c with
                | Some j => x + Z.of_nat j
                | None => 0
                end.
Proof.
  intros x c s Hc HN v. pose proof (nulfree_zs s HN) as NF.
  destruct (SM.strrchr (map (fun b : byte => bv_unsigned b) s) c) as [j|] eqn:E.
  - pose proof (proj1 (strrchr_last_at _ c j NF) E) as HL. split.
    + intros [(_ & NI)|(j' & HL' & ->)].
      * exfalso. destruct HL as (Hj & Hv & _). apply NI. rewrite <- Hv. apply nth_In. exact Hj.
      * rewrite (last_at_unique _ c j' j HL' HL). reflexivity.
    + intros ->. right. exists j. split; [exact HL | reflexivity].
  - pose proof (proj1 (strrchr_none _ c NF) E) as NI. split.
    + intros [(-> & _)|(j' & HL' & _)]; [reflexivity|].
      exfalso. destruct HL' as (Hj & Hv & _). apply NI. rewrite <- Hv. apply nth_In. exact Hj.
    + intros ->. left. split; [reflexivity | exact NI].
Qed.

End s.

(* ---- the closing: the record's laws discharged by the core's own law proof ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the per-binary record of fuzz_segconf.asan (A/AF0m.v) *)
Hypothesis HB : SegBSyms B.

Theorem seg_strrchr_closed : RtSeg.astrrchr_realizes tfibsegs B SegRtPC.PC_strrchr.
Proof. exact (seg_strrchr B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
End closed.

Print Assumptions seg_strrchr_closed.
