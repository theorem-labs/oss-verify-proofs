(* fm's runtime contract for the strncmp interceptor in the donor's form: astrncmp_realizes (RtBzHStr.v) at
   PC_strncmp = 0x4518c, the one-instruction trampoline `j 0x45fa4` (B/Bz/A/I_tramp.v tramp_strncmp) in front of
   the interceptor body, whose effect B/Bz/A/I_strncmp.v istrncmp_spec states (its range check's Section
   hypothesis discharged by B/Bz/A/R_isPoisoned.v rip_proof).
   - pre side: RtBzPre.v turns the contract's premises into the walk's (bytes, range check, stack, store, the
     runtime's fixed cells) and writes the call site's registers out as the walk states them (bz_canon);
   - post side: RtBzLift.v reads the walk at the call site (srr_of_canon_bz) and gives the donor-form post
     (rt_post_ro_win); RtBzPre.v bz_window gives its window facts;
   - the answer: the walk returns strncmp_res (B/Bz/A/IcptSpec.v:38), which is 0 exactly when the compared
     prefixes of the two strings with their NULs agree (strn_eq, RtBzHStr.v); proved here on the byte values,
     as FMspec_str.v does for strncasecmp (shared list facts: RtBzSpecStrn.v).
   Only the runtime layer is imported (RtBzHBase, RtBzHStr, RtBzPre, RtBzSpecStrn): no program module. *)
(* Relocated to plugin-hostd/fuzz_command from omx-clap-core/fuzz_manifest's program-free split
   (proofs/omx-clap-core/fuzz_manifest/lib/A/FMstrncmp.v): module paths, TfibSyms renamed CmdBSyms, the trampoline
   of this image; the strncmp interceptor's cells and range check (FMrt_pre_str.v icells_sc_of_ARm,
   icells_sc_of_ARm_clean, chk_ok_of_cstr) moved here from the generic RtBzPre.v, read with this image's constant
   table. *)
(* The image-B twin of lib/A/Rt/RtLStrncmp.v, for fuzz_command.asan-ubsan (no function proved): the B
   kit's walk (lib/B/Bz), the B bridge, B's strncmp trampoline 0x4518c in place of fuzz_manifest's PC_strncmp (A's), and
   every A address replaced by its B twin (each re-read from image B); the proof text is the A file's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtBzHBase RtBzHStr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtBzLift RtBzPre RtBzClean.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtBzSpecStrn.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strncmpw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.IcptSpec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strncmpw3.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strncmp.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_tramp.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.R_isPoisoned.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module SCS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.IcptSpec.
Module SCP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strncmpw3.
Module SCW := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strncmp.
Module TRP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_tramp.
Module RIP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.R_isPoisoned.
Module BSC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strncmpw.

(* ---- the walk's answer, read on the byte values ---- *)

(* the index the walk stops at (SCS.strncmp_idx_aux) on the byte values *)
Fixpoint zcmp_idx (k : nat) (m1 m2 : list Z) {struct k} : nat :=
  match k with
  | O => O
  | S k' => match m1, m2 with
            | x :: r1, y :: r2 => if negb (x =? y) || (x =? 0) then O else S (zcmp_idx k' r1 r2)
            | _, _ => O
            end
  end.

Lemma strncmp_idx_aux_z : forall (k : nat) (m1 m2 : list Z),
  Forall (fun c => 0 <= c < 256) m1 -> Forall (fun c => 0 <= c < 256) m2 ->
  SCS.strncmp_idx_aux (map (Z_to_bv 8) m1) (map (Z_to_bv 8) m2) k = zcmp_idx k m1 m2.
(* SCS.strncmp_idx_aux recurses on its first list, so each case first exposes that list's head *)
Proof.
  induction k as [|k IH]; intros m1 m2 H1 H2; [destruct m1; reflexivity|].
  destruct m1 as [|x r1]; [reflexivity|]. destruct m2 as [|y r2]; [reflexivity|].
  inversion H1 as [|? ? Hx H1']; subst. inversion H2 as [|? ? Hy H2']; subst.
  cbn [map SCS.strncmp_idx_aux zcmp_idx].
  rewrite (RtBzSpecStrn.u8 x Hx), (RtBzSpecStrn.u8 y Hy).
  destruct (negb (x =? y) || (x =? 0))%bool; [reflexivity|].
  rewrite (IH r1 r2 H1' H2'). reflexivity.
Qed.

Definition zcmp (x y : Z) : Z := if x <? y then -1 else if y <? x then 1 else 0.

(* the walk's answer (SCS.strncmp_res) on the byte values *)
Definition zcmp_res (k : nat) (m1 m2 : list Z) : Z :=
  let i := zcmp_idx k m1 m2 in if (i =? k)%nat then 0 else zcmp (nth i m1 0) (nth i m2 0).

Lemma zcmp_zero : forall x y, zcmp x y = 0 <-> x = y.
Proof.
  intros x y. unfold zcmp.
  destruct (x <? y) eqn:E1; destruct (y <? x) eqn:E2;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in E1, E2; split; intros; lia.
Qed.

Lemma zcmp_res_stop : forall k x y r1 r2, (negb (x =? y) || (x =? 0))%bool = true ->
  zcmp_res (S k) (x :: r1) (y :: r2) = zcmp x y.
Proof. intros k x y r1 r2 E. unfold zcmp_res. cbn [zcmp_idx]. rewrite E. reflexivity. Qed.

Lemma zcmp_res_step : forall k x r1 r2, x <> 0 -> zcmp_res (S k) (x :: r1) (x :: r2) = zcmp_res k r1 r2.
Proof.
  intros k x r1 r2 Hx. unfold zcmp_res. cbn [zcmp_idx]. rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq x 0) Hx). reflexivity.
Qed.

Lemma nul_last_nonempty : forall m, RtBzSpecStrn.nul_last m -> m <> [].
Proof. intros m (l & -> & _). destruct l; discriminate. Qed.

(* a zero answer and the program part's prefix equality are the same claim *)
Lemma zcmp_res_zero : forall (k : nat) (m1 m2 : list Z),
  RtBzSpecStrn.nul_last m1 -> RtBzSpecStrn.nul_last m2 ->
  (zcmp_res k m1 m2 = 0 <-> firstn k m1 = firstn k m2).
Proof.
  induction k as [|k IH]; intros m1 m2 N1 N2.
  { unfold zcmp_res. cbn [zcmp_idx firstn]. split; intros _; reflexivity. }
  destruct m1 as [|x r1]; [exfalso; exact (nul_last_nonempty _ N1 eq_refl)|].
  destruct m2 as [|y r2]; [exfalso; exact (nul_last_nonempty _ N2 eq_refl)|].
  cbn [firstn].
  destruct (Z.eq_dec x y) as [<-|NE].
  - destruct (Z.eq_dec x 0) as [->|NX].
    + rewrite zcmp_res_stop by reflexivity.
      assert (Hr1 : r1 = []) by (apply (RtBzSpecStrn.nul_last_cons 0 r1 N1); reflexivity).
      assert (Hr2 : r2 = []) by (apply (RtBzSpecStrn.nul_last_cons 0 r2 N2); reflexivity).
      subst r1 r2. split; intros _; reflexivity.
    + rewrite (zcmp_res_step k x r1 r2 NX).
      rewrite (IH r1 r2 (RtBzSpecStrn.nul_last_tl x r1 N1 NX) (RtBzSpecStrn.nul_last_tl x r2 N2 NX)).
      split; [intros Hq; rewrite Hq; reflexivity | intros Hq; injection Hq; intros; assumption].
  - rewrite zcmp_res_stop by (apply orb_true_iff; left; apply negb_true_iff, Z.eqb_neq; exact NE).
    rewrite zcmp_zero.
    split; [intros Hxy; contradiction | intros Hq; injection Hq; intros; assumption].
Qed.

(* the walk stops at or before each string's NUL *)
Lemma zcmp_idx_lt : forall (k : nat) (m1 m2 : list Z),
  RtBzSpecStrn.nul_last m1 -> RtBzSpecStrn.nul_last m2 ->
  (zcmp_idx k m1 m2 < length m1)%nat /\ (zcmp_idx k m1 m2 < length m2)%nat.
Proof.
  induction k as [|k IH]; intros m1 m2 N1 N2.
  - destruct N1 as (l1 & -> & _). destruct N2 as (l2 & -> & _).
    cbn [zcmp_idx]. rewrite !length_app. cbn [length]. lia.
  - destruct m1 as [|x r1]; [exfalso; exact (nul_last_nonempty _ N1 eq_refl)|].
    destruct m2 as [|y r2]; [exfalso; exact (nul_last_nonempty _ N2 eq_refl)|].
    cbn [zcmp_idx length].
    destruct (negb (x =? y) || (x =? 0))%bool eqn:EB; [lia|].
    apply orb_false_iff in EB as [EL EX]. apply negb_false_iff, Z.eqb_eq in EL. apply Z.eqb_neq in EX.
    subst y.
    destruct (IH r1 r2 (RtBzSpecStrn.nul_last_tl x r1 N1 EX) (RtBzSpecStrn.nul_last_tl x r2 N2 EX)). lia.
Qed.

Lemma strncmp_res_z : forall (n : Z) (m1 m2 : list Z), 0 <= n ->
  Forall (fun c => 0 <= c < 256) m1 -> Forall (fun c => 0 <= c < 256) m2 ->
  (zcmp_idx (Z.to_nat n) m1 m2 < length m1)%nat -> (zcmp_idx (Z.to_nat n) m1 m2 < length m2)%nat ->
  SCS.strncmp_res n (map (Z_to_bv 8) m1) (map (Z_to_bv 8) m2) = zcmp_res (Z.to_nat n) m1 m2.
Proof.
  intros n m1 m2 Hn H1 H2 L1 L2.
  unfold SCS.strncmp_res, zcmp_res, SCS.strncmp_idx.
  rewrite (strncmp_idx_aux_z (Z.to_nat n) m1 m2 H1 H2).
  set (i := zcmp_idx (Z.to_nat n) m1 m2) in *.
  assert (Hi : Z.to_nat (Z.of_nat i) = i) by apply Nat2Z.id.
  rewrite Hi.
  destruct (Nat.eq_dec i (Z.to_nat n)) as [E|NE].
  - rewrite E. replace (Z.of_nat (Z.to_nat n) =? n) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite Nat.eqb_refl. reflexivity.
  - replace (Z.of_nat i =? n) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (i =? Z.to_nat n)%nat with false by (symmetry; apply Nat.eqb_neq; exact NE).
    rewrite (RtBzSpecStrn.nth_error_map_nth m1 i L1), (RtBzSpecStrn.nth_error_map_nth m2 i L2).
    rewrite !RtBzSpecStrn.u8; [reflexivity | |].
    + apply (proj1 (Forall_forall _ _) H2 (nth i m2 0)). apply nth_In. exact L2.
    + apply (proj1 (Forall_forall _ _) H1 (nth i m1 0)). apply nth_In. exact L1.
Qed.

Lemma strncmp_res_range : forall n b1 b2, -1 <= SCS.strncmp_res n b1 b2 <= 1.
Proof.
  intros n b1 b2. unfold SCS.strncmp_res. cbv zeta.
  destruct (SCS.strncmp_idx n b1 b2 =? n); [lia|].
  destruct (nth_error b1 (Z.to_nat (SCS.strncmp_idx n b1 b2))) as [u|];
  destruct (nth_error b2 (Z.to_nat (SCS.strncmp_idx n b1 b2))) as [w|]; try lia.
  destruct (bv_unsigned u <? bv_unsigned w); [lia|]. destruct (bv_unsigned w <? bv_unsigned u); lia.
Qed.

(* what the walk needs of two C strings and what it answers: they are long enough for the compared length
   (strncmp_ok), that length is at most each string with its NUL (so cstr_ok's range facts cover it), and the
   answer is 0 exactly when the compared prefixes agree *)
Lemma strncmp_strs : forall (n : Z) (l1 l2 : list Z), 0 <= n ->
  Forall (fun c => 0 <= c < 256 /\ c <> 0) l1 -> Forall (fun c => 0 <= c < 256 /\ c <> 0) l2 ->
  SCS.strncmp_ok n (map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) (map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0]) /\
  0 <= SCS.strncmp_sz n (map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) (map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0])
    <= Z.of_nat (length l1) + 1 /\
  0 <= SCS.strncmp_sz n (map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) (map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0])
    <= Z.of_nat (length l2) + 1 /\
  (SCS.strncmp_res n (map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) (map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0]) = 0 <->
   strn_eq (Z.to_nat n) l1 l2).
Proof.
  intros n l1 l2 Hn F1 F2.
  assert (Eb1 : map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0] = map (Z_to_bv 8) (l1 ++ [0])) by (rewrite map_app; reflexivity).
  assert (Eb2 : map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0] = map (Z_to_bv 8) (l2 ++ [0])) by (rewrite map_app; reflexivity).
  rewrite Eb1, Eb2.
  assert (N1 : RtBzSpecStrn.nul_last (l1 ++ [0])).
  { exists l1. split; [reflexivity|].
    split; (eapply Forall_impl; [|exact F1]); intros c Hc; first [exact (proj2 Hc) | exact (proj1 Hc)]. }
  assert (N2 : RtBzSpecStrn.nul_last (l2 ++ [0])).
  { exists l2. split; [reflexivity|].
    split; (eapply Forall_impl; [|exact F2]); intros c Hc; first [exact (proj2 Hc) | exact (proj1 Hc)]. }
  assert (R1 : Forall (fun c => 0 <= c < 256) (l1 ++ [0])).
  { apply Forall_app. split; [eapply Forall_impl; [|exact F1]; intros c Hc; exact (proj1 Hc)|].
    apply Forall_cons; [lia | apply Forall_nil]. }
  assert (R2 : Forall (fun c => 0 <= c < 256) (l2 ++ [0])).
  { apply Forall_app. split; [eapply Forall_impl; [|exact F2]; intros c Hc; exact (proj1 Hc)|].
    apply Forall_cons; [lia | apply Forall_nil]. }
  destruct (zcmp_idx_lt (Z.to_nat n) _ _ N1 N2) as (L1 & L2).
  assert (EI : SCS.strncmp_idx n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0]))
             = Z.of_nat (zcmp_idx (Z.to_nat n) (l1 ++ [0]) (l2 ++ [0]))).
  { unfold SCS.strncmp_idx. rewrite (strncmp_idx_aux_z _ _ _ R1 R2). reflexivity. }
  assert (ES : SCS.strncmp_sz n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0]))
             = Z.min (Z.of_nat (zcmp_idx (Z.to_nat n) (l1 ++ [0]) (l2 ++ [0])) + 1) n).
  { unfold SCS.strncmp_sz. rewrite EI. reflexivity. }
  pose proof L1 as L1'. pose proof L2 as L2'.
  rewrite length_app in L1', L2'. cbn [length] in L1', L2'.
  split; [unfold SCS.strncmp_ok; rewrite ES, !length_map, !length_app; cbn [length]; lia|].
  split; [rewrite ES; lia|]. split; [rewrite ES; lia|].
  rewrite (strncmp_res_z n _ _ Hn R1 R2 L1 L2). unfold strn_eq. apply zcmp_res_zero; assumption.
Qed.

(* ---- the strncmp interceptor's fixed cells and range check (FMrt_pre_str.v) ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : CmdBSyms B.

Local Ltac c8 M := eapply (ro_c8 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M := eapply (ro_c1 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].

(* the strncmp interceptor's cells (Bz I_strncmpw.v:25) *)
Lemma icells_sc_of_ARm : forall ly S H mem, ARm B ly S (aview tfibsegs H mem) -> BSC.icells_sc (mrestrict H mem).
Proof.
  intros ly S H mem M. unfold BSC.icells_sc.
  split; [|split; [|split; [|split]]].
  - c8 M.
  - c8 M.
  - c8 M.
  - apply rw_of_ro; [c1 M | vm_compute; reflexivity].
  - c1 M.
Qed.

(* the same fixed cells on the cleaned store: each cell lies below 2^47 and holds the bytes it held, and a
   writable cell's addresses are writable in the image (decided) *)
Local Ltac roc RE H :=
  apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | exact H].
Local Ltac rwc RE H :=
  apply (RtBzClean.rw_cells_clean _ _ _ RE);
  [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity | exact H].

Lemma icells_sc_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> BSC.icells_sc (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. destruct (icells_sc_of_ARm ly S H mem M) as (C1 & C2 & C3 & C4 & C5).
  split; [|split; [|split; [|split]]].
  - roc RE C1.
  - roc RE C2.
  - roc RE C3.
  - rwc RE C4.
  - roc RE C5.
Qed.

(* a C string's range check over its first n <= len + 1 bytes *)
Lemma chk_ok_of_cstr : forall ly S (W : world tfibsegs) mem md p (l : list Z) n,
  AR tfibsegs B ly S W mem md -> cstr_ok tfibsegs W mem p l -> 0 <= n <= Z.of_nat (length l) + 1 ->
  BQ.chk_ok (mrestrict (w_H W) mem) p n.
Proof.
  intros ly S W mem md p l n HAR (_ & Hp & _ & H32 & Ham & HRA & HV & _) Hn.
  apply (chk_ok_of_pre B ly S W mem md p n HAR); [lia | lia | apply (amem_range_mono _ _ _ Ham); lia | |].
  - apply (ra_prefix _ _ _ _ HRA). lia.
  - intros Hn0. apply (hull_prefix _ _ _ _ HV). lia.
Qed.

End k.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.

Theorem astrncmp_holds : astrncmp_realizes tfibsegs B PC_strncmp.
Proof.
  unfold astrncmp_realizes. intros ly S W regs mem md x y n l1 l2 HPRE HROM HROMO G10 G11 G12 Hn C1 C2.
  pose proof HPRE as (HEP & HCEIL & HSLO & HPRS).
  pose proof HEP as (HAR & _).
  pose proof C1 as (CS1 & Hx0 & Hx8 & Hx32 & _).
  pose proof C2 as (CS2 & Hy0 & Hy8 & Hy32 & _).
  pose proof alloc_ceiling_lt as HCL.
  destruct (bytes_of_cstr W mem x l1 CS1 ltac:(lia) ltac:(lia)) as (BY1m & _ & F1).
  destruct (bytes_of_cstr W mem y l2 CS2 ltac:(lia) ltac:(lia)) as (BY2m & _ & F2).
  destruct (strncmp_strs n l1 l2 ltac:(lia) F1 F2) as (OK & SZ1 & SZ2 & RES).
  set (b1 := map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) in *.
  set (b2 := map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0]) in *.
  set (sz := SCS.strncmp_sz n b1 b2) in *.
  set (r := SCS.strncmp_res n b1 b2) in *.
  pose proof (chk_ok_of_cstr B ly S W mem md x l1 sz HAR C1 SZ1) as CK1m.
  pose proof (chk_ok_of_cstr B ly S W mem md y l2 sz HAR C2 SZ2) as CK2m.
  destruct (stk_of_pre B ly S W regs mem md STK_RT_STR HPRE ltac:(unfold STK_RT_STR, ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  pose proof (rom_eq_of_views B W mem TB HROM HROMO) as RE.
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - STK_RT_STR) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - STK_RT_STR) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_sc_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as IC.
  assert (BY1 : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x b1).
  { apply (bytes_at_clean _ x _ RE);
      [unfold b1; rewrite length_app, length_map; cbn [length];
       unfold BM.UTOP, STK_RT_STR, ESTACK in *; lia | exact BY1m]. }
  assert (BY2 : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) y b2).
  { apply (bytes_at_clean _ y _ RE);
      [unfold b2; rewrite length_app, length_map; cbn [length];
       unfold BM.UTOP, STK_RT_STR, ESTACK in *; lia | exact BY2m]. }
  assert (CK1 : BQ.chk_ok (clean (mrestrict (w_H W) mem)) x sz).
  { apply (chk_ok_clean _ x _ RE); [lia | unfold STK_RT_STR, ESTACK in *; lia | exact CK1m]. }
  assert (CK2 : BQ.chk_ok (clean (mrestrict (w_H W) mem)) y sz).
  { apply (chk_ok_clean _ y _ RE); [lia | unfold STK_RT_STR, ESTACK in *; lia | exact CK2m]. }
  set (lo := spZ regs - STK_RT_STR) in *.
  set (m := mrestrict (w_H W) mem) in *.
  assert (Hlo : alloc_ceiling <= lo) by exact HCs.
  eapply (bz_run_clean B TB W PC_strncmp regs mem md _ _ HROM HROMO).
  - apply bz_canon. apply TRP.tramp_strncmp.
    eapply (SCW.istrncmp_spec RIP.rip_proof) with (p1 := x) (p2 := y) (n := n) (b1 := b1) (b2 := b2) (lo := lo).
    + exact G10.
    + exact G11.
    + exact G12.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold lo, STK_RT_STR, ESTACK. lia.
    + unfold OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.R_m2s.kHighShadowEnd. lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
    + lia.
    + exact BY1.
    + exact BY2.
    + exact OK.
    + lia.
    + lia.
    + left. change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold lo, STK_RT_STR, ESTACK in *. lia.
    + left. change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold lo, STK_RT_STR, ESTACK in *. lia.
    + exact CK1.
    + exact CK2.
    + exact M2S.
    + exact IC.
    + exact MI.
  - intros msc ms' model' HQ Hcl Heqv Hsbm _.
    unfold SCP.istrncmp_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & ST').
    destruct (bz_window (clean m) m' (spZ regs) 2256 lo MU ST') as (MO & MN).
    { unfold lo, STK_RT_STR, ESTACK. lia. }
    { unfold TFIB_IMG_END. lia. }
    eapply (rt_post_ro_win_clean B LAWS STK_RT_STR 2256 ly S W regs mem md _ _ ms' model' (r mod 2 ^ 64) HPRE).
    + unfold STK_RT_STR, ESTACK. lia.
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
    + transitivity (Z_to_bv 64 r); [reflexivity|]. unfold w64. rewrite Z_to_bv64_mod. reflexivity.
    + apply Z.mod_pos_bound. lia.
    + rewrite <- RES. pose proof (strncmp_res_range n b1 b2) as Hr. fold r in Hr.
      Z.div_mod_to_equations. lia.
    + exact MO.
    + exact MN.
Qed.

End s.
