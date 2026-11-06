(* lib/A/ProgWorldRt.v -- fuzz_ctrl image A (libreac v1.9.0): the PROOFS of lib/A/ProgWorld.v's
   rt_of_core_stmt (Section RtOfCore) and RT_used_of_AR_stmt (Section RtUsed).  Written by a Theorem Labs lane; one
   writer.  lib/A/ProgWorld.v is a Theorem Labs lane's file and is NOT edited here: it is only Required.

   BUILD (type-check only, iteration evidence, never acceptance): rc=0 on FACTS ed6b6b7b0ab with PAU
   pau-libreac-v190, workspace (internal path) (a copy of (internal path) at a working branch 7ba9fe2f48), and `Print Assumptions
   rt_of_core` lists Rocq primitives only (PrimInt63.*, PrimString.*, PrimArray.array).  That build needs
   three LOCAL, NEVER COMMITTED stand-ins which replace port_core_refused_X by 0xX (planning core
   5d7c5ab2616): lib/A/AF0l.v, lib/A/AE2k.v, lib/A/AF0m.v.  lib/A/ACtlK.v and lib/A/ACtlCut.v need none:
   they are on the branch from 878cb7afbc4 (a Theorem Labs lane's frozen cut interface d3d572ab8f6).

   rule 24: NO function of the image is proved here.  Both lemmas are program-world facts about the core's own
   state: ctrl's narrowed runtime table ProgWorld.RT_used at a memory, from the core's AR.

   SHAPE (a Theorem Labs lane, 03:32Z).  RT_rest_of_AR, below, is every RT_used conjunct EXCEPT shadow_rw, from
   CtrlTSyms + AR alone.  It needs NO AR_states_vis0_shadow: each conjunct is one constant row of the bundle's
   table (ARm.am_const, Reusable/YG0n.v:211), which under CtrlTSyms (ts_const, A/AF0m.v:310) IS image A's
   Tfib_const (A/AF0m.v:279), read through the aview -> mrd bridge of lib/A/ProgWorld_Fs.v.  Then
     RT_used_of_AR = RT_rest_of_AR + shadow_rw, the latter from the file of record for that one conjunct,
                     lib/A/ProgWorldRtShadow.v (a Theorem Labs lane, afdf6883c32; its premises and binder
                     order are RT_used_of_AR_stmt's, so it applies with no adapter);
     rt_of_core   = RT_rest_of_AR at the cut's AR -- the FIRST conjunct of Reusable.YCbq.ajournal
                    (Reusable/YCbq.v:354) -- + shadow_rw from the carried A.ACtlCut.ctl_rt (A/ACtlCut.v:192).
   RT ignores sp and md: ctl_RT's sp and md arguments do not occur in its body (ProgWorld.v:161).

   REUSED, PROVED, Required (never copied): lib/A/ProgWorld_Fs.v's byte bridge -- pw_c8_bytes, pw_z4_bytes,
   pw_z1_bytes, pw_bytes_of_view, pw_bv8, pw_u64, pw_in_abs, pw_in_sym, pw_ext_range, pw_F_in_owned,
   pw_F_above (ASAN_GT = RT_GT = 0x5fe000 <= ly_F, from ALedger's al_img) and pw_app_mem_F -- and
   lib/A/ProgWorld.v's as_tp_RT_TP.  OWN, because ProgWorld_Fs has no such lemma: pwrt_zl_ok / pwrt_zl_nth /
   pwrt_cell_zl, which read a byte RANGE INSIDE one absolute row (the cf / opt / uw cells are sub-ranges of
   8-byte rows), and pwrt_bytes_split. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YK04 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YG00 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YCbq Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YConstIn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ProgWorld A.ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldRtShadow.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRT A.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.

(* The journal's sink_head is the core's own instance, as A.ACfn resolves it (A/AE2k.v:44). *)
#[local] Existing Instance A.AE2k.tfib_sink_head.

Notation segs := A.AB1v.tfibsegs (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   0. A byte RANGE inside one absolute row.  ProgWorld_Fs reads whole rows (pw_c8_bytes / pw_z4_bytes /
   pw_z1_bytes); the cf, opt and uw cells are sub-ranges of 8-byte rows, so they need this. *)

(* bs are the little-endian bytes of v from bit k up.  Decides by computation. *)
Fixpoint pwrt_zl_ok (v k : Z) (bs : list byte) : bool :=
  match bs with
  | nil => true
  | b :: t => andb (Z.eqb (bv_unsigned b) (Z.shiftr v k mod 2 ^ 8)) (pwrt_zl_ok v (k + 8) t)
  end.

Lemma pwrt_byte_eq : forall (b : byte) (x : Z), bv_unsigned b = (x mod 2 ^ 8)%Z -> b = Z_to_bv 8 x.
Proof.
  intros b x H. apply bv_eq. rewrite Z_to_bv_unsigned.
  change (bv_wrap 8 ?a) with (a mod 2 ^ 8)%Z. exact H.
Qed.

Lemma pwrt_zl_nth : forall (bs : list byte) (v k : Z) (i : nat),
  pwrt_zl_ok v k bs = true -> (i < length bs)%nat ->
  nth_error bs i = Some (Z_to_bv 8 (Z.shiftr v (k + 8 * Z.of_nat i))).
Proof.
  induction bs as [|b t IH]; intros v k i Hok Hi; cbn [length] in Hi; [lia|].
  cbn [pwrt_zl_ok] in Hok. apply andb_prop in Hok. destruct Hok as [Hb Ht].
  destruct i as [|j].
  - replace (k + 8 * Z.of_nat 0) with k by lia.
    cbn [nth_error]. f_equal. apply pwrt_byte_eq. apply Z.eqb_eq. exact Hb.
  - replace (k + 8 * Z.of_nat (S j)) with ((k + 8) + 8 * Z.of_nat j) by lia.
    cbn [nth_error]. apply IH; [exact Ht | lia].
Qed.

Lemma pwrt_le_byte_z : forall (v : Z) (w k : nat), (k < w)%nat ->
  lib.Reusable.YG0f.le_byte v w k = (Z.shiftr v (8 * Z.of_nat k) mod 2 ^ 8)%Z.
Proof.
  intros v w k Hk. unfold lib.Reusable.YG0f.le_byte.
  change 256 with (2 ^ 8)%Z. apply Lib.Mem.shiftr_mod_mod8; lia.
Qed.

Lemma pwrt_bytes_split : forall (m : word -> option byte) (ad : Z) (bs bs1 bs2 : list byte) (n : Z),
  bs = bs1 ++ bs2 -> n = Z.of_nat (length bs1) ->
  Lib.Mem.bytes_at A.Img0.rsegs m ad bs1 ->
  Lib.Mem.bytes_at A.Img0.rsegs m (ad + n) bs2 ->
  Lib.Mem.bytes_at A.Img0.rsegs m ad bs.
Proof.
  intros m ad bs bs1 bs2 n -> -> H1 H2.
  apply (proj2 (Lib.Mem.bytes_at_app A.Img0.rsegs m ad bs1 bs2)). split; assumption.
Qed.

Section PwrtRange.
Context {rc : lib.Reusable.YM05.RunCeil}.

Lemma pwrt_cell_zl : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte)
    (B : lib.Reusable.YG0f.asyms) (ly : lib.Reusable.YG0f.alayout)
    (a v : Z) (w off : nat) (bs : list byte) (ad : Z),
  lib.Reusable.YG0f.cell_holds B ly (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    (lib.Reusable.YG0f.ACell (lib.Reusable.YG0f.ANum a) w
       (lib.Reusable.YG0f.AV (lib.Reusable.YG0f.ANum v))) ->
  (off + length bs <= w)%nat ->
  pwrt_zl_ok v (8 * Z.of_nat off) bs = true ->
  ad = a + Z.of_nat off -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  Lib.Mem.bytes_at A.Img0.rsegs m ad bs.
Proof.
  intros W m B ly a v w off bs ad Hc Hw Hok -> H0 H1.
  apply (A.ProgWorld_Fs.pw_bytes_of_view W); [lia | lia |].
  intros i Hi.
  exists (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat off + 8 * Z.of_nat i))).
  split; [exact (pwrt_zl_nth bs v (8 * Z.of_nat off) i Hok Hi)|].
  unfold lib.Reusable.YG0f.cell_holds in Hc.
  cbn [lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_w] in Hc.
  specialize (Hc (off + i)%nat ltac:(lia)).
  cbn [lib.Reusable.YG0f.aeval] in Hc.
  replace (a + Z.of_nat off + Z.of_nat i) with (a + Z.of_nat (off + i)%nat) by lia.
  replace (8 * Z.of_nat off + 8 * Z.of_nat i) with (8 * Z.of_nat (off + i)%nat) by lia.
  rewrite Hc. f_equal.
  rewrite A.ProgWorld_Fs.pw_bv8.
  rewrite (pwrt_le_byte_z v w (off + i)%nat ltac:(lia)). reflexivity.
Qed.

End PwrtRange.

(* Membership of a row in image A's const table, by the row's own text and not by its position.  The in_eq / in_cons
   walk is quadratic in the table's length (a Theorem Labs lane 06:52Z); lib/Reusable/YConstIn.v's in_const_tbl decides it with one
   vm_compute of `existsb (row_eqb row) tbl` on a closed goal.  pwrt_mem stays for owned_extents, a two-row list of
   Z * Z that YConstIn's row_eqb (over acell) does not type. *)
Local Ltac pwrt_mem := repeat first [ apply in_eq | apply in_cons ].
Local Ltac pwrt_abs := apply A.ProgWorld_Fs.pw_in_abs; lib.Reusable.YConstIn.in_const_tbl.
Local Ltac pwrt_sym := apply A.ProgWorld_Fs.pw_in_sym; lib.Reusable.YConstIn.in_const_tbl.

(* the numeric side goals: every address of these rows is closed, so they decide by computation *)
Local Ltac pwrt_zle := apply Z.leb_le; vm_compute; reflexivity.
Local Ltac pwrt_zlt := apply Z.ltb_lt; vm_compute; reflexivity.
Local Ltac pwrt_nle := apply Nat.leb_le; vm_compute; reflexivity.
Local Ltac pwrt_vm := vm_compute; reflexivity.
Local Ltac pwrt_rng := split; [pwrt_zle | pwrt_zlt].

(* ---------------------------------------------------------------------------------------------------------
   1. RT_used except shadow_rw, from AR alone. *)
Section RtRest.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma RT_rest_of_AR :
  A.AF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    A.AsanRT.asan_cells m /\ A.AsanRT.asan_opt_cells m /\ A.AsanRT.asan_cf_cells m /\
    A.AsanRT.asan_uw_cells m /\ A.AsanRT.asan_fs_cells m /\
    Forall (fun p => In (fst p) A.ProgWorld.REAL_USED ->
                     Lib.Mem.bytes_at A.Img0.rsegs m (fst p) (Lib.Mem.le8 (Lib.Mem.wa (snd p))))
      A.AsanRT.RT_REALS.
Proof.
  intros HTS HL ly S W m md HAR.
  pose proof HAR as HAR0.
  destruct HAR as (HM & _ & _ & _ & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ HM) as Hlay.
  pose proof (lib.Reusable.YG0n.am_const _ _ _ _ HM) as Hconst.
  pose proof (lib.Reusable.YG0n.am_tsd _ _ _ _ HM) as Hlytsd.

  (* every row of image A's const table holds over this state's view *)
  assert (Hrow : forall c, In c (A.AF0m.Tfib_const ly) ->
            lib.Reusable.YG0f.cell_holds B ly
              (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) c).
  { intros c Hc. apply (proj1 (Forall_forall _ _) Hconst).
    rewrite (A.AF0m.ts_const B HTS ly). exact Hc. }

  (* the image's symbol values *)
  pose proof (A.ProgWorld.as_tp_RT_TP B HTS) as Htp.
  assert (Htsdly : lib.Reusable.YG0f.ly_tsd ly = A.AsanRT.RT_TSDMAIN).
  { rewrite Hlytsd, (A.AF0m.ts_tsd B HTS). reflexivity. }

  (* the fake stack and the dtv block, as owned application extents *)
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app ly Hlay)) as Happ.
  assert (HinF : lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_F ly)
                   lib.Reusable.YG0f.kFakeStackSize).
  { exact (Happ _ (A.ProgWorld_Fs.pw_F_in_owned ly)). }
  assert (HinD : lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_D ly) 4096).
  { apply (Happ (lib.Reusable.YG0f.ly_D ly, 4096)).
    unfold lib.Reusable.YG0f.owned_extents. pwrt_mem. }
  pose proof (A.ProgWorld_Fs.pw_ext_range _ _ HinF) as HF.
  pose proof (A.ProgWorld_Fs.pw_ext_range _ _ HinD) as HD.
  pose proof (A.ProgWorld_Fs.pw_F_above B ly S W m md HAR0) as HFgt.

  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).

  (* ---- asan_cells (17 rows) ---- *)
  - unfold A.AsanRT.asan_cells.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
            (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))).
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa8878)
               (lib.Reusable.YG0f.ANum 0x7fff8000));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x9fad0)
               (lib.Reusable.YG0f.ANum 0xa8878));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_z1_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa9558));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_rng | pwrt_rng].
    + apply (A.ProgWorld_Fs.pw_z1_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa9559));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_rng | pwrt_rng].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa0638)
               (lib.Reusable.YG0f.ANum 0xa9559));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_z4_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa8880));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_zle | pwrt_zle | pwrt_rng].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x9fb28)
               (lib.Reusable.YG0f.ANum 0xa8880));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_z1_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa80dc));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_rng | pwrt_rng].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa9560)
               (lib.Reusable.YG0f.ANum 0x7fffffffffff));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x9fae8)
               (lib.Reusable.YG0f.ANum 0xa9560));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa9568)
               (lib.Reusable.YG0f.ANum 0x0));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x9fad8)
               (lib.Reusable.YG0f.ANum 0xa9568));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa9570)
               (lib.Reusable.YG0f.ANum 0x0));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x9fae0)
               (lib.Reusable.YG0f.ANum 0xa9570));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa1930)
               (lib.Reusable.YG0f.ANum 0x97c0c));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa1938)
               (lib.Reusable.YG0f.ANum 0x98010));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x9faf0)
               (lib.Reusable.YG0f.ANum 0xa1938));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].

  (* ---- asan_opt_cells ---- *)
  - unfold A.AsanRT.asan_opt_cells.
    refine (conj _ (conj _ (conj _ _))).
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x9fac8)
               (lib.Reusable.YG0f.ANum 0xa6078));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    (* AF + 60: byte 4 of the row at 0xa60b0 *)
    + eapply (pwrt_cell_zl W m B ly 0xa60b0 0x100000055 8%nat 4%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x9fb20)
               (lib.Reusable.YG0f.ANum 0x138318));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_z4_bytes B ly W m (lib.Reusable.YG0f.ANum 0x138318));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_zle | pwrt_zle | pwrt_rng].

  (* ---- asan_cf_cells ---- *)
  - unfold A.AsanRT.asan_cf_cells.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x9fac0)
               (lib.Reusable.YG0f.ANum 0x13a3a8));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    (* CF + 32: the whole row at 0x13a3c8 *)
    + eapply (pwrt_cell_zl W m B ly 0x13a3c8 0x1e00010000 8%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 64: byte 0 of the row at 0x13a3e8 *)
    + eapply (pwrt_cell_zl W m B ly 0x13a3e8 0x0 8%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 84 *)
    + eapply (pwrt_cell_zl W m B ly 0x13a3fc 0x1 1%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 120 *)
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x13a420)
               (lib.Reusable.YG0f.ANum 18446744073709551615));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 137 *)
    + eapply (pwrt_cell_zl W m B ly 0x13a431 0x1 1%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 240: 21 bytes over the rows at 0x13a498, 0x13a4a0 and 0x13a4a8 *)
    + apply (pwrt_bytes_split m (A.AsanRT.RT_CF + 240) _
               (A.AsanRT.cf_b [0; 0; 0; 0; 1; 0; 1; 1])
               (A.AsanRT.cf_b [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0]) 8);
        [pwrt_vm | pwrt_vm | |].
      * eapply (pwrt_cell_zl W m B ly 0x13a498 0x101000100000000 8%nat 0%nat);
          [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
      * apply (pwrt_bytes_split m (A.AsanRT.RT_CF + 240 + 8) _
                 (A.AsanRT.cf_b [1; 1; 1; 1; 1; 1; 1; 1])
                 (A.AsanRT.cf_b [1; 1; 1; 1; 0]) 8);
          [pwrt_vm | pwrt_vm | |].
        -- eapply (pwrt_cell_zl W m B ly 0x13a4a0 0x101010101010101 8%nat 0%nat);
             [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
        -- eapply (pwrt_cell_zl W m B ly 0x13a4a8 0x1010101 8%nat 0%nat);
             [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* AF + 29: byte 5 of the row at 0xa6090 *)
    + eapply (pwrt_cell_zl W m B ly 0xa6090 0x101010000000001 8%nat 5%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].

  (* ---- asan_uw_cells ---- *)
  - unfold A.AsanRT.asan_uw_cells.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + eapply (pwrt_cell_zl W m B ly 0xa80e0 0x1 1%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_z4_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa80e4));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_zle | pwrt_zle | pwrt_rng].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x138320)
               (lib.Reusable.YG0f.ANum 0x1000));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x5db7b8)
               (lib.Reusable.YG0f.ANum 0x5fcbb8));
        [apply Hrow; pwrt_abs | pwrt_vm | reflexivity | pwrt_zle | pwrt_zle].
    (* the TSD main block holds the context map: a symbolic row *)
    + exists (Z_to_bv 64 (lib.Reusable.YG0f.ly_C ly)).
      apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATsd 0)
               (lib.Reusable.YG0f.AC 0)).
      * apply Hrow; pwrt_sym.
      * cbn [lib.Reusable.YG0f.aeval]. rewrite Htsdly. unfold A.AsanRT.RT_TSDMAIN. lia.
      * cbn [lib.Reusable.YG0f.aeval]. lia.
      * pwrt_zle.
      * pwrt_zle.

  (* ---- asan_fs_cells ---- *)
  - unfold A.AsanRT.asan_fs_cells.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    (* TLS_INDEX: the two words at 0xa07b0 and 0xa07b8 *)
    + apply (pwrt_bytes_split m A.AsanRT.RT_TLSIDX _
               (Lib.Mem.le8 (Z_to_bv 64 1)) (Lib.Mem.le8 (Z_to_bv 64 (-2048))) 8);
        [reflexivity | pwrt_vm | |].
      * apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa07b0)
                 (lib.Reusable.YG0f.ANum 1));
          [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
      (* the row's value is 0xfffffffffffff800, the goal's is -2048: same word, different Z, so the row is
         read as a byte range and not through pw_c8_bytes' value equality *)
      * eapply (pwrt_cell_zl W m B ly 0xa07b8 0xfffffffffffff800 8%nat 0%nat);
          [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa07c0)
               (lib.Reusable.YG0f.ANum 8));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x5db808)
               (lib.Reusable.YG0f.ANum 0x5db830));
        [apply Hrow; pwrt_abs | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0x5db838)
               (lib.Reusable.YG0f.ANum 0x5dc010));
        [apply Hrow; pwrt_abs | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* TP holds the side stack, whose whole window is application memory *)
    + exists (Z_to_bv 64 (lib.Reusable.YG0f.ly_F ly)).
      assert (HFb : 0 <= lib.Reusable.YG0f.ly_F ly < 2 ^ 64)
        by (unfold lib.Reusable.YG0f.kFakeStackSize in HF; lia).
      split.
      * apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATp 0)
                 (lib.Reusable.YG0f.AF 0)).
        -- apply Hrow; pwrt_sym.
        -- cbn [lib.Reusable.YG0f.aeval]. rewrite Htp. lia.
        -- cbn [lib.Reusable.YG0f.aeval]. lia.
        -- pwrt_zle.
        -- pwrt_zle.
      * rewrite (A.ProgWorld_Fs.pw_u64 _ HFb).
        unfold A.AsanRT.fs_value_ok, A.AsanRT.RT_GT, A.AsanRT.RT_FS_SIZE.
        split; [lia|]. split; [exact (lib.Reusable.YG0f.lo_F_al ly Hlay)|].
        split; [unfold A.Prog.asan_stack_malloc_c.ASAN_GT in HFgt; lia|].
        intros a Ha. apply (A.ProgWorld_Fs.pw_app_mem_F ly a HinF).
        unfold lib.Reusable.YG0f.kFakeStackSize. lia.
    (* TP + 8 holds the dtv block *)
    + exists (Z_to_bv 64 (lib.Reusable.YG0f.ly_D ly)).
      assert (HDb : 0 <= lib.Reusable.YG0f.ly_D ly < 2 ^ 64) by lia.
      split; [|split].
      * apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATp 8)
                 (lib.Reusable.YG0f.AD 0)).
        -- apply Hrow; pwrt_sym.
        -- cbn [lib.Reusable.YG0f.aeval]. rewrite Htp. unfold A.AsanRT.RT_TP. lia.
        -- cbn [lib.Reusable.YG0f.aeval]. lia.
        -- pwrt_zle.
        -- pwrt_zle.
      * rewrite (A.ProgWorld_Fs.pw_u64 _ HDb). lia.
      * rewrite (A.ProgWorld_Fs.pw_u64 _ HDb).
        unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
        destruct HinD as [HA0 [HA1 | [HA1 HA2]]];
          unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *;
          pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [CR _]; lia.

  (* ---- the four REAL slots the lifted runs read ---- *)
  - apply (proj2 (Forall_forall _ _)). intros p Hp.
    cbv [A.AsanRT.RT_REALS] in Hp. cbn [In] in Hp.
    repeat match type of Hp with _ \/ _ => destruct Hp as [Hp | Hp] end.
    all: try contradiction.
    all: subst p; cbn [fst snd]; intros Hu.
    all: try (destruct Hu as [E|[E|[E|[E|[]]]]]; discriminate E).
    (* REAL_TLS_GET_ADDR *)
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa1870)
               (lib.Reusable.YG0f.ANum 0x98800));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    (* REAL_BCMP *)
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa17f0)
               (lib.Reusable.YG0f.ANum 0x97b0c));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    (* REAL_MEMCHR *)
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa17f8)
               (lib.Reusable.YG0f.ANum 0x97b10));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    (* REAL_MEMCMP *)
    + apply (A.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum 0xa17e8)
               (lib.Reusable.YG0f.ANum 0x97bdc));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
Qed.

(* RT_used at ANY state of the core, for the callee-internal re-based stretches: RT_rest_of_AR, and the one
   conjunct it leaves out from the named hypothesis, through a Theorem Labs lane's hand lib/A/ProgWorldRtShadow.v. *)
Lemma RT_used_of_AR : A.ProgWorld.RT_used_of_AR_stmt B.
Proof.
  unfold A.ProgWorld.RT_used_of_AR_stmt.
  intros HTS HL Hvis0 ly S W m md HAR.
  destruct (RT_rest_of_AR HTS HL ly S W m md HAR)
    as (Hcells & Hopt & Hcf & Huw & Hfs & Hreals).
  unfold A.ProgWorld.RT_used.
  exact (conj Hcells
           (conj (A.ProgWorldRtShadow.shadow_rw_of_AR B HTS HL Hvis0 ly S W m md HAR)
              (conj Hopt (conj Hcf (conj Huw (conj Hfs Hreals)))))).
Qed.

End RtRest.

(* ---------------------------------------------------------------------------------------------------------
   2. rt_of_core: RT_rest_of_AR at the cut's AR, and shadow_rw from the carried ctl_rt. *)
Section RtOfCore.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Lemma rt_of_core : A.ProgWorld.rt_of_core_stmt B MT XM_LIB RLO RHI FP.
Proof.
  unfold A.ProgWorld.rt_of_core_stmt.
  intros HTS HL cx own k ly3 S3 W3 ms3 md3 Hbase Hj Hrt.
  destruct Hj as (HAR & _).
  destruct Hrt as (Hac & Hsh & Hro).
  destruct (RT_rest_of_AR B HTS HL ly3 S3 W3 (ms_mem ms3) md3 HAR)
    as (Hcells & Hopt & Hcf & Huw & Hfs & Hreals).
  unfold A.ProgWorld.ctl_RT, A.ProgWorld.RT_used.
  exact (conj Hcells (conj Hsh (conj Hopt (conj Hcf (conj Huw (conj Hfs Hreals)))))).
Qed.

End RtOfCore.

Print Assumptions RT_used_of_AR.
Print Assumptions rt_of_core.
