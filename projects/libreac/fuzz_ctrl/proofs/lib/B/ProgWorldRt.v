(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldRt.v (a working branch 9a4a1740d9e, re-synced
   to a working branch a48c4068c6e, whose text is the same at 1d23ced37fd: A adds RT_used_of_AR from
   lib/A/ProgWorldRtShadow.v and Requires YK11 YM05 YK04 YO09 from lib.Reusable; B takes both): the
   same lemmas, statements and proof steps with the image-B modules (A.AsanRT / A.Img0 / A.ACtlK / A.ACtlCut /
   A.ProgWorld / A.ProgWorld_Fs / A.ProgWorldRtShadow / A.Prog.asan_stack_malloc_c -> B.*, A.AF0m / A.AB1v / A.AE2k /
   A.ACfn -> lib.Reusable.YF0m / YB1v / YE2k / YCfn).  Six-module gate: YK11 / YM05 / YO09 (the core copies, as A
   takes them) are Required as `From ...fuzz_ctrl.lib.Reusable Require YK11 YM05 YK04 YO09`, as A writes it, and named
   lib.Reusable.X, as A names them.  Image-B Require difference: YP09 (also in lib/B/Reusable) and Lib.Mem (also in
   lib/B/Bz/Lib) are Required by their CORE path and Lib.Mem is named lib.Lib.Mem (fix_require6.py, as
   lib/B/ProgWorld.v on the base), where A writes `Require Reusable.YP09` / `Require ... Lib.Mem`.
   Differences in the proof text only, no statement differs: (1) every row address is written by its B.AsanRT name
   (e.g. B.AsanRT.CELL_K, B.AsanRT.RT_AF + 56) where A writes the image-A literal; (2) the value of a row read as a
   byte range (pwrt_cell_zl) is left to unification with its row in lib.Reusable.YF0m.Tfib_const_abs (`_`) where A
   writes the image-A literal; (3) the four REAL slots take their address and value from the goal (that is, from
   B.AsanRT.RT_REALS) in one step where A writes four literal bullets.  No image-B number is written here.
   Then to a working branch fec8db0a380: pwrt_abs / pwrt_sym decide const-table membership by
   lib/Reusable/YConstIn.v's in_const_tbl (Required as A does), as A.  Because of (2), pwrt_abs first fills a row
   value left to unification from the table's row at that address and width (pwrt_row_val, one vm_compute of
   List.find); in_const_tbl, which refuses a row with an evar, then checks the whole row.  A has no such step: it
   writes those values as literals.  *)

(* lib/B/ProgWorldRt.v -- fuzz_ctrl image B (libreac v1.9.0, asan-ubsan build): the PROOFS of lib/B/ProgWorld.v's
   rt_of_core_stmt (Section RtOfCore) and RT_used_of_AR_stmt (Section RtUsed).  lib/B/ProgWorld.v and
   lib/B/ProgWorld_Fs.v are NOT edited here: they are
   only Required.

   rule 24: NO function of the image is proved here.  Both lemmas are program-world facts about the core's own
   state: ctrl's narrowed runtime table ProgWorld.RT_used at a memory, from the core's AR.

   SHAPE (as A, a Theorem Labs lane 03:32Z).  RT_rest_of_AR, below, is every RT_used conjunct EXCEPT shadow_rw, from
   CtrlTSyms + AR alone.  It needs NO AR_states_vis0_shadow: each conjunct is one constant row of the bundle's
   table (ARm.am_const, Reusable/YG0n.v), which under CtrlTSyms (ts_const, Reusable/YF0m.v) IS image B's
   Tfib_const, read through the aview -> mrd bridge of lib/B/ProgWorld_Fs.v.  Then
     RT_used_of_AR = RT_rest_of_AR + shadow_rw, the latter from the file of record for that one conjunct,
                     lib/B/ProgWorldRtShadow.v (the twin of A's lib/A/ProgWorldRtShadow.v; its premises and binder
                     order are RT_used_of_AR_stmt's, so it applies with no adapter);
     rt_of_core   = RT_rest_of_AR at the cut's AR -- the FIRST conjunct of Reusable.YCbq.ajournal --
                    + shadow_rw from the carried B.ACtlCut.ctl_rt.
   RT ignores sp and md: ctl_RT's sp and md arguments do not occur in its body.

   REUSED, PROVED, Required (never copied): lib/B/ProgWorld_Fs.v's byte bridge -- pw_c8_bytes, pw_z4_bytes,
   pw_z1_bytes, pw_bytes_of_view, pw_bv8, pw_u64, pw_in_abs, pw_in_sym, pw_ext_range, pw_F_in_owned, pw_F_above and
   pw_app_mem_F -- and lib/B/ProgWorld.v's as_tp_RT_TP.  OWN, because ProgWorld_Fs has no such lemma: pwrt_zl_ok /
   pwrt_zl_nth / pwrt_cell_zl, which read a byte RANGE INSIDE one absolute row (the cf / opt / uw cells are
   sub-ranges of 8-byte rows), and pwrt_bytes_split.

   TLS_INDEX (a Theorem Labs lane's trap): asan_fs_cells states the second word as le8 (Z_to_bv 64 (-2048)) while its YF0m row
   (at B.AsanRT.RT_TLSIDX + 8) holds 0xfffffffffffff800: the same 64-bit word, a different Z, so that row is read as
   a byte range (pwrt_cell_zl) and not through pw_c8_bytes' value equality. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YK04 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YG00 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YCbq Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YConstIn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YE2k Reusable.YCfn Reusable.YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlK B.ACtlCut B.ProgWorld B.ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldRtShadow.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.

(* The journal's sink_head is the core's own instance, as lib.Reusable.YCfn resolves it (Reusable/YE2k.v:45). *)
#[local] Existing Instance lib.Reusable.YE2k.tfib_sink_head.

Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).

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
  change 256 with (2 ^ 8)%Z. apply lib.Lib.Mem.shiftr_mod_mod8; lia.
Qed.

Lemma pwrt_bytes_split : forall (m : word -> option byte) (ad : Z) (bs bs1 bs2 : list byte) (n : Z),
  bs = bs1 ++ bs2 -> n = Z.of_nat (length bs1) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m ad bs1 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (ad + n) bs2 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m ad bs.
Proof.
  intros m ad bs bs1 bs2 n -> -> H1 H2.
  apply (proj2 (lib.Lib.Mem.bytes_at_app B.Img0.rsegs m ad bs1 bs2)). split; assumption.
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
  lib.Lib.Mem.bytes_at B.Img0.rsegs m ad bs.
Proof.
  intros W m B ly a v w off bs ad Hc Hw Hok -> H0 H1.
  apply (B.ProgWorld_Fs.pw_bytes_of_view W); [lia | lia |].
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
  rewrite B.ProgWorld_Fs.pw_bv8.
  rewrite (pwrt_le_byte_z v w (off + i)%nat ltac:(lia)). reflexivity.
Qed.

End PwrtRange.

(* Membership of a row in image B's const table, by the row's own text and not by its position.  The in_eq / in_cons
   walk is quadratic in the table's length (a Theorem Labs lane 06:52Z); lib/Reusable/YConstIn.v's in_const_tbl decides it with one
   vm_compute of `existsb (row_eqb row) tbl` on a closed goal.  pwrt_mem stays for owned_extents, a two-row list of
   Z * Z that YConstIn's row_eqb (over acell) does not type.  Image-B step (header (2)): where a pwrt_cell_zl row's
   value is left to unification (`_`), in_const_tbl refuses the evar, so pwrt_row_val first unifies the value with
   that of the table's first row at the same address and width whose value is a number (one vm_compute of
   List.find, the row the in_eq / in_cons walk took); in_const_tbl then checks the whole row against the table. *)
Local Ltac pwrt_mem := repeat first [ apply in_eq | apply in_cons ].
Local Ltac pwrt_row_val :=
  lazymatch goal with
  | |- In (lib.Reusable.YG0f.ACell ?a ?w ?v) ?t =>
      tryif has_evar v then
        let r := eval vm_compute in
          (List.find (fun c => andb (andb (lib.Reusable.YConstIn.ci_aexp_eqb (lib.Reusable.YG0f.c_at c) a)
                                          (Nat.eqb (lib.Reusable.YG0f.c_w c) w))
                                    (match lib.Reusable.YG0f.c_val c with
                                     | lib.Reusable.YG0f.AV (lib.Reusable.YG0f.ANum _) => true
                                     | _ => false
                                     end)) t) in
        lazymatch r with
        | Some (lib.Reusable.YG0f.ACell _ _ ?cv) => unify v cv
        | None => fail 0 "pwrt_row_val: no row of the table at" a "of width" w
        end
      else idtac
  | |- _ => idtac
  end.
Local Ltac pwrt_abs := apply B.ProgWorld_Fs.pw_in_abs; pwrt_row_val; lib.Reusable.YConstIn.in_const_tbl.
Local Ltac pwrt_sym := apply B.ProgWorld_Fs.pw_in_sym; lib.Reusable.YConstIn.in_const_tbl.

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
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    B.AsanRT.asan_cells m /\ B.AsanRT.asan_opt_cells m /\ B.AsanRT.asan_cf_cells m /\
    B.AsanRT.asan_uw_cells m /\ B.AsanRT.asan_fs_cells m /\
    Forall (fun p => In (fst p) B.ProgWorld.REAL_USED ->
                     lib.Lib.Mem.bytes_at B.Img0.rsegs m (fst p) (lib.Lib.Mem.le8 (lib.Lib.Mem.wa (snd p))))
      B.AsanRT.RT_REALS.
Proof.
  intros HTS HL ly S W m md HAR.
  pose proof HAR as HAR0.
  destruct HAR as (HM & _ & _ & _ & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ HM) as Hlay.
  pose proof (lib.Reusable.YG0n.am_const _ _ _ _ HM) as Hconst.
  pose proof (lib.Reusable.YG0n.am_tsd _ _ _ _ HM) as Hlytsd.

  (* every row of image B's const table holds over this state's view *)
  assert (Hrow : forall c, In c (lib.Reusable.YF0m.Tfib_const ly) ->
            lib.Reusable.YG0f.cell_holds B ly
              (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) c).
  { intros c Hc. apply (proj1 (Forall_forall _ _) Hconst).
    rewrite (lib.Reusable.YF0m.ts_const B HTS ly). exact Hc. }

  (* the image's symbol values *)
  pose proof (B.ProgWorld.as_tp_RT_TP B HTS) as Htp.
  assert (Htsdly : lib.Reusable.YG0f.ly_tsd ly = B.AsanRT.RT_TSDMAIN).
  { rewrite Hlytsd, (lib.Reusable.YF0m.ts_tsd B HTS). reflexivity. }

  (* the fake stack and the dtv block, as owned application extents *)
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app ly Hlay)) as Happ.
  assert (HinF : lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_F ly)
                   lib.Reusable.YG0f.kFakeStackSize).
  { exact (Happ _ (B.ProgWorld_Fs.pw_F_in_owned ly)). }
  assert (HinD : lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.ly_D ly) 4096).
  { apply (Happ (lib.Reusable.YG0f.ly_D ly, 4096)).
    unfold lib.Reusable.YG0f.owned_extents. pwrt_mem. }
  pose proof (B.ProgWorld_Fs.pw_ext_range _ _ HinF) as HF.
  pose proof (B.ProgWorld_Fs.pw_ext_range _ _ HinD) as HD.
  pose proof (B.ProgWorld_Fs.pw_F_above B ly S W m md HAR0) as HFgt.

  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).

  (* ---- asan_cells (17 rows) ---- *)
  - unfold B.AsanRT.asan_cells.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
            (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))).
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.CELL_K)
               (lib.Reusable.YG0f.ANum B.AsanRT.ASAN_K));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.GOT_CELL_K)
               (lib.Reusable.YG0f.ANum B.AsanRT.CELL_K));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_z1_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.INITED));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_rng | pwrt_rng].
    + apply (B.ProgWorld_Fs.pw_z1_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.REPLACE));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_rng | pwrt_rng].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.GOT_REPLACE)
               (lib.Reusable.YG0f.ANum B.AsanRT.REPLACE));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_z4_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.UAR));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_zle | pwrt_zle | pwrt_rng].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.GOT_UAR)
               (lib.Reusable.YG0f.ANum B.AsanRT.UAR));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_z1_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.CANPOISON));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_rng | pwrt_rng].
    (* 0x7fffffffffff is the value B.AsanRT.asan_cells states at HIEND (ASan's kHighMemEnd, the same in both
       images) *)
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.HIEND)
               (lib.Reusable.YG0f.ANum 0x7fffffffffff));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.GOT_HIEND)
               (lib.Reusable.YG0f.ANum B.AsanRT.HIEND));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.MIDBEG)
               (lib.Reusable.YG0f.ANum 0));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.GOT_MIDBEG)
               (lib.Reusable.YG0f.ANum B.AsanRT.MIDBEG));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.MIDEND)
               (lib.Reusable.YG0f.ANum 0));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.GOT_MIDEND)
               (lib.Reusable.YG0f.ANum B.AsanRT.MIDEND));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.REAL_MEMCPY)
               (lib.Reusable.YG0f.ANum B.AsanRT.MUSL_MEMCPY));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.REAL_MEMSET)
               (lib.Reusable.YG0f.ANum B.AsanRT.MUSL_MEMSET));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.GOT_REAL_MEMSET)
               (lib.Reusable.YG0f.ANum B.AsanRT.REAL_MEMSET));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].

  (* ---- asan_opt_cells ---- *)
  - unfold B.AsanRT.asan_opt_cells.
    refine (conj _ (conj _ (conj _ _))).
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.RT_GOT_AF)
               (lib.Reusable.YG0f.ANum B.AsanRT.RT_AF));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    (* AF + 60: byte 4 of the row at AF + 56 (AF is 8-aligned; the row offsets are the struct's, the same in both
       images) *)
    + eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_AF + 56) _ 8%nat 4%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.RT_GOT_VERB)
               (lib.Reusable.YG0f.ANum B.AsanRT.RT_VERB));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_z4_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.RT_VERB));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_zle | pwrt_zle | pwrt_rng].

  (* ---- asan_cf_cells ---- *)
  - unfold B.AsanRT.asan_cf_cells.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.RT_GOT_CF)
               (lib.Reusable.YG0f.ANum B.AsanRT.RT_CF));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    (* CF + 32: the whole row at CF + 32 (CF is 8-aligned) *)
    + eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_CF + 32) _ 8%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 64: byte 0 of the row at CF + 64 *)
    + eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_CF + 64) _ 8%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 84: its 1-byte row *)
    + eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_CF + 84) _ 1%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 120: 2 ^ 64 - 1 is the value B.AsanRT.asan_cf_cells states there *)
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum (B.AsanRT.RT_CF + 120))
               (lib.Reusable.YG0f.ANum (2 ^ 64 - 1)));
        [apply Hrow; pwrt_abs | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 137: its 1-byte row *)
    + eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_CF + 137) _ 1%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* CF + 240: 21 bytes over the rows at CF + 240, CF + 248 and CF + 256; the byte lists are B.AsanRT's CF + 240
       list (the same in both images) cut after 8 and 16 bytes *)
    + apply (pwrt_bytes_split m (B.AsanRT.RT_CF + 240) _
               (B.AsanRT.cf_b [0; 0; 0; 0; 1; 0; 1; 1])
               (B.AsanRT.cf_b [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0]) 8);
        [pwrt_vm | pwrt_vm | |].
      * eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_CF + 240) _ 8%nat 0%nat);
          [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
      * apply (pwrt_bytes_split m (B.AsanRT.RT_CF + 240 + 8) _
                 (B.AsanRT.cf_b [1; 1; 1; 1; 1; 1; 1; 1])
                 (B.AsanRT.cf_b [1; 1; 1; 1; 0]) 8);
          [pwrt_vm | pwrt_vm | |].
        -- eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_CF + 248) _ 8%nat 0%nat);
             [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
        -- eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_CF + 256) _ 8%nat 0%nat);
             [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* AF + 29: byte 5 of the row at AF + 24 *)
    + eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_AF + 24) _ 8%nat 5%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].

  (* ---- asan_uw_cells ---- *)
  - unfold B.AsanRT.asan_uw_cells.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + eapply (pwrt_cell_zl W m B ly B.AsanRT.RT_TSDI _ 1%nat 0%nat);
        [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_z4_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.RT_TSDK));
        [apply Hrow; pwrt_abs | reflexivity | pwrt_zle | pwrt_zle | pwrt_rng].
    (* 4096 is the value B.AsanRT.asan_uw_cells states at PGSZ *)
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.RT_PGSZ)
               (lib.Reusable.YG0f.ANum 4096));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum (B.AsanRT.RT_TP - 88))
               (lib.Reusable.YG0f.ANum B.AsanRT.RT_TSDMAIN));
        [apply Hrow; pwrt_abs | pwrt_vm | reflexivity | pwrt_zle | pwrt_zle].
    (* the TSD main block holds the context map: a symbolic row *)
    + exists (Z_to_bv 64 (lib.Reusable.YG0f.ly_C ly)).
      apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATsd 0)
               (lib.Reusable.YG0f.AC 0)).
      * apply Hrow; pwrt_sym.
      * cbn [lib.Reusable.YG0f.aeval]. rewrite Htsdly. unfold B.AsanRT.RT_TSDMAIN. lia.
      * cbn [lib.Reusable.YG0f.aeval]. lia.
      * pwrt_zle.
      * pwrt_zle.

  (* ---- asan_fs_cells ---- *)
  - unfold B.AsanRT.asan_fs_cells.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    (* TLS_INDEX: the two words at TLSIDX and TLSIDX + 8; 1, -2048 and 8 are B.AsanRT.asan_fs_cells' text *)
    + apply (pwrt_bytes_split m B.AsanRT.RT_TLSIDX _
               (lib.Lib.Mem.le8 (Z_to_bv 64 1)) (lib.Lib.Mem.le8 (Z_to_bv 64 (-2048))) 8);
        [reflexivity | pwrt_vm | |].
      * apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.RT_TLSIDX)
                 (lib.Reusable.YG0f.ANum 1));
          [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
      (* the row's value is 0xfffffffffffff800, the goal's is -2048: same word, different Z, so the row is
         read as a byte range and not through pw_c8_bytes' value equality *)
      * eapply (pwrt_cell_zl W m B ly (B.AsanRT.RT_TLSIDX + 8) _ 8%nat 0%nat);
          [apply Hrow; pwrt_abs | pwrt_nle | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum B.AsanRT.RT_DTPOFF)
               (lib.Reusable.YG0f.ANum 8));
        [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum (B.AsanRT.RT_TP - 8))
               (lib.Reusable.YG0f.ANum (B.AsanRT.RT_TP + 32)));
        [apply Hrow; pwrt_abs | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    + apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum (B.AsanRT.RT_TP + 40))
               (lib.Reusable.YG0f.ANum (B.AsanRT.RT_TP + 2048)));
        [apply Hrow; pwrt_abs | pwrt_vm | pwrt_vm | pwrt_zle | pwrt_zle].
    (* TP holds the side stack, whose whole window is application memory *)
    + exists (Z_to_bv 64 (lib.Reusable.YG0f.ly_F ly)).
      assert (HFb : 0 <= lib.Reusable.YG0f.ly_F ly < 2 ^ 64)
        by (unfold lib.Reusable.YG0f.kFakeStackSize in HF; lia).
      split.
      * apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATp 0)
                 (lib.Reusable.YG0f.AF 0)).
        -- apply Hrow; pwrt_sym.
        -- cbn [lib.Reusable.YG0f.aeval]. rewrite Htp. lia.
        -- cbn [lib.Reusable.YG0f.aeval]. lia.
        -- pwrt_zle.
        -- pwrt_zle.
      * rewrite (B.ProgWorld_Fs.pw_u64 _ HFb).
        unfold B.AsanRT.fs_value_ok, B.AsanRT.RT_GT, B.AsanRT.RT_FS_SIZE.
        split; [lia|]. split; [exact (lib.Reusable.YG0f.lo_F_al ly Hlay)|].
        split; [unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HFgt; lia|].
        intros a Ha. apply (B.ProgWorld_Fs.pw_app_mem_F ly a HinF).
        unfold lib.Reusable.YG0f.kFakeStackSize. lia.
    (* TP + 8 holds the dtv block *)
    + exists (Z_to_bv 64 (lib.Reusable.YG0f.ly_D ly)).
      assert (HDb : 0 <= lib.Reusable.YG0f.ly_D ly < 2 ^ 64) by lia.
      split; [|split].
      * apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ATp 8)
                 (lib.Reusable.YG0f.AD 0)).
        -- apply Hrow; pwrt_sym.
        -- cbn [lib.Reusable.YG0f.aeval]. rewrite Htp. unfold B.AsanRT.RT_TP. lia.
        -- cbn [lib.Reusable.YG0f.aeval]. lia.
        -- pwrt_zle.
        -- pwrt_zle.
      * rewrite (B.ProgWorld_Fs.pw_u64 _ HDb). lia.
      * rewrite (B.ProgWorld_Fs.pw_u64 _ HDb).
        unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
        destruct HinD as [HA0 [HA1 | [HA1 HA2]]];
          unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *;
          pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [CR _]; lia.

  (* ---- the four REAL slots the lifted runs read (REAL_TLS_GET_ADDR, REAL_BCMP, REAL_MEMCHR, REAL_MEMCMP, in
     RT_REALS' order): each slot's address and value are read off its RT_REALS entry in the goal ---- *)
  - apply (proj2 (Forall_forall _ _)). intros p Hp.
    cbv [B.AsanRT.RT_REALS] in Hp. cbn [In] in Hp.
    repeat match type of Hp with _ \/ _ => destruct Hp as [Hp | Hp] end.
    all: try contradiction.
    all: subst p; cbn [fst snd]; intros Hu.
    all: try (destruct Hu as [E|[E|[E|[E|[]]]]]; discriminate E).
    all: match goal with
         | |- lib.Lib.Mem.bytes_at _ _ ?a (lib.Lib.Mem.le8 (lib.Lib.Mem.wa ?v)) =>
             apply (B.ProgWorld_Fs.pw_c8_bytes B ly W m (lib.Reusable.YG0f.ANum a)
                      (lib.Reusable.YG0f.ANum v));
             [apply Hrow; pwrt_abs | reflexivity | reflexivity | pwrt_zle | pwrt_zle]
         end.
Qed.

(* RT_used at ANY state of the core, for the callee-internal re-based stretches: RT_rest_of_AR, and the one
   conjunct it leaves out from the named hypothesis, through lib/B/ProgWorldRtShadow.v (A: a Theorem Labs lane's hand
   lib/A/ProgWorldRtShadow.v). *)
Lemma RT_used_of_AR : B.ProgWorld.RT_used_of_AR_stmt B.
Proof.
  unfold B.ProgWorld.RT_used_of_AR_stmt.
  intros HTS HL Hvis0 ly S W m md HAR.
  destruct (RT_rest_of_AR HTS HL ly S W m md HAR)
    as (Hcells & Hopt & Hcf & Huw & Hfs & Hreals).
  unfold B.ProgWorld.RT_used.
  exact (conj Hcells
           (conj (B.ProgWorldRtShadow.shadow_rw_of_AR B HTS HL Hvis0 ly S W m md HAR)
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

Lemma rt_of_core : B.ProgWorld.rt_of_core_stmt B MT XM_LIB RLO RHI FP.
Proof.
  unfold B.ProgWorld.rt_of_core_stmt.
  intros HTS HL cx own k ly3 S3 W3 ms3 md3 Hbase Hj Hrt.
  destruct Hj as (HAR & _).
  destruct Hrt as (Hac & Hsh & Hro).
  destruct (RT_rest_of_AR B HTS HL ly3 S3 W3 (ms_mem ms3) md3 HAR)
    as (Hcells & Hopt & Hcf & Huw & Hfs & Hreals).
  unfold B.ProgWorld.ctl_RT, B.ProgWorld.RT_used.
  exact (conj Hcells (conj Hsh (conj Hopt (conj Hcf (conj Huw (conj Hfs Hreals)))))).
Qed.

End RtOfCore.

Print Assumptions RT_used_of_AR.
Print Assumptions rt_of_core.
