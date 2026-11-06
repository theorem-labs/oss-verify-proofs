(* Image B twin of lib/A/RT_pf_kit.v at d49bd1db505: module paths lib.A -> lib.B; no image numeral (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *) (* Small helpers shared by fuzz_reply.asan-ubsan's snprintf chain proofs (RT_pf_vsn.v, RT_pf_snf.v, RT_pf_vf.v), in their
   own file so that the three can be built - and proved by different hands - independently.  No function is proved
   here.

   THE MEASUREMENT THAT SHAPES THIS FILE.  The chain meets GXA at TWO instances of the same image: A_img and
   A_img_vsn (RT_IImgA.v:96 and :107), which differ in ONE symbol-map row, 0x7f000400.  A fact proved at one and
   used at the other therefore needs a CONVERSION of the two records - and that conversion is catastrophic: a
   single `exact H` crossing them (ssp_cells at A_img_vsn used at A_img) ran 16 MINUTES without finishing on
   a build machine, and the same crossing inside a `first [ ... ]` over GXA's 29 premises did not finish in 25
   minutes.  Coq has to decide `A_sym = A_sym_vsn` structurally, which it cannot, and re-walks both maps under
   every binder of the unfolded cell predicates.
   THE RULE, and why every lemma below is shaped the way it is: NEVER let a cross-instance fact be converted.
   Reduce the record projections to their literal fields (`img_segs` of both instances IS `tfibsegs` = the Bz
   tree's `asegs`, by reflexivity), rewrite every `sym` application to its NUMBER (vm_compute, closed term), and
   only then the two sides are SYNTACTICALLY equal and `exact` is free.

   Contents:
   - hid / hide / show: keep a hypothesis out of lia's reach without losing it.  Also measured: `lia` splits on
     every disjunctive hypothesis in context, and each chain statement carries two (the destination's separation
     premises), so a proof that leaves them visible pays the split at every arithmetic side condition.
   - cj_bz_msteps / cj_bz_evt: the CJ -> Bz direction of RT_gxa_calls.v's vocabulary bridge (that file, and
     a Theorem Labs lane's relocated copy FMgxa_bzcj.v on a working branch 534b701a600, prove only Bz -> CJ).
   - pf_evt_fwd: one step forward past a trampoline when the post does not already hold (the donor's pattern,
     omx-clap-core/fuzz_state lib/A/Prog/snprintf_wrap.v snp_evt_fwd at 840c4afa7e2).
   - the segment list and the stack-protector / GLOBALS_TOP numerals at BOTH instances, and ssp_cells_vsn proved
     by rewriting to them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_pf_Tbl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pad.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Module CJE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Exec.
Module CJR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Module GP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pad.
Module GIF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Module RTA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA.

(* ---- lia hygiene ---- *)
Definition hid (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change T with (hid T) in H end.
Ltac show H := unfold hid in H.

(* ---- the two instances' segment list is the Bz tree's, by reflexivity ---- *)
Lemma segs_img : @CJR.img_segs RTA.A_img = asegs.
Proof. reflexivity. Qed.
Lemma segs_vsn : @CJR.img_segs RTA.A_img_vsn = asegs.
Proof. reflexivity. Qed.

(* ---- CJ -> Bz, the direction RT_gxa_calls.v does not prove ---- *)
Lemma cj_bz_msteps : forall s s', CJE.msteps (@CJR.img_segs RTA.A_img) s s' -> BzE.msteps asegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply BzE.msteps_refl.
  - eapply BzE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma cj_bz_evt : forall Q ms, CJE.evt (@CJR.img_segs RTA.A_img) Q ms -> BzE.evt asegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (cj_bz_msteps ms ms' H) | exact HQ]. Qed.

(* ---- one step forward past a trampoline ---- *)
Lemma pf_mstep_det : forall ms a b, mstep asegs ms a -> mstep asegs ms b -> a = b.
Proof. intros ms a b [_ Ha] [_ Hb]. congruence. Qed.

Lemma pf_msteps_inv : forall ms ms', msteps asegs ms ms' ->
  ms = ms' \/ exists ms1, mstep asegs ms ms1 /\ msteps asegs ms1 ms'.
Proof.
  intros ms ms' H. destruct H as [a | a b c H1 H2];
    [left; reflexivity | right; exists b; split; [exact H1 | exact H2]].
Qed.

Lemma pf_evt_fwd : forall (Q : machine_state -> Prop) ms ms1,
  evt asegs Q ms -> mstep asegs ms ms1 -> ~ Q ms -> evt asegs Q ms1.
Proof.
  intros Q ms ms1 (ms' & HS & HQ) HM NQ.
  destruct (pf_msteps_inv ms ms' HS) as [-> | (c & H1 & H2)]; [contradiction|].
  exists ms'. split; [rewrite (pf_mstep_det ms ms1 c HM H1); exact H2 | exact HQ].
Qed.

(* ---- the numerals of the symbol map that the chain needs, at BOTH instances ---- *)
Lemma got_ssp_val : @GP.got_ssp RTA.A_img = PF_GOT_SSP.
Proof. vm_compute. reflexivity. Qed.
Lemma ssp_guard_val : @GP.ssp_guard RTA.A_img = PF_SSP_GUARD.
Proof. vm_compute. reflexivity. Qed.
Lemma globals_top_val : @GIF.G_printf_iface.GLOBALS_TOP RTA.A_img = PF_GLOBALS_TOP.
Proof. vm_compute. reflexivity. Qed.
Lemma got_ssp_val_vsn : @GP.got_ssp RTA.A_img_vsn = PF_GOT_SSP.
Proof. vm_compute. reflexivity. Qed.
Lemma ssp_guard_val_vsn : @GP.ssp_guard RTA.A_img_vsn = PF_SSP_GUARD.
Proof. vm_compute. reflexivity. Qed.
Lemma globals_top_val_vsn : @GIF.G_printf_iface.GLOBALS_TOP RTA.A_img_vsn = PF_GLOBALS_TOP.
Proof. vm_compute. reflexivity. Qed.

(* the stack-protector cells cross the two instances by REWRITING to those numerals and to asegs - never by
   converting the two records (that is the 16-minute step) *)
Lemma ssp_cells_of_vsn : forall m c, @GP.ssp_cells RTA.A_img_vsn m c -> @GP.ssp_cells RTA.A_img m c.
Proof.
  intros m c H. unfold GP.ssp_cells in H |- *.
  rewrite got_ssp_val_vsn, ssp_guard_val_vsn, segs_vsn in H.
  rewrite got_ssp_val, ssp_guard_val, segs_img.
  exact H.
Qed.

Lemma ssp_cells_to_vsn : forall m c, @GP.ssp_cells RTA.A_img m c -> @GP.ssp_cells RTA.A_img_vsn m c.
Proof.
  intros m c H. unfold GP.ssp_cells in H |- *.
  rewrite got_ssp_val, ssp_guard_val, segs_img in H.
  rewrite got_ssp_val_vsn, ssp_guard_val_vsn, segs_vsn.
  exact H.
Qed.
(* ---- crossing the two TREES (not the two instances).  CJ's lib/CJ/Lib and Bz's lib/A/Bz/Lib are two copies of the
   same machine library, and most of their definitions are the same term, so they convert by `exact`.  TWO DO NOT,
   and knowing which saves a build: `msteps` (an Inductive in each tree - RT_gxa_calls.v's bz_cj_evt and this
   file's cj_bz_evt cross it by induction) and `cell` (an Inductive in each tree, so a `list Cells.cell` is NOT a
   `list cell`, and NO cast exists for rw_cells / ro_cells).  CONSEQUENCE for the chain proofs: never carry a CELL
   fact across the trees - transport a CJ cell fact with CJ's own Frame lemmas (over a CJ munch, cast below) and a
   Bz cell fact with Bz's.  Bytes, stacks, munch and wmono cross freely. ---- *)

Lemma bya_cj_bz : forall m A bs,
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.bytes_at (@CJR.img_segs RTA.A_img) m A bs ->
  bytes_at asegs m A bs.
Proof. intros m A bs H. exact H. Qed.

Lemma bya_bz_cj : forall m A bs,
  bytes_at asegs m A bs ->
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.bytes_at (@CJR.img_segs RTA.A_img) m A bs.
Proof. intros m A bs H. exact H. Qed.

Lemma stk_cj_bz : forall m lo hi,
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.stk (@CJR.img_segs RTA.A_img) m lo hi ->
  stk asegs m lo hi.
Proof. intros m lo hi H. exact H. Qed.

Lemma stk_bz_cj : forall m lo hi,
  stk asegs m lo hi ->
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.stk (@CJR.img_segs RTA.A_img) m lo hi.
Proof. intros m lo hi H. exact H. Qed.

Lemma munch_cj_bz : forall W m m',
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.munch W m m' -> munch W m m'.
Proof. intros W m m' H. exact H. Qed.

Lemma munch_bz_cj : forall W m m',
  munch W m m' -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.munch W m m'.
Proof. intros W m m' H. exact H. Qed.

Lemma wmono_cj_bz : forall m m',
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.wmono (@CJR.img_segs RTA.A_img) m m' ->
  wmono asegs m m'.
Proof. intros m m' H. exact H. Qed.

Lemma wmono_bz_cj : forall m m',
  wmono asegs m m' ->
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.wmono (@CJR.img_segs RTA.A_img) m m'.
Proof. intros m m' H. exact H. Qed.
(* ---- the GXA premises that are parameterised by the INSTANCE, and the ONLY form found to be cheap.  MEASURED,
   four ways, on this file (otherwise 9-15 s): `exact H` on an args_ok premise between the two concrete instances
   did not finish in 600 s; a per-constructor proof reducing arg_ok and rewriting img_segs did not finish in 8.5
   min; the FUNCTION equality `@args_ok A_img_vsn = @args_ok A_img` did not finish in 700 s.  What works is to
   state the crossing GENERICALLY over two instances with an `img_segs` equality premise, so that no step ever
   compares the two records: the bodies use the instance only through img_segs, and the proof rewrites with that
   equality.  The two args lemmas below are PfVf's text (RT_pf_vf.v:103, :115, where they compile in 4.7 s).
   Cross A_img -> A_img_vsn with `segs_img_vsn` below. ---- *)
Lemma arg_ok_cross : forall (I1 I2 : CJR.RImg), @CJR.img_segs I1 = @CJR.img_segs I2 ->
  forall Fp B BS RC RCS RE RES m lo sp ap w a,
    @GIF.G_printf_iface.arg_ok I1 Fp B BS RC RCS RE RES m lo sp ap w a ->
    @GIF.G_printf_iface.arg_ok I2 Fp B BS RC RCS RE RES m lo sp ap w a.
Proof.
  intros I1 I2 E Fp B BS RC RCS RE RES m lo sp ap w a H.
  destruct a as [s|i|u|d|l]; try exact H.
  destruct H as (slack & BY & REST). exists slack. split; [rewrite <- E; exact BY | exact REST].
Qed.

(* args_ok's structural argument is SLOTS, not args (both decrease; Coq takes the first), so the induction is on
   ws - on args the fixpoint stays stuck and even `args_ok .. ws []` is not True.  PfVf measured this. *)
Lemma args_ok_cross : forall (I1 I2 : CJR.RImg), @CJR.img_segs I1 = @CJR.img_segs I2 ->
  forall Fp B BS RC RCS RE RES m lo sp ap ws args,
    @GIF.G_printf_iface.args_ok I1 Fp B BS RC RCS RE RES m lo sp ap ws args ->
    @GIF.G_printf_iface.args_ok I2 Fp B BS RC RCS RE RES m lo sp ap ws args.
Proof.
  intros I1 I2 E Fp B BS RC RCS RE RES m lo sp ap ws args H. revert args H.
  induction ws as [|w ws IH]; intros args H.
  - destruct args as [|a args]; [exact I | destruct H].
  - destruct args as [|a args]; [exact I |].
    destruct H as [H1 H2].
    split; [exact (arg_ok_cross I1 I2 E _ _ _ _ _ _ _ _ _ _ _ _ _ H1) | exact (IH args H2)].
Qed.

(* OUT_snf / OUTFP_snf do not mention the instance at all, so the section discharge gave them NO IMG argument:
   `@OUT_snf I OM` is a type error, and a printf_model premise is literally the same term at both instances -
   it needs no crossing.  Only args_ok does. *)

Definition segs_img_vsn : @CJR.img_segs RTA.A_img = @CJR.img_segs RTA.A_img_vsn :=
  eq_trans segs_img (eq_sym segs_vsn).
(* ---- THE MEASUREMENT THAT MATTERS MOST, and the lemma that answers it.  Applying GXA's vsnprintf_x - whose
   conclusion is `evt (img_segs A_img_vsn) ...` - to a goal written `evt (img_segs A_img) ...` does NOT FINISH IN
   400 s even with every premise admitted: the two sides have the SAME head `img_segs`, so Coq tries the arguments
   first, `A_img =?= A_img_vsn`, and that is the catastrophic record comparison.  The rule: never let
   `img_segs A` meet `img_segs B`.  Make ONE side the Bz tree's `asegs` - a constant, which simply delta-reduces -
   by crossing with this segs-GENERIC form instead of the A_img one above. ---- *)
Lemma cj_bz_msteps_segs : forall segs s s', CJE.msteps segs s s' -> BzE.msteps segs s s'.
Proof.
  intros segs s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply BzE.msteps_refl.
  - eapply BzE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma cj_bz_evt_segs : forall segs Q ms, CJE.evt segs Q ms -> BzE.evt segs Q ms.
Proof. intros segs Q ms (ms' & H & HQ). exists ms'. split; [exact (cj_bz_msteps_segs segs ms ms' H) | exact HQ]. Qed.

(* the reverse, Bz -> CJ, is RT_gxa_calls.v's bz_cj_evt at A_img; a segs-generic version needs the two trees'
   `mstep` to convert, which they do not. *)
