(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44) on fuzz_ctrl's ASan build, image A: the GLUE PROOF of the cgif caller-journal contract
   whose statement is lib/A/Prog/C_reac_box_model_block.v (pb_reac_box_model_block_stmt, treac_box_model_block_spec).
   Callers Require only the statement file; this file Requires it qualified.  rule 24: no function is proved here (glue
   of an already-proved run; the header of Module BmbGlue below says how). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six core modules that ctrl's lib/A/Reusable duplicates (YI04, YI16, YK11, YK1b, YM05, YO09) are Required, never
   Imported, and written lib.Reusable.X.n (porter 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YI04 YI16 YM05 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0h YK0i YK14 YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlFrame
CtrlRo YC85.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcSynthLib.
(* the statement, qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_box_model_block.
#[local] Existing Instance CtrlImg.PI_ctrl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* =========================================================================================================
   THE GLUE PROOF of pb_reac_box_model_block (a Theorem Labs lane).  rule 24: no function is proved here;
   this is the cgif-form glue of an already-proved run.  The run is a Theorem Labs lane's proved v1.9 run of
   reac_box_model_block (a working branch d69f7c708f6), re-run over lib/Lib/StepF as the footprint
   (_F) files of this family; each silent stretch is lifted into the cgif world through the kit bridge
   (Reusable/YA0nR.v SRr_fevt_hid, footprint RNG_W (w_H W) of A/ProgBridge.v or a sub-footprint of it) on the
   normalized memory (A/MemNormF.v evtF_normalize_ro).  The function run holds two allocator events, so it is cut:
     S1  main_pre_F  [0x85b44 .. 0x85bb8), and the call instruction `jal __asan_stack_malloc_0` itself;
     event 1: cgif's astack_malloc_realizes SEGS B 0 through aj_stack_malloc_atS (YC85.v:291), fake frame;
     S2  main_mid_F  [0x85bbc .. 0x864f8);
     event 2: the flag release `sb zero,0(a0)` at 0x864f8: the store is one footprint step (as bmb_KR_Q0 runs it,
              epiF bmb_rel_step for its memory facts), the journal step is A/ProgWorldAstack.v
              ctl_release_of_free_law 0 (the fsteps twin of the core's aj_flag_store, over astack_free_law);
     S3  main_post_F [0x864fc .. ret 0x86560].
   The _F files are Required qualified, never Imported (glue closure rule, porter 23:38Z); the Lib layer is
   Imported inside Module BmbGlue only.  The six modules with two copies (YI04 YI16 YK11 YK1b YM05 YO09) are
   written lib.Reusable.X.n (porter 04:24Z). *)
From Ltac2 Require Ltac2.
(* The lib.Lib family is doubled under lib/A/Bz/Lib: Required from its own directory and named lib.Lib.X (a Theorem Labs lane 05:20Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Mem Frame Cells Step ExecF StepF Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.ProgBridge A.MemNorm A.MemNormF
  A.MemNormTr A.ProgWorld A.ProgWorld_Fs A.ProgWorldShadow A.ProgWorldAstack
  A.ProgWorldVisFrame A.ProgWorldVisWin A.ProgWorldVisHeap A.Prog.CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.RcAsanFPLib
  A.Prog.reac_box_model_block_c A.Prog.reac_box_model_block_cF A.Prog.rng_asan A.Prog.reac_box_model_block_base
  A.Prog.ImgBounds A.Prog.memset A.Prog.asan_memsetF A.Prog.asan_memsetF_on A.Prog.asan_memcpyF_on
  A.Prog.build_dt1_singleF
  A.Prog.reac_box_model_block_baseF A.Prog.reac_box_model_block_epi A.Prog.reac_box_model_block_epiF
  A.Prog.reac_box_model_blockF.
(* Route (C): the shadow premise of the narrowed _F files is the region of reac_box_model_block_c_on.v, not the
   universal shadow_rw (false at an AR state, ACtl.v:591). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.Prog.reac_box_model_block_c_on.
Module C_ON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.

Module BmbGlue.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.
Import A.Img0 A.AsanRT A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.reac_box_model_block_c.
Import Reusable.YK04R Reusable.YA0nR A.ProgBridge A.MemNorm A.MemNormTr.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals), as in the _F files. *)
Import lib.Lib.ExecF lib.Lib.StepF.
Import Ltac2.Ltac2.
Import ListNotations.
Local Open Scope Z_scope.

(* inst c applies c to the hypotheses of the context that carry the names of c's leading binders (the section
   variables and hypotheses its Section MainF generalized it over), as the _F files do. *)
Ltac2 rec inst_go (c : constr) (t : constr) (acc : constr list) :=
  let fin () := match acc with
                | [] => c
                | _ => Constr.Unsafe.make (Constr.Unsafe.App c (Array.of_list (List.rev acc)))
                end in
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod bnd body =>
      match Constr.Binder.name bnd with
      | Some id =>
          match Control.case (fun () => Control.hyp id) with
          | Val hv => let (h, _) := hv in inst_go c (Constr.Unsafe.substnl [h] 0 body) (h :: acc)
          | Err _ => fin ()
          end
      | None => fin ()
      end
  | _ => fin ()
  end.
Ltac2 inst (c : constr) := inst_go c (Constr.type c) [].
Ltac2 Notation "inst_exact" c(constr) := let r := inst c in exact $r.
Set Default Proof Mode "Classic".

(* baseF's footprint hook (its mb_accF), for the steps this file runs itself (the jal, the release store). *)
Ltac mb_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (wa ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG ?lo ?len |- _ =>
          apply (rng_acc_varZ RNG lo len (wa E) n nz H (@eq_refl Z nz));
          cbv [wa]; rewrite ?lib.Lib.MState.unsigned_lit_wrap; Z.div_mod_to_equations; lia
      end
  | |- acc_in ?RNG (?a, ?n) =>
      lazymatch a with
      | context [bv_unsigned (Z_to_bv 64 _)] =>
          let nz := eval cbv in (Z.of_nat n) in
          match goal with
          | H : rng RNG ?lo ?len |- _ =>
              apply (rng_acc_varZ RNG lo len a n nz H (@eq_refl Z nz));
              cbv [wa]; rewrite ?lib.Lib.MState.unsigned_lit_wrap; Z.div_mod_to_equations; lia
          end
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mb_accF.

(* epiF's norm_store (section-local there): a just-stored address in wa-form. *)
Ltac norm_store :=
  lazymatch goal with
  | |- evtF ?segs ?RG ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
      let E := addr_expr a in
      lazymatch a with
      | wa _ => idtac
      | Z_to_bv 64 _ => change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs)
      | _ => replace (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs) by (f_equal; addr_eq_tac)
      end
  end.

(* ---------------------------------------------------------------------------------------------------------
   The lift of one stretch, and the memory facts that only look at a memory pointwise. *)
Section Lift.
Context {fx : lib.Reusable.YK11.FPState}.

(* A footprint run on the normalized memory is a silent prefix of a world walk from the real memory, for any
   footprint that avoids the world's hidden bytes; the continuation gets the run (for ajournal_of_fsteps /
   ctl_release_of_free_law), the post carried back through ms_rel, and the hidden bytes kept. *)
Lemma SRr_evtF_norm : wx_segs_nowrap rsegs ->
  forall (W : YA0n.world rsegs) (RNG : footprint) (model : Model) (R F : bvmap 5 word) (pc : word) (fc : bv 32)
         (m : word -> option byte) (Q : machine_state -> Prop) (K : YA0n.world rsegs -> config -> Prop),
  fp_avoids (YA0n.w_H W) RNG ->
  ro_agree rsegs m ->
  evtF rsegs RNG Q (MS R F pc fc None (normalize rsegs m) (seg_rom rsegs)) ->
  (forall ms' model',
     fsteps rsegs RNG (MS R F pc fc None m (seg_rom rsegs)) ms' ->
     (exists s0, Q s0 /\ ms_rel rsegs ms' s0 /\ ro_same rsegs m (ms_mem ms')) ->
     (forall x : word, YA0n.w_H W x = true -> ms_mem ms' x = m x) ->
     same_but_materialized model model' -> YA0n.SRr rsegs W (mkCfg ms' model') K) ->
  YA0n.SRr rsegs W (mkCfg (MS R F pc fc None m (seg_rom rsegs)) model) K.
Proof.
  intros Hwx W RNG model R F pc fc m Q K Hfp Hro HN Hk.
  destruct (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ m _ Hro HN) as (ms' & Hrun & HP).
  pose proof (fsteps_of_mstepsF _ _ _ Hrun) as Hf.
  apply (SRr_fevt_hid rsegs Hwx W (MS R F pc fc None m (seg_rom rsegs)) model RNG
           (fun s => fsteps rsegs RNG (MS R F pc fc None m (seg_rom rsegs)) s /\
                     exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs m (ms_mem s))).
  - exists ms'. split; [exact Hf | split; [exact Hf | exact HP]].
  - exact Hfp.
  - intros ms1 model1 [Hf1 HP1] Hhid Hs. exact (Hk ms1 model1 Hf1 HP1 Hhid Hs).
Qed.

(* Footprint runs compose and widen; a footprint that avoids a hidden set avoids every smaller one. *)
Lemma fsteps_trans : forall RNG ms1 ms2 ms3,
  fsteps rsegs RNG ms1 ms2 -> fsteps rsegs RNG ms2 ms3 -> fsteps rsegs RNG ms1 ms3.
Proof.
  intros RNG ms1 ms2 ms3 H12 H23. induction H12 as [ms | ms ms1' ms2' Hs _ IH]; [exact H23|].
  eapply fsteps_cons; [exact Hs | exact (IH H23)].
Qed.

Lemma fsteps_mono : forall (RNG RNG' : Z -> nat -> Prop) ms ms',
  (forall b n, RNG b n -> RNG' b n) -> fsteps rsegs RNG ms ms' -> fsteps rsegs RNG' ms ms'.
Proof.
  intros RNG RNG' ms ms' Hsub H. induction H as [ms | ms ms1 ms2 [Hp (accs & Hst & HF)] _ IH];
    [apply fsteps_refl|].
  eapply fsteps_cons; [| exact IH]. split; [exact Hp|]. exists accs. split; [exact Hst|].
  eapply Forall_impl; [| exact HF]. intros acc Ha. exact (Hsub _ _ Ha).
Qed.

Lemma fp_avoids_mono : forall (H H' : word -> bool) RNG,
  (forall x, H x = true -> H' x = true) -> fp_avoids H' RNG -> fp_avoids H RNG.
Proof.
  intros H H' RNG Hsub Hfp a n Hr k Hk. specialize (Hfp a n Hr k Hk).
  destruct (H (woff a k)) eqn:E; [|reflexivity]. rewrite (Hsub _ E) in Hfp. discriminate Hfp.
Qed.

Lemma RNG_W_mono : forall (H H' : word -> bool) b n,
  (forall x, H x = true -> H' x = true) -> RNG_W H' b n -> RNG_W H b n.
Proof.
  intros H H' b n Hsub Hr k Hk. specialize (Hr k Hk).
  destruct (H (woff (Z_to_bv 64 b) k)) eqn:E; [|reflexivity]. rewrite (Hsub _ E) in Hr. discriminate Hr.
Qed.

(* S2's hidden set: the world's, and the class-0 hint word [lo, lo + 8), which S2 neither reads nor writes. *)
Definition hidden_plus (H : word -> bool) (lo : Z) : word -> bool :=
  fun x => H x || ((lo <=? bv_unsigned x) && (bv_unsigned x <? lo + 8)).

Lemma hidden_plus_off : forall (H : word -> bool) lo, H_off_segments rsegs H -> ImgBounds.IMG_HI <= lo ->
  H_off_segments rsegs (hidden_plus H lo).
Proof.
  intros H lo HH Hlo x Hx. unfold hidden_plus in Hx. apply orb_prop in Hx as [Hx | Hx]; [exact (HH x Hx)|].
  apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [sg|] eqn:E; [|reflexivity]. exfalso.
  pose proof (A.Prog.asan_memsetF.find_segment_img rsegs _ 1 sg A.Prog.asan_memsetF.rsegs_in_img E ltac:(lia))
    as [_ Hi].
  unfold ImgBounds.IMG_HI in Hlo.
  match type of Hi with _ <= ?c => let v := eval vm_compute in c in change c with v in Hi end. lia.
Qed.

Lemma fp_avoids_RNG_plus : forall (W : YA0n.world rsegs) lo, fp_avoids (YA0n.w_H W) (RNG_W (hidden_plus (YA0n.w_H W) lo)).
Proof.
  intros W lo. apply (fp_avoids_mono _ (hidden_plus (YA0n.w_H W) lo)); [|exact (fp_avoids_RNG_W _)].
  intros x Hx. unfold hidden_plus. rewrite Hx. reflexivity.
Qed.

(* No byte at or above the image end is read-only. *)
Lemma ro_addr_above : forall x, ImgBounds.IMG_HI <= x < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 x) = false.
Proof.
  intros x Hx. unfold ImgBounds.IMG_HI in Hx.
  unfold ro_addr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  destruct (find_segment rsegs x 1) as [sg|] eqn:E; [|reflexivity]. exfalso.
  pose proof (A.Prog.asan_memsetF.find_segment_img rsegs _ 1 sg A.Prog.asan_memsetF.rsegs_in_img E ltac:(lia))
    as [_ Hi].
  match type of Hi with _ <= ?c => let v := eval vm_compute in c in change c with v in Hi end. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The footprint facts of a stretch at RNG_W (hidden_plus (w_H W) FS): each range is visible in the world and
   avoids the class-0 hint word [FS, FS + 8). *)
Lemma range_visible_plus : forall (H : word -> bool) lo len FS,
  A.ProgBridge.range_visible H lo len -> (lo + len <= FS \/ FS + 8 <= lo) ->
  A.ProgBridge.range_visible (hidden_plus H FS) lo len.
Proof.
  intros H lo len FS (H0 & H1 & Hv) Hd. split; [exact H0|]. split; [exact H1|].
  intros a Ha. unfold hidden_plus. rewrite (Hv a Ha). cbn [orb].
  destruct (Z.leb_spec FS (bv_unsigned (Z_to_bv 64 a))) as [Hle|_]; [|reflexivity].
  rewrite Z_to_bv_unsigned in *. unfold bv_wrap in *. change (bv_modulus 64) with (2 ^ 64) in *.
  rewrite Z.mod_small in * by lia.
  destruct (Z.ltb_spec a (FS + 8)) as [Hlt|_]; [exfalso; lia | reflexivity].
Qed.

Lemma rng_plus : forall (W : YA0n.world rsegs) lo len FS,
  A.ProgBridge.range_visible (YA0n.w_H W) lo len -> (lo + len <= FS \/ FS + 8 <= lo) ->
  rng (RNG_W (hidden_plus (YA0n.w_H W) FS)) lo len.
Proof. intros W lo len FS Hv Hd. apply rng_of_visible. exact (range_visible_plus _ lo len FS Hv Hd). Qed.

Lemma vis_of_present : forall (W : YA0n.world rsegs) (m : word -> option byte) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> apresent (YA0n.w_H W) m a) ->
  A.ProgBridge.range_visible (YA0n.w_H W) lo len.
Proof.
  intros W m lo len H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. exact (proj1 (Hp a Ha)).
Qed.
End Lift.

(* An image byte, by its bounds and its visibility. *)
Lemma img_bounds_of_in_img : forall a, in_img AB1v.tfibsegs a -> 0x10000 <= a < 0x5fe000.
Proof.
  intros a (sg & Hsg & Hr).
  assert (Hin : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                  (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs))
    by (apply in_map_iff; exists sg; split; [reflexivity | exact Hsg]).
  rewrite A.ProgBridge.rsegs_spans in Hin.
  cbn [In] in Hin.
  destruct Hin as [E | [E | [E | [E | []]]]]; injection E as E1 E2; rewrite <- E1, <- E2 in Hr; lia.
Qed.

Lemma vis_of_in_img : forall (W : YA0n.world AB1v.tfibsegs) a,
  in_img AB1v.tfibsegs a -> YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W a Hin. pose proof (img_bounds_of_in_img a Hin) as Hb.
  destruct Hin as (sg & Hsg & Hr).
  apply (A.ProgBridge.vis_of_seg_span rsegs (YA0n.w_H W) (YA0n.w_Hoff W)
           (Z.of_N (seg_base sg)) (Z.of_N (seg_size sg)) a);
    [apply in_map_iff; exists sg; split; [reflexivity | exact Hsg] | lia | lia].
Qed.

(* A byte present at a non-image address stays present across a run that only grows what it can read
   (rd_mono, which the F lane carries); wmono alone would not: it allows a writable byte with no value. *)
Lemma present_of_rd_mono : forall (mA mB m0A m0B : word -> option byte) (H : word -> bool) a,
  mem_rel rsegs mA m0A -> mem_rel rsegs mB m0B ->
  A.Prog.reac_box_model_block_base.rd_mono m0A m0B ->
  0x5fe000 <= a < 2 ^ 64 ->
  apresent H mA a -> apresent H mB a.
Proof.
  intros mA mB m0A m0B H a (EA & _) (EB & _) RM Ha.
  assert (Hn : ~ in_img AB1v.tfibsegs a)
    by (intros Him; pose proof (img_bounds_of_in_img a Him); lia).
  assert (Ero : ro_addr rsegs (Z_to_bv 64 a) = false)
    by (apply ro_addr_above; unfold ImgBounds.IMG_HI; lia).
  intros (Hh & b & Hb).
  split; [exact Hh|].
  assert (E1 : mrd rsegs m0A (Z_to_bv 64 a) = Some b).
  { unfold mrd. rewrite EA. unfold normalize. rewrite Ero, Hb. reflexivity. }
  destruct (RM (Z_to_bv 64 a) (ex_intro _ b E1)) as (b' & E2).
  unfold mrd in E2. rewrite EB in E2. unfold normalize in E2. rewrite Ero in E2.
  assert (SR : seg_rom rsegs (Z_to_bv 64 a) = None).
  { apply (A.MemNorm.seg_rom_unmapped rsegs). rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    exact (find_segment_none AB1v.tfibsegs a Hn). }
  destruct (mB (Z_to_bv 64 a)) as [b''|] eqn:EM; [exists b''; reflexivity|].
  exfalso. rewrite SR in E2. discriminate E2.
Qed.

Section Ext.
(* Facts of a memory that read it byte by byte hold of any memory equal to it at every byte. *)
Variables (X Y : word -> option byte).
Hypothesis XY : forall a, Y a = X a.

Lemma munch_ext_r : forall (W : list ivl) (m0 : word -> option byte), munch W m0 X -> munch W m0 Y.
Proof. intros W m0 H x Hx. rewrite XY. exact (H x Hx). Qed.

Lemma wview_ext : forall a, wview rsegs Y a = wview rsegs X a.
Proof. intros a. unfold wview. rewrite XY. reflexivity. Qed.

Lemma mrd_ext : forall a, mrd rsegs Y a = mrd rsegs X a.
Proof. intros a. unfold mrd. rewrite XY. reflexivity. Qed.

Lemma wmono_ext_r : forall m0, wmono rsegs m0 X -> wmono rsegs m0 Y.
Proof. intros m0 H x Hx. rewrite wview_ext. exact (H x Hx). Qed.

Lemma rd_mono_ext_r : forall m0, A.Prog.reac_box_model_block_base.rd_mono m0 X ->
  A.Prog.reac_box_model_block_base.rd_mono m0 Y.
Proof. intros m0 H x Hx. rewrite mrd_ext. exact (H x Hx). Qed.

Lemma mem_inv_ext : mem_inv rsegs X -> mem_inv rsegs Y.
Proof. intros H a b Hb. rewrite XY in Hb. exact (H a b Hb). Qed.
End Ext.

(* store_ok at the normalization of a real memory from store_ok at a memory equal to it bytewise. *)
Lemma store_ok_norm : forall (mr X : word -> option byte) a n,
  (forall x, X x = normalize rsegs mr x) -> store_ok rsegs X a n = true ->
  store_ok rsegs (normalize rsegs mr) a n = true.
Proof.
  intros mr X a n HX H.
  apply (store_ok_rel rsegs (normalize rsegs mr) X n a); [|exact H].
  split.
  - intros x. rewrite HX. unfold normalize. destruct (ro_addr rsegs x); reflexivity.
  - intros x bb Hro Hb. unfold normalize in Hb. rewrite Hro in Hb. discriminate Hb.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   S1: main_pre_F (= reac_box_model_block_baseF.entry_pre_F) at m := normalize rsegs mr, mr the real memory at
   the entry, then the call instruction `jal __asan_stack_malloc_0` at 0x85bb8 (one step; the allocator's entry
   0x3d5b8 is the event).  The section repeats baseF's Section MainF under the same names (inst needs them); its
   memory facts are stated at m, the footprint facts at RNG := RNG_W (w_H W). *)
Section S1.
Context {fx : lib.Reusable.YK11.FPState}.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (mr : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
Variable W : YA0n.world rsegs.
Let m : word -> option byte := normalize rsegs mr.
Hypothesis Hoff : off = ASAN_K.
Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
Let MI0 : mem_inv rsegs m := mem_inv_normalize rsegs mr.
Hypothesis AC0 : asan_cells m.
Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
  (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K)
  (bv_unsigned sp).
Let RNG : footprint := RNG_W (YA0n.w_H W).
Hypothesis Rimg : rng RNG 0x10000 0x5ee000.
Hypothesis Rwin : rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
Hypothesis Rwsh : A.Prog.reac_box_model_block_cF.sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K)
  REAC_BOX_MODEL_BLOCK_K.
Hypothesis Rtp88 : rng RNG (bv_unsigned tp - 88) 8.
Hypothesis Rtp8 : rng RNG (bv_unsigned tp - 8) 24.
Hypothesis Rtls : A.Prog.reac_box_model_block_cF.reac_box_model_block_tls_rng RNG m (bv_unsigned tp).
Hypothesis RFSh : rng RNG FS (fs_frame FS 0%nat 0 - FS).
Hypothesis RFSw : A.Prog.reac_box_model_block_cF.rng_ivls RNG (fp_w [0%nat] FS).
Hypothesis RFSsh : rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8).
Let Rby : lib.Lib.RngBytes.rng_bytes RNG := rng_bytes_RNG_W (YA0n.w_H W).
Hypothesis Rwsw : A.Prog.rng_asan.sh_word_rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
Hypothesis RP : p <> 0 -> rng RNG p 296.
Hypothesis RPs : p <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover RNG p 296.
Hypothesis RO : o <> 0 -> rng RNG o 32.
Hypothesis ROs : o <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover RNG o 32.
Hypothesis RN : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  rng RNG (RcSynth.rname row) (Z.of_nat (length nb)).
Hypothesis RNs : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  A.Prog.reac_box_model_block_cF.sh_cover RNG (RcSynth.rname row) (Z.of_nat (length nb)).
Hypothesis RJ13s : b = 2 -> A.Prog.reac_box_model_block_cF.sh_cover RNG JOIN_0013 32.
Hypothesis RJ14s : b = 1 -> A.Prog.reac_box_model_block_cF.sh_cover RNG JOIN_0014 32.
(* The narrowed entry (baseF.entry_pre_F, route (C)) takes no shadow premise; its fk_facts_F reads the membership of
   the frame's shadow in the region instead, and its window lemma reads o's addressability: the data premises of
   baseF's Section MainF, at the entry memory. *)
Hypothesis Rp : 0 <= p < 2^64.
Hypothesis Rb : 0 <= b < 2^64.
Hypothesis Ro : 0 <= o < 2^64.
Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
  (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
  (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).

Let bmb_at_call := ltac2:(inst_exact @A.Prog.reac_box_model_block_baseF.bmb_at_call).
Let entry_pre_F := ltac2:(inst_exact @A.Prog.reac_box_model_block_baseF.entry_pre_F).

(* The state at the allocator's entry: the jal has set ra := 0x85bbc and pc := 0x3d5b8 =
   __asan_stack_malloc_0 (pc_stack_malloc (as_code B) 0 by CtrlFrame.palf_sm0). *)
Definition bmb_jal_post (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state -> Prop :=
  fun s => exists (a1' a2' : word) (m1 : word -> option byte), bmb_at_call m1 /\
    s = MS (mkR (Z_to_bv 64 0x85bbc) (Z_to_bv 64 A) gp tp t0 t1 t2 sp (Z_to_bv 64 A)
              (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5
              (Z_to_bv 64 b) s7 s8 (wa off) s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x3d5b8) fc None m1 (seg_rom rsegs).

Lemma bmb_S1_SRr : wx_segs_nowrap rsegs ->
  forall (model : Model) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (K : YA0n.world rsegs -> config -> Prop),
  ro_agree rsegs mr ->
  (forall ms' model',
     fsteps rsegs RNG (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o)
                              a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None mr (seg_rom rsegs)) ms' ->
     (exists s0', bmb_jal_post t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0' /\ ms_rel rsegs ms' s0' /\
                  ro_same rsegs mr (ms_mem ms')) ->
     (forall x : word, YA0n.w_H W x = true -> ms_mem ms' x = mr x) ->
     same_but_materialized model model' -> YA0n.SRr rsegs W (mkCfg ms' model') K) ->
  YA0n.SRr rsegs W
    (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o)
                    a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None mr (seg_rom rsegs)) model) K.
Proof.
  intros Hwx model t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K Hro Hk.
  apply (SRr_evtF_norm Hwx W RNG model _ F _ fc mr (bmb_jal_post t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6) K
           (fp_avoids_RNG_W (YA0n.w_H W)) Hro); [|exact Hk].
  apply (entry_pre_F t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 _ m eq_refl).
  intros a1' a2' m1 HC.
  step.
  apply evtF_done. exists a1', a2', m1. split; [exact HC | reflexivity].
Qed.
End S1.

(* ---------------------------------------------------------------------------------------------------------
   The release store and S3, in epiF's Section MainF.  m is the Section memory of S2 / S3 (the glue instantiates
   it at the normalized memory after the stack-malloc call); the real memories here are mld_r (at the store) and
   mfin_r (after it). *)
Section S3.
Context {fx : lib.Reusable.YK11.FPState}.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
Variable W : YA0n.world rsegs.
Hypothesis Hoff : off = ASAN_K.
Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis AC0 : asan_cells m.
Hypothesis SR0 : A.ShadowRwOn.shadow_rw_on (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
  (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K)
  (bv_unsigned sp).
Hypothesis Rp : 0 <= p < 2^64.
Hypothesis Rb : 0 <= b < 2^64.
Hypothesis Ro : 0 <= o < 2^64.
Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
  (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  RcBox.name_ok nb /\ bytes_at rsegs m (RcSynth.rname row) nb /\
  (bv_unsigned sp <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
  (o = 0 \/ o + 32 <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= o).
Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
  (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
Hypothesis AP : p <> 0 -> addressable m p 296.
Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  addressable m (RcSynth.rname row) (Z.of_nat (length nb)).
Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  fp_dj [(RcSynth.rname row, RcSynth.rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).
(* S2 / S3's footprint: every visible byte but the class-0 hint word [FS, FS + 8), which no stretch after the
   allocator call reads or writes; the footprint then keeps it (fsteps_keeps_hidden). *)
Let RNG : footprint := RNG_W (hidden_plus (YA0n.w_H W) FS).
Hypothesis Rimg : rng RNG 0x10000 0x5ee000.
Hypothesis Rwin : rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
Hypothesis Rwsh : A.Prog.reac_box_model_block_cF.sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K)
  REAC_BOX_MODEL_BLOCK_K.
Hypothesis Rtp88 : rng RNG (bv_unsigned tp - 88) 8.
Hypothesis Rtp8 : rng RNG (bv_unsigned tp - 8) 24.
Hypothesis Rtls : A.Prog.reac_box_model_block_cF.reac_box_model_block_tls_rng RNG m (bv_unsigned tp).
Hypothesis RFSh : rng RNG FS (fs_frame FS 0%nat 0 - FS).
Hypothesis RFSw : A.Prog.reac_box_model_block_cF.rng_ivls RNG (tl (fp_w [0%nat] FS)).
Hypothesis RFSsh : rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8).
Let Rby : lib.Lib.RngBytes.rng_bytes RNG := rng_bytes_RNG_W (hidden_plus (YA0n.w_H W) FS).
Hypothesis Rwsw : A.Prog.rng_asan.sh_word_rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
Hypothesis RP : p <> 0 -> rng RNG p 296.
Hypothesis RPs : p <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover RNG p 296.
Hypothesis RO : o <> 0 -> rng RNG o 32.
Hypothesis ROs : o <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover RNG o 32.
Hypothesis RN : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  rng RNG (RcSynth.rname row) (Z.of_nat (length nb)).
Hypothesis RNs : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  A.Prog.reac_box_model_block_cF.sh_cover RNG (RcSynth.rname row) (Z.of_nat (length nb)).
Hypothesis RJ13s : b = 2 -> A.Prog.reac_box_model_block_cF.sh_cover RNG JOIN_0013 32.
Hypothesis RJ14s : b = 1 -> A.Prog.reac_box_model_block_cF.sh_cover RNG JOIN_0014 32.

Notation FK := (A.Prog.reac_box_model_block_base.FK FS A).
Notation EB := (A.Prog.reac_box_model_block_base.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
Notation Q0 := (C_ON.reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
                  p b o FS row nb).
Let bmb_at_rel := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.bmb_at_rel).
Let bmb_after_rel := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.bmb_after_rel).
Let bmb_rel_step := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.bmb_rel_step).
Let epi_RFSfl_F := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.epi_RFSfl_F).
Let epi_post_F := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.epi_post_F).
Let epi_pre_F := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.epi_pre_F).
Let bmb_KR := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.bmb_KR).

(* The released state at 0x864fc (the start of S3): the store has written the flag byte 0. *)
Definition bmb_rel_post (fr j r : Z) (mc : word -> option byte)
    (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27 y28 y29 y30 y31 : word) : machine_state -> Prop :=
  fun s => exists mfin : word -> option byte, bmb_after_rel fr j mc mfin /\
    s = MS (mkR y1 (Z_to_bv 64 A) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
              (Z_to_bv 64 (fs_flag FS 0 j)) y11 y12 y13 y14 y15 y16 y17
              (Z_to_bv 64 fr) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) y22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) y26 y27 y28 y29 y30 y31)
           F (Z_to_bv 64 0x864fc) fc None mfin (seg_rom rsegs).

(* Event 2's store: [0x864f8 .. 0x864fc) from the state epi_pre_F hands over (bmb_at_rel at a memory equal
   bytewise to the normalization of the real memory mld_r). *)
Lemma bmb_REL_SRr : wx_segs_nowrap rsegs ->
  forall (model : Model) (mld_r mc mld : word -> option byte) (fr j r : Z)
         (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27 y28 y29 y30 y31 : word)
         (K : YA0n.world rsegs -> config -> Prop),
  0 <= j < fs_M 0%nat -> fr = fs_frame FS 0%nat j ->
  bmb_at_rel fr j mc mld -> mem_rel rsegs mld_r mld ->
  (forall ms' model',
     fsteps rsegs RNG (MS (mkR y1 (Z_to_bv 64 A) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
              (Z_to_bv 64 (fs_flag FS 0 j)) y11 y12 y13 y14 y15 y16 y17
              (Z_to_bv 64 fr) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) y22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) y26 y27 y28 y29 y30 y31)
           F (Z_to_bv 64 0x864f8) fc None mld_r (seg_rom rsegs)) ms' ->
     (exists s0', bmb_rel_post fr j r mc y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27 y28 y29 y30 y31 s0' /\
                  ms_rel rsegs ms' s0' /\ ro_same rsegs mld_r (ms_mem ms')) ->
     (forall x : word, YA0n.w_H W x = true -> ms_mem ms' x = mld_r x) ->
     same_but_materialized model model' -> YA0n.SRr rsegs W (mkCfg ms' model') K) ->
  YA0n.SRr rsegs W
    (mkCfg (MS (mkR y1 (Z_to_bv 64 A) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
              (Z_to_bv 64 (fs_flag FS 0 j)) y11 y12 y13 y14 y15 y16 y17
              (Z_to_bv 64 fr) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) y22 (Z_to_bv 64 fr)
              (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) y26 y27 y28 y29 y30 y31)
           F (Z_to_bv 64 0x864f8) fc None mld_r (seg_rom rsegs)) model) K.
Proof.
  intros Hwx model mld_r mc mld fr j r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27 y28 y29 y30 y31 K
    Hj Efr HREL HMR Hk.
  pose proof (ro_agree_of_mem_rel rsegs _ _ HMR) as Hro.
  assert (HNm : forall x, normalize rsegs mld_r x = mld x) by (intros x; symmetry; exact (proj1 HMR x)).
  assert (HREL' : bmb_at_rel fr j mc (normalize rsegs mld_r)).
  { destruct HREL as (MU1 & WM1 & MU2 & WM2 & RM & MI & HS).
    split; [exact (munch_ext_r _ _ HNm _ _ MU1)|]. split; [exact (wmono_ext_r _ _ HNm _ WM1)|].
    split; [exact (munch_ext_r _ _ HNm _ _ MU2)|]. split; [exact (wmono_ext_r _ _ HNm _ WM2)|].
    split; [exact (rd_mono_ext_r _ _ HNm _ RM)|]. split; [exact (mem_inv_ext _ _ HNm MI)|].
    exact (store_ok_norm mld_r mld _ _ (proj1 HMR) HS). }
  apply (SRr_evtF_norm Hwx W RNG model _ F _ fc mld_r
           (bmb_rel_post fr j r mc y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27 y28 y29 y30 y31) K
           (fp_avoids_RNG_plus W FS) Hro); [|exact Hk].
  pose proof HREL' as (_ & _ & _ & _ & _ & _ & HSflag).
  pose proof (epi_RFSfl_F j Hj) as RFL.
  step.
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?l) _) => try (replace l with [Z_to_bv 8 0] by reflexivity)
   end).
  norm_store.
  apply evtF_done. eexists. split; [exact (bmb_rel_step fr j mc _ Hj Efr HREL') | reflexivity].
Qed.

(* S3: main_post_F (= epi_post_F) from the released state, at the normalization of the real memory mfin_r; its
   post hands the final memory back (Q0 s /\ ms_mem s = the normalized memory: [0x864fc .. ret] stores nothing). *)
Lemma bmb_S3_SRr : wx_segs_nowrap rsegs ->
  forall (model : Model) (mfin_r mc mfin : word -> option byte) (r : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word)
         (spc fr f j n : Z) (w56 : word) (K : YA0n.world rsegs -> config -> Prop),
  FK fr f spc j n w56 -> EB fr f j n w56 mc -> n = 1 ->
  r = (if (p =? 0) || (o =? 0) then -1 else RcSynth.rc row b) ->
  bmb_after_rel fr j mc mfin -> mem_rel rsegs mfin_r mfin ->
  (forall ms' model',
     fsteps rsegs RNG (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x864fc) fc None mfin_r (seg_rom rsegs)) ms' ->
     (exists s0', (Q0 s0' /\ ms_mem s0' = normalize rsegs mfin_r) /\ ms_rel rsegs ms' s0' /\
                  ro_same rsegs mfin_r (ms_mem ms')) ->
     (forall x : word, YA0n.w_H W x = true -> ms_mem ms' x = mfin_r x) ->
     same_but_materialized model model' -> YA0n.SRr rsegs W (mkCfg ms' model') K) ->
  YA0n.SRr rsegs W
    (mkCfg (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x864fc) fc None mfin_r (seg_rom rsegs)) model) K.
Proof.
  intros Hwx model mfin_r mc mfin r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
    spc fr f j n w56 K HK HEB Hn Hr HREL HMR Hk.
  pose proof (ro_agree_of_mem_rel rsegs _ _ HMR) as Hro.
  assert (HNm : forall x, normalize rsegs mfin_r x = mfin x) by (intros x; symmetry; exact (proj1 HMR x)).
  assert (HREL' : bmb_after_rel fr j mc (normalize rsegs mfin_r)).
  { destruct HREL as (MU1 & WM1 & MU2 & WM2 & RM & MI & HF).
    split; [exact (munch_ext_r _ _ HNm _ _ MU1)|]. split; [exact (wmono_ext_r _ _ HNm _ WM1)|].
    split; [exact (munch_ext_r _ _ HNm _ _ MU2)|]. split; [exact (wmono_ext_r _ _ HNm _ WM2)|].
    split; [exact (rd_mono_ext_r _ _ HNm _ RM)|]. split; [exact (mem_inv_ext _ _ HNm MI)|].
    rewrite (mrd_ext _ _ HNm). exact HF. }
  apply (SRr_evtF_norm Hwx W RNG model _ F _ fc mfin_r (fun s => Q0 s /\ ms_mem s = normalize rsegs mfin_r) K
           (fp_avoids_RNG_plus W FS) Hro); [|exact Hk].
  exact (epi_post_F r mc _ x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
           spc fr f j n w56 HK HEB Hn Hr HREL').
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The tail in cgif's world: from the release state S2 hands over (bmb_rel_state, at the frame (0, jj) cgif
   allocated) through the store and S3 to the return, with the caller's journal: the release by
   A/ProgWorldAstack.v ctl_release_of_free_law 0 (a Theorem Labs lane, f5c48cc9a13; the fsteps twin of the core's aj_flag_store
   over astack_free_law) over S2's run and the store, then A/ProgWorld.v ajournal_of_fsteps over S3 (it writes
   nothing). *)
Context {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws AB1v.tfibsegs B.
Hypothesis ASF : astack_free_law AB1v.tfibsegs B.

Definition bmb_rel_state (jj : Z) : machine_state -> Prop := fun s =>
  exists (r : Z) (mc mld : word -> option byte)
         (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27 y28 y29 y30 y31 : word),
    EB (fs_frame FS 0%nat jj) (fs_frame FS 0%nat jj) jj 1 (Z_to_bv 64 (fs_flag FS 0 jj)) mc /\
    r = (if (p =? 0) || (o =? 0) then -1 else RcSynth.rc row b) /\
    bmb_at_rel (fs_frame FS 0%nat jj) jj mc mld /\
    s = MS (mkR y1 (Z_to_bv 64 A) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
              (Z_to_bv 64 (fs_flag FS 0 jj)) y11 y12 y13 y14 y15 y16 y17
              (Z_to_bv 64 (fs_frame FS 0%nat jj)) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) y22
              (Z_to_bv 64 (fs_frame FS 0%nat jj)) (Z_to_bv 64 (fs_frame FS 0%nat jj / 8 + off)) (Z_to_bv 64 off)
              y26 y27 y28 y29 y30 y31)
           F (Z_to_bv 64 0x864f8) fc None mld (seg_rom rsegs).

(* The tail's writes: EBW without the hint word (the window, the flag byte, the frame, its shadow, and o). *)
Definition bmb_WR (jj : Z) : list ivl :=
  [(bv_unsigned sp - 4272, bv_unsigned sp); (fs_flag FS 0 jj, fs_flag FS 0 jj + 1);
   (fs_frame FS 0%nat jj, fs_frame FS 0%nat jj + 64);
   (shadow_addr (fs_frame FS 0%nat jj), shadow_addr (fs_frame FS 0%nat jj) + 8)] ++
  (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)]).

Lemma munch_drop_hint : forall jj (m1 m2 : word -> option byte),
  munch (A.Prog.reac_box_model_block_base.EBW sp p o FS (fs_frame FS 0%nat jj) jj 1) m1 m2 ->
  (forall x : word, hidden_plus (YA0n.w_H W) FS x = true -> m2 x = m1 x) ->
  munch (bmb_WR jj) m1 m2.
Proof.
  intros jj m1 m2 HM HH x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) FS) as [h1 | h1].
  - apply HM. unfold A.Prog.reac_box_model_block_base.EBW, A.Prog.reac_box_model_block_base.Wf, bmb_WR in *.
    cbn [app outside] in *. destruct Hx as (X1 & X2 & X3 & X4 & X5).
    split; [exact X1|]. split; [lia|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. exact X5.
  - destruct (Z_lt_le_dec (bv_unsigned x) (FS + 8)) as [h2 | h2].
    + apply HH. unfold hidden_plus. apply orb_true_iff. right. apply andb_true_iff.
      split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    + apply HM. unfold A.Prog.reac_box_model_block_base.EBW, A.Prog.reac_box_model_block_base.Wf, bmb_WR in *.
      cbn [app outside] in *. destruct Hx as (X1 & X2 & X3 & X4 & X5).
      split; [exact X1|]. split; [lia|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. exact X5.
Qed.

Lemma ro_same_trans : forall m1 m2 m3, ro_same rsegs m1 m2 -> ro_same rsegs m2 m3 -> ro_same rsegs m1 m3.
Proof. intros m1 m2 m3 H12 H23 a Ha. rewrite (H23 a Ha). exact (H12 a Ha). Qed.

(* Two real memories whose normalizations agree and which agree on the read-only bytes are equal. *)
Lemma mem_eq_of_norm : forall mx my : word -> option byte,
  (forall a, normalize rsegs my a = normalize rsegs mx a) -> ro_same rsegs mx my -> forall a, my a = mx a.
Proof.
  intros mx my HNr Hro a. destruct (ro_addr rsegs a) eqn:E; [exact (Hro a E)|].
  specialize (HNr a). unfold normalize in HNr. rewrite E in HNr. exact HNr.
Qed.

Lemma bmb_tail : wx_segs_nowrap rsegs ->
  forall (mem2 : word -> option byte) (msR ms1 : machine_state) (md1 : Model) (jj : Z)
         STK sp0 (FPj : list (Z * Z)) ly S0 (W0 : YA0n.world rsegs) mem0 md0 own lyc S2 md2 k
         (Qpost : YA0n.world rsegs -> config -> Prop),
  0 <= jj < fs_M 0%nat ->
  m = normalize rsegs mem2 -> ro_agree rsegs mem2 ->
  ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FPj ly S0 W0 mem0 md0 ((0, jj) :: own) lyc S2 W mem2 md2 k ->
  FS = ly_F lyc ->
  ms_mem msR = mem2 ->
  fsteps rsegs RNG msR ms1 ->
  (exists st1, bmb_rel_state jj st1 /\ ms_rel rsegs ms1 st1 /\ ro_same rsegs mem2 (ms_mem ms1)) ->
  same_but_materialized md2 md1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside (bmb_WR jj) a ->
     awr_byte STK sp0 FPj (ablocks B ly S0) (ablocks B lyc S2) lyc ((0, jj) :: own) a \/ a = flag_addr lyc 0 jj) ->
  (forall ms3 md3 st3,
     ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FPj ly S0 W0 mem0 md0 own lyc (stack_free_state 0 jj S2) W
       (ms_mem ms3) md3 k ->
     Q0 st3 -> ms_rel rsegs ms3 st3 -> ro_same rsegs mem2 (ms_mem ms3) ->
     munch (bmb_WR jj) mem2 (ms_mem ms3) ->
     (forall a, 0x5fe000 <= a < 2 ^ 64 ->
        apresent (YA0n.w_H W) mem2 a -> apresent (YA0n.w_H W) (ms_mem ms3) a) ->
     YA0n.SRr rsegs W (mkCfg ms3 md3) Qpost) ->
  YA0n.SRr rsegs W (mkCfg ms1 md1) Qpost.
Proof.
  intros Hwx mem2 msR ms1 md1 jj STK sp0 FPj ly S0 W0 mem0 md0 own lyc S2 md2 k Qpost
    Hjj Em Hro2 HJ2 EFS EmR Hrun1 (st1 & HS1 & Hrel1 & Hros1) Hsame1 Hawr K.
  destruct HS1 as (r & mc & mld & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y22 & y26 & y27 &
                   y28 & y29 & y30 & y31 & HEB & Hr & HREL & ->).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ Hrel1) as [Ems1 HMR1].
  set (fr := fs_frame FS 0%nat jj) in *.
  assert (HFK : FK fr fr A jj 1 (Z_to_bv 64 (fs_flag FS 0 jj))) by (right; repeat split; lia || reflexivity).
  rewrite Ems1.
  eapply (bmb_REL_SRr Hwx md1 (ms_mem ms1) mc mld fr jj r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27
            y28 y29 y30 y31 Qpost Hjj eq_refl HREL HMR1).
  intros ms2 md2' Hrun2 (st2 & (mfin & HAF & ->) & Hrel2 & Hros2) _ Hsame2.
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ Hrel2) as [Ems2 HMR2].
  (* the release, as a journal step over S2's run and the store *)
  assert (Hrun12 : fsteps rsegs RNG msR ms2) by (eapply fsteps_trans; [exact Hrun1 | rewrite Ems1; exact Hrun2]).
  assert (Hros12 : ro_same rsegs mem2 (ms_mem ms2)) by exact (ro_same_trans _ _ _ Hros1 Hros2).
  assert (HMR0 : mem_rel rsegs mem2 m) by (rewrite Em; exact (mem_rel_normalize rsegs mem2 Hro2)).
  pose proof HAF as (_ & _ & MUe & _ & RMe & _ & Hfl0).
  assert (HMU : munch (bmb_WR jj) mem2 (ms_mem ms2)).
  { apply munch_drop_hint.
    - exact (munch_rel rsegs _ mem2 m (ms_mem ms2) mfin HMR0 HMR2 Hros12 MUe).
    - intros x Hx. rewrite <- EmR.
      apply (fsteps_keeps_hidden rsegs Hwx (hidden_plus (YA0n.w_H W) FS) RNG msR ms2); [| exact Hrun12 |
        exact (fp_avoids_RNG_W _) | exact Hx].
      apply hidden_plus_off; [exact (YA0n.w_Hoff W)|].
      pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & HPl & _). pose proof HPl as (_ & _ & P3 & _).
      unfold ImgBounds.IMG_HI. unfold ASAN_GT in P3. lia. }
  destruct (A.ProgWorld.ctl_fs_geom FS 0 jj ltac:(lia)) as (_ & _ & _ & G4 & _).
  change (Z.to_nat 0) with 0%nat in G4.
  assert (Efl : flag_addr lyc 0 jj = fs_flag FS 0 jj) by (rewrite G4, EFS; reflexivity).
  assert (Hflag0 : mbyte AB1v.tfibsegs (ms_mem ms2) (flag_addr lyc 0 jj) = Some (Z_to_bv 8 0)).
  { rewrite Efl. pose proof (proj1 HMR2 (wa (fs_flag FS 0 jj))) as E1.
    unfold mrd in Hfl0. rewrite E1 in Hfl0. unfold normalize in Hfl0.
    unfold mbyte. change AB1v.tfibsegs with rsegs. unfold wa in Hfl0.
    destruct (ro_addr rsegs (Z_to_bv 64 (fs_flag FS 0 jj))) eqn:Ero.
    - exfalso. rewrite ro_addr_above in Ero; [discriminate Ero|].
      pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & HPl & _). pose proof HPl as (_ & _ & P3 & P4 & _).
      pose proof (P4 (fs_flag FS 0 jj) ltac:(unfold fs_flag, FS_SIZE, fs_M in *; cbn [Z.of_nat] in *; lia)) as A4.
      unfold ImgBounds.IMG_HI. unfold ASAN_GT in P3. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A4.
      unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *. lia.
    - exact Hfl0. }
  assert (HJ3 : ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FPj ly S0 W0 mem0 md0 own lyc (stack_free_state 0 jj S2) W
                  (ms_mem ms2) md2' k).
  { refine (A.ProgWorldAstack.ctl_release_of_free_law (SK := SK) B 0 LAWS ASF Hwx ltac:(lia) STK sp0 FPj ly S0 W0
              mem0 md0 own lyc S2 W msR ms2 md2 md2' k jj RNG (bmb_WR jj) _ Hrun12 (fp_avoids_RNG_plus W FS) _
              (same_but_materialized_trans _ _ _ Hsame1 Hsame2) Hawr Hflag0).
    - rewrite EmR. exact HJ2.
    - rewrite EmR. exact HMU. }
  (* S3 *)
  rewrite Ems2.
  eapply (bmb_S3_SRr Hwx md2' (ms_mem ms2) mc mfin r y1 y5 y6 y7 (Z_to_bv 64 (fs_flag FS 0 jj)) y11 y12 y13 y14 y15
            y16 y17 y22 y26 y27 y28 y29 y30 y31 A fr fr jj 1 (Z_to_bv 64 (fs_flag FS 0 jj)) Qpost HFK HEB eq_refl Hr
            HAF HMR2).
  intros ms3 md3 Hrun3 (st3 & (HQ0 & Es3) & Hrel3 & Hros3) _ Hsame3.
  pose proof Hrel3 as (_ & _ & _ & _ & _ & _ & _ & HMR3).
  assert (Heq3 : forall a, ms_mem ms3 a = ms_mem ms2 a).
  { apply mem_eq_of_norm; [| exact Hros3]. intros a. rewrite <- (proj1 HMR3 a), Es3. reflexivity. }
  assert (HJ4 : ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FPj ly S0 W0 mem0 md0 own lyc (stack_free_state 0 jj S2) W
                  (ms_mem ms3) md3 k).
  { refine (A.ProgWorld.ajournal_of_fsteps (SK := SK) B LAWS Hwx STK sp0 FPj ly S0 W0 mem0 md0 own lyc
              (stack_free_state 0 jj S2) W ms2 ms3 md2' md3 k RNG [] HJ3 ltac:(rewrite Ems2; exact Hrun3)
              (fp_avoids_RNG_plus W FS) _ Hsame3 _).
    - intros x _. exact (Heq3 x).
    - intros a _ Hout. exfalso. apply Hout. exact I. }
  apply (K ms3 md3 st3 HJ4 HQ0 Hrel3).
  - intros a Ha. rewrite (Heq3 a). exact (Hros12 a Ha).
  - intros x Hx. rewrite (Heq3 x). exact (HMU x Hx).
  - intros a Ha Hp.
    destruct (present_of_rd_mono mem2 (ms_mem ms2) m mfin (YA0n.w_H W) a HMR0 HMR2 RMe Ha Hp) as (Hh & by0 & Hby).
    split; [exact Hh|]. exists by0. rewrite (Heq3 (Z_to_bv 64 a)). exact Hby.
Qed.

(* S2's handed-over obligation (main_mid_F's HKR) at the release continuation: the FK arm of the frame cgif allocated
   (class 0, index jj, n = 1) ends in bmb_rel_state jj by epi_pre_F; every other arm's obligation is True. *)
Definition bmb_Qrel (jj : Z) : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop :=
  fun fr f spc j n w56 s => if (j =? jj) && (n =? 1) then bmb_rel_state jj s else True.

Lemma bmb_KR_rel : forall jj, bmb_KR (bmb_Qrel jj).
Proof.
  intros jj r mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 spc fr f j n w56
    HK HEB Hr.
  unfold bmb_Qrel.
  destruct ((j =? jj) && (n =? 1)) eqn:E; [|apply evtF_done; exact I].
  apply andb_true_iff in E as [Ej En]. apply Z.eqb_eq in Ej. apply Z.eqb_eq in En. subst j n.
  destruct HK as [(_ & _ & _ & _ & Hn0) | (Hj & Efr & Ef & Espc & Ew & _)]; [discriminate Hn0|].
  subst fr f spc w56.
  apply (epi_pre_F _ r mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
           A (fs_frame FS 0%nat jj) (fs_frame FS 0%nat jj) jj 1 (Z_to_bv 64 (fs_flag FS 0 jj))
           ltac:(right; repeat split; lia || reflexivity) HEB Hr eq_refl).
  intros mld y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y26 y27 y28 y29 y30 y31 HREL.
  apply evtF_done.
  exists r, mc, mld, y1, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y22, y26, y27, y28, y29, y30, y31.
  split; [exact HEB|]. split; [exact Hr|]. split; [exact HREL | reflexivity].
Qed.

(* The callee contracts of S2 (main_mid_F's Section MainF), in their proved route (C) _F_on forms: a Theorem Labs lane's
   asan_memset_holds_F_on / asan_memcpy_holds_F_on and a Theorem Labs lane's build_dt1_single_F_holds_on_closed (all carried by
   path from a working branch d6c918af46f). *)
Let HMSF := A.Prog.asan_memsetF_on.asan_memset_holds_F_on A.Prog.memset.memset_holds.
Let HMCF := A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on.
Let HBDF := A.Prog.build_dt1_singleF.build_dt1_single_F_holds_on_closed.
(* S2 and the tail, from the allocator's return (0x85bbc, real memory mem2) to the return of the function, in cgif's
   world: S2 lifted (A.Prog.reac_box_model_blockF.main_mid_F at Q := bmb_Qrel jj, its obligation discharged by
   bmb_KR_rel), then bmb_tail. *)
Lemma bmb_from_ret : wx_segs_nowrap rsegs ->
  forall (mem2 : word -> option byte) (md2 : Model) (jj : Z)
         (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
         STK sp0 (FPj : list (Z * Z)) ly S0 (W0 : YA0n.world rsegs) mem0 md0 own lyc S2 k
         (Qpost : YA0n.world rsegs -> config -> Prop),
  m = normalize rsegs mem2 -> ro_agree rsegs mem2 ->
  0 <= jj < fs_M 0%nat ->
  bytes_at rsegs m (fs_flag FS 0 jj) [Z_to_bv 8 1] ->
  bytes_at rsegs m (fs_frame FS 0 jj + 56) (le8 (Z_to_bv 64 (fs_flag FS 0 jj))) ->
  bytes_at rsegs m (shadow_addr (fs_frame FS 0 jj)) (repeat (Z_to_bv 8 0) 8) ->
  addressable m (fs_frame FS 0 jj) 64 ->
  stk rsegs m (fs_frame FS 0 jj) (fs_frame FS 0 jj + 64) ->
  rw_cells rsegs m (bv_unsigned sp + -104) (A.Prog.reac_box_model_block_base.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FPj ly S0 W0 mem0 md0 ((0, jj) :: own) lyc S2 W mem2 md2 k ->
  FS = ly_F lyc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside (bmb_WR jj) a ->
     awr_byte STK sp0 FPj (ablocks B ly S0) (ablocks B lyc S2) lyc ((0, jj) :: own) a \/ a = flag_addr lyc 0 jj) ->
  (forall ms3 md3 s3,
     ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FPj ly S0 W0 mem0 md0 own lyc (stack_free_state 0 jj S2) W
       (ms_mem ms3) md3 k ->
     Q0 s3 -> ms_rel rsegs ms3 s3 -> ro_same rsegs mem2 (ms_mem ms3) ->
     munch (bmb_WR jj) mem2 (ms_mem ms3) ->
     (forall a, 0x5fe000 <= a < 2 ^ 64 ->
        apresent (YA0n.w_H W) mem2 a -> apresent (YA0n.w_H W) (ms_mem ms3) a) ->
     YA0n.SRr rsegs W (mkCfg ms3 md3) Qpost) ->
  YA0n.SRr rsegs W
    (mkCfg (MS (mkR x1' (Z_to_bv 64 A) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                  (Z_to_bv 64 (fs_frame FS 0 jj)) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                  (Z_to_bv 64 b) s7 s8 (wa off) s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x85bbc) fc None mem2 (seg_rom rsegs)) md2) Qpost.
Proof.
  intros Hwx mem2 md2 jj x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' STK sp0 FPj ly S0 W0 mem0 md0
    own lyc S2 k Qpost Em Hro2 Hjj Hfl H56 Hsh Had Hst Hsv HJ2 EFS Hawr K.
  apply (SRr_evtF_norm Hwx W RNG md2 _ F _ fc mem2 (bmb_rel_state jj) Qpost (fp_avoids_RNG_plus W FS) Hro2).
  - rewrite <- Em.
    set (Q := bmb_Qrel jj).
    pose proof (bmb_KR_rel jj) as HKR. fold Q in HKR.
    pose (MM := ltac2:(inst_exact @A.Prog.reac_box_model_blockF.main_mid_F)).
    apply (evtF_mono _ _ _ _ _ (MM Hjj Hfl H56 Hsh Had Hst Hsv)).
    intros s Hs. cbv delta [Q bmb_Qrel] beta zeta in Hs. rewrite !Z.eqb_refl in Hs. exact Hs.
  - intros ms1 md1 Hrun1 Hpost1 _ Hsame1.
    exact (bmb_tail Hwx mem2 _ ms1 md1 jj STK sp0 FPj ly S0 W0 mem0 md0 own lyc S2 md2 k Qpost Hjj Em Hro2 HJ2 EFS
             (eq_refl : ms_mem (MS _ F (Z_to_bv 64 0x85bbc) fc None mem2 (seg_rom rsegs)) = mem2)
             Hrun1 Hpost1 Hsame1 Hawr K).
Qed.
End S3.

(* ---------------------------------------------------------------------------------------------------------
   The cgif side.  SEGS = AB1v.tfibsegs, which is A/Img0.v's rsegs (ProgBridge.tfibsegs_rsegs, by conversion). *)
Local Notation rget := lib.Reusable.YK11.getr.
Local Notation rmkst := lib.Reusable.YK11.mkst.

(* Byte-level glue between the core's view and ctrl's raw-memory facts. *)
Lemma bytes_at_agree : forall (m m' : word -> option byte) a bs, bytes_at rsegs m a bs ->
  (forall i, (i < length bs)%nat -> m' (wa (a + Z.of_nat i)) = m (wa (a + Z.of_nat i))) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  specialize (H i Hi). unfold mrd in *. rewrite (E i Hi). exact H.
Qed.

Lemma wr_at_agree : forall (m m' : word -> option byte) a n, wr_at rsegs m a n ->
  (forall i, 0 <= i < n -> m' (wa (a + i)) = m (wa (a + i))) -> wr_at rsegs m' a n.
Proof.
  intros m m' a n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  specialize (H i Hi). unfold wview in *. rewrite (E i Hi). exact H.
Qed.

Lemma rw_cells_agree : forall (m m' : word -> option byte) a cs, rw_cells rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wa (a + i)) = m (wa (a + i))) -> rw_cells rsegs m' a cs.
Proof.
  intros m m' a cs [[Hwf Hb] Hw] E. split; [split; [exact Hwf|]|].
  - apply (bytes_at_agree m); [exact Hb|]. intros i Hi. apply E.
    rewrite (cells_bytes_length cs Hwf) in Hi. lia.
  - exact (wr_at_agree m m' a _ Hw E).
Qed.

(* At a visible address outside the segments the view determines the raw byte. *)
Lemma raw_of_aview : forall {fx : lib.Reusable.YK11.FPState} (W : YA0n.world AB1v.tfibsegs)
    (mem mem' : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> YA0n.w_H W (Z_to_bv 64 a) = false -> ~ in_img AB1v.tfibsegs a ->
  aview AB1v.tfibsegs (YA0n.w_H W) mem' a = aview AB1v.tfibsegs (YA0n.w_H W) mem a ->
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
  intros fx W mem mem' a Ha Hh Hni E.
  rewrite !(A.ProgWorld.aview_vis_mrd W _ a Hh) in E.
  assert (Hs : seg_rom rsegs (Z_to_bv 64 a) = None).
  { apply (A.MemNorm.seg_rom_unmapped rsegs). rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    exact (find_segment_none AB1v.tfibsegs a Hni). }
  unfold mrd in E. rewrite Hs in E.
  destruct (mem' (Z_to_bv 64 a)) as [b'|], (mem (Z_to_bv 64 a)) as [b0|]; cbn [option_map] in E;
    try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* Addresses at or above the allocation ceiling are outside the segments. *)
Lemma above_ceil_not_img : forall {rc : lib.Reusable.YM05.RunCeil} a, lib.Reusable.YM05.alloc_ceiling <= a ->
  ~ in_img AB1v.tfibsegs a.
Proof.
  intros rc a Ha Hi. pose proof (A.ProgWorld.pws_segs_low a Hi) as H.
  pose proof asan_consts as (C1 & _). unfold kLowMemEnd in H. lia.
Qed.

Section Glue.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.

Hypothesis LAWS : AR_laws AB1v.tfibsegs B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM0 : astack_malloc_realizes AB1v.tfibsegs B 0.

(* What a call keeps (acall_kept), after a stretch that wrote only a window of the machine stack. *)
Lemma acall_kept_after_munch : forall lyc Sc (W : YA0n.world AB1v.tfibsegs) (memc mem1 mem2 : word -> option byte)
    md (lo hi lo1 hi1 lo2 hi2 : Z) (E : Z -> Prop),
  AR AB1v.tfibsegs B lyc Sc W memc md ->
  lib.Reusable.YM05.alloc_ceiling <= lo -> lo2 <= lo -> hi <= hi2 -> lo2 <= lo1 -> hi1 <= hi2 ->
  munch [(lo, hi)] memc mem1 ->
  acall_kept AB1v.tfibsegs B lyc Sc W mem1 W mem2 lo1 hi1 E ->
  (forall a, lo2 <= a < hi2 -> apresent (YA0n.w_H W) mem2 a) ->
  acall_kept AB1v.tfibsegs B lyc Sc W memc W mem2 lo2 hi2 E.
Proof.
  intros lyc Sc W memc mem1 mem2 md lo hi lo1 hi1 lo2 hi2 E HAR Hc H1 H2 H3 H4 HM (K1 & K2 & K3 & K4 & K5 & K6) Hp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
            aview AB1v.tfibsegs (YA0n.w_H W) mem1 a = aview AB1v.tfibsegs (YA0n.w_H W) memc a).
  { intros a Ha Hn. apply aview_eq_of. unfold mrestrict. rewrite (HM (Z_to_bv 64 a)); [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    cbn [outside]. split; [lia | exact I]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn. rewrite (K1 a Ha ltac:(lia)). apply EQ; lia.
  - intros b0 m0 i Hin Hi HE. rewrite (K2 b0 m0 i Hin Hi HE).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 m0 HAR Hin) as (_ & Hb0 & Hb1 & _). apply EQ; lia.
  - intros a Hi Hs He. rewrite (K3 a Hi Hs He). pose proof (A.ProgWorld.pws_segs_low a Hi) as HL.
    unfold kLowMemEnd in HL. apply EQ; lia.
  - intros cid pos a Hin Hr HE. rewrite (K4 cid pos a Hin Hr HE).
    destruct (frames_bounds AB1v.tfibsegs B LAWS _ _ _ _ _ cid pos HAR Hin) as (F1 & F2 & F3).
    pose proof (fs_frame_bytes_nonneg cid) as Fn.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    + apply EQ; lia.
    + unfold YG0f.shadow_addr, YG0f.SHADOW_OFF in Hr. pose proof asan_consts as (D1 & _).
      apply EQ; Z.div_mod_to_equations; lia.
  - intros a Ha Hn Hpr. apply (K5 a Ha ltac:(lia)).
    destruct Hpr as [Hh (bb & Hb)]. split; [exact Hh|]. exists bb. rewrite (HM (Z_to_bv 64 a)); [exact Hb|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    cbn [outside]. split; [lia | exact I].
  - exact Hp.
Qed.

(* The callee-saved registers after the allocator returns: the values S1 left in them (the jal state). *)
Definition bmb_ret_regs (regs regs2 : bvmap 5 word) (A p b o : Z) : Prop :=
  rget regs2 2 = w64 A /\ rget regs2 3 = rget regs 3 /\ rget regs2 4 = rget regs 4 /\
  rget regs2 8 = rget regs 2 /\ rget regs2 9 = w64 A /\ rget regs2 18 = rget regs 18 /\
  rget regs2 19 = w64 o /\ rget regs2 20 = w64 p /\ rget regs2 21 = rget regs 21 /\
  rget regs2 22 = w64 b /\ rget regs2 23 = rget regs 23 /\ rget regs2 24 = rget regs 24 /\
  rget regs2 25 = w64 ASAN_K /\ rget regs2 26 = rget regs 26 /\ rget regs2 27 = rget regs 27.

Lemma pc_sm0 : pc_stack_malloc (as_code B) 0 = 0x3d5b8.
Proof. rewrite <- (palf_sm0 B TLF). vm_compute. reflexivity. Qed.

(* S1 and event 1: from the entry (cfg_at) to the return of __asan_stack_malloc_0 at 0x85bbc.  S1's Section facts
   at the normalized entry memory are premises here (the world supplies them below). *)
Lemma bmb_to_ret : wx_segs_nowrap AB1v.tfibsegs ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : YA0n.world AB1v.tfibsegs) memc mdc k
         (regs : bvmap 5 word) (p b o : Z) (row nb ob : list byte) (Q : YA0n.world AB1v.tfibsegs -> config -> Prop),
  ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  lib.Reusable.YK0s.ret_ok (rget regs 1) -> rget regs 3 = w64 (as_gp B) -> rget regs 4 = w64 (as_tp B) ->
  rget regs 10 = w64 p -> rget regs 11 = w64 b -> rget regs 12 = w64 o ->
  0 <= p < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK -> spZ regs <= sp0 ->
  count_cid 0 (frames Sc) < fs_frames 0 ->
  ro_agree rsegs memc ->
  stk rsegs (normalize rsegs memc) (spZ regs - 4272) (spZ regs) ->
  asan_cells (normalize rsegs memc) ->
  HIGHMEM_BEG <= spZ regs - 4272 -> spZ regs <= APPMEM_END ->
  addressable (normalize rsegs memc) (spZ regs - 4272) 4272 ->
  fp [0%nat] (normalize rsegs memc) (bv_unsigned (rget regs 4)) (ly_F lyc) (spZ regs - 4272) (spZ regs)
    (reac_box_model_block_W o (spZ regs)) (reac_box_model_block_D p o) ->
  (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs (normalize rsegs memc) p row /\
     (spZ regs <= p \/ p + 296 <= spZ regs - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
  (o <> 0 -> rw_cells rsegs (normalize rsegs memc) o [CB 32 ob] /\
     (spZ regs <= o \/ o + 32 <= spZ regs - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)) ->
  (o <> 0 -> addressable (normalize rsegs memc) o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o)) ->
  (forall S2 regs2 mem2 md2 pos,
     ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem2 md2 k ->
     frames S2 = (0, pos) :: frames Sc -> ~ In (0, pos) (frames Sc) -> ablocks B lyc S2 = ablocks B lyc Sc ->
     rget regs2 10 = w64 (frame_addr lyc 0 pos) ->
     bmb_ret_regs regs regs2 ((spZ regs - 160) / 32 * 32) p b o ->
     zero_shadow (aview AB1v.tfibsegs (YA0n.w_H W) mem2) SHADOW_OFF (frame_addr lyc 0 pos) (fs_frame_bytes 0) ->
     rdword (aview AB1v.tfibsegs (YA0n.w_H W) mem2) (frame_addr lyc 0 pos + fs_frame_bytes 0 - 8) =
       Some (flag_addr lyc 0 pos) ->
     acall_kept AB1v.tfibsegs B lyc Sc W memc W mem2 (spZ regs - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK)
       (spZ regs) (fun _ => False) ->
     (* the callee's own journal across the allocator call, from the memory at the call (which differs from the
        entry memory only inside the stack window) to the return memory *)
     (exists (mem1 : word -> option byte) (model1 : Model),
        munch [(spZ regs - 4272, spZ regs)] memc mem1 /\
        ajournal (SK := SK) AB1v.tfibsegs B ESTACK ((spZ regs - 160) / 32 * 32) [] lyc Sc W mem1 model1
          [(0, pos)] lyc S2 W mem2 md2 0) ->
     rw_cells rsegs mem2 (spZ regs + -104)
       (A.Prog.reac_box_model_block_base.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18)
          (rget regs 19) (rget regs 20) (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24)
          (rget regs 25) (rget regs 26) (rget regs 27)) ->
     YA0n.SRr AB1v.tfibsegs W (mkCfg (rmkst regs2 (w64 0x85bbc) mem2 (seg_rom AB1v.tfibsegs)) md2) Q) ->
  YA0n.SRr AB1v.tfibsegs W (cfg_at AB1v.tfibsegs 0x85b44 regs memc mdc) Q.
Proof.
  intros Hwx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b o row nb ob Q HJ Hra Hgp Htp Ha0 Ha1 Ha2
    Rp Rb Ro Hal Hlo Hhi Hroom Hro ST0 AC0 HHM HAE AW0 FP0 HP0 HO0 AO0 K.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5
    & HQT).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (ESTK : C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK = 4320) by reflexivity. rewrite ESTK in Hlo.
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  set (A := (spZ regs - 160) / 32 * 32) in *.
  assert (HA1 : spZ regs - 176 <= A <= spZ regs - 160 /\ A mod 32 = 0) by (subst A; Z.div_mod_to_equations; lia).
  assert (RWIN : rng (RNG_W (YA0n.w_H W)) (spZ regs - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K).
  { apply rng_of_visible. unfold REAC_BOX_MODEL_BLOCK_K. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  pose proof (rng_of_visible _ _ _ (img_vis_W W)) as RIMG.
  change (rget regs 10) with (reg_get regs 10) in Ha0.
  change (rget regs 11) with (reg_get regs 11) in Ha1.
  change (rget regs 12) with (reg_get regs 12) in Ha2.
  rewrite (cfg_at_MS AB1v.tfibsegs).
  apply (SRr_xregs_eqv AB1v.tfibsegs W (lib.Lib.Regs6ss.mkR_of regs) regs);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs))].
  unfold lib.Lib.Regs6ss.mkR_of. rewrite Ha0, Ha1, Ha2.
  refine (bmb_S1_SRr (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
            (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
            (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
            (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr memc p b o
            (ly_F lyc) ASAN_K A row nb ob W
            eq_refl eq_refl Hal ST0 AC0 HHM HAE AW0 FP0 RIMG RWIN Rp Rb Ro HP0 HO0 AO0 Hwx mdc
            (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 13) (reg_get regs 14)
            (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 28) (reg_get regs 29)
            (reg_get regs 30) (reg_get regs 31) Q Hro _).
  intros ms1 model1 Hrun1 (s1' & (a1' & a2' & m1 & HC & Es1) & HREL1 & HROS1) Hhid1 Hsame1.
  subst s1'.
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ HREL1) as [Ems1 HMR1].
  pose proof HC as (MU & WM & RM & MI & AC1 & SR1 & STc & FR & FP1).
  assert (HMU1 : munch [(spZ regs - 4272, spZ regs)] memc (ms_mem ms1))
    by exact (munch_rel rsegs _ memc (normalize rsegs memc) (ms_mem ms1) m1 (mem_rel_normalize rsegs memc Hro) HMR1
               HROS1 MU).
  assert (HJ1 : ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) model1 k).
  { lazymatch type of Hrun1 with fsteps _ _ ?ms0 _ =>
      refine (A.ProgWorld.ajournal_of_fsteps (SK := SK) B LAWS Hwx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W ms0 ms1
                mdc model1 k _ _ HJ Hrun1
                (fp_avoids_RNG_W _) HMU1 Hsame1 _) end.
    intros a Ha Hout. left. cbn [outside] in Hout. lia. }
  rewrite Ems1. clear Ems1.
  (* event 1: the allocator, cgif's astack_malloc_realizes SEGS B 0 (YC85.aj_stack_malloc_atS) *)
  lazymatch goal with |- YA0n.SRr _ _ {| cfg_ms := MS ?R _ _ _ _ ?mm _; cfg_model := _ |} _ =>
    set (regsT := R); set (mem1 := mm) in * end.
  rewrite <- pc_sm0.
  change (YA0n.SRr rsegs W (mkCfg (rmkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) 0)) mem1
            (lib.Reusable.YK11.seg_rom AB1v.tfibsegs)) model1) Q).
  change (rget regs 3) with (reg_get regs 3) in Hgp. change (rget regs 4) with (reg_get regs 4) in Htp.
  assert (EspT : spZ regsT = A).
  { unfold spZ. change (rget regsT 2) with (Z_to_bv 64 A). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  eapply SRr_bind.
  { refine (aj_stack_malloc_atS AB1v.tfibsegs B LAWS A.ProgWorld.pws_segs_low (pal_env B TL) ML SMP 0 ASM0
              ltac:(lia) W regsT mem1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc model1 k (A - sp0) (Z_to_bv 64 547772)
              HJ1 _ _ _ _ _ _ eq_refl _ Hroom).
    - rewrite EspT. lia.
    - Z.div_mod_to_equations. lia.
    - lia.
    - unfold ESTACK. lia.
    - exact Hgp.
    - exact Htp.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha02 & Eab & Hfrs2 & Hnin & Hnev2 &
    Hbb2 & Hz & Hflag & HK & HJin & (fS & ES2)).
  replace (sp0 + (A - sp0) - ESTACK) with (A - 4096) in HK by (unfold ESTACK; lia).
  replace (sp0 + (A - sp0)) with A in HK by lia.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  apply (K S2 regs2 mem2 md2 pos HJ2 Hfrs2 Hnin Eab Ha02).
  - unfold bmb_ret_regs.
    assert (P : forall r, acallee_saved r -> rget regs2 (Z_to_bv 5 r) = rget regsT (Z_to_bv 5 r)) by exact HP2.
    repeat split.
    all: lazymatch goal with
         | |- rget _ ?n = _ =>
             let z := eval vm_compute in (bv_unsigned n) in
             transitivity (rget regsT (Z_to_bv 5 z)); [exact (P z ltac:(unfold acallee_saved; lia)) | reflexivity]
         end.
  - exact Hz.
  - exact Hflag.
  - rewrite ESTK.
    apply (acall_kept_after_munch lyc Sc W memc mem1 mem2 mdc (spZ regs - 4272) (spZ regs) (A - 4096) A
             (spZ regs - 4320) (spZ regs) (fun _ => False) HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             HMU1 HK).
    intros a Ha. apply Hpres2. lia.
  - exists mem1, model1. split; [exact HMU1|].
    replace (sp0 + (A - sp0)) with A in HJin by lia. exact HJin.
  - apply (rw_cells_agree mem1).
    + exact (rw_cells_of_rel _ _ _ _ HMR1 FR).
    + intros i Hi. cbn [cells_size csize Nat.add A.Prog.reac_box_model_block_base.SAVES] in Hi.
      pose proof (proj1 (Hpres2 (spZ regs + -104 + i) ltac:(lia))) as Hv.
      apply (raw_of_aview W mem1 mem2); [lia | exact Hv | apply above_ceil_not_img; lia |].
      pose proof HK as (K1 & _). apply K1; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The Section facts of a stretch at the normalized memory of a cut, from the cut's world.  The runtime facts
   (ro_agree, asan_cells) come from a lemma outside this file (a Theorem Labs lane's bmb_rt_facts_on); the shadow premise is
   the narrowed region (reac_box_model_block_glue_sr.v); no universal shadow fact is taken here.  Every other world
   fact is a proved lemma. *)
Hypothesis TSY : A.AF0m.CtrlTSyms B.                  (* the bundle's const table is ctrl's [core composition] *)

Lemma win_facts : forall ly S (W : YA0n.world AB1v.tfibsegs) m md lo hi,
  AR AB1v.tfibsegs B ly S W m md -> ro_agree rsegs m ->
  ly_stk_lo ly <= lo -> lo <= hi -> hi <= ly_stk_hi ly ->
  (forall a, lo <= a < hi -> apresent (YA0n.w_H W) m a) ->
  stk rsegs (normalize rsegs m) lo hi /\ addressable (normalize rsegs m) lo (hi - lo) /\
  HIGHMEM_BEG <= lo /\ hi <= APPMEM_END /\ lib.Reusable.YM05.alloc_ceiling <= lo.
Proof.
  intros ly S W m md lo hi HAR Hro Hlo Hle Hhi Hp.
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_stk_ceil _ LO) as SC. pose proof (lo_top _ LO) as (_ & _ & _ & T4 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold ASAN_CEIL in SC.
  split; [|split; [|split; [|split]]].
  - apply stk_normalize_ro; [exact Hro | unfold ImgBounds.IMG_HI; lia |].
    apply (A.ProgWorld_Fs.pw_stk_of_present W); [lia | unfold kHighMemEnd in T4; lia | exact Hp].
  - apply addressable_normalize; [exact Hro|].
    exact (A.ProgWorldShadow.ctl_stack_shadow_of_AR B LAWS ly S W m md lo (hi - lo) HAR Hlo ltac:(lia) ltac:(lia)).
  - unfold HIGHMEM_BEG. lia.
  - unfold APPMEM_END. unfold kHighMemEnd in T4. lia.
  - lia.
Qed.

(* The side-stack premise fp moved to the normalized memory (the side stack is above the image). *)
Lemma asan_tls_cells_normalize : forall m TP DT TS C T DB k, ro_agree rsegs m ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells (normalize rsegs m) TP DT TS C T DB k.
Proof.
  intros m TP DT TS C T DB k Hro H. unfold asan_tls_cells in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15 & H16 &
                 H17 & H18 & H19).
  repeat (split; [first [apply bytes_at_normalize; [exact Hro | assumption] | assumption] |]).
  split; [exists tb, te; apply bytes_at_normalize; [exact Hro | assumption]|].
  repeat (split; [first [apply bytes_at_normalize; [exact Hro | assumption] | assumption] |]).
  apply bytes_at_normalize; [exact Hro | assumption].
Qed.

Lemma fp_normalize : forall cs m TP FS lo hi Wr D, ro_agree rsegs m ->
  fp cs m TP FS lo hi Wr D -> fp cs (normalize rsegs m) TP FS lo hi Wr D.
Proof.
  intros cs m TP FS lo hi Wr D Hro (DT & TS & C & T & DB & k & HT & HTP & HPl & H88 & H96 & HC & Hlo & Happ & HdW & HdD).
  pose proof HPl as (P1 & P2 & P3 & P4 & P5).
  exists DT, TS, C, T, DB, k.
  split; [exact (asan_tls_cells_normalize _ _ _ _ _ _ _ _ Hro HT)|].
  split; [apply bytes_at_normalize; assumption|].
  split.
  { split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    apply stk_normalize_ro; [exact Hro | unfold ImgBounds.IMG_HI; unfold ASAN_GT in P3; lia | exact P5]. }
  split; [apply bytes_at_normalize; assumption|].
  split; [apply bytes_at_normalize; assumption|].
  split; [|exact (conj Hlo (conj Happ (conj HdW HdD)))].
  eapply Forall_impl; [|exact HC]. intros c (Hc6 & h & flags & Hh & Hf & Hl & Hb).
  split; [exact Hc6|]. exists h, flags.
  split; [apply bytes_at_normalize; assumption|]. split; [apply bytes_at_normalize; assumption|]. split; assumption.
Qed.

(* FP0 at the normalized memory of a cut: ctl_fp_of_AR (ProgWorld_Fs.v, proved) with the disjointness facts of this
   function's write ranges W and data ranges D: the window is in the stack (above the ceiling, so above every
   allocator extent), p in the image (below the side stack), o in a live frame of class >= 1 (inside the side stack,
   past the class-0 area, apart from the other allocator extents by layout_ok's lo_disj) or in the stack. *)
Lemma fp0_facts : forall ly S (W : YA0n.world AB1v.tfibsegs) m md (sp p o : Z),
  AR AB1v.tfibsegs B ly S W m md -> ro_agree rsegs m ->
  lib.Reusable.YM05.alloc_ceiling <= sp - 4320 -> sp <= APPMEM_END ->
  (p <> 0 -> 0 <= p /\ p + 296 <= ASAN_GT) ->
  (o <> 0 -> 0 <= o /\
     ((exists cid pos, In (cid, pos) (frames S) /\ cid <> 0 /\
         forall x, o <= x < o + 32 -> in_zr x (frame_rng ly (cid, pos))) \/
      (lib.Reusable.YM05.alloc_ceiling <= o /\ o + 32 <= APPMEM_END))) ->
  fp [0%nat] (normalize rsegs m) RT_TP (ly_F ly) (sp - 4272) sp
    (reac_box_model_block_W o sp) (reac_box_model_block_D p o).
Proof.
  intros ly S W m md sp p o HAR Hro Hc Hsp Hp Ho.
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (A.ProgWorld_Fs.pw_F_above B ly S W m md HAR) as HGT. unfold ASAN_GT in HGT.
  assert (EXT : forall e, In e (owned_extents ly) -> 4096 <= fst e /\ fst e + snd e <= lib.Reusable.YM05.alloc_ceiling).
  { intros e He. pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e He) as [E0 E1].
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in E1. lia. }
  destruct (EXT (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as [F0 F1].
  destruct (EXT (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as [T0 T1].
  destruct (EXT (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto)) as [CC0 CC1].
  destruct (EXT (ly_D ly, 4096) ltac:(unfold owned_extents; cbn; tauto)) as [D0 D1].
  cbn [fst snd] in F0, F1, T0, T1, CC0, CC1, D0, D1.
  pose proof (lo_disj _ LO) as LD.
  assert (DTF : zdisjoint (ly_T ly, kThreadObjSize) (ly_F ly, kFakeStackSize))
    by exact (pairwise_In2 zdisjoint _ _ _ [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv)] []
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256); (ly_D ly, 4096);
                 (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  assert (DFC : zdisjoint (ly_F ly, kFakeStackSize) (ly_C ly, 256))
    by exact (pairwise_In2 zdisjoint _ _ _
                [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize)]
                [(ly_D ly, 4096); (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  assert (DFD : zdisjoint (ly_F ly, kFakeStackSize) (ly_D ly, 4096))
    by exact (pairwise_In2 zdisjoint _ _ _
                [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256)]
                [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  unfold zdisjoint in DTF, DFC, DFD. cbn [fst snd] in DTF, DFC, DFD.
  assert (Etsd : ly_tsd ly = 0x5fcbb8) by (rewrite (am_tsd _ _ _ _ M), (A.AF0m.ts_tsd B TSY); reflexivity).
  assert (ET : bv_unsigned (Z_to_bv 64 (ly_T ly)) = ly_T ly)
    by (apply A.ProgWorld_Fs.pw_u64; unfold kThreadObjSize in T1; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ly_D ly)) = ly_D ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 (ly_C ly)) = ly_C ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (ETS : bv_unsigned (Z_to_bv 64 0x5fcbb8) = 0x5fcbb8) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (EDT : bv_unsigned (Z_to_bv 64 (RT_TP + 32)) = RT_TP + 32) by (apply A.ProgWorld_Fs.pw_u64; unfold RT_TP; lia).
  (* o's range, by case *)
  assert (OR : o <> 0 -> 0 <= o /\
                 ((ly_F ly + kFakeFramesOff + 2 ^ 20 <= o /\ o + 32 <= ly_F ly + kFakeStackSize) \/
                  (lib.Reusable.YM05.alloc_ceiling <= o /\ o + 32 <= APPMEM_END))).
  { intros Ho0. destruct (Ho Ho0) as [Hog [(cid & pos & Hin & Hcid & Hx) | Hst]]; split; [exact Hog| |exact Hog|right; exact Hst].
    left. destruct (YG0s.frame_facts B ly S _ cid pos M Hin) as (Q1 & Q2 & _ & _ & _ & Q6 & Q7 & _).
    pose proof (Hx o ltac:(lia)) as X0. pose proof (Hx (o + 31) ltac:(lia)) as X1.
    unfold in_zr, frame_rng, frame_addr in X0, X1. cbn [fst snd] in X0, X1.
    assert (cid * 2 ^ 20 >= 2 ^ 20) by nia. lia. }
  apply fp_normalize; [exact Hro|].
  apply (A.ProgWorld_Fs.ctl_fp_of_AR B TSY LAWS ly S W m md [0%nat] (sp - 4272) sp _ _ HAR).
  - repeat constructor.
  - unfold FS_SIZE, kFakeStackSize in *. lia.
  - intros a Ha. unfold app_mem, HIGHMEM_BEG. right. lia.
  - unfold fp_dj, reac_box_model_block_W, fp_tls, REAC_BOX_MODEL_BLOCK_K.
    rewrite Etsd. rewrite ?ET, ?ED, ?EC, ?ETS, ?EDT.
    unfold TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF,
      RT_TP.
    assert (EF00 : fs_frame (ly_F ly) 0%nat 0 = ly_F ly + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    rewrite EF00. unfold kFakeFramesOff, kFakeStackSize, kThreadObjSize in *.
    destruct (o =? 0) eqn:Eo; [apply Z.eqb_eq in Eo | apply Z.eqb_neq in Eo];
      cbn [app]; repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd]; try lia.
    all: destruct (OR Eo) as [Og [Of | Os]]; lia.
  - unfold fp_dj, reac_box_model_block_D, fp_w, fp_w1. cbn [flat_map app].
    unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B. cbn [Z.of_nat].
    unfold shadow_addr, ASAN_K, kFakeFramesOff, kFakeStackSize in *. unfold ASAN_GT in Hp.
    destruct (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize)
                ltac:(unfold owned_extents; cbn; tauto)) as [FA0 FA1].
    cbn [fst snd] in FA1. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in FA1.
    destruct (p =? 0) eqn:Ep; [apply Z.eqb_eq in Ep | apply Z.eqb_neq in Ep];
      destruct (o =? 0) eqn:Eo; [apply Z.eqb_eq in Eo | apply Z.eqb_neq in Eo | apply Z.eqb_eq in Eo |
                                 apply Z.eqb_neq in Eo];
      cbn [app]; repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd].
    all: try (destruct (Hp Ep) as [Pg Pb]).
    all: try (destruct (OR Eo) as [Og [Of | Os]]).
    all: Z.div_mod_to_equations; lia.
Qed.


(* The thread cells at an AR state: ProgWorld_Fs.ctl_fp_of_AR's construction (a Theorem Labs lane, 7f07ac65e7b, lines 389-438),
   one row of the bundle's const table per cell (A/AF0m.v rows :24-27, :89-90, :100-102, :111, :116-117, :134, :136,
   :173, :185; each line is the same at the record e56483f863b). *)
Ltac bmb_mem := repeat (first [apply in_eq | apply in_cons]).
Ltac bmb_sym := apply A.ProgWorld_Fs.pw_in_sym; unfold A.AF0m.Tfib_const_sym; bmb_mem.
Ltac bmb_abs := apply A.ProgWorld_Fs.pw_in_abs; unfold A.AF0m.Tfib_const_abs; bmb_mem.
Ltac bmb_num := cbn [aeval];
  unfold TLS_INDEX, DTLS_TPOFF, REAL_TLS_GET_ADDR, MUSL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF,
    GOT_VERBOSITY, VERBOSITY, RT_TP; lia.

Lemma tls_cells_AR : forall ly S (W : YA0n.world AB1v.tfibsegs) m md,
  AR AB1v.tfibsegs B ly S W m md ->
  asan_tls_cells m RT_TP (Z_to_bv 64 (RT_TP + 32)) (Z_to_bv 64 (ly_tsd ly)) (Z_to_bv 64 (ly_C ly))
    (Z_to_bv 64 (ly_T ly)) (Z_to_bv 64 (ly_D ly)) 0.
Proof.
  intros ly S W m md HAR.
  pose proof HAR as (M & L & _).
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (am_tsd _ _ _ _ M) as Htsd.
  rewrite (A.AF0m.ts_tsd B TSY) in Htsd. unfold A.AF0m.TFIB_TSD in Htsd.
  assert (Etp : as_tp B = 0x5db810) by (rewrite (A.AF0m.ts_tp B TSY); reflexivity).
  assert (HT : In (ly_T ly, kThreadObjSize) (owned_extents ly)) by (unfold owned_extents; bmb_mem).
  assert (HC : In (ly_C ly, 256) (owned_extents ly)) by (unfold owned_extents; bmb_mem).
  assert (HD : In (ly_D ly, 4096) (owned_extents ly)) by (unfold owned_extents; bmb_mem).
  destruct (A.ProgWorld_Fs.pw_owned_range ly _ LO HT) as [RT0 RT1].
  destruct (A.ProgWorld_Fs.pw_owned_range ly _ LO HC) as [RC0 RC1].
  destruct (A.ProgWorld_Fs.pw_owned_range ly _ LO HD) as [RD0 RD1].
  cbn [fst snd] in RT0, RT1, RC0, RC1, RD0, RD1. unfold kThreadObjSize in RT1.
  unfold asan_tls_cells.
  rewrite (A.ProgWorld_Fs.pw_u64 (RT_TP + 32)) by (unfold RT_TP; lia).
  rewrite (A.ProgWorld_Fs.pw_u64 (ly_tsd ly)), (A.ProgWorld_Fs.pw_u64 (ly_C ly)),
    (A.ProgWorld_Fs.pw_u64 (ly_T ly)), (A.ProgWorld_Fs.pw_u64 (ly_D ly)) by lia.
  repeat (match goal with |- _ /\ _ => split end).
  - apply (proj2 (bytes_at_app _ _ _ _ _)). rewrite length_le8. split.
    + apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ANum 0xa07b0) (ANum 1)); [exact HAR | bmb_abs | bmb_num ..].
    + replace (Z_to_bv 64 (-2048)) with (Z_to_bv 64 0xfffffffffffff800) by (apply bv_eq; vm_compute; reflexivity).
      apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ANum 0xa07b8) (ANum 0xfffffffffffff800));
        [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ANum 0xa1870) (ANum 0x98800)); [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ANum 0x5db808) (ANum 0x5db830)); [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ANum 0x5db838) (ANum 0x5dc010)); [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_z1_row B TSY ly S W m md (ANum 0xa80e0) _ 1); [exact HAR | bmb_abs | bmb_num ..].
  - lia.
  - lia.
  - apply (A.ProgWorld_Fs.pw_z4_row B TSY ly S W m md (ANum 0xa80e4) _ 0); [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ATp (-88)) (ATsd 0)); [exact HAR | bmb_sym | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ATsd 0) (AC 0)); [exact HAR | bmb_sym | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (AC 152) (AT 0)); [exact HAR | bmb_sym | bmb_num ..].
  - exists (Z_to_bv 64 0x5dbf48), (Z_to_bv 64 0x5dc024).
    apply (proj2 (bytes_at_app _ _ _ _ _)). rewrite length_le8. split.
    + apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (AT 48) (ANum 0x5dbf48)); [exact HAR | bmb_sym | bmb_num ..].
    + apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (AT 56) (ANum 0x5dc024)); [exact HAR | bmb_sym | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ANum 0x9fac0) (ANum 0x13a3a8)); [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_z1_row B TSY ly S W m md (ANum 0x13a431) _ 1); [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ANum 0x9fb20) (ANum 0x138318)); [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_z4_row B TSY ly S W m md (ANum 0x138318) _ 0); [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ANum 0xa07c0) (ANum 8)); [exact HAR | bmb_abs | bmb_num ..].
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (ATp 8) (AD 0)); [exact HAR | bmb_sym | bmb_num ..].
  - lia.
  - apply (A.ProgWorld_Fs.pw_c8_row B TSY ly S W m md (AD 24) (ATp 0)); [exact HAR | bmb_sym | bmb_num ..].
Qed.

(* TLS0 of every stretch at a cut's normalized memory: any thread cells there are AR's (RcAsanFPLib.fl_tls_same with
   no write), and those lie apart from the class-0 side-stack bytes and from the shadow of a window in high memory. *)
Lemma tls0_facts : forall ly S (W : YA0n.world AB1v.tfibsegs) m md lo hi,
  AR AB1v.tfibsegs B ly S W m md -> ro_agree rsegs m ->
  lib.Reusable.YM05.alloc_ceiling <= lo -> lo <= hi -> hi <= APPMEM_END ->
  reac_box_model_block_tls (normalize rsegs m) RT_TP (ly_F ly) lo hi.
Proof.
  intros ly S W m md lo hi HAR Hro Hc Hle Hhi DT TS C T DB k HT.
  pose proof (asan_tls_cells_normalize _ _ _ _ _ _ _ _ Hro (tls_cells_AR ly S W m md HAR)) as X1.
  destruct (A.Prog.RcAsanFPLib.fl_tls_same _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HT (fun x _ => eq_refl)
              ltac:(apply Forall_forall; intros d _ x _; exact I)) as (<- & <- & <- & <- & <- & <-).
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (A.ProgWorld_Fs.pw_F_above B ly S W m md HAR) as HGT. unfold ASAN_GT in HGT.
  pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
  assert (EXT : forall e, In e (owned_extents ly) -> 4096 <= fst e /\
            (fst e + snd e <= 0x7fff7000 \/ (0x10007fff8000 <= fst e /\ fst e + snd e <= 0x7fffff800000))).
  { intros e He. pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e He) as [E0 E1].
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in E1. split; [exact E0|]. lia. }
  destruct (EXT (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as [F0 F1].
  destruct (EXT (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as [T0 T1].
  destruct (EXT (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto)) as [CC0 CC1].
  destruct (EXT (ly_D ly, 4096) ltac:(unfold owned_extents; cbn; tauto)) as [D0 D1].
  cbn [fst snd] in F0, F1, T0, T1, CC0, CC1, D0, D1.
  pose proof (lo_disj _ LO) as LD.
  assert (DTF : zdisjoint (ly_T ly, kThreadObjSize) (ly_F ly, kFakeStackSize))
    by exact (pairwise_In2 zdisjoint _ _ _ [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv)] []
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256); (ly_D ly, 4096);
                 (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  assert (DFC : zdisjoint (ly_F ly, kFakeStackSize) (ly_C ly, 256))
    by exact (pairwise_In2 zdisjoint _ _ _
                [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize)]
                [(ly_D ly, 4096); (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  assert (DFD : zdisjoint (ly_F ly, kFakeStackSize) (ly_D ly, 4096))
    by exact (pairwise_In2 zdisjoint _ _ _
                [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256)]
                [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  unfold zdisjoint in DTF, DFC, DFD. cbn [fst snd] in DTF, DFC, DFD.
  assert (Etsd : ly_tsd ly = 0x5fcbb8) by (rewrite (am_tsd _ _ _ _ M), (A.AF0m.ts_tsd B TSY); reflexivity).
  unfold kThreadObjSize, kFakeStackSize in *.
  assert (ET : bv_unsigned (Z_to_bv 64 (ly_T ly)) = ly_T ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ly_D ly)) = ly_D ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 (ly_C ly)) = ly_C ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (ETS : bv_unsigned (Z_to_bv 64 (ly_tsd ly)) = ly_tsd ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (EDT : bv_unsigned (Z_to_bv 64 (RT_TP + 32)) = RT_TP + 32) by (apply A.ProgWorld_Fs.pw_u64; unfold RT_TP; lia).
  unfold fp_dj, fp_tls, fp_w, fp_w1. cbn [flat_map app].
  rewrite ET, ED, EC, ETS, EDT, Etsd.
  unfold TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF, RT_TP.
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B. cbn [Z.of_nat].
  unfold shadow_addr, ASAN_K. unfold APPMEM_END in Hhi.
  repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd].
  all: Z.div_mod_to_equations; lia.
Qed.

(* The class-0 frame facts S2 (main_mid_F) takes at the return memory of __asan_stack_malloc_0, from AR at the new
   state and two pieces of the allocator's post (zero_shadow, the flag back-pointer).  The proof follows
   A/ProgWorldAstack.v ctl_fs_of_astack (a Theorem Labs lane, d447ec8f286) lines 229-311 for cid = 0, L = 64, without its
   ecall_pre / frame-condition premises, which only its last conjunct (the caller's stack) needs. *)
Lemma bmb_frame_facts : forall ly S' (W : YA0n.world AB1v.tfibsegs) mem' md' pos l,
  AR AB1v.tfibsegs B ly S' W mem' md' -> frames S' = (0, pos) :: l ->
  zero_shadow (aview AB1v.tfibsegs (YA0n.w_H W) mem') SHADOW_OFF (frame_addr ly 0 pos) (fs_frame_bytes 0) ->
  rdword (aview AB1v.tfibsegs (YA0n.w_H W) mem') (frame_addr ly 0 pos + fs_frame_bytes 0 - 8) =
    Some (flag_addr ly 0 pos) ->
  let FS := ly_F ly in
  let fr := fs_frame FS 0%nat pos in
  0 <= pos < fs_M 0%nat /\ frame_addr ly 0 pos = fr /\ flag_addr ly 0 pos = fs_flag FS 0 pos /\
  bytes_at rsegs mem' (fs_flag FS 0 pos) [Z_to_bv 8 1] /\
  bytes_at rsegs mem' (fr + 56) (le8 (Z_to_bv 64 (fs_flag FS 0 pos))) /\
  bytes_at rsegs mem' (shadow_addr fr) (repeat (Z_to_bv 8 0) 8) /\
  addressable mem' fr 64 /\ stk rsegs mem' fr (fr + 64) /\
  (forall a, fr <= a < fr + 64 -> apresent (YA0n.w_H W) mem' a) /\
  fr mod 64 = 0 /\ FS <= fr /\ fr + 64 <= FS + FS_SIZE /\ ASAN_GT <= fr.
Proof.
  intros ly S' W mem' md' pos l HAR' Hfr' Hzs Hrdw. cbv zeta.
  assert (Hin' : In (0, pos) (frames S')) by (rewrite Hfr'; left; reflexivity).
  pose proof HAR' as (M' & L' & _).
  destruct (YG0s.frame_facts B ly S' _ 0 pos M' Hin')
    as (Hc10 & Hpos & HFapp & _ & HFal & Hfo1 & Hfo2 & Hfo64 & Hfb64 & Hfbm & Hflb).
  destruct (A.ProgWorld.ctl_fs_geom (ly_F ly) 0 pos ltac:(lia)) as (G1 & G2 & G3 & G4 & _ & G6 & _).
  change (Z.to_nat 0) with 0%nat in G1, G2, G3, G4.
  assert (EB0 : fs_B 0%nat = 64) by reflexivity.
  assert (Efa : frame_addr ly 0 pos = fs_frame (ly_F ly) 0%nat pos) by (rewrite G3; reflexivity).
  assert (Efl : flag_addr ly 0 pos = fs_flag (ly_F ly) 0%nat pos) by (rewrite G4; reflexivity).
  assert (En : fs_frame_bytes 0 = 64) by reflexivity.
  rewrite En in Hzs, Hrdw, Hfbm, Hfb64. rewrite Efa in Hzs, Hrdw. rewrite Efl in Hrdw.
  rewrite G1, G6.
  destruct (A.ProgWorldAstack.pwfs_F_range ly HFapp) as [HF0 HF1].
  assert (Hfa64 : fs_frame (ly_F ly) 0%nat pos mod 64 = 0).
  { rewrite G3. unfold page_aligned in HFal.
    pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)) as D1.
    pose proof (Z.div_mod (fs_frame_off 0 pos) 64 ltac:(lia)) as D2.
    rewrite HFal in D1. rewrite Hfo64 in D2.
    replace (ly_F ly + fs_frame_off 0 pos) with ((64 * (ly_F ly / 4096) + fs_frame_off 0 pos / 64) * 64) by lia.
    apply Z.mod_mul. lia. }
  pose proof (A.ProgWorldAstack.pwfs_mod8 _ Hfa64) as Hfa8.
  assert (Efr : fs_frame (ly_F ly) 0%nat pos = ly_F ly + fs_frame_off 0 pos) by exact G3.
  assert (Eflv : fs_flag (ly_F ly) 0%nat pos = ly_F ly + fs_flag_off 0 pos) by exact G4.
  replace (2 ^ 20) with 1048576 in Hfo1 by reflexivity.
  unfold kFakeStackSize, kFakeFlagsOff, kFakeFramesOff in *.
  set (fa := fs_frame (ly_F ly) 0%nat pos) in *.
  set (fl := fs_flag (ly_F ly) 0%nat pos) in *.
  assert (Hsh : bytes_at rsegs mem' (shadow_addr fa) (repeat (Z_to_bv 8 0) 8)).
  { assert (Hd1 : fa / 8 <= fa) by (apply Z.div_le_upper_bound; lia).
    assert (Hd3 : 0 <= fa / 8) by (apply Z.div_pos; lia).
    apply (A.ProgWorldAstack.pwfs_bytes_of_view W).
    - unfold shadow_addr, ASAN_K. lia.
    - rewrite repeat_length. unfold shadow_addr, ASAN_K. cbn [Z.of_nat]. lia.
    - intros i Hi. rewrite repeat_length in Hi. exists (Z_to_bv 8 0).
      split; [apply nth_error_repeat; exact Hi|].
      replace (shadow_addr fa) with (YG0v.shadow_of_addr SHADOW_OFF fa)
        by (unfold shadow_addr, ASAN_K, YG0v.shadow_of_addr, SHADOW_OFF; lia).
      rewrite (Hzs (Z.of_nat i) ltac:(Z.div_mod_to_equations; lia)). rewrite A.ProgWorldAstack.pwfs_bv8. reflexivity. }
  destruct (al_frames _ _ LAWS ly S' W mem' md' 0 pos HAR' Hin') as (_ & _ & Hfb & _).
  rewrite ?En, ?Efa in Hfb.
  split; [exact Hpos|].
  split; [exact Efa|].
  split; [exact Efl|].
  split.
  { assert (Hfl : aview AB1v.tfibsegs (YA0n.w_H W) mem' fl = Some 1).
    { pose proof (am_flags _ _ _ _ M' 0 pos ltac:(lia) Hpos) as Hf.
      rewrite Hfr' in Hf. cbn [mem_pos] in Hf. rewrite !Z.eqb_refl in Hf. rewrite <- Efl. exact Hf. }
    apply (A.ProgWorldAstack.pwfs_byte_of_view W mem' _ 1 Hfl); lia. }
  split.
  { replace (fa + 56) with (fa + 64 - 8) by lia.
    exact (A.ProgWorldAstack.pwfs_rdword_bytes W mem' _ _ Hrdw ltac:(lia) ltac:(lia)). }
  split; [exact Hsh|].
  split.
  { split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
    intros i Hi. split; [apply (A.ProgWorldAstack.pwfs_app_mem_F ly _ HFapp); unfold kFakeStackSize; lia|].
    exists (Z_to_bv 8 0). split; [|left; vm_compute; reflexivity].
    pose proof Hsh as (_ & _ & Hs).
    assert (Hi8 : (Z.to_nat (i / 8) < length (repeat (Z_to_bv 8 0) 8))%nat).
    { rewrite repeat_length. assert (0 <= i / 8 < 8) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      lia. }
    replace (shadow_addr (fa + i)) with (shadow_addr fa + Z.of_nat (Z.to_nat (i / 8))).
    - rewrite (Hs _ Hi8). apply nth_error_repeat. rewrite repeat_length in Hi8. exact Hi8.
    - rewrite Z2Nat.id by (apply Z.div_pos; lia). unfold shadow_addr.
      pose proof (Z.div_mod fa 8 ltac:(lia)) as D. rewrite Hfa8 in D.
      replace (fa + i) with (i + (fa / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
  split; [apply (A.ProgWorldAstack.pwfs_stk_of_present W); [lia | lia | intros a Ha; exact (proj1 (Hfb a Ha))]|].
  split; [intros a Ha; exact (proj1 (Hfb a Ha))|].
  split; [exact Hfa64|].
  split; [lia|].
  split; [unfold FS_SIZE; lia|].
  pose proof (A.ProgWorldAstack.pwfs_F_above B ly S' W mem' md' HAR'). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The data the stretches read, at the allocator's return memory, from the frozen spec's premises at the entry memory
   and what the call keeps (acall_kept). *)
Lemma in_img_rsegs : forall a, 0x10000 <= a < 0x5fe000 -> in_img AB1v.tfibsegs a.
Proof.
  intros a Ha. pose proof A.ProgBridge.rsegs_spans as E.
  assert (Hm : exists b sz, In (b, sz) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs) /\
                            b <= a < b + sz).
  { rewrite E.
    destruct (Z_lt_le_dec a 0x30000); [exists 0x10000, 0x20000; split; [left; reflexivity | lia]|].
    destruct (Z_lt_le_dec a 0x9e000); [exists 0x30000, 0x6e000; split; [right; left; reflexivity | lia]|].
    destruct (Z_lt_le_dec a 0xa1000); [exists 0x9e000, 0x3000; split; [right; right; left; reflexivity | lia]|].
    exists 0xa1000, 0x55d000; split; [right; right; right; left; reflexivity | lia]. }
  destruct Hm as (b & sz & Hin & Hr). apply in_map_iff in Hin as (sg & Es & Hsg). injection Es as Eb Esz.
  exists sg. split; [exact Hsg | lia].
Qed.

Lemma aview_of_garr8 : forall (H : word -> bool) m a zs j,
  garr8 AB1v.tfibsegs (mrestrict H m) a zs -> (j < length zs)%nat ->
  aview AB1v.tfibsegs H m (a + Z.of_nat j) = Some (nth j zs 0).
Proof.
  intros H m a zs j G Hj. destruct (G j Hj) as [Hv Hr].
  pose proof (Hv 0%nat ltac:(lia)) as E. change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E.
  unfold aview. rewrite E. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  try unfold YO0f.le_byte; try unfold YG0f.le_byte.
  replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
  rewrite Z.shiftr_0_r. rewrite !(Z.mod_small (nth j zs 0)) by lia. reflexivity.
Qed.

Lemma bytes_at_of_garr8 : forall (W : YA0n.world AB1v.tfibsegs) memc mem2 a (bs : list byte),
  garr8 AB1v.tfibsegs (mrestrict (YA0n.w_H W) memc) a (C_reac_box_model_block.bmb_z bs) ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     aview AB1v.tfibsegs (YA0n.w_H W) mem2 (a + i) = aview AB1v.tfibsegs (YA0n.w_H W) memc (a + i)) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs mem2 a bs.
Proof.
  intros W memc mem2 a bs G K Ha Hb.
  apply (A.ProgWorldAstack.pwfs_bytes_of_view W); [exact Ha | exact Hb |].
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:En; [|apply nth_error_None in En; lia].
  exists b. split; [reflexivity|].
  rewrite (K (Z.of_nat i) ltac:(lia)).
  assert (Hi' : (i < length (C_reac_box_model_block.bmb_z bs))%nat)
    by (unfold C_reac_box_model_block.bmb_z; rewrite length_map; exact Hi).
  rewrite (aview_of_garr8 _ _ _ _ i G Hi'). f_equal.
  assert (E2 : nth_error (C_reac_box_model_block.bmb_z bs) i = Some (bv_unsigned b))
    by (unfold C_reac_box_model_block.bmb_z; rewrite nth_error_map, En; reflexivity).
  exact (nth_error_nth _ _ 0 E2).
Qed.

(* An image range the spec reads (not owned-static, not errno) has the same view after the call. *)
Lemma img_kept : forall lyc Sc (W : YA0n.world AB1v.tfibsegs) memc mem2 slo shi (E : Z -> Prop) a n,
  acall_kept AB1v.tfibsegs B lyc Sc W memc W mem2 slo shi E ->
  0x10000 <= a -> a + n <= 0x5fe000 ->
  (forall x, a <= x < a + n -> ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  forall i, 0 <= i < n -> aview AB1v.tfibsegs (YA0n.w_H W) mem2 (a + i) = aview AB1v.tfibsegs (YA0n.w_H W) memc (a + i).
Proof.
  intros lyc Sc W memc mem2 slo shi E a n (_ & _ & K3 & _) Ha Hn Hx i Hi.
  destruct (Hx (a + i) ltac:(lia)) as [H1 H2]. apply K3; [apply in_img_rsegs; lia | exact H1 | exact H2].
Qed.

(* HP and HN of the stretches at the normalized return memory. *)
Lemma bmb_bytes_norm : forall lyc Sc (W : YA0n.world AB1v.tfibsegs) memc mem2 slo shi (E : Z -> Prop) a (bs : list byte),
  acall_kept AB1v.tfibsegs B lyc Sc W memc W mem2 slo shi E -> ro_agree rsegs mem2 ->
  garr8 AB1v.tfibsegs (mrestrict (YA0n.w_H W) memc) a (C_reac_box_model_block.bmb_z bs) ->
  0x10000 <= a -> a + Z.of_nat (length bs) <= 0x5fe000 ->
  (forall x, a <= x < a + Z.of_nat (length bs) ->
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  bytes_at rsegs (normalize rsegs mem2) a bs.
Proof.
  intros lyc Sc W memc mem2 slo shi E a bs HK Hro G Ha Hb Hx.
  apply bytes_at_normalize; [exact Hro|].
  apply (bytes_at_of_garr8 W memc mem2 a bs G); [| lia | lia].
  exact (img_kept lyc Sc W memc mem2 slo shi E a _ HK Ha Hb Hx).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The caller's kept bytes at the return (tcj_kept), from what the allocator call kept (acall_kept, entry -> its
   return) and the writes of the rest of the run (munch WR, its return -> the function's return). *)
Lemma aview_munch_out : forall (W : YA0n.world AB1v.tfibsegs) (WR : list ivl) (m m' : word -> option byte) a,
  munch WR m m' -> 0 <= a < 2 ^ 64 -> outside WR a ->
  aview AB1v.tfibsegs (YA0n.w_H W) m' a = aview AB1v.tfibsegs (YA0n.w_H W) m a.
Proof.
  intros W WR m m' a HM Ha Ho. apply aview_eq_of. unfold mrestrict. rewrite (HM (Z_to_bv 64 a)); [reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  exact Ho.
Qed.

Lemma present_munch_out : forall (H : word -> bool) (WR : list ivl) (m m' : word -> option byte) a,
  munch WR m m' -> 0 <= a < 2 ^ 64 -> outside WR a -> apresent H m a -> apresent H m' a.
Proof.
  intros H WR m m' a HM Ha Ho [Hh (b & Hb)]. split; [exact Hh|]. exists b. rewrite (HM (Z_to_bv 64 a)); [exact Hb|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  exact Ho.
Qed.

Lemma outside_dec : forall (WR : list ivl) x, outside WR x \/ ~ outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H | H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [h1 | h1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [h2 | h2]; [right; intros [Hn _]; lia | left; split; [lia | exact H]].
Qed.

Lemma tcj_of_kept_munch : forall lyc Sc (W : YA0n.world AB1v.tfibsegs) memc mdc mem2 mfin (sp STK : Z) (E : Z -> Prop)
    (WR : list ivl),
  AR AB1v.tfibsegs B lyc Sc W memc mdc ->
  lib.Reusable.YM05.alloc_ceiling <= sp - STK ->
  acall_kept AB1v.tfibsegs B lyc Sc W memc W mem2 (sp - STK) sp (fun _ => False) ->
  munch WR mem2 mfin ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside WR a ->
     (sp - STK <= a < sp) \/ E a \/
     (a < lib.Reusable.YM05.alloc_ceiling /\ ~ in_img AB1v.tfibsegs a /\
      (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> a <> b + i) /\
      (forall cid pos, In (cid, pos) (frames Sc) ->
         ~ in_zr a (frame_rng lyc (cid, pos)) /\
         ~ in_zr a (YG0f.shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))) ->
  (forall a, E a -> ~ in_img AB1v.tfibsegs a) ->
  (forall a, E a -> lib.Reusable.YM05.alloc_ceiling <= a -> ~ (sp - STK <= a < sp) -> apresent (YA0n.w_H W) mfin a) ->
  (forall a, sp - STK <= a < sp -> apresent (YA0n.w_H W) mfin a) ->
  tcj_kept B STK lyc Sc W memc W mfin sp E.
Proof.
  intros lyc Sc W memc mdc mem2 mfin sp STK E WR HAR Hc (K1 & K2 & K3 & K4 & K5 & K6) HM HWR HEi HE HW.
  unfold tcj_kept.
  lazymatch goal with |- context [aview ?sg _ _ _] => change sg with AB1v.tfibsegs end.
  lazymatch goal with |- context [in_img ?sg _] => change sg with AB1v.tfibsegs | |- _ => idtac end.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn HnE.
    destruct (outside_dec WR (a)) as [Ho | Ho].
    + rewrite (aview_munch_out W WR mem2 mfin a HM ltac:(lia) Ho). exact (K1 a Ha Hn).
    + destruct (HWR a ltac:(lia) Ho) as [Hw | [He | (Hlt & _)]]; [lia | contradiction | lia].
  - intros b m i Hin Hi HnE.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hceil & _).
    destruct (outside_dec WR ((b + i))) as [Ho | Ho].
    + rewrite (aview_munch_out W WR mem2 mfin (b + i) HM ltac:(lia) Ho). exact (K2 b m i Hin Hi (fun F => F)).
    + destruct (HWR (b + i) ltac:(lia) Ho) as [Hw | [He | (Hlt & _ & Hb & _)]]; [lia | contradiction |].
      exfalso. exact (Hb b m i Hin Hi eq_refl).
  - intros a Hi Hs He.
    pose proof (A.ProgWorld.pws_segs_low a Hi) as HL. unfold kLowMemEnd in HL.
    assert (Ha : 0 <= a). { destruct Hi as (sg & _ & Hsg). lia. }
    destruct (outside_dec WR (a)) as [Ho | Ho].
    + rewrite (aview_munch_out W WR mem2 mfin a HM ltac:(lia) Ho). exact (K3 a Hi Hs He).
    + exfalso. destruct (HWR a ltac:(lia) Ho) as [Hw | [HEa | (_ & Hni & _)]]; [lia | | exact (Hni Hi)].
      exact (HEi a HEa Hi).
  - intros cid pos a Hin Hr HnE.
    destruct (frames_bounds AB1v.tfibsegs B LAWS _ _ _ _ _ cid pos HAR Hin) as (F1 & F2 & F3).
    pose proof (fs_frame_bytes_nonneg cid) as Fn.
    assert (Ha : 0 <= a < lib.Reusable.YM05.alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      unfold YG0f.shadow_addr, YG0f.SHADOW_OFF in Hr. Z.div_mod_to_equations. lia. }
    destruct (outside_dec WR (a)) as [Ho | Ho].
    + rewrite (aview_munch_out W WR mem2 mfin a HM ltac:(lia) Ho). exact (K4 cid pos a Hin Hr (fun F => F)).
    + exfalso. destruct (HWR a ltac:(lia) Ho) as [Hw | [He | (_ & _ & _ & Hf)]]; [lia | contradiction |].
      destruct (Hf cid pos Hin) as [Hf1 Hf2]. destruct Hr as [Hr | Hr]; [exact (Hf1 Hr) | exact (Hf2 Hr)].
  - intros a Ha Hn Hp.
    destruct (outside_dec WR (a)) as [Ho | Ho].
    + exact (present_munch_out (YA0n.w_H W) WR mem2 mfin a HM ltac:(lia) Ho (K5 a Ha Hn Hp)).
    + destruct (HWR a ltac:(lia) Ho) as [Hw | [He | (Hlt & _)]]; [lia | exact (HE a He ltac:(lia) Hn) | lia].
  - exact HW.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The footprint (rng) facts of a stretch at a cut, at RNG := RNG_W (hidden_plus (w_H W) FS). *)
Lemma bmb_FS_app : forall ly S (W : YA0n.world AB1v.tfibsegs) m md,
  AR AB1v.tfibsegs B ly S W m md ->
  4096 <= ly_F ly /\ (ly_F ly + kFakeStackSize <= kLowShadowBeg \/
                      (kHighMemBeg <= ly_F ly /\ ly_F ly + kFakeStackSize <= lib.Reusable.YM05.alloc_ceiling)) /\
  A.Prog.asan_stack_malloc_c.ASAN_GT <= ly_F ly.
Proof.
  intros ly S W m md HAR. pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) _ (A.ProgWorld_Fs.pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct F1 as [F0 F1].
  split; [exact F0|]. split; [unfold ASAN_CEIL in F1; exact F1|].
  exact (A.ProgWorld_Fs.pw_F_above B ly S W m md HAR).
Qed.

(* An image range, as a footprint range that avoids the hint word (the side stack is above the image). *)
Lemma img_rng_plus : forall (W : YA0n.world AB1v.tfibsegs) FS lo len,
  0x10000 <= lo -> 0 <= len -> lo + len <= 0x5fe000 -> A.Prog.asan_stack_malloc_c.ASAN_GT <= FS ->
  rng (RNG_W (hidden_plus (YA0n.w_H W) FS)) lo len.
Proof.
  intros W FS lo len H1 H2 H3 H4. unfold ASAN_GT in H4.
  apply rng_plus; [|left; lia].
  apply (A.ProgBridge.range_visible_sub _ ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO));
    [exact (A.ProgBridge.img_vis_W W) | unfold ImgBounds.IMG_LO; lia | lia |
     unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia].
Qed.

(* The shadow byte cover of an image range, from the bundle's img_shadow_vis. *)
Lemma img_sh_cover_plus : forall ly S (W : YA0n.world AB1v.tfibsegs) m md FS lo len,
  A.Prog.CtrlRo.img_shadow_vis AB1v.tfibsegs B -> AR AB1v.tfibsegs B ly S W m md ->
  FS = ly_F ly -> 0x10000 + 64 <= lo -> 0 <= len -> lo + len + 64 <= 0x5fe000 ->
  A.Prog.reac_box_model_block_cF.sh_cover (RNG_W (hidden_plus (YA0n.w_H W) FS)) lo len.
Proof.
  intros ly S W m md FS lo len HSV HAR EFS H1 H2 H3.
  destruct (bmb_FS_app ly S W m md HAR) as (F0 & Fapp & FGT). rewrite <- EFS in Fapp, FGT, F0.
  unfold ASAN_GT in FGT. unfold kLowShadowBeg, kHighMemBeg, kFakeStackSize in Fapp.
  unfold A.Prog.reac_box_model_block_cF.sh_cover.
  apply rng_plus.
  - split; [unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia|].
    split; [unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia|].
    intros a Ha. apply (A.ProgWorldVisFrame.vis_of_aview AB1v.tfibsegs W m).
    assert (Hx : exists x, 0x10000 <= x < 0x5fe000 /\ a = shadow_addr x).
    { exists (8 * (a - ASAN_K)). unfold shadow_addr, ASAN_K in *. Z.div_mod_to_equations. lia. }
    destruct Hx as (x & Hxr & ->).
    assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y)
      by (destruct (A.ProgWorld.ctl_fs_geom 0 0 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & HE); exact HE).
    rewrite ESH. unfold A.Prog.CtrlRo.img_shadow_vis in HSV.
    exact (HSV ly S W m md x HAR ltac:(unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI; lia)).
  - unfold shadow_addr, ASAN_K in *. Z.div_mod_to_equations. lia.
Qed.

Lemma img_sh_cover_strict : forall ly S (W : YA0n.world AB1v.tfibsegs) m md FS lo len,
  A.Prog.CtrlRo.img_shadow_vis AB1v.tfibsegs B -> AR AB1v.tfibsegs B ly S W m md ->
  FS = ly_F ly -> 0x10000 <= lo -> 1 <= len -> lo + len <= 0x5fe000 ->
  A.Prog.reac_box_model_block_cF.sh_cover (RNG_W (hidden_plus (YA0n.w_H W) FS)) lo len.
Proof.
  intros ly S W m md FS lo len HSV HAR EFS H1 H2 H3.
  destruct (bmb_FS_app ly S W m md HAR) as (F0 & Fapp & FGT). rewrite <- EFS in Fapp, FGT, F0.
  unfold ASAN_GT in FGT. unfold kLowShadowBeg, kHighMemBeg, kFakeStackSize in Fapp.
  unfold A.Prog.reac_box_model_block_cF.sh_cover.
  apply rng_plus.
  - split; [unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia|].
    split; [unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia|].
    intros a Ha. apply (A.ProgWorldVisFrame.vis_of_aview AB1v.tfibsegs W m).
    assert (Hx : exists x, 0x10000 <= x < 0x5fe000 /\ a = shadow_addr x).
    { exists (8 * (a - ASAN_K)). unfold shadow_addr, ASAN_K in *. Z.div_mod_to_equations. lia. }
    destruct Hx as (x & Hxr & ->).
    assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y)
      by (destruct (A.ProgWorld.ctl_fs_geom 0 0 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & HE); exact HE).
    rewrite ESH. unfold A.Prog.CtrlRo.img_shadow_vis in HSV.
    exact (HSV ly S W m md x HAR ltac:(unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI; lia)).
  - unfold shadow_addr, ASAN_K in *. Z.div_mod_to_equations. lia.
Qed.

(* Every byte of the shadow of the class-0..10 frames area is present (am_areas' ASh entry). *)
Lemma bmb_FSsh_present : forall ly S (W : YA0n.world AB1v.tfibsegs) m md a,
  AR AB1v.tfibsegs B ly S W m md ->
  YG0f.shadow_addr (ly_F ly + kFakeFramesOff) <= a <
    YG0f.shadow_addr (ly_F ly + kFakeFramesOff) + (kFakeStackSize - kFakeFramesOff) / 8 ->
  apresent (YA0n.w_H W) m a.
Proof.
  intros ly S W m md a HAR Ha. pose proof HAR as (M & L & _).
  pose proof (am_layout _ _ _ _ M) as LO.
  destruct (bmb_FS_app ly S W m md HAR) as (F0 & Fapp & FGT).
  pose proof (am_areas _ _ _ _ M) as AA. unfold aareas in AA.
  apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA].
  do 5 (apply Forall_cons_iff in AA as [_ AA]). apply Forall_cons_iff in AA as [ASh _].
  specialize (ASh (a - YG0f.shadow_addr (ly_F ly + kFakeFramesOff)) ltac:(cbn [snd]; lia)).
  cbn [fst aeval] in ASh.
  replace (YG0f.shadow_addr (ly_F ly + kFakeFramesOff) + (a - YG0f.shadow_addr (ly_F ly + kFakeFramesOff)))
    with a in ASh by lia.
  apply (YG0s.aview_present AB1v.tfibsegs ly S md (YA0n.w_H W) m a L).
  - unfold YG0f.shadow_addr, SHADOW_OFF, kFakeFramesOff, kFakeStackSize, kLowShadowBeg, kHighMemBeg in *.
    pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR. Z.div_mod_to_equations. lia.
  - pose proof (lo_img _ LO) as (I1 & I2 & I3 & _). unfold in_zr, kImgLo, kImgEnd in *. rewrite I1.
    unfold YG0f.shadow_addr, SHADOW_OFF, kFakeFramesOff, kLowShadowBeg, kHighMemBeg in *.
    intros Hin. Z.div_mod_to_equations. lia.
  - exact ASh.
Qed.

(* RFSw and RFSsh at the hint-hiding footprint: the side stack is visible (ProgWorld_Fs.pw_F_present) and the
   shadow of its frames area too (bmb_FSsh_present); tl (fp_w [0] FS) starts at the flags, above the hint word. *)
Lemma bmb_fs_rng : forall ly S (W : YA0n.world AB1v.tfibsegs) m md,
  AR AB1v.tfibsegs B ly S W m md ->
  A.Prog.reac_box_model_block_cF.rng_ivls (RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly)))
    (tl (fp_w [0%nat] (ly_F ly))) /\
  rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly)))
    (shadow_addr (fs_frame (ly_F ly) 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8).
Proof.
  intros ly S W m md HAR.
  destruct (bmb_FS_app ly S W m md HAR) as (F0 & Fapp & FGT).
  unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg in Fapp.
  pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR. unfold ASAN_GT in FGT.
  assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y)
    by (destruct (A.ProgWorld.ctl_fs_geom 0 0 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & HE); exact HE).
  assert (EF0 : fs_frame (ly_F ly) 0%nat 0 = ly_F ly + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (EFM : fs_frame (ly_F ly) 0%nat (fs_M 0%nat) = ly_F ly + 36864 + 1048576)
    by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  assert (EFl : fs_flag (ly_F ly) 0%nat 0 = ly_F ly + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (EM : fs_M 0%nat = 16384) by reflexivity.
  assert (EB0 : fs_B 0%nat = 64) by reflexivity.
  assert (VIS : forall lo len, ly_F ly <= lo -> 0 <= len -> lo + len <= ly_F ly + 11571200 ->
            A.ProgBridge.range_visible (YA0n.w_H W) lo len).
  { intros lo len H1 H2 H3. apply (vis_of_present W m); [lia | lia |].
    intros a Ha. apply (A.ProgWorld_Fs.pw_F_present B ly S W m md a HAR). unfold kFakeStackSize. lia. }
  assert (VISsh : forall lo len, YG0f.shadow_addr (ly_F ly + 36864) <= lo -> 0 <= len ->
            lo + len <= YG0f.shadow_addr (ly_F ly + 36864) + (11571200 - 36864) / 8 ->
            A.ProgBridge.range_visible (YA0n.w_H W) lo len).
  { intros lo len H1 H2 H3. apply (vis_of_present W m).
    - unfold YG0f.shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    - unfold YG0f.shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    - intros a Ha. apply (bmb_FSsh_present ly S W m md a HAR).
      unfold kFakeFramesOff, kFakeStackSize in *. change (4096 + 32768) with 36864. lia. }
  split.
  - assert (R1 : rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly))) (fs_flag (ly_F ly) 0%nat 0) (fs_M 0%nat)).
    { apply (rng_plus W _ _ (ly_F ly)).
      - apply VIS; rewrite ?EFl, ?EM; [lia | lia | lia].
      - right. rewrite EFl. lia. }
    assert (R2 : rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly))) (fs_frame (ly_F ly) 0%nat 0) 1048576).
    { apply (rng_plus W _ _ (ly_F ly)).
      - apply VIS; rewrite ?EF0; [lia | lia | lia].
      - right. rewrite EF0. lia. }
    assert (R3 : rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly)))
                   (shadow_addr (fs_frame (ly_F ly) 0%nat 0)) 131072).
    { apply (rng_plus W _ _ (ly_F ly)).
      - apply VISsh; rewrite ?ESH, ?EF0; [lia | lia |].
        unfold YG0f.shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
      - rewrite ESH, EF0. unfold YG0f.shadow_addr, SHADOW_OFF in *.
        destruct Fapp as [HFlow | [HFh1 HFh2]]; [right | left]; Z.div_mod_to_equations; lia. }
    unfold fp_w, fp_w1. cbn [flat_map app tl].
    repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; intros b jj Hb Hj.
    + exact (proj2 (proj2 R1) b jj ltac:(lia) ltac:(lia)).
    + exact (proj2 (proj2 R2) b jj ltac:(lia) ltac:(rewrite EFM, EF0 in *; lia)).
    + refine (proj2 (proj2 R3) b jj ltac:(lia) _).
      rewrite ESH, EFM in Hj. rewrite ESH, EF0 in *.
      unfold YG0f.shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
  - apply (rng_plus W _ _ (ly_F ly)).
    + apply VISsh; rewrite ?ESH, ?EF0, ?EM, ?EB0; [lia | lia |].
      unfold YG0f.shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    + rewrite ESH, EF0, EM, EB0. unfold YG0f.shadow_addr, SHADOW_OFF in *.
      destruct Fapp as [HFlow | [HFh1 HFh2]]; [right | left]; Z.div_mod_to_equations; lia.
Qed.
(* A const-table cell of the bundle is visible (its view reads every byte). *)
Lemma vis_c8_row : forall ly S (W : YA0n.world AB1v.tfibsegs) m md ea ev a,
  AR AB1v.tfibsegs B ly S W m md -> In (c8 ea ev) (A.AF0m.Tfib_const ly) -> aeval B ly ea = a ->
  0 <= a -> a + 8 <= 2 ^ 64 -> A.ProgBridge.range_visible (YA0n.w_H W) a 8.
Proof.
  intros ly S W m md ea ev a HAR Hin Ea H0 H1.
  pose proof (A.ProgWorld_Fs.pw_row B TSY ly S W m md (c8 ea ev) HAR Hin) as CH.
  unfold cell_holds, c8 in CH. cbn [c_at c_w c_val] in CH. rewrite Ea in CH.
  split; [exact H0|]. split; [exact H1|]. intros x Hx.
  apply (A.ProgWorldVisFrame.vis_of_aview AB1v.tfibsegs W m).
  specialize (CH (Z.to_nat (x - a)) ltac:(lia)). rewrite Z2Nat.id in CH by lia.
  replace (a + (x - a)) with x in CH by lia. rewrite CH. discriminate.
Qed.

(* Rwin / Rwsh / Rwsw at the hint-hiding footprint. *)
Lemma bmb_win_rng : forall ly S (W : YA0n.world AB1v.tfibsegs) m md (sp : Z),
  AR AB1v.tfibsegs B ly S W m md ->
  ly_F ly + FS_SIZE <= sp - 4272 -> ly_stk_lo ly <= sp - 4272 -> sp <= ly_stk_hi ly -> sp <= APPMEM_END ->
  (forall a, sp - 4272 <= a < sp -> apresent (YA0n.w_H W) m a) ->
  rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly))) (sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K /\
  A.Prog.reac_box_model_block_cF.sh_cover (RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly)))
    (sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K /\
  A.Prog.rng_asan.sh_word_rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly)))
    (sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
Proof.
  intros ly S W m md sp HAR HFS Hlo Hhi Hsp Hpres.
  destruct (bmb_FS_app ly S W m md HAR) as (F0 & Fapp & FGT).
  unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg in Fapp. unfold FS_SIZE in HFS.
  pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
  assert (EK : REAC_BOX_MODEL_BLOCK_K = 4272) by reflexivity.
  assert (HSH : A.ProgBridge.range_visible (YA0n.w_H W) (A.Prog.rng_asan.sh_al8_lo (sp - 4272))
                  (A.Prog.rng_asan.sh_al8_hi (sp - 4272) 4272 - A.Prog.rng_asan.sh_al8_lo (sp - 4272))).
  { destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly S W m md (sp - 4272) 4272 HAR Hlo ltac:(lia) ltac:(lia))
      as [E0 | HV]; [lia | exact HV]. }
  assert (HDJ : A.Prog.rng_asan.sh_al8_lo (sp - 4272) + (A.Prog.rng_asan.sh_al8_hi (sp - 4272) 4272 -
                  A.Prog.rng_asan.sh_al8_lo (sp - 4272)) <= ly_F ly \/
                ly_F ly + 8 <= A.Prog.rng_asan.sh_al8_lo (sp - 4272)).
  { unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, shadow_addr, ASAN_K, APPMEM_END in *.
    destruct Fapp as [HFlow | [HFh1 HFh2]]; [right | left]; Z.div_mod_to_equations; lia. }
  split; [|split].
  - rewrite EK. apply (rng_plus W _ _ (ly_F ly)); [|right; lia].
    apply (vis_of_present W m); [lia | unfold APPMEM_END in Hsp; lia |].
    intros a Ha. apply Hpres. lia.
  - rewrite EK. unfold A.Prog.reac_box_model_block_cF.sh_cover.
    change (shadow_addr (sp - 4272) / 8 * 8) with (A.Prog.rng_asan.sh_al8_lo (sp - 4272)).
    change (shadow_addr (sp - 4272 + 4272 - 1) / 8 * 8 + 8) with (A.Prog.rng_asan.sh_al8_hi (sp - 4272) 4272).
    exact (rng_plus W _ _ (ly_F ly) HSH HDJ).
  - rewrite EK. unfold A.Prog.rng_asan.sh_word_rng. right.
    exact (rng_plus W _ _ (ly_F ly) HSH HDJ).
Qed.

(* The allocator's own extents are apart from the side stack (layout_ok lo_disj). *)
Lemma bmb_ext_dj : forall ly S (W : YA0n.world AB1v.tfibsegs) m md,
  AR AB1v.tfibsegs B ly S W m md ->
  zdisjoint (ly_T ly, kThreadObjSize) (ly_F ly, kFakeStackSize) /\
  zdisjoint (ly_F ly, kFakeStackSize) (ly_C ly, 256) /\
  zdisjoint (ly_F ly, kFakeStackSize) (ly_D ly, 4096).
Proof.
  intros ly S W m md HAR. pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_disj _ LO) as LD.
  split; [|split].
  - exact (pairwise_In2 zdisjoint _ _ _ [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv)] []
             [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256); (ly_D ly, 4096);
              (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  - exact (pairwise_In2 zdisjoint _ _ _
             [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
             [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize)]
             [(ly_D ly, 4096); (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  - exact (pairwise_In2 zdisjoint _ _ _
             [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
             [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256)]
             [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
Qed.

(* Rtls at the hint-hiding footprint: the thread cells are AR's (fl_tls_same with no write) and each of the five
   ranges the run reads is visible -- two in the image, three in allocator extents apart from the side stack. *)
Lemma bmb_tls_rng : forall ly S (W : YA0n.world AB1v.tfibsegs) m md, ro_agree rsegs m ->
  AR AB1v.tfibsegs B ly S W m md ->
  A.Prog.reac_box_model_block_cF.reac_box_model_block_tls_rng
    (RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly))) (normalize rsegs m) RT_TP.
Proof.
  intros ly S W m md Hro HAR DT TS C T DB k HT.
  pose proof (asan_tls_cells_normalize _ _ _ _ _ _ _ _ Hro (tls_cells_AR ly S W m md HAR)) as X1.
  destruct (A.Prog.RcAsanFPLib.fl_tls_same _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HT (fun x _ => eq_refl)
              ltac:(apply Forall_forall; intros d _ x _; exact I)) as (<- & <- & <- & <- & <- & <-).
  destruct (bmb_FS_app ly S W m md HAR) as (F0 & Fapp & FGT). unfold ASAN_GT in FGT.
  destruct (bmb_ext_dj ly S W m md HAR) as (DTF & DFC & DFD).
  unfold zdisjoint, kThreadObjSize, kFakeStackSize in DTF, DFC, DFD. cbn [fst snd] in DTF, DFC, DFD.
  pose proof HAR as (M & _).
  assert (Etsd : ly_tsd ly = 0x5fcbb8) by (rewrite (am_tsd _ _ _ _ M), (A.AF0m.ts_tsd B TSY); reflexivity).
  pose proof (am_layout _ _ _ _ M) as LO.
  assert (EXT : forall e, In e (owned_extents ly) -> 4096 <= fst e /\ fst e + snd e <= 0x7fffff800000).
  { intros e He. exact (A.ProgWorld_Fs.pw_ext_range _ _ (proj1 (Forall_forall _ _) (lo_app _ LO) e He)). }
  destruct (EXT (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as [T0 T1].
  destruct (EXT (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto)) as [CC0 CC1].
  destruct (EXT (ly_D ly, 4096) ltac:(unfold owned_extents; cbn; tauto)) as [D0 D1].
  cbn [fst snd] in T0, T1, CC0, CC1, D0, D1. unfold kThreadObjSize in T1.
  assert (ET : bv_unsigned (Z_to_bv 64 (ly_T ly)) = ly_T ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ly_D ly)) = ly_D ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 (ly_C ly)) = ly_C ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (ETS : bv_unsigned (Z_to_bv 64 (ly_tsd ly)) = ly_tsd ly) by (apply A.ProgWorld_Fs.pw_u64; lia).
  assert (EDT : bv_unsigned (Z_to_bv 64 (RT_TP + 32)) = RT_TP + 32)
    by (apply A.ProgWorld_Fs.pw_u64; unfold RT_TP; lia).
  rewrite ET, ED, EC, ETS, EDT, Etsd.
  split; [|split; [|split; [|split]]].
  - apply (img_rng_plus W (ly_F ly)); unfold RT_TP, ASAN_GT in *; lia.
  - replace (0x5fcbb8 + 8 * 0) with 0x5fcbb8 by lia.
    apply (img_rng_plus W (ly_F ly)); unfold ASAN_GT in *; lia.
  - apply (rng_plus W _ _ (ly_F ly)); [| destruct DFC as [H | H]; [right | left]; lia].
    exact (vis_c8_row ly S W m md (AC 152) (AT 0) (ly_C ly + 152) HAR
             ltac:(apply A.ProgWorld_Fs.pw_in_sym; unfold A.AF0m.Tfib_const_sym;
                   repeat (first [apply in_eq | apply in_cons]))
             ltac:(cbn [aeval]; lia) ltac:(lia) ltac:(lia)).
  - apply (rng_plus W _ _ (ly_F ly)); [| destruct DTF as [H | H]; [left | right]; lia].
    pose proof (vis_c8_row ly S W m md (AT 48) (ANum 0x5dbf48) (ly_T ly + 48) HAR
                  ltac:(apply A.ProgWorld_Fs.pw_in_sym; unfold A.AF0m.Tfib_const_sym;
                        repeat (first [apply in_eq | apply in_cons]))
                  ltac:(cbn [aeval]; lia) ltac:(lia) ltac:(lia)) as V1.
    pose proof (vis_c8_row ly S W m md (AT 56) (ANum 0x5dc024) (ly_T ly + 56) HAR
                  ltac:(apply A.ProgWorld_Fs.pw_in_sym; unfold A.AF0m.Tfib_const_sym;
                        repeat (first [apply in_eq | apply in_cons]))
                  ltac:(cbn [aeval]; lia) ltac:(lia) ltac:(lia)) as V2.
    destruct V1 as (_ & _ & V1b). destruct V2 as (_ & _ & V2b).
    split; [lia|]. split; [lia|]. intros x Hx.
    destruct (Z_lt_le_dec x (ly_T ly + 56)) as [h | h]; [apply V1b; lia | apply V2b; lia].
  - apply (rng_plus W _ _ (ly_F ly)); [| destruct DFD as [H | H]; [right | left]; lia].
    exact (vis_c8_row ly S W m md (AD 24) (ATp 0) (ly_D ly + 24) HAR
             ltac:(apply A.ProgWorld_Fs.pw_in_sym; unfold A.AF0m.Tfib_const_sym;
                   repeat (first [apply in_eq | apply in_cons]))
             ltac:(cbn [aeval]; lia) ltac:(lia) ltac:(lia)).
Qed.


(* RP / RPs / RO / ROs / RN / RNs / RJ13s / RJ14s at the hint-hiding footprint. *)
Lemma bmb_data_rng : forall ly S (W : YA0n.world AB1v.tfibsegs) m md (p o : Z) (row nb : list byte),
  AR AB1v.tfibsegs B ly S W m md -> A.Prog.CtrlRo.img_shadow_vis AB1v.tfibsegs B ->
  (p <> 0 -> 0x10000 + 64 <= p /\ p + 296 + 64 <= 0x5fe000) ->
  (RcSynth.rname row <> 0 -> 0x10000 <= RcSynth.rname row /\ 1 <= Z.of_nat (length nb) /\
     RcSynth.rname row + Z.of_nat (length nb) <= 0x5fe000) ->
  (o <> 0 -> (forall a, o <= a < o + 32 -> aview AB1v.tfibsegs (YA0n.w_H W) m a <> None) /\
             shadow_hull_vis (aview AB1v.tfibsegs (YA0n.w_H W) m) o 32 /\
             ly_F ly + 8 <= o /\ o + 32 <= APPMEM_END) ->
  let RNGx := RNG_W (hidden_plus (YA0n.w_H W) (ly_F ly)) in
  (p <> 0 -> rng RNGx p 296) /\
  (p <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover RNGx p 296) /\
  (o <> 0 -> rng RNGx o 32) /\
  (o <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover RNGx o 32) /\
  (RcSynth.rname row <> 0 -> rng RNGx (RcSynth.rname row) (Z.of_nat (length nb))) /\
  (RcSynth.rname row <> 0 ->
     A.Prog.reac_box_model_block_cF.sh_cover RNGx (RcSynth.rname row) (Z.of_nat (length nb))) /\
  A.Prog.reac_box_model_block_cF.sh_cover RNGx JOIN_0013 32 /\
  A.Prog.reac_box_model_block_cF.sh_cover RNGx JOIN_0014 32.
Proof.
  intros ly S W m md p o row nb HAR HSV HP HN HO. cbv zeta.
  destruct (bmb_FS_app ly S W m md HAR) as (F0 & Fapp & FGT). unfold ASAN_GT in FGT.
  unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg in Fapp.
  pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
  assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y)
    by (destruct (A.ProgWorld.ctl_fs_geom 0 0 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & HE); exact HE).
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - intros Hp. destruct (HP Hp) as [P1 P2]. apply (img_rng_plus W (ly_F ly)); unfold ASAN_GT in *; lia.
  - intros Hp. destruct (HP Hp) as [P1 P2].
    apply (img_sh_cover_plus ly S W m md _ p 296 HSV HAR eq_refl); lia.
  - intros Ho. destruct (HO Ho) as (V1 & _ & Hdj & Hhi).
    apply (rng_plus W _ _ (ly_F ly)); [| right; lia].
    split; [unfold APPMEM_END in Hhi; lia|]. split; [unfold APPMEM_END in Hhi; lia|].
    intros a Ha. exact (A.ProgWorldVisFrame.vis_of_aview AB1v.tfibsegs W m a (V1 a Ha)).
  - intros Ho. destruct (HO Ho) as (_ & V2 & Hdj & Hhi). unfold APPMEM_END in Hhi.
    unfold A.Prog.reac_box_model_block_cF.sh_cover. rewrite !ESH.
    apply (rng_plus W _ _ (ly_F ly)).
    + split; [unfold YG0f.shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia|].
      split; [unfold YG0f.shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia|].
      intros a Ha. apply (A.ProgWorldVisFrame.vis_of_aview AB1v.tfibsegs W m).
      apply V2. lia.
    + unfold YG0f.shadow_addr, SHADOW_OFF in *.
      destruct Fapp as [HFlow | [HFh1 HFh2]]; [right | left]; Z.div_mod_to_equations; lia.
  - intros Hn. destruct (HN Hn) as (N1 & N0 & N2). apply (img_rng_plus W (ly_F ly)); unfold ASAN_GT in *; lia.
  - intros Hn. destruct (HN Hn) as (N1 & N0 & N2).
    apply (img_sh_cover_strict ly S W m md _ (RcSynth.rname row) (Z.of_nat (length nb)) HSV HAR eq_refl); lia.
  - apply (img_sh_cover_plus ly S W m md _ JOIN_0013 32 HSV HAR eq_refl); unfold JOIN_0013; lia.
  - apply (img_sh_cover_plus ly S W m md _ JOIN_0014 32 HSV HAR eq_refl); unfold JOIN_0014; lia.
Qed.

(* HP / HN of the stretches: the spec's image rows as bytes_at at the normalized return memory, with the
   separations the Section asks for. *)
Lemma bmb_hp : forall lyc Sc (W : YA0n.world AB1v.tfibsegs) memc mem2 slo shi (E : Z -> Prop) (p sp : Z)
    (row : list byte),
  acall_kept AB1v.tfibsegs B lyc Sc W memc W mem2 slo shi E -> ro_agree rsegs mem2 ->
  p <> 0 -> p mod 8 = 0 -> length row = 296%nat ->
  garr8 AB1v.tfibsegs (mrestrict (YA0n.w_H W) memc) p (C_reac_box_model_block.bmb_z row) ->
  0x10000 + 64 <= p -> p + 296 + 64 <= 0x5fe000 ->
  (forall x, p <= x < p + 296 ->
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  lib.Reusable.YM05.alloc_ceiling <= sp - 4272 ->
  p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs (normalize rsegs mem2) p row /\
  (sp <= p \/ p + 296 <= sp - 4272).
Proof.
  intros lyc Sc W memc mem2 slo shi E p sp row HK Hro Hp0 Hm8 Hlen HG H1 H2 Hx Hc.
  pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
  split; [exact Hm8|]. split; [exact Hlen|]. split.
  - apply (bmb_bytes_norm lyc Sc W memc mem2 slo shi E p row HK Hro HG); rewrite ?Hlen; [lia | lia |].
    intros x Hxr. apply Hx. lia.
  - right. lia.
Qed.

Lemma signed8_small : forall v, 0 <= v < 128 -> bv_signed (Z_to_bv 8 v) = v.
Proof.
  intros v Hv. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. lia.
Qed.

(* A byte outside the image is not read-only, so normalize keeps it. *)
Lemma ro_addr_not_img : forall a, 0 <= a < 2 ^ 64 -> ~ in_img AB1v.tfibsegs a ->
  ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hni. unfold ro_addr. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  pose proof (find_segment_none AB1v.tfibsegs a Hni) as E. change AB1v.tfibsegs with rsegs in E.
  rewrite E. reflexivity.
Qed.

(* HO: the 32 bytes at o as a cell block at the normalized return memory. *)
Lemma bmb_ho : forall (W : YA0n.world AB1v.tfibsegs) (mem2 : word -> option byte) (o sp : Z),
  (forall a, o <= o -> o <= a < o + 32 -> apresent (YA0n.w_H W) mem2 a) ->
  (forall x, o <= x < o + 32 -> ~ in_img AB1v.tfibsegs x) ->
  0 <= o -> o + 32 <= APPMEM_END ->
  (sp <= o \/ o + 32 <= sp - 4272) ->
  exists ob, rw_cells rsegs (normalize rsegs mem2) o [CB 32 ob] /\
             (sp <= o \/ o + 32 <= sp - 4272) /\ length ob = 32%nat.
Proof.
  intros W mem2 o sp Hpres Hni H0 H1 Hsp.
  unfold APPMEM_END in H1.
  assert (HB : forall i, 0 <= i < 32 -> exists b, normalize rsegs mem2 (wa (o + i)) = Some b).
  { intros i Hi. destruct (Hpres (o + i) ltac:(lia) ltac:(lia)) as [_ (b & Hb)]. exists b.
    unfold normalize, wa. rewrite (ro_addr_not_img (o + i) ltac:(lia) (Hni (o + i) ltac:(lia))). exact Hb. }
  set (ob := map (fun i : nat => match normalize rsegs mem2 (wa (o + Z.of_nat i)) with
                                | Some b => b | None => Z_to_bv 8 0 end) (seq 0 32)).
  assert (Hlen : length ob = 32%nat) by (unfold ob; rewrite length_map, length_seq; reflexivity).
  exists ob. split; [|split; [exact Hsp | exact Hlen]].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hlen | exact I].
  - replace (cells_bytes [CB 32 ob]) with ob by (cbn [cells_bytes cbytes]; symmetry; apply app_nil_r).
    split; [lia|]. split; [rewrite Hlen; cbn [Z.of_nat]; lia|].
    intros i Hi. rewrite Hlen in Hi.
    destruct (HB (Z.of_nat i) ltac:(lia)) as (b & Hb).
    unfold mrd. rewrite Hb. unfold ob.
    rewrite nth_error_map, (A.ProgWorld_Fs.pw_nth_seq 32 i 0 Hi). cbn [option_map].
    replace (0 + i)%nat with i by lia. rewrite Hb. reflexivity.
  - replace (Z.of_nat (cells_size [CB 32 ob])) with 32 by (cbn [cells_size csize Nat.add]; reflexivity).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (HB i ltac:(lia)) as (b & Hb). unfold wview. rewrite Hb. discriminate.
Qed.

(* AP / ANB: a registered global's bytes are addressable (globs_marked's block_shadow at the cut's memory). *)
Lemma bmb_glob_addressable : forall (G : list (Z * Z)) ly S (W : YA0n.world AB1v.tfibsegs) mem2 md q sz a n,
  A.Prog.CtrlRo.globs_marked AB1v.tfibsegs B G -> In (q, sz) G ->
  AR AB1v.tfibsegs B ly S W mem2 md ->
  q <= a -> 0 <= n -> a + n <= q + sz -> 0x10000 <= a -> a + n <= 0x5fe000 ->
  addressable (normalize rsegs mem2) a n.
Proof.
  intros G ly S W mem2 md q sz a n HGM Hin HAR Hqa Hn Hhi H1 H2.
  destruct (HGM ly S W mem2 md q sz Hin HAR) as (Hq8 & Hsz & HBS).
  assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y)
    by (destruct (A.ProgWorld.ctl_fs_geom 0 0 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & HE); exact HE).
  split; [lia|]. split; [exact Hn|]. split; [unfold APPMEM_END; lia|].
  intros i Hi. split; [unfold app_mem, LOWMEM_END; left; lia|].
  set (j := (a + i) / 8 - q / 8).
  assert (Hj0 : 0 <= j) by (unfold j; Z.div_mod_to_equations; lia).
  assert (Hjhi : j < (sz + 7) / 8) by (unfold j; Z.div_mod_to_equations; lia).
  pose proof (HBS j ltac:(lia)) as HV.
  assert (EA : YG0v.shadow_of_addr SHADOW_OFF q + j = YG0f.shadow_addr (a + i)).
  { unfold YG0v.shadow_of_addr, YG0f.shadow_addr, j. Z.div_mod_to_equations. lia. }
  rewrite EA in HV.
  destruct (A.ProgWorld_Fs.pw_view_mrd W mem2 _ _ HV) as [_ HM].
  exists (Z_to_bv 8 (if j <? sz / 8 then 0 else sz mod 8)).
  split.
  - rewrite ESH. unfold normalize, wa, mrd in *.
    rewrite (ro_addr_above (YG0f.shadow_addr (a + i))
               ltac:(unfold ImgBounds.IMG_HI, YG0f.shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia)).
    unfold mrd in HM. exact HM.
  - pose proof (Z.mod_pos_bound sz 8) as Hmb.
    destruct (Z.ltb_spec j (sz / 8)) as [Hlt | Hge].
    + left. rewrite signed8_small by lia. reflexivity.
    + right. rewrite signed8_small by lia.
      unfold j in Hge. split; [Z.div_mod_to_equations; lia | lia].
Qed.

(* AJ1 / AJ2: a zero-shadow global's bytes are addressable (ProgWorldShadow.ctl_zshadow_of_AR). *)
Lemma bmb_zs_addressable : forall ly S (W : YA0n.world AB1v.tfibsegs) mem2 md q sz a n,
  AR AB1v.tfibsegs B ly S W mem2 md -> ro_agree rsegs mem2 ->
  In (q, sz) (as_zero_shadow B) -> q <= a -> 0 <= n -> a + n <= q + 8 * (sz / 8) ->
  addressable (normalize rsegs mem2) a n.
Proof.
  intros ly S W mem2 md q sz a n HAR Hro Hin Hq Hn Hhi.
  apply addressable_normalize; [exact Hro|].
  exact (A.ProgWorldShadow.ctl_zshadow_of_AR B LAWS ly S W mem2 md (q, sz) a n HAR Hin
           ltac:(cbn [fst]; lia) Hn ltac:(cbn [fst snd]; lia)).
Qed.

(* AO, stack case: the caller's stack is addressable at any AR state. *)
Lemma bmb_ao_stack : forall ly S (W : YA0n.world AB1v.tfibsegs) mem2 md o n,
  AR AB1v.tfibsegs B ly S W mem2 md -> ro_agree rsegs mem2 ->
  ly_stk_lo ly <= o -> 0 <= n -> o + n <= ly_stk_hi ly ->
  addressable (normalize rsegs mem2) o n.
Proof.
  intros ly S W mem2 md o n HAR Hro H1 H2 H3.
  apply addressable_normalize; [exact Hro|].
  exact (A.ProgWorldShadow.ctl_stack_shadow_of_AR B LAWS ly S W mem2 md o n HAR H1 H2 H3).
Qed.

(* AO, frame case: the caller's range inside one of its own frames keeps its shadow across the call
   (acall_kept's frame clause), so the addressability it had at the entry holds at the return. *)
Lemma bmb_ao_frame : forall lyc Sc (W : YA0n.world AB1v.tfibsegs) memc mem2 slo shi (E : Z -> Prop) o n cid pos,
  acall_kept AB1v.tfibsegs B lyc Sc W memc W mem2 slo shi E -> ro_agree rsegs mem2 ->
  In (cid, pos) (frames Sc) ->
  (forall x, o <= x < o + n -> in_zr x (frame_rng lyc (cid, pos))) ->
  (forall x, o <= x < o + n -> ~ E (YG0f.shadow_addr x)) ->
  frame_addr lyc cid pos mod 8 = 0 -> fs_frame_bytes cid mod 8 = 0 ->
  0 <= o -> 0 <= n -> o + n <= APPMEM_END ->
  (forall x, o <= x < o + n -> app_mem x) ->
  YG0v.range_addressable (aview AB1v.tfibsegs (YA0n.w_H W) memc) SHADOW_OFF o n ->
  addressable (normalize rsegs mem2) o n.
Proof.
  intros lyc Sc W memc mem2 slo shi E o n cid pos (_ & _ & _ & K4 & _) Hro Hin Hfr HE Hfa8 Hfb8 H0 Hn Hhi Happ HRA.
  assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y)
    by (destruct (A.ProgWorld.ctl_fs_geom 0 0 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & HE'); exact HE').
  split; [exact H0|]. split; [exact Hn|]. split; [exact Hhi|].
  intros i Hi. split; [apply Happ; lia|].
  destruct (HRA (o + i) ltac:(lia)) as (s & Hs & Hok).
  assert (Esh : YG0v.shadow_of_addr SHADOW_OFF (o + i) = YG0f.shadow_addr (o + i)) by reflexivity.
  rewrite Esh in Hs.
  assert (Hin4 : in_zr (YG0f.shadow_addr (o + i))
                   (YG0f.shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).
  { pose proof (Hfr (o + i) ltac:(lia)) as Hx. unfold in_zr, frame_rng in *. cbn [fst snd] in *.
    unfold YG0f.shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. }
  rewrite <- (K4 cid pos _ Hin ltac:(right; exact Hin4) (HE (o + i) ltac:(lia))) in Hs.
  destruct (A.ProgWorld_Fs.pw_view_mrd W mem2 _ _ Hs) as [_ HM].
  exists (Z_to_bv 8 s). split.
  - rewrite ESH. unfold normalize, wa, mrd in *.
    rewrite (ro_addr_above (YG0f.shadow_addr (o + i))
               ltac:(unfold ImgBounds.IMG_HI, YG0f.shadow_addr, SHADOW_OFF, APPMEM_END in *;
                     Z.div_mod_to_equations; lia)).
    unfold mrd in HM. exact HM.
  - destruct Hok as [E0 | [H1 H2]]; [left; rewrite signed8_small by lia; exact E0|].
    right. rewrite signed8_small by lia. split; [exact H1 | lia].
Qed.

(* NDJ: the name range (in the image) is apart from the class-0 side-stack area. *)
Lemma bmb_ndj : forall ly S (W : YA0n.world AB1v.tfibsegs) m md (a n : Z),
  AR AB1v.tfibsegs B ly S W m md -> 0 <= a -> a + n <= 0x5fe000 ->
  fp_dj [(a, a + n)] (fp_w [0%nat] (ly_F ly)).
Proof.
  intros ly S W m md a n HAR H0 H1.
  destruct (bmb_FS_app ly S W m md HAR) as (F0 & Fapp & FGT). unfold ASAN_GT in FGT.
  assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y)
    by (destruct (A.ProgWorld.ctl_fs_geom 0 0 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & HE'); exact HE').
  unfold fp_dj, fp_w, fp_w1. cbn [flat_map app].
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B. cbn [Z.of_nat].
  rewrite ?ESH. unfold shadow_addr, ASAN_K, kFakeStackSize, kLowShadowBeg, kHighMemBeg in *.
  repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd];
    try (Z.div_mod_to_equations; lia).
  all: unfold YG0f.shadow_addr, YG0f.SHADOW_OFF; cbn [Z.of_nat];
       change (2 ^ 20) with 1048576; change (2 ^ (14 - 0)) with 16384; change (2 ^ 0) with 1;
       left; Z.div_mod_to_equations; lia.
Qed.

(* ret_pc of an even return address, and garr8 of the view from bytes_at. *)
Lemma ret_pc_of_ret_ok : forall ra0, lib.Reusable.YK0s.ret_ok ra0 -> ret_pc ra0 = ra0.
Proof.
  intros ra0 Hret. unfold lib.Reusable.YK0s.ret_ok in Hret.
  apply (f_equal bv_unsigned) in Hret.
  unfold lib.Reusable.YK14.v_jalr, lib.Reusable.YK11.jalr_tgtZ in Hret.
  pose proof (Z_to_bv_unsigned 64 (Z.land (bv_unsigned ra0 + 0) (-2))) as EZ.
  rewrite EZ, Z.add_0_r in Hret.
  pose proof (@bv_unsigned_in_range 64 ra0) as Rr. change (bv_modulus 64) with (2 ^ 64) in Rr.
  assert (B0 : Z.testbit (bv_unsigned ra0) 0 = false).
  { rewrite <- Hret. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.land_spec.
    rewrite Bool.andb_false_r. reflexivity. }
  rewrite Z.bit0_odd in B0.
  assert (Hev : bv_unsigned ra0 mod 2 = 0) by (rewrite Zmod_odd, B0; reflexivity).
  pose proof (ret_pc_even (bv_unsigned ra0) ltac:(lia) Hev) as E.
  rewrite (Z_to_bv_bv_unsigned ra0) in E. exact E.
Qed.

(* garr8 of the view from bytes_at at the normalized memory, for a range off the image. *)
Lemma garr8_of_bytes_at : forall (Wg : YA0n.world AB1v.tfibsegs) (mr : word -> option byte) a (bs : list byte),
  bytes_at rsegs (normalize rsegs mr) a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> YA0n.w_H Wg (Z_to_bv 64 x) = false) ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> ~ in_img AB1v.tfibsegs x) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 AB1v.tfibsegs (mrestrict (YA0n.w_H Wg) mr) a (C_reac_box_model_block.bmb_z bs).
Proof.
  intros Wg mr a bs (_ & _ & HB) Hvis Hni H0 H1 j Hj.
  unfold C_reac_box_model_block.bmb_z in Hj |- *. rewrite length_map in Hj.
  assert (Hn : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0)))
    by (rewrite <- (map_nth (fun b : byte => bv_unsigned b)); reflexivity).
  rewrite Hn. assert (R : 0 <= bv_unsigned (nth j bs (Z_to_bv 8 0)) < 256) by (pose proof (@bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as R0; change (bv_modulus 8) with 256 in R0; exact R0). split; [|lia].
  intros k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
  specialize (HB j Hj).
  assert (Hx : a <= a + Z.of_nat j < a + Z.of_nat (length bs)) by lia.
  assert (Ero : ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat j)) = false)
    by (apply ro_addr_not_img; [lia | exact (Hni _ Hx)]).
  assert (Erom : seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat j)) = None).
  { apply (A.MemNorm.seg_rom_unmapped rsegs). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    pose proof (find_segment_none AB1v.tfibsegs (a + Z.of_nat j) (Hni _ Hx)) as E.
    change AB1v.tfibsegs with rsegs in E. exact E. }
  unfold mrd, wa, normalize in HB. rewrite Ero, Erom in HB.
  destruct (mr (Z_to_bv 64 (a + Z.of_nat j))) as [bb|] eqn:Eb.
  - unfold mbyte, mrestrict, wa. rewrite (Hvis _ Hx), Eb. change AB1v.tfibsegs with rsegs.
    rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hj) in HB. injection HB as HB. rewrite HB.
    unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small _ 256 R).
    f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with 256. symmetry. apply Z.mod_small. exact R.
  - rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hj) in HB. discriminate HB.
Qed.

(* The facts of o's 32 bytes at the allocator's return memory that main_mid_F's footprint needs, from the spec's
   o premises at the entry memory and what the call keeps. *)
Lemma bmb_o_facts : forall lyc Sc S2 (W : YA0n.world AB1v.tfibsegs) memc mdc mem2 md2 slo shi (sp o : Z),
  AR AB1v.tfibsegs B lyc Sc W memc mdc -> AR AB1v.tfibsegs B lyc S2 W mem2 md2 ->
  acall_kept AB1v.tfibsegs B lyc Sc W memc W mem2 slo shi (fun _ => False) ->
  lib.Reusable.YM05.alloc_ceiling <= slo -> (shi <= o \/ o + 32 <= slo) ->
  ((exists cid pos, In (cid, pos) (frames Sc) /\ cid <> 0 /\
      forall x, o <= x < o + 32 -> in_zr x (frame_rng lyc (cid, pos))) \/
   (ly_stk_lo lyc <= o /\ o + 32 < ly_stk_hi lyc)) ->
  (forall a, o <= a < o + 32 -> aview AB1v.tfibsegs (YA0n.w_H W) memc a <> None) ->
  shadow_hull_vis (aview AB1v.tfibsegs (YA0n.w_H W) memc) o 32 ->
  (forall a, o <= a < o + 32 -> aview AB1v.tfibsegs (YA0n.w_H W) mem2 a <> None) /\
  shadow_hull_vis (aview AB1v.tfibsegs (YA0n.w_H W) mem2) o 32 /\
  ly_F lyc + 8 <= o /\ o + 32 <= APPMEM_END.
Proof.
  intros lyc Sc S2 W memc mdc mem2 md2 slo shi sp o HAR HAR2 (K1 & _ & _ & K4 & _) Hslo Hsep Hhome TV THU.
  assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y)
    by (destruct (A.ProgWorld.ctl_fs_geom 0 0 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & HE'); exact HE').
  pose proof ASAN_CEIL_range as [CRa _]. unfold ASAN_CEIL in CRa.
  destruct (bmb_FS_app lyc Sc W memc mdc HAR) as (FA0 & FAapp & FAgt).
  unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg in FAapp. unfold ASAN_GT in FAgt.
  destruct Hhome as [(cid & pos' & Hin & Hcid & Hx) | [Hs1 Hs2]].
  - destruct (YG0s.frame_facts B lyc Sc _ cid pos' (proj1 HAR) Hin)
      as (Hc10 & Hpos' & HFapp & _ & HFal & Hfo1 & Hfo2 & Hfo64 & Hfb64 & Hfbm & Hflb).
    pose proof (Hx o ltac:(lia)) as X0. pose proof (Hx (o + 31) ltac:(lia)) as X1.
    unfold in_zr, frame_rng in X0, X1. cbn [fst snd] in X0, X1.
    assert (Hfa64 : frame_addr lyc cid pos' mod 64 = 0).
    { unfold frame_addr, page_aligned in *.
      pose proof (Z.div_mod (ly_F lyc) 4096 ltac:(lia)) as D1. rewrite HFal in D1.
      pose proof (Z.div_mod (fs_frame_off cid pos') 64 ltac:(lia)) as D2. rewrite Hfo64 in D2.
      replace (ly_F lyc + fs_frame_off cid pos')
        with ((64 * (ly_F lyc / 4096) + fs_frame_off cid pos' / 64) * 64) by lia.
      apply Z.mod_mul. lia. }
    set (fa := frame_addr lyc cid pos') in *. set (fb := fs_frame_bytes cid) in *.
    assert (KEEPS : forall s, YG0f.shadow_addr o / 8 * 8 <= s < YG0f.shadow_addr (o + 32 - 1) / 8 * 8 + 8 ->
                      aview AB1v.tfibsegs (YA0n.w_H W) mem2 s = aview AB1v.tfibsegs (YA0n.w_H W) memc s).
    { intros s Hs. apply (K4 cid pos' s Hin); [|exact (fun F => F)]. right. unfold in_zr. cbn [fst snd].
      fold fa fb. clearbody fa fb. clear - Hs X0 X1 Hfa64 Hfbm. unfold YG0f.shadow_addr, SHADOW_OFF in *.
      apply Z.mod_divide in Hfa64; [|lia]. apply Z.mod_divide in Hfbm; [|lia].
      destruct Hfa64 as [ka ->]. destruct Hfbm as [kb ->].
      Z.div_mod_to_equations. lia. }
    split; [intros a Ha; rewrite (K4 cid pos' a Hin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia)
                                    (fun F => F)); exact (TV a Ha)|].
    split; [intros s Hs; rewrite ?ESH in Hs; rewrite (KEEPS s Hs); apply THU; rewrite ?ESH; exact Hs|].
    assert (HC2 : 2 ^ 20 <= cid * 2 ^ 20) by (change (2 ^ 20) with 1048576; lia).
    unfold fa, frame_addr, kFakeFramesOff in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    unfold APPMEM_END. lia.
  - pose proof HAR2 as (M2 & _). pose proof (am_zshadow _ _ _ _ M2) as ZS2.
    pose proof (proj1 (Forall_forall _ _) ZS2 (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
                  ltac:(unfold zero_shadow_ranges; left; reflexivity)) as ZSstk. cbn [fst snd] in ZSstk.
    pose proof (lo_stk_ceil _ (am_layout _ _ _ _ M2)) as SC2. unfold ASAN_CEIL in SC2.
    pose proof (lo_top _ (am_layout _ _ _ _ M2)) as (_ & _ & _ & T4 & PL2 & PA2 & _). unfold kHighMemEnd in T4.
    split.
    + intros a Ha. rewrite (K1 a ltac:(lia) ltac:(lia)). exact (TV a Ha).
    + split.
      * intros s Hs. rewrite ?ESH in Hs.
        assert (Hx : exists x, ly_stk_lo lyc <= x /\ x + 8 <= ly_stk_hi lyc /\
                       s = YG0v.shadow_of_addr SHADOW_OFF x /\ x mod 8 = 0).
        { exists (8 * (s - SHADOW_OFF)). clear - Hs Hs1 Hs2 PA2 PL2.
          unfold page_aligned in PA2, PL2. unfold YG0v.shadow_of_addr, YG0f.shadow_addr, SHADOW_OFF in *.
          Z.div_mod_to_equations. lia. }
        destruct Hx as (x & X1 & X2 & -> & X4).
        replace (YG0v.shadow_of_addr SHADOW_OFF x)
          with (YG0v.shadow_of_addr SHADOW_OFF (ly_stk_lo lyc) + (x - ly_stk_lo lyc) / 8)
          by (clear - X1 X4 PL2; unfold page_aligned in PL2; unfold YG0v.shadow_of_addr;
              Z.div_mod_to_equations; lia).
        rewrite (ZSstk ((x - ly_stk_lo lyc) / 8) ltac:(clear - X1 X2; Z.div_mod_to_equations; lia)).
        discriminate.
      * split; [lia | unfold APPMEM_END; lia].
Qed.

Lemma not_outside_cons : forall l h (Wl : list ivl) a, ~ outside ((l, h) :: Wl) a -> (l <= a < h) \/ ~ outside Wl a.
Proof.
  intros l h Wl a H. cbn [outside] in H.
  destruct (Z_lt_le_dec a l) as [h1 | h1]; [right; intros Ho; apply H; split; [lia | exact Ho]|].
  destruct (Z_lt_le_dec a h) as [h2 | h2]; [left; split; assumption|].
  right; intros Ho; apply H; split; [lia | exact Ho].
Qed.

(* A client block is apart from the side stack (its chunk is: YG0s.chunk_vs_F). *)
Lemma block_vs_F : forall ly S (W : YA0n.world AB1v.tfibsegs) mem md p n,
  AR AB1v.tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= ly_F ly \/ ly_F ly + kFakeStackSize <= p.
Proof.
  intros ly S W mem md p n HAR Hin. pose proof HAR as (M & _).
  apply (YG0s.In_ablocks B) in Hin as (k & Hk & _ & Ep & En).
  pose proof (YG0s.chunk_facts B ly S _ k M Hk) as (_ & _ & _ & Eu & Hrz & _ & _ & Hext & _).
  pose proof (YG0s.chunk_vs_F B ly S _ k M Hk) as D. unfold zdisjoint in D. cbn [fst snd] in D.
  subst p n. lia.
Qed.

(* The bytes of the side-stack area are apart from every caller frame of Sc and from its shadow, and from every block:
   for the flag byte, the class-0 frame cgif allocated, and that frame's shadow. *)
Lemma side_class : forall lyc Sc S2 (W : YA0n.world AB1v.tfibsegs) mem2 md2 jj a,
  AR AB1v.tfibsegs B lyc S2 W mem2 md2 -> frames S2 = (0, jj) :: frames Sc ->
  ablocks B lyc S2 = ablocks B lyc Sc -> 0 <= jj < fs_M 0%nat -> ~ In (0, jj) (frames Sc) ->
  (fs_flag (ly_F lyc) 0 jj <= a < fs_flag (ly_F lyc) 0 jj + 1 \/
   fs_frame (ly_F lyc) 0%nat jj <= a < fs_frame (ly_F lyc) 0%nat jj + 64 \/
   shadow_addr (fs_frame (ly_F lyc) 0%nat jj) <= a < shadow_addr (fs_frame (ly_F lyc) 0%nat jj) + 8) ->
  a < lib.Reusable.YM05.alloc_ceiling /\ ~ in_img AB1v.tfibsegs a /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> a <> b + i) /\
  (forall cid pos, In (cid, pos) (frames Sc) ->
     ~ in_zr a (frame_rng lyc (cid, pos)) /\
     ~ in_zr a (YG0f.shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).
Proof.
  intros lyc Sc S2 W mem2 md2 jj a HAR2 Hfrs2 Eab Hjj Hnin Ha.
  pose proof HAR2 as (M2 & _). pose proof (am_layout _ _ _ _ M2) as LO.
  assert (Hin0 : In (0, jj) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (YG0s.frame_facts B lyc S2 _ 0 jj M2 Hin0)
    as (_ & Hpos & HFapp & HFno & HFal & Hfo1 & Hfo2 & Hfo64 & Hfb64 & Hfbm & Hflb).
  destruct (A.ProgWorld.ctl_fs_geom (ly_F lyc) 0 jj ltac:(lia)) as (G1 & G2 & G3 & G4 & _ & G6 & G7).
  change (Z.to_nat 0) with 0%nat in G1, G2, G3, G4.
  assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y) by exact G7.
  pose proof (A.ProgWorld_Fs.pw_F_above B lyc S2 W mem2 md2 HAR2) as HGT. unfold ASAN_GT in HGT.
  pose proof ASAN_CEIL_range as [CRa _]. unfold ASAN_CEIL in CRa.
  unfold in_app, kLowShadowBeg, kHighMemBeg, kFakeStackSize, ASAN_CEIL in HFapp.
  assert (Efr : fs_frame (ly_F lyc) 0%nat jj = ly_F lyc + fs_frame_off 0 jj) by (rewrite <- G3; reflexivity).
  assert (Efl : fs_flag (ly_F lyc) 0 jj = ly_F lyc + fs_flag_off 0 jj) by (rewrite <- G4; reflexivity).
  rewrite Efr, Efl, ESH in Ha. unfold kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *.
  pose proof (al_sep _ _ LAWS lyc S2 W mem2 md2 HAR2) as (SEP & _).
  rewrite Hfrs2, Eab in SEP. cbn [map] in SEP.
  split; [unfold YG0f.shadow_addr, YG0f.SHADOW_OFF in Ha; Z.div_mod_to_equations; lia|].
  split.
  { intros Hi. pose proof (img_bounds_of_in_img a Hi) as Hb.
    unfold YG0f.shadow_addr, YG0f.SHADOW_OFF in Ha. Z.div_mod_to_equations; lia. }
  split.
  - intros b m i Hb Hi Ea. subst a.
    pose proof (block_vs_F lyc S2 W mem2 md2 b m HAR2 ltac:(rewrite Eab; exact Hb)) as BF.
    unfold kFakeStackSize in BF.
    destruct Ha as [Ha | [Ha | Ha]].
    + lia.
    + lia.
    + unfold YG0f.shadow_addr, YG0f.SHADOW_OFF in Ha.
      pose proof (al_blocks _ _ LAWS lyc S2 W mem2 md2 b m HAR2 ltac:(rewrite Eab; exact Hb)) as (_ & B1 & B2 & B3 & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in B3. Z.div_mod_to_equations. lia.
  - intros cid pos Hin.
    destruct (YG0s.frame_facts B lyc S2 _ cid pos M2 ltac:(rewrite Hfrs2; right; exact Hin))
      as (Hc' & _ & _ & _ & _ & Hfo1' & Hfo2' & Hfo64' & Hfb64' & Hfbm' & _).
    unfold frame_rng, in_zr, frame_addr. cbn [fst snd]. unfold kFakeFramesOff, kFakeStackSize in *.
    change (2 ^ 20) with 1048576 in *.
    destruct (YG0s.frame_facts B lyc S2 _ cid pos M2 ltac:(rewrite Hfrs2; right; exact Hin))
      as (Hc2 & Hp2 & _).
    assert (Hne : fs_frame_off 0 jj + 64 <= fs_frame_off cid pos \/ fs_frame_off cid pos + fs_frame_bytes cid <= fs_frame_off 0 jj).
    { assert (Hd : (0, jj) <> (cid, pos)) by (intros E; rewrite E in Hnin; exact (Hnin Hin)).
      pose proof (YG0s.frames_apart 0 jj cid pos ltac:(lia) Hpos Hc2 Hp2 Hd) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. change (fs_frame_bytes 0) with 64 in D. exact D. }
    split.
    + destruct Ha as [Ha | [Ha | Ha]]; [lia | lia |].
      unfold YG0f.shadow_addr, YG0f.SHADOW_OFF in Ha. Z.div_mod_to_equations. lia.
    + destruct Ha as [Ha | [Ha | Ha]]; unfold YG0f.shadow_addr, YG0f.SHADOW_OFF in *;
        [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |].
      unfold page_aligned in HFal.
      clear - Ha Hne HFal Hfo64 Hfo64' Hfbm' Hfb64'.
      apply Z.mod_divide in HFal; [|lia]. apply Z.mod_divide in Hfo64; [|lia].
      apply Z.mod_divide in Hfo64'; [|lia]. apply Z.mod_divide in Hfbm'; [|lia].
      destruct HFal as [f Ef]. destruct Hfo64 as [o0 Eo0]. destruct Hfo64' as [o1 Eo1]. destruct Hfbm' as [b1 Eb1].
      rewrite Ef, Eo0, Eo1, Eb1 in *. Z.div_mod_to_equations. lia.
Qed.
End Glue.
(* ---------------------------------------------------------------------------------------------------------
   The spec's post, in S3's context re-opened after Section Glue (it uses Glue's lemmas). *)
Section S3x.
Context {fx : lib.Reusable.YK11.FPState}.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
Variable W : YA0n.world rsegs.
Hypothesis Hoff : off = ASAN_K.
Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis AC0 : asan_cells m.
Hypothesis SR0 : A.ShadowRwOn.shadow_rw_on (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
  (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K)
  (bv_unsigned sp).
Hypothesis Rp : 0 <= p < 2^64.
Hypothesis Rb : 0 <= b < 2^64.
Hypothesis Ro : 0 <= o < 2^64.
Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
  (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  RcBox.name_ok nb /\ bytes_at rsegs m (RcSynth.rname row) nb /\
  (bv_unsigned sp <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
  (o = 0 \/ o + 32 <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= o).
Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
  (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
Hypothesis AP : p <> 0 -> addressable m p 296.
Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  addressable m (RcSynth.rname row) (Z.of_nat (length nb)).
Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  fp_dj [(RcSynth.rname row, RcSynth.rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).
(* S2 / S3's footprint: every visible byte but the class-0 hint word [FS, FS + 8), which no stretch after the
   allocator call reads or writes; the footprint then keeps it (fsteps_keeps_hidden). *)
Let RNG : footprint := RNG_W (hidden_plus (YA0n.w_H W) FS).
Hypothesis Rimg : rng RNG 0x10000 0x5ee000.
Hypothesis Rwin : rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
Hypothesis Rwsh : A.Prog.reac_box_model_block_cF.sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K)
  REAC_BOX_MODEL_BLOCK_K.
Hypothesis Rtp88 : rng RNG (bv_unsigned tp - 88) 8.
Hypothesis Rtp8 : rng RNG (bv_unsigned tp - 8) 24.
Hypothesis Rtls : A.Prog.reac_box_model_block_cF.reac_box_model_block_tls_rng RNG m (bv_unsigned tp).
Hypothesis RFSh : rng RNG FS (fs_frame FS 0%nat 0 - FS).
Hypothesis RFSw : A.Prog.reac_box_model_block_cF.rng_ivls RNG (tl (fp_w [0%nat] FS)).
Hypothesis RFSsh : rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8).
Let Rby : lib.Lib.RngBytes.rng_bytes RNG := rng_bytes_RNG_W (hidden_plus (YA0n.w_H W) FS).
Hypothesis Rwsw : A.Prog.rng_asan.sh_word_rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
Hypothesis RP : p <> 0 -> rng RNG p 296.
Hypothesis RPs : p <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover RNG p 296.
Hypothesis RO : o <> 0 -> rng RNG o 32.
Hypothesis ROs : o <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover RNG o 32.
Hypothesis RN : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  rng RNG (RcSynth.rname row) (Z.of_nat (length nb)).
Hypothesis RNs : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  A.Prog.reac_box_model_block_cF.sh_cover RNG (RcSynth.rname row) (Z.of_nat (length nb)).
Hypothesis RJ13s : b = 2 -> A.Prog.reac_box_model_block_cF.sh_cover RNG JOIN_0013 32.
Hypothesis RJ14s : b = 1 -> A.Prog.reac_box_model_block_cF.sh_cover RNG JOIN_0014 32.

Notation FK := (A.Prog.reac_box_model_block_base.FK FS A).
Notation EB := (A.Prog.reac_box_model_block_base.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
Notation Q0 := (C_ON.reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
                  p b o FS row nb).
Let bmb_at_rel := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.bmb_at_rel).
Let bmb_after_rel := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.bmb_after_rel).
Let bmb_rel_step := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.bmb_rel_step).
Let epi_RFSfl_F := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.epi_RFSfl_F).
Let epi_post_F := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.epi_post_F).
Let epi_pre_F := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.epi_pre_F).
Let bmb_KR := ltac2:(inst_exact @A.Prog.reac_box_model_block_epiF.bmb_KR).

Context {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws AB1v.tfibsegs B.
Hypothesis ASF : astack_free_law AB1v.tfibsegs B.

Let bmb_WR := ltac2:(inst_exact @bmb_WR).

(* The spec's post from what the tail hands over. *)
Lemma bmb_post : forall STK sp0 (FPj : list (Z * Z)) ly0 S0 (W0x : YA0n.world rsegs) mem0 md0 own lyc Sc S2 k
    (regs : bvmap 5 word) (mem2 memc0 : word -> option byte) (mdc md2x : Model) jj ms3 md3 st3,
  ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FPj ly0 S0 W0x mem0 md0 own lyc (stack_free_state 0 jj S2) W
    (ms_mem ms3) md3 k ->
  Q0 st3 -> ms_rel rsegs ms3 st3 -> ro_same rsegs mem2 (ms_mem ms3) ->
  munch (bmb_WR jj) mem2 (ms_mem ms3) ->
  frames S2 = (0, jj) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  ly_F lyc = FS -> m = normalize rsegs mem2 ->
  lib.Reusable.YK11.getr regs 1 = ra -> lib.Reusable.YK11.getr regs 2 = sp ->
  lib.Reusable.YK0s.ret_ok ra -> F = lib.Reusable.YK11.fp_regs -> fc = lib.Reusable.YK11.fp_csr ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 2) = sp ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 3) = gp ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 4) = tp ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 8) = s0 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 9) = s1 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 18) = s2 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 19) = s3 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 20) = s4 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 21) = s5 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 22) = s6 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 23) = s7 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 24) = s8 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 25) = s9 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 26) = s10 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 27) = s11 ->
  (forall x, o <> 0 -> o <= x < o + 32 -> YA0n.w_H W (Z_to_bv 64 x) = false) ->
  (forall x, o <> 0 -> o <= x < o + 32 -> ~ in_img AB1v.tfibsegs x) ->
  0 <= o -> o + 32 <= 2 ^ 64 ->
  (* for tcj_kept *)
  model_laws (as_universe B) ->
  AR AB1v.tfibsegs B lyc Sc W memc0 mdc -> AR AB1v.tfibsegs B lyc S2 W mem2 md2x ->
  lib.Reusable.YM05.alloc_ceiling <= bv_unsigned sp - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK ->
  acall_kept AB1v.tfibsegs B lyc Sc W memc0 W mem2 (bv_unsigned sp - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK)
    (bv_unsigned sp) (fun _ => False) ->
  0 <= jj < fs_M 0%nat -> ~ In (0, jj) (frames Sc) ->
  (forall a, bv_unsigned sp - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK <= a < bv_unsigned sp ->
     apresent (YA0n.w_H W) (ms_mem ms3) a) ->
  (p <> 0 -> o <> 0 -> forall a, o <= a < o + 32 -> lib.Reusable.YM05.alloc_ceiling <= a ->
     ~ (bv_unsigned sp - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK <= a < bv_unsigned sp) ->
     apresent (YA0n.w_H W) (ms_mem ms3) a) ->
  (o <> 0 -> bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK) ->
  (p <> 0 -> length row = 296%nat) ->
  C_reac_box_model_block.treac_box_model_block_post B STK sp0 FPj ly0 S0 W0x mem0 md0 own lyc Sc W memc0 k
    regs p b o row nb W (mkCfg ms3 md3).
Proof.
  intros STK sp0 FPj ly0 S0 W0x mem0 md0 own lyc Sc S2 k regs mem2 memc0 mdc md2x jj ms3 md3 st3
    HJ3 HQ0 Hrel3 Hros3 HMU3 Hfrs2 Eab EFS Em Era Esp Hret EFr Efcs E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 Hvis Hni Ho0 Ho1 ML HAR HAR2 Hceil HK2 Hjj Hnin HWf HOf Hosep Hlen.
  destruct HQ0 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                   & m' & Est3 & Hmem & _).
  pose proof Hrel3 as (Eregs3 & Efr3 & Epc3 & Esv3 & Erv3 & Efc3 & Ero3 & HMR3).
  rewrite Est3 in Eregs3, Epc3, Efr3, Esv3, Erv3, Efc3, Ero3.
  unfold C_reac_box_model_block.treac_box_model_block_post.
  exists lyc, (stack_free_state 0 jj S2), (ms_regs ms3), (ms_mem ms3), md3.
  split.
  { destruct ms3 as [R3 F3 pc3 sv3 rv3 m3 ro3]. simpl in Eregs3, Epc3, Efr3, Esv3, Erv3, Efc3, Ero3 |- *.
    unfold lib.Reusable.YK11.mkst. rewrite Efr3, Esv3, Erv3, Efc3, Ero3.
    rewrite Epc3, (ret_pc_of_ret_ok ra Hret), <- Era, EFr, Efcs. reflexivity. }
  split.
  { replace (k + C_reac_box_model_block.EV_BMB) with k by (unfold C_reac_box_model_block.EV_BMB; lia).
    exact HJ3. }
  split.
  { unfold aregs_preserved. intros r Hr. rewrite Eregs3.
    unfold acallee_saved in Hr.
    destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | Hr]]]]]; [subst r; match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end .. |].
    destruct (Z.eq_dec r 18) as [->|N18]; [match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end|].
    destruct (Z.eq_dec r 19) as [->|N19]; [match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end|].
    destruct (Z.eq_dec r 20) as [->|N20]; [match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end|].
    destruct (Z.eq_dec r 21) as [->|N21]; [match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end|].
    destruct (Z.eq_dec r 22) as [->|N22]; [match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end|].
    destruct (Z.eq_dec r 23) as [->|N23]; [match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end|].
    destruct (Z.eq_dec r 24) as [->|N24]; [match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end|].
    destruct (Z.eq_dec r 25) as [->|N25]; [match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end|].
    destruct (Z.eq_dec r 26) as [->|N26]; [match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end|].
    assert (E27r : r = 27) by (clear - Hr N18 N19 N20 N21 N22 N23 N24 N25 N26; Zify.zify; xlia zchecker).
    subst r; match goal with E : lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) = _ |- _ = lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) => rewrite E; reflexivity end. }

  split.
  { pose proof (am_wf _ _ _ _ (proj1 HAR2)) as HWF.
    destruct (ml_stack_free _ ML S2 0 jj HWF ltac:(rewrite Hfrs2; left; reflexivity)) as (_ & l1 & l2 & E1f & E2f).
    rewrite E2f. rewrite Hfrs2 in E1f.
    destruct l1 as [|f l1'].
    - cbn in E1f. injection E1f as E1f. rewrite E1f. reflexivity.
    - exfalso. cbn in E1f. injection E1f as <- E1'. apply Hnin. rewrite E1'. apply in_or_app. right. left. reflexivity. }
  split; [transitivity (ablocks B lyc S2); [unfold ablocks; rewrite blocks_stack_free_state; reflexivity | exact Eab]|].
  (* the caller's kept bytes: what the tail wrote is the window, o, or side-stack bytes apart from the caller *)
  assert (CLASS : forall (E : Z -> Prop), (p <> 0 -> o <> 0 -> forall a, o <= a < o + 32 -> E a) ->
            forall a, 0 <= a < 2 ^ 64 -> ~ outside (bmb_WR jj) a ->
            (bv_unsigned sp - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK <= a < bv_unsigned sp) \/ E a \/
            (a < lib.Reusable.YM05.alloc_ceiling /\ ~ in_img AB1v.tfibsegs a /\
             (forall b0 m0 i, In (b0, m0) (ablocks B lyc Sc) -> 0 <= i < req_size m0 -> a <> b0 + i) /\
             (forall cid pos, In (cid, pos) (frames Sc) ->
                ~ in_zr a (frame_rng lyc (cid, pos)) /\
                ~ in_zr a (YG0f.shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))).
  { intros E HEo a Ha Hout.
    assert (HIN : (bv_unsigned sp - 4272 <= a < bv_unsigned sp) \/
                  (fs_flag FS 0 jj <= a < fs_flag FS 0 jj + 1 \/ fs_frame FS 0%nat jj <= a < fs_frame FS 0%nat jj + 64 \/
                   shadow_addr (fs_frame FS 0%nat jj) <= a < shadow_addr (fs_frame FS 0%nat jj) + 8) \/
                  (p <> 0 /\ o <> 0 /\ o <= a < o + 32)).
    { unfold bmb_WR in Hout. try (cbv delta [reac_box_model_block_glue.BmbGlue.bmb_WR] beta in Hout).
      cbn [app] in Hout.
      apply not_outside_cons in Hout as [Hw | Hout]; [left; exact Hw|].
      apply not_outside_cons in Hout as [Hf | Hout]; [right; left; left; exact Hf|].
      apply not_outside_cons in Hout as [Hf | Hout]; [right; left; right; left; exact Hf|].
      apply not_outside_cons in Hout as [Hf | Hout]; [right; left; right; right; exact Hf|].
      case_eq ((p =? 0) || (o =? 0)); intros EB'; rewrite EB' in Hout.
      - exfalso. apply Hout. exact I.
      - apply orb_false_iff in EB' as [EP EO]. apply Z.eqb_neq in EP. apply Z.eqb_neq in EO.
        apply not_outside_cons in Hout as [Ho | Hout]; [right; right; split; [exact EP | split; [exact EO | exact Ho]]|].
        exfalso. apply Hout. exact I. }
    destruct HIN as [Hw | [Hs | (Hp & Ho & Hr)]].
    - left. unfold C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK, C_reac_box_model_block.BUILD_DT1_SINGLE_STK, ESTACK.
      lia.
    - right; right. rewrite <- EFS in Hs.
      exact (side_class B LAWS lyc Sc S2 W mem2 md2x jj a HAR2 Hfrs2 Eab Hjj Hnin Hs).
    - right; left. exact (HEo Hp Ho a Hr). }
  replace (spZ regs) with (bv_unsigned sp) by (unfold spZ; rewrite Esp; reflexivity).
  case_eq ((p =? 0) || (o =? 0)); intros EB.
  - cbv iota.
    split; [rewrite Eregs3; rewrite EB; reflexivity|].
    apply (tcj_of_kept_munch B LAWS lyc Sc W memc0 mdc mem2 (ms_mem ms3) (bv_unsigned sp)
             C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK (fun _ => False) (bmb_WR jj) HAR Hceil HK2 HMU3).
    + apply CLASS. intros Hp Ho. apply orb_true_iff in EB as [EB | EB]; apply Z.eqb_eq in EB; contradiction.
    + intros a Fa; destruct Fa.
    + intros a Fa; destruct Fa.
    + exact HWf.
  - cbv iota.
    rewrite EB in Hmem.
    split; [rewrite Eregs3; rewrite EB; reflexivity|].
    apply orb_false_iff in EB as [EP EO]. apply Z.eqb_neq in EP. apply Z.eqb_neq in EO.
    split.
    +
      destruct Hmem as (Hbo & _).
      pose proof (proj1 HMR3) as HN3.
      apply (garr8_of_bytes_at W (ms_mem ms3) o (RcSynth.synth row b nb)).
      * rewrite Est3 in HN3. cbn [ms_mem] in HN3. apply (bytes_at_agree m'); [exact Hbo|].
        intros i Hi. symmetry. apply HN3.
      * intros x Hx. apply (Hvis x EO). rewrite (RcSynthLib.rs_synth_len row b nb (Hlen EP)) in Hx. lia.
      * intros x Hx. apply (Hni x EO). rewrite (RcSynthLib.rs_synth_len row b nb (Hlen EP)) in Hx. lia.
      * exact Ho0.
      * rewrite (RcSynthLib.rs_synth_len row b nb (Hlen EP)). lia.
    + apply (tcj_of_kept_munch B LAWS lyc Sc W memc0 mdc mem2 (ms_mem ms3) (bv_unsigned sp)
               C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK (fun a => o <= a < o + 32) (bmb_WR jj) HAR Hceil HK2
               HMU3).
      * apply CLASS. intros _ _ a Ha. exact Ha.
      * intros a Ha. exact (Hni a EO Ha).
      * intros a Ha Hc Hn. exact (HOf EP EO a Ha Hc Hn).
      * exact HWf.
Qed.

Let bmb_from_ret := ltac2:(inst_exact @bmb_from_ret).

(* The whole tail of the glue: from the allocator's return to the spec's post. *)
Lemma bmb_body : wx_segs_nowrap rsegs ->
  forall (mem2 : word -> option byte) (md2 : Model) (jj : Z)
         (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
         STK sp0 (FPj : list (Z * Z)) ly0 S0 (W0x : YA0n.world rsegs) mem0 md0 own lyc Sc S2 k
         (regs : bvmap 5 word) (memc0 : word -> option byte) (mdc : Model),
  m = normalize rsegs mem2 -> ro_agree rsegs mem2 ->
  0 <= jj < fs_M 0%nat ->
  bytes_at rsegs m (fs_flag FS 0 jj) [Z_to_bv 8 1] ->
  bytes_at rsegs m (fs_frame FS 0 jj + 56) (le8 (Z_to_bv 64 (fs_flag FS 0 jj))) ->
  bytes_at rsegs m (shadow_addr (fs_frame FS 0 jj)) (repeat (Z_to_bv 8 0) 8) ->
  addressable m (fs_frame FS 0 jj) 64 ->
  stk rsegs m (fs_frame FS 0 jj) (fs_frame FS 0 jj + 64) ->
  rw_cells rsegs m (bv_unsigned sp + -104)
    (A.Prog.reac_box_model_block_base.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  ajournal (SK := SK) AB1v.tfibsegs B STK sp0 FPj ly0 S0 W0x mem0 md0 ((0, jj) :: own) lyc S2 W mem2 md2 k ->
  FS = ly_F lyc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside (bmb_WR jj) a ->
     awr_byte STK sp0 FPj (ablocks B ly0 S0) (ablocks B lyc S2) lyc ((0, jj) :: own) a \/ a = flag_addr lyc 0 jj) ->
  (* what bmb_post needs *)
  model_laws (as_universe B) ->
  AR AB1v.tfibsegs B lyc Sc W memc0 mdc -> AR AB1v.tfibsegs B lyc S2 W mem2 md2 ->
  lib.Reusable.YM05.alloc_ceiling <= bv_unsigned sp - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK ->
  acall_kept AB1v.tfibsegs B lyc Sc W memc0 W mem2
    (bv_unsigned sp - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK) (bv_unsigned sp) (fun _ => False) ->
  frames S2 = (0, jj) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc -> ~ In (0, jj) (frames Sc) ->
  lib.Reusable.YK11.getr regs 1 = ra -> lib.Reusable.YK11.getr regs (Z_to_bv 5 2) = sp ->
  lib.Reusable.YK11.getr regs 2 = sp -> lib.Reusable.YK0s.ret_ok ra ->
  F = lib.Reusable.YK11.fp_regs -> fc = lib.Reusable.YK11.fp_csr ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 3) = gp -> lib.Reusable.YK11.getr regs (Z_to_bv 5 4) = tp ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 8) = s0 -> lib.Reusable.YK11.getr regs (Z_to_bv 5 9) = s1 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 18) = s2 -> lib.Reusable.YK11.getr regs (Z_to_bv 5 19) = s3 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 20) = s4 -> lib.Reusable.YK11.getr regs (Z_to_bv 5 21) = s5 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 22) = s6 -> lib.Reusable.YK11.getr regs (Z_to_bv 5 23) = s7 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 24) = s8 -> lib.Reusable.YK11.getr regs (Z_to_bv 5 25) = s9 ->
  lib.Reusable.YK11.getr regs (Z_to_bv 5 26) = s10 -> lib.Reusable.YK11.getr regs (Z_to_bv 5 27) = s11 ->
  (forall x, o <> 0 -> o <= x < o + 32 -> YA0n.w_H W (Z_to_bv 64 x) = false) ->
  (forall x, o <> 0 -> o <= x < o + 32 -> ~ in_img AB1v.tfibsegs x) ->
  0 <= o -> o + 32 <= 2 ^ 64 -> (p <> 0 -> length row = 296%nat) ->
  (o <> 0 -> bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK) ->
  (o <> 0 -> forall a, o <= a < o + 32 -> apresent (YA0n.w_H W) memc0 a) ->
  bv_unsigned sp <= 2 ^ 64 ->
  YA0n.SRr rsegs W
    (mkCfg (MS (mkR x1' (Z_to_bv 64 A) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                  (Z_to_bv 64 (fs_frame FS 0 jj)) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                  (Z_to_bv 64 b) s7 s8 (wa off) s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x85bbc) fc None mem2 (seg_rom rsegs)) md2)
    (C_reac_box_model_block.treac_box_model_block_post B STK sp0 FPj ly0 S0 W0x mem0 md0 own lyc Sc W memc0 k
       regs p b o row nb).
Proof.
  intros Hwx mem2 md2 jj x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' STK sp0 FPj ly0 S0 W0x mem0 md0
    own lyc Sc S2 k regs memc0 mdc Em Hro2 Hjj Hfl H56 Hsh Had Hst Hsv HJ2 EFS Hawr ML HAR HAR2 Hceil HK2 Hfrs2 Eab
    Hnin Era E2 Esp Hret EFr Efcs E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 Hvis Hni Ho0 Ho1 Hlen Hosep HOm Hsp64.
  apply (bmb_from_ret Hwx mem2 md2 jj x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' STK sp0 FPj ly0 S0
           W0x mem0 md0 own lyc S2 k _ Em Hro2 Hjj Hfl H56 Hsh Had Hst Hsv HJ2 EFS Hawr).
  intros ms3 md3 st3 HJ3 HQ0 Hrel3 Hros3 HMU3 HPRES.
  pose proof HK2 as (_ & _ & _ & _ & K5 & K6).
  pose proof (lib.Reusable.YM05.alloc_ceiling_value) as (Hcv & _).
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hstk3 & _).
  pose proof Hstk3 as (_ & _ & Hceil3 & Hslo3 & Hshi3 & _).
  apply YA0n.SRr_ret.
  refine (bmb_post STK sp0 FPj ly0 S0 W0x mem0 md0 own lyc Sc S2 k regs mem2 memc0 mdc md2 jj ms3 md3 st3
           HJ3 HQ0 Hrel3 Hros3 HMU3 Hfrs2 Eab (eq_sym EFS) Em Era Esp Hret EFr Efcs E2 E3 E4 E8 E9 E18 E19 E20 E21
           E22 E23 E24 E25 E26 E27 Hvis Hni Ho0 Ho1 ML HAR HAR2 Hceil HK2 Hjj Hnin _ _ Hosep Hlen).
  - intros a Ha. apply (HPRES a ltac:(lia)). exact (K6 a Ha).
  - intros Hp Ho a Ha Hc Hns. apply (HPRES a ltac:(lia)).
    exact (K5 a ltac:(lia) Hns (HOm Ho a Ha)).
Qed.
End S3x.
End BmbGlue.
