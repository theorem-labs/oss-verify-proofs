(* The post side of the adapter (G3, the write posts): a lib/B/Bz body walk run on the cleaned store
   (RtBzClean.clean), read at a call site of this tree's contracts as RtDefs.art_post with a write set E.

   omx-clap-core/fuzz_manifest's rt_post_ro (RtBzHStr.v) is the read-only case: a call that writes nothing but its
   stack window. Four of the five entries lifted here (strcpy, strcat, atoi, strtol) write outside that window - the
   destination, *endptr, errno - and our art_post states the bytes of the store they return, so the window argument is
   generalised to "the window and E":
   - art_post_clean: the walk's end state msc gives art_post, with the caller choosing E and Q; what the caller
     must prove of Q is stated over an abstract store with two facts: outside the window and E the caller's view
     is kept, and on E the view is the walk's own store, read through the walks' reader (BM.mrd).
   - the store only grows along a walk (evt_grows, from YI04.msteps_mem_grows), which is what keeps every visible
     byte visible and every present byte present across the call - the two clauses art_post and the donor's frame
     law (YG0d.v:447 al_frame) ask for.
   Each byte of E must be outside the model's owned set (awrite_ok gives that for a destination), not a dropped
   address (RtBzClean.Dc: the cleaned store holds nothing at a read-only image address, so a walk cannot write
   there) and not hidden (RtBzAdapt.wH_false_of_writable gives that from awrite_ok). *)
(* The image-B twin of lib/A/Rt/RtBzAdaptP.v, for fuzz_command.asan-ubsan: lib/B/Bz for lib/A/Bz, B's per-binary
   files and lib/B/Rt's RtDefs and twins (RtBzHBase and RtBzHStr included). No lib/A module is required. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YK1b YP03 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtBzHBase RtBzHStr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtBzLift RtBzPre RtBzClean RtBzAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtBzBridge.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib.Exec.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BzX := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib.Exec.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the store a walk returns holds every byte the store it started from held *)
Lemma evt_grows : forall (Q : machine_state -> Prop) ms,
  BzX.evt BI.asegs Q ms ->
  BzX.evt BI.asegs (fun ms' => Q ms' /\ YK1b.mem_grows (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros Q ms (ms' & Hs & HQ). exists ms'. split; [exact Hs|]. split; [exact HQ|].
  apply (YI04.msteps_mem_grows tfibsegs). apply RtBzBridge.bz_msteps_tfib. exact Hs.
Qed.

End g.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* ---- the post of a cleaned walk, with a write set ---- *)
Theorem art_post_clean : forall (stk K : Z) ly S (W : world tfibsegs) regs mem md
  (E : Z -> Prop) (Q : bvmap 5 word -> (word -> option byte) -> Prop) msc ms' model',
  ecall_pre_stk tfibsegs B stk ly S W regs mem md -> 0 <= K <= stk ->
  hclean Dc msc ->
  R6.ms_eqv (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' ->
  same_but_materialized md model' ->
  ms_pc_val msc = LMS.ret_pc (getr regs 1) -> ms_fregs msc = fp_regs -> ms_svc_pending msc = None ->
  ms_resv msc = None -> ms_fcsr msc = fp_csr -> ms_rom msc = seg_rom tfibsegs ->
  (forall r, acallee_saved r -> getr (ms_regs msc) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (* the walk changed only its stack window and E *)
  (forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) -> ~ E (bv_unsigned x) ->
     ms_mem msc x = clean (mrestrict (w_H W) mem) x) ->
  (forall a, spZ regs - K <= a < spZ regs -> ms_mem msc (Z_to_bv 64 a) <> None) ->
  YK1b.mem_grows (clean (mrestrict (w_H W) mem)) (ms_mem msc) ->
  (* E: outside the model's owned set, a byte of the store and not a dropped address *)
  (forall a, E a -> ~ aowned B ly S a /\ 0 <= a < 2 ^ 64 /\ Dc (Z_to_bv 64 a) = false /\
             w_H W (Z_to_bv 64 a) = false) ->
  (* what the caller must prove of the registers and the store the entry returns *)
  (forall regs' mem',
     (forall r : bv 5, getr regs' r = getr (ms_regs msc) r) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk stk regs a -> ~ E a ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
     (forall a, E a ->
        aview tfibsegs (w_H W) mem' a =
        option_map (fun b : byte => bv_unsigned b) (BM.mrd BI.asegs (ms_mem msc) (BM.wa a))) ->
     Q regs' mem') ->
  art_post tfibsegs B stk ly S W regs mem md E Q W
    (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros stk K ly S W regs mem md E Q msc ms' model' HPRE HK Hcl Heqv Hsbm
    P0 F0 S0 R0 C0 RO0 KEEP MOUT MIN GROW HE HQ.
  destruct HPRE as (HEP & Hslo & HpresS).
  pose proof HEP as (HAR & Hra & _ & Hlo & Hshi & _ & _ & _).
  set (H := w_H W) in *.
  set (m0 := mrestrict H mem) in *.
  set (ms0 := unrestrict Dc m0 msc) in *.
  pose proof Heqv as (_ & _ & _ & _ & _ & _ & Emem & _).
  set (mem' := munrestrict H mem (ms_mem ms')) in *.
  (* the store of the walk's end state, put back into the caller's *)
  assert (MS0 : forall x : word, ms_mem ms0 x = if Dc x then m0 x else ms_mem msc x).
  { intros x. unfold ms0. rewrite unrestrict_mem. reflexivity. }
  assert (MEM' : forall x : word, mem' x = if H x then mem x else ms_mem ms0 x).
  { intros x. unfold mem'. rewrite <- Emem. reflexivity. }
  (* outside the window and E the walk's store is the caller's *)
  assert (OUT0 : forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) -> ~ E (bv_unsigned x) ->
            ms_mem ms0 x = m0 x).
  { intros x Hx HEx. rewrite MS0. destruct (Dc x) eqn:ED; [reflexivity|].
    rewrite (MOUT x Hx HEx). unfold clean, mrestrict. rewrite ED. reflexivity. }
  assert (OUTM : forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) -> ~ E (bv_unsigned x) ->
            mem' x = mem x).
  { intros x Hx HEx. rewrite MEM'. destruct (H x) eqn:EH; [reflexivity|].
    rewrite (OUT0 x Hx HEx). unfold m0, mrestrict. rewrite EH. reflexivity. }
  (* the store only grows, so nothing visible or present goes away *)
  assert (GR0 : forall x : word, m0 x <> None -> ms_mem ms0 x <> None).
  { intros x Hx. rewrite MS0. destruct (Dc x) eqn:ED; [exact Hx|].
    apply GROW. unfold clean, mrestrict. rewrite ED. exact Hx. }
  assert (VIS : forall a, aview tfibsegs H mem a <> None -> aview tfibsegs H mem' a <> None).
  { intros a Hv. rewrite (RtBzLift.aview_mod H mem' a). rewrite (RtBzLift.aview_mod H mem a) in Hv.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *.
    unfold aview, mbyte, mrestrict in Hv |- *.
    destruct (H (Z_to_bv 64 a')) eqn:EH.
    - exact Hv.
    - destruct (mem (Z_to_bv 64 a')) as [b|] eqn:EM.
      + assert (HN : ms_mem ms0 (Z_to_bv 64 a') <> None)
          by (apply GR0; unfold m0, mrestrict; rewrite EH, EM; discriminate).
        rewrite (MEM' (Z_to_bv 64 a')), EH.
        destruct (ms_mem ms0 (Z_to_bv 64 a')) as [c|] eqn:EC; [cbn; discriminate|].
        exfalso. exact (HN eq_refl).
      + rewrite (MEM' (Z_to_bv 64 a')), EH.
        destruct (ms_mem ms0 (Z_to_bv 64 a')) as [c|] eqn:EC; [cbn; discriminate|].
        cbn in Hv |- *. exact Hv. }
  assert (PRS : forall a, apresent H mem a -> apresent H mem' a).
  { intros a [Hh [b Hb]]. split; [exact Hh|].
    rewrite (MEM' (Z_to_bv 64 a)), Hh.
    assert (HN : ms_mem ms0 (Z_to_bv 64 a) <> None)
      by (apply GR0; unfold m0, mrestrict; rewrite Hh, Hb; discriminate).
    destruct (ms_mem ms0 (Z_to_bv 64 a)) as [c|] eqn:EC; [exists c; reflexivity|].
    exfalso. exact (HN eq_refl). }
  (* outside the window and E the caller's view is kept *)
  assert (AVOUT : forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk stk regs a -> ~ E a ->
            aview tfibsegs H mem' a = aview tfibsegs H mem a).
  { intros a Ha Hs HEa. apply RtBzLift.aview_same.
    apply OUTM; rewrite unsigned_lit_small by lia; [unfold ascratch_stk in Hs; lia | exact HEa]. }
  assert (AVOWN : forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a ->
            aview tfibsegs H mem' a = aview tfibsegs H mem a).
  { intros a Ha Hown. apply AVOUT; [exact Ha | | intros HEa; exact (proj1 (HE a HEa) Hown)].
    intros Hsc. unfold ascratch_stk in Hsc.
    exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown). }
  (* on E the entry's view is the walk's own store *)
  assert (AVE : forall a, E a ->
            aview tfibsegs H mem' a =
            option_map (fun b : byte => bv_unsigned b) (BM.mrd BI.asegs (ms_mem msc) (BM.wa a))) .
  { intros a HEa. destruct (HE a HEa) as (_ & Ha & EDc & EHh).
    unfold aview. rewrite <- RtBzPre.mrd_mbyte. f_equal.
    unfold BM.mrd, BM.wa, mrestrict. rewrite EHh.
    rewrite (MEM' (Z_to_bv 64 a)), EHh, (MS0 (Z_to_bv 64 a)), EDc. reflexivity. }
  (* AR survives the call *)
  destruct (same_but_materialized_frame md model' Hsbm)
    as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
  assert (HAR' : AR tfibsegs B ly S W mem' model').
  { apply (al_frame _ _ LAWS ly S W mem md _ model' HAR);
      [exact AVOWN | exact VIS | exact E1 | exact E2 | exact E3 |].
    intros a _ Hh. rewrite (MEM' (w64 a)).
    replace (H (w64 a)) with true by (symmetry; exact Hh). reflexivity. }
  unfold art_post. split; [reflexivity|].
  exists (ms_regs ms'), mem', model'.
  split.
  { unfold cfg_at. f_equal.
    exact (RtBzLift.unrestrict_ret regs H mem ms0 ms' Heqv Hra P0 F0 S0 R0 C0 RO0). }
  split; [exact HAR'|].
  split; [intros r Hr; rewrite (RtBzLift.ms_eqv_getr ms0 ms' _ Heqv); exact (KEEP r Hr)|].
  split; [exact Hsbm|].
  split; [exact (HQ (ms_regs ms') mem'
                   (fun r => RtBzLift.ms_eqv_getr ms0 ms' r Heqv) AVOUT AVE)|].
  split; [intros a Ha Hs HEa; exact (AVOUT a Ha Hs HEa)|].
  split; [exact PRS|].
  intros a Ha. apply PRS. exact (HpresS a Ha).
Qed.

(* the read-only case: a call that writes nothing but its stack window *)
Theorem art_post_ro_clean : forall (stk K : Z) ly S (W : world tfibsegs) regs mem md
  (Q : bvmap 5 word -> (word -> option byte) -> Prop) msc ms' model',
  ecall_pre_stk tfibsegs B stk ly S W regs mem md -> 0 <= K <= stk ->
  hclean Dc msc ->
  R6.ms_eqv (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' ->
  same_but_materialized md model' ->
  ms_pc_val msc = LMS.ret_pc (getr regs 1) -> ms_fregs msc = fp_regs -> ms_svc_pending msc = None ->
  ms_resv msc = None -> ms_fcsr msc = fp_csr -> ms_rom msc = seg_rom tfibsegs ->
  (forall r, acallee_saved r -> getr (ms_regs msc) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) ->
     ms_mem msc x = clean (mrestrict (w_H W) mem) x) ->
  (forall a, spZ regs - K <= a < spZ regs -> ms_mem msc (Z_to_bv 64 a) <> None) ->
  YK1b.mem_grows (clean (mrestrict (w_H W) mem)) (ms_mem msc) ->
  (forall regs' mem',
     (forall r : bv 5, getr regs' r = getr (ms_regs msc) r) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk stk regs a ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
     Q regs' mem') ->
  art_post tfibsegs B stk ly S W regs mem md (fun _ => False) Q W
    (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros stk K ly S W regs mem md Q msc ms' model' HPRE HK Hcl Heqv Hsbm
    P0 F0 S0 R0 C0 RO0 KEEP MOUT MIN GROW HQ.
  apply (art_post_clean stk K ly S W regs mem md (fun _ => False) Q msc ms' model' HPRE HK Hcl Heqv Hsbm
           P0 F0 S0 R0 C0 RO0 KEEP);
    [intros x Hx _; exact (MOUT x Hx) | exact MIN | exact GROW | intros a Hf; destruct Hf |].
  intros regs' mem' HR HO _. exact (HQ regs' mem' HR (fun a Ha Hs => HO a Ha Hs ltac:(intros Hf; destruct Hf))).
Qed.

End p.
