(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_ubjson_encoder/lib/S8/AsanAcct.v, with its module paths and module names changed; 408 of its 528 lines of code are new or changed and 1138 lines of the source are left out. *)
(* A lib/A/Bz body walk run on the CLEANED store, carried back to the real one.
   Every Bz walk takes `Mem.mem_inv asegs m` (A/Bz/Lib/Mem.v:96-102): the store holds no byte at a read-only image
   address and none at or above 2^47.  AR does not say that of the real store (it reads memory only through `aview`).
   So the walk is run on `clean m`, the store with every entry at such an address dropped (`clean = mrestrict Dc`),
   where mem_inv holds by construction (mem_inv_clean), and its run is carried back:
   - a store at a dropped address faults on the cleaned store (no entry there, and the image gives no writable byte:
     the address is read-only or outside every segment), so a successful cleaned run writes no dropped address;
   - a read at a dropped address either faults on the cleaned store (at or above 2^47 no segment supplies a byte) or
     reads the image byte, which is what the real store reads there too: `rom_eq` (every read-only address reads as
     the image byte), from the contracts' rom_viewN (the non-owned read-only bytes) and rom_viewO (the owned ones);
   - fetch never reads the store: fm.asan has no writable and executable segment.
   The step-level proof follows lib/Reusable/YK04.v (step_accesses_restrict for the lazy-page hidden set), with the
   read side by value agreement (`ragree`) instead of avoidance.  Entry point: srr_of_clean_bz; post side:
   clean_window; premise side: mem_inv_clean, bytes_at_clean, ro_cells_clean, stk_clean, chk_ok_clean. *)
(* Relocated to plugin-hostd/fuzz_command from omx-clap-core/fuzz_manifest's program-free split
   (proofs/omx-clap-core/fuzz_manifest/lib/A/FMbz_clean.v): module paths, TfibSyms renamed SegBSyms (this image's
   per-binary record, B/YF0m.v); the decided image facts (asegs_no_wx, Dc_above, errno_not_ro) are recomputed on this
   image; the unused FMupoison import left out. *)
(* The image-B twin of lib/A/Rt/RtBzClean.v, for fuzz_command.asan-ubsan: lib/B/Bz (the image-B Bz kit, whose Lib
   layer is a copy with ImageA.asegs = the ASan+UBSan segments) for lib/A/Bz, B/YB1v, YF0m, YF0x for A's per-binary
   files, the lib/B/Rt twins of RtBzHBase, RtBzHStr, RtBzLift and RtBzStr, and lib/B/Img0.v's rsegs where the A
   file names lib/A/Img0.v's; the decided image facts are recomputed on B. No lib/A module is required. *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YP03 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YK06 YM05.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtBzHBase RtBzHStr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtBzLift.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtBzStr.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Common.PropExec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Step.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.Shadow.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Img0.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.MState.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".

Module R6 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Regs6ss.
Module BPE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Common.PropExec.
Module BzE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Exec.
Module BzI := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.ImageA.
Module BM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Mem.
Module BC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Cells.
Module BS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Step.
Module BF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Frame.
Module BSh := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.Shadow.
Module BQ := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_qck.
Module LEX := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Exec.

(* lib/Lib's walk relation is the B kit's: one step body, one image (the converse of RtBzLift.bz_evt_lib) *)
Lemma lib_evt_bz : forall (Q : machine_state -> Prop) ms, LEX.evt Img0.rsegs Q ms -> BzE.evt BzI.asegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [|exact HQ]. clear HQ.
  induction H as [ms | ms ms1 ms2 Hs _ IH]; [apply BzE.msteps_refl | eapply BzE.msteps_cons; [exact Hs | exact IH]].
Qed.

(* ---- the step, for any dropped set D the image never lets a store write ---- *)
Section g.
Open Scope bv_scope.
Variable segs : list Segment.
Variable D : word -> bool.
(* no dropped address is a writable image byte *)
Hypothesis HND : forall a, D a = true ->
  match find_segment segs (bv_unsigned a) 1 with Some sg => seg_writable sg = false | None => True end.
(* no segment is writable and executable, so fetch reads the image only *)
Hypothesis HNX : forall sg, In sg segs -> seg_executable sg && seg_writable sg = false.

(* the byte a load reads: the store's, else the image's *)
Definition rd1 (m : word -> option byte) (a : word) : option byte :=
  match m a with Some b => Some b | None => YK11.seg_rom segs a end.

(* at a dropped address the image supplies, the store holds nothing or the image byte *)
Definition ragree (m : word -> option byte) : Prop :=
  forall a b, D a = true -> YK11.seg_rom segs a = Some b -> m a = None \/ m a = Some b.

Lemma ragree_ext : forall m m', (forall x, D x = true -> m' x = m x) -> ragree m -> ragree m'.
Proof. intros m m' E HR x b Hx Hb. rewrite (E x Hx). exact (HR x b Hx Hb). Qed.

Lemma rd1_clean : forall m a b, ragree m -> rd1 (mrestrict D m) a = Some b -> rd1 m a = Some b.
Proof.
  intros m a b HR E. unfold rd1, mrestrict in E. unfold rd1.
  destruct (D a) eqn:Ha; [|exact E].
  destruct (HR a b Ha E) as [E'|E']; rewrite E'; [exact E | reflexivity].
Qed.

Lemma ov_read_cons : forall m a n,
  ov_read_bytes segs m a (S n) =
  match rd1 m a with
  | Some b => match ov_read_bytes segs m (a + 1) n with Some r => Some (b :: r) | None => None end
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma ov_read_bytes_clean : forall n m a bs, ragree m ->
  ov_read_bytes segs (mrestrict D m) a n = Some bs -> ov_read_bytes segs m a n = Some bs.
Proof.
  induction n as [|n IH]; intros m a bs HR Hr; [exact Hr|].
  rewrite ov_read_cons in Hr |- *.
  destruct (rd1 (mrestrict D m) a) as [b|] eqn:E1; [|discriminate].
  rewrite (rd1_clean m a b HR E1).
  destruct (ov_read_bytes segs (mrestrict D m) (a + 1) n) as [r|] eqn:E2; [|discriminate].
  rewrite (IH m (a + 1) r HR E2). exact Hr.
Qed.

Lemma wview_clean : forall m a, wview segs (mrestrict D m) a = if D a then None else wview segs m a.
Proof.
  intros m a. unfold wview, mrestrict. destruct (D a) eqn:Ha; [|reflexivity].
  pose proof (HND a Ha) as N.
  destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:Ef; [|reflexivity].
  rewrite N. reflexivity.
Qed.

Lemma store_ok_clean : forall n m a, store_ok segs (mrestrict D m) a n = true ->
  store_ok segs m a n = true /\ range_avoids D a n.
Proof.
  induction n as [|n IH]; intros m a Hs.
  - split; [reflexivity | intros k Hk; lia].
  - cbn [store_ok] in Hs |- *. rewrite wview_clean in Hs.
    destruct (D a) eqn:Ha; [discriminate|].
    destruct (wview segs m a) as [b|]; [|discriminate].
    destruct (IH m (a + 1) Hs) as [Hfull Hav].
    split; [exact Hfull | apply range_avoids_cons; assumption].
Qed.

Lemma ragree_write : forall m a bs, ragree m -> range_avoids D a (length bs) -> ragree (write_to_mem m a bs).
Proof.
  intros m a bs HR Hav x b Hx E. rewrite (write_to_mem_hidden D bs m a x Hav Hx). exact (HR x b Hx E).
Qed.

Lemma interp_eff_accesses_clean : forall t m c mr' rs, ragree m ->
  interp_eff_accesses segs t (mrestrict D m) = MachineOk (@mkAccessReport _ (c, mr') rs) ->
  exists mf', interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, mf') rs) /\
    mr' = mrestrict D mf' /\ (forall x, D x = true -> mf' x = m x).
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c mr' rs HR Hi; cbn [interp_eff_accesses] in Hi |- *; try discriminate.
  - injection Hi as <- <- <-. exists m. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
  - destruct (ov_read_bytes segs (mrestrict D m) a (width_bytes n)) as [bs|] eqn:Hrd; [|discriminate].
    rewrite (ov_read_bytes_clean _ m a bs HR Hrd).
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict D m))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ m c1 m1 rs1 HR Hk) as (mf' & Hint & Hmr & Hhid).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr | exact Hhid].
  - destruct (store_ok segs (mrestrict D m) a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (store_ok_clean _ m a Hso) as [Hfull Hav]. rewrite Hfull.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict D (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      in Hi by (rewrite Hlen; exact Hav).
    destruct (interp_eff_accesses segs k
                (mrestrict D (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    assert (HRw : ragree (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      by (apply ragree_write; [exact HR | rewrite Hlen; exact Hav]).
    destruct (IH _ c1 m1 rs1 HRw Hk) as (mf' & Hint & Hmr & Hhid).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|].
    intros x Hx. rewrite (Hhid x Hx).
    apply (write_to_mem_hidden D _ m a x); [rewrite Hlen; exact Hav | exact Hx].
Qed.

Lemma decode_exec_accesses_clean : forall ms w msr' rs', ragree (ms_mem ms) ->
  decode_exec_accesses segs (restrict D ms) w = MachineOk (@mkAccessReport _ msr' rs') ->
  decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ (unrestrict D (ms_mem ms) msr') rs') /\
  hclean D msr'.
Proof.
  intros ms w msr' rs' HR Hd. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-. split; [|apply (restrict_hclean D ms)].
    unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
    rewrite munrestrict_mrestrict. destruct ms; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
    destruct (interp_eff_accesses segs
                (exec (Z_to_bv 64 isz) i
                   {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
                      c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
                      c_resv := ms_resv ms |})
                (mrestrict D (ms_mem ms)))
      as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    destruct (interp_eff_accesses_clean _ _ c1 m1 rs1 HR Hint) as (mf' & Hfull & -> & Hhid).
    rewrite Hfull. cbn [access_value accessed_ranges].
    split.
    + unfold unrestrict. cbn.
      replace (munrestrict D (ms_mem ms) (mrestrict D mf')) with mf'; [reflexivity|].
      apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
      destruct (D x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.

Lemma code_read_ov_clean : forall m a n, code_read_ov segs (mrestrict D m) a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [sg|] eqn:Hf; [|reflexivity].
  destruct (find_segment_some_spec segs _ _ sg Hf) as (Hin & _ & _).
  rewrite (HNX sg Hin). reflexivity.
Qed.
Lemma fetch_word_ov_clean : forall m a, fetch_word_ov segs (mrestrict D m) a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_clean. reflexivity. Qed.
Lemma fetch_half_ov_clean : forall m a, fetch_half_ov segs (mrestrict D m) a = fetch_half_ov segs m a.
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_clean. reflexivity. Qed.
Lemma fetch_half_any_clean : forall m a, fetch_half_any segs (mrestrict D m) a = fetch_half_any segs m a.
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_clean. reflexivity. Qed.
Lemma fetch_tail_any_clean : forall m a, fetch_tail_any segs (mrestrict D m) a = fetch_tail_any segs m a.
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_clean. reflexivity. Qed.
Lemma fetch_failure_clean : forall m a, fetch_failure segs (mrestrict D m) a = fetch_failure segs m a.
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_clean. reflexivity. Qed.

Theorem step_accesses_clean : forall ms msr' rs', ragree (ms_mem ms) ->
  step_accesses segs (restrict D ms) = MachineOk (@mkAccessReport _ msr' rs') ->
  step_accesses segs ms = MachineOk (@mkAccessReport _ (unrestrict D (ms_mem ms) msr') rs') /\ hclean D msr'.
Proof.
  intros ms msr' rs' HR Hs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
  rewrite fetch_word_ov_clean, fetch_tail_any_clean, fetch_failure_clean in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_clean ms w msr' rs' HR Hs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_clean ms w msr' rs' HR Hs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_clean ms w msr' rs' HR Hs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

Theorem step_clean : forall ms msr', ragree (ms_mem ms) ->
  RiscvSemantics.step segs (restrict D ms) = MachineOk msr' ->
  RiscvSemantics.step segs ms = MachineOk (unrestrict D (ms_mem ms) msr') /\ hclean D msr'.
Proof.
  intros ms msr' HR Hs. unfold RiscvSemantics.step, drop_access_report in Hs |- *.
  destruct (step_accesses segs (restrict D ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
  injection Hs as ->.
  destruct (step_accesses_clean ms msr' rs HR Hsa) as (Hfull & Hcl).
  rewrite Hfull. split; [reflexivity | exact Hcl].
Qed.

Lemma unrestrict_ext : forall (f f' : word -> option byte) ms,
  (forall x, D x = true -> f' x = f x) -> unrestrict D f' ms = unrestrict D f ms.
Proof.
  intros f f' ms E. unfold unrestrict. f_equal. apply functional_extensionality. intro x.
  unfold munrestrict. destruct (D x) eqn:Hx; [exact (E x Hx) | reflexivity].
Qed.

Lemma msteps_clean : forall msc msc', BzE.msteps segs msc msc' ->
  forall ms, msc = restrict D ms -> ragree (ms_mem ms) ->
  BzE.msteps segs ms (unrestrict D (ms_mem ms) msc') /\ hclean D msc'.
Proof.
  intros msc msc' H. induction H as [msc | msc msc1 msc2 Hstep _ IH]; intros ms Ems HR.
  - subst msc. split; [rewrite unrestrict_restrict; apply BzE.msteps_refl | apply restrict_hclean].
  - destruct Hstep as [Hsvc Hok]. subst msc.
    destruct (step_clean ms msc1 HR Hok) as (Hst & Hcl).
    assert (E1 : msc1 = restrict D (unrestrict D (ms_mem ms) msc1))
      by (symmetry; apply restrict_unrestrict_clean; exact Hcl).
    assert (EM : forall x, D x = true -> ms_mem (unrestrict D (ms_mem ms) msc1) x = ms_mem ms x).
    { intros x Hx. rewrite unrestrict_mem. unfold munrestrict. rewrite Hx. reflexivity. }
    destruct (IH (unrestrict D (ms_mem ms) msc1) E1 (ragree_ext _ _ EM HR)) as (Hrest & Hcl2).
    split; [|exact Hcl2].
    rewrite (unrestrict_ext (ms_mem ms) (ms_mem (unrestrict D (ms_mem ms) msc1)) msc2 EM) in Hrest.
    eapply BzE.msteps_cons; [split; [exact Hsvc | exact Hst] | exact Hrest].
Qed.

(* a walk from the cleaned state is a walk from the real one, ending in the real store: the cleaned final store
   at every address not dropped, the starting store at every dropped one *)
Theorem evt_clean : forall (Q : machine_state -> Prop) ms, ragree (ms_mem ms) ->
  BzE.evt segs Q (restrict D ms) ->
  BzE.evt segs (fun ms1 => exists msc, Q msc /\ hclean D msc /\ ms1 = unrestrict D (ms_mem ms) msc) ms.
Proof.
  intros Q ms HR (msc' & Hs & HQ).
  destruct (msteps_clean _ _ Hs ms eq_refl HR) as (Hs' & Hcl).
  exists (unrestrict D (ms_mem ms) msc'). split; [exact Hs'|].
  exists msc'. split; [exact HQ|]. split; [exact Hcl | reflexivity].
Qed.

End g.

Open Scope Z_scope.

(* ---- fm.asan: the dropped set, the cleaned store ---- *)
(* dropped: a read-only image address, or an address at or above 2^47 *)
Definition Dc (a : word) : bool := BM.ro_addr BzI.asegs a || (BM.UTOP <=? bv_unsigned a).
Definition clean (m : word -> option byte) : word -> option byte := mrestrict Dc m.

Lemma find_segment_below : forall (a : word) sg,
  find_segment BzI.asegs (bv_unsigned a) 1 = Some sg -> bv_unsigned a < BM.UTOP.
Proof. intros a sg E. apply RtBzStr.seg_addr_below. unfold BM.seg_addr. rewrite E. reflexivity. Qed.

Lemma Dc_nowrite : forall a, Dc a = true ->
  match find_segment BzI.asegs (bv_unsigned a) 1 with Some sg => seg_writable sg = false | None => True end.
Proof.
  intros a Ha. unfold Dc in Ha. apply orb_true_iff in Ha as [Ha|Ha].
  - unfold BM.ro_addr in Ha.
    destruct (find_segment BzI.asegs (bv_unsigned a) 1) as [sg|] eqn:E; [|exact I].
    apply negb_true_iff in Ha. exact Ha.
  - destruct (find_segment BzI.asegs (bv_unsigned a) 1) as [sg|] eqn:E; [|exact I].
    exfalso. pose proof (find_segment_below a sg E). apply Z.leb_le in Ha. lia.
Qed.

Lemma asegs_no_wx : forall sg, In sg BzI.asegs -> seg_executable sg && seg_writable sg = false.
Proof.
  assert (C : forallb (fun sg => negb (seg_executable sg && seg_writable sg)) BzI.asegs = true)
    by (vm_compute; reflexivity).
  intros sg Hin. pose proof (proj1 (forallb_forall _ _) C sg Hin) as H. apply negb_true_iff in H. exact H.
Qed.

Lemma Dc_false : forall x, BM.ro_addr BzI.asegs x = false -> bv_unsigned x < BM.UTOP -> Dc x = false.
Proof. intros x H1 H2. unfold Dc. rewrite H1. cbn [orb]. apply Z.leb_gt. exact H2. Qed.

(* above the image (the stack, the shadow, the heap) nothing is dropped below 2^47 *)
Lemma Dc_above : forall x, YF0x.TFIB_IMG_END <= bv_unsigned x < BM.UTOP -> Dc x = false.
Proof.
  intros x Hx. apply Dc_false; [|lia]. unfold BM.ro_addr.
  destruct (find_segment BzI.asegs (bv_unsigned x) 1) as [sg|] eqn:E; [|reflexivity].
  exfalso. pose proof (find_segment_some_spec BzI.asegs _ _ sg E) as (Hin & Hlo & Hhi).
  assert (C : RtBzStr.seg_tops_below BzI.asegs YF0x.TFIB_IMG_END = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C sg Hin) as Hb. apply Z.leb_le in Hb. lia.
Qed.

(* the walks' standing store fact holds of every cleaned store *)
Lemma mem_inv_clean : forall m, BM.mem_inv BzI.asegs (clean m).
Proof.
  intros m. unfold clean. apply RtBzStr.mem_inv_of_store_clean. intros a Ha. unfold mrestrict in Ha.
  destruct (Dc a) eqn:E; [exfalso; exact (Ha eq_refl)|].
  unfold Dc in E. apply orb_false_iff in E as (E1 & E2).
  split; [exact E1 | apply Z.leb_gt in E2; exact E2].
Qed.

(* every read-only address reads as the image byte *)
Definition rom_eq (m : word -> option byte) : Prop :=
  forall a, BM.ro_addr BzI.asegs a = true -> BM.mrd BzI.asegs m a = YK11.seg_rom BzI.asegs a.

Lemma seg_rom_high : forall a : word, BM.UTOP <= bv_unsigned a -> YK11.seg_rom BzI.asegs a = None.
Proof.
  intros a Ha. unfold YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment BzI.asegs (bv_unsigned a) 1) as [sg|] eqn:E; [|reflexivity].
  pose proof (find_segment_below a sg E). lia.
Qed.

Lemma ragree_of_rom_eq : forall m, rom_eq m -> ragree BzI.asegs Dc m.
Proof.
  intros m HE a b Ha Hb. unfold Dc in Ha. apply orb_true_iff in Ha as [Ha|Ha].
  - specialize (HE a Ha). unfold BM.mrd in HE. destruct (m a) as [c|] eqn:E; [|left; reflexivity].
    right. rewrite HE. exact Hb.
  - apply Z.leb_le in Ha. rewrite (seg_rom_high a Ha) in Hb. discriminate.
Qed.

(* below 2^47 the cleaned store reads as the real one *)
Lemma mrd_clean : forall m a, rom_eq m -> bv_unsigned a < BM.UTOP ->
  BM.mrd BzI.asegs (clean m) a = BM.mrd BzI.asegs m a.
Proof.
  intros m a HE Ha. unfold BM.mrd at 1. unfold clean, mrestrict. destruct (Dc a) eqn:E.
  - unfold Dc in E. apply orb_true_iff in E as [E|E]; [|apply Z.leb_le in E; lia].
    rewrite (HE a E). reflexivity.
  - reflexivity.
Qed.

Lemma mrd_clean_nd : forall m a, Dc a = false -> BM.mrd BzI.asegs (clean m) a = BM.mrd BzI.asegs m a.
Proof. intros m a E. unfold BM.mrd, clean, mrestrict. rewrite E. reflexivity. Qed.

Lemma wview_clean_nd : forall m a, Dc a = false -> wview BzI.asegs (clean m) a = wview BzI.asegs m a.
Proof. intros m a E. unfold clean. rewrite (wview_clean BzI.asegs Dc Dc_nowrite m a), E. reflexivity. Qed.

(* at a writable address below 2^47 the cleaned store is writable where the real one is *)
Lemma wview_clean_rw : forall m a, BM.ro_addr BzI.asegs a = false -> bv_unsigned a < BM.UTOP ->
  wview BzI.asegs (clean m) a = wview BzI.asegs m a.
Proof. intros m a H1 H2. apply wview_clean_nd. exact (Dc_false a H1 H2). Qed.

(* every address of [a, a + n) is writable in the image (decided for the fixed cells) *)
Definition rw_range (a : Z) (n : nat) : bool :=
  forallb (fun i => negb (BM.ro_addr BzI.asegs (BM.wa (a + Z.of_nat i)))) (seq 0 n).

Lemma bytes_at_clean : forall m a bs, rom_eq m -> a + Z.of_nat (length bs) <= BM.UTOP ->
  BM.bytes_at BzI.asegs m a bs -> BM.bytes_at BzI.asegs (clean m) a bs.
Proof.
  intros m a bs HE Hu (H0 & H1 & HB). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite mrd_clean; [exact (HB i Hi) | exact HE |].
  unfold BM.UTOP in *. rewrite BM.wa_unsigned by lia. lia.
Qed.

Lemma ro_cells_clean : forall m a cs, rom_eq m -> a + Z.of_nat (BC.cells_size cs) <= BM.UTOP ->
  BS.ro_cells BzI.asegs m a cs -> BS.ro_cells BzI.asegs (clean m) a cs.
Proof.
  intros m a cs HE Hu (Hwf & Hb). split; [exact Hwf|].
  apply (bytes_at_clean m a _ HE); [rewrite (BC.cells_bytes_length cs Hwf); exact Hu | exact Hb].
Qed.
Lemma rw_cells_clean : forall m a cs, rom_eq m -> 0 <= a -> a + Z.of_nat (BC.cells_size cs) <= BM.UTOP ->
  rw_range a (BC.cells_size cs) = true ->
  BS.rw_cells BzI.asegs m a cs -> BS.rw_cells BzI.asegs (clean m) a cs.
Proof.
  intros m a cs HE Ha Hu HRW (HC & Hw0 & Hw1 & HW). split.
  - apply (ro_cells_clean m a cs HE Hu HC).
  - split; [exact Hw0|]. split; [exact Hw1|]. intros i Hi.
    assert (Ew : bv_unsigned (BM.wa (a + i)) = a + i)
      by (apply BM.wa_unsigned; unfold BM.UTOP in *; lia).
    assert (ER : BM.ro_addr BzI.asegs (BM.wa (a + i)) = false).
    { pose proof (proj1 (forallb_forall _ _) HRW (Z.to_nat i)) as Hc.
      rewrite in_seq in Hc. specialize (Hc ltac:(lia)). rewrite Z2Nat.id in Hc by lia.
      apply negb_true_iff in Hc. exact Hc. }
    rewrite (wview_clean_rw m _ ER ltac:(rewrite Ew; unfold BM.UTOP in *; lia)). exact (HW i Hi).
Qed.


Lemma stk_clean : forall m lo hi, YF0x.TFIB_IMG_END <= lo -> hi <= BM.UTOP ->
  BF.stk BzI.asegs m lo hi -> BF.stk BzI.asegs (clean m) lo hi.
Proof.
  intros m lo hi Hlo Hhi (H0 & H1 & ST). split; [exact H0|]. split; [exact H1|].
  intros a Ha. assert (Ew : bv_unsigned (BM.wa a) = a) by (apply BM.wa_unsigned; unfold BM.UTOP in *; lia).
  assert (E : Dc (BM.wa a) = false) by (apply Dc_above; rewrite Ew; lia).
  destruct (ST a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_clean_nd m _ E). exact Hw.
  - exists b. rewrite (mrd_clean_nd m _ E). exact Hb.
Qed.

(* the interceptors' range check reads only shadow bytes, all below 2^47 *)
Lemma chk_ok_clean : forall m p n, rom_eq m -> 0 <= p -> p + n <= 2 ^ 47 ->
  BQ.chk_ok m p n -> BQ.chk_ok (clean m) p n.
Proof.
  intros m p n HE Hp Hn (HA & HQ & HR). split; [|split; [|exact HR]].
  - intros i Hi. destruct (HA i Hi) as (b & Hb & Hs). exists b. split; [|exact Hs].
    apply (bytes_at_clean m _ [b] HE); [|exact Hb]. unfold BSh.shad, BSh.SHB, BM.UTOP. cbn [length].
    assert (0 <= (p + i) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia.
  - intros Hn1. destruct (HQ Hn1) as (w1 & w2 & H1 & H2). exists w1, w2.
    assert (AL : forall y, 0 <= y < p + n -> BQ.al8 (BSh.shad y) + Z.of_nat (BC.cells_size [BC.C8 w1]) <= BM.UTOP /\
                                              BQ.al8 (BSh.shad y) + Z.of_nat (BC.cells_size [BC.C8 w2]) <= BM.UTOP).
    { intros y Hy. change (BC.cells_size [BC.C8 w1]) with 8%nat. change (BC.cells_size [BC.C8 w2]) with 8%nat.
      unfold BQ.al8, BSh.shad, BSh.SHB, BM.UTOP.
      assert (0 <= y / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
      assert (0 <= 8 * ((y / 8 + 2147450880) / 8) <= y / 8 + 2147450880)
        by (split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | apply Z.mul_div_le; lia]).
      lia. }
    split.
    + apply (ro_cells_clean m _ _ HE); [apply (AL p); lia | exact H1].
    + apply (ro_cells_clean m _ _ HE); [apply (AL (p + n - 1)); lia | exact H2].
Qed.

(* ---- rom_eq from the contracts' read-only premises ---- *)
Lemma errno_not_ro : forall a : word, TFIB_ERRNO <= bv_unsigned a < TFIB_ERRNO + 4 -> BM.ro_addr BzI.asegs a = false.
Proof.
  intros a Ha. unfold BM.ro_addr.
  destruct (find_segment BzI.asegs (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
  pose proof (find_segment_some_spec BzI.asegs _ _ s E) as (Hin & Hlo & Hhi).
  assert (C : forallb (fun s : Segment => seg_writable s || (TFIB_ERRNO + 4 <=? Z.of_N (seg_base s))
                         || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? TFIB_ERRNO)) BzI.asegs = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C s Hin) as X. cbv beta in X.
  destruct (seg_writable s) eqn:Ew; [reflexivity|]. exfalso.
  cbn [orb] in X. apply orb_prop in X as [X|X]; apply Z.leb_le in X; unfold TFIB_ERRNO in *; lia.
Qed.

Lemma Exists_in_zr_dec : forall a (l : list (Z * Z)), Exists (in_zr a) l \/ ~ Exists (in_zr a) l.
Proof.
  intros a l. induction l as [|r l IH].
  - right. intros X. inversion X.
  - destruct (Z_le_dec (fst r) a) as [H1|H1]; [destruct (Z_lt_dec a (fst r + snd r)) as [H2|H2]|].
    + left. apply Exists_cons_hd. unfold in_zr. lia.
    + destruct IH as [IH|IH]; [left; apply Exists_cons_tl; exact IH|].
      right. intros X. apply Exists_cons in X as [X|X]; [unfold in_zr in X; lia | exact (IH X)].
    + destruct IH as [IH|IH]; [left; apply Exists_cons_tl; exact IH|].
      right. intros X. apply Exists_cons in X as [X|X]; [unfold in_zr in X; lia | exact (IH X)].
Qed.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the donor's view of one byte, read as the walks' reader *)
Lemma mrd_of_view : forall (H : word -> bool) mem (a : word),
  aview tfibsegs H mem (bv_unsigned a) =
    option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 (bv_unsigned a))) ->
  BM.mrd BzI.asegs (mrestrict H mem) a = YK11.seg_rom BzI.asegs a.
Proof.
  intros H mem a E.
  assert (E2 : option_map (fun b : byte => bv_unsigned b) (BM.mrd BzI.asegs (mrestrict H mem) (Z_to_bv 64 (bv_unsigned a))) =
               option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom BzI.asegs (Z_to_bv 64 (bv_unsigned a))))
    by exact E.
  rewrite Z_to_bv_bv_unsigned in E2.
  destruct (BM.mrd BzI.asegs (mrestrict H mem) a) as [b|]; destruct (YK11.seg_rom BzI.asegs a) as [c|];
    cbn in E2; try discriminate; [|reflexivity].
  injection E2 as E3. f_equal. apply bv_eq. exact E3.
Qed.

(* the two halves of rom_view (FMH_Base.v: rom_viewN, rom_viewO) give rom_eq; errno is not read-only *)
Lemma rom_eq_of_views : forall B (W : world tfibsegs) mem, SegBSyms B ->
  rom_viewN tfibsegs B W mem -> rom_viewO tfibsegs B W mem -> rom_eq (mrestrict (w_H W) mem).
Proof.
  intros B W mem TB HN HO a Ha. apply mrd_of_view.
  pose proof (RtBzStr.ro_addr_in_rom a Ha) as Hr.
  destruct (Exists_in_zr_dec (bv_unsigned a) (as_owned_static B)) as [Ho|Ho].
  - exact (HO _ Hr Ho).
  - apply HN; [exact Hr | exact Ho |]. rewrite (ts_errno B TB). intros He.
    rewrite (errno_not_ro a He) in Ha. discriminate.
Qed.

(* and so does the donor's whole rom_view (YG0d.v:382) *)
Lemma rom_eq_of_rom_view : forall (W : world tfibsegs) mem, rom_view tfibsegs W mem -> rom_eq (mrestrict (w_H W) mem).
Proof. intros W mem HR a Ha. apply mrd_of_view. apply HR. exact (RtBzStr.ro_addr_in_rom a Ha). Qed.

(* the two read-agreement facts in the contracts' own words, for a proof that wants them straight:
   below 2^47 the cleaned store reads as the real one, and it is writable wherever the real one is *)
Lemma mrd_clean_views : forall B (W : world tfibsegs) mem, SegBSyms B ->
  rom_viewN tfibsegs B W mem -> rom_viewO tfibsegs B W mem ->
  forall a : word, bv_unsigned a < 2 ^ 47 ->
  BM.mrd BzI.asegs (clean (mrestrict (w_H W) mem)) a = BM.mrd BzI.asegs (mrestrict (w_H W) mem) a.
Proof.
  intros B W mem TB HN HO a Ha. apply mrd_clean; [exact (rom_eq_of_views B W mem TB HN HO) | exact Ha].
Qed.

Lemma wview_clean_views : forall (W : world tfibsegs) mem (a : word),
  BM.ro_addr BzI.asegs a = false -> bv_unsigned a < 2 ^ 47 ->
  wview BzI.asegs (clean (mrestrict (w_H W) mem)) a = wview BzI.asegs (mrestrict (w_H W) mem) a.
Proof. intros W mem a H1 H2. exact (wview_clean_rw _ a H1 H2). Qed.

(* ---- the entry point: a Bz walk from the cleaned call-site state, read in the donor's form ---- *)
Theorem srr_of_clean_bz_eq : forall (W : world tfibsegs) (pc : Z) regs mem md
  (Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
  rom_eq (mrestrict (w_H W) mem) ->
  BzE.evt BzI.asegs Q (canon_at regs pc (clean (mrestrict (w_H W) mem))) ->
  (forall msc ms' model', Q msc -> hclean Dc msc ->
     R6.ms_eqv (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' -> same_but_materialized md model' ->
     hclean (w_H W) ms' -> POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof.
  intros W pc regs mem md Q POST HE Hev HK.
  apply (srr_of_canon_bz W pc regs mem md
           (fun ms1 => exists msc, Q msc /\ hclean Dc msc /\ ms1 = unrestrict Dc (mrestrict (w_H W) mem) msc)).
  - exact (evt_clean BzI.asegs Dc Dc_nowrite asegs_no_wx Q (canon_at regs pc (mrestrict (w_H W) mem))
             (ragree_of_rom_eq _ HE) Hev).
  - intros ms0 ms' model' (msc & HQ & Hcl & ->) Heqv Hsbm Hcl'. exact (HK msc ms' model' HQ Hcl Heqv Hsbm Hcl').
Qed.

Theorem srr_of_clean_bz : forall B, SegBSyms B ->
  forall (W : world tfibsegs) (pc : Z) regs mem md (Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
  rom_viewN tfibsegs B W mem -> rom_viewO tfibsegs B W mem ->
  BzE.evt BzI.asegs Q (canon_at regs pc (clean (mrestrict (w_H W) mem))) ->
  (forall msc ms' model', Q msc -> hclean Dc msc ->
     R6.ms_eqv (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' -> same_but_materialized md model' ->
     hclean (w_H W) ms' -> POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof.
  intros B TB W pc regs mem md Q POST HN HO.
  exact (srr_of_clean_bz_eq W pc regs mem md Q POST (rom_eq_of_views B W mem TB HN HO)).
Qed.

(* the name the contracts' proofs use *)
Theorem bz_run_clean : forall B, SegBSyms B ->
  forall (W : world tfibsegs) (pc : Z) regs mem md (Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
  rom_viewN tfibsegs B W mem -> rom_viewO tfibsegs B W mem ->
  BzE.evt BzI.asegs Q (canon_at regs pc (clean (mrestrict (w_H W) mem))) ->
  (forall msc ms' model', Q msc -> hclean Dc msc ->
     R6.ms_eqv (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' -> same_but_materialized md model' ->
     hclean (w_H W) ms' -> POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof. exact srr_of_clean_bz. Qed.

(* the same for a walk of lib/Lib (its step relation is the one the B kit uses: both are
   RiscvSemantics.step over the same image), read by RtBzLift.srr_of_canon *)
Theorem lib_run_clean : forall B, SegBSyms B ->
  forall (W : world tfibsegs) (pc : Z) regs mem md (Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
  rom_viewN tfibsegs B W mem -> rom_viewO tfibsegs B W mem ->
  LEX.evt Img0.rsegs Q (canon_at regs pc (clean (mrestrict (w_H W) mem))) ->
  (forall msc ms' model', Q msc -> hclean Dc msc ->
     R6.ms_eqv (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' -> same_but_materialized md model' ->
     hclean (w_H W) ms' -> POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof.
  intros B TB W pc regs mem md Q POST HN HO Hev HK.
  apply (srr_of_clean_bz B TB W pc regs mem md Q POST HN HO); [|exact HK].
  exact (lib_evt_bz Q _ Hev).
Qed.

End v.

(* ---- the post side: a walk that changed only [lo, hi) of the cleaned store changed only [lo, hi) of the real one,
   and left every byte there in the store ---- *)
Lemma clean_window : forall (m0 : word -> option byte) (msc : machine_state) (lo hi : Z),
  hclean Dc msc ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> ms_mem msc x = clean m0 x) ->
  (forall a, lo <= a < hi -> ms_mem msc (Z_to_bv 64 a) <> None) ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> ms_mem (unrestrict Dc m0 msc) x = m0 x) /\
  (forall a, lo <= a < hi -> ms_mem (unrestrict Dc m0 msc) (Z_to_bv 64 a) <> None).
Proof.
  intros m0 msc lo hi Hcl MOUT MIN. split.
  - intros x Hx. rewrite unrestrict_mem. unfold munrestrict. destruct (Dc x) eqn:E; [reflexivity|].
    rewrite (MOUT x Hx). unfold clean, mrestrict. rewrite E. reflexivity.
  - intros a Ha. rewrite unrestrict_mem. unfold munrestrict. destruct (Dc (Z_to_bv 64 a)) eqn:E.
    + exfalso. exact (MIN a Ha (Hcl _ E)).
    + exact (MIN a Ha).
Qed.

Module LMS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.MState.

(* the donor-form post of a cleaned walk: RtBzLift.rt_post_ro_win read on the walk's own end state, whose
   window facts are over the cleaned store *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem rt_post_ro_win_clean : forall (STK K : Z) ly S (W : world tfibsegs) regs mem md (R : Z -> Prop)
  msc ms' model' (v : Z),
  ecall_pre_k tfibsegs B STK ly S W regs mem md -> 0 <= K <= STK -> hclean Dc msc ->
  R6.ms_eqv (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' -> same_but_materialized md model' ->
  ms_pc_val msc = LMS.ret_pc (getr regs 1) -> ms_fregs msc = fp_regs -> ms_svc_pending msc = None ->
  ms_resv msc = None -> ms_fcsr msc = fp_csr -> ms_rom msc = seg_rom tfibsegs ->
  (forall r, acallee_saved r -> getr (ms_regs msc) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  getr (ms_regs msc) 10 = w64 v -> 0 <= v < 2 ^ 64 -> R v ->
  (forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) ->
     ms_mem msc x = clean (mrestrict (w_H W) mem) x) ->
  (forall a, spZ regs - K <= a < spZ regs -> ms_mem msc (Z_to_bv 64 a) <> None) ->
  rt_post_ro tfibsegs B STK ly S W regs mem md R W (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros STK K ly S W regs mem md R msc ms' model' v HPRE HK Hcl Heqv Hsbm P0 F0 S0 R0 C0 RO0 KEEP A10 Hv HR
    MOUT MIN.
  destruct (clean_window (mrestrict (w_H W) mem) msc (spZ regs - K) (spZ regs) Hcl MOUT MIN) as (MO & MN).
  exact (rt_post_ro_win B LAWS STK K ly S W regs mem md R (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' model' v
           HPRE HK Heqv Hsbm P0 F0 S0 R0 C0 RO0 KEEP A10 Hv HR MO MN).
Qed.

End w.
