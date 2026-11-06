(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import CatSim ExitSim ShapeAlg AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode RzCPS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Transfer.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.

Lemma seg_rom_hidden : forall a, H a = true -> seg_rom segs a = None.
Proof.
  intros a Ha. unfold seg_rom. rewrite (memory_read1_hidden segs H HH a Ha). reflexivity.
Qed.

Lemma mrd_restrict : forall m a b, mrd segs (mrestrict H m) a = Some b -> H a = false /\ mrd segs m a = Some b.
Proof.
  intros m a b E. unfold mrd, mrestrict in *. destruct (H a) eqn:Ha.
  - rewrite (seg_rom_hidden a Ha) in E. discriminate.
  - split; [reflexivity| exact E].
Qed.

Lemma bytes_at_restrict : forall m a bs, bytes_at segs (mrestrict H m) a bs ->
  bytes_at segs m a bs /\ (forall i, (i < length bs)%nat -> H (wa (a + Z.of_nat i)) = false).
Proof.
  intros m a bs (H0 & H1 & H2). split.
  - split; [exact H0|]. split; [exact H1|]. intros i Hi. specialize (H2 i Hi).
    destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
    exact (proj2 (mrd_restrict m _ b H2)).
  - intros i Hi. specialize (H2 i Hi). destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
    exact (proj1 (mrd_restrict m _ b H2)).
Qed.

Lemma wview_restrict_some : forall m a, wview segs (mrestrict H m) a <> None -> H a = false /\ wview segs (mrestrict H m) a = wview segs m a.
Proof.
  intros m a E. unfold wview, mrestrict in *. destruct (H a) eqn:Ha.
  - rewrite (HH a Ha) in E. exfalso. apply E. reflexivity.
  - split; reflexivity.
Qed.

Lemma wr_at_restrict : forall m a n, wr_at segs (mrestrict H m) a n ->
  wr_at segs m a n /\ (forall i, 0 <= i < n -> H (wa (a + i)) = false).
Proof.
  intros m a n (H0 & H1 & H2). split.
  - split; [exact H0|]. split; [exact H1|]. intros i Hi. specialize (H2 i Hi).
    destruct (wview_restrict_some m _ H2) as [_ E]. rewrite <- E. exact H2.
  - intros i Hi. exact (proj1 (wview_restrict_some m _ (H2 i Hi))).
Qed.

Lemma range_avoids_of_visible : forall a n, 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall i, (i < n)%nat -> H (wa (a + Z.of_nat i)) = false) -> range_avoids H (wa a) n.
Proof.
  intros a n Ha Han Hv k Hk. unfold woff. unfold wa. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64).
  destruct (Z.eq_dec a (2^64)) as [E|NE]; [subst; cbn in Hk; lia|].
  rewrite (Z.mod_small a (2^64)) by lia. exact (Hv k Hk).
Qed.

End Transfer.

Lemma restrict_areg : forall H ms r, areg (restrict H ms) r = areg ms r.
Proof. reflexivity. Qed.

Lemma restrict_svc : forall H ms, ms_svc_pending (restrict H ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.

Lemma restrict_rom' : forall H ms, ms_rom (restrict H ms) = ms_rom ms.
Proof. reflexivity. Qed.

Lemma vm_same_refl : forall mo, vm_same mo mo.
Proof. intros. repeat split; reflexivity. Qed.

Lemma vm_same_with_fds : forall mo f, vm_same mo (with_fds f mo).
Proof. intros mo f. repeat split; reflexivity. Qed.

Lemma io_eff_mkEffect : forall r ws, io_eff (mkEffect r ws []).
Proof. intros. repeat split; reflexivity. Qed.

Lemma io_eff_copyins : forall R eff, io_eff eff -> io_eff (with_copyins R eff).
Proof. intros R [r ws zs us cs ci] H. exact H. Qed.

Lemma ranges_avoid_nil' : forall H, ranges_avoid H [].
Proof. intros H a n []. Qed.

Lemma accesses_mkEffect_nil : forall r, syscall_effect_accesses (mkEffect r [] []) = [].
Proof. reflexivity. Qed.

Section Rules.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

Lemma AST_off : forall A Pm PM c, AST segtop A Pm PM c -> H_off_segments segs (HID A (cfg_model c)).
Proof. intros A Pm PM c (Hmc & _). exact (HID_off segs segtop Hsegs A _ Hmc). Qed.

Lemma ast_exit : forall A Pm PM c code fs,
  AST segtop A Pm PM c ->
  (forall ms, Pm ms -> (ms_svc_pending ms = Some (Z_to_bv 64 93) \/ ms_svc_pending ms = Some (Z_to_bv 64 94))
                       /\ areg ms 10 = code) ->
  (forall mo, PM mo -> m_fs mo = fs) ->
  realizes segs c (t_exit (bv_and code (Z_to_bv 64 255)) fs).
Proof using Hwx Hsegs.
  intros A Pm PM [ms mo] code fs (Hmc & HPm & HPM & _) Hm HM. cbn [cfg_ms cfg_model] in *.
  destruct (Hm _ HPm) as [Hsvc Ha0]. rewrite restrict_svc in Hsvc. rewrite restrict_areg in Ha0.
  pose proof Hmc as (_ & _ & Hh & _). rewrite <- (HM mo HPM), <- Ha0.
  destruct Hsvc as [Hsvc|Hsvc]; apply (rz_exit segs ms mo _ Hh Hsvc); unfold is_exit_no; rewrite unsigned_lit by lia; auto.
Qed.

Lemma ast_node1 : forall A Pm PM K KM,
  mat_stable KM ->
  (forall ms mo, AST segtop A Pm PM (mkCfg ms mo) ->
     exists x8 eff mdl, ms_svc_pending ms = Some x8
       /\ (forall r, syscall_spec (sys_input segs ms x8) mo r <-> r = Ok eff mdl [])
       /\ vm_same mo mdl /\ io_eff eff /\ ranges_avoid (HID A mo) (syscall_effect_accesses eff)
       /\ K (nretA (restrict (HID A mo) ms) eff) /\ KM mdl) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM HKM Hnode T [ms mo] Hc Hk.
  destruct (Hnode ms mo Hc) as (x8 & eff & mdl & Hsvc & Hchar & Hvm & Hio & Hav & HK & HKMm).
  pose proof (syscall_spec_acfg_det _ _ _ _ _ Hchar) as HcharA.
  destruct (ast_node_core segs segtop A Pm PM unit (fun _ => []) (fun _ => K) (fun _ => KM) ms mo x8
             (fun _ => eff) (fun _ => mdl) Hc Hsvc) as (nx & Hnd & Hnx).
  - intros []. apply HcharA. reflexivity.
  - intros r Hr. exists tt. apply HcharA. exact Hr.
  - intros []. exact Hvm.
  - intros []. exact Hio.
  - intros []. exact Hav.
  - intros []. exact HK.
  - intros []. exact HKMm.
  - intros []. exact HKM.
  - apply (rz_silent1 segs _ (nx tt) T).
    + destruct Hnd as [H1 H2]. split; [intros []; exact (H1 tt)|].
      intros e st Hs. destruct (H2 e st Hs) as ([] & -> & ->). exists tt. split; reflexivity.
    + exact (Hk _ (Hnx tt)).
Qed.

Lemma ast_close : forall A Pm PM K KM fd,
  3 <= fd < 2^32 -> mat_stable KM ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 57) /\ areg ms 10 = Z_to_bv 64 fd
                       /\ K (nretA ms (eff0 (Z_to_bv 64 0)))) ->
  (forall mo, PM mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) <> None
                       /\ KM (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo)) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM fd Hfd HKM Hm HM. apply ast_node1; [exact HKM|].
  intros ms mo (Hmc & HPm & HPM & _). cbn [cfg_ms cfg_model] in *.
  destruct (Hm _ HPm) as (Hsvc & Ha0 & HK). destruct (HM _ HPM) as (Hlk & HKMm).
  rewrite restrict_svc in Hsvc. rewrite restrict_areg in Ha0.
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hl; [|congruence].
  exists (Z_to_bv 64 57), (eff0 (Z_to_bv 64 0)), (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
  split; [exact Hsvc|]. split.
  { intros r. rewrite syscall_spec_57 by reflexivity. rewrite in_a0_si, Ha0.
    rewrite fd32_id by (rewrite unsigned_lit; lia). apply (close_outcome _ _ _ _ _ Hl). }
  split; [apply vm_same_with_fds|]. split; [apply io_eff_mkEffect|]. split; [apply ranges_avoid_nil'|].
  split; assumption.
Qed.

Lemma ast_ioctl : forall A Pm PM K KM fd,
  0 <= fd <= 2 -> mat_stable KM ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 29) /\ areg ms 10 = Z_to_bv 64 fd
                       /\ areg ms 11 = Z_to_bv 64 21523 /\ K (nretA ms (efferr ENOTTY))) ->
  (forall mo, PM mo -> (exists c, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel c)) /\ KM mo) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using Hwx Hsegs.

  intros A Pm PM K KM fd Hfd HKM Hm HM. apply ast_node1; [exact HKM|].
  intros ms mo (Hmc & HPm & HPM & _). cbn [cfg_ms cfg_model] in *.
  destruct (Hm _ HPm) as (Hsvc & Ha0 & Ha1 & HK). destruct (HM _ HPM) as ([ch Hl] & HKMm).
  rewrite restrict_svc in Hsvc. rewrite restrict_areg in Ha0, Ha1.
  exists (Z_to_bv 64 29), (efferr ENOTTY), mo.
  split; [exact Hsvc|]. split.
  { intros r. rewrite syscall_spec_29 by reflexivity. rewrite in_a0_si, in_a1_si, Ha0, Ha1.
    rewrite fd32_id by (rewrite unsigned_lit; lia).
    apply (ioctl_tty_outcome _ _ _ _ _ _ Hl); [discriminate|discriminate|]. vm_compute. reflexivity. }
  split; [apply vm_same_refl|]. split; [apply io_eff_mkEffect|]. split; [apply ranges_avoid_nil'|].
  split; assumption.
Qed.

Lemma ast_read_file : forall A Pm PM K KM fd buf count p off data,
  3 <= fd < 2^32 -> 0 < count <= 0x7ffff000 -> buf + count <= 0x800000000000 -> mat_stable KM ->
  let bs := file_read data off (Z_to_bv 64 count) in
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 63) /\ areg ms 10 = Z_to_bv 64 fd
                       /\ areg ms 11 = Z_to_bv 64 buf /\ areg ms 12 = Z_to_bv 64 count /\ wr_at segs (ms_mem ms) buf count
                       /\ K (nretA ms (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []))) ->
  (forall mo, PM mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\ fs_lookup (m_fs mo) p = Some data
                       /\ KM (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo)) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM fd buf count p off data Hfd Hcnt Hbuf HKM bs Hm HM. apply ast_node1; [exact HKM|].
  intros ms mo Hc. pose proof (AST_off A Pm PM _ Hc) as HH. destruct Hc as (Hmc & HPm & HPM & _). cbn [cfg_ms cfg_model] in *.
  destruct (Hm _ HPm) as (Hsvc & Ha0 & Ha1 & Ha2 & W & HK). destruct (HM _ HPM) as (Hlk & Hfs & HKMm).
  rewrite restrict_svc in Hsvc. rewrite restrict_areg in Ha0, Ha1, Ha2. rewrite restrict_mem in W.
  destruct (wr_at_restrict segs _ HH _ _ _ W) as [Wf Hvis].
  pose proof Wf as (Hb0 & _ & _).
  assert (Hlen : Z.of_nat (length bs) <= count).
  { subst bs. rewrite file_read_unguarded, length_firstn. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
  destruct (wr_at_read_bytes_map segs ms buf count (len_word bs) Wf) as [w Hw].
  { unfold len_word. rewrite unsigned_lit; lia. }
  exists (Z_to_bv 64 63), (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []),
    (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo).
  split; [exact Hsvc|]. split.
  { intros r. rewrite syscall_spec_63 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2.
    rewrite fd32_id by (rewrite unsigned_lit; lia).
    assert (Hacc : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true) by (apply access_okb_wr; unfold TASK_SIZE; lia).
    assert (Hcl : Z_to_bv 64 (rw_count_clamp (Z_to_bv 64 count)) = Z_to_bv 64 count).
    { rewrite rw_count_clamp_small by (unfold MAX_RW_COUNT; rewrite unsigned_lit; lia). apply Z_to_bv_bv_unsigned. }
    pose proof (read_file_outcome (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) (sys_input segs ms (Z_to_bv 64 63)) mo r
                  p off data w Hlk Hacc Hfs) as R.
    rewrite Hcl in R. apply R. rewrite in_wmem_si. exact Hw. }
  split; [apply vm_same_with_fds|]. split; [apply io_eff_mkEffect|]. split; [|split; assumption].

  unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
  destruct bs as [|b bs'] eqn:Ebs; cbn [delivered_writes write_accesses]; [apply ranges_avoid_nil'|].
  apply ranges_avoid_cons; [|apply ranges_avoid_nil'].
  apply (range_avoids_of_visible _ buf (length (b :: bs'))); [lia| lia|].
  intros i Hi. apply Hvis. lia.
Qed.

Lemma ast_read_dir : forall A Pm PM K KM fd buf count,
  3 <= fd < 2^32 -> 0 < count <= 0x7ffff000 -> 0 <= buf -> buf + count <= 0x800000000000 -> mat_stable KM ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 63) /\ areg ms 10 = Z_to_bv 64 fd
                       /\ areg ms 11 = Z_to_bv 64 buf /\ areg ms 12 = Z_to_bv 64 count
                       /\ K (nretA ms (efferr EISDIR))) ->
  (forall mo, PM mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir /\ KM mo) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM fd buf count Hfd Hcnt Hb0 Hbuf HKM Hm HM. apply ast_node1; [exact HKM|].
  intros ms mo (Hmc & HPm & HPM & _). cbn [cfg_ms cfg_model] in *.
  destruct (Hm _ HPm) as (Hsvc & Ha0 & Ha1 & Ha2 & HK). destruct (HM _ HPM) as (Hlk & HKMm).
  rewrite restrict_svc in Hsvc. rewrite restrict_areg in Ha0, Ha1, Ha2.
  exists (Z_to_bv 64 63), (efferr EISDIR), mo.
  split; [exact Hsvc|]. split.
  { intros r. rewrite syscall_spec_63 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2.
    rewrite fd32_id by (rewrite unsigned_lit; lia).
    assert (Hacc : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true) by (apply access_okb_wr; unfold TASK_SIZE; lia).
    apply (read_dir_outcome _ _ _ _ _ _ Hlk Hacc). }
  split; [apply vm_same_refl|]. split; [apply io_eff_mkEffect|]. split; [apply ranges_avoid_nil'|].
  split; assumption.
Qed.

Definition open_ent (p : list byte) (fs : Fs) : option FdEntry :=
  if (path_max <=? length p)%nat then None
  else match p with
       | [] => None
       | _ :: _ => if path_eqb p dot_path then Some FdDir
                   else match fs_lookup fs p with None => None | Some _ => Some (FdFile p (Z_to_bv 64 0)) end
       end.

Definition open_at (path : list byte) (ms : machine_state) : Prop :=
  ms_svc_pending ms = Some (Z_to_bv 64 56) /\ areg ms 10 = Z_to_bv 64 (-100) /\
  Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = 0 /\ ~ In (Z_to_bv 8 0) path /\
  path_has_slash path = false /\ path_eqb path dotdot_path = false /\
  ms_rom ms = seg_rom segs /\ bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0]).

Lemma cstr_access_len_le : forall str mp a fuel, bytes_in mp a (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
  (cstr_access_len_aux mp (wa a) fuel <= S (length str))%nat.
Proof.
  induction str as [|b str IH]; intros mp a fuel Hin Hnz; destruct fuel as [|fuel]; cbn [cstr_access_len_aux]; try lia.
  - cbn [app] in Hin. apply bytes_in_cons in Hin as [Hb _]. rewrite Hb. rewrite bv_eqb_refl. cbn. lia.
  - cbn [app] in Hin. apply bytes_in_cons in Hin as [Hb Hin]. rewrite Hb.
    assert (Hne : bv_eqb b (Z_to_bv 8 0) = false).
    { destruct (bv_eqb b (Z_to_bv 8 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnz. left. congruence. }
    rewrite Hne. rewrite wa_succ. cbn [length]. specialize (IH mp (a + 1) fuel Hin (fun H => Hnz (or_intror H))). lia.
Qed.

Lemma open_char : forall ms mo path,
  open_at path ms ->
  let i := sys_input segs ms (Z_to_bv 64 56) in
  let R := open_reads i (areg ms 11) in
  match open_ent path (m_fs mo) with
  | None => exists e, 1 <= e <= 4095 /\
              forall r, syscall_spec i mo r <-> r = Ok (with_copyins R (mkEffect (errno_ret e) [] [])) mo []
  | Some ent => forall r, syscall_spec i mo r <-> open_out R mo (fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo) r
  end.
Proof.
  intros ms mo path (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hdd & Hrom & Hp). cbv zeta.
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  set (i := sys_input segs ms (Z_to_bv 64 56)).
  assert (Hmf : modeled_open_flags (areg ms 12) = true) by (apply modeled_open_flags_rd; exact Hfl).
  assert (Hsp : forall o, syscall_spec i mo o <-> openat_spec AT_FDCWD32 (areg ms 11) (areg ms 12) i mo o).
  { intros o. subst i. rewrite syscall_spec_56 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, Ha0.
    rewrite AT_FDCWD32_eq. reflexivity. }
  assert (Hmem : in_mem i = ms_read_byte ms) by reflexivity.
  rewrite <- (wa_unsigned_id (areg ms 11)) in Hsp |- *.
  unfold open_ent. destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
  - replace (path_max <=? length path)%nat with true by (symmetry; apply Nat.leb_le; lia).
    exists ENAMETOOLONG. split; [unfold ENAMETOOLONG; lia|]. intros r. rewrite Hsp.
    apply (openat_toolong_outcome _ _ _ _ _ Hmf).
    unfold read_cstr. rewrite Hmem. apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong|exact Hnz|].
    apply bytes_in_app in Hin as [Hin _]. exact Hin.
  - replace (path_max <=? length path)%nat with false by (symmetry; apply Nat.leb_gt; lia).
    assert (Hc : read_cstr (in_mem i) (wa (bv_unsigned (areg ms 11))) = CstrOk path).
    { unfold read_cstr. rewrite Hmem. apply (read_cstr_aux_bytes_in path path_max); [lia|exact Hnz|exact Hin]. }
    destruct path as [|c path'].
    + exists ENOENT. split; [unfold ENOENT; lia|]. intros r. rewrite Hsp. apply (openat_empty_outcome _ _ _ _ _ Hmf _ Hc).
    + destruct (path_eqb (c :: path') dot_path) eqn:Hdot.
      * apply path_eqb_eq in Hdot. intros r. rewrite Hsp. rewrite Hdot in Hc.
        apply (openat_dot_outcome _ _ _ _ _ Hmf eq_refl Hfl). exact Hc.
      * assert (Hnd : path_is_dirref (c :: path') = false) by (unfold path_is_dirref; rewrite Hdot, Hdd; reflexivity).
        destruct (fs_lookup (m_fs mo) (c :: path')) as [d|] eqn:Hfs.
        -- intros r. rewrite Hsp. apply (openat_file_outcome _ _ _ _ _ Hmf eq_refl Hfl _ d); [exact Hc| discriminate| exact Hsl| exact Hnd| exact Hfs].
        -- exists ENOENT. split; [unfold ENOENT; lia|]. intros r. rewrite Hsp.
           apply (openat_absent_outcome _ _ _ _ _ Hmf eq_refl Hfl (c :: path')); [exact Hc| discriminate| exact Hsl| exact Hnd| exact Hfs].
Qed.

Lemma open_reads_avoid : forall (H : word -> bool) ms path,
  open_at path ms ->
  (forall i, (i < length (path ++ [Z_to_bv 8 0]))%nat -> H (wa (bv_unsigned (areg ms 11) + Z.of_nat i)) = false) ->
  ranges_avoid H (open_reads (sys_input segs ms (Z_to_bv 64 56)) (areg ms 11)).
Proof.
  intros H ms path (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hdd & Hrom & Hp) Hvis. unfold open_reads.
  apply ranges_avoid_cons; [|apply ranges_avoid_nil'].
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  pose proof (cstr_access_len_le path (in_mem (sys_input segs ms (Z_to_bv 64 56))) (bv_unsigned (areg ms 11)) path_max Hin Hnz) as Hle.
  pose proof Hp as (Hb0 & Hb1 & _). rewrite length_app in Hb1. cbn [length] in Hb1.
  rewrite <- (wa_unsigned_id (areg ms 11)).
  apply (range_avoids_of_visible H _ _); [lia| lia|]. intros k Hk. apply Hvis. rewrite length_app. cbn [length]. lia.
Qed.

Lemma nretA_copyins : forall ms R eff, nretA ms (with_copyins R eff) = nretA ms eff.
Proof. reflexivity. Qed.

Lemma open_at_transfer : forall (H : word -> bool) ms path, H_off_segments segs H ->
  open_at path (restrict H ms) ->
  open_at path ms /\ (forall i, (i < length (path ++ [Z_to_bv 8 0]))%nat -> H (wa (bv_unsigned (areg ms 11) + Z.of_nat i)) = false).
Proof.
  intros H ms path HH (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hdd & Hrom & Hp).
  rewrite restrict_mem, restrict_areg in Hp. destruct (bytes_at_restrict segs H HH _ _ _ Hp) as [Hp' Hvis].
  split; [|exact Hvis]. exact (conj Hsvc (conj Ha0 (conj Hfl (conj Hnz (conj Hsl (conj Hdd (conj Hrom Hp'))))))).
Qed.

Lemma ast_open_fail : forall A Pm PM (Ke : Z -> machine_state -> Prop) KMe path fs,
  mat_stable KMe -> open_ent path fs = None ->
  (forall ms, Pm ms -> open_at path ms /\ forall e, 1 <= e <= 4095 -> Ke e (nretA ms (efferr e))) ->
  (forall mo, PM mo -> m_fs mo = fs /\ KMe mo) ->
  cps segs (AST segtop A Pm PM) (fun c => exists e, 1 <= e <= 4095 /\ AST segtop A (Ke e) KMe c).
Proof using Hwx Hsegs.
  intros A Pm PM Ke KMe path fs HKM Hcl Hm HM T [ms mo] Hc Hk.
  pose proof (AST_off A Pm PM _ Hc) as HH. pose proof Hc as (Hmc & HPm & HPM & _). cbn [cfg_ms cfg_model] in *.
  destruct (Hm _ HPm) as (Hat & HK). destruct (HM _ HPM) as (Hfs & HKMm).
  destruct (open_at_transfer _ ms path HH Hat) as [Hat' Hvis].
  pose proof (open_char ms mo path Hat') as Hch. cbv zeta in Hch. rewrite Hfs, Hcl in Hch.
  destruct Hch as (e & He & Hchar).
  set (R := open_reads (sys_input segs ms (Z_to_bv 64 56)) (areg ms 11)) in *.
  destruct (ast_node_core segs segtop A Pm PM unit (fun _ => []) (fun _ => Ke e) (fun _ => KMe) ms mo (Z_to_bv 64 56)
             (fun _ => with_copyins R (mkEffect (errno_ret e) [] [])) (fun _ => mo) Hc) as (nx & Hnd & Hnx).
  - exact (proj1 Hat').
  - intros []. apply (syscall_spec_acfg_no segs ms _ 56); [reflexivity | reflexivity |]. apply Hchar. reflexivity.
  - intros r Hr. exists tt. apply Hchar. apply (syscall_spec_acfg_no segs ms _ 56) in Hr; [exact Hr | reflexivity | reflexivity].
  - intros []. apply vm_same_refl.
  - intros []. apply io_eff_copyins, io_eff_mkEffect.
  - intros []. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes with_copyins app write_accesses].
    rewrite app_nil_r. apply (open_reads_avoid _ ms path Hat' Hvis).
  - intros []. rewrite nretA_copyins. exact (HK e He).
  - intros []. exact HKMm.
  - intros []. exact HKM.
  - apply (rz_silent1 segs _ (nx tt) T).
    + destruct Hnd as [H1 H2]. split; [intros []; exact (H1 tt)|].
      intros ev st Hs. destruct (H2 ev st Hs) as ([] & -> & ->). exists tt. split; reflexivity.
    + apply Hk. exists e. split; [exact He| exact (Hnx tt)].
Qed.

Lemma ast_open_br : forall A Pm PM (Ke : Z -> machine_state -> Prop) KMe (Ko : word -> machine_state -> Prop)
    (KMo : word -> Model -> Prop) path fs ent,
  mat_stable KMe -> (forall fdw, mat_stable (KMo fdw)) -> open_ent path fs = Some ent ->
  (forall ms, Pm ms -> open_at path ms /\ (forall e, 1 <= e <= 4095 -> Ke e (nretA ms (efferr e)))
                       /\ (forall fdw, Ko fdw (nretA ms (eff0 fdw)))) ->
  (forall mo, PM mo -> m_fs mo = fs /\ KMe mo /\ fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None
                       /\ KMo (alloc_fd (m_fds mo)) (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo)) ->
  cps2 segs (AST segtop A Pm PM) (fun c => exists e, In e openat_errnos /\ AST segtop A (Ke e) KMe c)
                                  (fun c => exists fdw, AST segtop A (Ko fdw) (KMo fdw) c).
Proof using Hwx Hsegs.
  intros A Pm PM Ke KMe Ko KMo path fs ent HKMe HKMo Hcl Hm HM T1 T2 [ms mo] Hc Hk1 Hk2.
  pose proof (AST_off A Pm PM _ Hc) as HH. pose proof Hc as (Hmc & HPm & HPM & _). cbn [cfg_ms cfg_model] in *.
  destruct (Hm _ HPm) as (Hat & HKe & HKo). destruct (HM _ HPM) as (Hfs & HKMem & Hfree & HKMom).
  destruct (open_at_transfer _ ms path HH Hat) as [Hat' Hvis].
  pose proof (open_char ms mo path Hat') as Hch. cbv zeta in Hch. rewrite Hfs, Hcl in Hch.
  set (R := open_reads (sys_input segs ms (Z_to_bv 64 56)) (areg ms 11)) in *.
  set (fdw := alloc_fd (m_fds mo)) in *.
  set (I := ({e : Z | In e openat_errnos} + unit)%type).
  set (eff := fun i : I => match i with inl e => with_copyins R (mkEffect (errno_ret (proj1_sig e)) [] [])
                                        | inr _ => with_copyins R (mkEffect fdw [] []) end).
  set (mdl := fun i : I => match i with inl _ => mo | inr _ => with_fds (fd_insert (m_fds mo) fdw ent) mo end).
  set (K := fun i : I => match i with inl e => Ke (proj1_sig e) | inr _ => Ko fdw end).
  set (KM := fun i : I => match i with inl _ => KMe | inr _ => KMo fdw end).
  destruct (ast_node_core segs segtop A Pm PM I (fun _ => []) K KM ms mo (Z_to_bv 64 56) eff mdl Hc) as (nx & Hnd & Hnx).
  - exact (proj1 Hat').
  - intros [[e He]|[]]; (apply (syscall_spec_acfg_no segs ms _ 56); [reflexivity | reflexivity |]); apply Hch; [left; exists e; auto| right; auto].
  - intros r Hr. apply (syscall_spec_acfg_no segs ms _ 56) in Hr; [| reflexivity | reflexivity].
    apply Hch in Hr. destruct Hr as [(e & He & ->)|(_ & ->)].
    + exists (inl (exist _ e He)). reflexivity.
    + exists (inr tt). reflexivity.
  - intros [e|[]]; [apply vm_same_refl| apply vm_same_with_fds].
  - intros [e|[]]; apply io_eff_copyins, io_eff_mkEffect.
  - intros [e|[]]; unfold syscall_effect_accesses; cbn [eff with_copyins eff_copyins eff_writes app write_accesses];
      rewrite app_nil_r; apply (open_reads_avoid _ ms path Hat' Hvis).
  - intros [[e He]|[]]; cbn [K eff]; rewrite nretA_copyins; [apply HKe; apply openat_errnos_range; exact He| apply HKo].
  - intros [e|[]]; [exact HKMem| exact HKMom].
  - intros [e|[]]; [exact HKMe| apply HKMo].
  - assert (R1 : realizes segs (nx (inl (exist _ ENOMEM (or_introl eq_refl)))) T1).
    { apply Hk1. exists ENOMEM. split; [left; reflexivity| exact (Hnx (inl _))]. }
    assert (R2 : realizes segs (nx (inr tt)) T2) by (apply Hk2; exists fdw; exact (Hnx (inr tt))).
    pose proof (realizes_nonempty segs _ _ R1) as N1. pose proof (realizes_nonempty segs _ _ R2) as N2.
    eapply rz_conseq.
    + apply (rz_node segs _ I (fun _ => []) nx (fun i => match i with inl _ => T1 | inr _ => T2 end) (inr tt) Hnd).
      intros [[e He]|[]].
      * apply Hk1. exists e. split; [exact He| exact (Hnx (inl _))].
      * exact R2.
    + intros tr. unfold t_alt2. split.
      * intros [[e|[]] Hi]; [left; exact (proj1 (t_emit_nil_eq T1 N1 tr) Hi)| right; exact (proj1 (t_emit_nil_eq T2 N2 tr) Hi)].
      * intros [Ht|Ht]; [exists (inl (exist _ ENOMEM (or_introl eq_refl))); exact (proj2 (t_emit_nil_eq T1 N1 tr) Ht)
                        | exists (inr tt); exact (proj2 (t_emit_nil_eq T2 N2 tr) Ht)].
Qed.

End Rules.
