(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Adapter Driver HarnessU ProgA ProgZ
  BridgeU_stmt BridgeU_base BridgeU_stdio BridgeU_stdout BridgeU_read.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition oclass (fs : Fs.Fs) (pb : list byte) : Z + FdEntry :=
  if (path_max <=? length pb)%nat then inl ENAMETOOLONG
  else match pb with
       | [] => inl ENOENT
       | _ => if path_is_dirref pb then inr FdDir
              else match fs_lookup fs pb with
                   | None => inl ENOENT
                   | Some _ => inr (FdFile pb (Z_to_bv 64 0))
                   end
       end.

Lemma nstep_open_class : forall pb mo eff mo' evs,
  nstep (NOpen pb) mo eff mo' evs <->
  evs = [] /\ match oclass (m_fs mo) pb with
              | inl e => eff = efferr e /\ mo' = mo
              | inr ent => open_result mo ent eff mo'
              end.
Proof.
  intros pb mo eff mo' evs. cbn [nstep]. unfold oclass.
  destruct (path_max <=? length pb)%nat; [tauto|]. destruct pb as [|c pb']; [tauto|].
  destruct (path_is_dirref (c :: pb')); [tauto|]. destruct (fs_lookup (m_fs mo) (c :: pb')); tauto.
Qed.

Lemma oclass_errno : forall fs pb e, oclass fs pb = inl e -> 1 <= e <= 4095.
Proof.
  intros fs pb e H. unfold oclass in H. destruct (path_max <=? length pb)%nat; [injection H as <-; unfold ENAMETOOLONG; lia|].
  destruct pb; [injection H as <-; unfold ENOENT; lia|]. destruct (path_is_dirref (b :: pb)); [discriminate|].
  destruct (fs_lookup fs (b :: pb)); [discriminate|]. injection H as <-. unfold ENOENT; lia.
Qed.

Section ReadAll.
Variable rs : Z.
Variable fs : Fs.Fs.
Notation zio := (ioA AAllocZ).
Notation FD3 := (Z_to_bv 64 3).

Definition mo_open (ent : FdEntry) (mo : Model) : Model := with_fds (fd_insert (m_fds mo) FD3 ent) mo.

(* [comment removed for export] *)
Lemma open_T_run1 : forall pb e (s : ZSt) mo, m_fs mo = fs -> oclass fs pb = inl e ->
  run1 (msys (NOpen pb) dec_open s) mo [] (SErr e, s) (eq mo).
Proof.
  intros pb e s mo Hmf Hc. pose proof (oclass_errno _ _ _ Hc) as He. unfold msys. apply run1_enode.
  - intros rsp mo1 evs Hst. apply nstep_open_class in Hst. rewrite Hmf, Hc in Hst. destruct Hst as (-> & -> & ->).
    split; [|auto]. unfold dec_open. rewrite (dec_plain_err _ [] e He). reflexivity.
  - exists (efferr e). apply nstep_open_class. rewrite Hmf, Hc. auto.
  - intros code mo' H. exact H.
Qed.

(* [comment removed for export] *)
Lemma open_O_sound : forall pb ent (s : ZSt) mo, m_fs mo = fs -> m_fds mo = bridge_init_fds -> oclass fs pb = inr ent ->
  sound (msys (NOpen pb) dec_open s) mo
        (fun tr x mo1 => tr = [] /\ ((exists e, x = (SErr e, s) /\ mo1 = mo) \/ (x = (SVal 3, s) /\ mo1 = mo_open ent mo))).
Proof.
  intros pb ent s mo Hmf Hfds Hc. unfold msys. apply sound_enode.
  - intros rsp mo1 evs Hst. apply nstep_open_class in Hst. rewrite Hmf, Hc in Hst. destruct Hst as (-> & [(e & Hin & -> & ->)|(Hlk & -> & ->)]).
    + pose proof (openat_errnos_range e Hin) as He. exists (SErr e, s). split.
      * unfold dec_open. rewrite (dec_plain_err _ [] e He). reflexivity.
      * split; [reflexivity|]. left. exists e. auto.
    + rewrite Hfds in *. change (alloc_fd bridge_init_fds) with FD3 in *. exists (SVal 3, s). split.
      * unfold dec_open. rewrite (dec_plain_val _ [] 3) by (try reflexivity; lia). reflexivity.
      * split; [reflexivity|]. right. unfold mo_open. rewrite Hfds. auto.
  - intros code mo' H. exact H.
Qed.

Lemma open_O_ex_err : forall pb ent (s : ZSt) mo, m_fs mo = fs -> oclass fs pb = inr ent ->
  ex (msys (NOpen pb) dec_open s) mo [] (SErr ENOMEM, s) (eq mo).
Proof.
  intros pb ent s mo Hmf Hc. unfold msys. eapply (ex_enode _ _ mo (efferr ENOMEM) mo []).
  - apply nstep_open_class. rewrite Hmf, Hc. split; [reflexivity|]. left. exists ENOMEM. split; [cbn; auto|auto].
  - unfold dec_open. rewrite (dec_plain_err _ [] ENOMEM) by (unfold ENOMEM; lia). reflexivity.
  - reflexivity.
Qed.

Lemma open_O_ex_ok : forall pb ent (s : ZSt) mo, m_fs mo = fs -> m_fds mo = bridge_init_fds -> oclass fs pb = inr ent ->
  ex (msys (NOpen pb) dec_open s) mo [] (SVal 3, s) (eq (mo_open ent mo)).
Proof.
  intros pb ent s mo Hmf Hfds Hc. unfold msys. eapply (ex_enode _ _ mo (eff0 FD3) (mo_open ent mo) []).
  - apply nstep_open_class. rewrite Hmf, Hc. split; [reflexivity|]. right. rewrite Hfds. cbv zeta.
    change (alloc_fd bridge_init_fds) with FD3. split; [reflexivity|]. split; [reflexivity|]. unfold mo_open. rewrite Hfds. reflexivity.
  - unfold dec_open. rewrite (dec_plain_val _ [] 3) by (try reflexivity; lia). reflexivity.
  - reflexivity.
Qed.

Definition FsR (mo1 : Model) : Prop := m_fs mo1 = fs.

Lemma close_run1 : forall (s : ZSt) mo, fd_lookup (m_fds mo) FD3 <> None ->
  run1 (msys (NClose 3) dec_close s) mo [] (SVal 0, s) (eq (with_fds (fd_remove (m_fds mo) FD3) mo)).
Proof.
  intros s mo Hlk. unfold msys. apply run1_enode_mo.
  - intros rsp mo1 evs Hst. cbn [nstep] in Hst. destruct Hst as (-> & _ & Hst).
    destruct (fd_lookup (m_fds mo) FD3); [|congruence]. destruct Hst as [-> ->]. auto.
  - exists (eff0 (Z_to_bv 64 0)). cbn [nstep]. split; [reflexivity|]. split; [lia|].
    destruct (fd_lookup (m_fds mo) FD3); [auto|congruence].
  - intros code mo2 H. exact H.
Qed.

(* [comment removed for export] *)
Lemma file_tail_run1 : forall pb data path (s : ZSt) mo3,
  fs_lookup fs pb = Some data -> m_fs mo3 = fs -> fd_lookup (m_fds mo3) FD3 = Some (FdFile pb (Z_to_bv 64 0)) ->
  run1 (mbind (zmalloc 65536) (fun b =>
          match b with
          | None => mbind (io_diag zio DOom) (fun _ => mret RdExit)
          | Some buf =>
              mbind (mloop READ_FUEL (@read_loop_body ZSt unit zio zmalloc zfree rs 3 path) (mkRd buf 65536 []))
                    (fun res => match res with
                                | RdExit => mret RdExit
                                | RdDone buf' content => mbind (msys (NClose 3) dec_close) (fun _ => mret (RdDone buf' content))
                                end)
          end) s)
       mo3 (rd_out_tr data) (rd_out_res data, s) FsR.
Proof.
  intros pb data path s mo3 Hfs Hmf Hlk.
  change (rd_out_tr data) with ([] ++ rd_out_tr data).
  eapply run1_mbind with (R1 := eq mo3) (a := Some tt) (s1 := s); [apply run1_pure; reflexivity|]. intros mo1 <-. cbv beta iota.
  remember READ_FUEL as F eqn:HF.
  assert (HFu : MAX_INPUT - 0 + 2 <= Z.of_nat F) by (subst F; unfold READ_FUEL, MAX_INPUT; lia). clear HF.
  rewrite <- (app_nil_r (rd_out_tr data)).
  eapply run1_mbind with (R1 := RdR 3 fs).
  - apply (read_loop_run1 3 rs path pb data fs Hfs F (mkRd tt 65536 []) s mo3 0 O); cbn [rd_cap rd_content]; try assumption; try reflexivity; try lia.
  - intros mo1 [Hmf1 Hlk1]. unfold rd_out_res. destruct (MAX_INPUT <=? Z.of_nat (length data)).
    + apply run1_conseq with (R := eq mo1); [apply run1_pure; reflexivity|]. intros mo2 <-. exact Hmf1.
    + change (@nil event) with (@nil event ++ []).
      eapply run1_mbind; [apply (close_run1 s mo1 Hlk1)|]. intros mo2 <-.
      apply run1_conseq with (R := eq (with_fds (fd_remove (m_fds mo1) FD3) mo1)); [apply run1_pure; reflexivity|].
      intros mo3' <-. exact Hmf1.
Qed.

(* [comment removed for export] *)
Lemma dir_tail_run1 : forall path (s : ZSt) mo3, PIECE_OK path -> m_fs mo3 = fs -> fd_lookup (m_fds mo3) FD3 = Some FdDir ->
  run1 (mbind (zmalloc 65536) (fun b =>
          match b with
          | None => mbind (io_diag zio DOom) (fun _ => mret RdExit)
          | Some buf =>
              mbind (mloop READ_FUEL (@read_loop_body ZSt unit zio zmalloc zfree rs 3 path) (mkRd buf 65536 []))
                    (fun res => match res with
                                | RdExit => mret RdExit
                                | RdDone buf' content => mbind (msys (NClose 3) dec_close) (fun _ => mret (RdDone buf' content))
                                end)
          end) s)
       mo3 (Wz 2 (diag_bytes (DReadError path))) (RdExit, s) FsR.
Proof.
  intros path s mo3 Hp Hmf Hlk.
  change (Wz 2 (diag_bytes (DReadError path))) with ([] ++ Wz 2 (diag_bytes (DReadError path))).
  eapply run1_mbind with (R1 := eq mo3) (a := Some tt) (s1 := s); [apply run1_pure; reflexivity|]. intros mo1 <-. cbv beta iota.
  remember READ_FUEL as F eqn:HF.
  assert (HFu : 1 <= Z.of_nat F) by (subst F; unfold READ_FUEL, MAX_INPUT; lia). clear HF.
  destruct F as [|f]; [lia|].
  rewrite <- (app_nil_r (Wz 2 (diag_bytes (DReadError path)))).
  eapply run1_mbind with (R1 := eq mo3).
  - apply (read_dir_run1 3 rs path f s mo3 Hp Hlk).
  - intros mo1 <-. apply run1_conseq with (R := eq mo3); [apply run1_pure; reflexivity|]. intros mo2 <-. exact Hmf.
Qed.

(* [comment removed for export] *)
Definition ra_tail (fd : Z) (path : list Z) : Monad.M ZSt (@rd_result unit) :=
  mbind (zmalloc 65536) (fun b =>
    match b with
    | None => mbind (io_diag zio DOom) (fun _ => mret RdExit)
    | Some buf =>
        mbind (mloop READ_FUEL (@read_loop_body ZSt unit zio zmalloc zfree rs fd path) (mkRd buf 65536 []))
              (fun res => match res with
                          | RdExit => mret RdExit
                          | RdDone buf' content => mbind (msys (NClose fd) dec_close) (fun _ => mret (RdDone buf' content))
                          end)
    end).
Notation zread_all := (@read_all ZSt unit zio zmalloc zfree rs).
Definition pbytes (path : list Z) : list byte := map (Z_to_bv 8) path.

Lemma read_all_eq : forall path,
  zread_all path = mbind (msys (NOpen (pbytes path)) dec_open) (fun r =>
                     match r with
                     | SErr _ => mbind (io_diag zio (DCannotOpen path)) (fun _ => mret RdExit)
                     | SVal fd => ra_tail fd path
                     end).
Proof. intros path. unfold read_all, ra_tail, pbytes. reflexivity. Qed.

Definition cannot_tr (path : list Z) : list event := Wz 2 (diag_bytes (DCannotOpen path)).

Lemma read_all_T : forall path e (s : ZSt) mo, PIECE_OK path -> m_fs mo = fs -> oclass fs (pbytes path) = inl e ->
  run1 (zread_all path s) mo (cannot_tr path) (RdExit, s) FsR.
Proof.
  intros path e s mo Hp Hmf Hc. rewrite read_all_eq. change (cannot_tr path) with ([] ++ cannot_tr path).
  eapply run1_mbind; [apply (open_T_run1 _ e s mo Hmf Hc)|]. intros mo1 <-. cbv beta iota.
  unfold cannot_tr. rewrite <- (app_nil_r (Wz 2 _)).
  eapply run1_mbind; [apply (s_diag_run1 (DCannotOpen path) s mo Hp)|]. intros mo1 <-.
  apply run1_conseq with (R := eq mo); [apply run1_pure; reflexivity|]. intros mo1 <-. exact Hmf.
Qed.

(* [comment removed for export] *)
Section Openable.
Variable path : list Z.
Variable ent : FdEntry.
Variable ok_tr : list event.
Variable ok_res : @rd_result unit.
Hypothesis Hp : PIECE_OK path.
Hypothesis Hc : oclass fs (pbytes path) = inr ent.
Hypothesis TAIL : forall (s : ZSt) mo3, m_fs mo3 = fs -> fd_lookup (m_fds mo3) FD3 = Some ent -> run1 (ra_tail 3 path s) mo3 ok_tr (ok_res, s) FsR.

Lemma mo_open_facts : forall mo, m_fs mo = fs -> m_fs (mo_open ent mo) = fs /\ fd_lookup (m_fds (mo_open ent mo)) FD3 = Some ent.
Proof.
  intros mo Hmf. unfold mo_open. split; [exact Hmf|]. rewrite m_fds_with_fds. unfold fd_insert. cbn [fd_lookup]. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma read_all_O_sound : forall (s : ZSt) mo, m_fs mo = fs -> m_fds mo = bridge_init_fds ->
  sound (zread_all path s) mo
        (fun tr x mo1 => FsR mo1 /\ ((tr = cannot_tr path /\ x = (RdExit, s)) \/ (tr = ok_tr /\ x = (ok_res, s)))).
Proof.
  intros s mo Hmf Hfds. rewrite read_all_eq. unfold mbind at 1.
  eapply sound_ebind; [apply (open_O_sound _ ent s mo Hmf Hfds Hc)|].
  intros tr x mo1 (-> & [(e & -> & ->)|(-> & ->)]); cbn [fst snd app].
  - rewrite <- (app_nil_r (cannot_tr path)). unfold cannot_tr.
    eapply sound_conseq.
    + eapply (proj1 (run1_mbind _ _ s mo _ tt s (eq mo) [] RdExit s (eq mo) (s_diag_run1 (DCannotOpen path) s mo Hp) _)).
    + cbn beta. intros tr2 y mo2 (-> & -> & <-). split; [exact Hmf|]. left. rewrite app_nil_r. auto.
  - destruct (mo_open_facts mo Hmf) as [H1 H2]. eapply sound_conseq; [exact (proj1 (TAIL s _ H1 H2))|].
    cbn beta. intros tr2 y mo2 (-> & -> & HR). split; [exact HR|]. right. auto.
  Unshelve. intros mo1 <-. apply run1_pure. reflexivity.
Qed.

Lemma read_all_O_ex_err : forall (s : ZSt) mo, m_fs mo = fs -> ex (zread_all path s) mo (cannot_tr path) (RdExit, s) FsR.
Proof.
  intros s mo Hmf. rewrite read_all_eq. unfold mbind at 1. change (cannot_tr path) with ([] ++ cannot_tr path).
  eapply ex_ebind; [apply (open_O_ex_err _ ent s mo Hmf Hc)|]. intros mo1 <-. cbn [fst snd].
  unfold cannot_tr. rewrite <- (app_nil_r (Wz 2 _)).
  assert (H : run1 (mbind (io_diag zio (DCannotOpen path)) (fun _ => mret (@RdExit unit)) s) mo (Wz 2 (diag_bytes (DCannotOpen path)) ++ []) (RdExit, s) (eq mo)).
  { eapply run1_mbind; [apply (s_diag_run1 (DCannotOpen path) s mo Hp)|]. intros mo1 <-. apply run1_pure. reflexivity. }
  eapply ex_conseq; [exact (proj2 H)|]. intros mo1 <-. exact Hmf.
Qed.

Lemma read_all_O_ex_ok : forall (s : ZSt) mo, m_fs mo = fs -> m_fds mo = bridge_init_fds -> ex (zread_all path s) mo ok_tr (ok_res, s) FsR.
Proof.
  intros s mo Hmf Hfds. rewrite read_all_eq. unfold mbind at 1. change ok_tr with ([] ++ ok_tr).
  eapply ex_ebind; [apply (open_O_ex_ok _ ent s mo Hmf Hfds Hc)|]. intros mo1 <-. cbn [fst snd].
  destruct (mo_open_facts mo Hmf) as [H1 H2]. exact (proj2 (TAIL s _ H1 H2)).
Qed.
End Openable.

End ReadAll.

(* [comment removed for export] *)
Section Main.
Variable rs : Z.
Variable fs : Fs.Fs.
Notation zio := (ioA AAllocZ).

Lemma land3_range : forall c, 0 <= Z.land c 3 <= 3.
Proof.
  intros c. change 3 with (Z.ones 2) at 1 2. rewrite Z.land_ones by (intro; discriminate). change (2 ^ 2) with 4.
  pose proof (Z.mod_pos_bound c 4 eq_refl). lia.
Qed.

(* [comment removed for export] *)
Lemma runZ_run1 : forall cfg payload cl mo,
  run1 (runA AAllocZ cfg payload (mkZ stdout_init cl)) mo (Wz 1 [48;10])
       (0, mkZ (mkStdout true (zlines (Z.to_nat (Z.land cfg 3))) false false) (Some tt)) (eq mo).
Proof.
  intros cfg payload cl mo. unfold runA, Adapter.target_run.
  pose proof (land3_range cfg) as H3.
  replace (Z.to_nat (1 + Z.land cfg 3)) with (S (Z.to_nat (Z.land cfg 3))) by lia.
  set (k := Z.to_nat (Z.land cfg 3)).
  change (Wz 1 [48;10]) with ([] ++ Wz 1 [48;10]).
  eapply run1_mbind with (R1 := eq mo) (s1 := mkZ stdout_init cl)
    (a := if zlength payload =? 0 then Some None else Some (Some tt)).
  - destruct (zlength payload =? 0); apply run1_pure; reflexivity.
  - intros mo1 <-. destruct (zlength payload =? 0); cbv beta iota.
    + rewrite <- (app_nil_r (Wz 1 [48;10])). eapply run1_mbind.
      * apply (run_calls_first k payload cl mo). unfold k, STDOUT_BUFSIZ. lia.
      * intros mo1 <-. apply run1_pure. reflexivity.
    + rewrite <- (app_nil_r (Wz 1 [48;10])). eapply run1_mbind.
      * apply (run_calls_first k payload cl mo). unfold k, STDOUT_BUFSIZ. lia.
      * intros mo1 <-. apply run1_pure. reflexivity.
Qed.

(* [comment removed for export] *)
Definition main_tail (buf : unit) (content : list Z) : Monad.M ZSt Z :=
  let len := zlength content in
  if len <? HDR_MIN then mbind (io_diag zio DShortHdr) (fun _ => mbind (zfree buf) (fun _ => mret 2))
  else
    let cfg_word := le16 content in
    let count_allocs := Z.testbit cfg_word 15 in
    let config_len := Z.land cfg_word 0x7fff in
    if len <? HDR_MIN + config_len then mbind (io_diag zio DCfgOverrun) (fun _ => mbind (zfree buf) (fun _ => mret 2))
    else
      let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
      let payload := skipn (Z.to_nat (6 + config_len)) content in
      let cfg := if 0 <? config_len then znth content 2 else 0 in
      mbind (alloc_initA AAllocZ bitmap) (fun _ =>
      mbind (runA AAllocZ cfg payload) (fun status =>
      mbind (if count_allocs then mbind (alloc_countA AAllocZ) (fun n => mret (if n <? COUNT_MAX then n else COUNT_MAX)) else mret status) (fun status' =>
      mbind (zfree buf) (fun _ => mret status')))).

(* [comment removed for export] *)
Definition mt_cfg (content : list Z) : Z := if 0 <? Z.land (le16 content) 0x7fff then znth content 2 else 0.
Definition mt_tr (content : list Z) : list event :=
  if zlength content <? HDR_MIN then Wz 2 (diag_bytes DShortHdr)
  else if zlength content <? HDR_MIN + Z.land (le16 content) 0x7fff then Wz 2 (diag_bytes DCfgOverrun)
  else Wz 1 [48;10].
Definition mt_code (content : list Z) : Z :=
  if zlength content <? HDR_MIN then 2 else if zlength content <? HDR_MIN + Z.land (le16 content) 0x7fff then 2 else 0.
Definition mt_st (content : list Z) (cl : option unit) : ZSt :=
  if zlength content <? HDR_MIN then mkZ stdout_init cl
  else if zlength content <? HDR_MIN + Z.land (le16 content) 0x7fff then mkZ stdout_init cl
  else mkZ (mkStdout true (zlines (Z.to_nat (Z.land (mt_cfg content) 3))) false false) (Some tt).

Lemma main_tail_run1 : forall buf content cl mo,
  run1 (main_tail buf content (mkZ stdout_init cl)) mo (mt_tr content) (mt_code content, mt_st content cl) (eq mo).
Proof.
  intros buf content cl mo. unfold main_tail, mt_tr, mt_code, mt_st. cbv zeta.
  destruct (zlength content <? HDR_MIN).
  { rewrite <- (app_nil_r (Wz 2 _)). eapply run1_mbind; [apply (s_diag_run1 DShortHdr _ mo I)|]. intros mo1 <-. apply run1_pure. reflexivity. }
  destruct (zlength content <? HDR_MIN + Z.land (le16 content) 32767).
  { rewrite <- (app_nil_r (Wz 2 _)). eapply run1_mbind; [apply (s_diag_run1 DCfgOverrun _ mo I)|]. intros mo1 <-. apply run1_pure. reflexivity. }
  change (Wz 1 [48;10]) with ([] ++ Wz 1 [48;10]).
  eapply run1_mbind with (R1 := eq mo); [apply run1_pure; reflexivity|]. intros mo1 <-.
  rewrite <- (app_nil_r (Wz 1 [48;10])).
  eapply run1_mbind; [apply runZ_run1|]. intros mo1 <-. fold (mt_cfg content).
  destruct (Z.testbit (le16 content) 15); apply run1_pure; reflexivity.
Qed.

End Main.

(* [comment removed for export] *)
Section Prog.
Variable rs : Z.
Variable fs : Fs.Fs.
Notation zio := (ioA AAllocZ).
Notation zmain := (@main_model ZSt unit zio zmalloc zfree rs (alloc_initA AAllocZ) (runA AAllocZ) (alloc_countA AAllocZ)).
Notation zread_all := (@read_all ZSt unit zio zmalloc zfree rs).

Lemma zmain_eq : forall argv,
  zmain argv = if negb (Z.of_nat (length argv) =? 2)
               then mbind (io_diag zio (DUsage (nth 0 argv []))) (fun _ => mret 2)
               else mbind (zread_all (nth 1 argv [])) (fun ra =>
                      match ra with RdExit => mret 2 | RdDone buf content => main_tail buf content end).
Proof. intros argv. unfold main_model, main_tail. reflexivity. Qed.

(* [comment removed for export] *)
Inductive st_ok : ZSt -> Prop :=
| st_ok_init : forall cl, st_ok (mkZ stdout_init cl)
| st_ok_buf : forall buf cl, zlength buf <= STDOUT_BUFSIZ -> st_ok (mkZ (mkStdout true buf false false) cl).

Lemma mt_st_ok : forall content cl, st_ok (mt_st content cl).
Proof.
  intros content cl. unfold mt_st. destruct (zlength content <? HDR_MIN); [constructor|].
  destruct (zlength content <? HDR_MIN + Z.land (le16 content) 32767); [constructor|].
  constructor. rewrite zlength_zlines. pose proof (land3_range (mt_cfg content)). unfold STDOUT_BUFSIZ. lia.
Qed.

(* [comment removed for export] *)
Definition ptail (code : Z) : Monad.M ZSt Empty_set := mbind (client_exitA AAllocZ) (fun _ => exit_model zio code).

Lemma ptail_xrun : forall code st mo, st_ok st -> m_fs mo = fs ->
  xrun (ptail code st) mo (Wz 1 (so_buf (z_so st)) ++ [ExitEv (Nodes.exit_code code) fs]).
Proof.
  intros code st mo Hst Hmf. unfold ptail, mbind at 1.
  change (Wz 1 (so_buf (z_so st)) ++ [ExitEv (Nodes.exit_code code) fs]) with ([] ++ (Wz 1 (so_buf (z_so st)) ++ [ExitEv (Nodes.exit_code code) fs])).
  destruct st as [so cl]. destruct (client_exitZ_pure so cl) as (cl' & Hce).
  eapply xrun_ebind with (R := eq mo); [apply run1_pure; exact Hce|]. intros mo1 <-. cbn [fst snd z_so].
  unfold exit_model, mbind at 1.
  eapply xrun_ebind with (R := eq mo) (x := (tt, mkZ (if so_active so then mkStdout true [] false false else so) cl')).
  - inversion Hst as [cl0 E0|buf cl0 Hb E0]; subst.
    + cbn [so_buf stdout_init so_active]. apply flush_init.
    + cbn [so_buf so_active]. apply flush_buf. exact Hb.
  - intros mo1 <-. cbn [fst snd]. unfold msys. rewrite <- Hmf. apply xrun_exit.
Qed.

(* [comment removed for export] *)
Lemma prog_of_main : forall argv mo E code st (R : Model -> Prop),
  run1 (zmain argv sZ_init) mo E (code, st) R -> (forall mo1, R mo1 -> m_fs mo1 = fs) -> st_ok st ->
  xrun (progZ_tree rs argv) mo (E ++ Wz 1 (so_buf (z_so st)) ++ [ExitEv (Nodes.exit_code code) fs]).
Proof.
  intros argv mo E code st R Hm HR Hst. unfold progZ_tree, progA_tree. apply xrun_outer.
  unfold progA_main, mbind at 1. eapply xrun_ebind; [exact Hm|]. intros mo1 H1. cbn [fst snd].
  exact (ptail_xrun code st mo1 Hst (HR _ H1)).
Qed.

(* [comment removed for export] *)
Lemma prog_of_main2 : forall argv mo E1 c1 st1 E2 c2 st2,
  sound (zmain argv sZ_init) mo (fun tr x mo1 => m_fs mo1 = fs /\ ((tr = E1 /\ x = (c1, st1)) \/ (tr = E2 /\ x = (c2, st2)))) ->
  ex (zmain argv sZ_init) mo E1 (c1, st1) (fun mo1 => m_fs mo1 = fs) ->
  ex (zmain argv sZ_init) mo E2 (c2, st2) (fun mo1 => m_fs mo1 = fs) ->
  st_ok st1 -> st_ok st2 ->
  let full1 := E1 ++ Wz 1 (so_buf (z_so st1)) ++ [ExitEv (Nodes.exit_code c1) fs] in
  let full2 := E2 ++ Wz 1 (so_buf (z_so st2)) ++ [ExitEv (Nodes.exit_code c2) fs] in
  xsound (progZ_tree rs argv) mo (fun tr => tr = full1 \/ tr = full2)
  /\ texitN (progZ_tree rs argv) mo full1 /\ texitN (progZ_tree rs argv) mo full2.
Proof.
  intros argv mo E1 c1 st1 E2 c2 st2 Hs He1 He2 Hst1 Hst2 full1 full2.
  unfold progZ_tree, progA_tree. split; [|split].
  - apply xsound_outer. unfold progA_main, mbind at 1. eapply xsound_ebind; [exact Hs|].
    intros tr x mo1 (Hmf & [(-> & ->)|(-> & ->)]); cbn [fst snd].
    + destruct (ptail_xrun c1 st1 mo1 Hst1 Hmf) as [[G1 G2] _]. split; [exact G1|]. intros tr2 H2. left. rewrite (G2 _ H2). reflexivity.
    + destruct (ptail_xrun c2 st2 mo1 Hst2 Hmf) as [[G1 G2] _]. split; [exact G1|]. intros tr2 H2. right. rewrite (G2 _ H2). reflexivity.
  - apply texit_ebind_outer. unfold progA_main, mbind at 1. eapply texit_ebind_ex; [exact He1|].
    intros mo1 Hmf. cbn [fst snd]. exact (proj2 (ptail_xrun c1 st1 mo1 Hst1 Hmf)).
  - apply texit_ebind_outer. unfold progA_main, mbind at 1. eapply texit_ebind_ex; [exact He2|].
    intros mo1 Hmf. cbn [fst snd]. exact (proj2 (ptail_xrun c2 st2 mo1 Hst2 Hmf)).
Qed.

(* [comment removed for export] *)
Lemma zmain_usage : forall argv (s : ZSt) mo, length argv <> 2%nat -> PIECE_OK (nth 0 argv []) ->
  run1 (zmain argv s) mo (Wz 2 (diag_bytes (DUsage (nth 0 argv [])))) (2, s) (eq mo).
Proof.
  intros argv s mo Hl Hp. rewrite zmain_eq.
  replace (Z.of_nat (length argv) =? 2) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite <- (app_nil_r (Wz 2 _)). eapply run1_mbind; [apply (s_diag_run1 (DUsage (nth 0 argv [])) s mo Hp)|].
  intros mo1 <-. apply run1_pure. reflexivity.
Qed.

Lemma zmain_T : forall argv e (s : ZSt) mo, length argv = 2%nat -> PIECE_OK (nth 1 argv []) -> m_fs mo = fs ->
  oclass fs (pbytes (nth 1 argv [])) = inl e ->
  run1 (zmain argv s) mo (cannot_tr (nth 1 argv [])) (2, s) (FsR fs).
Proof.
  intros argv e s mo Hl Hp Hmf Hc. rewrite zmain_eq.
  replace (Z.of_nat (length argv) =? 2) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
  rewrite <- (app_nil_r (cannot_tr _)). eapply run1_mbind; [apply (read_all_T rs fs _ e s mo Hp Hmf Hc)|].
  intros mo1 H1. apply run1_conseq with (R := eq mo1); [apply run1_pure; reflexivity|]. intros mo2 <-. exact H1.
Qed.

(* [comment removed for export] *)
Definition after_tr (ra : @rd_result unit) : list event := match ra with RdExit => [] | RdDone _ content => mt_tr content end.
Definition after_code (ra : @rd_result unit) : Z := match ra with RdExit => 2 | RdDone _ content => mt_code content end.
Definition after_st (ra : @rd_result unit) (cl : option unit) : ZSt := match ra with RdExit => mkZ stdout_init cl | RdDone _ content => mt_st content cl end.

Lemma after_run1 : forall ra cl mo,
  run1 ((match ra with RdExit => mret 2 | RdDone buf content => main_tail buf content end) (mkZ stdout_init cl)) mo
       (after_tr ra) (after_code ra, after_st ra cl) (eq mo).
Proof. intros [|buf content] cl mo; [apply run1_pure; reflexivity|apply main_tail_run1]. Qed.

Lemma after_st_ok : forall ra cl, st_ok (after_st ra cl).
Proof. intros [|buf content] cl; [constructor|apply mt_st_ok]. Qed.

Section MainO.
Variable argv : list (list Z).
Variable ent : FdEntry.
Variable ok_tr : list event.
Variable ok_res : @rd_result unit.
Hypothesis Hl : length argv = 2%nat.
Hypothesis Hp : PIECE_OK (nth 1 argv []).
Hypothesis Hc : oclass fs (pbytes (nth 1 argv [])) = inr ent.
Hypothesis TAIL : forall (s : ZSt) mo3, m_fs mo3 = fs -> fd_lookup (m_fds mo3) (Z_to_bv 64 3) = Some ent ->
  run1 (ra_tail rs 3 (nth 1 argv []) s) mo3 ok_tr (ok_res, s) (FsR fs).

Lemma zmain_O_sound : forall cl mo, m_fs mo = fs -> m_fds mo = bridge_init_fds ->
  sound (zmain argv (mkZ stdout_init cl)) mo
        (fun tr x mo1 => m_fs mo1 = fs /\ ((tr = cannot_tr (nth 1 argv []) /\ x = (2, mkZ stdout_init cl))
                                         \/ (tr = ok_tr ++ after_tr ok_res /\ x = (after_code ok_res, after_st ok_res cl)))).
Proof.
  intros cl mo Hmf Hfds. rewrite zmain_eq.
  replace (Z.of_nat (length argv) =? 2) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. unfold mbind at 1.
  eapply sound_ebind; [apply (read_all_O_sound rs fs _ ent ok_tr ok_res Hp Hc TAIL _ mo Hmf Hfds)|].
  intros tr x mo1 (H1 & [(-> & ->)|(-> & ->)]); cbn [fst snd].
  - apply sound_ret. split; [exact H1|]. left. rewrite app_nil_r. auto.
  - eapply sound_conseq; [exact (proj1 (after_run1 ok_res cl mo1))|]. cbn beta. intros tr2 y mo2 (-> & -> & <-).
    split; [exact H1|]. right. auto.
Qed.

Lemma zmain_O_ex_err : forall cl mo, m_fs mo = fs ->
  ex (zmain argv (mkZ stdout_init cl)) mo (cannot_tr (nth 1 argv [])) (2, mkZ stdout_init cl) (fun mo1 => m_fs mo1 = fs).
Proof.
  intros cl mo Hmf. rewrite zmain_eq.
  replace (Z.of_nat (length argv) =? 2) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. unfold mbind at 1.
  rewrite <- (app_nil_r (cannot_tr _)).
  eapply ex_ebind; [apply (read_all_O_ex_err rs fs _ ent Hp Hc _ mo Hmf)|]. intros mo1 H1. cbn [fst snd]. apply ex_ret. exact H1.
Qed.

Lemma zmain_O_ex_ok : forall cl mo, m_fs mo = fs -> m_fds mo = bridge_init_fds ->
  ex (zmain argv (mkZ stdout_init cl)) mo (ok_tr ++ after_tr ok_res) (after_code ok_res, after_st ok_res cl) (fun mo1 => m_fs mo1 = fs).
Proof.
  intros cl mo Hmf Hfds. rewrite zmain_eq.
  replace (Z.of_nat (length argv) =? 2) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. unfold mbind at 1.
  eapply ex_ebind; [apply (read_all_O_ex_ok rs fs _ ent ok_tr ok_res Hc TAIL _ mo Hmf Hfds)|]. intros mo1 H1. cbn [fst snd].
  eapply ex_conseq; [exact (proj2 (after_run1 ok_res cl mo1))|]. intros mo2 <-. exact H1.
Qed.
End MainO.

End Prog.
