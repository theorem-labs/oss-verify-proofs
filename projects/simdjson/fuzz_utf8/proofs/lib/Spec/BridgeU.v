(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Adapter Driver HarnessU ProgA ProgZ
  BridgeU_stmt BridgeU_base BridgeU_stdio BridgeU_stdout BridgeU_read BridgeU_driver.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require ShapeAlg Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Module RA := OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Spec.
Module SA := OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ShapeAlg.

(* [comment removed for export] *)
Lemma is_prefix_refl : forall {A} (l : list A), is_prefix l l.
Proof. induction l; cbn; auto. Qed.

Lemma emit_exit_iff : forall E c fs tr, SA.t_emit E (SA.t_exit c fs) tr <-> is_prefix tr (E ++ [ExitEv c fs]).
Proof.
  intros E c fs tr. unfold SA.t_emit, SA.t_exit, SA.t_nil. split.
  - intros [H|(tr' & -> & [H|(tr'' & -> & ->)])].
    + apply SA.is_prefix_app_r. exact H.
    + clear -H. induction E as [|e E IH]; cbn; [exact H|]. split; [reflexivity|exact IH].
    + rewrite app_nil_r. apply is_prefix_refl.
  - intros H. apply SA.is_prefix_app_split in H as [H|(b' & -> & H)]; [left; exact H|]. right. exists b'. split; [reflexivity|].
    left. exact H.
Qed.

(* [comment removed for export] *)
Lemma traces_of_xrun : forall {X} (t : itree node (exc X)) mo E tr,
  xrun t mo E -> (TopLevel.tree_traces t mo tr <-> is_prefix tr E).
Proof.
  intros X t mo E tr [Hs He]. unfold TopLevel.tree_traces. split.
  - intros (full & Ht & Hp). rewrite (xsound_ttrace t mo _ full Hs Ht) in Hp. exact Hp.
  - intros Hp. exists E. split; [apply texit_ttrace; exact He|exact Hp].
Qed.

Lemma traces_of_x2 : forall {X} (t : itree node (exc X)) mo F1 F2 tr,
  xsound t mo (fun full => full = F1 \/ full = F2) -> texitN t mo F1 -> texitN t mo F2 ->
  (TopLevel.tree_traces t mo tr <-> is_prefix tr F1 \/ is_prefix tr F2).
Proof.
  intros X t mo F1 F2 tr Hs H1 H2. unfold TopLevel.tree_traces. split.
  - intros (full & Ht & Hp). destruct (xsound_ttrace t mo _ full Hs Ht) as [->| ->]; auto.
  - intros [Hp|Hp]; [exists F1|exists F2]; (split; [apply texit_ttrace; assumption|exact Hp]).
Qed.

(* [comment removed for export] *)
Lemma byte_rt : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma to_bytes_u8s : forall l : list byte, to_bytes (map bv_unsigned l) = l.
Proof. intros l. unfold to_bytes. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext. exact byte_rt. Qed.

Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.

Lemma to_bytes_str : forall s, to_bytes (str s) = RA.s2b s.
Proof.
  intros s. unfold to_bytes, str, RA.s2b. rewrite map_map. apply map_ext. intros a. f_equal.
  unfold nat_of_ascii. rewrite N_nat_Z. reflexivity.
Qed.

Lemma Wz_W : forall fd l bs, to_bytes l = bs -> Wz fd l = RA.W fd bs.
Proof. intros fd l bs <-. reflexivity. Qed.

Lemma exit_code_2 : Nodes.exit_code 2 = RA.exit_code 2.
Proof. unfold Nodes.exit_code, RA.exit_code. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma exit_code_0 : Nodes.exit_code 0 = RA.exit_code 0.
Proof. unfold Nodes.exit_code, RA.exit_code. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma msg_usage_eq : forall a0 : list byte, to_bytes (diag_bytes (DUsage (map bv_unsigned a0))) = RA.msg_usage a0.
Proof.
  intros a0. unfold diag_bytes, pieces_usage, RA.msg_usage. cbn [concat]. rewrite !app_nil_r. cbn [app].
  rewrite !to_bytes_app, !to_bytes_str, to_bytes_u8s. reflexivity.
Qed.
Lemma msg_cannot_eq : forall p : list byte, to_bytes (diag_bytes (DCannotOpen (map bv_unsigned p))) = RA.msg_cannot_open p.
Proof.
  intros p. unfold diag_bytes, pieces_cannot_open, RA.msg_cannot_open. cbn [concat]. rewrite !app_nil_r. cbn [app].
  rewrite !to_bytes_app, !to_bytes_str, to_bytes_u8s. reflexivity.
Qed.
Lemma msg_read_eq : forall p : list byte, to_bytes (diag_bytes (DReadError (map bv_unsigned p))) = RA.msg_read_error p.
Proof.
  intros p. unfold diag_bytes, pieces_read_error, RA.msg_read_error. cbn [concat]. rewrite !app_nil_r. cbn [app].
  rewrite !to_bytes_app, !to_bytes_str, to_bytes_u8s. reflexivity.
Qed.
Lemma msg_refused_eq : to_bytes (diag_bytes DTooBig) = RA.msg_refused. Proof. vm_compute. reflexivity. Qed.
Lemma msg_short_eq : to_bytes (diag_bytes DShortHdr) = RA.msg_short. Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_eq : to_bytes (diag_bytes DCfgOverrun) = RA.msg_overrun. Proof. vm_compute. reflexivity. Qed.

Lemma zlines_zero_lines : forall k, to_bytes (zlines k) = RA.zero_lines k.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [zlines RA.zero_lines]. unfold to_bytes in *. cbn [map]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Section Header.
Variable data : list byte.
Let content : list Z := u8s_of_bytes data.

Lemma zlength_content : zlength content = Z.of_nat (length data).
Proof. unfold content, u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.

Lemma znth_content : forall i : nat, znth content (Z.of_nat i) = bv_unsigned (nth i data (Z_to_bv 8 0)).
Proof.
  intros i. unfold znth, content, u8s_of_bytes. destruct (Z.ltb_spec (Z.of_nat i) 0); [lia|]. rewrite Nat2Z.id.
  change 0 with (bv_unsigned (Z_to_bv 8 0)) at 1. apply map_nth.
Qed.

Lemma le16_content : le16 content = RA.cfg_word data.
Proof.
  unfold le16, RA.cfg_word. pose proof (znth_content 0) as H0. pose proof (znth_content 1) as H1.
  change (Z.of_nat 0) with 0 in H0. change (Z.of_nat 1) with 1 in H1. rewrite H0, H1. lia.
Qed.

Lemma land_cfg : Z.land (le16 content) 32767 = RA.cfg_word data mod 32768.
Proof. rewrite le16_content. change 32767 with (Z.ones 15). rewrite Z.land_ones by (intro; discriminate). reflexivity. Qed.

Lemma cfg_mod_nonneg : 0 <= RA.cfg_word data mod 32768.
Proof. apply Z.mod_pos_bound. reflexivity. Qed.

Lemma calls_eq : RA.calls_of data = S (Z.to_nat (Z.land (mt_cfg content) 3)).
Proof.
  unfold RA.calls_of, RA.config_len, mt_cfg. change 32767 with 32767. rewrite land_cfg.
  pose proof cfg_mod_nonneg as Hn. destruct (Z.ltb_spec 0 (RA.cfg_word data mod 32768)) as [Hp|Hz].
  - destruct (Z.to_nat (RA.cfg_word data mod 32768)) eqn:E; [lia|]. f_equal. f_equal.
    pose proof (znth_content 2) as H2. change (Z.of_nat 2) with 2 in H2. rewrite H2.
    change 3 with (Z.ones 2). rewrite Z.land_ones by (intro; discriminate). reflexivity.
  - replace (RA.cfg_word data mod 32768) with 0 by lia. reflexivity.
Qed.

Variable fs : Fs.Fs.

(* [comment removed for export] *)
Definition file_full (cl : option unit) : list event :=
  (rd_out_tr data ++ after_tr (rd_out_res data))
  ++ Wz 1 (so_buf (z_so (after_st (rd_out_res data) cl))) ++ [ExitEv (Nodes.exit_code (after_code (rd_out_res data))) fs].

Lemma file_shape : forall cl tr, RA.t_body data fs tr <-> is_prefix tr (file_full cl).
Proof.
  intros cl tr. unfold RA.t_body, file_full, rd_out_tr, rd_out_res. change RA.MAX_INPUT with MAX_INPUT.
  destruct (MAX_INPUT <=? Z.of_nat (length data)).
  { cbn [after_tr after_st after_code z_so so_buf stdout_init]. change (Wz 1 []) with (@nil event). rewrite app_nil_r. cbn [app].
    unfold RA.t_die. rewrite emit_exit_iff. rewrite (Wz_W 2 _ _ msg_refused_eq), exit_code_2. reflexivity. }
  cbn [after_tr after_st after_code app]. fold content. unfold mt_tr, mt_st, mt_code.
  rewrite zlength_content, land_cfg. unfold RA.HDR_MIN, HDR_MIN, RA.config_len.
  pose proof cfg_mod_nonneg as Hn.
  destruct (Nat.ltb_spec (length data) 6) as [H1|H1]; destruct (Z.ltb_spec (Z.of_nat (length data)) 6) as [H1'|H1']; try lia.
  { cbn [z_so so_buf stdout_init]. change (Wz 1 []) with (@nil event). cbn [app].
    unfold RA.t_die. rewrite emit_exit_iff. rewrite (Wz_W 2 _ _ msg_short_eq), exit_code_2. reflexivity. }
  destruct (Nat.ltb_spec (length data) (6 + Z.to_nat (RA.cfg_word data mod 32768))) as [H2|H2];
    destruct (Z.ltb_spec (Z.of_nat (length data)) (6 + RA.cfg_word data mod 32768)) as [H2'|H2']; try lia.
  { cbn [z_so so_buf stdout_init]. change (Wz 1 []) with (@nil event). cbn [app].
    unfold RA.t_die. rewrite emit_exit_iff. rewrite (Wz_W 2 _ _ msg_overrun_eq), exit_code_2. reflexivity. }
  cbn [z_so so_buf]. rewrite emit_exit_iff. unfold RA.lib_lines, RA.lib_status. rewrite calls_eq. fold content.
  rewrite exit_code_0. rewrite app_assoc, <- Wz_app.
  change ([48; 10] ++ zlines (Z.to_nat (Z.land (mt_cfg content) 3))) with (zlines (S (Z.to_nat (Z.land (mt_cfg content) 3)))).
  rewrite (Wz_W 1 _ _ (zlines_zero_lines _)). reflexivity.
Qed.

End Header.

(* [comment removed for export] *)
Lemma list_byte_eqb_path_eqb : forall p q, RA.list_byte_eqb p q = path_eqb p q.
Proof. induction p as [|a p IH]; intros [|b q]; cbn; try reflexivity; rewrite IH; reflexivity. Qed.

Lemma piece_ok_of_len : forall a : list byte, Z.of_nat (length a) <= 131071 -> PIECE_OK (map bv_unsigned a).
Proof. intros a H. unfold PIECE_OK, WRITE_MAX, INTERNAL_BUFSIZ, zlength. rewrite length_map. lia. Qed.

(* [comment removed for export] *)
Section Bridge.
Variable moZ : Model.
Variable rs : Z.
Variable fs : Fs.Fs.
Hypothesis Hfds : m_fds moZ = bridge_init_fds.
Hypothesis Hfs : m_fs moZ = fs.

Lemma die_iff : forall E msg tr, E = RA.W 2 msg ->
  (is_prefix tr (E ++ Wz 1 (so_buf (z_so (mkZ stdout_init None))) ++ [ExitEv (Nodes.exit_code 2) fs]) <-> RA.t_die msg fs tr).
Proof.
  intros E msg tr ->. cbn [z_so so_buf stdout_init]. change (Wz 1 []) with (@nil event). cbn [app].
  unfold RA.t_die. rewrite emit_exit_iff, exit_code_2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bridge_usage : forall argvb, valid_argv argvb -> length argvb <> 2%nat ->
  xrun (progZ_tree rs (bridge_argv_Z argvb)) moZ
       (RA.W 2 (RA.msg_usage (hd [] argvb)) ++ Wz 1 (so_buf (z_so (mkZ stdout_init None))) ++ [ExitEv (Nodes.exit_code 2) fs]).
Proof.
  intros argvb (_ & _ & Hlen & _) Hl. set (argv := bridge_argv_Z argvb).
  assert (E0 : nth 0 argv [] = map bv_unsigned (hd [] argvb)) by (unfold argv, bridge_argv_Z; destruct argvb; reflexivity).
  assert (Hp : PIECE_OK (nth 0 argv [])).
  { rewrite E0. apply piece_ok_of_len. destruct argvb as [|a0 r]; [cbn; lia|]. inversion Hlen; assumption. }
  rewrite <- (Wz_W 2 _ _ (msg_usage_eq (hd [] argvb))). rewrite <- E0.
  apply (prog_of_main rs fs argv moZ _ 2 (mkZ stdout_init None) (eq moZ)).
  - apply zmain_usage; [unfold argv, bridge_argv_Z; rewrite length_map; exact Hl|exact Hp].
  - intros mo1 <-. exact Hfs.
  - constructor.
Qed.

(* [comment removed for export] *)
Definition core_ok (argvb : list (list byte)) : Prop :=
  exists F1 F2,
    xsound (progZ_tree rs (bridge_argv_Z argvb)) moZ (fun full => full = F1 \/ full = F2)
    /\ texitN (progZ_tree rs (bridge_argv_Z argvb)) moZ F1 /\ texitN (progZ_tree rs (bridge_argv_Z argvb)) moZ F2
    /\ forall tr, (is_prefix tr F1 \/ is_prefix tr F2) <-> RA.spec argvb fs tr.

Lemma core_of_xrun : forall argvb E, xrun (progZ_tree rs (bridge_argv_Z argvb)) moZ E ->
  (forall tr, is_prefix tr E <-> RA.spec argvb fs tr) -> core_ok argvb.
Proof.
  intros argvb E [[H1 H2] He] Hiff. exists E, E. split; [|split; [exact He|split; [exact He|]]].
  - split; [exact H1|]. intros tr Hx. left. exact (H2 _ Hx).
  - intros tr. rewrite <- Hiff. tauto.
Qed.

Theorem bridge_core : forall argvb, valid_argv argvb -> core_ok argvb.
Proof.
  intros argvb Hva. pose proof Hva as (_ & _ & Hlen & _ & Htl).
  destruct argvb as [|a0 [|path [|x r]]].
  1,2,4: (apply (core_of_xrun _ _ (bridge_usage _ Hva ltac:(cbn; lia))); intros tr; cbn [RA.spec hd]; apply die_iff; reflexivity).
  (* [comment removed for export] *)
  set (argv := bridge_argv_Z [a0; path]).
  assert (Hl2 : length argv = 2%nat) by reflexivity.
  assert (Epath : nth 1 argv [] = map bv_unsigned path) by reflexivity.
  assert (Hp : PIECE_OK (nth 1 argv [])).
  { rewrite Epath. apply piece_ok_of_len. inversion Hlen as [|? ? _ Hr]; subst. inversion Hr; assumption. }
  assert (Epb : pbytes (nth 1 argv []) = path) by (rewrite Epath; apply to_bytes_u8s).
  assert (Hdd : path_eqb path dotdot_path = false) by (cbn [tl] in Htl; inversion Htl as [|? ? [_ H] _]; exact H).
  assert (Ecannot : cannot_tr (nth 1 argv []) = RA.W 2 (RA.msg_cannot_open path)).
  { unfold cannot_tr. rewrite Epath. apply Wz_W. apply msg_cannot_eq. }
  assert (DIE : forall e, oclass fs path = inl e ->
            (forall tr, RA.t_die (RA.msg_cannot_open path) fs tr <-> RA.spec [a0; path] fs tr) -> core_ok [a0; path]).
  { intros e Hc Hspec. rewrite <- Epb in Hc.
    apply (core_of_xrun _ _ (prog_of_main rs fs argv moZ _ 2 _ _ (zmain_T rs fs argv _ sZ_init moZ Hl2 Hp Hfs Hc) (fun _ H => H) (st_ok_init None))).
    intros tr. rewrite <- Hspec. apply die_iff. exact Ecannot. }
  assert (TWO : forall ent ok_tr ok_res,
            oclass fs path = inr ent ->
            (forall (s : ZSt) mo3, m_fs mo3 = fs -> fd_lookup (m_fds mo3) (Z_to_bv 64 3) = Some ent ->
               run1 (ra_tail rs 3 (nth 1 argv []) s) mo3 ok_tr (ok_res, s) (FsR fs)) ->
            (forall tr, (RA.t_die (RA.msg_cannot_open path) fs tr
                         \/ is_prefix tr ((ok_tr ++ after_tr ok_res) ++ Wz 1 (so_buf (z_so (after_st ok_res None)))
                                          ++ [ExitEv (Nodes.exit_code (after_code ok_res)) fs]))
                        <-> RA.spec [a0; path] fs tr) ->
            core_ok [a0; path]).
  { intros ent ok_tr ok_res Hc TAIL Hspec. rewrite <- Epb in Hc.
    pose proof (prog_of_main2 rs fs argv moZ _ _ _ _ _ _
                  (zmain_O_sound rs fs argv ent ok_tr ok_res Hl2 Hp Hc TAIL None moZ Hfs Hfds)
                  (zmain_O_ex_err rs fs argv ent Hl2 Hp Hc None moZ Hfs)
                  (zmain_O_ex_ok rs fs argv ent ok_tr ok_res Hl2 Hc TAIL None moZ Hfs Hfds)
                  (st_ok_init None) (after_st_ok ok_res None)) as (Hs & H1 & H2).
    cbv zeta in Hs, H1, H2. eexists _, _. split; [exact Hs|]. split; [exact H1|]. split; [exact H2|].
    intros tr. rewrite <- Hspec. rewrite (die_iff _ (RA.msg_cannot_open path) tr Ecannot). reflexivity. }
  (* [comment removed for export] *)
  assert (SPEC : forall tr, RA.spec [a0; path] fs tr <->
            (if (path_max <=? length path)%nat then RA.t_die (RA.msg_cannot_open path) fs
             else if path_eqb path [] then RA.t_die (RA.msg_cannot_open path) fs
             else if path_eqb path dot_path then SA.t_alt2 (RA.t_die (RA.msg_cannot_open path) fs) (RA.t_opened_dir path fs)
             else match fs_lookup fs path with
                  | None => RA.t_die (RA.msg_cannot_open path) fs
                  | Some data => SA.t_alt2 (RA.t_die (RA.msg_cannot_open path) fs) (RA.t_opened data fs)
                  end) tr) by (intros tr; reflexivity).
  destruct (path_max <=? length path)%nat eqn:Elong.
  { apply (DIE ENAMETOOLONG); [unfold oclass; rewrite Elong; reflexivity|]. intros tr. rewrite SPEC. reflexivity. }
  destruct path as [|c path'].
  { apply (DIE ENOENT); [unfold oclass; rewrite Elong; reflexivity|]. intros tr. rewrite SPEC. reflexivity. }
  set (path := c :: path') in *.
  assert (Hne : path_eqb path [] = false) by reflexivity.
  assert (Hcls : oclass fs path = if path_eqb path dot_path then inr FdDir
                                  else match fs_lookup fs path with None => inl ENOENT | Some _ => inr (FdFile path (Z_to_bv 64 0)) end).
  { unfold oclass. rewrite Elong. unfold path at 1. fold path. unfold path_is_dirref. rewrite Hdd, orb_false_r. reflexivity. }
  rewrite Hne in SPEC.
  destruct (path_eqb path dot_path) eqn:Edot.
  - (* [comment removed for export] *)
    apply (TWO FdDir (Wz 2 (diag_bytes (DReadError (nth 1 argv [])))) RdExit Hcls
             (fun s mo3 H1 H2 => dir_tail_run1 rs fs (nth 1 argv []) s mo3 Hp H1 H2)).
    intros tr. rewrite SPEC. unfold SA.t_alt2, RA.t_opened_dir. cbn [after_tr after_st after_code]. rewrite app_nil_r.
    rewrite (die_iff _ (RA.msg_read_error path) tr); [reflexivity|]. rewrite Epath. apply Wz_W. apply msg_read_eq.
  - destruct (fs_lookup fs path) as [data|] eqn:Elk.
    + (* [comment removed for export] *)
      apply (TWO (FdFile path (Z_to_bv 64 0)) (rd_out_tr data) (rd_out_res data) Hcls
               (fun s mo3 H1 H2 => file_tail_run1 rs fs path data (nth 1 argv []) s mo3 Elk H1 H2)).
      intros tr. rewrite SPEC. unfold SA.t_alt2, RA.t_opened. rewrite (file_shape data fs None tr). reflexivity.
    + apply (DIE ENOENT); [exact Hcls|]. intros tr. rewrite SPEC. reflexivity.
Qed.

End Bridge.

(* [comment removed for export] *)
Theorem bridgeU : bridgeU_stmt.
Proof.
  intros inp moZ rs Hvi _ _ Hfds Hfs tr.
  destruct (bridge_core moZ rs (in_fs inp) Hfds Hfs (in_argv inp) (proj1 Hvi)) as (F1 & F2 & Hs & H1 & H2 & Hiff).
  rewrite <- Hiff. apply traces_of_x2; assumption.
Qed.

(* [comment removed for export] *)
Theorem progZ_no_leaf_gen : forall (inp : ProcInput) (moZ : Model) (rs : Z),
  valid_input_either inp -> m_fds moZ = bridge_init_fds -> m_fs moZ = in_fs inp ->
  forall tr r mo', ~ tpath nstep (progZ_tree rs (bridge_argv_Z (in_argv inp))) moZ tr r mo'.
Proof.
  intros inp moZ rs Hvi Hfds Hfs.
  destruct (bridge_core moZ rs (in_fs inp) Hfds Hfs (in_argv inp) (proj1 Hvi)) as (F1 & F2 & Hs & _).
  exact (xsound_no_leaf _ _ _ Hs).
Qed.
