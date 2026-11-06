(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import RelSpec SimInv ExitSim PropExec CatSim CatExec ErrEscape SeqExec StreamExec StreamSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.
Lemma with_fds_halted : forall f m, m_halted (with_fds f m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
Proof. reflexivity. Qed.
Lemma with_fs_fs : forall f m, m_fs (with_fs f m) = f.
Proof. reflexivity. Qed.
Lemma with_fs_halted : forall f m, m_halted (with_fs f m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_fs_fds : forall f m, m_fds (with_fs f m) = m_fds m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_eff_ret : forall regs pc x8 mem rom r,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mem; ms_rom := rom |} (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
  intros regs pc x8 mem rom r.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes apply_zeros].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma adv_eff_ret_copyins : forall regs pc x8 mem rom r copyins,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mem; ms_rom := rom |}
    (with_copyins copyins (mkEffect r [] [])))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
  intros regs pc x8 mem rom r copyins.
  unfold with_copyins.
  apply adv_eff_ret.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
Lemma in_wmem_si : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma path_eqb_neq : forall p q, p <> q -> path_eqb p q = false.
Proof.
  intros p q Hne. destruct (path_eqb p q) eqn:E; [|reflexivity].
  apply path_eqb_eq in E. congruence.
Qed.

Lemma fs_lookup_set_eq : forall fs p d, fs_lookup (fs_set fs p d) p = Some d.
Proof.
  induction fs as [|[q dq] fs IH]; intros p d; cbn.
  - rewrite path_eqb_refl. reflexivity.
  - destruct (path_ltb p q); cbn.
    + rewrite path_eqb_refl. reflexivity.
    + destruct (path_eqb p q) eqn:E; cbn.
      * rewrite path_eqb_refl. reflexivity.
      * rewrite E. apply IH.
Qed.

Lemma fs_lookup_set_neq : forall fs p d q, q <> p ->
  fs_lookup (fs_set fs p d) q = fs_lookup fs q.
Proof.
  induction fs as [|[r dr] fs IH]; intros p d q Hne; cbn.
  - rewrite path_eqb_neq by exact Hne. reflexivity.
  - destruct (path_ltb p r); cbn.
    + rewrite path_eqb_neq by exact Hne. reflexivity.
    + destruct (path_eqb p r) eqn:E; cbn.
      * apply path_eqb_eq in E. subst r.
        rewrite path_eqb_neq by exact Hne. reflexivity.
      * destruct (path_eqb q r); [reflexivity | apply IH; exact Hne].
Qed.

Lemma path_ltb_irrefl : forall p, path_ltb p p = false.
Proof.
  induction p as [|a p IH]; cbn; [reflexivity|].
  unfold bv_ltu. rewrite Z.ltb_irrefl, bv_eqb_refl, IH. reflexivity.
Qed.

Lemma fs_set_set : forall fs p d d', fs_set (fs_set fs p d) p d' = fs_set fs p d'.
Proof.
  induction fs as [|[q dq] fs IH]; intros p d d'; cbn.
  - rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
  - destruct (path_ltb p q) eqn:EL; cbn.
    + rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
    + destruct (path_eqb p q) eqn:EE; cbn.
      * rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
      * rewrite EL, EE, IH. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd_lookup_cons_eq : forall fds fd e, fd_lookup ((fd, e) :: fds) fd = Some e.
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma fd_lookup_cons_neq : forall fds k e fd, k <> fd ->
  fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd.
Proof.
  intros fds k e fd Hne. cbn.
  rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

Lemma fd_lookup_cons_None : forall fds k e fd,
  fd_lookup ((k, e) :: fds) fd = None -> k <> fd /\ fd_lookup fds fd = None.
Proof.
  intros fds k e fd H. cbn in H.
  destruct (bv_eqb k fd) eqn:E; [discriminate|].
  split; [|exact H].
  intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma fd_filter_id : forall fds fd,
  fd_lookup fds fd = None ->
  List.filter (fun p => negb (bv_eqb (fst p) fd)) fds = fds.
Proof.
  induction fds as [|[k e] fds IH]; intros fd H; [reflexivity|].
  apply fd_lookup_cons_None in H. destruct H as [Hne H].
  cbn [List.filter fst]. rewrite (bv_eqb_neq k fd Hne). cbn [negb].
  rewrite IH by exact H. reflexivity.
Qed.

Lemma fd_insert_fresh : forall fds fd e,
  fd_lookup fds fd = None -> fd_insert fds fd e = (fd, e) :: fds.
Proof.
  intros fds fd e H. unfold fd_insert. rewrite fd_filter_id by exact H.
  reflexivity.
Qed.

Lemma fd_lookup_filter_neq : forall fds fd fd', fd' <> fd ->
  fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) fd' = fd_lookup fds fd'.
Proof.
  induction fds as [|[k e] fds IH]; intros fd fd' Hne; [reflexivity|].
  cbn [List.filter fst].
  destruct (bv_eqb k fd) eqn:Hk.
  - apply bv_eqb_eq in Hk. subst k.
    cbn [negb]. rewrite IH by exact Hne. cbn [fd_lookup].
    rewrite bv_eqb_neq by congruence. reflexivity.
  - cbn [negb fd_lookup]. destruct (bv_eqb k fd'); [reflexivity | apply IH; exact Hne].
Qed.

Lemma fd_lookup_insert_eq : forall fds fd e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros. unfold fd_insert. apply fd_lookup_cons_eq. Qed.

Lemma fd_lookup_insert_neq : forall fds fd e fd', fd' <> fd ->
  fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd'.
Proof.
  intros fds fd e fd' Hne. unfold fd_insert.
  rewrite fd_lookup_cons_neq by congruence.
  apply fd_lookup_filter_neq. exact Hne.
Qed.

Lemma fd_lookup_remove_neq : forall fds fd fd', fd' <> fd ->
  fd_lookup (fd_remove fds fd) fd' = fd_lookup fds fd'.
Proof. intros. unfold fd_remove. apply fd_lookup_filter_neq. assumption. Qed.

Lemma fd_lookup_some_none_neq : forall fds a b ea,
  fd_lookup fds a = Some ea -> fd_lookup fds b = None -> a <> b.
Proof. intros fds a b ea Ha Hb ->. congruence. Qed.

(* [comment removed for export] *)
Lemma free_fd_after_open : forall x y z fdin e,
  exists w, fd_lookup (fd_insert
      [(Z_to_bv 64 0, x); (Z_to_bv 64 1, y); (Z_to_bv 64 2, z)] fdin e) w = None
    /\ (bv_unsigned w < 2 ^ 31)%Z.
Proof.
  intros x y z fdin e.
  destruct (decide (fdin = Z_to_bv 64 3)) as [->|Hne].
  - exists (Z_to_bv 64 4). split.
    + rewrite fd_lookup_insert_neq
        by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
      reflexivity.
    + change (bv_unsigned (Z_to_bv 64 4)) with 4%Z. lia.
  - exists (Z_to_bv 64 3). split.
    + rewrite fd_lookup_insert_neq by congruence. reflexivity.
    + change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
Qed.

Lemma filter_fd_cons_keep : forall {B} (fds : list (word * B)) k (e : B) fd,
  k <> fd ->
  List.filter (fun p => negb (bv_eqb (fst p) fd)) ((k, e) :: fds)
  = (k, e) :: List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
  intros B fds k e fd Hne. cbn [List.filter fst].
  rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

Lemma filter_fd_cons_drop : forall {B} (fds : list (word * B)) fd (e : B),
  List.filter (fun p => negb (bv_eqb (fst p) fd)) ((fd, e) :: fds)
  = List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
  intros B fds fd e. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_file_read : forall data off count,
  length (file_read data off count)
  = Nat.min (word_to_nat count) (length data - word_to_nat off)%nat.
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite length_firstn, length_skipn. reflexivity.
Qed.

Lemma file_read_nil : forall data off count,
  (length data <= word_to_nat off)%nat -> file_read data off count = [].
Proof.
  intros data off count H. rewrite file_read_unguarded.
  rewrite skipn_all2 by exact H. apply firstn_nil.
Qed.

(* [comment removed for export] *)
Lemma file_write_append : forall data off bs,
  word_to_nat off = length data -> file_write data off bs = data ++ bs.
Proof.
  intros data off bs Hoff. unfold file_write.
  destruct bs as [|b bs]; [now rewrite app_nil_r|]. cbv zeta.
  rewrite Hoff, Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
  rewrite firstn_all.
  rewrite skipn_all2 by lia.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma firstn_add {A} : forall (l : list A) n m,
  firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  induction l as [|x l IH]; intros n m.
  - rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|].
    cbn [firstn skipn Nat.add app]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma copy_step : forall data (off count : word),
  firstn (word_to_nat off) data ++ file_read data off count
  = firstn (word_to_nat off
            + Nat.min (word_to_nat count) (length data - word_to_nat off)) data.
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite firstn_add. f_equal.
  destruct (Nat.le_ge_cases (word_to_nat count)
              (length data - word_to_nat off)) as [H|H].
  - rewrite Nat.min_l by exact H. reflexivity.
  - rewrite Nat.min_r by exact H.
    rewrite firstn_all2 by (rewrite length_skipn; lia).
    rewrite firstn_all2 by (rewrite length_skipn; lia).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrb (segs : list Segment) (mem : word -> option byte)
    : word -> option byte :=
  fun a => match mem a with Some b => Some b | None => seg_rom segs a end.

Lemma ms_read_byte_mrb : forall segs regs pc mem,
  ms_read_byte (mkst regs pc mem (seg_rom segs)) = mrb segs mem.
Proof. reflexivity. Qed.

Lemma ms_read_byte_rec_mrb : forall segs regs fr pc sv rv fc mem,
  ms_read_byte {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := sv;
                  ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := seg_rom segs |}
  = mrb segs mem.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mrb_first : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> mrb segs mem a = Some b.
Proof.
  intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; congruence.
Qed.

(* [comment removed for export] *)
Lemma rdn_tail : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> rdn segs mem (a + 1) n = Some rest.
Proof.
  intros segs mem a n b rest H. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; reflexivity.
Qed.

Lemma read_cstr_aux_of_rdn : forall segs str fuel mem a,
  (length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
  rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
  read_cstr_aux (mrb segs mem) a fuel = CstrOk str.
Proof.
  intros segs str; induction str as [|b str IH]; intros fuel mem a Hf Hnz Hr.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    assert (Hb0 : mrb segs mem a = Some (Z_to_bv 8 0))
      by (apply (mrb_first segs mem a 0 (Z_to_bv 8 0) []); exact Hr).
    cbn [read_cstr_aux]. rewrite Hb0. reflexivity.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    cbn [read_cstr_aux]. cbn [app] in Hr.
    assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
    assert (Hfirst : mrb segs mem a = Some b)
      by (apply (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    assert (Htail : rdn segs mem (a + 1) (length str + 1)
                    = Some (str ++ [Z_to_bv 8 0]))
      by (apply (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
    rewrite (IH fuel mem (a + 1) ltac:(lia)
               ltac:(intro; apply Hnz; right; assumption) Htail).
    reflexivity.
Qed.

Lemma read_cstr_of_rdn : forall segs mem a str,
  (length str <= 4095)%nat -> ~ In (Z_to_bv 8 0) str ->
  rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
  read_cstr (mrb segs mem) a = CstrOk str.
Proof.
  intros segs mem a str Hlen Hnz Hr.
  unfold read_cstr. apply read_cstr_aux_of_rdn; [|exact Hnz|exact Hr].
  change path_max with 4096%nat. lia.
Qed.

(* [comment removed for export] *)
Lemma read_cstr_aux_toolong_of_rdn : forall segs fuel bs mem a,
  length bs = fuel -> ~ In (Z_to_bv 8 0) bs ->
  rdn segs mem a fuel = Some bs ->
  read_cstr_aux (mrb segs mem) a fuel = CstrTooLong.
Proof.
  intros segs fuel; induction fuel as [|fuel IH]; intros bs mem a Hlen Hnz Hr;
    [reflexivity|].
  destruct bs as [|b bs]; [cbn in Hlen; lia|].
  cbn [read_cstr_aux].
  assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
  assert (Hfirst : mrb segs mem a = Some b)
    by (apply (mrb_first segs mem a fuel b bs); exact Hr).
  assert (Htail : rdn segs mem (a + 1) fuel = Some bs)
    by (apply (rdn_tail segs mem a fuel b bs); exact Hr).
  rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
  rewrite (IH bs mem (a + 1) ltac:(cbn in Hlen; lia)
             ltac:(intro; apply Hnz; right; assumption) Htail).
  reflexivity.
Qed.

Lemma read_cstr_toolong_of_rdn : forall segs mem a bs,
  length bs = 4096%nat -> ~ In (Z_to_bv 8 0) bs ->
  rdn segs mem a 4096%nat = Some bs ->
  read_cstr (mrb segs mem) a = CstrTooLong.
Proof.
  intros segs mem a bs Hlen Hnz Hr.
  unfold read_cstr. change path_max with 4096%nat.
  eapply read_cstr_aux_toolong_of_rdn; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_argv_cstr_k : forall ph segs (sp : word) av ev k uid hw rnd,
  (k < length av)%nat ->
  (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
      (cat_argv_ptr sp av ev k) (length (nth k av []) + 1)
  = Some (nth k av [] ++ [Z_to_bv 8 0]).
Proof.
  intros ph segs sp av ev k uid hw rnd Hk Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    pre (nth k av [] ++ [Z_to_bv 8 0]) post (length (nth k av []) + 1)) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr sp av ev k)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [exact E | | exact Hnw].
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma read_argv_prefix_k : forall ph segs (sp : word) av ev k n uid hw rnd,
  (k < length av)%nat -> (n <= length (nth k av []))%nat ->
  (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
      (cat_argv_ptr sp av ev k) n
  = Some (firstn n (nth k av [])).
Proof.
  intros ph segs sp av ev k n uid hw rnd Hk Hn Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    pre (firstn n (nth k av []))
    ((skipn n (nth k av []) ++ [Z_to_bv 8 0]) ++ post) n) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr sp av ev k)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [| |exact Hnw].
  - rewrite E. rewrite <- !app_assoc.
    rewrite (app_assoc (firstn n (nth k av [])) (skipn n (nth k av []))).
    rewrite firstn_skipn. reflexivity.
  - apply firstn_length_le. exact Hn.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fd_not_error : forall fd : word,
  (bv_unsigned fd < 2 ^ 31)%Z -> addr_is_error_b fd = false.
Proof.
  intros fd H. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
Proof. left. reflexivity. Qed.

Lemma openat_errno_range : forall e,
  In e openat_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range openat_errnos e eq_refl HIn). Qed.

(* [comment removed for export] *)
Definition open_copyins (ms : machine_state) : list (word * nat) :=
  [(ms_gpr ms 1,
    cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)].

Lemma open_copyins_reads : forall segs ms x8,
  open_reads (sys_input segs ms x8) (ms_gpr ms 1) = open_copyins ms.
Proof. reflexivity. Qed.
