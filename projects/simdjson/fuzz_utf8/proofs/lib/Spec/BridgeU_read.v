(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Adapter Driver HarnessU ProgA ProgZ
  BridgeU_base BridgeU_stdio BridgeU_stdout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section ReadLoop.
Variable fd : Z.
Variable rs : Z.
Variable path : list Z.
Variable p : list byte.
Variable data : list byte.
Variable fs : Fs.Fs.
Hypothesis Hfs : fs_lookup fs p = Some data.

Notation FD := (Z_to_bv 64 fd).
Notation zio := (ioA AAllocZ).
Notation zbody := (@read_loop_body ZSt unit zio zmalloc zfree rs fd path).
Let L : Z := Z.of_nat (length data).

(* [comment removed for export] *)
Definition rd_out_tr : list event := if MAX_INPUT <=? Z.of_nat (length data) then Wz 2 (diag_bytes DTooBig) else [].
Definition rd_out_res : @rd_result unit := if MAX_INPUT <=? Z.of_nat (length data) then RdExit else RdDone tt (u8s_of_bytes data).
Definition RdR (mo1 : Model) : Prop := m_fs mo1 = fs /\ fd_lookup (m_fds mo1) FD <> None.

(* [comment removed for export] *)
Lemma read_run1 : forall (s : ZSt) mo off want,
  m_fs mo = fs -> fd_lookup (m_fds mo) FD = Some (FdFile p (Z_to_bv 64 off)) ->
  0 <= off < 2^63 -> 0 <= want < 2^63 ->
  let bs := firstn (Z.to_nat want) (skipn (Z.to_nat off) data) in
  run1 (msys (NRead fd rs want) (dec_read rs want) s) mo [] (RdData bs, s)
       (eq (with_fds (fd_insert (m_fds mo) FD (FdFile p (Z_to_bv 64 (off + Z.of_nat (length bs))))) mo)).
Proof.
  intros s mo off want Hmf Hlk Hoff Hwant bs. unfold msys.
  assert (Ebs : file_read data (Z_to_bv 64 off) (Z_to_bv 64 want) = bs).
  { rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia. reflexivity. }
  assert (Eoff : (Z_to_bv 64 off + len_word bs)%bv = Z_to_bv 64 (off + Z.of_nat (length bs))).
  { unfold len_word. apply lit_add_lit. }
  apply run1_enode_mo.
  - intros rsp mo1 evs Hst. apply nstep_dec_read in Hst; [|lia]. destruct Hst as (-> & a & Hd & Ha).
    destruct a as [e|bs'].
    + destruct Ha as (_ & [[_ Hn]|[_ Hn]]); rewrite Hlk in Hn; discriminate Hn.
    + destruct Ha as (p' & off' & data' & Hlk' & Hfs' & -> & ->).
      rewrite Hlk in Hlk'. injection Hlk' as <- <-. rewrite Hmf, Hfs in Hfs'. injection Hfs' as <-.
      rewrite Ebs in *. rewrite Hd, Eoff. auto.
  - eexists. cbn [nstep]. split; [reflexivity|]. rewrite Hlk, Hmf, Hfs. rewrite Ebs, Eoff. split; reflexivity.
  - intros code mo2 H. exact H.
Qed.

(* [comment removed for export] *)
Definition zgrow (st : @rd_st unit) : Monad.M ZSt (option (@rd_st unit)) :=
  let len := zlength (rd_content st) in
  if len =? rd_cap st then
    if MAX_INPUT <=? rd_cap st then mbind (io_diag zio DTooBig) (fun _ => mret None)
    else mbind (zmalloc (rd_cap st * 2)) (fun nb =>
           match nb with
           | None => mbind (io_diag zio DOom) (fun _ => mret None)
           | Some nb' => mbind (zfree (rd_buf st)) (fun _ => mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st))))
           end)
  else mret (Some st).
Definition zrest (st : @rd_st unit) (g : option (@rd_st unit)) : Monad.M ZSt (@rd_st unit + @rd_result unit) :=
  let len := zlength (rd_content st) in
  match g with
  | None => mret (inr RdExit)
  | Some st1 =>
      let want0 := rd_cap st1 - len in
      let want := if 65536 <? want0 then 65536 else want0 in
      mbind (msys (NRead fd rs want) (dec_read rs want)) (fun a =>
      match a with
      | RdErr _ => mbind (io_diag zio (DReadError path)) (fun _ => mret (inr RdExit))
      | RdData bs =>
          if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
          else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
      end)
  end.
Lemma zbody_eq : forall st, zbody st = mbind (zgrow st) (zrest st).
Proof. reflexivity. Qed.

Lemma u8s_firstn_len : forall off, 0 <= off <= L -> zlength (u8s_of_bytes (firstn (Z.to_nat off) data)) = off.
Proof. intros off H. unfold zlength, u8s_of_bytes, L in *. rewrite length_map, firstn_length_le by lia. lia. Qed.

Lemma firstn_plus : forall {A} (l : list A) a b, firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
  destruct l as [|x l]; [cbn; rewrite firstn_nil; reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zrest_run1 : forall (s : ZSt) mo off cap0 cap1 content,
  m_fs mo = fs -> fd_lookup (m_fds mo) FD = Some (FdFile p (Z_to_bv 64 off)) ->
  0 <= off <= L -> content = u8s_of_bytes (firstn (Z.to_nat off) data) -> off < cap1 <= MAX_INPUT ->
  let want := if 65536 <? cap1 - off then 65536 else cap1 - off in
  let bs := firstn (Z.to_nat want) (skipn (Z.to_nat off) data) in
  let mo' := with_fds (fd_insert (m_fds mo) FD (FdFile p (Z_to_bv 64 (off + Z.of_nat (length bs))))) mo in
  run1 (zrest (mkRd tt cap0 content) (Some (mkRd tt cap1 content)) s) mo []
       ((if (length bs =? 0)%nat then inr (RdDone tt content) else inl (mkRd tt cap1 (content ++ u8s_of_bytes bs))), s) (eq mo').
Proof.
  intros s mo off cap0 cap1 content Hmf Hlk Hoff Hc Hcap want bs mo'.
  assert (Hlen : zlength content = off) by (rewrite Hc; apply u8s_firstn_len; exact Hoff).
  unfold zrest. cbn [rd_cap rd_content rd_buf]. rewrite Hlen. fold want.
  assert (Hw : 1 <= want <= 65536) by (unfold want; destruct (Z.ltb_spec 65536 (cap1 - off)); lia).
  change (@nil event) with (@nil event ++ []).
  eapply run1_mbind.
  - apply (read_run1 s mo off want Hmf Hlk); unfold MAX_INPUT in *; lia.
  - intros mo1 <-. fold bs. fold mo'. destruct (length bs =? 0)%nat; apply run1_pure; reflexivity.
Qed.

Lemma read_loop_run1 : forall fuel (st : @rd_st unit) (s : ZSt) mo off j,
  m_fs mo = fs -> fd_lookup (m_fds mo) FD = Some (FdFile p (Z_to_bv 64 off)) ->
  0 <= off <= L -> rd_content st = u8s_of_bytes (firstn (Z.to_nat off) data) ->
  rd_cap st = 2 ^ (16 + Z.of_nat j) -> (j <= 10)%nat -> off <= rd_cap st ->
  MAX_INPUT - off + 2 <= Z.of_nat fuel ->
  run1 (mloop fuel zbody st s) mo rd_out_tr (rd_out_res, s) RdR.
Proof.
  induction fuel as [|f IH]; intros st s mo off j Hmf Hlk Hoff Hc Hcap Hj Hle Hfuel.
  { exfalso. assert (2 ^ (16 + Z.of_nat j) <= 2 ^ 26) by (apply Z.pow_le_mono_r; lia). unfold MAX_INPUT in Hfuel. lia. }
  assert (Hcap26 : rd_cap st <= MAX_INPUT).
  { rewrite Hcap. unfold MAX_INPUT. change 67108864 with (2 ^ 26). apply Z.pow_le_mono_r; lia. }
  assert (Hlen : zlength (rd_content st) = off) by (rewrite Hc; apply u8s_firstn_len; exact Hoff).
  destruct st as [[] cap content]. cbn [rd_cap rd_content rd_buf] in *.
  cbn [mloop]. rewrite zbody_eq.
  (* [comment removed for export] *)
  assert (GROW : (off = cap /\ MAX_INPUT <= cap) \/
                 exists cap1 j1, zgrow (mkRd tt cap content) s = Ret (Ok (Some (mkRd tt cap1 content), s))
                                 /\ cap1 = 2 ^ (16 + Z.of_nat j1) /\ (j1 <= 10)%nat /\ off < cap1).
  { destruct (Z.eqb_spec off cap) as [Eoc|Eoc].
    - destruct (Z.leb_spec MAX_INPUT cap) as [Hbig|Hsmall]; [left; auto|]. right.
      exists (cap * 2), (S j). split; [|split; [|split]].
      + unfold zgrow. cbn [rd_cap rd_content rd_buf]. rewrite Hlen.
        replace (off =? cap) with true by (symmetry; apply Z.eqb_eq; exact Eoc).
        replace (MAX_INPUT <=? cap) with false by (symmetry; apply Z.leb_gt; exact Hsmall). reflexivity.
      + rewrite Hcap. replace (16 + Z.of_nat (S j)) with ((16 + Z.of_nat j) + 1) by lia. rewrite (Z.pow_add_r 2 (16 + Z.of_nat j) 1) by lia. reflexivity.
      + destruct (Nat.eq_dec j 10) as [->|]; [|lia]. exfalso. rewrite Hcap in Hsmall. unfold MAX_INPUT in Hsmall. cbn in Hsmall. lia.
      + assert (0 < cap) by (rewrite Hcap; apply Z.pow_pos_nonneg; lia). lia.
    - right. exists cap, j. split; [|split; [exact Hcap|split; [exact Hj|lia]]].
      unfold zgrow. cbn [rd_cap rd_content rd_buf]. rewrite Hlen.
      replace (off =? cap) with false by (symmetry; apply Z.eqb_neq; exact Eoc). reflexivity. }
  destruct GROW as [[Eoc Hbig]|(cap1 & j1 & Hg & Hcap1 & Hj1 & Hlt)].
  - (* [comment removed for export] *)
    assert (HL : (MAX_INPUT <=? Z.of_nat (length data)) = true) by (apply Z.leb_le; unfold L in Hoff; lia).
    unfold rd_out_tr, rd_out_res. rewrite HL.
    rewrite <- (app_nil_r (Wz 2 (diag_bytes DTooBig))).
    eapply run1_mbind with (R1 := eq mo).
    + rewrite <- (app_nil_r (Wz 2 (diag_bytes DTooBig))).
      eapply run1_mbind with (R1 := eq mo) (a := None) (s1 := s).
      * unfold zgrow. cbn [rd_cap rd_content]. rewrite Hlen.
        replace (off =? cap) with true by (symmetry; apply Z.eqb_eq; exact Eoc).
        replace (MAX_INPUT <=? cap) with true by (symmetry; apply Z.leb_le; exact Hbig).
        rewrite <- (app_nil_r (Wz 2 (diag_bytes DTooBig))).
        eapply run1_mbind with (R1 := eq mo); [apply (s_diag_run1 DTooBig s mo I)|].
        intros mo1 <-. apply run1_pure. reflexivity.
      * intros mo1 <-. apply run1_pure. reflexivity.
    + intros mo1 <-. apply run1_conseq with (R := eq mo); [apply run1_pure; reflexivity|].
      intros mo1 <-. split; [exact Hmf|]. rewrite Hlk. discriminate.
  - (* [comment removed for export] *)
    assert (Hcap1m : cap1 <= MAX_INPUT).
    { rewrite Hcap1. unfold MAX_INPUT. change 67108864 with (2 ^ 26). apply Z.pow_le_mono_r; lia. }
    pose proof (zrest_run1 s mo off cap cap1 content Hmf Hlk Hoff Hc (conj Hlt Hcap1m)) as HR. cbv zeta in HR.
    set (want := if 65536 <? cap1 - off then 65536 else cap1 - off) in *.
    set (bs := firstn (Z.to_nat want) (skipn (Z.to_nat off) data)) in *.
    set (mo' := with_fds (fd_insert (m_fds mo) FD (FdFile p (Z_to_bv 64 (off + Z.of_nat (length bs))))) mo) in *.
    assert (Hw : 1 <= want <= cap1 - off) by (unfold want; destruct (Z.ltb_spec 65536 (cap1 - off)); lia).
    assert (Hbl : Z.of_nat (length bs) <= want /\ Z.of_nat (length bs) <= L - off).
    { unfold bs, L. rewrite length_firstn, length_skipn. lia. }
    assert (Hmf' : m_fs mo' = fs) by exact Hmf.
    assert (Hlk' : fd_lookup (m_fds mo') FD = Some (FdFile p (Z_to_bv 64 (off + Z.of_nat (length bs))))).
    { unfold mo'. rewrite m_fds_with_fds. unfold fd_insert. cbn [fd_lookup]. rewrite bv_eqb_refl. reflexivity. }
    change rd_out_tr with ([] ++ rd_out_tr).
    eapply run1_mbind with (R1 := eq mo').
    + change (@nil event) with (@nil event ++ []).
      eapply run1_mbind with (R1 := eq mo); [apply run1_pure; exact Hg|]. intros mo1 <-. exact HR.
    + intros mo1 <-. destruct (Nat.eqb_spec (length bs) 0) as [Hz|Hnz].
      * (* [comment removed for export] *)
        assert (HoffL : off = L).
        { unfold bs in Hz. rewrite length_firstn, length_skipn in Hz. unfold L in *. lia. }
        assert (HL : (MAX_INPUT <=? Z.of_nat (length data)) = false) by (apply Z.leb_gt; unfold L in *; lia).
        unfold rd_out_tr, rd_out_res. rewrite HL.
        apply run1_conseq with (R := eq mo').
        -- apply run1_pure. rewrite Hc, HoffL. unfold L. rewrite Nat2Z.id, firstn_all. reflexivity.
        -- intros mo1 <-. split; [exact Hmf'|]. rewrite Hlk'. discriminate.
      * (* [comment removed for export] *)
        apply (IH (mkRd tt cap1 (content ++ u8s_of_bytes bs)) s mo' (off + Z.of_nat (length bs)) j1); cbn [rd_cap rd_content]; try assumption; try lia.
        rewrite Hc. unfold u8s_of_bytes. rewrite <- map_app. f_equal.
        rewrite Z2Nat.inj_add by lia. rewrite Nat2Z.id. rewrite firstn_plus. f_equal.
        unfold bs at 2. rewrite length_firstn. unfold bs.
        generalize (skipn (Z.to_nat off) data) (Z.to_nat want). intros X w. clear.
        revert w. induction X as [|x X IHX]; intros [|w]; cbn; try reflexivity. f_equal. apply IHX.
Qed.

(* [comment removed for export] *)
Lemma read_dir_run1 : forall f (s : ZSt) mo, PIECE_OK path ->
  fd_lookup (m_fds mo) FD = Some FdDir ->
  run1 (mloop (S f) zbody (mkRd tt 65536 []) s) mo (Wz 2 (diag_bytes (DReadError path))) (RdExit, s) (eq mo).
Proof.
  intros f s mo Hp Hlk. cbn [mloop]. rewrite zbody_eq.
  rewrite <- (app_nil_r (Wz 2 (diag_bytes (DReadError path)))).
  eapply run1_mbind with (R1 := eq mo) (a := inr RdExit) (s1 := s).
  - change (Wz 2 (diag_bytes (DReadError path))) with ([] ++ Wz 2 (diag_bytes (DReadError path))).
    eapply run1_mbind with (R1 := eq mo); [apply run1_pure; reflexivity|]. intros mo1 <-.
    unfold zrest. cbn [rd_cap rd_content rd_buf]. change (zlength (@nil Z)) with 0.
    change (if 65536 <? 65536 - 0 then 65536 else 65536 - 0) with 65536.
    change (Wz 2 (diag_bytes (DReadError path))) with ([] ++ Wz 2 (diag_bytes (DReadError path))).
    eapply run1_mbind with (R1 := eq mo) (a := RdErr EISDIR) (s1 := s).
    + unfold msys. apply run1_enode.
      * intros rsp mo1 evs Hst. cbn [nstep] in Hst. rewrite Hlk in Hst. destruct Hst as (-> & -> & ->). auto.
      * exists (efferr EISDIR). cbn [nstep]. rewrite Hlk. auto.
      * intros code mo' H. exact H.
    + intros mo1 <-. rewrite <- (app_nil_r (Wz 2 (diag_bytes (DReadError path)))).
      eapply run1_mbind with (R1 := eq mo); [apply (s_diag_run1 (DReadError path) s mo Hp)|].
      intros mo1 <-. apply run1_pure. reflexivity.
  - intros mo1 <-. apply run1_pure. reflexivity.
Qed.

End ReadLoop.
