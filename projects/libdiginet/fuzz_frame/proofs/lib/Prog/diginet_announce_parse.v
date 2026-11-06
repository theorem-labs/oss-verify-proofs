(* Walk of diginet_announce_parse (src/diginet_frame.c:138-151 at 835f336c) in fuzz_frame.plain,
   0x13ab0..0x13b84. The two loops at 0x13b00 and 0x13b44 are the inlined copy_strz
   (src/diginet_frame.c:130-136) of the version (body + 15) and of the name (body + 24); each
   copies at most 9 bytes and stops at a NUL. The 24 bytes ap + 0 .. ap + 23 are one byte cell
   while the loops run; INV is the state of memory at each loop head.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_announce_parse_c.
Import ListNotations.
Open Scope Z_scope.

(** * Lists *)

Lemma ne_skipn : forall {A} (l : list A) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros A l n. revert l. induction n as [|n IH]; intros [|x l] i; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma at8_ne : forall l i b, nth_error l i = Some b -> at8 l i = bz b.
Proof.
  induction l as [|x l IH]; intros [|i] b H; cbn in H; try discriminate.
  - injection H as E. subst. reflexivity.
  - unfold at8 in *. cbn [nth]. apply IH. exact H.
Qed.

Lemma byte_at : forall (l : list byte) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof.
  intros l i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|].
  apply nth_error_None in N. lia.
Qed.

Lemma firstn_snoc_nth : forall (s : list byte) j b, nth_error s j = Some b -> firstn (S j) s = firstn j s ++ [b].
Proof.
  induction s as [|c s IH]; intros [|j] b H; cbn in H; try discriminate.
  - injection H as E. subst. reflexivity.
  - cbn [firstn]. rewrite (IH j b H). reflexivity.
Qed.

Lemma upd_bytes_app_l : forall (xs ys bs : list byte) i, (i + length bs <= length xs)%nat ->
  upd_bytes (xs ++ ys) i bs = upd_bytes xs i bs ++ ys.
Proof.
  intros xs ys bs i H. unfold upd_bytes. rewrite firstn_app, skipn_app.
  replace (i - length xs)%nat with 0%nat by lia.
  replace (i + length bs - length xs)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r. rewrite !app_assoc. reflexivity.
Qed.

Lemma upd_at_end : forall (P R : list byte) i z, length P = i -> upd_bytes (P ++ R) i [z] = P ++ z :: skipn 1 R.
Proof.
  intros P R i z <-. unfold upd_bytes. rewrite firstn_app, skipn_app, Nat.sub_diag, firstn_all.
  rewrite (skipn_all2 (n := (length P + length [z])%nat) P) by (cbn [length]; lia).
  cbn [length]. replace (length P + 1 - length P)%nat with 1%nat by lia.
  cbn [firstn app]. rewrite app_nil_r. reflexivity.
Qed.

(* One byte of the loop: the field at o holds j bytes of s, then byte j of s is stored. *)
Lemma upd_snoc : forall (V s X : list byte) (o j : nat) b, length V = o -> nth_error s j = Some b ->
  upd_bytes (V ++ firstn j s ++ skipn (o + j) X) (o + j) [b] = V ++ firstn (S j) s ++ skipn (o + S j) X.
Proof.
  intros V s X o j b HV Hn.
  assert (Hj : (j < length s)%nat) by (apply nth_error_Some; congruence).
  rewrite (app_assoc V (firstn j s) (skipn (o + j) X)).
  rewrite upd_at_end by (rewrite length_app, length_firstn; lia).
  rewrite (firstn_snoc_nth s j b Hn). rewrite skipn_skipn.
  replace (1 + (o + j))%nat with (o + S j)%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma skipn_firstn_app : forall (l : list byte) a n, (a <= n)%nat -> (n <= length l)%nat ->
  skipn a l = skipn a (firstn n l) ++ skipn n l.
Proof.
  intros l a n H1 H2. rewrite <- (firstn_skipn n l) at 1. rewrite skipn_app, length_firstn.
  replace (a - Nat.min n (length l))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma strz_len_le_len : forall src, (strz_len src <= length src)%nat.
Proof.
  intros src. unfold strz_len. pose proof (nz_run_le (firstn 9 src)) as H. rewrite length_firstn in H. lia.
Qed.

(* The 24 bytes after the NUL of the version. *)
Lemma ver_nul : forall (bb aj : list byte), length aj = 40%nat ->
  upd_bytes (firstn (strz_len (skipn 15 bb)) (skipn 15 bb) ++ skipn (strz_len (skipn 15 bb)) (firstn 24 aj))
            (strz_len (skipn 15 bb)) [b8 0]
  = ann_version bb (firstn 10 aj) ++ skipn 10 (firstn 24 aj).
Proof.
  intros bb aj Haj.
  pose proof (strz_len_le (skipn 15 bb)) as Hk.
  pose proof (strz_len_le_len (skipn 15 bb)) as Hk2.
  rewrite upd_at_end by (rewrite length_firstn; lia).
  unfold ann_version, copy_strz. change (copy_len 10 9 (skipn 15 bb)) with (strz_len (skipn 15 bb)).
  rewrite <- app_assoc. cbn [app]. f_equal. f_equal.
  rewrite skipn_skipn. cbn [Nat.add].
  replace (firstn 10 aj) with (firstn 10 (firstn 24 aj)) by (rewrite firstn_firstn; reflexivity).
  apply skipn_firstn_app; [lia | rewrite length_firstn; lia].
Qed.

(* The 24 bytes after the NUL of the name: version, name, 4 bytes not written. *)
Lemma name_nul : forall (bb aj : list byte), length aj = 40%nat ->
  upd_bytes (ann_version bb (firstn 10 aj) ++ firstn (strz_len (skipn 24 bb)) (skipn 24 bb)
               ++ skipn (10 + strz_len (skipn 24 bb)) (firstn 24 aj))
            (10 + strz_len (skipn 24 bb)) [b8 0]
  = ann_version bb (firstn 10 aj) ++ ann_name bb (firstn 10 (skipn 10 aj)) ++ firstn 4 (skipn 20 aj).
Proof.
  intros bb aj Haj.
  pose proof (strz_len_le (skipn 24 bb)) as Hk.
  pose proof (strz_len_le_len (skipn 24 bb)) as Hk2.
  assert (HV : length (ann_version bb (firstn 10 aj)) = 10%nat)
    by (apply length_copy_strz; rewrite length_firstn; lia).
  rewrite app_assoc.
  rewrite upd_at_end by (rewrite length_app, length_firstn; lia).
  rewrite <- app_assoc. f_equal.
  unfold ann_name, copy_strz. change (copy_len 10 9 (skipn 24 bb)) with (strz_len (skipn 24 bb)).
  rewrite <- app_assoc. cbn [app]. f_equal. f_equal.
  rewrite skipn_skipn.
  replace (1 + (10 + strz_len (skipn 24 bb)))%nat with (S (strz_len (skipn 24 bb)) + 10)%nat by lia.
  rewrite <- skipn_skipn. rewrite skipn_firstn_comm.
  replace (24 - 10)%nat with 14%nat by reflexivity.
  rewrite (skipn_firstn_app (firstn 14 (skipn 10 aj)) (S (strz_len (skipn 24 bb))) 10)
    by (try lia; rewrite length_firstn, length_skipn; lia).
  rewrite firstn_firstn. replace (Nat.min 10 14) with 10%nat by reflexivity.
  f_equal. rewrite skipn_firstn_comm, skipn_skipn. reflexivity.
Qed.

(** * Memory *)

Lemma ro_of_bytes : forall m A cs, cells_wf cs -> bytes_at rsegs m A (cells_bytes cs) -> ro_cells rsegs m A cs.
Proof. intros m A cs H1 H2. split; assumption. Qed.

Lemma firstn1_skipn : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma rdb : forall m A l (i : nat) b, bytes_at rsegs m A l -> nth_error l i = Some b ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m A l i b BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL ltac:(lia)). f_equal. apply firstn1_skipn. exact N.
Qed.

(* A byte store at A + i inside the byte cell that starts at A. *)
Lemma stb : forall W m0 m1 A n xs cs (i : nat) (b : byte),
  rw_cells rsegs m1 A (CB n xs :: cs) -> (i < n)%nat ->
  munch W m0 m1 -> inside W (A + Z.of_nat i) 1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs (write_to_mem m1 (wa (A + Z.of_nat i)) [b]) A (CB n (upd_bytes xs i [b]) :: cs) /\
  munch W m0 (write_to_mem m1 (wa (A + Z.of_nat i)) [b]) /\
  wmono rsegs m0 (write_to_mem m1 (wa (A + Z.of_nat i)) [b]) /\
  mem_inv rsegs (write_to_mem m1 (wa (A + Z.of_nat i)) [b]).
Proof.
  intros W m0 m1 A n xs cs i b [[[Hl Hwf] Hb] Hw] Hi MU Hin WM MI.
  cbn [cells_bytes cbytes cells_size csize] in Hb, Hw. cbn [cell_wf] in Hl.
  pose proof (bytes_at_bound rsegs _ _ _ Hb) as HB. rewrite length_app in HB.
  assert (HS : store_ok rsegs m1 (wa (A + Z.of_nat i)) 1 = true)
    by (apply (wr_at_store_ok rsegs m1 A _ (Z.of_nat i) 1 Hw); lia).
  split; [|split; [|split]].
  - split; [split|].
    + cbn [cells_wf cell_wf]. split; [|exact Hwf]. rewrite upd_bytes_length; cbn [length]; lia.
    + cbn [cells_bytes cbytes].
      pose proof (bytes_at_write_inside rsegs m1 A (xs ++ cells_bytes cs) (Z.of_nat i) [b] Hb ltac:(lia)
                    ltac:(rewrite length_app; cbn [length]; lia)) as W1.
      rewrite Nat2Z.id in W1. rewrite upd_bytes_app_l in W1 by (cbn [length]; lia). exact W1.
    + cbn [cells_size csize]. apply wr_at_write. exact Hw.
  - apply munch_write; [exact MU | lia | cbn [length]; lia | exact Hin].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS].
Qed.

(* The memory at a loop head: the 40 bytes at ap are the byte cell L of 24 bytes, unknown and
   unknown_len; the frame fields and the body are unchanged. *)
Definition INV (m0 m1 : word -> option byte) (ap f body : Z) (bb L : list byte) : Prop :=
  rw_cells rsegs m1 ap [CB 24 L; C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 15)] /\
  munch [(ap, ap + 40)] m0 m1 /\ wmono rsegs m0 m1 /\ mem_inv rsegs m1 /\
  bytes_at rsegs m1 body bb /\
  ro_cells rsegs m1 (f + 32) [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 (Z.of_nat (length bb)))].

Lemma inv_store_ok : forall m0 m1 ap f body bb L (i : nat) (w : word),
  INV m0 m1 ap f body bb L -> (i < 24)%nat -> w = Z_to_bv 64 (ap + Z.of_nat i) ->
  store_ok rsegs m1 w 1 = true.
Proof.
  intros m0 m1 ap f body bb L i w (CA & _) Hi ->. destruct CA as [_ Hw].
  cbn [cells_size csize Nat.add] in Hw.
  exact (wr_at_store_ok rsegs m1 ap _ (Z.of_nat i) 1 Hw ltac:(lia) ltac:(lia)).
Qed.

Lemma inv_rd : forall m0 m1 ap f body bb L (n : nat) b,
  INV m0 m1 ap f body bb L -> nth_error bb n = Some b ->
  ov_read_bytes rsegs m1 (wa (body + Z.of_nat n)) 1 = Some [b].
Proof. intros m0 m1 ap f body bb L n b (_ & _ & _ & _ & BB & _) N. eapply rdb; eauto. Qed.

Lemma stb_inv : forall m0 m1 ap f body bb L (i : nat) (w : word) (b : byte),
  INV m0 m1 ap f body bb L -> (i < 24)%nat -> w = Z_to_bv 64 (ap + Z.of_nat i) ->
  (ap + 40 <= body \/ body + Z.of_nat (length bb) <= ap) -> (ap + 40 <= f + 30 \/ f + 48 <= ap) ->
  INV m0 (write_to_mem m1 w [b]) ap f body bb (upd_bytes L i [b]).
Proof.
  intros m0 m1 ap f body bb L i w b (CA & MU & WM & MI & BB & RF) Hi -> DB DF.
  pose proof (rw_cells_bound rsegs m1 ap _ CA) as HA. cbn [cells_size csize Nat.add] in HA.
  destruct (stb [(ap, ap + 40)] m0 m1 ap 24 L [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 15)] i b
              CA Hi MU ltac:(cbn [inside]; lia) WM MI) as (CA' & MU' & WM' & MI').
  refine (conj CA' (conj MU' (conj WM' (conj MI' (conj _ _))))).
  - apply bytes_at_write_other; [exact BB | lia | cbn [length]; lia | cbn [length]; lia].
  - apply ro_cells_frame; [exact RF | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
Qed.

Lemma rw_split3 : forall m A (V N T : list byte) cs, length V = 10%nat -> length N = 10%nat -> length T = 4%nat ->
  rw_cells rsegs m A (CB 24 (V ++ N ++ T) :: cs) -> rw_cells rsegs m A (CB 10 V :: CB 10 N :: CB 4 T :: cs).
Proof.
  intros m A V N T cs HV HN HT [[[_ Hwf] Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite <- !app_assoc in Hb. exact Hb.
  - cbn [cells_size csize] in *. replace (10 + (10 + (4 + cells_size cs)))%nat with (24 + cells_size cs)%nat by lia.
    exact Hw.
Qed.

(** * Words *)

Lemma eqb_nz : forall x, x <> 0 -> -2^64 < x < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof.
  intros x H1 H2. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). apply Z.eqb_neq. rewrite Z.mod_0_l by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cmd_test : forall cmd, 0 <= cmd < 2^8 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 cmd))) 254)) (Z_to_bv 64 224) = ann_cmd cmd.
Proof.
  assert (G : forall cmd, 0 <= cmd < 2^8 ->
    Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 cmd))) 254)) (Z_to_bv 64 224)) (ann_cmd cmd) = true).
  { apply (byte_forall (fun cmd =>
      Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 cmd))) 254)) (Z_to_bv 64 224)) (ann_cmd cmd))).
    vm_compute. reflexivity. }
  intros cmd Hc. apply Bool.eqb_prop. exact (G cmd Hc).
Qed.

Lemma zb_eq0 : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bz b =? 0).
Proof.
  intros b. pose proof (bz_range b) as R. unfold bz in *. unfold bv_eqb, zxb.
  rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma le1_0 : le1 (Z_to_bv 64 0) = [b8 0].
Proof. vm_compute. reflexivity. Qed.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

(* After the store step of a byte at ap + i: the new memory is a fresh variable and I its INV. *)
Ltac stored I i DB DF :=
  rewrite ?le1_zxb, ?le1_0;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?w [?bv]) _) =>
      let I' := fresh "I" in
      pose proof (stb_inv _ mm _ _ _ _ _ i w bv I ltac:(lia) ltac:(first [reflexivity | f_equal; lia]) DB DF) as I';
      let mn := fresh "m" in
      set (mn := write_to_mem mm w [bv]) in *; clearbody mn; clear I; rename I' into I
  end.

Theorem diginet_announce_parse_holds : diginet_announce_parse_contract.
Proof.
  unfold diginet_announce_parse_contract, DIGINET_ANNOUNCE_PARSE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f ap cmd body bb aj Hf Hap Hcmd Hbody BC BF BB CA DF DB MI.
  assert (RC : ro_cells rsegs m (f + 30) [C1 (b8 cmd)]) by (apply ro_of_bytes; [repeat split | exact BC]).
  assert (RF : ro_cells rsegs m (f + 32) [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 (Z.of_nat (length bb)))]).
  { apply ro_of_bytes; [repeat split|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BF. }
  clear BC BF.
  pose proof (rw_cells_bound rsegs m ap _ CA) as HA. cbn [cells_size csize] in HA.
  pose proof (bytes_at_bound rsegs m body bb BB) as HB.
  pose proof (ro_cells_bound rsegs m (f + 30) _ RC) as HC. cbn [cells_size csize] in HC.
  assert (Laj : length aj = 40%nat) by (destruct CA as [[[Hl _] _] _]; exact Hl).
  pose proof (munch_refl [(ap, ap + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. rewrite (eqb_nz f) by lia; cbv iota.
  step. rewrite (eqb_nz ap) by lia; cbv iota.
  step. step. step. step. rewrite cmd_test by lia.
  destruct (ann_cmd cmd) eqn:AC; cbn [negb]; cbv iota.
  2: { step. step. step. step.
       replace (ann_code cmd (Z.of_nat (length bb))) with (-9) by (unfold ann_code; rewrite AC; reflexivity).
       apply evt_done. do 7 eexists. split; [reflexivity|]. cbn [Z.eqb].
       refine (conj MU (conj WM (conj MI CA))). }
  step. step. step.
  destruct (Z.ltb_spec (Z.of_nat (length bb)) 33) as [L33|L33].
  { br false. step. step. step. step.
    replace (ann_code cmd (Z.of_nat (length bb))) with (-4)
      by (unfold ann_code; rewrite AC; cbn [negb];
          replace (Z.of_nat (length bb) <? 33) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    apply evt_done. do 7 eexists. split; [reflexivity|]. cbn [Z.eqb].
    refine (conj MU (conj WM (conj MI CA))). }
  br true.
  (* the announce parses: the code is 0 *)
  assert (Hcode : ann_code cmd (Z.of_nat (length bb)) = 0).
  { unfold ann_code. rewrite AC. cbn [negb].
    replace (Z.of_nat (length bb) <? 33) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (strz_len_le (skipn 15 bb)) as K1.
  pose proof (strz_len_le (skipn 24 bb)) as K2.
  assert (L15 : (18 <= length (skipn 15 bb))%nat) by (rewrite length_skipn; lia).
  assert (L24 : (9 <= length (skipn 24 bb))%nat) by (rewrite length_skipn; lia).
  (* 0x13b70: the NUL of the name, the result 0 *)
  assert (FIN : forall (m2 : word -> option byte) (x2 x4 x5 x6 : word) (v3 : Z),
    v3 = Z.of_nat (strz_len (skipn 24 bb)) ->
    INV m m2 ap f body bb (ann_version bb (firstn 10 aj) ++ firstn (strz_len (skipn 24 bb)) (skipn 24 bb)
                             ++ skipn (10 + strz_len (skipn 24 bb)) (firstn 24 aj)) ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (body + 24)) (Z_to_bv 64 (ap + 10)) x2
                         (Z_to_bv 64 v3) x4 x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x13b70) fc None m2 (seg_rom rsegs))).
  { intros m2 x2 x4 x5 x6 v3 -> I.
    step. step.
    assert (HS : store_ok rsegs m2 (Z_to_bv 64 (ap + 10 + Z.of_nat (strz_len (skipn 24 bb)))) 1 = true)
      by (eapply (inv_store_ok _ _ _ _ _ _ _ (10 + strz_len (skipn 24 bb))); [exact I | lia | f_equal; lia]).
    step. clear HS.
    stored I (10 + strz_len (skipn 24 bb))%nat DB DF.
    rewrite name_nul in I by exact Laj.
    step. step.
    apply evt_done. unfold QQ. cbv beta. rewrite Hcode. do 7 eexists. split; [reflexivity|]. cbn [Z.eqb].
    destruct I as (CA3 & MU3 & WM3 & MI3 & _ & _).
    refine (conj MU3 (conj WM3 (conj MI3 _))). unfold ann_cells.
    apply rw_split3; [ | | | exact CA3].
    - apply length_copy_strz. rewrite length_firstn. lia.
    - apply length_copy_strz. rewrite length_firstn, length_skipn. lia.
    - rewrite length_firstn, length_skipn. lia. }
  assert (HV : length (ann_version bb (firstn 10 aj)) = 10%nat)
    by (apply length_copy_strz; rewrite length_firstn; lia).
  (* 0x13b44: the loop of the name; j bytes copied *)
  assert (LOOP2 : forall (k j : nat) (m1 : word -> option byte) (x3 x4 x5 x6 : word) (v2 : Z),
    (j + S k = 9)%nat -> v2 = Z.of_nat j ->
    (forall i, (i < j)%nat -> at8 (skipn 24 bb) i <> 0) ->
    INV m m1 ap f body bb (ann_version bb (firstn 10 aj) ++ firstn j (skipn 24 bb) ++ skipn (10 + j) (firstn 24 aj)) ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (body + 24)) (Z_to_bv 64 (ap + 10)) (Z_to_bv 64 v2)
                         x3 x4 x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x13b44) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros j m1 x3 x4 x5 x6 v2 Hk -> Hnz I.
    all: destruct (byte_at bb (24 + j) ltac:(lia)) as [b Nb].
    all: pose proof (inv_rd _ _ _ _ _ _ _ _ _ I Nb) as HR.
    all: replace (body + Z.of_nat (24 + j)) with (body + 24 + Z.of_nat j) in HR by lia.
    all: assert (Nb' : nth_error (skipn 24 bb) j = Some b) by (rewrite ne_skipn; exact Nb).
    all: pose proof (at8_ne _ _ _ Nb') as Ab.
    all: step; step; clear HR; step; rewrite zb_eq0.
    all: destruct (Z.eqb_spec (bz b) 0) as [Z0|Z0]; cbv iota.
    1, 3: assert (Ek : strz_len (skipn 24 bb) = j) by (apply strz_len_char; [lia | lia | exact Hnz | intros; lia]);
          step; eapply FIN; [rewrite Ek; reflexivity | rewrite Ek; exact I].
    all: step; step; step.
    all: assert (HS : store_ok rsegs m1 (Z_to_bv 64 (ap + 10 + Z.of_nat j)) 1 = true)
           by (eapply (inv_store_ok _ _ _ _ _ _ _ (10 + j)); [exact I | lia | f_equal; lia]).
    all: step; clear HS.
    all: stored I (10 + j)%nat DB DF.
    all: rewrite (upd_snoc (ann_version bb (firstn 10 aj)) (skipn 24 bb) (firstn 24 aj) 10 j b HV Nb') in I.
    all: step; step.
    - br false. step.
      assert (Ek : strz_len (skipn 24 bb) = 9%nat).
      { apply strz_len_char; [lia | lia | | lia].
        intros i Hi. destruct (Nat.eq_dec i j) as [->|NE]; [lia | apply Hnz; lia]. }
      eapply FIN; [rewrite Ek; reflexivity | rewrite Ek; replace (S j) with 9%nat in I by lia; exact I].
    - br true. eapply (IH (S j)); [lia | lia | | exact I].
      intros i Hi. destruct (Nat.eq_dec i j) as [->|NE]; [lia | apply Hnz; lia]. }
  (* 0x13b2c: the NUL of the version, the body address again, the name's start *)
  assert (AFTER1 : forall (m2 : word -> option byte) (x2 x5 x6 : word) (v4 : Z),
    v4 = Z.of_nat (strz_len (skipn 15 bb)) ->
    INV m m2 ap f body bb (firstn (strz_len (skipn 15 bb)) (skipn 15 bb) ++ skipn (strz_len (skipn 15 bb)) (firstn 24 aj)) ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 ap) x2 (Z_to_bv 64 (body + 15))
                         (Z_to_bv 64 v4) x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x13b2c) fc None m2 (seg_rom rsegs))).
  { intros m2 x2 x5 x6 v4 -> I.
    step. step.
    assert (HS : store_ok rsegs m2 (Z_to_bv 64 (ap + Z.of_nat (strz_len (skipn 15 bb)))) 1 = true)
      by (eapply (inv_store_ok _ _ _ _ _ _ _ (strz_len (skipn 15 bb))); [exact I | lia | reflexivity]).
    step. clear HS.
    stored I (strz_len (skipn 15 bb)) DB DF.
    rewrite ver_nul in I by exact Laj.
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 I))))) as RF3.
    step. clear RF3. step. step.
    eapply (LOOP2 8%nat 0%nat); [lia | reflexivity | intros; lia | exact I]. }
  (* 0x13b00: the loop of the version; i bytes copied *)
  assert (LOOP1 : forall (k i : nat) (m1 : word -> option byte) (x4 x5 x6 : word) (v2 : Z),
    (i + S k = 9)%nat -> v2 = Z.of_nat i ->
    (forall j, (j < i)%nat -> at8 (skipn 15 bb) j <> 0) ->
    INV m m1 ap f body bb (firstn i (skipn 15 bb) ++ skipn i (firstn 24 aj)) ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 ap) (Z_to_bv 64 v2)
                         (Z_to_bv 64 (body + 15)) x4 x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x13b00) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i m1 x4 x5 x6 v2 Hk -> Hnz I.
    all: destruct (byte_at bb (15 + i) ltac:(lia)) as [b Nb].
    all: pose proof (inv_rd _ _ _ _ _ _ _ _ _ I Nb) as HR.
    all: replace (body + Z.of_nat (15 + i)) with (body + 15 + Z.of_nat i) in HR by lia.
    all: assert (Nb' : nth_error (skipn 15 bb) i = Some b) by (rewrite ne_skipn; exact Nb).
    all: pose proof (at8_ne _ _ _ Nb') as Ab.
    all: step; step; clear HR; step; rewrite zb_eq0.
    all: destruct (Z.eqb_spec (bz b) 0) as [Z0|Z0]; cbv iota.
    1, 3: assert (Ek : strz_len (skipn 15 bb) = i) by (apply strz_len_char; [lia | lia | exact Hnz | intros; lia]);
          step; eapply AFTER1; [rewrite Ek; reflexivity | rewrite Ek; exact I].
    all: step; step; step.
    all: assert (HS : store_ok rsegs m1 (Z_to_bv 64 (ap + Z.of_nat i)) 1 = true)
           by (eapply (inv_store_ok _ _ _ _ _ _ _ i); [exact I | lia | reflexivity]).
    all: step; clear HS.
    all: stored I i DB DF.
    all: replace (upd_bytes (firstn i (skipn 15 bb) ++ skipn i (firstn 24 aj)) i [b])
           with (firstn (S i) (skipn 15 bb) ++ skipn (S i) (firstn 24 aj)) in I
           by (symmetry; exact (upd_snoc [] (skipn 15 bb) (firstn 24 aj) 0 i b eq_refl Nb')).
    all: step; step.
    - br false. step.
      assert (Ek : strz_len (skipn 15 bb) = 9%nat).
      { apply strz_len_char; [lia | lia | | lia].
        intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [lia | apply Hnz; lia]. }
      eapply AFTER1; [rewrite Ek; reflexivity | rewrite Ek; replace (S i) with 9%nat in I by lia; exact I].
    - br true. eapply (IH (S i)); [lia | lia | | exact I].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [lia | apply Hnz; lia]. }
  (* 0x13ae8: unknown and unknown_len, then the version's loop from 0 *)
  step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (I : INV m m1 ap f body bb (firstn 24 aj))
      by (refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); eassumption)
  end.
  eapply (LOOP1 8%nat 0%nat); [lia | reflexivity | intros; lia | exact I].
Qed.
