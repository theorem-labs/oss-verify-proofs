(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require PropExec CatSim AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec RegsEquiv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mkst_MS : forall F fc R pc m rom,
  @AS.PropExec.mkst (AS.PropExec.mkFP F fc) R pc m rom = MS R F pc fc None m rom.
Proof. reflexivity. Qed.

Lemma msteps_bridge : forall segs a b, AS.CatSim.msteps segs a b -> Exec.msteps segs a b.
Proof.
  intros segs a b H. induction H as [ms|ms ms1 ms2 Hsvc Hstep _ IH]; [apply msteps_refl|].
  eapply msteps_cons; [split; [exact Hsvc | exact Hstep] | exact IH].
Qed.

Lemma getr_reg_get : forall R (r : reg), bv_eqb r 0 = false -> AS.PropExec.getr R r = reg_get R r.
Proof. intros R r H. unfold AS.PropExec.getr. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rkeys : list Z := [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%Z.

Lemma regs_ok_mkR : forall E sr x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  map (fun k => edenot E (sr_get sr (Z_to_bv 5 k))) rkeys
    = [x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16;x17;x18;x19;x20;x21;x22;x23;x24;x25;x26;x27;x28;x29;x30;x31] ->
  regs_ok E sr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof.
  intros E sr x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 H.
  unfold rkeys in H. cbn [map] in H.
  injection H as H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31.
  intros r. destruct (reg_of_nat r) as (n & -> & Hn).
  destruct n as [|n]; [reflexivity|].
  do 31 (destruct n as [|n]; [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; etransitivity; [|symmetry; eassumption]; reflexivity |]).
  exfalso; lia.
Qed.

Lemma regs_ok_canon : forall E sr R, rfull R -> regs_ok E sr R ->
  R = mkR (edenot E (sr_get sr 1)) (edenot E (sr_get sr 2)) (edenot E (sr_get sr 3)) (edenot E (sr_get sr 4)) (edenot E (sr_get sr 5))
          (edenot E (sr_get sr 6)) (edenot E (sr_get sr 7)) (edenot E (sr_get sr 8)) (edenot E (sr_get sr 9)) (edenot E (sr_get sr 10))
          (edenot E (sr_get sr 11)) (edenot E (sr_get sr 12)) (edenot E (sr_get sr 13)) (edenot E (sr_get sr 14)) (edenot E (sr_get sr 15))
          (edenot E (sr_get sr 16)) (edenot E (sr_get sr 17)) (edenot E (sr_get sr 18)) (edenot E (sr_get sr 19)) (edenot E (sr_get sr 20))
          (edenot E (sr_get sr 21)) (edenot E (sr_get sr 22)) (edenot E (sr_get sr 23)) (edenot E (sr_get sr 24)) (edenot E (sr_get sr 25))
          (edenot E (sr_get sr 26)) (edenot E (sr_get sr 27)) (edenot E (sr_get sr 28)) (edenot E (sr_get sr 29)) (edenot E (sr_get sr 30))
          (edenot E (sr_get sr 31)).
Proof.
  intros E sr R HF HR. rewrite (rfull_canon R HF) at 1.
  f_equal; (rewrite <- (getr_reg_get R) by reflexivity; apply HR).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Fixpoint wr_ok (A : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match wview segs (fun _ => None) (wa A) with Some _ => wr_ok (A + 1) n' | None => false end
  end.

Lemma wr_ok_sound : forall n A m, wr_ok A n = true -> (0 <= A)%Z -> (A + Z.of_nat n <= 2^64)%Z -> wr_at segs m A (Z.of_nat n).
Proof.
  intros n A m H HA HB. split; [lia|]. split; [lia|]. revert A H HA HB.
  induction n as [|n IH]; intros A H HA HB i Hi; [lia|].
  cbn [wr_ok] in H. destruct (wview segs (fun _ => None) (wa A)) as [b|] eqn:Ew; [|discriminate].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r. unfold wview in *. destruct (m (wa A)); [discriminate|]. rewrite Ew. discriminate.
  - replace (A + i)%Z with ((A + 1) + (i - 1))%Z by lia. apply (IH (A + 1)%Z H); lia.
Qed.

Definition exp_ok (kn : list kentry) (e : Z * list byte) : bool :=
  (Z.leb 0 (fst e) && Z.leb (fst e + Z.of_nat (length (snd e))) (2^64) && chunk_ok segs kn (fst e) (snd e) && wr_ok (fst e) (length (snd e)))%bool.

Lemma exp_ok_sound : forall E m kn e, know_ok segs E m kn -> exp_ok kn e = true ->
  rw_cells segs m (fst e) [CB (length (snd e)) (snd e)].
Proof.
  intros E m kn [A bs] HK H. unfold exp_ok in H. cbn [fst snd] in *.
  apply andb_prop in H as [H Hw]. apply andb_prop in H as [H Hc]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0, H1.
  split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [lia|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:En; [|apply nth_error_None in En; lia].
    exact (chunk_ok_sound segs E m kn bs A HK Hc i b En).
  - cbn [cells_size csize]. rewrite Nat.add_0_r. apply wr_ok_sound; [exact Hw | lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint sr_eqb (a b : list expr) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => expr_eqb x y && sr_eqb a' b'
  | _, _ => false
  end.
Lemma sr_eqb_eq : forall a b, sr_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. rewrite (expr_eqb_eq _ _ H1), (IH _ H2). reflexivity.
Qed.

(* [comment removed for export] *)
Definition wexp : Type := (expr * Z * nat * expr)%type.
Definition wexp_ok (nx : nat) (kn : list kentry) (x : wexp) : bool :=
  match x with (b, off, w, v) => (expr_vars_lt nx b && expr_vars_lt nx v && kword_has kn (SA b off) w v)%bool end.
Definition wexp_den (E : env) (m' : word -> option byte) (x : wexp) : Prop :=
  match x with (b, off, w, v) => bytes_at segs m' (bv_unsigned (edenot E b) + off) (word_to_le_bytes w (edenot E v)) end.

Lemma wexp_ok_sound : forall nx E E' m' kn x,
  env_agree nx E E' -> know_ok segs E' m' kn -> wexp_ok nx kn x = true -> wexp_den E m' x.
Proof.
  intros nx E E' m' kn [[[b off] w] v] Hag HK H. cbn [wexp_ok] in H.
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hb Hv].
  destruct (kword_has_sound segs E' m' kn (SA b off) w v HK Hk) as [Hfl Hrd].
  cbn [wexp_den]. rewrite (edenot_agree nx E E' b Hag Hb), (edenot_agree nx E E' v Hag Hv).
  destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
  unfold adenot, AS.PropExec.v_addi in Hrd. cbn [a_base a_off] in Hrd.
  set (A := (bv_unsigned (edenot E' b) + off)%Z) in *.
  split; [exact F1|]. split; [rewrite length_word_to_le_bytes; exact F4|].
  intros i Hi. rewrite length_word_to_le_bytes in Hi.
  exact (rdn_nth segs m' w A _ F1 F4 Hrd i Hi).
Qed.

(* [comment removed for export] *)
Definition scheck_k (IT : itab) (fuel : nat) (stops : list Z) (ss : sym_state) (W : list fpwin)
                    (pcF : Z) (srF : list expr) (knF : list kentry) (exports : list (Z * list byte)) (wexports : list wexp) : bool :=
  match srun segs IT fuel stops ss with
  | Some (ss', lg) =>
      (Z.eqb (s_pc ss') pcF && sr_eqb (s_regs ss') srF && sr_vars_lt (s_next ss) srF && fp_closed (s_next ss) W
       && forallb (se_in_fp W) lg && forallb (exp_ok (s_know ss')) exports && forallb (wexp_ok (s_next ss) (s_know ss')) wexports
       && kn_vars_lt (s_next ss) knF && kn_sub knF (s_know ss'))%bool
  | None => false
  end.
Definition scheck (IT : itab) (fuel : nat) (stops : list Z) (ss : sym_state) (W : list fpwin)
                  (pcF : Z) (srF : list expr) (exports : list (Z * list byte)) (wexports : list wexp) : bool :=
  scheck_k IT fuel stops ss W pcF srF [] exports wexports.

Lemma outsideZ_outside : forall W x, outside W x -> outsideZ W x.
Proof. induction W as [|[lo hi] W IH]; intros x H; [exact I|]. cbn in *. destruct H as [H1 H2]. split; [exact H1 | apply IH; exact H2]. Qed.

Lemma env_agree_sym : forall b E E', env_agree b E E' -> env_agree b E' E.
Proof. intros b E E' [H1 H2]. split; [intros n Hn; symmetry; apply H1; exact Hn | symmetry; exact H2]. Qed.

Theorem scheck_k_sound : forall IT fuel stops ss W pcF srF knF exports wexports,
  itab_sound segs IT ->
  scheck_k IT fuel stops ss W pcF srF knF exports wexports = true ->
  forall E m rom R (F : bvmap 5 word) (fc : bv 32), rfull R -> regs_ok E (s_regs ss) R -> know_ok segs E m (s_know ss) -> mem_inv segs m ->
  exists R' m',
    msteps segs (MS R F (Z_to_bv 64 (s_pc ss)) fc None m rom)
                (MS R' F (Z_to_bv 64 pcF) fc None m' rom)
    /\ rfull R' /\ regs_ok E srF R'
    /\ munch (map (fpwin_den E) W) m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ (forall lo hi, stk segs m lo hi -> stk segs m' lo hi)
    /\ Forall (fun e => rw_cells segs m' (fst e) [CB (length (snd e)) (snd e)]) exports
    /\ Forall (wexp_den E m') wexports
    /\ know_ok segs E m' knF.
Proof.
  intros IT fuel stops ss W pcF srF knF exports wexports HIT Hc E m rom R F fc HF HR HK MI.
  unfold scheck_k in Hc. destruct (srun segs IT fuel stops ss) as [[ss' lg]|] eqn:Hrun; [|discriminate].
  apply andb_prop in Hc as [Hc Hksub]. apply andb_prop in Hc as [Hc Hkvl].
  apply andb_prop in Hc as [Hc Hwexp]. apply andb_prop in Hc as [Hc Hexp]. apply andb_prop in Hc as [Hc Hfp].
  apply andb_prop in Hc as [Hc Hfc]. apply andb_prop in Hc as [Hc Hvl].
  apply andb_prop in Hc as [Hpc Hsr]. apply Z.eqb_eq in Hpc. apply sr_eqb_eq in Hsr.
  destruct (@srun_sound (AS.PropExec.mkFP F fc) segs IT fuel stops ss ss' lg HIT Hrun E m rom R HR HK)
    as (E' & R' & Hag & Hle & HR' & Hlf & HK' & Hms).
  rewrite !mkst_MS in Hms. apply msteps_bridge in Hms. rewrite Hpc in Hms. rewrite Hsr in HR'.
  exists R', (mem_denot E' m lg).
  pose proof (msteps_wrel segs _ _ Hms) as HW. cbn [ms_mem MS] in HW.
  split; [exact Hms|].
  split; [exact (msteps_rfull segs _ _ Hms HF)|].
  split; [eapply regs_ok_agree; [apply env_agree_sym; exact Hag | exact Hvl | exact HR']|].
  split.
  { intros x Hx. apply (mem_denot_outside E' W m lg x Hlf Hfp).
    rewrite (fpwin_den_agree _ E E' W Hag Hfc). apply outsideZ_outside. exact Hx. }
  split; [exact (wrel_wmono segs _ _ HW)|].
  split; [exact (wrel_mem_inv segs _ _ HW MI)|].
  split; [exact (wrel_stk segs _ _ HW)|].
  split.
  { apply Forall_forall. intros e He.
    apply (exp_ok_sound E' _ (s_know ss') e HK'). exact (proj1 (forallb_forall _ _) Hexp e He). }
  split.
  { apply Forall_forall. intros x Hx.
    exact (wexp_ok_sound _ E E' _ _ x Hag HK' (proj1 (forallb_forall _ _) Hwexp x Hx)). }
  eapply know_ok_agree; [apply env_agree_sym; exact Hag | exact Hkvl |].
  exact (kn_sub_ok segs E' _ knF (s_know ss') Hksub HK').
Qed.

Theorem scheck_sound : forall IT fuel stops ss W pcF srF exports wexports,
  itab_sound segs IT ->
  scheck IT fuel stops ss W pcF srF exports wexports = true ->
  forall E m rom R (F : bvmap 5 word) (fc : bv 32), rfull R -> regs_ok E (s_regs ss) R -> know_ok segs E m (s_know ss) -> mem_inv segs m ->
  exists R' m',
    msteps segs (MS R F (Z_to_bv 64 (s_pc ss)) fc None m rom)
                (MS R' F (Z_to_bv 64 pcF) fc None m' rom)
    /\ rfull R' /\ regs_ok E srF R'
    /\ munch (map (fpwin_den E) W) m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ (forall lo hi, stk segs m lo hi -> stk segs m' lo hi)
    /\ Forall (fun e => rw_cells segs m' (fst e) [CB (length (snd e)) (snd e)]) exports
    /\ Forall (wexp_den E m') wexports.
Proof.
  intros IT fuel stops ss W pcF srF exports wexports HIT Hc E m rom R F fc HF HR HK MI.
  destruct (scheck_k_sound IT fuel stops ss W pcF srF [] exports wexports HIT Hc E m rom R F fc HF HR HK MI)
    as (R' & m' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
  exists R', m'. auto 10.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Know.
Variable segs : list Segment.
Variable E : env.
Variable m : word -> option byte.

Lemma kn_range : forall e lo hi, (lo <= bv_unsigned (edenot E e) <= hi)%Z -> kentry_ok segs E m (KRange e lo hi).
Proof. intros e lo hi H. exact H. Qed.

Lemma kn_align : forall e k, (0 < k)%Z -> (bv_unsigned (edenot E e) mod k = 0)%Z -> kentry_ok segs E m (KAlign e k).
Proof. intros e k H1 H2. split; assumption. Qed.

Lemma kn_img : forall lo hi, (0 <= lo)%Z -> (hi <= 2^64)%Z ->
  (forall a : word, (lo <= bv_unsigned a < hi)%Z -> m a = None) -> kentry_ok segs E m (KImg lo hi).
Proof.
  intros lo hi H1 H2 H. split; [exact H1|]. split; [exact H2|]. intros i Hi. apply H.
  rewrite Z_to_bv_unsigned, bv_wrap_small; [exact Hi | unfold bv_modulus; lia].
Qed.

(* [comment removed for export] *)
Lemma kn_wr : forall b off K (base : Z),
  (bv_unsigned (edenot E b) + off = base)%Z -> (0 <= base)%Z -> (0 <= K < 2^64)%Z -> (base + K <= 2^64)%Z -> (base < 2^64)%Z ->
  (forall x : word, (base <= bv_unsigned x < base + K)%Z -> wview segs m x <> None) ->
  kentry_ok segs E m (KWr (SA b off) (ELit K)).
Proof.
  intros b off K base Hb H0 HK Hhi Hlt Hw. cbn [kentry_ok].
  assert (HKe : elenZ E (ELit K) = K).
  { unfold elenZ. rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; lia]. }
  assert (Hst : estart E (SA b off) = base) by (unfold estart; cbn [a_base a_off]; exact Hb).
  rewrite HKe, Hst. split; [unfold flat; rewrite Hst; lia|].
  intros d mm Hd Hdm. destruct mm as [|mm]; [reflexivity|].
  assert (Hu : bv_unsigned (Z_to_bv 64 (base + d)) = (base + d)%Z).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; lia]. }
  apply AS.StoreOk.store_ok_of_all; rewrite Hu; [lia|].
  intros x Hx. apply Hw. lia.
Qed.

Lemma stk_wview : forall lo hi (x : word), stk segs m lo hi -> (lo <= bv_unsigned x < hi)%Z -> wview segs m x <> None.
Proof.
  intros lo hi x (S1 & S2 & S3) Hx. destruct (S3 (bv_unsigned x) Hx) as [Hw _].
  unfold wa in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma kn_word : forall A w e bs,
  bytes_at segs m A bs -> length bs = w -> (0 < w <= 8)%nat -> word_to_le_bytes w (edenot E e) = bs ->
  kentry_ok segs E m (KWord (SA (ELit 0) A) w e).
Proof.
  intros A w e bs HB HL Hw8 Hbs. cbn [kentry_ok].
  pose proof (bytes_at_bound segs m A bs HB) as [HA0 HA1]. rewrite HL in HA1.
  split; [lia|].
  assert (Hst : estart E (SA (ELit 0) A) = A).
  { unfold estart. cbn [a_base a_off]. rewrite edenot_lit. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
  split; [unfold flat; rewrite Hst; lia|].
  assert (Had : adenot E (SA (ELit 0) A) = wa A).
  { unfold adenot. cbn [a_base a_off]. rewrite edenot_lit. unfold AS.PropExec.v_addi. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. reflexivity. }
  rewrite Had, Hbs.
  pose proof (bytes_at_rdn segs m A bs 0 w HB ltac:(lia)) as Hr. rewrite Z.add_0_r in Hr. cbn [skipn] in Hr.
  rewrite <- HL in Hr at 2. rewrite firstn_all in Hr. exact Hr.
Qed.

End Know.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_eq_unsigned : forall a b : list byte, map bv_unsigned a = map bv_unsigned b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn [map] in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma rw_cells_recast_u : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> map bv_unsigned (cells_bytes cs') = map bv_unsigned (cells_bytes cs) ->
  cells_size cs' = cells_size cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. apply bytes_eq_unsigned in Eb.
  split; [split; [exact Hwf' | rewrite Eb; exact Hb] | rewrite Es; exact Hw].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_sub_u : forall segs m A n bs (k : nat) cs',
  rw_cells segs m A [CB n bs] -> cells_wf cs' ->
  map bv_unsigned (cells_bytes cs') = map bv_unsigned (firstn (cells_size cs') (skipn k bs)) ->
  (k + cells_size cs' <= n)%nat ->
  rw_cells segs m (A + Z.of_nat k) cs'.
Proof.
  intros segs m A n bs k cs' [[[Hn _] Hb] Hw] Hwf' Eb Hk. apply bytes_eq_unsigned in Eb.
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  cbn [cell_wf] in Hn.
  assert (Hsplit : bs = firstn k bs ++ firstn (cells_size cs') (skipn k bs) ++ skipn (k + cells_size cs') bs) by (symmetry; apply CB3_bytes; lia).
  rewrite Hsplit in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb]. apply bytes_at_app in Hb. destruct Hb as [Hb _].
  rewrite firstn_length, Nat.min_l in Hb by lia.
  split; [split; [exact Hwf' | rewrite Eb; exact Hb]|].
  destruct Hw as (W1 & W2 & W3). split; [lia|]. split; [lia|].
  intros i Hi. replace (A + Z.of_nat k + i)%Z with (A + (Z.of_nat k + i))%Z by lia. apply W3. lia.
Qed.
