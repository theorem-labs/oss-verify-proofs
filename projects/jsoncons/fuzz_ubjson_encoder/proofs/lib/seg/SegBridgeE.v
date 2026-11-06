(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* Bridging lemmas for segment certificates whose rc.2 walk stores in a different pattern than the OLD one (musl
   memset over a range whose rc.2 address moved by a delta that is not 0 mod 8). The certificate proved on rc.2 (the
   core) and the interface the consumers use (the uniformly relocated pieces) cover the same bytes; these lemmas carry
   the core's soundness over to the uniform interface. All checks are boolean and run by vm_compute at the use. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound
  AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundK AsanPlanSoundSums LibSym SegRun SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Mem.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.

Module SBR.

(* ---------- byte loops ---------- *)

Fixpoint all_bytes (lo : Z) (k : nat) (P : Z -> bool) : bool :=
  match k with O => true | S k' => P lo && all_bytes (lo + 1) k' P end.

Lemma all_bytes_spec : forall k lo P, all_bytes lo k P = true -> forall i, 0 <= i < Z.of_nat k -> P (lo + i) = true.
Proof.
  induction k as [|k IH]; intros lo P H i Hi; cbn [all_bytes] in *.
  - lia.
  - apply andb_prop in H as [H1 H2].
    destruct (Z.eq_dec i 0) as [->|Hne].
    + rewrite Z.add_0_r. exact H1.
    + replace (lo + i) with ((lo + 1) + (i - 1)) by lia. apply IH; [exact H2|lia].
Qed.

Definition in_iv (x : Z) (iv : Z * Z) : bool := let '(lo, n) := iv in (lo <=? x) && (x <? lo + n).

Lemma in_iv_spec : forall x lo n, in_iv x (lo, n) = true -> lo <= x < lo + n.
Proof. intros x lo n H. cbn in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.

(* ---------- literal pieces of a knowledge list ---------- *)

Definition kwr_iv (K : kentry) : option (Z * Z) :=
  match K with KWr (SA (ELit lo0) lo) (ELit n) => if Z.eqb lo0 0 then Some (lo, n) else None | _ => None end.
Definition kz_iv (K : kentry) : option (Z * Z) :=
  match K with
  | KWord (SA (ELit lo0) lo) w (ELit v) => if Z.eqb lo0 0 && Z.eqb v 0 then Some (lo, Z.of_nat w) else None
  | _ => None
  end.

Definition lit_ok (lo n : Z) : bool := (0 <=? lo) && (0 <=? n) && (n <? 2 ^ 64) && (lo + n <=? 2 ^ 64).

Lemma lit_ok_spec : forall lo n, lit_ok lo n = true -> 0 <= lo /\ 0 <= n < 2 ^ 64 /\ lo + n <= 2 ^ 64.
Proof.
  intros lo n H. unfold lit_ok in H. repeat (apply andb_prop in H as [H ?]).
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
  lia.
Qed.

Lemma unsigned_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. lia. Qed.

Lemma estart_lit : forall E lo, estart E (SA (ELit 0) lo) = lo.
Proof. intros E lo. unfold estart. cbn [a_base a_off edenot]. rewrite unsigned_lit by lia. lia. Qed.

Lemma elenZ_lit : forall E n, 0 <= n < 2 ^ 64 -> elenZ E (ELit n) = n.
Proof. intros E n Hn. unfold elenZ. cbn [edenot]. apply unsigned_lit. exact Hn. Qed.

(* ---------- store_ok from bytes ---------- *)

Lemma store_ok_of_bytes : forall segs M m x,
  0 <= x -> x + Z.of_nat m <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat m -> RiscvSemantics.store_ok segs M (Z_to_bv 64 (x + i)) 1 = true) ->
  RiscvSemantics.store_ok segs M (Z_to_bv 64 x) m = true.
Proof.
  intros segs M m. induction m as [|m IH]; intros x Hx Hb H.
  - reflexivity.
  - cbn [RiscvSemantics.store_ok].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [RiscvSemantics.store_ok] in H0.
    destruct (wview segs M (Z_to_bv 64 x)) eqn:W; [|discriminate].
    pose proof (Mem.wa_succ x) as Hs. unfold Mem.wa in Hs. rewrite Hs.
    apply IH; [lia|lia|]. intros i Hi. replace (x + 1 + i) with (x + (i + 1)) by lia. apply H. lia.
Qed.

Lemma store_ok_byte_of_kwr : forall segs E M lo n x,
  lit_ok lo n = true ->
  kentry_ok segs E M (KWr (SA (ELit 0) lo) (ELit n)) -> lo <= x < lo + n ->
  RiscvSemantics.store_ok segs M (Z_to_bv 64 x) 1 = true.
Proof.
  intros segs E M lo n x Hl K Hx. apply lit_ok_spec in Hl. cbn [kentry_ok] in K. destruct K as [_ K].
  rewrite elenZ_lit in K by lia. specialize (K (x - lo) 1%nat ltac:(lia) ltac:(lia)).
  rewrite estart_lit in K. replace (lo + (x - lo)) with x in K by lia. exact K.
Qed.

(* ---------- KWr pieces covered by other KWr pieces ---------- *)

Definition kwr_cover (U : list kentry) (K : kentry) : bool :=
  match kwr_iv K with
  | Some (lo, n) =>
      lit_ok lo n && (0 <? n) &&
      all_bytes lo (Z.to_nat n) (fun x => existsb (fun K' => match kwr_iv K' with
                                                          | Some iv => lit_ok (fst iv) (snd iv) && in_iv x iv
                                                          | None => false end) U)
  | None => false
  end.

Lemma kwr_iv_inv : forall K lo n, kwr_iv K = Some (lo, n) -> K = KWr (SA (ELit 0) lo) (ELit n).
Proof.
  intros K lo n H. unfold kwr_iv in H.
  repeat match type of H with
  | (if Z.eqb ?a 0 then _ else _) = _ => destruct (Z.eqb_spec a 0); [subst|discriminate]
  | (if (Z.eqb ?a 0 && Z.eqb ?b 0)%bool then _ else _) = _ =>
      destruct (Z.eqb_spec a 0); [|discriminate]; destruct (Z.eqb_spec b 0); [|discriminate]; subst; cbn in H
  | match ?x with _ => _ end = _ => destruct x; try discriminate
  end.
  injection H as <- <-. reflexivity.
Qed.

Lemma kwr_cover_sound : forall segs E M U K,
  Forall (kentry_ok segs E M) U -> kwr_cover U K = true -> kentry_ok segs E M K.
Proof.
  intros segs E M U K HU H. unfold kwr_cover in H.
  destruct (kwr_iv K) as [[lo n]|] eqn:Hk; [|discriminate].
  apply kwr_iv_inv in Hk. subst K.
  apply andb_prop in H as [H Hall]. apply andb_prop in H as [Hl Hn]. apply Z.ltb_lt in Hn.
  pose proof (lit_ok_spec _ _ Hl) as Hl'.
  cbn [kentry_ok]. rewrite elenZ_lit by lia. split.
  - unfold flat. rewrite estart_lit. lia.
  - intros d m Hd Hm. rewrite estart_lit. apply store_ok_of_bytes; [lia|lia|].
    intros i Hi. pose proof (all_bytes_spec _ _ _ Hall (d + i) ltac:(rewrite Z2Nat.id by lia; lia)) as Hb.
    apply existsb_exists in Hb as [K' [HK' Hb]].
    destruct (kwr_iv K') as [[lo' n']|] eqn:Hk'; [|discriminate].
    apply kwr_iv_inv in Hk'. subst K'. cbn [fst snd] in Hb. apply andb_prop in Hb as [Hl2 Hin].
    apply in_iv_spec in Hin. rewrite Forall_forall in HU.
    replace (lo + d + i) with (lo + (d + i)) by lia.
    eapply store_ok_byte_of_kwr; [exact Hl2|apply HU; exact HK'|lia].
Qed.

(* ---------- knowledge lists ---------- *)

Definition kn_check (U C : list kentry) : bool :=
  forallb (fun K => existsb (APC.kentry_eqb K) U || kwr_cover U K) C.

Lemma kn_check_sound : forall segs E M U C, know_ok segs E M U -> kn_check U C = true -> know_ok segs E M C.
Proof.
  intros segs E M U C HU H. unfold know_ok in *. apply Forall_forall. intros K HK.
  unfold kn_check in H. rewrite forallb_forall in H. specialize (H K HK). apply orb_prop in H as [H|H].
  - apply existsb_exists in H as [K' [HK' Heq]]. apply APS.kentry_eqb_eq in Heq. subst K'.
    rewrite Forall_forall in HU. apply HU. exact HK'.
  - eapply kwr_cover_sound; eauto.
Qed.

(* ---------- frame regions ---------- *)

Definition reg_eqb (r r' : SGP.region) : bool :=
  let '(b, k, n) := r in let '(b', k', n') := r' in expr_eqb b b' && Z.eqb k k' && expr_eqb n n'.

Lemma reg_eqb_eq : forall r r', reg_eqb r r' = true -> r = r'.
Proof.
  intros [[b k] n] [[b' k'] n'] H. cbn in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H3. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Definition reg_iv (r : SGP.region) : option (Z * Z) :=
  match r with (ELit b0, lo, ELit n) => if Z.eqb b0 0 then Some (lo, n) else None | _ => None end.

Lemma reg_iv_inv : forall r lo n, reg_iv r = Some (lo, n) -> r = (ELit 0, lo, ELit n).
Proof.
  intros [[b k] ne] lo n H. unfold reg_iv in H.
  repeat match type of H with
  | (if Z.eqb ?a 0 then _ else _) = _ => destruct (Z.eqb_spec a 0); [subst|discriminate]
  | (if (Z.eqb ?a 0 && Z.eqb ?b 0)%bool then _ else _) = _ =>
      destruct (Z.eqb_spec a 0); [|discriminate]; destruct (Z.eqb_spec b 0); [|discriminate]; subst; cbn in H
  | match ?x with _ => _ end = _ => destruct x; try discriminate
  end.
  injection H as <- <-. reflexivity.
Qed.

(* every core region is a uniform one, or a literal one whose bytes all lie in literal uniform regions *)
Definition out_check (U C : list SGP.region) : bool :=
  forallb (fun r => existsb (reg_eqb r) U ||
             match reg_iv r with
             | Some (lo, n) => lit_ok lo n &&
                 all_bytes lo (Z.to_nat n) (fun x => existsb (fun r' => match reg_iv r' with
                                                                     | Some iv => lit_ok (fst iv) (snd iv) && in_iv x iv
                                                                     | None => false end) U)
             | None => false
             end) C.

Lemma out_check_sound : forall E U C a, out_check U C = true -> SGP.outside E U a -> SGP.outside E C a.
Proof.
  intros E U C a H HU. unfold SGP.outside in *. rewrite Forall_forall in *. intros r Hr.
  unfold out_check in H. rewrite forallb_forall in H. specialize (H r Hr). apply orb_prop in H as [H|H].
  - apply existsb_exists in H as [r' [Hr' Heq]]. apply reg_eqb_eq in Heq. subst r'. exact (HU r Hr').
  - destruct (reg_iv r) as [[lo n]|] eqn:Hi; [|discriminate]. apply reg_iv_inv in Hi. subst r.
    apply andb_prop in H as [Hl Hall]. pose proof (lit_ok_spec _ _ Hl) as Hl'.
    rewrite estart_lit, elenZ_lit by lia.
    destruct (Z_lt_le_dec (bv_unsigned a) lo) as [Hlt|Hge]; [left; exact Hlt|].
    destruct (Z_lt_le_dec (bv_unsigned a) (lo + n)) as [Hin|Hout]; [|right; exact Hout].
    exfalso. pose proof (all_bytes_spec _ _ _ Hall (bv_unsigned a - lo) ltac:(rewrite Z2Nat.id by lia; lia)) as Hb.
    replace (lo + (bv_unsigned a - lo)) with (bv_unsigned a) in Hb by lia.
    apply existsb_exists in Hb as [r' [Hr' Hb]].
    destruct (reg_iv r') as [[lo' n']|] eqn:Hi'; [|discriminate]. apply reg_iv_inv in Hi'. subst r'.
    cbn [fst snd] in Hb. apply andb_prop in Hb as [Hl2 Hb]. apply in_iv_spec in Hb. pose proof (lit_ok_spec _ _ Hl2).
    specialize (HU _ Hr'). cbn beta iota in HU. rewrite estart_lit, elenZ_lit in HU by lia. lia.
Qed.

(* every uniform region is a core one, or a literal one that is well formed *)
Definition rok_check (U C : list SGP.region) : bool :=
  forallb (fun r => existsb (reg_eqb r) C ||
             match reg_iv r with Some (lo, n) => lit_ok lo n && (0 <? n) | None => false end) U.

Lemma rok_check_sound : forall E U C, rok_check U C = true -> SGP.regions_ok E C -> SGP.regions_ok E U.
Proof.
  intros E U C H HC. unfold SGP.regions_ok in *. rewrite Forall_forall in *. intros r Hr.
  unfold rok_check in H. rewrite forallb_forall in H. specialize (H r Hr). apply orb_prop in H as [H|H].
  - apply existsb_exists in H as [r' [Hr' Heq]]. apply reg_eqb_eq in Heq. subst r'. exact (HC r Hr').
  - destruct (reg_iv r) as [[lo n]|] eqn:Hi; [|discriminate]. apply reg_iv_inv in Hi. subst r.
    apply andb_prop in H as [Hl Hn]. apply Z.ltb_lt in Hn. pose proof (lit_ok_spec _ _ Hl).
    cbn beta iota. rewrite estart_lit, elenZ_lit by lia. lia.
Qed.

(* ---------- post cells: zero words ---------- *)

Lemma word_to_le_bytes_zero : forall w, (w <= 8)%nat -> word_to_le_bytes w (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) w.
Proof.
  intros w Hw. do 9 (destruct w as [|w]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma map_const_seq : forall (b : byte) n s, map (fun _ : nat => b) (seq s n) = repeat b n.
Proof. intros b n. induction n as [|n IH]; intros s; [reflexivity|]. cbn. f_equal. apply IH. Qed.

Lemma zero_byte_of_cell : forall segs E M lo w x,
  kentry_ok segs E M (KWord (SA (ELit 0) lo) w (ELit 0)) -> lo <= x < lo + Z.of_nat w ->
  rdn segs M (Z_to_bv 64 x) 1 = Some [Z_to_bv 8 0].
Proof.
  intros segs E M lo w x K Hx. cbn [kentry_ok] in K. destruct K as [Hw [Hf Hr]].
  pose proof (flat_u _ _ _ Hf) as Hu. rewrite estart_lit in Hu.
  unfold flat in Hf. rewrite estart_lit in Hf. cbn [edenot] in Hr.
  rewrite word_to_le_bytes_zero in Hr by exact Hw.
  assert (Hb : bv_unsigned (adenot E (SA (ELit 0) lo)) + Z.of_nat w <= 2 ^ 64) by (rewrite Hu; lia).
  pose proof (APSX.rdn_nth segs M w (adenot E (SA (ELit 0) lo)) _ (Z.to_nat (x - lo)) Hb Hr ltac:(lia)) as H.
  rewrite Hu, Z2Nat.id in H by lia. replace (lo + (x - lo)) with x in H by lia. rewrite H.
  f_equal. f_equal. apply nth_repeat.
Qed.

Definition zcover (C : list kentry) (K : kentry) : bool :=
  match kz_iv K with
  | Some (lo, n) =>
      lit_ok lo n && (0 <? n) && (n <=? 8) &&
      all_bytes lo (Z.to_nat n) (fun x => existsb (fun K' => match kz_iv K' with
                                                          | Some iv => lit_ok (fst iv) (snd iv) && in_iv x iv
                                                          | None => false end) C)
  | None => false
  end.

Lemma kz_iv_inv : forall K lo n, kz_iv K = Some (lo, n) ->
  exists w, n = Z.of_nat w /\ K = KWord (SA (ELit 0) lo) w (ELit 0).
Proof.
  intros K lo n H. unfold kz_iv in H.
  repeat match type of H with
  | (if Z.eqb ?a 0 then _ else _) = _ => destruct (Z.eqb_spec a 0); [subst|discriminate]
  | (if (Z.eqb ?a 0 && Z.eqb ?b 0)%bool then _ else _) = _ =>
      destruct (Z.eqb_spec a 0); [|discriminate]; destruct (Z.eqb_spec b 0); [|discriminate]; subst; cbn in H
  | match ?x with _ => _ end = _ => destruct x; try discriminate
  end.
  injection H as <- <-. eexists. split; reflexivity.
Qed.

Lemma zcover_sound : forall segs E M C K,
  (forall K', In K' C -> kentry_ok segs E M K') -> zcover C K = true -> kentry_ok segs E M K.
Proof.
  intros segs E M C K HC H. unfold zcover in H.
  destruct (kz_iv K) as [[lo n]|] eqn:Hk; [|discriminate].
  apply kz_iv_inv in Hk as [w [-> ->]].
  apply andb_prop in H as [H Hall]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [Hl Hn].
  apply Z.leb_le in Hw. apply Z.ltb_lt in Hn.
  pose proof (lit_ok_spec _ _ Hl) as Hl'.
  cbn [kentry_ok]. split; [lia|]. split.
  - unfold flat. rewrite estart_lit. lia.
  - assert (Hu : bv_unsigned (adenot E (SA (ELit 0) lo)) = lo).
    { rewrite flat_u with (n := Z.of_nat w); [apply estart_lit|]. unfold flat. rewrite estart_lit. lia. }
    cbn [edenot]. rewrite word_to_le_bytes_zero by lia. rewrite <- map_const_seq with (s := 0%nat).
    apply APSX.rdn_of_nth; [rewrite Hu; lia|]. intros j Hj. rewrite Hu.
    pose proof (all_bytes_spec _ _ _ Hall (Z.of_nat j) ltac:(rewrite Z2Nat.id by lia; lia)) as Hb.
    apply existsb_exists in Hb as [K' [HK' Hb]].
    destruct (kz_iv K') as [[lo' n']|] eqn:Hk'; [|discriminate].
    apply kz_iv_inv in Hk' as [w' [-> ->]]. cbn [fst snd] in Hb. apply andb_prop in Hb as [Hl2 Hin].
    apply in_iv_spec in Hin. eapply zero_byte_of_cell; [apply HC; exact HK'|lia].
Qed.

Definition cells_check (U C : list kentry) : bool :=
  forallb (fun K => existsb (APC.kentry_eqb K) C || zcover C K) U.

Lemma cells_check_sound : forall segs E M U C,
  (forall K, In K C -> kentry_ok segs E M K) -> cells_check U C = true -> forall K, In K U -> kentry_ok segs E M K.
Proof.
  intros segs E M U C HC H K HK. unfold cells_check in H. rewrite forallb_forall in H.
  specialize (H K HK). apply orb_prop in H as [H|H].
  - apply existsb_exists in H as [K' [HK' Heq]]. apply APS.kentry_eqb_eq in Heq. subst K'. apply HC. exact HK'.
  - eapply zcover_sound; eauto.
Qed.

(* ---------- post specs ---------- *)

Fixpoint pss_check (U C : list SR.post_spec) : bool :=
  match U, C with
  | [], [] => true
  | u :: U', c :: C' =>
      Z.eqb (SR.ps_pc u) (SR.ps_pc c)
      && forallb (fun ie => existsb (fun je => Nat.eqb (fst ie) (fst je) && expr_eqb (snd ie) (snd je)) (SR.ps_regs c))
                 (SR.ps_regs u)
      && cells_check (SR.ps_cells u) (SR.ps_cells c) && pss_check U' C'
  | _, _ => false
  end.

Lemma pss_check_nth : forall U C i c, pss_check U C = true -> nth_error C i = Some c ->
  exists u, nth_error U i = Some u /\ SR.ps_pc u = SR.ps_pc c
         /\ (forall ie, In ie (SR.ps_regs u) -> In ie (SR.ps_regs c))
         /\ cells_check (SR.ps_cells u) (SR.ps_cells c) = true.
Proof.
  induction U as [|u U IH]; intros [|c' C] i c H Hn; cbn [pss_check] in H; try discriminate.
  - destruct i; discriminate.
  - repeat (apply andb_prop in H as [H ?]).
    destruct i as [|i].
    + cbn in Hn. injection Hn as Hc. subst c'. exists u. split; [reflexivity|]. split; [apply Z.eqb_eq; assumption|].
      split; [|assumption].
      intros [k e] Hie. match goal with Hr : forallb _ (SR.ps_regs u) = true |- _ => rewrite forallb_forall in Hr; specialize (Hr _ Hie) end.
      match goal with Hr : existsb _ _ = true |- _ => apply existsb_exists in Hr as [[k' e'] [Hin Heq]] end.
      apply andb_prop in Heq as [Hq1 Hq2]. apply Nat.eqb_eq in Hq1. apply expr_eqb_eq in Hq2. cbn in Hq1, Hq2. subst. exact Hin.
    + cbn in Hn. eapply IH; eassumption.
Qed.

(* ---------- the bridge ---------- *)

Section Bridge.
Variable segs : list Segment.
Variables (sr0 : list expr) (U_kn C_kn : list kentry) (U_F C_F : list SGP.region) (U_PSS C_PSS : list SR.post_spec).
Variables (nx0 : nat) (BR : list SGP.bfact) (pc0 : Z).

Hypothesis core : forall (fx : FPState) E R M,
  regs_ok E sr0 R -> know_ok segs E M C_kn -> SGP.bfacts_ok BR E ->
  exists (fx' : FPState) E' R' M' i ps,
       nth_error C_PSS i = Some ps
    /\ env_agree nx0 E E'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom segs))
    /\ (forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
    /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0
    /\ SGP.regions_ok E' C_F
    /\ (forall a : word, SGP.outside E' C_F a -> M' a = M a)
    /\ (forall K, In K (SR.ps_cells ps) -> kentry_ok segs E' M' K)
    /\ mem_grows M M'.

Hypothesis Hkn : kn_check U_kn C_kn = true.
Hypothesis Hout : out_check U_F C_F = true.
Hypothesis Hrok : rok_check U_F C_F = true.
Hypothesis Hpss : pss_check U_PSS C_PSS = true.

Theorem bridge : forall (fx : FPState) E R M,
  regs_ok E sr0 R -> know_ok segs E M U_kn -> SGP.bfacts_ok BR E ->
  exists (fx' : FPState) E' R' M' i ps,
       nth_error U_PSS i = Some ps
    /\ env_agree nx0 E E'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom segs))
    /\ (forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
    /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0
    /\ SGP.regions_ok E' U_F
    /\ (forall a : word, SGP.outside E' U_F a -> M' a = M a)
    /\ (forall K, In K (SR.ps_cells ps) -> kentry_ok segs E' M' K)
    /\ mem_grows M M'.
Proof.
  intros fx E R M HR HK HB.
  destruct (core fx E R M HR (kn_check_sound _ _ _ _ _ HK Hkn) HB)
    as (fx' & E' & R' & M' & i & c & Hn & Hag & Hms & Hregs & H0 & Hrok' & Hfr & Hcells & Hg).
  destruct (pss_check_nth _ _ _ _ Hpss Hn) as (u & Hu & Hpc & Hreg & Hcc).
  exists fx', E', R', M', i, u. split; [exact Hu|]. split; [exact Hag|]. split; [rewrite Hpc; exact Hms|].
  split; [intros k e Hie; apply Hregs, Hreg, Hie|]. split; [exact H0|].
  split; [exact (rok_check_sound _ _ _ Hrok Hrok')|].
  split; [intros a Ha; apply Hfr; exact (out_check_sound _ _ _ _ Hout Ha)|].
  split; [exact (cells_check_sound _ _ _ _ _ Hcells Hcc)|exact Hg].
Qed.
End Bridge.

End SBR.
