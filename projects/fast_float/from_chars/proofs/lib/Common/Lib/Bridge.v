(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning MState Mem Cells Exec Step Frame Image RegsEquiv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mkst_MS : forall (fx : FPState) regs pc mem rom,
  @mkst fx regs pc mem rom = MS regs (@fp_regs fx) pc (@fp_csr fx) None mem rom.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition fp_of (F : bvmap 5 word) (fc : bv 32) : FPState := mkFP F fc.

Lemma MS_mkst : forall regs F pc fc mem rom,
  MS regs F pc fc None mem rom = @mkst (fp_of F fc) regs pc mem rom.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma msteps_catsim : forall a b, Exec.msteps segs a b -> CatSim.msteps segs a b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a b H. induction H as [ms | ms ms1 ms2 [Hsvc Hst] Hrest IH].
  - apply CatSim.mst_refl.
  - eapply CatSim.mst_step; eassumption.
Qed.

#[using="Type"] Lemma catsim_msteps : forall a b, CatSim.msteps segs a b -> Exec.msteps segs a b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a b H. induction H as [ms | ms ms1 ms2 Hsvc Hst Hrest IH].
  - apply msteps_refl.
  - eapply msteps_cons; [split; eassumption | exact IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma mkst_eqv_mkR_of : forall (fx : FPState) regs pc mem rom,
  ms_eqv (@mkst fx regs pc mem rom) (MS (mkR_of regs) (@fp_regs fx) pc (@fp_csr fx) None mem rom).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros. split; [| split; [| repeat split]]; cbn.
  - apply regs_eqv_mkR.
  - apply fregs_eqv_refl.
Qed.

#[using="Type"] Theorem evt_bridge : forall (fx : FPState) regs pc mem rom (Q : machine_state -> Prop),
  evt segs Q (MS (mkR_of regs) (@fp_regs fx) pc (@fp_csr fx) None mem rom) ->
  exists s, CatSim.msteps segs (@mkst fx regs pc mem rom) s /\ exists s0, Q s0 /\ ms_eqv s0 s.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fx regs pc mem rom Q Hevt.
  pose proof (evt_eqv_l segs Q _ _ (mkst_eqv_mkR_of fx regs pc mem rom) Hevt) as H.
  destruct (evt_elim segs Q _ H) as (s & Hrun & s0 & HQ & Hs0).
  exists s. split; [apply msteps_catsim; exact Hrun|]. exists s0. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma evt_resume : forall Q (fx : FPState) regs pc mem rom,
  evt segs Q (MS (mkR_of regs) (@fp_regs fx) pc (@fp_csr fx) None mem rom) ->
  evt segs Q (@mkst fx regs pc mem rom).
Proof. LiaFast.lf_pins LiaFast.u0. intros Q fx regs pc mem rom H. eapply evt_eqv_l; [apply mkst_eqv_mkR_of | exact H]. Qed.

#[using="Type"] Lemma evt_after_summary : forall Q (fx fx' : FPState) regs regs' pc pc' mem mem' rom,
  CatSim.msteps segs (@mkst fx regs pc mem rom) (@mkst fx' regs' pc' mem' rom) ->
  evt segs Q (MS (mkR_of regs') (@fp_regs fx') pc' (@fp_csr fx') None mem' rom) ->
  evt segs Q (@mkst fx regs pc mem rom).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Q fx fx' regs regs' pc pc' mem mem' rom Hrun H.
  eapply evt_msteps; [apply catsim_msteps; exact Hrun|]. apply evt_resume. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ms_eqv_MS_inv : forall R F pc fc m ro s,
  ms_eqv (MS R F pc fc None m ro) s ->
  exists (fx' : FPState) regs',
    s = @mkst fx' regs' pc m ro
    /\ (forall r, getr regs' r = getr R r)
    /\ (forall r, reg_get (@fp_regs fx') r = reg_get F r)
    /\ @fp_csr fx' = fc.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R F pc fc m ro [R' F' pc' svc' rv' fc' m' ro'] (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  cbn in *. subst.
  exists (fp_of F' fc'), R'. split; [reflexivity|]. split; [|split; [|reflexivity]].
  - intros r. symmetry. apply HR.
  - intros r. symmetry. apply HF.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma frame_of_munch : forall W m m',
  munch W m m' -> wmono segs m m' ->
  (forall x : word, outside W (bv_unsigned x) -> m' x = m x)
  /\ (forall x : word, m x <> None -> m' x <> None).
Proof. LiaFast.lf_pins LiaFast.u0. intros W m m' MU WM. split; [exact MU | exact WM]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition in_rng (a base : word) (len : Z) : Prop :=
  (bv_unsigned base <= bv_unsigned a < bv_unsigned base + len)%Z.

Fixpoint woutside (a : word) (rs : list (word * Z)) : Prop :=
  match rs with
  | [] => True
  | (b, n) :: rs' => ~ in_rng a b n /\ woutside a rs'
  end.

Definition mem_grows (m m' : word -> option byte) : Prop :=
  forall x, m x <> None -> m' x <> None.

Definition frame_mod (mem mem' : word -> option byte) (rs : list (word * Z)) : Prop :=
  (forall a, woutside a rs -> mem' a = mem a) /\ mem_grows mem mem'.

(* [comment removed for export] *)
Definition ivls_of (rs : list (word * Z)) : list ivl :=
  map (fun bn => (bv_unsigned (fst bn), bv_unsigned (fst bn) + snd bn)%Z) rs.

#[using="Type"] Lemma woutside_outside : forall rs a, woutside a rs -> outside (ivls_of rs) (bv_unsigned a).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction rs as [|[b n] rs IH]; intros a H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [exact H1| apply IH; exact H2].
Qed.

#[using="Type"] Lemma frame_mod_of_munch : forall rs m m',
  munch (ivls_of rs) m m' -> wmono segs m m' -> frame_mod m m' rs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rs m m' MU WM. split; [| exact WM].
  intros a Ha. apply MU. apply woutside_outside. exact Ha.
Qed.

#[using="Type"] Lemma outside_woutside : forall rs a, outside (ivls_of rs) (bv_unsigned a) -> woutside a rs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction rs as [|[b n] rs IH]; intros a H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma munch_of_frame_mod : forall rs m m',
  frame_mod m m' rs -> munch (ivls_of rs) m m' /\ wmono segs m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rs m m' [HO HG]. split; [| exact HG].
  intros x Hx. apply HO. apply outside_woutside. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma find_segment_none_above : forall (sl : list Segment) a n,
  Forall (fun sg => (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= a)%Z) sl -> (0 < n)%Z ->
  find_segment sl a n = None.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction sl as [|sg sl IH]; intros a n H Hn; cbn; [reflexivity|].
  inversion H; subst.
  destruct (Z.leb_spec0 (Z.of_N (seg_base sg)) a); destruct (Z.leb_spec0 (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))); cbn [andb];
    try (apply IH; assumption). exfalso. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_of_store_ok : forall m lo (n : nat),
  store_ok segs m (wa lo) n = true -> (0 <= lo)%Z -> (lo + Z.of_nat n <= 2^64)%Z ->
  (forall a, (lo <= a < lo + Z.of_nat n)%Z -> find_segment segs a 1 = None) ->
  stk segs m lo (lo + Z.of_nat n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo n Hs Hlo Hhi Hout. split; [lia|]. split; [lia|].
  intros a Ha.
  pose proof (store_ok_wview segs m (wa lo) n (Z.to_nat (a - lo)) Hs ltac:(lia)) as W.
  rewrite wa_unsigned in W by lia. replace (lo + Z.of_nat (Z.to_nat (a - lo)))%Z with a in W by lia.
  split; [exact W|].
  unfold wview in W. unfold mrd. rewrite wa_unsigned in W by lia. rewrite (Hout a Ha) in W.
  destruct (m (wa a)) as [b|]; [exists b; reflexivity|]. exfalso. apply W. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_of_readable : forall m (A : Z) (n : nat),
  (0 <= A)%Z -> (A + Z.of_nat n <= 2^64)%Z ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> exists b, rdn segs m (wa (A + i)) 1 = Some [b]) ->
  exists bs, length bs = n /\ bytes_at segs m A bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A n HA Hn H.
  assert (G : forall k, (k <= n)%nat -> exists bs, length bs = k /\
             forall i, (i < k)%nat -> mrd segs m (wa (A + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb).
      exists (bs ++ [b]). split. { rewrite app_length. cbn. lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2, Hlen, Nat.sub_diag by lia. cbn.
        rewrite rdn_unfold in Hb. destruct (mrd segs m (wa (A + Z.of_nat k))) as [b'|]; [|discriminate].
        cbn in Hb. inversion Hb. reflexivity.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G n ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_of_defined : forall m (A : Z) (n : nat),
  (0 <= A)%Z -> (A + Z.of_nat n <= 2^64)%Z ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> m (wa (A + i)) <> None) ->
  exists bs, length bs = n /\ bytes_at segs m A bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A n HA Hn H. apply bytes_at_of_readable; [exact HA | exact Hn |].
  intros i Hi. specialize (H i Hi). rewrite rdn_unfold. unfold mrd.
  destruct (m (wa (A + i))) as [b|]; [| exfalso; apply H; reflexivity].
  exists b. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pristine_of_list : forall (L : list (Z * Z)) m lo hi,
  (forall lo' hi' j, In (lo', hi') L -> (lo' <= j < hi')%Z -> m (Z_to_bv 64 j) = None) ->
  In (lo, hi) L -> (0 <= lo)%Z -> (hi <= 2^64)%Z -> pristine m lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L m lo hi H Hin Hlo Hhi. split; [lia|]. split; [lia|].
  intros i Hi. unfold wa. apply (H lo hi i Hin Hi).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ret_pc_landZ : forall k : word,
  ret_pc k = Z_to_bv 64 (Z.land (bv_unsigned k + 0) (-2)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k. unfold ret_pc. apply bv_eq.
  rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1%Z. change (Z.lnot 1) with (-2)%Z. rewrite Z.add_0_r.
  rewrite <- Z_land_m2_wrap. f_equal. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

#[using="Type"] Lemma ret_pc_of_ret_ok : forall k : word,
  Z_to_bv 64 (Z.land (bv_unsigned k + 0) (-2)) = k -> ret_pc k = k.
Proof. LiaFast.lf_pins LiaFast.u0. intros k H. rewrite ret_pc_landZ. exact H. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac bridge_destruct_exs PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => let x := fresh "pv" in destruct PO as [x PO]; bridge_destruct_exs PO
  | _ => idtac
  end.

Ltac lib_bridge SPEC :=
  lazymatch goal with
  | |- exists (fx' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte),
         CatSim.msteps ?segs (@mkst ?fx ?regs ?pc ?mem ?rom) _ /\ _ =>
    let s := fresh "s" in let RUN := fresh "BR_run" in let s0 := fresh "s0" in
    let PO := fresh "BR_post" in let EQV := fresh "EQV" in
    destruct (evt_bridge segs fx regs pc mem rom _ SPEC) as (s & RUN & s0 & PO & EQV);
    (* [comment removed for export] *)
    bridge_destruct_exs PO;
    let E := fresh "E" in
    destruct PO as [E PO]; subst s0;
    let fx' := fresh "fx'" in let regs' := fresh "regs'" in
    let Es := fresh "Es" in
    destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as (fx' & regs' & Es & BR_regs & BR_fregs & BR_fcsr);
    clear EQV; subst s;
    exists fx', regs';
    lazymatch type of RUN with
    | CatSim.msteps _ _ (@mkst _ _ _ ?m' _) => exists m'
    end;
    split; [ exact RUN | clear RUN ]
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac simp_getr :=
  repeat match goal with
  | |- context [getr ?R ?r] =>
      is_concrete_map R;
      let b := eval vm_compute in (bv_eqb r 0) in
      change (getr R r) with (if b then Z_to_bv 64 0 else reg_get R r); cbv iota
  end;
  simp_regs;
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Ltac simp_getr_in H :=
  repeat match type of H with
  | context [getr ?R ?r] =>
      is_concrete_map R;
      let b := eval vm_compute in (bv_eqb r 0) in
      change (getr R r) with (if b then Z_to_bv 64 0 else reg_get R r) in H; cbv iota in H;
      let p := eval vm_compute in (bv_key r) in
      change (reg_get R r) with (match tget p R with Some v => v | None => w0 end) in H;
      cbv beta iota delta [tget mkR] in H
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac norm_pc_lit_in RUN :=
  lazymatch type of RUN with
  | CatSim.msteps _ (@mkst _ _ ?pcA _ _) _ =>
      lazymatch pcA with
      | Z_to_bv 64 _ => idtac
      | _ => tryif is_var pcA then idtac else
             (let z := eval vm_compute in (bv_unsigned pcA) in
              replace pcA with (Z_to_bv 64 z) in RUN by (apply bv_eq; vm_compute; reflexivity))
      end
  | _ => idtac
  end.

Ltac resume_after_summary RUN :=
  norm_pc_lit_in RUN;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc None ?m ?ro) =>
      change (evt segs Q (@mkst (fp_of F fc) R pc m ro));
      eapply (evt_after_summary segs Q (fp_of F fc));
      [ exact RUN | unfold mkR_of ]
  end.

(* [comment removed for export] *)
Lemma In_of_existsb : forall (r : reg) (l : list reg),
  existsb (fun x => bv_eqb x r) l = true -> In r l.
Proof.
  intros r l. induction l as [|x l IH]; cbn; intros H; [discriminate|].
  destruct (bv_eqb x r) eqn:E.
  - left. apply bv_eqb_eq in E. exact E.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Ltac use_kept KEEP :=
  lazymatch type of KEEP with
  | forall r, In r ?L -> getr ?R' r = _ =>
      repeat match goal with
      | |- context [getr R' ?k] => rewrite (KEEP k (In_of_existsb k L eq_refl))
      end
  end.
Ltac use_kept_in KEEP H :=
  lazymatch type of KEEP with
  | forall r, In r ?L -> getr ?R' r = _ =>
      repeat match type of H with
      | context [getr R' ?k] => rewrite (KEEP k (In_of_existsb k L eq_refl)) in H
      end
  end.
