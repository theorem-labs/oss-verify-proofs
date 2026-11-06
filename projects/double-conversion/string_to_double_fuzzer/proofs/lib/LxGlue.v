(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk LibIface BnContract.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck LxSem LxWf LxSoundVal LxSoundMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS LXM LXI LXC LXSEM LXWF LXSV LXSM.
Open Scope Z_scope.

Module LXG.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint forall_zrange (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => f lo &&& forall_zrange f (lo + 1) n'
  end.
Lemma forall_zrange_sound : forall f lo n a, forall_zrange f lo n = true -> lo <= a < lo + Z.of_nat n -> f a = true.
Proof.
  intros f lo n. revert lo. induction n as [|n IH]; intros lo a H Ha; [lia|].
  cbn [forall_zrange] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec a lo) as [->|NE]; [exact H1|]. apply (IH (lo + 1)); [exact H2 | lia].
Qed.
Definition forall_ranges (f : Z -> bool) (rs : list (Z * Z)) : bool :=
  forallb (fun r => forall_zrange f (fst r) (Z.to_nat (snd r - fst r))) rs.
Lemma forall_ranges_sound : forall f rs a, forall_ranges f rs = true -> in_rangesZ a rs -> f a = true.
Proof.
  intros f rs a H (r & Hin & Hr). unfold forall_ranges in H. rewrite forallb_forall in H.
  specialize (H r Hin). eapply forall_zrange_sound; [exact H | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition byte_writable (segs : list Segment) (a : Z) : bool :=
  match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition byte_readable (segs : list Segment) (a : Z) : bool :=
  match memory_read segs (Z_to_bv 64 a) 1%N with Some [_] => true | _ => false end.
Definition ranges_disjointb (xs ys : list (Z * Z)) : bool :=
  forallb (fun x => forallb (fun y => (Z.leb (snd x) (fst y) ||| Z.leb (snd y) (fst x) ||| Z.leb (snd x) (fst x) ||| Z.leb (snd y) (fst y))) ys) xs.

(* [comment removed for export] *)
Definition scells_okb (U : uenv) : bool :=
  forallb (fun c : Z * sym => Nat.eqb (snd c) SYM_SC0 &&& Z.leb 0 (fst c) &&& Z.leb (fst c + 8) (2 ^ 32)
                              &&& forall_zrange (fun a => negb (LXM.in_ranges a 1 (ue_rw U))) (fst c) 8) (ue_scells U).

Definition uenv_okb (U : uenv) : bool :=
  forall_ranges (byte_writable (ue_segs U)) (ue_rw U)
  &&& forall_ranges (byte_readable (ue_segs U)) (ue_rw U)
  &&& forallb (fun r => Z.leb 0 (fst r) &&& Z.leb (snd r) (2 ^ 32)) (ue_rw U ++ ue_ro U)
  &&& ranges_disjointb (ue_rw U) (ue_ro U)
  &&& Z.leb 0 (ue_fr U)
  &&& tables_validb U
  &&& scells_okb U.

Lemma store_ok_1 : forall segs m a, byte_writable segs a = true -> store_ok segs m (Z_to_bv 64 a) 1 = true.
Proof.
  intros segs m a H. unfold byte_writable in H. cbn [store_ok]. unfold wview in *.
  destruct (m (Z_to_bv 64 a)); [reflexivity|].
  destruct (find_segment segs _ 1) as [seg|]; [|discriminate]. destruct (seg_writable seg); [|discriminate].
  destruct (segment_byte_at _ _); [reflexivity | discriminate].
Qed.

Lemma in_ranges1_false : forall a rs, LXM.in_ranges a 1 rs = false -> ~ in_rangesZ a rs.
Proof.
  intros a rs H (r & Hin & Hr). unfold LXM.in_ranges in H.
  assert (X : existsb (fun r0 : Z * Z => (fst r0 <=? a) &&& (a + 1 <=? snd r0)) rs = true).
  { apply existsb_exists. exists r. split; [exact Hin|]. apply andb_true_intro; split; apply Z.leb_le; lia. }
  rewrite X in H. discriminate.
Qed.

Lemma uenv_okb_sound : forall U, uenv_okb U = true -> uenv_ok U.
Proof.
  intros U H. unfold uenv_okb in H.
  apply andb_prop in H as [H HSC].
  apply andb_prop in H as [H HT]. apply andb_prop in H as [H HF]. apply andb_prop in H as [H HD].
  apply andb_prop in H as [H HS]. apply andb_prop in H as [HW HR].
  constructor.
  - intros a m Ha. apply store_ok_1. eapply forall_ranges_sound; eauto.
  - intros a Ha. pose proof (forall_ranges_sound _ _ a HR Ha) as X. unfold byte_readable in X.
    unfold w64. destruct (memory_read (ue_segs U) (Z_to_bv 64 a) 1) as [[|b [|]]|]; try discriminate. exists b; reflexivity.
  - intros a [Ha|Ha]; destruct Ha as (r & Hin & Hr); rewrite forallb_forall in HS;
      (specialize (HS r ltac:(apply in_app_iff; auto)); apply andb_prop in HS as [S1 S2]; apply Z.leb_le in S1; apply Z.leb_le in S2; lia).
  - intros a (r & Hin & Hr) (q & Hinq & Hq). unfold ranges_disjointb in HD. rewrite forallb_forall in HD.
    specialize (HD r Hin). rewrite forallb_forall in HD. specialize (HD q Hinq). cbn in HD.
    destruct (Z.leb_spec (snd r) (fst q)); [lia|]. destruct (Z.leb_spec (snd q) (fst r)); [lia|].
    destruct (Z.leb_spec (snd r) (fst r)); [lia|]. destruct (Z.leb_spec (snd q) (fst q)); [lia|]. discriminate.
  - apply Z.leb_le. exact HF.
  - exact HT.
  - intros a x Hin. unfold scells_okb in HSC. rewrite forallb_forall in HSC. specialize (HSC _ Hin). cbn [fst snd] in HSC.
    apply andb_prop in HSC as [HSC H4]. apply andb_prop in HSC as [HSC H3]. apply andb_prop in HSC as [H1 H2].
    apply Nat.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros i Hi. apply in_ranges1_false. pose proof (forall_zrange_sound _ a 8 (a + i) H4 ltac:(lia)) as X. cbv beta in X.
    destruct (LXM.in_ranges (a + i) 1 (ue_rw U)); [discriminate | reflexivity].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bm_get_In : forall bm a b, bm_get bm a = Some b -> In (a, b) bm.
Proof.
  induction bm as [|[x y] r IH]; intros a b H; cbn in H; [discriminate|].
  destruct (Z.ltb a x); [discriminate|]. destruct (Z.eqb_spec a x); [injection H; intros <-; subst; left; reflexivity | right; apply IH; exact H].
Qed.

Definition glue_okb (U : uenv) (HULL : Z * Z) (LIBR SNAP : list (Z * Z)) : bool :=
  match ue_rw U with [(lo, hi)] => Z.eqb lo (fst HULL) &&& Z.eqb hi (snd HULL) | _ => false end
  &&& forallb (fun r => Z.leb (fst HULL) (fst r) &&& Z.leb (snd r) (snd HULL)) LIBR
  &&& forallb (fun ab : Z * Z => in_rangesb (fst ab) LIBR &&& Z.leb 0 (snd ab) &&& Z.ltb (snd ab) 256) SNAP
  &&& forall_ranges (fun a => match bm_get SNAP a with Some _ => true | None => false end) LIBR
  &&& forallb (fun ab : Z * Z => match bm_get SNAP (fst ab) with Some b => Z.eqb b (snd ab) | None => false end) SNAP.

Record glue_ok (U : uenv) (HULL : Z * Z) (LIBR SNAP : list (Z * Z)) : Prop := GlueOk {
  go_rw : ue_rw U = [HULL];
  go_libr : forall a, LibIface.in_ranges a LIBR -> fst HULL <= a < snd HULL;
  go_snap : forall a b, In (a, b) SNAP -> LibIface.in_ranges a LIBR /\ 0 <= b < 256;
  go_cover : forall a, LibIface.in_ranges a LIBR -> exists b, bm_get SNAP a = Some b;
  go_func : forall a b, In (a, b) SNAP -> bm_get SNAP a = Some b
}.

Lemma in_ranges_rangesZ : forall a rs, LibIface.in_ranges a rs <-> in_rangesZ a rs.
Proof. intros; unfold LibIface.in_ranges, in_rangesZ; tauto. Qed.

Lemma glue_okb_sound : forall U HULL LIBR SNAP, glue_okb U HULL LIBR SNAP = true -> glue_ok U HULL LIBR SNAP.
Proof.
  intros U [hlo hhi] LIBR SNAP H. unfold glue_okb in H.
  apply andb_prop in H as [H HFN]. apply andb_prop in H as [H HC]. apply andb_prop in H as [H HSN]. apply andb_prop in H as [HRW HL].
  constructor; cbn [fst snd] in *.
  - destruct (ue_rw U) as [|[lo hi] [|]]; try discriminate. apply andb_prop in HRW as [E1 E2]. apply Z.eqb_eq in E1; apply Z.eqb_eq in E2. subst; reflexivity.
  - intros a (r & Hin & Hr). rewrite forallb_forall in HL. specialize (HL r Hin). apply andb_prop in HL as [L1 L2]. apply Z.leb_le in L1; apply Z.leb_le in L2. lia.
  - intros a b Hin. rewrite forallb_forall in HSN. specialize (HSN _ Hin). cbn [fst snd] in HSN.
    apply andb_prop in HSN as [X B2]. apply andb_prop in X as [B0 B1]. apply in_rangesb_spec in B0. apply Z.leb_le in B1. apply Z.ltb_lt in B2. split; [exact B0 | lia].
  - intros a Ha. pose proof (forall_ranges_sound _ _ a HC ltac:(apply in_ranges_rangesZ; exact Ha)) as X. cbv beta in X.
    destruct (bm_get SNAP a) as [b|]; [exists b; reflexivity | discriminate].
  - intros a b Hin. rewrite forallb_forall in HFN. specialize (HFN _ Hin). cbn [fst snd] in HFN.
    destruct (bm_get SNAP a) as [b'|]; [|discriminate]. apply Z.eqb_eq in HFN. subst; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Variable U : uenv.
  Variables (HULL : Z * Z) (LIBR SNAP : list (Z * Z)).
  Hypothesis UOK : uenv_ok U.
  Hypothesis GOK : glue_ok U HULL LIBR SNAP.
  Let segs := ue_segs U.

  (* [comment removed for export] *)
  Definition greg (regs : bvmap 5 word) (r : Z) : Z := bv_unsigned (getr regs (Z_to_bv 5 r)).
  Definition rho_entry (regs : bvmap 5 word) (n sc : Z) : valuation := fun x =>
    nth x [greg regs 2; greg regs 10; n; greg regs 1; greg regs 3; greg regs 4; greg regs 8; greg regs 9;
           greg regs 18; greg regs 19; greg regs 20; greg regs 21; greg regs 22; greg regs 23; greg regs 24; greg regs 25;
           greg regs 26; greg regs 27; sc] 0.

  (* [comment removed for export] *)
  Lemma entry_scells : forall (regs : bvmap 5 word) (n : Z) (c : word) (mem : word -> option byte),
    (forall a x, In (a, x) (ue_scells U) -> rdn segs mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 c)) ->
    scells_ok U (rho_entry regs n (bv_unsigned c)) mem.
  Proof.
    intros regs n c mem H a x Hin. exists (word_to_le_bytes 8 c). split; [apply (H a x); exact Hin|].
    rewrite SeqExec.bytes_le_to_Z_8. destruct (uo_scells U UOK a x Hin) as [-> _]. reflexivity.
  Qed.

  Lemma getr_reg_get : forall regs r, (1 <= r < 32)%nat -> reg_get regs (Z_to_bv 5 (Z.of_nat r)) = getr regs (Z_to_bv 5 (Z.of_nat r)).
  Proof.
    intros regs r Hr. unfold getr. destruct (bv_eqb (Z_to_bv 5 (Z.of_nat r)) 0) eqn:E; [|reflexivity].
    exfalso. unfold bv_eqb in E. apply Z.eqb_eq in E. rewrite Z_to_bv_unsigned in E.
    unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by lia. change (bv_unsigned 0) with 0 in E. lia.
  Qed.

  Theorem entry_R : forall (fx : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte) (n sc : Z) (ENTRY NMAX : Z) (abs0 : list (Z * Z)),
    let sp := greg regs 2 in
    let data := greg regs 10 in
    let ret := greg regs 1 in
    getr regs (Z_to_bv 5 11) = Z_to_bv 64 n ->
    0 <= n < NMAX -> ret mod 4 = 0 ->
    4096 <= data -> data + n + 4096 < 2 ^ 62 -> data mod 16 = 0 ->
    sp mod 16 = 0 -> 2 ^ 32 <= sp - ue_fr U -> sp < 2 ^ 62 ->
    (data + n <= sp - ue_fr U \/ sp <= data) ->
    (forall a, sp - ue_fr U <= a < sp -> find_segment segs a 1 = None) ->
    (forall i, 0 <= i < n -> exists b, rdn segs mem (Z_to_bv 64 (data + i)) 1 = Some [b]) ->
    store_ok segs mem (Z_to_bv 64 (sp - ue_fr U)) (Z.to_nat (ue_fr U)) = true ->
    ro_ok segs (ue_ro U) mem ->
    ((abs0 = [] /\ statics_pristine LIBR mem) \/ (abs0 = SNAP /\ statics_snap SNAP mem)) ->
    (forall a, fst HULL <= a < snd HULL -> ~ LibIface.in_ranges a LIBR -> mem (Z_to_bv 64 a) = None) ->
    frm_zero fx ->
    R U (rho_entry regs n sc) mem (rho_entry regs n sc) (entry_state ENTRY NMAX abs0) (@mkst fx regs (Z_to_bv 64 ENTRY) mem rom).
  Proof.
    intros fx regs mem rom n sc ENTRY NMAX abs0 sp data ret Hn Hnr Hret Hd1 Hd2 Hd3 Hs1 Hs2 Hs3 Hdisj Hnoseg Hpay Hst Hro Habs Hhull Hfrm.
    cbv delta [sp data ret] in *. clear sp data ret. unfold greg in *.
    pose proof (uo_fr U UOK) as Hfr.
    set (sp := bv_unsigned (getr regs (Z_to_bv 5 2))).
    assert (WIN : forall a, sp - ue_fr U <= a < sp -> exists b, mem (w64 a) = Some b).
    { intros a Ha.
      assert (Hlo : bv_unsigned (Z_to_bv 64 (sp - ue_fr U)) = sp - ue_fr U).
      { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
      assert (Ha64 : bv_unsigned (Z_to_bv 64 a) = a).
      { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
      pose proof (store_ok_all segs mem (Z.to_nat (ue_fr U)) (Z_to_bv 64 (sp - ue_fr U)) ltac:(rewrite Hlo; lia) Hst (Z_to_bv 64 a)
                    ltac:(rewrite Hlo, Ha64; lia)) as SO.
      unfold wview in SO. unfold w64. destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
      rewrite Ha64 in SO. unfold segs in SO, Hnoseg. cbn in SO. rewrite (Hnoseg a Ha) in SO. exfalso; apply SO; reflexivity. }
    subst sp.
    constructor; cbn [s_pc s_regs s_ctx s_next s_stk s_arrs s_abs s_pcache s_resv s_pay entry_state ms_pc_val ms_svc_pending ms_regs ms_mem ms_resv ms_fcsr mkst].
    - intros x Hx; reflexivity.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *) intros r Hr. rewrite getr_reg_get by exact Hr.
      do 32 (destruct r as [|r];
        [ match goal with |- context [Z.of_nat ?k] => let v := eval cbv in (Z.of_nat k) in change (Z.of_nat k) with v end;
          cbn -[getr Z_to_bv]; try exact I; rewrite lvar_sound; unfold rho_entry; cbn -[getr Z_to_bv]; unfold greg;
          first [ symmetry; apply Z_to_bv_bv_unsigned | rewrite Hn; reflexivity ] |]). lia.
    - (* [comment removed for export] *) split.
      + unfold entry_ctx. split.
        * constructor; [|constructor].
          rewrite laddc_sound, lneg_sound, ladd_sound, !lvar_sound. unfold rho_entry, greg. cbn -[Z.pow Z.sub Z.add Z.opp getr Z_to_bv bv_unsigned]. lia.
        * pose proof (bv_unsigned_in_range _ (getr regs (Z_to_bv 5 1))) as RR. change (bv_modulus 64) with (2 ^ 64) in RR.
          intros y. unfold bget, SYM_N, SYM_DATA, SYM_SP0, SYM_RA. cbn [find fst snd].
          do 4 (destruct y as [|y]; [cbn; unfold in_itv, rho_entry, greg; cbn -[Z.pow Z.sub getr Z_to_bv bv_unsigned]; try lia; try exact (conj I I)|]).
          cbn. exact (conj I I).
      + reflexivity.
    - constructor.
    - constructor.
    - (* [comment removed for export] *) split; [exact WIN | exact Hnoseg].
    - (* [comment removed for export] *) split; [|split; [|split; [intros ? ? ? []| intros ? ? []]]];
        unfold rho_entry, SYM_SP0, SYM_DATA, SYM_N, greg; cbn -[Z.pow Z.sub Z.add Z.opp Z.mul getr Z_to_bv bv_unsigned rd1]; [|lia].
      intros i Hi. destruct (Hpay i Hi) as [b Hb]. exists b. unfold rd1. unfold segs in Hb. unfold w64. rewrite Hb. reflexivity.
    - (* [comment removed for export] *) split; [|split].
      + intros a b Hg. destruct Habs as [[-> HP]|[-> HS]]; [cbn in Hg; discriminate|].
        pose proof (bm_get_In _ _ _ Hg) as Hin. destruct (go_snap _ _ _ _ GOK a b Hin) as [Hl Hb].
        split; [|split; [exact Hb|]].
        * rewrite (go_rw _ _ _ _ GOK). exists HULL. split; [left; reflexivity|]. apply (go_libr _ _ _ _ GOK). exact Hl.
        * apply HS. exact Hin.
      + intros a Ha Hg. rewrite (go_rw _ _ _ _ GOK) in Ha. destruct Ha as (r & [<-|[]] & Hr).
        destruct (in_rangesb a LIBR) eqn:Hl.
        * apply in_rangesb_spec in Hl. destruct Habs as [[-> HP]|[-> HS]]; [apply HP; exact Hl|].
          destruct (go_cover _ _ _ _ GOK a Hl) as [b Hb]. rewrite Hb in Hg. discriminate.
        * apply Hhull; [exact Hr|]. intros X. apply in_rangesb_spec in X. rewrite X in Hl. discriminate.
      + intros a b Ha Hm. apply (Hro a b); [apply in_ranges_rangesZ; exact Ha | exact Hm].
    - exact I.
    - exact Hfrm.
    - split; [intros; reflexivity | intros a b Hb; exists b; exact Hb].
    - unfold rho_entry, SYM_SP0. cbn -[Z.pow Z.sub Z.add Z.opp Z.mul getr Z_to_bv bv_unsigned]. unfold greg. lia.
    - unfold rho_entry, SYM_SP0, SYM_DATA. cbn -[Z.pow Z.sub Z.add Z.opp Z.mul Z.modulo getr Z_to_bv bv_unsigned]. unfold greg. split; assumption.
    - unfold rho_entry, SYM_RA. cbn -[Z.pow Z.sub Z.add Z.opp Z.mul Z.modulo getr Z_to_bv bv_unsigned]. unfold greg.
      pose proof (bv_unsigned_in_range _ (getr regs (Z_to_bv 5 1))) as RR. change (bv_modulus 64) with (2 ^ 64) in RR. split; [lia | exact Hret].
    - unfold rho_entry, SYM_DATA, SYM_N. cbn -[Z.pow Z.sub Z.add Z.opp Z.mul getr Z_to_bv bv_unsigned]. unfold greg. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bm_eqb_eq : forall a b, bm_eqb a b = true -> a = b.
  Proof.
    induction a as [|[x y] a' IH]; intros [|[u v] b'] H; cbn in H; try discriminate; [reflexivity|].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1; apply Z.eqb_eq in H2. subst.
    rewrite (IH _ H3). reflexivity.
  Qed.

  Theorem exit_post : forall (G : sym -> Z) (M0 : word -> option byte) (fx : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (n sc : Z)
                             (Un : unitT) (S : astate) (rho' : valuation) (ms' : machine_state),
    G = rho_entry regs n sc -> M0 = mem -> un_env Un = U -> un_snap Un = SNAP ->
    (forall a, fst HULL <= a < snd HULL -> ~ LibIface.in_ranges a LIBR -> mem (Z_to_bv 64 a) = None) ->
    exit_ok Un S = true ->
    R U G M0 rho' (set_pc S (rho' SYM_RA)) ms' ->
    exists (fx' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte),
         ms' = @mkst fx' regs' (getr regs (Z_to_bv 5 1)) mem' (ms_rom ms')
      /\ keeps_cs regs regs'
      /\ getr regs' (Z_to_bv 5 10) = Z_to_bv 64 0
      /\ mem_frame mem mem' ((greg regs 2 - ue_fr U, greg regs 2) :: LIBR)
      /\ lib_statics HULL LIBR SNAP mem'
      /\ frm_zero fx'.
  Proof.
    intros G M0 fx regs mem n sc Un S rho' ms' HG HM HUn HSn Hhull Hex HR. subst G M0.
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
    cbn [s_pc s_regs s_ctx s_next s_stk s_arrs s_abs s_pcache s_resv s_pay set_pc] in *.
    unfold exit_ok in Hex. apply andb_prop in Hex as [Hex Hrv]. apply andb_prop in Hex as [Hex Habs].
    apply andb_prop in Hex as [Hex Ha0]. apply andb_prop in Hex as [Hsp Hcs].
    (* [comment removed for export] *)
    assert (GL : forall x, (x < NGLOB)%nat -> rho' x = rho_entry regs n sc x) by (intros x Hx; apply Rglob; exact Hx).
    (* [comment removed for export] *)
    assert (RS : forall r x, (1 <= r < 32)%nat -> (x < NGLOB)%nat -> reg_is_sym S r x = true ->
                 reg_get (ms_regs ms') (Z_to_bv 5 (Z.of_nat r)) = w64 (rho_entry regs n sc x)).
    { intros r x Hr Hx H. unfold reg_is_sym, getreg in H. specialize (Rregs r Hr).
      destruct (Nat.eqb_spec r 0); [lia|].
      destruct (list_get (s_regs S) r Top) as [|l| |] eqn:El; try discriminate.
      apply leqb_sound in H. subst l. cbn in Rregs. rewrite lvar_sound, (GL x Hx) in Rregs. exact Rregs. }
    exists (mkFP (ms_fregs ms') (ms_fcsr ms')), (ms_regs ms'), (ms_mem ms').
    assert (RESV : ms_resv ms' = None).
    { unfold resv_ok in Rresv. destruct (s_resv S); [discriminate|]. destruct (ms_resv ms'); [destruct Rresv | reflexivity]. }
    split.
    { destruct ms' as [mregs mfregs mpc msvc mresv mfcsr mmem mrom]; cbn in *. subst. unfold mkst. cbn. f_equal.
      rewrite (GL SYM_RA) by (unfold SYM_RA, NGLOB; lia). unfold rho_entry, SYM_RA, greg. cbn -[getr Z_to_bv bv_unsigned].
      apply Z_to_bv_bv_unsigned. }
    assert (CS1 : forall r x, (1 <= r < 32)%nat -> (x < NGLOB)%nat -> reg_is_sym S r x = true ->
                  rho_entry regs n sc x = greg regs (Z.of_nat r) ->
                  getr (ms_regs ms') (Z_to_bv 5 (Z.of_nat r)) = getr regs (Z_to_bv 5 (Z.of_nat r))).
    { intros r x Hr Hx H E. rewrite <- (getr_reg_get (ms_regs ms') r Hr), (RS r x Hr Hx H), E. unfold greg. apply Z_to_bv_bv_unsigned. }
    rewrite forallb_forall in Hcs.
    split.
    { (* [comment removed for export] *) intros r Hr. unfold cs_regs in Hr.
      repeat match type of Hr with
      | In _ (_ :: _) => destruct Hr as [<-|Hr]
      | In _ [] => destruct Hr
      end;
      first [ apply (CS1 2%nat SYM_SP0); [lia | unfold SYM_SP0, NGLOB; lia | exact Hsp | reflexivity]
            | match goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
                let rn := eval cbv in (Z.to_nat z) in
                match eval cbv in cs_reg_syms with context [(rn, ?x)] =>
                  apply (CS1 rn x); [lia | unfold NGLOB; lia | apply (Hcs (rn, x)); cbn; tauto | reflexivity] end end ]. }
    split.
    { (* [comment removed for export] *) change (Z_to_bv 5 10) with (Z_to_bv 5 (Z.of_nat 10)). rewrite <- (getr_reg_get (ms_regs ms') 10 ltac:(lia)). specialize (Rregs 10%nat ltac:(lia)).
      unfold getreg in Ha0. cbn [Nat.eqb] in Ha0.
      destruct (list_get (s_regs S) 10 Top) as [|l| |] eqn:El; try discriminate. apply leqb_sound in Ha0. subst l.
      cbn in Rregs. rewrite lconst_sound in Rregs. exact Rregs. }
    (* [comment removed for export] *)
    assert (ABS : s_abs S = [] \/ s_abs S = SNAP).
    { destruct (bm_eqb (s_abs S) []) eqn:E1; [left; apply bm_eqb_eq; exact E1|].
      cbn in Habs. right. rewrite <- HSn. apply bm_eqb_eq. exact Habs. }
    destruct Rabs as (A1 & A2 & A3). rewrite (go_rw _ _ _ _ GOK) in A1, A2.
    assert (HULLNONE : forall a, fst HULL <= a < snd HULL -> ~ LibIface.in_ranges a LIBR -> ms_mem ms' (Z_to_bv 64 a) = None).
    { intros a Ha Hn. apply A2; [exists HULL; split; [left; reflexivity | exact Ha]|].
      destruct ABS as [-> | ->]; [reflexivity|].
      destruct (bm_get SNAP a) as [b|] eqn:Hg; [|reflexivity]. exfalso. apply Hn.
      exact (proj1 (go_snap _ _ _ _ GOK a b (bm_get_In _ _ _ Hg))). }
    split; [|split].
    - (* [comment removed for export] *) destruct Rframe as [F1 F2]. split; [|exact F2].
      intros a Hnin. rewrite (GL SYM_SP0) in F1 by (unfold SYM_SP0, NGLOB; lia).
      unfold rho_entry, SYM_SP0 in F1. cbn -[Z.pow Z.sub Z.add Z.opp Z.mul getr Z_to_bv bv_unsigned] in F1.
      destruct (Z.lt_ge_cases (bv_unsigned a) (greg regs 2 - ue_fr U)) as [Hlt|Hge];
        [|destruct (Z.lt_ge_cases (bv_unsigned a) (greg regs 2)) as [Hlt2|Hge2];
          [exfalso; apply Hnin; exists (greg regs 2 - ue_fr U, greg regs 2); split; [left; reflexivity | cbn; lia]|]].
      all: destruct (in_rangesb (bv_unsigned a) LIBR) eqn:Hl;
        [exfalso; apply Hnin; apply in_rangesb_spec in Hl; destruct Hl as (r & Hr & Hin); exists r; split; [right; exact Hr | exact Hin]|].
      all: assert (Hnl : ~ LibIface.in_ranges (bv_unsigned a) LIBR) by (intros X; apply in_rangesb_spec in X; rewrite X in Hl; discriminate).
      all: destruct (Z.lt_ge_cases (bv_unsigned a) (fst HULL)) as [H1|H1];
        [apply F1; [unfold greg in *; lia | intros X; rewrite (go_rw _ _ _ _ GOK) in X; destruct X as (r & [<-|[]] & Hr); lia]|].
      all: destruct (Z.lt_ge_cases (bv_unsigned a) (snd HULL)) as [H2|H2];
        [|apply F1; [unfold greg in *; lia | intros X; rewrite (go_rw _ _ _ _ GOK) in X; destruct X as (r & [<-|[]] & Hr); lia]].
      all: rewrite <- (Z_to_bv_bv_unsigned 64 a), (HULLNONE (bv_unsigned a)), (Hhull (bv_unsigned a)); try reflexivity; try assumption; lia.
    - (* [comment removed for export] *) split; [|exact HULLNONE].
      destruct ABS as [E|E]; rewrite E in A1, A2.
      + left. intros a Ha. apply A2; [|reflexivity]. exists HULL. split; [left; reflexivity|]. apply (go_libr _ _ _ _ GOK). exact Ha.
      + right. intros a b Hin. destruct (A1 a b (go_func _ _ _ _ GOK a b Hin)) as (_ & _ & Hm). exact Hm.
    - (* [comment removed for export] *) exact Rfrm.
  Qed.
End Entry.
End LXG.
