(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec SeqExec StoreOk RefMemcpyLib AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2 AX2S APC AP APS APSX.
Open Scope Z_scope.

Module HSN.
Section X.
  Variable segs : list Segment.
  Variable nx0 : N.
  (* [comment removed for export] *)
  Definition node_forget8 (cs : acs) (a lo hi : Z) : option acs :=
    let k0 := kn cs in
    if negb (flat_x k0 (ELit 0) a (ELit 8) && Z.leb 0 a && Z.ltb (a + 8) two64 && Z.leb 0 lo && Z.leb lo hi)%bool then None else
    match know_lookup segs k0 (ELit 0) a 8 false [] [] with
    | LHit e sc _ =>
        match sc, erange k0 e with
        | [], Some (elo, ehi) =>
            if (Z.leb lo elo && Z.leb ehi hi)%bool then
              let cs1 := node_droprange cs (ELit a) (ELit 8) in
              if fresh_ok nx0 cs1 then
                let v := nxt cs1 in
                Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1))
                                         (KRange (EVar v) lo hi :: KWord (SA (ELit 0) a) 8 (EVar v) :: kn cs1) (N.succ v)))
              else None
            else None
        | _, _ => None
        end
    | _ => None
    end.

  (* [comment removed for export] *)
  Definition node_neq_reg (cs : acs) (r : Z) : option acs :=
    if negb (Z.leb 0 r && Z.ltb r 32)%bool then None else
    let e := reg cs (Z.to_nat r) in
    match e with
    | ELit _ => Some cs                      (* [comment removed for export] *)
    | EAlu ALU_SLTU (EAlu ALU_XOR a b) (ELit c) =>
        if negb (Z.eqb c 1) then None else
        match erange (kn cs) a, erange (kn cs) b with
        | Some (al, ah), Some (bl, bh) =>
            if (Z.ltb ah bl || Z.ltb bh al)%bool then Some (add_kn cs [KRange e 0 0]) else None
        | _, _ => None
        end
    | _ => None
    end.

  Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
    match id, args with
    | 103%nat, [ELit a; ELit lo; ELit hi] => node_forget8 cs a lo hi
    | 104%nat, [ELit r] => node_neq_reg cs r
    | _, _ => None
    end.
End X.
End HSN.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.

Lemma node_forget8_sound : forall a lo hi, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => HSN.node_forget8 SEGS nx0 cs a lo hi).
Proof.
  intros a lo hi cs cs' E R FULL model T HC _ Hn Hk.
  unfold HSN.node_forget8 in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in Hn.
  apply andb_prop in Hc as [Hc Hlohi]. apply andb_prop in Hc as [Hc Hlo0]. apply andb_prop in Hc as [Hc Ha8]. apply andb_prop in Hc as [Hfl Ha0].
  apply Z.leb_le in Ha0. apply Z.ltb_lt in Ha8. unfold two64 in Ha8. apply Z.leb_le in Hlo0. apply Z.leb_le in Hlohi.
  destruct (know_lookup SEGS (kn cs) (ELit 0) a 8 false [] []) as [e sc hs|sc hs|] eqn:HL; try discriminate.
  destruct sc; [|discriminate].
  destruct (erange (kn cs) e) as [[elo ehi]|] eqn:Her; [|discriminate].
  destruct (Z.leb_spec lo elo); [|discriminate]. destruct (Z.leb_spec ehi hi); [|discriminate]. cbn [andb] in Hn.
  set (cs1 := node_droprange cs (ELit a) (ELit 8)) in Hn.
  destruct (fresh_ok nx0 cs1) eqn:Hf; [|discriminate].
  injection Hn as <-.
  pose proof HC as HKN0. apply co_know in HKN0.
  set (M := Mr A argH E cs model FULL) in *.
  pose proof (erange_sound SEGS E M (kn cs) e elo ehi HKN0 Her) as Hrg.
  destruct (flat_x_sound SEGS E M (kn cs) (ELit 0) a (ELit 8) HKN0 Hfl) as (Clo & Chi & _).
  assert (HCst : estart E (SA (ELit 0) a) = a).
  { unfold estart; cbn [a_base a_off edenot]. rewrite u_small by lia. lia. }
  rewrite HCst in Clo, Chi. cbn [edenot] in Chi. rewrite u_small in Chi by lia.
  destruct (lookup_piece SEGS E M (kn cs) (ELit 0) a 8 e hs HKN0 ltac:(lia) HL ltac:(unfold flat; rewrite HCst; cbn [edenot]; rewrite ?u_small by lia; lia))
    as (bs & Hrd & Hlen & Hbs).
  rewrite HCst in Hrd.
  pose proof (droprange_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model (ELit a) (ELit 8) HC) as HC1. fold cs1 in HC1.
  assert (Hpc1 : pc cs1 = pc cs) by (unfold cs1, node_droprange; destruct (split_lit (ELit a)); reflexivity).
  assert (Hnx : nxt cs1 = nxt cs) by (unfold cs1, node_droprange; destruct (split_lit (ELit a)); reflexivity).
  assert (HM1 : Mr A argH E cs1 model FULL = M) by (unfold cs1, node_droprange; destruct (split_lit (ELit a)); reflexivity).
  destruct (w_fresh_ok_parts nx0 cs1 Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  (* [comment removed for export] *)
  set (v := nxt cs1). set (E' := ext1 E v (edenot E e)).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (w_cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree nx0_ge7 FS0 E E' cs1 R FULL model Hag Hf HC1) as HC'.
  set (cs' := with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) (KRange (EVar v) lo hi :: KWord (SA (ELit 0) a) 8 (EVar v) :: kn cs1) (N.succ v))) in *.
  assert (Hpc' : pc cs' = pc cs) by (unfold cs'; cbn; exact Hpc1).
  rewrite <- Hpc'. apply (Hk E' R FULL model).
  - split; [eapply env_agree_le; [exact Hag | exact Fle] | rewrite <- Hnx; exact Hag].
  - assert (HMr : forall ss, Mr A argH E' (with_ss cs1 ss) model FULL = Mr A argH E' cs1 model FULL) by reflexivity.
    assert (HA : forall ss, allowA A E' (with_ss cs1 ss) = allowA A E' cs1) by reflexivity.
    assert (HM' : Mr A argH E' cs1 model FULL = M).
    { rewrite <- HM1. unfold Mr. rewrite (w_hid_agree A nx0 argH argH_agree v E E' cs1 model Hag Fle Fallow). reflexivity. }
    assert (Hv : edenot E' (EVar v) = edenot E e) by (cbn [edenot]; unfold E'; rewrite ext1_at; reflexivity).
    destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
      cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
      try assumption; try reflexivity.
    (* [comment removed for export] *)
    assert (Ev : ev E' (nxt cs1) = edenot E e) by (unfold E', v; rewrite ext1_at; reflexivity).
    constructor.
    { cbn [kentry_ok edenot]. fold v. rewrite ?Ev. unfold v. rewrite ?Ev. lia. }
    constructor; [|exact co_know0]. cbn [kentry_ok]. split; [lia|]. split.
    + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite !u_small by lia. lia.
    + unfold adenot. cbn [a_base a_off edenot]. fold v. rewrite ?Ev. unfold v. rewrite ?Ev. rewrite HM', Hbs. rewrite ?u_small by lia.
      first [exact Hrd | rewrite Z.add_0_l; exact Hrd | replace (0 + a) with a by lia; exact Hrd].
  - reflexivity.
Qed.

Lemma xor_seqz_disjoint : forall (x y : word) (al ah bl bh : Z),
  (al <= bv_unsigned x <= ah)%Z -> (bl <= bv_unsigned y <= bh)%Z -> (ah < bl \/ bh < al)%Z ->
  bv_unsigned (alu64 ALU_SLTU (alu64 ALU_XOR x y) (Z_to_bv 64 1)) = 0%Z.
Proof.
  intros x y al ah bl bh Hx Hy Hd.
  rewrite u_sltu64, u_xor64, u_small by lia.
  pose proof (bv_unsigned_in_range 64 x) as Rx. pose proof (bv_unsigned_in_range 64 y) as Ry. change (bv_modulus 64) with (2^64)%Z in Rx, Ry.
  assert (NE : bv_unsigned x <> bv_unsigned y) by lia.
  assert (NZ : Z.lxor (bv_unsigned x) (bv_unsigned y) <> 0%Z).
  { intros H0. apply Z.lxor_eq in H0. exact (NE H0). }
  assert (NN : (0 <= Z.lxor (bv_unsigned x) (bv_unsigned y))%Z) by (apply Z.lxor_nonneg; lia).
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned x) (bv_unsigned y)) 1); [lia|reflexivity].
Qed.

Lemma node_neq_reg_sound : forall r, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => HSN.node_neq_reg cs r).
Proof.
  intros r cs cs' E R FULL model T HC _ Hn Hk.
  unfold HSN.node_neq_reg in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in Hn.
  set (e := reg cs (Z.to_nat r)) in Hn.
  destruct e as [| |op a b| | | | |] eqn:He; try discriminate.
  { injection Hn as <-. apply (Hk E R FULL model); [split; apply env_agree_refl | exact HC | reflexivity]. }
  destruct op; try discriminate. destruct a as [| |op2 a1 b1| | | | |]; try discriminate. destruct op2; try discriminate.
  destruct b as [c| | | | | | |]; try discriminate.
  destruct (Z.eqb_spec c 1) as [Ec|]; [|discriminate]. cbn [negb] in Hn.
  destruct (erange (kn cs) a1) as [[al ah]|] eqn:Ha; [|discriminate].
  destruct (erange (kn cs) b1) as [[bl bh]|] eqn:Hb; [|discriminate].
  match type of Hn with (if ?d then _ else _) = _ => destruct d eqn:Hd; [|discriminate] end.
  injection Hn as <-.
  pose proof HC as HKN0. apply co_know in HKN0.
  set (M := Mr A argH E cs model FULL) in *.
  pose proof (erange_sound SEGS E M (kn cs) a1 al ah HKN0 Ha) as Ra.
  pose proof (erange_sound SEGS E M (kn cs) b1 bl bh HKN0 Hb) as Rb.
  assert (Hdz : (ah < bl \/ bh < al)%Z).
  { apply Bool.orb_prop in Hd. destruct Hd as [Hd|Hd]; apply Z.ltb_lt in Hd; lia. }
  assert (HK : kentry_ok SEGS E M (KRange (EAlu ALU_SLTU (EAlu ALU_XOR a1 b1) (ELit c)) 0 0)).
  { cbn [kentry_ok edenot]. subst c. rewrite (xor_seqz_disjoint _ _ al ah bl bh Ra Rb Hdz). lia. }
  assert (HC' : cs_ok SEGS A LIMIT SINV argH FS0 E (add_kn cs [KRange (EAlu ALU_SLTU (EAlu ALU_XOR a1 b1) (ELit c)) 0 0]) R FULL model).
  { unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [exact HK | exact HKN0]. }
  assert (Hpc' : pc (add_kn cs [KRange (EAlu ALU_SLTU (EAlu ALU_XOR a1 b1) (ELit c)) 0 0]) = pc cs) by reflexivity.
  rewrite <- Hpc'. apply (Hk E R FULL model).
  - split; apply env_agree_refl.
  - exact HC'.
  - reflexivity.
Qed.

Theorem hs_xn_sound : ext_stmt SEGS A nx0 LIMIT (HSN.xn SEGS nx0) SINV argH FS0.
Proof.
  intros id args. destruct id as [|id]; [intros cs cs' E R FULL model T _ _ H; discriminate H|].
  do 102 (destruct id as [|id]; [intros cs cs' E R FULL model T _ _ H; discriminate H|]).
  destruct id as [|id].
  { destruct args as [|[a| | | | | | | ] [|[lo| | | | | | | ] [|[hi| | | | | | | ] [|? ?]]]]; try (intros cs cs' E R FULL model T _ _ H; discriminate H).
    exact (node_forget8_sound a lo hi). }
  destruct id as [|id]; [|intros cs cs' E R FULL model T _ _ H; discriminate H].
  destruct args as [|[r| | | | | | | ] [|? ?]]; try (intros cs cs' E R FULL model T _ _ H; discriminate H).
  exact (node_neq_reg_sound r).
Qed.
End Sound.
