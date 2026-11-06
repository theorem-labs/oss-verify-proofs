(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec Hoare Frame
  RefMemcpyLib UbPrintfBufBase UbPrintfBuf.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan UbSymSlots
  UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH UbSymPlanSoundSW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rng_lo (E : env) (r : expr * Z * expr) : Z := match r with (b, o, n) => estart E (SA b o) end.
Definition rng_len (E : env) (r : expr * Z * expr) : Z := match r with (b, o, n) => elenZ E n end.

Fixpoint inrs (E : env) (rs : list (expr * Z * expr)) (x : word) : bool :=
  match rs with
  | [] => false
  | r :: rest => inr (rng_lo E r) (rng_len E r) x || inrs E rest x
  end.

(* [comment removed for export] *)
Fixpoint slots_keeps (k : list kentry) (rs : list (expr * Z * expr)) (ss : list sslot) : list sslot :=
  match rs with
  | [] => ss
  | (b, o, n) :: rest => slots_keeps k rest (slots_keep k b o n ss)
  end.

(* [comment removed for export] *)
Lemma know_ok_memeq : forall E M M' k,
  (forall x : word, M' x = M x) -> know_ok RSEGS E M k -> know_ok RSEGS E M' k.
Proof.
  intros E M M' k EQ HK. unfold know_ok in *. apply Forall_forall. intros K HinK.
  pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
  eapply (kentry_keep_sem E M M' K (match kfoot E K with Some (s, l) => s + l | None => 0 end) 0);
    [exact HKK | unfold kfoot_apart; destruct (kfoot E K) as [[s l]|]; [lia | exact I] | intros x _; apply EQ].
Qed.

Lemma slots_ok_memeq : forall E M M' ss,
  (forall x : word, M' x = M x) -> slots_ok E M ss -> slots_ok E M' ss.
Proof.
  intros E M M' ss EQ HS. unfold slots_ok in *. apply Forall_forall. intros s Hin.
  eapply slot_ok_agree; [exact (proj1 (Forall_forall _ _) HS s Hin) | intros x _ _; apply EQ].
Qed.

(* [comment removed for export] *)
Lemma havocs_frame : forall E rs M0 k0 M M',
  know_ok RSEGS E M0 k0 ->
  (forall x : word, inrs E rs x = false -> M' x = M x) ->
  mem_grows M M' ->
  (forall k, know_ok RSEGS E M k -> know_ok RSEGS E M' (kn_havocs k rs))
  /\ (forall ss, slots_ok E M ss -> slots_ok E M' (slots_keeps k0 rs ss)).
Proof.
  intros E rs M0 k0. induction rs as [|[[b o] n] rest IH]; intros M M' HK0 Hout Hg.
  - assert (EQ : forall x, M' x = M x) by (intros x; apply Hout; reflexivity).
    split; [intros k HK; cbn [kn_havocs]; eapply know_ok_memeq; eassumption
          | intros ss HS; cbn [slots_keeps]; eapply slots_ok_memeq; eassumption].
  - set (a := estart E (SA b o)). set (l := elenZ E n).
    set (M1 := fun x : word => if inrs E rest x then M x else M' x).
    assert (O1 : forall x : word, (bv_unsigned x < a \/ a + l <= bv_unsigned x)%Z -> M1 x = M x).
    { intros x Hx. unfold M1. destruct (inrs E rest x) eqn:Er; [reflexivity|].
      apply Hout. cbn [inrs]. rewrite Er, orb_false_r. apply inr_false. unfold rng_lo, rng_len. fold a l. lia. }
    assert (G1 : mem_grows M M1).
    { intros x Hx. unfold M1. destruct (inrs E rest x); [exact Hx | exact (Hg x Hx)]. }
    assert (O2 : forall x : word, inrs E rest x = false -> M' x = M1 x).
    { intros x Hx. unfold M1. rewrite Hx. reflexivity. }
    assert (G2 : mem_grows M1 M').
    { intros x Hx. unfold M1 in Hx. destruct (inrs E rest x); [exact (Hg x Hx) | exact Hx]. }
    destruct (IH M1 M' HK0 O2 G2) as [IHk IHs].
    split.
    + intros k HK. cbn [kn_havocs]. apply IHk. eapply know_ok_havoc; [exact HK | exact O1 | exact G1].
    + intros ss HS. cbn [slots_keeps]. apply IHs. eapply (slots_keep_sound E M0 k0); [exact HK0 | exact HS | exact O1].
Qed.

(* [comment removed for export] *)
Lemma outside_of_inrs : forall E rs (regs : list (word * Z)) x,
  Forall2 (fun r g => bv_unsigned (fst g) = rng_lo E r /\ snd g = rng_len E r /\ 0 <= rng_lo E r /\ rng_lo E r + rng_len E r <= 2 ^ 64) rs regs ->
  inrs E rs x = false -> outside x regs.
Proof.
  intros E rs regs x HF. induction HF as [|r [gb gn] rs' regs' (H1 & H2 & H3 & H4) HF IH]; intros Hin; cbn [outside]; [exact I|].
  cbn [inrs] in Hin. apply Bool.orb_false_iff in Hin as [Hr Hrest]. cbn [fst snd] in H1, H2.
  split; [| apply IH; exact Hrest].
  apply inr_false in Hr. unfold in_rng. subst gn. rewrite H1. lia.
Qed.

(* [comment removed for export] *)

Lemma w2b2_0a30 : forall E, word_to_le_bytes 2 (edenot E (ELit 0x0a30)) = [Z_to_bv 8 0x30; Z_to_bv 8 0x0a].
Proof.
  intros E. cbn [edenot]. unfold word_to_le_bytes. rewrite u64_lit by lia. cbn [Z_to_le_bytes].
  f_equal; apply bv_eq; reflexivity.
Qed.

Lemma rdn_split2 : forall M (a : Z) b0 b1,
  0 <= a -> a + 2 <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) 2 = Some [b0; b1] ->
  rdn RSEGS M (Z_to_bv 64 a) 1 = Some [b0] /\ rdn RSEGS M (Z_to_bv 64 (a + 1)) 1 = Some [b1].
Proof.
  intros M a b0 b1 Ha Ha2 H. cbn [rdn] in *.
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [x|]; [|discriminate].
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1) : word) in H.
  2:{ apply bv_eq. rewrite (u_add1 (Z_to_bv 64 a)) by (rewrite u64_lit by lia; lia). rewrite !u64_lit by lia. reflexivity. }
  destruct (match M (Z_to_bv 64 (a + 1)) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 (a + 1)) end) as [y|]; [|discriminate].
  injection H as <- <-. split; reflexivity.
Qed.

Section NX0.
Variable nx0 : nat.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)

Theorem call_printf_sound'_fx : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_printf U0 -> call_printf RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  
  intros cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_printf in Hn.
  change (d_stdout U0) with 0xb3488%Z in Hn. change (d_stdout_buf U0) with 0xe5808%Z in Hn.
  change (d_canary U0) with 0xe5288%Z in Hn. change (t_printf_ret U0) with 0x329e0%Z in Hn.
  change (- PF_WIN)%Z with (-1056)%Z in Hn. unfold PF_WIN in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [[|p11|p11]|] eqn:H11; try discriminate.
  destruct (negb (Z.eqb ret 0x329e0)) eqn:Hreq; [discriminate|].
  apply negb_false_iff in Hreq. apply Z.eqb_eq in Hreq. subst ret.
  destruct (kreadZ RSEGS (kn cs) (ELit 0) 0xb3488 4) as [flags|] eqn:Hflags; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb3488 + 32) 8) as [wend|] eqn:Hwend; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb3488 + 40) 8) as [w|] eqn:Hw; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb3488 + 96) 8) as [bsz|] eqn:Hbsz; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb3488 + 140) 4) as [lock|] eqn:Hlock; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb3488 + 144) 4) as [lbf|] eqn:Hlbf; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) 0xe5288) as [canv|] eqn:Hcan; [|discriminate].
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-1056))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (k0 := kimg_cut (kimg_cut (kimg_cut (kn cs) 0xb3488 4) (0xb3488 + 40) 8) w 2) in Hn.
  set (k4 := kn_havoc (kn_havoc (kn_havoc (kn_havoc k0 qb qk (ELit 1056)) (ELit 0) 0xb3488 (ELit 4))
                        (ELit 0) (0xb3488 + 40) (ELit 8)) (ELit 0) w (ELit 2)) in Hn.
  set (k5 := KWord (SA (ELit 0) 0xb3488) 4 (ELit 5)
             :: KWord (SA (ELit 0) (0xb3488 + 40)) 8 (ELit (w + 2))
             :: KWord (SA (ELit 0) w) 2 (ELit 0x0a30) :: k4) in Hn.
  destruct (after_call nx0 cs 0x329e0 None k5) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some ?c = Some cs' => assert (Ecs : cs' = c) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hrw]. apply andb_prop in Hcond as [Hcond Heal]. apply andb_prop in Hcond as [Hcond Himg].
  apply andb_prop in Hcond as [Hcond Hlbf']. apply andb_prop in Hcond as [Hcond Hlock']. apply andb_prop in Hcond as [Hcond Hbsz'].
  apply andb_prop in Hcond as [Hcond Hwhi]. apply andb_prop in Hcond as [Hcond Hwlo]. apply andb_prop in Hcond as [Hflags' Hwend'].
  apply Z.eqb_eq in Hflags'. apply Z.eqb_eq in Hwend'. apply Z.leb_le in Hwlo. apply Z.leb_le in Hwhi. apply Z.eqb_eq in Hbsz'.
  rewrite ITOP_eq in Hsplo'. rewrite IRW_eq in Himg.
  apply Z.eqb_eq in Hlock'. apply Z.eqb_eq in Hlbf'. apply Z.leb_le in Heal. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  subst flags wend bsz lock lbf.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model 0x329e0 HC Hret) as (R1 & Hrok & _).
  destruct (reg_lit_sound E cs R M model 11 0 HC ltac:(lia) H11) as [R11 _].
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
  set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsplo2. fold sp in Hsplo2. fold su in Hsplo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphi2. fold sp in Hsphi2. fold su in Hsphi2.
  pose proof (u64_range sp) as Hspr. fold su in Hspr.
  (* [comment removed for export] *)
  assert (Hspm : edenot E spm = Z_to_bv 64 (su - 1056)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
  destruct (rw_okb_sound E M (kn cs) qb qk 1056 HKN Hrw ltac:(lia)) as (Wst & Wdef & Wimg & W0 & Wnw).
  assert (Hq : (bv_unsigned (edenot E qb) + qk = su - 1056)%Z).
  { apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by lia. lia. }
  rewrite Hq in Wst, Wdef, Wimg.
  (* [comment removed for export] *)
  destruct (ealign_sound RSEGS E M (kn cs) (reg cs 2) HKN) as [Heal0 Hdiv]. fold sp in Hdiv. fold su in Hdiv.
  assert (Hsu16 : su mod 16 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) (reg cs 2) - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C D. apply flat_abs0; lia. }
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) 0xb3488 4 5 HKN Hflags ltac:(lia) ltac:(apply FL; lia)) as [Rflags _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb3488 + 32) 8 _ HKN Hwend ltac:(lia) ltac:(apply FL; lia)) as [Rwend _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb3488 + 40) 8 w HKN Hw ltac:(lia) ltac:(apply FL; lia)) as [Rw Hwr].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb3488 + 96) 8 _ HKN Hbsz ltac:(lia) ltac:(apply FL; lia)) as [Rbsz _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb3488 + 140) 4 _ HKN Hlock ltac:(lia) ltac:(apply FL; lia)) as [Rlock _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb3488 + 144) 4 _ HKN Hlbf ltac:(lia) ltac:(apply FL; lia)) as [Rlbf _].
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) 0xe5288 canv HKN Hcan ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_abs0 in Rflags, Rwend, Rw, Rbsz, Rlock, Rlbf, Rcan.
  (* [comment removed for export] *)
  assert (IMG : forall i, 0x10000 <= i < 0xb3000 -> M (Z_to_bv 64 i) = None).
  { unfold kimg_covers in Himg. apply existsb_exists in Himg as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [Hil Hih].
    apply Z.leb_le in Hil. apply Z.leb_le in Hih.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & Hnone).
    intros i Hi. apply Hnone. lia. }
  (* [comment removed for export] *)
  assert (PH : pfH M sp w (bv_unsigned (edenot E canv))).
  { constructor.
    - exact Hsu16.
    - lia.
    - lia.
    - unfold SymRun.stk_ok, PF_FR. intros a n Ha Hn.
      eapply (store_ok_sub RSEGS M (Z_to_bv 64 (su - 1056)) a (Z.to_nat 1056) n);
        rewrite ?u64_lit by lia; rewrite ?Z2Nat.id by lia; try lia. exact Wst.
    - exact IMG.
    - exact Rflags.
    - exact Rwend.
    - exact Rw.
    - lia.
    - exact Rbsz.
    - exact Rlock.
    - exact Rlbf.
    - rewrite Z_to_bv_bv_unsigned. exact Rcan.
    - apply u64_range. }
  destruct (printf0_buffered R M (seg_rom RSEGS) sp w (bv_unsigned (edenot E canv)) PH R1 ltac:(exact R2) R11)
    as (R' & M' & Hms & Hkeeps & Hframe & Bw & Bwpos & Bflags).
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. change (t_printf U0) with 0x32a8c%Z.
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh' Hnx0]. apply Nat.leb_le in Hnx0.
  set (nx := s_next (c_ss cs)) in *.
  pose proof (ext_call_agree E nx R') as Hag.
  destruct Hframe as [Hout Hgrows].
  set (rs := [(qb, qk, ELit 1056); (ELit 0, 0xb3488%Z, ELit 4); (ELit 0, (0xb3488 + 40)%Z, ELit 8); (ELit 0, w, ELit 2)]).
  assert (HOUT : forall x : word, inrs E rs x = false -> M' x = M x).
  { intros x Hx. apply Hout. eapply (outside_of_inrs E rs); [|exact Hx]. subst rs.
    repeat apply Forall2_cons; try apply Forall2_nil; unfold rng_lo, rng_len, estart; cbn [fst snd a_base a_off edenot];
      rewrite ?Hq; unfold elenZ; cbn [edenot]; rewrite !u64_lit by lia; lia. }
  destruct (havocs_frame E rs M (kn cs) M M' HKN HOUT Hgrows) as [HKV HSV].
  destruct (after_call_sound nx0 cs 0x329e0 None k5 csa E R R' M M' model
              (slots_keep (kn cs) (ELit 0) w (ELit 2)
                 (slots_keep (kn cs) (ELit 0) (0xb3488 + 40) (ELit 8)
                    (slots_keep (kn cs) (ELit 0) 0xb3488 (ELit 4)
                       (slots_keep (kn cs) qb qk (ELit 1056) (c_slots cs))))) Hac HC) as [HC' Hpc'].
  - (* [comment removed for export] *)
    apply kept_regs. intros kk Hin.
    assert (KEPT : forall r : bv 5, In r RefMemcpyLib.callee_saved -> getr R' r = getr R r) by exact Hkeeps.
    cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      (apply KEPT; unfold RefMemcpyLib.callee_saved; cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
       repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end).
  - exact I.
  - (* [comment removed for export] *)
    assert (HK0 : know_ok RSEGS E M k0) by (subst k0; apply kimg_cut_sound, kimg_cut_sound, kimg_cut_sound, HKN).
    pose proof (HKV k0 HK0) as HK4. change (kn_havocs k0 rs) with k4 in HK4.
    subst k5.
    pose proof (rdn_split2 M' w _ _ ltac:(lia) ltac:(lia) Bw) as [B0 B1].
    repeat apply Forall_cons; [ | | | exact HK4]; cbn [kentry_ok]; (split; [lia|]); (split; [apply FL; lia|]); rewrite adenot_abs0.
    + exact Bflags.
    + cbn [edenot]. exact Bwpos.
    + rewrite w2b2_0a30. exact Bw.
  - (* [comment removed for export] *)
    pose proof (HSV (c_slots cs) HSL) as HS4. exact HS4.
  - (* [comment removed for export] *)
    apply andb_prop in Hfresh' as [_ Hslv]. apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply slots_vars_lt_keep. exact Hslv.
  - (* [comment removed for export] *)
    eapply lib_ok_frame; [|exact (co_lib _ _ _ _ _ HC)]. intros a Ha. unfold HULL_LO, HULL_HI in Ha; cbn in Ha.
    apply Hout. cbn [outside]. unfold in_rng. rewrite !u64_lit by lia. repeat split; try exact I; lia.
  - (* [comment removed for export] *)
    subst cs'. specialize (HK (ext_call E nx R') R' M' ltac:(eapply env_agree_le; [exact Hag | exact (max1_le_l _ _ Hnx0)]) HC').
    rewrite Hpc' in HK. unfold cfg_of in HK. exact HK.
Qed.

Theorem call_printf_ok_fx : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_printf U0 -> call_printf RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof. exact call_printf_sound'_fx. Qed.

End NX0.

(* [comment removed for export] *)
Theorem call_printf_sound' : forall nx0, printf_sound_stmt nx0.
Proof. intros nx0  fx. exact (call_printf_sound'_fx nx0 ). Qed.
Theorem call_printf_ok : forall nx0, printf_sound_stmt nx0.
Proof. intros nx0  fx. exact (call_printf_ok_fx nx0 ). Qed.
