(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec SpecConsts LibWritev RefNodes RefExitBase Hoare Frame
  RefStdioDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA SymPlanSound SymPlanSoundH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition ref_stdio_write_stmt : Prop :=
  forall (fx : FPState) regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0xb2000 <= f)%Z -> (f + 232 <= 0xe4b88)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (0 <= wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->   (* [comment removed for export] *)
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 40)%Z ->   (* [comment removed for export] *)
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->   (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall regs' mem',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' ->
     realizes RSEGS (mkCfg (mkst regs' ret mem' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst regs (0x9ba34 : word) mem (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).

Section NX0.
Variable nx0 : nat.
Context {fx : PropExec.FPState}.
Hypothesis REF : ref_stdio_write_stmt.

(* [comment removed for export] *)

Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.

Lemma inr_spec : forall lo n x, inr lo n x = true <-> (lo <= bv_unsigned x < lo + n)%Z.
Proof.
  intros lo n x. unfold inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma inr_false : forall lo n x, inr lo n x = false <-> ~ (lo <= bv_unsigned x < lo + n)%Z.
Proof.
  intros lo n x. rewrite <- inr_spec. destruct (inr lo n x); split; congruence.
Qed.

(* [comment removed for export] *)
Lemma know_ok_havoc3 : forall E M M' k b1 o1 n1 b2 o2 n2 b3 o3 n3,
  know_ok RSEGS E M k ->
  (forall x : word,
     ~ (estart E (SA b1 o1) <= bv_unsigned x < estart E (SA b1 o1) + elenZ E n1)%Z ->
     ~ (estart E (SA b2 o2) <= bv_unsigned x < estart E (SA b2 o2) + elenZ E n2)%Z ->
     ~ (estart E (SA b3 o3) <= bv_unsigned x < estart E (SA b3 o3) + elenZ E n3)%Z ->
     M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_havoc (kn_havoc (kn_havoc k b1 o1 n1) b2 o2 n2) b3 o3 n3)
  /\ (forall ss, slots_ok E M ss ->
        slots_ok E M' (slots_keep k b3 o3 n3 (slots_keep k b2 o2 n2 (slots_keep k b1 o1 n1 ss)))).
Proof.
  intros E M M' k b1 o1 n1 b2 o2 n2 b3 o3 n3 HK Hout Hg.
  set (a1 := estart E (SA b1 o1)). set (l1 := elenZ E n1).
  set (a2 := estart E (SA b2 o2)). set (l2 := elenZ E n2).
  set (a3 := estart E (SA b3 o3)). set (l3 := elenZ E n3).
  set (M1 := fun x : word => if (inr a2 l2 x || inr a3 l3 x)%bool then M x else M' x).
  set (M2 := fun x : word => if inr a3 l3 x then M x else M' x).
  assert (O1 : forall x : word, (bv_unsigned x < a1 \/ a1 + l1 <= bv_unsigned x)%Z -> M1 x = M x).
  { intros x Hx. unfold M1. destruct (inr a2 l2 x) eqn:E2; [reflexivity|]. destruct (inr a3 l3 x) eqn:E3; [reflexivity|].
    cbn [orb]. apply inr_false in E2. apply inr_false in E3. apply Hout; [lia | exact E2 | exact E3]. }
  assert (G1 : mem_grows M M1).
  { intros x Hx. unfold M1. destruct (inr a2 l2 x || inr a3 l3 x)%bool; [exact Hx | exact (Hg x Hx)]. }
  assert (O2 : forall x : word, (bv_unsigned x < a2 \/ a2 + l2 <= bv_unsigned x)%Z -> M2 x = M1 x).
  { intros x Hx. unfold M1, M2. destruct (inr a3 l3 x) eqn:E3; [rewrite orb_true_r; reflexivity|].
    destruct (inr a2 l2 x) eqn:E2; [|reflexivity]. apply inr_spec in E2. lia. }
  assert (G2 : mem_grows M1 M2).
  { intros x Hx. unfold M1, M2 in *. destruct (inr a3 l3 x); [rewrite orb_true_r in Hx; exact Hx|].
    destruct (inr a2 l2 x); cbn [orb] in Hx; [exact (Hg x Hx) | exact Hx]. }
  assert (O3 : forall x : word, (bv_unsigned x < a3 \/ a3 + l3 <= bv_unsigned x)%Z -> M' x = M2 x).
  { intros x Hx. unfold M2. destruct (inr a3 l3 x) eqn:E3; [|reflexivity]. apply inr_spec in E3. lia. }
  assert (G3 : mem_grows M2 M').
  { intros x Hx. unfold M2 in Hx. destruct (inr a3 l3 x); [exact (Hg x Hx) | exact Hx]. }
  split.
  - eapply know_ok_havoc; [| exact O3 | exact G3].
    eapply know_ok_havoc; [| exact O2 | exact G2].
    eapply know_ok_havoc; [exact HK | exact O1 | exact G1].
  - intros ss HS.
    eapply (slots_keep_sound E M k); [exact HK | | exact O3].
    eapply (slots_keep_sound E M k); [exact HK | | exact O2].
    eapply (slots_keep_sound E M k); [exact HK | exact HS | exact O1].
Qed.

(* [comment removed for export] *)
Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | |lo hi| | | |]; cbn [kimg_cut1]; try (apply Forall_one; exact HKK).
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_one; exact HKK|].
  apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Himg).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
  - destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
Qed.

(* [comment removed for export] *)

Lemma kept_regs : forall (R R' : bvmap 5 word),
  (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
     getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr R' r = getr R r.
Proof.
  intros R R' Hk r Hr0 Hn.
  pose proof (kept_of_not_caller_saved r
    (map (fun k => Z_to_bv 5 (Z.of_nat k)) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat)
    ltac:(intros k Hin; apply (in_map (fun k : nat => Z_to_bv 5 (Z.of_nat k))); exact Hin) Hr0 Hn) as Hin.
  apply in_map_iff in Hin as (k & <- & Hin). apply Hk. exact Hin.
Qed.

Lemma u_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros E. cbn [edenot]. apply u64_lit. lia. Qed.

Lemma flat_abs0 : forall E off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z ->
  flat E (SA (ELit 0) off) n.
Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite u_lit0. lia. Qed.

Lemma adenot_abs0 : forall E off, adenot E (SA (ELit 0) off) = Z_to_bv 64 off.
Proof. intros E off. rewrite adenot_SA, u_lit0. f_equal. Qed.

(* [comment removed for export] *)

Theorem node_stdio_write_sound'_fx : forall cs cs' fd bs E R M model T,
  cs_ok E cs R M model -> pc cs = t_stdio_write P0 ->
  node_stdio_write RSEGS P0 nx0 cs = Some (fd, bs, cs') ->
  T [] ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_emit (Wz fd bs) T).
Proof.
  
  intros cs cs' fd bs E R M model T HC Hpc Hn HT HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold node_stdio_write in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 10) as [f|] eqn:H10; [|discriminate].
  destruct (reg_lit cs 12) as [l|] eqn:H12; [|discriminate].
  destruct (negb (Z.eqb f (d_stdout P0))) eqn:Hf; [discriminate|].
  apply negb_false_iff in Hf. apply Z.eqb_eq in Hf. change (d_stdout P0) with 0xb2d90%Z in Hf.
  change (d_canary_got P0) with 0xb1bb0%Z in Hn. change (d_canary P0) with 0xe4b88%Z in Hn.
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (f + 120) 4) as [fd'|] eqn:Hfd; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (f + 40) 8) as [wp|] eqn:Hwp; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (f + 56) 8) as [wb|] eqn:Hwb; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (f + 88)) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (f + 96)) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) 0xb1bb0 8) as [cg|] eqn:Hcg; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) 0xe4b88) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hss.
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-112))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  destruct (kread_bytes RSEGS (Z.to_nat (wp - wb)) (kn cs) (ELit 0) wb) as [pend|] eqn:Hpend; [|discriminate].
  destruct (kread_bytes RSEGS (Z.to_nat l) (kn cs) sb sk) as [extra|] eqn:Hextra; [|discriminate].
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  destruct (ehi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (k0 := kimg_cut (kimg_cut (kn cs) (f + 32) 16) (f + 56) 8) in Hn.
  set (k1 := kn_havoc k0 qb qk (ELit 112)) in Hn.
  set (k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 16)) in Hn.
  set (k3 := kn_havoc k2 (ELit 0) (f + 56) (ELit 8)) in Hn.
  set (k4 := KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
             :: KWord (SA (ELit 0) (f + 40)) 8 bufp :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3) in Hn.
  destruct (after_call nx0 cs ret (Some (ELit l)) k4) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some (?a, ?b, ?c) = Some (fd, bs, cs') =>
    assert (Efd : fd = a) by congruence; assert (Ebs : bs = b) by congruence; assert (Ecs : cs' = c) by congruence end.
  clear Hn. subst fd bs.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hds]. apply andb_prop in Hcond as [Hcond Hdw].
  apply andb_prop in Hcond as [Hcond Hfls]. apply andb_prop in Hcond as [Hcond Hsl64]. apply andb_prop in Hcond as [Hcond Hwp47].   (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hrw].
  apply andb_prop in Hcond as [Hcond Hcg8]. apply andb_prop in Hcond as [Hcond Hcg0].
  apply andb_prop in Hcond as [Hcond Hcan8]. apply andb_prop in Hcond as [Hcond Hf232]. apply andb_prop in Hcond as [Hcond Hf0].
  apply andb_prop in Hcond as [Hcond Hmax]. apply andb_prop in Hcond as [Hcond Hnp0].
  apply andb_prop in Hcond as [Hfd1 Hcgv].
  apply Z.eqb_eq in Hfd1. subst fd'. apply Z.eqb_eq in Hcgv.
  apply Z.leb_le in Hnp0. apply Z.leb_le in Hmax. apply Z.leb_le in Hf0. apply Z.leb_le in Hf232.
  apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'. apply Z.leb_le in Hsl64. apply Z.leb_le in Hwp47.
  clear Hcan8 Hcg0 Hcg8.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (reg_lit_sound E cs R M model 10 f HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound E cs R M model 12 l HC ltac:(lia) H12) as [R12 Hlr]. unfold two64 in Hlr.
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in R12 by (apply bv_eq; reflexivity).
  set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
  set (s := edenot E (reg cs 11)) in *.
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsplo2. fold sp in Hsplo2. fold su in Hsplo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphi2. fold sp in Hsphi2. fold su in Hsphi2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hshi) as Hshi2. fold s in Hshi2.
  pose proof (u64_range s) as Hsr. pose proof (u64_range sp) as Hspr. fold su in Hspr.
  (* [comment removed for export] *)
  assert (Hspm : edenot E spm = Z_to_bv 64 (su - 112)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
  destruct (rw_okb_sound E M (kn cs) qb qk 112 HKN Hrw ltac:(lia)) as (Wst & Wdef & Wimg & W0 & Wnw).
  assert (Hq : (bv_unsigned (edenot E qb) + qk = su - 112)%Z).
  { apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by lia. lia. }
  rewrite Hq in Wst, Wdef, Wimg.
  (* [comment removed for export] *)
  assert (FL8 : forall off, (0 <= off)%Z -> (off + 8 <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) 8).
  { intros off A B. apply flat_abs0; lia. }
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (f + 120) 4 1 HKN Hfd ltac:(lia) ltac:(apply flat_abs0; lia)) as [Rfd _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (f + 40) 8 wp HKN Hwp ltac:(lia) ltac:(apply FL8; lia)) as [Rwp Hwpr].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (f + 56) 8 wb HKN Hwb ltac:(lia) ltac:(apply FL8; lia)) as [Rwb Hwbr].
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (f + 88) bufp HKN Hbufp ltac:(apply FL8; lia)) as Rbufp.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (f + 96) bufsz HKN Hbufsz ltac:(apply FL8; lia)) as Rbufsz.
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) 0xb1bb0 8 cg HKN Hcg ltac:(lia) ltac:(apply FL8; lia)) as [Rcg _].
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) 0xe4b88 canv HKN Hcan ltac:(apply FL8; lia)) as Rcan.
  rewrite adenot_abs0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan. unfold two64 in Hwpr, Hwbr.
  (* [comment removed for export] *)
  destruct (kread_bytes_rdn E M (kn cs) (Z.to_nat (wp - wb)) (ELit 0) wb pend HKN Hpend
              ltac:(rewrite u_lit0; lia) ltac:(rewrite u_lit0; lia)) as [Rpend Lpend].
  rewrite u_lit0, Z.add_0_l in Rpend.
  pose proof (flat_b_sound E M (kn cs) sb sk (Z.max l 1) HKN Hfls) as Hfl. unfold flat, estart in Hfl. cbn [a_base a_off] in Hfl.
  destruct (kread_bytes_rdn E M (kn cs) (Z.to_nat l) sb sk extra HKN Hextra ltac:(lia) ltac:(lia)) as [Rextra Lextra].
  pose proof (split_lit_denot E (reg cs 11) sb sk Hss) as Hsd. fold s in Hsd.
  assert (Hsu : bv_unsigned s = (bv_unsigned (edenot E sb) + sk)%Z) by (rewrite Hsd, u64_lit by lia; reflexivity).
  rewrite <- Hsu, Z_to_bv_bv_unsigned in Rextra.
  (* [comment removed for export] *)
  assert (Dw : (wp <= su - 112 \/ su <= wb)%Z).
  { apply orb_prop in Hdw as [Hx|Hx]; apply (lin_ge0_sound RSEGS E M (kn cs)) in Hx; [|exact HKN| |exact HKN];
      cbn [xt_den edenot] in Hx; rewrite ?u64_lit in Hx by lia; rewrite ?Hspm in Hx; rewrite ?u64_lit in Hx by lia; fold sp su in Hx; lia. }
  assert (Ds : (bv_unsigned s + l <= su - 112 \/ su <= bv_unsigned s)%Z).
  { apply orb_prop in Hds as [Hx|Hx]; apply (lin_ge0_sound RSEGS E M (kn cs)) in Hx; [|exact HKN| |exact HKN];
      cbn [xt_den] in Hx; rewrite ?Hspm in Hx; rewrite ?u64_lit in Hx by lia; fold s sp su in Hx; lia. }
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_stdio_write P0)) with (0x9ba34%bv : word) by (apply bv_eq; reflexivity).
  rewrite Wz_map, map_app.
  eapply (REF fx R M model su f wb wp 1 s (Z_to_bv 64 l) (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            (map (fun z => Z_to_bv 8 z) pend) (map (fun z => Z_to_bv 8 z) extra) T).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst.
  - lia.
  - lia.
  - constructor; [exact Rwp | exact Rwb | exact Rfd | exact Rbufp | exact Rbufsz].
  - split; [rewrite Rcg, Hcgv; reflexivity | exact Rcan].
  - lia.
  - apply fd_lookup_std1. exact (co_fds _ _ _ _ _ HC).
  - exact (co_halt _ _ _ _ _ HC).
  - exact (co_lazy _ _ _ _ _ HC).
  - lia.
  - lia.
  - rewrite length_map, Lpend. rewrite Z2Nat.id by lia. reflexivity.
  - rewrite length_map, Lextra, u64_lit by lia. rewrite Z2Nat.id by lia. reflexivity.
  - rewrite !length_map, Lpend, Lextra, !Z2Nat.id by lia. pose proof rw_bytes_max_ge17. lia.
  - rewrite !length_map, Lpend, Lextra, !Z2Nat.id by lia. lia.
  - exact Dw.
  - rewrite u64_lit by lia. exact Ds.
  - rewrite u64_lit by lia. lia.
  - rewrite length_map, Lpend. exact Rpend.
  - rewrite length_map, Lextra. exact Rextra.
  - exact Hrok.
  - exact HT.
  - (* [comment removed for export] *)
    intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
    unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh' Hnx0]. apply Nat.leb_le in Hnx0.
    set (nx := s_next (c_ss cs)) in *.
    pose proof (ext_call_agree E nx R') as Hag.
    destruct (after_call_sound nx0 cs ret (Some (ELit l)) k4 csa E R R' M M' model
                (slots_keep (kn cs) (ELit 0) (f + 56) (ELit 8)
                   (slots_keep (kn cs) (ELit 0) (f + 32) (ELit 16)
                      (slots_keep (kn cs) qb qk (ELit 112) (c_slots cs)))) Hac HC) as [HC' Hpc'].
    + (* [comment removed for export] *)
      apply kept_regs. intros kk Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
          first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
        end.
    + (* [comment removed for export] *)
      replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10. cbn [edenot]. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK0 : know_ok RSEGS E M k0) by (subst k0; apply kimg_cut_sound, kimg_cut_sound, HKN).
      destruct (know_ok_havoc3 E M M' k0 qb qk (ELit 112) (ELit 0) (f + 32) (ELit 16) (ELit 0) (f + 56) (ELit 8) HK0) as [HK3 _].
      { intros x N1 N2 N3. apply Pagree.
        - unfold estart in N1. cbn [a_base a_off] in N1. rewrite Hq, elenZ_lit in N1 by lia. lia.
        - unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0, elenZ_lit in N2 by lia. lia.
        - unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0, elenZ_lit in N3 by lia. lia. }
      { exact Pgrows. }
      subst k4 k3 k2 k1.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply FL8; lia|]); rewrite adenot_abs0.
      * rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. exact Pwend.
      * exact Pwpos.
      * exact Pwbase.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      destruct (know_ok_havoc3 E M M' (kn cs) qb qk (ELit 112) (ELit 0) (f + 32) (ELit 16) (ELit 0) (f + 56) (ELit 8) HKN) as [_ HS3].
      { intros x N1 N2 N3. apply Pagree.
        - unfold estart in N1. cbn [a_base a_off] in N1. rewrite Hq, elenZ_lit in N1 by lia. lia.
        - unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0, elenZ_lit in N2 by lia. lia.
        - unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0, elenZ_lit in N3 by lia. lia. }
      { exact Pgrows. }
      apply HS3. exact HSL.
    + (* [comment removed for export] *)
      apply andb_prop in Hfresh' as [_ Hslv]. apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply slots_vars_lt_keep. exact Hslv.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      eapply lib_ok_frame; [|exact (co_lib _ _ _ _ _ HC)]. intros a Ha. unfold HULL_LO, HULL_HI in Ha; cbn in Ha.
      apply Pagree; rewrite u64_lit by lia; lia.
    + (* [comment removed for export] *)
      subst cs'. specialize (HK (ext_call E nx R') R' M' ltac:(eapply env_agree_le; [exact Hag | exact (max1_le_l _ _ Hnx0)]) HC').
      rewrite Hpc' in HK. unfold cfg_of in HK. exact HK.
Qed.

Theorem node_stdio_write_ok_fx : forall cs cs' fd bs E R M model T,
  cs_ok E cs R M model -> pc cs = t_stdio_write P0 ->
  node_stdio_write RSEGS P0 nx0 cs = Some (fd, bs, cs') ->
  T [] ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_emit (Wz fd bs) T).
Proof. exact node_stdio_write_sound'_fx. Qed.

End NX0.

(* [comment removed for export] *)
Theorem node_stdio_write_sound' : forall nx0, ref_stdio_write_stmt -> stdio_write_sound_stmt nx0.
Proof. intros nx0 REF fx. exact (node_stdio_write_sound'_fx nx0 REF). Qed.
Theorem node_stdio_write_ok : forall nx0, ref_stdio_write_stmt -> stdio_write_sound_stmt nx0.
Proof. intros nx0 REF fx. exact (node_stdio_write_ok_fx nx0 REF). Qed.
