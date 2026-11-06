(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare AgentLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesRP AsanWordLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cell8 (SEGS : list Segment) (m : word -> option byte) (a v : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition img_cell (SEGS : list Segment) (a v : Z) : Prop :=
  forall m, (forall i, a <= i < a + 8 -> m (Z_to_bv 64 i) = None) -> cell8 SEGS m a v.
Record rp_img (SEGS : list Segment) (T : RPN.rptab) : Prop := {
  ri_gsb : img_cell SEGS (RPN.rp_gsb T) (RPN.rp_csb T);
  ri_gm1 : img_cell SEGS (RPN.rp_gm1 T) (RPN.rp_cm1 T);
  ri_gm2 : img_cell SEGS (RPN.rp_gm2 T) (RPN.rp_cm2 T);
  ri_ghi : img_cell SEGS (RPN.rp_ghi T) (RPN.rp_chi T);
  ri_cm1 : img_cell SEGS (RPN.rp_cm1 T) 0;
  ri_cm2 : img_cell SEGS (RPN.rp_cm2 T) 0
}.

(* [comment removed for export] *)
Definition rp_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (beg n usp : Z) (regs : bvmap 5 word) (ra : word),
    16 <= n <= 2 ^ 40 -> 0 <= beg ->
    (beg + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= beg /\ beg + n <= RPN.kHighEnd)) ->
    80 <= usp < 2 ^ 64 ->
    RPN.SB + (beg + n - 1) / 8 < usp - 72 ->
    (forall g, beg / 8 <= g <= (beg + n - 1) / 8 -> mem (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)) ->
    (forall a, usp - 72 <= a < usp -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true) ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    cell8 SEGS mem (RPN.rp_gm1 T) (RPN.rp_cm1 T) -> cell8 SEGS mem (RPN.rp_cm1 T) 0 ->
    cell8 SEGS mem (RPN.rp_gm2 T) (RPN.rp_cm2 T) -> cell8 SEGS mem (RPN.rp_cm2 T) 0 ->
    cell8 SEGS mem (RPN.rp_ghi T) (RPN.rp_chi T) -> cell8 SEGS mem (RPN.rp_chi T) RPN.kHighEnd ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = Z_to_bv 64 usp ->
    getr regs 10%bv = Z_to_bv 64 beg -> getr regs 11%bv = Z_to_bv 64 n ->
    exists regs' mem',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.rp_entry T)) mem (seg_rom SEGS)) (mkst regs' ra mem' (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 0
      /\ (forall x : word, bv_unsigned x < usp - 72 \/ usp <= bv_unsigned x -> mem' x = mem x)
      /\ mem_grows mem mem'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_img : forall SEGS n m (a : Z),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> m (Z_to_bv 64 i) = None) ->
  rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros SEGS n. induction n as [|n IH]; intros m a Ha Hn Hm; [reflexivity|].
  cbn [rdn]. rewrite (Hm a) by lia.
  rewrite zbv_add1. rewrite (IH m (a + 1)); [reflexivity | lia | lia |].
  intros i Hi. apply Hm. lia.
Qed.

(* [comment removed for export] *)
Lemma map_unsigned_inj : forall (x y : list byte), map bv_unsigned x = map bv_unsigned y -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hab Hxy. f_equal; [apply bv_eq; exact Hab | apply IH; exact Hxy].
Qed.
Lemma obytes_eq_of_unsigned : forall (x y : option (list byte)),
  option_map (map bv_unsigned) x = option_map (map bv_unsigned) y -> x = y.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate; [|reflexivity].
  injection H as H. f_equal. apply map_unsigned_inj. exact H.
Qed.
Ltac img_cell_vm :=
  intros m Hm; unfold cell8; rewrite (rdn_img _ 8 m) by (first [lia | intros i Hi; apply Hm; lia]);
  apply obytes_eq_of_unsigned; vm_compute; reflexivity.







(* [comment removed for export] *)
Definition rc_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (buf res : Z) (regs : bvmap 5 word),
    1 <= res <= 64 -> 0 <= buf -> buf + 64 < 2 ^ 64 ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    (forall j, 0 <= j < 16 -> mem (Z_to_bv 64 ((RPN.SB + buf / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)) ->
    getr regs 9%bv = Z_to_bv 64 buf -> getr regs 10%bv = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.rc_entry T)) mem rom) (mkst regs' (Z_to_bv 64 (RPN.rc_exit T)) mem rom)
      /\ getr regs' 11%bv = Z_to_bv 64 (RPN.SB + buf / 8)
      /\ getr regs' 12%bv = Z_to_bv 64 (RPN.SB + (buf + res - 1) / 8)
      /\ getr regs' 13%bv = Z_to_bv 64 (buf + res - 1)
      /\ getr regs' 14%bv = Z_to_bv 64 0 /\ getr regs' 15%bv = Z_to_bv 64 0
      /\ getr regs' 20%bv = v_addi (v_addi (getr regs 8%bv) (-2048)) (-72)
      /\ (forall r, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 20%bv -> getr regs' r = getr regs r).



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.
Variable T : RPN.rptab.
Hypothesis IMG : rp_img SEGS T.
Hypothesis SPEC : rp_spec SEGS T.
Hypothesis RSPEC : rc_spec SEGS T.

#[using="Type"] Lemma u_spw_sub72 : forall (spw : word), 72 <= bv_unsigned spw ->
  bv_unsigned (Sem.alu64 ALU_ADD spw (Z_to_bv 64 (-72))) = bv_unsigned spw - 72.
Proof.
  intros spw Hs. pose proof (u64_range spw). rewrite alu_add. unfold v_add.
  rewrite (u_lit64 (-72)). unfold two64.
  change ((-72) mod 2 ^ 64) with (2 ^ 64 - 72).
  replace (bv_unsigned spw + (2 ^ 64 - 72)) with ((bv_unsigned spw - 72) + 1 * 2 ^ 64) by lia.
  rewrite u_lit64. unfold two64. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma srl3_div8 : forall (x y : word), bv_unsigned y mod 64 = 3 ->
  Sem.alu64 ALU_SRL x y = Z_to_bv 64 (bv_unsigned x / 8).
Proof.
  intros x y Hy. rewrite alu_srl. unfold v_srl. rewrite Hy. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

#[local] Notation M_of E cs model FULL := (Mr A argH E cs model FULL).

(* [comment removed for export] *)
#[using="Type"] Lemma lit_cell_sound : forall E M k cell v,
  know_ok SEGS E M k -> 0 <= cell -> RPN.lit_cell SEGS k cell v = true -> cell8 SEGS M cell v.
Proof.
  intros E M k cell v HK Hc H. unfold RPN.lit_cell in H. apply andb_prop in H as [Hfl H].
  destruct (know_lookup SEGS k (ELit 0) cell 8 false [] []) as [e sc hs|sc hs|] eqn:HL; try discriminate.
  destruct sc; [|discriminate].
  destruct (erange k e) as [[lo hi]|] eqn:Her; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst lo hi.
  pose proof (erange_sound SEGS E M k e v v HK Her) as Hv.
  destruct (flat_x_sound SEGS E M k (ELit 0) cell (ELit 8) HK Hfl) as (Clo & Chi & _).
  assert (HCst : estart E (SA (ELit 0) cell) = cell).
  { unfold estart; cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. }
  destruct (lookup_piece SEGS E M k (ELit 0) cell 8 e hs HK ltac:(lia) HL ltac:(unfold flat; rewrite HCst; rewrite HCst in Chi; cbn [edenot] in Chi; rewrite u64_lit in Chi by lia; lia))
    as (bs & Hrd & Hlen & Hbs).
  rewrite HCst in Hrd. unfold cell8. rewrite Hrd, <- Hbs. do 2 f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E e)). f_equal. lia.
Qed.

#[using="Type"] Lemma img8_sound : forall E M k a v,
  know_ok SEGS E M k -> RPN.img8 k a = true -> img_cell SEGS a v -> cell8 SEGS M a v.
Proof.
  intros E M k a v HK H Himg. apply Himg. intros i Hi. exact (img_cov_sound SEGS E M k a (a + 8) HK H i Hi).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[using="SEGS_wx SEGS_in_hull HULL_ok argH_high argH_agree SINV_frame SINV_agree nx0_ge7 IMG SPEC"] Theorem node_rpoison_int_sound :
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (RPN.node_rpoison_int SEGS nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  rewrite RPN.node_rpoison_int_eq in Hn. unfold RPN.node_rpoison_int_ref in Hn.   (* [comment removed for export] *)
  destruct (Z.eqb (pc cs) (RPN.rp_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (eaddz (reg cs 2) (-72))) as [qb qk] eqn:Hsq.
  destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsb.
  destruct (split_lit (eadd (ELit (RPN.SB + bk / 8)) (mkSrl (kn cs) bb 3))) as [hb hk] eqn:Hsh.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Lhi]. apply andb_prop in Hcond as [Hcond Lsb].
  apply andb_prop in Hcond as [Hcond Icm2]. apply andb_prop in Hcond as [Hcond Icm1].
  apply andb_prop in Hcond as [Hcond Ighi]. apply andb_prop in Hcond as [Hcond Igm2].
  apply andb_prop in Hcond as [Hcond Igm1]. apply andb_prop in Hcond as [Hcond Igsb].
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hflh].
  apply andb_prop in Hcond as [Hcond Hflq]. apply andb_prop in Hcond as [Hcond Hwr].
  apply andb_prop in Hcond as [Hcond B8]. apply andb_prop in Hcond as [Hcond B7]. apply andb_prop in Hcond as [Hcond B6]. apply andb_prop in Hcond as [Hcond B5].
  apply andb_prop in Hcond as [Hcond B4]. apply andb_prop in Hcond as [Hcond B3]. apply andb_prop in Hcond as [Hcond B2]. apply andb_prop in Hcond as [Hcond B1].
  apply andb_prop in Hcond as [Hcond P8]. apply andb_prop in Hcond as [Hcond P7]. apply andb_prop in Hcond as [Hcond P6]. apply andb_prop in Hcond as [Hcond P5].
  apply andb_prop in Hcond as [Hcond P4]. apply andb_prop in Hcond as [Hcond P3]. apply andb_prop in Hcond as [Hcond P2]. apply andb_prop in Hcond as [Hcond P1].
  apply andb_prop in Hcond as [Hcond Hdisj]. apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hflb]. apply andb_prop in Hcond as [Hcond Hal]. apply andb_prop in Hcond as [Hcond Hrng].
  apply andb_prop in Hcond as [Hn16 Hn40].
  apply Z.leb_le in Hn16. apply Z.leb_le in Hn40. apply Z.leb_le in Hal. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'. apply Z.ltb_lt in Hdisj.
  apply Z.leb_le in P1. apply Z.leb_le in P2. apply Z.leb_le in P3. apply Z.leb_le in P4. apply Z.leb_le in P5. apply Z.leb_le in P6. apply Z.leb_le in P7. apply Z.leb_le in P8.
  apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply Z.leb_le in B5. apply Z.leb_le in B6. apply Z.leb_le in B7. apply Z.leb_le in B8.
  unfold two64 in Hsphi'.
  (* [comment removed for export] *)
  destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Hblo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (begw := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *. set (nw := edenot E (reg cs 11)) in *.
  set (n := bv_unsigned nw) in *. set (usp := bv_unsigned spw) in *. set (beg := bv_unsigned begw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range begw) as Hbr. fold beg in Hbr.
  pose proof (u64_range spw) as Hsr. fold usp in Hsr.
  assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HspW : Z_to_bv 64 usp = spw) by (apply Z_to_bv_bv_unsigned).
  assert (HbgW : Z_to_bv 64 beg = begw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot in Hq. cbn [edenot] in Hq. fold spw in Hq.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 72 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = usp - 72).
  { apply (f_equal bv_unsigned) in Hq. rewrite (u_spw_sub72 spw) in Hq by lia. fold usp in Hq.
    rewrite u_lit64 in Hq. unfold two64 in Hq. rewrite (Z.mod_small Q) in Hq by lia. lia. }
  assert (Hstk : forall a, usp - 72 <= a < usp -> store_ok SEGS M (Z_to_bv 64 a) 1 = true).
  { intros a Ha. apply store_ok_of_all; [cbn; rewrite u64_lit by lia; lia|].
    intros x Hx. eapply (store_ok_all SEGS M 72 (Z_to_bv 64 Q)); [rewrite u64_lit by lia; cbn; lia | exact Qst |].
    rewrite u64_lit in Hx |- * by lia. cbn in Hx |- *. lia. }
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E (reg cs 10) bb bk Hsb) as Hbeg. fold begw in Hbeg.
  destruct (flat_x_sound SEGS E M (kn cs) bb bk (ELit 1) HKN Hflb) as (Blo & Bhi & _).
  set (bbu := bv_unsigned (edenot E bb)) in *.
  replace (bv_unsigned (edenot E (ELit 1))) with 1 in Bhi by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (HuB : beg = bbu + bk).
  { unfold beg. rewrite Hbeg. unfold estart in Blo, Bhi. cbn [a_base a_off] in Blo, Bhi. fold bbu in Blo, Bhi. apply u64_lit. lia. }
  destruct (ealign_sound SEGS E M (kn cs) bb HKN) as [Hea1 Hea2]. fold bbu in Hea2.
  assert (Hal8 : exists q, bbu = 8 * q).
  { destruct Hea2 as [q Hq8]. exists (q * 2 ^ (ealign (kn cs) bb - 3)). rewrite Hq8.
    replace (ealign (kn cs) bb) with ((ealign (kn cs) bb - 3) + 3) at 1 by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia. }
  destruct Hal8 as [q Hq8].
  assert (Hdiv1 : beg / 8 = q + bk / 8).
  { rewrite HuB, Hq8. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
  assert (Hdiv2 : (beg + n - 1) / 8 = q + (bk + n - 1) / 8).
  { rewrite HuB, Hq8. replace (8 * q + bk + n - 1) with (q * 8 + (bk + n - 1)) by lia. rewrite Z.div_add_l by lia. reflexivity. }
  assert (Hdiv3 : (bk + n - 1) / 8 <= (bk + nhi - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (Hdiv4 : bbu / 8 = q) by (rewrite Hq8, Z.mul_comm; apply Z.div_mul; lia).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ hb hk Hsh) as Hsa.
  unfold eadd in Hsa. rewrite mkAlu_denot in Hsa.
  rewrite (mkSrl_denot SEGS E M (kn cs) bb 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)) in Hsa.
  rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity). fold bbu in Hsa.
  cbn [edenot] in Hsa. rewrite alu_add in Hsa. unfold v_add in Hsa.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) hb hk (ELit ((bk + nhi - 1) / 8 - bk / 8 + 1)) HKN HKN Hkz) as (Zb & Hlo' & Hhi').
  set (H := estart E (SA hb hk)) in *.
  change (bv_unsigned (edenot E hb) + hk) with H in Hsa.
  set (L := (bk + nhi - 1) / 8 - bk / 8 + 1) in *.
  assert (HL1 : 1 <= L).
  { unfold L. pose proof (Z.div_le_mono bk (bk + nhi - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  replace (elenZ E (ELit L)) with L in Zb, Hhi' by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (Hq0 : 0 <= q + bk / 8) by (rewrite <- Hdiv1; apply Z.div_pos; lia).
  assert (Hq1 : q + bk / 8 < 2 ^ 61) by (rewrite <- Hdiv1; apply Z.div_lt_upper_bound; lia).
  assert (HH : H = RPN.SB + beg / 8).
  { apply (f_equal bv_unsigned) in Hsa. rewrite Hdiv4 in Hsa.
    rewrite !u_lit64 in Hsa. unfold two64 in Hsa. rewrite Hdiv1. unfold RPN.SB in *.
    rewrite <- Z.add_mod in Hsa by lia.
    rewrite (Z.mod_small (2147450880 + bk / 8 + q)) in Hsa by lia. rewrite (Z.mod_small H) in Hsa by lia. lia. }
  assert (Hz : forall g, beg / 8 <= g <= (beg + n - 1) / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)).
  { intros g Hg. rewrite Hdiv2 in Hg. rewrite Hdiv1 in Hg, HH. replace (RPN.SB + g) with (H + (g - q - bk / 8)) by lia. apply Zb. unfold L. lia. }
  (* [comment removed for export] *)
  pose proof (img8_sound E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B5 Lsb) as C2.
  pose proof (img8_sound E M (kn cs) _ _ HKN Igm1 (ri_gm1 _ _ IMG)) as C3.
  pose proof (img8_sound E M (kn cs) _ _ HKN Icm1 (ri_cm1 _ _ IMG)) as C4.
  pose proof (img8_sound E M (kn cs) _ _ HKN Igm2 (ri_gm2 _ _ IMG)) as C5.
  pose proof (img8_sound E M (kn cs) _ _ HKN Icm2 (ri_cm2 _ _ IMG)) as C6.
  pose proof (img8_sound E M (kn cs) _ _ HKN Ighi (ri_ghi _ _ IMG)) as C7.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B8 Lhi) as C8.
  (* [comment removed for export] *)
  assert (Hrng2 : beg + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= beg /\ beg + n <= RPN.kHighEnd)).
  { apply orb_prop in Hrng as [Hr|Hr]; [apply orb_prop in Hr as [Hr|Hr]|].
    - apply Z.leb_le in Hr; left; lia.
    - apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2. right. lia.
    - (* [comment removed for export] *)
      pose proof (off_band_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model bb bk (reg cs 11) HC Hr) as OB.
      unfold estart, elenZ in OB. cbn [a_base a_off] in OB. fold nw in OB. fold n in OB. fold bbu in OB. rewrite <- HuB in OB.
      specialize (OB ltac:(lia)).
      unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd, LOWTOP, KHI, TOPMAX, STK in *. lia. }
  (* [comment removed for export] *)
  destruct (SPEC M beg n usp R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hrng2 ltac:(lia) ltac:(lia) Hz Hstk
              C1 C2 C3 C4 C5 C6 C7 C8 Hrok R1 ltac:(rewrite HspW; exact R2) ltac:(rewrite HbgW; exact R10) ltac:(rewrite HnwN; exact R11))
    as (regs' & M' & Hms & Hkept & Ha0 & Hout & Hgr).
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs cs' E R FULL model TT ret (Some (ELit 0)) _ regs' M' HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - cbn [edenot]. exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | exact Hgr].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 72)) with 72 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply Hout. lia.
  - exact Hk.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma find_zone_sound : forall k0 k hb hk glast, RPN.find_zone k0 k hb hk glast = true ->
  exists zb zk zn ze, In (KZero (SA zb zk) zn) k /\ xlo k0 (eadd (eaddz zb zk) zn) = Some ze /\ glast < ze
                      /\ lin_ge0 k0 [(hb, hk)] [(zb, zk)] = true.
Proof.
  intros k0 k hb hk glast. induction k as [|K rest IH]; intros H; cbn [RPN.find_zone] in H; [discriminate|].
  destruct K as [| [zb zk] zn | | | | | | | | |]; try (destruct (IH H) as (zb' & zk' & zn' & ze & HIn & R1 & R2 & R3);
                                                        exists zb', zk', zn', ze; split; [right; exact HIn | auto]).
  destruct (xlo k0 (eadd (eaddz zb zk) zn)) as [ze|] eqn:Hx.
  - destruct (Z.ltb glast ze && lin_ge0 k0 [(hb, hk)] [(zb, zk)])%bool eqn:Hc.
    + apply andb_prop in Hc as [H1 H2]. apply Z.ltb_lt in H1. exists zb, zk, zn, ze. split; [left; reflexivity|]. auto.
    + destruct (IH H) as (zb' & zk' & zn' & ze' & HIn & R1 & R2 & R3). exists zb', zk', zn', ze'. split; [right; exact HIn | auto].
  - cbv beta iota in H. destruct (IH H) as (zb' & zk' & zn' & ze' & HIn & R1 & R2 & R3). exists zb', zk', zn', ze'. split; [right; exact HIn | auto].
Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok argH_high argH_agree SINV_frame SINV_agree nx0_ge7 IMG SPEC"] Theorem node_rpoison_rel_sound :
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (RPN.node_rpoison_rel SEGS nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  rewrite RPN.node_rpoison_rel_eq in Hn. unfold RPN.node_rpoison_rel_ref in Hn. cbv zeta in Hn.   (* [comment removed for export] *)
  destruct (Z.eqb (pc cs) (RPN.rp_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (eaddz (reg cs 2) (-72))) as [qb qk] eqn:Hsq.
  set (sh := match srl_split (kn cs) (reg cs 10) 3 with Some e => e | None => mkSrl (kn cs) (reg cs 10) 3 end) in Hn.
  destruct (split_lit (eadd (ELit RPN.SB) sh)) as [hb hk] eqn:Hsh.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  destruct (xhi2 (kn cs) (eadd (reg cs 10) (reg cs 11))) as [eh|] eqn:Heh; [|discriminate].
  cbv zeta in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hnw].
  apply andb_prop in Hcond as [Hcond Lhi]. apply andb_prop in Hcond as [Hcond Lsb].
  apply andb_prop in Hcond as [Hcond Icm2]. apply andb_prop in Hcond as [Hcond Icm1].
  apply andb_prop in Hcond as [Hcond Ighi]. apply andb_prop in Hcond as [Hcond Igm2].
  apply andb_prop in Hcond as [Hcond Igm1]. apply andb_prop in Hcond as [Hcond Igsb].
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hflh].
  apply andb_prop in Hcond as [Hcond Hflq]. apply andb_prop in Hcond as [Hcond Hwr].
  apply andb_prop in Hcond as [Hcond B8]. apply andb_prop in Hcond as [Hcond B7]. apply andb_prop in Hcond as [Hcond B6]. apply andb_prop in Hcond as [Hcond B5].
  apply andb_prop in Hcond as [Hcond B4]. apply andb_prop in Hcond as [Hcond B3]. apply andb_prop in Hcond as [Hcond B2]. apply andb_prop in Hcond as [Hcond B1].
  apply andb_prop in Hcond as [Hcond P8]. apply andb_prop in Hcond as [Hcond P7]. apply andb_prop in Hcond as [Hcond P6]. apply andb_prop in Hcond as [Hcond P5].
  apply andb_prop in Hcond as [Hcond P4]. apply andb_prop in Hcond as [Hcond P3]. apply andb_prop in Hcond as [Hcond P2]. apply andb_prop in Hcond as [Hcond P1].
  apply andb_prop in Hcond as [Hcond Hdisj]. apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hrng].
  apply andb_prop in Hcond as [Hn16 Hn40].
  apply Z.leb_le in Hn16. apply Z.leb_le in Hn40. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'. apply Z.ltb_lt in Hdisj.
  apply Z.leb_le in P1. apply Z.leb_le in P2. apply Z.leb_le in P3. apply Z.leb_le in P4. apply Z.leb_le in P5. apply Z.leb_le in P6. apply Z.leb_le in P7. apply Z.leb_le in P8.
  apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply Z.leb_le in B5. apply Z.leb_le in B6. apply Z.leb_le in B7. apply Z.leb_le in B8.
  apply Z.ltb_lt in Hnw.
  unfold two64 in Hsphi', Hnw.
  (* [comment removed for export] *)
  destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Hblo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  pose proof (xhi2_sound SEGS E M (kn cs) _ _ HKN Heh) as Heh2.
  unfold eadd in Heh2. rewrite mkAlu_denot in Heh2. cbn [alu64 alu] in Heh2. rewrite bv_add_unsigned in Heh2.
  set (begw := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *. set (nw := edenot E (reg cs 11)) in *.
  set (n := bv_unsigned nw) in *. set (usp := bv_unsigned spw) in *. set (beg := bv_unsigned begw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range begw) as Hbr. fold beg in Hbr.
  pose proof (u64_range spw) as Hsr. fold usp in Hsr.
  assert (Hbn : beg + n <= eh).
  { unfold bv_wrap in Heh2. change (bv_modulus 64) with (2 ^ 64) in Heh2. rewrite Z.mod_small in Heh2 by lia. exact Heh2. }
  assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HspW : Z_to_bv 64 usp = spw) by (apply Z_to_bv_bv_unsigned).
  assert (HbgW : Z_to_bv 64 beg = begw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot in Hq. cbn [edenot] in Hq. fold spw in Hq.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 72 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = usp - 72).
  { apply (f_equal bv_unsigned) in Hq. rewrite (u_spw_sub72 spw) in Hq by lia. fold usp in Hq.
    rewrite u_lit64 in Hq. unfold two64 in Hq. rewrite (Z.mod_small Q) in Hq by lia. lia. }
  assert (Hstk : forall a, usp - 72 <= a < usp -> store_ok SEGS M (Z_to_bv 64 a) 1 = true).
  { intros a Ha. apply store_ok_of_all; [cbn; rewrite u64_lit by lia; lia|].
    intros x Hx. eapply (store_ok_all SEGS M 72 (Z_to_bv 64 Q)); [rewrite u64_lit by lia; cbn; lia | exact Qst |].
    rewrite u64_lit in Hx |- * by lia. cbn in Hx |- *. lia. }
  (* [comment removed for export] *)
  assert (Hshd : edenot E sh = Sem.alu64 ALU_SRL begw (Z_to_bv 64 3)).
  { unfold sh. destruct (srl_split (kn cs) (reg cs 10) 3) as [e|] eqn:Hsp.
    - rewrite (srl_split_denot SEGS E M (kn cs) (reg cs 10) 3 e HKN ltac:(lia) Hsp). reflexivity.
    - apply (mkSrl_denot SEGS E M (kn cs) (reg cs 10) 3 (Z_to_bv 64 3) HKN). rewrite u64_lit by lia. reflexivity. }
  pose proof (w_split_lit_denot E _ hb hk Hsh) as Hsa.
  unfold eadd in Hsa. rewrite mkAlu_denot, Hshd in Hsa.
  rewrite (srl3_div8 begw (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity). fold beg in Hsa.
  cbn [edenot] in Hsa. rewrite alu_add in Hsa. unfold v_add in Hsa.
  destruct (flat_x_sound SEGS E M (kn cs) hb hk (ELit 1) HKN Hflh) as (Hlo' & Hhi' & _).
  set (H := estart E (SA hb hk)) in *.
  replace (bv_unsigned (edenot E (ELit 1))) with 1 in Hhi' by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  change (bv_unsigned (edenot E hb) + hk) with H in Hsa.
  assert (Hb8 : 0 <= beg / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (HH : H = RPN.SB + beg / 8).
  { apply (f_equal bv_unsigned) in Hsa.
    rewrite !u_lit64 in Hsa. unfold two64 in Hsa. unfold RPN.SB in *.
    rewrite <- Z.add_mod in Hsa by lia.
    rewrite (Z.mod_small (2147450880 + beg / 8)) in Hsa by lia. rewrite (Z.mod_small H) in Hsa by lia. lia. }
  (* [comment removed for export] *)
  destruct (find_zone_sound _ _ _ _ _ Hkz) as (zb & zk & zn & ze & HinZ & Hze & Hglast & Hlin).
  pose proof (proj1 (Forall_forall _ _) HKN _ HinZ) as HZ. cbn [kentry_ok] in HZ. destruct HZ as [Zflat Zz].
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hlin) as Lz. cbn [xt_den] in Lz.
  change (bv_unsigned (edenot E hb) + hk) with H in Lz.
  set (Zs := estart E (SA zb zk)) in *. set (zlen := elenZ E zn) in *.
  assert (LzS : Zs <= H) by (unfold Zs, estart; cbn [a_base a_off]; lia).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hze) as Hze2.
  unfold eadd, eaddz in Hze2. rewrite !mkAlu_denot in Hze2. cbn [alu64 alu edenot] in Hze2. rewrite !bv_add_unsigned in Hze2.
  unfold flat in Zflat. unfold bv_wrap in Hze2. change (bv_modulus 64) with (2 ^ 64) in Hze2.
  rewrite Z_to_bv_unsigned in Hze2. unfold bv_wrap in Hze2. change (bv_modulus 64) with (2 ^ 64) in Hze2.
  assert (Hzs : (bv_unsigned (edenot E zb) + zk mod 2 ^ 64) mod 2 ^ 64 = Zs).
  { rewrite Z.add_mod_idemp_r by lia. unfold Zs, estart. cbn [a_base a_off]. apply Z.mod_small.
    unfold Zs, estart in Zflat. cbn [a_base a_off] in Zflat. lia. }
  rewrite Hzs in Hze2. change (bv_unsigned (edenot E zn)) with zlen in Hze2.
  assert (Hgl0 : 0 < RPN.SB + (eh - 1) / 8).
  { unfold RPN.SB. pose proof (Z.div_pos (eh - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (Hend : RPN.SB + (eh - 1) / 8 < Zs + zlen).
  { destruct (Z.eq_dec (Zs + zlen) (2 ^ 64)) as [Eq|Ne].
    - rewrite Eq, Z_mod_same_full in Hze2. lia.
    - rewrite Z.mod_small in Hze2 by lia. lia. }
  assert (Hz : forall g, beg / 8 <= g <= (beg + n - 1) / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)).
  { intros g Hg.
    assert (D1 : (beg + n - 1) / 8 <= (eh - 1) / 8) by (apply Z.div_le_mono; lia).
    replace (RPN.SB + g) with (Zs + (RPN.SB + g - Zs)) by lia. apply Zz. lia. }
  (* [comment removed for export] *)
  pose proof (img8_sound E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B5 Lsb) as C2.
  pose proof (img8_sound E M (kn cs) _ _ HKN Igm1 (ri_gm1 _ _ IMG)) as C3.
  pose proof (img8_sound E M (kn cs) _ _ HKN Icm1 (ri_cm1 _ _ IMG)) as C4.
  pose proof (img8_sound E M (kn cs) _ _ HKN Igm2 (ri_gm2 _ _ IMG)) as C5.
  pose proof (img8_sound E M (kn cs) _ _ HKN Icm2 (ri_cm2 _ _ IMG)) as C6.
  pose proof (img8_sound E M (kn cs) _ _ HKN Ighi (ri_ghi _ _ IMG)) as C7.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B8 Lhi) as C8.
  (* [comment removed for export] *)
  assert (Hrng2 : beg + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= beg /\ beg + n <= RPN.kHighEnd)).
  { apply orb_prop in Hrng as [Hr|Hr].
    - apply Z.leb_le in Hr; left; lia.
    - apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2. right. lia. }
  assert (Hdisj2 : RPN.SB + (beg + n - 1) / 8 < usp - 72).
  { assert (D1 : (beg + n - 1) / 8 <= (eh - 1) / 8) by (apply Z.div_le_mono; lia). lia. }
  (* [comment removed for export] *)
  destruct (SPEC M beg n usp R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hrng2 ltac:(lia) Hdisj2 Hz Hstk
              C1 C2 C3 C4 C5 C6 C7 C8 Hrok R1 ltac:(rewrite HspW; exact R2) ltac:(rewrite HbgW; exact R10) ltac:(rewrite HnwN; exact R11))
    as (regs' & M' & Hms & Hkept & Ha0 & Hout & Hgr).
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs cs' E R FULL model TT ret (Some (ELit 0)) _ regs' M' HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - cbn [edenot]. exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | exact Hgr].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 72)) with 72 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply Hout. lia.
  - exact Hk.
Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok argH_high argH_agree SINV_frame SINV_agree nx0_ge7 IMG SPEC"] Theorem node_rpoison_sound :
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (RPN.node_rpoison SEGS nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC Hpre Hn Hk. unfold RPN.node_rpoison in Hn.
  destruct (RPN.node_rpoison_int SEGS nx0 T cs) as [cs1|] eqn:H1.
  - injection Hn as <-. exact (node_rpoison_int_sound cs cs1 E R FULL model TT HC Hpre H1 Hk).
  - exact (node_rpoison_rel_sound cs cs' E R FULL model TT HC Hpre Hn Hk).
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[using="Type"] Lemma v_addi_as_add : forall (x : word) i, v_addi x i = Sem.alu64 ALU_ADD x (Z_to_bv 64 i).
Proof.
  intros x i. rewrite alu_add. unfold v_add, v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

#[using="Type"] Lemma nth_rc_regs : forall sr e1 e2 e3 e20 i,
  nth i (RPN.rc_regs sr e1 e2 e3 e20) (ELit 0) =
  if Nat.eqb i 20 then e20 else if Nat.eqb i 15 then ELit 0 else if Nat.eqb i 14 then ELit 0
  else if Nat.eqb i 13 then e3 else if Nat.eqb i 12 then e2 else if Nat.eqb i 11 then e1 else nth i sr (ELit 0).
Proof.
  intros. unfold RPN.rc_regs.
  rewrite (nth_sr_upd 20). destruct (Nat.eqb i 20); [reflexivity|].
  rewrite (nth_sr_upd 15). destruct (Nat.eqb i 15); [reflexivity|].
  rewrite (nth_sr_upd 14). destruct (Nat.eqb i 14); [reflexivity|].
  rewrite (nth_sr_upd 13). destruct (Nat.eqb i 13); [reflexivity|].
  rewrite (nth_sr_upd 12). destruct (Nat.eqb i 12); [reflexivity|].
  rewrite (nth_sr_upd 11). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_add_zbv_mod : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[using="SEGS_wx SEGS_in_hull HULL_ok argH_high argH_agree SINV_frame SINV_agree nx0_ge7 IMG RSPEC"] Theorem node_readcheck_sound :
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (RPN.node_readcheck SEGS nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold RPN.node_readcheck in Hn.
  destruct (Z.eqb (pc cs) (RPN.rc_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (split_lit (reg cs 9)) as [bb bk] eqn:Hsb.
  destruct (split_lit (eadd (ELit (RPN.SB + bk / 8 - (RPN.SB + bk / 8) mod 8)) (mkSrl (kn cs) bb 3))) as [hb hk] eqn:Hsh.
  destruct (xlo (kn cs) (reg cs 10)) as [rlo|] eqn:Hrlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [rhi|] eqn:Hrhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 9)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Lsb]. apply andb_prop in Hcond as [Hcond Igsb].
  apply andb_prop in Hcond as [Hcond B2]. apply andb_prop in Hcond as [Hcond B1].
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hflh].
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hflb]. apply andb_prop in Hcond as [Hcond Hal].
  apply andb_prop in Hcond as [Hcond Hd64]. apply andb_prop in Hcond as [Hr1 Hr64].
  apply Z.leb_le in Hr1. apply Z.leb_le in Hr64. apply Z.ltb_lt in Hd64. apply Z.leb_le in Hal. apply Z.leb_le in B1. apply Z.leb_le in B2.
  unfold two64 in Hd64. injection Hn as <-.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 8 HC ltac:(lia)) as R8.
  replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) in R8 by (apply bv_eq; reflexivity).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hrlo) as Hrlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hrhi) as Hrhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  set (dw := edenot E (reg cs 9)) in *. set (rw := edenot E (reg cs 10)) in *.
  set (buf := bv_unsigned dw) in *. set (res := bv_unsigned rw) in *.
  pose proof (u64_range dw) as Hbr. fold buf in Hbr. pose proof (u64_range rw) as Hrr. fold res in Hrr.
  assert (HdwB : Z_to_bv 64 buf = dw) by (apply Z_to_bv_bv_unsigned).
  assert (HrwR : Z_to_bv 64 res = rw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E (reg cs 9) bb bk Hsb) as Hbeg. fold dw in Hbeg.
  destruct (flat_x_sound SEGS E M (kn cs) bb bk (ELit 1) HKN Hflb) as (Blo & Bhi & _).
  set (bbu := bv_unsigned (edenot E bb)) in *.
  replace (bv_unsigned (edenot E (ELit 1))) with 1 in Bhi by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (HuB : buf = bbu + bk).
  { unfold buf. rewrite Hbeg. unfold estart in Blo, Bhi. cbn [a_base a_off] in Blo, Bhi. fold bbu in Blo, Bhi. apply u64_lit. lia. }
  destruct (ealign_sound SEGS E M (kn cs) bb HKN) as [Hea1 Hea2]. fold bbu in Hea2.
  assert (Hal64 : exists q, bbu = 64 * q).
  { destruct Hea2 as [q Hq8]. exists (q * 2 ^ (ealign (kn cs) bb - 6)). rewrite Hq8.
    replace (ealign (kn cs) bb) with ((ealign (kn cs) bb - 6) + 6) at 1 by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 6) with 64. lia. }
  destruct Hal64 as [q Hq64].
  assert (Hdiv4 : bbu / 8 = 8 * q) by (rewrite Hq64; replace (64 * q) with (8 * q * 8) by lia; apply Z.div_mul; lia).
  assert (Hdiv1 : buf / 8 = 8 * q + bk / 8).
  { rewrite HuB, Hq64. replace (64 * q + bk) with (8 * q * 8 + bk) by lia. rewrite Z.div_add_l by lia. reflexivity. }
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ hb hk Hsh) as Hsa.
  unfold eadd in Hsa. rewrite mkAlu_denot in Hsa.
  rewrite (mkSrl_denot SEGS E M (kn cs) bb 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)) in Hsa.
  rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity). fold bbu in Hsa.
  cbn [edenot] in Hsa. rewrite alu_add in Hsa. unfold v_add in Hsa.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) hb hk (ELit 16) HKN HKN Hkz) as (Zb & Hlo' & Hhi').
  set (H := estart E (SA hb hk)) in *.
  change (bv_unsigned (edenot E hb) + hk) with H in Hsa.
  replace (elenZ E (ELit 16)) with 16 in Zb, Hhi' by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  pose proof (Z.mod_pos_bound (RPN.SB + bk / 8) 8 ltac:(lia)) as Hm.
  assert (HH : H = (RPN.SB + buf / 8) / 8 * 8).
  { apply (f_equal bv_unsigned) in Hsa. rewrite Hdiv4 in Hsa.
    rewrite !u_lit64 in Hsa. unfold two64 in Hsa. rewrite Hdiv1. unfold RPN.SB in *.
    rewrite <- Z.add_mod in Hsa by lia.
    rewrite (Z.mod_small (2147450880 + bk / 8 - (2147450880 + bk / 8) mod 8 + 8 * q)) in Hsa by lia.
    rewrite (Z.mod_small H) in Hsa by lia. lia. }
  assert (Hz : forall j, 0 <= j < 16 -> M (Z_to_bv 64 ((RPN.SB + buf / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. rewrite <- HH. apply Zb. lia. }
  (* [comment removed for export] *)
  pose proof (img8_sound E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B2 Lsb) as C2.
  (* [comment removed for export] *)
  destruct (RSPEC M (seg_rom SEGS) buf res R ltac:(lia) ltac:(lia) ltac:(lia) C1 C2 Hz
              ltac:(rewrite HdwB; exact R9) ltac:(rewrite HrwR; exact R10))
    as (regs' & Hms & P11 & P12 & P13 & P14 & P15 & P20 & Pother).
  lazymatch type of Hk with context [mk_ss _ ?sr _ _] =>
    eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
              cs E E R FULL model TT (RPN.rc_exit T) sr (kn cs) (nxt cs) regs' M HC Hfresh (env_agree_refl _ E))
  end.
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
    { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
      exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
    cbn [s_regs mk_ss]. rewrite nth_rc_regs.
    assert (RX : forall n (rb : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rb -> Nat.eqb (ridx r) n = true -> r = rb).
    { intros n rb Hn Hrb E1. first [apply Nat.eqb_eq in E1 | apply N.eqb_eq in E1]. rewrite (reg_of_ridx r n E1). apply bv_eq.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hrb. }
    destruct (Nat.eqb (ridx r) 20) eqn:E20; [apply (RX 20%nat 20%bv ltac:(lia) eq_refl) in E20; subst r|].
    { rewrite P20, R8. unfold eaddz. do 2 rewrite mkAlu_denot. cbn [edenot]. do 2 rewrite v_addi_as_add. reflexivity. }
    destruct (Nat.eqb (ridx r) 15) eqn:E15; [apply (RX 15%nat 15%bv ltac:(lia) eq_refl) in E15; subst r; rewrite P15; reflexivity|].
    destruct (Nat.eqb (ridx r) 14) eqn:E14; [apply (RX 14%nat 14%bv ltac:(lia) eq_refl) in E14; subst r; rewrite P14; reflexivity|].
    destruct (Nat.eqb (ridx r) 13) eqn:E13; [apply (RX 13%nat 13%bv ltac:(lia) eq_refl) in E13; subst r|].
    { rewrite P13. unfold eaddz, eadd. do 2 rewrite mkAlu_denot. cbn [edenot]. fold dw rw. rewrite <- HdwB, <- HrwR.
      rewrite <- v_addi_as_add. rewrite alu_add. rewrite v_add_zbv by lia. rewrite v_addi_zbv by lia. first [reflexivity | f_equal; lia]. }
    destruct (Nat.eqb (ridx r) 12) eqn:E12; [apply (RX 12%nat 12%bv ltac:(lia) eq_refl) in E12; subst r|].
    { rewrite P12. unfold eadd, eaddz. rewrite mkAlu_denot.
      rewrite (mkSrl_denot SEGS E M (kn cs) _ 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)).
      do 2 rewrite mkAlu_denot. cbn [edenot]. fold dw rw. rewrite <- HdwB, <- HrwR.
      rewrite <- (v_addi_as_add (Sem.alu64 ALU_ADD (Z_to_bv 64 buf) (Z_to_bv 64 res))).
      rewrite (alu_add (Z_to_bv 64 buf)). rewrite (v_add_zbv buf res) by lia. rewrite v_addi_zbv by lia.
      replace (buf + res + -1) with (buf + res - 1) by lia.
      rewrite (srl3_div8 _ (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity). rewrite zbv_u by lia.
      rewrite alu_add. rewrite v_add_zbv_mod. reflexivity. }
    destruct (Nat.eqb (ridx r) 11) eqn:E11; [apply (RX 11%nat 11%bv ltac:(lia) eq_refl) in E11; subst r|].
    { rewrite P11. unfold eadd. rewrite mkAlu_denot.
      rewrite (mkSrl_denot SEGS E M (kn cs) bb 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)).
      rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity). fold bbu. rewrite Hdiv4.
      cbn [edenot]. rewrite alu_add, v_add_zbv_mod. rewrite Hdiv1. apply (f_equal (Z_to_bv 64)). lia. }
    rewrite Pother; [apply HRr; exact Hr0
                   | intros ->; cbv in E11; discriminate E11 | intros ->; cbv in E12; discriminate E12
                   | intros ->; cbv in E13; discriminate E13 | intros ->; cbv in E14; discriminate E14
                   | intros ->; cbv in E15; discriminate E15 | intros ->; cbv in E20; discriminate E20 ].
  - exact HKN.
  - intros R' FULL' model' HC' Hfs'. apply (Hk E R' FULL' model' (conj (env_agree_refl _ E) (env_agree_refl _ E)) HC' Hfs').
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="SEGS_wx SEGS_in_hull HULL_ok argH_high argH_agree SINV_frame SINV_agree nx0_ge7 IMG SPEC RSPEC"] Theorem rp_xn_sound : ext_stmt SEGS A nx0 LIMIT (RPN.xn SEGS nx0 T) SINV argH FS0.
Proof.
  intros id args. unfold RPN.xn.
  destruct (Nat.eqb id 100); [apply node_rpoison_sound|].
  destruct (Nat.eqb id 101); [apply node_readcheck_sound|].
  intros cs cs' E R FULL model TT _ _ H. discriminate H.
Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
