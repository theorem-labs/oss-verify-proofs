(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare AgentLib.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound CxPlanSoundSums.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AsanNodesRP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE CxNodesRPSound.
Import ListNotations.
Import AX2 AX2S CAP CXS APSX.
Open Scope Z_scope.

Module RPU.
Section WithSegs.
Variable segs : list Segment.
Variable nx0 : nat.
Variable T : RPN.rptab.
Definition node_rpoison_u (args : list expr) (cs : acs) : option acs :=
  match args with
  | [bb; u] =>
    let k := kn cs in
    if negb (Z.eqb (pc cs) (RPN.rp_entry T)) then None else
    match ret_lit cs with
    | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(qb, qk) := split_lit (eaddz sp (-72)) in
      match erange k (esub beg (eadd bb u)), xlo k u, xhi k u with
      | Some (bk, bk'), Some ulo, Some uhi =>
        let '(hb, hk) := split_lit (eadd (ELit (RPN.SB + (bk + ulo) / 8)) (mkSrl k bb 3)) in
        match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
        | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
          let L := (bk + uhi + nhi - 1) / 8 - (bk + ulo) / 8 + 1 in
          if (Z.eqb bk bk' && Z.leb 0 bk && Z.leb 0 ulo && Z.leb 16 nlo && Z.leb nhi (2 ^ 40)
              && (Z.leb (bhi + nhi) RPN.kLowEnd || (Z.leb RPN.kHighBeg blo && Z.leb (bhi + nhi) RPN.kHighEnd))
              && Z.leb 3 (ealign k bb) && flat_x k bb (bk + uhi) (ELit 1)
              && Z.leb 80 splo && Z.ltb sphi two64
              && Z.ltb (RPN.SB + (bhi + nhi - 1) / 8) (splo - 72)
              && Z.leb (RPN.rp_chi T + 8) (splo - 72) && Z.leb (RPN.rp_cm2 T + 8) (splo - 72) && Z.leb (RPN.rp_cm1 T + 8) (splo - 72)
              && Z.leb (RPN.rp_csb T + 8) (splo - 72) && Z.leb (RPN.rp_ghi T + 8) (splo - 72) && Z.leb (RPN.rp_gm2 T + 8) (splo - 72)
              && Z.leb (RPN.rp_gm1 T + 8) (splo - 72) && Z.leb (RPN.rp_gsb T + 8) (splo - 72)
              && Z.leb 0 (RPN.rp_gsb T) && Z.leb 0 (RPN.rp_gm1 T) && Z.leb 0 (RPN.rp_gm2 T) && Z.leb 0 (RPN.rp_ghi T)
              && Z.leb 0 (RPN.rp_csb T) && Z.leb 0 (RPN.rp_cm1 T) && Z.leb 0 (RPN.rp_cm2 T) && Z.leb 0 (RPN.rp_chi T)
              && kwritable k k qb qk 72 && flat_x k qb qk (ELit 72)
              && flat_x k hb hk (ELit L) && kzero_x k k hb hk (ELit L)
              && RPN.img8 k (RPN.rp_gsb T) && RPN.img8 k (RPN.rp_gm1 T) && RPN.img8 k (RPN.rp_gm2 T) && RPN.img8 k (RPN.rp_ghi T)
              && RPN.img8 k (RPN.rp_cm1 T) && RPN.img8 k (RPN.rp_cm2 T)
              && RPN.lit_cell segs k (RPN.rp_csb T) RPN.SB && RPN.lit_cell segs k (RPN.rp_chi T) RPN.kHighEnd)%bool
          then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc k qb qk (ELit 72))
          else None
        | _, _, _, _, _, _ => None
        end
      | _, _, _ => None
      end
    | None => None
    end
  | _ => None
  end.
End WithSegs.
End RPU.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.
Variable T : RPN.rptab.
Hypothesis IMG : rp_img SEGS T.
Hypothesis SPEC : rp_spec SEGS T.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Theorem node_rpoison_u_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (RPU.node_rpoison_u SEGS nx0 T args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold RPU.node_rpoison_u in Hn.
  destruct args as [|bb [|u [|? ?]]]; try discriminate Hn.
  destruct (Z.eqb (pc cs) (RPN.rp_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (eaddz (reg cs 2) (-72))) as [qb qk] eqn:Hsq.
  destruct (erange (kn cs) (esub (reg cs 10) (eadd bb u))) as [[bk bk']|] eqn:Her; [|discriminate].
  destruct (xlo (kn cs) u) as [ulo|] eqn:Hulo; [|discriminate].
  destruct (xhi (kn cs) u) as [uhi|] eqn:Huhi; [|discriminate].
  destruct (split_lit (eadd (ELit (RPN.SB + (bk + ulo) / 8)) (mkSrl (kn cs) bb 3))) as [hb hk] eqn:Hsh.
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
  apply andb_prop in Hcond as [Hcond Hn40]. apply andb_prop in Hcond as [Hcond Hn16]. apply andb_prop in Hcond as [Hcond Hulo0]. apply andb_prop in Hcond as [Hbkk Hbk0].
  apply Z.eqb_eq in Hbkk. subst bk'. apply Z.leb_le in Hbk0. apply Z.leb_le in Hulo0.
  apply Z.leb_le in Hn16. apply Z.leb_le in Hn40. apply Z.leb_le in Hal. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'. apply Z.ltb_lt in Hdisj.
  apply Z.leb_le in P1. apply Z.leb_le in P2. apply Z.leb_le in P3. apply Z.leb_le in P4. apply Z.leb_le in P5. apply Z.leb_le in P6. apply Z.leb_le in P7. apply Z.leb_le in P8.
  apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply Z.leb_le in B5. apply Z.leb_le in B6. apply Z.leb_le in B7. apply Z.leb_le in B8.
  unfold two64 in Hsphi'.
  (* [comment removed for export] *)
  destruct (ret_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Hblo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hulo) as Hulo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Huhi) as Huhi2.
  pose proof (erange_sound SEGS E M (kn cs) _ bk bk HKN Her) as Hdiff.
  set (begw := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *. set (nw := edenot E (reg cs 11)) in *.
  set (n := bv_unsigned nw) in *. set (usp := bv_unsigned spw) in *. set (beg := bv_unsigned begw) in *.
  set (uu := bv_unsigned (edenot E u)) in *. set (bbu := bv_unsigned (edenot E bb)) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range begw) as Hbr. fold beg in Hbr.
  pose proof (u64_range spw) as Hsr. fold usp in Hsr. pose proof (u64_range (edenot E u)) as Hur. fold uu in Hur.
  pose proof (u64_range (edenot E bb)) as Hbbr. fold bbu in Hbbr. unfold two64 in *.
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
  destruct (flat_x_sound SEGS E M (kn cs) bb (bk + uhi) (ELit 1) HKN Hflb) as (Blo & Bhi & _).
  replace (bv_unsigned (edenot E (ELit 1))) with 1 in Bhi by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  unfold estart in Blo, Bhi. cbn [a_base a_off] in Blo, Bhi. fold bbu in Blo, Bhi.
  assert (HuB : beg = bbu + uu + bk).
  { unfold esub, eadd in Hdiff. rewrite !mkAlu_denot in Hdiff. rewrite u_sub64, u_add64 in Hdiff. fold begw beg uu bbu in Hdiff.
    rewrite (Z.mod_small (bbu + uu)) in Hdiff by lia.
    destruct (Z_lt_ge_dec (beg - (bbu + uu)) 0) as [Hneg|Hpos].
    - exfalso. assert (Y : (beg - (bbu + uu)) mod 2 ^ 64 = beg - (bbu + uu) + 2 ^ 64) by (symmetry; apply (Z.mod_unique _ _ (-1)); lia). lia.
    - rewrite Z.mod_small in Hdiff by lia. lia. }
  destruct (ealign_sound SEGS E M (kn cs) bb HKN) as [Hea1 Hea2]. fold bbu in Hea2.
  assert (Hal8 : exists q, bbu = 8 * q).
  { destruct Hea2 as [q Hq8]. exists (q * 2 ^ (ealign (kn cs) bb - 3)). rewrite Hq8.
    replace (ealign (kn cs) bb) with ((ealign (kn cs) bb - 3) + 3) at 1 by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia. }
  destruct Hal8 as [q Hq8].
  assert (Hdiv1 : beg / 8 = q + (uu + bk) / 8).
  { rewrite HuB, Hq8. replace (8 * q + uu + bk) with (q * 8 + (uu + bk)) by lia. rewrite Z.div_add_l by lia. reflexivity. }
  assert (Hdiv2 : (beg + n - 1) / 8 = q + (uu + bk + n - 1) / 8).
  { rewrite HuB, Hq8. replace (8 * q + uu + bk + n - 1) with (q * 8 + (uu + bk + n - 1)) by lia. rewrite Z.div_add_l by lia. reflexivity. }
  assert (Hdiv3 : (uu + bk + n - 1) / 8 <= (bk + uhi + nhi - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (Hdiv3' : (bk + ulo) / 8 <= (uu + bk) / 8) by (apply Z.div_le_mono; lia).
  assert (Hdiv4 : bbu / 8 = q) by (rewrite Hq8, Z.mul_comm; apply Z.div_mul; lia).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ hb hk Hsh) as Hsa.
  unfold eadd in Hsa. rewrite mkAlu_denot in Hsa.
  rewrite (mkSrl_denot SEGS E M (kn cs) bb 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)) in Hsa.
  rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity). fold bbu in Hsa.
  cbn [edenot] in Hsa. rewrite alu_add in Hsa. unfold v_add in Hsa.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) hb hk (ELit ((bk + uhi + nhi - 1) / 8 - (bk + ulo) / 8 + 1)) HKN HKN Hkz) as (Zb & Hlo' & Hhi').
  set (H := estart E (SA hb hk)) in *.
  change (bv_unsigned (edenot E hb) + hk) with H in Hsa.
  set (L := (bk + uhi + nhi - 1) / 8 - (bk + ulo) / 8 + 1) in *.
  assert (HL1 : 1 <= L).
  { unfold L. pose proof (Z.div_le_mono (bk + ulo) (bk + uhi + nhi - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  replace (elenZ E (ELit L)) with L in Zb, Hhi' by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (Hq0 : 0 <= q) by lia.
  assert (Hq1 : q + (bk + ulo) / 8 < 2 ^ 61).
  { assert (X : q + (bk + ulo) / 8 <= beg / 8) by lia. pose proof (Z.div_lt_upper_bound beg 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia. }
  assert (Hq2 : 0 <= (bk + ulo) / 8) by (apply Z.div_pos; lia).
  assert (HH : H = RPN.SB + (bk + ulo) / 8 + q).
  { apply (f_equal bv_unsigned) in Hsa. rewrite Hdiv4 in Hsa.
    rewrite !u_lit64 in Hsa. unfold two64 in Hsa. unfold RPN.SB in *.
    rewrite <- Z.add_mod in Hsa by lia.
    rewrite (Z.mod_small (2147450880 + (bk + ulo) / 8 + q)) in Hsa by lia. rewrite (Z.mod_small H) in Hsa by lia. lia. }
  assert (Hz : forall g, beg / 8 <= g <= (beg + n - 1) / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)).
  { intros g Hg. rewrite Hdiv2 in Hg. rewrite Hdiv1 in Hg. replace (RPN.SB + g) with (H + (g - q - (bk + ulo) / 8)) by lia. apply Zb. unfold L. lia. }
  (* [comment removed for export] *)
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B5 Lsb) as C2.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm1 (ri_gm1 _ _ IMG)) as C3.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm1 (ri_cm1 _ _ IMG)) as C4.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm2 (ri_gm2 _ _ IMG)) as C5.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm2 (ri_cm2 _ _ IMG)) as C6.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Ighi (ri_ghi _ _ IMG)) as C7.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B8 Lhi) as C8.
  (* [comment removed for export] *)
  assert (Hrng2 : beg + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= beg /\ beg + n <= RPN.kHighEnd)).
  { apply orb_prop in Hrng as [Hr|Hr]; [apply Z.leb_le in Hr; left; lia|].
    apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2. right. lia. }
  (* [comment removed for export] *)
  destruct (SPEC M beg n usp R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hrng2 ltac:(lia) ltac:(lia) Hz Hstk
              C1 C2 C3 C4 C5 C6 C7 C8 Hrok R1 ltac:(rewrite HspW; exact R2) ltac:(rewrite HbgW; exact R10) ltac:(rewrite HnwN; exact R11))
    as (regs' & M' & Hms & Hkept & Ha0 & Hout & Hgr).
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH ISP argH_high NX0_spw argH_agree SINV_frame SINV_agree FS0
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End Sound.
