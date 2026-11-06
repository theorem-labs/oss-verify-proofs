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
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec LibWritev RefNodes UbExitBase UbLibCas UbLibCas2 Hoare Frame
  RefMemcpyLib UbMemcpyBase UbMemcpy SymExec
  MallocDefs UbEnframeBase RefEnframeArith UbEnframe UbGetMeta UbFreePro.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan UbSymSlots UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.
Section NX0.
Variable nx0 : nat.
Context {fx : PropExec.FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="Type"] Lemma slots_vars_lt_carry : forall b k log ss, slots_vars_lt b ss = true -> slots_vars_lt b (slots_carry k log ss) = true.
Proof.
  intros b k log ss H. rewrite slots_carry_eq. (* [comment removed for export] *)
  induction log as [|[[bb o] w v] older IH]; cbn [slots_carry_ref]; [exact H|].
  apply slots_vars_lt_keep. exact IH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma call_freepro_sound' : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_freepro U0 -> call_freepro RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_freepro in Hn.
  destruct (find_slot (kn cs) (reg cs 10) (c_slots cs)) as [s|] eqn:Hfind; [|discriminate].
  cbv zeta in Hn.
  set (strd := sl_stride s) in Hn. set (idx := sl_idx s) in Hn.
  set (sidx := match strd with ELit z => Some ((z mod two64) * idx)%Z | _ => if idx =? 0 then Some 0%Z else None end) in Hn.
  destruct (decode_W (sl_W s)) as [[Se c]|] eqn:HdW; [|discriminate].
  destruct (xlo (kn cs) strd) as [slo|] eqn:Hslo; [|discriminate].
  destruct (xhi (kn cs) strd) as [shi|] eqn:Hshi; [|discriminate].
  destruct sidx as [si|] eqn:Hsidx; [|discriminate].
  cbv zeta in Hn.
  set (Me := mkAlu ALU_ADD (sl_start s) (ELit (- (16 + si)))) in Hn.
  destruct (split_lit Me) as [mb mk] eqn:Hsme.
  destruct (kread8e RSEGS (kn cs) mb mk) as [ge|] eqn:Hge; [|discriminate].
  destruct (split_lit ge) as [gb gk] eqn:Hsg.
  destruct (kread8e RSEGS (kn cs) gb (gk + 16)) as [Me'|] eqn:HMe'; [|discriminate].
  destruct (kread8e RSEGS (kn cs) gb (gk + 32)) as [We|] eqn:HWe; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) gb (gk + 24) 4) as [avail|] eqn:Hav; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) gb (gk + 28) 4) as [freed|] eqn:Hfr; [|discriminate].
  destruct (lin_lowbits_kn (kn cs) ge 12) as [gm12|] eqn:Hlow; [|discriminate].
  set (area := mkAlu ALU_ADD ge (ELit (- gm12))) in Hn.
  destruct (split_lit area) as [ab ak] eqn:Hsa.
  destruct (split_lit (sl_start s)) as [hb hk] eqn:Hsh.
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-48))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  set (eexp := mkAlu ALU_ADD (sl_start s) (mkAlu ALU_ADD strd (ELit (-4)))) in Hn.
  destruct (split_lit eexp) as [eb ek] eqn:Hsee.
  destruct (kread8e RSEGS (kn cs) ab ak) as [se|] eqn:Hse; [|discriminate].
  change (d_malloc_ctx U0) with 0xe5428%Z in Hn.
  destruct (kread8e RSEGS (kn cs) (ELit 0) 0xe5428) as [se'|] eqn:Hse'; [|discriminate].
  destruct (xlo (kn cs) (sl_off s)) as [olo|] eqn:Holo; [|discriminate].
  destruct (xhi (kn cs) (sl_off s)) as [ohi|] eqn:Hohi; [|discriminate].
  destruct (ehi (kn cs) ge) as [ghi|] eqn:Hghi; [|discriminate].
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) hb) as [hh|] eqn:Hhh; [|discriminate].
  destruct (xlo (kn cs) Se) as [Slo|] eqn:HSlo; [|discriminate].
  destruct (xhi (kn cs) Se) as [Shi|] eqn:HShi; [|discriminate].
  set (reserved := mkAlu ALU_SUB (mkAlu ALU_ADD strd (ELit (-4))) (mkAlu ALU_ADD (sl_n s) (times16 (sl_off s)))) in Hn.
  set (e12 := mkAlu ALU_ADD (sl_start s) (mkAlu ALU_ADD strd (ELit (-16)))) in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (log := [SE (SA qb (qk + 8)) 8 (reg cs 19); SE (SA qb (qk + 16)) 8 (reg cs 18);
               SE (SA qb (qk + 24)) 8 (reg cs 9); SE (SA qb (qk + 32)) 8 (reg cs 8);
               SE (SA qb (qk + 40)) 8 (reg cs 1)]) in Hn.
  destruct (carry log (kn cs) []) as [[kn' scs] hs] eqn:Hcar.
  destruct scs; [|discriminate].
  destruct (kn_vars_lt (s_next (c_ss cs)) kn') eqn:Hkv; [|discriminate].
  lazymatch type of Hn with Some ?x = Some _ => assert (Ecs : cs' = x) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hvars]. apply andb_prop in Hcond as [Hcond Hs3]. apply andb_prop in Hcond as [Hcond Hs2].
  apply andb_prop in Hcond as [Hcond Hs1]. apply andb_prop in Hcond as [Hcond Hstk]. apply andb_prop in Hcond as [Hcond Himg].
  apply andb_prop in Hcond as [Hcond Hflh]. apply andb_prop in Hcond as [Hcond Hrwe]. apply andb_prop in Hcond as [Hcond Hend].
  apply andb_prop in Hcond as [Hcond Hfla]. apply andb_prop in Hcond as [Hcond Hflg]. apply andb_prop in Hcond as [Hcond Hflm].
  apply andb_prop in Hcond as [Hcond Hsec]. apply andb_prop in Hcond as [Hcond Hfrb]. apply andb_prop in Hcond as [Hcond Havb].
  apply andb_prop in Hcond as [Hcond Holo0]. apply andb_prop in Hcond as [Hcond Hml]. apply andb_prop in Hcond as [Hcond Hsc].
  apply andb_prop in Hcond as [Hcond Hli]. apply andb_prop in Hcond as [Hcond Hidx0]. apply andb_prop in Hcond as [Hcond HShi40].
  apply andb_prop in Hcond as [HMe Hw]. apply Z.leb_le in HShi40.
  rename Hli into Hidxl. apply Z.leb_le in Hidx0. apply Z.leb_le in Hidxl.
  apply Z.leb_le in Holo0.
  apply negb_true_iff in Havb. apply negb_true_iff in Hfrb.
  apply expr_eqb_eq in Hsec. subst se'.
  apply Z.leb_le in Hs3.   (* [comment removed for export] *)
  apply expr_eqb_eq in Hw.
  (* [comment removed for export] *)
  apply find_some in Hfind as [Hsin Hsp].
  pose proof (proj1 (Forall_forall _ _) HSL s Hsin) as HS.
  unfold slot_ok in HS. rewrite Hsh in HS. fold strd idx in HS.
  destruct (split_lit (sl_p s)) as [pb pk] eqn:Hspp.
  destruct HS as (P & Hp & Hh & Hpp & Hsd & Hsc48 & Hsd2 & Hmod & Hmod2 & Hlo & Hnw & Hidx32 & Hq).
  unfold uE in P, Hp, Hh, Hpp, Hsd, Hsc48, Hsd2, Hmod, Hmod2, Hlo, Hnw, Hidx32, Hq.
  set (st := bv_unsigned (edenot E (sl_start s))) in *.
  set (nn := bv_unsigned (edenot E (sl_n s))) in *.
  set (o := bv_unsigned (edenot E (sl_off s))) in *.
  set (stride := bv_unsigned (edenot E strd)) in *.
  set (W := bv_unsigned (edenot E (sl_W s))) in *.
  pose proof (u64_range (edenot E (sl_n s))) as Hnnr. fold nn in Hnnr.
  pose proof (u64_range (edenot E (sl_off s))) as Hor. fold o in Hor.
  pose proof (u64_range (edenot E strd)) as Hstr_r. fold stride in Hstr_r.
  pose proof (u64_range (edenot E (sl_W s))) as HW_r. fold W in HW_r.
  pose proof (xlo_sound RSEGS E M (kn cs) strd slo HKN Hslo) as Hslo'. fold stride in Hslo'.
  pose proof (xhi_sound RSEGS E M (kn cs) strd shi HKN Hshi) as Hshi'. fold stride in Hshi'.
  pose proof (xlo_sound RSEGS E M (kn cs) Se Slo HKN HSlo) as HSlo'.
  pose proof (xhi_sound RSEGS E M (kn cs) Se Shi HKN HShi) as HShi'.
  pose proof (u64_range (edenot E Se)) as HSer.
  pose proof (decode_W_range _ _ _ HdW) as Hc.
  destruct (decode_W_sound E (sl_W s) Se c HdW ltac:(lia)) as [HWdec _]. fold W in HWdec.
  destruct (W_fields (bv_unsigned (edenot E Se)) c ltac:(lia) Hc) as (Fml & Fli & Fsc). rewrite <- HWdec in Fml, Fli, Fsc.
  assert (Hsi : si = (stride * idx)%Z).
  { subst sidx. destruct strd as [z| | | | | | |];
      first [ injection Hsidx as <-; subst stride; cbn [edenot]; rewrite u_lit64; reflexivity
            | destruct (idx =? 0) eqn:Hi0; [|discriminate]; injection Hsidx as <-; apply Z.eqb_eq in Hi0; rewrite Hi0; lia ]. }
  subst si.
  pose proof P as P'. destruct P' as [pp pe pr pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. subst pp pe pr pq.
  (* [comment removed for export] *)
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
  assert (Epa : edenot E (reg cs 10) = Z_to_bv 64 (st + 16 * o)).
  { assert (Ep : edenot E (sl_p s) = edenot E (reg cs 10)).
    { destruct (expr_eqb (sl_p s) (reg cs 10)) eqn:Heq.
      - apply expr_eqb_eq in Heq. rewrite Heq. reflexivity.
      - exact (len_eqb_sound E M (kn cs) _ _ HKN Hsp). }
    rewrite <- Ep, <- Hp. symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Epa in R10.
  (* [comment removed for export] *)
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  set (spv := bv_unsigned (edenot E (reg cs 2))) in *.
  pose proof (elo_sound E M (kn cs) (reg cs 2) splo HKN Hsplo) as Hsplo'. fold spv in Hsplo'.
  pose proof (u64_range (edenot E (reg cs 2))) as Hspr. fold spv in Hspr.
  assert (R2' : getr R (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 spv) by (rewrite R2; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  destruct (rw_okb_sound E M (kn cs) qb qk 48 HKN Hstk ltac:(lia)) as (Qst & Qdef & Qimg & Q0 & Qnw).
  assert (Hspm : edenot E spm = Z_to_bv 64 (spv - 48)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold spv. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hq1. rewrite Hspm in Hq1.
  apply (f_equal bv_unsigned) in Hq1. rewrite !u64_lit in Hq1 by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (flat_b_sound E M (kn cs) gb gk 40 HKN Hflg) as Fg.
  pose proof (split_lit_denot E ge gb gk Hsg) as Hgd.
  set (g := (bv_unsigned (edenot E gb) + gk)%Z) in *.
  assert (Fg' : (0 <= g)%Z /\ (g + 40 <= 2 ^ 64)%Z) by (destruct Fg as (F1 & F2 & F3 & F4); unfold estart in *; cbn [a_base a_off] in *; lia).
  assert (Hug : bv_unsigned (edenot E ge) = g) by (rewrite Hgd, u64_lit by lia; reflexivity).
  pose proof (ehi_sound E M (kn cs) ge ghi HKN Hghi) as Hghi'. rewrite Hug in Hghi'.
  (* [comment removed for export] *)
  assert (Hg88 : (g + 88 <= spv)%Z).
  { apply orb_prop in Hs2 as [Hs2|Hs2].
    - apply Z.leb_le in Hs2. lia.
    - pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HKN Hs2) as X. cbn [xt_den] in X. rewrite Hug in X. fold spv in X. lia. }
  clear Hs2.
  (* [comment removed for export] *)
  set (Mz := (st - 16 - stride * idx)%Z).
  pose proof (flat_b_sound E M (kn cs) mb mk 8 HKN Hflm) as Fm.
  assert (HMe_d : edenot E Me = Z_to_bv 64 Mz).
  { subst Me. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold st. rewrite Z.add_mod_idemp_r by lia. f_equal. subst Mz. lia. }
  assert (Amb : adenot E (SA mb mk) = Z_to_bv 64 Mz).
  { rewrite adenot_Z, <- (split_lit_denot E Me mb mk Hsme). exact HMe_d. }
  pose proof (kread8e_rdn E M (kn cs) mb mk ge HKN Hge Fm) as Rmeta. rewrite Amb in Rmeta.
  (* [comment removed for export] *)
  assert (A16 : adenot E (SA gb (gk + 16)) = Z_to_bv 64 (g + 16)) by (rewrite adenot_Z; f_equal; subst g; lia).
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 16) Me' HKN HMe' ltac:(eapply flat_sub; [exact Fg| lia | lia | lia])) as Rmem.
  rewrite A16 in Rmem. rewrite (len_eqb_sound E M (kn cs) _ _ HKN HMe), HMe_d in Rmem.
  (* [comment removed for export] *)
  assert (A32 : adenot E (SA gb (gk + 32)) = Z_to_bv 64 (g + 32)) by (rewrite adenot_Z; f_equal; subst g; lia).
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 32) We HKN HWe ltac:(eapply flat_sub; [exact Fg| lia | lia | lia])) as RW.
  rewrite A32 in RW. rewrite Hw in RW. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (sl_W s))) in RW. fold W in RW.
  (* [comment removed for export] *)
  assert (A24 : adenot E (SA gb (gk + 24)) = Z_to_bv 64 (g + 24)) by (rewrite adenot_Z; f_equal; subst g; lia).
  assert (A28 : adenot E (SA gb (gk + 28)) = Z_to_bv 64 (g + 28)) by (rewrite adenot_Z; f_equal; subst g; lia).
  destruct (kreadZ_rdn E M (kn cs) gb (gk + 24) 4 avail HKN Hav ltac:(lia) ltac:(eapply flat_sub; [exact Fg| lia | lia | lia])) as [Rav Hav_r].
  destruct (kreadZ_rdn E M (kn cs) gb (gk + 28) 4 freed HKN Hfr ltac:(lia) ltac:(eapply flat_sub; [exact Fg| lia | lia | lia])) as [Rfr Hfr_r].
  rewrite A24, wle_low4 in Rav. rewrite A28, wle_low4 in Rfr.
  (* [comment removed for export] *)
  destruct (lin_lowbits_kn_sound RSEGS E M (kn cs) ge 12 gm12 HKN ltac:(lia) Hlow) as [Hgm Hgm_r]. rewrite Hug in Hgm.
  change (2 ^ 12)%Z with 4096%Z in Hgm, Hgm_r.
  pose proof (flat_b_sound E M (kn cs) ab ak 8 HKN Hfla) as Fa.
  assert (Aar : adenot E (SA ab ak) = Z_to_bv 64 (g - g mod 4096)).
  { rewrite adenot_Z, <- (split_lit_denot E area ab ak Hsa). subst area. rewrite mkAlu_denot. cbn [edenot].
    rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Hug.
    rewrite Z.add_mod_idemp_r by lia. f_equal. lia. }
  pose proof (kread8e_rdn E M (kn cs) ab ak se HKN Hse Fa) as Rar. rewrite Aar in Rar.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) 0xe5428 se HKN Hse' ltac:(apply flat_abs; lia)) as Rsec.
  rewrite adenot_Z in Rsec. cbn [edenot] in Rsec. rewrite (u64_lit 0) in Rsec by lia. cbn [Z.add] in Rsec.
  (* [comment removed for export] *)
  pose proof (flat_b_sound E M (kn cs) hb (hk - 4) (shi + 5) HKN Hflh) as Fh.
  destruct (rw_okb_sound E M (kn cs) eb ek 1 HKN Hrwe ltac:(lia)) as (_ & Edef & _ & E0 & Enw).
  destruct (kreadZ_rdn E M (kn cs) eb ek 1 0 HKN ltac:(destruct (kreadZ RSEGS (kn cs) eb ek 1) as [z|]; [destruct z; try discriminate; reflexivity | discriminate])
              ltac:(lia) ltac:(unfold flat, estart; cbn [a_base a_off]; lia)) as [Rend _].
  rewrite adenot_Z, w2lb1 in Rend.
  assert (Aee : Z_to_bv 64 (bv_unsigned (edenot E eb) + ek) = (Z_to_bv 64 (st + stride - 4) : word)).
  { rewrite <- (split_lit_denot E eexp eb ek Hsee). subst eexp. rewrite mkAlu_denot. cbn [edenot]. rewrite mkAlu_denot. cbn [edenot].
    rewrite !alu_add. unfold v_add. rewrite !alu_add. unfold v_add. fold st stride. apply eqm_Z_to_bv.
    pose proof (eqm_u_lit (stride + bv_unsigned (Z_to_bv 64 (-4)))) as [q1 H1].
    pose proof (eqm_u_lit (-4)) as [q2 H2].
    exists (q1 + q2)%Z. lia. }
  assert (Mend : M (Z_to_bv 64 (st + stride - 4)) = Some (Z_to_bv 8 0)).
  { rewrite <- Aee. specialize (Edef 0 ltac:(lia)). rewrite Z.add_0_r in Edef.
    destruct (M (Z_to_bv 64 (bv_unsigned (edenot E eb) + ek))) as [b|] eqn:HMb; [|contradiction].
    cbn [rdn] in Rend. rewrite HMb in Rend. cbn in Rend. congruence. }
  (* [comment removed for export] *)
  assert (IMG : sz_img M).
  { rewrite DSC_eq in Himg. unfold kimg_covers in Himg. apply existsb_exists in Himg as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKimg. cbn [kentry_ok] in HKimg. destruct HKimg as (_ & _ & Hnone).
    intros i Hi. apply Hnone. lia. }
  (* [comment removed for export] *)
  pose proof (xlo_sound RSEGS E M (kn cs) (sl_off s) olo HKN Holo) as Holo'. fold o in Holo'.
  pose proof (xhi_sound RSEGS E M (kn cs) (sl_off s) ohi HKN Hohi) as Hohi'. fold o in Hohi'.
  pose proof (ehi_sound E M (kn cs) hb hh HKN Hhh) as Hhh'.
  (* [comment removed for export] *)
  assert (HE4 : (st + stride - 4 + 4 <= spv - 48)%Z).
  { destruct Fh as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F3, F4; cbn [a_base a_off] in F1, F2, F3, F4.
    destruct (hh + hk + shi + 48 <=? splo) eqn:Hnum.
    - apply Z.leb_le in Hnum. lia.
    - (* [comment removed for export] *)
      apply andb_prop in Hs1 as [Hs1 Hc48]. apply andb_prop in Hs1 as [Hkd Hhi]. apply Z.leb_le in Hhi.
      pose proof (kdisj_apart_x_sound RSEGS E M (kn cs) (kn cs) _ _ _ _ _ _ HKN HKN Hkd) as Hd.
      unfold estart in Hd; cbn [a_base a_off edenot] in Hd.
      rewrite (elenZ_lit E 4), (elenZ_lit E STKTOP) in Hd by (unfold SP.STKTOP; lia).
      destruct (lin_inside_sound E M (kn cs) qb qk 48 (EVar SP0V) (- STKWIN) STKWIN HKN Hc48) as [I1 I2].
      unfold estart in I1, I2; cbn [a_base a_off edenot] in I1, I2.
      pose proof (vo_sp0w _ _ _ _ _ (co_vm _ _ _ _ _ HC)) as Hsp0w. rewrite (vo_sp0 _ _ _ _ _ (co_vm _ _ _ _ _ HC)) in Hsp0w.
      assert (Eek : (bv_unsigned (edenot E eb) + ek = st + stride - 4)%Z).
      { pose proof Aee as A. apply (f_equal bv_unsigned) in A. rewrite !u_small in A; [exact A | | ];
        unfold flat, estart in E0, Enw; cbn [a_base a_off] in E0, Enw; lia. }
      rewrite Eek in Hd. unfold SP.STKTOP, SP.STKWIN, sp_window_lo, sp_window_hi in *. lia. }
  (* [comment removed for export] *)
  set (e := (st + stride - 4)%Z). set (r := (stride - 4 - nn - 16 * o)%Z). set (q := (stride * idx / 16 + o)%Z).
  assert (PRE : free_pre M spv (st + 16 * o) e Mz g idx o nn stride r q W (avail mod 2 ^ 32) (freed mod 2 ^ 32) (edenot E se)).
  { constructor.
    - exact Hsd.
    - subst Mz. lia.
    - subst e Mz. lia.
    - reflexivity.
    - reflexivity.
    - replace (st + 16 * o)%Z with (st + o * 16)%Z by lia. rewrite Z.mod_add by lia. exact Hmod2.
    - subst Mz. nia.
    - rewrite Fli. lia.
    - lia.
    - lia.
    - subst r. lia.
    - subst q. lia.
    - lia.
    - lia.
    - (* [comment removed for export] *)
      rewrite Fsc, Fml, Fli. subst q.
      apply orb_prop in Hsc as [Hsc|Hsc].
      + left. apply andb_prop in Hsc as [Hsc H3]. apply andb_prop in Hsc as [H1 H2].
        apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia.
      + right. apply andb_prop in Hsc as [Hsc H3]. apply andb_prop in Hsc as [H1 H2].
        apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. lia.
    - intros Hml0. rewrite Fml in Hml0. subst q.
      apply orb_prop in Hml as [Hml|Hml]; [apply Z.eqb_eq in Hml; lia | apply Z.leb_le in Hml; rewrite Fml].
      clear - Hml Hohi' HSlo'. nia.
    - apply Z.mod_pos_bound. lia.
    - rewrite testbit_mod32 by lia. exact Havb.
    - apply Z.mod_pos_bound. lia.
    - rewrite testbit_mod32 by lia. exact Hfrb.
    - lia.
    - subst e. lia.
    - rewrite Hq1. exact Qst.
    - exact Pm4.
    - exact Pm3.
    - exact Pm2.
    - exact Pzr.
    - exact Pe5.
    - exact Pe4.
    - exact Mend.
    - rewrite <- Hug, Z_to_bv_bv_unsigned. exact Rmeta.
    - exact Rmem.
    - exact RW.
    - exact Rav.
    - exact Rfr.
    - exact Rar.
    - exact Rsec.
    - exact IMG. }
  (* [comment removed for export] *)
  destruct (ref_free_pro R M (seg_rom RSEGS) spv (st + 16 * o) e Mz g idx o nn stride r q W _ _ _ PRE R2' R10)
    as (R' & Hms & G2 & G9 & G8 & G10 & G11 & G14 & G15 & G18 & G19 & G3 & G4 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  set (M1 := free_mem1 M spv (getr R 1) (getr R 8) (getr R 9) (getr R 18) (getr R 19)) in Hms.
  (* [comment removed for export] *)
  assert (LF : log_flat E log).
  { subst log. cbn [log_flat]. unfold flat, estart; cbn [a_base a_off]. repeat split; try lia. }
  assert (HM1 : mem_denot E M log = M1).
  { subst log M1. cbn [mem_denot]. unfold free_mem1.
    rewrite !adenot_Z.
    rewrite <- (reg_sound E cs R M model 19 HC ltac:(lia)), <- (reg_sound E cs R M model 18 HC ltac:(lia)),
            <- (reg_sound E cs R M model 9 HC ltac:(lia)), <- (reg_sound E cs R M model 8 HC ltac:(lia)),
            <- (reg_sound E cs R M model 1 HC ltac:(lia)).
    replace (bv_unsigned (edenot E qb) + (qk + 8))%Z with (spv - 40)%Z by lia.
    replace (bv_unsigned (edenot E qb) + (qk + 16))%Z with (spv - 32)%Z by lia.
    replace (bv_unsigned (edenot E qb) + (qk + 24))%Z with (spv - 24)%Z by lia.
    replace (bv_unsigned (edenot E qb) + (qk + 32))%Z with (spv - 16)%Z by lia.
    replace (bv_unsigned (edenot E qb) + (qk + 40))%Z with (spv - 8)%Z by lia.
    reflexivity. }
  pose proof (carry_sound RSEGS E M M log (kn cs) [] kn' [] hs Hcar LF HKN ltac:(constructor)) as HK1. rewrite HM1 in HK1.
  (* [comment removed for export] *)
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh Hnx0]. apply andb_prop in Hfresh as [Hfresh Hslv].
  apply andb_prop in Hfresh as [Hfresh Hmv]. apply andb_prop in Hfresh as [Hsv Hkv0]. apply Nat.leb_le in Hnx0.
  set (nx := s_next (c_ss cs)) in *.
  set (E' := ext_call E nx R').
  pose proof (ext_call_agree E nx R') as Hag. fold E' in Hag.
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_freepro U0)) with (0x98a54%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  specialize (HK E' R' M1 ltac:(eapply env_agree_le; [exact Hag | exact (max1_le_l _ _ Hnx0)])).
  rewrite Ecs in HK. unfold cfg_of in HK. cbn [pc c_ss s_pc] in HK.
  replace (Z_to_bv 64 (t_freepro_k U0)) with (0x98b30%bv : word) in HK by (apply bv_eq; reflexivity).
  apply HK. clear HK.
  destruct HC as [HR HKc HL Hhalt Hlz Hmt Hfd HV HSLc HLIB].
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - (* [comment removed for export] *)
    change (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_fresh (s_regs (c_ss cs)) caller_saved nx) 2 spm) 9 (reg cs 10))
              8 (ELit idx)) 10 ge) 11 We) 14 reserved) 15 e12)
      with (sr_upds (sr_fresh (s_regs (c_ss cs)) caller_saved nx)
              [(2%nat, spm); (9%nat, reg cs 10); (8%nat, ELit idx); (10%nat, ge); (11%nat, We); (14%nat, reserved); (15%nat, e12)]).
    apply andb_prop in Hvars as [Hvars VWe]. apply andb_prop in Hvars as [Hvars Vpa]. apply andb_prop in Hvars as [Hvars Ve12].
    apply andb_prop in Hvars as [Hvars Vres]. apply andb_prop in Hvars as [Vge Vspm].
    assert (Eres : edenot E reserved = Z_to_bv 64 r).
    { subst reserved. rewrite mkAlu_denot. cbn [edenot]. rewrite ?mkAlu_denot. cbn [edenot]. rewrite ?mkAlu_denot. cbn [edenot]. rewrite times16_denot.
      fold o. rewrite !alu_sub, !alu_add. unfold v_sub, v_add. rewrite ?alu_add. unfold v_add. fold nn stride.
      apply eqm_Z_to_bv. subst r.
      pose proof (eqm_u_lit (stride + bv_unsigned (Z_to_bv 64 (-4)))) as [q1 H1]. pose proof (eqm_u_lit (-4)) as [q4 H4].
      pose proof (eqm_u_lit (16 * o)) as [q2 H2].
      pose proof (eqm_u_lit (nn + bv_unsigned (Z_to_bv 64 (16 * o)))) as [q3 H3].
      exists (q1 + q4 - q3 - q2)%Z. clear - H1 H2 H3 H4. lia. }
    assert (Ee12 : edenot E e12 = Z_to_bv 64 (e - 12)).
    { subst e12. rewrite !mkAlu_denot. cbn [edenot]. rewrite ?mkAlu_denot. cbn [edenot]. rewrite !alu_add. unfold v_add.
      rewrite ?alu_add. unfold v_add. fold st stride. apply eqm_Z_to_bv. subst e.
      pose proof (eqm_u_lit (stride + bv_unsigned (Z_to_bv 64 (-16)))) as [q1 H1]. pose proof (eqm_u_lit (-16)) as [q2 H2].
      exists (q1 + q2)%Z. lia. }
    apply (regs_after_ovr E (s_regs (c_ss cs)) R R' nx); [exact HR | exact Hsv | |  |].
    + cbn [map fst]. repeat (constructor; [cbn [In]; lia|]). constructor.
    + intros io Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd]; split;
        first [ exact Vspm | exact Vpa | exact Vge | exact Vres | exact Ve12 | exact VWe | reflexivity | idtac ].
      * replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G2, Hspm. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G9, Epa. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G8. cbn [edenot]. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10, <- Hug, Z_to_bv_bv_unsigned. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G11, Hw. subst W. rewrite Z_to_bv_bv_unsigned. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G14, Eres. reflexivity.
      * replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G15, Ee12. reflexivity.
    + intros rr Hr0 Hncs Hnov. cbn [map fst In] in Hnov. unfold caller_saved in Hncs. cbn [In] in Hncs.
      pose proof (ridx_range rr) as Hrr.
      assert (KEPT : forall k : nat, In k [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
                     getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
      { intros k Hk. cbn [In] in Hk.
        destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
          lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
            first [ replace (Z_to_bv 5 (Z.of_nat k)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                  | replace (Z_to_bv 5 (Z.of_nat k)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
          end. }
      rewrite (reg_of_ridx rr _ eq_refl). apply KEPT. cbn [In].
      assert (Hz : ridx rr <> 0%nat).
      { intros X. apply Hr0. rewrite (reg_of_ridx rr 0%nat X). apply bv_eq. reflexivity. }
      lia.
  - eapply know_ok_ext; [exact Hag | exact Hkv | exact HK1].
  - reflexivity.
  - exact Hhalt.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - eapply vm_ok_ext; [exact Hag | exact Hmv | | exact HV].
    (* [comment removed for export] *) match goal with H : Nat.leb (Nat.max 1 nx0) _ = true |- _ => apply Nat.leb_le in H; exact (max1_le_0 _ _ H) | H : (Nat.max 1 nx0 <= _)%nat |- _ => exact (max1_le_0 _ _ H) end.
  - eapply slots_ok_ext; [exact Hag | |].
    + apply slots_vars_lt_carry. unfold remove_slot. apply slots_vars_lt_filter. exact Hslv.
    + rewrite <- HM1. eapply slots_carry_sound; [exact HK1 | exact LF | apply slots_ok_filter; exact HSLc].
  - (* [comment removed for export] *)
    eapply lib_ok_frame; [|exact HLIB]. intros a Ha. unfold HULL_LO, HULL_HI in Ha; cbn in Ha.
    subst M1. unfold free_mem1.
    repeat (rewrite MemSplit.wbytes_outside; [| rewrite length_N_to_le_bytes, u64_lit by lia; lia | rewrite length_N_to_le_bytes, !u64_lit by lia; lia]).
    reflexivity.
Qed.

#[using="Type"] Theorem call_freepro_ok_fx : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_freepro U0 -> call_freepro RSEGS U0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof. exact call_freepro_sound'. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End NX0.

(* [comment removed for export] *)
Theorem call_freepro_ok : forall nx0, freepro_sound_stmt nx0.
Proof. intros nx0  fx. exact (call_freepro_ok_fx nx0 ). Qed.
