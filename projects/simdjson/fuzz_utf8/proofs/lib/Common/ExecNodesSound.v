(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import SymStepR AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesAux. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArgSound ExecNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import EXN.
Open Scope Z_scope.

Module EXNS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pure.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma le_val_bytes : forall bs, le_val (map bv_unsigned bs) = bytes_le_to_Z bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map le_val bytes_le_to_Z]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma scan_sound : forall kl B sx n step cnt a acc mn mx,
  scan segs kl B sx n a step cnt acc = Some (mn, mx) ->
  (match acc with Some (m0, m1) => mn <= m0 /\ m1 <= mx | None => True end) /\
  forall u j, 0 <= j < Z.of_nat cnt -> u = a + step * j -> exists v, elem_val segs kl B sx n u = Some v /\ mn <= v <= mx.
Proof.
  intros kl B sx n step cnt. induction cnt as [|c IH]; intros a acc mn mx Hs.
  - cbn in Hs. subst acc. split; [lia|]. intros u j Hj. lia.
  - cbn [scan] in Hs. destruct (elem_val segs kl B sx n a) as [v|] eqn:Hv; [|discriminate].
    destruct acc as [[m0 m1]|].
    + destruct (IH (a + step) (Some (Z.min m0 v, Z.max m1 v)) mn mx Hs) as [Hacc Hall]. split; [lia|].
      intros u j Hj Hu. destruct (Z.eq_dec j 0) as [->|Hne].
      * rewrite Z.mul_0_r, Z.add_0_r in Hu. subst u. exists v. split; [exact Hv | lia].
      * apply (Hall u (j - 1)); lia.
    + destruct (IH (a + step) (Some (v, v)) mn mx Hs) as [Hacc Hall]. split; [exact I|].
      intros u j Hj Hu. destruct (Z.eq_dec j 0) as [->|Hne].
      * rewrite Z.mul_0_r, Z.add_0_r in Hu. subst u. exists v. split; [exact Hv | lia].
      * apply (Hall u (j - 1)); lia.
Qed.

Lemma know_bytes_lit_length : forall kl B k n zs, know_bytes_lit segs kl B k n = Some zs -> length zs = n.
Proof.
  intros kl B k n. revert k. induction n as [|n IH]; intros k zs H.
  - cbn in H. injection H as <-. reflexivity.
  - cbn [know_bytes_lit] in H. destruct (know_byte_lit segs kl B k); [|discriminate].
    destruct (know_bytes_lit segs kl B (k + 1) n) eqn:Hr; [|discriminate]. injection H as <-. cbn. f_equal. eapply IH. exact Hr.
Qed.

(* [comment removed for export] *)
Definition macc_ok (acc : option (option Z)) (b : Z) : Prop :=
  match acc with None => True | Some o => match o with None => False | Some b0 => b0 = b end end.
Lemma scan_mask_sound : forall kl B sx n step cnt m a acc b,
  scan_mask segs kl B sx n a step cnt m acc = Some (Some b) ->
  macc_ok acc b /\
  forall u j, 0 <= j < Z.of_nat cnt -> u = a + step * j -> exists v, elem_val segs kl B sx n u = Some v /\ Z.land v m = b.
Proof.
  intros kl B sx n step cnt m. induction cnt as [|c IH]; intros a acc b Hs.
  - cbn in Hs. split; [|intros u j Hj; lia]. destruct acc as [[b0|]|]; [injection Hs as ->; reflexivity | discriminate | discriminate].
  - cbn [scan_mask] in Hs. destruct (elem_val segs kl B sx n a) as [v|] eqn:Hv; [|discriminate].
    assert (STEP : forall acc', scan_mask segs kl B sx n (a + step) step c m acc' = Some (Some b) ->
              macc_ok acc' b ->
              Z.land v m = b ->
              forall u j, 0 <= j < Z.of_nat (S c) -> u = a + step * j -> exists v0, elem_val segs kl B sx n u = Some v0 /\ Z.land v0 m = b).
    { intros acc' Hs' _ Hb u j Hj Hu. destruct (IH (a + step) acc' b Hs') as [_ Hall].
      destruct (Z.eq_dec j 0) as [->|Hne].
      - rewrite Z.mul_0_r, Z.add_0_r in Hu. subst u. exists v. split; [exact Hv | exact Hb].
      - apply (Hall u (j - 1)); lia. }
    destruct acc as [[b0|]|].
    + destruct (Z.eqb_spec b0 (Z.land v m)) as [E|NE].
      * destruct (IH _ _ _ Hs) as [Hb0 _]. cbn in Hb0. split; [exact Hb0|]. apply (STEP _ Hs); [exact Hb0 | congruence].
      * destruct (IH _ _ _ Hs) as [F _]. cbn in F. destruct F.
    + destruct (IH _ _ _ Hs) as [F _]. cbn in F. destruct F.
    + destruct (IH _ _ _ Hs) as [Hb0 _]. cbn in Hb0. split; [exact I|]. apply (STEP _ Hs); [exact Hb0 | exact Hb0].
Qed.

End Pure.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
  Context {fx : FPState}.
  Variable SEGS : list Segment.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound SEGS IT.
  Variable A : atable.
  Variable nx0 : nat.
  Hypothesis NX0_min : APS.nx0_min_ok nx0.   (* [comment removed for export] *)
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  (* [comment removed for export] *)
  Hypothesis SEGS_wr : forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).

  (* [comment removed for export] *)
  Lemma seg_rom_in_hull : forall a : word, seg_rom SEGS a <> None -> in_hull A (bv_unsigned a) = true.
  Proof.
    intros a H. destruct (in_hull A (bv_unsigned a)) eqn:Hh; [reflexivity|]. exfalso. apply H.
    exact (seg_rom_off_hull SEGS A SEGS_in_hull a Hh).
  Qed.

  Lemma hid_hull : forall E cs model (a : word), in_hull A (bv_unsigned a) = true -> hid A argH E cs model a = false.
  Proof.
    intros E cs model a Hh. unfold hid. rewrite (proj2 (negb_false_iff _)).
    2: { unfold vis. rewrite Hh. reflexivity. }
    rewrite orb_false_r. destruct (argH E a) eqn:Ha; [|reflexivity]. exfalso.
    pose proof (argH_high E a Ha) as Hc. unfold in_hull in Hh. apply andb_prop in Hh as [_ Hh]. apply Z.ltb_lt in Hh.
    pose proof HULL_ok as HU. unfold hull_ok in HU. unfold AP.CEIL, APC.CEIL, AP.KHI, APC.KHI in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem node_tabread_soundF : forall args,
    node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_tabread SEGS IT nx0 cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_tabread in Hn.
    destruct (fresh_ok nx0 cs && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64)%bool eqn:Hg; [|discriminate]. cbn [negb] in Hn.
    apply andb_prop in Hg as [Hg Hp4]. apply andb_prop in Hg as [Hfresh Hp0]. apply Z.leb_le in Hp0. apply Z.ltb_lt in Hp4.
    destruct (itab_lookup IT (pc cs)) as [ins|] eqn:Hit; [|discriminate].
    destruct ins; try discriminate. rename sz into sz0. rename signed into sx. rename rd into rd'. rename rs1 into rs. rename imm into imm'.
    destruct (bv_eqb rd' 0%bv) eqn:Hrd; [discriminate|].
    set (n := load_width sz0) in Hn.
    set (sx' := match sz0 with SZ8 => false | _ => sx end) in Hn.
    set (e := mkAlu ALU_ADD (sr_get (s_regs (a_ss cs)) rs) (ELit (bv_signed imm'))) in Hn.
    set (msk := match args with [_; ELit m] => if (Z.leb 0 m && Z.ltb m two64)%bool then Some m else None | _ => None end) in Hn.
    destruct (match args with [] => Some (ELit 0, e) | [B] | [B; ELit _] => Some (B, mkAlu ALU_SUB e B) | _ => None end)
      as [[B X]|] eqn:HBX; [|discriminate].
    assert (CASEB : (B = ELit 0 /\ X = e) \/ X = mkAlu ALU_SUB e B).
    { destruct args as [|B0 [|m0 [|? ?]]]; cbn in HBX.
      - injection HBX as E1 E2. left. subst. split; reflexivity.
      - injection HBX as E1 E2. right. subst. reflexivity.
      - destruct m0; try discriminate HBX. injection HBX as E1 E2. right. subst. reflexivity.
      - destruct m0; discriminate HBX. }
    destruct (split_lit B) as [Bb Bo] eqn:HsplB.
    destruct (xlo (kn cs) X) as [xl|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) X) as [xh|] eqn:Hxh; [|discriminate].
    destruct (xlo (kn cs) B) as [bl|] eqn:Hbl; [|discriminate].
    destruct (xhi (kn cs) B) as [bh|] eqn:Hbh; [|discriminate].
    destruct (xlo (kn cs) Bb) as [bbl|] eqn:Hbbl; [|discriminate].
    destruct (xhi (kn cs) Bb) as [bbh|] eqn:Hbbh; [|discriminate].
    set (st := 2 ^ stride_log (kn cs) X xl) in Hn. set (cnt := (xh - xl) / st + 1) in Hn.
    destruct (Z.leb 0 xl && Z.leb xl xh && Z.leb cnt TAB_CAP && Z.leb 0 (bl + xl) && Z.leb (bh + xh + Z.of_nat n) two64
              && Z.leb 0 (bbl + Bo) && Z.ltb (bbh + Bo) two64)%bool eqn:Hc;
      [|discriminate]. cbn [negb] in Hn.
    apply andb_prop in Hc as [Hc Hbbhi]. apply andb_prop in Hc as [Hc Hbblo].
    apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Hlo]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hxl0 Hlohi].
    apply Z.leb_le in Hlohi. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.leb_le in Hxl0. apply Z.leb_le in Hbblo. apply Z.ltb_lt in Hbbhi.
    set (kl := List.filter (tab_entry Bb) (kn cs)) in Hn.
    destruct (scan SEGS kl Bb sx' n (Bo + xl) st (Z.to_nat cnt) None) as [[mn mx]|] eqn:Hscan; [|discriminate].
    set (rv := if Z.eqb mn mx then ELit mn else EVar (nxt cs)) in Hn.
    set (mfact := match msk with
                  | Some m => if Z.eqb mn mx then [] else
                              match scan_mask SEGS kl Bb sx' n (Bo + xl) st (Z.to_nat cnt) m None with
                              | Some (Some b) => [KRange (mkAlu ALU_AND rv (ELit m)) b b]
                              | _ => []
                              end
                  | None => [] end) in Hn.
    injection Hn as <-.
    (* [comment removed for export] *)
    pose proof (IT_ok _ _ Hit) as Hentry. unfold itab_entry in Hentry.
    destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
    destruct (is_ecall w) eqn:Hec; [discriminate|].
    destruct (decode_any w) as [[ins isz]|] eqn:Hd; [|discriminate].
    destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz. injection Hentry as ->.
    (* [comment removed for export] *)
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    set (H := hid A argH E cs model). set (MR := Mr A argH E cs model FULL).
    assert (HKl : know_ok SEGS E MR kl).
    { unfold kl, know_ok. apply incl_Forall with (l1 := kn cs); [apply incl_filter | exact HK]. }
    (* [comment removed for export] *)
    set (av := v_addi (getr R rs) (bv_signed imm')).
    assert (Hav : edenot E e = av).
    { unfold e, av, v_addi. rewrite mkAlu_denot. cbn [edenot]. rewrite <- (HR rs). rewrite alu_add. unfold v_add.
      apply bv_eq. rewrite !u_lit64. unfold two64. rewrite Zplus_mod_idemp_r. reflexivity. }
    set (u := bv_unsigned av). set (uB := bv_unsigned (edenot E B)). set (uX := bv_unsigned (edenot E X)).
    set (uBb := bv_unsigned (edenot E Bb)).
    pose proof (xlo_sound SEGS E _ (kn cs) X xl HK Hxl) as HxlS. pose proof (xhi_sound SEGS E _ (kn cs) X xh HK Hxh) as HxhS.
    pose proof (xlo_sound SEGS E _ (kn cs) B bl HK Hbl) as HblS. pose proof (xhi_sound SEGS E _ (kn cs) B bh HK Hbh) as HbhS.
    pose proof (xlo_sound SEGS E _ (kn cs) Bb bbl HK Hbbl) as HbblS. pose proof (xhi_sound SEGS E _ (kn cs) Bb bbh HK Hbbh) as HbbhS.
    fold uX in HxlS, HxhS. fold uB in HblS, HbhS. fold uBb in HbblS, HbbhS.
    (* [comment removed for export] *)
    assert (HuB : uB = uBb + Bo).
    { unfold uB. rewrite (split_lit_denot E B Bb Bo HsplB). fold uBb. rewrite u_lit64. unfold two64 in *. apply Z.mod_small. lia. }
    assert (Hn18 : (1 <= n)%nat /\ (n <= 8)%nat) by (unfold n; destruct sz0; cbn; lia). destruct Hn18 as [Hn1 Hn8].
    assert (HBXv : Z_to_bv 64 (uB + uX) = av /\ u = uB + uX).
    { pose proof (u64_range av) as Hur. fold u in Hur.
      assert (Heq : Z_to_bv 64 (uB + uX) = av).
      { destruct CASEB as [[EB EX] | EX]; [subst B X | subst X].
        - unfold uB, uX. cbn [edenot]. rewrite u_lit64, Hav. unfold two64. rewrite Z.mod_0_l by lia. rewrite Z.add_0_l.
          apply Z_to_bv_bv_unsigned.
        - unfold uB, uX. rewrite mkAlu_denot. cbn [edenot]. rewrite Hav, u_sub64.
          clearbody av. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          rewrite Zplus_mod_idemp_r. replace (bv_unsigned (edenot E B) + (bv_unsigned av - bv_unsigned (edenot E B)))
            with (bv_unsigned av) by lia. apply Z.mod_small. apply u64_range. }
      split; [exact Heq|]. unfold u. rewrite <- Heq, u_lit64. unfold two64 in *. apply Z.mod_small. lia. }
    destruct HBXv as [HBXv Hu].
    assert (Hfl : flat E (SA Bb (Bo + uX)) (Z.of_nat n)).
    { unfold flat, estart. cbn [a_base a_off]. fold uBb. unfold two64 in Hhi. lia. }
    assert (Hadr : adenot E (SA Bb (Bo + uX)) = av).
    { unfold adenot, v_addi. cbn [a_base a_off]. fold uBb. rewrite <- HBXv. f_equal. lia. }
    (* [comment removed for export] *)
    destruct (scan_sound SEGS kl Bb sx' n st _ _ _ _ _ Hscan) as [_ Hall].
    (* [comment removed for export] *)
    assert (Hst : 0 < st /\ (st | uX - xl)).
    { unfold st, stride_log.
      destruct (ealign_sound SEGS E _ (kn cs) (mkAlu ALU_SUB X (ELit xl)) HK) as [Hal Hdiv].
      rewrite mkAlu_denot in Hdiv. cbn [edenot] in Hdiv. rewrite u_sub64, u_lit64 in Hdiv. fold uX in Hdiv. unfold two64 in Hdiv.
      rewrite Zminus_mod_idemp_r, (Z.mod_small (uX - xl)) in Hdiv by (pose proof (u64_range (edenot E X)) as UXR; fold uX in UXR; lia).
      split; [apply Z.pow_pos_nonneg; lia|].
      eapply Z.divide_trans; [|exact Hdiv]. exists (2 ^ (ealign (kn cs) (mkAlu ALU_SUB X (ELit xl)) - Z.min 6 (ealign (kn cs) (mkAlu ALU_SUB X (ELit xl))))).
      rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    destruct Hst as [Hst0 [q Hq]].
    assert (Hcnt : 0 <= q < Z.of_nat (Z.to_nat cnt)).
    { rewrite Z2Nat.id by (unfold cnt; pose proof (Z.div_pos (xh - xl) st ltac:(lia) Hst0); lia). unfold cnt.
      assert (0 <= q) by (apply (Z.mul_nonneg_cancel_r q st Hst0); lia).
      split; [lia|]. apply Zle_lt_succ. rewrite <- (Z.div_mul q st) by lia. apply Z.div_le_mono; lia. }
    destruct (Hall (Bo + uX) q Hcnt ltac:(lia)) as (v & Hev & Hvb).
    (* [comment removed for export] *)
    assert (Hmask : forall m b, scan_mask SEGS kl Bb sx' n (Bo + xl) st (Z.to_nat cnt) m None = Some (Some b) -> Z.land v m = b).
    { intros m b Hsm. destruct (scan_mask_sound SEGS kl Bb sx' n st _ m _ _ b Hsm) as [_ HallM].
      destruct (HallM (Bo + uX) q Hcnt ltac:(lia)) as (v' & Hev' & Hb'). rewrite Hev in Hev'. injection Hev' as <-. exact Hb'. }
    unfold elem_val in Hev. destruct (know_bytes_lit SEGS kl Bb (Bo + uX) n) as [zs|] eqn:Hkb; [|discriminate].
    destruct (know_bytes_lit_sound SEGS E MR kl Bb n (Bo + uX) zs HKl Hkb Hfl) as (bs & Hrdn & Hmap).
    pose proof (know_bytes_lit_length SEGS kl Bb (Bo + uX) n zs Hkb) as Hlen. rewrite <- Hmap, length_map in Hlen.
    rewrite Hadr in Hrdn.
    (* [comment removed for export] *)
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    set (val := load_result sz0 sx bs).
    assert (Hn8' : n = SymStepR.msize_bytes sz0) by (unfold n; destruct sz0; reflexivity).
    pose proof (stepR_load SEGS R (Z_to_bv 64 (pc cs)) MR (seg_rom SEGS) None w sz0 sx rd' rs imm' bs Hf Hec Hd
                  ltac:(rewrite <- Hn8'; exact Hrdn)) as STEP.
    rewrite Hrd in STEP. rewrite v_addi_lit in STEP by (unfold two64 in *; lia). rewrite !mkstR_None in STEP. fold val in STEP.
    assert (Hms' : msteps SEGS (restrict H ms) (mkst (regupd R rd' val) (Z_to_bv 64 (pc cs + 4)) MR (seg_rom SEGS))).
    { unfold ms, MR, Mr. rewrite restrict_mkst. eapply mst_step; [reflexivity | exact STEP | apply mst_refl]. }
    (* [comment removed for export] *)
    assert (HnA : n = AX2.msize_bytes sz0) by (unfold n; destruct sz0; reflexivity).
    assert (Hval : bv_unsigned val = v).
    { unfold val. rewrite (load_result_val sz0 sx bs) by (rewrite <- HnA; exact Hlen).
      injection Hev as <-. rewrite <- Hmap, le_val_bytes.
      pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
      assert (Hle : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; [lia|]; unfold n; destruct sz0; cbn; lia).
      unfold extz. subst n sx'.
      destruct sz0; destruct sx; cbn -[Z.pow Z.mul Z.of_nat bv_swrap Z.modulo bytes_le_to_Z two64];
        first [ rewrite u_lit64; reflexivity
              | rewrite u_lit64; unfold two64; rewrite Z.mod_small; [reflexivity | cbn in Hb, Hle; lia] ]. }
    unfold cfg_of. fold ms.
    apply (srz_msteps_restricted_T SEGS H (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_hid SEGS A LIMIT SINV argH FS0 HULL_ok E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H (ms_mem ms) (mkst (regupd R rd' val) (Z_to_bv 64 (pc cs + 4)) MR (seg_rom SEGS)))
      with (mkst (regupd R rd' val) (Z_to_bv 64 (pc cs + 4)) (munrestrict H FULL MR) (seg_rom SEGS)).
    unfold MR, Mr. fold H. rewrite munrestrict_mrestrict.
    (* [comment removed for export] *)
    set (E' := eupd E (nxt cs) val).
    assert (Hag : env_agree (nxt cs) E E').
    { unfold E'. split; [|reflexivity]. intros m Hm. cbn [ev eupd]. destruct (Nat.eqb_spec m (nxt cs)); [lia | reflexivity]. }
    destruct (fresh_ok_parts _ cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    assert (Hrv : edenot E' rv = val).
    { unfold rv. destruct (Z.eqb_spec mn mx) as [Hmm|Hmm].
      - cbn [edenot]. rewrite <- (Z_to_bv_bv_unsigned 64 val). f_equal. lia.
      - cbn [edenot]. unfold E'. apply eupd_at. }
    specialize (Hk E' (regupd R rd' val) model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
    unfold cfg_of, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame) | exact (APS.mvis_of_materialized _ _ Hsame) | ].
    2: { apply (APS.hid_extF A nx0 argH argH_agree (nxt cs)); [reflexivity | exact Hag | exact Fle | exact Fallow | exact (APS.mvis_of_materialized _ _ Hsame)]. }
    (* [comment removed for export] *)
    pose proof (cs_ok_agree SEGS A nx0 NX0_min LIMIT SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.   (* [comment removed for export] *)
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') as HR'.
    eapply cs_ok_frame; [exact SINV_frame | exact HC' | exact Hsame | | | reflexivity | | intros; reflexivity].
    - rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
    - cbn [s_regs].
      pose proof (regs_ok_upd E' (s_regs (a_ss cs)) R rd' val rv HR') as RU. rewrite Hrd in RU. apply RU. exact Hrv.
    - cbn [s_know]. unfold Mr. rewrite (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow). fold H.
      apply Forall_app. split; [apply Forall_app; split|apply Forall_app; split].
      + (* [comment removed for export] *)
        unfold rv. destruct (Z.eqb mn mx); [constructor|]. apply Forall_cons; [|constructor].
        cbn [kentry_ok edenot]. unfold E'. rewrite eupd_at. rewrite Hval. exact Hvb.
      + (* [comment removed for export] *)
        unfold mfact. destruct msk as [m|] eqn:Hmsk; [|constructor].
        assert (Hm : 0 <= m < two64).
        { unfold msk in Hmsk. destruct args as [|? [|m0 l]]; try discriminate Hmsk. destruct m0; try discriminate Hmsk.
          destruct l; cbn in Hmsk; [|discriminate Hmsk].
          destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:Hz; [|discriminate]. injection Hmsk as <-.
          apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. lia. }
        destruct (Z.eqb mn mx); [constructor|].
        destruct (scan_mask SEGS kl Bb sx' n (Bo + xl) st (Z.to_nat cnt) m None) as [[b|]|] eqn:Hsm; try constructor; [|constructor].
        cbn [kentry_ok]. rewrite mkAlu_denot. cbn [edenot]. rewrite u_and64, Hrv, u_lit64, Hval.
        rewrite (Z.mod_small m) by (unfold two64 in *; lia). rewrite (Hmask m b Hsm). lia.
      + (* [comment removed for export] *)
        destruct (rec_onb (kn cs)); [|constructor]. apply Forall_cons; [|constructor].
        assert (Hav' : edenot E' e = av).
        { unfold e, av, v_addi. rewrite mkAlu_denot. cbn [edenot]. rewrite <- (HR' rs). rewrite alu_add. unfold v_add.
          apply bv_eq. rewrite !u_lit64. unfold two64. rewrite Zplus_mod_idemp_r. reflexivity. }
        assert (Hadr' : adenot E' (SA e 0) = av).
        { unfold adenot. cbn [a_base a_off]. rewrite Hav'. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
        cbn [kentry_ok]. split; [exact Hn8|]. split.
        { unfold flat, estart. cbn [a_base a_off]. rewrite Hav'. fold u. unfold two64 in Hhi. lia. }
        rewrite Hadr'. change (mrestrict H FULL) with MR. rewrite Hrdn. f_equal. rewrite Hrv. unfold val.
        rewrite (load_result_val sz0 sx bs) by (rewrite <- HnA; exact Hlen). rewrite <- HnA.
        symmetry. apply word_to_le_bytes_extz; [exact Hlen | exact Hn1 | exact Hn8].
      + pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC') as HK'. unfold Mr in HK'.
        rewrite (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow) in HK'. exact HK'.
  Qed.

  Theorem node_tabread_sound : forall args,
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_tabread SEGS IT nx0 cs args).
  Proof. intros args. apply node1_stmtF_stmt. apply node_tabread_soundF. Qed.

  (* [comment removed for export] *)
  Lemma set_kn_sound : forall cs k E R FULL model T,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    know_ok SEGS E (Mr A argH E cs model FULL) k ->
    (forall E' R' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok SEGS A LIMIT SINV argH FS0 E' (set_kn cs k) R' FULL model' ->
        m_fs model' = m_fs model -> APS.mvis_eq model model' ->
        APS.hid A argH E' (set_kn cs k) model' = APS.hid A argH E cs model ->
        srealizes SEGS (cfg_of SEGS R' (pc (set_kn cs k)) FULL model') T) ->
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T.
  Proof.
    intros cs k E R FULL model T HC HK Hk.
    specialize (Hk E R model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    replace (pc (set_kn cs k)) with (pc cs) in Hk by reflexivity. apply Hk; [|reflexivity|apply APS.mvis_refl|apply (APS.hid_extF0 A argH); [reflexivity | apply APS.mvis_refl]].
    apply cs_ok_set_kn; [exact HC | exact HK].
  Qed.

  Theorem node_recon_soundF : forall args,
    node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_recon cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_recon in Hn. destruct args; [|discriminate].
    destruct (rec_onb (kn cs)).
    - injection Hn as <-. apply (Hk E R model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E)) HC eq_refl (APS.mvis_refl _) eq_refl).
    - injection Hn as <-. eapply set_kn_sound; [exact HC | | exact Hk].
      constructor; [cbn [kentry_ok KRec edenot]; rewrite u_small by lia; lia | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
  Qed.

  Theorem node_recoff_soundF : forall args,
    node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_recoff cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_recoff in Hn. destruct args; [|discriminate].
    injection Hn as <-. eapply set_kn_sound; [exact HC | | exact Hk].
    unfold know_ok. apply incl_Forall with (l1 := kn cs); [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
    apply incl_filter.
  Qed.

  (* [comment removed for export] *)
  Lemma ext_Z_01_mod : forall sx z z', z mod 256 = z' mod 256 -> ext_Z sx 0 1 z = ext_Z sx 0 1 z'.
  Proof.
    intros sx z z' H. unfold ext_Z. change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
    rewrite !Z.div_1_r, H. reflexivity.
  Qed.
  Lemma u_ext01_mod : forall sx (x : word), bv_unsigned (ext_val sx 0 1 x) mod 256 = bv_unsigned x mod 256.
  Proof.
    intros sx x. pose proof (Z.mod_pos_bound (bv_unsigned x) 256 ltac:(lia)) as Hm.
    set (x' := Z_to_bv 64 (bv_unsigned x mod 256)).
    assert (Hx' : bv_unsigned x' = bv_unsigned x mod 256) by (unfold x'; rewrite u_lit64; unfold two64; apply Z.mod_small; lia).
    assert (E : ext_val sx 0 1 x = ext_val sx 0 1 x').
    { unfold ext_val. f_equal. apply ext_Z_01_mod. rewrite Hx'. symmetry. apply Z.mod_mod. lia. }
    assert (Hx'r : 0 <= bv_unsigned x' < 256) by (rewrite Hx'; lia).
    rewrite E. destruct sx.
    - destruct (Z_lt_le_dec (bv_unsigned x') 128) as [L|L].
      + rewrite u_ext_sx0_small; [rewrite Hx'; apply Z.mod_mod; lia|]. change (2 ^ (8 * Z.of_nat 1)) with 256. change (256 / 2) with 128. exact L.
      + rewrite u_ext_sx0_high; [| change (2 ^ (8 * Z.of_nat 1)) with 256; change (256 / 2) with 128; lia | lia].
        change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Hx'.
        replace (2 ^ 64 - 256 + bv_unsigned x mod 256) with (bv_unsigned x mod 256 + 72057594037927935 * 256) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
    - rewrite u_ext_zx0_small; [rewrite Hx'; apply Z.mod_mod; lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia].
  Qed.
  Lemma bcore_mod : forall E e v, bcore e = Some v -> bv_unsigned (edenot E e) mod 256 = bv_unsigned (ev E v) mod 256.
  Proof.
    intros E e v. induction e; cbn [bcore]; try discriminate.
    destruct lo; [|discriminate]. destruct n as [|[|n]]; try discriminate.
    destruct e; try discriminate; intros H.
    - injection H as ->. cbn [edenot]. apply u_ext01_mod.
    - cbn [edenot]. rewrite u_ext01_mod. apply IHe. exact H.
  Qed.
  Lemma brespell_denot : forall E sx a v, bcore (EExt sx 0 1 a) = Some v ->
    edenot E (if sx then EExt true 0 1 (EExt false 0 1 (EVar v)) else EExt false 0 1 (EVar v)) = edenot E (EExt sx 0 1 a).
  Proof.
    intros E sx a v H.
    assert (Ha : bv_unsigned (edenot E a) mod 256 = bv_unsigned (ev E v) mod 256).
    { cbn [bcore] in H. destruct a; try discriminate; [injection H as ->; reflexivity | exact (bcore_mod E _ v H)]. }
    destruct sx; cbn [edenot]; unfold ext_val; f_equal; apply ext_Z_01_mod.
    - fold (ext_val false 0 1 (ev E v)). rewrite u_ext01_mod. symmetry. exact Ha.
    - symmetry. exact Ha.
  Qed.
  Lemma cs_ok_set_reg_same : forall E cs R FULL model n e',
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> (0 < n < 32)%nat -> edenot E e' = edenot E (reg cs n) ->
    cs_ok SEGS A LIMIT SINV argH FS0 E (set_reg cs n e') R FULL model.
  Proof.
    intros E cs R FULL model n e' HC Hn He.
    destruct HC; constructor; cbn [set_reg with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_props kn mk_ss s_regs s_log s_know s_pc s_next];
      try assumption; try reflexivity.
    apply APS.regs_ok_respell; [assumption | exact Hn | exact He].
  Qed.
  Theorem node_brespell_soundF : forall args,
    node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_brespell cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_brespell in Hn.
    destruct args as [|[r| | | | | | |] [|? ?]]; try discriminate.
    destruct (Nat.ltb 0 (Z.to_nat r) && Nat.ltb (Z.to_nat r) 32)%bool eqn:Hrn; [|discriminate]. cbn [negb] in Hn.
    apply andb_prop in Hrn as [H0 H32]. apply Nat.ltb_lt in H0. apply Nat.ltb_lt in H32.
    destruct (reg cs (Z.to_nat r)) as [| | | | | |sx lo n a|] eqn:Hreg; try discriminate.
    destruct lo; [|discriminate]. destruct n as [|[|n]]; try discriminate.
    destruct (bcore (EExt sx 0 1 a)) as [v|] eqn:Hb; [|discriminate]. injection Hn as <-.
    specialize (Hk E R model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    apply Hk; [| reflexivity | apply APS.mvis_refl | apply (APS.hid_extF0 A argH); [reflexivity | apply APS.mvis_refl]].
    apply cs_ok_set_reg_same; [exact HC | lia |]. rewrite Hreg. apply brespell_denot. exact Hb.
  Qed.

  Theorem node_recon_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_recon cs args).
  Proof. intros args. apply node1_stmtF_stmt. apply node_recon_soundF. Qed.
  Theorem node_recoff_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_recoff cs args).
  Proof. intros args. apply node1_stmtF_stmt. apply node_recoff_soundF. Qed.

  (* [comment removed for export] *)
  Lemma find_segment_In' : forall segs z n seg, find_segment segs z n = Some seg -> In seg segs.
  Proof.
    intros segs z n seg. induction segs as [|s0 rest IH]; cbn [find_segment]; intros H; [discriminate|].
    destruct (Z.leb (Z.of_N (seg_base s0)) z && Z.leb (z + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
    - injection H as <-. left. reflexivity.
    - right. apply IH. exact H.
  Qed.
  (* [comment removed for export] *)
  Lemma wview_rd1' : forall M (a : word) b,
    wview SEGS M a = Some b ->
    (match M a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b.
  Proof.
    intros M a b H. unfold wview in H. destruct (M a) as [b0|]; [exact H|].
    unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
    destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
    destruct (seg_writable seg) eqn:Hw; [|discriminate].
    rewrite (SEGS_wr seg (find_segment_In' _ _ _ _ Hf) Hw).
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite H. reflexivity.
  Qed.
  Lemma store_ok_rdn' : forall n M (a : word),
    bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    store_ok SEGS M a n = true ->
    exists bs, rdn SEGS M a n = Some bs /\ length bs = n.
  Proof.
    induction n as [|n IH]; intros M a Hnw Hst.
    - exists []. split; reflexivity.
    - cbn [store_ok] in Hst. destruct (wview SEGS M a) as [b|] eqn:Hv; [|discriminate].
      cbn [rdn]. rewrite (wview_rd1' M a b Hv).
      destruct n as [|n'].
      + exists [b]. split; reflexivity.
      + assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
        destruct (IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst) as (bs & Hrd & Hlen).
        rewrite Hrd. exists (b :: bs). split; [reflexivity | cbn; lia].
  Qed.

  Theorem node_namecell_soundF : forall args,
    node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_namecell nx0 cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_namecell in Hn.
    destruct args as [|a rest]; [discriminate|]. destruct rest as [|e2 rest]; [discriminate|].
    destruct e2 as [nz| | | | | | |]; try discriminate. destruct rest as [|? ?]; [|discriminate].
    destruct (split_lit a) as [ab ao] eqn:Hsplit.
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hwr]. apply andb_prop in Hc as [Hc Hvab]. apply andb_prop in Hc as [Hfresh Hnz].
    assert (Hn18 : (1 <= Z.to_nat nz <= 8)%nat /\ 0 <= nz <= 8).
    { repeat (apply orb_prop in Hnz as [Hnz|Hnz]); apply Z.eqb_eq in Hnz; subst nz; cbn; lia. }
    destruct Hn18 as [Hn18 Hnz8].
    set (n := Z.to_nat nz) in *.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    set (MR := Mr A argH E cs model FULL) in *.
    (* [comment removed for export] *)
    destruct (AsanNodesAux.kwritable_sound SEGS E MR (kn cs) (kn cs) ab ao nz HK HK Hwr ltac:(lia)) as (Hst & Hlo & Hhi).
    fold n in Hst.
    set (u := estart E (SA ab ao)) in *.
    destruct (store_ok_rdn' n MR (Z_to_bv 64 u) ltac:(rewrite u64_lit by lia; lia) Hst) as (bs & Hrdn & Hlen).
    set (val := Z_to_bv 64 (bytes_le_to_Z bs)).
    (* [comment removed for export] *)
    set (E' := eupd E (nxt cs) val).
    assert (Hag : env_agree (nxt cs) E E').
    { unfold E'. split; [|reflexivity]. intros m Hm. cbn [ev eupd]. destruct (Nat.eqb_spec m (nxt cs)); [lia | reflexivity]. }
    destruct (fresh_ok_parts _ cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    specialize (Hk E' R model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
    unfold cfg_of, pc in Hk |- *. cbn [with_ss a_ss mk_ss s_pc] in Hk.
    apply Hk; [| reflexivity | apply APS.mvis_refl | ].
    2: { apply (APS.hid_extF A nx0 argH argH_agree (nxt cs)); [reflexivity | exact Hag | exact Fle | exact Fallow | apply APS.mvis_refl]. }
    (* [comment removed for export] *)
    pose proof (cs_ok_agree SEGS A nx0 NX0_min LIMIT SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
    eapply cs_ok_frame; [exact SINV_frame | exact HC' | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC')
                        | exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | reflexivity | | intros; reflexivity].
    cbn [s_know]. apply Forall_cons.
    - (* [comment removed for export] *)
      assert (Eab : edenot E' ab = edenot E ab) by (symmetry; exact (edenot_agree' (nxt cs) E E' ab Hag Hvab)).
      assert (Hu' : estart E' (SA ab ao) = u) by (unfold estart, u; cbn [a_base a_off]; rewrite Eab; reflexivity).
      assert (HMR : Mr A argH E' cs model FULL = MR).
      { unfold MR, Mr. rewrite (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow). reflexivity. }
      rewrite HMR. cbn [kentry_ok]. split; [lia|]. split.
      { unfold flat. rewrite Hu'. lia. }
      assert (Hadr : adenot E' (SA ab ao) = Z_to_bv 64 u).
      { rewrite <- Hu'. rewrite <- (flat_u E' (SA ab ao) (Z.of_nat n)) by (unfold flat; rewrite Hu'; lia).
        symmetry. apply Z_to_bv_bv_unsigned. }
      rewrite Hadr, Hrdn. f_equal. cbn [edenot]. unfold E'. rewrite eupd_at. unfold val.
      symmetry. exact (word_to_le_bytes_extz false n bs Hlen ltac:(lia) ltac:(lia)).
    - exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC').
  Qed.
  Theorem node_namecell_sound : forall args,
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_namecell nx0 cs args).
  Proof. intros args. apply node1_stmtF_stmt. apply node_namecell_soundF. Qed.

  (* [comment removed for export] *)
  Corollary xn_soundF : forall id, ext_stmtF SEGS A nx0 LIMIT (EXN.xn SEGS IT nx0) SINV argH FS0 id.
  Proof.
    intros id args. unfold EXN.xn. rewrite ?EXN.node_tabreadM_eqf.   (* [comment removed for export] *)
    destruct id as [|id]; [intros cs cs' E R FULL model T _ _ H; discriminate|].
    do 39 (destruct id as [|id]; [intros cs cs' E R FULL model T _ _ H; discriminate|]).
    destruct id as [|id]; [apply node_tabread_soundF|].
    destruct id as [|id]; [apply node_recon_soundF|].
    destruct id as [|id]; [apply node_recoff_soundF|].
    destruct id as [|id]; [intros cs cs' E R FULL model T _ _ H; discriminate|].
    destruct id as [|id]; [apply node_brespell_soundF|].   (* [comment removed for export] *)
    destruct id as [|id]; [apply node_namecell_soundF|].   (* [comment removed for export] *)
    intros cs cs' E R FULL model T _ _ H; discriminate.
  Qed.
  Corollary xn_sound : ext_stmt SEGS A nx0 LIMIT (EXN.xn SEGS IT nx0) SINV argH FS0.
  Proof. intros id args. apply node1_stmtF_stmt. apply xn_soundF. Qed.
End Sound.
End EXNS.
