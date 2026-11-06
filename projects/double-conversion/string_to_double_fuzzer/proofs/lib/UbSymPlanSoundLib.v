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
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec LibWritev RefNodes UbExitBase Hoare Frame
  RefMemcpyLib MemSplit LibTail
  MallocDefs UbEnframeBase LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec2Sound SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan UbSymSlots UbSymPlanSoundA UbSymPlanSound UbSymPlanSoundH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.
#[local] Notation "'FR'" := 4096%Z (only parsing).
#[local] Notation "'FRN'" := 4096%nat (only parsing).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seg_rom_memory_read : forall (a : word) b,
  seg_rom RSEGS a = Some b -> memory_read RSEGS a 1%N = Some [b].
Proof.
  intros a b H. unfold seg_rom in H.
  destruct (memory_read RSEGS a 1) as [l|] eqn:Hm; [|discriminate].
  unfold memory_read in Hm.
  destruct (find_segment RSEGS (bv_unsigned a) (Z.of_N 1)) as [seg|]; [|discriminate].
  destruct (seg_readable seg); [|discriminate].
  change (N.to_nat 1) with 1%nat in Hm. cbn [segment_read_bytes] in Hm.
  destruct (segment_byte_at _ _) as [b'|]; [|discriminate].
  destruct l as [|b1 [|b2 l2]]; try discriminate. congruence.
Qed.

(* [comment removed for export] *)
Lemma rdn_ro_byte : forall M (a : Z) n bs j b,
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 a) n = Some bs ->
  rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs ->
  (j < n)%nat ->
  M (Z_to_bv 64 (a + Z.of_nat j)) = Some b -> memory_read RSEGS (Z_to_bv 64 (a + Z.of_nat j)) 1%N = Some [b].
Proof.
  intros M a n bs j b Ha Hn HM HI Hj Hb.
  pose proof (rdn_byte_Z RSEGS M a n bs j HM Hj Ha ltac:(lia)) as B1.
  pose proof (rdn_byte_Z RSEGS (fun _ => None) a n bs j HI Hj Ha ltac:(lia)) as B2.
  cbn [rdn] in B1, B2. rewrite Hb in B1.
  destruct (seg_rom RSEGS (Z_to_bv 64 (a + Z.of_nat j))) as [c|] eqn:Hc; [|discriminate].
  injection B1 as E1. injection B2 as E2. apply seg_rom_memory_read. rewrite Hc. congruence.
Qed.

(* [comment removed for export] *)
Lemma find_segment_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.

Lemma find_segment_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0xe6000 <= a)%Z ->
  find_segment RSEGS a n = None.
Proof.
  intros a n Hn H. unfold ImgU.M.loaded_segments, ImgU_loaded_segments.
  rewrite 4 find_segment_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size ImgU_segment_000 ImgU_segment_001 ImgU_segment_002 ImgU_segment_003]; lia.
Qed.

Section NX0.
Variable nx0 : nat.
Context {fx : FPState}.
Hypothesis FRM : frm_zero fx.
Hypothesis LIB : lib_stmt_U.

(* [comment removed for export] *)
Lemma ro_cells_sound : forall E M k,
  know_ok RSEGS E M k -> lib_ok M -> ro_cells_ok RSEGS U0 k (t_ro U0) = true -> ro_ok RSEGS RO_U M.
Proof.
  intros E M k HK HLIB Hro. unfold ro_ok. intros a b (r & Hin & Hr) Hb.
  change (t_ro U0) with RO_U in Hro. unfold ro_cells_ok in Hro.
  apply (proj1 (forallb_forall _ _)) with (x := r) in Hro; [|exact Hin].
  destruct r as [lo hi]. cbn [fst snd] in Hr.
  destruct (in_hull U0 (lo, hi)) eqn:Hh.
  - (* [comment removed for export] *)
    exfalso. unfold in_hull in Hh. cbn [fst snd] in Hh. apply andb_prop in Hh as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    change (t_hull_lo U0) with HULL_LO in H1. change (t_hull_hi U0) with HULL_HI in H2.
    destruct HLIB as [_ HP]. rewrite HULL_eq in HP. cbn [fst snd] in HP.
    assert (HN : ~ in_ranges a LIBR_U).
    { intros Hl. destruct Hl as ([ql qh] & Hq & Ha'). cbn [fst snd] in Ha'.
      (* [comment removed for export] *)
      assert (Y : forallb (fun q => forallb (fun r => (snd q <=? fst r) || (snd r <=? fst q)) RO_U)%bool LIBR_U = true) by (vm_compute; reflexivity).
      apply (proj1 (forallb_forall _ _)) with (x := (ql, qh)) in Y; [|exact Hq].
      apply (proj1 (forallb_forall _ _)) with (x := (lo, hi)) in Y; [|exact Hin]. cbn [fst snd] in Y.
      apply orb_prop in Y as [Y|Y]; apply Z.leb_le in Y; lia. }
    rewrite (HP a ltac:(lia) HN) in Hb. discriminate.
  - unfold ro_cell_ok in Hro. cbn [fst snd] in Hro.
    destruct (kimg_covers k lo hi) eqn:Hcov.
    + (* [comment removed for export] *)
      unfold kimg_covers in Hcov. apply existsb_exists in Hcov as (K & HinK & HK2).
      destruct K as [| | |l h| | | |]; try discriminate. apply andb_prop in HK2 as [Hl Hh2]. apply Z.leb_le in Hl. apply Z.leb_le in Hh2.
      pose proof (proj1 (Forall_forall _ _) HK _ HinK) as (_ & _ & Hnone). rewrite (Hnone a ltac:(lia)) in Hb. discriminate.
    + (* [comment removed for export] *)
      apply andb_prop in Hro as [Hro Heq]. apply andb_prop in Hro as [Hpos Hle8].
      apply Z.ltb_lt in Hpos. apply Z.leb_le in Hle8.
      destruct (kreadZ RSEGS k (ELit 0) lo (Z.to_nat (hi - lo))) as [v|] eqn:Hkr; [|discriminate].
      destruct (img_readZ RSEGS lo (Z.to_nat (hi - lo))) as [w|] eqn:Hir; [|discriminate]. apply Z.eqb_eq in Heq. subst w.
      unfold img_readZ in Hir. destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 lo) (Z.to_nat (hi - lo))) as [bs|] eqn:Hbs; [|discriminate].
      injection Hir as Hv.
      pose proof (u64_range (Z_to_bv 64 a)) as Har.
      assert (Hlo0 : 0 <= lo).
      { (* [comment removed for export] *)
        assert (Y : forallb (fun r => (0 <=? fst r) && (snd r <=? 2 ^ 64))%bool RO_U = true) by (vm_compute; reflexivity).
        apply (proj1 (forallb_forall _ _)) with (x := (lo, hi)) in Y; [|exact Hin]. cbn [fst snd] in Y.
        apply andb_prop in Y as [Y1 Y2]. apply Z.leb_le in Y1. lia. }
      assert (Hhi64 : hi <= 2 ^ 64).
      { assert (Y : forallb (fun r => (0 <=? fst r) && (snd r <=? 2 ^ 64))%bool RO_U = true) by (vm_compute; reflexivity).
        apply (proj1 (forallb_forall _ _)) with (x := (lo, hi)) in Y; [|exact Hin]. cbn [fst snd] in Y.
        apply andb_prop in Y as [Y1 Y2]. apply Z.leb_le in Y2. lia. }
      destruct (kreadZ_rdn E M k (ELit 0) lo (Z.to_nat (hi - lo)) v HK Hkr ltac:(lia)
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite u_lit0, Z2Nat.id by lia; lia)) as [HM _].
      rewrite adenot_SA in HM. cbn [edenot] in HM. rewrite u_lit0, Z.add_0_l in HM.
      pose proof (rdn_length _ _ _ _ _ Hbs) as Hlen.
      rewrite <- Hv, (word_to_le_bytes_of_lez (Z.to_nat (hi - lo)) bs Hlen ltac:(lia)) in HM.
      replace a with (lo + Z.of_nat (Z.to_nat (a - lo))) in Hb |- * by lia.
      eapply (rdn_ro_byte M lo (Z.to_nat (hi - lo)) bs); [lia | lia | exact HM | exact Hbs | lia | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma keeps_cs_kept : forall R R', keeps_cs R R' ->
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr R' r = getr R r.
Proof.
  intros R R' HK r Hr0 Hnin. pose proof (ridx_range r) as Hrr.
  assert (Hr : ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold caller_saved in Hnin. cbn [In] in Hnin.
  rewrite (reg_of_ridx r (ridx r) eq_refl).
  apply HK. unfold cs_regs. cbn [In]. lia.
Qed.

Lemma call_lib_sound' : forall cs cs' E R M model T,
  cs_ok E cs R M model -> (0 <= t_lib U0)%Z -> pc cs = t_lib U0 -> call_lib RSEGS U0 nx0 cs = Some cs' ->
  (forall (fx' : FPState), frm_zero fx' -> forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of (fx:=fx') R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
  intros cs cs' E R M model T HC Hgate Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_lib _ _ _ _ _ HC) as HLIB.
  unfold call_lib in Hn. cbv zeta in Hn.
  change (t_lib_frame U0) with FR in Hn. change (t_lib_ret U0) with 0x329d0%Z in Hn.
  change (t_hull_lo U0) with 0xc3620%Z in Hn. change (t_hull_hi U0) with 0xc4708%Z in Hn. change (i_top U0) with 0xe6000%Z in Hn.
  change (0xc4708 - 0xc3620)%Z with 0x10e8%Z in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (ehi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (elo (kn cs) (reg cs 10)) as [dlo|] eqn:Hdlo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hfresh].
  apply andb_prop in Hcond as [Hcond Hcan].   (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hro].
  apply andb_prop in Hcond as [Hcond _].   (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond _].   (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond _].   (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hdata].
  apply andb_prop in Hcond as [Hcond Hrs].
  apply andb_prop in Hcond as [Hcond Hdisj].
  apply andb_prop in Hcond as [Hcond Hsphi62].
  apply andb_prop in Hcond as [Hcond Hsplo32].
  apply andb_prop in Hcond as [Hcond HFR].
  apply andb_prop in Hcond as [Hcond Hspal].
  apply andb_prop in Hcond as [Hcond Hdal].
  apply andb_prop in Hcond as [Hcond Hd62].
  apply andb_prop in Hcond as [Hcond Hd4096].
  apply andb_prop in Hcond as [Hcond Hn26].
  apply andb_prop in Hcond as [Hcond Hn0].
  apply andb_prop in Hcond as [Hretv Hret4].
  apply Z.eqb_eq in Hretv. apply Z.eqb_eq in Hret4. subst ret.
  apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn26. apply Z.leb_le in Hd4096. apply Z.ltb_lt in Hd62.
  apply Z.leb_le in Hdal. apply Z.leb_le in Hspal. apply Z.leb_le in Hsplo32. apply Z.ltb_lt in Hsphi62. clear HFR.
  destruct (ret_lit_sound E cs R M model _ HC Hret) as (R1 & Hrok & Hretr).
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hnhi) as Hnle.
  pose proof (elo_sound E M (kn cs) _ _ HKN Hdlo) as Hdlole.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hdhi) as Hdhile.
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsple.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphe.
  set (data := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 11)) in *.
  set (sp := edenot E (reg cs 2)) in *.
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (- FR))) in *.
  pose proof (u64_range nw) as Hnwr. pose proof (u64_range data) as Hdr. pose proof (u64_range sp) as Hspr.
  assert (Hspm : edenot E spm = Z_to_bv 64 (bv_unsigned sp - FR)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  destruct (rw_ok_sound E M (kn cs) spm FR HKN Hrs ltac:(lia)) as (Pst & Pdef & Pimg & U0' & Pnw & Pspl).
  rewrite Hspm in Pst, Pdef, Pimg, U0', Pnw.
  assert (Hspu : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - FR)) = (bv_unsigned sp - FR)%Z) by (rewrite u64_lit by lia; reflexivity).
  rewrite Hspu in Pdef, Pimg, U0', Pnw.
  (* [comment removed for export] *)
  assert (AL16 : forall e, 4 <= ealign (kn cs) e -> (bv_unsigned (edenot E e) mod 16 = 0)%Z).
  { intros e He. destruct (ealign_sound RSEGS E M (kn cs) e HKN) as [Hr [q Hq]].
    assert (Hd : (2 ^ 4 | 2 ^ ealign (kn cs) e)%Z) by (apply pow2_divide_le; lia).
    destruct Hd as [r Hr']. rewrite Hq, Hr'. replace (q * (r * 2 ^ 4))%Z with ((q * r) * 16)%Z by (change (2^4)%Z with 16%Z; ring).
    apply Z.mod_mul. lia. }
  pose proof (AL16 _ Hdal) as Hdal16. fold data in Hdal16. pose proof (AL16 _ Hspal) as Hspal16. fold sp in Hspal16.
  (* [comment removed for export] *)
  assert (RWX : nhi <> 0 -> rw_ok_x U0 (kn cs) (reg cs 10) (reg cs 11) = true).
  { intros Hnz. rewrite (proj2 (Z.eqb_neq nhi 0) Hnz) in Hdata. exact Hdata. }
  assert (DISJ : (bv_unsigned data + bv_unsigned nw <= bv_unsigned sp - FR \/ bv_unsigned sp <= bv_unsigned data)%Z).
  { apply orb_prop in Hdisj as [Hnum|Hap].
    - apply orb_prop in Hnum as [H1|H2]; [apply Z.leb_le in H1; lia | apply Z.leb_le in H2; lia].
    - apply andb_prop in Hap as [Hnz Hap].
      assert (Hnz' : nhi <> 0) by (intros X; rewrite (proj2 (Z.eqb_eq nhi 0) X) in Hnz; discriminate).
      destruct (rw_ok_x_sound E M (kn cs) (reg cs 10) (reg cs 11) HKN (RWX Hnz')) as (_ & _ & _ & _ & _ & Sspl & _).
      pose proof (apart_x_loc E M (kn cs) (reg cs 10) (reg cs 11) spm (ELit FR) HKN Hap Sspl Pspl) as D.
      fold data in D. unfold elenZ in D. fold nw in D. rewrite Hspm, Hspu in D. cbn [edenot] in D.
      rewrite (u64_lit FR) in D by lia. lia. }
  assert (DATA : forall i, (0 <= i < bv_unsigned nw)%Z ->
            exists b, rdn RSEGS M (Z_to_bv 64 (bv_unsigned data + i)) 1 = Some [b]).
  { intros i Hi. assert (Hnz' : nhi <> 0) by lia.
    destruct (rw_ok_x_sound E M (kn cs) (reg cs 10) (reg cs 11) HKN (RWX Hnz')) as (_ & Sdef & _ & S0 & Snw & _ & _).
    fold data in Sdef, S0, Snw. unfold elenZ in Sdef, Snw. fold nw in Sdef, Snw.
    destruct (rdn_defined M (bv_unsigned data + i) 1 ltac:(lia) ltac:(cbn; lia)
               ltac:(intros j Hj; cbn in Hj; replace (bv_unsigned data + i + j)%Z with (bv_unsigned data + (i + j))%Z by lia; apply Sdef; lia))
      as (bs1 & Hrb1 & Hl1).
    destruct bs1 as [|b [|]]; cbn in Hl1; try lia. exists b. exact Hrb1. }
  assert (IMG : (bv_unsigned nw = 0 \/ bv_unsigned data + bv_unsigned nw <= 0x10000 \/ 0xe6000 <= bv_unsigned data)%Z).
  { destruct (Z.eq_dec nhi 0) as [Hz|Hnz']; [left; lia | right].
    destruct (rw_ok_x_sound E M (kn cs) (reg cs 10) (reg cs 11) HKN (RWX Hnz')) as (_ & _ & Simg & _).
    fold data in Simg. unfold elenZ in Simg. fold nw in Simg. exact Simg. }
  (* [comment removed for export] *)
  assert (SEGN : forall a, (bv_unsigned sp - FR <= a < bv_unsigned sp)%Z -> find_segment RSEGS a 1 = None).
  { intros a Ha. apply find_segment_off; lia. }
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
  pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  fold data in R10. fold nw in R11. fold sp in R2.
  pose proof (ro_cells_sound E M (kn cs) HKN HLIB Hro) as RO.
  assert (CAN : exists c : word, rdn RSEGS M (Z_to_bv 64 CANARY_U) 8%nat = Some (word_to_le_bytes 8 c)).
  { change (d_canary U0) with CANARY_U in Hcan.
    destruct (kread8e RSEGS (kn cs) (ELit 0) CANARY_U) as [cv|] eqn:Hce; [|discriminate].
    exists (edenot E cv).
    pose proof (kread8e_rdn E M (kn cs) (ELit 0) CANARY_U cv HKN Hce
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite u_lit0; unfold CANARY_U; lia)) as X.
    rewrite adenot_SA in X. cbn [edenot] in X. rewrite u_lit0, Z.add_0_l in X. exact X. }
  destruct (LIB fx R M (seg_rom RSEGS) (Z_to_bv 64 0x329d0) sp data (bv_unsigned nw)
              R1 ltac:(rewrite u64_lit by lia; exact Hret4) R2 R10
              ltac:(rewrite Z_to_bv_bv_unsigned; exact R11)
              ltac:(unfold NMAX_U; lia) ltac:(lia) ltac:(lia) Hdal16 Hspal16
              ltac:(unfold FR_U; lia) ltac:(lia)
              ltac:(unfold FR_U; exact DISJ) ltac:(lia)
              ltac:(unfold FR_U; exact SEGN) DATA
              ltac:(unfold FR_U; exact Pst) RO CAN HLIB FRM)
    as (fx' & R' & M' & Hms & Hkeeps & Ha0 & Hframe & HLIB' & FRM').
  unfold cfg_of. rewrite Hpc. change (Z_to_bv 64 (t_lib U0)) with (Z_to_bv 64 ENTRY_U).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  destruct Hframe as [Hout Hgrow]. unfold FR_U in Hout.
  destruct (after_call nx0 cs 0x329d0%Z (Some (ELit 0)) (kn_havoc (havoc_e (kn cs) spm FR) (ELit 0) 0xc3620 (ELit 0x10e8))) as [csa|] eqn:Hac; [|discriminate].
  destruct (split_lit spm) as [qb qk] eqn:Hspq. cbn in Pspl.
  injection Hn as <-.
  (* [comment removed for export] *)
  assert (OUT : forall x : word,
            (bv_unsigned x < bv_unsigned sp - FR \/ bv_unsigned sp <= bv_unsigned x)%Z ->
            (bv_unsigned x < 0xc3620 \/ 0xc4708 <= bv_unsigned x)%Z -> M' x = M x).
  { intros x Hx Hh. apply Hout. intros ([l h] & Hin & Hr). cbn [fst snd] in Hr.
    destruct Hin as [Heq|Hin].
    - injection Heq as <- <-. lia.
    - pose proof (LIBR_in_hull (bv_unsigned x) ltac:(exists (l, h); split; [exact Hin | exact Hr])) as X.
      unfold HULL_LO, HULL_HI in X. cbn in X. lia. }
  (* [comment removed for export] *)
  set (inh := fun x : word => ((0xc3620 <=? bv_unsigned x) && (bv_unsigned x <? 0xc4708))%bool).
  set (M1 := fun x : word => if inh x then M x else M' x).
  assert (M1eq : forall x, M1 x = (if ((0xc3620 <=? bv_unsigned x) && (bv_unsigned x <? 0xc4708))%bool then M x else M' x)) by reflexivity.
  clearbody M1. clear inh.
  assert (W1 : forall x : word, (bv_unsigned x < bv_unsigned sp - FR \/ bv_unsigned sp - FR + FR <= bv_unsigned x)%Z -> M1 x = M x).
  { intros x Hx. rewrite M1eq.
    destruct (Z.leb_spec 0xc3620 (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) 0xc4708); cbn [andb]; try reflexivity;
      apply OUT; lia. }
  assert (W2 : forall x : word, (bv_unsigned x < 0xc3620 \/ 0xc3620 + 0x10e8 <= bv_unsigned x)%Z -> M' x = M1 x).
  { intros x Hx. rewrite M1eq.
    destruct (Z.leb_spec 0xc3620 (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) 0xc4708); cbn [andb]; try reflexivity. lia. }
  assert (G1 : mem_grows M M1).
  { intros x Hx. rewrite M1eq. destruct ((0xc3620 <=? bv_unsigned x) && (bv_unsigned x <? 0xc4708))%bool; [exact Hx|].
    destruct (M x) as [b|] eqn:HMx; [|exfalso; apply Hx; reflexivity].
    destruct (Hgrow x b HMx) as [b' Hb']. rewrite Hb'. discriminate. }
  assert (G2 : mem_grows M1 M').
  { intros x Hx. rewrite M1eq in Hx. destruct ((0xc3620 <=? bv_unsigned x) && (bv_unsigned x <? 0xc4708))%bool; [|exact Hx].
    destruct (M x) as [b|] eqn:HMx; [|exfalso; apply Hx; reflexivity].
    destruct (Hgrow x b HMx) as [b' Hb']. rewrite Hb'. discriminate. }
  destruct (after_call_sound nx0 cs 0x329d0%Z (Some (ELit 0)) (kn_havoc (havoc_e (kn cs) spm FR) (ELit 0) 0xc3620 (ELit 0x10e8)) csa E R R' M M' model
              (slots_keep (kn cs) (ELit 0) 0xc3620 (ELit 0x10e8) (slots_keep (kn cs) qb qk (ELit FR) (c_slots cs))) Hac HC) as [HC' Hpc'].
  + exact (keeps_cs_kept R R' Hkeeps).
  + cbn [edenot]. exact Ha0.
  + eapply (know_ok_havoc E M1 M').
    * eapply know_ok_havoc_e; [exact HKN | exact Hrs | lia | lia | | exact G1].
      intros x Hx. rewrite Hspm, Hspu in Hx. apply W1. exact Hx.
    * intros x Hx. apply W2. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
      rewrite u_lit0, (u64_lit 0x10e8) in Hx by lia. lia.
    * exact G2.
  + eapply (slots_keep_sound E M (kn cs) _ _ _ _ M1 M'); [exact HKN | |].
    * eapply slots_keep_sound; [exact HKN | exact (co_slots _ _ _ _ _ HC) |].
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite u_lit64. change (FR mod two64)%Z with FR.
      rewrite Hspm, Hspu in Pspl. rewrite <- Pspl. exact W1.
    * unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite u_lit0, (u64_lit 0x10e8) by lia.
      intros x Hx. apply W2. lia.
  + apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply (fresh_ok_slots nx0). eapply after_call_fresh. exact Hac.
  + exact HLIB'.
  + rewrite <- Hpc'. apply (HK fx' FRM' (ext_call E (s_next (c_ss cs)) R') R' M'); [|exact HC'].
    eapply env_agree_le; [apply ext_call_agree | eapply after_call_nx0; exact Hac].
Qed.

End NX0.

Theorem call_lib_ok : lib_stmt_U -> forall nx0, lib_sound_stmt nx0.
Proof. intros HL nx0 fx Hfrm. exact (@call_lib_sound' nx0 fx Hfrm HL). Qed.
