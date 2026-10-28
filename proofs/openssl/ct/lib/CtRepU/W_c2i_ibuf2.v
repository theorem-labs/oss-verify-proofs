(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Stdio ApBase ApParse ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac W_get_object W_get_object_walk W_c2i_ibuf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac step := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition c2i_ibuf_copy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C r PNEG neg lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (bytes : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (C, C + r); (PNEG, PNEG + 4)]%Z m m'
    /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' C [CB (Z.to_nat r) bytes] /\ rw_cells ctusegs m' PNEG [C4 (Z_to_bv 64 neg)].

Lemma lxor_byte : forall a b, 0 <= a < 256 -> (b = 0 \/ b = 255) -> 0 <= Z.lxor a b < 256.
Proof.
  intros a b Ha Hb. assert (Hb' : 0 <= b < 256) by lia.
  assert (NN : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia). split; [exact NN|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [lia|].
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lxor_0_l; lia|]. destruct (Z.eq_dec b 0) as [->|Nb]; [rewrite Z.lxor_0_r; lia|].
  apply (Z.log2_lt_pow2 (Z.lxor a b) 8); [lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Definition pbf (b : Z) : Z := Z.shiftr (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl b 56))) 7) 18446744073709551615) 56.
Lemma pbf_check : forallb (fun i => let b := Z.of_nat i in ((pbf b =? 0) && (b <? 128)) || ((pbf b =? 255) && (128 <=? b))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pb_cases : forall b, 0 <= b < 256 -> (pbf b = 0 /\ b < 128) \/ (pbf b = 255 /\ 128 <= b).
Proof.
  intros b Hb. pose proof pbf_check as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat b) ltac:(apply in_seq; lia)). cbv beta zeta in H. rewrite Z2Nat.id in H by lia.
  apply orb_true_iff in H. destruct H as [H|H]; apply andb_true_iff in H; destruct H as [H1 H2]; [left|right]; split; lia.
Qed.

Section Proofs.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo D : Z) (d : list Z) (cont plen r C PNEG : Z) (junk pj : list byte).
  Notation SP := (bv_unsigned sp).
  Notation b0 := (znth d cont).
  Notation neg := (Z.land (znth d cont) 128).
  Notation W := [(bv_unsigned sp - 48, bv_unsigned sp); (C, C + r); (PNEG, PNEG + 4)]%Z.
  Hypothesis MI0 : mem_inv ctusegs m.
  Hypothesis ST0 : stk ctusegs m lo SP.
  Hypothesis LO : 0 <= lo <= SP - 48.
  Hypothesis HB0 : bytes_at ctusegs m D (to_bytes d).
  Hypothesis DF : Forall (fun c => 0 <= c < 256) d.
  Hypothesis DRNG : 0 < D /\ D + zlength d <= lo.
  Hypothesis CT0 : 0 <= cont.
  Hypothesis PL1 : 1 <= plen < 2 ^ 31.
  Hypothesis CPL : cont + plen <= zlength d.
  Hypothesis RES : c2i_ibuf_len d cont plen = IbOk r.
  Hypothesis DST0 : rw_cells ctusegs m C [CB (Z.to_nat r) junk].
  Hypothesis LJ0 : length junk = Z.to_nat r.      (* [comment removed for export] *)
  Hypothesis CRNG : 0 < C /\ C + r <= lo.
  Hypothesis SEP_CD : D + zlength d <= C \/ C + r <= D.
  Hypothesis PN0 : rw_cells ctusegs m PNEG [CB 4 pj].
  Hypothesis PNR : SP <= PNEG /\ PNEG + 4 <= 2 ^ 63.

  Notation POST := (c2i_ibuf_copy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C r PNEG neg lo m).

  (* [comment removed for export] *)
  Lemma r_facts : (r = plen \/ (r = plen - 1 /\ 2 <= plen)) /\ 1 <= r.
  Proof using LJ0 PL1 RES.
    pose proof RES as H. unfold c2i_ibuf_len in H.
    destruct (Z.eqb_spec plen 0); [discriminate|]. destruct (Z.eqb_spec plen 1) as [E1|N1]; [injection H as E; lia|].
    set (pad := if b0 =? 0 then 1 else _) in H.
    assert (HP : pad = 0 \/ pad = 1) by (subst pad; destruct (b0 =? 0); [lia|]; destruct (b0 =? 255); [|lia]; destruct (forallb _ _); lia).
    destruct (negb (pad =? 0) && _); [discriminate|]. injection H as E. lia.
  Qed.

  Lemma ctx_facts : 0 <= SP < 2 ^ 64 /\ Z.of_nat (length (to_bytes d)) = zlength d /\ length junk = Z.to_nat r /\ 0 <= b0 < 256.
  Proof using DF LJ0.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    split; [lia|]. split; [apply zlength_to_bytes|]. split; [exact LJ0| apply znth_range; exact DF].
  Qed.

  (* [comment removed for export] *)
  Definition INV (FB : Z) (cs : list cell) (mX : word -> option byte) (bs : list byte) : Prop :=
    u8arr ctusegs mX C bs /\ length bs = Z.to_nat r /\ bytes_at ctusegs mX D (to_bytes d) /\
    mem_inv ctusegs mX /\ munch W m mX /\ wmono ctusegs m mX /\
    rw_cells ctusegs mX FB cs /\ stk ctusegs mX lo FB /\ rw_cells ctusegs mX PNEG [C4 (Z_to_bv 64 neg)] /\ SP + -48 <= FB.
  Local Notation fr32 jk := [CB 8 jk; C8 s1; C8 s0; C8 ra].

  Ltac open_inv H := destruct H as (DST & LBS & HB & MI & MU & WM & FR & ST & PN & LFB).

  Lemma cp_store_ok : forall FB cs mX bs P (k : nat) a,
    INV FB cs mX bs -> (0 <= P)%Z -> (P + Z.of_nat k <= r)%Z -> a = wa (C + P) -> store_ok ctusegs mX a k = true.
  Proof using LJ0.
    intros FB cs mX bs P k a I HP Hk Ha; open_inv I.
    eapply (F_strcpy.u8arr_store_ok_n mX C bs P k a DST); [lia| rewrite LBS; lia | exact Ha].
  Qed.

  Lemma cp_store : forall FB cs mX bs P xs a,
    INV FB cs mX bs -> (0 <= P)%Z -> (P + Z.of_nat (length xs) <= r)%Z -> a = wa (C + P) ->
    INV FB cs (write_to_mem mX a xs) (upd_bytes bs (Z.to_nat P) xs).
  Proof using CRNG DF LJ0 LO PNR SEP_CD.
    intros FB cs mX bs P xs a I HP Hk Ha. pose proof I as I'. open_inv I. pose proof ctx_facts as (SPR & DLEN & LJ & B0R).
    pose proof (cp_store_ok FB cs mX bs P (length xs) a I' HP Hk Ha) as SOK. subst a.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    - apply (F_strcpy.u8arr_write_bytes mX C bs P xs DST); [lia|]. rewrite LBS. lia.
    - rewrite upd_bytes_length; [exact LBS|]. rewrite LBS. lia.
    - apply bytes_at_write_other; [exact HB| lia| lia| rewrite DLEN; lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU| lia| lia|]. cbn [inside]. right. left. lia.
    - apply wmono_write. exact WM.
    - apply rw_cells_frame; [exact FR| lia| lia|]. cbn [cells_size csize Nat.add]. lia.
    - apply stk_write; [exact ST| lia| lia].
    - apply rw_cells_frame; [exact PN| lia| lia|]. cbn [cells_size csize Nat.add]. lia.
    - exact LFB.
  Qed.

  (* [comment removed for export] *)
  Lemma fin : forall jk mX bs (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 : word),
    INV (SP + -32) (fr32 jk) mX bs ->
    evt ctusegs POST
      (MS (mkR x1 (Z_to_bv 64 (SP + -32)) gp tp x5 x6 x7 sp (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x114794) fc None mX (seg_rom ctusegs)).
  Proof using DF LJ0 LO.
    intros until x28. intros I. open_inv I. pose proof ctx_facts as (SPR & DLEN & LJ & B0R).
    step. step. step. step. step. release_frame FR ST (bv_unsigned sp). step.
    apply evt_done. unfold c2i_ibuf_copy_post.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mX, bs.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [| exact PN]. rewrite <- LBS. apply rw_cells_of_u8arr. exact DST.
  Qed.

  (* [comment removed for export] *)
  Lemma tc_loop : forall k (j c pb : Z) (x5 x6 x7 x17 x28 : word) jk mX bs,
    Z.to_nat j = k -> 1 <= j <= r -> 0 <= c <= 1 -> (pb = 0 \/ pb = 255) ->
    INV (SP + -48) (C8 sp :: C8 (Z_to_bv 64 0x114794) :: fr32 jk) mX bs ->
    evt ctusegs POST
      (MS (mkR (Z_to_bv 64 0x114794) (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 (Z_to_bv 64 (SP + -32)) (Z_to_bv 64 r) (Z_to_bv 64 (- j))
               (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 pb) (Z_to_bv 64 (D + cont + (plen - r) + j)) (Z_to_bv 64 c) (Z_to_bv 64 (C + j)) x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x115020) fc None mX (seg_rom ctusegs)).
  Proof using CPL CRNG CT0 DF DRNG LJ0 LO PL1 PNR RES SEP_CD.
    induction k as [|k IH]; intros j c pb x5 x6 x7 x17 x28 jk mX bs Hk Hj Hc Hpb I; [lia|].
    pose proof I as I'. open_inv I. pose proof ctx_facts as (SPR & DLEN & LJ & B0R). pose proof r_facts as [RF R1].
    assert (HPR : 0 <= plen - r <= 1) by lia.
    pose proof (znth_range d (cont + (plen - r) + j - 1) DF) as BR.
    step. replace (D + cont + (plen - r) + j + -1) with (D + cont + (plen - r) + j - 1) by lia.
    pose proof (payload_read _ D d (cont + (plen - r) + j - 1) (wa (D + cont + (plen - r) + j - 1)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD.
    rewrite (zxb_lit (znth d (cont + (plen - r) + j - 1))) by lia.
    step. rewrite ?(unsigned_lit pb) by lia. rewrite ?(unsigned_lit (znth d (cont + (plen - r) + j - 1))) by lia.
    pose proof (lxor_byte (znth d (cont + (plen - r) + j - 1)) pb BR Hpb) as LX.
    step. rewrite ?(unsigned_lit c) by lia. rewrite ?(unsigned_lit (Z.lxor _ _)) by lia.
    pose proof (cp_store_ok _ _ mX bs (j - 1) 1 (Z_to_bv 64 (C + j + -1)) I' ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep. clear SOK. cbv beta.
    set (sum := c + Z.lxor (znth d (cont + (plen - r) + j - 1)) pb) in *.
    assert (SUMR : 0 <= sum <= 256) by lia.
    pose proof (cp_store _ _ mX bs (j - 1) (le1 (Z_to_bv 64 sum)) (Z_to_bv 64 (C + j + -1)) I' ltac:(lia) ltac:(rewrite length_le1; cbn; lia) ltac:(unfold wa; f_equal; lia)) as I2.
    remember (write_to_mem mX (Z_to_bv 64 (C + j + -1)) (le1 (Z_to_bv 64 sum))) as m2 eqn:Em. clear Em.
    remember (upd_bytes bs (Z.to_nat (j - 1)) (le1 (Z_to_bv 64 sum))) as bs2 eqn:Ebs. clear Ebs.
    clear I' DST LBS HB MI MU WM FR ST PN LFB.
    step. step. zstep.
    assert (SH : 0 <= Z.shiftr sum 8 <= 1) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 8) with 256; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    setreg 15 (Z_to_bv 64 (Z.shiftr sum 8)) ltac:(f_equal; unfold bv_wrap; change (bv_modulus 32) with 4294967296; rewrite (Z.mod_small sum) by lia; symmetry; apply swrap32_small; lia).
    step. if_cases KX; zc KX.
    - assert (J2 : j <> 1) by (intro E; rewrite E in KX; apply KX; reflexivity). clear KX.
      replace (C + j + -1) with (C + (j - 1)) by lia. replace (D + cont + (plen - r) + j - 1) with (D + cont + (plen - r) + (j - 1)) by lia.
      replace (- j + 1) with (- (j - 1)) by lia.
      eapply (IH (j - 1) (Z.shiftr sum 8) pb); [clear - Hk; lia| clear - Hj J2; lia| exact SH| exact Hpb| exact I2].
    - assert (KX' : Z.land (- j + 1) 18446744073709551615 = 0) by (destruct (Z.eq_dec (Z.land (- j + 1) 18446744073709551615) 0); [assumption| exfalso; tauto]).
      assert (J1 : j = 1) by (change 18446744073709551615 with (Z.ones 64) in KX'; rewrite Z.land_ones in KX' by (clear; lia); clear - KX' Hj RF R1 PL1; Z.div_mod_to_equations; lia).
      clear KX.
      pose proof I2 as I3. open_inv I3.
      step. step. step.
      change (C8 sp :: C8 (Z_to_bv 64 0x114794) :: fr32 jk) with ([C8 sp; C8 (Z_to_bv 64 0x114794)] ++ fr32 jk) in FR.
      apply rw_cells_app in FR. destruct FR as [FR2 FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      replace (SP + -48 + 16) with (SP + -32) in FR by lia.
      release_frame FR2 ST (SP + -32).
      step. eapply (fin jk m2 bs2).
      split; [exact DST|]. split; [exact LBS|]. split; [exact HB|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|].
      split; [exact FR|]. split; [exact ST|]. split; [exact PN| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ibuf_ge2 : forall pad, 2 <= plen ->
    pad = (if b0 =? 0 then 1 else if b0 =? 255
           then (if forallb (fun b => b =? 0) (firstn (Z.to_nat (plen - 1)) (skipn (Z.to_nat (cont + 1)) d)) then 0 else 1) else 0) ->
    c2i_ibuf_len d cont plen = if negb (pad =? 0) && (neg =? Z.land (znth d (cont + 1)) 128) then IbPad else IbOk (plen - pad).
  Proof using LJ0 PL1.
    intros pad H2 ->. unfold c2i_ibuf_len. rewrite (proj2 (Z.eqb_neq plen 0)) by lia. rewrite (proj2 (Z.eqb_neq plen 1)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma or_loop2 : forall fuel (i acc : Z) (x6 x7 x9 x28 : word) jk mX bs (POST' : machine_state -> Prop),
    INV (SP + -32) (fr32 jk) mX bs -> Z.to_nat (plen - i) = fuel -> 1 <= i < plen -> 0 <= acc < 256 ->
    (acc = 0 <-> forall k, 1 <= k < i -> znth d (cont + k) = 0) ->
    (forall acc' (x6' : word), 0 <= acc' < 256 ->
       (acc' = 0 <-> forall k, 1 <= k < plen -> znth d (cont + k) = 0) ->
       evt ctusegs POST'
         (MS (mkR ra (Z_to_bv 64 (SP + -32)) gp tp (Z_to_bv 64 (D + cont + plen)) x6' x7 sp x9 (Z_to_bv 64 C) (Z_to_bv 64 (D + cont + plen)) (Z_to_bv 64 (D + cont)) (Z_to_bv 64 plen)
                  (Z_to_bv 64 b0) (Z_to_bv 64 neg) (Z_to_bv 64 acc') (Z_to_bv 64 (D + cont + plen)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
             F (Z_to_bv 64 0x114720) fc None mX (seg_rom ctusegs))) ->
    evt ctusegs POST'
      (MS (mkR ra (Z_to_bv 64 (SP + -32)) gp tp (Z_to_bv 64 (D + cont + i)) x6 x7 sp x9 (Z_to_bv 64 C) (Z_to_bv 64 (D + cont + i)) (Z_to_bv 64 (D + cont)) (Z_to_bv 64 plen)
               (Z_to_bv 64 b0) (Z_to_bv 64 neg) (Z_to_bv 64 acc) (Z_to_bv 64 (D + cont + plen)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x114708) fc None mX (seg_rom ctusegs)).
  Proof using CPL CRNG CT0 DF DRNG LJ0 LO PNR.
    induction fuel as [|fuel IH]; intros i acc x6 x7 x9 x28 jk mX bs POST' I Hf Hi Hacc INVA KONT; [lia|].
    pose proof I as I'. open_inv I. pose proof ctx_facts as (SPR & DLEN & LJ & B0R).
    pose proof (znth_range d (cont + i) DF) as BR.
    pose proof (payload_read _ D d (cont + i) (wa (D + cont + i)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD.
    rewrite (zxb_lit (znth d (cont + i))) by lia.
    step. step. step. rewrite ?(unsigned_lit (znth d (cont + i))) by lia. rewrite ?(unsigned_lit acc) by lia.
    pose proof (lor_byte acc (znth d (cont + i)) Hacc BR) as LB'.
    assert (INVB : Z.lor acc (znth d (cont + i)) = 0 <-> forall k, 1 <= k < i + 1 -> znth d (cont + k) = 0).
    { rewrite (lor_zero_iff acc (znth d (cont + i))) by lia. rewrite INVA. split.
      - intros [H1 H2] k Hk. destruct (Z.eq_dec k i) as [->|Hne]; [exact H2| apply H1; lia].
      - intros H1. split; [intros k Hk; apply H1; lia| apply H1; lia]. }
    step. if_cases KX; zc KX.
    - replace (D + cont + i + 1) with (D + cont + (i + 1)) by lia.
      eapply (IH (i + 1) (Z.lor acc (znth d (cont + i)))); [exact I'| lia| lia| exact LB'| exact INVB| exact KONT].
    - assert (Ei : i + 1 = plen) by lia.
      replace (D + cont + i + 1) with (D + cont + plen) by lia.
      eapply KONT; [exact LB'|]. rewrite <- Ei. exact INVB.
  Qed.

  (* [comment removed for export] *)
  Lemma tc_entry : forall jk (x5 x6 x7 x11 x16 x17 x28 : word) (npad pad src : Z) mX bs,
    INV (SP + -32) (fr32 jk) mX bs -> (pad = 0 \/ pad = 1) -> npad = - pad -> r = plen - pad -> src = D + cont + pad ->
    evt ctusegs POST
      (MS (mkR ra (Z_to_bv 64 (SP + -32)) gp tp x5 x6 x7 sp (Z_to_bv 64 npad) (Z_to_bv 64 C) x11 (Z_to_bv 64 src) (Z_to_bv 64 plen)
               (Z_to_bv 64 b0) (Z_to_bv 64 neg) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x114774) fc None mX (seg_rom ctusegs)).
  Proof using CPL CRNG CT0 DF DRNG LJ0 LO PL1 PNR RES SEP_CD.
    intros jk x5 x6 x7 x11 x16 x17 x28 npad pad src mX bs I Hpad Hnp Hr Hsrc. pose proof I as I'. open_inv I. pose proof ctx_facts as (SPR & DLEN & LJ & B0R). pose proof r_facts as [RF R1].
    subst npad src. zstep. replace (- pad + plen) with r by lia. rewrite ?(unsigned_lit r) by lia.
    step. if_cases KC; zc KC; [exfalso; lia|].
    do 5 zstep. step.
    carve_frame 16%nat ST. do 4 step.
    step. if_cases KR; zc KR; [exfalso; lia|].
    step. step. step. step. step.
    change (Z.shiftr (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl b0 56))) 7) 18446744073709551615) 56) with (pbf b0).
    pose proof (pb_cases b0 B0R) as PBC.
    assert (PBR : 0 <= pbf b0 < 2 ^ 64) by (destruct PBC as [[E _]|[E _]]; rewrite E; lia).
    assert (HC : 0 <= Z.land (pbf b0) 1 <= 1) by (destruct PBC as [[E _]|[E _]]; rewrite E; [change (Z.land 0 1) with 0| change (Z.land 255 1) with 1]; lia).
    rewrite (unsigned_lit (pbf b0)) by lia. rewrite (unsigned_lit r) by lia.
    replace (0 + - r) with (- r) by lia. replace (r + (D + cont + pad)) with (D + cont + (plen - r) + r) by lia.
    pose proof FR as FRX. replace (SP + -32) with (SP + -48 + Z.of_nat (cells_size [C8 sp; C8 (Z_to_bv 64 0x114794)])) in FRX
      by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    pose proof (proj2 (rw_cells_app _ _ [C8 sp; C8 (Z_to_bv 64 0x114794)] (fr32 jk)) (conj FR0 FRX)) as FRC.
    cbn [app] in FRC.
    eapply (tc_loop (Z.to_nat r) r (Z.land (pbf b0) 1) (pbf b0)); [lia| lia| exact HC| destruct PBC as [[E _]|[E _]]; lia|].
    split; [exact DST|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact FRC|]. split; [exact ST|]. split; [eassumption| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pad1_check : forall (x5 x6 x7 x9 x11 x16 x17 x28 : word) jk mX bs,
    INV (SP + -32) (fr32 jk) mX bs -> 2 <= plen -> r = plen - 1 -> neg <> Z.land (znth d (cont + 1)) 128 ->
    evt ctusegs POST
      (MS (mkR ra (Z_to_bv 64 (SP + -32)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 C) x11 (Z_to_bv 64 (D + cont)) (Z_to_bv 64 plen)
               (Z_to_bv 64 b0) (Z_to_bv 64 neg) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x114724) fc None mX (seg_rom ctusegs)).
  Proof using CPL CRNG CT0 DF DRNG LJ0 LO PL1 PNR RES SEP_CD.
    intros x5 x6 x7 x9 x11 x16 x17 x28 jk mX bs I H2 Hr Hne. pose proof I as I'. open_inv I. pose proof ctx_facts as (SPR & DLEN & LJ & B0R).
    pose proof (znth_range d (cont + 1) DF) as B1R.
    pose proof (land128_cases b0 B0R) as C0. pose proof (land128_cases (znth d (cont + 1)) B1R) as C1.
    pose proof (payload_read _ D d (cont + 1) (wa (D + cont + 1)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD.
    rewrite (zxb_lit (znth d (cont + 1))) by lia.
    step. rewrite ?(unsigned_lit (znth d (cont + 1))) by lia.
    step. if_cases KP; zc KP; [| exfalso; lia].
    step. eapply (tc_entry _ _ _ _ _ _ _ _ (-1) 1 (D + cont + 1)); [exact I'| lia| reflexivity| lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Theorem cp_main : PNEG mod 4 = 0 -> forall (t0 t1 t2 t3 a4 a5 a6 a7 : word),
    evt ctusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 PNEG) (Z_to_bv 64 (D + cont)) (Z_to_bv 64 plen) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 C2I_IBUF) fc None m (seg_rom ctusegs)).
  Proof using CPL CRNG CT0 DF DRNG DST0 HB0 LJ0 LO MI0 PL1 PN0 PNR RES SEP_CD ST0.
    intros PA4 t0 t1 t2 t3 a4 a5 a6 a7. pose proof ctx_facts as (SPR & DLEN & LJ & B0R). pose proof r_facts as [RF R1]. unfold C2I_IBUF.
    assert (DSTF : frozen (u8arr ctusegs m C junk)) by exact (u8arr_of_rw_cells _ _ _ _ _ DST0).
    pose proof ST0 as ST. pose proof MI0 as MI. pose proof HB0 as HB. pose proof PN0 as PN. clear DST0.
    pose proof (munch_refl [(SP - 48, SP); (PNEG, PNEG + 4)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    carve_frame 32%nat ST. do 5 step.
    step. if_cases K0; zc K0; [exfalso; lia|].
    pose proof (payload_read _ D d cont (wa (D + cont)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
    rewrite (zxb_lit b0) by lia.
    step. rewrite ?(unsigned_lit b0) by lia.
    step. if_cases KN; zc KN; [exfalso; lia|].
    step. name_mem m1.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jk := j) in FR; clearbody jk end.
    assert (I : INV (SP + -32) (fr32 jk) m1 junk).
    { split. { eapply u8arr_transport; [exact DSTF| exact MU| exact WM| cbn; rewrite LJ; lia]. }
      split; [exact LJ|]. split; [exact HB|]. split; [exact MI|].
      split. { eapply munch_weaken; [| exact MU]. intros x; cbn; lia. }
      split; [exact WM|]. split; [exact FR|]. split; [exact ST|]. split; [exact PN| lia]. }
    clear DSTF.
    step. step. if_cases K1; zc K1.
    - (* [comment removed for export] *)
      pose proof (payload_read _ D d cont (wa (D + cont)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
      rewrite (zxb_lit b0) by lia.
      step. if_cases KB0; zc KB0.
      + (* [comment removed for export] *)
        pose proof (ibuf_ge2 1 ltac:(lia) ltac:(rewrite (proj2 (Z.eqb_eq _ _) KB0); reflexivity)) as EQ. rewrite RES in EQ.
        destruct (Z.eqb_spec neg (Z.land (znth d (cont + 1)) 128)) as [EN|NN]; [discriminate|]. injection EQ as ER.
        eapply pad1_check; [exact I| lia| lia| exact NN].
      + step. step. if_cases KFF; zc KFF.
        * (* [comment removed for export] *)
          pose proof (ibuf_ge2 0 ltac:(lia) ltac:(rewrite (proj2 (Z.eqb_neq _ _) KB0), (proj2 (Z.eqb_neq _ _) KFF); reflexivity)) as EQ. rewrite RES in EQ.
          cbn [Z.eqb negb andb] in EQ. injection EQ as ER.
          step. step.
          eapply (tc_entry _ _ _ _ _ _ _ _ 0 0 (D + cont)); [exact I| lia| reflexivity| lia| lia].
        * (* [comment removed for export] *)
          step. step. step. step. udecide. step. step. step. step. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
          replace (D + cont + (plen + -2) + 2) with (D + cont + plen) by lia.
          eapply (or_loop2 (Z.to_nat (plen - 1)) 1 0); [exact I| lia| lia| lia| split; [intros _ k Hk; lia| intros; reflexivity]|].
          intros acc' x6' Hacc' HINV.
          step. if_cases KA; zc KA.
          -- (* [comment removed for export] *)
             assert (FB : forallb (fun b => b =? 0) (firstn (Z.to_nat (plen - 1)) (skipn (Z.to_nat (cont + 1)) d)) = true).
             { apply (proj2 (zeros_iff d (cont + 1) (plen - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
               intros k Hk. replace (cont + 1 + k) with (cont + (k + 1)) by lia. apply (proj1 HINV ltac:(lia)). lia. }
             pose proof (ibuf_ge2 0 ltac:(lia) ltac:(rewrite (proj2 (Z.eqb_neq _ _) KB0), (proj2 (Z.eqb_eq _ _) KFF), FB; reflexivity)) as EQ. rewrite RES in EQ.
             cbn [Z.eqb negb andb] in EQ. injection EQ as ER.
             step. step.
             eapply (tc_entry _ _ _ _ _ _ _ _ 0 0 (D + cont)); [exact I| lia| reflexivity| lia| lia].
          -- (* [comment removed for export] *)
             destruct (forallb (fun b => b =? 0) (firstn (Z.to_nat (plen - 1)) (skipn (Z.to_nat (cont + 1)) d))) eqn:FB.
             { exfalso. apply KA. apply (proj2 HINV). intros k Hk. replace (cont + k) with (cont + 1 + (k - 1)) by lia.
               apply (proj1 (zeros_iff d (cont + 1) (plen - 1) ltac:(lia) ltac:(lia) ltac:(lia)) FB). lia. }
             pose proof (ibuf_ge2 1 ltac:(lia) ltac:(rewrite (proj2 (Z.eqb_neq _ _) KB0), (proj2 (Z.eqb_eq _ _) KFF), FB; reflexivity)) as EQ. rewrite RES in EQ.
             destruct (Z.eqb_spec neg (Z.land (znth d (cont + 1)) 128)) as [EN|NN]; [discriminate|]. injection EQ as ER.
             eapply pad1_check; [exact I| lia| lia| exact NN].
    - (* [comment removed for export] *)
      assert (ER : r = 1) by (pose proof RES as EQ; unfold c2i_ibuf_len in EQ; rewrite (proj2 (Z.eqb_neq plen 0)) in EQ by lia; rewrite (proj2 (Z.eqb_eq plen 1)) in EQ by lia; injection EQ as E'; lia).
      step. if_cases KC; zc KC; [exfalso; lia|].
      pose proof (payload_read _ D d cont (wa (D + cont)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
      rewrite (zxb_lit b0) by lia.
      step. if_cases KNEG; zc KNEG.
      + (* [comment removed for export] *)
        pose proof (cp_store_ok _ _ m1 junk 0 1 (Z_to_bv 64 C) I ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
        zstep. clear SOK. cbv beta.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?xs) _) =>
          pose proof (cp_store _ _ m1 junk 0 xs a I ltac:(lia) ltac:(rewrite ?length_le1; cbn; lia) ltac:(unfold wa; f_equal; lia)) as I2;
          remember (write_to_mem mX a xs) as m2 eqn:Em; clear Em;
          remember (upd_bytes junk (Z.to_nat 0) xs) as bs2 eqn:Ebs; clear Ebs end.
        clear I. step. setreg 9 (Z_to_bv 64 r) ltac:(f_equal; lia). eapply fin. exact I2.
      + (* [comment removed for export] *)
        zstep.
        pose proof (cp_store_ok _ _ m1 junk 0 1 (Z_to_bv 64 C) I ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
        zstep. clear SOK. cbv beta.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?xs) _) =>
          pose proof (cp_store _ _ m1 junk 0 xs a I ltac:(lia) ltac:(rewrite ?length_le1; cbn; lia) ltac:(unfold wa; f_equal; lia)) as I2;
          remember (write_to_mem mX a xs) as m2 eqn:Em; clear Em;
          remember (upd_bytes junk (Z.to_nat 0) xs) as bs2 eqn:Ebs; clear Ebs end.
        clear I. step. setreg 9 (Z_to_bv 64 r) ltac:(f_equal; lia). eapply fin. exact I2.
  Qed.

End Proofs.

(* [comment removed for export] *)
Theorem c2i_ibuf_copy_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo D : Z) (d : list Z) (cont plen r C PNEG : Z) (junk pj : list byte),
  mem_inv ctusegs m -> stk ctusegs m lo (bv_unsigned sp) -> 0 <= lo <= bv_unsigned sp - 48 ->
  bytes_at ctusegs m D (to_bytes d) -> Forall (fun c => 0 <= c < 256) d -> 0 < D /\ D + zlength d <= lo ->
  0 <= cont -> 1 <= plen < 2 ^ 31 -> cont + plen <= zlength d ->
  c2i_ibuf_len d cont plen = IbOk r ->
  rw_cells ctusegs m C [CB (Z.to_nat r) junk] -> 0 < C /\ C + r <= lo -> (D + zlength d <= C \/ C + r <= D) ->
  rw_cells ctusegs m PNEG [CB 4 pj] -> bv_unsigned sp <= PNEG /\ PNEG + 4 <= 2 ^ 63 -> PNEG mod 4 = 0 ->
  evt ctusegs (c2i_ibuf_copy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C r PNEG (Z.land (znth d cont) 128) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 PNEG) (Z_to_bv 64 (D + cont)) (Z_to_bv 64 plen) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 C2I_IBUF) fc None m (seg_rom ctusegs)).
Proof.
  intros until pj. intros MI ST LO HB DF DR CT0 PL1 CPL RES DST CR SEP PN PNR PA4.
  assert (LJ : length junk = Z.to_nat r) by (destruct DST as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [Hn _]; exact Hn).
  eapply (cp_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m lo D d cont plen r C PNEG junk pj); eassumption.
Qed.
End WithCeiling0.
