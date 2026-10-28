(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_get_object_walk W_c2i_ibuf W_c2i_int W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_leaves W_memdup W_sct_set1_signature SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Lemma lor_shl8 : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (a * 256) b = a * 256 + b.
Proof.
  intros a b Ha Hb.
  assert (L : Z.land (a * 256) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8).
    - replace (a * 256) with (a * 2 ^ 8) by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite (Z.bits_above_log2 b i); [apply Bool.andb_false_r| lia|].
      destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia| lia]. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

(* [comment removed for export] *)
Lemma subw_m4 : forall z, 0 <= z < 2 ^ 16 -> Z_to_bv 64 (bv_swrap 32 (z - (2 ^ 64 - 4))) = Z_to_bv 64 (z + 4).
Proof.
  intros z Hz. f_equal. rewrite swrap32_eq.
  rewrite <- (Z.mod_add (z - (2 ^ 64 - 4) + 2147483648) 4294967296 4294967296) by lia.
  replace (z - (2 ^ 64 - 4) + 2147483648 + 4294967296 * 4294967296) with (z + 4 + 2147483648) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Section Act.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (errv canary : word) (K : list block).
  Variables (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (c : list Z) (D p len PIN : Z).
  Hypothesis PRE : ap_pre s st m OW LB E bo sp lo B errv canary O2I_SCT_SIGNATURE_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis FRM : frm0 fc.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_ok m LB D c.
  Hypothesis CNE : 0 < zlength c.
  Hypothesis P0 : 0 <= p.
  Hypothesis LEN0 : 0 <= len.
  Hypothesis PL : p + len <= zlength c.
  Hypothesis HXIN : In (sc_blk x, adr (sc_blk x), SCT_SIZE) LB.
  Hypothesis SEPD : D + zlength c <= adr (sc_blk x) \/ adr (sc_blk x) + SCT_SIZE <= D.
  Hypothesis PAYNE : forall pb PA psz, In (pb, PA, psz) LB -> PA <= D -> D + zlength c <= PA + psz -> pb <> sc_blk x.
  Hypothesis HX : rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs).
  Hypothesis V0 : sc_version x = 0.
  Hypothesis SIG0 : sc_sig x = None.
  Hypothesis XIN : forall b, In b (sct_blocks adr x) -> In b LB.
  Hypothesis XND : List.NoDup (map blk_id (sct_blocks adr x)).
  Hypothesis PINlo : bv_unsigned sp <= PIN.
  Hypothesis PINhi : PIN + 8 <= B.
  Hypothesis ALP : PIN mod 8 = 0.
  Hypothesis HPIN : rw_cells ctusegs m PIN [C8 (wz (D + p))].

  Local Notation A := (adr (sc_blk x)) (only parsing).
  Local Notation W0 := ([(bv_unsigned sp - O2I_SCT_SIGNATURE_STACK, bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + 104); (PIN, PIN + 8)]%Z) (only parsing).
  Local Notation X0 := ([(PIN, PIN + 8); (adr (sc_blk x), adr (sc_blk x) + 104)] ++ LIBW_AP) (only parsing).
  Local Notation SPOST := (o2i_sig_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr x vs c D p len PIN) (only parsing).
  Definition sg_frame : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition sg_inv (m1 : mem) (x1 : sctr bptr) : Prop :=
    munch W0 m m1 /\ wmono ctusegs m m1 /\ mem_inv ctusegs m1 /\ stk ctusegs m1 lo (bv_unsigned sp + -64)
    /\ rw_cells ctusegs m1 (bv_unsigned sp + -64) sg_frame
    /\ bytes_at ctusegs m1 D (to_bytes c) /\ rw_cells ctusegs m1 3355012 [C4 errv]
    /\ rw_cells ctusegs m1 PIN [C8 (wz (D + p))]
    /\ rw_cells ctusegs m1 (adr (sc_blk x)) (sct_cells adr x1 (-1) vs).

  Lemma ctx_facts :
    Forall (fun b => 0 <= b < 256) c /\ 0 < D /\ D + zlength c < 2 ^ 63 /\ zlength c < 2 ^ 30 /\ D + zlength c <= alloc_ceiling
    /\ alloc_ceiling <= lo /\ 3493888 <= lo /\ lo <= bv_unsigned sp - O2I_SCT_SIGNATURE_STACK /\ bv_unsigned sp <= B /\ B < 2 ^ 63 /\ 0 <= bv_unsigned sp < 2 ^ 64
    /\ Z.of_nat (length (to_bytes c)) = zlength c
    /\ 0 < adr (sc_blk x) /\ adr (sc_blk x) + 104 <= alloc_ceiling /\ (adr (sc_blk x) + 104 <= 65536 \/ 3493888 <= adr (sc_blk x))
    /\ ~ In (sc_blk x) (map blk_id OW) /\ List.NoDup (map blk_id (OW ++ LB)).
  Proof using CNE HXIN PAY PAYNE PINlo PL PRE SEPD.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    destruct PAY as (_ & HF' & D0 & D63 & D30 & HB).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (DC' : D + zlength c <= alloc_ceiling).
    { destruct HB as [->|(blk & HBLK & BL1 & BL2)]; [exfalso; revert CNE; cbn; unfold zlength; cbn; lia|].
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HBLK)) as (BB0 & BB1 & BB2 & BB3 & BB4). lia. }
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HXIN)) as (BX0 & BX1 & BX2 & BX3 & BX4). unfold SCT_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    pose proof (LH_nodup _ _ _ HEAP) as ND.
    assert (NOW : ~ In (sc_blk x) (map blk_id OW)).
    { rewrite map_app in ND. intros Hin. exact (NoDup_app_disjoint _ _ _ ND Hin (in_ids _ _ _ _ HXIN)). }
    unfold GLOBALS_TOP in *.
    repeat (split; [first [assumption|lia|apply zlength_to_bytes]|]). exact ND.
  Qed.

  Lemma ALX : adr (sc_blk x) mod 16 = 0.
  Proof using HXIN PRE.
    destruct PRE as (HEAP & _). exact (proj2 (proj2 (proj2 (proj2 (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HXIN)))))).
  Qed.

  Local Ltac sg_unpack GI := destruct GI as (MU & WM & MI & ST & FR & HB & ERR & HP & HC); unfold sg_frame in FR.
  Local Ltac ctx := pose proof ctx_facts as (DF & D0 & D63 & D30 & DCEIL & CEIL & GLO & LO & SPB & B63 & SPR & DLEN & BX0 & BXC & BXI & NOW & NDL);
                   unfold O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK in LO; pose proof SEPD as SEPD'; unfold SCT_SIZE in SEPD'.

  (* [comment removed for export] *)
  Lemma pre_at_call0 : forall m2,
    munch W0 m m2 -> wmono ctusegs m m2 -> mem_inv ctusegs m2 -> stk ctusegs m2 lo (bv_unsigned sp + -64) -> rw_cells ctusegs m2 3355012 [C4 errv] ->
    ap_pre s st m2 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo B errv canary ERR_SET_ERROR_STACK
    /\ lx_pres LB (bv_unsigned sp) X0 m m2
    /\ kept K m m2.
  Proof using ALP CNE HXIN KOW PAY PAYNE PINhi PINlo PL PRE SEPD.
    intros m2 MU WM MI ST ERR. ctx.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    unfold O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK in MU.
    assert (HW : Forall (fun iv : Z * Z => lo <= fst iv \/ iv = (3355012, 3355016)
               \/ (exists q Aq n, In (q, Aq, n) (OW ++ LB) /\ ~ In q (map blk_id OW) /\ Aq <= fst iv /\ snd iv <= Aq + n))
               [(bv_unsigned sp - (64 + (80 + 96 + 48 + 8192)), bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + 104); (PIN, PIN + 8)]%Z).
    { constructor; [left; cbn; lia|]. constructor; [| constructor; [left; cbn; lia| constructor]]. right. right. exists (sc_blk x), (adr (sc_blk x)), 104.
      split; [apply in_app_iff; right; exact HXIN|]. split; [exact NOW|]. cbn. lia. }
    assert (HEAP2 : RHEAP s (OW ++ LB) m2).
    { eapply LH_frame; [exact HEAP|exact MU|exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [apply W_ok_stack; cbn; lia| constructor]].
      eapply (W_ok_block _ (sc_blk x, adr (sc_blk x), 104)); [apply in_app_iff; right; exact HXIN| cbn; lia| cbn; lia]. }
    split; [|split].
    - unfold ap_pre. rewrite ESP. split; [exact HEAP2|].
      split. { eapply (ap_state_of_munch_blk st m m2 OW E bo s (OW ++ LB)); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|exact HW]. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch s (OW ++ LB) _ m m2); [exact DC|intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OW _ i q k OD Hd))|exact HEAP|exact CEIL|exact MU|exact WM|].
               eapply Forall_impl; [|exact HW]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
               exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros i q' k Hd E0. apply H2. rewrite <- E0. eapply in_ids. exact (proj1 (optb_ok_nth OW _ i q' k OD Hd)). }
      split. { eapply rauxv_ok_frame; [exact AUX|exact MU|exact WM|]. constructor; [cbn; unfold RAUXV_CELL, GLOBALS_TOP in *; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
               constructor; [cbn; unfold RAUXV_CELL, GLOBALS_TOP in *; lia| constructor]. }
      split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold ERR_SET_ERROR_STACK; lia|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAP2|].
      split; [exact MI|]. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia. rewrite Zminus_mod, SP16. reflexivity.
    - eapply lx_pres_of_munch; [exact MU|exact WM|]. intros a Ha [HXa Hc]. cbn [rin_ivs fst snd app] in HXa. cbn.
      destruct Hc as [Hc|[(b & Hb & Hr)|Hc]].
      + repeat split; try lia; tauto.
      + destruct b as [[q Aq] n]. cbn [blk_addr blk_size fst snd] in Hr.
        pose proof (blk_bounds _ _ _ q Aq n HEAP ltac:(apply in_app_iff; right; exact Hb)). repeat split; lia.
      + unfold ralloc_static in Hc. repeat split; lia.
    - eapply (kept_of_munch s (OW ++ LB) _ m m2 K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      eapply Forall_impl; [|exact HW]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
      exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros Hin. apply H2. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). rewrite <- Eb. apply in_map. apply KOW. exact Hb.
  Qed.

  Lemma pre_at_call : forall m2 x1, sg_inv m2 x1 ->
    ap_pre s st m2 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo B errv canary ERR_SET_ERROR_STACK
    /\ lx_pres LB (bv_unsigned sp) X0 m m2
    /\ kept K m m2.
  Proof using ALP CNE HXIN KOW PAY PAYNE PINhi PINlo PL PRE SEPD. intros m2 x1 GI. sg_unpack GI. apply pre_at_call0; assumption. Qed.

  (* [comment removed for export] *)
  Lemma pre_resp : forall sF (st' : ap_st bptr) mX OW' LB' (errv' : word) stk0,
    ap_pre sF st' mX OW' LB' E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo B errv' canary stk0 ->
    stk ctusegs mX lo (bv_unsigned sp) ->
    ap_pre sF st' mX OW' LB' E bo sp lo B errv' canary 0.
  Proof using CNE HXIN PAY PAYNE PINlo PL PRE SEPD.
    intros until stk0. intros PREX ST4. ctx.
    destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16).
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP16e).
    unfold ap_pre. repeat (split; [first [assumption|lia]|]). exact SP16e.
  Qed.

  (* [comment removed for export] *)
  Lemma set_sig_cells_rec : forall (x1 : sctr bptr) pn C n et,
    sc_blk x1 = sc_blk x -> sc_logid x1 = sc_logid x -> sc_ext x1 = sc_ext x -> sc_blob x1 = sc_blob x ->
    ~ In pn (map blk_id LB) ->
    sct_cells (fun b => if bptr_eqb b pn then C else adr b) (set_sig (Some (pn, n)) x1) et 0 = set_sig_cells adr x1 et C n.
  Proof using XIN.
    intros x1 pn C n et E1 E2 E3 E4 NIN. destruct x1 as [xb xv xbl xlg xts xex xexl xh xsa xsg]. cbn in E1, E2, E3, E4. subst xb xlg xex xbl.
    unfold sct_cells, set_sig_cells. cbn -[optr logid_len u32 osz32 wz].
    change (optr (fun b : bptr => if bptr_eqb b pn then C else adr b) (Some (pn, n))) with (if bptr_eqb pn pn then C else adr pn). rewrite bptr_eqb_refl.
    assert (OB : forall o, (forall q k, o = Some (q, k) -> In (q, adr q, k) LB) -> optr (fun b => if bptr_eqb b pn then C else adr b) o = optr adr o).
    { intros [[q k]|] Ho; cbn; [|reflexivity]. rewrite (bptr_eqb_neq q pn); [reflexivity|]. intros ->. apply NIN. eapply in_ids. apply (Ho pn k). reflexivity. }
    rewrite !OB; [reflexivity| | |].
    - intros q k Hq. apply XIN. unfold sct_blocks. rewrite Hq. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
    - intros q k Hq. apply XIN. unfold sct_blocks. unfold osz32 in Hq |- *. destruct (sc_logid x) as [q0|]; cbn in Hq |- *; [| discriminate]. injection Hq; intros <- <-. left. reflexivity.
    - intros q k Hq. apply XIN. unfold sct_blocks. rewrite Hq. rewrite !in_app_iff. right. right. right. left. left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition site_ok (base : Z) (nj : nat) (rs : rsite) : Prop :=
    (base = 0x19c534 /\ nj = 7%nat /\ rs = RS_sig_len4) \/ (base = 0x19c5e8 /\ nj = 6%nat /\ rs = RS_sig_nid) \/ (base = 0x19c5cc /\ nj = 7%nat /\ rs = RS_sig_overrun).

  (* [comment removed for export] *)
  Definition raise_post (x8 x9 x18 x19 x20 x21 x22 : word) (m2 : mem) (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word),
      ms' = MS (mkR (Z_to_bv 64 0x19c614) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4' t5' t6')
               F' (Z_to_bv 64 0x19c614) fc' None m' (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
      /\ ap_pre s' (snd r) m' OW' LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo B errv' canary 0
      /\ lx_pres LB (bv_unsigned sp + -64) LIBW_AP m2 m'
      /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
      /\ blocks_kept K (snd r) OW' m m'.

  Lemma raise_seq : forall base nj rs (x1' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word) m2 x1,
    site_ok base nj rs -> sg_inv m2 x1 ->
    implM ctusegs (interp (ap_embed (err_raise rs st))) s (raise_post x8 x9 x18 x19 x20 x21 x22 m2)
      (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 base) fc None m2 (seg_rom ctusegs)).
  Proof using ALP CNE FRM HF HM HXIN KIDS KOW PAY PAYNE PINhi PINlo PL PRE SEPD TP.
    intros until x1. intros SITE GI.
    destruct (pre_at_call m2 x1 GI) as (PRE2 & LX2 & KP2).
    sg_unpack GI. ctx. subst tp.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    destruct (lit_ok_auto A_CT_OCT_C 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_ok_auto A_O2I_SCT_SIGNATURE 18 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    assert (RSF : rs_flen rs = 19) by (destruct SITE as [(_ & _ & ->)|[(_ & _ & ->)|(_ & _ & ->)]]; reflexivity).
    assert (RSN : rs_fnlen rs = 18) by (destruct SITE as [(_ & _ & ->)|[(_ & _ & ->)|(_ & _ & ->)]]; reflexivity).
    rewrite <- RSF in LF. rewrite <- RSN in LN.
    unfold err_raise.
    (* [comment removed for export] *)
    assert (TAIL : forall (r1 : unit * ap_st bptr) (sA : PState) (q5 q6 q7 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (F1 : bvmap 5 word) (fc1 : bv 32) mA OW1 (errv1 : word),
      frm0 fc1 -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get F k) ->
      ap_pre sA (snd r1) mA OW1 LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo B errv1 canary 0 ->
      lx_pres LB (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))) LIBW_AP m2 mA -> ps_so sA = ps_so s -> ps_fa sA = ps_fa s ->
      blocks_kept K (snd r1) OW1 m2 mA ->
      implM ctusegs (interp (ap_embed (abind (err_set_debug rs) (fun _ => err_set_error rs) (snd r1)))) sA (raise_post x8 x9 x18 x19 x20 x21 x22 m2)
        (MS (mkR (Z_to_bv 64 0x19c604) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) q5 q6 q7 x8 x9 (wz A_CT_OCT_C) (wz (rs_line rs)) (wz A_O2I_SCT_SIGNATURE) q13 q14 q15 q16 q17
                  x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 q28 q29 q30 q31)
            F1 (wz ERR_SET_DEBUG) fc1 None mA (seg_rom ctusegs))).
    { intros until errv1. intros FRM1 FE1 PREa LXa SOa FAa BKa.
      assert (KIDS1 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKa) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      eapply implM_abind.
      { pose proof (ERR_set_debug_walk HM HF rs A_CT_OCT_C A_O2I_SCT_SIGNATURE bo _ _ _ _ LF LN) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREa|rewrite ESP; unfold ERR_SET_DEBUG_STACK; lia]|reflexivity|exact FRM1|repeat split; reflexivity|exact (proj1 BKa)|exact KIDS1]. }
      intros r2 sB ms2 PO2. cbv beta in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                       & -> & FRM2 & FE2 & PREb & LXb & SOb & FAb & BKb & EBO2).
      subst bo2.
      replace (ret_pc (Z_to_bv 64 0x19c604)) with (Z_to_bv 64 0x19c604) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KIDS2 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKb) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      unfold implM. iprefix. do 4 step.
      ihere. to_implM.
      eapply implM_mono.
      { pose proof (ERR_set_error_walk rs 50 107 bo) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREb|rewrite ESP; unfold ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM2| |exact (proj1 BKb)|exact KIDS2].
        cbn. unfold ERR_LIB_SYS, MallocRep.wz. repeat split; try reflexivity; try lia. all: destruct SITE as [(_ & _ & ->)|[(_ & _ & ->)|(_ & _ & ->)]]; reflexivity. }
      intros r3 sC ms3 PO3. cbv beta in PO3.
      destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & errv3 & bo3
                       & -> & FRM3 & FE3 & PREc & LXc & SOc & FAc & BKc & EBO3). subst bo3.
      replace (ret_pc (Z_to_bv 64 0x19c614)) with (Z_to_bv 64 0x19c614) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold raise_post. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3.
      split; [reflexivity|]. split; [exact FRM3|]. split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk); apply (FE1 k Hk)|].
      split; [exact PREc|]. split; [rewrite <- ESP; eapply lx_pres_trans; [exact LXa|eapply lx_pres_trans; [exact LXb|exact LXc]]|].
      split; [rewrite SOc, SOb; exact SOa|]. split; [rewrite FAc, FAb; exact FAa|].
      split; [exact (proj1 BKc)|]. split; [exact (proj1 (proj2 BKc))|].
      eapply kept_trans; [exact KP2|]. eapply kept_trans; [exact (proj2 (proj2 BKa))|]. eapply kept_trans; [exact (proj2 (proj2 BKb))|exact (proj2 (proj2 BKc))]. }
    (* [comment removed for export] *)
    destruct SITE as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
      (unfold implM; iprefix; step; ihere; to_implM;
       eapply implM_abind;
       [ pose proof (ERR_new_walk HF bo) as W; unfold ap_stmt in W;
         eapply W; [eapply ap_pre_stack_le; [exact PRE2|unfold ERR_NEW_STACK, ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM|reflexivity|exact KOW|exact KIDS]
       | intros r1 sA ms1 PO1; cbv beta in PO1;
         destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1 & bo1
                          & -> & FRM1 & FE1 & PREa & LXa & SOa & FAa & BKa & EBO1);
         subst bo1;
         lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end;
         unfold implM; iprefix ]).
    - do 7 step. ihere. to_implM. eapply TAIL; eassumption.
    - do 6 step. ihere. to_implM. eapply TAIL; eassumption.
    - do 7 step. ihere. to_implM. eapply TAIL; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma client_cells : forall mA mB (x1 : sctr bptr),
    lx_pres LB (bv_unsigned sp + -64) LIBW_AP mA mB ->
    (rw_cells ctusegs mA (bv_unsigned sp + -64) sg_frame -> rw_cells ctusegs mB (bv_unsigned sp + -64) sg_frame)
    /\ (rw_cells ctusegs mA PIN [C8 (wz (D + p))] -> rw_cells ctusegs mB PIN [C8 (wz (D + p))])
    /\ (rw_cells ctusegs mA (adr (sc_blk x)) (sct_cells adr x1 (-1) vs) -> rw_cells ctusegs mB (adr (sc_blk x)) (sct_cells adr x1 (-1) vs))
    /\ (bytes_at ctusegs mA D (to_bytes c) -> bytes_at ctusegs mB D (to_bytes c)).
  Proof using ALP CNE HXIN PAY PAYNE PINlo PL PRE SEPD.
    intros mA mB x1 LX. ctx. pose proof (agree_of_lx_pres _ _ _ _ _ LX) as AG.
    assert (CLs : forall a, bv_unsigned sp + -64 <= a -> lx_client LB (bv_unsigned sp + -64) LIBW_AP a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|left; exact Ha]. }
    assert (CLb : forall a, adr (sc_blk x) <= a < adr (sc_blk x) + 104 -> lx_client LB (bv_unsigned sp + -64) LIBW_AP a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|]. right. left. exists (sc_blk x, adr (sc_blk x), SCT_SIZE). split; [exact HXIN| cbn; unfold SCT_SIZE; lia]. }
    split; [|split; [|split]].
    - intros H. apply (rw_cells_agree _ _ _ _ _ AG); [exact H|]. intros a Ha; apply CLs; cbn in Ha; lia.
    - intros H. apply (rw_cells_agree _ _ _ _ _ AG); [exact H|]. intros a Ha; apply CLs; cbn in Ha; lia.
    - intros H. apply (rw_cells_agree _ _ _ _ _ AG); [exact H|]. intros a Ha; apply CLb. rewrite sct_cells_size in Ha. unfold SCT_SIZE in Ha. lia.
    - intros H. destruct PAY as (_ & _ & _ & _ & _ & HBL). apply (bytes_at_agree _ _ _ _ _ AG); [exact H|]. intros a Ha. rewrite DLEN in Ha.
      destruct HBL as [E0|(blk & HBLK & BL1 & BL2)]; [rewrite E0 in Ha; unfold zlength in Ha; cbn in Ha; lia|].
      split; [| right; left; exists blk; split; [exact HBLK| lia]].
      pose proof PRE as (HEAP & _). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HBLK)) as (_ & _ & _ & _ & BI4).
      unfold LIBW_AP; cbn [rin_ivs fst snd]. unfold GLOBALS_TOP in BI4. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_raise : forall x1 (x8 x9 x18 x19 x20 x21 x22 : word) m2 (r : unit * ap_st bptr) sF msF,
    sg_inv m2 x1 ->
    sc_blk x1 = sc_blk x /\ sc_logid x1 = sc_logid x /\ sc_ext x1 = sc_ext x /\ sc_blob x1 = sc_blob x /\ sc_version x1 = sc_version x /\ sc_sig x1 = None ->
    raise_post x8 x9 x18 x19 x20 x21 x22 m2 r sF msF ->
    evt ctusegs (fun ms'' => o2i_sig_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr x vs c D p len PIN ((x1, -1), snd r) sF ms'') msF.
  Proof using ALP CNE HXIN KOW PAY PAYNE PINhi PINlo PL PRE SEPD.
    intros until msF. intros GI (E1 & E2 & E3 & E4 & E5 & E6) RP. pose proof GI as GI'. sg_unpack GI. ctx. subst tp.
    unfold raise_post in RP.
    destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & errvF
                    & -> & FRMF & FEF & PREF & LXF & SOF & FAF & BKF).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    pose proof PREF as (HEAPF & ASF & IDSF & DCF & AUXF & SPBF & B63F & STF & CEILF & GLOF & LOF & ERRF & SSPF & MIF & SP16F). rewrite ESP in STF.
    destruct (client_cells m2 mF x1 LXF) as (TF & TP' & TC & TB).
    specialize (TF FR). specialize (TP' HP). specialize (TC HC). rename TF into FRf. unfold sg_frame in FRf. unfold sct_cells, MallocRep.wz in TC.
    clear MU WM MI ST HB ERR.
    pose proof (munch_refl (@nil (Z * Z)) mF) as MU. pose proof (wmono_refl ctusegs mF) as WM.
    step. do 8 step. release_frame FRf STF (bv_unsigned sp). step. step.
    apply evt_done. unfold o2i_sig_post. cbn [fst snd].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FF, fcF, mF, OWF, errvF, bo, adr, [].
    split; [unfold MallocRep.wz; reflexivity|]. split; [exact FRMF|]. split; [exact FEF|].
    split. { cbn [app]. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP16e).
             unfold ap_pre. repeat (split; [first [assumption|lia]|]). exact SP16e. }
    split. { eapply lx_pres_trans; [exact (proj1 (proj2 (pre_at_call _ _ GI')))|].
             eapply lx_pres_weaken; [exact LXF|lia|intros b Hb; exact Hb|]. intros a Ha. cbn [rin_ivs fst snd app]. cbn [rin_ivs fst snd app] in Ha. tauto. }
    split; [exact SOF|]. split; [exact FAF|]. split; [exact BKF|].
    split; [intros b Hb; reflexivity|].
    split; [cbn; unfold sct_cells, MallocRep.wz; exact TC|].
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    cbn. split; [reflexivity|]. split; [reflexivity|]. split; [exact E6|]. exact TP'.
  Qed.

  Lemma nodup_blk_eq : forall (L0 : list block) q A1 n1 A2 n2,
    List.NoDup (map blk_id L0) -> In (q, A1, n1) L0 -> In (q, A2, n2) L0 -> A1 = A2 /\ n1 = n2.
  Proof.
    induction L0 as [|b L0 IH]; intros q A1 n1 A2 n2 ND H1 H2; [destruct H1|]. cbn in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
    destruct H1 as [->|H1]; destruct H2 as [E2|H2].
    - injection E2; auto.
    - exfalso. apply NI. cbn. apply (in_ids _ _ _ _ H2).
    - exfalso. apply NI. subst b. cbn. apply (in_ids _ _ _ _ H1).
    - eapply IH; eassumption.
  Qed.

  Theorem sig_main : forall (t0 t1 t2 t3 a3 a4 a5 a6 a7 t4 t5 t6 : word),
    implM ctusegs (interp (ap_embed (o2i_sct_signature x c p len st))) s
          (o2i_sig_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr x vs c D p len PIN)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (adr (sc_blk x))) (wz PIN) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz O2I_SCT_SIGNATURE) fc None m (seg_rom ctusegs)).
  Proof using ALP CNE FRM HF HM HPIN HX HXIN KIDS KOW LEN0 P0 PAY PAYNE PINhi PINlo PL PRE SEPD SIG0 TP V0 XIN.
    intros.
    pose proof PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & SP16). ctx.
    pose proof PAY as (HB & _).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    unfold o2i_sct_signature. rewrite V0. cbn [negb Z.eqb].
    unfold O2I_SCT_SIGNATURE, MallocRep.wz.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK in MU.
    pose proof HX as HC. clear HX. unfold sct_cells in HC. rewrite V0, SIG0 in HC. cbn [u32 Z.modulo optr sc_siglen Z.pow_pos Pos.iter Z.mul] in HC. unfold MallocRep.wz in HC.
    unfold MallocRep.wz in HPIN.
    assert (SEPA : adr (sc_blk x) + 104 <= bv_unsigned sp - (64 + (80 + 96 + 48 + 8192))) by lia.
    pose proof ALX as AX16.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 9 step. step. uchk. step. step. uchk.
    step. step. if_cases KV; zc KV; [| exfalso; apply KV; reflexivity]. clear KV.
    step. step.
    name_mem m1.
    assert (GI : sg_inv m1 x).
    { split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|]. split; [exact HB|]. split; [exact ERR|]. split; [exact HPIN|].
      unfold sct_cells. rewrite V0, SIG0. cbn [u32 Z.modulo optr sc_siglen Z.pow_pos Pos.iter Z.mul]. unfold MallocRep.wz. exact HC. }
    step. if_cases KL; zc KL.
    - (* [comment removed for export] *)
      replace (len <=? 4) with false by (symmetry; apply Z.leb_gt; lia).
      assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
      { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range c i DF). lia. }
      pose proof (znth_range c p DF) as R0. pose proof (znth_range c (p + 1) DF) as R1.
      step. uchk. step. uchk. step. step. step. uchk.
      pose proof (payload_read m1 D c p (wa (D + p)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
      step. step. step. rewrite le1_zxb. mem_after_store. uchk.
      pose proof (payload_read _ D c (p + 1) (wa (D + p + 1)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD.
      step. rewrite le1_zxb. mem_after_store.
      step. step.
      name_mem m2.
      (* [comment removed for export] *)
      assert (RV : ro_cells ctusegs m2 (adr (sc_blk x) + SCTO_VERSION) [C4 (Z_to_bv 64 0)]).
      { unfold SCTO_VERSION. rewrite Z.add_0_r. exact (proj1 (proj1 (proj1 (rw_cells_app _ _ [C4 (Z_to_bv 64 0)] _) HC))). }
      assert (RA : ro_cells ctusegs m2 (adr (sc_blk x) + SCTO_ALGS) [C1 (Z_to_bv 8 (znth c p)); C1 (Z_to_bv 8 (znth c (p + 1)))]).
      { unfold SCTO_ALGS.
        lazymatch type of HC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
          pose proof (proj2 (proj1 (rw_cells_app _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8] _) HC)) as HA; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HA;
          exact (proj1 (proj1 (proj1 (rw_cells_app _ _ [c9; c10] _) HA))) end. }
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
      eapply evt_cut; [eapply (SCT_get_signature_nid_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (adr (sc_blk x)) 0);
        [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| unfold SCT_SIZE; lia| clear - AX16; Z.div_mod_to_equations; lia| exact RV| exact RA| lia| lia| lia| reflexivity]|].
      unfold nid_post. post_call_esp ESP m2. name_mem m3. rename POST into ST3, MI0 into MI3.
      cbn [Z.eqb]. unfold sct_nid. cbn [sc_version sc_hash sc_sigalg set_algs]. rewrite V0, !BY by lia.
      set (nid := sig_nid 0 (znth c p) (znth c (p + 1))) in *.
      assert (NR : 0 <= nid <= 794).
      { subst nid. unfold sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption.
        destruct ((0 =? 0) && (znth c p =? 4)); [destruct (znth c (p + 1) =? 3); [| destruct (znth c (p + 1) =? 1)]|]; lia. }
      set (xS := set_algs (znth c p) (znth c (p + 1)) x) in *.
      assert (GI3 : sg_inv m3 xS).
      { split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact FR|]. split; [exact HB|]. split; [exact ERR|]. split; [exact HPIN|].
        subst xS. unfold sct_cells. cbn [sc_version sc_hash sc_sigalg set_algs sc_blk sc_blob sc_logid sc_ts sc_ext sc_extlen sc_sig sc_siglen sc_bloblen].
        rewrite V0, SIG0. cbn [u32 Z.modulo optr Z.pow_pos Pos.iter Z.mul]. unfold MallocRep.wz. exact HC. }
      step. if_cases KN; zc KN.
      + (* [comment removed for export] *)
        replace (nid =? NID_undef) with true by (symmetry; apply Z.eqb_eq; unfold NID_undef; revert KN; rewrite ?unsigned_lit by lia; lia).
        apply evt_done. cbv beta. to_implM.
        eapply implM_abind; [eapply (raise_seq 0x19c5e8 6%nat RS_sig_nid); [right; left; repeat split; reflexivity| exact GI3]|].
        intros r sF msF RP. cbv beta. apply implM_aret. eapply (fin_raise xS); [exact GI3| subst xS; cbn; repeat split; try reflexivity; exact SIG0| exact RP].
      + (* [comment removed for export] *)
        assert (NIDOK : nid <> NID_undef) by (unfold NID_undef; revert KN; rewrite ?unsigned_lit by lia; lia).
        replace (nid =? NID_undef) with false by (symmetry; apply Z.eqb_neq; exact NIDOK). clear KN.
        step. uchk. step. uchk.
        pose proof (znth_range c (p + 2) DF) as R2. pose proof (znth_range c (p + 3) DF) as R3.
        pose proof (payload_read _ D c (p + 2) (wa (D + p + 2)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD. rewrite (zxb_lit (znth c (p + 2))) by lia.
        pose proof (payload_read _ D c (p + 3) (wa (D + p + 3)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD. rewrite (zxb_lit (znth c (p + 3))) by lia.
        step. step. step.
        setreg 20%Z (Z_to_bv 64 (u16be c (p + 2)))
          ltac:(unfold u16be; rewrite !BY by lia; replace (p + 2 + 1) with (p + 3) by lia; f_equal;
                rewrite (unsigned_lit (znth c (p + 2))), (unsigned_lit (znth c (p + 3))) by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256;
                rewrite (unsigned_lit (znth c (p + 2) * 256)) by lia; symmetry; apply lor_shl8; lia).
        step. setreg 21%Z (Z_to_bv 64 (D + p + 4)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
        step. step. setreg 19%Z (Z_to_bv 64 (len - 4)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
        pose proof (u16be_range c (p + 2)) as SR.
        step. if_cases KO; zc KO.
        * (* [comment removed for export] *)
          assert (SLE : u16be c (p + 2) <= len - 4) by (revert KO; rewrite ?unsigned_lit by lia; lia).
          replace (len - 4 <? u16be c (p + 2)) with false by (symmetry; apply Z.ltb_ge; lia). clear KO.
          set (siglen := u16be c (p + 2)) in *.
          subst xS. cbn [sc_sig set_algs afree_opt option_map]. rewrite SIG0. cbn [abind apbind aret afree_opt option_map fst snd].
          set (xS := set_algs (znth c p) (znth c (p + 1)) x) in *.
          step. step. step. setreg 22%Z (Z_to_bv 64 (2 ^ 64 - 4)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
          step.
          pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HXIN)) as BRX. cbn [blk_addr blk_size fst snd] in BRX.
          pose proof AS as (_ & _ & (CS0 & RS0 & _) & _).
          assert (CS3 : crypto_statics m3).
          { eapply BnRep.crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS0].
            intros a Ha. cbn. split; [| split; [| split; [| exact I]]]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia. }
          destruct PAY as (_ & _ & _ & _ & _ & [E0|([[pb PA] psz] & HPB & PB1 & PB2)]); [exfalso; rewrite E0 in CNE; unfold zlength in CNE; cbn in CNE; lia|].
          cbn [blk_addr blk_size fst snd] in PB1, PB2.
          pose proof (PAYNE pb PA psz HPB PB1 PB2) as NPX.
          pose proof GI3 as (_ & _ & _ & _ & _ & _ & _ & _ & HCf).
          destruct (Z.eq_dec siglen 0) as [Z0|ZP].
          -- (* [comment removed for export] *)
             rewrite Z0. cbn [Z.ltb abind apbind aret fst snd ap_embed]. replace (len - (len - 4 - 0)) with 4 by lia.
             apply evt_done. cbv beta. to_implM. apply implM_ret.
             eapply evt_cut; [eapply (SCT_set1_signature_zero_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo adr xS (-1) vs);
               [rewrite ESP; exact ST3| exact CEIL| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact MI3| exact CS3| exact HCf| subst xS; cbn; exact SIG0| exact BRX| reflexivity| reflexivity]|].
             intros ms' PO. unfold SCT_SIZE in PO. change (sc_blk xS) with (sc_blk x) in PO. revert ms' PO. post_call_esp ESP m3. name_mem m4. rename PC into ST4, POST into HC4.
             unfold set_sig_cells, MallocRep.wz in HC4.
             (* [comment removed for export] *)
             step. step. if_cases K1; zc K1; [exfalso; apply K1; reflexivity|]. clear K1.
             step. uchk.
             step. step. step. setreg 10%Z (Z_to_bv 64 4) ltac:(apply bv_eq; vm_compute; reflexivity).
             step. name_mem m5.
             destruct (pre_at_call0 m5 MU WM MI ST4 ERR) as (PRE5 & LX5 & KP5).
             do 8 step. release_frame FR ST4 (bv_unsigned sp). step. step.
             rewrite TP. apply evt_done. unfold o2i_sig_post. cbn [fst snd].
             eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m5, OW, errv, bo, adr, [].
             split; [reflexivity|]. split; [exact FRM|]. split; [intros; reflexivity|].
             split; [cbn [app]; eapply pre_resp; [exact PRE5| exact ST4]|].
             split; [exact LX5|]. split; [reflexivity|]. split; [reflexivity|].
             split; [split; [exact KOW| split; [intros b Hb Hin; apply (KIDS b Hb); apply in_app_iff; left; exact Hin| exact KP5]]|].
             split; [intros; reflexivity|].
             split; [cbn; subst xS; unfold sct_cells; cbn; unfold MallocRep.wz; setreg 10%Z (Z_to_bv 64 4) ltac:(idtac) || exact HC4|].
             subst xS; cbn -[sct_nid]. repeat (split; [first [reflexivity| lia]|]).
             split. { unfold MallocRep.wz.
               match goal with H : rw_cells ctusegs m5 PIN [C8 ?v] |- _ => replace (Z_to_bv 64 (D + p + 4)) with v; [exact H| apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve] end. }
             repeat (split; [first [reflexivity| lia]|]). split; [unfold sct_nid; cbn [sc_version sc_hash sc_sigalg set_sig set_algs]; rewrite V0; exact NIDOK| reflexivity].
          -- (* [comment removed for export] *)
             replace (0 <? siglen) with true by (symmetry; apply Z.ltb_lt; lia). cbn [abind apbind amalloc aret fst snd ap_embed].
             apply evt_done. cbv beta. to_implM.
             destruct (pre_at_call0 m3 MU WM MI3 ST3 ERR) as (PRE3 & LX3 & KP3).
             pose proof PRE3 as (HEAP3 & AS3 & _ & DC3 & AUX3 & _). rewrite ESP in AUX3 || idtac.
             assert (SRC : bytes_at ctusegs m3 (D + p + 4) (to_bytes (slice c (p + 4) siglen))).
             { unfold slice, to_bytes. rewrite <- firstn_map, <- skipn_map. fold (to_bytes c). apply bytes_at_firstn.
               replace (D + p + 4) with (D + Z.of_nat (Z.to_nat (p + 4))) by lia. apply bytes_at_skipn; [exact HB|]. apply Nat2Z.inj_le. rewrite DLEN. lia. }
             assert (SLEN : length (to_bytes (slice c (p + 4) siglen)) = Z.to_nat siglen) by (unfold to_bytes; rewrite length_map; apply slice_length; lia).
             eapply (SCT_set1_signature_walk HM) with (B := B) (lo := lo) (errv := errv) (L := OW ++ LB) (adr := adr) (x := xS) (et := -1) (vs := vs)
                                                    (pp := pb) (PA := PA) (psz := psz) (P := D + p + 4) (n := siglen) (src := to_bytes (slice c (p + 4) siglen));
               [exact HEAP3| exact AUX3| rewrite ESP; lia| rewrite ESP; exact ST3| exact CEIL| unfold GLOBALS_TOP; lia
               | rewrite ESP; unfold SCT_SET1_SIGNATURE_STACK, CRYPTO_MEMDUP_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
               | unfold LX_ERRNO, RATP; exact ERR| exact MI3| exact TP| exact CS3
               | apply in_app_iff; right; exact HXIN| exact HCf| subst xS; cbn; exact SIG0
               | apply in_app_iff; right; exact HPB| exact NPX| lia| lia| exact SRC| exact SLEN| reflexivity| reflexivity| reflexivity| lia| reflexivity|].
             intros pn sN msN PON. unfold oalloc_post in PON. rewrite ?ESP in PON.
             destruct PON as (n0 & n1 & n2 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n3 & n4 & n5 & n6 & mN & C & errvN
                              & -> & MIN & STN & ERRN & AUXN & HPN & FAN & SON & BRN & HEAPN & (BLKN & SRCN & HCN)).
             replace (ret_pc (Z_to_bv 64 0x19c650)) with (Z_to_bv 64 0x19c650) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
             pose proof BRN as (C0 & C16 & _ & CC & CI).
             pose proof (LH_nodup _ _ _ HEAPN) as NDN. cbn [map blk_id fst snd] in NDN. apply NoDup_cons_iff in NDN. destruct NDN as [NPN _].
             assert (HPB' : In (pb, PA, psz) (lb_remove (sc_blk x) (OW ++ LB))) by (apply lb_remove_In; split; [apply in_app_iff; right; exact HPB| cbn; exact NPX]).
             pose proof (agree_of_heap_pres _ _ _ _ HPN) as AGN.
             apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros a Ha; left; cbn in Ha; lia].
             apply (rw_cells_agree _ _ _ _ _ AGN) in HPIN; [| intros a Ha; left; cbn in Ha; lia].
             apply (bytes_at_agree _ _ _ _ _ AGN) in HB; [| intros a Ha; right; right; exists (pb, PA, psz); split; [exact HPB'| cbn; rewrite DLEN in Ha; lia]].
             unfold LX_ERRNO, RATP in ERRN. change (3355176 - 164) with 3355012 in ERRN.
             unfold set_sig_cells, MallocRep.wz in HCN. apply (f_equal (fun P : Prop => P)) in HCN || idtac. change (frozen (rw_cells ctusegs mN (adr (sc_blk x)) (set_sig_cells adr xS (-1) C siglen))) in HCN.
             pose proof (munch_refl [(bv_unsigned sp - (64 + (80 + 96 + 48 + 8192)), bv_unsigned sp); (PIN, PIN + 8)]%Z mN) as MU2. pose proof (wmono_refl ctusegs mN) as WM2.
             assert (SEPC : C + siglen <= bv_unsigned sp - (64 + (80 + 96 + 48 + 8192))) by lia.
             (* [comment removed for export] *)
             cbn [apbind aret ap_embed fst snd interp]. apply implM_ret. unfold MallocRep.wz.
             step. step. if_cases K1; zc K1; [exfalso; apply K1; reflexivity|]. clear K1.
             step. uchk.
             step. setreg 21%Z (Z_to_bv 64 (D + p + 4 + siglen)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
             step. step. setreg 10%Z (Z_to_bv 64 (len - (len - 4 - siglen)))
               ltac:(rewrite (unsigned_lit siglen) by lia; rewrite ?(unsigned_lit (2 ^ 64 - 4)) by lia; try change 18446744073709551612 with (2 ^ 64 - 4); rewrite subw_m4 by lia; f_equal; lia).
             step. name_mem m6.
             assert (HEAP6 : RHEAP sN (OW ++ (pn, C, siglen) :: LB) m6).
             { eapply RHEAP_perm; [| apply Permutation_middle]. eapply LH_frame; [exact HEAPN| exact MU2| exact WM2|].
               constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
             assert (OWI : forall b, In b OW -> In b (lb_remove (sc_blk x) (OW ++ LB))).
             { intros b Hb. apply lb_remove_In. split; [apply in_app_iff; left; exact Hb|]. intros E0. apply NOW. rewrite <- E0. apply in_map. exact Hb. }
             assert (HW2 : Forall (fun iv : Z * Z => lo <= fst iv \/ iv = (3355012, 3355016)
                        \/ (exists q Aq n, In (q, Aq, n) ((pn, C, siglen) :: OW ++ LB) /\ ~ In q (map blk_id OW) /\ Aq <= fst iv /\ snd iv <= Aq + n))
                        [(bv_unsigned sp - (64 + (80 + 96 + 48 + 8192)), bv_unsigned sp); (PIN, PIN + 8)]%Z).
             { constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
             pose proof (ap_state_es _ _ _ _ _ AS3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD3).
             do 8 step. release_frame FR STN (bv_unsigned sp). step. step.
             try rewrite TP. apply evt_done. unfold o2i_sig_post. cbn [fst snd].
             eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m6, OW, errvN, bo, (fun b => if bptr_eqb b pn then C else adr b), [(pn, C, siglen)].
             split; [reflexivity|]. split; [exact FRM|]. split; [intros; reflexivity|].
             split. { unfold ap_pre. cbn [app]. split; [exact HEAP6|].
                      split. { eapply (ap_state_of_munch_blk st mN m6 OW E bo sN ((pn, C, siglen) :: OW ++ LB));
                                 [eapply ap_state_heap_pres; [exact AS3| exact HPN| exact OWI]| exact HEAPN| intros b Hb; right; apply in_app_iff; left; exact Hb
                                 | exact MU2| exact WM2| exact CEIL| unfold GLOBALS_TOP; lia| exact HW2]. }
                      split; [exact IDS|].
                      split. { eapply (data_cells_of_munch sN ((pn, C, siglen) :: OW ++ LB) _ mN m6);
                                 [eapply data_cells_heap_pres; [exact DC3| exact HPN| intros i q k Hd; apply OWI; exact (proj1 (optb_ok_nth OW _ i q k OD3 Hd))]
                                 | intros i q k Hd; right; apply in_app_iff; left; exact (proj1 (optb_ok_nth OW _ i q k OD3 Hd))| exact HEAPN| exact CEIL| exact MU2| exact WM2|].
                               eapply Forall_impl; [| exact HW2]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
                               exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros i q' k Hd E0. apply H2. rewrite <- E0. eapply in_ids. exact (proj1 (optb_ok_nth OW _ i q' k OD3 Hd)). }
                      split. { eapply rauxv_ok_frame; [exact AUXN| exact MU2| exact WM2|]. constructor; [cbn; unfold RAUXV_CELL, GLOBALS_TOP in *; lia|].
                               constructor; [cbn; unfold RAUXV_CELL, GLOBALS_TOP in *; lia| constructor]. }
                      split; [lia|]. split; [lia|]. split; [exact STN|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
                      split; [unfold MallocRep.wz; rewrite EA; exact ERRN|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAP6|].
                      split; [exact MIN|exact SP16]. }
             split. { eapply lx_pres_trans; [exact LX3|]. eapply lx_pres_trans.
                      - intros a Ha [HXa Hc]. apply HPN; [exact Ha|]. cbn [rin_ivs fst snd app] in HXa.
                        destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia| | right; left; exact Hc].
                        right. right. exists b. split; [| exact Hr]. apply lb_remove_In. split; [apply in_app_iff; right; exact Hb|].
                        intros E0. destruct b as [[qb Ab] nb]. cbn in E0. subst qb. cbn [blk_addr blk_size fst snd] in Hr.
                        destruct (nodup_blk_eq _ _ _ _ _ _ NDL ltac:(apply in_app_iff; right; exact Hb) ltac:(apply in_app_iff; right; exact HXIN)) as [-> ->]. apply HXa. right. left. unfold SCT_SIZE in Hr |- *. lia.
                      - eapply lx_pres_of_munch; [exact MU2| exact WM2|]. intros a Ha [HXa Hc]. cbn [rin_ivs fst snd app] in HXa. cbn.
                        destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [repeat split; lia| | unfold ralloc_static in Hc; repeat split; lia].
                        destruct b as [[qb Ab] nb]. cbn [blk_addr blk_size fst snd] in Hr.
                        pose proof (blk_bounds _ _ _ qb Ab nb HEAP ltac:(apply in_app_iff; right; exact Hb)). repeat split; lia. }
             split; [exact SON|]. split; [exact FAN|].
             split. { split; [exact KOW|]. split; [intros b Hb Hin; apply (KIDS b Hb); apply in_app_iff; left; exact Hin|].
                      eapply kept_trans; [exact KP3|]. eapply kept_trans; [eapply kept_of_heap_pres; [exact HPN| intros b Hb; apply OWI; apply KOW; exact Hb]|].
                      eapply (kept_of_munch sN ((pn, C, siglen) :: OW ++ LB) _ mN m6 K lo); [exact HEAPN| intros b Hb; right; apply in_app_iff; left; apply KOW; exact Hb| exact CEIL| exact MU2|].
                      eapply Forall_impl; [| exact HW2]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
                      exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros Hin. apply H2. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). rewrite <- Eb. apply in_map. apply KOW. exact Hb. }
             assert (NPL : ~ In pn (map blk_id LB)) by (intros Hin; apply NPN; rewrite map_app; apply in_app_iff; right; exact Hin).
             split. { intros b Hb. rewrite (bptr_eqb_neq (blk_id b) pn); [reflexivity|]. intros E0. apply NPL. rewrite <- E0. apply in_map. exact Hb. }
             replace (len - (len - 4 - siglen) <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
             split. { rewrite (set_sig_cells_rec xS pn C siglen (-1)); [| subst xS; reflexivity| subst xS; reflexivity| subst xS; reflexivity| subst xS; reflexivity| exact NPL].
                      unfold frozen in HCN. eapply rw_cells_transport; [exact HCN| exact MU2| exact WM2|]. cbn [disjoint_from]. rewrite sct_cells_size || idtac. unfold set_sig_cells. cbn. lia. }
             subst xS; cbn -[sct_nid]. repeat (split; [first [reflexivity| lia]|]). split.
             { replace (D + p + (len - (len - 4 - siglen))) with (D + p + 4 + siglen) by lia. unfold MallocRep.wz. exact HPIN. }
             repeat (split; [first [reflexivity| lia]|]). split; [unfold sct_nid; cbn [sc_version sc_hash sc_sigalg set_sig set_algs]; rewrite V0; exact NIDOK|].
             rewrite bptr_eqb_refl. split; [reflexivity|]. split; [lia|]. split; [exact NPN|]. exact BLKN.
        * (* [comment removed for export] *)
          replace (len - 4 <? u16be c (p + 2)) with true by (symmetry; apply Z.ltb_lt; revert KO; rewrite ?unsigned_lit by lia; lia).
          apply evt_done. cbv beta. to_implM.
          eapply implM_abind; [eapply (raise_seq 0x19c5cc 7%nat RS_sig_overrun); [right; right; repeat split; reflexivity| exact GI3]|].
          intros r sF msF RP. cbv beta. apply implM_aret. eapply (fin_raise xS); [exact GI3| subst xS; cbn; repeat split; try reflexivity; exact SIG0| exact RP].
    - (* [comment removed for export] *)
      replace (len <=? 4) with true by (symmetry; apply Z.leb_le; lia).
      apply evt_done. cbv beta. to_implM.
      eapply implM_abind; [eapply (raise_seq 0x19c534 7%nat RS_sig_len4); [left; repeat split; reflexivity| exact GI]|].
      intros r sF msF RP. cbv beta. apply implM_aret. eapply (fin_raise x); [exact GI| repeat split; try reflexivity; exact SIG0| exact RP].
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem o2i_sct_signature_walk : o2i_sct_signature_spec.
  Proof using HF HM.
    unfold o2i_sct_signature_spec. intros until PIN. intros PRE TP FRM KOW KIDS PAY CNE P0 LEN0 PL HXIN SEPD PAYNE HX V0 SIG0 XIN XND PINlo PINhi ALP HPIN -> -> ->.
    eapply sig_main; eassumption.
  Qed.
End Proofs.
End WithCeiling0.
