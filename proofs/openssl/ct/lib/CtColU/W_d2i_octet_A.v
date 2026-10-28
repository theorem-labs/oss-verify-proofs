(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Startup_B.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_c2i_int W_get_object W_get_object_walk W_check_tlen W_asn1_string W_item_d2i_stmt W_item_d2i_img W_item_d2i_front W_item_d2i_tail.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import W_asn1_enc_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColU Require Import ColKit ColDefs W_bufmem W_check_tlen_gen W_collect.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
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

(* [comment removed for export] *)
Definition EXPRIM_RET : Z := 0x1125b8.        (* [comment removed for export] *)
Definition EXPRIM_ERR : Z := 0x106114.        (* [comment removed for export] *)
Definition EXPRIM_CONS : Z := 0x10622c.       (* [comment removed for export] *)
Definition EXPRIM_PRIM : Z := 0x105fb4.       (* [comment removed for export] *)
Definition EXPRIM_C2I : Z := 0x112244.        (* [comment removed for export] *)
Definition EXPRIM_AFTER_TLEN : Z := 0x111f5c. (* [comment removed for export] *)
Definition ITEM_EX_FREE : Z := 0x1136f0.
Definition EMBED_D2I_LENCHK : Z := 0x110ff4.  (* [comment removed for export] *)

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HGO : ASN1_get_object_spec.

  Section Act.
  (* [comment removed for export] *)
  Variables (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block).
  Variables (d : list Z) (D : Z).
  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (st : ap_st bptr) (OW : list block) (bo : Z * Z) (errv : word) (adr : bptr -> Z) (OPP OCT : Z).
  Hypothesis DF : Forall (fun b => 0 <= b < 256) d.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis PBX : d = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength d <= PA + psz.
  Hypothesis D1 : 0 < D.
  Hypothesis D63 : D + zlength d < 2 ^ 63.
  Hypothesis D30 : zlength d < 2 ^ 30.
  Hypothesis OPPlo : bv_unsigned sp <= OPP.
  Hypothesis OPPhi : OPP + 8 <= B.
  Hypothesis OCTlo : bv_unsigned sp <= OCT.
  Hypothesis OCThi : OCT + 8 <= B.
  Hypothesis DJXP : OPP + 8 <= OCT \/ OCT + 8 <= OPP.
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Lemma D0 : 0 <= D. Proof using D1 sp. lia. Qed.

  Definition XPO : list (Z * Z) := [(OPP, OPP + 8); (OCT, OCT + 8)].
  Lemma XPok : Forall (fun iv : Z * Z => bv_unsigned sp <= fst iv /\ snd iv <= B) XPO.
  Proof using OCThi OCTlo OPPhi OPPlo. unfold XPO. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. Qed.

  Local Notation oinvK OFS STK := (oinv sp m s LB E lo B canary K d D XPO OFS STK).
  Local Notation SP := (bv_unsigned sp) (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition xsaved : list cell :=
    [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
     C8 (Z_to_bv 64 OCT); C8 (Z_to_bv 64 ITEM_OCTET); C8 (Z_to_bv 64 (bv_unsigned sp + -64)); C8 (Z_to_bv 64 RA_INTERN)].
  (* [comment removed for export] *)
  Definition iframe : list cell :=
    [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 s3; C8 s2; C8 (Z_to_bv 64 OCT); C8 sp; C8 (Z_to_bv 64 RA_D2IEX)].
  (* [comment removed for export] *)
  Definition dframe_hi : list cell := [C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dx_fin_none : forall (OFS' STK' : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
      sX stX mX OWX errvX boX (ov : word),
    lo <= SP + OFS' - STK' -> OFS' <= 0 -> 0 <= STK' ->
    oinvK OFS' STK' sX stX mX OWX errvX boX [] -> stk ctusegs mX lo SP -> frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
    rw_cells ctusegs mX OPP [C8 ov] -> rw_cells ctusegs mX OCT [C8 (Z_to_bv 64 0)] ->
    d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT (None, stX) sX
      (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F' (ret_pc ra) fc' None mX (seg_rom ctusegs)).
  Proof using SP16 SPB.
    intros until ov. intros LO OFS0 STK0 OI ST FRM FE HOPP HOCT.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (OI0 : oinvK 0 0 sX stX mX OWX errvX boX []).
    { eapply (oinv_reframe sp m s LB E lo B canary K d D XPO OFS' STK' 0 0); [exact OI| exact SPB| exact SP16| rewrite Z.add_0_r; exact ST| lia| lia| lia| reflexivity]. }
    pose proof OI0 as (PRE0 & LX0 & KO & KI & KP & SO & FA & HB).
    unfold d2i_octet_post. cbn [fst snd].
    eexists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', mX, OWX, errvX, boX, adr, [], ov, (Z_to_bv 64 0).
    split; [reflexivity|]. split; [exact FRM|]. split; [exact FE|].
    split; [eapply (pre_resp sp E lo B canary d 0 0); [lia| lia| lia| exact SPB| exact SP16| exact PRE0| exact ST]|].
    split; [exact LX0|]. split; [exact SO|]. split; [exact FA|].
    split; [split; [exact KO| split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP]]|].
    split; [intros b Hb; reflexivity|]. split; [intros b []|]. split; [exact HOPP|]. split; [exact HOCT|]. reflexivity.
  Qed.

  Lemma dx_fin_some : forall (OFS' STK' : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
      sX stX mX OWX errvX boX (ov : word) (os : octet bptr) (adr' : bptr -> Z),
    lo <= SP + OFS' - STK' -> OFS' <= 0 -> 0 <= STK' ->
    oinvK OFS' STK' sX stX mX OWX errvX boX (oct_blocks adr' os) -> stk ctusegs mX lo SP -> frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
    rw_cells ctusegs mX OPP [C8 ov] -> rw_cells ctusegs mX OCT [C8 (Z_to_bv 64 (adr' (os_blk os)))] ->
    octet_rep mX (OWX ++ oct_blocks adr' os ++ LB) adr' os -> (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b)) ->
    d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT (Some os, stX) sX
      (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz (adr' (os_blk os))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F' (ret_pc ra) fc' None mX (seg_rom ctusegs)).
  Proof using SP16 SPB.
    intros until adr'. intros LO OFS0 STK0 OI ST FRM FE HOPP HOCT REP ADR'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (OI0 : oinvK 0 0 sX stX mX OWX errvX boX (oct_blocks adr' os)).
    { eapply (oinv_reframe sp m s LB E lo B canary K d D XPO OFS' STK' 0 0); [exact OI| exact SPB| exact SP16| rewrite Z.add_0_r; exact ST| lia| lia| lia| reflexivity]. }
    pose proof (oinv_facts sp m s LB E lo B canary K d D XPO 0 0 _ _ _ _ _ _ _ OI0) as (_ & _ & _ & FRESH & _).
    pose proof OI0 as (PRE0 & LX0 & KO & KI & KP & SO & FA & HB).
    unfold d2i_octet_post. cbn [fst snd].
    eexists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', mX, OWX, errvX, boX, adr', (oct_blocks adr' os), ov, (Z_to_bv 64 (adr' (os_blk os))).
    split; [reflexivity|]. split; [exact FRM|]. split; [exact FE|].
    split; [eapply (pre_resp sp E lo B canary d 0 0); [lia| lia| lia| exact SPB| exact SP16| exact PRE0| exact ST]|].
    split; [exact LX0|]. split; [exact SO|]. split; [exact FA|].
    split; [split; [exact KO| split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP]]|].
    split; [exact ADR'|]. split; [intros [[q Aq] n] Hb; cbn; exact (FRESH q Aq n Hb)|]. split; [exact HOPP|]. split; [exact HOCT|].
    split; [reflexivity|]. split; [exact REP| reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dx_fail_tail : forall (STK3 : Z)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (FA : bvmap 5 word) (fcA : bv 32) sA stA mA OWA errvA boA (ov : word) (jlo jd : list byte),
    lo <= SP + -320 - STK3 -> 0 <= STK3 ->
    oinvK (-320) STK3 sA stA mA OWA errvA boA [] -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get F k) ->
    rw_cells ctusegs mA OPP [C8 ov] -> rw_cells ctusegs mA OCT [C8 (Z_to_bv 64 0)] -> OCT mod 8 = 0 ->
    rw_cells ctusegs mA (SP + -320) [CB 96 jlo] -> rw_cells ctusegs mA (SP + -224) xsaved -> rw_cells ctusegs mA (SP + -128) iframe ->
    rw_cells ctusegs mA (SP + -64) [CB 40 jd] -> rw_cells ctusegs mA (SP + -24) dframe_hi ->
    evt ctusegs (d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT (None, stA) sA)
      (MS (mkR x1 (Z_to_bv 64 (SP + -320)) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 0) x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          FA (Z_to_bv 64 EXPRIM_RET) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL GLO OCThi OCTlo OPPhi OPPlo PBX SP16 SPB.
    intros until jd. intros LO STK0 OI FRMA FEA HOPP HOCT OCT8 FLO FSV FI FDL FDH.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (OFS0 : -320 <= 0) by lia. assert (OFS16 : (-320) mod 16 = 0) by reflexivity.
    pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK3 GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _ & ASA).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    pose proof ASA as (_ & IMG & _).
    pose proof (item_cells_octet mA IMG) as (IT0 & IT8 & IT8L & IT16 & IT32). unfold ITEM_OCTET in IT0, IT8, IT8L, IT16, IT32.
    unfold xsaved, iframe, dframe_hi, EXPRIM_RET, RA_INTERN, RA_D2IEX, ITEM_OCTET, MallocRep.wz in *.
    pose proof (munch_refl [(SP - 320, SP)]%Z mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    rename MIA into MI.
    (* [comment removed for export] *)
    step. do 12 step. step. release_frame FLO STA (SP + -224). release_frame FSV STA (SP + -128). step.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 1117828)) with (Z_to_bv 64 1117828) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. if_false. step. step. step.
    (* [comment removed for export] *)
    carve_frame 16%nat STA. do 8 step. release_frame FR STA (SP + -128). step.
    assert (ESP3 : bv_unsigned (Z_to_bv 64 (SP + -128)) = SP + -128) by (apply unsigned_lit; lia).
    name_mem m3. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
    eapply embed_free_null with (lo := lo) (PVAL := OCT) (IT := 2960328) (w := 4);
      [rewrite ?ESP3; exact STA| exact MI3| lia| rewrite ?ESP3; lia| rewrite ?ESP3; lia| rewrite ?ESP3; lia| lia| exact OCT8| exact HOCT| lia| lia| reflexivity
      | exact IT0| exact IT8| exact IT16| exact IT32| lia| lia|].
    intros t0'' t1'' a0'' a1'' a2'' a3'' m4 MU4 WM4 MI4 ST4. rewrite ?ESP3 in *.
    xport FI MU4 WM4. xport FDL MU4 WM4. xport FDH MU4 WM4. xport HOPP MU4 WM4. xport HOCT MU4 WM4. xport ERRA MU4 WM4.
    assert (MU' : munch [(SP - 320, SP)]%Z mA m4).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU4]. intros x; cbn; lia. }
    pose proof (wmono_trans _ _ _ _ WM WM4) as WM'. clear MU WM MU4 WM4 MI3 IT0 IT8 IT8L IT16 IT32. rename MU' into MU. rename WM' into WM.
    replace (ret_pc (Z_to_bv 64 1117848)) with (Z_to_bv 64 1117848) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    step. step. do 5 step. step. release_frame FI ST4 (SP + -64). step.
    replace (ret_pc (Z_to_bv 64 1118008)) with (Z_to_bv 64 1118008) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_true. step. step. step. step. step.
    release_frame FDL ST4 (SP + -24). release_frame FDH ST4 (bv_unsigned sp). step.
    name_mem m5. match goal with H : mem_inv ctusegs m5 |- _ => rename H into MI5 end.
    apply evt_done.
    eapply (dx_fin_none (-320) STK3); [exact LO| exact OFS0| exact STK0| | exact ST4| exact FRMA| exact FEA| exact HOPP| exact HOCT].
    eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK3 CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OI| exact MU| exact WM| exact MI5| | exact ERRA|].
    - destruct (stk_carve ctusegs m5 lo (bv_unsigned sp) 320 ST4 ltac:(lia)) as [ST5 _]. replace (bv_unsigned sp - Z.of_nat 320) with (bv_unsigned sp + -320) in ST5 by lia. exact ST5.
    - constructor; [left; cbn; lia| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma octet_rep_munch : forall sX L mX mY W adr' os,
    octet_rep mX L adr' os -> RHEAP sX L mX -> munch W mX mY -> wmono ctusegs mX mY ->
    (forall A n, A + n <= alloc_ceiling -> disjoint_from W A n) ->
    octet_rep mY L adr' os.
  Proof using sp.
    intros until os. intros (IN1 & CELLS & LEN & RNG & L31 & DAT) HEAP MU WM DJ.
    pose proof (LH_block_range _ _ _ _ HEAP IN1) as (B0 & B1 & B2 & B3 & B4). cbn [blk_addr blk_size fst snd] in B0, B1, B2, B3, B4. unfold ASN1_STRING_SIZE in B3.
    split; [exact IN1|]. split.
    { eapply rw_cells_transport; [exact CELLS| exact MU| exact WM|]. apply DJ. cbn. lia. }
    split; [exact LEN|]. split; [exact RNG|]. split; [exact L31|].
    destruct (os_data os) as [[dp n]|]; [| exact DAT]. destruct DAT as (NE & IN2 & LE & BY). split; [exact NE|]. split; [exact IN2|]. split; [exact LE|].
    pose proof (LH_block_range _ _ _ _ HEAP IN2) as (C0 & C1' & C2 & C3 & C4'). cbn [blk_addr blk_size fst snd] in C0, C1', C2, C3, C4'.
    eapply bytes_at_transport; [exact BY| exact MU|]. apply DJ. rewrite zlength_to_bytes. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dx_ok_tail : forall (STK3 : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (FA : bvmap 5 word) (fcA : bv 32) sA stA mA OWA errvA boA (ov : word) (pe : Z) (jb j5 jm jd : list byte) (os : octet bptr) (adr' : bptr -> Z),
    lo <= SP + -320 - STK3 -> 0 <= STK3 ->
    oinvK (-320) STK3 sA stA mA OWA errvA boA (oct_blocks adr' os) -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get F k) ->
    rw_cells ctusegs mA OPP [C8 ov] -> rw_cells ctusegs mA OCT [C8 (Z_to_bv 64 (adr' (os_blk os)))] -> OCT mod 8 = 0 ->
    octet_rep mA (OWA ++ oct_blocks adr' os ++ LB) adr' os -> (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b)) ->
    0 <= pe < 2 ^ 64 ->
    rw_cells ctusegs mA (SP + -320) [CB 40 jb; C8 (Z_to_bv 64 pe); CB 5 j5; C1 (Z_to_bv 8 0); CB 42 jm] -> rw_cells ctusegs mA (SP + -224) xsaved ->
    rw_cells ctusegs mA (SP + -128) iframe -> rw_cells ctusegs mA (SP + -64) [CB 40 jd] -> rw_cells ctusegs mA (SP + -24) dframe_hi ->
    evt ctusegs (d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT (Some os, stA) sA)
      (MS (mkR x1 (Z_to_bv 64 (SP + -320)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (SP + -128)) (Z_to_bv 64 OPP) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          FA (Z_to_bv 64 D2I_OK_TAIL) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL DJXP GLO OCThi OCTlo OPPhi OPPlo PBX SP16 SPB.
    intros until adr'. intros LO STK0 OI FRMA FEA HOPP HOCT OCT8 REP ADR' PE FB FSV FI FDL FDH.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (OFS0 : -320 <= 0) by lia. assert (OFS16 : (-320) mod 16 = 0) by reflexivity.
    pose proof (oinv_call sp m s LB E lo B canary K d D XPO (-320) STK3 GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (HEAPA & _ & _ & STA & _ & _ & ERRA & MIA & _).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    pose proof (oinv_facts sp m s LB E lo B canary K d D XPO (-320) STK3 _ _ _ _ _ _ _ OI) as (_ & _ & BND & _).
    pose proof (BND (os_blk os) (adr' (os_blk os)) ASN1_STRING_SIZE ltac:(apply in_app_iff; right; apply in_app_iff; left; left; reflexivity)) as (BA0 & _).
    unfold xsaved, iframe, dframe_hi, D2I_OK_TAIL, RA_INTERN, RA_D2IEX, ITEM_OCTET, MallocRep.wz in *.
    pose proof (munch_refl [(OPP, OPP + 8)]%Z mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    rename MIA into MI.
    (* [comment removed for export] *)
    step. step. step.
    step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. if_true.
    step. do 12 step. step. release_frame FB STA (SP + -224). release_frame FSV STA (SP + -128). step.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 1117828)) with (Z_to_bv 64 1117828) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. if_true. step. do 5 step. step. release_frame FI STA (SP + -64). step.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 1118008)) with (Z_to_bv 64 1118008) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_false.
    zstep. zstep. if_cases KC; zify_cond KC;
      [exfalso; rewrite ?unsigned_lit in KC by lia; change 7 with (Z.ones 3) in KC; rewrite Z.land_ones in KC by lia; clear - KC OCT8; Z.div_mod_to_equations; lia|]. clear KC.
    step. step. step. step. step. step.
    release_frame FDL STA (SP + -24). release_frame FDH STA (bv_unsigned sp). step.
    name_mem m5. match goal with H : mem_inv ctusegs m5 |- _ => rename H into MI5 end.
    apply evt_done.
    eapply (dx_fin_some (-320) STK3); [exact LO| exact OFS0| exact STK0| | exact STA| exact FRMA| exact FEA| exact HOPP| exact HOCT| | exact ADR'].
    - eapply (oinv_munch sp m s LB E lo B canary K d D XPO (-320) STK3 CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OI| exact MU| exact WM| exact MI5| | exact ERRA|].
      + destruct (stk_carve ctusegs m5 lo (bv_unsigned sp) 320 STA ltac:(lia)) as [ST5 _]. replace (bv_unsigned sp - Z.of_nat 320) with (bv_unsigned sp + -320) in ST5 by lia. exact ST5.
      + constructor; [right; left; unfold XPO; left; reflexivity| constructor].
    - eapply octet_rep_munch; [exact REP| exact HEAPA| exact MU| exact WM|]. intros A' n' HA'. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dx_site (base rad : Z) (nt : nat) (pcq : Z) (rs : rsite) (rsn fa : Z) : Prop :=
    (base = 0x1110ac /\ rad = 0x1110c8 /\ nt = 4%nat /\ pcq = 0x1110d8 /\ rs = RS_td_small /\ rsn = 224 /\ fa = A_ASN1_ITEM_EMBED_D2I)
    \/ (base = 0x111f68 /\ rad = 0x111f84 /\ nt = 5%nat /\ pcq = 0x111f98 /\ rs = RS_prim_nested /\ rsn = ERR_R_NESTED_ASN1_ERROR /\ fa = A_ASN1_D2I_EX_PRIMITIVE).

  Definition dx_raise_post (OFS' STK' pcq : Z) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (FX : bvmap 5 word) (mX : mem) (NEW : list block)
      (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY (errvY : word) boY,
      ms' = MS (mkR (Z_to_bv 64 pcq) (Z_to_bv 64 (SP + OFS')) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F' (Z_to_bv 64 pcq) fc' None mY (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get FX k)
      /\ oinvK OFS' STK' s' (snd r) mY OWY errvY boY NEW
      /\ lx_pres (NEW ++ LB) (SP + OFS') LIBW_AP mX mY.

  Lemma dx_raise : forall base rad nt pcq rs rsn fa (OFS' STK' : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (FX : bvmap 5 word) (fcX : bv 32) sX stX mX OWX errvX boX NEW,
    dx_site base rad nt pcq rs rsn fa ->
    lo <= SP + OFS' - STK' -> OFS' <= 0 -> OFS' mod 16 = 0 -> ERR_SET_ERROR_STACK <= STK' ->
    oinvK OFS' STK' sX stX mX OWX errvX boX NEW -> frm0 fcX ->
    implM ctusegs (interp (ap_embed (err_raise rs stX))) sX (dx_raise_post OFS' STK' pcq x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 FX mX NEW)
      (MS (mkR x1 (Z_to_bv 64 (SP + OFS')) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FX (Z_to_bv 64 base) fcX None mX (seg_rom ctusegs)).
  Proof using B63 CEIL GLO HF HM OCThi OCTlo OPPhi OPPlo PBX SPB.
    intros until NEW. intros SITE LO OFS0 OFS16 STKG OI FRMX.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (STK0 : 0 <= STK') by (unfold ERR_SET_ERROR_STACK in STKG; lia).
    pose proof (ESP sp lo B OFS' STK' GLO LO STK0 OFS0 SPB B63) as ESP.
    destruct (lit_ok_auto A_TASN_DEC_C 23 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    assert (LN0 : exists ns nk, lit_ok fa ns nk (rs_fnlen rs)).
    { destruct SITE as [(_ & _ & _ & _ & -> & _ & ->)|(_ & _ & _ & _ & -> & _ & ->)].
      - exact (lit_ok_auto A_ASN1_ITEM_EMBED_D2I 20 ltac:(vm_compute; reflexivity)).
      - exact (lit_ok_auto A_ASN1_D2I_EX_PRIMITIVE 22 ltac:(vm_compute; reflexivity)). }
    destruct LN0 as (ns & nk & LN).
    assert (RSF : rs_flen rs = 23) by (destruct SITE as [(_ & _ & _ & _ & -> & _)|(_ & _ & _ & _ & -> & _)]; reflexivity).
    assert (RC : rs_code rs = ERR_PACK 13 rsn /\ 0 <= rsn < 8388608)
      by (destruct SITE as [(_ & _ & _ & _ & -> & -> & _)|(_ & _ & _ & _ & -> & -> & _)]; (split; [reflexivity| unfold ERR_R_NESTED_ASN1_ERROR; lia])).
    destruct RC as [RC RB].
    rewrite <- RSF in LF.
    unfold err_raise. pose proof OI as (PREX & LXX & KO & KI & KP & SO & FA & HB).
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    (* [comment removed for export] *)
    assert (TAIL : forall (r1 : unit * ap_st bptr) (sA : PState) (q5 q6 q7 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (F1 : bvmap 5 word) (fc1 : bv 32) mA OW1 (errv1 : word) bo1,
      frm0 fc1 -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get FX k) ->
      oinvK OFS' STK' sA (snd r1) mA OW1 errv1 bo1 NEW -> lx_pres (NEW ++ LB) (SP + OFS') LIBW_AP mX mA ->
      implM ctusegs (interp (ap_embed (abind (err_set_debug rs) (fun _ => err_set_error rs) (snd r1)))) sA (dx_raise_post OFS' STK' pcq x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 FX mX NEW)
        (MS (mkR (Z_to_bv 64 rad) (Z_to_bv 64 (SP + OFS')) gp (wz RATP) q5 q6 q7 x8 x9 (wz A_TASN_DEC_C) (wz (rs_line rs)) (wz fa) q13 q14 q15 q16 q17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 q28 q29 q30 q31)
            F1 (wz ERR_SET_DEBUG) fc1 None mA (seg_rom ctusegs))).
    { intros until bo1. intros FRM1 FE1 OIa LXa.
      eapply implM_abind.
      { eapply (oinv_ap_call sp m s LB E lo B canary K d D XPO OFS' STK' CEIL GLO LO STK0 OFS0 SPB B63 OFS16 XPok PBX);
          [exact (ERR_set_debug_walk HM HF rs A_TASN_DEC_C fa bo1 _ _ _ _ LF LN)| exact OIa| unfold ERR_SET_DEBUG_STACK, ERR_SET_ERROR_STACK in *; lia| exact FRM1| cbv beta; repeat split; reflexivity]. }
      intros r2 sB ms2 PO2. unfold ap_call_post in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                       & -> & FRM2 & FE2 & OIb & LXb & EBO2). cbv beta in EBO2. subst bo2.
      unfold MallocRep.wz.
      assert (SE : forall (q5' q6' q7' q13' q14' q15' q16' q17' q28' q29' q30' q31' : word) mB',
        mB' = mB ->
        implM ctusegs (interp (ap_embed (err_set_error rs (snd r2)))) sB (dx_raise_post OFS' STK' pcq x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 FX mX NEW)
          (MS (mkR (Z_to_bv 64 pcq) (Z_to_bv 64 (SP + OFS')) gp (Z_to_bv 64 RATP) q5' q6' q7' x8 x9 (Z_to_bv 64 13) (Z_to_bv 64 rsn) (Z_to_bv 64 0) q13' q14' q15' q16' q17'
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 q28' q29' q30' q31')
              F2 (Z_to_bv 64 ERR_SET_ERROR) fc2 None mB' (seg_rom ctusegs))).
      { intros until mB'. intros ->.
        eapply implM_mono.
        { eapply (oinv_ap_call sp m s LB E lo B canary K d D XPO OFS' STK' CEIL GLO LO STK0 OFS0 SPB B63 OFS16 XPok PBX);
            [exact (ERR_set_error_walk rs 13 rsn bo1)| exact OIb| lia| exact FRM2|].
          cbv beta. unfold ERR_LIB_SYS, MallocRep.wz. repeat split; first [reflexivity| lia| exact RC]. }
        intros r3 sC ms3 PO3. unfold ap_call_post in PO3.
        destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & errv3 & bo3
                         & -> & FRM3 & FE3 & OIc & LXc & EBO3). cbv beta in EBO3. subst bo3.
        assert (PCQ : ret_pc (Z_to_bv 64 pcq) = Z_to_bv 64 pcq).
        { destruct SITE as [(_ & _ & _ & -> & _)|(_ & _ & _ & -> & _)]; (apply ret_pc_even; [lia| reflexivity]). }
        rewrite PCQ.
        unfold dx_raise_post. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3, bo1.
        split; [reflexivity|]. split; [exact FRM3|]. split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk); apply (FE1 k Hk)|].
        split; [exact OIc|]. eapply lx_pres_trans; [exact LXa|]. eapply lx_pres_trans; [exact LXb| exact LXc]. }
      pose proof (oinv_call sp m s LB E lo B canary K d D XPO OFS' STK' GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIb) as (_ & _ & _ & STb & _ & _ & ERRb & MIb & _).
      unfold LX_ERRNO, RATP in ERRb. change (3355176 - 164) with 3355012 in ERRb.
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctusegs mB) as WM.
      unfold implM. iprefix.
      destruct SITE as [(-> & -> & -> & -> & RS & -> & ->)|(-> & -> & -> & -> & RS & -> & ->)];
        (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).
      - do 4 step. ihere. to_implM. apply SE. reflexivity.
      - unfold ERR_R_NESTED_ASN1_ERROR in SE. do 5 step. ihere. to_implM. apply SE. reflexivity. }
    (* [comment removed for export] *)
    destruct SITE as [(-> & -> & -> & -> & -> & -> & ->)|(-> & -> & -> & -> & -> & -> & ->)];
      (unfold implM; iprefix; step; ihere; to_implM;
       eapply implM_abind;
       [ eapply (oinv_ap_call sp m s LB E lo B canary K d D XPO OFS' STK' CEIL GLO LO STK0 OFS0 SPB B63 OFS16 XPok PBX);
         [exact (ERR_new_walk HF boX)| exact OI| unfold ERR_NEW_STACK, ERR_SET_ERROR_STACK in *; lia| exact FRMX| reflexivity]
       | intros r1 sA ms1 PO1; unfold ap_call_post in PO1;
         destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1 & bo1
                          & -> & FRM1 & FE1 & OIa & LXa & EBO1); cbv beta in EBO1; subst bo1;
         lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end;
         pose proof (oinv_call sp m s LB E lo B canary K d D XPO OFS' STK' GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIa) as (_ & _ & _ & STa & _ & _ & ERRa & MIa & _);
         unfold LX_ERRNO, RATP in ERRa; change (3355176 - 164) with 3355012 in ERRa;
         clear MU WM; pose proof (munch_refl (@nil (Z * Z)) mA) as MU; pose proof (wmono_refl ctusegs mA) as WM;
         unfold implM; iprefix; do 5 step; step; ihere; to_implM;
         eapply (TAIL r1 sA); [exact FRM1| exact FE1| exact OIa| exact LXa] ]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blob_of : forall mX a cs n, rw_cells ctusegs mX a cs -> cells_size cs = n -> exists j, rw_cells ctusegs mX a [CB n j].
  Proof. intros mX a cs n H <-. exists (cells_bytes cs). apply rw_cells_CB_of. exact H. Qed.

  (* [comment removed for export] *)
  Lemma fb_pack : forall mX (z0 z1 z2 z3 pw cw u : word) (fcb bi bc : byte) (pl : word) (j5 j4 j16 j0 : list byte),
    rw_cells ctusegs mX (SP + -312) [C8 z0; C8 z1; C8 z2; C8 z3] -> rw_cells ctusegs mX (SP + -280) [C8 pw] ->
    rw_cells ctusegs mX (SP + -272) [CB 5 j5] -> rw_cells ctusegs mX (SP + -267) [C1 fcb] ->
    rw_cells ctusegs mX (SP + -266) [C1 bi; C1 bc; C8 pl] -> rw_cells ctusegs mX (SP + -256) [CB 4 j4] ->
    rw_cells ctusegs mX (SP + -252) [C4 u] -> rw_cells ctusegs mX (SP + -248) [CB 16 j16] -> rw_cells ctusegs mX (SP + -232) [C8 cw] ->
    rw_cells ctusegs mX (SP + -320) [CB 8 j0] ->
    exists jb jm, rw_cells ctusegs mX (SP + -320) [CB 40 jb; C8 pw; CB 5 j5; C1 fcb; CB 42 jm].
  Proof.
    intros until j0. intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    join2 H9 H0.
    destruct (blob_of _ _ _ 40%nat H9 eq_refl) as [jb HB].
    join2 H4 H5. join2 H4 H6. join2 H4 H7. join2 H4 H8.
    destruct (blob_of _ _ _ 42%nat H4 eq_refl) as [jm HJ].
    exists jb, jm. join2 HB H1. join2 HB H2. join2 HB H3. join2 HB HJ. exact HB.
  Qed.

  Lemma fb_blob : forall mX (pw : word) (fcb : byte) (jb j5 jm : list byte),
    rw_cells ctusegs mX (SP + -320) [CB 40 jb; C8 pw; CB 5 j5; C1 fcb; CB 42 jm] -> exists jlo, rw_cells ctusegs mX (SP + -320) [CB 96 jlo].
  Proof. intros until jm. intros H. exact (blob_of _ _ _ 96%nat H eq_refl). Qed.

  Lemma fd_pack : forall mX (z : word) (vb : byte) (j : list byte),
    rw_cells ctusegs mX (SP + -64) [C8 z] -> rw_cells ctusegs mX (SP + -56) [C1 vb; CB 31 j] -> exists jd, rw_cells ctusegs mX (SP + -64) [CB 40 jd].
  Proof.
    intros until j. intros H0 H1. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    join2 H0 H1. exact (blob_of _ _ _ 40%nat H0 eq_refl).
  Qed.

  End Act.
End Proofs.
End WithCeiling0.
