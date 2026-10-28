(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApIface W_c2i_int.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColU Require Import ColKit ColDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac ubchk_strong := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep;
  let C := fresh "Cs" in if_cases C;
  [ exfalso; zify_cond C;
    repeat (first [ rewrite ub_land64_small in C by lia | rewrite ub_lxor_sign63 in C by lia | rewrite unsigned_lit in C by lia ]);
    ub_ltb_cases C
  | clear C ].
Local Ltac ub1c :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (ub_kind pc) in
      lazymatch k with
      | 1%Z => zstep
      | 2%Z => first [ (zstep; udecide) | ubchk_strong | uchk ]
      end
  end.
Local Ltac step := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
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
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Section Act.
  (* [comment removed for export] *)
  Variables (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block).
  Variables (c : list Z) (D : Z) (XP : list (Z * Z)).
  Hypothesis DF : Forall (fun b => 0 <= b < 256) c.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis XPok : Forall (fun iv : Z * Z => bv_unsigned sp <= fst iv /\ snd iv <= B) XP.
  Hypothesis PBX : c = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz.
  Hypothesis D0 : 0 <= D.

  Local Notation oinvK OFS STK := (oinv sp m s LB E lo B canary K c D XP OFS STK).

  (* [comment removed for export] *)
  Definition grow_post (OFS STK : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX : bvmap 5 word) (fcX : bv 32)
      (stX : ap_st bptr) (OWX : list block) (boX : Z * Z) (mX : mem) (NEW1 : list block) (b : bufm bptr) (len BUF : Z) (bytes : list byte)
      (r : bufm bptr * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) mY (errvY : word) (q : bptr) (A n : Z) (rest : list byte),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz RATP) t0 t1 t2 s0 s1 (wz len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FX (ret_pc ra) fcX None mY (seg_rom ctusegs)
      /\ snd r = stX /\ fst r = mkBuf len (Some (q, n)) (bm_bytes b)
      /\ oinvK OFS STK s' stX mY OWX errvY boX ((q, A, n) :: NEW1)
      /\ rw_cells ctusegs mY BUF [C8 (wz len); C8 (wz A); C8 (wz n); C8 (wz 0)]
      /\ rw_cells ctusegs mY A [CB (Z.to_nat (bm_len b)) (firstn (Z.to_nat (bm_len b)) bytes); CB (Z.to_nat (n - bm_len b)) rest]
      /\ len <= n /\ 4 <= n < 2 ^ 31 /\ 0 < A /\ A + n <= alloc_ceiling
      /\ lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_AP) mX mY.

  Lemma BUF_MEM_grow_clean_walk : forall (OFS STK : Z)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX NEW1 (b : bufm bptr) (len BUF A0 : Z) (bytes : list byte),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> GROW_STACK <= STK ->
    oinvK OFS STK sX stX mX OWX errvX boX (buf_blk b A0 ++ NEW1) -> frm0 fcX ->
    bv_unsigned sp + OFS <= BUF -> BUF + 32 <= bv_unsigned sp -> BUF mod 8 = 0 ->
    rw_cells ctusegs mX BUF (buf_cells b A0) ->
    0 <= bm_len b <= bm_max b -> bm_len b < len -> len <= 2 ^ 30 ->
    match bm_data b with None => A0 = 0 | Some (q, n) => 4 <= n < 2 ^ 31 /\ rw_cells ctusegs mX A0 [CB (Z.to_nat n) bytes] end ->
    implM ctusegs (interp (ap_embed (buf_grow_clean b len stX))) sX
          (grow_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX fcX stX OWX boX mX NEW1 b len BUF bytes)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz RATP) t0 t1 t2 s0 s1 (wz BUF) (wz len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              FX (wz BUF_GROW_CLEAN) fcX None mX (seg_rom ctusegs)).
  Proof using B63 CEIL GLO HF HM PBX SP16 SPB XPok.
    intros until bytes. intros LO OFS0 OFS16 STKG OI FRMX BUFlo BUFhi BUFal HBUF LENB LTL LEN30 HDATA.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (STK0 : 0 <= STK) by (unfold GROW_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK in STKG; lia).
    pose proof (ESP sp lo B OFS STK GLO LO STK0 OFS0 SPB B63) as ESP.
    destruct b as [L0 [[q0 n0]|] bys]; unfold buf_blk, buf_cells, bm_max in *; cbn [bm_len bm_data bm_bytes app] in *;
      unfold GROW_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK in STKG; unfold BUF_GROW_CLEAN, MallocRep.wz in *;
      unfold buf_grow_clean, bm_max; cbn [bm_len bm_data bm_bytes];
      replace (len <=? L0) with false by (symmetry; apply Z.leb_gt; lia);
      cut_hd HBUF HLEN (BUF + 8); cut_hd HBUF HDAT (BUF + 16); cut_hd HBUF HMAX (BUF + 24); rename HBUF into HFLG.
    + (* [comment removed for export] *)
      destruct HDATA as [N4 HBLK].
      pose proof (oinv_facts sp m s LB E lo B canary K c D XP OFS STK _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & DJL & DJO).
      pose proof (oinv_call sp m s LB E lo B canary K c D XP OFS STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (_ & AUXX & SPBX & STX & _ & _ & ERRX & MIX & CSX & ASX).
      pose proof OI as (PREX & LXX & KO & KI & KP & SO & FA & HB).
      unfold LX_ERRNO, RATP in ERRX. change (3355176 - 164) with 3355012 in ERRX. clear HB.
      pose proof (BND q0 A0 n0 ltac:(apply in_app_iff; right; left; reflexivity)) as (BA0 & _ & BAC & BAI & _).
      pose proof (munch_refl [(bv_unsigned sp + OFS - 112, bv_unsigned sp + OFS); (BUF, BUF + 32); (A0, A0 + n0)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
      unfold implM. iprefix.
      (* [comment removed for export] *)
      carve_frame 48%nat STX. do 7 step.
      step. step. step.
      step. if_cases K0; zc K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; lia|]. clear K0.
      step.
      step. if_cases KR; zc KR.
      * (* [comment removed for export] *)
        replace (len <=? n0) with true by (symmetry; apply Z.leb_le; lia).
        step. step. step. step. step. step.
        step. setreg 12%Z (Z_to_bv 64 (len - L0)) ltac:(rewrite (unsigned_lit L0) by lia; f_equal; lia).
        (* [comment removed for export] *)
        pose proof (cb_len _ _ _ _ HBLK) as BL.
        replace (Z.to_nat n0) with (Z.to_nat L0 + Z.to_nat (n0 - L0))%nat in HBLK by lia.
        apply cb_split in HBLK. cut_hd HBLK HB1 (A0 + L0).
        replace (Z.to_nat (n0 - L0)) with (Z.to_nat (len - L0) + Z.to_nat (n0 - len))%nat in HBLK by lia.
        apply cb_split in HBLK. cut_hd HBLK HB2 (A0 + len). rename HBLK into HB3.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end. setreg 10%Z (Z_to_bv 64 (A0 + L0)) ltac:(f_equal; lia).
        eapply evt_cut.
        { eapply (memset_specZ (A0 + L0) (len - L0) 0); [exact HB2| assumption| reflexivity| reflexivity| reflexivity| lia| lia| lia]. }
        intros ms' PO. unfold memsetZ_post in PO.
        destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & HZ2).
        xport FR MU2 WM2. xport HLEN MU2 WM2. xport HDAT MU2 WM2. xport HMAX MU2 WM2. xport HFLG MU2 WM2. xport HB1 MU2 WM2. xport HB3 MU2 WM2. xport ERRX MU2 WM2.
        match goal with H : stk ctusegs m1 lo _ |- _ => rename H into ST1 end.
        assert (ST2 : stk ctusegs m2 lo (bv_unsigned sp + OFS + -48)).
        { eapply stk_transport; [exact ST1| exact MU2| exact WM2|]. intros x Hx. left. cbn. lia. }
        assert (MU' : munch [(bv_unsigned sp + OFS - 112, bv_unsigned sp + OFS); (BUF, BUF + 32); (A0, A0 + n0)]%Z mX m2).
        { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x; cbn; lia. }
        pose proof (wmono_trans _ _ _ _ WM WM2) as WM'. clear MU WM MU2 WM2 ST1. rename MU' into MU. rename WM' into WM.
        replace (ret_pc (Z_to_bv 64 1145376)) with (Z_to_bv 64 1145376) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        (* [comment removed for export] *)
        step. step. do 6 step. release_frame FR ST2 (bv_unsigned sp + OFS). step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end.
        match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
        ihere. to_implM. apply implM_aret. apply evt_done.
        (* [comment removed for export] *)
        join2 HZ2 HB3. apply cb_join in HZ2. replace (Z.to_nat (len - L0) + Z.to_nat (n0 - len))%nat with (Z.to_nat (n0 - L0)) in HZ2 by lia. join2 HB1 HZ2.
        join2 HLEN HDAT. join2 HLEN HMAX. join2 HLEN HFLG.
        unfold grow_post. cbn [fst snd].
        eexists u0, u1, u2, _, _, _, _, _, _, _, u3, u4, u5, u6, m3, errvX, q0, A0, n0, _.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split. { eapply (oinv_munch sp m s LB E lo B canary K c D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OI| exact MU| exact WM| exact MI3| exact ST3| exact ERRX|].
                 constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists q0, A0, n0. split; [left; reflexivity| cbn; lia]. }
        split; [exact HLEN|]. split; [exact HB1|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        eapply (lx_pres_munch_gen sX (OWX ++ [(q0, A0, n0)]) (NEW1 ++ LB)); [rewrite <- app_assoc; exact HEAPX| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; left; lia]|].
        constructor; [| constructor]. right. right. exists q0, A0, n0. split; [apply in_app_iff; right; left; reflexivity| cbn; lia].
      * (* [comment removed for export] *)
        replace (len <=? n0) with false by (symmetry; apply Z.leb_gt; lia).
        replace (LIMIT_BEFORE_EXPANSION <? len) with false by (symmetry; apply Z.ltb_ge; unfold LIMIT_BEFORE_EXPANSION; lia).
        pose proof (grow_size_bounds len ltac:(lia)) as GB. cbv zeta in GB. set (n := (len + 3) / 3 * 4) in *.
        step. step. step. if_cases KL; zc KL; [| exfalso; revert KL; rewrite ?unsigned_lit by lia; lia]. clear KL.
        apply c8_zero_bytes in HFLG. cut_hd HFLG HFL0 (BUF + 25).
        step. step. step. step. step. step. step. step. step. step. step.
        setreg 19%Z (Z_to_bv 64 n) ltac:(f_equal; symmetry; subst n; apply magic_div3_word; lia).
        step. if_false.
        join2 HFL0 HFLG. apply c8_zero_of_bytes in HFL0. rename HFL0 into HFLG.
        (* [comment removed for export] *)
        step. step. step. step. step. step.
        (* [comment removed for export] *)
        match goal with H : stk ctusegs _ lo (bv_unsigned sp + OFS + -48) |- _ => rename H into STg end.
        carve_frame 64%nat STg. do 9 step. step. step.
        step. if_cases KN; zc KN; [exfalso; revert KN; rewrite ?unsigned_lit by lia; lia|]. clear KN.
        step. step.
        step. if_cases KZ; zc KZ; [exfalso; revert KZ; rewrite ?unsigned_lit by lia; lia|]. clear KZ.
        step. if_cases KG; zc KG; [| exfalso; revert KG; rewrite ?unsigned_lit by lia; lia]. clear KG.
        step. step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
        match goal with H : stk ctusegs mc lo _ |- _ => rename H into STc end.
        match goal with H : mem_inv ctusegs mc |- _ => rename H into MIc end.
        match goal with H : rw_cells ctusegs mc (bv_unsigned sp + OFS + -112) _ |- _ => rename H into FR2 end.
        assert (E112 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS + -112)) = bv_unsigned sp + OFS + -112) by (apply unsigned_lit; lia).
        (* [comment removed for export] *)
        stk_join STc FR2 STf (bv_unsigned sp + OFS + -48). stk_join STf FR STF (bv_unsigned sp + OFS). clear STf.
        assert (OIc : oinvK OFS STK sX stX mc OWX errvX boX ((q0, A0, n0) :: NEW1)).
        { eapply (oinv_munch sp m s LB E lo B canary K c D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OI| exact MU| exact WM| exact MIc| exact STF| exact ERRX|].
          constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists q0, A0, n0. split; [left; reflexivity| cbn; lia]. }
        pose proof (oinv_call sp m s LB E lo B canary K c D XP OFS STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIc) as (HEAPc & AUXc & _ & _ & _ & _ & ERRc & _ & CSc & ASc).
        assert (LX1 : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_AP) mX mc).
        { eapply (lx_pres_munch_gen sX (OWX ++ [(q0, A0, n0)]) (NEW1 ++ LB)); [rewrite <- app_assoc; exact HEAPX| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
          constructor; [left; cbn; lia|]. constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; left; lia]|].
          constructor; [| constructor]. right. right. exists q0, A0, n0. split; [apply in_app_iff; right; left; reflexivity| cbn; lia]. }
        ihere. cbn [abind apbind amalloc aret afree_opt afree option_map ap_embed fst snd]. to_implM.
        eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (errv := errvX) (n := n) (L := OWX ++ ((q0, A0, n0) :: NEW1) ++ LB);
          [exact HEAPc| exact AUXc| rewrite E112; lia| rewrite E112; exact STc| exact CEIL| unfold GLOBALS_TOP; lia
          | rewrite E112; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia| exact ERRc| exact MIc| reflexivity| exact CSc| reflexivity| lia| reflexivity|].
        intros pn sN msN PON. unfold calloc_post in PON. rewrite ?E112 in PON.
        destruct PON as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & mN & A & errvN
                         & -> & MIN & STN & ERRN & AUXN & HPN & FAN & SON & BRN & HEAPN & (junkN & BLKN)).
        replace (ret_pc (Z_to_bv 64 0xe9f38)) with (Z_to_bv 64 0xe9f38) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof BRN as (BA0' & BA16' & _ & BAC' & BAI').
        pose proof (oinv_facts sp m s LB E lo B canary K c D XP OFS STK _ _ _ _ _ _ _ OIc) as (_ & NDc & _).
        assert (OIN : oinvK OFS STK sN stX mN OWX errvN boX ((pn, A, n) :: (q0, A0, n0) :: NEW1)).
        { eapply (oinv_alloc sp m s LB E lo B canary K c D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 PBX); [exact OIc| | exact HEAPN| exact MIN| | exact ERRN| exact AUXN| exact FAN| exact SON].
          - eapply rheap_pres_weaken; [exact HPN| lia| intros b Hb; exact Hb].
          - pose proof (agree_of_heap_pres _ _ _ _ HPN) as AG0.
            apply (rw_cells_agree _ _ _ _ _ AG0) in FR; [| intros a Ha; left; cbn in Ha; lia].
            apply (rw_cells_agree _ _ _ _ _ AG0) in FR2; [| intros a Ha; left; cbn in Ha; lia].
            stk_join STN FR2 ST1 (bv_unsigned sp + OFS + -48). stk_join ST1 FR ST2 (bv_unsigned sp + OFS). exact ST2. }
        pose proof (oinv_facts sp m s LB E lo B canary K c D XP OFS STK _ _ _ _ _ _ _ OIN) as (HEAPN' & NDN & BNDN & FRESHN & DJLN & DJON).
        (* [comment removed for export] *)
        pose proof (agree_of_heap_pres _ _ _ _ HPN) as AGN.
        assert (LX2 : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_AP) mc mN).
        { eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HPN| lia| | intros a Ha; exact Ha].
          intros b Hb. apply in_app_iff. right. right. exact Hb. }
        apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in FR2; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in HLEN; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in HDAT; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in HMAX; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in HFLG; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in HBLK; [| intros a Ha; right; right; exists (q0, A0, n0); split; [apply in_app_iff; right; left; reflexivity| cbn; cbn in Ha; lia]].
        unfold LX_ERRNO, RATP in ERRN. change (3355176 - 164) with 3355012 in ERRN.
        assert (NEQ : pn <> q0).
        { pose proof (LH_nodup _ _ _ HEAPN) as ND0. cbn [map blk_id fst snd] in ND0. apply NoDup_cons_iff in ND0.
          intros ->. apply (proj1 ND0). rewrite map_app. apply in_app_iff. right. left. reflexivity. }
        assert (SEP : A + n <= A0 \/ A0 + n0 <= A).
        { eapply (blk_disjoint _ _ _ pn A n q0 A0 n0 HEAPN'); [apply in_app_iff; right; left; reflexivity| apply in_app_iff; right; right; left; reflexivity| exact NEQ]. }
        clear MU WM AGN. pose proof (munch_refl [(bv_unsigned sp + OFS - 112, bv_unsigned sp + OFS); (BUF, BUF + 32); (A0, A0 + n0); (A, A + n)]%Z mN) as MU. pose proof (wmono_refl ctusegs mN) as WM.
        clear MIc STc. rename MIN into MI.
        (* [comment removed for export] *)
        unfold implM. iprefix.
        step. if_cases KA; zc KA; [exfalso; revert KA; rewrite ?unsigned_lit by lia; lia|]. clear KA.
        step. step. step. step. step.
        pose proof (cb_len _ _ _ _ BLKN) as JL. pose proof (cb_len _ _ _ _ HBLK) as BL.
        replace (Z.to_nat n) with (Z.to_nat n0 + Z.to_nat (n - n0))%nat in BLKN by lia.
        apply cb_split in BLKN. cut_hd BLKN HN1 (A + n0). rename BLKN into HN2.
        pose proof (rw_cells_bytes_at _ _ _ _ HBLK) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
        eapply evt_cut.
        { eapply memcpy_callZ with (Dst := A) (Src := A0) (N := n0) (src := bytes);
            [exact SRC| exact BL| exact HN1| lia| lia| lia| lia| exact MI]. }
        intros ms' PO. unfold memcpy_postZ in PO.
        destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & HCP & SRC2).
        xport FR MU2 WM2. xport FR2 MU2 WM2. xport HLEN MU2 WM2. xport HDAT MU2 WM2. xport HMAX MU2 WM2. xport HFLG MU2 WM2. xport HBLK MU2 WM2. xport HN2 MU2 WM2. xport ERRN MU2 WM2.
        match goal with H : stk ctusegs mN lo _ |- _ => rename H into ST1 end.
        assert (ST2 : stk ctusegs m2 lo (bv_unsigned sp + OFS + -112)).
        { eapply stk_transport; [exact ST1| exact MU2| exact WM2|]. intros x Hx. left. cbn. lia. }
        assert (MU' : munch [(bv_unsigned sp + OFS - 112, bv_unsigned sp + OFS); (BUF, BUF + 32); (A0, A0 + n0); (A, A + n)]%Z mN m2).
        { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x; cbn; lia. }
        pose proof (wmono_trans _ _ _ _ WM WM2) as WM'. clear MU WM MU2 WM2 ST1 MI. rename MU' into MU. rename WM' into WM. rename MI2 into MI.
        replace (ret_pc (Z_to_bv 64 0xe9f50)) with (Z_to_bv 64 0xe9f50) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        (* [comment removed for export] *)
        step. step. step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into md end.
        match goal with H : stk ctusegs md lo _ |- _ => rename H into STd end.
        stk_join STd FR2 STf (bv_unsigned sp + OFS + -48). stk_join STf FR STF2 (bv_unsigned sp + OFS). clear STf.
        assert (OId : oinvK OFS STK sN stX md OWX errvN boX ((pn, A, n) :: (q0, A0, n0) :: NEW1)).
        { eapply (oinv_munch sp m s LB E lo B canary K c D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OIN| exact MU| exact WM| exact MI| exact STF2| exact ERRN|].
          constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [right; right; exists q0, A0, n0; split; [right; left; reflexivity| cbn; lia]|].
          constructor; [| constructor]. right. right. exists pn, A, n. split; [left; reflexivity| cbn; lia]. }
        pose proof (oinv_call sp m s LB E lo B canary K c D XP OFS STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OId) as (HEAPd & AUXd & _ & _ & _ & _ & ERRd & _ & CSd & ASd).
        assert (LX3 : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_AP) mN md).
        { eapply (lx_pres_munch_gen sN (OWX ++ [(pn, A, n); (q0, A0, n0)]) (NEW1 ++ LB)); [rewrite <- app_assoc; exact HEAPN'| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
          constructor; [left; cbn; lia|]. constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; left; lia]|].
          constructor; [right; right; exists q0, A0, n0; split; [apply in_app_iff; right; right; left; reflexivity| cbn; lia]|].
          constructor; [| constructor]. right. right. exists pn, A, n. split; [apply in_app_iff; right; left; reflexivity| cbn; lia]. }
        ihere. cbn [abind apbind amalloc aret afree_opt afree option_map ap_embed fst snd]. to_implM.
        eapply (CRYPTO_clear_free_walk HF) with (B := B) (lo := lo) (errv := errvN) (A := A0) (n := n0) (num := n0) (L := OWX ++ ((pn, A, n) :: (q0, A0, n0) :: NEW1) ++ LB);
          [exact HEAPd| apply in_app_iff; right; right; left; reflexivity| exact AUXd| rewrite E112; lia| rewrite E112; exact STd| exact CEIL| unfold GLOBALS_TOP; lia
          | rewrite E112; unfold CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia| exact ERRd| exact MI| reflexivity| exact CSd| exact HBLK| lia| reflexivity| reflexivity|].
        intros sF msF POF. unfold cfree_post in POF. rewrite ?E112 in POF.
        destruct POF as (z0 & z1 & z2 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z3 & z4 & z5 & z6 & mF & -> & MIF & STF' & ERRF & AUXF & HPF & FAF & SOF & HEAPF).
        replace (ret_pc (Z_to_bv 64 0xe9f64)) with (Z_to_bv 64 0xe9f64) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (lb_remove_mid (OWX ++ [(pn, A, n)]) (q0, A0, n0) NEW1 LB) as LREM. cbn [blk_id fst snd] in LREM. rewrite <- !app_assoc in LREM. cbn [app] in LREM.
        specialize (LREM NDN). rewrite LREM in HEAPF, HPF.
        assert (OIF : oinvK OFS STK sF stX mF OWX errvN boX ((pn, A, n) :: NEW1)).
        { eapply (oinv_heap sp m s LB E lo B canary K c D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 PBX) with (L1 := OWX ++ ((pn, A, n) :: NEW1) ++ LB);
            [exact OId| eapply rheap_pres_weaken; [exact HPF| lia| intros b Hb; exact Hb]| | exact HEAPF| apply Permutation_refl| exact MIF| | exact ERRF| exact AUXF| exact FAF| exact SOF].
          - intros b [Hb|Hb]; apply in_app_iff; [left; exact Hb| right; right; apply in_app_iff; right; exact Hb].
          - pose proof (agree_of_heap_pres _ _ _ _ HPF) as AG0.
            apply (rw_cells_agree _ _ _ _ _ AG0) in FR; [| intros a Ha; left; cbn in Ha; lia].
            apply (rw_cells_agree _ _ _ _ _ AG0) in FR2; [| intros a Ha; left; cbn in Ha; lia].
            stk_join STF' FR2 ST1 (bv_unsigned sp + OFS + -48). stk_join ST1 FR ST2 (bv_unsigned sp + OFS). exact ST2. }
        pose proof (oinv_facts sp m s LB E lo B canary K c D XP OFS STK _ _ _ _ _ _ _ OIF) as (HEAPF' & NDF & BNDF & FRESHF & DJLF & DJOF).
        (* [comment removed for export] *)
        pose proof (agree_of_heap_pres _ _ _ _ HPF) as AGF.
        assert (LX4 : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_AP) md mF).
        { eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HPF| lia| | intros a Ha; exact Ha].
          intros b Hb. apply in_app_iff. right. right. exact Hb. }
        apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGF) in FR2; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGF) in HLEN; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGF) in HDAT; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGF) in HMAX; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGF) in HFLG; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGF) in HCP; [| intros a Ha; right; right; exists (pn, A, n); split; [apply in_app_iff; right; left; reflexivity| cbn; cbn in Ha; lia]].
        apply (rw_cells_agree _ _ _ _ _ AGF) in HN2; [| intros a Ha; right; right; exists (pn, A, n); split; [apply in_app_iff; right; left; reflexivity| cbn; cbn in Ha; lia]].
        unfold LX_ERRNO, RATP in ERRF. change (3355176 - 164) with 3355012 in ERRF.
        clear MU WM AGF HEAPd AUXd ERRd CSd ASd OId STd STF2 MI. rename MIF into MI.
        pose proof (munch_refl [(bv_unsigned sp + OFS - 112, bv_unsigned sp + OFS); (BUF, BUF + 32); (A, A + n)]%Z mF) as MU. pose proof (wmono_refl ctusegs mF) as WM.
        (* [comment removed for export] *)
        unfold implM. iprefix.
        step. step. step. do 8 step. release_frame FR2 STF' (bv_unsigned sp + OFS + -48). step.
        replace (ret_pc (Z_to_bv 64 0x1179f4)) with (Z_to_bv 64 0x1179f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        step. if_cases KA; zc KA; [exfalso; revert KA; rewrite ?unsigned_lit by lia; lia|]. clear KA.
        unfold MallocRep.wz in *. step. step. step. step. step. step. step.
        step. setreg 12%Z (Z_to_bv 64 (len - L0)) ltac:(rewrite (unsigned_lit L0) by lia; f_equal; lia).
        (* [comment removed for export] *)
        join2 HCP HN2. apply cb_join in HCP.
        replace (Z.to_nat n0 + Z.to_nat (n - n0))%nat with (Z.to_nat L0 + Z.to_nat (n - L0))%nat in HCP by lia.
        apply cb_split in HCP. cut_hd HCP HB1 (A + L0).
        replace (Z.to_nat (n - L0)) with (Z.to_nat (len - L0) + Z.to_nat (n - len))%nat in HCP by lia.
        apply cb_split in HCP. cut_hd HCP HB2 (A + len). rename HCP into HB3.
        step. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end. setreg 10%Z (Z_to_bv 64 (A + L0)) ltac:(f_equal; lia).
        eapply evt_cut.
        { eapply (memset_specZ (A + L0) (len - L0) 0); [exact HB2| assumption| reflexivity| reflexivity| reflexivity| lia| lia| lia]. }
        intros ms' PO. unfold memsetZ_post in PO.
        destruct PO as (y0 & y1 & y2 & x1' & x2' & x3 & x4 & x5 & x6 & x7 & y3 & y4 & y5 & y6 & m6 & -> & MU6 & WM6 & MI6 & HZ6).
        xport FR MU6 WM6. xport HLEN MU6 WM6. xport HDAT MU6 WM6. xport HMAX MU6 WM6. xport HFLG MU6 WM6. xport HB1 MU6 WM6. xport HB3 MU6 WM6. xport ERRF MU6 WM6.
        match goal with H : stk ctusegs m5 lo _ |- _ => rename H into ST5 end.
        assert (ST6 : stk ctusegs m6 lo (bv_unsigned sp + OFS + -48)).
        { eapply stk_transport; [exact ST5| exact MU6| exact WM6|]. intros x Hx. left. cbn. lia. }
        assert (MU' : munch [(bv_unsigned sp + OFS - 112, bv_unsigned sp + OFS); (BUF, BUF + 32); (A, A + n)]%Z mF m6).
        { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU6]. intros x; cbn; lia. }
        pose proof (wmono_trans _ _ _ _ WM WM6) as WM'. clear MU WM MU6 WM6 ST5 MI. rename MU' into MU. rename WM' into WM. rename MI6 into MI.
        replace (ret_pc (Z_to_bv 64 1145376)) with (Z_to_bv 64 1145376) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        (* [comment removed for export] *)
        step. step. do 6 step. release_frame FR ST6 (bv_unsigned sp + OFS). step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
        match goal with H : stk ctusegs m7 lo _ |- _ => rename H into ST7 end.
        ihere. to_implM. apply implM_aret. apply evt_done.
        (* [comment removed for export] *)
        join2 HZ6 HB3. apply cb_join in HZ6. replace (Z.to_nat (len - L0) + Z.to_nat (n - len))%nat with (Z.to_nat (n - L0)) in HZ6 by lia. join2 HB1 HZ6.
        join2 HLEN HDAT. join2 HLEN HMAX. join2 HLEN HFLG.
        unfold grow_post. cbn [fst snd].
        eexists y0, y1, y2, _, _, _, _, _, _, _, y3, y4, y5, y6, m7, errvN, pn, A, n, _.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split. { eapply (oinv_munch sp m s LB E lo B canary K c D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OIF| exact MU| exact WM| exact MI| exact ST7| exact ERRF|].
                 constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists pn, A, n. split; [left; reflexivity| cbn; lia]. }
        split; [exact HLEN|].
        split. { rewrite firstn_app in HB1. replace (Z.to_nat L0 - length bytes)%nat with 0%nat in HB1 by lia. cbn [take] in HB1. rewrite app_nil_r in HB1. exact HB1. }
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        eapply lx_pres_trans; [exact LX1|]. eapply lx_pres_trans; [exact LX2|]. eapply lx_pres_trans; [exact LX3|]. eapply lx_pres_trans; [exact LX4|].
        eapply (lx_pres_munch_gen sF (OWX ++ [(pn, A, n)]) (NEW1 ++ LB)); [rewrite <- app_assoc; exact HEAPF'| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; left; lia]|].
        constructor; [| constructor]. right. right. exists pn, A, n. split; [apply in_app_iff; right; left; reflexivity| cbn; lia].
    + (* [comment removed for export] *)
      assert (L00 : L0 = 0) by lia. subst A0. rewrite L00 in *. clear LENB L00.
      pose proof (oinv_facts sp m s LB E lo B canary K c D XP OFS STK _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & DJL & DJO).
      pose proof (oinv_call sp m s LB E lo B canary K c D XP OFS STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (_ & AUXX & SPBX & STX & _ & _ & ERRX & MIX & CSX & ASX).
      pose proof OI as (PREX & LXX & KO & KI & KP & SO & FA & HB).
      unfold LX_ERRNO, RATP in ERRX. change (3355176 - 164) with 3355012 in ERRX. clear HB.
      pose proof (munch_refl [(bv_unsigned sp + OFS - 112, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
      replace (len <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
      replace (LIMIT_BEFORE_EXPANSION <? len) with false by (symmetry; apply Z.ltb_ge; unfold LIMIT_BEFORE_EXPANSION; lia).
      pose proof (grow_size_bounds len ltac:(lia)) as GB. cbv zeta in GB. set (n := (len + 3) / 3 * 4) in *.
      unfold implM. iprefix.
      (* [comment removed for export] *)
      carve_frame 48%nat STX. do 7 step.
      step. step. step.
      step. if_cases K0; zc K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; lia|]. clear K0.
      step.
      step. if_cases KR; zc KR; [exfalso; revert KR; rewrite ?unsigned_lit by lia; lia|]. clear KR.
      step. step. step. if_cases KL; zc KL; [| exfalso; revert KL; rewrite ?unsigned_lit by lia; lia]. clear KL.
      apply c8_zero_bytes in HFLG. cut_hd HFLG HFL0 (BUF + 25).
      step. step. step. step. step. step. step. step. step. step. step.
      setreg 19%Z (Z_to_bv 64 n) ltac:(f_equal; symmetry; subst n; apply magic_div3_word; lia).
      step. if_false.
      join2 HFL0 HFLG. apply c8_zero_of_bytes in HFL0. rename HFL0 into HFLG.
      (* [comment removed for export] *)
      step. step. step. step. step. step.
      match goal with H : stk ctusegs _ lo (bv_unsigned sp + OFS + -48) |- _ => rename H into STg end.
      carve_frame 64%nat STg. do 9 step. step. step.
      step. if_cases KN; zc KN; [| exfalso; revert KN; rewrite ?unsigned_lit by lia; lia]. clear KN.
      step. step. step. do 8 step.
      match goal with H : rw_cells ctusegs _ (bv_unsigned sp + OFS + -112) _ |- _ => rename H into FR2 end.
      match goal with H : stk ctusegs _ lo (bv_unsigned sp + OFS + -112) |- _ => release_frame FR2 H (bv_unsigned sp + OFS + -48) end.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
      match goal with H : stk ctusegs mc lo _ |- _ => rename H into STc end.
      match goal with H : mem_inv ctusegs mc |- _ => rename H into MIc end.
      assert (E48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS + -48)) = bv_unsigned sp + OFS + -48) by (apply unsigned_lit; lia).
      stk_join STc FR STF (bv_unsigned sp + OFS).
      assert (OIc : oinvK OFS STK sX stX mc OWX errvX boX NEW1).
      { eapply (oinv_munch sp m s LB E lo B canary K c D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OI| exact MU| exact WM| exact MIc| exact STF| exact ERRX|].
        constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
      pose proof (oinv_call sp m s LB E lo B canary K c D XP OFS STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIc) as (HEAPc & AUXc & _ & _ & _ & _ & ERRc & _ & CSc & ASc).
      assert (LX1 : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_AP) mX mc).
      { eapply (lx_pres_munch_gen sX OWX (NEW1 ++ LB)); [exact HEAPX| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; left; lia]| constructor]. }
      ihere. cbn [abind apbind amalloc aret afree_opt afree option_map ap_embed fst snd]. to_implM.
      eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (errv := errvX) (n := n) (L := OWX ++ NEW1 ++ LB);
        [exact HEAPc| exact AUXc| rewrite E48; lia| rewrite E48; exact STc| exact CEIL| unfold GLOBALS_TOP; lia
        | rewrite E48; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia| exact ERRc| exact MIc| reflexivity| exact CSc| reflexivity| lia| reflexivity|].
      intros pn sN msN PON. unfold calloc_post in PON. rewrite ?E48 in PON.
      destruct PON as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & mN & A & errvN
                       & -> & MIN & STN & ERRN & AUXN & HPN & FAN & SON & BRN & HEAPN & (junkN & BLKN)).
      replace (ret_pc (Z_to_bv 64 0x1179f4)) with (Z_to_bv 64 0x1179f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof BRN as (BA0' & BA16' & _ & BAC' & BAI').
      assert (OIN : oinvK OFS STK sN stX mN OWX errvN boX ((pn, A, n) :: NEW1)).
      { eapply (oinv_alloc sp m s LB E lo B canary K c D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 PBX); [exact OIc| | exact HEAPN| exact MIN| | exact ERRN| exact AUXN| exact FAN| exact SON].
        - eapply rheap_pres_weaken; [exact HPN| lia| intros b Hb; exact Hb].
        - pose proof (agree_of_heap_pres _ _ _ _ HPN) as AG0.
          apply (rw_cells_agree _ _ _ _ _ AG0) in FR; [| intros a Ha; left; cbn in Ha; lia].
          stk_join STN FR ST2 (bv_unsigned sp + OFS). exact ST2. }
      pose proof (oinv_facts sp m s LB E lo B canary K c D XP OFS STK _ _ _ _ _ _ _ OIN) as (HEAPN' & NDN & BNDN & FRESHN & DJLN & DJON).
      pose proof (agree_of_heap_pres _ _ _ _ HPN) as AGN.
      assert (LX2 : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_AP) mc mN).
      { eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HPN| lia| | intros a Ha; exact Ha].
        intros b Hb. apply in_app_iff. right. exact Hb. }
      apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HLEN; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HDAT; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HMAX; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HFLG; [| intros a Ha; left; cbn in Ha; lia].
      unfold LX_ERRNO, RATP in ERRN. change (3355176 - 164) with 3355012 in ERRN.
      clear MU WM AGN MIc STc STF. rename MIN into MI.
      pose proof (munch_refl [(bv_unsigned sp + OFS - 112, bv_unsigned sp + OFS); (BUF, BUF + 32); (A, A + n)]%Z mN) as MU. pose proof (wmono_refl ctusegs mN) as WM.
      (* [comment removed for export] *)
      unfold implM. iprefix.
      step. if_cases KA; zc KA; [exfalso; revert KA; rewrite ?unsigned_lit by lia; lia|]. clear KA.
      unfold MallocRep.wz in *. step. step. step. step. step. step. step.
      step. setreg 12%Z (Z_to_bv 64 len) ltac:(f_equal; rewrite ?unsigned_lit by lia; lia). setreg 10%Z (Z_to_bv 64 A) ltac:(f_equal; lia).
      pose proof (cb_len _ _ _ _ BLKN) as JL.
      replace (Z.to_nat n) with (Z.to_nat len + Z.to_nat (n - len))%nat in BLKN by lia.
      apply cb_split in BLKN. cut_hd BLKN HB2 (A + len). rename BLKN into HB3.
      step. try setreg 10%Z (Z_to_bv 64 A) ltac:(f_equal; lia). lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      eapply evt_cut.
      { eapply (memset_specZ A len 0); [exact HB2| assumption| reflexivity| reflexivity| reflexivity| lia| lia| lia]. }
      intros ms' PO. unfold memsetZ_post in PO.
      destruct PO as (y0 & y1 & y2 & x1' & x2' & x3 & x4 & x5 & x6 & x7 & y3 & y4 & y5 & y6 & m6 & -> & MU6 & WM6 & MI6 & HZ6).
      xport FR MU6 WM6. xport HLEN MU6 WM6. xport HDAT MU6 WM6. xport HMAX MU6 WM6. xport HFLG MU6 WM6. xport HB3 MU6 WM6. xport ERRN MU6 WM6.
      match goal with H : stk ctusegs m5 lo _ |- _ => rename H into ST5 end.
      assert (ST6 : stk ctusegs m6 lo (bv_unsigned sp + OFS + -48)).
      { eapply stk_transport; [exact ST5| exact MU6| exact WM6|]. intros x Hx. left. cbn. lia. }
      assert (MU' : munch [(bv_unsigned sp + OFS - 112, bv_unsigned sp + OFS); (BUF, BUF + 32); (A, A + n)]%Z mN m6).
      { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU6]. intros x; cbn; lia. }
      pose proof (wmono_trans _ _ _ _ WM WM6) as WM'. clear MU WM MU6 WM6 ST5 MI. rename MU' into MU. rename WM' into WM. rename MI6 into MI.
      replace (ret_pc (Z_to_bv 64 1145376)) with (Z_to_bv 64 1145376) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      step. step. do 6 step. release_frame FR ST6 (bv_unsigned sp + OFS). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
      match goal with H : stk ctusegs m7 lo _ |- _ => rename H into ST7 end.
      ihere. to_implM. apply implM_aret. apply evt_done.
      (* [comment removed for export] *)
      join2 HZ6 HB3. apply cb_join in HZ6.
      assert (HB1 : rw_cells ctusegs m7 A [CB (Z.to_nat 0) (firstn (Z.to_nat 0) bytes); CB (Z.to_nat (n - 0)) (repeat (Z_to_bv 8 0) (Z.to_nat len) ++ drop (Z.to_nat len) junkN)]).
      { eapply rw_cells_recast; [exact HZ6| cbn; rewrite length_app, repeat_length, length_drop; repeat split; lia| reflexivity| cbn; lia]. }
      join2 HLEN HDAT. join2 HLEN HMAX. join2 HLEN HFLG.
      unfold grow_post. cbn [fst snd].
      eexists y0, y1, y2, _, _, _, _, _, _, _, y3, y4, y5, y6, m7, errvN, pn, A, n, _.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split. { eapply (oinv_munch sp m s LB E lo B canary K c D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OIN| exact MU| exact WM| exact MI| exact ST7| exact ERRN|].
               constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists pn, A, n. split; [left; reflexivity| cbn; lia]. }
      split; [exact HLEN|]. split; [exact HB1|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      eapply lx_pres_trans; [exact LX1|]. eapply lx_pres_trans; [exact LX2|].
      eapply (lx_pres_munch_gen sN (OWX ++ [(pn, A, n)]) (NEW1 ++ LB)); [rewrite <- app_assoc; exact HEAPN'| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
      constructor; [left; cbn; lia|]. constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; left; lia]|].
      constructor; [| constructor]. right. right. exists pn, A, n. split; [apply in_app_iff; right; left; reflexivity| cbn; lia].
  Qed.
  End Act.
End Proofs.
End WithCeiling0.
