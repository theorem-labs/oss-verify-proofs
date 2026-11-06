(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_getrn Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_lh_retrieve : Z := 0x1fd020.
Definition SITE_lh_retrieve_getrn : Z := 0x1fd07c.     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cb8_c8_in : forall (m : mem) A pre post bs, rw_cells bsegs m A (pre ++ CB 8 bs :: post) -> rw_cells bsegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. pose proof (img_le8_of_bytes bs H2) as E8. replace (le8 (le_bytes_to_word bs)) with bs by (symmetry; exact E8). exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Definition lh_retrieve_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (v : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (lh + 96, lh + 100)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ lh_rep bsegs LH_CEIL (DVerr GOBJ) m' (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks
    /\ (v = 0 \/ DVerr GOBJ v).

(* [comment removed for export] *)
Definition lh_retrieve_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data lo : Z) (kw : word),
  lh_rep bsegs LH_CEIL (DVerr GOBJ) m (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks -> lapart L ->
  acc bsegs m lh 104 -> lh mod 8 = 0 -> lh + 104 <= lo -> 0x10007fff8000 <= lh ->
  acc bsegs m B (8 * g_na g) -> B mod 8 = 0 -> B + 8 * g_na g <= lo ->
  (forall p A, In (p, A) (concat bks) -> acc bsegs m A 24 /\ A mod 8 = 0 /\ A + 24 <= lo) ->
  (forall d, DVerr GOBJ d -> (exists e : word, ro_cells bsegs m d [C8 e]) /\ acc bsegs m d 8) -> IMG_UT_HI <= lo ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 data ->
  ro_cells bsegs m data [C8 kw] -> acc bsegs m data 8 -> data mod 8 = 0 -> data + 8 <= lo -> 0 < data -> (data + 8 <= lh \/ lh + 104 <= data) ->
  acc bsegs m (bv_unsigned sp - 32) 32 -> bv_unsigned sp mod 16 = 0 ->
  img_untouched m -> ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk bsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 144 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv bsegs m ->
  evt bsegs (lh_retrieve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L lh B g bks)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_lh_retrieve) fc None m (seg_rom bsegs)).

Theorem lh_retrieve_proof : lh_retrieve_stmt.
Proof.
  unfold lh_retrieve_stmt, g_shadow_memory_dynamic_address, SHB, e_lh_retrieve.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m GOBJ L lh B g bks data lo kw
         REP LAP ACCL ALL LLO LHI ACCB ALB BLO NODES DVF UTLO -> -> KC KA KAL KLO KNZ KSEP ACCF SPAL UT SHC ST LO0 LO HTOP MI.
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB. pose proof G as (G1 & G2 & G3 & G4 & G5 & G6).
  unfold lh_cells, ERR_FNS_A, lf_comp, lf_hash, lf_hashw, lf_compw, wz, e_err_cmp, e_err_hash, e_err_hash_thunk, e_err_comp_thunk in SC.
  destruct (lh_sep bsegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ (ownL_apart L LAP) REP) as (S_LB & S_N & S_X & S_F).
  unfold USTACK_TOP, IMG_UT_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (ro_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (lh + 96, lh + 100)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-32) EU1.
  (* [comment removed for export] *)
  assert (KEYAT : forall mc, munch [(bv_unsigned sp - 144, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc -> ro_cells bsegs mc data [C8 kw]).
  { intros mc MUc. eapply ro_cells_transport; [exact KC| exact MUc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (SHCAT : forall mc, munch [(bv_unsigned sp - 144, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc -> ro_cells bsegs mc 6943544 [C8 (Z_to_bv 64 2147450880)]).
  { intros mc MUc. eapply ro_cells_transport; [exact SHC| exact MUc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (NODESAT : forall mc, munch [(bv_unsigned sp - 144, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc ->
    forall p A, In (p, A) (concat bks) -> acc bsegs mc A 24 /\ A mod 8 = 0 /\ A + 24 <= lo).
  { intros mc MUc q A Hin. destruct (NODES q A Hin) as (X1 & X2 & X3). split; [| split; [exact X2| exact X3]].
    apply in_concat in Hin as (ns & Hns & HinA). destruct (In_nth _ _ [] Hns) as (i & Hi & <-).
    pose proof (CH (Z.of_nat i) ltac:(lia)) as (c0 & SS & _). rewrite Nat2Z.id in SS. pose proof (lseg_ranges bsegs LH_CEIL _ _ _ _ _ _ SS q A HinA) as [R0 _].
    exact (acc_munch_sh _ m _ _ _ X1 MUc HWS ltac:(lia) ltac:(lia)). }
  assert (DVFAT : forall mc, munch [(bv_unsigned sp - 144, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc ->
    forall d, DVerr GOBJ d -> (exists e : word, ro_cells bsegs mc d [C8 e]) /\ acc bsegs mc d 8).
  { intros mc MUc d Hd. pose proof Hd as (_ & D1 & D2 & _). unfold IMG_UT_LO, IMG_UT_HI in D1, D2. destruct (DVF d Hd) as ((e & C) & X). split.
    - exists e. eapply ro_cells_transport; [exact C| exact MUc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - exact (acc_munch_sh _ m _ _ _ X MUc HWS ltac:(lia) ltac:(lia)). }
  (* [comment removed for export] *)
  assert (REPAT : forall mc (err' : word), munch [(bv_unsigned sp - 144, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc -> wmono bsegs m mc ->
    rw_cells bsegs mc lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 2077204); C8 (Z_to_bv 64 2077056); C8 (Z_to_bv 64 2077340); C8 (Z_to_bv 64 2077372); C8 x40; C8 x48;
                          C4 (Z_to_bv 64 (g_nn g)); C4 (Z_to_bv 64 (g_na g)); C4 (Z_to_bv 64 (g_p g)); C4 (Z_to_bv 64 (g_pmax g)); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256);
                          C8 (Z_to_bv 64 (g_items g)); C4 err'; C4 pad] ->
    lh_rep bsegs LH_CEIL (DVerr GOBJ) mc (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks).
  { intros mc err' MUc WMc SCc. pose proof (LhRep.agree_on_of_munch bsegs _ _ _ MUc WMc) as AGc.
    eapply (lh_rep_upd bsegs LH_CEIL (DVerr GOBJ) m mc (ownL L) (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g g bks bks (fun _ => False) REP); try reflexivity; try assumption.
    - intros i. right. intros X. exact X.
    - exists x40, x48, err', pad. unfold lh_cells, ERR_FNS_A, lf_comp, lf_hash, lf_hashw, lf_compw, wz, e_err_cmp, e_err_hash, e_err_hash_thunk, e_err_comp_thunk. exact SCc.
    - intros q A n nm _ X. exact X.
    - intros i Hi [].
    - intros i Hi _. split; [reflexivity|]. eapply LhRep.agree_on_mono; [exact AGc|]. intros a [Ha|(q & A & Hq & Ha)]; cbn [outside]; [lia|].
      assert (LI : (Z.to_nat i < length bks)%nat) by lia. destruct (S_N _ q A LI Hq) as [X1 _].
      pose proof (NODES q A (in_concat_nth bks _ _ LI Hq)) as (_ & _ & X3). lia. }
  (* [comment removed for export] *)
  assert (EPI : forall (v : Z) (err' z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 hv : word) (mc2 : mem),
    (v = 0 \/ DVerr GOBJ v) ->
    rw_cells bsegs mc2 (bv_unsigned sp + -32) [C8 hv] -> rw_cells bsegs mc2 (bv_unsigned sp + -24) [C8 s1; C8 s0; C8 ra] ->
    rw_cells bsegs mc2 lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 2077204); C8 (Z_to_bv 64 2077056); C8 (Z_to_bv 64 2077340); C8 (Z_to_bv 64 2077372); C8 x40; C8 x48;
                        C4 (Z_to_bv 64 (g_nn g)); C4 (Z_to_bv 64 (g_na g)); C4 (Z_to_bv 64 (g_p g)); C4 (Z_to_bv 64 (g_pmax g)); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256);
                        C8 (Z_to_bv 64 (g_items g)); C4 err'; C4 pad] ->
    stk bsegs mc2 lo (bv_unsigned sp + -32) -> munch [(bv_unsigned sp - 144, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc2 -> wmono bsegs m mc2 -> mem_inv bsegs mc2 ->
    evt bsegs (lh_retrieve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L lh B g bks)
      (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp z1 z2 z3 sp (Z_to_bv 64 2147450880) (Z_to_bv 64 v) z4 z5 z6 z7 z8 z9 z10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z11 z12 z13 z14)
          F (Z_to_bv 64 0x1fd0b8) fc None mc2 (seg_rom bsegs))).
  { intros v err' z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 hv mc2 VOK F0 FS SC2 ST2 MU2 WM2 MI2.
    assert (FJ : rw_cells bsegs mc2 (bv_unsigned sp + -32) ([C8 hv] ++ [C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact F0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by lia. exact FS. }
    cbn [app] in FJ. clear F0 FS.
    do 3 zstep. release_frame FJ ST2 (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold lh_retrieve_post. do 14 eexists. exists mc2, v. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact (REPAT mc2 err' MU2 WM2 SC2)| exact VOK]. }
  (* [comment removed for export] *)
  assert (TAIL : forall (err' y3 y4 : word) (jj : list byte) (mc : mem),
    rw_cells bsegs mc (bv_unsigned sp + -32) [CB 8 jj; C8 s1; C8 s0; C8 ra] ->
    rw_cells bsegs mc lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 2077204); C8 (Z_to_bv 64 2077056); C8 (Z_to_bv 64 2077340); C8 (Z_to_bv 64 2077372); C8 x40; C8 x48;
                        C4 (Z_to_bv 64 (g_nn g)); C4 (Z_to_bv 64 (g_na g)); C4 (Z_to_bv 64 (g_p g)); C4 (Z_to_bv 64 (g_pmax g)); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256);
                        C8 (Z_to_bv 64 (g_items g)); C4 err'; C4 pad] ->
    stk bsegs mc lo (bv_unsigned sp + -32) -> munch [(bv_unsigned sp - 144, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    evt bsegs (lh_retrieve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L lh B g bks)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 2147450880) (Z_to_bv 64 lh) (Z_to_bv 64 data) (Z_to_bv 64 (lh + 96)) y3 y4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1fd074) fc None mc (seg_rom bsegs))).
  { intros err' y3 y4 jj mc FRc SCc STc MUc WMc MIc.
    apply (cb8_c8_in mc _ [] _ _) in FRc. cbn [app] in FRc.
    lazymatch type of FRc with rw_cells _ _ _ [C8 ?hs; C8 s1; C8 s0; C8 ra] => change [C8 hs; C8 s1; C8 s0; C8 ra] with ([C8 hs] ++ [C8 s1; C8 s0; C8 ra]) in FRc end.
    apply (proj1 (rw_cells_app _ _ _ _)) in FRc. destruct FRc as [F0 FS]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FS.
    replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in FS by lia.
    assert (HPA : acc bsegs mc (bv_unsigned sp + -32) 8).
    { pose proof (acc_munch_sh _ m _ _ _ ACCF MUc HWS ltac:(lia) ltac:(lia)) as X. apply (acc_sub bsegs mc _ _ _ _ X); lia. }
    zstep. zstep.
    eapply evt_cut; [eapply getrn_proof with (GOBJ := GOBJ) (L := L) (lh := lh) (B := B) (g := g) (bks := bks) (data := data) (hp := bv_unsigned sp + -32) (lo := lo) | post_call bsegs mc];
      [exact (REPAT mc err' MUc WMc SCc)| exact (acc_munch_sh _ m _ _ _ ACCL MUc HWS ltac:(lia) ltac:(lia))| exact ALL| exact LLO
      | exact (acc_munch_sh _ m _ _ _ ACCB MUc HWS ltac:(lia) ltac:(lia))| exact ALB| exact BLO| exact (NODESAT mc MUc)| exact (DVFAT mc MUc)| unfold IMG_UT_HI; lia
      | reflexivity| reflexivity| reflexivity
      | exact (KEYAT mc MUc)| exact (acc_munch_sh _ m _ _ _ KA MUc HWS ltac:(lia) ltac:(lia))| exact KAL| exact KLO| exact KNZ
      | exact F0| exact HPA| Z.div_mod_to_equations; lia
      | rewrite EU1; lia| unfold USTACK_TOP; lia
      | exact (ut_munch _ m _ UT MUc HWU)| exact (SHCAT mc MUc)| rewrite EU1; exact STc| lia| rewrite EU1; lia| lia| assumption|].
    lazymatch goal with S1 : lseg _ _ _ ?mq _ _ ?n1 ?r, C2 : chain _ _ _ _ _ _ ?n2, HI : 0 <= ?i < _, HP2 : rw_cells _ _ (bv_unsigned sp + -32) [C8 ?hh] |- _ =>
      rename mq into m2; rename r into rn; rename n1 into ns1; rename n2 into ns2; rename i into idx; rename hh into h end.
    lazymatch goal with H : stk bsegs m2 lo _ |- _ => rewrite EU1 in H; rename H into ST2 end.
    lazymatch goal with H : lseg _ _ _ m2 _ _ ns1 rn |- _ => rename H into S1 end.
    lazymatch goal with H : chain _ _ _ m2 _ rn ns2 |- _ => rename H into C2 end.
    lazymatch goal with H : nth _ bks [] = ns1 ++ ns2 |- _ => rename H into ENTH end.
    lazymatch goal with H : rw_cells _ m2 (bv_unsigned sp + -32) [C8 h] |- _ => rename H into HP2 end.
    assert (LI : (Z.to_nat idx < length bks)%nat) by lia.
    destruct (chain_chainv bsegs LH_CEIL _ _ _ _ _ C2) as (v & CRN & CV). unfold wz in CRN.
    pose proof (rw_cells_bound _ _ _ _ CRN) as RNB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in RNB.
    (* [comment removed for export] *)
    assert (RNACC : exists p n, acc bsegs m p n /\ p mod 8 = 0 /\ 0 <= p /\ p <= rn /\ rn + 8 <= p + n /\ p + n <= 2^47).
    { destruct (lseg_end_loc bsegs LH_CEIL _ _ _ _ _ _ S1) as [[_ ->]|(pre & q & A & -> & ->)].
      - exists B, (8 * g_na g). split; [exact ACCB|]. split; [exact ALB|]. lia.
      - destruct (NODES q A ltac:(eapply in_concat_nth; [exact LI| rewrite ENTH; apply in_or_app; left; apply in_or_app; right; left; reflexivity])) as (X1 & X2 & X3).
        pose proof (lseg_ranges bsegs LH_CEIL _ _ _ _ _ _ S1 q A ltac:(apply in_or_app; right; left; reflexivity)) as [R0 _].
        exists A, 24. split; [exact X1|]. split; [exact X2|]. lia. }
    (* [comment removed for export] *)
    assert (RNAL : rn mod 8 = 0).
    { destruct (lseg_end_loc bsegs LH_CEIL _ _ _ _ _ _ S1) as [[_ ->]|(pre & q & A & -> & ->)].
      - clear - ALB. lia.
      - destruct (NODES q A ltac:(eapply in_concat_nth; [exact LI| rewrite ENTH; apply in_or_app; left; apply in_or_app; right; left; reflexivity])) as (_ & X2 & _). clear - X2. lia. }
    destruct RNACC as (pa & na' & PACC & PAL & PA0 & PA1 & PA2 & PA3).
    zstep. zstep. ubs_if.
    do 3 zstep. zstep. th_if_lit. zstep.
    destruct ns2 as [|[pk Ak] rest]; cbn [chainv] in CV.
    - subst v. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
      eapply (EPI 0); try eassumption. left. reflexivity.
    - destruct CV as (-> & OWNk & RGk & (d & hN & N1 & DVd & N2) & _). unfold wz in N1. unfold LH_CEIL, USTACK_TOP in RGk.
      destruct (NODES pk Ak ltac:(eapply in_concat_nth; [exact LI| rewrite ENTH; apply in_or_app; right; left; reflexivity])) as (Y1 & Y2 & Y3).
      zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
      zstep. zstep. ubs_if.                                                (* [comment removed for export] *)
      do 3 zstep. zstep. th_if_lit. zstep.
      eapply (EPI d); try eassumption. right. exact DVd. }
  (* [comment removed for export] *)
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 5 zstep. zstep. ubs_if. zstep. zstep. ubs_if.                         (* [comment removed for export] *)
  do 3 zstep. do 4 zstep. zstep. th_if_lit. zstep.
  zstep. if_cases K.
  - eapply TAIL; eassumption.
  - zstep. zstep. th_if_lit. zstep. th_fix_lit_store.
    eapply TAIL; eassumption.
Qed.
