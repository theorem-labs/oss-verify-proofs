(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_getrn : Z := 0x200920.
Definition SITE_getrn_hash : Z := 0x2009a8.     (* [comment removed for export] *)
Definition SITE_getrn_comp : Z := 0x200ac0.     (* [comment removed for export] *)

Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma m_remu : forall a b : word, bv_unsigned b <> 0 -> mul_div Instr.M_REMU a b = Z_to_bv 64 (bv_unsigned a mod bv_unsigned b).
Proof.
  intros a b Hb. unfold mul_div. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|_]; [contradiction|].
  apply bv_eq. rewrite bv_modu_unsigned, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ a) as RA. pose proof (bv_unsigned_in_range _ b) as RB. pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma zlxor_sign : forall n, 0 <= n < 2^63 -> Z.lxor n 9223372036854775808 = n + 9223372036854775808.
Proof.
  intros n Hn. symmetry. rewrite Z.add_nocarry_lxor; [reflexivity|]. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec i 63) as [->|NE].
  - replace (Z.testbit n 63) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec n 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - change 9223372036854775808 with (2^63). rewrite (Z.pow2_bits_eqb 63 i) by lia. replace (63 =? i) with false by (symmetry; apply Z.eqb_neq; lia). apply Bool.andb_false_r.
Qed.

(* [comment removed for export] *)
Ltac ubs_slot i b :=
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia); replace (8 * i + b <? 1) with false by (symmetry; apply Z.ltb_ge; lia); cbn [Z.b2z];
  zstep; th_if_lit; zstep; zstep;
  replace (8 * i + b <? b) with false by (symmetry; apply Z.ltb_ge; lia); rewrite (zlxor_sign (8 * i)) by lia;
  replace (8 * i + 9223372036854775808 <? 0 + 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia); cbn [Z.b2z];
  zstep; zstep; zstep; th_if_lit; zstep; ubs_if; zstep; zstep; ubs_if.

Definition getrn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (B nn hp : Z) (bks : list (list (bptr * Z))) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (i : Z) (ns1 ns2 : list (bptr * Z)) (rn : Z) (h : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rn) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 <= i < nn /\ nth (Z.to_nat i) bks [] = ns1 ++ ns2
    /\ lseg asegs LH_CEIL (DVerr GOBJ) m' (ownL L) (B + 8 * i) ns1 rn /\ chain asegs LH_CEIL (DVerr GOBJ) m' (ownL L) rn ns2
    /\ rw_cells asegs m' hp [C8 h].

(* [comment removed for export] *)
Definition getrn_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data hp lo : Z) (kw old : word),
  lh_rep asegs LH_CEIL (DVerr GOBJ) m (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> lh + 104 <= lo ->
  acc asegs m B (8 * g_na g) -> B mod 8 = 0 -> B + 8 * g_na g <= lo ->
  (forall p A, In (p, A) (concat bks) -> acc asegs m A 24 /\ A mod 8 = 0 /\ A + 24 <= lo) ->
  (forall d, DVerr GOBJ d -> (exists e : word, ro_cells asegs m d [C8 e]) /\ acc asegs m d 8) -> IMG_UT_HI <= lo ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 data -> a2 = Z_to_bv 64 hp ->
  ro_cells asegs m data [C8 kw] -> acc asegs m data 8 -> data mod 8 = 0 -> data + 8 <= lo -> 0 < data ->     (* [comment removed for export] *)
  rw_cells asegs m hp [C8 old] -> acc asegs m hp 8 -> hp mod 8 = 0 -> bv_unsigned sp <= hp -> hp + 8 <= USTACK_TOP ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L B (g_nn g) hp bks)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_getrn) fc None m (seg_rom asegs)).

Theorem getrn_proof : getrn_stmt.
Proof.
  unfold getrn_stmt, g_shadow_memory_dynamic_address, SHB, e_getrn.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m GOBJ L lh B g bks data hp lo kw old
         REP ACCL ALL LLO ACCB ALB BLO NODES DVF UTLO -> -> -> KC KA KAL KLO KNZ HPC HPA HPAL HPS HPT UT SHC ST LO0 LO HTOP MI.
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
  destruct g as [nn na p pmax items]. cbn [g_nn g_na g_p g_pmax g_items] in *.
  unfold lh_cells, ERR_FNS_A, lf_comp, lf_hash, lf_hashw, lf_compw, wz, e_err_cmp, e_err_hash, e_err_hash_thunk, e_err_comp_thunk in SC.
  cbn [g_nn g_na g_p g_pmax g_items] in SC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  unfold USTACK_TOP in HPT.
  pose proof (ro_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (rw_cells_bound _ _ _ _ HPC) as HB. cbn [cells_size csize Nat.add] in HB.
  assert (SWR : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z).
  { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
    rewrite Z.mod_small by lia. lia. }
  cl_eu (bv_unsigned sp) (-96) EU1.
  (* [comment removed for export] *)
  assert (KEYAT : forall mc, munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> ro_cells asegs mc data [C8 kw]).
  { intros mc MUc. eapply ro_cells_transport; [exact KC| exact MUc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (SHCAT : forall mc, munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> ro_cells asegs mc 6736696 [C8 (Z_to_bv 64 2147450880)]).
  { intros mc MUc. eapply ro_cells_transport; [exact SHC| exact MUc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  (* [comment removed for export] *)
  th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 14 zstep.
  do 8 zstep. zstep. th_if_lit. do 5 zstep. zstep. th_if_lit. do 3 zstep. zstep. th_if_lit. zstep.
  call err_hash_thunk_proof; [reflexivity| rewrite unsigned_lit by lia; exact KC| rewrite unsigned_lit by lia; exact (acc_munch_sh _ m _ _ _ KA MU HWS ltac:(lia) ltac:(lia))
    | rewrite unsigned_lit by lia; exact KAL| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact KLO| exact (ut_munch _ m _ UT MU HWU)| exact SHC| rewrite EU1; exact ST| lia
    | rewrite EU1; lia| rewrite EU1; lia| assumption|].
  rewrite EU1 in POST. rename POST into ST.
  (* [comment removed for export] *)
  do 2 zstep.                                                              (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit. zstep.
  do 4 zstep. zstep. th_if_lit.
  do 4 zstep. zstep. rewrite (zx32_small pmax) by lia. zstep. th_if_lit. zstep. zstep.
  rewrite (zx32_small p) by lia. rewrite m_remu by (rewrite unsigned_lit by lia; lia). rewrite (unsigned_lit pmax) by lia.
  lazymatch goal with HPh : rw_cells _ _ hp [C8 ?hh] |- _ => set (h := hh) in * end.
  (* [comment removed for export] *)
  assert (SCAT : forall mc, munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono asegs m mc ->
    exists x40' x48' err' pad', rw_cells asegs mc lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 2096404); C8 (Z_to_bv 64 2096272); C8 (Z_to_bv 64 2096512); C8 (Z_to_bv 64 2096544); C8 x40'; C8 x48';
                     C4 (Z_to_bv 64 nn); C4 (Z_to_bv 64 na); C4 (Z_to_bv 64 p); C4 (Z_to_bv 64 pmax); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 items); C4 err'; C4 pad']).
  { intros mc MUc WMc. destruct REP as (_ & _ & _ & (x40' & x48' & err' & pad' & SCm) & _). exists x40', x48', err', pad'.
    unfold lh_cells, ERR_FNS_A, lf_comp, lf_hash, lf_hashw, lf_compw, wz, e_err_cmp, e_err_hash, e_err_hash_thunk, e_err_comp_thunk in SCm. cbn [g_nn g_na g_p g_pmax g_items] in SCm.
    eapply rw_cells_transport; [exact SCm| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  (* [comment removed for export] *)
  assert (AGLO : forall mc, munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono asegs m mc -> LhRep.agree_on asegs (fun a => a + 1 <= lo) m mc).
  { intros mc MUc WMc. eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ m mc MUc WMc)|]. intros a Ha. cbv beta. cbn [outside]. lia. }
  (* [comment removed for export] *)
  assert (EXIT : forall (idx rn : Z) (ns1 ns2 : list (bptr * Z)) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 : word) (mc : mem),
    0 <= idx < nn -> nth (Z.to_nat idx) bks [] = ns1 ++ ns2 ->
    lseg asegs LH_CEIL (DVerr GOBJ) m (ownL L) (B + 8 * idx) ns1 rn -> chain asegs LH_CEIL (DVerr GOBJ) m (ownL L) rn ns2 ->
    rw_cells asegs mc (bv_unsigned sp + -96) [CB 8 (firstn 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -96) -> rw_cells asegs mc hp [C8 h] ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evt asegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L B nn hp bks)
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13
               y14 y15 (Z_to_bv 64 rn) y16 y17 y18 y19 y20 s10 s11 y21 y22 y23 t6)
          F (Z_to_bv 64 0x200b10) fc None mc (seg_rom asegs))).
  { intros idx rn ns1 ns2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 mc IDXR ENTH S1 C2 FRc STc HPc MUc WMc MIc.
    do 13 zstep. release_frame FRc STc (bv_unsigned sp). zstep.
    apply evt_done. unfold getrn_post. do 14 eexists. exists mc, idx, ns1, ns2, rn, h.
    assert (NB : forall q A, In (q, A) (ns1 ++ ns2) -> A + 24 <= lo).
    { intros q A Hin. assert (LI : (Z.to_nat idx < length bks)%nat) by lia. rewrite <- ENTH in Hin. exact (proj2 (proj2 (NODES q A (in_concat_nth bks _ _ LI Hin)))). }
    split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDXR|]. split; [exact ENTH|].
    split.
    { eapply lseg_agree; [exact S1| | intros q A _ O; exact O]. eapply LhRep.agree_on_mono; [exact (AGLO mc MUc WMc)|].
      intros a Ha. cbv beta. destruct (lseg_fp_where _ _ _ Ha) as [H0|(q & A & Hq & H0)]; [lia|]. pose proof (NB q A ltac:(apply in_or_app; left; exact Hq)). lia. }
    split; [| exact HPc].
    eapply chain_agree; [exact C2| | intros q A _ O; exact O]. eapply LhRep.agree_on_mono; [exact (AGLO mc MUc WMc)|].
    intros a [H0|(q & A & Hq & H0)]; cbv beta.
    - destruct (lseg_end_loc asegs LH_CEIL _ _ _ _ _ _ S1) as [[_ ->]|(pre & q & A & -> & ->)]; [lia|].
      pose proof (NB q A ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)). lia.
    - pose proof (NB q A ltac:(apply in_or_app; right; exact Hq)). lia. }
  (* [comment removed for export] *)
  assert (BODY : forall (idx : Z) (ns1 rest : list (bptr * Z)) (c : Z) (pn : bptr) (A : Z)
      (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (mc : mem),
    0 <= idx < nn -> nth (Z.to_nat idx) bks [] = ns1 ++ (pn, A) :: rest ->
    lseg asegs LH_CEIL (DVerr GOBJ) m (ownL L) (B + 8 * idx) ns1 c -> chain asegs LH_CEIL (DVerr GOBJ) m (ownL L) c ((pn, A) :: rest) ->
    (forall (q : bptr) (Bq : Z) (rest' : list (bptr * Z)) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 : word) (mc' : mem),
       rest = (q, Bq) :: rest' ->
       lseg asegs LH_CEIL (DVerr GOBJ) m (ownL L) (B + 8 * idx) (ns1 ++ [(pn, A)]) (A + 8) -> chain asegs LH_CEIL (DVerr GOBJ) m (ownL L) (A + 8) ((q, Bq) :: rest') ->
       rw_cells asegs mc' (bv_unsigned sp + -96) [CB 8 (firstn 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
       stk asegs mc' lo (bv_unsigned sp + -96) -> rw_cells asegs mc' hp [C8 h] ->
       munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc' -> wmono asegs m mc' -> mem_inv asegs mc' ->
       evt asegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L B nn hp bks)
         (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z1 z2 z3 sp (Z_to_bv 64 data) z4 z5 z6 z7 z8 z9 z10 z11
                  h (Z_to_bv 64 (lh + 32)) (Z_to_bv 64 (A + 8)) (Z_to_bv 64 (lh + 8)) (Z_to_bv 64 Bq) (Z_to_bv 64 2147450880)
                  (Z_to_bv 64 ((lh + 32) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 8) ≫ 3 + 2147450880)) s10 s11 z12 z13 z14 t6)
             F (Z_to_bv 64 0x200a6c) fc None mc' (seg_rom asegs))) ->
    rw_cells asegs mc (bv_unsigned sp + -96) [CB 8 (firstn 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -96) -> rw_cells asegs mc hp [C8 h] ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evt asegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L B nn hp bks)
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y1 y2 y3 sp (Z_to_bv 64 data) y4 y5 y6 y7 y8 y9 y10 y11
               h (Z_to_bv 64 (lh + 32)) (Z_to_bv 64 c) (Z_to_bv 64 (lh + 8)) (Z_to_bv 64 A) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 ((lh + 32) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 8) ≫ 3 + 2147450880)) s10 s11 y12 y13 y14 t6)
          F (Z_to_bv 64 0x200a6c) fc None mc (seg_rom asegs))).
  { intros idx ns1 rest c pn A y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 mc IDXR ENTH S1 C2 CONT FRc STc HPc MUc WMc MIc.
    pose proof C2 as (c' & (CC & OWN & RG & (d & hN & N1 & DVd & N2) & RSEG) & TERM). unfold LH_CEIL, USTACK_TOP in RG. unfold wz in N1, CC, TERM.
    assert (LI : (Z.to_nat idx < length bks)%nat) by lia.
    destruct (NODES pn A ltac:(eapply in_concat_nth; [exact LI| rewrite ENTH; apply in_or_app; right; left; reflexivity])) as (ACCA & ALA & ALO).
    pose proof DVd as (DAL & DLO & DHI & _). unfold IMG_UT_LO, IMG_UT_HI in DLO, DHI. unfold IMG_UT_HI in UTLO. destruct (DVF d DVd) as ((e1 & DC) & DACC). assert (DLO8 : d + 8 <= lo) by lia.
    set (nxt := match rest with [] => 0 | (_, Bq) :: _ => Bq end).
    assert (NXm : rw_cells asegs m (A + 8) [C8 (Z_to_bv 64 nxt)]).
    { unfold nxt. destruct rest as [|[q Bq] rest']; cbn [lseg] in RSEG; [subst c'; exact TERM| unfold wz in RSEG; exact (proj1 RSEG)]. }
    assert (S1' : lseg asegs LH_CEIL (DVerr GOBJ) m (ownL L) (B + 8 * idx) (ns1 ++ [(pn, A)]) (A + 8)).
    { eapply lseg_app; [exact S1|]. cbn [lseg]. split; [exact CC|]. split; [exact OWN|]. split; [unfold LH_CEIL, USTACK_TOP; exact RG|]. split; [exists d, hN; auto| reflexivity]. }
    (* [comment removed for export] *)
    assert (NEXT : forall (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 : word) (mc2 : mem),
      rw_cells asegs mc2 (bv_unsigned sp + -96) [CB 8 (firstn 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk asegs mc2 lo (bv_unsigned sp + -96) -> rw_cells asegs mc2 hp [C8 h] ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc2 -> wmono asegs m mc2 -> mem_inv asegs mc2 ->
      evt asegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L B nn hp bks)
        (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z1 z2 z3 sp (Z_to_bv 64 data) z4 z5 z6 z7 z8 z9 z10 z11
                 h (Z_to_bv 64 (lh + 32)) (Z_to_bv 64 c) (Z_to_bv 64 (lh + 8)) (Z_to_bv 64 A) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 ((lh + 32) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 8) ≫ 3 + 2147450880)) s10 s11 z12 z13 z14 t6)
            F (Z_to_bv 64 0x200af4) fc None mc2 (seg_rom asegs))).
    { intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 mc2 FR2 ST2 HP2 MU2 WM2 MI2.
      assert (NX2 : rw_cells asegs mc2 (A + 8) [C8 (Z_to_bv 64 nxt)]).
      { eapply rw_cells_transport; [exact NXm| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
      do 4 zstep. zstep. th_if_lit. zstep.
      destruct rest as [|[q Bq] rest'].
      - (* [comment removed for export] *)
        zstep. if_cases K9; zify_cond K9. { exfalso. unfold nxt in K9. rewrite ?unsigned_lit in K9 by lia. lia. }
        eapply (EXIT idx (A + 8) (ns1 ++ [(pn, A)]) []); try eassumption.
        + rewrite <- app_assoc. exact ENTH.
        + exists (A + 8). split; [reflexivity|]. cbn [lseg] in RSEG. subst c'. exact TERM.
      - pose proof RSEG as (_ & _ & RGq & _). unfold LH_CEIL, USTACK_TOP in RGq. cbn [lseg] in RSEG.
        zstep. if_cases K9; zify_cond K9. 2:{ exfalso. unfold nxt in K9. rewrite ?unsigned_lit in K9 by lia. lia. }
        eapply (CONT q Bq rest'); try eassumption; [reflexivity|]. exists c'. split; [exact RSEG| exact TERM]. }
    assert (N1c : rw_cells asegs mc A [C8 (Z_to_bv 64 d)]).
    { eapply rw_cells_transport; [exact N1| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    assert (N2c : rw_cells asegs mc (A + 16) [C8 hN]).
    { eapply rw_cells_transport; [exact N2| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    assert (DCc : ro_cells asegs mc d [C8 e1]).
    { eapply ro_cells_transport; [exact DC| exact MUc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    destruct (SCAT mc MUc WMc) as (x40c & x48c & errc & padc & SCc).
    (* [comment removed for export] *)
    do 4 zstep. zstep. th_if_lit. zstep. zstep. if_cases K5.
    { eapply NEXT; eassumption. }
    (* [comment removed for export] *)
    zstep. zstep. th_if_lit. zstep. zstep. th_if_lit.
    do 3 zstep. zstep. th_if_lit. zstep. zstep. th_if_lit. do 3 zstep. zstep.
    call err_comp_thunk_proof; [reflexivity
      | rewrite unsigned_lit by lia; exact DCc| rewrite unsigned_lit by lia; exact (acc_munch_sh _ m _ _ _ DACC MUc HWS ltac:(lia) ltac:(lia))
      | rewrite unsigned_lit by lia; exact DAL| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact DLO8
      | rewrite unsigned_lit by lia; exact (KEYAT mc MUc)| rewrite unsigned_lit by lia; exact (acc_munch_sh _ m _ _ _ KA MUc HWS ltac:(lia) ltac:(lia))
      | rewrite unsigned_lit by lia; exact KAL| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact KLO
      | exact (ut_munch _ m _ UT MUc HWU)| exact (SHCAT mc MUc)| rewrite EU1; exact STc| lia| rewrite EU1; lia| rewrite EU1; lia| assumption|].
    rewrite EU1 in POST.
    zstep. if_cases K7.
    - (* [comment removed for export] *) eapply (EXIT idx c ns1 ((pn, A) :: rest)); eassumption.
    - zstep. eapply NEXT; eassumption. }
  (* [comment removed for export] *)
  assert (LOOP : forall (rest : list (bptr * Z)) (idx : Z) (ns1 : list (bptr * Z)) (c : Z) (pn : bptr) (A : Z)
      (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (mc : mem),
    0 <= idx < nn -> nth (Z.to_nat idx) bks [] = ns1 ++ (pn, A) :: rest ->
    lseg asegs LH_CEIL (DVerr GOBJ) m (ownL L) (B + 8 * idx) ns1 c -> chain asegs LH_CEIL (DVerr GOBJ) m (ownL L) c ((pn, A) :: rest) ->
    rw_cells asegs mc (bv_unsigned sp + -96) [CB 8 (firstn 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -96) -> rw_cells asegs mc hp [C8 h] ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evt asegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L B nn hp bks)
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y1 y2 y3 sp (Z_to_bv 64 data) y4 y5 y6 y7 y8 y9 y10 y11
               h (Z_to_bv 64 (lh + 32)) (Z_to_bv 64 c) (Z_to_bv 64 (lh + 8)) (Z_to_bv 64 A) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 ((lh + 32) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 8) ≫ 3 + 2147450880)) s10 s11 y12 y13 y14 t6)
          F (Z_to_bv 64 0x200a6c) fc None mc (seg_rom asegs))).
  { induction rest as [|[q Bq] rest' IH]; intros idx ns1 c pn A y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 mc IDXR ENTH S1 C2 FRc STc HPc MUc WMc MIc.
    - eapply (BODY idx ns1 [] c pn A); try eassumption. intros q Bq rest' z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 mc' E. discriminate E.
    - eapply (BODY idx ns1 ((q, Bq) :: rest') c pn A); try eassumption.
      intros q0 Bq0 rest0 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 mc' E S1' C2' FR' ST' HP' MU' WM' MI'. inversion E; subst q0 Bq0 rest0.
      eapply (IH idx (ns1 ++ [(pn, A)]) (A + 8) q Bq); try eassumption. rewrite <- app_assoc. exact ENTH. }
  (* [comment removed for export] *)
  assert (IDX : forall (idx : Z) (y0 y1 y2 y3 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 : word) (mc : mem),
    0 <= idx < nn ->
    rw_cells asegs mc (bv_unsigned sp + -96) [CB 8 (firstn 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -96) -> rw_cells asegs mc hp [C8 h] ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evt asegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m GOBJ L B nn hp bks)
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y1 y2 y3 sp (Z_to_bv 64 data) (Z_to_bv 64 idx) y5 y6 y7 y8 y9 y10 y11
               h (Z_to_bv 64 lh) (Z_to_bv 64 hp) y12 y13 (Z_to_bv 64 2147450880) y14 y15 s10 s11 y16 y17 y18 t6)
          F (Z_to_bv 64 0x200a1c) fc None mc (seg_rom asegs))).
  { intros idx y0 y1 y2 y3 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 mc IDXR FRc STc HPc MUc WMc MIc.
    destruct (SCAT mc MUc WMc) as (x40c & x48c & errc & padc & SCc).
    pose proof (CH idx ltac:(lia)) as CHI.
    destruct (nth (Z.to_nat idx) bks []) as [|[pn A] rest] eqn:ENTH.
    - (* [comment removed for export] *)
      pose proof CHI as (c' & E & TERM). cbn [lseg] in E. subst c'. unfold wz in TERM.
      assert (TC : rw_cells asegs mc (B + 8 * idx) [C8 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact TERM| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
      remember (B + 8 * idx) as cb eqn:ECB.
      assert (EA : Z.land (bv_swrap 32 (idx + 0)) 18446744073709551615 ≪ 3 = 8 * idx).
      { rewrite Z.add_0_r, SWR by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
        rewrite Z.shiftl_mul_pow2 by lia. lia. }
      do 3 zstep. zstep. th_if_lit. do 4 zstep. rewrite EA.
      rewrite <- ECB.
      do 3 zstep. zstep. th_if_lit. zstep.
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
      subst cb.
      eapply (EXIT idx (B + 8 * idx) [] []); try eassumption; reflexivity.
    - pose proof CHI as (c' & (CC & OWN & RG & NC & RSEG) & TERM). unfold LH_CEIL, USTACK_TOP in RG. unfold wz in CC.
      assert (TC : rw_cells asegs mc (B + 8 * idx) [C8 (Z_to_bv 64 A)]).
      { eapply rw_cells_transport; [exact CC| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
      remember (B + 8 * idx) as cb eqn:ECB.
      assert (EA : Z.land (bv_swrap 32 (idx + 0)) 18446744073709551615 ≪ 3 = 8 * idx).
      { rewrite Z.add_0_r, SWR by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
        rewrite Z.shiftl_mul_pow2 by lia. lia. }
      do 3 zstep. zstep. th_if_lit. do 4 zstep. rewrite EA.
      rewrite <- ECB.
      do 3 zstep. zstep. th_if_lit. zstep.
      zstep. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
      do 6 zstep. subst cb.
      eapply (LOOP rest idx [] (B + 8 * idx) pn A); try eassumption. reflexivity. }
  (* [comment removed for export] *)
  zstep. if_cases K1; zify_cond K1.
  - eapply (IDX (bv_unsigned h mod pmax)); try eassumption. pose proof (Z.mod_pos_bound (bv_unsigned h) pmax ltac:(lia)). lia.
  - do 3 zstep. zstep. zstep. th_if_lit. zstep.
    rewrite (zx32_small na) by lia.
    zstep. rewrite m_remu by (rewrite unsigned_lit by lia; lia). rewrite (unsigned_lit na) by lia.
    eapply (IDX (bv_unsigned h mod na)); try eassumption.
    rewrite ?unsigned_lit in K1 by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned h) na ltac:(lia)) as RB0.
    rewrite <- (Z.mod_mod_divide (bv_unsigned h) na pmax ltac:(exists 2; lia)) in K1.
    set (r := bv_unsigned h mod na) in *. clearbody r. clear - K1 RB0 G1 G2 G3 G4. subst na nn.
    assert (Q : r / pmax = 0 \/ r / pmax = 1) by (assert (0 <= r / pmax < 2) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]); lia).
    pose proof (Z.div_mod r pmax ltac:(lia)). destruct Q as [Q|Q]; rewrite Q in *; lia.
Qed.
