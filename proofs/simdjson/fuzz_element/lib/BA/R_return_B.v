(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_classid R_prim_defs R_prim_kit R_mmapfixed R_ensurefa R_ensurefa_B R_popfree R_getfrom R_return R_return_T R_return_A.
Import ListNotations.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Open Scope bv_scope.
Notation mem := (word -> option byte).

Ltac tr_bx m0 MU WM H GE SE :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (rw_cells_transport asegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes;
      let G := fresh "G" in let S := fresh "S" in
      pose proof (unbox _ GE) as G; pose proof (unbox _ SE) as S; clear - G S; repeat split; lia ]
  end.
Ltac tr_bxa m0 MU WM H X GE SE :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (u32arr_transport asegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes;
      let G := fresh "G" in let S := fresh "S" in
      pose proof (unbox _ GE) as G; pose proof (unbox _ SE) as S; clear - G S X; repeat split; lia ]
  end.
Ltac sub_bx GE := let G := fresh "G" in pose proof (unbox _ GE) as G; clear - G; solve_sub_fp2.

Section RTAB.
Variable PC : mem -> Prop.
Hypothesis HPS : poison_stmt PC.
Hypothesis HPF : PC_framed PC.

Definition rta_B_W (sp : word) (SB c R new esa esn T : Z) : list (Z * Z) :=
  [(R, R + 8); (R + 16, R + 32); (R + 80, R + 88); (fa SB c, fa SB c + new); (esa, esa + esn); (T + 2872, T + 2888);
   (bv_unsigned sp - 576, bv_unsigned sp)]%Z.

Definition rta_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R CH cb n nfree mfa new auser muser esa esn T TCX : Z) (mm0 md0 : word) (ws chs : list word) (rand : word)
    (exh : byte) (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (rta_B_W sp SB c R new esa esn T) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ ri_lock m' R 0
    /\ ri_core m' R (nfree + n) new auser muser
    /\ ri_tail m' R rand exh pad nalloc (nfreed + n) r0 r1 r2 r3
    /\ fl_arr m' SB c (dest2 (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4))) chs nfree cb (Z.to_nat n))
    /\ rw_cells asegs m' esa [CB (Z.to_nat esn) (repeat (Z_to_bv 8 250) (Z.to_nat esn))]
    /\ rw_cells asegs m' (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm0 + 1)); C8 (Z_to_bv 64 (bv_unsigned md0 + (new - mfa)))]
    /\ mm_gcells m' /\ thread_cells TCX T m' /\ PC m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma rta_B_spec : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R mapper CH cb n nfree mfa new auser muser esa esn T TCX : Z)
    (mm0 md0 : word) (shj : list byte) (ws chs : list word) (rand : word) (exh : byte) (pad : list byte)
    (nalloc nfreed r0 r1 r2 r3 lo : Z) (junk : list byte),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (1 <= n <= 16)%Z -> (0 <= cb /\ cb + n <= 16)%Z -> (0 <= nfree < 2^32)%Z ->
  (0 <= mfa <= 2^29)%Z -> (mfa mod 2^18 = 0)%Z -> (4 * Z.of_nat (length ws) = mfa)%Z -> (mfa < 4 * (nfree + n))%Z ->
  new = round_fa (4 * (nfree + n)) -> (new <= 2^29)%Z ->
  esa = shad (fa SB c + mfa) -> esn = ((new - mfa) / 8)%Z ->
  tsep ACEIL SB T TCX ->
  (T + 208 <= CH /\ CH + 64 <= T + 2768)%Z -> length chs = 16%nat ->
  (0 <= nfreed < 2^64 /\ 0 <= r0 < 2^64 /\ 0 <= auser < 2^64 /\ 0 <= muser < 2^64)%Z ->
  efs_A_cells m (Z_to_bv 64 (bv_unsigned sp - 128)) (Z_to_bv 64 rta_retE) (Z_to_bv 64 R) (Z_to_bv 64 nfree)
    (Z_to_bv 64 c) (Z_to_bv 64 mapper) (Z_to_bv 64 INST) R (fa SB c + mfa) (new - mfa) new lo ->
  rw_cells asegs m (bv_unsigned sp - 128)
    [CB 16 junk; C8 (Z_to_bv 64 (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
     C8 s1; C8 s0; C8 ra] ->
  ri_lock m R 1152921504606846976 ->
  ri_core m R nfree mfa auser muser ->
  ri_tail m R rand exh pad nalloc nfreed r0 r1 r2 r3 ->
  fl_arr m SB c ws -> u32arr asegs m CH chs -> inst_cells SB m ->
  thread_cells TCX T m ->
  rw_cells asegs m (T + 2872) [C8 mm0; C8 md0] ->
  rw_cells asegs m esa [CB (Z.to_nat esn) shj] ->
  PC m ->
  (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 576)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (rta_B_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB c R CH cb n nfree mfa new
               auser muser esa esn T TCX mm0 md0 ws chs rand exh pad nalloc nfreed r0 r1 r2 r3 lo m)
    (nret (MSsvc (mfi_regs (Z_to_bv 64 efs_retB) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) - 48)) gp
                           (Z_to_bv 64 tpA) t0 t1 t2 a6 (fa SB c + mfa) (new - mfa) (Z_to_bv 64 str_freearray)
                           (Z_to_bv 64 n) (Z_to_bv 64 (CH + 4 * cb)) (Z_to_bv 64 (nfree + n))
                           (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 1152921504607895551)
                           (Z_to_bv 64 1152921504606846976) t3 t4 t5 t6) F
                 (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m (seg_rom asegs))
          (mkEffect (Z_to_bv 64 (fa SB c + mfa)) [] [(Z_to_bv 64 (fa SB c + mfa), Z_to_bv 64 (new - mfa))])).
Proof.
  intros until junk. intros HSB Hc ER Hn Hcb Hnf Hmfa Hmfal Hws Hgrow Enew Hnew Esa Esn HTS HCHT Hchs Hrng
    AC FRG LK RC RT FL CHS IC TC ST8 SHF PCm HLO HLOH HLO2 HSP MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  pose proof HTS as (HT & HTCX0 & HTCX1 & HTCXI & SEPT & SEPTCX & SEPTT & OUTT & OUTTCX).
  pose proof HT as (HT1 & HT2 & HT3 & HT4 & HT5).
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
    unfold kHighShadowEnd in HLOH. lia. }
  pose proof (round_fa_ge (4 * (nfree + n)) ltac:(lia)) as RGN.
  pose proof (round_fa_aligned (4 * (nfree + n))) as RAN.
  rewrite <- Enew in RGN, RAN.

  apply box in FRG, LK, RT, CHS, IC.
  apply box in SEPT, SEPTCX, SEPTT, OUTT, OUTTCX, HT5, HTCXI, HT2, HSB2.

  eapply evt_cut; [eapply (efs_B_spec PC HPS HPF) with (ACEIL := ACEIL) (SB := SB) (c := c) (R := R) (mfa := mfa) (new := new)
                     (T := T) (TCX := TCX) (nfree := nfree) (auser := auser) (muser := muser)
                     (mm0 := mm0) (md0 := md0) (shj := shj)
                     (lo := lo) (esa := esa) (esn := esn) (ra := Z_to_bv 64 rta_retE) (s0 := Z_to_bv 64 R)
                     (s1 := Z_to_bv 64 nfree) (s2 := Z_to_bv 64 c) (s3 := Z_to_bv 64 mapper) (s4 := Z_to_bv 64 INST) | ].
  all: first [ assumption | lia | (rewrite Esp; lia) | idtac ].
  intros ms1 PO. unfold efs_B_post in PO. destruct_exs PO.
  destruct PO as (E1 & MU1 & WM1 & MI1 & ZNEW & SHN2 & RC2 & ST82 & GC2 & TC2 & PC2 & ST1). subst ms1.
  unfold efs_WB in MU1. rewrite Esp in MU1.
  unfold kHighShadowEnd, rinfo, RIS_of, ri_lock, fl_arr, ri_core in *.
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  assert (Hsh : (0x7fff8000 <= esa /\ esa + esn <= 0x10007fff8000 /\ 0 < esn)%Z).
  { pose proof (unbox _ HSB2) as HSB2'. subst esa esn. unfold shad, SHB, fa, rb in *. Z.div_mod_to_equations; lia. }
  assert (GEO : R = (SB + 2^37 + 128 * c)%Z /\ (1 <= c <= 31)%Z /\ (17594333495295 < SB)%Z /\ (SB + 2^37 + 4096 <= ACEIL)%Z
     /\ (ACEIL <= lo)%Z /\ (17594333495303 <= lo)%Z /\ (lo <= bv_unsigned sp - 576)%Z /\ (bv_unsigned sp <= 2^47)%Z
     /\ (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z
     /\ (0x7fff8000 <= esa /\ esa + esn <= 0x10007fff8000 /\ 0 < esn)%Z
     /\ (4 * (nfree + n) <= new <= 2^29)%Z /\ (0 <= mfa < new)%Z
     /\ (4 * Z.of_nat (length ws) = mfa)%Z /\ (1 <= n <= 16)%Z /\ (0 <= nfree < 2^32)%Z
     /\ (T + 208 <= CH /\ CH + 64 <= T + 2768)%Z /\ (0 < T)%Z /\ (T + 4096 <= ACEIL)%Z /\ (0 < TCX)%Z /\ (TCX + 160 <= ACEIL)%Z
     /\ bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { repeat split; first [assumption | lia]. }
  assert (SEP : (T + 4096 <= SB \/ SB + 2^37 + 4096 <= T)%Z /\ (T + 4096 <= 2147450880 \/ 17594333495295 < T)%Z
     /\ (T + 4096 <= 65536 \/ 7118848 <= T)%Z /\ (TCX + 160 <= SB \/ SB + 2^37 + 4096 <= TCX)%Z
     /\ (TCX + 160 <= T \/ T + 4096 <= TCX)%Z).
  { pose proof (unbox _ SEPT) as X1. pose proof (unbox _ OUTT) as X2. pose proof (unbox _ HT5) as X3. pose proof (unbox _ SEPTCX) as X4.
    pose proof (unbox _ SEPTT) as X5. unfold img_hull_lo, img_hull_hi in X1, X2, X3, X4, X5 |- *. clear - X1 X2 X3 X4 X5. tauto. }
  apply box in GEO, SEP.
  apply box in Esa, Esn, Hmfal, Enew, RAN.

  apply unbox in FL.
  tr_bxa m MU1 WM1 FL Hws GEO SEP.
  lazymatch type of MU1 with munch _ _ ?mc => rename mc into m1 end.
  assert (Ek : Z.to_nat (new - mfa) = (4 * Z.to_nat ((new - mfa) / 4))%nat).
  { pose proof (unbox _ RAN). pose proof (unbox _ Hmfal). Z.div_mod_to_equations. lia. }
  rewrite Ek in ZNEW.
  replace (fa SB c + mfa)%Z with (fa SB c + 4 * Z.of_nat (length ws))%Z in ZNEW by lia.
  pose proof (u32arr_app_zeros m1 (fa SB c) ws (Z.to_nat ((new - mfa) / 4)) FL ZNEW) as FL2. clear FL ZNEW.
  assert (Hws2 : (4 * Z.of_nat (length (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4)))) = new)%Z).
  { rewrite app_length, repeat_length. pose proof (unbox _ RAN). pose proof (unbox _ Hmfal). Z.div_mod_to_equations. lia. }

  apply unbox in FRG, LK, RT, CHS, IC.
  destruct IC as (IC1 & IC2). unfold i_spacebeg, i_premapped, INST, g_instance in IC1, IC2.
  change (1508824 + 32)%Z with 1508856%Z in IC1. change (1508824 + 56)%Z with 1508880%Z in IC2.
  tr_bx m MU1 WM1 FRG GEO SEP. tr_bx m MU1 WM1 LK GEO SEP. tr_bx m MU1 WM1 RT GEO SEP. tr_bxa m MU1 WM1 CHS Hchs GEO SEP.
  tr_bx m MU1 WM1 IC1 GEO SEP. tr_bx m MU1 WM1 IC2 GEO SEP.
  unfold rta_retE.
  replace (ret_pc (Z_to_bv 64 386072)) with (Z_to_bv 64 386072) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  rewrite Esp in ST1.
  eapply evt_mono; [eapply (rta_tail_spec ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ACEIL SB c R CH cb n
     nfree new auser muser mapper lo (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4))) chs rand exh pad
     nalloc nfreed r0 r1 r2 r3 m1) | ].
  all: first [ assumption | lia | (eexists; eassumption)
             | (unfold inst_cells, i_spacebeg, i_premapped, INST, g_instance; split; assumption)
             | (let G := fresh "G" in let S := fresh "S" in
                pose proof (unbox _ GEO) as G; pose proof (unbox _ SEP) as S; clear - G S Hws2; lia) | idtac ].
  intros ms3 PO3. unfold rta_Q, rta_ret_post in PO3. destruct_exs PO3.
  destruct PO3 as (E3 & MU4 & WM4 & MI4 & LK4 & RC4 & RT4 & FL4 & ST4). subst ms3.
  unfold rta_tail_W in MU4.
  lazymatch type of MU4 with munch _ ?mb ?mc => rename mc into m4 end.

  assert (MUf : munch (rta_B_W sp SB c R new esa esn T) m m4).
  { unfold rta_B_W. eapply munch_trans; [eapply munch_weaken; [|exact MU1]| eapply munch_weaken; [|exact MU4]]; sub_bx GEO. }
  assert (WMf : wmono asegs m m4) by (eapply wmono_trans; [exact WM1| exact WM4]).
  destruct GC2 as (G1 & G2 & G3 & G4 & G5). destruct TC2 as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  tr_bx m1 MU4 WM4 SHN2 GEO SEP. tr_bx m1 MU4 WM4 ST82 GEO SEP.
  tr_bx m1 MU4 WM4 G1 GEO SEP. tr_bx m1 MU4 WM4 G2 GEO SEP. tr_bx m1 MU4 WM4 G3 GEO SEP. tr_bx m1 MU4 WM4 G4 GEO SEP.
  tr_bx m1 MU4 WM4 G5 GEO SEP. tr_bx m1 MU4 WM4 KI GEO SEP. tr_bx m1 MU4 WM4 K GEO SEP. tr_bx m1 MU4 WM4 TS GEO SEP.
  tr_bx m1 MU4 WM4 T0 GEO SEP.
  assert (PCf : PC m4) by (apply (HPF m1 m4 _ PC2 MU4 WM4); cbn [disjoint_from];
    let G := fresh "G" in let S := fresh "S" in
    pose proof (unbox _ GEO) as G; pose proof (unbox _ SEP) as S; unfold img_hull_lo, img_hull_hi; clear - G S; lia).
  tr_bx m1 MU4 WM4 TT GEO SEP.
  unfold rta_B_post.
  do 16 eexists. split; [reflexivity|].
  split; [exact MUf|]. split; [exact WMf|].
  split; [assumption|]. split; [assumption|]. split; [exact RC4|]. split; [assumption|]. split; [exact FL4|].
  split; [exact SHN2|]. split; [exact ST82|].
  split; [unfold mm_gcells; repeat (split; [assumption|]); assumption|].
  split; [unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
          split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]|].
  split; [exact PCf| exact ST4].
Qed.
End RTAB.
