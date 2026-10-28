(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_prim_kit R_mmapfixed R_ensurefa R_ensurefa_B R_popfree R_popfree_T R_popfree_B R_getfrom R_getfrom_A.
Import ListNotations.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.

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

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).

Section GFAB1.
Variable PC : mem -> Prop.
Hypothesis HPS : poison_stmt PC.
Hypothesis HPF : PC_framed PC.

Definition gfa_B1_W (sp : word) (SB c R CH n muser msz sa sn T total : Z) : list (Z * Z) :=
  [(R, R + 8); (R + 16, R + 56); (R + 68, R + 69); (R + 72, R + 80); (fa SB c, fa SB c + 4 * total);
   (rb SB c + muser, rb SB c + muser + msz); (sa, sa + sn); (T + 2792, T + 2800); (T + 2872, T + 2888);
   (CH, CH + 4 * n); (bv_unsigned sp - 592, bv_unsigned sp)]%Z.

Definition gfa_B1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R CH n nfree mfa auser muser msz sa sn T TCX : Z) (mm0 md0 : word) (ws chs : list word) (rand : word)
    (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (gfa_B1_W sp SB c R CH n muser msz sa sn T (nfree + pfa_newc auser muser msz (ClassSize c))) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ ri_lock m' R 0
    /\ ri_core m' R (nfree + pfa_newc auser muser msz (ClassSize c) - n) mfa
         (auser + pfa_newc auser muser msz (ClassSize c) * ClassSize c) (muser + msz)
    /\ ri_tail m' R rand (Z_to_bv 8 0) pad (nalloc + n) nfreed r0 r1 r2 r3
    /\ fl_arr m' SB c (carve ws (nfree + pfa_newc auser muser msz (ClassSize c)) auser (ClassSize c)
                         (Z.to_nat (pfa_newc auser muser msz (ClassSize c))))
    /\ u32arr bsegs m' CH (dest (carve ws (nfree + pfa_newc auser muser msz (ClassSize c)) auser (ClassSize c)
                                      (Z.to_nat (pfa_newc auser muser msz (ClassSize c)))) chs
                               (nfree + pfa_newc auser muser msz (ClassSize c) - n) (Z.to_nat n))
    /\ rw_cells bsegs m' (rb SB c + muser) [CB (Z.to_nat msz) (repeat (Z_to_bv 8 0) (Z.to_nat msz))]
    /\ rw_cells bsegs m' sa [CB (Z.to_nat sn) (repeat (Z_to_bv 8 250) (Z.to_nat sn))]
    /\ rw_cells bsegs m' (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm0 + 1)); C8 (Z_to_bv 64 (bv_unsigned md0 + msz))]
    /\ (exists w, rw_cells bsegs m' (T + 2792) [C8 w])
    /\ mm_gcells m' /\ thread_cells TCX T m' /\ PC m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma gfa_B1_spec : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R CH n nfree mfa auser muser msz sa sn T TCX : Z)
    (mm0 md0 w0 : word) (shj : list byte) (ws chs : list word) (rand : word) (exh : byte) (pad : list byte)
    (nalloc nfreed r0 r1 r2 r3 lo : Z) (junk : list byte),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (1 <= n <= 16)%Z -> (0 <= nfree < n)%Z ->
  (0 <= auser <= muser)%Z -> (muser < auser + (n - nfree) * ClassSize c)%Z -> (muser mod 2^18 = 0)%Z ->
  msz = umap_size auser muser (n - nfree) (ClassSize c) -> (muser + msz <= 0xE0000000)%Z ->
  (0 <= mfa <= 2^29)%Z -> (4 * Z.of_nat (length ws) = mfa)%Z ->
  (4 * (nfree + pfa_newc auser muser msz (ClassSize c)) <= mfa)%Z ->
  sa = shad (rb SB c + muser) -> sn = (msz / 8)%Z ->
  tsep ACEIL SB T TCX ->
  (T + 208 <= CH /\ CH + 64 <= T + 2768)%Z -> length chs = 16%nat -> length pad = 3%nat -> (0 <= nalloc < 2^64)%Z ->
  pfa_cells1 m (Z_to_bv 64 (bv_unsigned sp - 128)) (Z_to_bv 64 gfa_retP) (Z_to_bv 64 R) (Z_to_bv 64 INST)
    (Z_to_bv 64 (R + 8)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 CH) (Z_to_bv 64 n)
    R (cstats T) (rb SB c) muser msz lo ->
  rw_cells bsegs m (bv_unsigned sp - 128)
    [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ri_lock m R 1152921504606846976 ->
  ri_core m R nfree mfa auser muser ->
  ri_tail m R rand exh pad nalloc nfreed r0 r1 r2 r3 ->
  fl_arr m SB c ws -> u32arr bsegs m CH chs ->
  thread_cells TCX T m ->
  rw_cells bsegs m (T + 2792) [C8 w0] ->
  rw_cells bsegs m (T + 2872) [C8 mm0; C8 md0] ->
  rw_cells bsegs m sa [CB (Z.to_nat sn) shj] ->
  PC m ->
  (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 592)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (gfa_B1_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB c R CH n nfree mfa auser
               muser msz sa sn T TCX mm0 md0 ws chs rand pad nalloc nfreed r0 r1 r2 r3 lo m)
    (nret (MSsvc (mfi_regs (Z_to_bv 64 pfa_retB1) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) - 64)) gp
                           (Z_to_bv 64 tpA) t0 t1 t2 a6 (rb SB c + muser) msz (Z_to_bv 64 str_regiondata)
                           (Z_to_bv 64 (ClassSize c)) (Z_to_bv 64 INST) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500)
                           (Z_to_bv 64 16140901064495857663) s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m (seg_rom bsegs))
          (mkEffect (Z_to_bv 64 (rb SB c + muser)) [] [(Z_to_bv 64 (rb SB c + muser), Z_to_bv 64 msz)])).
Proof.
  intros until junk. intros HSB Hc ER Hn Hnf Hau Htot Hmual Emsz Hcap Hmfa Hws Hroom Esa Esn HTS HCHT Hchs Hpad Hna
    AC FRG LK RC RT FL CHS TC SAM ST8 SH PCm HLO HLOH HLO2 HSP MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  pose proof HTS as (HT & HTCX0 & HTCX1 & HTCXI & SEPT & SEPTCX & SEPTT & OUTT & OUTTCX).
  pose proof HT as (HT1 & HT2 & HT3 & HT4 & HT5).
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
    unfold kHighShadowEnd in HLOH. lia. }
  destruct (ri_tail_split _ _ _ _ _ _ _ _ _ _ _ RT Hpad) as (RT1 & RT2 & RT3). clear RT.
  unfold ri_lock, fl_arr in *.

  eapply evt_cut; [eapply (pfa_mid_spec PC HPS HPF) with (k := (n - nfree)%Z) (nfree := nfree) (mfa := mfa) (ACEIL := ACEIL)
                     (lo := lo) (SB := SB) (auser := auser) (muser := muser) (T := T) (TCX := TCX) (w0 := w0)
                     (mm0 := mm0) (md0 := md0) (shj := shj) (R := R) (sa := sa) (sn := sn) (ra := Z_to_bv 64 gfa_retP)
                     (s0o := Z_to_bv 64 R) (s1o := Z_to_bv 64 INST) (s2o := Z_to_bv 64 (R + 8))
                     (s3o := Z_to_bv 64 2305843009213693952) (s4o := Z_to_bv 64 (fa SB c)) (s5o := Z_to_bv 64 CH)
                     (s6o := Z_to_bv 64 n) | ].
  all: first [ assumption | (arith_goal; try rewrite Esp; unfold kHighShadowEnd in *; lia) | idtac ].
  intros ms1 PO. unfold pfa_mid_post in PO. destruct_exs PO.
  destruct PO as (E & MU1 & WM1 & MI1 & FRP & ZU & SHN & RC1 & ST81 & SAM1 & GC1 & TC1 & PC1 & ST1). subst ms1.
  unfold pfa_W1 in MU1. rewrite Esp in MU1.
  unfold kHighShadowEnd, rinfo, RIS_of, cstats in *.
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  assert (UM : (SB + 2^32 <= rb SB c + muser /\ rb SB c + muser + msz <= fa SB c)%Z) by (unfold fa, rb; lia).
  pose proof (round_fa_ge (auser + (n - nfree) * ClassSize c - muser) ltac:(lia)) as RG.
  unfold umap_size in Emsz. rewrite <- Emsz in RG.
  assert (Hsh : (0x7fff8000 <= sa /\ sa + sn <= 0x10007fff8000 /\ 0 < sn)%Z).
  { subst sa sn. assert (Hn8 : ((rb SB c + muser) mod 8 = 0 /\ msz mod 8 = 0)%Z).
    { pose proof (round_fa_aligned (auser + (n - nfree) * ClassSize c - muser)) as RA. rewrite <- Emsz in RA.
      unfold rb. split; Z.div_mod_to_equations; lia. }
    destruct (shad_range (rb SB c + muser) msz ltac:(lia) ltac:(lia) (proj1 Hn8) (proj2 Hn8) ltac:(lia)) as (SH1 & SH2 & SH3).
    unfold kHighShadowEnd in SH2. lia. }
  assert (Hmsz0 : (0 < msz)%Z) by lia.
  apply box in SEPTCX, SEPTT, OUTTCX, HT5, HTCXI, HT2, HSB2, Hmual, Emsz, Htot.
  tr_from0 m MU1 WM1 FRG. tr_from0 m MU1 WM1 LK. tr_from0 m MU1 WM1 RT1. tr_from0 m MU1 WM1 RT2. tr_from0 m MU1 WM1 RT3.
  tr_from0a m MU1 WM1 FL. tr_from0a m MU1 WM1 CHS.
  apply box in Esa, Esn, ZU, SHN, ST81, SAM1, GC1, TC1, PC1.
  clear AC SAM ST8 SH RC TC PCm.
  lazymatch type of MU1 with munch _ _ ?mc =>
    pose proof (munch_refl [(R, R + 8); (R + 16, R + 56); (R + 68, R + 69); (R + 72, R + 80);
                            (fa SB c, fa SB c + 4 * (nfree + pfa_newc auser muser msz (ClassSize c))); (CH, CH + 4 * n);
                            (bv_unsigned sp - 592, bv_unsigned sp)]%Z mc) as MU2;
    pose proof (wmono_refl bsegs mc) as WM2; rename mc into m1 end.
  unfold ri_core, pfa_frame in *.

  rewrite Esp. rewrite Esp in ST1, FRP.
  assert (Esp2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128 - 64)) = (bv_unsigned sp - 128 - 64)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  pose proof (ClassSize_range c Hc) as HCS.
  assert (Hnewc : (n - nfree <= pfa_newc auser muser msz (ClassSize c) <= 2^28)%Z).
  { unfold pfa_newc. split.
    - apply Z.div_le_lower_bound; [lia|]. pose proof (unbox _ Htot). lia.
    - apply Z.div_le_upper_bound; [lia|]. lia. }
  call (efs_fast_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ R
          (nfree + pfa_newc auser muser msz (ClassSize c)) nfree mfa auser (muser + msz) lo).
  all: first [ assumption | (arith_goal; rewrite ?Esp2; lia) | idtac ].
  1:{ rewrite Esp2. assumption. }
  unfold pfa_retE.
  replace (ret_pc (Z_to_bv 64 410312)) with (Z_to_bv 64 410312) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  rewrite Esp2 in POST.
  replace (Z_to_bv 64 (bv_unsigned sp - 128 - 64)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) - 64))
    by (rewrite Esp; reflexivity).
  rewrite <- Esp in FRP, POST.
  eapply evt_cut; [eapply (pfa_T_spec (Z_to_bv 64 gfa_retP) (Z_to_bv 64 (bv_unsigned sp - 128)) gp (Z_to_bv 64 tpA)
     (Z_to_bv 64 R) (Z_to_bv 64 INST) (Z_to_bv 64 (R + 8)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c))
     (Z_to_bv 64 CH) (Z_to_bv 64 n) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500) (Z_to_bv 64 16140901064495857663)
     s10 s11 F fc ACEIL SB c R nfree mfa auser (muser + msz) (pfa_newc auser muser msz (ClassSize c)) lo ws) | ].
  all: first [ assumption | (arith_goal; rewrite ?Esp; lia) | idtac ].
  1:{ unfold pfa_newc. reflexivity. }
  1:{ exact RT2. }
  intros ms2 PO2. unfold pfa_Q, pfa_tail_post in PO2. destruct_exs PO2.
  destruct PO2 as (E2 & MU3 & WM3 & MI3 & FL3 & RC3 & EXH3 & ST3). subst ms2.
  unfold pfa_tail_W in MU3. rewrite Esp in MU3.
  lazymatch type of MU3 with munch _ ?mb ?mc =>
    tr_from0 mb MU3 WM3 FRG; tr_from0 mb MU3 WM3 LK; tr_from0 mb MU3 WM3 RT1; tr_from0 mb MU3 WM3 RT3;
    tr_from0a mb MU3 WM3 CHS end.
  unfold gfa_retP.
  replace (ret_pc (Z_to_bv 64 409832)) with (Z_to_bv 64 409832) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  unfold ri_core in RC3. unfold fl_arr in FL3. rewrite Esp in ST3.
  pose proof (carve_length ws (nfree + pfa_newc auser muser msz (ClassSize c)) auser (ClassSize c)
                (Z.to_nat (pfa_newc auser muser msz (ClassSize c)))) as CL3.
  zhide.
  zstep. ifF.
  zstep. zstep. zstep. ifF.
  do 5 zstep.
  pose proof (ri_tail_join _ _ _ _ _ _ _ _ _ _ _ RT1 EXH3 RT3) as RT.
  eapply evt_mono; [eapply (gfa_tail_spec ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ACEIL SB c R CH n
     (nfree + pfa_newc auser muser msz (ClassSize c) - n) lo
     (carve ws (nfree + pfa_newc auser muser msz (ClassSize c)) auser (ClassSize c) (Z.to_nat (pfa_newc auser muser msz (ClassSize c))))
     chs rand (Z_to_bv 8 0) pad nalloc nfreed r0 r1 r2 r3) | ].
  all: first [ assumption | (arith_goal; lia) | (eexists; eassumption) | idtac ].
  intros ms3 PO3. unfold gfa_Q, gfa_ret_post in PO3. destruct_exs PO3.
  destruct PO3 as (E3 & MU4 & WM4 & MI4 & LK4 & RT4 & CHS4 & ST4). subst ms3.
  unfold gfa_tail_W in MU4.
  tr_from0 m0 MU4 WM4 RC3. tr_from0a m0 MU4 WM4 FL3.

  assert (MU2f : munch [(R, R + 8); (R + 16, R + 56); (R + 68, R + 69); (R + 72, R + 80);
                        (fa SB c, fa SB c + 4 * (nfree + pfa_newc auser muser msz (ClassSize c))); (CH, CH + 4 * n);
                        (bv_unsigned sp - 592, bv_unsigned sp)]%Z m1 x53).
  { eapply munch_trans; [eapply munch_trans; [exact MU2|]|].
    - eapply munch_weaken; [|exact MU3]. unfold sub_fp; cbn [outside]; intros; lia.
    - eapply munch_weaken; [|exact MU4]. unfold sub_fp; cbn [outside]; intros; lia. }
  assert (WM2f : wmono bsegs m1 x53) by (eapply wmono_trans; [eapply wmono_trans; [exact WM2| exact WM3]| exact WM4]).
  apply unbox in ZU, SHN, ST81, SAM1, GC1, TC1, PC1.
  destruct SAM1 as (w1 & SAM1). destruct GC1 as (G1 & G2 & G3 & G4 & G5). destruct TC1 as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  apply box in SEPT, OUTT.
  pose proof (unbox _ SEPT) as SEPT'.
  tr_from0 m1 MU2f WM2f ZU. tr_from0 m1 MU2f WM2f ST81. tr_from0 m1 MU2f WM2f SAM1.
  clear SEPT'. pose proof (unbox _ OUTT) as OUTT'.
  tr_from0 m1 MU2f WM2f SHN.
  clear OUTT'. pose proof (unbox _ HT5) as HT5'. unfold img_hull_lo, img_hull_hi in HT5'.
  tr_from0 m1 MU2f WM2f G1. tr_from0 m1 MU2f WM2f G2. tr_from0 m1 MU2f WM2f G3. tr_from0 m1 MU2f WM2f G4. tr_from0 m1 MU2f WM2f G5.
  tr_from0 m1 MU2f WM2f KI. tr_from0 m1 MU2f WM2f K. tr_from0 m1 MU2f WM2f TS. tr_from0 m1 MU2f WM2f T0.
  assert (PCf : PC x53) by (apply (HPF m1 x53 _ PC1 MU2f WM2f); unfold img_hull_lo, img_hull_hi in *; cbn [disjoint_from]; lia).
  clear HT5'.
  pose proof (unbox _ SEPTCX) as SEPTCX'. pose proof (unbox _ SEPTT) as SEPTT'.
  tr_from0 m1 MU2f WM2f TT.
  clear SEPTCX' SEPTT'.
  unfold gfa_B1_post.
  do 15 eexists. split; [reflexivity|].
  split.
  { eapply munch_trans; [eapply munch_trans|];
      [eapply munch_weaken; [|exact MU1] | eapply munch_weaken; [|exact MU3] | eapply munch_weaken; [|exact MU4]];
      unfold sub_fp, gfa_B1_W; cbn [outside]; intros; lia. }
  split; [eapply wmono_trans; [eapply wmono_trans; [exact WM1| exact WM3]| exact WM4]|].
  split; [assumption|]. split; [assumption|]. split; [exact RC3|]. split; [assumption|]. split; [exact FL3|].
  split; [assumption|]. split; [exact ZU|]. split; [exact SHN|]. split; [exact ST81|]. split; [eexists; exact SAM1|].
  split; [unfold mm_gcells; repeat (split; [assumption|]); assumption|].
  split; [unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
          split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]|].
  split; [exact PCf| exact ST4].
Qed.
End GFAB1.
