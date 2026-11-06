From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLib CtrlParsed disco_classify_c SightModel SightLib bcmp_c check_sighting_c.
Import ListNotations.
Open Scope Z_scope.

Lemma cs_memcmp : forall n (l r : list byte) v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  -256 < v < 256 /\ (v = 0 <-> map bv_unsigned l = map bv_unsigned r).
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] v Hl Hr H; cbn [length memcmp_model map] in *; try discriminate.
  - injection H as <-. split; [lia| tauto].
  - injection Hl as Hl. injection Hr as Hr.
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    change (bv_modulus 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH l r v Hl Hr H) as [Hv Hi]. split; [exact Hv|]. rewrite Hi, E.
      split; [intros ->; reflexivity | intros Hc; injection Hc as Hc; exact Hc].
    + injection H as <-. split; [lia|]. split; [lia | intros Hc; injection Hc as Hc _; contradiction].
Qed.

Lemma cs_bv : forall m A (bs : list byte), bytes_at rsegs m A bs -> A < 2 ^ 64 ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 A)) bs.
Proof. intros m A bs H HA. pose proof (bytes_at_bound rsegs m A bs H). rewrite unsigned_lit by lia. exact H. Qed.

Local Ltac cs_call BCH H1 H2 HV :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BCH; [ apply cs_bv; [ exact H1 | lia ] | apply cs_bv; [ exact H2 | lia ] | exact HV | assumption ]
      | post_call segs mm ];
      repeat match goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end
  end.

Local Ltac cond_is b tac :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [ cbv iota | symmetry; tac ]
  end.

Local Ltac fc_norm len :=
  let Ux := fresh "Ux" in let Uq := fresh "Uq" in let U36 := fresh "U36" in
  assert (Ux : bv_unsigned (Z_to_bv 64 (len + -52)) = len - 52) by (apply unsigned_lit; lia);
  rewrite ?Ux; clear Ux;
  rewrite ?(kq_div (len - 52)) by lia;
  assert (Uq : bv_unsigned (Z_to_bv 64 ((len - 52) / 36)) = (len - 52) / 36)
    by (apply unsigned_lit; Z.div_mod_to_equations; lia);
  rewrite ?Uq; clear Uq;
  assert (U36 : bv_unsigned (Z_to_bv 64 ((len - 52) / 36 * 36)) = (len - 52) / 36 * 36)
    by (apply unsigned_lit; Z.div_mod_to_equations; lia);
  rewrite ?U36; clear U36;
  try replace (len - 52 - (len - 52) / 36 * 36) with ((len - 52) mod 36) by (rewrite Z.mod_eq by lia; lia).

Definition cs_hide (P : Prop) : Prop := P.

Definition cs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

Local Ltac cs_exit FR ST MU WM MI sp :=
  step; step; step; step; step; step; step; step;
  release_frame FR ST (bv_unsigned sp);
  apply evt_done; unfold cs_post; cbv beta;
  do 15 eexists; eexists; split; [ reflexivity | ];
  split; [ exact MU | ]; split; [ exact WM | ]; split; [ exact MI | ]; exact ST.

Lemma cs_loop : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bs : list byte),
  0 < p -> p + 50 <= 2 ^ 64 -> length bs = 32%nat -> bytes_at rsegs m (p + 18) bs ->
  (forall x4 : word, evt rsegs Q
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (psum bs 32)) (Z_to_bv 64 (p + 50)) (Z_to_bv 64 (p + 50)) x4
              a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x146ec) fc None m (seg_rom rsegs))) ->
  forall n i x4, (i + n = 32)%nat -> (0 < n)%nat ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (psum bs i)) (Z_to_bv 64 (p + 18 + Z.of_nat i))
             (Z_to_bv 64 (p + 50)) x4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x146dc) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bs
    Hp Hp50 Hlen HB K.
  induction n as [|n IH]; intros i x4 Hin Hn; [lia|].
  pose proof (rd_byte rsegs m (p + 18) bs i HB ltac:(lia)) as RD.
  step. step. step. step.
  assert (R1 : 0 < p + 18 + Z.of_nat i + 1 <= 2 ^ 64) by lia.
  assert (R2 : 0 < p + 50 <= 2 ^ 64) by lia.
  rewrite (eqb_le64 (p + 18 + Z.of_nat i + 1) (p + 50) R1 R2).
  rewrite psum_S_zxb.
  destruct n as [|n].
  - replace (p + 18 + Z.of_nat i + 1 =? p + 50) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb].
    replace i with 31%nat by lia.
    replace (p + 18 + Z.of_nat 31 + 1) with (p + 50) by lia.
    apply K.
  - replace (p + 18 + Z.of_nat i + 1 =? p + 50) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb].
    replace (p + 18 + Z.of_nat i + 1) with (p + 18 + Z.of_nat (S i)) by lia.
    apply (IH (S i)); lia.
Qed.

Lemma cs_fin : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo s f : Z) (Sb FB : list byte)
    (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' t3 t4 t5 t6 : word),
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo + 48 <= bv_unsigned sp ->
  munch [(bv_unsigned sp + -48, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m s Sb -> length Sb = 24%nat -> bytes_at rsegs m f FB -> length FB = 50%nat -> 0 < f ->
  (fb Sb 12 = 0 \/ (fb Sb 12 = 1 /\ fb Sb 13 <= 40 /\ fb Sb 14 <= 40)) ->
  (bv_unsigned a0 <> 0 \/ fsum FB = 0) ->
  evt rsegs (cs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 f)
             a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x146d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m lo s f Sb FB
    ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' t3 t4 t5 t6 FR ST LO MU WM MI HS HSl HF HFl Hf0 Hdecl Hfl.
  change (cs_hide (bv_unsigned a0 <> 0 \/ fsum FB = 0)) in Hfl.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (bytes_at_bound rsegs m s Sb HS) as Bs. rewrite HSl in Bs.
  pose proof (bytes_at_bound rsegs m f FB HF) as Bf. rewrite HFl in Bf.
  pose proof (bytes_at_fld rsegs m f FB 18 32 HF ltac:(lia)) as HB. change (Z.of_nat 18) with 18 in HB.
  pose proof (rd_byte rsegs m s Sb 12 HS ltac:(lia)) as RD12. change (Z.of_nat 12) with 12 in RD12.
  pose proof (rd_byte rsegs m s Sb 13 HS ltac:(lia)) as RD13. change (Z.of_nat 13) with 13 in RD13.
  pose proof (rd_byte rsegs m s Sb 14 HS ltac:(lia)) as RD14. change (Z.of_nat 14) with 14 in RD14.
  pose proof (zxb_u (nth 12 Sb (Z_to_bv 8 0))) as U12.
  pose proof (zxb_u (nth 13 Sb (Z_to_bv 8 0))) as U13.
  pose proof (zxb_u (nth 14 Sb (Z_to_bv 8 0))) as U14.
  step. step. step.
  replace (f + 18) with (f + 18 + Z.of_nat 0) by lia.
  eapply cs_loop with (bs := fld FB 18 32) (i := 0%nat) (n := 32%nat);
    [ lia | lia | apply fld_length; lia | exact HB | | reflexivity | lia ].
  intros x4.
  pose proof (psum_range (fld FB 18 32) 32) as PR. change (Z.of_nat 32) with 32 in PR.
  unfold cs_hide, fsum, blocksum in Hfl.
  set (P := psum (fld FB 18 32) 32) in *. clearbody P.
  step. step. step. step.
  cond_is false ltac:(apply lor_ne0; rewrite sltiu1_u, land255 by lia;
    destruct Hfl as [Hfl|Hfl]; [ left; exact Hfl | right; rewrite Hfl; discriminate ]).
  step. step.
  unfold fb, zb in Hdecl.
  destruct Hdecl as [D0 | (D1 & D13 & D14)].
  - if_true.
    cs_exit FR ST MU WM MI sp.
  - if_false.
    step. step. step. if_false.
    step. step. step. if_false.
    cs_exit FR ST MU WM MI sp.
Qed.

Lemma cs_tail : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo s f : Z) (Sb FB : list byte)
    (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' t3 t4 t5 t6 : word),
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo + 48 <= bv_unsigned sp ->
  munch [(bv_unsigned sp + -48, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m s Sb -> length Sb = 24%nat -> bytes_at rsegs m f FB -> length FB = 50%nat -> 0 < f ->
  0 <= s32 (fu Sb 8 4) <= 2 ->
  (fb Sb 12 = 0 \/ (fb Sb 12 = 1 /\ fb Sb 13 <= 40 /\ fb Sb 14 <= 40)) ->
  ((fb FB 16 = 0 /\ fb FB 17 = 0) \/ fsum FB = 0) ->
  evt rsegs (cs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 f)
             a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x146ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m lo s f Sb FB
    ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' t3 t4 t5 t6 FR ST LO MU WM MI HS HSl HF HFl Hf0 Hrole Hdecl E6.
  pose proof (bytes_at_bound rsegs m s Sb HS) as Bs. rewrite HSl in Bs.
  pose proof (bytes_at_bound rsegs m f FB HF) as Bf. rewrite HFl in Bf.
  pose proof (rd_le4 rsegs m s Sb 8 HS ltac:(lia)) as RD8. change (Z.of_nat 8) with 8 in RD8.
  pose proof (rd_byte rsegs m f FB 16 HF ltac:(lia)) as RF16. change (Z.of_nat 16) with 16 in RF16.
  pose proof (rd_byte rsegs m f FB 17 HF ltac:(lia)) as RF17. change (Z.of_nat 17) with 17 in RF17.
  pose proof (fu4_range Sb 8 ltac:(lia)) as Rr.
  pose proof (role_small _ Rr Hrole) as Hr.
  assert (Ur : bv_unsigned (sx32 (Z_to_bv 64 (fu Sb 8 4))) = fu Sb 8 4).
  { rewrite sx32_sw by lia. rewrite sw_small by lia. apply unsigned_lit. lia. }
  pose proof (zxb_u (nth 16 FB (Z_to_bv 8 0))) as U16.
  pose proof (zxb_u (nth 17 FB (Z_to_bv 8 0))) as U17.
  unfold fb, zb in E6. lazymatch type of E6 with ?T => change (cs_hide T) in E6 end.
  step. step. step. if_false.
  step. step.
  destruct (Z.eq_dec (bv_unsigned (nth 16 FB (Z_to_bv 8 0))) 0) as [Z16|N16].
  - if_true. step. step.
    eapply cs_fin; [ exact FR | exact ST | exact LO | exact MU | exact WM | exact MI | exact HS | exact HSl
                   | exact HF | exact HFl | exact Hf0 | exact Hdecl | ].
    rewrite sltiu1_u, U17.
    destruct (Z.eq_dec (bv_unsigned (nth 17 FB (Z_to_bv 8 0))) 0) as [Z17|N17].
    + left. rewrite Z17. discriminate.
    + right. unfold cs_hide in E6. destruct E6 as [[_ E]|E]; [contradiction | exact E].
  - if_false. step. step.
    eapply cs_fin; [ exact FR | exact ST | exact LO | exact MU | exact WM | exact MI | exact HS | exact HSl
                   | exact HF | exact HFl | exact Hf0 | exact Hdecl | ].
    right. unfold cs_hide in E6. destruct E6 as [[E _]|E]; [contradiction | exact E].
Qed.

Local Ltac cs_go Sb FB E6 :=
  unfold cs_hide in E6; eapply cs_tail with (Sb := Sb) (FB := FB); eassumption.

Theorem check_sighting_holds : bcmp_contract -> check_sighting_contract.
Proof.
  intros BC.
  unfold check_sighting_contract, CHECK_SIGHTING, CHECK_SIGHTING_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo s f len u st Sb FB U -> -> -> -> -> Hs0 Hs4 HS Hf0 Hflen HFl HF HUl HU Hst SF ST LO Ds Df Du HI.
  change (evt rsegs (cs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 u) (Z_to_bv 64 st)
             a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x145c8) fc None m (seg_rom rsegs))).
  destruct SF as (L50 & E2 & E3 & E4a & E4b & (HSl & Hrole & Hdecl) & E6).
  lazymatch type of E6 with ?T => change (cs_hide T) in E6 end.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (bytes_at_bound rsegs m s Sb HS) as Bs. rewrite HSl in Bs.
  pose proof (bytes_at_bound rsegs m f FB HF) as Bf. rewrite HFl in Bf.
  pose proof (bytes_at_bound rsegs m u U HU) as Bu. rewrite HUl in Bu.
  assert (Us : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (Uf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (Uu : bv_unsigned (Z_to_bv 64 u) = u) by (apply unsigned_lit; lia).
  assert (Ust : bv_unsigned (Z_to_bv 64 st) = st) by (apply unsigned_lit; lia).
  pose proof (fu4_range Sb 20 ltac:(lia)) as Rch.
  pose proof (geo_range len) as Rgeo.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  step. step. step. step. step. step. step. step. step. step.
  if_false.
  step. step. step. step. step. step.
  pose proof (bytes_at_fld rsegs _ s Sb 0 6 HS ltac:(lia)) as HS6. rewrite Z.add_0_r in HS6.
  pose proof (bytes_at_fld rsegs _ f FB 6 6 HF ltac:(lia)) as HF6. change (Z.of_nat 6) with 6 in HF6.
  destruct (memcmp_model_total (fld Sb 0 6) (fld FB 6 6) 6 ltac:(rewrite fld_length; lia) ltac:(rewrite fld_length; lia))
    as [v1 Hv1].
  destruct (cs_memcmp 6 (fld Sb 0 6) (fld FB 6 6) v1 ltac:(apply fld_length; lia) ltac:(apply fld_length; lia) Hv1)
    as [Rv1 Iv1].
  step.
  cs_call BC HS6 HF6 Hv1.
  step.
  assert (V1 : v1 = 0) by (apply Iv1; apply bytes_eqb_true; exact E2). subst v1.
  if_false.
  step. step. step. step.
  destruct (memcmp_model_total (fld Sb 0 6) U 6 ltac:(rewrite fld_length; lia) ltac:(lia)) as [v2 Hv2].
  destruct (cs_memcmp 6 (fld Sb 0 6) U v2 ltac:(apply fld_length; lia) HUl Hv2) as [Rv2 Iv2].
  cs_call BC HS6 HU Hv2.
  step.
  assert (V2 : v2 <> 0) by (intros E; apply Iv2 in E; exact (bytes_eqb_false _ _ E3 E)).
  if_false_by (bv_eqb_nz v2 Rv2 V2).
  clear HS6 HF6.
  pose proof (rd_le4 rsegs _ s Sb 20 HS ltac:(lia)) as RD20. change (Z.of_nat 20) with 20 in RD20.
  step.
  destruct (Z.eq_dec st 0) as [Hz|Hnz].
  - subst st. if_true. specialize (E4a eq_refl).
    step. step. step.
    destruct (Z_lt_ge_dec len 52) as [Hl|Hg].
    + if_false. step. step. step. step.
      rewrite (geo_0 len (or_introl Hl)) in E4a. rewrite E4a.
      if_false.
      cs_go Sb FB E6.
    + if_true.
      step. step. step. step. step. step. step. step. step. step. step. step. step.
      fc_norm len.
      rewrite (mask_sel ((len - 52) mod 36) ((len - 52) / 36)) by (Z.div_mod_to_equations; lia).
      rewrite (geo_sw len) by lia.
      rewrite (sx32_sw (fu Sb 20 4)) by lia. rewrite E4a.
      if_false.
      cs_go Sb FB E6.
  - if_false. specialize (E4b Hnz).
    step. step.
    destruct (Z_lt_ge_dec len 52) as [Hl|Hg].
    + if_true. cs_go Sb FB E6.
    + if_false.
      step. step. step. step. step. step. step. step. step.
      fc_norm len.
      assert (Urm : bv_unsigned (Z_to_bv 64 ((len - 52) mod 36)) = (len - 52) mod 36)
        by (apply unsigned_lit; Z.div_mod_to_equations; lia).
      destruct (Z.eq_dec ((len - 52) mod 36) 0) as [R0|Rn].
      * if_false.
        step. step. step.
        fc_norm len.
        rewrite (Z.add_0_r ((len - 52) / 36)).
        rewrite <- (sw_mod ((len - 52) / 36)).
        rewrite <- (geo_q len) by lia.
        rewrite (sx32_sw (fu Sb 20 4)) by lia.
        rewrite (sw_ltu (fu Sb 20 4) (geo len)) by lia.
        if_true.
        cs_go Sb FB E6.
      * if_true. cs_go Sb FB E6.
Qed.
