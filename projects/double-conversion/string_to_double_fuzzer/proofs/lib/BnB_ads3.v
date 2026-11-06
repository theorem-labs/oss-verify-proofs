(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
 BnModel BnMath BnMem BnDefs LibIface BnP_add BnP_ads2 BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_frame
 BnB_lib BnB_mul7 BnB_add2 BnB_ads1 BnB_ads2.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Ltac flia0 := first [ lia | match goal with H : hide _ |- _ => unfold hide in H; lia end | (unfold hide in *; lia) ].
#[local] Ltac BnB_ads1.flia ::= lf_once flia0.
Ltac inr0 H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
#[local] Ltac BnB_ads1.inr H tac ::= lf_once ltac:(inr0 H tac).
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (o buf len sp sp1 FS p2 g og bg0 bgl : Z) (ds : list Z).
Hypothesis GG : adsG o buf len sp sp1 FS p2 g og bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.
Hypothesis DOK : digits_ok ds.

#[local] Abbreviation F := (FS + 5279744 + p2 * 2048).
#[local] Abbreviation G := g.
#[local] Abbreviation AMBs := (AMB o buf bg0 bgl ds).
#[local] Abbreviation NSs := (NS o FS p2 g).
#[local] Abbreviation SL1s := (SL1 o sp1 g og).
#[local] Abbreviation SL2s := (SL2 o buf sp1 FS p2).
#[local] Abbreviation WINs := (WIN o sp FS p2 g).
#[local] Abbreviation AMBu := (AMB_unch o buf len sp sp1 FS p2 g og bg0 bgl ds GG Hds).
#[local] Abbreviation SL1u := (SL1_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).
#[local] Abbreviation SL2u := (SL2_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).
#[local] Abbreviation WINg := (WIN_grows o sp FS p2 g).
#[local] Abbreviation NS2s := (NS2 o sp1 FS p2 g).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="len GG Hds DOK"] Lemma loop19_B : forall f regs m (done rest : list Z) (b : bn),
  let pos := zlen done in let rem := zlen rest in
  ds = done ++ rest ->
  getr regs 9%bv = Z_to_bv 64 sp1 -> getr regs 2%bv = Z_to_bv 64 sp1 -> getr regs 24%bv = Z_to_bv 64 buf ->
  getr regs 22%bv = Z_to_bv 64 pos -> getr regs 21%bv = Z_to_bv 64 rem -> getr regs 20%bv = Z_to_bv 64 SHA ->
  getr regs 26%bv = Z_to_bv 64 10 -> getr regs 25%bv = Z_to_bv 64 o -> getr regs 19%bv = Z_to_bv 64 MASK ->
  AMBs m -> SL1s m -> SL2s m -> WINs m ->
  19 <= rem -> (Nat.div (length rest) 19 <= f)%nat ->
  bn_at SEGS_B m o b -> ok (cells b) -> norm (cells b) -> ex b = 0 -> 0 <= val (cells b) < 10 ^ pos ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9f2c) m rom) (mkst regs' (Z_to_bv 64 0x0aa414) m' rom)
    /\ (let b' := fst (ads_loop f rest b) in let rest' := snd (ads_loop f rest b) in
        bn_at SEGS_B m' o b' /\ ok (cells b') /\ norm (cells b') /\ ex b' = 0
        /\ 0 <= val (cells b') < 10 ^ (pos + rem - zlen rest') /\ 0 <= zlen rest' < 19
        /\ (exists mid, rest = mid ++ rest')
        /\ getr regs' 22%bv = Z_to_bv 64 (pos + rem - zlen rest') /\ getr regs' 21%bv = Z_to_bv 64 (zlen rest')
        /\ getr regs' 11%bv = Z_to_bv 64 (zlen rest'))
    /\ getr regs' 24%bv = Z_to_bv 64 buf
    /\ keeps K19B regs regs' /\ AMBs m' /\ SL1s m' /\ SL2s m' /\ WINs m'
    /\ unch m m' NS2s /\ mem_grows m m'.
Proof.
  induction f as [|f IH]; intros regs m done rest b pos rem Hsplit R9 R2 R24 R22 R21 R20 R26 R25 R19 AM L1 L2 W Hrem Hf Hbn Hok Hn Hex Hval.
  { exfalso. unfold rem, zlen in Hrem. pose proof (Nat.div_mod_eq (length rest) 19).
    assert (E0 : Nat.div (length rest) 19 = 0%nat) by lia. apply Nat.div_small_iff in E0; lia. }
  assert (Epos : pos = Z.of_nat (length done)) by reflexivity. assert (Erem : rem = Z.of_nat (length rest)) by reflexivity.
  assert (Hpr : pos + rem = len).
  { pose proof Hds as X. rewrite Hsplit, length_app in X. pose proof (g_len _ _ _ _ _ _ _ _ _ _ _ GG). lia. }
  destruct (iter19_B rom o buf len sp sp1 FS p2 g og bg0 bgl ds GG Hds DOK regs m done rest b Hsplit R9 R2 R24 R22 R21 R20 R26 R25 R19 AM L1 L2 W Hrem Hbn Hok Hn Hex Hval)
    as (regs1 & m1 & M1 & Hbn1 & A22 & A20 & A11 & A26 & K1 & AM1 & L11 & L21 & W1 & U1 & G1).
  fold pos rem in M1, A22, A20, A11. clearbody pos rem.
  pose proof DOK as DOK'. rewrite Hsplit in DOK'. destruct (digits_ok_app_inv _ _ DOK') as [DOKd DOKr].
  assert (Hchz : zlen (firstn 19 rest) = 19) by (unfold zlen; rewrite length_firstn; lia).
  pose proof (ads_step_bound (firstn 19 rest) b pos Hok Hn Hex (digits_ok_firstn _ _ DOKr) Hchz Hval ltac:(lia)) as SB.
  cbn zeta in SB. destruct SB as (Hok1 & Hn1 & Hex1 & Hval1).
  remember (ads_step (firstn 19 rest) b) as b1 eqn:Eb1.
  cbn [ads_loop]. replace (zlen rest <? 19) with false by (symmetry; apply Z.ltb_ge; unfold zlen; lia). rewrite <- Eb1.
  assert (Hz1 : zlen (skipn 19 rest) = rem - 19) by (unfold zlen; rewrite length_skipn; lia).
  destruct (Z.ltb_spec (rem - 19) 19) as [Hlt|Hge].
  - (* [comment removed for export] *)
    assert (Hal : ads_loop f (skipn 19 rest) b1 = (b1, skipn 19 rest)).
    { destruct f; cbn [ads_loop]; [reflexivity|]. replace (zlen (skipn 19 rest) <? 19) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    rewrite Hal. cbn [fst snd]. rewrite Hz1.
    eexists regs1, m1. split; [exact M1|].
    split.
    { split; [exact Hbn1|]. split; [exact Hok1|]. split; [exact Hn1|]. split; [exact Hex1|].
      split; [replace (pos + rem - (rem - 19)) with (pos + 19) by lia; exact Hval1|].
      split; [lia|]. split; [exists (firstn 19 rest); symmetry; apply firstn_skipn|].
      split; [rewrite A22; f_equal; lia|]. split; [exact A20 | exact A11]. }
    split; [exact A26|]. split; [exact K1|]. split; [exact AM1|]. split; [exact L11|]. split; [exact L21|]. split; [exact W1|].
    split; [exact U1 | exact G1].
  - (* [comment removed for export] *)
    assert (Hsplit1 : ds = (done ++ firstn 19 rest) ++ skipn 19 rest) by (rewrite <- app_assoc, firstn_skipn; exact Hsplit).
    destruct (IH regs1 m1 (done ++ firstn 19 rest) (skipn 19 rest) b1 Hsplit1) as (regs2 & m2 & M2 & POST & B26 & K2 & AM2 & L12 & L22 & W2 & U2 & G2).
    { kept K1 9 R9. } { kept K1 2 R2. } { exact A26. }
    { rewrite A22. f_equal. rewrite zlen_app, Hchz. unfold zlen in *. lia. }
    { rewrite A20. f_equal. unfold zlen in *. lia. }
    { kept K1 20 R20. } { kept K1 26 R26. } { kept K1 25 R25. } { kept K1 19 R19. }
    { exact AM1. } { exact L11. } { exact L21. } { exact W1. }
    { unfold zlen in *. lia. }
    { rewrite length_skipn. pose proof (Nat.div_mod_eq (length rest) 19). pose proof (Nat.div_mod_eq (length rest - 19) 19).
      assert (Nat.div (length rest - 19) 19 = Nat.div (length rest) 19 - 1)%nat; [|lia].
      replace (length rest) with ((length rest - 19) + 1 * 19)%nat at 2 by lia. rewrite Nat.div_add by lia. lia. }
    { subst b1. exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hex1. }
    { rewrite zlen_app, Hchz. replace (zlen done) with pos by (unfold zlen in *; lia). exact Hval1. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact M1 | exact M2]|].
    destruct (ads_loop f (skipn 19 rest) b1) as [b2 rest2]. cbn [fst snd] in *.
    rewrite zlen_app, Hchz, Hz1 in POST.
    destruct POST as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & (mid & Qmid) & Q8 & Q9 & Q10).
    split.
    { split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
      split; [replace (pos + rem - zlen rest2) with (zlen done + 19 + (rem - 19) - zlen rest2) by (unfold zlen in *; lia); exact Q5|].
      split; [exact Q6|]. split; [exists (firstn 19 rest ++ mid); rewrite <- app_assoc, <- Qmid; symmetry; apply firstn_skipn|].
      split; [rewrite Q8; f_equal; unfold zlen in *; lia|]. split; [exact Q9 | exact Q10]. }
    split; [exact B26|]. split; [eapply keeps_trans; [exact K1 | exact K2]|].
    split; [exact AM2|]. split; [exact L12|]. split; [exact L22|]. split; [exact W2|].
    split; [eapply unch_trans; [exact U1 | exact U2] | eapply mem_grows_trans; [exact G1 | exact G2]].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation rt_pins := [(24%bv : reg, ZV 32); (12%bv : reg, ZV 33); (19%bv : reg, ZV 34); (13%bv : reg, ZV 35); (15%bv : reg, ZL 10);
                         (20%bv : reg, ZL SHA); (14%bv : reg, ZSub (ZL 18446744073709551615) (ZV 32))].
Abbreviation rt_uvi := [Some (IMG, HIE - 1); Some (0, 780); Some (0, 10 ^ 18); Some (0, 780); Some (48, 57)].
Definition rt_keepB : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 13; 14; 15; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="o sp sp1 FS p2 g og ds GG Hds"] Lemma rdtail_B : forall t regs m (idx acc e : Z),
  getr regs 24%bv = Z_to_bv 64 buf -> getr regs 12%bv = Z_to_bv 64 idx -> getr regs 19%bv = Z_to_bv 64 acc ->
  getr regs 13%bv = Z_to_bv 64 e -> getr regs 15%bv = Z_to_bv 64 10 -> getr regs 20%bv = Z_to_bv 64 SHA ->
  getr regs 14%bv = Z_to_bv 64 (18446744073709551615 - buf) ->
  e = idx + zlen t -> t <> [] -> digits_ok t ->
  (forall k, (k < length t)%nat -> cellN SEGS_B m (buf + idx + Z.of_nat k) 1 (nth k t 0)) -> dsh bg0 bgl m ->
  0 <= acc -> (acc + 1) * 10 ^ zlen t <= 10 ^ 18 -> 0 <= idx -> e <= len ->
  exists regs',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa448) m rom) (mkst regs' (Z_to_bv 64 0x0aa498) m rom)
    /\ getr regs' 19%bv = Z_to_bv 64 (read_digits t acc) /\ getr regs' 12%bv = Z_to_bv 64 e
    /\ keeps rt_keepB regs regs'.
Proof.
  induction t as [|d t IH]; intros regs m idx acc e R24 R12 R19 R13 R15 R20 R14 He Hne Hdok Hcells DSH Hacc Hacc2 Hi He2; [congruence|].
  geom GG.
  rewrite zlen_cons in *. pose proof (zlen_nonneg t) as Ht0.
  apply Forall_cons_iff in Hdok. destruct Hdok as [Hd Hdok].
  pose proof (Hcells 0%nat ltac:(cbn; lia)) as D0. cbn [nth] in D0. rewrite Z.add_0_r in D0.
  assert (Hp : 10 ^ (zlen t + 1) = 10 ^ zlen t * 10) by (rewrite Z.pow_add_r by lia; lia).
  rewrite Hp in Hacc2. assert (Hp1 : 1 <= 10 ^ zlen t) by (pose proof (Z.pow_pos_nonneg 10 (zlen t)); lia).
  assert (Hacc3 : acc < 10 ^ 18) by nia.
  cbn [read_digits].
  destruct t as [|d2 t'].
  - rewrite zlen_nil in *.
    zx_run SEGS_B constr:(CTX (vi_regs ++ rt_uvi) [KC (ZAdd (ZV 32) (ZV 33)) 0 1 (ZV 36); KC (ZDivP (ZAdd (ZV 32) (ZV 33)) 3) SHA 1 (ZL 0)] (@nil kwin))
      14%nat [0x0aa448; 0x0aa498] (SCR [false] []) constr:(rt_pins) [buf; idx; acc; e; d] constr:(rt_uvi) regs m rom 0x0aa448.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 D0; kc1 (DSH ((buf + idx) / 8) ltac:(lia)); exact I) ltac:(exact I) ltac:(idtac; zx_scs ltac:(lia)). zx_name regs1.
    exists regs1. split; [exact ZM|]. cbn [read_digits].
    split; [zx_regv ZR|]. split; [zx_regv ZR|]. eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
  - rewrite zlen_cons in *. pose proof (zlen_nonneg t') as Ht1.
    zx_run SEGS_B constr:(CTX (vi_regs ++ rt_uvi) [KC (ZAdd (ZV 32) (ZV 33)) 0 1 (ZV 36); KC (ZDivP (ZAdd (ZV 32) (ZV 33)) 3) SHA 1 (ZL 0)] (@nil kwin))
      14%nat [0x0aa448; 0x0aa498] (SCR [true] []) constr:(rt_pins) [buf; idx; acc; e; d] constr:(rt_uvi) regs m rom 0x0aa448.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 D0; kc1 (DSH ((buf + idx) / 8) ltac:(lia)); exact I) ltac:(exact I) ltac:(idtac; zx_scs ltac:(lia)). zx_name regs1.
    assert (Hp' : 10 ^ (zlen t' + 1) = 10 ^ zlen t' * 10) by (rewrite Z.pow_add_r by lia; lia).
    destruct (IH regs1 m (idx + 1) (acc * 10 + (d - 48)) e) as (regs2 & M2 & C19 & C12 & K2).
    { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
    { lia. } { congruence. } { exact Hdok. }
    { intros k Hk. specialize (Hcells (S k) ltac:(cbn in Hk |- *; lia)). cbn [nth] in Hcells. eapply cellN_eqa; [exact Hcells | lia | reflexivity]. }
    { exact DSH. } { lia. } { rewrite Hp'. nia. } { lia. } { lia. }
    exists regs2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [exact C19|]. split; [exact C12|].
    eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2].
Qed.

End S.
