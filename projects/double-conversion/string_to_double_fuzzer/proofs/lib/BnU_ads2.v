(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnU_mul3 BnU_mul5 BnP_ads1 BnP_ads2 BnU_ads1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition digsU (m : word -> option byte) (buf : Z) (ds : list Z) : Prop :=
  forall k, (k < length ds)%nat -> cellN SEGS_U m (buf + Z.of_nat k) 1 (nth k ds 0).

Lemma digsU_unch : forall m m' buf ds rs,
  unch m m' rs -> 0 <= buf -> buf + zlen ds <= 2 ^ 62 -> (forall r, In r rs -> buf + zlen ds <= fst r \/ snd r <= buf) ->
  digsU m buf ds -> digsU m' buf ds.
Proof.
  intros m m' buf ds rs U Hb1 Hb2 Hd D k Hk. unfold zlen in *.
  eapply cellN_unch; [exact U | lia | zwidth; lia | | exact (D k Hk)].
  intros rg Hrg. specialize (Hd rg Hrg). cbn. zwidth. lia.
Qed.

(* [comment removed for export] *)
Definition K19U : list Z := [2; 3; 4; 8; 9; 21; 22; 23; 24; 25].

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Hypothesis ADD : add_U_spec rom.

#[using="Type"] Lemma rd_regsU_keeps : forall regs regs' buf, rd_regsU regs buf -> keeps K19U regs regs' -> rd_regsU regs' buf.
Proof.
  intros regs regs' buf (Q21 & Q22 & Q23 & Q24 & Q25) K. unfold rd_regsU.
  repeat split; [etransitivity; [exact (K 21 ltac:(inl)) | exact Q21] | etransitivity; [exact (K 22 ltac:(inl)) | exact Q22]
  | etransitivity; [exact (K 23 ltac:(inl)) | exact Q23] | etransitivity; [exact (K 24 ltac:(inl)) | exact Q24]
  | etransitivity; [exact (K 25 ltac:(inl)) | exact Q25]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="ADD"] Lemma iter19_U : forall regs m (o buf sp : Z) (done rest : list Z) (b : bn),
  let pos := zlen done in let rem := zlen rest in
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 9%bv = Z_to_bv 64 buf -> getr regs 19%bv = Z_to_bv 64 pos ->
  getr regs 18%bv = Z_to_bv 64 rem -> getr regs 2%bv = Z_to_bv 64 (sp - 752) ->
  rd_regsU regs buf -> ptr_tblU m sp buf -> digsU m buf (done ++ rest) -> digits_ok (done ++ rest) ->
  19 <= rem -> pos + rem <= 780 ->
  bn_at SEGS_U m o b -> ok (cells b) -> norm (cells b) -> ex b = 0 -> 0 <= val (cells b) < 10 ^ pos ->
  arr32 SEGS_U m 80520 five_tbl ->
  1 <= buf -> buf + zlen (done ++ rest) <= 2 ^ 62 -> 81384 <= sp -> sp <= 2 ^ 62 -> 80568 <= o -> o + 516 <= 2 ^ 62 ->
  (o + 516 <= sp - 816 \/ sp <= o) -> (buf + zlen (done ++ rest) <= sp - 816 \/ sp <= buf) -> (buf + zlen (done ++ rest) <= o \/ o + 516 <= buf) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 816)) 816 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35bf0) m rom)
                  (mkst regs' (Z_to_bv 64 (if rem - 19 <? 19 then 0x35e7c else 0x35bf0)) m' rom)
    /\ bn_at SEGS_U m' o (ads_step (firstn 19 rest) b)
    /\ getr regs' 19%bv = Z_to_bv 64 (pos + 19) /\ getr regs' 18%bv = Z_to_bv 64 (rem - 19) /\ getr regs' 11%bv = Z_to_bv 64 (rem - 19)
    /\ keeps K19U regs regs'
    /\ ptr_tblU m' sp buf /\ arr32 SEGS_U m' 80520 five_tbl
    /\ unch m m' [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m m'.
Proof.
  intros regs m o buf sp done rest b pos rem R8 R9 R19 R18 R2 RD PT DG DOK Hrem Hpr Hbn Hok Hn Hex Hval Htbl
    Hb1 Hb2 Hsp1 Hsp2 Ho1 Ho2 Hdo Hdb Hbo Hsto Hsts.
  assert (Epos : pos = Z.of_nat (length done)) by reflexivity. assert (Erem : rem = Z.of_nat (length rest)) by reflexivity.
  clearbody pos rem. assert (Hpos0 : 0 <= pos) by lia. assert (Hrem0 : 0 <= rem) by lia.
  set (ch := firstn 19 rest).
  assert (Hchl : length ch = 19%nat) by (unfold ch; rewrite length_firstn; lia).
  assert (Hchz : zlen ch = 19) by (unfold zlen; rewrite Hchl; reflexivity).
  destruct (digits_ok_app_inv _ _ DOK) as [DOKd DOKr].
  assert (DOKc : digits_ok ch) by (unfold ch; apply digits_ok_firstn; exact DOKr).
  (* [comment removed for export] *)
  rewrite zlen_app in Hb2, Hdb, Hbo. unfold zlen in Hb2, Hdb, Hbo. rewrite <- Epos, <- Erem in Hb2, Hdb, Hbo.
  destruct (rd19_U rom regs m o buf pos sp ch R8 R9 R19 R2 RD PT Hchl DOKc) as (regs1 & M1 & A25 & A1 & A10 & A11 & K1); try lia.
  { intros k Hk. unfold ch. rewrite <- (firstn_skipn 19 rest) in DG.
    specialize (DG (length done + k)%nat ltac:(rewrite !length_app, length_firstn; lia)).
    rewrite app_nth2 in DG by lia. replace (length done + k - length done)%nat with k in DG by lia.
    rewrite app_nth1 in DG by (rewrite length_firstn; lia).
    eapply cellN_eqa; [exact DG | lia | reflexivity]. }
  pose proof (decval_bound ch DOKc) as Hdv. rewrite Hchz in Hdv.
  (* [comment removed for export] *)
  assert (B8 : getr regs1 8%bv = Z_to_bv 64 o) by (etransitivity; [exact (K1 8 ltac:(inl)) | exact R8]).
  assert (B2 : getr regs1 2%bv = Z_to_bv 64 (sp - 752)) by (etransitivity; [exact (K1 2 ltac:(inl)) | exact R2]).
  destruct (mulpow10_U rom regs1 m o 19 (sp - 752) (Z_to_bv 64 0x35e40) b A10 A11 B2 A1 ltac:(vm_compute; reflexivity)
              ltac:(lia) Hbn Hok Hn) as (regs2 & m2 & M2 & K2 & Hbn2 & Htbl2 & U2 & G2).
  { apply (val_bound_mul _ pos 19); lia. }
  { rewrite Hex. cbn. lia. }
  { exact Htbl. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Hsto. }
  { eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
  pose proof (mulpow10_spec 19 b Hok Hn ltac:(lia)) as SPM. cbn zeta in SPM. destruct SPM as (Hok2 & Hn2 & Hv2 & Hex2 & Hnil2).
  assert (Hex2' : ex (mulpow10 19 b) = 0).
  { destruct (cells b) eqn:Ec; [unfold mulpow10; cbn [Z.eqb]; rewrite Ec; exact Hex | rewrite Hex2 by congruence; rewrite Hex; reflexivity]. }
  assert (Hv2b : 0 <= val (cells (mulpow10 19 b)) < B ^ 124).
  { split; [apply val_nonneg; exact Hok2|]. rewrite Hv2. change (19 mod 28) with 19. apply (proj1 (val_bound_next _ pos Hval ltac:(lia) ltac:(lia))). }
  assert (Hlen2 : zlen (cells (mulpow10 19 b)) <= 124) by (apply len_bound; auto; lia).
  remember (mulpow10 19 b) as b1 eqn:Eb1. destruct b1 as [l1 e1]. cbn [cells BnModel.ex] in *. subst e1.
  (* [comment removed for export] *)
  assert (C25 : getr regs2 20%bv = Z_to_bv 64 (decval ch)) by (etransitivity; [exact (K2 20 ltac:(inl)) | exact A25]).
  assert (C8 : getr regs2 8%bv = Z_to_bv 64 o) by (etransitivity; [exact (K2 8 ltac:(inl)) | exact B8]).
  assert (C2 : getr regs2 2%bv = Z_to_bv 64 (sp - 752)) by (etransitivity; [exact (K2 2 ltac:(inl)) | exact B2]).
  assert (C24 : getr regs2 25%bv = Z_to_bv 64 MASK).
  { etransitivity; [exact (K2 25 ltac:(inl)) |]. etransitivity; [exact (K1 25 ltac:(inl)) | ]. destruct RD as (_ & _ & _ & _ & Q25). exact Q25. }
  assert (C19 : getr regs2 19%bv = Z_to_bv 64 pos).
  { etransitivity; [exact (K2 19 ltac:(inl)) |]. etransitivity; [exact (K1 19 ltac:(inl)) | exact R19]. }
  assert (C18 : getr regs2 18%bv = Z_to_bv 64 rem).
  { etransitivity; [exact (K2 18 ltac:(inl)) |]. etransitivity; [exact (K1 18 ltac:(inl)) | exact R18]. }
  assert (K12 : keeps K19U regs regs2).
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]. }
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_U m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  assert (Hsts2 : RiscvSemantics.store_ok SEGS_U m2 (Z_to_bv 64 (sp - 816)) 816 = true) by (eapply store_ok_grows; [exact G2 | exact Hsts]).
  assert (U2' : unch m m2 [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)]).
  { eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; [eexists; split; [left; reflexivity|cbn; lia] | eexists; split; [right; left; reflexivity|cbn; lia]]. }
  (* [comment removed for export] *)
  assert (ADDP : exists regs3 m3,
    msteps SEGS_U (mkst regs2 (Z_to_bv 64 0x35e40) m2 rom) (mkst regs3 (Z_to_bv 64 0x35bd8) m3 rom)
    /\ bn_at SEGS_U m3 o (add_u64 (decval ch) (BN l1 0))
    /\ keeps CS20 regs2 regs3
    /\ unch m2 m3 [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m2 m3).
  { unfold add_u64. destruct (Z.eqb_spec (decval ch) 0) as [Hd0|Hd0].
    - zx_run SEGS_U constr:(CTX vi_regs (@nil kcell) (@nil kwin)) 10%nat [0x35bd8; 0x35e44] (SCR [] []) constr:([(20%bv : reg, ZL 0)])
        (@nil Z) constr:(@nil (option (Z * Z))) regs2 m2 rom 0x35e40.
      zx_use ZXB ltac:(zx_pins; rewrite C25, Hd0; reflexivity) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      eexists regs3, m2. split; [exact ZM|]. split; [exact Hbn2|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [apply unch_refl | apply mem_grows_refl].
    - zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (1, 2 ^ 64 - 1)]) (@nil kcell) (@nil kwin)) 10%nat [0x35bd8; 0x35e44] (SCR [] []) constr:([(20%bv : reg, ZV 32)])
        [decval ch] constr:([Some (1, 2 ^ 64 - 1)]) regs2 m2 rom 0x35e40.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      assert (K3 : keeps CS20 regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      destruct (au64add_U1 rom ADD regs3 m2 o sp (decval ch) l1) as (regs4 & m4 & M4 & Hbn4 & K4 & U4 & G4).
      { etransitivity; [exact (reg_kept _ _ _ _ (8%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C8]. }
      { etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C2]. }
      { zx_regv ZR. }
      { etransitivity; [exact (reg_kept _ _ _ _ (25%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C24]. }
      { lia. } { exact Hbn2. } { exact Hok2. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Hsto2. } { exact Hsts2. }
      eexists regs4, m4. split; [eapply msteps_trans; [exact ZM | exact M4]|].
      split; [unfold add_bn; cbn [cells BnModel.ex]; exact Hbn4|].
      split; [eapply keeps_trans; [exact K3 | exact K4]|].
      split; [exact U4 | exact G4]. }
  destruct ADDP as (regs3 & m3 & M3 & Hbn3 & K3 & U3 & G3).
  assert (D19 : getr regs3 19%bv = Z_to_bv 64 pos) by (etransitivity; [exact (K3 19 ltac:(inl)) | exact C19]).
  assert (D18 : getr regs3 18%bv = Z_to_bv 64 rem) by (etransitivity; [exact (K3 18 ltac:(inl)) | exact C18]).
  (* [comment removed for export] *)
  assert (LATCH : forall (dir : bool) tgt, (if dir then rem <= 37 /\ tgt = 0x35e7c else 37 < rem /\ tgt = 0x35bf0) ->
    exists regs4,
      msteps SEGS_U (mkst regs3 (Z_to_bv 64 0x35bd8) m3 rom) (mkst regs4 (Z_to_bv 64 tgt) m3 rom)
      /\ getr regs4 19%bv = Z_to_bv 64 (pos + 19) /\ getr regs4 18%bv = Z_to_bv 64 (rem - 19) /\ getr regs4 11%bv = Z_to_bv 64 (rem - 19)
      /\ keeps K19U regs3 regs4).
  { intros dir tgt Hdir. destruct dir; destruct Hdir as [Hc ->].
    - zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 761); Some (19, 37)]) (@nil kcell) (@nil kwin)) 10%nat [0x35e7c; 0x35bf0] (SCR [true] [])
        constr:([(19%bv : reg, ZV 32); (18%bv : reg, ZV 33)]) [pos; rem] constr:([Some (0, 761); Some (19, 37)]) regs3 m3 rom 0x35bd8.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs4.
      exists regs4. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
    - zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 761); Some (38, 780)]) (@nil kcell) (@nil kwin)) 10%nat [0x35e7c; 0x35bf0] (SCR [false] [])
        constr:([(19%bv : reg, ZV 32); (18%bv : reg, ZV 33)]) [pos; rem] constr:([Some (0, 761); Some (38, 780)]) regs3 m3 rom 0x35bd8.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs4.
      exists regs4. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  assert (U23 : unch m m3 [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)]) by (eapply unch_trans; [exact U2' | exact U3]).
  assert (FIN : forall tgt regs4,
    msteps SEGS_U (mkst regs3 (Z_to_bv 64 0x35bd8) m3 rom) (mkst regs4 (Z_to_bv 64 tgt) m3 rom) ->
    getr regs4 19%bv = Z_to_bv 64 (pos + 19) -> getr regs4 18%bv = Z_to_bv 64 (rem - 19) -> getr regs4 11%bv = Z_to_bv 64 (rem - 19) ->
    keeps K19U regs3 regs4 ->
    exists regs' m',
      msteps SEGS_U (mkst regs (Z_to_bv 64 0x35bf0) m rom) (mkst regs' (Z_to_bv 64 tgt) m' rom)
      /\ bn_at SEGS_U m' o (ads_step ch b)
      /\ getr regs' 19%bv = Z_to_bv 64 (pos + 19) /\ getr regs' 18%bv = Z_to_bv 64 (rem - 19) /\ getr regs' 11%bv = Z_to_bv 64 (rem - 19)
      /\ keeps K19U regs regs'
      /\ ptr_tblU m' sp buf /\ arr32 SEGS_U m' 80520 five_tbl
      /\ unch m m' [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m m').
  { intros tgt regs4 M4 E19 E18 E11 K4.
    eexists regs4, m3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4]|].
    split; [unfold ads_step; rewrite Hchz, <- Eb1; unfold decval in Hbn3; exact Hbn3|].
    split; [exact E19|]. split; [exact E18|]. split; [exact E11|].
    split; [eapply keeps_trans; [exact K12|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity | exact K4]|].
    split; [eapply (ptr_tblU_unch m m3); [exact U23 | lia | lia | | exact PT]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]]; cbn; lia|].
    split; [eapply arr32_unch; [exact U3 | lia | cbn; lia | | exact Htbl2]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]]; cbn; lia|].
    split; [exact U23 | eapply mem_grows_trans; [exact G2 | exact G3]]. }
  destruct (Z.ltb_spec (rem - 19) 19) as [Hlt|Hge].
  - destruct (LATCH true 0x35e7c ltac:(split; [lia|reflexivity])) as (regs4 & M4 & E19 & E18 & E11 & K4). eapply FIN; eauto.
  - destruct (LATCH false 0x35bf0 ltac:(split; [lia|reflexivity])) as (regs4 & M4 & E19 & E18 & E11 & K4). eapply FIN; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="ADD"] Lemma loop19_U : forall f regs m (o buf sp : Z) (done rest : list Z) (b : bn),
  let pos := zlen done in let rem := zlen rest in
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 9%bv = Z_to_bv 64 buf -> getr regs 19%bv = Z_to_bv 64 pos ->
  getr regs 18%bv = Z_to_bv 64 rem -> getr regs 2%bv = Z_to_bv 64 (sp - 752) ->
  rd_regsU regs buf -> ptr_tblU m sp buf -> digsU m buf (done ++ rest) -> digits_ok (done ++ rest) ->
  19 <= rem -> pos + rem <= 780 -> (Nat.div (length rest) 19 <= f)%nat ->
  bn_at SEGS_U m o b -> ok (cells b) -> norm (cells b) -> ex b = 0 -> 0 <= val (cells b) < 10 ^ pos ->
  arr32 SEGS_U m 80520 five_tbl ->
  1 <= buf -> buf + zlen (done ++ rest) <= 2 ^ 62 -> 81384 <= sp -> sp <= 2 ^ 62 -> 80568 <= o -> o + 516 <= 2 ^ 62 ->
  (o + 516 <= sp - 816 \/ sp <= o) -> (buf + zlen (done ++ rest) <= sp - 816 \/ sp <= buf) -> (buf + zlen (done ++ rest) <= o \/ o + 516 <= buf) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 816)) 816 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35bf0) m rom) (mkst regs' (Z_to_bv 64 0x35e7c) m' rom)
    /\ (let b' := fst (ads_loop f rest b) in let rest' := snd (ads_loop f rest b) in
        bn_at SEGS_U m' o b' /\ ok (cells b') /\ norm (cells b') /\ ex b' = 0
        /\ 0 <= val (cells b') < 10 ^ (pos + rem - zlen rest') /\ 0 <= zlen rest' < 19
        /\ (exists mid, rest = mid ++ rest')
        /\ getr regs' 19%bv = Z_to_bv 64 (pos + rem - zlen rest') /\ getr regs' 18%bv = Z_to_bv 64 (zlen rest')
        /\ getr regs' 11%bv = Z_to_bv 64 (zlen rest'))
    /\ keeps K19U regs regs' /\ ptr_tblU m' sp buf /\ arr32 SEGS_U m' 80520 five_tbl
    /\ unch m m' [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m m'.
Proof.
  induction f as [|f IH]; intros regs m o buf sp done rest b pos rem R8 R9 R19 R18 R2 RD PT DG DOK Hrem Hpr Hf Hbn Hok Hn Hex Hval Htbl
    Hb1 Hb2 Hsp1 Hsp2 Ho1 Ho2 Hdo Hdb Hbo Hsto Hsts.
  { exfalso. unfold rem, zlen in Hrem. pose proof (Nat.div_mod_eq (length rest) 19).
    assert (E0 : Nat.div (length rest) 19 = 0%nat) by lia. apply Nat.div_small_iff in E0; lia. }
  assert (Epos : pos = Z.of_nat (length done)) by reflexivity. assert (Erem : rem = Z.of_nat (length rest)) by reflexivity.
  destruct (iter19_U regs m o buf sp done rest b R8 R9 R19 R18 R2 RD PT DG DOK Hrem Hpr Hbn Hok Hn Hex Hval Htbl
              Hb1 Hb2 Hsp1 Hsp2 Ho1 Ho2 Hdo Hdb Hbo Hsto Hsts)
    as (regs1 & m1 & M1 & Hbn1 & A19 & A18 & A11 & K1 & PT1 & Htbl1 & U1 & G1).
  fold pos rem in M1, A19, A18, A11. clearbody pos rem.
  destruct (digits_ok_app_inv _ _ DOK) as [DOKd DOKr].
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
      split; [rewrite A19; f_equal; lia|]. split; [exact A18 | exact A11]. }
    split; [exact K1|]. split; [exact PT1|]. split; [exact Htbl1|]. split; [exact U1 | exact G1].
  - (* [comment removed for export] *)
    assert (Hsto1 : RiscvSemantics.store_ok SEGS_U m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G1 | exact Hsto]).
    assert (Hsts1 : RiscvSemantics.store_ok SEGS_U m1 (Z_to_bv 64 (sp - 816)) 816 = true) by (eapply store_ok_grows; [exact G1 | exact Hsts]).
    assert (DG1 : digsU m1 buf ((done ++ firstn 19 rest) ++ skipn 19 rest)).
    { rewrite <- app_assoc, firstn_skipn. eapply digsU_unch; [exact U1 | lia | rewrite zlen_app; unfold zlen in *; rewrite ?length_app in *; lia | | exact DG].
      intros rg Hrg; cbn in Hrg; rewrite zlen_app; destruct Hrg as [<-|[<-|[<-|[]]]]; cbn; unfold zlen in *; rewrite ?length_app in *; lia. }
    assert (DOK1 : digits_ok ((done ++ firstn 19 rest) ++ skipn 19 rest)) by (rewrite <- app_assoc, firstn_skipn; exact DOK).
    destruct (IH regs1 m1 o buf sp (done ++ firstn 19 rest) (skipn 19 rest) b1) as (regs2 & m2 & M2 & POST & K2 & PT2 & Htbl2 & U2 & G2).
    { etransitivity; [exact (K1 8 ltac:(inl)) | exact R8]. }
    { etransitivity; [exact (K1 9 ltac:(inl)) | exact R9]. }
    { rewrite A19. f_equal. rewrite zlen_app, Hchz. unfold zlen in *. lia. }
    { rewrite A18. f_equal. unfold zlen in *. lia. }
    { etransitivity; [exact (K1 2 ltac:(inl)) | exact R2]. }
    { eapply rd_regsU_keeps; [exact RD | exact K1]. }
    { exact PT1. } { exact DG1. } { exact DOK1. }
    { unfold zlen in *. lia. } { rewrite zlen_app, Hchz. unfold zlen in *. lia. }
    { rewrite length_skipn. pose proof (Nat.div_mod_eq (length rest) 19). pose proof (Nat.div_mod_eq (length rest - 19) 19).
      assert (Nat.div (length rest - 19) 19 = Nat.div (length rest) 19 - 1)%nat; [|lia].
      replace (length rest) with ((length rest - 19) + 1 * 19)%nat at 2 by lia. rewrite Nat.div_add by lia. lia. }
    { subst b1. exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hex1. } { rewrite zlen_app, Hchz. replace (zlen done) with pos by (unfold zlen in *; lia). exact Hval1. } { exact Htbl1. }
    { lia. } { rewrite <- app_assoc, firstn_skipn. exact Hb2. } { lia. } { lia. } { lia. } { lia. } { exact Hdo. }
    { rewrite <- app_assoc, firstn_skipn. exact Hdb. } { rewrite <- app_assoc, firstn_skipn. exact Hbo. } { exact Hsto1. } { exact Hsts1. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact M1 | exact M2]|].
    destruct (ads_loop f (skipn 19 rest) b1) as [b2 rest2]. cbn [fst snd] in *.
    rewrite zlen_app, Hchz, Hz1 in POST.
    destruct POST as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & (mid & Qmid) & Q8 & Q9 & Q10).
    split.
    { split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
      split; [replace (pos + rem - zlen rest2) with (zlen done + 19 + (rem - 19) - zlen rest2) by (unfold zlen in *; lia); exact Q5|].
      split; [exact Q6|]. split; [exists (firstn 19 rest ++ mid); rewrite <- app_assoc, <- Qmid; symmetry; apply firstn_skipn|].
      split; [rewrite Q8; f_equal; unfold zlen in *; lia|]. split; [exact Q9 | exact Q10]. }
    split; [eapply keeps_trans; [exact K1 | exact K2]|]. split; [exact PT2|]. split; [exact Htbl2|].
    split; [eapply unch_trans; [exact U1 | exact U2] | eapply mem_grows_trans; [exact G1 | exact G2]].
Qed.
End S.
