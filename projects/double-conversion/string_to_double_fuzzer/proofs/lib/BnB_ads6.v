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
 BnModel BnMath BnMem BnDefs LibIface BnP_add BnP_ads2 BnP_ads3 BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsRtLibB AsZX AsZXTac AsZXDefs BnA_lib BnA_frame
 BnB_lib BnB_mul7 BnB_add2 AsMallocB AsFree5B BnB_ads1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Ltac flia0 := first [ lia | match goal with H : hide _ |- _ => unfold hide in H; lia end | (unfold hide in *; lia) ].
#[local] Ltac BnB_ads1.flia ::= lf_once flia0.
Ltac inr0 H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
#[local] Ltac BnB_ads1.inr H tac ::= lf_once ltac:(inr0 H tac).
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Record adsE (o buf len sp FS og bg0 bgl : Z) : Prop := AdsE {
  e_o1 : APP o 516; e_o2 : o + 516 <= HIE; e_o8 : o = 8 * og;
  e_b1 : APP buf len; e_b2 : buf + len <= HIE; e_len : 1 <= len <= 780;
  e_bg0 : 8 * bg0 <= buf < 8 * bg0 + 8; e_bgl : 8 * bgl <= buf + len - 1 < 8 * bgl + 8;
  e_sp1 : KHI + 656 <= sp; e_sp2 : sp <= HIE; e_sp16 : exists q, sp = 16 * q;
  e_fs1 : APP FS FS_LEN; e_fs2 : FS + FS_LEN <= HIE; e_fs4 : exists q, FS = 4096 * q;
  e_osp : o + 516 <= sp - 656 \/ sp <= o;
  e_bsp : buf + len <= sp - 656 \/ sp <= buf;
  e_bo : buf + len <= o \/ o + 516 <= buf;
  e_spFS : sp <= FS \/ FS + FS_LEN <= sp - 656;
  e_ohd : FS + 36864 <= o /\ o + 516 <= FS + FS_LEN;
  e_bhd : buf + len <= FS + 40 \/ FS + 48 <= buf;
  e_bh2 : buf + len <= FS + 35840 \/ FS + 36352 <= buf }.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (o buf len sp FS og bg0 bgl : Z) (ds : list Z) (fl : Z -> Z).
Hypothesis GE : adsE o buf len sp FS og bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.
Hypothesis DOK : digits_ok ds.
(* [comment removed for export] *)
Hypothesis Hfl01 : forall j, 0 <= j < 512 -> fl j = 0 \/ fl j = 1.
Hypothesis Hflex : exists j, 0 <= j < 512 /\ fl j = 0.
Hypothesis HoFR : forall j, 0 <= j < 512 -> fl j = 0 -> o + 516 <= FS + 5279744 + j * 2048 \/ FS + 5279744 + j * 2048 + 2048 <= o.
Hypothesis HbFR : forall j, 0 <= j < 512 -> fl j = 0 -> buf + len <= FS + 5279744 + j * 2048 \/ FS + 5279744 + j * 2048 + 2048 <= buf.

Definition sp1 : Z := 32 * ((sp - 384) / 32).

#[using="o buf len FS og bg0 bgl fl GE"] Lemma sp1_facts : sp - 400 <= sp1 <= sp - 384 /\ (exists q, sp1 = 32 * q) /\ sp1 mod 16 = 0.
Proof.
  clear Hds DOK Hfl01 Hflex HoFR HbFR.
  destruct GE as [Eo1 Eo2 Eo8 Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dosp Dbsp Dbo DspFS [Eoh1 Eoh2] Dbhd Dbh2].
  unfold sp1. subst sp. split; [lia|]. split; [eexists; reflexivity | lia].
Qed.

#[using="GE HoFR HbFR"] Lemma geomE : forall p, 0 <= p < 512 -> fl p = 0 ->
  adsG o buf len sp sp1 FS p (SHA + (FS + 5279744 + p * 2048) / 8) og bg0 bgl.
Proof.
  clear Hds DOK Hflex. intros p Hp Hf. pose proof (HoFR p Hp Hf) as A. pose proof (HbFR p Hp Hf) as B.
  pose proof sp1_facts as (S1 & S2 & _).
  destruct GE as [Eo1 Eo2 Eo8 Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dosp Dbsp Dbo DspFS [Eoh1 Eoh2] Dbhd Dbh2].
  constructor; try assumption; try lia. exists qf; exact Hqf.
Qed.

#[local] Abbreviation AMBs := (AMB o buf bg0 bgl ds).
#[local] Abbreviation SAVu p GG := (SAV_unch o buf len sp sp1 FS p (SHA + (FS + 5279744 + p * 2048) / 8) og bg0 bgl ds GG Hds).

(* [comment removed for export] *)
Abbreviation en_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (12%bv : reg, ZV 34); (2%bv : reg, ZV 35)].
Abbreviation en_uvi := [Some (IMG, HIE - 516); Some (IMG, HIE - 1); Some (1, 780); Some (KHI + 656, HIE)].
Abbreviation en_kn := [KC (ZL 0) 0x12a3d8 8 (ZL 0x132740); KC (ZL 0) 0x132740 4 (ZL 1); KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL SHA)].

(* [comment removed for export] *)
Definition savs (regs : bvmap 5 word) (ret : word) : list Z :=
  [bv_unsigned ret; bv_unsigned (getr regs 8%bv); bv_unsigned (getr regs 9%bv); bv_unsigned (getr regs 18%bv);
   bv_unsigned (getr regs 19%bv); bv_unsigned (getr regs 20%bv); bv_unsigned (getr regs 21%bv); bv_unsigned (getr regs 22%bv);
   bv_unsigned (getr regs 23%bv); bv_unsigned (getr regs 24%bv); bv_unsigned (getr regs 25%bv); bv_unsigned (getr regs 26%bv);
   bv_unsigned (getr regs 27%bv)].

(* [comment removed for export] *)
#[using="GE Hds Hfl01 Hflex HoFR HbFR"] Lemma ads_pro_B : forall regs m (ret : word),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 buf -> getr regs 12%bv = Z_to_bv 64 len ->
  getr regs 2%bv = Z_to_bv 64 sp -> getr regs 1%bv = ret -> bv_unsigned ret mod 4 = 0 -> getr regs 4%bv = Z_to_bv 64 TP_B ->
  rt_ok_B m -> ro_ok SEGS_B RO_B m -> gsh_ok_B m -> objshB m o -> digs buf ds m -> dsh bg0 bgl m ->
  mem_def m (sp - 656) 656 -> mem_def m o 516 ->
  malloc_ctx_ok_B (sp - 656) sp FS m -> rd_u64_B m FSTLS_B FS ->
  mem_def m FS FS_LEN -> mem_def m (sh FS + FS_SHLO) (FS_SHHI - FS_SHLO) -> mem_u64 m (FS + 88) 20 -> mem_byte m (FS + 96) 0 ->
  (forall j, 0 <= j < 512 -> mem_byte m (fs_flag FS 5 j) (fl j)) ->
  exists regs7 m7 p F g,
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9c5c) m rom) (mkst regs7 (Z_to_bv 64 0x0a9e00) m7 rom)
    /\ 0 <= p < 512 /\ fl p = 0 /\ F = FS + 5279744 + p * 2048 /\ F = 8 * (g - SHA)
    /\ adsG o buf len sp sp1 FS p g og bg0 bgl
    /\ getr regs7 9%bv = Z_to_bv 64 sp1 /\ getr regs7 2%bv = Z_to_bv 64 sp1 /\ getr regs7 4%bv = Z_to_bv 64 TP_B
    /\ getr regs7 8%bv = Z_to_bv 64 sp /\ getr regs7 19%bv = Z_to_bv 64 g /\ getr regs7 18%bv = Z_to_bv 64 F
    /\ getr regs7 21%bv = Z_to_bv 64 len /\ getr regs7 25%bv = Z_to_bv 64 o /\ getr regs7 26%bv = Z_to_bv 64 F
    /\ getr regs7 24%bv = Z_to_bv 64 buf /\ getr regs7 20%bv = Z_to_bv 64 SHA
    /\ getr regs7 10%bv = Z_to_bv 64 18446744073709551603 /\ getr regs7 11%bv = Z_to_bv 64 og
    /\ keeps [3; 4] regs regs7
    /\ AMB o buf bg0 bgl ds m7 /\ WIN o sp FS p g m7 /\ SAV sp m7 (savs regs ret)
    /\ cellN SEGS_B m7 (sp1 + 240) 8 (g + 86) /\ cellN SEGS_B m7 (sp1 + 24) 8 (g + 4)
    /\ rt_ok_B m7 /\ ro_ok SEGS_B RO_B m7 /\ mem_u64 m7 (F + 2040) (FS + 35840 + p) /\ mem_byte m7 (FS + 35840 + p) 1
    /\ unch m m7 [(sp - 400, sp); (sp1 - 256, sp1); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1);
                   (F, F + 32); (F + 2040, F + 2048); (g, g + 256); (sp1 + 240, sp1 + 248); (sp1 + 272, sp1 + 280); (sp1 + 24, sp1 + 32)]
    /\ mem_grows m m7.
Proof.
  intros regs m ret R10 R11 R12 R2 R1 Hret4 R4 RT RO GSH OSH DG DSH Dsp Do MCX TLS DFS DSHD L88 B96 FL.
  pose proof (ret_ok_of_mod4 ret Hret4) as Hret.
  pose proof sp1_facts as (Hs1 & [q1 Hq1] & Hs16).
  pose proof GE as GE0. destruct GE as [Eo1 Eo2 Eo8 Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dosp Dbsp Dbo DspFS [Eoh1 Eoh2] Dbhd Dbh2].
  destruct Eo1 as [Eo1 Zo]. destruct Eb1 as [Eb1 Zb]. destruct Efs1 as [Efs1 Zfs].   (* [comment removed for export] *)
  unfold FS_LEN in *. hide Zo; hide Zb; hide Dbhd; hide Dbh2; hide Dbo; hide Dbsp; hide DspFS; hide Dosp; hide Zfs. move Zfs at bottom.
  pose proof (u64_range ret) as W1. pose proof (u64_range (getr regs 8%bv)) as W8. pose proof (u64_range (getr regs 9%bv)) as W9.
  pose proof (u64_range (getr regs 18%bv)) as W18. pose proof (u64_range (getr regs 19%bv)) as W19.
  pose proof (u64_range (getr regs 20%bv)) as W20. pose proof (u64_range (getr regs 21%bv)) as W21.
  pose proof (u64_range (getr regs 22%bv)) as W22. pose proof (u64_range (getr regs 23%bv)) as W23.
  pose proof (u64_range (getr regs 24%bv)) as W24. pose proof (u64_range (getr regs 25%bv)) as W25.
  pose proof (u64_range (getr regs 26%bv)) as W26. pose proof (u64_range (getr regs 27%bv)) as W27.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  pose proof (suarB_intro m RT RO) as [SU1 SU2]. pose proof (shcellsB_intro m RT RO) as [SC1 SC2].
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ en_uvi) en_kn [KW (ZV 35) (-400) 0]) 40%nat [0x5b7e4] (SCR [] []) constr:(en_pins)
    [o; buf; len; sp] constr:(en_uvi) regs m rom 0x0a9c5c.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 SU1; kc1 SU2; kc1 SC1; kc1 SC2; exact I) ltac:(kwd Dsp; exact I) ltac:(exact I). zx_name regs1.
  zx_reg ZR (2%bv : reg) as A2raw. zx_reg ZR (1%bv : reg) as A1. zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (21%bv : reg) as A21.
  zx_reg ZR (24%bv : reg) as A24. zx_reg ZR (20%bv : reg) as A20. zx_reg ZR (25%bv : reg) as A25. zx_reg ZR (9%bv : reg) as A9raw.
  assert (A4 : getr regs1 4%bv = Z_to_bv 64 TP_B) by (etransitivity; [exact (reg_kept _ _ _ _ (4%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R4]).
  assert (K1 : keeps [3; 4] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  assert (Hland : Z.land ((sp + -384) mod 18446744073709551616) (-32 mod 18446744073709551616) = sp1).
  { rewrite (Z.mod_small (sp + -384)) by lia. unfold sp1.
    replace (-32 mod 18446744073709551616) with ((-32) mod 2 ^ 64) by reflexivity. rewrite land_align32 by lia. lia. }
  assert (A2 : getr regs1 2%bv = Z_to_bv 64 sp1) by (rewrite A2raw, Hland; reflexivity).
  assert (A9 : getr regs1 9%bv = Z_to_bv 64 sp1) by (rewrite A9raw, Hland; reflexivity).
  clear A2raw A9raw Hland Hret4. rename ZM into M1. clear ZE ZR ZF.
  set (m1 := wbytes _ _ _) in M1.
  set (vs := savs regs ret).
  assert (SVc : cellN SEGS_B m1 (sp + -8) 8 (bv_unsigned ret) /\ cellN SEGS_B m1 (sp + -16) 8 (bv_unsigned (getr regs 8%bv))
    /\ cellN SEGS_B m1 (sp + -24) 8 (bv_unsigned (getr regs 9%bv)) /\ cellN SEGS_B m1 (sp + -32) 8 (bv_unsigned (getr regs 18%bv))
    /\ cellN SEGS_B m1 (sp + -40) 8 (bv_unsigned (getr regs 19%bv)) /\ cellN SEGS_B m1 (sp + -48) 8 (bv_unsigned (getr regs 20%bv))
    /\ cellN SEGS_B m1 (sp + -56) 8 (bv_unsigned (getr regs 21%bv)) /\ cellN SEGS_B m1 (sp + -64) 8 (bv_unsigned (getr regs 22%bv))
    /\ cellN SEGS_B m1 (sp + -72) 8 (bv_unsigned (getr regs 23%bv)) /\ cellN SEGS_B m1 (sp + -80) 8 (bv_unsigned (getr regs 24%bv))
    /\ cellN SEGS_B m1 (sp + -88) 8 (bv_unsigned (getr regs 25%bv)) /\ cellN SEGS_B m1 (sp + -96) 8 (bv_unsigned (getr regs 26%bv))
    /\ cellN SEGS_B m1 (sp + -104) 8 (bv_unsigned (getr regs 27%bv))).
  { subst m1. rewrite <- R1. rewrite <- R1 in W1. clear - Esp1 Esp2 W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27.
    cbv [Z.of_nat Pos.of_succ_nat Pos.succ].
    change (getr regs (Z_to_bv 5 8)) with (getr regs 8%bv). change (getr regs (Z_to_bv 5 9)) with (getr regs 9%bv).
    change (getr regs (Z_to_bv 5 18)) with (getr regs 18%bv). change (getr regs (Z_to_bv 5 19)) with (getr regs 19%bv).
    change (getr regs (Z_to_bv 5 20)) with (getr regs 20%bv). change (getr regs (Z_to_bv 5 21)) with (getr regs 21%bv).
    change (getr regs (Z_to_bv 5 22)) with (getr regs 22%bv). change (getr regs (Z_to_bv 5 23)) with (getr regs 23%bv).
    change (getr regs (Z_to_bv 5 24)) with (getr regs 24%bv). change (getr regs (Z_to_bv 5 25)) with (getr regs 25%bv).
    change (getr regs (Z_to_bv 5 26)) with (getr regs 26%bv). change (getr regs (Z_to_bv 5 27)) with (getr regs 27%bv).
    repeat split; cellx2. }
  assert (SV1 : SAV sp m1 vs).
  { destruct SVc as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12). subst vs. unfold savs. clear - C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12.
    intros k Hk.
    destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]; [| | | | | | | | | | | | | lia]; cbv [nth Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul];
      [eapply cellN_eqa; [exact C0 | lia | reflexivity] | eapply cellN_eqa; [exact C1 | lia | reflexivity] | eapply cellN_eqa; [exact C2 | lia | reflexivity] | eapply cellN_eqa; [exact C3 | lia | reflexivity] | eapply cellN_eqa; [exact C4 | lia | reflexivity] | eapply cellN_eqa; [exact C5 | lia | reflexivity] | eapply cellN_eqa; [exact C6 | lia | reflexivity] | eapply cellN_eqa; [exact C7 | lia | reflexivity] | eapply cellN_eqa; [exact C8 | lia | reflexivity] | eapply cellN_eqa; [exact C9 | lia | reflexivity] | eapply cellN_eqa; [exact C10 | lia | reflexivity] | eapply cellN_eqa; [exact C11 | lia | reflexivity] | eapply cellN_eqa; [exact C12 | lia | reflexivity]]. }
  clear SVc.
  assert (U01 : unch m m1 [(sp - 400, sp)]) by (subst m1; clear - Esp1 Esp2; unchx).
  assert (G01 : mem_grows m m1) by (subst m1; growsx).
  assert (HR01 : forall r, In r [(sp - 400, sp)] -> highr r) by (clear W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 R10 R11 R12 R2 R1 R4; intros r Hr; unfold highr; inr Hr ltac:(cbn; flia)).
  (* [comment removed for export] *)
  pose proof mallocB_5 as MS. unfold malloc_stmt_B in MS.
  pose proof fs5_consts as (EN5 & EFLO5 & EFRO5 & EFSZ5).
  destruct (MS fx regs1 m1 rom (Z_to_bv 64 0x0a9cd4) sp1 FS fl) as (regs2 & m2 & p & M2 & K2 & Hp & Hflp & B10 & FL1 & Q2040 & SHZ & FR2);
    clear MS.
  { exact A1. } { vm_compute. reflexivity. } { exact A2. } { exact Hs16. } { unfold KHI_A, MALLOC_FR. lia. } { unfold HIEND_A. lia. }
  { unfold MALLOC_FR. eapply mem_def_grows; [exact G01|]. eapply mem_def_sub; [exact Dsp | lia | lia]. }
  { exact A4. }
  { eapply rt_ok_B_unch; [exact U01 | exact HR01 | exact RT]. } { eapply ro_ok_unchB; [exact U01 | exact HR01 | exact RO]. }
  { eapply malloc_ctx_ok_B_unch; [exact MCX | exact U01 | exact G01 | | unfold MALLOC_FR; lia | lia].
    intros r Hr. inr Hr ltac:(cbn; unfold FS_LEN, KHI_A; lia). all: match goal with |- ?g => idtac g end. }
  { eapply cellN_low_unchB; [exact U01 | exact HR01 | unfold FSTLS_B; lia | unfold FSTLS_B; cbn; lia | exact TLS]. }
  { rewrite Hqf, Z.mul_comm. apply Z_mod_mult. } { unfold IMGHI_A. lia. } { unfold app_mem, LOSH_A, KHI_A, FS_LEN. unfold hide in Zfs. lia. } { unfold HIEND_A, FS_LEN. lia. }   (* [comment removed for export] *)
  { unfold MALLOC_FR, FS_LEN. unfold hide in DspFS. lia. }
  { eapply mem_def_grows; [exact G01 | exact DFS]. } { eapply mem_def_grows; [exact G01 | exact DSHD]. }
  { eapply mem_u64_unch; [exact U01 | lia | lia | intros r Hr; inr Hr ltac:(cbn; unfold hide in DspFS; lia) | exact L88]. }
  { eapply mem_byte_unch; [exact U01 | lia | intros r Hr; inr Hr ltac:(cbn; unfold hide in DspFS; lia) | exact B96]. }
  { rewrite EN5. intros j Hj. split; [| exact (Hfl01 j Hj)].
    eapply mem_byte_unch; [exact U01 | rewrite fs_flag5; lia | intros r Hr; inr Hr ltac:(cbn; rewrite fs_flag5; unfold hide in DspFS; lia) | exact (FL j Hj)]. }
  { rewrite EN5. exact Hflex. }
  clear Hs16. rewrite EN5 in Hp. rewrite fs_frame5, fs_flag5 in *. rewrite EFSZ5 in *. rewrite fs_hint5 in FR2.
  apply keeps_of_cs in K2.
  pose proof (unch_of_frame _ _ _ FR2) as U12. pose proof (grows_of_frame _ _ _ FR2) as G12. clear FR2.
  (* [comment removed for export] *)
  set (F := FS + 5279744 + p * 2048) in *.
  pose proof (geomE p Hp Hflp) as GG. fold F in GG.
  set (g := SHA + F / 8) in *.
  assert (HgF : F = 8 * (g - SHA)) by (subst g F; rewrite Hqf; lia).
  unfold sh, SH_A in U12, SHZ. fold g in U12. fold g in SHZ.
  replace (F + 2048 - 8) with (F + 2040) in Q2040, U12 by lia.
  clear Dosp Dbsp Dbo DspFS Dbhd Dbh2. pose proof GG as GG0. geom GG.
  assert (HFdef : F = FS + 5279744 + p * 2048) by reflexivity.
  change (2048 / 8) with 256 in U12, SHZ. unfold MALLOC_FR in U12. replace (FS + 40 + 8) with (FS + 48) in U12 by lia.
  clearbody F g.
  (* [comment removed for export] *)
  assert (U02 : unch m m2 [(sp - 400, sp); (sp1 - 256, sp1); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F + 24, F + 32); (F + 2040, F + 2048); (g, g + 256)]).
  { eapply unch_trans; [eapply unch_widen; [exact U01|] | eapply unch_widen; [exact U12|]];
      intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [ eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]
        | eexists; split; [do 2 right; left; reflexivity | cbn; lia] | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
        | eexists; split; [do 4 right; left; reflexivity | cbn; lia] | eexists; split; [do 5 right; left; reflexivity | cbn; lia]
        | eexists; split; [do 6 right; left; reflexivity | cbn; lia] ]). }
  assert (G02 : mem_grows m m2) by (eapply mem_grows_trans; [exact G01 | exact G12]).
  assert (AM0 : AMBs m).
  { split; [exact (conj SC1 SC2)|]. split; [exact (mscellsB_intro m RO)|]. split; [exact (five_tblB_intro m RO)|].
    split; [exact (tblshB_intro m GSH)|]. split; [exact OSH|]. split; [exact DG|]. split; [exact DSH | exact (k27_intro m RO)]. }
  pose proof (AMB_unch o buf len sp sp1 FS p g og bg0 bgl ds GG0 Hds m m2 _ U02 ltac:(clear W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 R10 R11 R12 R2 R1 R4; rngs) AM0) as AM2.
  assert (W2 : WIN o sp FS p g m2).
  { split; [eapply mem_def_grows; [exact G02 | exact Dsp]|]. split; [eapply mem_def_grows; [exact G02 | exact Do]|].
    split; (eapply mem_def_grows; [exact G02|]).
    - eapply mem_def_sub; [exact DFS | lia | lia].
    - eapply mem_def_sub; [exact DSHD | unfold sh, SH_A, FS_SHLO, FS_FRAMES; rewrite Hqf in *; lia | unfold sh, SH_A, FS_SHLO, FS_SHHI, FS_FRAMES; unfold FS_LEN; rewrite Hqf in *; lia]. }
  assert (SV2 : SAV sp m2 vs).
  { eapply (SAV_unch o buf len sp sp1 FS p g og bg0 bgl GG0 m1 m2); [exact U12 | clear W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 R10 R11 R12 R2 R1 R4; rngs | exact SV1]. }
  assert (B9 : getr regs2 9%bv = Z_to_bv 64 sp1) by (kept K2 9 A9).
  assert (B2 : getr regs2 2%bv = Z_to_bv 64 sp1) by (kept K2 2 A2).
  assert (B8 : getr regs2 8%bv = Z_to_bv 64 sp) by (kept K2 8 A8).
  assert (B21 : getr regs2 21%bv = Z_to_bv 64 len) by (kept K2 21 A21).
  assert (B24 : getr regs2 24%bv = Z_to_bv 64 buf) by (kept K2 24 A24).
  assert (B20 : getr regs2 20%bv = Z_to_bv 64 SHA) by (kept K2 20 A20).
  assert (B25 : getr regs2 25%bv = Z_to_bv 64 o) by (kept K2 25 A25).
  assert (B4 : getr regs2 4%bv = Z_to_bv 64 TP_B) by (kept K2 4 A4).
  assert (K02 : keeps [3; 4] regs regs2) by (eapply keeps_trans; [exact K1 | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]).
  assert (M02 : msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9c5c) m rom) (mkst regs2 (Z_to_bv 64 0x0a9cd4) m2 rom)).
  { eapply msteps_trans; [exact M1 | exact M2]. }
  clear M1 M2 K1 K2 A1 A2 A4 A8 A9 A20 A21 A24 A25 SV1 U01 G01 HR01 U12 G12 regs1.
  (* [comment removed for export] *)
  pose proof W2 as (Wsp2 & Wo2 & WF2 & WG2).
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (IMG, HIE - 2048)]) (@nil kcell)
                          [KW (ZV 32) 0 280; KW (ZV 33) 0 24; KW (ZDivP (ZV 33) 3) SHA (SHA + 256)])
    40%nat [0x78590] (SCR [] []) constr:([(9%bv : reg, ZV 32); (10%bv : reg, ZV 33); (20%bv : reg, ZL SHA)]) [sp1; F]
    constr:([Some (KHI + 256, HIE - 384); Some (IMG, HIE - 2048)]) regs2 m2 rom 0x0a9cd4.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I)
    ltac:(kwd Wsp2; kwd WF2; kwd WG2; exact I) ltac:(exact I). zx_name regs3.
  zx_reg ZR (1%bv : reg) as C1. zx_reg ZR (10%bv : reg) as C10. zx_reg ZR (11%bv : reg) as C11. zx_reg ZR (18%bv : reg) as C18.
  zx_reg ZR (19%bv : reg) as C19. zx_reg ZR (26%bv : reg) as C26.
  assert (K3 : keeps [2; 3; 4; 8; 9; 20; 21; 22; 23; 24; 25; 27] regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M3. clear ZE ZR ZF. set (m3 := wbytes _ _ _) in M3.
  assert (U23 : unch m2 m3 [(sp1 + 272, sp1 + 280); (F, F + 24); (g, g + 4); (sp1 + 24, sp1 + 32)]) by (subst m3; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; unchx).
  assert (G23 : mem_grows m2 m3) by (subst m3; growsx).
  assert (S24 : cellN SEGS_B m3 (sp1 + 24) 8 (g + 4)) by (subst m3; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; cellx2).
  pose proof AM2 as (_ & MC2 & _).
  destruct (setsh_B rom true regs3 m3 (g + 4) 65 (Z_to_bv 64 0x0a9d60)) as (regs4 & M4 & K4).
  { rewrite C10; f_equal; lia. } { exact C11. } { exact C1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact G23 | exact WG2]|]. zwidth. lia. }
  { eapply mscellsB_unch; [exact U23 | intros r Hr; unfold highr; inr Hr ltac:(cbn; flia) | exact MC2]. }
  cbn [negb] in M4. set (m4 := wbytes m3 _ _) in M4.
  assert (U34 : unch m3 m4 [(g + 4, g + 69)]).
  { unfold m4. eapply (unch_store_bs m3 (g + 4)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G34 : mem_grows m3 m4) by (unfold m4; apply grows_store).
  assert (D9 : getr regs4 9%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K4 9 ltac:(in_list)) | kept K3 9 B9]).
  assert (D19 : getr regs4 19%bv = Z_to_bv 64 g) by (etransitivity; [exact (K4 19 ltac:(in_list)) | etransitivity; [exact C19 | f_equal; lia]]).
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256)]) (@nil kcell) [KW (ZV 32) 0 280; KW (ZV 33) 0 256])
    40%nat [0x78590] (SCR [] []) constr:([(9%bv : reg, ZV 32); (19%bv : reg, ZV 33)]) [sp1; g]
    constr:([Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256)]) regs4 m4 rom 0x0a9d60.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I)
    ltac:(kwd (mem_def_grows _ _ _ _ (mem_grows_trans _ _ _ G23 G34) Wsp2); kwd (mem_def_grows _ _ _ _ (mem_grows_trans _ _ _ G23 G34) WG2); exact I) ltac:(exact I).
  zx_name regs5.
  zx_reg ZR (1%bv : reg) as E1. zx_reg ZR (10%bv : reg) as E10. zx_reg ZR (11%bv : reg) as E11.
  assert (K5 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs4 regs5) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M5. clear ZE ZR ZF. set (m5 := wbytes _ _ _) in M5.
  assert (S240 : cellN SEGS_B m5 (sp1 + 240) 8 (g + 86)) by (subst m5; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; cellx2).
  assert (U45 : unch m4 m5 [(g + 69, g + 86); (sp1 + 240, sp1 + 248)]) by (subst m5; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; unchx).
  assert (G45 : mem_grows m4 m5) by (subst m5; growsx).
  assert (U25 : unch m2 m5 [(sp1 + 272, sp1 + 280); (F, F + 24); (g, g + 86); (sp1 + 240, sp1 + 248); (sp1 + 24, sp1 + 32)]).
  { eapply unch_trans; [eapply unch_widen; [exact U23|] | eapply unch_trans; [eapply unch_widen; [exact U34|] | eapply unch_widen; [exact U45|]]];
      intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [ eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]
        | eexists; split; [do 2 right; left; reflexivity | cbn; lia] | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
        | eexists; split; [do 4 right; left; reflexivity | cbn; lia] ]). }
  assert (G25 : mem_grows m2 m5) by (eapply mem_grows_trans; [exact G23|]; eapply mem_grows_trans; [exact G34 | exact G45]).
  assert (S24' : cellN SEGS_B m5 (sp1 + 24) 8 (g + 4)).
  { eapply cellN_unch; [exact U45 | lia | cbn; lia | intros r Hr; inr Hr ltac:(cbn; flia) |].
    eapply cellN_unch; [exact U34 | lia | cbn; lia | intros r Hr; inr Hr ltac:(cbn; flia) | exact S24]. }
  destruct (setsh_B rom true regs5 m5 (g + 86) 65 (Z_to_bv 64 0x0a9db8)) as (regs6 & M6 & K6).
  { rewrite E10; f_equal; lia. } { exact E11. } { exact E1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [eapply mem_def_grows; [exact G25 | exact WG2]|]. zwidth. lia. }
  { eapply mscellsB_unch; [exact U25 | intros r Hr; unfold highr; inr Hr ltac:(cbn; flia) | exact MC2]. }
  cbn [negb] in M6. set (m6 := wbytes m5 _ _) in M6.
  assert (U56 : unch m5 m6 [(g + 86, g + 151)]).
  { unfold m6. eapply (unch_store_bs m5 (g + 86)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G56 : mem_grows m5 m6) by (unfold m6; apply grows_store).
  assert (F19 : getr regs6 19%bv = Z_to_bv 64 g) by (etransitivity; [exact (K6 19 ltac:(in_list)) | kept K5 19 D19]).
  assert (F25 : getr regs6 25%bv = Z_to_bv 64 o).
  { etransitivity; [exact (K6 25 ltac:(in_list)) |]. etransitivity; [exact (K5 25 ltac:(in_list)) |].
    etransitivity; [exact (K4 25 ltac:(in_list)) | kept K3 25 B25]. }
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (SHA, KHI - 256); Some (IMG, HIE - 516)]) (@nil kcell) [KW (ZV 32) 0 256])
    40%nat [0x0a9e00] (SCR [] []) constr:([(19%bv : reg, ZV 32); (25%bv : reg, ZV 33)]) [g; o]
    constr:([Some (SHA, KHI - 256); Some (IMG, HIE - 516)]) regs6 m6 rom 0x0a9db8.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I)
    ltac:(kwd (mem_def_grows _ _ _ _ (mem_grows_trans _ _ _ G25 G56) WG2); exact I) ltac:(exact I).
  zx_name regs7.
  zx_reg ZR (10%bv : reg) as H10. zx_reg ZR (11%bv : reg) as H11.
  assert (K7 : keeps [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs6 regs7) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M7. clear ZE ZR ZF. set (m7 := wbytes _ _ _) in M7.
  assert (U67 : unch m6 m7 [(g + 151, g + 167)]) by (subst m7; clear - Hs1 Esp1 Esp2 Efs1 Efs2 Hp HFdef HgF; unchx).
  assert (G67 : mem_grows m6 m7) by (subst m7; growsx).
  assert (U27 : unch m2 m7 [(sp1 + 272, sp1 + 280); (F, F + 24); (g, g + 167); (sp1 + 240, sp1 + 248); (sp1 + 24, sp1 + 32)]).
  { eapply unch_trans; [eapply unch_widen; [exact U25|] | eapply unch_trans; [eapply unch_widen; [exact U56|] | eapply unch_widen; [exact U67|]]];
      intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [ eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]
        | eexists; split; [do 2 right; left; reflexivity | cbn; lia] | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
        | eexists; split; [do 4 right; left; reflexivity | cbn; lia] ]). }
  assert (G27 : mem_grows m2 m7) by (eapply mem_grows_trans; [exact G25|]; eapply mem_grows_trans; [exact G56 | exact G67]).
  pose proof (AMB_unch o buf len sp sp1 FS p g og bg0 bgl ds GG0 Hds m2 m7 _ U27 ltac:(clear W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 R10 R11 R12 R2 R1 R4; rngs) AM2) as AM7.
  pose proof AM7 as (SC7 & MC7 & TBL7 & TSH7 & OSH7 & DG7 & DSH7 & K27C7).
  pose proof (WIN_grows o sp FS p g m2 m7 G27 W2) as W7. pose proof W7 as (Wsp7 & Wo7 & WF7 & WG7).
  assert (S240' : cellN SEGS_B m7 (sp1 + 240) 8 (g + 86)).
  { eapply cellN_unch; [exact U67 | lia | cbn; lia | intros r Hr; inr Hr ltac:(cbn; flia) |].
    eapply cellN_unch; [exact U56 | lia | cbn; lia | intros r Hr; inr Hr ltac:(cbn; flia) | exact S240]. }
  assert (S24'' : cellN SEGS_B m7 (sp1 + 24) 8 (g + 4)).
  { eapply cellN_unch; [exact U67 | lia | cbn; lia | intros r Hr; inr Hr ltac:(cbn; flia) |].
    eapply cellN_unch; [exact U56 | lia | cbn; lia | intros r Hr; inr Hr ltac:(cbn; flia) | exact S24']. }
  pose proof (OSH7 0 ltac:(lia)) as SHo. rewrite Z.add_0_r in SHo.
  (* [comment removed for export] *)
  assert (I9 : getr regs7 9%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K7 9 ltac:(in_list)) |]; etransitivity; [exact (K6 9 ltac:(in_list)) | kept K5 9 D9]).
  assert (I19 : getr regs7 19%bv = Z_to_bv 64 g) by (kept K7 19 F19).
  assert (I25 : getr regs7 25%bv = Z_to_bv 64 o) by (kept K7 25 F25).
  assert (I20 : getr regs7 20%bv = Z_to_bv 64 SHA).
  { etransitivity; [exact (K7 20 ltac:(in_list)) |]. etransitivity; [exact (K6 20 ltac:(in_list)) |]. etransitivity; [exact (K5 20 ltac:(in_list)) |].
    etransitivity; [exact (K4 20 ltac:(in_list)) | kept K3 20 B20]. }
  assert (I18 : getr regs7 18%bv = Z_to_bv 64 F).
  { etransitivity; [exact (K7 18 ltac:(in_list)) |]. etransitivity; [exact (K6 18 ltac:(in_list)) |]. etransitivity; [exact (K5 18 ltac:(in_list)) |].
    etransitivity; [exact (K4 18 ltac:(in_list)) | exact C18]. }
  assert (I21 : getr regs7 21%bv = Z_to_bv 64 len).
  { etransitivity; [exact (K7 21 ltac:(in_list)) |]. etransitivity; [exact (K6 21 ltac:(in_list)) |]. etransitivity; [exact (K5 21 ltac:(in_list)) |].
    etransitivity; [exact (K4 21 ltac:(in_list)) | kept K3 21 B21]. }
  assert (I26 : getr regs7 26%bv = Z_to_bv 64 F).
  { etransitivity; [exact (K7 26 ltac:(in_list)) |]. etransitivity; [exact (K6 26 ltac:(in_list)) |]. etransitivity; [exact (K5 26 ltac:(in_list)) |].
    etransitivity; [exact (K4 26 ltac:(in_list)) | exact C26]. }
  assert (I24 : getr regs7 24%bv = Z_to_bv 64 buf).
  { etransitivity; [exact (K7 24 ltac:(in_list)) |]. etransitivity; [exact (K6 24 ltac:(in_list)) |]. etransitivity; [exact (K5 24 ltac:(in_list)) |].
    etransitivity; [exact (K4 24 ltac:(in_list)) | kept K3 24 B24]. }
  assert (I8 : getr regs7 8%bv = Z_to_bv 64 sp).
  { etransitivity; [exact (K7 8 ltac:(in_list)) |]. etransitivity; [exact (K6 8 ltac:(in_list)) |]. etransitivity; [exact (K5 8 ltac:(in_list)) |].
    etransitivity; [exact (K4 8 ltac:(in_list)) | kept K3 8 B8]. }
  assert (I2 : getr regs7 2%bv = Z_to_bv 64 sp1).
  { etransitivity; [exact (K7 2 ltac:(in_list)) |]. etransitivity; [exact (K6 2 ltac:(in_list)) |]. etransitivity; [exact (K5 2 ltac:(in_list)) |].
    etransitivity; [exact (K4 2 ltac:(in_list)) | kept K3 2 B2]. }
  assert (I4 : getr regs7 4%bv = Z_to_bv 64 TP_B).
  { etransitivity; [exact (K7 4 ltac:(in_list)) |]. etransitivity; [exact (K6 4 ltac:(in_list)) |]. etransitivity; [exact (K5 4 ltac:(in_list)) |].
    etransitivity; [exact (K4 4 ltac:(in_list)) | kept K3 4 B4]. }
  assert (K27 : keeps [3; 4] regs2 regs7).
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity|].
    eapply keeps_sub_dec; [exact K7|]; vm_compute; reflexivity. }
  assert (M07 : msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9c5c) m rom) (mkst regs7 (Z_to_bv 64 0x0a9e00) m7 rom)).
  { eapply msteps_trans; [exact M02|]. eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M4|].
    eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6 | exact M7]. }
  clear M02 M3 M4 M5 M6 M7 K3 K4 K5 K6 K7 C1 C10 C11 C18 C19 C26 E1 E10 E11 D9 D19 F19 F25 regs3 regs4 regs5 regs6.
  exists regs7, m7, p, F, g. split; [exact M07|].
  split; [exact Hp|]. split; [exact Hflp|]. split; [exact HFdef|]. split; [exact HgF|]. split; [exact GG0|].
  split; [exact I9|]. split; [exact I2|]. split; [exact I4|]. split; [exact I8|]. split; [exact I19|]. split; [exact I18|].
  split; [exact I21|]. split; [exact I25|]. split; [exact I26|]. split; [exact I24|]. split; [exact I20|].
  split; [exact H10|]. split; [rewrite H11; f_equal; lia|].
  split; [eapply keeps_trans; [exact K02 | exact K27]|].
  split; [exact AM7|]. split; [exact W7|].
  split; [eapply (SAV_unch o buf len sp sp1 FS p g og bg0 bgl GG0 m2 m7); [exact U27 | clear W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 R10 R11 R12 R2 R1 R4; rngs | exact SV2]|].
  split; [exact S240'|]. split; [exact S24''|].
  assert (HR27 : forall r, In r [(sp1 + 272, sp1 + 280); (F, F + 24); (g, g + 167); (sp1 + 240, sp1 + 248); (sp1 + 24, sp1 + 32)] -> highr r) by (clear W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 R10 R11 R12 R2 R1 R4; intros r Hr; unfold highr; inr Hr ltac:(cbn; flia)).
  assert (HR02 : forall r, In r [(sp - 400, sp); (sp1 - 256, sp1); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F + 24, F + 32); (F + 2040, F + 2048); (g, g + 256)] -> highr r)
    by (clear W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 R10 R11 R12 R2 R1 R4; intros r Hr; unfold highr; inr Hr ltac:(cbn; flia)).
  split; [eapply rt_ok_B_unch; [exact U27 | exact HR27 |]; eapply rt_ok_B_unch; [exact U02 | exact HR02 | exact RT]|].
  split; [eapply ro_ok_unchB; [exact U27 | exact HR27 |]; eapply ro_ok_unchB; [exact U02 | exact HR02 | exact RO]|].
  split; [eapply mem_u64_unch; [exact U27 | lia | lia | intros r Hr; inr Hr ltac:(slia) | exact Q2040]|].
  split; [eapply mem_byte_unch; [exact U27 | lia | intros r Hr; inr Hr ltac:(slia) | exact FL1]|].
  split; [|eapply mem_grows_trans; [exact G02 | exact G27]].
  clear W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 R10 R11 R12 R2 R1 R4; 
  eapply unch_trans; [eapply unch_widen; [exact U02|] | eapply unch_widen; [exact U27|]];
    intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [ eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]
      | eexists; split; [do 2 right; left; reflexivity | cbn; lia] | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
      | eexists; split; [do 4 right; left; reflexivity | cbn; lia] | eexists; split; [do 5 right; left; reflexivity | cbn; lia]
      | eexists; split; [do 6 right; left; reflexivity | cbn; lia] | eexists; split; [do 7 right; left; reflexivity | cbn; lia]
      | eexists; split; [do 8 right; left; reflexivity | cbn; lia] | eexists; split; [do 9 right; left; reflexivity | cbn; lia] ]).
Qed.
End S.
