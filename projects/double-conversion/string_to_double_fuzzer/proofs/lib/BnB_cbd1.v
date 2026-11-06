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
  BnModel BnMath BnMem BnDefs LibIface BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsRtLibB AsZX AsZXTac AsZXDefs BnA_lib BnA_frame BnB_lib AsMallocB BnB_ads1 BnB_ads6.
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
Record cbdE (buf len sp FS bg0 bgl : Z) : Prop := CbdE {
  c_b1 : APP buf len; c_b2 : buf + len <= HIE; c_len : 1 <= len <= 780;
  c_bg0 : 8 * bg0 <= buf < 8 * bg0 + 8; c_bgl : 8 * bgl <= buf + len - 1 < 8 * bgl + 8;
  c_sp1 : KHI + 3072 <= sp; c_sp2 : sp <= HIE; c_sp16 : exists q, sp = 16 * q;
  c_fs1 : APP FS FS_LEN; c_fs2 : FS + FS_LEN <= HIE; c_fs4 : exists q, FS = 4096 * q;
  c_bsp : buf + len <= sp - 3072 \/ sp <= buf;
  c_spFS : sp <= FS \/ FS + FS_LEN <= sp - 3072;
  c_bh : buf + len <= FS + 40 \/ FS + 48 <= buf;
  c_bfl : buf + len <= FS + 35840 \/ FS + 36352 <= buf;
  c_bfr : buf + len <= FS + 5279744 \/ FS + 5279744 + 1048576 <= buf }.

Definition csp1 (sp : Z) : Z := 32 * ((sp - 160) / 32).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (buf len sp FS bg0 bgl : Z) (ds : list Z).
Hypothesis CE : cbdE buf len sp FS bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.

#[local] Abbreviation sp1 := (csp1 sp).

#[using="buf len FS bg0 bgl CE"] Lemma csp1_facts : sp - 176 <= sp1 <= sp - 160 /\ (exists q, sp1 = 32 * q) /\ sp1 mod 16 = 0.
Proof.
  clear Hds. destruct CE as [Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dbsp DspFS Dbh Dbfl Dbfr].
  unfold csp1. subst sp. split; [lia|]. split; [eexists; reflexivity | lia].
Qed.

Ltac cgeom CE :=
  destruct CE as [Eb1 Eb2 Elen Ebg0 Ebgl Esp1 Esp2 [qs Hqs] Efs1 Efs2 [qf Hqf] Dbsp DspFS Dbh Dbfl Dbfr];
  unfold FS_LEN in *; hide Dbh; hide Dbfl; hide Dbfr; hide DspFS; hide Dbsp.

(* [comment removed for export] *)
Abbreviation b0b_pins := [(2%bv : reg, ZV 32); (9%bv : reg, ZV 32); (10%bv : reg, ZV 33); (11%bv : reg, ZV 34); (12%bv : reg, ZV 35); (13%bv : reg, ZV 36); (14%bv : reg, ZV 37)].
Abbreviation b0b_uvi := [Some (KHI + 2048, HIE - 160); Some (IMG, HIE - 1); Some (1, 780); Some (0, 18446744073709551615); Some (0, 18446744073709551615); Some (0, 18446744073709551615)].
Abbreviation b0b_kn := [KC (ZL 0) 0x12a3d8 8 (ZL 0x132740); KC (ZL 0) 0x132740 4 (ZL 1); KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL SHA)].

(* [comment removed for export] *)
#[using="CE Hds"] Lemma cbd_pro1 : forall regs m (ret f : word) (expo w4 : Z),
  getr regs 10%bv = Z_to_bv 64 buf -> getr regs 11%bv = Z_to_bv 64 len -> getr regs 12%bv = Z_to_bv 64 expo ->
  getr regs 13%bv = f -> getr regs 14%bv = Z_to_bv 64 w4 -> 0 <= expo < 2 ^ 64 -> 0 <= w4 < 2 ^ 64 ->
  getr regs 2%bv = Z_to_bv 64 sp -> getr regs 1%bv = ret -> getr regs 4%bv = Z_to_bv 64 TP_B ->
  rt_ok_B m -> ro_ok SEGS_B RO_B m -> gsh_ok_B m -> digs buf ds m -> dsh bg0 bgl m ->
  mem_def m (sp - 3072) 3072 ->
  malloc_ctx_ok_B (sp - 3072) sp FS m -> rd_u64_B m FSTLS_B FS ->
  mem_def m FS FS_LEN -> mem_def m (sh FS + FS_SHLO) (FS_SHHI - FS_SHLO) -> mem_u64 m (FS + 88) 20 -> mem_byte m (FS + 96) 0 ->
  (forall j, 0 <= j < 512 -> mem_byte m (fs_flag FS 5 j) 0) ->
  exists regs2 m2 p F g,
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9444) m rom) (mkst regs2 (Z_to_bv 64 0x0a94c4) m2 rom)
    /\ 0 <= p < 512 /\ F = FS + 5279744 + p * 2048 /\ F = 8 * (g - SHA)
    /\ getr regs2 10%bv = Z_to_bv 64 F /\ getr regs2 9%bv = Z_to_bv 64 sp1 /\ getr regs2 20%bv = Z_to_bv 64 SHA /\ getr regs2 2%bv = Z_to_bv 64 sp1
    /\ getr regs2 4%bv = Z_to_bv 64 TP_B /\ getr regs2 8%bv = Z_to_bv 64 sp /\ getr regs2 21%bv = Z_to_bv 64 expo /\ getr regs2 27%bv = Z_to_bv 64 buf
    /\ keeps [3; 4] regs regs2
    /\ mscellsB m2 /\ mem_def m2 g 256 /\ mem_def m2 F 2048 /\ mem_def m2 (sp - 3072) 3072
    /\ (cellN SEGS_B m2 (sp1 + 16) 8 len /\ cellN SEGS_B m2 (sp1 + 24) 8 (bv_unsigned f) /\ cellN SEGS_B m2 (sp1 + 8) 8 w4)
    /\ SAV sp m2 (savs regs ret)
    /\ mem_byte m2 (FS + 35840 + p) 1 /\ mem_u64 m2 (F + 2040) (FS + 35840 + p)
    /\ unch m m2 [(sp - 432, sp); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F, F + 1344); (F + 2040, F + 2048); (g, g + 256)]
    /\ mem_grows m m2.
Proof.
  intros regs m ret f expo w4 R10 R11 R12 R13 R14 Hexpo Hw4 R2 R1 R4 RT RO GSH DG DSH Dsp MCX TLS DFS DSHD L88 B96 FL0.
  pose proof csp1_facts as (Hs1 & [q1 Hq1] & Hs16).
  pose proof CE as CE0. cgeom CE.
  pose proof (u64_range ret) as W1. pose proof (u64_range f) as Wf. pose proof (u64_range (getr regs 8%bv)) as W8. pose proof (u64_range (getr regs 9%bv)) as W9.
  pose proof (u64_range (getr regs 18%bv)) as W18. pose proof (u64_range (getr regs 19%bv)) as W19.
  pose proof (u64_range (getr regs 20%bv)) as W20. pose proof (u64_range (getr regs 21%bv)) as W21.
  pose proof (u64_range (getr regs 22%bv)) as W22. pose proof (u64_range (getr regs 23%bv)) as W23.
  pose proof (u64_range (getr regs 24%bv)) as W24. pose proof (u64_range (getr regs 25%bv)) as W25.
  pose proof (u64_range (getr regs 26%bv)) as W26. pose proof (u64_range (getr regs 27%bv)) as W27.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  replace (13%bv : reg) with (Z_to_bv 5 13 : reg) in R13 by (apply bv_eq; reflexivity).
  pose proof (suarB_intro m RT RO) as [SU1 SU2]. pose proof (shcellsB_intro m RT RO) as [SC1 SC2].
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 3072, HIE)]) (@nil kcell) [KW (ZV 32) (-176) 0]) 30%nat [0x0a948c] (SCR [] []) constr:([(2%bv : reg, ZV 32)])
    [sp] constr:([Some (KHI + 3072, HIE)]) regs m rom 0x0a9444.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kwd Dsp; exact I) ltac:(exact I). zx_name regs0.
  zx_reg ZR (2%bv : reg) as A2raw. zx_reg ZR (8%bv : reg) as A8.
  assert (KA : keeps [3; 4; 10; 11; 12; 13; 14] regs regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  assert (Hland : Z.land ((sp + -160) mod 18446744073709551616) (-32 mod 18446744073709551616) = sp1).
  { rewrite (Z.mod_small (sp + -160)) by lia. unfold csp1.
    replace (-32 mod 18446744073709551616) with ((-32) mod 2 ^ 64) by reflexivity. rewrite land_align32 by lia. lia. }
  assert (A2 : getr regs0 2%bv = Z_to_bv 64 sp1) by (rewrite A2raw, Hland; reflexivity).
  assert (A9 : getr regs0 9%bv = Z_to_bv 64 sp1) by (zx_reg ZR (9%bv : reg) as X; rewrite X, Hland; reflexivity).
  clear A2raw Hland. rename ZM into MA. clear ZE ZR ZF. set (mA := wbytes _ _ _) in MA.
  assert (SVc : cellN SEGS_B mA (sp + -8) 8 (bv_unsigned ret) /\ cellN SEGS_B mA (sp + -16) 8 (bv_unsigned (getr regs 8%bv))
    /\ cellN SEGS_B mA (sp + -24) 8 (bv_unsigned (getr regs 9%bv)) /\ cellN SEGS_B mA (sp + -32) 8 (bv_unsigned (getr regs 18%bv))
    /\ cellN SEGS_B mA (sp + -40) 8 (bv_unsigned (getr regs 19%bv)) /\ cellN SEGS_B mA (sp + -48) 8 (bv_unsigned (getr regs 20%bv))
    /\ cellN SEGS_B mA (sp + -56) 8 (bv_unsigned (getr regs 21%bv)) /\ cellN SEGS_B mA (sp + -64) 8 (bv_unsigned (getr regs 22%bv))
    /\ cellN SEGS_B mA (sp + -72) 8 (bv_unsigned (getr regs 23%bv)) /\ cellN SEGS_B mA (sp + -80) 8 (bv_unsigned (getr regs 24%bv))
    /\ cellN SEGS_B mA (sp + -88) 8 (bv_unsigned (getr regs 25%bv)) /\ cellN SEGS_B mA (sp + -96) 8 (bv_unsigned (getr regs 26%bv))
    /\ cellN SEGS_B mA (sp + -104) 8 (bv_unsigned (getr regs 27%bv))).
  { subst mA. rewrite <- R1. rewrite <- R1 in W1. clear - Esp1 Esp2 W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27.
    cbv [Z.of_nat Pos.of_succ_nat Pos.succ].
    change (getr regs (Z_to_bv 5 8)) with (getr regs 8%bv). change (getr regs (Z_to_bv 5 9)) with (getr regs 9%bv).
    change (getr regs (Z_to_bv 5 18)) with (getr regs 18%bv). change (getr regs (Z_to_bv 5 19)) with (getr regs 19%bv).
    change (getr regs (Z_to_bv 5 20)) with (getr regs 20%bv). change (getr regs (Z_to_bv 5 21)) with (getr regs 21%bv).
    change (getr regs (Z_to_bv 5 22)) with (getr regs 22%bv). change (getr regs (Z_to_bv 5 23)) with (getr regs 23%bv).
    change (getr regs (Z_to_bv 5 24)) with (getr regs 24%bv). change (getr regs (Z_to_bv 5 25)) with (getr regs 25%bv).
    change (getr regs (Z_to_bv 5 26)) with (getr regs 26%bv). change (getr regs (Z_to_bv 5 27)) with (getr regs 27%bv).
    repeat split; cellx2. }
  assert (SVA : SAV sp mA (savs regs ret)).
  { destruct SVc as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12). unfold savs. clear - C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12.
    intros k Hk.
    destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]; [| | | | | | | | | | | | | lia]; cbv [nth Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul];
      [eapply cellN_eqa; [exact C0 | lia | reflexivity] | eapply cellN_eqa; [exact C1 | lia | reflexivity] | eapply cellN_eqa; [exact C2 | lia | reflexivity]
      | eapply cellN_eqa; [exact C3 | lia | reflexivity] | eapply cellN_eqa; [exact C4 | lia | reflexivity] | eapply cellN_eqa; [exact C5 | lia | reflexivity]
      | eapply cellN_eqa; [exact C6 | lia | reflexivity] | eapply cellN_eqa; [exact C7 | lia | reflexivity] | eapply cellN_eqa; [exact C8 | lia | reflexivity]
      | eapply cellN_eqa; [exact C9 | lia | reflexivity] | eapply cellN_eqa; [exact C10 | lia | reflexivity] | eapply cellN_eqa; [exact C11 | lia | reflexivity]
      | eapply cellN_eqa; [exact C12 | lia | reflexivity]]. }
  clear SVc.
  assert (U0A : unch m mA [(sp - 176, sp)]) by (subst mA; clear - Esp1 Esp2; unchx).
  assert (G0A : mem_grows m mA) by (subst mA; growsx).
  assert (HR0A : forall r, In r [(sp - 176, sp)] -> highr r) by (intros r Hr; unfold highr; inr Hr ltac:(cbn; lia)).
  assert (SU1' : cellN SEGS_B mA 0x12a3d8 8 0x132740) by (eapply cellN_low_unchB; [exact U0A | exact HR0A | lia | cbn; lia | exact SU1]).
  assert (SU2' : cellN SEGS_B mA 0x132740 4 1) by (eapply cellN_low_unchB; [exact U0A | exact HR0A | lia | cbn; lia | exact SU2]).
  assert (SC1' : cellN SEGS_B mA 0x12a380 8 0x132738) by (eapply cellN_low_unchB; [exact U0A | exact HR0A | lia | cbn; lia | exact SC1]).
  assert (SC2' : cellN SEGS_B mA 0x132738 8 SHA) by (eapply cellN_low_unchB; [exact U0A | exact HR0A | lia | cbn; lia | exact SC2]).
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ b0b_uvi) b0b_kn [KW (ZV 32) 0 160]) 30%nat [0x5b7e4] (SCR [] []) constr:(b0b_pins)
    [sp1; buf; len; expo; bv_unsigned f; w4] constr:(b0b_uvi) regs0 mA rom 0x0a948c.
  zx_use2 ZXB ltac:(zx_pins; first [exact A2 | exact A9 | kept KA 10 R10 | kept KA 11 R11 | kept KA 12 R12 | kept KA 14 R14
                          | etransitivity; [exact (KA 13 ltac:(in_list)) | rewrite Z_to_bv_bv_unsigned; exact R13]])
    ltac:(zx_lia)
    ltac:(kc1 SU1'; kc1 SU2'; kc1 SC1'; kc1 SC2'; exact I)
    ltac:(kwd (mem_def_grows _ _ _ _ G0A Dsp); exact I) ltac:(exact I). zx_name regs1.
  zx_reg ZR (1%bv : reg) as B1'. zx_reg ZR (21%bv : reg) as B20. zx_reg ZR (20%bv : reg) as B21. zx_reg ZR (27%bv : reg) as B26.
  assert (KB : keeps [2; 3; 4; 8; 9] regs0 regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into MB. clear ZE ZR ZF. set (mB := wbytes _ _ _) in MB.
  assert (SL8 : cellN SEGS_B mB (sp1 + 16) 8 len /\ cellN SEGS_B mB (sp1 + 24) 8 (bv_unsigned f) /\ cellN SEGS_B mB (sp1 + 8) 8 w4).
  { subst mB; clear - Hs1 Esp1 Esp2 Elen Wf Hw4. repeat split; cellx2. }
  assert (UAB : unch mA mB [(sp1 + 8, sp1 + 32)]) by (subst mB; clear - Hs1 Esp1 Esp2; unchx).
  assert (GAB : mem_grows mA mB) by (subst mB; growsx).
  assert (U0B : unch m mB [(sp - 176, sp)]).
  { eapply unch_trans; [exact U0A|]. eapply unch_widen; [exact UAB|]. intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(eexists; split; [left; reflexivity | cbn; lia]). }
  assert (G0B : mem_grows m mB) by (eapply mem_grows_trans; [exact G0A | exact GAB]).
  (* [comment removed for export] *)
  pose proof mallocB_5 as MS. unfold malloc_stmt_B in MS.
  pose proof fs5_consts as (EN5 & EFLO5 & EFRO5 & EFSZ5).
  destruct (MS fx regs1 mB rom (Z_to_bv 64 0x0a94c4) sp1 FS (fun _ => 0)) as (regs2 & m2 & p & M2 & K2 & Hp & _ & C10 & FL1 & Q2040 & SHZ & FR2);
    clear MS.
  { exact B1'. } { vm_compute. reflexivity. } { kept KB 2 A2. } { exact Hs16. } { unfold KHI_A, MALLOC_FR. lia. } { unfold HIEND_A. lia. }
  { unfold MALLOC_FR. eapply mem_def_grows; [exact G0B|]. eapply mem_def_sub; [exact Dsp | lia | lia]. }
  { etransitivity; [exact (KB 4 ltac:(in_list)) | kept KA 4 R4]. }
  { eapply rt_ok_B_unch; [exact U0B | exact HR0A | exact RT]. } { eapply ro_ok_unchB; [exact U0B | exact HR0A | exact RO]. }
  { eapply malloc_ctx_ok_B_unch; [exact MCX | exact U0B | exact G0B | | unfold MALLOC_FR; lia | lia].
    intros r Hr. inr Hr ltac:(cbn; unfold FS_LEN, KHI_A; lia). }
  { eapply cellN_low_unchB; [exact U0B | exact HR0A | unfold FSTLS_B; lia | unfold FSTLS_B; cbn; lia | exact TLS]. }
  { rewrite Hqf, Z.mul_comm. apply Z_mod_mult. } { unfold IMGHI_A. lia. } { unfold app_mem, LOSH_A, KHI_A, FS_LEN. lia. } { unfold HIEND_A, FS_LEN. lia. }   (* [comment removed for export] *)
  { unfold MALLOC_FR, FS_LEN. unfold hide in DspFS. lia. }
  { eapply mem_def_grows; [exact G0B | exact DFS]. } { eapply mem_def_grows; [exact G0B | exact DSHD]. }
  { eapply mem_u64_unch; [exact U0B | lia | lia | intros r Hr; inr Hr ltac:(cbn; unfold hide in DspFS; lia) | exact L88]. }
  { eapply mem_byte_unch; [exact U0B | lia | intros r Hr; inr Hr ltac:(cbn; unfold hide in DspFS; lia) | exact B96]. }
  { rewrite EN5. intros j Hj. split; [| left; reflexivity].
    eapply mem_byte_unch; [exact U0B | rewrite fs_flag5; lia | intros r Hr; inr Hr ltac:(cbn; rewrite fs_flag5; unfold hide in DspFS; lia) | exact (FL0 j Hj)]. }
  { rewrite EN5. exists 0. split; [lia | reflexivity]. }
  clear Hs16. rewrite EN5 in Hp. rewrite fs_frame5, fs_flag5 in *. rewrite EFSZ5 in *. rewrite fs_hint5 in FR2.
  apply keeps_of_cs in K2.
  pose proof (unch_of_frame _ _ _ FR2) as U12. pose proof (grows_of_frame _ _ _ FR2) as G12. clear FR2.
  set (F := FS + 5279744 + p * 2048) in *.
  assert (HFdef : F = FS + 5279744 + p * 2048) by reflexivity.
  set (g := SHA + F / 8) in *.
  assert (HgF : F = 8 * (g - SHA)) by (subst g F; rewrite Hqf; lia).
  unfold sh, SH_A in U12, SHZ. fold g in U12. fold g in SHZ.
  replace (F + 2048 - 8) with (F + 2040) in Q2040, U12 by lia.
  change (2048 / 8) with 256 in U12, SHZ. unfold MALLOC_FR in U12. replace (FS + 40 + 8) with (FS + 48) in U12 by lia.
  clearbody F g.
  (* [comment removed for export] *)
  assert (U02 : unch m m2 [(sp - 432, sp); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F, F + 1344); (F + 2040, F + 2048); (g, g + 256)]).
  { eapply unch_trans; [eapply unch_widen; [exact U0B|] | eapply unch_widen; [exact U12|]];
      intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [ eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]
        | eexists; split; [do 2 right; left; reflexivity | cbn; lia] | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
        | eexists; split; [do 4 right; left; reflexivity | cbn; lia] | eexists; split; [do 5 right; left; reflexivity | cbn; lia] ]). }
  assert (G02 : mem_grows m m2) by (eapply mem_grows_trans; [exact G0B | exact G12]).
  assert (HR12 : forall r, In r [(sp1 - 256, sp1); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F + 24, F + 32); (F + 2040, F + 2048); (g, g + 256)] -> highr r)
    by (intros r Hr; unfold highr; inr Hr ltac:(cbn; lia)).
  pose proof (mscellsB_intro m RO) as MC0.
  assert (MC2 : mscellsB m2) by (eapply mscellsB_unch; [exact U12 | exact HR12 |]; eapply mscellsB_unch; [exact U0B | exact HR0A | exact MC0]).
  assert (WG2 : mem_def m2 g 256).
  { eapply mem_def_grows; [exact G02|]. eapply mem_def_sub; [exact DSHD | unfold sh, SH_A, FS_SHLO, FS_FRAMES; rewrite Hqf in *; lia | unfold sh, SH_A, FS_SHLO, FS_SHHI, FS_FRAMES; unfold FS_LEN; rewrite Hqf in *; lia]. }
  assert (WF2 : mem_def m2 F 2048) by (eapply mem_def_grows; [exact G02|]; eapply mem_def_sub; [exact DFS | lia | lia]).
  assert (Wsp2 : mem_def m2 (sp - 3072) 3072) by (eapply mem_def_grows; [exact G02 | exact Dsp]).
  assert (SL2' : cellN SEGS_B m2 (sp1 + 16) 8 len /\ cellN SEGS_B m2 (sp1 + 24) 8 (bv_unsigned f) /\ cellN SEGS_B m2 (sp1 + 8) 8 w4).
  { destruct SL8 as (X1 & X2 & X3). repeat split; (eapply cellN_unch; [exact U12 | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | assumption]). }
  assert (SV2 : SAV sp m2 (savs regs ret)).
  { intros k Hk. eapply cellN_unch; [exact U12 | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) |].
    eapply cellN_unch; [exact UAB | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | exact (SVA k Hk)]. }
  assert (D9 : getr regs2 9%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K2 9 ltac:(in_list)) | kept KB 9 A9]).
  assert (D21 : getr regs2 20%bv = Z_to_bv 64 SHA) by (kept K2 20 B21).
  assert (D2 : getr regs2 2%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K2 2 ltac:(in_list)) | kept KB 2 A2]).
  change (getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 F) in C10.
  assert (D4 : getr regs2 4%bv = Z_to_bv 64 TP_B) by (etransitivity; [exact (K2 4 ltac:(in_list)) |]; etransitivity; [exact (KB 4 ltac:(in_list)) | kept KA 4 R4]).
  assert (D8 : getr regs2 8%bv = Z_to_bv 64 sp) by (etransitivity; [exact (K2 8 ltac:(in_list)) |]; etransitivity; [exact (KB 8 ltac:(in_list)) | exact A8]).
  assert (D20 : getr regs2 21%bv = Z_to_bv 64 expo) by (kept K2 21 B20).
  assert (D26 : getr regs2 27%bv = Z_to_bv 64 buf) by (kept K2 27 B26).
  exists regs2, m2, p, F, g.
  split; [eapply msteps_trans; [exact MA|]; eapply msteps_trans; [exact MB | exact M2]|].
  split; [exact Hp|]. split; [exact HFdef|]. split; [exact HgF|].
  split; [exact C10|]. split; [exact D9|]. split; [exact D21|]. split; [exact D2|]. split; [exact D4|]. split; [exact D8|]. split; [exact D20|]. split; [exact D26|].
  split.
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact KA|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact KB|]; vm_compute; reflexivity|].
    eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity. }
  split; [exact MC2|]. split; [exact WG2|]. split; [exact WF2|]. split; [exact Wsp2|]. split; [exact SL2'|]. split; [exact SV2|].
  split; [exact FL1|]. split; [exact Q2040|]. split; [exact U02 | exact G02].
Qed.
End S.
