(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require PropExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec FP Image RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegCall SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import SegLibBr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjS1Bytes SjS1Ghost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import A1G_mc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3. Import ST.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma asan_ctab_image : ro_bytes_b asegs 0x28140 ctab_bytes = true.
Proof. vm_compute. reflexivity. Qed.

Module A1B.
Section Bridge.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).

Definition hmH (M : word -> option byte) : Prop := AHEAP AI L RNGh st LB M /\ mem_inv asegs M.
Definition hmA (a : Z) : Prop := aclient_addr (aci AI) LB (ATOP + 4096) a.
Definition hmC (lo hi : Z) : Prop := aclient_range (aci AI) LB (ATOP + 4096) lo (hi - lo).
Definition hmR (rom : word -> option byte) : Prop := rom = seg_rom asegs.

Lemma HMC_sub : forall lo hi lo' hi', hmC lo hi -> lo <= lo' -> hi' <= hi -> hmC lo' hi'.
Proof.
  intros lo hi lo' hi' H A B. unfold hmC, aclient_range, aclient_app_range in *.
  destruct H as [[H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]] | [(b & Hb & H1 & H2) | [H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]]]].
  - left. left. lia.
  - left. right. left. exists iv. split; [exact Hiv | lia].
  - left. right. right. exists c, FA, fn. split; [exact Hb | lia].
  - right. left. exists b. split; [exact Hb | lia].
  - right. right. left. lia.
  - right. right. right. left. exists iv. split; [exact Hiv | lia].
  - right. right. right. right. exists c, FA, fn. split; [exact Hb | lia].
Qed.

Lemma HMF : forall E W M M', SP.wins_client hmC E W -> hmH M -> PIosRegs.wrel asegs M M' ->
  (forall x : word, SP.outside_wins E W (bv_unsigned x) -> M' x = M x) -> hmH M'.
Proof.
  intros E W M M' HWC [HH MI] HW HO. split; [|exact (wrel_mem_inv asegs _ _ HW MI)].
  apply (AI_frame AI L RNGh st LB M M' (map (SP.win_den E) W) HH).
  - intros x Hx. apply HO. unfold SP.outside_wins. clear -Hx. induction W as [|w W IH]; [constructor|].
    cbn [map outside] in Hx. destruct (SP.win_den E w) as [lo hi] eqn:Ew. destruct Hx as [H1 H2].
    constructor; [rewrite Ew; lia | exact (IH H2)].
  - exact (wrel_wmono asegs _ _ HW).
  - unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw).
Qed.

Hypothesis MEMCPY : asan_memcpy_stmt.

Lemma u64 : forall i, 0 <= i < 2^64 -> bv_unsigned (Z_to_bv 64 i) = i.
Proof. exact SLB.u64. Qed.

Lemma shad_div8 : forall a, shad a = ASHOFF + a / 8.
Proof. intros a. unfold shad. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma unpoisoned_of_zero : forall m lo hi sb,
  0 <= lo -> lo < hi -> hi <= 2^64 -> sb = ASHOFF + lo / 8 ->
  (forall i, 0 <= i < (hi + 7) / 8 - lo / 8 -> m (wa (sb + i)) = Some (Z_to_bv 8 0)) ->
  unpoisoned m lo hi.
Proof.
  intros m lo hi sb H0 H1 H2 Hsb HZ. split; [lia|]. split; [lia|]. intros G _ HG1 HG2.
  exists (Z_to_bv 8 0). split.
  - replace (ASHOFF + G) with (sb + (G - lo / 8)) by lia. apply HZ. Z.div_mod_to_equations. lia.
  - left. reflexivity.
Qed.

Lemma mcg_lib : forall d, SLib.summ_libH asegs (s1_gp d) hmH hmA hmC hmR MCG.
Proof.
  intros d E M rom R F fc HRom HAG HWC HHM HRF HR HK _ HZ.
  unfold hmR in HRom. subst rom. destruct HHM as [HH MI].
  cbn [MCG SP.SUMR SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know MCG_pre MCG_post TM] in *.
  rewrite (regs_ok_canon E MCG_pre_regs R HRF HR).
  unfold know_ok, MCG_pre_kn in HK.
  inversion HK as [|? ? K0 HK1]; subst. inversion HK1 as [|? ? K1 HK2]; subst. inversion HK2 as [|? ? K2 HK3]; subst.
  inversion HK3 as [|? ? K3 HK4]; subst. inversion HK4 as [|? ? K4 HK5]; subst. inversion HK5 as [|? ? K5 HK6]; subst.
  inversion HK6 as [|? ? K6 HK7]; subst. inversion HK7 as [|? ? K7 HK8]; subst. inversion HK8 as [|? ? K8 HK9]; subst.
  inversion HK9 as [|? ? K9 HK10]; subst. inversion HK10 as [|? ? K10 HK11]; subst. inversion HK11 as [|? ? K11 HK12]; subst.
  inversion HK12 as [|? ? K12 HK13]; subst. inversion HK13 as [|? ? K13 HK14]; subst. inversion HK14 as [|? ? K14 _]; subst.
  cbn [kentry_ok MGV edenot] in K0, K1, K2, K3, K4.
  (* [comment removed for export] *)
  set (RA := ev E 0) in *. set (SP := ev E 1) in *. set (TAB := ev E 16) in *. set (SHD := ev E 17) in *.
  set (sp := bv_unsigned SP) in *. set (T := bv_unsigned TAB) in *.
  assert (RT : 0 <= T < 2^64) by apply SLB.urange. assert (RS : 0 <= sp < 2^64) by apply SLB.urange.
  destruct K3 as [K3a K3b]. unfold bv_modulus in K3b.
  cbn [MG_dst edenot] in *.
  (* [comment removed for export] *)
  assert (HSHD : 8 * bv_unsigned SHD = T - 8192 + 8 * MG_SHOFF).
  { cbn [kentry_ok] in K5, K6. cbn [edenot MGV] in K5, K6. fold SHD TAB T in K5, K6.
    rewrite alu_sub in K5. unfold v_sub in K5. rewrite Z_to_bv_unsigned, bv_wrap64_mod in K5. cbn [mul_div] in K5.
    rewrite bv_mul_unsigned, Z_to_bv_unsigned in K5. unfold bv_wrap in K5. change (bv_modulus 64) with (2^64) in K5.
    rewrite (Z.mod_small 8 (2^64)) in K5 by lia. fold T in K5.
    rewrite (Z.mod_small (8 * bv_unsigned SHD) (2^64)) in K5 by lia. unfold MG_SHOFF in *.
    destruct K5 as [K5a K5b]. assert (Hc : (8 * bv_unsigned SHD - T) mod 2^64 = 8 * 2147450880 - 8192) by lia.
    rewrite Zmod_eq_full in Hc by lia.
    destruct (Z.lt_ge_cases (8 * bv_unsigned SHD - T) 0) as [Hn|Hn].
    - assert (Hq : (8 * bv_unsigned SHD - T) / 2^64 = -1).
      { symmetry. apply Z.div_unique with (2^64 + (8 * bv_unsigned SHD - T)); [left|]; lia. }
      rewrite Hq in Hc. clear Hq. lia.
    - assert (Hq : (8 * bv_unsigned SHD - T) / 2^64 = 0) by (apply Z.div_small; lia). rewrite Hq in Hc. clear Hq. lia. }
  (* [comment removed for export] *)
  cbn [kentry_ok edenot MGV] in K3a, K3b, K4.
  assert (HT16 : T mod 16 = 0) by exact K3b.
  assert (HTSP : 400 <= T - sp <= 8192).
  { rewrite alu_sub in K4. unfold v_sub in K4. rewrite Z_to_bv_unsigned, bv_wrap64_mod in K4. fold SP sp TAB T in K4.
    destruct (Z.lt_ge_cases (T - sp) 0) as [Hn|Hn].
    - rewrite Zmod_eq_full in K4 by lia.
      assert (Hq : (T - sp) / 2^64 = -1) by (symmetry; apply Z.div_unique with (2^64 + (T - sp)); [left|]; lia).
      rewrite Hq in K4. lia.
    - rewrite Z.mod_small in K4 by lia. lia. }
  assert (HA0 : bv_unsigned (edenot E MG_dst) = T - 400).
  { unfold MG_dst. cbn [edenot MGV]. rewrite alu_add. unfold v_add. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold TAB T.
    rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
  (* [comment removed for export] *)
  pose proof (SLB.kn_stk asegs E M _ _ _ K7 K8) as STK. cbn [edenot MGV] in STK. fold SP sp in STK.
  replace (sp + -2224 + bv_unsigned (Z_to_bv 64 2224)) with sp in STK by (rewrite u64 by lia; lia).
  replace (sp + -2224) with (sp - 2224) in STK by lia.
  (* [comment removed for export] *)
  destruct (AI_rtcells AI L RNGh st LB M HH) as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
  (* [comment removed for export] *)
  assert (SRCB : bytes_at asegs M 0x28140 ctab_bytes).
  { apply ro_bytes_at; [exact MI | lia | unfold ctab_bytes; rewrite length_map, length_seq; lia |].
    apply ro_bytes_b_sound. exact asan_ctab_image. }
  assert (SRCL : length ctab_bytes = Z.to_nat (bv_unsigned (Z_to_bv 64 256))) by (unfold ctab_bytes; rewrite length_map, length_seq, u64 by lia; reflexivity).
  (* [comment removed for export] *)
  destruct (SLB.kn_rw_CB asegs E M _ _ _ K9 K10) as (junk & DST). cbn [edenot MGV] in DST. fold TAB T in DST.
  rewrite u64 in DST by lia. replace (T + -400) with (T - 400) in DST by lia.
  (* [comment removed for export] *)
  assert (UNS : unpoisoned M 0x28140 (0x28140 + 256)).
  { apply (unpoisoned_of_zero M 0x28140 (0x28140 + 256) 0x7fffd028); [lia | lia | lia | unfold ASHOFF; reflexivity |].
    intros i Hi. pose proof (SLB.kn_zero_bytes asegs E M _ _ _ K11 i) as Z0. cbn [edenot] in Z0. rewrite !u64 in Z0 by lia.
    rewrite Z.add_0_l in Z0. apply Z0. lia. }
  assert (UND : unpoisoned M (T - 400) (T - 400 + 256)).
  { apply (unpoisoned_of_zero M (T - 400) (T - 400 + 256) (bv_unsigned SHD + 974)); [lia | lia | lia | |].
    - unfold ASHOFF, MG_SHOFF in *. Z.div_mod_to_equations. lia.
    - intros i Hi. pose proof (SLB.kn_zero_bytes asegs E M _ _ _ K13 i) as Z0. cbn [edenot MGV] in Z0. fold SHD in Z0.
      rewrite u64 in Z0 by lia. apply Z0. Z.div_mod_to_equations. lia. }
  assert (WRS : wr_at asegs M (shad 0x28140) (shad (0x28140 + 256) - shad 0x28140)).
  { pose proof (SLB.kn_wr_at asegs E M _ _ _ K12) as W. cbn [edenot] in W. rewrite !u64 in W by lia. rewrite Z.add_0_l in W.
    rewrite !shad_div8. unfold ASHOFF. replace (2147450880 + (0x28140 + 256) / 8 - (2147450880 + 0x28140 / 8)) with 32 by reflexivity.
    replace (2147450880 + 0x28140 / 8) with 2147471400 by reflexivity. exact W. }
  (* [comment removed for export] *)
  set (RLO2 := 64 * ((T - 400) / 64)).
  assert (HR2 : T - 463 <= RLO2 <= T - 400 /\ RLO2 mod 64 = 0).
  { split; [unfold RLO2; Z.div_mod_to_equations; lia|]. unfold RLO2. rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (WRD : wr_at asegs M (shad RLO2) (shad (RLO2 + 320) - shad RLO2)).
  { pose proof (SLB.kn_wr_at asegs E M _ _ _ K14) as W. cbn [edenot MGV] in W. fold SHD in W. rewrite u64 in W by lia. rewrite Z.add_0_r in W.
    rewrite !shad_div8. destruct W as (W1 & W2 & W3).
    assert (E1 : (RLO2 + 320) / 8 = RLO2 / 8 + 40) by (replace (RLO2 + 320) with (40 * 8 + RLO2) by lia; rewrite Z.div_add_l by lia; lia).
    rewrite E1. replace (ASHOFF + (RLO2 / 8 + 40) - (ASHOFF + RLO2 / 8)) with 40 by lia.
    assert (E2 : bv_unsigned SHD <= ASHOFF + RLO2 / 8 /\ ASHOFF + RLO2 / 8 + 40 <= bv_unsigned SHD + 1024)
      by (unfold ASHOFF, MG_SHOFF in *; Z.div_mod_to_equations; lia).
    split; [unfold ASHOFF in *; lia|]. split; [lia|]. intros i Hi.
    replace (ASHOFF + RLO2 / 8 + i) with (bv_unsigned SHD + (ASHOFF + RLO2 / 8 - bv_unsigned SHD + i)) by lia. apply W3. lia. }
  (* [comment removed for export] *)
  assert (RW : forall w lo len, In w MCG_A -> fst (SX.awin_den E w) <= lo -> lo + len <= snd (SX.awin_den E w) -> 0 <= len ->
                 ExecF.rng (SX.fp_of (Some MCG_A) E) lo len).
  { intros w lo len Hw H1 H2 H3. pose proof (SLib.rng_fp_of MCG_A E w HAG Hw) as R0. eapply ExecF.rng_sub; [exact R0 | lia | lia]. }
  assert (AW : forall b k n, In (b, k, n) MCG_A -> SX.awin_den E (b, k, n) = (bv_unsigned (edenot E b) + k, bv_unsigned (edenot E b) + k + bv_unsigned (edenot E n)))
    by (intros; reflexivity).
  assert (RIMG : ExecF.rng (SX.fp_of (Some MCG_A) E) 0x10000 0x655000).
  { apply (RW (ELit 0, 0x10000, ELit 0x655000)); [cbn; tauto | cbn [SX.awin_den edenot fst snd]; rewrite !u64 by lia; lia .. | lia]. }
  assert (RSTK : ExecF.rng (SX.fp_of (Some MCG_A) E) (sp - 2224) (sp - (sp - 2224))).
  { apply (RW (MGV 1, -2224, ELit 2224)); [cbn; tauto | cbn [SX.awin_den edenot MGV fst snd]; fold SP sp; rewrite ?u64 by lia; lia .. | lia]. }
  assert (RSRC : ExecF.rng (SX.fp_of (Some MCG_A) E) 0x28140 256).
  { apply (RW (ELit 0, 0x10000, ELit 0x655000)); [cbn; tauto | cbn [SX.awin_den edenot fst snd]; rewrite !u64 by lia; lia .. | lia]. }
  assert (RDST : ExecF.rng (SX.fp_of (Some MCG_A) E) (T - 400) 256).
  { apply (RW (MGV 16, -400, ELit 256)); [cbn; tauto | cbn [SX.awin_den edenot MGV fst snd]; fold TAB T; rewrite ?u64 by lia; lia .. | lia]. }
  assert (RSH1 : ExecF.rng (SX.fp_of (Some MCG_A) E) (shad 0x28140) (shad (0x28140 + 256) - shad 0x28140)).
  { rewrite !shad_div8. unfold ASHOFF. apply (RW (ELit 0, 0x7fffd028, ELit 32)); [cbn; tauto | cbn [SX.awin_den edenot fst snd]; rewrite !u64 by lia; lia .. | lia]. }
  assert (RSH2 : ExecF.rng (SX.fp_of (Some MCG_A) E) (shad RLO2) (shad (RLO2 + 320) - shad RLO2)).
  { rewrite !shad_div8.
    assert (E1 : (RLO2 + 320) / 8 = RLO2 / 8 + 40) by (replace (RLO2 + 320) with (40 * 8 + RLO2) by lia; rewrite Z.div_add_l by lia; lia).
    assert (E2 : bv_unsigned SHD <= ASHOFF + RLO2 / 8 /\ ASHOFF + RLO2 / 8 + 40 <= bv_unsigned SHD + 1024)
      by (unfold ASHOFF, MG_SHOFF in *; Z.div_mod_to_equations; lia).
    apply (RW (MGV 17, 0, ELit 1024)); [cbn; tauto | cbn [SX.awin_den edenot MGV fst snd]; fold SHD; rewrite ?u64 by lia; lia .. | lia]. }
  (* [comment removed for export] *)
  pose proof (MEMCPY (SX.fp_of (Some MCG_A) E) (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 18) (ev E 19) (ev E 20) (ev E 4) (ev E 5)
                (edenot E MG_dst) (Z_to_bv 64 0x28140) (Z_to_bv 64 256) (ev E 21) (ev E 22) (ev E 23) (ev E 24) (ev E 25)
                (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15)
                (ev E 26) (ev E 27) (ev E 28) (ev E 29) F fc M (sp - 2224) ctab_bytes junk 0x28140 (0x28140 + 256) RLO2 (RLO2 + 320)) as RUN.
  cbv zeta in RUN. rewrite HA0 in RUN. rewrite !u64 in RUN by lia. fold SP sp in RUN.
  specialize (RUN MI STK ltac:(unfold AMEMCPY_STACK; lia) ltac:(unfold KHIGH; lia) GOT RIC SHB INI LAY REAL SRCB SRCL DST).
  specialize (RUN ltac:(lia) ltac:(unfold AMEMCPY_STACK; lia) ltac:(lia)).
  specialize (RUN ltac:(unfold app_blk, KLOW, KHIGH, KEND; lia) ltac:(unfold app_blk, KLOW, KHIGH, KEND; lia) UNS UND ltac:(lia)).
  specialize (RUN ltac:(unfold KEND; lia) ltac:(unfold KEND; lia) WRS WRD RIMG RSTK RSRC RDST RSH1 RSH2).
  (* [comment removed for export] *)
  destruct RUN as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel asegs _ _ (ExecF.mstepsF_msteps asegs _ _ _ Hrun)) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & STK' & DST' & SRC').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact Hrun|].
  set (E' := SLB.env_ext E 30 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 30)%nat -> ev E' v = ev E v) by (intros v Hv; apply SLB.env_ext_lt; exact Hv).
  exists MCG_post, E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (edenot E MG_dst) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  (* [comment removed for export] *)
  assert (DEF : forall i, 0 <= i < 256 -> m' (wa (T - 400 + i)) <> None).
  { intros i Hi. apply (SC.wrel_grows asegs _ _ HW). pose proof (SLB.kn_defined asegs E M _ _ _ K10 i) as D0.
    cbn [edenot MGV] in D0. fold TAB T in D0. rewrite u64 in D0 by lia. replace (T + -400 + i) with (T - 400 + i) in D0 by lia. exact (D0 Hi). }
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [MCG_post t_pc]. f_equal.
    assert (Hra : RA = Z_to_bv 64 0x976c8) by (apply bv_eq; rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); lia).
    change (ret_pc RA = Z_to_bv 64 0x976c8). rewrite Hra. apply ret_pc_even; lia. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor]. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off MGV edenot].
    rewrite (EQ 16%nat ltac:(lia)). fold TAB T. rewrite u64 by lia.
    split; [unfold flat, estart, elenZ; cbn [a_base a_off MGV edenot]; rewrite ?(EQ 16%nat ltac:(lia)); fold TAB T; rewrite ?u64 by lia; lia|].
    intros i Hi. replace (T + -400 + i) with (T - 400 + i) by lia. exact (DEF i Hi). }
  split.
  { constructor; [|constructor]. cbn [g_id g_args map MGV edenot]. rewrite (EQ 16%nat ltac:(lia)). fold TAB.
    cbn [s1_gp g_tab]. fold T. split; [lia|].
    destruct DST' as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. rewrite HA0 in B.
    assert (LT : Z.of_nat (length ctab_bytes) = 256) by (unfold ctab_bytes; rewrite length_map, length_seq; reflexivity).
    intros i Hi. rewrite LT in Hi.
    exact (SLB.mbytes_of_bytes_at asegs m' (T - 400) ctab_bytes B ltac:(rewrite LT; exact DEF) i ltac:(rewrite LT; exact Hi)). }
  split; [apply SLB.gagree_ext; cbn [MCG SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  assert (EQW : map (SP.win_den E) MCG_W = [(sp - 2224, sp); (T - 400, T - 400 + 256)]).
  { cbn [map MCG_W SP.win_den edenot MGV]. fold SP sp TAB T. rewrite !u64 by lia.
    replace (sp + -2224) with (sp - 2224) by lia. replace (sp - 2224 + 2224) with sp by lia. replace (T + -400) with (T - 400) by lia.
    reflexivity. }
  rewrite HA0 in MU. rewrite u64 in MU by lia. fold SP sp in MU.
  split.
  { split; [|exact MI'].
    apply (AI_frame AI L RNGh st LB M m' [(sp - 2224, sp); (T - 400, T - 400 + 256)] HH MU WM).
    rewrite <- EQW. unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw). }
  cbn [SP.frame_ok MCG SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. rewrite EQW. exact MU.
Qed.

Theorem mcg_ok : forall d, SP.summ_okH asegs (s1_gp d) hmH hmA hmC hmR MCG.
Proof. intros d. apply SLib.summ_of_libH. exact (mcg_lib d). Qed.
End Bridge.
End A1B.
Print Assumptions A1B.mcg_ok.
