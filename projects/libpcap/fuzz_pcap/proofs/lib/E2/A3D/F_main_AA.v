(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.CallKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.ImgAny.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require I_read. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_read.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_target_runA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvFactsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_target_runA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AsanHexZero.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ _ _ => apply implMG_from_evtF end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition img_lit (A : Z) (n : nat) : list byte := match image_bytes asegs A n with Some bs => bs | None => [] end.
Definition MSG_OOM_bytes : list byte := img_lit MSG_OOM 19.
Definition MSG_SHORT_HDR_bytes : list byte := img_lit MSG_SHORT_HDR 31.
Definition MSG_CFG_OVERRUN_bytes : list byte := img_lit MSG_CFG_OVERRUN 31.

Lemma MSG_OOM_ok : ro_bytes_b asegs MSG_OOM MSG_OOM_bytes = true /\ map bv_unsigned MSG_OOM_bytes = List.concat pieces_oom /\ length MSG_OOM_bytes = 19%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma MSG_SHORT_HDR_ok : ro_bytes_b asegs MSG_SHORT_HDR MSG_SHORT_HDR_bytes = true /\ map bv_unsigned MSG_SHORT_HDR_bytes = List.concat pieces_short_hdr /\ length MSG_SHORT_HDR_bytes = 31%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma MSG_CFG_OVERRUN_ok : ro_bytes_b asegs MSG_CFG_OVERRUN MSG_CFG_OVERRUN_bytes = true /\ map bv_unsigned MSG_CFG_OVERRUN_bytes = List.concat pieces_cfg_overrun /\ length MSG_CFG_OVERRUN_bytes = 31%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma lit_bytes_at : forall m A bs, mem_inv asegs m -> ro_bytes_b asegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z -> bytes_at asegs m A bs.
Proof. intros m A bs MI RB HA HB. apply ro_bytes_at; [exact MI | exact HA | exact HB |]. apply ro_bytes_b_sound. exact RB. Qed.

Lemma cap_double_ok : forall cap j, (cap = 65536 * 2 ^ j)%Z -> (0 <= j)%Z -> (cap < 67108864)%Z ->
  (cap * 2 = 65536 * 2 ^ (j + 1))%Z /\ (cap * 2 <= 67108864)%Z.
Proof.
  intros cap j -> Hj Hc. split. { rewrite Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z. lia. }
  assert (Hj10 : (2 ^ j < 2 ^ 10)%Z) by (change (2 ^ 10)%Z with 1024%Z; lia).
  apply Z.pow_lt_mono_r_iff in Hj10; [|lia|lia].
  assert (2 ^ (j + 1) <= 2 ^ 10)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 10)%Z with 1024%Z in H. rewrite Z.pow_add_r in H by lia. change (2 ^ 1)%Z with 2%Z in H. lia.
Qed.

Lemma ltu_cond_true : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.
Lemma ltu_cond_false : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltz_cond_false : forall x, (0 <= x < 2^63)%Z -> bv_lts (Z_to_bv 64 x) z64 = false.
Proof. intros. rewrite bv_lts_zero_r, unsigned_lit by lia. apply Z.leb_gt. lia. Qed.
Lemma ltz_cond_m1 : bv_lts (Z_to_bv 64 (-1)) z64 = true.
Proof. reflexivity. Qed.
Lemma neq_cond : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
Proof. intros x y Hx Hy Hn. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hn. Qed.
Lemma eq_cond : forall x, negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 x)) = false.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma beq_cond : forall x, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 x) = true.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma bne_cond_false : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy Hn. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma forall_range : forall (f : Z -> bool) (n : nat),
  forallb f (map Z.of_nat (seq 0 n)) = true -> forall z, (0 <= z < Z.of_nat n)%Z -> f z = true.
Proof.
  intros f n Hf z Hz. rewrite forallb_forall in Hf. apply Hf. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Lemma hdr_hi : forall c1 : byte,
  Z.shiftr ((Z.shiftl (bv_unsigned (sxb c1)) 57) mod 18446744073709551616) 49 = ((bv_unsigned c1) mod 128 * 256)%Z.
Proof.
  intros c1. unfold sxb. rewrite unsigned_lit_wrap. unfold bv_signed.
  pose proof (bv_unsigned_in_range 8 c1) as R. unfold bv_modulus in R. cbn in R.
  generalize dependent R. generalize (bv_unsigned c1). intros u R.
  pose proof (forall_range (fun u => Z.eqb (Z.shiftr ((Z.shiftl ((bv_swrap 8 u) mod 2^64) 57) mod 18446744073709551616) 49) (u mod 128 * 256)) 256 ltac:(vm_cast_no_check (eq_refl true)) u ltac:(cbn; lia)) as E.   (* [comment removed for export] *)
  apply Z.eqb_eq in E. exact E.
Qed.

Lemma lor_disjoint8 : forall m u0, (0 <= m < 128)%Z -> (0 <= u0 < 256)%Z -> Z.lor (m * 256) u0 = (m * 256 + u0)%Z.
Proof.
  intros m u0 Hm Hu.
  pose proof (forall_range (fun m => forallb (fun u0 => Z.eqb (Z.lor (m * 256) u0) (m * 256 + u0)) (map Z.of_nat (seq 0 256))) 128 ltac:(vm_cast_no_check (eq_refl true)) m ltac:(cbn; lia)) as E.   (* [comment removed for export] *)
  cbn beta in E. pose proof (forall_range _ 256 E u0 ltac:(cbn; lia)) as E2. apply Z.eqb_eq in E2. exact E2.
Qed.

Lemma land_7fff : forall u0 u1, (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> Z.land (u0 + u1 * 256) 32767 = (u1 mod 128 * 256 + u0)%Z.
Proof.
  intros. change 32767%Z with (2^15 - 1)%Z. rewrite zb_land_mask by lia. change (2^15)%Z with 32768%Z.
  rewrite (Z.div_mod u1 128) at 1 by lia.
  replace (u0 + (128 * (u1 / 128) + u1 mod 128) * 256)%Z with ((u1 mod 128 * 256 + u0) + (u1 / 128) * 32768)%Z by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound u1 128). lia.
Qed.

Lemma testbit15 : forall u0 u1, (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> Z.testbit (u0 + u1 * 256) 15 = (128 <=? u1)%Z.
Proof.
  intros. destruct (Z.leb_spec 128 u1).
  - apply Z.testbit_true; [lia|]. change (2^15)%Z with 32768%Z.
    replace ((u0 + u1 * 256) / 32768)%Z with 1%Z; [reflexivity|]. Z.div_mod_to_equations. lia.
  - apply Z.testbit_false; [lia|]. change (2^15)%Z with 32768%Z.
    replace ((u0 + u1 * 256) / 32768)%Z with 0%Z; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

Lemma sxb_ltz : forall c1 : byte, bv_lts (sxb c1) (Z_to_bv 64 0) = (128 <=? bv_unsigned c1)%Z.
Proof.
  intros c1. rewrite bv_lts_zero_r. unfold sxb. rewrite unsigned_lit_wrap. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range 8 c1) as R. unfold bv_modulus in R. cbn in R.
  change (Z.of_N 8) with 8%Z. change (2^8)%Z with 256%Z. cbn [Z.div Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  destruct (Z.leb_spec 128 (bv_unsigned c1)).
  - apply Z.leb_le. Z.div_mod_to_equations. lia.
  - apply Z.leb_gt. Z.div_mod_to_equations. lia.
Qed.


Definition MAIN_STACK : Z := TARGET_RUN_STACK + 0x1000.    (* [comment removed for export] *)
Definition RA_MAIN : Z := 0x940c4.                          (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma rw_bytes_b_zero_w : forall segs n A,
  (forall i, (0 <= i < Z.of_nat n)%Z -> seg_rom segs (wa (A + i)) = Some (Z_to_bv 8 0) /\ wview segs (fun _ => None) (wa (A + i)) <> None) ->
  rw_bytes_b segs A (repeat (Z_to_bv 8 0) n) = true.
Proof.
  intros segs n. induction n as [|n IH]; intros A H; cbn [repeat rw_bytes_b]; [reflexivity|].
  destruct (H 0%Z ltac:(lia)) as [E1 E2]. rewrite Z.add_0_r in E1, E2. rewrite E1.
  destruct (wview segs (fun _ => None) (wa A)) as [w|] eqn:EW; [|congruence].
  replace (bv_eqb (Z_to_bv 8 0) (Z_to_bv 8 0)) with true by reflexivity. cbn [andb].
  apply IH. intros i Hi. replace (A + 1 + i)%Z with (A + (1 + i))%Z by lia. apply H. lia.
Qed.
Local Lemma asegs_zero_rs : forall a, (0x5d0c50 <= a < 0x5d0c50 + 65536)%Z ->
  seg_rom asegs (wa a) = Some (Z_to_bv 8 0) /\ wview asegs (fun _ => None) (wa a) <> None.
Proof.
  intros a Ha.
  assert (ZW : zwin Asan_seg_bytes_003 (Uint63.of_Z 10827936) (Uint63.of_Z 131072) = true) by (vm_cast_no_check (eq_refl true)).
  assert (HB : hex_byte_at Asan_seg_bytes_003 (Z.to_N (a - 0xa7000)) = Some (Z_to_bv 8 0)).
  { apply (zwin_hex_byte_at _ _ _ _ ZW).
    - change (Uint63.to_Z (Uint63.of_Z 131072)) with 131072%Z. change (Uint63.to_Z PrimString.max_length) with 16777211%Z. lia.
    - change (Uint63.to_Z (Uint63.of_Z 10827936)) with 10827936%Z. lia.
    - change (Uint63.to_Z (Uint63.of_Z 10827936)) with 10827936%Z. change (Uint63.to_Z (Uint63.of_Z 131072)) with 131072%Z. lia. }
  assert (LEN : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5619712%N) by reflexivity.
  assert (F : find_segment asegs a 1 = Some Asan_segment_003).
  { unfold asegs, Asan.M.loaded_segments, Asan_loaded_segments.
    cbn [find_segment Asan_segment_000 Asan_segment_001 Asan_segment_002 Asan_segment_003 seg_base seg_size Z.of_N].
    repeat match goal with |- context [Z.leb ?x ?y] =>
      first [ replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
            | replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia) ] end.
    reflexivity. }
  assert (HSB : segment_byte_at (seg_bytes Asan_segment_003) (Z.to_N (a - 0xa7000)) = Some (Z_to_bv 8 0)).
  { cbn [seg_bytes Asan_segment_003 segment_byte_at]. rewrite LEN.
    replace (Z.to_N (a - 0xa7000) <? 5619712)%N with true by (symmetry; apply N.ltb_lt; lia). exact HB. }
  assert (SEGB : Z.of_N (seg_base Asan_segment_003) = 0xa7000%Z) by reflexivity.
  split.
  - unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1%Z. rewrite F.
    replace (seg_readable Asan_segment_003) with true by reflexivity.
    rewrite SEGB. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite HSB. reflexivity.
  - unfold wview. rewrite wa_unsigned by lia. rewrite F.
    replace (seg_writable Asan_segment_003) with true by reflexivity.
    rewrite SEGB. rewrite HSB. discriminate.
Qed.
Local Lemma RS_ok_pre : rw_bytes_b asegs 0x5d0c50 (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) = true.
Proof. apply rw_bytes_b_zero_w. intros i Hi. rewrite Z2Nat.id in Hi by lia. apply asegs_zero_rs. lia. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Main.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  (* [comment removed for export] *)
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation USP := (bv_unsigned sp0).
  Notation SBK := (build_stack_bytes a_phdrs sp0 argv envp uid hw rnd).
  Variables (L : alayout) (LO : Z).
  (* [comment removed for export] *)
  Variable AT_EXIT : Z -> PS -> footprint -> machine_state -> Prop.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GD : gia_drv_laws GIOA USP SBK.
  Hypothesis MALLOC : malloc_stmt_d HO GIOA.
  Hypothesis FREE : free_stmt_d HO GIOA.
  Hypothesis EPR_USAGE : eprintf_s_stmt_o GIOA FMT_USAGE 16 pieces_usage.
  Hypothesis EPR_OPEN : eprintf_s_stmt_o GIOA FMT_CANNOT_OPEN 20 pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt_o GIOA FMT_READ_ERROR 22 pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt_o GIOA FMT_TOO_BIG 32 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt_o GIOA.
  Hypothesis SITE_RS : sites SiteReadStage = READ_STAGE.
  Hypothesis TRUN : target_run_stmt_o HO FO sites GIOA TP.       (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis LO_lo : (ATOP + 4096 <= LO)%Z.
  Hypothesis LO_hi : (LO + MAIN_STACK <= USP - 128)%Z.
  Hypothesis USP16 : (USP mod 16 = 0)%Z.
  Hypothesis TOP_lo : (USP - 160 <= al_top L)%Z.
  Hypothesis TOP47 : (al_top L <= 2^47)%Z.
  Hypothesis USP47 : (USP + Z.of_nat (length SBK) <= 2^47)%Z.
  Hypothesis TRD : traces_drv L.
  Hypothesis TRF : traces_fuzz_one TP L RA_FUZZ [].

  (* [comment removed for export] *)
  Definition rngs (RNG : footprint) : Prop :=
    rng RNG LO (al_top L - LO) /\ rng RNG LO (USP - LO) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG.
  #[using="Type"] Lemma rngs_le : forall RNG RNG', fp_le RNG RNG' -> rngs RNG -> rngs RNG'.
  Proof.
    intros RNG RNG' FP (A & B & C & D & E). unfold rngs.
    split; [exact (rng_fp_le _ _ _ _ FP A)|]. split; [exact (rng_fp_le _ _ _ _ FP B)|]. split; [exact (rng_fp_le _ _ _ _ FP C)|].
    split; [exact (rng_fp_le _ _ _ _ FP D)| exact (rng_fp_le _ _ _ _ FP E)].
  Qed.

  Hypothesis AT_EXIT_I : forall (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (s : PS) (CL FB : list cblk) (code : Z),
    GIOA L RNG s CL FB [] m -> mem_inv asegs m -> stk asegs m LO (bv_unsigned sp) -> (LO + MAIN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= USP - 48)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> rngs RNG ->
    AT_EXIT code s RNG
      (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EXIT_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Let drv_lit_mobjA := drv_lit_mobjA FO GIOA fflagA USP SBK GL GD.
  Let drv_stack_writes := drv_stack_writes FO GIOA fflagA GL.
  Let drv_keeps := drv_keeps FO GIOA fflagA GL.
  Let block_mobjA := block_mobjA FO GIOA fflagA GL.

  (* [comment removed for export] *)
  #[using="rc sp0 argv envp uid hw rnd"] Lemma slack_trunc : forall (m : mem) (P : Z) (str slackF : list byte) (B : Z),
    bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slackF) -> ((- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slackF))%Z ->
    (P + Z.of_nat (length str) + 1 <= B)%Z -> (B mod 8 = 0)%Z ->
    exists slack, bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) /\ ((- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z
                  /\ (P + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= B)%Z.
  Proof.
    intros m P str slackF B HB HS HP HB8.
    set (k := Z.to_nat ((- (P + Z.of_nat (length str) + 1)) mod 8)).
    assert (K8 : (0 <= (- (P + Z.of_nat (length str) + 1)) mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
    assert (LK : length (firstn k slackF) = k) by (rewrite length_firstn; subst k; lia).
    exists (firstn k slackF). split; [| split].
    - rewrite <- (firstn_skipn k slackF) in HB.
      replace (str ++ Z_to_bv 8 0 :: firstn k slackF ++ skipn k slackF) with ((str ++ Z_to_bv 8 0 :: firstn k slackF) ++ skipn k slackF) in HB
        by (rewrite <- app_assoc; reflexivity).
      exact (proj1 (proj1 (bytes_at_app asegs m P _ _) HB)).
    - rewrite LK. subst k. rewrite Z2Nat.id by lia. lia.
    - rewrite LK. subst k. rewrite Z2Nat.id by lia. clear - HP HB8 K8. Z.div_mod_to_equations. lia.
  Qed.

  #[using="rc argv envp uid hw rnd LO LO_lo LO_hi USP47"] Lemma usp_facts : (0x7fff7f800000 + 100000 <= USP <= 2^47)%Z.
  Proof. pose proof (Nat2Z.is_nonneg (length SBK)) as N0. pose proof LO_lo as A. pose proof LO_hi as B. pose proof USP47 as C. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in B. atop_facts. lia. Qed.

  (* [comment removed for export] *)
  #[using="rc sp0 argv envp uid hw rnd"] Lemma unw_main : forall RNG (m : mem) PC (sp s0 ra : word) X,
    (bv_unsigned s0 <= bv_unsigned sp)%Z -> ra = Z_to_bv 64 X -> (ACLIENT_LO <= X < ACLIENT_HI)%Z -> ~ (ACLIENT_LO <= PC < ACLIENT_HI)%Z ->
    In [PC; X] (al_U L) -> In [PC] (al_U L) -> rng RNG LO (al_top L - LO) -> (bv_unsigned sp < 2^47)%Z ->
    unw_okA L RNG m LO PC sp s0 ra.
  Proof.
    intros RNG m PC sp s0 ra X HS0 -> HX HPC HU2 HU1 HR HSP.
    assert (EX : bv_unsigned (Z_to_bv 64 X) = X) by (apply unsigned_lit; unfold ACLIENT_LO, ACLIENT_HI in HX; lia).
    destruct (Z_lt_le_dec (bv_unsigned sp + 16) (al_top L)) as [LT|GE].
    - eapply unw_of_ucaller with (trC := @nil Z) (d := 0%nat);
        [ eapply (ucaller_data 0%nat _ _ _ _ _ X); [exact HS0 | reflexivity | exact HX | lia] | exact HPC | exact LT | rewrite EX; exact HU2 | exact HR ].
    - unfold unw_okA. rewrite EX. split; [exists (@nil Z); right; split; [exact GE| split; [exact HSP| exact HU1]]|].
      unfold ACLIENT_LO, ACLIENT_HI in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac name_spm :=
    remember (Z_to_bv 64 (USP + -128)) as spm eqn:Espm;
    assert (Hspm : bv_unsigned spm = (USP + -128)%Z) by (rewrite Espm; apply unsigned_lit; pose proof usp_facts; lia).
  Ltac unname_spm := match goal with Hs : bv_unsigned ?s = (USP + -128)%Z |- _ => is_var s; try rewrite Hs in *; subst s; clear Hs end.
  Ltac aln16 := generalize USP16; clear; intros; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Ltac std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5 :=
    pose proof usp_facts as USPF__;
    split; [exact G|]; split; [rewrite Hspm; exact ST|]; split; [exact LO_lo|];
    split; [generalize LO_hi; unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK, MALLOC_STACK, FREE_STACK; rewrite Hspm; lia|];
    split; [rewrite Hspm; split; [lia| exact TOP47]|]; split; [exact MI|]; split; [reflexivity|]; split; [rewrite Hspm; aln16|];
    split; [exact R1|]; split; [rewrite Hspm; eapply rng_sub'; [exact R2| lia]|]; split; [exact R3|]; split; [exact R4| exact R5].

  (* [comment removed for export] *)
  Definition main_entry (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (FB : list cblk),
      ms = MS (mkR (Z_to_bv 64 RA_MAIN) (Z_to_bv 64 (USP + -48)) gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1
                   (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (USP + 8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 MAIN_ENTRY) fc None m (seg_rom asegs)
      /\ GIOA L RNG s [] FB [] m /\ mem_inv asegs m /\ stk asegs m LO (USP + -48) /\ valid_argv argv /\ rngs RNG
      /\ bytes_at asegs m USP SBK.      (* [comment removed for export] *)

  Definition main_post : Z -> PS -> footprint -> machine_state -> Prop := AT_EXIT.

  (* [comment removed for export] *)
  Definition at_exit2 (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (CL FB : list cblk),
      ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x843a8) fc None m (seg_rom asegs)
      /\ GIOA L RNG s CL FB [] m /\ mem_inv asegs m /\ stk asegs m LO (USP + -128) /\ rngs RNG.

  #[using="argv envp uid hw rnd LO_lo LO_hi USP16 USP47 AT_EXIT_I"] Lemma at_exit2_exit : forall s RNG ms (Q : rd_result (ptr:=hptr) -> PS -> footprint -> machine_state -> Prop),
    at_exit2 s RNG ms ->
    (forall ms', main_post 2 s RNG ms' -> Q RdExit s RNG ms') ->
    evtF asegs RNG (Q RdExit s RNG) ms.
  Proof.
    intros s RNG ms Q (ra & gp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & CL & FB & -> & G & MI & ST & RS) HQ.
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    zstep. zstep. apply evtF_done. apply HQ. unfold main_post.
    eapply AT_EXIT_I; [exact G | exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; generalize LO_hi; lia
                      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; aln16 | exact RS].
  Qed.

  (* [comment removed for export] *)
  Definition main_usage__stmt : Prop := forall s RNG ms,
    main_entry s RNG ms -> Z.of_nat (length argv) <> 2%Z ->
    implMG RNG (main_prog HO FO sites (argv_Z argv)) s main_post ms.
  Section Zd1.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'main_usage__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'main_usage__stmt 1).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'main_usage__stmt 2).
  #[using="fflagA GL GD EPR_USAGE LO_lo LO_hi USP16 TOP_lo TOP47 USP47 AT_EXIT_I drv_lit_mobjA drv_stack_writes"] Lemma main_usage__body : ltac:(let T := type of (fun (h : main_usage__stmt) => h s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, ms))) as _.
    intros (gp & t0 & t1 & t2 & s0 & s1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & FB & -> & G & MI & ST & VA & RS & CS) HC.
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post). pose proof VA as VA'. (nd_pre VA' 5%nat; intros VA1 VA2 VA3 VA4 VA5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI. unfold MAIN_ENTRY.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G) as CSO.
    (pose proof CSO as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ CSR _; nd_post).
    assert (EA : exists argv0 argvr, argv = argv0 :: argvr) by (destruct argv as [|x y]; [cbn in VA1; lia| eauto]).
    (nd_pre EA 3%nat; intros argv0 argvr EARGV; nd_post).
    assert (HA0 : nth_error argv 0 = Some argv0) by (rewrite EARGV; reflexivity).
    pose proof (raw_len_nonneg a_phdrs sp0 argv envp uid hw rnd) as RN.
    pose proof (build_stack_bytes_length a_phdrs sp0 argv envp uid hw rnd) as BL.
    pose proof (bytes_at_bound _ _ _ _ CS) as CSB.
    unfold main_prog, main_model. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length argv) =? 2)%Z with false by (symmetry; apply Z.eqb_neq; exact HC). cbn [negb].
    pose proof (munch_refl [(USP - 128, USP - 48)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    ienterG.
    carve_frame 80%nat ST.
    do 11 zstep.
    zstep. if_true_by (neq_cond (argc argv) 2 ltac:(unfold argc; lia) ltac:(lia) ltac:(unfold argc; exact HC)).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      (nd_pre (stack_argv_string_slack asegs a_phdrs sp0 argv envp uid hw rnd m1 CS
                  ltac:(generalize USP16; clear; intros; Z.div_mod_to_equations; lia) 0 argv0 HA0) 8%nat; intros P0 slackF HP0 P0lo P0hi STRF SLKF ENDF; nd_post);
      pose proof (stack_argv_ptr_read asegs a_phdrs sp0 argv envp uid hw rnd m1 CS 0 _ HP0) as RD0
    end.
    replace (USP + 8 + 8 * Z.of_nat 0)%Z with (USP + 8)%Z in RD0 by lia.
    unfold InitMem.str_base, InitMem.env_base, InitMem.str_base in P0lo, P0hi.
    (nd_pre (slack_trunc _ P0 argv0 slackF (USP + Z.of_nat (length SBK) - 16) STRF SLKF
                ltac:(rewrite BL; unfold raw_len, pad_len in *; clear - P0hi RN; lia)
                ltac:(rewrite BL; generalize USP16; unfold pad_len; clear; intros; Z.div_mod_to_equations; lia)) 4%nat; intros slack0 STR0 SLK0 END0; nd_post).
    assert (RA0 : rng RNG (USP + 8) 8).
    { eapply rng_sub'; [exact CSR|]. rewrite BL. unfold raw_len, struct_size, InitMem.argc, InitMem.envc. clear - RN. lia. }
    do 7 zstep.
    (* [comment removed for export] *)
    lazymatch type of MU with munch _ _ ?mb =>
      destruct (drv_stack_writes L RNG s [] FB m mb _ (USP - 48)%Z G MU WM) as [G1 AG0]; [constructor; [cbn [fst snd]; lia| constructor] | lia |] end.
    clear MU WM.
    pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G1) as CSO1.
    name_spm.
    apply evtF_done. unfold diag, diag_usage. rewrite EARGV at 1. cbn [nth argv_Z map]. eapply implMG_bind.
    { eapply EPR_USAGE with (P := P0) (str := argv0) (slack := slack0); [ | | reflexivity | reflexivity | reflexivity | | exact STR0 | | | exact SLK0 | | ].
      - std_pre_tac G1 ST MI Hspm R1 R2 R3 R4 R5.
      - rewrite Hspm; generalize TOP_lo; clear; intros; lia.                 (* [comment removed for export] *)
      - eapply drv_lit_mobjA; [exact G1 | exact R3 | exact R4 | unfold FMT_USAGE; lia | unfold FMT_USAGE, DRV_RODATA_HI; lia | lia].
      - exact (proj1 (Forall_forall _ _) VA4 _ (nth_error_In _ _ HA0)).
      - pose proof (proj1 (Forall_forall _ _) VA3 _ (nth_error_In _ _ HA0)) as X. cbv beta in X. lia.
      - eapply mobjA_sub; [exact CSO1 | lia | lia | lia].
      - intros a Ha. left. rewrite Hspm. lia. }
    intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
    unfold hpost_regs in E. destruct_exs E. subst ms'.
    pose proof (rngs_le _ _ FP RS) as RS'.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
    replace (ret_pc (Z_to_bv 64 0x842d4)) with (Z_to_bv 64 0x842d4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite Hspm in *.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
    unname_spm.
    ienterG. do 13 zstep.
    replace (ret_pc (Z_to_bv 64 RA_MAIN)) with (Z_to_bv 64 RA_MAIN) by (symmetry; apply ret_pc_even; [unfold RA_MAIN; lia|reflexivity]).
    unfold RA_MAIN. zstep.
    apply evtF_done. apply implMG_ret. apply evtF_done. unfold main_post.
    release_frame FR ST2 (USP + -48)%Z.
    eapply AT_EXIT_I; [exact G2 | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; generalize LO_hi; lia
                      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; aln16 | exact RS'].
  Qed.
  End Zd1.
  #[using="fflagA GL GD EPR_USAGE LO_lo LO_hi USP16 TOP_lo TOP47 USP47 AT_EXIT_I drv_lit_mobjA drv_stack_writes"] Lemma main_usage : ltac:(let t := eval cbv delta [main_usage__stmt] in main_usage__stmt in exact t).
  Proof. exact main_usage__body. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mframe (m : mem) : Prop :=
    exists (j0 : list byte) (f1 f2 f3 f4 f5 f6 f7 f8 : word),
      rw_cells asegs m (USP + -128) [CB 8 j0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7; C8 f8; C8 (Z_to_bv 64 RA_MAIN)].

  (* [comment removed for export] *)
  Definition mbuf (s : PS) (RNG : footprint) (m : mem) (q : hptr) (A cap : Z) (CBs : list byte) : Prop :=
    (exists FB, GIOA L RNG s [(q, A, cap)] FB [] m) /\ mem_inv asegs m /\ stk asegs m LO (USP + -128) /\ mframe m
    /\ (exists junk, rw_cells asegs m A [CB (length CBs) CBs; CB (Z.to_nat (cap - Z.of_nat (length CBs))) junk])
    /\ (Z.of_nat (length CBs) <= cap)%Z /\ (65536 <= cap <= MAX_INPUT)%Z /\ (exists j, cap = 65536 * 2 ^ j)%Z
    /\ rngs RNG.

  (* [comment removed for export] *)
  Definition LH (fd P1 : Z) (path slack : list byte) (st : rd_st (ptr:=hptr)) (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (A : Z) (CBs : list byte) (pc : Z),
      ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 P1) (Z_to_bv 64 (rd_len st)) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 0x5d0c50) (Z_to_bv 64 A) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 pc) fc None m (seg_rom asegs)
      /\ (pc = 0x841a8 \/ (pc = 0x84188 /\ rd_len st = 0))%Z
      /\ mbuf s RNG m (rd_buf st) A (rd_cap st) CBs /\ rd_content st = of_bytes CBs /\ rd_len st = Z.of_nat (length CBs)
      /\ bytes_at asegs m P1 (path ++ Z_to_bv 8 0 :: slack) /\ (USP <= P1)%Z /\ (3 <= fd <= 4096)%Z.

  (* [comment removed for export] *)
  Definition LX (fd P1 : Z) (path slack : list byte) (res : rd_result (ptr:=hptr)) (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    match res with
    | RdExit => at_exit2 s RNG ms
    | RdDone q content =>
        exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
               (m : mem) (A cap : Z) (CBs : list byte),
          ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 P1) (Z_to_bv 64 (Z.of_nat (length CBs))) (Z_to_bv 64 fd) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x84214) fc None m (seg_rom asegs)
          /\ mbuf s RNG m q A cap CBs /\ content = of_bytes CBs
    end.

  (* [comment removed for export] *)
  #[using="rc sp0 argv envp uid hw rnd"] Lemma want_spec : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (cap len : Z),
    s5 = Z_to_bv 64 cap -> s3 = Z_to_bv 64 len -> (0 <= len < cap)%Z -> (cap <= 67108864)%Z -> rng_aimg RNG ->
    evtF asegs RNG (fun ms' => exists a0', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 (Z_to_bv 64 (Z.min (cap - len) 65536)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                          F (Z_to_bv 64 0x841fc) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x841ec) fc None m (seg_rom asegs)).
  Proof.
    intros until len. intros -> -> Hr Hc RIMG.
    zstep. zstep. zstep.
    destruct (Z_lt_le_dec (cap - len) 65536).
    - if_true_by (ltu_cond_true (cap - len)%Z 65536%Z ltac:(lia) ltac:(lia)).
      rewrite Z.min_l by lia. apply evtF_done. eexists. reflexivity.
    - if_false_by (ltu_cond_false (cap - len)%Z 65536%Z ltac:(lia) ltac:(lia)). zstep.
      rewrite Z.min_r by lia. apply evtF_done. eexists. reflexivity.
  Qed.

  #[using="rc sp0 argv envp uid hw rnd"] Lemma cap_shift_zero : forall cap j, (cap = 65536 * 2 ^ j)%Z -> (0 <= j)%Z -> (cap < 67108864)%Z -> Z.shiftr cap 26 = 0%Z.
  Proof. intros cap j -> Hj Hc. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

  (* [comment removed for export] *)
  Definition grow_post (fd P1 : Z) (path slack : list byte) (len0 : Z) : option (rd_st (ptr:=hptr)) -> PS -> footprint -> machine_state -> Prop :=
    fun g s' RNG' ms' =>
      match g with
      | None => at_exit2 s' RNG' ms'
      | Some st1 => rd_len st1 = len0 /\ exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
                           (m : mem) (A : Z) (CBs : list byte),
          ms' = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 P1) (Z_to_bv 64 (rd_len st1)) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 0x5d0c50) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x841ec) fc None m (seg_rom asegs)
          /\ mbuf s' RNG' m (rd_buf st1) A (rd_cap st1) CBs /\ rd_content st1 = of_bytes CBs /\ rd_len st1 = Z.of_nat (length CBs)
          /\ (rd_len st1 < rd_cap st1)%Z
          /\ bytes_at asegs m P1 (path ++ Z_to_bv 8 0 :: slack)
      end.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA sp0 argv envp uid hw rnd GL block_mobjA"] Lemma blk_facts : forall RNG s CL FB m b, GIOA L RNG s CL FB [] m -> In b CL -> (0 <= cb_size b)%Z ->
    mobjA RNG m (cb_addr b) (cb_size b) /\ (cb_addr b + cb_size b <= ATOP)%Z /\ (0x603000 <= cb_addr b)%Z.
  Proof.
    intros RNG s CL FB m b G Hb Hn. (nd_pre (block_mobjA L RNG s CL FB m (cb_addr b) (cb_size b) G ltac:(exists b; split; [exact Hb| lia]) Hn) 3%nat; intros A1 A2 A3; nd_post).
    unfold AIMG_HI in A3. auto.
  Qed.
  (* [comment removed for export] *)
  #[using="FO fflagA sp0 argv envp uid hw rnd GL"] Lemma blk_tclr : forall RNG s CL FB m b, GIOA L RNG s CL FB [] m -> In b CL -> (0 < cb_size b)%Z ->
    (cb_addr b + cb_size b <= ATPv + -200 \/ ATPv + 304 <= cb_addr b)%Z.
  Proof.
    intros RNG s CL FB m b G Hb Hn.
    destruct (Z_le_gt_dec (cb_addr b + cb_size b) (ATPv + -200)) as [X|X]; [left; exact X|].
    destruct (Z_le_gt_dec (ATPv + 304) (cb_addr b)) as [Y|Y]; [right; exact Y|]. exfalso.
    apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max (cb_addr b) (ATPv + -200)) G).
    - left. apply in_block_app. left. apply in_block_In. exists b. split; [exact Hb| lia].
    - unfold ATP. lia.
  Qed.

  (* [comment removed for export] *)
  Definition grow_spec__stmt : Prop := forall fd P1 path slack (st : rd_st (ptr:=hptr)) s RNG ms,
    LH fd P1 path slack st s RNG ms -> rd_len st = rd_cap st ->
    implMG RNG
      (if (MAX_INPUT <=? rd_cap st)%Z then diag DTooBig ;;; mret None
       else nb <- pmalloc HO (rd_cap st * 2) ;;
            match nb with
            | None => diag DOom ;;; mret None
            | Some nb' => pfree HO (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_len st) (rd_chunks st)))
            end) s
      (grow_post fd P1 path slack (rd_len st)) ms.
  Section Zd2.   (* [comment removed for export] *)
  Variable fd : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 0).
  Variable P1 : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 1).
  Variable path : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 2).
  Variable slack : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 3).
  Variable st : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 4).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 5).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 6).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 7).
  #[using="FO fflagA argv envp uid hw rnd GL GD MALLOC FREE EPR_BIG LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma grow_spec__body : ltac:(let T := type of (fun (h : grow_spec__stmt) => h fd P1 path slack st s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (fd, (P1, (path, (slack, (st, (s, (RNG, ms)))))))) as _.
    intros LHH Hfull.
    (nd_pre LHH 29%nat; intros ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A CBs pc ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros HPC MB HC HL PATH HP1 HFD; nd_post).
    (nd_pre MB 9%nat; intros (FB & G) MI ST (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) (junk & BUF) HLC HCAP (j & Hj) RS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    destruct st as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *. subst len.
    (nd_pre (blk_facts RNG s _ FB m (q, A, cap) G ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros _ B1 B2; nd_post). cbn [cb_addr cb_size fst snd] in B1, B2.
    pose proof (bytes_at_bound _ _ _ _ PATH) as PB. rewrite length_app in PB; cbn [length] in PB.
    assert (Hj0 : (0 <= j)%Z). { destruct (Z_lt_le_dec j 0); [|lia]. rewrite Z.pow_neg_r in Hj by lia. lia. }
    rewrite Hfull in *.
    (* [comment removed for export] *)
    destruct HPC as [->|[_ H0]]; [|exfalso; unfold MAX_INPUT in *; lia].
    ienterG. zstep. if_true_by (beq_cond cap). zstep.
    destruct (Z_le_gt_dec MAX_INPUT cap) as [HBIG|HOK].
    - (* [comment removed for export] *)
      replace (MAX_INPUT <=? cap)%Z with true by (symmetry; apply Z.leb_le; exact HBIG).
      assert (Ecap : cap = 67108864%Z) by (unfold MAX_INPUT in *; lia).
      replace (Z.shiftr cap 26) with 1%Z by (rewrite Ecap; reflexivity).
      zstep. if_true. do 7 zstep.
      name_spm.
      apply evtF_done. unfold diag, diag_too_big. eapply implMG_bind.
      { eapply EPR_BIG; [ | | reflexivity | reflexivity | reflexivity | ].
        - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
        - rewrite Hspm; generalize TOP_lo; clear; intros; lia.                 (* [comment removed for export] *)
        - eapply drv_lit_mobjA; [exact G | exact R3 | exact R4 | unfold FMT_TOO_BIG; lia | unfold FMT_TOO_BIG, DRV_RODATA_HI; lia | lia]. }
      intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP RS) as RS'.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
      replace (ret_pc (Z_to_bv 64 0x84384)) with (Z_to_bv 64 0x84384) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *. unname_spm.
      ienterG. zstep.
      apply evtF_done. apply implMG_ret. apply evtF_done.
      unfold grow_post, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2|]. split; [exact ST2| exact RS'].
    - (* [comment removed for export] *)
      replace (MAX_INPUT <=? cap)%Z with false by (symmetry; apply Z.leb_gt; lia).
      rewrite (cap_shift_zero cap j Hj Hj0 ltac:(unfold MAX_INPUT in HOK; lia)).
      zstep. if_false. zstep. zstep. zstep.
      rewrite (Z.shiftl_mul_pow2 cap 1) by lia. change (2 ^ 1)%Z with 2%Z.
      destruct (cap_double_ok cap j Hj Hj0 ltac:(unfold MAX_INPUT in HOK; lia)) as [Hj' HC2].
      name_spm.
      apply evtF_done. eapply implMG_bind.
      { eapply MALLOC with (n := (cap * 2)%Z); [ | reflexivity | unfold MAX_INPUT in HOK; lia | ].
        - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
        - eapply (unw_main RNG _ AMALLOC_PC spm _ _ 0x841c8%Z);
            [ rewrite Hspm, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold AMALLOC_PC, ACLIENT_LO, ACLIENT_HI; lia
            | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | exact R1 | rewrite Hspm; lia ]. }
      intros r s' RNG1 ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP1 a0v m1 E OF1 MI1 ST1 AG1 CASES; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP1 RS) as RS1.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      replace (ret_pc (Z_to_bv 64 0x841c8)) with (Z_to_bv 64 0x841c8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ _ AG1) in PATH; [|lia].
      apply (keeps_rw_cells_block _ _ _ _ _ _ _ AG1) in BUF.
      2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
      unname_spm.
      destruct r as [nb|]; [| destruct CASES].
      (* [comment removed for export] *)
      (nd_pre CASES 3%nat; intros A' junk' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G1 BLK; nd_post).
      (nd_pre (blk_facts RNG1 s' _ FB m1 (nb, A', (cap * 2)%Z) G1 ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros DOBJ C1 C2; nd_post). cbn [cb_addr cb_size fst snd] in DOBJ, C1, C2.
      (nd_pre (blk_facts RNG1 s' _ FB m1 (q, A, cap) G1 ltac:(right; left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros SOBJ _ _; nd_post). cbn [cb_addr cb_size fst snd] in SOBJ.
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G1) as AP. apply blocks_apart_app_inv in AP as (AP & _ & _). cbn [blocks_apart] in AP. destruct AP as [AP _].
      apply Forall_cons_iff in AP as [AP _]. unfold apart in AP. cbn [cb_addr cb_size fst snd] in AP.
      cbv beta iota. ienterG.
      zstep. if_false_by (eqz_cond_false A' ltac:(lia)). zstep.
      zstep. if_false_by (eqz_cond_false cap ltac:(lia)). zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat cap; Z.to_nat cap]) in BLK; [|cbn; lia]. cbn [app mk_CB_cells] in BLK.
      apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BLK as [BLK1 BLK2]. cbn [cells_size csize Nat.add] in BLK2.
      rewrite Nat.add_0_r, Z2Nat.id in BLK2 by lia.
      pose proof BUF as BUF'. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BUF' as [BUF1 _].
      assert (SRC : bytes_at asegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A CBs).
      { destruct BUF1 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (munch_refl [(USP + -128 - 2240, USP + -128); (A', A' + cap)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
      pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G1) as (RT1 & _).
      call_sp (memcpy_i_specZ RNG1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LO A' A cap CBs (firstn (Z.to_nat cap) junk'));
        [ first [reflexivity | assumption | lia | (eapply mobjA_sub; [exact DOBJ| lia| lia| lia]) | (eapply rng_sub'; [exact R2| lia])] .. | ].
      rename PC into ST2. rename PC0 into DST. clear POST BUF1 SRC BUF.
      lazymatch type of MU2 with munch _ _ ?mb =>
        assert (G2 : GIOA L RNG1 s' ((nb, A', (cap * 2)%Z) :: [(q, A, cap)]) FB [] mb);
        [ eapply (gl_client_frame _ _ _ GL); [exact G1 | exact MU2 | exact WM2 |];
          constructor; [left; cbn [fst snd]; lia | constructor; [| constructor]];
          right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ]
      end.
      clear MU2 WM2 G1.
      zstep. zstep.
      name_spm.
      apply evtF_done. eapply implMG_bind.
      { eapply FREE with (C1 := [(nb, A', (cap * 2)%Z)]) (C2 := @nil cblk) (q := q) (A := A) (n := cap); [| reflexivity |].
        - std_pre_tac G2 ST2 MI Hspm R1 R2 R3 R4 R5.
        - eapply (unw_main RNG1 _ AFREE_PC spm _ _ 0x841ec%Z);
            [ rewrite Hspm, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia
            | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | exact R1 | rewrite Hspm; lia ]. }
      intros [] s'' RNG2 ms'' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP2 a0v2 m3 E OF2 MI3 ST3 AG3 G3; nd_post).
      unfold hpost_regs in E. destruct_exs E. subst ms''.
      cbn [app] in AG3, G3.
      pose proof (rngs_le _ _ FP2 RS1) as RS2.
      replace (ret_pc (Z_to_bv 64 0x841ec)) with (Z_to_bv 64 0x841ec) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG3) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ _ AG3) in PATH; [|lia].
      apply (keeps_rw_cells_block _ _ _ _ _ _ _ AG3) in DST.
      2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
      apply (keeps_rw_cells_block _ _ _ _ _ _ _ AG3) in BLK2.
      2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
      unname_spm.
      (* [comment removed for export] *)
      apply implMG_ret. apply evtF_done.
      unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks rd_content]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { split; [exists FB; exact G3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
        split.
        { exists (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk')).
          replace (length CBs) with (Z.to_nat cap) by lia.
          replace (Z.to_nat (cap * 2 - Z.of_nat (Z.to_nat cap))) with (Z.to_nat cap) by lia.
          apply rw_cells_join2; [exact DST|]. cbn [csize]. rewrite Z2Nat.id by lia. exact BLK2. }
        split; [lia|]. split; [unfold MAX_INPUT; lia|]. split; [exists (j + 1)%Z; exact Hj'| exact RS2]. }
      split; [exact HC|]. split; [symmetry; exact Hfull|]. split; [lia| exact PATH].
  Qed.
  End Zd2.
  #[using="FO fflagA argv envp uid hw rnd GL GD MALLOC FREE EPR_BIG LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma grow_spec : ltac:(let t := eval cbv delta [grow_spec__stmt] in grow_spec__stmt in exact t).
  Proof. exact grow_spec__body. Qed.

  Definition body_post (fd P1 : Z) (path slack : list byte) : (rd_st (ptr:=hptr) + rd_result (ptr:=hptr)) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => match r with inl st' => LH fd P1 path slack st' s' RNG' ms' | inr res => LX fd P1 path slack res s' RNG' ms' end.

  (* [comment removed for export] *)
  #[using="Type"] Lemma RS_ok : rw_bytes_b asegs 0x5d0c50 (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) = true.
  Proof. exact RS_ok_pre. Qed.   (* [comment removed for export] *)
  #[using="rc sp0 argv envp uid hw rnd"] Lemma RS_chunk : forall m : mem, exists rsj, rw_cells asegs m 0x5d0c50 [CB (Z.to_nat 65536) rsj].
  Proof.
    intros m. (nd_pre (rw_cells_any asegs m 0x5d0c50%Z (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) RS_ok ltac:(lia) ltac:(rewrite repeat_length; lia)) 3%nat; intros rsj RSL RSC; nd_post).
    rewrite repeat_length in RSC. exists rsj. exact RSC.
  Qed.
  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA sp0 argv envp uid hw rnd GL GD"] Lemma stage_mobjA : forall RNG s CL FB m n, GIOA L RNG s CL FB [] m -> rng_aimg RNG -> rng_aimg_sh RNG -> (0 <= n <= 65536)%Z ->
    mobjA RNG m 0x5d0c50 n.
  Proof.
    intros RNG s CL FB m n G RI RSH Hn. destruct (gd_unp _ _ _ GD _ _ _ _ _ _ _ G) as [_ U]. destruct (gl_globals _ _ _ GL _ _ _ _ _ _ _ G) as [W _].
    unfold READ_STAGE in U. apply static_mobjA; [lia | lia | lia | eapply unpoisoned_sub; [exact U| lia| lia] | exact W | exact RI | exact RSH].
  Qed.

  #[using="sp0 argv envp uid hw rnd"] Lemma atp_unsigned : bv_unsigned (Z_to_bv 64 ATP) = ATP.
  Proof. pose proof atp_lin as ((TL & _) & _). atop_facts. unfold ATP. apply unsigned_lit. lia. Qed.

  (* [comment removed for export] *)
  Definition read_step__stmt : Prop := forall fd P1 path slack (len0 : Z) (st1 : rd_st (ptr:=hptr)) s RNG ms,
    grow_post fd P1 path slack len0 (Some st1) s RNG ms ->
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z -> (3 <= fd <= 4096)%Z -> (USP <= P1)%Z ->
    (P1 + Z.of_nat (length path) + 1 + Z.of_nat (length slack) <= USP + Z.of_nat (length SBK) - 16)%Z ->
    implMG RNG
      (s0 <- mget ;;
       (let buf := sites SiteReadStage in
        let want := (rd_cap st1 - len0)%Z in
        let want' := (if READ_CHUNK <? want then READ_CHUNK else want)%Z in
        a <- msys (NRead fd buf want') (dec_read buf want') ;;
        match a with
        | RdErr _ => diag (DReadError (map bv_unsigned path)) ;;; mret (inr RdExit)
        | RdData bs => if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
                       else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (len0 + zlength bs)%Z (rd_chunks st1 ++ [of_bytes bs])))
        end)) s (body_post fd P1 path slack) ms.
  Section Zd3.   (* [comment removed for export] *)
  Variable fd : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 0).
  Variable P1 : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 1).
  Variable path : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 2).
  Variable slack : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 3).
  Variable len0 : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 4).
  Variable st1 : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 5).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 6).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 7).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 8).
  #[using="FO fflagA GL GD EPR_READ SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 drv_lit_mobjA block_mobjA"] Lemma read_step__body : ltac:(let T := type of (fun (h : read_step__stmt) => h fd P1 path slack len0 st1 s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (fd, (P1, (path, (slack, (len0, (st1, (s, (RNG, ms))))))))) as _.
    intros GP HNUL HPL HFD HP1 HPEND.
    destruct GP as [<- GP].
    (nd_pre GP 28%nat; intros ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A CBs ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MB HC HL HLT PATH; nd_post).
    (nd_pre MB 9%nat; intros (FB & G) MI ST (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) (junk & BUF) HLC HCAP (j & Hj) RS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    destruct (gd_errno _ _ _ GD _ _ _ _ _ _ _ G) as (e & T2).
    pose proof atp_unsigned as ETP. pose proof atp_lin as ((TL & _) & _). pose proof atp_below_atop as TBA. unfold ATP in *.
    destruct st1 as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *. subst len.
    set (len := Z.of_nat (length CBs)) in *.
    (nd_pre (blk_facts RNG s _ FB m (q, A, cap) G ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros BOBJ B1 B2; nd_post). cbn [cb_addr cb_size fst snd] in BOBJ, B1, B2.
    pose proof (blk_tclr RNG s _ FB m (q, A, cap) G ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) as BTLS. cbn [cb_addr cb_size fst snd] in BTLS.
    pose proof (bytes_at_bound _ _ _ _ PATH) as PB. rewrite length_app in PB; cbn [length] in PB.
    apply implMG_get_bind. cbv beta zeta.
    rewrite SITE_RS. unfold READ_STAGE.
    set (want := Z.min (cap - len) 65536).
    replace (if READ_CHUNK <? cap - len then READ_CHUNK else cap - len)%Z with want.
    2:{ subst want. unfold READ_CHUNK. destruct (Z.ltb_spec 65536 (cap - len)); lia. }
    assert (HW : (1 <= want <= 65536)%Z /\ (want <= cap - len)%Z) by (subst want; lia).
    destruct HW as [HW1 HW2].
    ienterG.
    eapply evtF_cut; [eapply (want_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m cap len); [reflexivity | reflexivity | lia | unfold MAX_INPUT in HCAP; lia | exact R3] |].
    cbv beta. intros ms' [a0' ->]. fold want.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    destruct (RS_chunk m) as (rsj & RSC).
    apply (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat want; Z.to_nat (65536 - want)]) in RSC; [|cbn; lia]. cbn [app mk_CB_cells] in RSC.
    apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in RSC as [RSw _].
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    name_spm.
    apply evtF_done. eapply implMG_msys_of_enode.
    { eapply (read_i_specZ RNG _ spm _ (Z_to_bv 64 ATPv)) with (lo := LO) (fd := fd) (B := 0x5d0c50%Z) (count := want) (errv := e);
        [ reflexivity | reflexivity | reflexivity | exact MI | rewrite Hspm; exact ST | rewrite Hspm; lia | exact LOLO | exact RT | exact ETP
        | exact RSw | exact T2 | lia | lia | right; lia | lia | (unfold tclr; pose proof ATPv_img; lia)
        | eapply stage_mobjA; [exact G | exact R3 | exact R4 | lia] | exact R3 | rewrite Hspm; eapply rng_sub'; [exact R2| lia] | exact R5 ]. }
    intros a RNG' ms' PO. unfold read_i_post in PO. destruct PO as (-> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MU WM MI' ST' CASE; nd_post).
    replace (ret_pc (Z_to_bv 64 0x84208)) with (Z_to_bv 64 0x84208) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite ETP in *. rewrite Z2Nat.id in MU by lia.
    clear RSw.
    lazymatch type of MU with munch _ ?ma ?mb => transport_after_call asegs ma mb MU WM end.
    clear MI. rename MI' into MI.
    apply (munch_weaken _ [(ATPv + -164, ATPv + -160); (bv_unsigned spm - 2208, bv_unsigned spm); (0x5d0c50, 0x5d0c50 + want)]%Z) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
    (* [comment removed for export] *)
    assert (G' : forall ev, rw_cells asegs ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end) (ATPv + -164) [C4 ev] ->
                 GIOA L RNG s [(q, A, cap)] FB [] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
    { intros ev HEV. eapply (gd_frame_errno _ _ _ GD); [exact G | exact MU | exact WM | | exact HEV].
      constructor; [left; left; cbn [fst snd]; rewrite Hspm; lia|].
      constructor; [right; unfold rs_iv, READ_STAGE; cbn [fst snd]; lia| constructor]. }
    clear MU WM G.
    destruct a as [err|bs].
    - (* [comment removed for export] *)
      (nd_pre CASE 3%nat; intros _ ERR Herr; nd_post). specialize (G' _ ERR).
      clear CM1 CM2. (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G') 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
      pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G') as CSO.
      unfold read_ret. rewrite Hspm in *. unname_spm.
      ienterG. zstep. if_true_by ltz_cond_m1. do 8 zstep.
      name_spm.
      apply evtF_done. unfold diag, diag_read_error. eapply implMG_bind.
      { eapply EPR_READ with (P := P1) (str := path) (slack := slack); [ | | reflexivity | reflexivity | reflexivity | | exact PATH | exact HNUL | exact (proj1 HPL) | exact (proj2 HPL) | | intros a Ha; left; rewrite Hspm; lia ].
        - std_pre_tac G' ST' MI Hspm R1 R2 R3 R4 R5.
        - rewrite Hspm; generalize TOP_lo; clear; intros; lia.                 (* [comment removed for export] *)
        - eapply drv_lit_mobjA; [exact G' | exact R3 | exact R4 | unfold FMT_READ_ERROR; lia | unfold FMT_READ_ERROR, DRV_RODATA_HI; lia | lia].
        - eapply mobjA_sub; [exact CSO | lia | lia | lia]. }
      intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP RS) as RS'.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
      replace (ret_pc (Z_to_bv 64 0x84384)) with (Z_to_bv 64 0x84384) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *. unname_spm.
      ienterG. zstep.
      apply evtF_done. apply implMG_ret. apply evtF_done.
      unfold body_post, LX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2|]. split; [exact ST2| exact RS'].
    - (* [comment removed for export] *)
      (nd_pre CASE 3%nat; intros RSr ERR Hbs; nd_post). specialize (G' _ ERR).
      unfold read_ret. rewrite Hspm in *. unname_spm.
      pose proof (Nat2Z.is_nonneg (length bs)) as LB0.
      ienterG. zstep. if_false_by (ltz_cond_false (Z.of_nat (length bs)) ltac:(lia)). zstep.
      destruct bs as [|b bs'].
      + (* [comment removed for export] *)
        zstep. if_false_by (eq_cond 0).
        apply evtF_done. cbn [length Nat.eqb]. apply implMG_ret. apply evtF_done.
        unfold body_post, LX. cbn [rd_content rd_chunks].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|]. split; [| exact HC].
        split; [exists FB; exact G'|]. split; [exact MI|]. split; [exact ST'|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
        split; [exists junk; exact BUF|].
        split; [lia|]. split; [exact HCAP|]. split; [exists j; exact Hj| exact RS].
      + (* [comment removed for export] *)
        set (n := Z.of_nat (length (b :: bs'))) in *.
        assert (Hn : (1 <= n <= want)%Z) by (subst n; cbn [length] in *; lia).
        zstep. if_true_by (nez_cond n ltac:(lia)).
        zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in RSr as [RSd _].
        assert (SRC : bytes_at asegs ltac:(lazymatch type of RSd with rw_cells _ ?mm _ _ => exact mm end) 0x5d0c50 (b :: bs')).
        { destruct RSd as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
        clear RSd.
        pose proof BUF as BUF0. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BUF as [BUF1 BUF2]. cbn [cells_size csize Nat.add] in BUF2.
        rewrite Nat.add_0_r in BUF2. fold len in BUF2.
        apply (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat n; Z.to_nat (cap - len - n)]) in BUF2; [|cbn; lia]. cbn [app mk_CB_cells] in BUF2.
        apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BUF2 as [BUFw BUF3]. cbn [cells_size csize Nat.add] in BUF3.
        rewrite Nat.add_0_r, Z2Nat.id in BUF3 by lia.
        clear BUF0.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (munch_refl [(USP + -128 - 2240, USP + -128); (A + len, A + len + n)]%Z m1) as MU2; pose proof (wmono_refl asegs m1) as WM2 end.
        pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G') as (RT' & _).
        (nd_pre (blk_facts RNG s _ FB _ (q, A, cap) G' ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros BOBJ' _ _; nd_post). cbn [cb_addr cb_size fst snd] in BOBJ'.
        pose proof (stage_mobjA RNG s _ FB _ n G' R3 R4 ltac:(lia)) as SOBJ.
        call_sp (memcpy_i_specZ RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LO (A + len)%Z 0x5d0c50%Z n (b :: bs') (firstn (Z.to_nat n) junk));
          [ first [reflexivity | assumption | lia | (subst n; lia) | (eapply mobjA_sub; [exact BOBJ'| lia| lia| lia]) | (eapply rng_sub'; [exact R2| lia])] .. | ].
        rename PC into ST2. rename PC0 into DST. clear POST. try clear SRC.
        lazymatch type of MU2 with munch _ _ ?mb =>
          assert (G2 : GIOA L RNG s [(q, A, cap)] FB [] mb);
          [ eapply (gl_client_frame _ _ _ GL); [exact G' | exact MU2 | exact WM2 |];
            constructor; [left; cbn [fst snd]; lia | constructor; [| constructor]];
            right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ]
        end.
        clear MU2 WM2 G'.
        (* [comment removed for export] *)
        zstep. zstep.
        (* [comment removed for export] *)
        assert (BUF : exists junk', rw_cells asegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A
                        [CB (length (CBs ++ b :: bs')) (CBs ++ b :: bs'); CB (Z.to_nat (cap - (len + n))) junk']).
        { eexists.
          assert (J : rw_cells asegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A
                        ([CB (length CBs) CBs] ++ [CB (Z.to_nat n) (b :: bs')] ++ [CB (Z.to_nat (cap - len - n)) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))])).
          { apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [exact BUF1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. fold len.
            apply (proj2 (rw_cells_app asegs _ _ [_] [_])). split; [exact DST|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact BUF3. }
          cbn [app] in J.
          apply (rw_cells_merge asegs _ _ [] [CB (length CBs) CBs; CB (Z.to_nat n) (b :: bs')] [_]) in J. cbn [cells_size csize cells_bytes cbytes app] in J.
          replace (length CBs + (Z.to_nat n + 0))%nat with (length (CBs ++ b :: bs')) in J by (rewrite length_app; subst n; lia).
          rewrite ?app_nil_r in J.
          replace (Z.to_nat (cap - len - n)) with (Z.to_nat (cap - (len + n))) in J by lia. exact J. }
        clear BUF1 DST BUF3. destruct BUF as [junk' BUF].
        apply evtF_done. replace (length (b :: bs') =? 0)%nat with false by reflexivity. apply implMG_ret. apply evtF_done.
        unfold body_post, LH. cbn [rd_buf rd_cap rd_len rd_chunks rd_content].
        replace (n + len)%Z with (len + zlength (b :: bs'))%Z by (unfold zlength; subst n; lia).
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [left; reflexivity|].
        split.
        { split; [exists FB; exact G2|]. split; [eassumption|]. split; [exact ST2|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
          split. { exists junk'. replace (cap - Z.of_nat (length (CBs ++ b :: bs')))%Z with (cap - (len + n))%Z by (rewrite length_app; subst n len; lia). exact BUF. }
          split; [rewrite length_app; subst n len; lia|]. split; [exact HCAP|]. split; [exists j; exact Hj| exact RS]. }
        split. { unfold rd_content in *. cbn [rd_chunks] in HC |- *. rewrite concat_app. cbn [concat]. rewrite app_nil_r, HC. unfold of_bytes. rewrite map_app. reflexivity. }
        split; [unfold zlength; rewrite length_app; subst len; lia|].
        split; [exact PATH|]. split; [exact HP1| exact HFD].
  Qed.
  End Zd3.
  #[using="FO fflagA GL GD EPR_READ SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 drv_lit_mobjA block_mobjA"] Lemma read_step : ltac:(let t := eval cbv delta [read_step__stmt] in read_step__stmt in exact t).
  Proof. exact read_step__body. Qed.

  (* [comment removed for export] *)
  Definition body_spec__stmt : Prop := forall fd P1 path slack (st : rd_st (ptr:=hptr)) s RNG ms,
    LH fd P1 path slack st s RNG ms -> ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
    (P1 + Z.of_nat (length path) + 1 + Z.of_nat (length slack) <= USP + Z.of_nat (length SBK) - 16)%Z ->
    implMG RNG (read_loop_body diag (pmalloc HO) (pfree HO) (sites SiteReadStage) fd (map bv_unsigned path) st) s (body_post fd P1 path slack) ms.
  Section Zd4.   (* [comment removed for export] *)
  Variable fd : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 0).
  Variable P1 : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 1).
  Variable path : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 2).
  Variable slack : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 3).
  Variable st : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 4).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 5).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 6).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 7).
  #[using="FO fflagA GL GD MALLOC FREE EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma body_spec__body : ltac:(let T := type of (fun (h : body_spec__stmt) => h fd P1 path slack st s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (fd, (P1, (path, (slack, (st, (s, (RNG, ms)))))))) as _.
    intros LHH HNUL HPL HPEND.
    pose proof LHH as LHH'.
    (nd_pre LHH' 36%nat; intros ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A CBs pc Ems HPC MB HC HL PATH HP1 HFD; nd_post). subst ms.
    pose proof MB as MB'. (nd_pre MB' 9%nat; intros (FB & G) MI ST FRm BUF HLC HCAP HJ RS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    unfold read_loop_body. cbv zeta.
    eapply implMG_bind with (Q1 := grow_post fd P1 path slack (rd_len st)).
    - destruct (Z.eqb_spec (rd_len st) (rd_cap st)) as [E|NE].
      + apply grow_spec; [exact LHH | exact E].
      + apply implMG_ret.
        destruct st as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *.
        (* [comment removed for export] *)
        destruct HPC as [->|[-> H0]].
        * zstep. if_false_by (bne_cond_false len cap ltac:(unfold MAX_INPUT in *; lia) ltac:(unfold MAX_INPUT in *; lia) NE). zstep. zstep.
          apply evtF_done. unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|]. split; [exact MB|]. split; [exact HC|]. split; [exact HL|]. split; [lia| exact PATH].
        * zstep. if_true_by (neq_cond 0 cap ltac:(lia) ltac:(unfold MAX_INPUT in *; lia) ltac:(unfold MAX_INPUT in *; lia)). zstep. zstep.
          apply evtF_done. unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|]. split; [exact MB|]. split; [exact HC|]. split; [exact HL|]. split; [lia| exact PATH].
    - intros g s' RNG' ms' GP. destruct g as [st1|].
      + cbv beta iota. eapply read_step; [exact GP | exact HNUL | exact HPL | exact HFD | exact HP1 | exact HPEND].
      + cbv beta iota. apply implMG_ret. apply evtF_done. exact GP.
  Qed.
  End Zd4.
  #[using="FO fflagA GL GD MALLOC FREE EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma body_spec : ltac:(let t := eval cbv delta [body_spec__stmt] in body_spec__stmt in exact t).
  Proof. exact body_spec__body. Qed.

  (* [comment removed for export] *)
  #[using="FO fflagA GL GD MALLOC FREE EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma loop_spec : forall fuel fd P1 path slack (st : rd_st (ptr:=hptr)) s RNG ms,
    LH fd P1 path slack st s RNG ms -> ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
    (P1 + Z.of_nat (length path) + 1 + Z.of_nat (length slack) <= USP + Z.of_nat (length SBK) - 16)%Z ->
    implMG RNG (mloop fuel (read_loop_body diag (pmalloc HO) (pfree HO) (sites SiteReadStage) fd (map bv_unsigned path)) st) s
      (LX fd P1 path slack) ms.
  Proof.
    induction fuel as [|fuel IH]; intros fd P1 path slack st s RNG ms LHH HNUL HPL HPEND.
    - cbn [mloop]. apply implMG_unr.
    - apply implMG_loop_S. eapply implMG_mono; [eapply body_spec; [exact LHH | exact HNUL | exact HPL | exact HPEND]|].
      cbv beta. intros [st'|res] s' RNG' ms' BP; unfold body_post in BP.
      + apply IH; [exact BP | exact HNUL | exact HPL | exact HPEND].
      + apply evtF_done. exact BP.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma to_bytes_of_bytes : forall l : list byte, to_bytes (map bv_unsigned l) = l.
  Proof.
    intros l. unfold to_bytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
    apply definitions.Z_to_bv_bv_unsigned.
  Qed.

  #[using="Type"] Lemma rw_cells_nil_CB : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A (CB 0 [] :: cs).
  Proof.
    intros m A cs [[Hwf HB] HW]. split; [split|].
    - split; [reflexivity| exact Hwf].
    - cbn [cells_bytes cbytes app]. exact HB.
    - cbn [cells_size csize Nat.add]. exact HW.
  Qed.

  (* [comment removed for export] *)
  Definition P2 (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (FB : list cblk),
      ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 (Z_to_bv 64 (USP + 8)) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x84150) fc None m (seg_rom asegs)
      /\ GIOA L RNG s [] FB [] m /\ mem_inv asegs m /\ stk asegs m LO (USP + -128) /\ mframe m /\ rngs RNG /\ bytes_at asegs m USP SBK.

  (* [comment removed for export] *)
  Definition RAX (res : rd_result (ptr:=hptr)) (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    match res with
    | RdExit => at_exit2 s RNG ms
    | RdDone q content =>
        exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
               (m : mem) (A cap : Z) (CBs : list byte),
          ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (Z.of_nat (length CBs))) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8421c) fc None m (seg_rom asegs)
          /\ mbuf s RNG m q A cap CBs /\ content = of_bytes CBs
    end.

  Definition read_all_spec__stmt : Prop := forall s RNG ms argv1,
    P2 s RNG ms -> nth_error argv 1 = Some argv1 -> valid_argv argv ->
    implMG RNG (read_all diag (pmalloc HO) (pfree HO) (sites SiteReadStage) (map bv_unsigned argv1)) s RAX ms.
  Section Zd5.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'read_all_spec__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'read_all_spec__stmt 1).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'read_all_spec__stmt 2).
  Variable argv1 : ltac2:(SecDietF.SzSecF.ty 'read_all_spec__stmt 3).
  #[using="FO fflagA GL GD MALLOC FREE EPR_OPEN EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma read_all_spec__body : ltac:(let T := type of (fun (h : read_all_spec__stmt) => h s RNG ms argv1) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, (ms, argv1)))) as _.
    intros (ra & gp & t0 & t1 & t2 & s1 & a0 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & FB & -> & G & MI & ST & (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) & RS & CS) HA1 VA.
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post). pose proof VA as VA'. (nd_pre VA' 5%nat; intros VA1 VA2 VA3 VA4 VA5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    destruct (gd_errno _ _ _ GD _ _ _ _ _ _ _ G) as (e & T2). destruct (gd_canary _ _ _ GD _ _ _ _ _ _ _ G) as (L2 & (can & L3)).
    pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G) as CSO. (pose proof CSO as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ CSR _; nd_post).
    pose proof atp_unsigned as ETP. pose proof atp_lin as ((TL & _) & _). pose proof atp_below_atop as TBA. pose proof ATPv_img as TIMG. unfold ATP in *.
    pose proof (raw_len_nonneg a_phdrs sp0 argv envp uid hw rnd) as RN.
    pose proof (build_stack_bytes_length a_phdrs sp0 argv envp uid hw rnd) as BL.
    pose proof (bytes_at_bound _ _ _ _ CS) as CSB.
    (nd_pre (stack_argv_string_slack asegs a_phdrs sp0 argv envp uid hw rnd m CS
                ltac:(generalize USP16; clear; intros; Z.div_mod_to_equations; lia) 1 argv1 HA1) 8%nat; intros P1 slackF HP1 P1lo P1hi STRF SLKF ENDF; nd_post).
    assert (P1hi' : (P1 + Z.of_nat (length argv1) + 1 <= USP + Z.of_nat (length SBK) - 16)%Z)
      by (rewrite BL; unfold InitMem.str_base, InitMem.env_base, InitMem.str_base, raw_len, pad_len in *; clear - P1hi RN; lia).
    (nd_pre (slack_trunc _ P1 argv1 slackF (USP + Z.of_nat (length SBK) - 16) STRF SLKF P1hi'
                ltac:(rewrite BL; generalize USP16; unfold pad_len; clear; intros; Z.div_mod_to_equations; lia)) 4%nat; intros slack1 STRS SLK1 END1; nd_post).
    destruct (proj1 (bytes_at_app asegs m P1 (argv1 ++ [Z_to_bv 8 0]) slack1) ltac:(rewrite <- app_assoc; exact STRS)) as [STR1 _].
    pose proof (stack_argv_ptr_read asegs a_phdrs sp0 argv envp uid hw rnd m CS 1 _ HP1) as RD1.
    replace (USP + 8 + 8 * Z.of_nat 1)%Z with (USP + 16)%Z in RD1 by lia.
    unfold InitMem.str_base, InitMem.env_base, InitMem.str_base in P1lo, P1hi.
    assert (P1lo' : (USP <= P1)%Z) by (unfold struct_size, InitMem.argc, InitMem.envc in P1lo; lia).
    assert (HNUL : ~ In (Z_to_bv 8 0) argv1). { apply (proj1 (Forall_forall _ _) VA4). eapply nth_error_In. exact HA1. }
    assert (HSLD : Namei.path_has_slash argv1 = false /\ Fs.path_eqb argv1 Namei.dotdot_path = false).
    { clear - HA1 VA5. destruct argv as [|x tlv]; [discriminate|]. cbn [tl] in VA5.
      change (nth_error tlv 0 = Some argv1) in HA1.
      exact (proj1 (Forall_forall _ _) VA5 _ (nth_error_In _ _ HA1)). }
    assert (HPL : (Z.of_nat (length argv1) < 2^24 /\ (- (P1 + Z.of_nat (length argv1) + 1)) mod 8 <= Z.of_nat (length slack1))%Z).
    { split; [|exact SLK1]. pose proof (proj1 (Forall_forall _ _) VA3 _ (nth_error_In _ _ HA1)). cbn beta in *. lia. }
    assert (HPEND : (P1 + Z.of_nat (length argv1) + 1 + Z.of_nat (length slack1) <= USP + Z.of_nat (length SBK) - 16)%Z) by lia.
    pose proof (bytes_at_bound _ _ _ _ STRS) as PBS. rewrite length_app in PBS; cbn [length] in PBS.
    pose proof (bytes_at_bound _ _ _ _ STR1) as PB. rewrite length_app in PB; cbn [length] in PB.
    assert (RA1 : rng RNG (USP + 16) 8).
    { eapply rng_sub'; [exact CSR|]. rewrite BL. unfold raw_len, struct_size, InitMem.argc, InitMem.envc. clear - RN. lia. }
    unfold read_all. rewrite to_bytes_of_bytes.
    ienterG. zstep. zstep. zstep. zstep.
    name_spm.
    apply evtF_done. eapply implMG_msys_of_enode.
    { eapply (open_spec RNG _ spm _ (Z_to_bv 64 ATPv)) with (lo := LO) (path := argv1) (errv := e) (canary := can);
        [ rewrite Hspm; exact ST | rewrite unsigned_lit by lia; exact STR1 | rewrite ETP; exact T2 | exact L2 | exact L3 | exact MI | reflexivity | exact HNUL
        | exact (proj1 HSLD) | exact (proj2 HSLD)
        | rewrite Hspm; lia | rewrite Hspm, ETP; lia | rewrite Hspm, unsigned_lit by lia; lia
        | rewrite ETP, unsigned_lit by lia; lia | rewrite Hspm; unfold ssp_guard; lia
        | rewrite ETP; unfold ssp_guard; lia | rewrite ETP; unfold got_ssp; lia | rewrite ETP; lia
        | rewrite Hspm; eapply rng_sub'; [exact R2| lia] | rewrite ETP; eapply rng_sub'; [exact R5| lia]
        | rewrite unsigned_lit by lia; eapply rng_sub'; [exact CSR| lia] | exact R3 ]. }
    intros r RNG' ms' PO. unfold open_post in PO. destruct PO as (-> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 9%nat; intros MU WM MI' ST' ERR STR GOT GUARD Hr; nd_post).
    replace (ret_pc (Z_to_bv 64 0x84160)) with (Z_to_bv 64 0x84160) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite ETP in *. rewrite unsigned_lit in STR by lia.
    lazymatch type of MU with munch _ ?ma ?mb => transport_after_call asegs ma mb MU WM end.
    clear MI. rename MI' into MI.
    apply (munch_weaken _ [(ATPv + -164, ATPv + -160); (bv_unsigned spm - 112, bv_unsigned spm)]%Z) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
    assert (G' : GIOA L RNG s [] FB [] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
    { eapply (gd_frame_errno _ _ _ GD); [exact G | exact MU | exact WM | | exact ERR].
      constructor; [left; left; cbn [fst snd]; rewrite Hspm; lia| constructor]. }
    clear MU WM G CM1 CM2. (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G') 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G') as CSO'.
    destruct r as [err|fd].
    - (* [comment removed for export] *)
      unfold open_ret. rewrite Hspm in *. unname_spm.
      cbv beta iota. ienterG. zstep. if_true_by ltz_cond_m1. do 9 zstep.
      name_spm.
      apply evtF_done. unfold diag, diag_cannot_open. eapply implMG_bind.
      { eapply EPR_OPEN with (P := P1) (str := argv1) (slack := slack1); [ | | reflexivity | reflexivity | reflexivity | | exact STRS | exact HNUL | exact (proj1 HPL) | exact (proj2 HPL) | | intros a Ha; left; rewrite Hspm; lia ].
        - std_pre_tac G' ST' MI Hspm R1 R2 R3 R4 R5.
        - rewrite Hspm; generalize TOP_lo; clear; intros; lia.                 (* [comment removed for export] *)
        - eapply drv_lit_mobjA; [exact G' | exact R3 | exact R4 | unfold FMT_CANNOT_OPEN; lia | unfold FMT_CANNOT_OPEN, DRV_RODATA_HI; lia | lia].
        - eapply mobjA_sub; [exact CSO' | lia | lia | lia]. }
      intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP RS) as RS'.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
      replace (ret_pc (Z_to_bv 64 0x84384)) with (Z_to_bv 64 0x84384) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *. unname_spm.
      ienterG. zstep.
      apply evtF_done. apply implMG_ret. apply evtF_done.
      unfold RAX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2|]. split; [exact ST2| exact RS'].
    - (* [comment removed for export] *)
      unfold open_ret. rewrite Hspm in *. unname_spm.
      cbv beta iota. ienterG. zstep. if_false_by (ltz_cond_false fd ltac:(lia)). do 4 zstep.
      name_spm.
      apply evtF_done. eapply implMG_bind.
      { eapply MALLOC with (n := 65536%Z); [ | reflexivity | lia | ].
        - std_pre_tac G' ST' MI Hspm R1 R2 R3 R4 R5.
        - eapply (unw_main RNG _ AMALLOC_PC spm _ _ 0x84174%Z);
            [ rewrite Hspm, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold AMALLOC_PC, ACLIENT_LO, ACLIENT_HI; lia
            | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | exact R1 | rewrite Hspm; lia ]. }
      intros r s' RNG1 ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP1 a0v m1 E OF1 MI1 ST1 AG1 CASES; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP1 RS) as RS1.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      replace (ret_pc (Z_to_bv 64 0x84174)) with (Z_to_bv 64 0x84174) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ _ AG1) in STR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ _ AG1) in STRS; [|lia].
      unname_spm.
      destruct r as [q|]; [| destruct CASES].
      (nd_pre CASES 3%nat; intros A junk ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G1 BLK; nd_post).
      (nd_pre (blk_facts RNG1 s' _ FB m1 (q, A, 65536%Z) G1 ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros _ B1 B2; nd_post). cbn [cb_addr cb_size fst snd] in B1, B2.
      (* [comment removed for export] *)
      cbv beta iota. ienterG. zstep. if_false_by (eqz_cond_false A ltac:(lia)). zstep. zstep. zstep. zstep.
      apply evtF_done. eapply implMG_bind with (Q1 := LX fd P1 argv1 slack1).
      { eapply loop_spec; [| exact HNUL | exact HPL | exact HPEND].
        unfold LH. cbn [rd_buf rd_cap rd_len rd_chunks rd_content concat].
        repeat (lazymatch goal with |- @ex (list byte) _ => exists (@nil byte) | |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [right; split; reflexivity|].
        split.
        { split; [exists FB; exact G1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
          split; [exists junk; apply rw_cells_nil_CB; exact BLK|].
          cbn [length Z.of_nat]. split; [lia|]. split; [unfold MAX_INPUT; lia|]. split; [exists 0%Z; reflexivity| exact RS1]. }
        split; [reflexivity|]. split; [reflexivity|].
        split; [exact STRS|]. split; [lia| lia]. }
      intros res s'' RNG2 ms'' LXH. destruct res as [|q' content].
      + cbv beta iota. apply implMG_ret. apply evtF_done. exact LXH.
      + (nd_pre LXH 31%nat; intros ra' gp' y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 w5 w6 w7 w8 w9 w10 w11 y3 y4 y5 y6 F' fc' m'' A' cap' CBs' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros MB HC; nd_post).
        (nd_pre MB 9%nat; intros (FB2 & G2) MI2 ST2 (h0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & FR2) (junk2 & BUF2) HLC2 HCAP2 HJ2 RS2; nd_post).
        (pose proof RS2 as ndP__; nd_pre ndP__ 5%nat; intros Q1 Q2 Q3 Q4 Q5; nd_post).
        destruct (gd_errno _ _ _ GD _ _ _ _ _ _ _ G2) as (e2 & ERR2).
        (nd_pre (blk_facts RNG2 s'' _ FB2 m'' (q', A', cap') G2 ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros _ D1 D2; nd_post). cbn [cb_addr cb_size fst snd] in D1, D2.
        pose proof (blk_tclr RNG2 s'' _ FB2 m'' (q', A', cap') G2 ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) as BTLS. cbn [cb_addr cb_size fst snd] in BTLS.
        cbv beta iota. ienterG. zstep. zstep.
        name_spm.
        apply evtF_done. eapply implMG_msys_of_enode.
        { eapply (close_spec RNG2 _ spm _ (Z_to_bv 64 ATPv)) with (lo := LO) (fd := fd) (errv := e2);
            [ rewrite Hspm; exact ST2 | rewrite ETP; exact ERR2 | exact MI2 | reflexivity | lia | rewrite Hspm; lia | rewrite Hspm, ETP; lia | rewrite ETP; lia
            | rewrite Hspm; eapply rng_sub'; [exact Q2| lia] | rewrite ETP; eapply rng_sub'; [exact Q5| lia] ]. }
        intros r RNG3 ms' PO. unfold close_post in PO. destruct PO as (-> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MU WM MI3 ST3 ERR3; nd_post).
        replace (ret_pc (Z_to_bv 64 0x8421c)) with (Z_to_bv 64 0x8421c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite ETP in *.
        lazymatch type of MU with munch _ ?ma ?mb => transport_after_call asegs ma mb MU WM end.
        apply (munch_weaken _ [(ATPv + -164, ATPv + -160); (bv_unsigned spm - 32, bv_unsigned spm)]%Z) in MU.
        2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
        assert (G3 : GIOA L RNG2 s'' [(q', A', cap')] FB2 [] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
        { eapply (gd_frame_errno _ _ _ GD); [exact G2 | exact MU | exact WM | | exact ERR3].
          constructor; [left; left; cbn [fst snd]; rewrite Hspm; lia| constructor]. }
        rewrite Hspm in *. unname_spm.
        apply implMG_ret. apply evtF_done.
        unfold RAX. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [| exact HC].
        split; [exists FB2; exact G3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists h0, g1, g2, g3, g4, g5, g6, g7, g8; exact FR2|].
        split; [exists junk2; exact BUF2|]. split; [exact HLC2|]. split; [exact HCAP2|]. split; [exact HJ2| exact RS2].
  Qed.
  End Zd5.
  #[using="FO fflagA GL GD MALLOC FREE EPR_OPEN EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma read_all_spec : ltac:(let t := eval cbv delta [read_all_spec__stmt] in read_all_spec__stmt in exact t).
  Proof. exact read_all_spec__body. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_ret_spec__stmt : Prop := forall s RNG (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (FB : list cblk) (q : hptr) (A cap code : Z),
    GIOA L RNG s [(q, A, cap)] FB [] m -> mem_inv asegs m -> stk asegs m LO (USP + -128) -> mframe m -> rngs RNG -> (0 <= code <= 255)%Z ->
    implMG RNG (pfree HO q ;;; mret code) s main_post
      (MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84314) fc None m (seg_rom asegs)).
  Section Zd6.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 1).
  Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 2).
  Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 3).
  Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 4).
  Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 5).
  Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 6).
  Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 7).
  Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 8).
  Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 9).
  Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 10).
  Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 11).
  Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 12).
  Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 13).
  Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 14).
  Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 15).
  Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 16).
  Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 17).
  Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 18).
  Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 19).
  Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 20).
  Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 21).
  Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 22).
  Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 23).
  Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 24).
  Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 25).
  Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 26).
  Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 27).
  Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 28).
  Variable F : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 29).
  Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 30).
  Variable m : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 31).
  Variable FB : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 32).
  Variable q : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 33).
  Variable A : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 34).
  Variable cap : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 35).
  Variable code : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 36).
  #[using="argv envp uid hw rnd FREE LO_lo LO_hi USP16 TOP47 USP47 TRD AT_EXIT_I"] Lemma free_ret_spec__body : ltac:(let T := type of (fun (h : free_ret_spec__stmt) => h s RNG ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m FB q A cap code) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, (ra, (gp, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (FB, (q, (A, (cap, code))))))))))))))))))))))))))))))))))))) as _.
 intros G MI ST (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) RS HCODE.
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    ienterG. zstep. zstep.
    name_spm.
    apply evtF_done. eapply implMG_bind.
    { eapply FREE with (C1 := @nil cblk) (C2 := @nil cblk) (q := q) (A := A) (n := cap); [| reflexivity |].
      - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
      - eapply (unw_main RNG _ AFREE_PC spm _ _ 0x8431c%Z);
          [ rewrite Hspm, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia
          | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | exact R1 | rewrite Hspm; lia ]. }
    intros [] s' RNG' ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
    unfold hpost_regs in E. destruct_exs E. subst ms'.
    cbn [app] in AG2, G2.
    pose proof (rngs_le _ _ FP RS) as RS'.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
    replace (ret_pc (Z_to_bv 64 0x8431c)) with (Z_to_bv 64 0x8431c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite Hspm in *.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
    unname_spm.
    ienterG. do 12 zstep.
    replace (ret_pc (Z_to_bv 64 RA_MAIN)) with (Z_to_bv 64 RA_MAIN) by (symmetry; apply ret_pc_even; [unfold RA_MAIN; lia|reflexivity]).
    unfold RA_MAIN. zstep.
    apply evtF_done. apply implMG_ret. apply evtF_done. unfold main_post.
    release_frame FR ST2 (USP + -48)%Z.
    eapply AT_EXIT_I; [exact G2 | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; generalize LO_hi; lia
                      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; aln16 | exact RS'].
  Qed.
  End Zd6.
  #[using="argv envp uid hw rnd FREE LO_lo LO_hi USP16 TOP47 USP47 TRD AT_EXIT_I"] Lemma free_ret_spec : ltac:(let t := eval cbv delta [free_ret_spec__stmt] in free_ret_spec__stmt in exact t).
  Proof. exact free_ret_spec__body. Qed.

  #[using="rc sp0 argv envp uid hw rnd"] Lemma geu_cond_true : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
  Proof. intros. rewrite ltu_cond_false by lia. reflexivity. Qed.
  #[using="rc sp0 argv envp uid hw rnd"] Lemma geu_cond_false : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
  Proof. intros. rewrite ltu_cond_true by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition tail_spec__stmt : Prop := forall s RNG ms q content,
    RAX (RdDone q content) s RNG ms ->
    implMG RNG (let len := zlength content in
                 if len <? HDR_MIN then diag DShortHdr ;;; pfree HO q ;;; mret 2
                 else let cfg_word := le16 content in
                      let count_allocs := Z.testbit cfg_word 15 in
                      let config_len := Z.land cfg_word 0x7fff in
                      if len <? HDR_MIN + config_len then diag DCfgOverrun ;;; pfree HO q ;;; mret 2
                      else let config := firstn (Z.to_nat config_len) (skipn 2 content) in
                           let payload := skipn (Z.to_nat (6 + config_len)) content in
                           status <- run HO FO sites config payload ;;
                           (let status' := (if count_allocs then 0 else status)%Z in pfree HO q ;;; mret status'))%Z
      s main_post ms.
  Section Zd7.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 1).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 2).
  Variable q : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 3).
  Variable content : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 4).
  #[using="TP fflagA argv envp uid hw rnd GL GD FREE EFW TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF AT_EXIT_I drv_lit_mobjA block_mobjA"] Lemma tail_spec__body : ltac:(let T := type of (fun (h : tail_spec__stmt) => h s RNG ms q content) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, (ms, (q, content))))) as _.
    intros RX.
    (nd_pre RX 33%nat; intros ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A cap CBs ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros MB ndR3__; nd_post; revert ndR3__; intros ->).
    (nd_pre MB 9%nat; intros (FB & G) MI ST FRm (junk & BUF) HLC HCAP HJ RS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    (nd_pre (blk_facts RNG s _ FB m (q, A, cap) G ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros (_ & _ & _ & BRNG & _) B1 B2; nd_post). cbn [cb_addr cb_size fst snd] in BRNG, B1, B2.
    unfold zlength, of_bytes at 1. rewrite length_map. set (len := Z.of_nat (length CBs)) in *.
    cbv zeta. unfold HDR_MIN.
    ienterG. zstep. zstep.
    destruct (Z_lt_le_dec len 6) as [SHORT|LONG].
    - (* [comment removed for export] *)
      replace (len <? 6)%Z with true by (symmetry; apply Z.ltb_lt; exact SHORT).
      if_true_by (geu_cond_true 5 len ltac:(lia) ltac:(lia)).
      do 9 zstep.
      (nd_pre MSG_SHORT_HDR_ok 3%nat; intros RB EM LM; nd_post).
      name_spm.
      apply evtF_done. unfold diag, diag_short_hdr. rewrite <- EM. eapply implMG_bind.
      { eapply EFW with (MSG := MSG_SHORT_HDR) (bs := MSG_SHORT_HDR_bytes);
          [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI | exact RB | unfold MSG_SHORT_HDR; lia | rewrite LM; unfold MSG_SHORT_HDR; lia]
            | rewrite LM; unfold MSG_SHORT_HDR, DRV_RODATA_LO, DRV_RODATA_HI; lia | rewrite LM; lia | ].
        - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
        - eapply drv_lit_mobjA; [exact G | exact R3 | exact R4 | unfold MSG_SHORT_HDR; lia | rewrite LM; unfold MSG_SHORT_HDR, DRV_RODATA_HI; lia | lia]. }
      intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP RS) as RS'.
      replace (ret_pc (Z_to_bv 64 0x84314)) with (Z_to_bv 64 0x84314) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *.
      (nd_pre FRm 10%nat; intros j0 f1 f2 f3 f4 f5 f6 f7 f8 FR; nd_post). apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_spm.
      eapply free_ret_spec; [exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact RS' | lia].
    - (* [comment removed for export] *)
      replace (len <? 6)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      if_false_by (geu_cond_false 5 len ltac:(lia) ltac:(lia)).
      destruct CBs as [|c0 [|c1 rest]]; [subst len; cbn in LONG; lia..|].
      pose proof BUF as BUF'. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BUF' as [BUF1 _].
      assert (BY : bytes_at asegs m A (c0 :: c1 :: rest)).
      { destruct BUF1 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
      pose proof (bytes_at_read asegs _ A _ 0 1 BY ltac:(lia) ltac:(cbn; lia)) as HR0. change (Z.to_nat 0) with 0%nat in HR0. cbn [firstn skipn] in HR0. rewrite Z.add_0_r in HR0.
      pose proof (bytes_at_read asegs _ A _ 1 1 BY ltac:(lia) ltac:(cbn; lia)) as HR1. change (Z.to_nat 1) with 1%nat in HR1. cbn [firstn skipn] in HR1.
      pose proof (bv_unsigned_in_range 8 c0) as RC0. pose proof (bv_unsigned_in_range 8 c1) as RC1. unfold bv_modulus in RC0, RC1. cbn in RC0, RC1.
      zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite hdr_hi. rewrite lor_disjoint8 by (pose proof (Z.mod_pos_bound (bv_unsigned c1) 128); lia).
      assert (EL16 : le16 (of_bytes (c0 :: c1 :: rest)) = (bv_unsigned c0 + bv_unsigned c1 * 256)%Z) by reflexivity.
      rewrite EL16. rewrite land_7fff by lia. rewrite testbit15 by lia.
      set (Lc := (bv_unsigned c1 mod 128 * 256 + bv_unsigned c0)%Z) in *.
      assert (HL : (0 <= Lc < 32768)%Z) by (pose proof (Z.mod_pos_bound (bv_unsigned c1) 128); lia).
      unfold of_bytes. rewrite length_map. fold len.
      zstep.
      destruct (Z_lt_le_dec len (6 + Lc)) as [OVR|OK].
      + (* [comment removed for export] *)
        replace (len <? 6 + Lc)%Z with true by (symmetry; apply Z.ltb_lt; exact OVR).
        if_true_by (ltu_cond_true len (Lc + 6)%Z ltac:(lia) ltac:(lia)).
        do 8 zstep.
        (nd_pre MSG_CFG_OVERRUN_ok 3%nat; intros RB EM LM; nd_post).
        name_spm.
        apply evtF_done. unfold diag, diag_cfg_overrun. rewrite <- EM. eapply implMG_bind.
        { eapply EFW with (MSG := MSG_CFG_OVERRUN) (bs := MSG_CFG_OVERRUN_bytes);
            [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI | exact RB | unfold MSG_CFG_OVERRUN; lia | rewrite LM; unfold MSG_CFG_OVERRUN; lia]
              | rewrite LM; unfold MSG_CFG_OVERRUN, DRV_RODATA_LO, DRV_RODATA_HI; lia | rewrite LM; lia | ].
          - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
          - eapply drv_lit_mobjA; [exact G | exact R3 | exact R4 | unfold MSG_CFG_OVERRUN; lia | rewrite LM; unfold MSG_CFG_OVERRUN, DRV_RODATA_HI; lia | lia]. }
        intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
        unfold hpost_regs in E. destruct_exs E. subst ms'.
        pose proof (rngs_le _ _ FP RS) as RS'.
        replace (ret_pc (Z_to_bv 64 0x84314)) with (Z_to_bv 64 0x84314) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite Hspm in *.
        (nd_pre FRm 10%nat; intros j0 f1 f2 f3 f4 f5 f6 f7 f8 FR; nd_post). apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
        unname_spm.
        eapply free_ret_spec; [exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact RS' | lia].
      + (* [comment removed for export] *)
        replace (len <? 6 + Lc)%Z with false by (symmetry; apply Z.ltb_ge; lia).
        if_false_by (ltu_cond_false len (Lc + 6)%Z ltac:(lia) ltac:(lia)).
        assert (exists d0 d1 d2 d3 rest', skipn (Z.to_nat (2 + Lc)) (c0 :: c1 :: rest) = d0 :: d1 :: d2 :: d3 :: rest') as (d0 & d1 & d2 & d3 & rest' & ED).
        { pose proof (length_skipn (Z.to_nat (2 + Lc)) (c0 :: c1 :: rest)) as LS.
          destruct (skipn (Z.to_nat (2 + Lc)) (c0 :: c1 :: rest)) as [|d0 [|d1 [|d2 [|d3 rest']]]]; cbn [length] in LS, LONG, OK; try (subst len; cbn [length] in *; lia).
          repeat eexists. }
        assert (BYp : bytes_at asegs m (A + (2 + Lc)) (d0 :: d1 :: d2 :: d3 :: rest')).
        { rewrite <- ED. pose proof BY as BY2. rewrite <- (firstn_skipn (Z.to_nat (2 + Lc)) (c0 :: c1 :: rest)) in BY2.
          apply bytes_at_app in BY2 as [_ X]. rewrite length_firstn in X.
          replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + Lc)) (length (c0 :: c1 :: rest))))%Z with (A + (2 + Lc))%Z in X by (subst len; lia). exact X. }
        pose proof (bytes_at_read asegs _ _ _ 0 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB0. change (Z.to_nat 0) with 0%nat in HB0. cbn [firstn skipn] in HB0.
        pose proof (bytes_at_read asegs _ _ _ 1 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB1. change (Z.to_nat 1) with 1%nat in HB1. cbn [firstn skipn] in HB1.
        pose proof (bytes_at_read asegs _ _ _ 2 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB2. change (Z.to_nat 2) with 2%nat in HB2. cbn [firstn skipn] in HB2.
        pose proof (bytes_at_read asegs _ _ _ 3 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB3. change (Z.to_nat 3) with 3%nat in HB3. cbn [firstn skipn] in HB3.
        do 6 zstep. do 16 zstep.
        (* [comment removed for export] *)
        (nd_pre FRm 10%nat; intros j0 f1 f2 f3 f4 f5 f6 f7 f8 FR; nd_post).
        assert (Elen : len = Z.of_nat (length (c0 :: c1 :: rest))) by reflexivity. clearbody len.
        name_spm.
        apply evtF_done. eapply implMG_bind.
        { eapply TRUN with (L := L) (RNG := RNG) (CL := [(q, A, cap)]) (FB := FB) (lo := LO) (Lc := Lc) (A := A) (content := c0 :: c1 :: rest);
            [ | rewrite Hspm; generalize TOP_lo; lia | exact TRD | exact TRF | exact BY | lia | lia | unfold MAX_INPUT in *; lia
              | exists (q, A, cap); split; [left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]
              | reflexivity | reflexivity | f_equal; lia | f_equal; lia ].
          std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5. }
        intros r s' RNG' ms' PO. unfold target_run_post in PO. destruct PO as (FP & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MI2 ST2 AG2 G2 Hr; nd_post). clear MI.
        pose proof (rngs_le _ _ FP RS) as RS'.
        repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
        replace (ret_pc (Z_to_bv 64 0x84294)) with (Z_to_bv 64 0x84294) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite Hspm in *.
        apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
        unname_spm.
        cbv zeta. ienterG. zstep.
        destruct (Z.leb_spec 128 (bv_unsigned c1)) as [CA|NCA].
        * (* [comment removed for export] *)
          replace (128 <=? bv_unsigned c1)%Z with true by (symmetry; apply Z.leb_le; exact CA).
          if_true_by (eq_trans (sxb_ltz c1) (proj2 (Z.leb_le _ _) CA)).
          do 5 zstep. zstep.
          apply evtF_done. eapply free_ret_spec; [exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact RS' | lia].
        * replace (128 <=? bv_unsigned c1)%Z with false by (symmetry; apply Z.leb_gt; exact NCA).
          if_false_by (eq_trans (sxb_ltz c1) (proj2 (Z.leb_gt _ _) NCA)).
          zstep. zstep.
          apply evtF_done. eapply free_ret_spec; [exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact RS' | lia].
  Qed.
  End Zd7.
  #[using="TP fflagA argv envp uid hw rnd GL GD FREE EFW TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF AT_EXIT_I drv_lit_mobjA block_mobjA"] Lemma tail_spec : ltac:(let t := eval cbv delta [tail_spec__stmt] in tail_spec__stmt in exact t).
  Proof. exact tail_spec__body. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition main_spec__stmt : Prop := forall s RNG ms,
    main_entry s RNG ms ->
    implMG RNG (main_prog HO FO sites (argv_Z argv)) s main_post ms.
  Section Zd8.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'main_spec__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'main_spec__stmt 1).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'main_spec__stmt 2).
  #[using="TP fflagA GL GD MALLOC FREE EPR_USAGE EPR_OPEN EPR_READ EPR_BIG EFW SITE_RS TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF AT_EXIT_I drv_lit_mobjA drv_stack_writes block_mobjA"] Lemma main_spec__body : ltac:(let T := type of (fun (h : main_spec__stmt) => h s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, ms))) as _.
    intros ME.
    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2].
    2:{ exact (main_usage s RNG ms ME NE2). }
    (nd_pre ME 31%nat; intros gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m FB ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros G MI ST VA RS CS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI. unfold MAIN_ENTRY.
    assert (EA : exists av0 av1, argv = [av0; av1]) by (destruct argv as [|x [|y [|z w]]]; cbn in E2; try lia; eauto).
    (nd_pre EA 3%nat; intros av0 av1 EARGV; nd_post).
    unfold main_prog, main_model. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length argv) =? 2)%Z with true by (symmetry; apply Z.eqb_eq; exact E2). cbn [negb].
    replace (nth 1 (argv_Z argv) []) with (map bv_unsigned av1) by (rewrite EARGV; reflexivity).
    pose proof (munch_refl [(USP - 128, USP - 48)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    carve_frame 80%nat ST.
    do 11 zstep.
    replace (argc argv) with 2%Z by (unfold argc; lia).
    zstep. if_false_by (eq_cond 2).
    lazymatch type of MU with munch _ _ ?mb =>
      destruct (drv_stack_writes L RNG s [] FB m mb _ (USP - 48)%Z G MU WM) as [G1 AG0]; [constructor; [cbn [fst snd]; lia| constructor] | lia |] end.
    clear MU WM.
    apply evtF_done. eapply implMG_bind with (Q1 := RAX).
    - eapply (read_all_spec _ _ _ av1); [| rewrite EARGV; reflexivity | exact VA].
      unfold P2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G1|]. split; [exact MI|]. split; [exact ST|].
      split; [eexists _, _, _, _, _, _, _, _, _; exact FR|]. split; [exact RS|].
      first [exact CS | assumption | match goal with HB : bytes_at _ _ USP SBK |- _ => exact HB end].
    - intros res s' RNG' ms' RX. destruct res as [|q content].
      + cbv beta iota. apply implMG_ret.
        eapply (at_exit2_exit s' RNG' ms' (fun _ s0 R0 ms0 => main_post 2 s0 R0 ms0)); [exact RX | intros ms0 HP; exact HP].
      + cbv beta iota. apply tail_spec. exact RX.
  Qed.
  End Zd8.
  #[using="TP fflagA GL GD MALLOC FREE EPR_USAGE EPR_OPEN EPR_READ EPR_BIG EFW SITE_RS TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF AT_EXIT_I drv_lit_mobjA drv_stack_writes block_mobjA"] Theorem main_spec : ltac:(let t := eval cbv delta [main_spec__stmt] in main_spec__stmt in exact t).
  Proof. exact main_spec__body. Qed.
End Main.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.CallKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.ImgAny.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.I_read.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvFactsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_target_runA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ _ _ => apply implMG_from_evtF end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition img_lit (A : Z) (n : nat) : list byte := match image_bytes asegs A n with Some bs => bs | None => [] end.
Definition MSG_OOM_bytes : list byte := img_lit MSG_OOM 19.
Definition MSG_SHORT_HDR_bytes : list byte := img_lit MSG_SHORT_HDR 31.
Definition MSG_CFG_OVERRUN_bytes : list byte := img_lit MSG_CFG_OVERRUN 31.

Lemma MSG_OOM_ok : ro_bytes_b asegs MSG_OOM MSG_OOM_bytes = true /\ map bv_unsigned MSG_OOM_bytes = List.concat pieces_oom /\ length MSG_OOM_bytes = 19%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma MSG_SHORT_HDR_ok : ro_bytes_b asegs MSG_SHORT_HDR MSG_SHORT_HDR_bytes = true /\ map bv_unsigned MSG_SHORT_HDR_bytes = List.concat pieces_short_hdr /\ length MSG_SHORT_HDR_bytes = 31%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma MSG_CFG_OVERRUN_ok : ro_bytes_b asegs MSG_CFG_OVERRUN MSG_CFG_OVERRUN_bytes = true /\ map bv_unsigned MSG_CFG_OVERRUN_bytes = List.concat pieces_cfg_overrun /\ length MSG_CFG_OVERRUN_bytes = 31%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma lit_bytes_at : forall m A bs, mem_inv asegs m -> ro_bytes_b asegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z -> bytes_at asegs m A bs.
Proof. intros m A bs MI RB HA HB. apply ro_bytes_at; [exact MI | exact HA | exact HB |]. apply ro_bytes_b_sound. exact RB. Qed.

Lemma cap_double_ok : forall cap j, (cap = 65536 * 2 ^ j)%Z -> (0 <= j)%Z -> (cap < 67108864)%Z ->
  (cap * 2 = 65536 * 2 ^ (j + 1))%Z /\ (cap * 2 <= 67108864)%Z.
Proof.
  intros cap j -> Hj Hc. split. { rewrite Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z. lia. }
  assert (Hj10 : (2 ^ j < 2 ^ 10)%Z) by (change (2 ^ 10)%Z with 1024%Z; lia).
  apply Z.pow_lt_mono_r_iff in Hj10; [|lia|lia].
  assert (2 ^ (j + 1) <= 2 ^ 10)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 10)%Z with 1024%Z in H. rewrite Z.pow_add_r in H by lia. change (2 ^ 1)%Z with 2%Z in H. lia.
Qed.

Lemma ltu_cond_true : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.
Lemma ltu_cond_false : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltz_cond_false : forall x, (0 <= x < 2^63)%Z -> bv_lts (Z_to_bv 64 x) z64 = false.
Proof. intros. rewrite bv_lts_zero_r, unsigned_lit by lia. apply Z.leb_gt. lia. Qed.
Lemma ltz_cond_m1 : bv_lts (Z_to_bv 64 (-1)) z64 = true.
Proof. reflexivity. Qed.
Lemma neq_cond : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
Proof. intros x y Hx Hy Hn. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hn. Qed.
Lemma eq_cond : forall x, negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 x)) = false.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma beq_cond : forall x, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 x) = true.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma bne_cond_false : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy Hn. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma forall_range : forall (f : Z -> bool) (n : nat),
  forallb f (map Z.of_nat (seq 0 n)) = true -> forall z, (0 <= z < Z.of_nat n)%Z -> f z = true.
Proof.
  intros f n Hf z Hz. rewrite forallb_forall in Hf. apply Hf. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Lemma hdr_hi : forall c1 : byte,
  Z.shiftr ((Z.shiftl (bv_unsigned (sxb c1)) 57) mod 18446744073709551616) 49 = ((bv_unsigned c1) mod 128 * 256)%Z.
Proof.
  intros c1. unfold sxb. rewrite unsigned_lit_wrap. unfold bv_signed.
  pose proof (bv_unsigned_in_range 8 c1) as R. unfold bv_modulus in R. cbn in R.
  generalize dependent R. generalize (bv_unsigned c1). intros u R.
  pose proof (forall_range (fun u => Z.eqb (Z.shiftr ((Z.shiftl ((bv_swrap 8 u) mod 2^64) 57) mod 18446744073709551616) 49) (u mod 128 * 256)) 256 ltac:(vm_cast_no_check (eq_refl true)) u ltac:(cbn; lia)) as E.   (* [comment removed for export] *)
  apply Z.eqb_eq in E. exact E.
Qed.

Lemma lor_disjoint8 : forall m u0, (0 <= m < 128)%Z -> (0 <= u0 < 256)%Z -> Z.lor (m * 256) u0 = (m * 256 + u0)%Z.
Proof.
  intros m u0 Hm Hu.
  pose proof (forall_range (fun m => forallb (fun u0 => Z.eqb (Z.lor (m * 256) u0) (m * 256 + u0)) (map Z.of_nat (seq 0 256))) 128 ltac:(vm_cast_no_check (eq_refl true)) m ltac:(cbn; lia)) as E.   (* [comment removed for export] *)
  cbn beta in E. pose proof (forall_range _ 256 E u0 ltac:(cbn; lia)) as E2. apply Z.eqb_eq in E2. exact E2.
Qed.

Lemma land_7fff : forall u0 u1, (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> Z.land (u0 + u1 * 256) 32767 = (u1 mod 128 * 256 + u0)%Z.
Proof.
  intros. change 32767%Z with (2^15 - 1)%Z. rewrite zb_land_mask by lia. change (2^15)%Z with 32768%Z.
  rewrite (Z.div_mod u1 128) at 1 by lia.
  replace (u0 + (128 * (u1 / 128) + u1 mod 128) * 256)%Z with ((u1 mod 128 * 256 + u0) + (u1 / 128) * 32768)%Z by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound u1 128). lia.
Qed.

Lemma testbit15 : forall u0 u1, (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> Z.testbit (u0 + u1 * 256) 15 = (128 <=? u1)%Z.
Proof.
  intros. destruct (Z.leb_spec 128 u1).
  - apply Z.testbit_true; [lia|]. change (2^15)%Z with 32768%Z.
    replace ((u0 + u1 * 256) / 32768)%Z with 1%Z; [reflexivity|]. Z.div_mod_to_equations. lia.
  - apply Z.testbit_false; [lia|]. change (2^15)%Z with 32768%Z.
    replace ((u0 + u1 * 256) / 32768)%Z with 0%Z; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

Lemma sxb_ltz : forall c1 : byte, bv_lts (sxb c1) (Z_to_bv 64 0) = (128 <=? bv_unsigned c1)%Z.
Proof.
  intros c1. rewrite bv_lts_zero_r. unfold sxb. rewrite unsigned_lit_wrap. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range 8 c1) as R. unfold bv_modulus in R. cbn in R.
  change (Z.of_N 8) with 8%Z. change (2^8)%Z with 256%Z. cbn [Z.div Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  destruct (Z.leb_spec 128 (bv_unsigned c1)).
  - apply Z.leb_le. Z.div_mod_to_equations. lia.
  - apply Z.leb_gt. Z.div_mod_to_equations. lia.
Qed.


Definition MAIN_STACK : Z := TARGET_RUN_STACK + 0x1000.    (* [comment removed for export] *)
Definition RA_MAIN : Z := 0x944a8.                          (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
(* [comment removed for export] *)
Local Lemma rw_bytes_b_zero_w : forall segs n A,
  (forall i, (0 <= i < Z.of_nat n)%Z -> seg_rom segs (wa (A + i)) = Some (Z_to_bv 8 0) /\ wview segs (fun _ => None) (wa (A + i)) <> None) ->
  rw_bytes_b segs A (repeat (Z_to_bv 8 0) n) = true.
Proof.
  intros segs n. induction n as [|n IH]; intros A H; cbn [repeat rw_bytes_b]; [reflexivity|].
  destruct (H 0%Z ltac:(lia)) as [E1 E2]. rewrite Z.add_0_r in E1, E2. rewrite E1.
  destruct (wview segs (fun _ => None) (wa A)) as [w|] eqn:EW; [|congruence].
  replace (bv_eqb (Z_to_bv 8 0) (Z_to_bv 8 0)) with true by reflexivity. cbn [andb].
  apply IH. intros i Hi. replace (A + 1 + i)%Z with (A + (1 + i))%Z by lia. apply H. lia.
Qed.
Local Lemma asegs_zero_rs : forall a, (0x5d1050 <= a < 0x5d1050 + 65536)%Z ->
  seg_rom asegs (wa a) = Some (Z_to_bv 8 0) /\ wview asegs (fun _ => None) (wa a) <> None.
Proof.
  intros a Ha.
  assert (ZW : zwin AsanUbsan_seg_bytes_003 (Uint63.of_Z 10829984) (Uint63.of_Z 131072) = true) by (vm_cast_no_check (eq_refl true)).
  assert (HB : hex_byte_at AsanUbsan_seg_bytes_003 (Z.to_N (a - 0xa7000)) = Some (Z_to_bv 8 0)).
  { apply (zwin_hex_byte_at _ _ _ _ ZW).
    - change (Uint63.to_Z (Uint63.of_Z 131072)) with 131072%Z. change (Uint63.to_Z PrimString.max_length) with 16777211%Z. lia.
    - change (Uint63.to_Z (Uint63.of_Z 10829984)) with 10829984%Z. lia.
    - change (Uint63.to_Z (Uint63.of_Z 10829984)) with 10829984%Z. change (Uint63.to_Z (Uint63.of_Z 131072)) with 131072%Z. lia. }
  assert (LEN : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5623808%N) by reflexivity.
  assert (F : find_segment asegs a 1 = Some AsanUbsan_segment_003).
  { unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments.
    cbn [find_segment AsanUbsan_segment_000 AsanUbsan_segment_001 AsanUbsan_segment_002 AsanUbsan_segment_003 seg_base seg_size Z.of_N].
    repeat match goal with |- context [Z.leb ?x ?y] =>
      first [ replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
            | replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia) ] end.
    reflexivity. }
  assert (HSB : segment_byte_at (seg_bytes AsanUbsan_segment_003) (Z.to_N (a - 0xa7000)) = Some (Z_to_bv 8 0)).
  { cbn [seg_bytes AsanUbsan_segment_003 segment_byte_at]. rewrite LEN.
    replace (Z.to_N (a - 0xa7000) <? 5623808)%N with true by (symmetry; apply N.ltb_lt; lia). exact HB. }
  assert (SEGB : Z.of_N (seg_base AsanUbsan_segment_003) = 0xa7000%Z) by reflexivity.
  split.
  - unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1%Z. rewrite F.
    replace (seg_readable AsanUbsan_segment_003) with true by reflexivity.
    rewrite SEGB. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite HSB. reflexivity.
  - unfold wview. rewrite wa_unsigned by lia. rewrite F.
    replace (seg_writable AsanUbsan_segment_003) with true by reflexivity.
    rewrite SEGB. rewrite HSB. discriminate.
Qed.
Local Lemma RS_ok_pre : rw_bytes_b asegs 0x5d1050 (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) = true.
Proof. apply rw_bytes_b_zero_w. intros i Hi. rewrite Z2Nat.id in Hi by lia. apply asegs_zero_rs. lia. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Main.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  (* [comment removed for export] *)
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation USP := (bv_unsigned sp0).
  Notation SBK := (build_stack_bytes a_phdrs sp0 argv envp uid hw rnd).
  Variables (L : alayout) (LO : Z).
  (* [comment removed for export] *)
  Variable AT_EXIT : Z -> PS -> footprint -> machine_state -> Prop.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GD : gia_drv_laws GIOA USP SBK.
  Hypothesis MALLOC : malloc_stmt_d HO GIOA.
  Hypothesis FREE : free_stmt_d HO GIOA.
  Hypothesis EPR_USAGE : eprintf_s_stmt_o GIOA FMT_USAGE 16 pieces_usage.
  Hypothesis EPR_OPEN : eprintf_s_stmt_o GIOA FMT_CANNOT_OPEN 20 pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt_o GIOA FMT_READ_ERROR 22 pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt_o GIOA FMT_TOO_BIG 32 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt_o GIOA.
  Hypothesis SITE_RS : sites SiteReadStage = READ_STAGE.
  Hypothesis TRUN : target_run_stmt_o HO FO sites GIOA TP.       (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis LO_lo : (ATOP + 4096 <= LO)%Z.
  Hypothesis LO_hi : (LO + MAIN_STACK <= USP - 128)%Z.
  Hypothesis USP16 : (USP mod 16 = 0)%Z.
  Hypothesis TOP_lo : (USP - 160 <= al_top L)%Z.
  Hypothesis TOP47 : (al_top L <= 2^47)%Z.
  Hypothesis USP47 : (USP + Z.of_nat (length SBK) <= 2^47)%Z.
  Hypothesis TRD : traces_drv L.
  Hypothesis TRF : traces_fuzz_one TP L RA_FUZZ [].

  (* [comment removed for export] *)
  Definition rngs (RNG : footprint) : Prop :=
    rng RNG LO (al_top L - LO) /\ rng RNG LO (USP - LO) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG.
  #[using="Type"] Lemma rngs_le : forall RNG RNG', fp_le RNG RNG' -> rngs RNG -> rngs RNG'.
  Proof.
    intros RNG RNG' FP (A & B & C & D & E). unfold rngs.
    split; [exact (rng_fp_le _ _ _ _ FP A)|]. split; [exact (rng_fp_le _ _ _ _ FP B)|]. split; [exact (rng_fp_le _ _ _ _ FP C)|].
    split; [exact (rng_fp_le _ _ _ _ FP D)| exact (rng_fp_le _ _ _ _ FP E)].
  Qed.

  Hypothesis AT_EXIT_I : forall (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (s : PS) (CL FB : list cblk) (code : Z),
    GIOA L RNG s CL FB [] m -> mem_inv asegs m -> stk asegs m LO (bv_unsigned sp) -> (LO + MAIN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= USP - 48)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> rngs RNG ->
    AT_EXIT code s RNG
      (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EXIT_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Let drv_lit_mobjA := drv_lit_mobjA FO GIOA fflagA USP SBK GL GD.
  Let drv_stack_writes := drv_stack_writes FO GIOA fflagA GL.
  Let drv_keeps := drv_keeps FO GIOA fflagA GL.
  Let block_mobjA := block_mobjA FO GIOA fflagA GL.

  (* [comment removed for export] *)
  #[using="rc sp0 argv envp uid hw rnd"] Lemma slack_trunc : forall (m : mem) (P : Z) (str slackF : list byte) (B : Z),
    bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slackF) -> ((- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slackF))%Z ->
    (P + Z.of_nat (length str) + 1 <= B)%Z -> (B mod 8 = 0)%Z ->
    exists slack, bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) /\ ((- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z
                  /\ (P + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= B)%Z.
  Proof.
    intros m P str slackF B HB HS HP HB8.
    set (k := Z.to_nat ((- (P + Z.of_nat (length str) + 1)) mod 8)).
    assert (K8 : (0 <= (- (P + Z.of_nat (length str) + 1)) mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
    assert (LK : length (firstn k slackF) = k) by (rewrite length_firstn; subst k; lia).
    exists (firstn k slackF). split; [| split].
    - rewrite <- (firstn_skipn k slackF) in HB.
      replace (str ++ Z_to_bv 8 0 :: firstn k slackF ++ skipn k slackF) with ((str ++ Z_to_bv 8 0 :: firstn k slackF) ++ skipn k slackF) in HB
        by (rewrite <- app_assoc; reflexivity).
      exact (proj1 (proj1 (bytes_at_app asegs m P _ _) HB)).
    - rewrite LK. subst k. rewrite Z2Nat.id by lia. lia.
    - rewrite LK. subst k. rewrite Z2Nat.id by lia. clear - HP HB8 K8. Z.div_mod_to_equations. lia.
  Qed.

  #[using="rc argv envp uid hw rnd LO LO_lo LO_hi USP47"] Lemma usp_facts : (0x7fff7f800000 + 100000 <= USP <= 2^47)%Z.
  Proof. pose proof (Nat2Z.is_nonneg (length SBK)) as N0. pose proof LO_lo as A. pose proof LO_hi as B. pose proof USP47 as C. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in B. atop_facts. lia. Qed.

  (* [comment removed for export] *)
  #[using="rc sp0 argv envp uid hw rnd"] Lemma unw_main : forall RNG (m : mem) PC (sp s0 ra : word) X,
    (bv_unsigned s0 <= bv_unsigned sp)%Z -> ra = Z_to_bv 64 X -> (ACLIENT_LO <= X < ACLIENT_HI)%Z -> ~ (ACLIENT_LO <= PC < ACLIENT_HI)%Z ->
    In [PC; X] (al_U L) -> In [PC] (al_U L) -> rng RNG LO (al_top L - LO) -> (bv_unsigned sp < 2^47)%Z ->
    unw_okA L RNG m LO PC sp s0 ra.
  Proof.
    intros RNG m PC sp s0 ra X HS0 -> HX HPC HU2 HU1 HR HSP.
    assert (EX : bv_unsigned (Z_to_bv 64 X) = X) by (apply unsigned_lit; unfold ACLIENT_LO, ACLIENT_HI in HX; lia).
    destruct (Z_lt_le_dec (bv_unsigned sp + 16) (al_top L)) as [LT|GE].
    - eapply unw_of_ucaller with (trC := @nil Z) (d := 0%nat);
        [ eapply (ucaller_data 0%nat _ _ _ _ _ X); [exact HS0 | reflexivity | exact HX | lia] | exact HPC | exact LT | rewrite EX; exact HU2 | exact HR ].
    - unfold unw_okA. rewrite EX. split; [exists (@nil Z); right; split; [exact GE| split; [exact HSP| exact HU1]]|].
      unfold ACLIENT_LO, ACLIENT_HI in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac name_spm :=
    remember (Z_to_bv 64 (USP + -128)) as spm eqn:Espm;
    assert (Hspm : bv_unsigned spm = (USP + -128)%Z) by (rewrite Espm; apply unsigned_lit; pose proof usp_facts; lia).
  Ltac unname_spm := match goal with Hs : bv_unsigned ?s = (USP + -128)%Z |- _ => is_var s; try rewrite Hs in *; subst s; clear Hs end.
  Ltac aln16 := generalize USP16; clear; intros; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Ltac std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5 :=
    pose proof usp_facts as USPF__;
    split; [exact G|]; split; [rewrite Hspm; exact ST|]; split; [exact LO_lo|];
    split; [generalize LO_hi; unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK, MALLOC_STACK, FREE_STACK; rewrite Hspm; lia|];
    split; [rewrite Hspm; split; [lia| exact TOP47]|]; split; [exact MI|]; split; [reflexivity|]; split; [rewrite Hspm; aln16|];
    split; [exact R1|]; split; [rewrite Hspm; eapply rng_sub'; [exact R2| lia]|]; split; [exact R3|]; split; [exact R4| exact R5].

  (* [comment removed for export] *)
  Definition main_entry (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (FB : list cblk),
      ms = MS (mkR (Z_to_bv 64 RA_MAIN) (Z_to_bv 64 (USP + -48)) gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1
                   (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (USP + 8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 MAIN_ENTRY) fc None m (seg_rom asegs)
      /\ GIOA L RNG s [] FB [] m /\ mem_inv asegs m /\ stk asegs m LO (USP + -48) /\ valid_argv argv /\ rngs RNG
      /\ bytes_at asegs m USP SBK.      (* [comment removed for export] *)

  Definition main_post : Z -> PS -> footprint -> machine_state -> Prop := AT_EXIT.

  (* [comment removed for export] *)
  Definition at_exit2 (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (CL FB : list cblk),
      ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x84410) fc None m (seg_rom asegs)
      /\ GIOA L RNG s CL FB [] m /\ mem_inv asegs m /\ stk asegs m LO (USP + -128) /\ rngs RNG.

  #[using="argv envp uid hw rnd LO_lo LO_hi USP16 USP47 AT_EXIT_I"] Lemma at_exit2_exit : forall s RNG ms (Q : rd_result (ptr:=hptr) -> PS -> footprint -> machine_state -> Prop),
    at_exit2 s RNG ms ->
    (forall ms', main_post 2 s RNG ms' -> Q RdExit s RNG ms') ->
    evtF asegs RNG (Q RdExit s RNG) ms.
  Proof.
    intros s RNG ms Q (ra & gp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & CL & FB & -> & G & MI & ST & RS) HQ.
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    zstep. zstep. apply evtF_done. apply HQ. unfold main_post.
    eapply AT_EXIT_I; [exact G | exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; generalize LO_hi; lia
                      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; aln16 | exact RS].
  Qed.

  (* [comment removed for export] *)
  Definition main_usage__stmt : Prop := forall s RNG ms,
    main_entry s RNG ms -> Z.of_nat (length argv) <> 2%Z ->
    implMG RNG (main_prog HO FO sites (argv_Z argv)) s main_post ms.
  Section Zd1.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'main_usage__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'main_usage__stmt 1).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'main_usage__stmt 2).
  #[using="fflagA GL GD EPR_USAGE LO_lo LO_hi USP16 TOP_lo TOP47 USP47 AT_EXIT_I drv_lit_mobjA drv_stack_writes"] Lemma main_usage__body : ltac:(let T := type of (fun (h : main_usage__stmt) => h s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, ms))) as _.
    intros (gp & t0 & t1 & t2 & s0 & s1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & FB & -> & G & MI & ST & VA & RS & CS) HC.
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post). pose proof VA as VA'. (nd_pre VA' 5%nat; intros VA1 VA2 VA3 VA4 VA5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI. unfold MAIN_ENTRY.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G) as CSO.
    (pose proof CSO as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ CSR _; nd_post).
    assert (EA : exists argv0 argvr, argv = argv0 :: argvr) by (destruct argv as [|x y]; [cbn in VA1; lia| eauto]).
    (nd_pre EA 3%nat; intros argv0 argvr EARGV; nd_post).
    assert (HA0 : nth_error argv 0 = Some argv0) by (rewrite EARGV; reflexivity).
    pose proof (raw_len_nonneg a_phdrs sp0 argv envp uid hw rnd) as RN.
    pose proof (build_stack_bytes_length a_phdrs sp0 argv envp uid hw rnd) as BL.
    pose proof (bytes_at_bound _ _ _ _ CS) as CSB.
    unfold main_prog, main_model. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length argv) =? 2)%Z with false by (symmetry; apply Z.eqb_neq; exact HC). cbn [negb].
    pose proof (munch_refl [(USP - 128, USP - 48)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    ienterG.
    carve_frame 80%nat ST.
    do 11 zstep.
    zstep. if_true_by (neq_cond (argc argv) 2 ltac:(unfold argc; lia) ltac:(lia) ltac:(unfold argc; exact HC)).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      (nd_pre (stack_argv_string_slack asegs a_phdrs sp0 argv envp uid hw rnd m1 CS
                  ltac:(generalize USP16; clear; intros; Z.div_mod_to_equations; lia) 0 argv0 HA0) 8%nat; intros P0 slackF HP0 P0lo P0hi STRF SLKF ENDF; nd_post);
      pose proof (stack_argv_ptr_read asegs a_phdrs sp0 argv envp uid hw rnd m1 CS 0 _ HP0) as RD0
    end.
    replace (USP + 8 + 8 * Z.of_nat 0)%Z with (USP + 8)%Z in RD0 by lia.
    unfold InitMem.str_base, InitMem.env_base, InitMem.str_base in P0lo, P0hi.
    (nd_pre (slack_trunc _ P0 argv0 slackF (USP + Z.of_nat (length SBK) - 16) STRF SLKF
                ltac:(rewrite BL; unfold raw_len, pad_len in *; clear - P0hi RN; lia)
                ltac:(rewrite BL; generalize USP16; unfold pad_len; clear; intros; Z.div_mod_to_equations; lia)) 4%nat; intros slack0 STR0 SLK0 END0; nd_post).
    assert (RA0 : rng RNG (USP + 8) 8).
    { eapply rng_sub'; [exact CSR|]. rewrite BL. unfold raw_len, struct_size, InitMem.argc, InitMem.envc. clear - RN. lia. }
    do 7 zstep.
    (* [comment removed for export] *)
    lazymatch type of MU with munch _ _ ?mb =>
      destruct (drv_stack_writes L RNG s [] FB m mb _ (USP - 48)%Z G MU WM) as [G1 AG0]; [constructor; [cbn [fst snd]; lia| constructor] | lia |] end.
    clear MU WM.
    pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G1) as CSO1.
    name_spm.
    apply evtF_done. unfold diag, diag_usage. rewrite EARGV at 1. cbn [nth argv_Z map]. eapply implMG_bind.
    { eapply EPR_USAGE with (P := P0) (str := argv0) (slack := slack0); [ | | reflexivity | reflexivity | reflexivity | | exact STR0 | | | exact SLK0 | | ].
      - std_pre_tac G1 ST MI Hspm R1 R2 R3 R4 R5.
      - rewrite Hspm; generalize TOP_lo; clear; intros; lia.                 (* [comment removed for export] *)
      - eapply drv_lit_mobjA; [exact G1 | exact R3 | exact R4 | unfold FMT_USAGE; lia | unfold FMT_USAGE, DRV_RODATA_HI; lia | lia].
      - exact (proj1 (Forall_forall _ _) VA4 _ (nth_error_In _ _ HA0)).
      - pose proof (proj1 (Forall_forall _ _) VA3 _ (nth_error_In _ _ HA0)) as X. cbv beta in X. lia.
      - eapply mobjA_sub; [exact CSO1 | lia | lia | lia].
      - intros a Ha. left. rewrite Hspm. lia. }
    intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
    unfold hpost_regs in E. destruct_exs E. subst ms'.
    pose proof (rngs_le _ _ FP RS) as RS'.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
    replace (ret_pc (Z_to_bv 64 0x8433c)) with (Z_to_bv 64 0x8433c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite Hspm in *.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
    unname_spm.
    ienterG. do 13 zstep.
    replace (ret_pc (Z_to_bv 64 RA_MAIN)) with (Z_to_bv 64 RA_MAIN) by (symmetry; apply ret_pc_even; [unfold RA_MAIN; lia|reflexivity]).
    unfold RA_MAIN. zstep.
    apply evtF_done. apply implMG_ret. apply evtF_done. unfold main_post.
    release_frame FR ST2 (USP + -48)%Z.
    eapply AT_EXIT_I; [exact G2 | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; generalize LO_hi; lia
                      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; aln16 | exact RS'].
  Qed.
  End Zd1.
  #[using="fflagA GL GD EPR_USAGE LO_lo LO_hi USP16 TOP_lo TOP47 USP47 AT_EXIT_I drv_lit_mobjA drv_stack_writes"] Lemma main_usage : ltac:(let t := eval cbv delta [main_usage__stmt] in main_usage__stmt in exact t).
  Proof. exact main_usage__body. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mframe (m : mem) : Prop :=
    exists (j0 : list byte) (f1 f2 f3 f4 f5 f6 f7 f8 : word),
      rw_cells asegs m (USP + -128) [CB 8 j0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7; C8 f8; C8 (Z_to_bv 64 RA_MAIN)].

  (* [comment removed for export] *)
  Definition mbuf (s : PS) (RNG : footprint) (m : mem) (q : hptr) (A cap : Z) (CBs : list byte) : Prop :=
    (exists FB, GIOA L RNG s [(q, A, cap)] FB [] m) /\ mem_inv asegs m /\ stk asegs m LO (USP + -128) /\ mframe m
    /\ (exists junk, rw_cells asegs m A [CB (length CBs) CBs; CB (Z.to_nat (cap - Z.of_nat (length CBs))) junk])
    /\ (Z.of_nat (length CBs) <= cap)%Z /\ (65536 <= cap <= MAX_INPUT)%Z /\ (exists j, cap = 65536 * 2 ^ j)%Z
    /\ rngs RNG.

  (* [comment removed for export] *)
  Definition LH (fd P1 : Z) (path slack : list byte) (st : rd_st (ptr:=hptr)) (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (A : Z) (CBs : list byte) (pc : Z),
      ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 P1) (Z_to_bv 64 (rd_len st)) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 0x5d1050) (Z_to_bv 64 A) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 pc) fc None m (seg_rom asegs)
      /\ (pc = 0x84210 \/ (pc = 0x841f0 /\ rd_len st = 0))%Z
      /\ mbuf s RNG m (rd_buf st) A (rd_cap st) CBs /\ rd_content st = of_bytes CBs /\ rd_len st = Z.of_nat (length CBs)
      /\ bytes_at asegs m P1 (path ++ Z_to_bv 8 0 :: slack) /\ (USP <= P1)%Z /\ (3 <= fd <= 4096)%Z.

  (* [comment removed for export] *)
  Definition LX (fd P1 : Z) (path slack : list byte) (res : rd_result (ptr:=hptr)) (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    match res with
    | RdExit => at_exit2 s RNG ms
    | RdDone q content =>
        exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
               (m : mem) (A cap : Z) (CBs : list byte),
          ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 P1) (Z_to_bv 64 (Z.of_nat (length CBs))) (Z_to_bv 64 fd) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8427c) fc None m (seg_rom asegs)
          /\ mbuf s RNG m q A cap CBs /\ content = of_bytes CBs
    end.

  (* [comment removed for export] *)
  #[using="rc sp0 argv envp uid hw rnd"] Lemma want_spec : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (cap len : Z),
    s5 = Z_to_bv 64 cap -> s3 = Z_to_bv 64 len -> (0 <= len < cap)%Z -> (cap <= 67108864)%Z -> rng_aimg RNG ->
    evtF asegs RNG (fun ms' => exists a0', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 (Z_to_bv 64 (Z.min (cap - len) 65536)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                          F (Z_to_bv 64 0x84264) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84254) fc None m (seg_rom asegs)).
  Proof.
    intros until len. intros -> -> Hr Hc RIMG.
    zstep. zstep. zstep.
    destruct (Z_lt_le_dec (cap - len) 65536).
    - if_true_by (ltu_cond_true (cap - len)%Z 65536%Z ltac:(lia) ltac:(lia)).
      rewrite Z.min_l by lia. apply evtF_done. eexists. reflexivity.
    - if_false_by (ltu_cond_false (cap - len)%Z 65536%Z ltac:(lia) ltac:(lia)). zstep.
      rewrite Z.min_r by lia. apply evtF_done. eexists. reflexivity.
  Qed.

  #[using="rc sp0 argv envp uid hw rnd"] Lemma cap_shift_zero : forall cap j, (cap = 65536 * 2 ^ j)%Z -> (0 <= j)%Z -> (cap < 67108864)%Z -> Z.shiftr cap 26 = 0%Z.
  Proof. intros cap j -> Hj Hc. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

  (* [comment removed for export] *)
  Definition grow_post (fd P1 : Z) (path slack : list byte) (len0 : Z) : option (rd_st (ptr:=hptr)) -> PS -> footprint -> machine_state -> Prop :=
    fun g s' RNG' ms' =>
      match g with
      | None => at_exit2 s' RNG' ms'
      | Some st1 => rd_len st1 = len0 /\ exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
                           (m : mem) (A : Z) (CBs : list byte),
          ms' = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 P1) (Z_to_bv 64 (rd_len st1)) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 0x5d1050) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x84254) fc None m (seg_rom asegs)
          /\ mbuf s' RNG' m (rd_buf st1) A (rd_cap st1) CBs /\ rd_content st1 = of_bytes CBs /\ rd_len st1 = Z.of_nat (length CBs)
          /\ (rd_len st1 < rd_cap st1)%Z
          /\ bytes_at asegs m P1 (path ++ Z_to_bv 8 0 :: slack)
      end.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA sp0 argv envp uid hw rnd GL block_mobjA"] Lemma blk_facts : forall RNG s CL FB m b, GIOA L RNG s CL FB [] m -> In b CL -> (0 <= cb_size b)%Z ->
    mobjA RNG m (cb_addr b) (cb_size b) /\ (cb_addr b + cb_size b <= ATOP)%Z /\ (0x604000 <= cb_addr b)%Z.
  Proof.
    intros RNG s CL FB m b G Hb Hn. (nd_pre (block_mobjA L RNG s CL FB m (cb_addr b) (cb_size b) G ltac:(exists b; split; [exact Hb| lia]) Hn) 3%nat; intros A1 A2 A3; nd_post).
    unfold AIMG_HI in A3. auto.
  Qed.
  (* [comment removed for export] *)
  #[using="FO fflagA sp0 argv envp uid hw rnd GL"] Lemma blk_tclr : forall RNG s CL FB m b, GIOA L RNG s CL FB [] m -> In b CL -> (0 < cb_size b)%Z ->
    (cb_addr b + cb_size b <= ATPv + -200 \/ ATPv + 304 <= cb_addr b)%Z.
  Proof.
    intros RNG s CL FB m b G Hb Hn.
    destruct (Z_le_gt_dec (cb_addr b + cb_size b) (ATPv + -200)) as [X|X]; [left; exact X|].
    destruct (Z_le_gt_dec (ATPv + 304) (cb_addr b)) as [Y|Y]; [right; exact Y|]. exfalso.
    apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max (cb_addr b) (ATPv + -200)) G).
    - left. apply in_block_app. left. apply in_block_In. exists b. split; [exact Hb| lia].
    - unfold ATP. lia.
  Qed.

  (* [comment removed for export] *)
  Definition grow_spec__stmt : Prop := forall fd P1 path slack (st : rd_st (ptr:=hptr)) s RNG ms,
    LH fd P1 path slack st s RNG ms -> rd_len st = rd_cap st ->
    implMG RNG
      (if (MAX_INPUT <=? rd_cap st)%Z then diag DTooBig ;;; mret None
       else nb <- pmalloc HO (rd_cap st * 2) ;;
            match nb with
            | None => diag DOom ;;; mret None
            | Some nb' => pfree HO (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_len st) (rd_chunks st)))
            end) s
      (grow_post fd P1 path slack (rd_len st)) ms.
  Section Zd2.   (* [comment removed for export] *)
  Variable fd : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 0).
  Variable P1 : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 1).
  Variable path : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 2).
  Variable slack : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 3).
  Variable st : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 4).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 5).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 6).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'grow_spec__stmt 7).
  #[using="FO fflagA argv envp uid hw rnd GL GD MALLOC FREE EPR_BIG LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma grow_spec__body : ltac:(let T := type of (fun (h : grow_spec__stmt) => h fd P1 path slack st s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (fd, (P1, (path, (slack, (st, (s, (RNG, ms)))))))) as _.
    intros LHH Hfull.
    (nd_pre LHH 29%nat; intros ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A CBs pc ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros HPC MB HC HL PATH HP1 HFD; nd_post).
    (nd_pre MB 9%nat; intros (FB & G) MI ST (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) (junk & BUF) HLC HCAP (j & Hj) RS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    destruct st as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *. subst len.
    (nd_pre (blk_facts RNG s _ FB m (q, A, cap) G ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros _ B1 B2; nd_post). cbn [cb_addr cb_size fst snd] in B1, B2.
    pose proof (bytes_at_bound _ _ _ _ PATH) as PB. rewrite length_app in PB; cbn [length] in PB.
    assert (Hj0 : (0 <= j)%Z). { destruct (Z_lt_le_dec j 0); [|lia]. rewrite Z.pow_neg_r in Hj by lia. lia. }
    rewrite Hfull in *.
    (* [comment removed for export] *)
    destruct HPC as [->|[_ H0]]; [|exfalso; unfold MAX_INPUT in *; lia].
    ienterG. zstep. if_true_by (beq_cond cap). zstep.
    destruct (Z_le_gt_dec MAX_INPUT cap) as [HBIG|HOK].
    - (* [comment removed for export] *)
      replace (MAX_INPUT <=? cap)%Z with true by (symmetry; apply Z.leb_le; exact HBIG).
      assert (Ecap : cap = 67108864%Z) by (unfold MAX_INPUT in *; lia).
      replace (Z.shiftr cap 26) with 1%Z by (rewrite Ecap; reflexivity).
      zstep. if_true. do 7 zstep.
      name_spm.
      apply evtF_done. unfold diag, diag_too_big. eapply implMG_bind.
      { eapply EPR_BIG; [ | | reflexivity | reflexivity | reflexivity | ].
        - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
        - rewrite Hspm; generalize TOP_lo; clear; intros; lia.                 (* [comment removed for export] *)
        - eapply drv_lit_mobjA; [exact G | exact R3 | exact R4 | unfold FMT_TOO_BIG; lia | unfold FMT_TOO_BIG, DRV_RODATA_HI; lia | lia]. }
      intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP RS) as RS'.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
      replace (ret_pc (Z_to_bv 64 0x843ec)) with (Z_to_bv 64 0x843ec) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *. unname_spm.
      ienterG. zstep.
      apply evtF_done. apply implMG_ret. apply evtF_done.
      unfold grow_post, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2|]. split; [exact ST2| exact RS'].
    - (* [comment removed for export] *)
      replace (MAX_INPUT <=? cap)%Z with false by (symmetry; apply Z.leb_gt; lia).
      rewrite (cap_shift_zero cap j Hj Hj0 ltac:(unfold MAX_INPUT in HOK; lia)).
      zstep. if_false. zstep. zstep. zstep.
      rewrite (Z.shiftl_mul_pow2 cap 1) by lia. change (2 ^ 1)%Z with 2%Z.
      destruct (cap_double_ok cap j Hj Hj0 ltac:(unfold MAX_INPUT in HOK; lia)) as [Hj' HC2].
      name_spm.
      apply evtF_done. eapply implMG_bind.
      { eapply MALLOC with (n := (cap * 2)%Z); [ | reflexivity | unfold MAX_INPUT in HOK; lia | ].
        - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
        - eapply (unw_main RNG _ AMALLOC_PC spm _ _ 0x84230%Z);
            [ rewrite Hspm, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold AMALLOC_PC, ACLIENT_LO, ACLIENT_HI; lia
            | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | exact R1 | rewrite Hspm; lia ]. }
      intros r s' RNG1 ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP1 a0v m1 E OF1 MI1 ST1 AG1 CASES; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP1 RS) as RS1.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      replace (ret_pc (Z_to_bv 64 0x84230)) with (Z_to_bv 64 0x84230) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ _ AG1) in PATH; [|lia].
      apply (keeps_rw_cells_block _ _ _ _ _ _ _ AG1) in BUF.
      2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
      unname_spm.
      destruct r as [nb|]; [| destruct CASES].
      (* [comment removed for export] *)
      (nd_pre CASES 3%nat; intros A' junk' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G1 BLK; nd_post).
      (nd_pre (blk_facts RNG1 s' _ FB m1 (nb, A', (cap * 2)%Z) G1 ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros DOBJ C1 C2; nd_post). cbn [cb_addr cb_size fst snd] in DOBJ, C1, C2.
      (nd_pre (blk_facts RNG1 s' _ FB m1 (q, A, cap) G1 ltac:(right; left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros SOBJ _ _; nd_post). cbn [cb_addr cb_size fst snd] in SOBJ.
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G1) as AP. apply blocks_apart_app_inv in AP as (AP & _ & _). cbn [blocks_apart] in AP. destruct AP as [AP _].
      apply Forall_cons_iff in AP as [AP _]. unfold apart in AP. cbn [cb_addr cb_size fst snd] in AP.
      cbv beta iota. ienterG.
      zstep. if_false_by (eqz_cond_false A' ltac:(lia)). zstep.
      zstep. if_false_by (eqz_cond_false cap ltac:(lia)). zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat cap; Z.to_nat cap]) in BLK; [|cbn; lia]. cbn [app mk_CB_cells] in BLK.
      apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BLK as [BLK1 BLK2]. cbn [cells_size csize Nat.add] in BLK2.
      rewrite Nat.add_0_r, Z2Nat.id in BLK2 by lia.
      pose proof BUF as BUF'. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BUF' as [BUF1 _].
      assert (SRC : bytes_at asegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A CBs).
      { destruct BUF1 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (munch_refl [(USP + -128 - 2240, USP + -128); (A', A' + cap)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
      pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G1) as (RT1 & _).
      call_sp (memcpy_i_specZ RNG1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LO A' A cap CBs (firstn (Z.to_nat cap) junk'));
        [ first [reflexivity | assumption | lia | (eapply mobjA_sub; [exact DOBJ| lia| lia| lia]) | (eapply rng_sub'; [exact R2| lia])] .. | ].
      rename PC into ST2. rename PC0 into DST. clear POST BUF1 SRC BUF.
      lazymatch type of MU2 with munch _ _ ?mb =>
        assert (G2 : GIOA L RNG1 s' ((nb, A', (cap * 2)%Z) :: [(q, A, cap)]) FB [] mb);
        [ eapply (gl_client_frame _ _ _ GL); [exact G1 | exact MU2 | exact WM2 |];
          constructor; [left; cbn [fst snd]; lia | constructor; [| constructor]];
          right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ]
      end.
      clear MU2 WM2 G1.
      zstep. zstep.
      name_spm.
      apply evtF_done. eapply implMG_bind.
      { eapply FREE with (C1 := [(nb, A', (cap * 2)%Z)]) (C2 := @nil cblk) (q := q) (A := A) (n := cap); [| reflexivity |].
        - std_pre_tac G2 ST2 MI Hspm R1 R2 R3 R4 R5.
        - eapply (unw_main RNG1 _ AFREE_PC spm _ _ 0x84254%Z);
            [ rewrite Hspm, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia
            | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | exact R1 | rewrite Hspm; lia ]. }
      intros [] s'' RNG2 ms'' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP2 a0v2 m3 E OF2 MI3 ST3 AG3 G3; nd_post).
      unfold hpost_regs in E. destruct_exs E. subst ms''.
      cbn [app] in AG3, G3.
      pose proof (rngs_le _ _ FP2 RS1) as RS2.
      replace (ret_pc (Z_to_bv 64 0x84254)) with (Z_to_bv 64 0x84254) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG3) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ _ AG3) in PATH; [|lia].
      apply (keeps_rw_cells_block _ _ _ _ _ _ _ AG3) in DST.
      2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
      apply (keeps_rw_cells_block _ _ _ _ _ _ _ AG3) in BLK2.
      2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
      unname_spm.
      (* [comment removed for export] *)
      apply implMG_ret. apply evtF_done.
      unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks rd_content]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { split; [exists FB; exact G3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
        split.
        { exists (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk')).
          replace (length CBs) with (Z.to_nat cap) by lia.
          replace (Z.to_nat (cap * 2 - Z.of_nat (Z.to_nat cap))) with (Z.to_nat cap) by lia.
          apply rw_cells_join2; [exact DST|]. cbn [csize]. rewrite Z2Nat.id by lia. exact BLK2. }
        split; [lia|]. split; [unfold MAX_INPUT; lia|]. split; [exists (j + 1)%Z; exact Hj'| exact RS2]. }
      split; [exact HC|]. split; [symmetry; exact Hfull|]. split; [lia| exact PATH].
  Qed.
  End Zd2.
  #[using="FO fflagA argv envp uid hw rnd GL GD MALLOC FREE EPR_BIG LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma grow_spec : ltac:(let t := eval cbv delta [grow_spec__stmt] in grow_spec__stmt in exact t).
  Proof. exact grow_spec__body. Qed.

  Definition body_post (fd P1 : Z) (path slack : list byte) : (rd_st (ptr:=hptr) + rd_result (ptr:=hptr)) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => match r with inl st' => LH fd P1 path slack st' s' RNG' ms' | inr res => LX fd P1 path slack res s' RNG' ms' end.

  (* [comment removed for export] *)
  #[using="Type"] Lemma RS_ok : rw_bytes_b asegs 0x5d1050 (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) = true.
  Proof. exact RS_ok_pre. Qed.   (* [comment removed for export] *)
  #[using="rc sp0 argv envp uid hw rnd"] Lemma RS_chunk : forall m : mem, exists rsj, rw_cells asegs m 0x5d1050 [CB (Z.to_nat 65536) rsj].
  Proof.
    intros m. (nd_pre (rw_cells_any asegs m 0x5d1050%Z (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) RS_ok ltac:(lia) ltac:(rewrite repeat_length; lia)) 3%nat; intros rsj RSL RSC; nd_post).
    rewrite repeat_length in RSC. exists rsj. exact RSC.
  Qed.
  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA sp0 argv envp uid hw rnd GL GD"] Lemma stage_mobjA : forall RNG s CL FB m n, GIOA L RNG s CL FB [] m -> rng_aimg RNG -> rng_aimg_sh RNG -> (0 <= n <= 65536)%Z ->
    mobjA RNG m 0x5d1050 n.
  Proof.
    intros RNG s CL FB m n G RI RSH Hn. destruct (gd_unp _ _ _ GD _ _ _ _ _ _ _ G) as [_ U]. destruct (gl_globals _ _ _ GL _ _ _ _ _ _ _ G) as [W _].
    unfold READ_STAGE in U. apply static_mobjA; [lia | lia | lia | eapply unpoisoned_sub; [exact U| lia| lia] | exact W | exact RI | exact RSH].
  Qed.

  #[using="sp0 argv envp uid hw rnd"] Lemma atp_unsigned : bv_unsigned (Z_to_bv 64 ATP) = ATP.
  Proof. pose proof atp_lin as ((TL & _) & _). atop_facts. unfold ATP. apply unsigned_lit. lia. Qed.

  (* [comment removed for export] *)
  Definition read_step__stmt : Prop := forall fd P1 path slack (len0 : Z) (st1 : rd_st (ptr:=hptr)) s RNG ms,
    grow_post fd P1 path slack len0 (Some st1) s RNG ms ->
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z -> (3 <= fd <= 4096)%Z -> (USP <= P1)%Z ->
    (P1 + Z.of_nat (length path) + 1 + Z.of_nat (length slack) <= USP + Z.of_nat (length SBK) - 16)%Z ->
    implMG RNG
      (s0 <- mget ;;
       (let buf := sites SiteReadStage in
        let want := (rd_cap st1 - len0)%Z in
        let want' := (if READ_CHUNK <? want then READ_CHUNK else want)%Z in
        a <- msys (NRead fd buf want') (dec_read buf want') ;;
        match a with
        | RdErr _ => diag (DReadError (map bv_unsigned path)) ;;; mret (inr RdExit)
        | RdData bs => if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
                       else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (len0 + zlength bs)%Z (rd_chunks st1 ++ [of_bytes bs])))
        end)) s (body_post fd P1 path slack) ms.
  Section Zd3.   (* [comment removed for export] *)
  Variable fd : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 0).
  Variable P1 : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 1).
  Variable path : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 2).
  Variable slack : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 3).
  Variable len0 : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 4).
  Variable st1 : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 5).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 6).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 7).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'read_step__stmt 8).
  #[using="FO fflagA GL GD EPR_READ SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 drv_lit_mobjA block_mobjA"] Lemma read_step__body : ltac:(let T := type of (fun (h : read_step__stmt) => h fd P1 path slack len0 st1 s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (fd, (P1, (path, (slack, (len0, (st1, (s, (RNG, ms))))))))) as _.
    intros GP HNUL HPL HFD HP1 HPEND.
    destruct GP as [<- GP].
    (nd_pre GP 28%nat; intros ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A CBs ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MB HC HL HLT PATH; nd_post).
    (nd_pre MB 9%nat; intros (FB & G) MI ST (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) (junk & BUF) HLC HCAP (j & Hj) RS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    destruct (gd_errno _ _ _ GD _ _ _ _ _ _ _ G) as (e & T2).
    pose proof atp_unsigned as ETP. pose proof atp_lin as ((TL & _) & _). pose proof atp_below_atop as TBA. unfold ATP in *.
    destruct st1 as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *. subst len.
    set (len := Z.of_nat (length CBs)) in *.
    (nd_pre (blk_facts RNG s _ FB m (q, A, cap) G ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros BOBJ B1 B2; nd_post). cbn [cb_addr cb_size fst snd] in BOBJ, B1, B2.
    pose proof (blk_tclr RNG s _ FB m (q, A, cap) G ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) as BTLS. cbn [cb_addr cb_size fst snd] in BTLS.
    pose proof (bytes_at_bound _ _ _ _ PATH) as PB. rewrite length_app in PB; cbn [length] in PB.
    apply implMG_get_bind. cbv beta zeta.
    rewrite SITE_RS. unfold READ_STAGE.
    set (want := Z.min (cap - len) 65536).
    replace (if READ_CHUNK <? cap - len then READ_CHUNK else cap - len)%Z with want.
    2:{ subst want. unfold READ_CHUNK. destruct (Z.ltb_spec 65536 (cap - len)); lia. }
    assert (HW : (1 <= want <= 65536)%Z /\ (want <= cap - len)%Z) by (subst want; lia).
    destruct HW as [HW1 HW2].
    ienterG.
    eapply evtF_cut; [eapply (want_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m cap len); [reflexivity | reflexivity | lia | unfold MAX_INPUT in HCAP; lia | exact R3] |].
    cbv beta. intros ms' [a0' ->]. fold want.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    destruct (RS_chunk m) as (rsj & RSC).
    apply (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat want; Z.to_nat (65536 - want)]) in RSC; [|cbn; lia]. cbn [app mk_CB_cells] in RSC.
    apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in RSC as [RSw _].
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    name_spm.
    apply evtF_done. eapply implMG_msys_of_enode.
    { eapply (read_i_specZ RNG _ spm _ (Z_to_bv 64 ATPv)) with (lo := LO) (fd := fd) (B := 0x5d1050%Z) (count := want) (errv := e);
        [ reflexivity | reflexivity | reflexivity | exact MI | rewrite Hspm; exact ST | rewrite Hspm; lia | exact LOLO | exact RT | exact ETP
        | exact RSw | exact T2 | lia | lia | right; lia | lia | (unfold tclr; pose proof ATPv_img; lia)
        | eapply stage_mobjA; [exact G | exact R3 | exact R4 | lia] | exact R3 | rewrite Hspm; eapply rng_sub'; [exact R2| lia] | exact R5 ]. }
    intros a RNG' ms' PO. unfold read_i_post in PO. destruct PO as (-> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MU WM MI' ST' CASE; nd_post).
    replace (ret_pc (Z_to_bv 64 0x84270)) with (Z_to_bv 64 0x84270) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite ETP in *. rewrite Z2Nat.id in MU by lia.
    clear RSw.
    lazymatch type of MU with munch _ ?ma ?mb => transport_after_call asegs ma mb MU WM end.
    clear MI. rename MI' into MI.
    apply (munch_weaken _ [(ATPv + -164, ATPv + -160); (bv_unsigned spm - 2208, bv_unsigned spm); (0x5d1050, 0x5d1050 + want)]%Z) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
    (* [comment removed for export] *)
    assert (G' : forall ev, rw_cells asegs ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end) (ATPv + -164) [C4 ev] ->
                 GIOA L RNG s [(q, A, cap)] FB [] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
    { intros ev HEV. eapply (gd_frame_errno _ _ _ GD); [exact G | exact MU | exact WM | | exact HEV].
      constructor; [left; left; cbn [fst snd]; rewrite Hspm; lia|].
      constructor; [right; unfold rs_iv, READ_STAGE; cbn [fst snd]; lia| constructor]. }
    clear MU WM G.
    destruct a as [err|bs].
    - (* [comment removed for export] *)
      (nd_pre CASE 3%nat; intros _ ERR Herr; nd_post). specialize (G' _ ERR).
      clear CM1 CM2. (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G') 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
      pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G') as CSO.
      unfold read_ret. rewrite Hspm in *. unname_spm.
      ienterG. zstep. if_true_by ltz_cond_m1. do 8 zstep.
      name_spm.
      apply evtF_done. unfold diag, diag_read_error. eapply implMG_bind.
      { eapply EPR_READ with (P := P1) (str := path) (slack := slack); [ | | reflexivity | reflexivity | reflexivity | | exact PATH | exact HNUL | exact (proj1 HPL) | exact (proj2 HPL) | | intros a Ha; left; rewrite Hspm; lia ].
        - std_pre_tac G' ST' MI Hspm R1 R2 R3 R4 R5.
        - rewrite Hspm; generalize TOP_lo; clear; intros; lia.                 (* [comment removed for export] *)
        - eapply drv_lit_mobjA; [exact G' | exact R3 | exact R4 | unfold FMT_READ_ERROR; lia | unfold FMT_READ_ERROR, DRV_RODATA_HI; lia | lia].
        - eapply mobjA_sub; [exact CSO | lia | lia | lia]. }
      intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP RS) as RS'.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
      replace (ret_pc (Z_to_bv 64 0x843ec)) with (Z_to_bv 64 0x843ec) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *. unname_spm.
      ienterG. zstep.
      apply evtF_done. apply implMG_ret. apply evtF_done.
      unfold body_post, LX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2|]. split; [exact ST2| exact RS'].
    - (* [comment removed for export] *)
      (nd_pre CASE 3%nat; intros RSr ERR Hbs; nd_post). specialize (G' _ ERR).
      unfold read_ret. rewrite Hspm in *. unname_spm.
      pose proof (Nat2Z.is_nonneg (length bs)) as LB0.
      ienterG. zstep. if_false_by (ltz_cond_false (Z.of_nat (length bs)) ltac:(lia)). zstep.
      destruct bs as [|b bs'].
      + (* [comment removed for export] *)
        zstep. if_false_by (eq_cond 0).
        apply evtF_done. cbn [length Nat.eqb]. apply implMG_ret. apply evtF_done.
        unfold body_post, LX. cbn [rd_content rd_chunks].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|]. split; [| exact HC].
        split; [exists FB; exact G'|]. split; [exact MI|]. split; [exact ST'|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
        split; [exists junk; exact BUF|].
        split; [lia|]. split; [exact HCAP|]. split; [exists j; exact Hj| exact RS].
      + (* [comment removed for export] *)
        set (n := Z.of_nat (length (b :: bs'))) in *.
        assert (Hn : (1 <= n <= want)%Z) by (subst n; cbn [length] in *; lia).
        zstep. if_true_by (nez_cond n ltac:(lia)).
        zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in RSr as [RSd _].
        assert (SRC : bytes_at asegs ltac:(lazymatch type of RSd with rw_cells _ ?mm _ _ => exact mm end) 0x5d1050 (b :: bs')).
        { destruct RSd as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
        clear RSd.
        pose proof BUF as BUF0. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BUF as [BUF1 BUF2]. cbn [cells_size csize Nat.add] in BUF2.
        rewrite Nat.add_0_r in BUF2. fold len in BUF2.
        apply (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat n; Z.to_nat (cap - len - n)]) in BUF2; [|cbn; lia]. cbn [app mk_CB_cells] in BUF2.
        apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BUF2 as [BUFw BUF3]. cbn [cells_size csize Nat.add] in BUF3.
        rewrite Nat.add_0_r, Z2Nat.id in BUF3 by lia.
        clear BUF0.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (munch_refl [(USP + -128 - 2240, USP + -128); (A + len, A + len + n)]%Z m1) as MU2; pose proof (wmono_refl asegs m1) as WM2 end.
        pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G') as (RT' & _).
        (nd_pre (blk_facts RNG s _ FB _ (q, A, cap) G' ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros BOBJ' _ _; nd_post). cbn [cb_addr cb_size fst snd] in BOBJ'.
        pose proof (stage_mobjA RNG s _ FB _ n G' R3 R4 ltac:(lia)) as SOBJ.
        call_sp (memcpy_i_specZ RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LO (A + len)%Z 0x5d1050%Z n (b :: bs') (firstn (Z.to_nat n) junk));
          [ first [reflexivity | assumption | lia | (subst n; lia) | (eapply mobjA_sub; [exact BOBJ'| lia| lia| lia]) | (eapply rng_sub'; [exact R2| lia])] .. | ].
        rename PC into ST2. rename PC0 into DST. clear POST. try clear SRC.
        lazymatch type of MU2 with munch _ _ ?mb =>
          assert (G2 : GIOA L RNG s [(q, A, cap)] FB [] mb);
          [ eapply (gl_client_frame _ _ _ GL); [exact G' | exact MU2 | exact WM2 |];
            constructor; [left; cbn [fst snd]; lia | constructor; [| constructor]];
            right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ]
        end.
        clear MU2 WM2 G'.
        (* [comment removed for export] *)
        zstep. zstep.
        (* [comment removed for export] *)
        assert (BUF : exists junk', rw_cells asegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A
                        [CB (length (CBs ++ b :: bs')) (CBs ++ b :: bs'); CB (Z.to_nat (cap - (len + n))) junk']).
        { eexists.
          assert (J : rw_cells asegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A
                        ([CB (length CBs) CBs] ++ [CB (Z.to_nat n) (b :: bs')] ++ [CB (Z.to_nat (cap - len - n)) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))])).
          { apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [exact BUF1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. fold len.
            apply (proj2 (rw_cells_app asegs _ _ [_] [_])). split; [exact DST|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact BUF3. }
          cbn [app] in J.
          apply (rw_cells_merge asegs _ _ [] [CB (length CBs) CBs; CB (Z.to_nat n) (b :: bs')] [_]) in J. cbn [cells_size csize cells_bytes cbytes app] in J.
          replace (length CBs + (Z.to_nat n + 0))%nat with (length (CBs ++ b :: bs')) in J by (rewrite length_app; subst n; lia).
          rewrite ?app_nil_r in J.
          replace (Z.to_nat (cap - len - n)) with (Z.to_nat (cap - (len + n))) in J by lia. exact J. }
        clear BUF1 DST BUF3. destruct BUF as [junk' BUF].
        apply evtF_done. replace (length (b :: bs') =? 0)%nat with false by reflexivity. apply implMG_ret. apply evtF_done.
        unfold body_post, LH. cbn [rd_buf rd_cap rd_len rd_chunks rd_content].
        replace (n + len)%Z with (len + zlength (b :: bs'))%Z by (unfold zlength; subst n; lia).
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [left; reflexivity|].
        split.
        { split; [exists FB; exact G2|]. split; [eassumption|]. split; [exact ST2|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
          split. { exists junk'. replace (cap - Z.of_nat (length (CBs ++ b :: bs')))%Z with (cap - (len + n))%Z by (rewrite length_app; subst n len; lia). exact BUF. }
          split; [rewrite length_app; subst n len; lia|]. split; [exact HCAP|]. split; [exists j; exact Hj| exact RS]. }
        split. { unfold rd_content in *. cbn [rd_chunks] in HC |- *. rewrite concat_app. cbn [concat]. rewrite app_nil_r, HC. unfold of_bytes. rewrite map_app. reflexivity. }
        split; [unfold zlength; rewrite length_app; subst len; lia|].
        split; [exact PATH|]. split; [exact HP1| exact HFD].
  Qed.
  End Zd3.
  #[using="FO fflagA GL GD EPR_READ SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 drv_lit_mobjA block_mobjA"] Lemma read_step : ltac:(let t := eval cbv delta [read_step__stmt] in read_step__stmt in exact t).
  Proof. exact read_step__body. Qed.

  (* [comment removed for export] *)
  Definition body_spec__stmt : Prop := forall fd P1 path slack (st : rd_st (ptr:=hptr)) s RNG ms,
    LH fd P1 path slack st s RNG ms -> ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
    (P1 + Z.of_nat (length path) + 1 + Z.of_nat (length slack) <= USP + Z.of_nat (length SBK) - 16)%Z ->
    implMG RNG (read_loop_body diag (pmalloc HO) (pfree HO) (sites SiteReadStage) fd (map bv_unsigned path) st) s (body_post fd P1 path slack) ms.
  Section Zd4.   (* [comment removed for export] *)
  Variable fd : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 0).
  Variable P1 : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 1).
  Variable path : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 2).
  Variable slack : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 3).
  Variable st : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 4).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 5).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 6).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'body_spec__stmt 7).
  #[using="FO fflagA GL GD MALLOC FREE EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma body_spec__body : ltac:(let T := type of (fun (h : body_spec__stmt) => h fd P1 path slack st s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (fd, (P1, (path, (slack, (st, (s, (RNG, ms)))))))) as _.
    intros LHH HNUL HPL HPEND.
    pose proof LHH as LHH'.
    (nd_pre LHH' 36%nat; intros ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A CBs pc Ems HPC MB HC HL PATH HP1 HFD; nd_post). subst ms.
    pose proof MB as MB'. (nd_pre MB' 9%nat; intros (FB & G) MI ST FRm BUF HLC HCAP HJ RS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    unfold read_loop_body. cbv zeta.
    eapply implMG_bind with (Q1 := grow_post fd P1 path slack (rd_len st)).
    - destruct (Z.eqb_spec (rd_len st) (rd_cap st)) as [E|NE].
      + apply grow_spec; [exact LHH | exact E].
      + apply implMG_ret.
        destruct st as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *.
        (* [comment removed for export] *)
        destruct HPC as [->|[-> H0]].
        * zstep. if_false_by (bne_cond_false len cap ltac:(unfold MAX_INPUT in *; lia) ltac:(unfold MAX_INPUT in *; lia) NE). zstep. zstep.
          apply evtF_done. unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|]. split; [exact MB|]. split; [exact HC|]. split; [exact HL|]. split; [lia| exact PATH].
        * zstep. if_true_by (neq_cond 0 cap ltac:(lia) ltac:(unfold MAX_INPUT in *; lia) ltac:(unfold MAX_INPUT in *; lia)). zstep. zstep.
          apply evtF_done. unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|]. split; [exact MB|]. split; [exact HC|]. split; [exact HL|]. split; [lia| exact PATH].
    - intros g s' RNG' ms' GP. destruct g as [st1|].
      + cbv beta iota. eapply read_step; [exact GP | exact HNUL | exact HPL | exact HFD | exact HP1 | exact HPEND].
      + cbv beta iota. apply implMG_ret. apply evtF_done. exact GP.
  Qed.
  End Zd4.
  #[using="FO fflagA GL GD MALLOC FREE EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma body_spec : ltac:(let t := eval cbv delta [body_spec__stmt] in body_spec__stmt in exact t).
  Proof. exact body_spec__body. Qed.

  (* [comment removed for export] *)
  #[using="FO fflagA GL GD MALLOC FREE EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma loop_spec : forall fuel fd P1 path slack (st : rd_st (ptr:=hptr)) s RNG ms,
    LH fd P1 path slack st s RNG ms -> ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
    (P1 + Z.of_nat (length path) + 1 + Z.of_nat (length slack) <= USP + Z.of_nat (length SBK) - 16)%Z ->
    implMG RNG (mloop fuel (read_loop_body diag (pmalloc HO) (pfree HO) (sites SiteReadStage) fd (map bv_unsigned path)) st) s
      (LX fd P1 path slack) ms.
  Proof.
    induction fuel as [|fuel IH]; intros fd P1 path slack st s RNG ms LHH HNUL HPL HPEND.
    - cbn [mloop]. apply implMG_unr.
    - apply implMG_loop_S. eapply implMG_mono; [eapply body_spec; [exact LHH | exact HNUL | exact HPL | exact HPEND]|].
      cbv beta. intros [st'|res] s' RNG' ms' BP; unfold body_post in BP.
      + apply IH; [exact BP | exact HNUL | exact HPL | exact HPEND].
      + apply evtF_done. exact BP.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma to_bytes_of_bytes : forall l : list byte, to_bytes (map bv_unsigned l) = l.
  Proof.
    intros l. unfold to_bytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
    apply definitions.Z_to_bv_bv_unsigned.
  Qed.

  #[using="Type"] Lemma rw_cells_nil_CB : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A (CB 0 [] :: cs).
  Proof.
    intros m A cs [[Hwf HB] HW]. split; [split|].
    - split; [reflexivity| exact Hwf].
    - cbn [cells_bytes cbytes app]. exact HB.
    - cbn [cells_size csize Nat.add]. exact HW.
  Qed.

  (* [comment removed for export] *)
  Definition P2 (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (FB : list cblk),
      ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 (Z_to_bv 64 (USP + 8)) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x841b8) fc None m (seg_rom asegs)
      /\ GIOA L RNG s [] FB [] m /\ mem_inv asegs m /\ stk asegs m LO (USP + -128) /\ mframe m /\ rngs RNG /\ bytes_at asegs m USP SBK.

  (* [comment removed for export] *)
  Definition RAX (res : rd_result (ptr:=hptr)) (s : PS) (RNG : footprint) (ms : machine_state) : Prop :=
    match res with
    | RdExit => at_exit2 s RNG ms
    | RdDone q content =>
        exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
               (m : mem) (A cap : Z) (CBs : list byte),
          ms = MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (Z.of_nat (length CBs))) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x84284) fc None m (seg_rom asegs)
          /\ mbuf s RNG m q A cap CBs /\ content = of_bytes CBs
    end.

  Definition read_all_spec__stmt : Prop := forall s RNG ms argv1,
    P2 s RNG ms -> nth_error argv 1 = Some argv1 -> valid_argv argv ->
    implMG RNG (read_all diag (pmalloc HO) (pfree HO) (sites SiteReadStage) (map bv_unsigned argv1)) s RAX ms.
  Section Zd5.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'read_all_spec__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'read_all_spec__stmt 1).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'read_all_spec__stmt 2).
  Variable argv1 : ltac2:(SecDietF.SzSecF.ty 'read_all_spec__stmt 3).
  #[using="FO fflagA GL GD MALLOC FREE EPR_OPEN EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma read_all_spec__body : ltac:(let T := type of (fun (h : read_all_spec__stmt) => h s RNG ms argv1) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, (ms, argv1)))) as _.
    intros (ra & gp & t0 & t1 & t2 & s1 & a0 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & FB & -> & G & MI & ST & (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) & RS & CS) HA1 VA.
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post). pose proof VA as VA'. (nd_pre VA' 5%nat; intros VA1 VA2 VA3 VA4 VA5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    destruct (gd_errno _ _ _ GD _ _ _ _ _ _ _ G) as (e & T2). destruct (gd_canary _ _ _ GD _ _ _ _ _ _ _ G) as (L2 & (can & L3)).
    pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G) as CSO. (pose proof CSO as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ CSR _; nd_post).
    pose proof atp_unsigned as ETP. pose proof atp_lin as ((TL & _) & _). pose proof atp_below_atop as TBA. pose proof ATPv_img as TIMG. unfold ATP in *.
    pose proof (raw_len_nonneg a_phdrs sp0 argv envp uid hw rnd) as RN.
    pose proof (build_stack_bytes_length a_phdrs sp0 argv envp uid hw rnd) as BL.
    pose proof (bytes_at_bound _ _ _ _ CS) as CSB.
    (nd_pre (stack_argv_string_slack asegs a_phdrs sp0 argv envp uid hw rnd m CS
                ltac:(generalize USP16; clear; intros; Z.div_mod_to_equations; lia) 1 argv1 HA1) 8%nat; intros P1 slackF HP1 P1lo P1hi STRF SLKF ENDF; nd_post).
    assert (P1hi' : (P1 + Z.of_nat (length argv1) + 1 <= USP + Z.of_nat (length SBK) - 16)%Z)
      by (rewrite BL; unfold InitMem.str_base, InitMem.env_base, InitMem.str_base, raw_len, pad_len in *; clear - P1hi RN; lia).
    (nd_pre (slack_trunc _ P1 argv1 slackF (USP + Z.of_nat (length SBK) - 16) STRF SLKF P1hi'
                ltac:(rewrite BL; generalize USP16; unfold pad_len; clear; intros; Z.div_mod_to_equations; lia)) 4%nat; intros slack1 STRS SLK1 END1; nd_post).
    destruct (proj1 (bytes_at_app asegs m P1 (argv1 ++ [Z_to_bv 8 0]) slack1) ltac:(rewrite <- app_assoc; exact STRS)) as [STR1 _].
    pose proof (stack_argv_ptr_read asegs a_phdrs sp0 argv envp uid hw rnd m CS 1 _ HP1) as RD1.
    replace (USP + 8 + 8 * Z.of_nat 1)%Z with (USP + 16)%Z in RD1 by lia.
    unfold InitMem.str_base, InitMem.env_base, InitMem.str_base in P1lo, P1hi.
    assert (P1lo' : (USP <= P1)%Z) by (unfold struct_size, InitMem.argc, InitMem.envc in P1lo; lia).
    assert (HNUL : ~ In (Z_to_bv 8 0) argv1). { apply (proj1 (Forall_forall _ _) VA4). eapply nth_error_In. exact HA1. }
    assert (HSLD : Namei.path_has_slash argv1 = false /\ Fs.path_eqb argv1 Namei.dotdot_path = false).
    { clear - HA1 VA5. destruct argv as [|x tlv]; [discriminate|]. cbn [tl] in VA5.
      change (nth_error tlv 0 = Some argv1) in HA1.
      exact (proj1 (Forall_forall _ _) VA5 _ (nth_error_In _ _ HA1)). }
    assert (HPL : (Z.of_nat (length argv1) < 2^24 /\ (- (P1 + Z.of_nat (length argv1) + 1)) mod 8 <= Z.of_nat (length slack1))%Z).
    { split; [|exact SLK1]. pose proof (proj1 (Forall_forall _ _) VA3 _ (nth_error_In _ _ HA1)). cbn beta in *. lia. }
    assert (HPEND : (P1 + Z.of_nat (length argv1) + 1 + Z.of_nat (length slack1) <= USP + Z.of_nat (length SBK) - 16)%Z) by lia.
    pose proof (bytes_at_bound _ _ _ _ STRS) as PBS. rewrite length_app in PBS; cbn [length] in PBS.
    pose proof (bytes_at_bound _ _ _ _ STR1) as PB. rewrite length_app in PB; cbn [length] in PB.
    assert (RA1 : rng RNG (USP + 16) 8).
    { eapply rng_sub'; [exact CSR|]. rewrite BL. unfold raw_len, struct_size, InitMem.argc, InitMem.envc. clear - RN. lia. }
    unfold read_all. rewrite to_bytes_of_bytes.
    ienterG. zstep. zstep. zstep. zstep.
    name_spm.
    apply evtF_done. eapply implMG_msys_of_enode.
    { eapply (open_spec RNG _ spm _ (Z_to_bv 64 ATPv)) with (lo := LO) (path := argv1) (errv := e) (canary := can);
        [ rewrite Hspm; exact ST | rewrite unsigned_lit by lia; exact STR1 | rewrite ETP; exact T2 | exact L2 | exact L3 | exact MI | reflexivity | exact HNUL
        | exact (proj1 HSLD) | exact (proj2 HSLD)
        | rewrite Hspm; lia | rewrite Hspm, ETP; lia | rewrite Hspm, unsigned_lit by lia; lia
        | rewrite ETP, unsigned_lit by lia; lia | rewrite Hspm; unfold ssp_guard; lia
        | rewrite ETP; unfold ssp_guard; lia | rewrite ETP; unfold got_ssp; lia | rewrite ETP; lia
        | rewrite Hspm; eapply rng_sub'; [exact R2| lia] | rewrite ETP; eapply rng_sub'; [exact R5| lia]
        | rewrite unsigned_lit by lia; eapply rng_sub'; [exact CSR| lia] | exact R3 ]. }
    intros r RNG' ms' PO. unfold open_post in PO. destruct PO as (-> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 9%nat; intros MU WM MI' ST' ERR STR GOT GUARD Hr; nd_post).
    replace (ret_pc (Z_to_bv 64 0x841c8)) with (Z_to_bv 64 0x841c8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite ETP in *. rewrite unsigned_lit in STR by lia.
    lazymatch type of MU with munch _ ?ma ?mb => transport_after_call asegs ma mb MU WM end.
    clear MI. rename MI' into MI.
    apply (munch_weaken _ [(ATPv + -164, ATPv + -160); (bv_unsigned spm - 112, bv_unsigned spm)]%Z) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
    assert (G' : GIOA L RNG s [] FB [] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
    { eapply (gd_frame_errno _ _ _ GD); [exact G | exact MU | exact WM | | exact ERR].
      constructor; [left; left; cbn [fst snd]; rewrite Hspm; lia| constructor]. }
    clear MU WM G CM1 CM2. (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G') 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    pose proof (gd_args _ _ _ GD _ _ _ _ _ _ _ G') as CSO'.
    destruct r as [err|fd].
    - (* [comment removed for export] *)
      unfold open_ret. rewrite Hspm in *. unname_spm.
      cbv beta iota. ienterG. zstep. if_true_by ltz_cond_m1. do 9 zstep.
      name_spm.
      apply evtF_done. unfold diag, diag_cannot_open. eapply implMG_bind.
      { eapply EPR_OPEN with (P := P1) (str := argv1) (slack := slack1); [ | | reflexivity | reflexivity | reflexivity | | exact STRS | exact HNUL | exact (proj1 HPL) | exact (proj2 HPL) | | intros a Ha; left; rewrite Hspm; lia ].
        - std_pre_tac G' ST' MI Hspm R1 R2 R3 R4 R5.
        - rewrite Hspm; generalize TOP_lo; clear; intros; lia.                 (* [comment removed for export] *)
        - eapply drv_lit_mobjA; [exact G' | exact R3 | exact R4 | unfold FMT_CANNOT_OPEN; lia | unfold FMT_CANNOT_OPEN, DRV_RODATA_HI; lia | lia].
        - eapply mobjA_sub; [exact CSO' | lia | lia | lia]. }
      intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP RS) as RS'.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
      replace (ret_pc (Z_to_bv 64 0x843ec)) with (Z_to_bv 64 0x843ec) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *. unname_spm.
      ienterG. zstep.
      apply evtF_done. apply implMG_ret. apply evtF_done.
      unfold RAX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2|]. split; [exact ST2| exact RS'].
    - (* [comment removed for export] *)
      unfold open_ret. rewrite Hspm in *. unname_spm.
      cbv beta iota. ienterG. zstep. if_false_by (ltz_cond_false fd ltac:(lia)). do 4 zstep.
      name_spm.
      apply evtF_done. eapply implMG_bind.
      { eapply MALLOC with (n := 65536%Z); [ | reflexivity | lia | ].
        - std_pre_tac G' ST' MI Hspm R1 R2 R3 R4 R5.
        - eapply (unw_main RNG _ AMALLOC_PC spm _ _ 0x841dc%Z);
            [ rewrite Hspm, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold AMALLOC_PC, ACLIENT_LO, ACLIENT_HI; lia
            | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | exact R1 | rewrite Hspm; lia ]. }
      intros r s' RNG1 ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP1 a0v m1 E OF1 MI1 ST1 AG1 CASES; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP1 RS) as RS1.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      replace (ret_pc (Z_to_bv 64 0x841dc)) with (Z_to_bv 64 0x841dc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ _ AG1) in STR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ _ AG1) in STRS; [|lia].
      unname_spm.
      destruct r as [q|]; [| destruct CASES].
      (nd_pre CASES 3%nat; intros A junk ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G1 BLK; nd_post).
      (nd_pre (blk_facts RNG1 s' _ FB m1 (q, A, 65536%Z) G1 ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros _ B1 B2; nd_post). cbn [cb_addr cb_size fst snd] in B1, B2.
      (* [comment removed for export] *)
      cbv beta iota. ienterG. zstep. if_false_by (eqz_cond_false A ltac:(lia)). zstep. zstep. zstep. zstep.
      apply evtF_done. eapply implMG_bind with (Q1 := LX fd P1 argv1 slack1).
      { eapply loop_spec; [| exact HNUL | exact HPL | exact HPEND].
        unfold LH. cbn [rd_buf rd_cap rd_len rd_chunks rd_content concat].
        repeat (lazymatch goal with |- @ex (list byte) _ => exists (@nil byte) | |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [right; split; reflexivity|].
        split.
        { split; [exists FB; exact G1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
          split; [exists junk; apply rw_cells_nil_CB; exact BLK|].
          cbn [length Z.of_nat]. split; [lia|]. split; [unfold MAX_INPUT; lia|]. split; [exists 0%Z; reflexivity| exact RS1]. }
        split; [reflexivity|]. split; [reflexivity|].
        split; [exact STRS|]. split; [lia| lia]. }
      intros res s'' RNG2 ms'' LXH. destruct res as [|q' content].
      + cbv beta iota. apply implMG_ret. apply evtF_done. exact LXH.
      + (nd_pre LXH 31%nat; intros ra' gp' y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 w5 w6 w7 w8 w9 w10 w11 y3 y4 y5 y6 F' fc' m'' A' cap' CBs' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros MB HC; nd_post).
        (nd_pre MB 9%nat; intros (FB2 & G2) MI2 ST2 (h0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & FR2) (junk2 & BUF2) HLC2 HCAP2 HJ2 RS2; nd_post).
        (pose proof RS2 as ndP__; nd_pre ndP__ 5%nat; intros Q1 Q2 Q3 Q4 Q5; nd_post).
        destruct (gd_errno _ _ _ GD _ _ _ _ _ _ _ G2) as (e2 & ERR2).
        (nd_pre (blk_facts RNG2 s'' _ FB2 m'' (q', A', cap') G2 ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros _ D1 D2; nd_post). cbn [cb_addr cb_size fst snd] in D1, D2.
        pose proof (blk_tclr RNG2 s'' _ FB2 m'' (q', A', cap') G2 ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) as BTLS. cbn [cb_addr cb_size fst snd] in BTLS.
        cbv beta iota. ienterG. zstep. zstep.
        name_spm.
        apply evtF_done. eapply implMG_msys_of_enode.
        { eapply (close_spec RNG2 _ spm _ (Z_to_bv 64 ATPv)) with (lo := LO) (fd := fd) (errv := e2);
            [ rewrite Hspm; exact ST2 | rewrite ETP; exact ERR2 | exact MI2 | reflexivity | lia | rewrite Hspm; lia | rewrite Hspm, ETP; lia | rewrite ETP; lia
            | rewrite Hspm; eapply rng_sub'; [exact Q2| lia] | rewrite ETP; eapply rng_sub'; [exact Q5| lia] ]. }
        intros r RNG3 ms' PO. unfold close_post in PO. destruct PO as (-> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MU WM MI3 ST3 ERR3; nd_post).
        replace (ret_pc (Z_to_bv 64 0x84284)) with (Z_to_bv 64 0x84284) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite ETP in *.
        lazymatch type of MU with munch _ ?ma ?mb => transport_after_call asegs ma mb MU WM end.
        apply (munch_weaken _ [(ATPv + -164, ATPv + -160); (bv_unsigned spm - 32, bv_unsigned spm)]%Z) in MU.
        2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
        assert (G3 : GIOA L RNG2 s'' [(q', A', cap')] FB2 [] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
        { eapply (gd_frame_errno _ _ _ GD); [exact G2 | exact MU | exact WM | | exact ERR3].
          constructor; [left; left; cbn [fst snd]; rewrite Hspm; lia| constructor]. }
        rewrite Hspm in *. unname_spm.
        apply implMG_ret. apply evtF_done.
        unfold RAX. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [| exact HC].
        split; [exists FB2; exact G3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists h0, g1, g2, g3, g4, g5, g6, g7, g8; exact FR2|].
        split; [exists junk2; exact BUF2|]. split; [exact HLC2|]. split; [exact HCAP2|]. split; [exact HJ2| exact RS2].
  Qed.
  End Zd5.
  #[using="FO fflagA GL GD MALLOC FREE EPR_OPEN EPR_READ EPR_BIG SITE_RS LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD drv_lit_mobjA block_mobjA"] Lemma read_all_spec : ltac:(let t := eval cbv delta [read_all_spec__stmt] in read_all_spec__stmt in exact t).
  Proof. exact read_all_spec__body. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_ret_spec__stmt : Prop := forall s RNG (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (FB : list cblk) (q : hptr) (A cap code : Z),
    GIOA L RNG s [(q, A, cap)] FB [] m -> mem_inv asegs m -> stk asegs m LO (USP + -128) -> mframe m -> rngs RNG -> (0 <= code <= 255)%Z ->
    implMG RNG (pfree HO q ;;; mret code) s main_post
      (MS (mkR ra (Z_to_bv 64 (USP + -128)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8437c) fc None m (seg_rom asegs)).
  Section Zd6.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 1).
  Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 2).
  Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 3).
  Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 4).
  Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 5).
  Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 6).
  Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 7).
  Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 8).
  Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 9).
  Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 10).
  Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 11).
  Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 12).
  Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 13).
  Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 14).
  Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 15).
  Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 16).
  Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 17).
  Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 18).
  Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 19).
  Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 20).
  Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 21).
  Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 22).
  Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 23).
  Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 24).
  Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 25).
  Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 26).
  Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 27).
  Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 28).
  Variable F : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 29).
  Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 30).
  Variable m : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 31).
  Variable FB : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 32).
  Variable q : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 33).
  Variable A : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 34).
  Variable cap : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 35).
  Variable code : ltac2:(SecDietF.SzSecF.ty 'free_ret_spec__stmt 36).
  #[using="argv envp uid hw rnd FREE LO_lo LO_hi USP16 TOP47 USP47 TRD AT_EXIT_I"] Lemma free_ret_spec__body : ltac:(let T := type of (fun (h : free_ret_spec__stmt) => h s RNG ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m FB q A cap code) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, (ra, (gp, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (FB, (q, (A, (cap, code))))))))))))))))))))))))))))))))))))) as _.
 intros G MI ST (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) RS HCODE.
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    ienterG. zstep. zstep.
    name_spm.
    apply evtF_done. eapply implMG_bind.
    { eapply FREE with (C1 := @nil cblk) (C2 := @nil cblk) (q := q) (A := A) (n := cap); [| reflexivity |].
      - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
      - eapply (unw_main RNG _ AFREE_PC spm _ _ 0x84384%Z);
          [ rewrite Hspm, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia
          | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | exact R1 | rewrite Hspm; lia ]. }
    intros [] s' RNG' ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
    unfold hpost_regs in E. destruct_exs E. subst ms'.
    cbn [app] in AG2, G2.
    pose proof (rngs_le _ _ FP RS) as RS'.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
    replace (ret_pc (Z_to_bv 64 0x84384)) with (Z_to_bv 64 0x84384) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite Hspm in *.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
    unname_spm.
    ienterG. do 12 zstep.
    replace (ret_pc (Z_to_bv 64 RA_MAIN)) with (Z_to_bv 64 RA_MAIN) by (symmetry; apply ret_pc_even; [unfold RA_MAIN; lia|reflexivity]).
    unfold RA_MAIN. zstep.
    apply evtF_done. apply implMG_ret. apply evtF_done. unfold main_post.
    release_frame FR ST2 (USP + -48)%Z.
    eapply AT_EXIT_I; [exact G2 | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; generalize LO_hi; lia
                      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; aln16 | exact RS'].
  Qed.
  End Zd6.
  #[using="argv envp uid hw rnd FREE LO_lo LO_hi USP16 TOP47 USP47 TRD AT_EXIT_I"] Lemma free_ret_spec : ltac:(let t := eval cbv delta [free_ret_spec__stmt] in free_ret_spec__stmt in exact t).
  Proof. exact free_ret_spec__body. Qed.

  #[using="rc sp0 argv envp uid hw rnd"] Lemma geu_cond_true : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
  Proof. intros. rewrite ltu_cond_false by lia. reflexivity. Qed.
  #[using="rc sp0 argv envp uid hw rnd"] Lemma geu_cond_false : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
  Proof. intros. rewrite ltu_cond_true by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition tail_spec__stmt : Prop := forall s RNG ms q content,
    RAX (RdDone q content) s RNG ms ->
    implMG RNG (let len := zlength content in
                 if len <? HDR_MIN then diag DShortHdr ;;; pfree HO q ;;; mret 2
                 else let cfg_word := le16 content in
                      let count_allocs := Z.testbit cfg_word 15 in
                      let config_len := Z.land cfg_word 0x7fff in
                      if len <? HDR_MIN + config_len then diag DCfgOverrun ;;; pfree HO q ;;; mret 2
                      else let config := firstn (Z.to_nat config_len) (skipn 2 content) in
                           let payload := skipn (Z.to_nat (6 + config_len)) content in
                           status <- run HO FO sites config payload ;;
                           (let status' := (if count_allocs then 0 else status)%Z in pfree HO q ;;; mret status'))%Z
      s main_post ms.
  Section Zd7.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 1).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 2).
  Variable q : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 3).
  Variable content : ltac2:(SecDietF.SzSecF.ty 'tail_spec__stmt 4).
  #[using="TP fflagA argv envp uid hw rnd GL GD FREE EFW TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF AT_EXIT_I drv_lit_mobjA block_mobjA"] Lemma tail_spec__body : ltac:(let T := type of (fun (h : tail_spec__stmt) => h s RNG ms q content) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, (ms, (q, content))))) as _.
    intros RX.
    (nd_pre RX 33%nat; intros ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A cap CBs ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros MB ndR3__; nd_post; revert ndR3__; intros ->).
    (nd_pre MB 9%nat; intros (FB & G) MI ST FRm (junk & BUF) HLC HCAP HJ RS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI.
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros CM1 CM2 _; nd_post). unfold GOT_STDERR, STDERR_P, STDERR_FILE in CM1, CM2.
    (nd_pre (blk_facts RNG s _ FB m (q, A, cap) G ltac:(left; reflexivity) ltac:(cbn [cb_size snd]; lia)) 3%nat; intros (_ & _ & _ & BRNG & _) B1 B2; nd_post). cbn [cb_addr cb_size fst snd] in BRNG, B1, B2.
    unfold zlength, of_bytes at 1. rewrite length_map. set (len := Z.of_nat (length CBs)) in *.
    cbv zeta. unfold HDR_MIN.
    ienterG. zstep. zstep.
    destruct (Z_lt_le_dec len 6) as [SHORT|LONG].
    - (* [comment removed for export] *)
      replace (len <? 6)%Z with true by (symmetry; apply Z.ltb_lt; exact SHORT).
      if_true_by (geu_cond_true 5 len ltac:(lia) ltac:(lia)).
      do 9 zstep.
      (nd_pre MSG_SHORT_HDR_ok 3%nat; intros RB EM LM; nd_post).
      name_spm.
      apply evtF_done. unfold diag, diag_short_hdr. rewrite <- EM. eapply implMG_bind.
      { eapply EFW with (MSG := MSG_SHORT_HDR) (bs := MSG_SHORT_HDR_bytes);
          [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI | exact RB | unfold MSG_SHORT_HDR; lia | rewrite LM; unfold MSG_SHORT_HDR; lia]
            | rewrite LM; unfold MSG_SHORT_HDR, DRV_RODATA_LO, DRV_RODATA_HI; lia | rewrite LM; lia | ].
        - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
        - eapply drv_lit_mobjA; [exact G | exact R3 | exact R4 | unfold MSG_SHORT_HDR; lia | rewrite LM; unfold MSG_SHORT_HDR, DRV_RODATA_HI; lia | lia]. }
      intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      pose proof (rngs_le _ _ FP RS) as RS'.
      replace (ret_pc (Z_to_bv 64 0x8437c)) with (Z_to_bv 64 0x8437c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hspm in *.
      (nd_pre FRm 10%nat; intros j0 f1 f2 f3 f4 f5 f6 f7 f8 FR; nd_post). apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_spm.
      eapply free_ret_spec; [exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact RS' | lia].
    - (* [comment removed for export] *)
      replace (len <? 6)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      if_false_by (geu_cond_false 5 len ltac:(lia) ltac:(lia)).
      destruct CBs as [|c0 [|c1 rest]]; [subst len; cbn in LONG; lia..|].
      pose proof BUF as BUF'. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in BUF' as [BUF1 _].
      assert (BY : bytes_at asegs m A (c0 :: c1 :: rest)).
      { destruct BUF1 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
      pose proof (bytes_at_read asegs _ A _ 0 1 BY ltac:(lia) ltac:(cbn; lia)) as HR0. change (Z.to_nat 0) with 0%nat in HR0. cbn [firstn skipn] in HR0. rewrite Z.add_0_r in HR0.
      pose proof (bytes_at_read asegs _ A _ 1 1 BY ltac:(lia) ltac:(cbn; lia)) as HR1. change (Z.to_nat 1) with 1%nat in HR1. cbn [firstn skipn] in HR1.
      pose proof (bv_unsigned_in_range 8 c0) as RC0. pose proof (bv_unsigned_in_range 8 c1) as RC1. unfold bv_modulus in RC0, RC1. cbn in RC0, RC1.
      zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite hdr_hi. rewrite lor_disjoint8 by (pose proof (Z.mod_pos_bound (bv_unsigned c1) 128); lia).
      assert (EL16 : le16 (of_bytes (c0 :: c1 :: rest)) = (bv_unsigned c0 + bv_unsigned c1 * 256)%Z) by reflexivity.
      rewrite EL16. rewrite land_7fff by lia. rewrite testbit15 by lia.
      set (Lc := (bv_unsigned c1 mod 128 * 256 + bv_unsigned c0)%Z) in *.
      assert (HL : (0 <= Lc < 32768)%Z) by (pose proof (Z.mod_pos_bound (bv_unsigned c1) 128); lia).
      unfold of_bytes. rewrite length_map. fold len.
      zstep.
      destruct (Z_lt_le_dec len (6 + Lc)) as [OVR|OK].
      + (* [comment removed for export] *)
        replace (len <? 6 + Lc)%Z with true by (symmetry; apply Z.ltb_lt; exact OVR).
        if_true_by (ltu_cond_true len (Lc + 6)%Z ltac:(lia) ltac:(lia)).
        do 8 zstep.
        (nd_pre MSG_CFG_OVERRUN_ok 3%nat; intros RB EM LM; nd_post).
        name_spm.
        apply evtF_done. unfold diag, diag_cfg_overrun. rewrite <- EM. eapply implMG_bind.
        { eapply EFW with (MSG := MSG_CFG_OVERRUN) (bs := MSG_CFG_OVERRUN_bytes);
            [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI | exact RB | unfold MSG_CFG_OVERRUN; lia | rewrite LM; unfold MSG_CFG_OVERRUN; lia]
              | rewrite LM; unfold MSG_CFG_OVERRUN, DRV_RODATA_LO, DRV_RODATA_HI; lia | rewrite LM; lia | ].
          - std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5.
          - eapply drv_lit_mobjA; [exact G | exact R3 | exact R4 | unfold MSG_CFG_OVERRUN; lia | rewrite LM; unfold MSG_CFG_OVERRUN, DRV_RODATA_HI; lia | lia]. }
        intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI2 ST2 AG2 G2; nd_post). clear MI.
        unfold hpost_regs in E. destruct_exs E. subst ms'.
        pose proof (rngs_le _ _ FP RS) as RS'.
        replace (ret_pc (Z_to_bv 64 0x8437c)) with (Z_to_bv 64 0x8437c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite Hspm in *.
        (nd_pre FRm 10%nat; intros j0 f1 f2 f3 f4 f5 f6 f7 f8 FR; nd_post). apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
        unname_spm.
        eapply free_ret_spec; [exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact RS' | lia].
      + (* [comment removed for export] *)
        replace (len <? 6 + Lc)%Z with false by (symmetry; apply Z.ltb_ge; lia).
        if_false_by (ltu_cond_false len (Lc + 6)%Z ltac:(lia) ltac:(lia)).
        assert (exists d0 d1 d2 d3 rest', skipn (Z.to_nat (2 + Lc)) (c0 :: c1 :: rest) = d0 :: d1 :: d2 :: d3 :: rest') as (d0 & d1 & d2 & d3 & rest' & ED).
        { pose proof (length_skipn (Z.to_nat (2 + Lc)) (c0 :: c1 :: rest)) as LS.
          destruct (skipn (Z.to_nat (2 + Lc)) (c0 :: c1 :: rest)) as [|d0 [|d1 [|d2 [|d3 rest']]]]; cbn [length] in LS, LONG, OK; try (subst len; cbn [length] in *; lia).
          repeat eexists. }
        assert (BYp : bytes_at asegs m (A + (2 + Lc)) (d0 :: d1 :: d2 :: d3 :: rest')).
        { rewrite <- ED. pose proof BY as BY2. rewrite <- (firstn_skipn (Z.to_nat (2 + Lc)) (c0 :: c1 :: rest)) in BY2.
          apply bytes_at_app in BY2 as [_ X]. rewrite length_firstn in X.
          replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + Lc)) (length (c0 :: c1 :: rest))))%Z with (A + (2 + Lc))%Z in X by (subst len; lia). exact X. }
        pose proof (bytes_at_read asegs _ _ _ 0 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB0. change (Z.to_nat 0) with 0%nat in HB0. cbn [firstn skipn] in HB0.
        pose proof (bytes_at_read asegs _ _ _ 1 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB1. change (Z.to_nat 1) with 1%nat in HB1. cbn [firstn skipn] in HB1.
        pose proof (bytes_at_read asegs _ _ _ 2 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB2. change (Z.to_nat 2) with 2%nat in HB2. cbn [firstn skipn] in HB2.
        pose proof (bytes_at_read asegs _ _ _ 3 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB3. change (Z.to_nat 3) with 3%nat in HB3. cbn [firstn skipn] in HB3.
        do 6 zstep. do 16 zstep.
        (* [comment removed for export] *)
        (nd_pre FRm 10%nat; intros j0 f1 f2 f3 f4 f5 f6 f7 f8 FR; nd_post).
        assert (Elen : len = Z.of_nat (length (c0 :: c1 :: rest))) by reflexivity. clearbody len.
        name_spm.
        apply evtF_done. eapply implMG_bind.
        { eapply TRUN with (L := L) (RNG := RNG) (CL := [(q, A, cap)]) (FB := FB) (lo := LO) (Lc := Lc) (A := A) (content := c0 :: c1 :: rest);
            [ | rewrite Hspm; generalize TOP_lo; lia | exact TRD | exact TRF | exact BY | lia | lia | unfold MAX_INPUT in *; lia
              | exists (q, A, cap); split; [left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]
              | reflexivity | reflexivity | f_equal; lia | f_equal; lia ].
          std_pre_tac G ST MI Hspm R1 R2 R3 R4 R5. }
        intros r s' RNG' ms' PO. unfold target_run_post in PO. destruct PO as (FP & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MI2 ST2 AG2 G2 Hr; nd_post). clear MI.
        pose proof (rngs_le _ _ FP RS) as RS'.
        repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
        replace (ret_pc (Z_to_bv 64 0x842fc)) with (Z_to_bv 64 0x842fc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite Hspm in *.
        apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
        unname_spm.
        cbv zeta. ienterG. zstep.
        destruct (Z.leb_spec 128 (bv_unsigned c1)) as [CA|NCA].
        * (* [comment removed for export] *)
          replace (128 <=? bv_unsigned c1)%Z with true by (symmetry; apply Z.leb_le; exact CA).
          if_true_by (eq_trans (sxb_ltz c1) (proj2 (Z.leb_le _ _) CA)).
          do 5 zstep. zstep.
          apply evtF_done. eapply free_ret_spec; [exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact RS' | lia].
        * replace (128 <=? bv_unsigned c1)%Z with false by (symmetry; apply Z.leb_gt; exact NCA).
          if_false_by (eq_trans (sxb_ltz c1) (proj2 (Z.leb_gt _ _) NCA)).
          zstep. zstep.
          apply evtF_done. eapply free_ret_spec; [exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact RS' | lia].
  Qed.
  End Zd7.
  #[using="TP fflagA argv envp uid hw rnd GL GD FREE EFW TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF AT_EXIT_I drv_lit_mobjA block_mobjA"] Lemma tail_spec : ltac:(let t := eval cbv delta [tail_spec__stmt] in tail_spec__stmt in exact t).
  Proof. exact tail_spec__body. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition main_spec__stmt : Prop := forall s RNG ms,
    main_entry s RNG ms ->
    implMG RNG (main_prog HO FO sites (argv_Z argv)) s main_post ms.
  Section Zd8.   (* [comment removed for export] *)
  Variable s : ltac2:(SecDietF.SzSecF.ty 'main_spec__stmt 0).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'main_spec__stmt 1).
  Variable ms : ltac2:(SecDietF.SzSecF.ty 'main_spec__stmt 2).
  #[using="TP fflagA GL GD MALLOC FREE EPR_USAGE EPR_OPEN EPR_READ EPR_BIG EFW SITE_RS TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF AT_EXIT_I drv_lit_mobjA drv_stack_writes block_mobjA"] Lemma main_spec__body : ltac:(let T := type of (fun (h : main_spec__stmt) => h s RNG ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (s, (RNG, ms))) as _.
    intros ME.
    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2].
    2:{ exact (main_usage s RNG ms ME NE2). }
    (nd_pre ME 31%nat; intros gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m FB ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros G MI ST VA RS CS; nd_post).
    pose proof usp_facts as USPF. (pose proof RS as ndP__; nd_pre ndP__ 5%nat; intros R1 R2 R3 R4 R5; nd_post).
    pose proof LO_lo as LOLO. pose proof LO_hi as LOHI. unfold MAIN_STACK, TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in LOHI. unfold MAIN_ENTRY.
    assert (EA : exists av0 av1, argv = [av0; av1]) by (destruct argv as [|x [|y [|z w]]]; cbn in E2; try lia; eauto).
    (nd_pre EA 3%nat; intros av0 av1 EARGV; nd_post).
    unfold main_prog, main_model. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length argv) =? 2)%Z with true by (symmetry; apply Z.eqb_eq; exact E2). cbn [negb].
    replace (nth 1 (argv_Z argv) []) with (map bv_unsigned av1) by (rewrite EARGV; reflexivity).
    pose proof (munch_refl [(USP - 128, USP - 48)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    carve_frame 80%nat ST.
    do 11 zstep.
    replace (argc argv) with 2%Z by (unfold argc; lia).
    zstep. if_false_by (eq_cond 2).
    lazymatch type of MU with munch _ _ ?mb =>
      destruct (drv_stack_writes L RNG s [] FB m mb _ (USP - 48)%Z G MU WM) as [G1 AG0]; [constructor; [cbn [fst snd]; lia| constructor] | lia |] end.
    clear MU WM.
    apply evtF_done. eapply implMG_bind with (Q1 := RAX).
    - eapply (read_all_spec _ _ _ av1); [| rewrite EARGV; reflexivity | exact VA].
      unfold P2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G1|]. split; [exact MI|]. split; [exact ST|].
      split; [eexists _, _, _, _, _, _, _, _, _; exact FR|]. split; [exact RS|].
      first [exact CS | assumption | match goal with HB : bytes_at _ _ USP SBK |- _ => exact HB end].
    - intros res s' RNG' ms' RX. destruct res as [|q content].
      + cbv beta iota. apply implMG_ret.
        eapply (at_exit2_exit s' RNG' ms' (fun _ s0 R0 ms0 => main_post 2 s0 R0 ms0)); [exact RX | intros ms0 HP; exact HP].
      + cbv beta iota. apply tail_spec. exact RX.
  Qed.
  End Zd8.
  #[using="TP fflagA GL GD MALLOC FREE EPR_USAGE EPR_OPEN EPR_READ EPR_BIG EFW SITE_RS TRUN LO_lo LO_hi USP16 TOP_lo TOP47 USP47 TRD TRF AT_EXIT_I drv_lit_mobjA drv_stack_writes block_mobjA"] Theorem main_spec : ltac:(let t := eval cbv delta [main_spec__stmt] in main_spec__stmt in exact t).
  Proof. exact main_spec__body. Qed.
End Main.
End CANSEC1.
End TwB.
