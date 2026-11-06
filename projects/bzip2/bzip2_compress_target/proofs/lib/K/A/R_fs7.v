(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA Arr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require R_intalloc F_memset R_setshadow R_poison.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s R_thread R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_intalloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_memset.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_setshadow.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_ok.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma land127 : forall x, 0 <= x -> Z.land x 127 = x mod 128.
Proof. intros x Hx. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fs7_scan : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
    ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
  fs_flags FSB 7 m fl -> Z.of_nat (length fl) = 128 -> flags_ok 7 fl ->
  0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 7 + 128 <= 2 ^ 47 ->
  scan_from fl 128 h 128 = Some j ->
  (forall t0 a0, evt bsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 7 + (h + Z.of_nat j) mod 128))
               (Z_to_bv 64 (fl_base FSB 7)) (Z_to_bv 64 127) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 128))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3e41c) fc None m (seg_rom bsegs))) ->
  mem_inv bsegs m ->
  forall (k : nat), (k <= j)%nat -> forall t0 a3 a7,
  evt bsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (128 - Z.of_nat (j - k))) a1 (Z_to_bv 64 (h + Z.of_nat (j - k)))
             a3 (Z_to_bv 64 (fl_base FSB 7)) (Z_to_bv 64 127) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e3d0) fc None m (seg_rom bsegs)).
Proof.
  intros until fc. intros FL LEN OK HH HF HB SC K MI.
  destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  induction k as [|k IH]; intros Hk t0 a3 a7.
  - rewrite Nat.sub_0_r.
    assert (E1 : Z.land (h + Z.of_nat j) 127 = (h + Z.of_nat j) mod 128) by (apply land127; lia).
    zhide.
    do 2 zstep. rewrite E1.
    set (pos := (h + Z.of_nat j) mod 128) in *.
    assert (Hpos : 0 <= pos < 128) by (apply Z.mod_pos_bound; lia).
    pose proof (u8arr_read bsegs m (fl_base FSB 7) (map b8 fl) pos (b8 0) (Z_to_bv 64 (fl_base FSB 7 + pos)) FL) as RD.
    rewrite nth_error_map_b8, Hfree in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
    zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 0)) with (Z_to_bv 64 0).
    zstep. ifT.
    exact (K _ _).
  - set (i := (j - S k)%nat) in *.
    assert (Hi : (i < j)%nat) by (unfold i; lia).
    assert (E1 : Z.land (h + Z.of_nat i) 127 = (h + Z.of_nat i) mod 128) by (apply land127; lia).
    do 2 zstep. rewrite E1.
    set (pos := (h + Z.of_nat i) mod 128) in *.
    assert (Hpos : 0 <= pos < 128) by (apply Z.mod_pos_bound; lia).
    assert (Hb1 : nth (Z.to_nat pos) fl 1 = 1).
    { destruct (flags_ok_nth 7 fl (Z.to_nat pos) OK ltac:(lia)) as [H0|H0]; [|exact H0].
      exfalso. exact (Hbusy i Hi H0). }
    pose proof (u8arr_read bsegs m (fl_base FSB 7) (map b8 fl) pos (b8 1) (Z_to_bv 64 (fl_base FSB 7 + pos)) FL) as RD.
    rewrite nth_error_map_b8, Hb1 in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
    zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 1)) with (Z_to_bv 64 1).
    zstep. ifF.
    do 2 zstep.
    replace (bv_swrap 32 (128 - Z.of_nat i + -1)) with (128 - Z.of_nat (j - k)).
    2:{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. unfold i in *. lia. }
    replace (h + Z.of_nat i + 1) with (h + Z.of_nat (j - k)) by (unfold i in *; lia).
    zstep. ifT.
    apply IH. lia.
Qed.

Corollary fs7_scan0 : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
    ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
  fs_flags FSB 7 m fl -> Z.of_nat (length fl) = 128 -> flags_ok 7 fl ->
  0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 7 + 128 <= 2 ^ 47 ->
  scan_from fl 128 h 128 = Some j ->
  (forall t0 a0, evt bsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 7 + (h + Z.of_nat j) mod 128))
               (Z_to_bv 64 (fl_base FSB 7)) (Z_to_bv 64 127) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 128))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3e41c) fc None m (seg_rom bsegs))) ->
  mem_inv bsegs m ->
  forall t0 a3 a7,
  evt bsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 128) a1 (Z_to_bv 64 h)
             a3 (Z_to_bv 64 (fl_base FSB 7)) (Z_to_bv 64 127) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e3d0) fc None m (seg_rom bsegs)).
Proof.
  intros. pose proof (fs7_scan Q m FSB h fl j ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    H H0 H1 H2 H3 H4 H5 H6 H7 j ltac:(lia) t0 a3 a7) as X.
  rewrite Nat.sub_diag in X. cbn [Z.of_nat] in X. rewrite Z.sub_0_r, Z.add_0_r in X. exact X.
Qed.

Definition sm7_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB h : Z) (fl : list Z) (lo size : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (j : nat) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 (Z_to_bv 64 (frame_addr FSB 7 ((h + Z.of_nat j) mod 128)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm_W 7 FSB ((h + Z.of_nat j) mod 128) (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ (j < 128)%nat /\ nth (Z.to_nat ((h + Z.of_nat j) mod 128)) fl 1 = 0
    /\ fs_hint FSB 7 m' (h + Z.of_nat j + 1) /\ fs_const FSB m'
    /\ fs_flags FSB 7 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 128)) 1)
    /\ wr_at bsegs m' (frame_addr FSB 7 ((h + Z.of_nat j) mod 128)) 8192
    /\ rw_cells bsegs m' (frame_addr FSB 7 ((h + Z.of_nat j) mod 128) + 8184) [C8 (Z_to_bv 64 (fl_base FSB 7 + (h + Z.of_nat j) mod 128))]
    /\ wr_at bsegs m' (shad (frame_addr FSB 7 ((h + Z.of_nat j) mod 128))) 1024
    /\ rw_cells bsegs m' (shad (frame_addr FSB 7 ((h + Z.of_nat j) mod 128)))
         [CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (size / 8)))]
    /\ fs_free_frames FSB 7 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 128)) 1).

Definition sm7_entry : Z := 0x3e334.

Lemma stack_malloc_7_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB h : Z) (fl : list Z) (DTV dtvbeg TCX T lo size : Z) (tb te : word),
  fs_const FSB m -> fs_hint FSB 7 m h -> fs_flags FSB 7 m fl -> flags_ok 7 fl -> (nbusy fl < 128)%nat -> 0 <= h < 2 ^ 61 ->
  fs_free_frames FSB 7 m fl -> rw_cells bsegs m tpA [C8 (Z_to_bv 64 FSB)] ->
  tga_cells DTV dtvbeg m -> thread_cells TCX T m -> ttls_cells T m tb te -> m2s_cells m ->
  FSB_ok2 FSB -> 0x7fff00000000 <= lo -> FSB + kFakeStackSize <= lo ->
  0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 -> 0 < TCX -> TCX + 0xa0 <= lo -> 0 < T -> T + 4096 <= lo ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 224 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 size -> 0 < size <= 8192 -> size mod 8 = 0 -> ps_cells m ->
  evt bsegs (sm7_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB h fl lo size m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sm7_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until te. intros FC HI FL OK NB HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL HB HX HXL HT HTL ST LO SPH MI Ha0 Hsz Hsz8 PS. subst a0.
  pose proof OK as (LEN & _). rewrite NF_7 in LEN.
  destruct (scan_target_exists fl 128 h LEN ltac:(lia)) as (j & SC).
  destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
  set (pos := (h + Z.of_nat j) mod 128) in *.
  assert (Hpos : 0 <= pos < 128) by (apply Z.mod_pos_bound; lia).
  destruct (FF pos ltac:(rewrite NF_7; lia) Hfree) as [[junkF FRm] [junkS SHm]].
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  rewrite shad_frame in SHm by lia. rewrite fsz_7 in FRm, SHm. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in SHm.
  unfold frame_addr, fsz in FRm, SHm.
  change (7 * 2 ^ 20) with 7340032 in FRm.
  change (7 * 2 ^ 17) with 917504 in SHm. change (8192 / 8) with 1024 in SHm. change (Z.to_nat 1024) with 1024%nat in SHm.
  replace (FSB + 36864 + 7340032 + pos * 8192) with (FSB + 7376896 + pos * 8192) in FRm by lia.
  assert (FRW : wr_at bsegs m (FSB + 7376896 + pos * 8192) 8192).
  { destruct FRm as [_ W]. cbn [cells_size csize] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W. }
  pose proof (rw_cells_split_CB bsegs m _ [] (Z.to_nat 8192) junkF [] [32%nat; Z.to_nat 8152; 8%nat] FRm ltac:(cbn [sum_nat]; lia)) as FRs.
  cbn [app mk_CB_cells] in FRs. clear FRm.
  lazymatch type of FRs with rw_cells _ _ ?A0 (?c1 :: ?rest) => apply (proj1 (rw_cells_app2 m A0 [c1] rest)) in FRs end. destruct FRs as [FRm FRs].
  lazymatch type of FRs with rw_cells _ _ ?A0 (?c1 :: ?rest) => apply (proj1 (rw_cells_app2 m A0 [c1] rest)) in FRs end. destruct FRs as [_ FRhi].
  lazymatch type of FRhi with rw_cells _ _ ?A0 _ => replace A0 with (FSB + 7376896 + pos * 8192 + 8184) in FRhi by (cbn [cells_size csize]; lia) end.
  set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
  clearbody F8.
  replace (SHB + F8 + 4608 + 917504 + pos * 1024) with (F8 + pos * 1024 + 2148372992) in SHm by (unfold SHB; lia).
  (* [comment removed for export] *)
  assert (PA : ps_args_ok (FSB + 7376896 + pos * 8192) size).
  { unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [split; [|split; [exact Hsz8 | lia]]|lia].
    rewrite EF8. replace (8 * F8 + 7376896 + pos * 8192) with ((F8 + 922112 + pos * 1024) * 8) by lia. apply Z.mod_mul. lia. }
  assert (SHW : wr_at bsegs m (F8 + pos * 1024 + 2148372992) 1024) by (destruct SHm as [_ W]; exact W).
  assert (Hq8 : 0 <= size / 8 <= 1024) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  set (k8 := Z.to_nat (size / 8)) in *.
  pose proof (rw_cells_split_CB bsegs m _ [] 1024%nat junkS [] [k8; (1024 - k8)%nat] SHm ltac:(cbn [sum_nat]; unfold k8; lia)) as SHs.
  cbn [app mk_CB_cells] in SHs. clear SHm.
  apply (rw_cells_app2 m _ [CB k8 (firstn k8 junkS)] [CB (1024 - k8) (firstn (1024 - k8) (skipn k8 junkS))]) in SHs. destruct SHs as [SHa SHb].
  cbn [cells_size csize Nat.add] in SHb. rewrite Nat.add_0_r in SHb. unfold k8 in SHb at 1. rewrite Z2Nat.id in SHb by lia.
  unfold fs_flags, fl_base, flags_off in FL. change (32768 - 2 ^ (15 - 7)) with 32512 in FL.
  replace (FSB + 4096 + 32512) with (FSB + 36608) in FL by lia.
  assert (LENM : Z.of_nat (length (map b8 fl)) = 128) by (rewrite length_map; exact LEN).
  destruct M2S as (M2a & M2b & M2c).
  destruct TGA as (AI & RL & DP & D1 & DC). destruct TC as (TS & TX). destruct TS as (KI & K & TS & T0).
  destruct DC as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  unfold fs_const, fs_hint, ttls_cells, tpA, g_real_tls_get_addr, musl_tls_get_addr_entry, g_tls_index, g_dtv_ptr, g_dtv, g_dtv1,
    dtv1_val, g_got_common_flags, g_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity,
    g_got_dtls_off, g_tls_dtls, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, sm7_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl (sm_W 7 FSB pos (bv_unsigned sp)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold sm_W in MU. rewrite shad_frame in MU by lia. unfold frame_addr, fsz, fl_base, flags_off in MU.
  change (7 * 2 ^ 20) with 7340032 in MU. change (64 * 2 ^ 7) with 8192 in MU. change (7 * 2 ^ 17) with 917504 in MU.
  change (8192 / 8) with 1024 in MU. change (32768 - 2 ^ (15 - 7)) with 32512 in MU. unfold SHB in MU.
  replace (FSB + 36864 + 7340032 + pos * 8192) with (FSB + 7376896 + pos * 8192) in MU by lia.
  replace (FSB + 4096 + 32512) with (FSB + 36608) in MU by lia.
  replace (2147450880 + FSB / 8 + 4608 + 917504 + pos * 1024) with (F8 + pos * 1024 + 2148372992) in MU
    by (rewrite EF8, (Z.mul_comm 8 F8), Z.div_mul by lia; lia).
  replace (FSB + 8 * 7) with (FSB + 56) in MU, HI by lia.
  carve_frame 48%nat ST.
  zidle_begin sp 48%Z MUz WMz.
  zhide.
  zhide. do 11 zstep.
  zidle_end MUz WMz.
  sp_facts.
  call (tls_get_addr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ DTV dtvbeg TCX T lo tb te).
  1: exact (conj AI (conj RL (conj DP (conj D1 (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 G8))))))))))).
  1: exact (conj (conj KI (conj K (conj TS T0))) TX).
  1: exact TT.
  all: rewrite ?Esp; try lia; try assumption.
  rewrite Esp in POST. rename POST into ST.
  clear AI RL DP D1 G1 G2 G3 G4 G5 G6 G7 G8 KI K TS T0 TX TT.
  unfold tpA. zstep. zstep. ifF.
  do 3 zstep. ifT.
  do 5 zstep. ifF.
  zhide. do 15 zstep.
  replace (Z_to_bv 64 (FSB + 36608)) with (Z_to_bv 64 (fl_base FSB 7)) by (unfold fl_base, flags_off; f_equal; cbn; lia).
  eapply (fs7_scan0 _ x13 FSB h fl j).
  1:{ unfold fs_flags, fl_base, flags_off. change (32768 - 2 ^ (15 - 7)) with 32512.
      replace (FSB + 4096 + 32512) with (FSB + 36608) by lia. exact FL. }
  all: try assumption; try lia.
  1:{ unfold fl_base, flags_off. cbn. lia. }
  intros t0' a0'.
  change ((h + Z.of_nat j) mod 128) with pos.
  replace (fl_base FSB 7) with (FSB + 36608) by (unfold fl_base, flags_off; cbn; lia).
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_store_ok bsegs mm (FSB + 36608) (map b8 fl) pos (wa (FSB + 36608 + pos)) FL ltac:(lia) ltac:(f_equal; lia)) as SOK;
    pose proof (u8arr_write bsegs mm (FSB + 36608) (map b8 fl) pos (b8 1) FL ltac:(lia)) as FL2 end.
  zstep. change (le1 (Z_to_bv 64 1)) with [b8 1]. clear FL. store_done.
  do 8 zstep.
  assert (SH13 : pos ≪ 13 = pos * 8192) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity). rewrite SH13.
  replace (FSB + 36864 + (7340032 + pos * 8192)) with (FSB + 7376896 + pos * 8192) by lia.
  do 3 zstep.
  zstep. zstep.
  call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 7376896 + pos * 8192)).
  1: reflexivity.
  1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
  1: exact (conj M2a (conj M2b M2c)).
  1: assumption.
  assert (ESH : shad (FSB + 7376896 + pos * 8192) = F8 + pos * 1024 + 2148372992).
  { unfold shad, SHB. rewrite EF8. replace (8 * F8 + 7376896 + pos * 8192) with ((F8 + 922112 + pos * 1024) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  clear TLS M2a M2b M2c.
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ps_cells_framed m mm _ PS MU WM ltac:(unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia)) as PSm end.
  rewrite <- ESH in SHa.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 7376896 + pos * 8192) size 0 lo (firstn k8 junkS)).
  1: exact PA.
  1: lia.
  1: right; lia.
  1: exact SHa.
  1: exact PSm.
  all: rewrite ?Esp; try lia; try assumption; try (unfold kHighShadowEnd; lia).
  rewrite Esp in POST. rename POST into ST.
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  assert (EFR : FSB + 7376896 + pos * 8192 = frame_addr FSB 7 pos) by (unfold frame_addr, fsz; cbn; lia).
  rewrite EFR.
  lazymatch type of MU with munch _ _ ?mm => rename mm into mF end.
  apply evt_done. unfold sm7_post. change ((h + Z.of_nat j) mod 128) with pos.
  do 15 eexists. exists mF.
  split; [reflexivity|]. change ((h + Z.of_nat j) mod 128) with pos.
  assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (MU' : munch (sm_W 7 FSB pos (bv_unsigned sp)) m mF).
  { replace (sm_W 7 FSB pos (bv_unsigned sp)) with
      [(FSB + 56, FSB + 56 + 8); (FSB + 36608 + pos, FSB + 36608 + pos + 1);
       (FSB + 7376896 + pos * 8192, FSB + 7376896 + pos * 8192 + 8192);
       (F8 + pos * 1024 + 2148372992, F8 + pos * 1024 + 2148372992 + 1024);
       (bv_unsigned sp - 224, bv_unsigned sp)]; [exact MU|].
    unfold sm_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
    change (7 * 2 ^ 20) with 7340032. change (64 * 2 ^ 7) with 8192. change (7 * 2 ^ 17) with 917504.
    change (8192 / 8) with 1024. change (32768 - 2 ^ (15 - 7)) with 32512.
    repeat (f_equal; try lia). }
  split; [exact MU'|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [change (Z.to_nat 128) with 128%nat in Hj; exact Hj|]. split; [exact Hfree|].
  split; [exact HI|]. split; [exact FC|].
  split.
  { unfold fs_flags. rewrite map_b8_upd. replace (fl_base FSB 7) with (FSB + 36608) by (unfold fl_base, flags_off; cbn; lia).
    exact FL2. }
  split; [rewrite <- EFR; exact FRW|].
  split.
  { rewrite <- EFR. replace (fl_base FSB 7 + pos) with (FSB + 36608 + pos) by (unfold fl_base, flags_off; cbn; lia). exact FRhi. }
  split; [rewrite <- EFR, ESH; exact SHW|].
  split; [rewrite <- EFR; assumption|].
  apply (fs_free_frames_transport FSB 7 m mF _ _ (fs_free_frames_take FSB 7 m fl (Z.to_nat pos) FF) MU' WM).
  intros p Hp Hf. pose proof (nth_upd_free_other _ _ _ Hf) as Hne. rewrite NF_7 in Hp.
  assert (Hne' : p <> pos) by (intro E; apply Hne; rewrite E; reflexivity).
  unfold sm_W. rewrite !shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
  change (7 * 2 ^ 20) with 7340032. change (64 * 2 ^ 7) with 8192. change (7 * 2 ^ 17) with 917504.
  change (8192 / 8) with 1024. change (32768 - 2 ^ (15 - 7)) with 32512.
  cbn [disjoint_from]. split; repeat split; lia.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import R_intalloc F_memset R_setshadow R_poison.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s R_thread R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma land127 : forall x, 0 <= x -> Z.land x 127 = x mod 128.
Proof. intros x Hx. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fs7_scan : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
    ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
  fs_flags FSB 7 m fl -> Z.of_nat (length fl) = 128 -> flags_ok 7 fl ->
  0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 7 + 128 <= 2 ^ 47 ->
  scan_from fl 128 h 128 = Some j ->
  (forall t0 a0, evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 7 + (h + Z.of_nat j) mod 128))
               (Z_to_bv 64 (fl_base FSB 7)) (Z_to_bv 64 127) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 128))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3e534) fc None m (seg_rom asegs))) ->
  mem_inv asegs m ->
  forall (k : nat), (k <= j)%nat -> forall t0 a3 a7,
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (128 - Z.of_nat (j - k))) a1 (Z_to_bv 64 (h + Z.of_nat (j - k)))
             a3 (Z_to_bv 64 (fl_base FSB 7)) (Z_to_bv 64 127) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e4e8) fc None m (seg_rom asegs)).
Proof.
  intros until fc. intros FL LEN OK HH HF HB SC K MI.
  destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  induction k as [|k IH]; intros Hk t0 a3 a7.
  - rewrite Nat.sub_0_r.
    assert (E1 : Z.land (h + Z.of_nat j) 127 = (h + Z.of_nat j) mod 128) by (apply land127; lia).
    zhide.
    do 2 zstep. rewrite E1.
    set (pos := (h + Z.of_nat j) mod 128) in *.
    assert (Hpos : 0 <= pos < 128) by (apply Z.mod_pos_bound; lia).
    pose proof (u8arr_read asegs m (fl_base FSB 7) (map b8 fl) pos (b8 0) (Z_to_bv 64 (fl_base FSB 7 + pos)) FL) as RD.
    rewrite nth_error_map_b8, Hfree in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
    zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 0)) with (Z_to_bv 64 0).
    zstep. ifT.
    exact (K _ _).
  - set (i := (j - S k)%nat) in *.
    assert (Hi : (i < j)%nat) by (unfold i; lia).
    assert (E1 : Z.land (h + Z.of_nat i) 127 = (h + Z.of_nat i) mod 128) by (apply land127; lia).
    do 2 zstep. rewrite E1.
    set (pos := (h + Z.of_nat i) mod 128) in *.
    assert (Hpos : 0 <= pos < 128) by (apply Z.mod_pos_bound; lia).
    assert (Hb1 : nth (Z.to_nat pos) fl 1 = 1).
    { destruct (flags_ok_nth 7 fl (Z.to_nat pos) OK ltac:(lia)) as [H0|H0]; [|exact H0].
      exfalso. exact (Hbusy i Hi H0). }
    pose proof (u8arr_read asegs m (fl_base FSB 7) (map b8 fl) pos (b8 1) (Z_to_bv 64 (fl_base FSB 7 + pos)) FL) as RD.
    rewrite nth_error_map_b8, Hb1 in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
    zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 1)) with (Z_to_bv 64 1).
    zstep. ifF.
    do 2 zstep.
    replace (bv_swrap 32 (128 - Z.of_nat i + -1)) with (128 - Z.of_nat (j - k)).
    2:{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. unfold i in *. lia. }
    replace (h + Z.of_nat i + 1) with (h + Z.of_nat (j - k)) by (unfold i in *; lia).
    zstep. ifT.
    apply IH. lia.
Qed.

Corollary fs7_scan0 : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
    ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
  fs_flags FSB 7 m fl -> Z.of_nat (length fl) = 128 -> flags_ok 7 fl ->
  0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 7 + 128 <= 2 ^ 47 ->
  scan_from fl 128 h 128 = Some j ->
  (forall t0 a0, evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 7 + (h + Z.of_nat j) mod 128))
               (Z_to_bv 64 (fl_base FSB 7)) (Z_to_bv 64 127) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 128))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3e534) fc None m (seg_rom asegs))) ->
  mem_inv asegs m ->
  forall t0 a3 a7,
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 128) a1 (Z_to_bv 64 h)
             a3 (Z_to_bv 64 (fl_base FSB 7)) (Z_to_bv 64 127) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e4e8) fc None m (seg_rom asegs)).
Proof.
  intros. pose proof (fs7_scan Q m FSB h fl j ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    H H0 H1 H2 H3 H4 H5 H6 H7 j ltac:(lia) t0 a3 a7) as X.
  rewrite Nat.sub_diag in X. cbn [Z.of_nat] in X. rewrite Z.sub_0_r, Z.add_0_r in X. exact X.
Qed.

Definition sm7_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB h : Z) (fl : list Z) (lo size : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (j : nat) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 (Z_to_bv 64 (frame_addr FSB 7 ((h + Z.of_nat j) mod 128)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm_W 7 FSB ((h + Z.of_nat j) mod 128) (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ (j < 128)%nat /\ nth (Z.to_nat ((h + Z.of_nat j) mod 128)) fl 1 = 0
    /\ fs_hint FSB 7 m' (h + Z.of_nat j + 1) /\ fs_const FSB m'
    /\ fs_flags FSB 7 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 128)) 1)
    /\ wr_at asegs m' (frame_addr FSB 7 ((h + Z.of_nat j) mod 128)) 8192
    /\ rw_cells asegs m' (frame_addr FSB 7 ((h + Z.of_nat j) mod 128) + 8184) [C8 (Z_to_bv 64 (fl_base FSB 7 + (h + Z.of_nat j) mod 128))]
    /\ wr_at asegs m' (shad (frame_addr FSB 7 ((h + Z.of_nat j) mod 128))) 1024
    /\ rw_cells asegs m' (shad (frame_addr FSB 7 ((h + Z.of_nat j) mod 128)))
         [CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (size / 8)))]
    /\ fs_free_frames FSB 7 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 128)) 1).

Definition sm7_entry : Z := 0x3e44c.

Lemma stack_malloc_7_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB h : Z) (fl : list Z) (DTV dtvbeg TCX T lo size : Z) (tb te : word),
  fs_const FSB m -> fs_hint FSB 7 m h -> fs_flags FSB 7 m fl -> flags_ok 7 fl -> (nbusy fl < 128)%nat -> 0 <= h < 2 ^ 61 ->
  fs_free_frames FSB 7 m fl -> rw_cells asegs m tpA [C8 (Z_to_bv 64 FSB)] ->
  tga_cells DTV dtvbeg m -> thread_cells TCX T m -> ttls_cells T m tb te -> m2s_cells m ->
  FSB_ok2 FSB -> 0x7fff00000000 <= lo -> FSB + kFakeStackSize <= lo ->
  0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 -> 0 < TCX -> TCX + 0xa0 <= lo -> 0 < T -> T + 4096 <= lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 224 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 size -> 0 < size <= 8192 -> size mod 8 = 0 -> ps_cells m ->
  evt asegs (sm7_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB h fl lo size m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sm7_entry) fc None m (seg_rom asegs)).
Proof.
  intros until te. intros FC HI FL OK NB HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL HB HX HXL HT HTL ST LO SPH MI Ha0 Hsz Hsz8 PS. subst a0.
  pose proof OK as (LEN & _). rewrite NF_7 in LEN.
  destruct (scan_target_exists fl 128 h LEN ltac:(lia)) as (j & SC).
  destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
  set (pos := (h + Z.of_nat j) mod 128) in *.
  assert (Hpos : 0 <= pos < 128) by (apply Z.mod_pos_bound; lia).
  destruct (FF pos ltac:(rewrite NF_7; lia) Hfree) as [[junkF FRm] [junkS SHm]].
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  rewrite shad_frame in SHm by lia. rewrite fsz_7 in FRm, SHm. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in SHm.
  unfold frame_addr, fsz in FRm, SHm.
  change (7 * 2 ^ 20) with 7340032 in FRm.
  change (7 * 2 ^ 17) with 917504 in SHm. change (8192 / 8) with 1024 in SHm. change (Z.to_nat 1024) with 1024%nat in SHm.
  replace (FSB + 36864 + 7340032 + pos * 8192) with (FSB + 7376896 + pos * 8192) in FRm by lia.
  assert (FRW : wr_at asegs m (FSB + 7376896 + pos * 8192) 8192).
  { destruct FRm as [_ W]. cbn [cells_size csize] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W. }
  pose proof (rw_cells_split_CB asegs m _ [] (Z.to_nat 8192) junkF [] [32%nat; Z.to_nat 8152; 8%nat] FRm ltac:(cbn [sum_nat]; lia)) as FRs.
  cbn [app mk_CB_cells] in FRs. clear FRm.
  lazymatch type of FRs with rw_cells _ _ ?A0 (?c1 :: ?rest) => apply (proj1 (rw_cells_app2 m A0 [c1] rest)) in FRs end. destruct FRs as [FRm FRs].
  lazymatch type of FRs with rw_cells _ _ ?A0 (?c1 :: ?rest) => apply (proj1 (rw_cells_app2 m A0 [c1] rest)) in FRs end. destruct FRs as [_ FRhi].
  lazymatch type of FRhi with rw_cells _ _ ?A0 _ => replace A0 with (FSB + 7376896 + pos * 8192 + 8184) in FRhi by (cbn [cells_size csize]; lia) end.
  set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
  clearbody F8.
  replace (SHB + F8 + 4608 + 917504 + pos * 1024) with (F8 + pos * 1024 + 2148372992) in SHm by (unfold SHB; lia).
  (* [comment removed for export] *)
  assert (PA : ps_args_ok (FSB + 7376896 + pos * 8192) size).
  { unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [split; [|split; [exact Hsz8 | lia]]|lia].
    rewrite EF8. replace (8 * F8 + 7376896 + pos * 8192) with ((F8 + 922112 + pos * 1024) * 8) by lia. apply Z.mod_mul. lia. }
  assert (SHW : wr_at asegs m (F8 + pos * 1024 + 2148372992) 1024) by (destruct SHm as [_ W]; exact W).
  assert (Hq8 : 0 <= size / 8 <= 1024) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  set (k8 := Z.to_nat (size / 8)) in *.
  pose proof (rw_cells_split_CB asegs m _ [] 1024%nat junkS [] [k8; (1024 - k8)%nat] SHm ltac:(cbn [sum_nat]; unfold k8; lia)) as SHs.
  cbn [app mk_CB_cells] in SHs. clear SHm.
  apply (rw_cells_app2 m _ [CB k8 (firstn k8 junkS)] [CB (1024 - k8) (firstn (1024 - k8) (skipn k8 junkS))]) in SHs. destruct SHs as [SHa SHb].
  cbn [cells_size csize Nat.add] in SHb. rewrite Nat.add_0_r in SHb. unfold k8 in SHb at 1. rewrite Z2Nat.id in SHb by lia.
  unfold fs_flags, fl_base, flags_off in FL. change (32768 - 2 ^ (15 - 7)) with 32512 in FL.
  replace (FSB + 4096 + 32512) with (FSB + 36608) in FL by lia.
  assert (LENM : Z.of_nat (length (map b8 fl)) = 128) by (rewrite length_map; exact LEN).
  destruct M2S as (M2a & M2b & M2c).
  destruct TGA as (AI & RL & DP & D1 & DC). destruct TC as (TS & TX). destruct TS as (KI & K & TS & T0).
  destruct DC as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  unfold fs_const, fs_hint, ttls_cells, tpA, g_real_tls_get_addr, musl_tls_get_addr_entry, g_tls_index, g_dtv_ptr, g_dtv, g_dtv1,
    dtv1_val, g_got_common_flags, g_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity,
    g_got_dtls_off, g_tls_dtls, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, sm7_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl (sm_W 7 FSB pos (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold sm_W in MU. rewrite shad_frame in MU by lia. unfold frame_addr, fsz, fl_base, flags_off in MU.
  change (7 * 2 ^ 20) with 7340032 in MU. change (64 * 2 ^ 7) with 8192 in MU. change (7 * 2 ^ 17) with 917504 in MU.
  change (8192 / 8) with 1024 in MU. change (32768 - 2 ^ (15 - 7)) with 32512 in MU. unfold SHB in MU.
  replace (FSB + 36864 + 7340032 + pos * 8192) with (FSB + 7376896 + pos * 8192) in MU by lia.
  replace (FSB + 4096 + 32512) with (FSB + 36608) in MU by lia.
  replace (2147450880 + FSB / 8 + 4608 + 917504 + pos * 1024) with (F8 + pos * 1024 + 2148372992) in MU
    by (rewrite EF8, (Z.mul_comm 8 F8), Z.div_mul by lia; lia).
  replace (FSB + 8 * 7) with (FSB + 56) in MU, HI by lia.
  carve_frame 48%nat ST.
  zidle_begin sp 48%Z MUz WMz.
  zhide.
  zhide. do 11 zstep.
  zidle_end MUz WMz.
  sp_facts.
  call (tls_get_addr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ DTV dtvbeg TCX T lo tb te).
  1: exact (conj AI (conj RL (conj DP (conj D1 (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 G8))))))))))).
  1: exact (conj (conj KI (conj K (conj TS T0))) TX).
  1: exact TT.
  all: rewrite ?Esp; try lia; try assumption.
  rewrite Esp in POST. rename POST into ST.
  clear AI RL DP D1 G1 G2 G3 G4 G5 G6 G7 G8 KI K TS T0 TX TT.
  unfold tpA. zstep. zstep. ifF.
  do 3 zstep. ifT.
  do 5 zstep. ifF.
  zhide. do 15 zstep.
  replace (Z_to_bv 64 (FSB + 36608)) with (Z_to_bv 64 (fl_base FSB 7)) by (unfold fl_base, flags_off; f_equal; cbn; lia).
  eapply (fs7_scan0 _ x13 FSB h fl j).
  1:{ unfold fs_flags, fl_base, flags_off. change (32768 - 2 ^ (15 - 7)) with 32512.
      replace (FSB + 4096 + 32512) with (FSB + 36608) by lia. exact FL. }
  all: try assumption; try lia.
  1:{ unfold fl_base, flags_off. cbn. lia. }
  intros t0' a0'.
  change ((h + Z.of_nat j) mod 128) with pos.
  replace (fl_base FSB 7) with (FSB + 36608) by (unfold fl_base, flags_off; cbn; lia).
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_store_ok asegs mm (FSB + 36608) (map b8 fl) pos (wa (FSB + 36608 + pos)) FL ltac:(lia) ltac:(f_equal; lia)) as SOK;
    pose proof (u8arr_write asegs mm (FSB + 36608) (map b8 fl) pos (b8 1) FL ltac:(lia)) as FL2 end.
  zstep. change (le1 (Z_to_bv 64 1)) with [b8 1]. clear FL. store_done.
  do 8 zstep.
  assert (SH13 : pos ≪ 13 = pos * 8192) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity). rewrite SH13.
  replace (FSB + 36864 + (7340032 + pos * 8192)) with (FSB + 7376896 + pos * 8192) by lia.
  do 3 zstep.
  zstep. zstep.
  call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 7376896 + pos * 8192)).
  1: reflexivity.
  1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
  1: exact (conj M2a (conj M2b M2c)).
  1: assumption.
  assert (ESH : shad (FSB + 7376896 + pos * 8192) = F8 + pos * 1024 + 2148372992).
  { unfold shad, SHB. rewrite EF8. replace (8 * F8 + 7376896 + pos * 8192) with ((F8 + 922112 + pos * 1024) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  clear TLS M2a M2b M2c.
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ps_cells_framed m mm _ PS MU WM ltac:(unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia)) as PSm end.
  rewrite <- ESH in SHa.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 7376896 + pos * 8192) size 0 lo (firstn k8 junkS)).
  1: exact PA.
  1: lia.
  1: right; lia.
  1: exact SHa.
  1: exact PSm.
  all: rewrite ?Esp; try lia; try assumption; try (unfold kHighShadowEnd; lia).
  rewrite Esp in POST. rename POST into ST.
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  assert (EFR : FSB + 7376896 + pos * 8192 = frame_addr FSB 7 pos) by (unfold frame_addr, fsz; cbn; lia).
  rewrite EFR.
  lazymatch type of MU with munch _ _ ?mm => rename mm into mF end.
  apply evt_done. unfold sm7_post. change ((h + Z.of_nat j) mod 128) with pos.
  do 15 eexists. exists mF.
  split; [reflexivity|]. change ((h + Z.of_nat j) mod 128) with pos.
  assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (MU' : munch (sm_W 7 FSB pos (bv_unsigned sp)) m mF).
  { replace (sm_W 7 FSB pos (bv_unsigned sp)) with
      [(FSB + 56, FSB + 56 + 8); (FSB + 36608 + pos, FSB + 36608 + pos + 1);
       (FSB + 7376896 + pos * 8192, FSB + 7376896 + pos * 8192 + 8192);
       (F8 + pos * 1024 + 2148372992, F8 + pos * 1024 + 2148372992 + 1024);
       (bv_unsigned sp - 224, bv_unsigned sp)]; [exact MU|].
    unfold sm_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
    change (7 * 2 ^ 20) with 7340032. change (64 * 2 ^ 7) with 8192. change (7 * 2 ^ 17) with 917504.
    change (8192 / 8) with 1024. change (32768 - 2 ^ (15 - 7)) with 32512.
    repeat (f_equal; try lia). }
  split; [exact MU'|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [change (Z.to_nat 128) with 128%nat in Hj; exact Hj|]. split; [exact Hfree|].
  split; [exact HI|]. split; [exact FC|].
  split.
  { unfold fs_flags. rewrite map_b8_upd. replace (fl_base FSB 7) with (FSB + 36608) by (unfold fl_base, flags_off; cbn; lia).
    exact FL2. }
  split; [rewrite <- EFR; exact FRW|].
  split.
  { rewrite <- EFR. replace (fl_base FSB 7 + pos) with (FSB + 36608 + pos) by (unfold fl_base, flags_off; cbn; lia). exact FRhi. }
  split; [rewrite <- EFR, ESH; exact SHW|].
  split; [rewrite <- EFR; assumption|].
  apply (fs_free_frames_transport FSB 7 m mF _ _ (fs_free_frames_take FSB 7 m fl (Z.to_nat pos) FF) MU' WM).
  intros p Hp Hf. pose proof (nth_upd_free_other _ _ _ Hf) as Hne. rewrite NF_7 in Hp.
  assert (Hne' : p <> pos) by (intro E; apply Hne; rewrite E; reflexivity).
  unfold sm_W. rewrite !shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
  change (7 * 2 ^ 20) with 7340032. change (64 * 2 ^ 7) with 8192. change (7 * 2 ^ 17) with 917504.
  change (8192 / 8) with 1024. change (32768 - 2 ^ (15 - 7)) with 32512.
  cbn [disjoint_from]. split; repeat split; lia.
Qed.
