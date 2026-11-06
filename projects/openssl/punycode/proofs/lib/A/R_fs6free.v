(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA Arr.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow R_small R_m2s R_thread R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr R_arrkit R_fs6.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
(* [comment removed for export] *)
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | clear_big; repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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
Local Ltac zidle_na H A a := tryif constr_eq A a then idtac else zidle1 H.
Local Ltac zidle_begin_at a n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(a, a + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_na H A a
    | H : ro_cells segs m ?A _ |- _ => zidle_na H A a
    | H : u8arr segs m ?A _ |- _ => zidle_na H A a
    | H : u32arr segs m ?A _ |- _ => zidle_na H A a
    | H : u64arr segs m ?A _ |- _ => zidle_na H A a
    | H : bytes_at segs m ?A _ |- _ => zidle_na H A a
    | H : u8ro segs m ?A _ |- _ => zidle_na H A a
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Lemma fill8_f6 : fill8_stmt 0x1a70b8.
Proof.
  unfold fill8_stmt.
  induction n as [|n IH]; intros i A v tl m0 m; intros until Q; intros N1 I0 IN LT A0 AHI ARR MI MU WM K; [lia|].
  destruct tl as [|t tl']; [cbn in LT; lia|]. cbn [length] in LT.
  pose proof (u64arr_bound asegs m A _ ARR) as BND.
  rewrite length_app, repeat_length in BND. cbn [length] in BND.
  pose proof (u64arr_store_ok asegs m A _ i (wa (A + 8 * i)) ARR
                ltac:(rewrite length_app, repeat_length; cbn [length]; lia) eq_refl) as SOK.
  pose proof (u64arr_write asegs m A _ i v ARR ltac:(rewrite length_app, repeat_length; cbn [length]; lia)) as ARR1.
  zstep. clear ARR. store_done.
  rewrite <- (repeat_length v (Z.to_nat i)) in ARR1 at 2. rewrite upd_app_len, repeat_snoc_app in ARR1.
  zstep. zstep.
  destruct n as [|n'].
  - ifF. destruct tl' as [|? ?]; [|cbn in LT; lia]. rewrite app_nil_r in ARR1.
    replace (S (Z.to_nat i)) with 64%nat in ARR1 by lia.
    replace (A + 8 * i + 8) with (A + 512) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => apply (K mm ARR1); assumption end.
  - ifT.
    replace (A + 8 * i + 8) with (A + 8 * (i + 1)) by lia.
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in ARR1 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH (i + 1) A v tl' m0 mm); try eassumption; try lia end.
Qed.

(* [comment removed for export] *)
Definition F5W : word := Z_to_bv 64 0xf5f5f5f5f5f5f5f5.

(* [comment removed for export] *)
Definition sf_W (FSB pos usp : Z) : list (Z * Z) :=
  [(fl_base FSB 6 + pos, fl_base FSB 6 + pos + 1);
   (shad (frame_addr FSB 6 pos), shad (frame_addr FSB 6 pos) + 512);
   (usp - 16, usp)].

Definition sf6_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB pos : Z) (fl : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sf_W FSB pos (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ fs_flags FSB 6 m' (upd fl (Z.to_nat pos) 0)
    /\ u64arr asegs m' (shad (frame_addr FSB 6 pos)) (repeat F5W 64).

Definition sf6_entry : Z := 0x1a708c.

Lemma stack_free_6_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB pos : Z) (fl : list Z) (lo : Z) (junkS : list byte),
  a0 = Z_to_bv 64 (frame_addr FSB 6 pos) -> 0 <= pos < 256 ->
  fs_flags FSB 6 m fl -> flags_ok 6 fl ->
  rw_cells asegs m (frame_addr FSB 6 pos + 4088) [C8 (Z_to_bv 64 (fl_base FSB 6 + pos))] ->
  rw_cells asegs m (shad (frame_addr FSB 6 pos)) [CB 512 junkS] ->
  m2s_cells m -> FSB_ok2 FSB -> 0x10007fff8000 <= lo -> FSB + kFakeStackSize <= lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (sf6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB pos fl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sf6_entry) fc None m (seg_rom asegs)).
Proof.
  intros until junkS. intros -> Hpos FL OK FLP SHm M2S FSOK HLO FSL ST LO SPH MI.
  pose proof OK as (LEN & _). rewrite NF_6 in LEN.
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  rewrite shad_frame in SHm by lia.
  unfold frame_addr, fsz in FLP, SHm.
  change (6 * 2 ^ 20) with 6291456 in FLP. change (64 * 2 ^ 6) with 4096 in FLP, SHm.
  change (6 * 2 ^ 17) with 786432 in SHm. change (4096 / 8) with 512 in SHm.
  replace (FSB + 36864 + 6291456 + pos * 4096 + 4088) with (FSB + 6328320 + pos * 4096 + 4088) in FLP by lia.
  set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
  clearbody F8.
  replace (SHB + F8 + 4608 + 786432 + pos * 512) with (F8 + pos * 512 + 2148241920) in SHm by (unfold SHB; lia).
  unfold fs_flags, fl_base, flags_off in FL, FLP. change (32768 - 2 ^ (15 - 6)) with 32256 in FL, FLP.
  replace (FSB + 4096 + 32256) with (FSB + 36352) in FL, FLP by lia.
  assert (LENM : Z.of_nat (length (map b8 fl)) = 256) by (rewrite length_map; exact LEN).
  destruct M2S as (M2a & M2b & M2c).
  unfold sf6_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl (sf_W FSB pos (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold sf_W in MU. rewrite shad_frame in MU by lia. unfold frame_addr, fsz, fl_base, flags_off in MU.
  change (6 * 2 ^ 20) with 6291456 in MU. change (64 * 2 ^ 6) with 4096 in MU. change (6 * 2 ^ 17) with 786432 in MU.
  change (4096 / 8) with 512 in MU. change (32768 - 2 ^ (15 - 6)) with 32256 in MU. unfold SHB in MU.
  replace (FSB + 4096 + 32256) with (FSB + 36352) in MU by lia.
  replace (2147450880 + FSB / 8 + 4608 + 786432 + pos * 512) with (F8 + pos * 512 + 2148241920) in MU
    by (rewrite EF8, (Z.mul_comm 8 F8), Z.div_mul by lia; lia).
  unfold frame_addr, fsz. change (6 * 2 ^ 20) with 6291456. change (64 * 2 ^ 6) with 4096.
  replace (FSB + 36864 + 6291456 + pos * 4096) with (FSB + 6328320 + pos * 4096) by lia.
  carve_frame 16%nat ST.
  zhide.
  do 3 zstep.
  sp_facts.
  do 3 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_store_ok asegs mm (FSB + 36352) (map b8 fl) pos (wa (FSB + 36352 + pos)) FL ltac:(lia) ltac:(f_equal; lia)) as SOK;
    pose proof (u8arr_write asegs mm (FSB + 36352) (map b8 fl) pos (b8 0) FL ltac:(lia)) as FL2 end.
  zstep. change (le1 (Z_to_bv 64 0)) with [b8 0]. clear FL. store_done.
  zstep.
  call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 6328320 + pos * 4096)).
  1: reflexivity.
  1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
  1: exact (conj M2a (conj M2b M2c)).
  1: assumption.
  assert (ESH : shad (FSB + 6328320 + pos * 4096) = F8 + pos * 512 + 2148241920).
  { unfold shad, SHB. rewrite EF8. replace (8 * F8 + 6328320 + pos * 4096) with ((F8 + 791040 + pos * 512) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  rewrite ESH. clear M2a M2b M2c.
  do 3 zstep.
  destruct (u64arr_of_CB asegs _ _ 64%nat _ _ SHm eq_refl) as (ws & LWS & ARR). clear SHm.
  replace (F8 + pos * 512 + 2148242432) with (F8 + pos * 512 + 2148241920 + 512) by lia.
  set (A := F8 + pos * 512 + 2148241920) in *.
  assert (HA0 : 0 <= A) by (unfold A; lia).
  assert (HA1 : A + 512 < 2 ^ 64) by (unfold A; lia).
  replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 8 * 0)) by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply (fill8_f6 64%nat 0 A (Z_to_bv 64 17723342345328784885) ws mm mm);
      [lia | lia | lia | exact LWS | exact HA0 | exact HA1 | exact ARR | assumption | apply munch_refl | apply wmono_refl | ] end.
  intros m' ARR' MI' MUf WMf. clear ARR.
  lazymatch type of MUf with munch _ ?m0 _ => transport_after_call asegs m0 m' MUf WMf end.
  clear MUf WMf.
  do 3 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. unfold sf6_post.
  do 15 eexists. exists m'.
  split; [reflexivity|].
  assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (ESHF : shad (frame_addr FSB 6 pos) = A).
  { rewrite shad_frame by lia. rewrite EQ8. unfold fsz, SHB, A. change (6 * 2 ^ 17) with 786432. change (64 * 2 ^ 6 / 8) with 512. lia. }
  assert (MU' : munch (sf_W FSB pos (bv_unsigned sp)) m m').
  { replace (sf_W FSB pos (bv_unsigned sp)) with
      [(FSB + 36352 + pos, FSB + 36352 + pos + 1); (A, A + 512); (bv_unsigned sp - 16, bv_unsigned sp)]; [exact MU|].
    unfold sf_W. rewrite ESHF. unfold fl_base, flags_off. change (32768 - 2 ^ (15 - 6)) with 32256.
    repeat (f_equal; try lia). }
  split; [exact MU'|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST|].
  split.
  { unfold fs_flags. rewrite map_b8_upd. replace (fl_base FSB 6) with (FSB + 36352) by (unfold fl_base, flags_off; cbn; lia).
    exact FL2. }
  rewrite ESHF. exact ARR'.
Qed.

(* [comment removed for export] *)
Lemma bytes_eq_unsigned : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; destruct l2 as [|b l2]; cbn [map]; intros H; try discriminate; [reflexivity|].
  inversion H. f_equal; [apply bv_eq; assumption | apply IH; assumption].
Qed.

Lemma f5_bytes : u64s (repeat F5W 64) = repeat (Z_to_bv 8 0xf5) 512.
Proof. apply bytes_eq_unsigned. vm_compute. reflexivity. Qed.

Lemma sf6_shadow_bytes : forall (m : mem) A, u64arr asegs m A (repeat F5W 64) -> rw_cells asegs m A [CB 512 (repeat (Z_to_bv 8 0xf5) 512)].
Proof.
  intros m A H. pose proof (u64arr_as_CB asegs m A _ H) as H1. rewrite f5_bytes in H1. rewrite repeat_length in H1. exact H1.
Qed.
