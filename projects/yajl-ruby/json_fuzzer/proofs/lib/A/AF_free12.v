(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_qkit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Ltac phyps := match goal with |- _ => repeat match goal with H : ?t |- _ => idtac H ":" t; fail end end.
Ltac djs := cbn [disjoint_from length cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Pos.add]; rewrite ?length_le8, ?length_le4; repeat split; try exact I; lia.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac slia ::= first [ exact I | dlia | split; [dlia | exact I] ].
Local Ltac flia ::= first [ assumption | lia ].
Local Definition carry_skip (P : Prop) := P.
Local Ltac skipH H := lazymatch type of H with ?TS => change TS with (carry_skip TS) in H end.

Local Ltac dlia1 := dlia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac incl_leaves xq Hq :=
  repeat match type of Hq with _ /\ _ => let Q := fresh "Q" in destruct Hq as [Q Hq] end;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  let C := fresh "C" in intros C;
  first [ match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end
        | match goal with D : _ \/ _ |- _ => destruct D as [XD|XD]; match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end end ].
(* [comment removed for export] *)
Local Ltac solve_covers ::=
  let lo := fresh "lo" in let hi := fresh "hi" in let Hin := fresh "Hin" in
  intros lo hi Hin; cbn [In app] in Hin;
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe] |]
  | _ = _ => injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe]
  | False => contradiction
  end.
Local Ltac carry_rw H MU WM ::= eapply rw_cells_transport in H; [| exact MU| exact WM| cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]].
Local Ltac carry_all mc m' MUc WMc ::=
  repeat match goal with
  | H : rw_cells asegs mc _ _ |- _ => first [ carry_rw H MUc WMc | skipH H ]
  | H : bytes_at asegs mc _ _ |- _ => first [ eapply bytes_at_transport in H; [| exact MUc| cbn [disjoint_from length]; rewrite ?repeat_length, ?length_le8, ?length_le4; lia] | skipH H ]
  | H : stk asegs mc _ _ |- _ => first [ eapply stk_transport in H; [| exact MUc| exact WMc| intros; left; cbn; lia] | skipH H ]
  | H : wr_at asegs mc _ _ |- _ => first [ eapply wr_at_transport in H; [| exact WMc] | skipH H ]
  | H : u8arr asegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; rewrite ?repeat_length; lia] | skipH H ]
  | H : u64arr asegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : u32arr asegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : munch ?W ?ma mc |- _ =>
      let H2 := fresh in
      first [ assert (H2 : munch W ma m')
          by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc];
              first [ sub_fp_fast | let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; decompose [and] Hq; clear Hq; repeat match goal with |- _ /\ _ => split end; try exact I; match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end ]]);
        clear H; rename H2 into H | skipH H ]
  | H : wmono asegs ?ma mc |- _ =>
      let H2 := fresh in
      assert (H2 : wmono asegs ma m') by (eapply wmono_trans; [exact H| exact WMc]);
      clear H; rename H2 into H
  end;
  repeat match goal with H : carry_skip _ |- _ => unfold carry_skip in H end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma drl_class_ok : forall SB b, SB <= b -> b < SB + 2^37 ->
  Z.shiftr (Z.shiftl (b - SB) 27 mod 18446744073709551616) 59 = class_of_addr SB b.
Proof.
  intros SB b H1 H2. unfold class_of_addr, kRegionSize, kNumClasses.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small _ 18446744073709551616) by (split; [lia|]; change 18446744073709551616 with (2^37 * 2^27); nia).
  rewrite (Z.mod_small (_ / _) 32) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  replace ((b - SB) * 2^27 / 2^59) with ((b - SB) * 2^27 / 2^27 / 2^32) by (rewrite Z.div_div by lia; f_equal; lia).
  rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_app_split12 : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. aceil.
  intros segs m A cs1 cs2 [[WF B] W]. apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in W. destruct W as (Wa & Wb & Wr).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Wr. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Wr. lia.
Qed.

Lemma bhd_or_nonneg' : forall rest, (rest = [] \/ 0 < bhd rest < 2^64) -> 0 <= bhd rest < 2^64.
Proof. intros rest [->|H]; [cbn; lia| lia]. Qed.

Section DRL.
Variable P : acc -> Prop.
Variables (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (usp lo CP SB RI : Z) (cachep stackp : word).
(* [comment removed for export] *)
Variables (ora os0 os1 os2 os3 os4 os5 os6 os7 os8 os9 : word).
Notation INST := 0xaa518.

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 112.
Hypothesis SPA : usp mod 16 = 0.
(* [comment removed for export] *)
Hypothesis HCP : usp <= CP /\ CP + 32 <= 2^47.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PCP : forall a k, CP <= a -> a + Z.of_nat k <= CP + 32 -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition drl_fr_lo (m : mem) (j8 : list byte) : Prop := rw_cells asegs m (usp + -112) [CB 8 j8].
Definition drl_fr_cb (m : mem) : Prop := rw_cells asegs m (usp + -104) [C8 cachep; C8 stackp].
Definition drl_fr_hi (m : mem) : Prop :=
  rw_cells asegs m (usp + -88) [C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ora].
(* [comment removed for export] *)
Definition tmpc (m : mem) (l : list batch) : Prop :=
  rw_cells asegs m CP [C8 (Z_to_bv 64 (blen l)); C8 (Z_to_bv 64 (bhd l)); C8 (Z_to_bv 64 (blast l)); C8 (Z_to_bv 64 (qbytes l))].

(* [comment removed for export] *)
Definition drl_head (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word) (cnt : Z) (m : mem) : machine_state :=
  MS (mkR xra (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 CP) (Z_to_bv 64 INST) (Z_to_bv 64 cnt) xa1 xa2 xa3 xa4 xa5 xa6 xa7
          (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) xs4 (Z_to_bv 64 (2^37)) xs6 xs7 xs8 xs9 s10 s11 xt3 xt4 xt5 xt6)
     F (Z_to_bv 64 0x34d98) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition drl_call (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (b bc i : Z) (it : word) (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x34de4) (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 CP) (Z_to_bv 64 INST) (Z_to_bv 64 (usp + -104)) it xa2 xa3 xa4 xa5 xa6 xa7
          (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 bc) (Z_to_bv 64 (b + 152 + 8 * i)) (Z_to_bv 64 (bc + 16)) (Z_to_bv 64 (16 + i))
          s10 s11 xt3 xt4 xt5 xt6)
     F (Z_to_bv 64 0x34e58) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition drl_bd (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word) (b : Z) (m : mem) : machine_state :=
  MS (mkR xra (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 CP) (Z_to_bv 64 INST) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
          (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) xs6 xs7 xs8 xs9 s10 s11 xt3 xt4 xt5 xt6)
     F (Z_to_bv 64 0x34df0) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition drl_latch (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word) (m : mem) : machine_state :=
  MS (mkR xra (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 CP) (Z_to_bv 64 INST) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
          (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) xs4 (Z_to_bv 64 (2^37)) xs6 xs7 xs8 xs9 s10 s11 xt3 xt4 xt5 xt6)
     F (Z_to_bv 64 0x34e1c) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition drl_ret (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (m : mem) : machine_state :=
  MS (mkR ora (Z_to_bv 64 usp) gp tp xt0 xt1 xt2 os0 os1 (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7 os2 os3 os4 os5 os6 os7 os8 os9 s10 s11 xt3 xt4 xt5 xt6)
     F (ret_pc ora) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Lemma drl_epi : forall m (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word) (j8 : list byte),
  mem_inv asegs m -> stk asegs m lo (usp + -112) -> drl_fr_lo m j8 -> drl_fr_cb m -> drl_fr_hi m ->
  (stk asegs m lo usp -> evtA asegs P Q (drl_ret xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m)) ->
  evtA asegs P Q (MS (mkR xra (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x34e24) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until j8. intros MI SK FLO FCB FHI CONT.
  pose proof LOC as LOC0. aceil. unfold drl_fr_lo in FLO. unfold drl_fr_cb in FCB. unfold drl_fr_hi in FHI.
  assert (MU : munch [] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  do 11 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  release_frame FLO SK (usp + -104). release_frame FCB SK (usp + -88). release_frame FHI SK usp.
  zstepA. (* [comment removed for export] *)
  apply CONT. exact SK.
Qed.

(* [comment removed for export] *)
Lemma drl_entry : forall m l (xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  mem_inv asegs m -> stk asegs m lo usp -> tmpc m l -> blen l < 2^40 ->
  (* [comment removed for export] *)
  (forall m' , l = [] -> mem_inv asegs m' -> stk asegs m' lo usp -> munch [(usp + -112, usp)] m m' -> wmono asegs m m' -> tmpc m' l ->
     evtA asegs P Q (drl_ret xt0 xt1 xt2 (Z_to_bv 64 CP) cachep stackp xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m')) ->
  (* [comment removed for export] *)
  (forall m' j8, l <> [] -> mem_inv asegs m' -> stk asegs m' lo (usp + -112) -> munch [(usp + -112, usp)] m m' -> wmono asegs m m' -> tmpc m' l ->
     drl_fr_lo m' j8 -> drl_fr_cb m' -> drl_fr_hi m' ->
     evtA asegs P Q (drl_head ora xt0 xt1 xt2 (Z_to_bv 64 0xa9d64) cachep stackp xa4 xa5 xa6 xa7 os4 os6 os7 os8 os9 xt3 xt4 xt5 xt6 (blen l) m')) ->
  evtA asegs P Q (MS (mkR ora (Z_to_bv 64 usp) gp tp xt0 xt1 xt2 os0 os1 xa0 (Z_to_bv 64 CP) cachep stackp xa4 xa5 xa6 xa7 os2 os3 os4 os5 os6 os7 os8 os9 s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x34d20) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until xt6. intros MI SK TC LEN CNIL CCONS.
  pose proof LOC as LOC0. aceil. unfold tmpc in TC.
  assert (LEN0 : 0 <= blen l) by (clear; lia).
  assert (MU : munch [(usp + -112, usp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 112%nat SK.
  do 12 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  (* [comment removed for export] *)
  lazymatch goal with FRX : rw_cells asegs m1 (usp + -112) _ |- _ =>
    pose proof (rw_cells_app_split12 asegs m1 (usp + -112) [CB 8 _] _ FRX) as [FLO FR2];
    pose proof (rw_cells_app_split12 asegs m1 _ [C8 cachep; C8 stackp] _ FR2) as [FCB FHI]; clear FR2 FRX end.
  cbn [cells_size csize Nat.add Nat.mul] in FCB, FHI.
  lazymatch type of FCB with rw_cells _ _ ?x _ => replace x with (usp + -104) in FCB by (clear; lia) end.
  lazymatch type of FHI with rw_cells _ _ ?x _ => replace x with (usp + -88) in FHI by (clear; lia) end.
  zstepA. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    assert (LN : l = []) by (destruct l; [reflexivity| exfalso; revert K0; rewrite ?unsigned_lit by lia; cbn [length]; lia]).
    replace (Z_to_bv 64 (blen l)) with (Z_to_bv 64 0) by (rewrite LN; reflexivity).
    eapply drl_epi; [exact MI| exact SK| exact FLO| exact FCB| exact FHI|].
    intros SK'. eapply CNIL; [exact LN| exact MI| exact SK'| exact MU| exact WM| exact TC].
  - assert (LNN : l <> []) by (intros E; apply K0; rewrite E; reflexivity).
    do 8 zstepA. (* [comment removed for export] *)
    eapply CCONS; [exact LNN| exact MI| exact SK| exact MU| exact WM| exact TC| exact FLO| exact FCB| exact FHI].
Qed.

(* [comment removed for export] *)
Lemma drl_deq : forall m l (b : batch) (rest : list batch) (ws : list word) (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word),
  l = b :: rest -> (rest = [] \/ 0 < bhd rest < 2^64) -> blen l < 2^40 -> 0 <= qbytes rest -> 0 <= b_size b -> qbytes l < 2^63 -> (bcnt b <= 1021)%Z ->
  0x10007fff8000 <= b_addr b -> b_addr b + 8192 <= lo ->
  mem_inv asegs m -> stk asegs m lo (usp + -112) -> tmpc m l ->
  rw_cells asegs m (b_addr b) [C8 (Z_to_bv 64 (bhd rest)); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (bcnt b))] ->
  u64arr asegs m (b_addr b + 24) ws -> length ws = 1021%nat ->
  (forall a k, b_addr b <= a -> a + Z.of_nat k <= b_addr b + 8192 -> P (Z_to_bv 64 a, k)) ->
  (* [comment removed for export] *)
  (forall m', b_items b = [] -> mem_inv asegs m' -> stk asegs m' lo (usp + -112) -> munch [(CP, CP + 32)] m m' -> wmono asegs m m' -> tmpc m' rest ->
     rw_cells asegs m' (b_addr b) [C8 (Z_to_bv 64 (bhd rest)); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (bcnt b))] -> u64arr asegs m' (b_addr b + 24) ws ->
     evtA asegs P Q (drl_bd xra xt0 xt1 xt2 (Z_to_bv 64 (b_size b)) (Z_to_bv 64 (qbytes rest)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 0) xs7 xs8 xs9 xt3 xt4 xt5 xt6 (b_addr b) m')) ->
  (* [comment removed for export] *)
  (forall m' it0, nth_error ws 0 = Some it0 -> (0 < bcnt b)%Z -> mem_inv asegs m' -> stk asegs m' lo (usp + -112) -> munch [(CP, CP + 32)] m m' -> wmono asegs m m' -> tmpc m' rest ->
     rw_cells asegs m' (b_addr b) [C8 (Z_to_bv 64 (bhd rest)); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (bcnt b))] -> u64arr asegs m' (b_addr b + 24) ws ->
     evtA asegs P Q (drl_call xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (b_addr b) (bcnt b) 0 it0 m')) ->
  evtA asegs P Q (drl_head xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 (blen l) m).
Proof. aceil.
  intros until xt6. intros L HR LEN Q0 S0 QL BC HB1 HB2 MI SK TC HDR ITS LW PB CNIL CCONS.
  pose proof LOC as LOC0. aceil. unfold tmpc in TC. unfold drl_head.
  assert (LEN0 : 0 <= blen rest) by (clear; lia).
  assert (BC0 : (0 <= bcnt b)%Z) by (clear; lia).
  assert (EL : blen l = blen rest + 1) by (rewrite L; cbn [length]; lia).
  assert (EH : bhd l = b_addr b) by (rewrite L; reflexivity).
  assert (EQ : qbytes l = b_size b + qbytes rest) by (rewrite L; reflexivity).
  rewrite EL in TC |- *. rewrite EH, EQ in TC.
  pose proof (bhd_or_nonneg' rest HR) as HR0.
  assert (MU : munch [(CP, CP + 32)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  set (MID := fun ms1 => exists m2, ms1 = MS (mkR xra (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 CP) (Z_to_bv 64 INST) (Z_to_bv 64 (blen rest + 1)) (Z_to_bv 64 (bhd rest)) xa2 xa3 xa4 xa5 xa6 xa7
          (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 (b_addr b)) (Z_to_bv 64 (2^37)) xs6 xs7 xs8 xs9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x34dac) fc None m2 (seg_rom asegs)
       /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + -112) /\ munch [(CP, CP + 32)] m m2 /\ wmono asegs m m2
       /\ rw_cells asegs m2 CP [C8 (Z_to_bv 64 (blen rest + 1)); C8 (Z_to_bv 64 (bhd rest)); C8 (Z_to_bv 64 (blast rest)); C8 (Z_to_bv 64 (b_size b + qbytes rest))]
       /\ rw_cells asegs m2 (b_addr b) [C8 (Z_to_bv 64 (bhd rest)); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (bcnt b))] /\ u64arr asegs m2 (b_addr b + 24) ws).
  eapply (evtA_cut asegs P MID).
  { zstepA. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (RN : rest <> []) by (intros E; apply K1; rewrite E; reflexivity).
      apply evtA_done. eexists. split; [reflexivity|].
      assert (EB : blast l = blast rest) by (rewrite L; apply blast_cons; exact RN). rewrite EB in TC.
      repeat match goal with |- _ /\ _ => split end; eassumption.
    - (* [comment removed for export] *)
      assert (RE : rest = []) by (destruct HR as [RE|POS]; [exact RE| exfalso; revert K1 POS; rewrite ?unsigned_lit by lia; intros K1 POS; lia]).
      zstepA. (* [comment removed for export] *)
      apply evtA_done. eexists. split; [reflexivity|].
      replace (blast rest) with 0 by (rewrite RE; reflexivity).
      repeat match goal with |- _ /\ _ => split end; eassumption. }
  clear MI SK TC HDR ITS MU WM m1.
  intros ms1 (m2 & -> & MI & SK & MU & WM & TC & HDR & ITS).
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  try replace (b_size b + qbytes rest - b_size b) with (qbytes rest) by (clear; lia).
  zstepA. (* [comment removed for export] *)
  lazymatch goal with TC2 : rw_cells asegs ?mc CP _ |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (TC' : tmpc mc rest);
    [ unfold tmpc;
      lazymatch type of TC2 with rw_cells _ _ _ ?cs2 => lazymatch goal with |- rw_cells _ _ _ ?cs => replace cs with cs2; [exact TC2|] end end;
      change 18446744073709551616 with (2^64); rewrite ?Z_to_bv_mod64;
      repeat first [ reflexivity | apply (f_equal2 cons) | apply (f_equal C8) | apply (f_equal (Z_to_bv 64)); clear; lia ]
    | clear TC2 ] end.
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    assert (BN : b_items b = []) by (destruct (b_items b); [reflexivity| exfalso; revert K2; rewrite ?unsigned_lit by lia; cbn [length]; lia]).
    replace (Z_to_bv 64 (bcnt b)) with (Z_to_bv 64 0) by (rewrite BN; reflexivity).
    eapply CNIL; [exact BN| exact MI| exact SK| exact MU| exact WM| exact TC'| exact HDR| exact ITS].
  - assert (BP : (0 < bcnt b)%Z) by (destruct (b_items b) eqn:EB; [exfalso; apply K2; reflexivity| cbn [length]; lia]).
    destruct (nth_error ws 0) as [it0|] eqn:NTH0. 2:{ exfalso. apply nth_error_None in NTH0. rewrite LW in NTH0. clear -NTH0. cbn in NTH0. lia. }
    lazymatch type of ITS with u64arr _ ?mc _ _ => pose proof (u64arr_read asegs mc (b_addr b + 24) ws 0 it0 (Z_to_bv 64 (b_addr b + 152 + -128)) ITS NTH0 ltac:(clear; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD end.
    zstepA. zstepA. zstepA. (* [comment removed for export] *)
    zstepA. clear RD. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    unfold drl_call in CCONS.
    replace (b_addr b + 152 + 8 * 0) with (b_addr b + 152) in CCONS by (clear; lia).
    eapply CCONS; [reflexivity| exact BP| exact MI| exact SK| exact MU| exact WM| exact TC'| exact HDR| exact ITS].
Qed.

(* [comment removed for export] *)
Lemma drl_item_next : forall m (b bc i : Z) (ws : list word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  0 <= i -> i + 1 <= bc -> bc <= 1021 -> 0x10007fff8000 <= b -> b + 8192 <= lo ->
  mem_inv asegs m -> stk asegs m lo (usp + -112) -> u64arr asegs m (b + 24) ws -> length ws = 1021%nat ->
  (forall a k, b <= a -> a + Z.of_nat k <= b + 8192 -> P (Z_to_bv 64 a, k)) ->
  (forall it', i + 1 < bc -> nth_error ws (Z.to_nat (i + 1)) = Some it' ->
     evtA asegs P Q (drl_call xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 b bc (i + 1) it' m)) ->
  (i + 1 = bc ->
     evtA asegs P Q (drl_bd xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 bc) (Z_to_bv 64 (b + 152 + 8 * (i + 1))) (Z_to_bv 64 (bc + 16)) (Z_to_bv 64 (16 + (i + 1))) xt3 xt4 xt5 xt6 b m)) ->
  evtA asegs P Q (MS (mkR xra (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 CP) (Z_to_bv 64 INST) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                          (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 bc) (Z_to_bv 64 (b + 152 + 8 * i)) (Z_to_bv 64 (bc + 16)) (Z_to_bv 64 (16 + i))
                          s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x34de4) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until xt6. intros I0 I1 BC HB1 HB2 MI SK ITS LW PB CMORE CLAST.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA. zstepA. (* [comment removed for export] *)
  replace (16 + i + 1) with (16 + (i + 1)) by (clear; lia).
  replace (b + 152 + 8 * i + 8) with (b + 152 + 8 * (i + 1)) by (clear; lia).
  zstepA. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    assert (LT : i + 1 < bc) by (revert K1; rewrite ?unsigned_lit by lia; intros K1; lia).
    destruct (nth_error ws (Z.to_nat (i + 1))) as [it'|] eqn:NTH.
    2:{ exfalso. apply nth_error_None in NTH. rewrite LW in NTH. clear -NTH LT BC I0. cbn in NTH. lia. }
    pose proof (u64arr_read asegs m (b + 24) ws (i + 1) it' (Z_to_bv 64 (b + 152 + 8 * (i + 1) + -128)) ITS NTH ltac:(clear -I0; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    zstepA. clear RD. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    eapply CMORE; [exact LT| reflexivity].
  - assert (EQ : i + 1 = bc) by (revert K1; rewrite ?unsigned_lit by lia; clear -I0 I1 BC; intros K1; lia).
    eapply CLAST. exact EQ.
Qed.

(* [comment removed for export] *)
Lemma drl_bdealloc : forall m (b : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word),
  SB <= b -> b + 8192 <= SB + kSpaceSize ->
  mem_inv asegs m -> stk asegs m lo (usp + -112) ->
  rw_cells asegs m 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  drl_fr_cb m ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x34e1c) (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 CP) (Z_to_bv 64 INST) cachep (Z_to_bv 64 INST) (Z_to_bv 64 (class_of_addr SB b)) (Z_to_bv 64 b) xa4 xa5 xa6 xa7
                          (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) xs6 xs7 xs8 xs9 s10 s11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x3525c) fc None m (seg_rom asegs)) ->
  evtA asegs P Q (drl_bd xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 b m).
Proof. aceil.
  intros until xt6. intros HB1 HB2 MI SK INS FCB CONT.
  pose proof LOC as LOC0. aceil. pose proof HSB as HSB0. unfold kSpaceSize in HSB0, HB2. unfold drl_fr_cb in FCB. unfold drl_bd.
  assert (MU : munch [] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. clear -CEILB HB1 HB2 HSB0. intros K1. lia. } clear K1.
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit by lia. clear -CEILB HB1 HB2 HSB0. intros K2. lia. } clear K2.
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  rewrite (drl_class_ok SB b) by (clear -HB1 HB2; lia).
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  exact CONT.
Qed.

(* [comment removed for export] *)
Lemma drl_latch_step : forall m l (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word) (j8 : list byte),
  blen l < 2^40 ->
  mem_inv asegs m -> stk asegs m lo (usp + -112) -> tmpc m l -> drl_fr_lo m j8 -> drl_fr_cb m -> drl_fr_hi m ->
  (l <> [] -> evtA asegs P Q (drl_head xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 (blen l) m)) ->
  (l = [] -> stk asegs m lo usp -> evtA asegs P Q (drl_ret xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m)) ->
  evtA asegs P Q (drl_latch xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 m).
Proof. aceil.
  intros until j8. intros LEN MI SK TC FLO FCB FHI CMORE CDONE.
  pose proof LOC as LOC0. aceil. pose proof TC as TC0. unfold tmpc in TC. unfold drl_latch.
  assert (LEN0 : 0 <= blen l) by (clear; lia).
  assert (MU : munch [] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1.
  - assert (LNN : l <> []) by (intros E; apply K1; rewrite E; reflexivity).
    apply CMORE. exact LNN.
  - assert (LN : l = []) by (destruct l; [reflexivity| exfalso; revert K1; rewrite ?unsigned_lit by lia; cbn [length]; lia]).
    replace (Z_to_bv 64 (blen l)) with (Z_to_bv 64 0) by (rewrite LN; reflexivity).
    eapply drl_epi; [exact MI| exact SK| exact FLO| exact FCB| exact FHI|].
    apply CDONE. exact LN.
Qed.
End DRL.
End RC__1.
