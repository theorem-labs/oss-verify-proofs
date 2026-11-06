(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtS4t2 ARtSoqz AMTac ARt2_lib ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73 ARt_png ARt_fpo ANodeA7 ANodeA6 ANodl61 AFreeH AFreeH0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zmod := first [ assumption | reflexivity
                   | match goal with
                     | |- (?k * ?x) mod ?n = 0 =>
                         apply Znumtheory.Zdivide_mod; apply Z.divide_mul_l; let q := eval compute in (Z.div k n) in exists q; reflexivity
                     | |- (?x * ?k) mod ?n = 0 =>
                         apply Znumtheory.Zdivide_mod; apply Z.divide_mul_r; let q := eval compute in (Z.div k n) in exists q; reflexivity
                     end
                   | apply mod_add_lit; [lia | zmod | zmod]
                   | match goal with
                     | H : ?x mod ?b = 0 |- ?x mod ?n = 0 =>
                         apply (mod0_down x b n); [let q := eval compute in (Z.div b n) in exists q; reflexivity | exact H]
                     end
                   | lazymatch goal with
                     | |- (?a - ?b) mod ?n = 0 => replace (a - b) with (a + - b) by lia; apply mod_add_lit; [lia | zmod | apply Z_mod_zero_opp_full; zmod]
                     end ].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma maxc_half : forall maxc, 2 <= maxc <= 16 -> maxc mod 2 = 0 -> maxc = 2 * Z.shiftr maxc 1 /\ 1 <= Z.shiftr maxc 1 <= 8.
Proof.
  intros maxc MXR MXE. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. pose proof (Z_div_mod_eq_full maxc 2) as EQ. rewrite MXE in EQ.
  set (q := maxc / 2) in *. clearbody q. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac tf_threshold ::= constr:(4%nat).   (* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TfIncl.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_with_region B S a n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TfIncl.tf_with_region_fast B S a n.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.simpl_arr_sizes ::= rewrite ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.u32s_length, ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.u64s_length, ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.upd_length.
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma line_chunks : forall (m : word -> option byte) E (a b c : word) ks (i n : nat),
  rw_cells rsegs m E [C4 a; C4 b; C8 c; CB 64 (u32s ks)] -> length ks = 16%nat -> (i + n <= 16)%nat ->
  u32arr rsegs m (E + 16 + 4 * Z.of_nat i) (firstn n (skipn i ks)).
Proof.
  intros m E a b c ks i n [[WF BA] WR] L HN.
  cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
  apply bytes_at_app in BA as [_ BA]. rewrite length_le4 in BA.
  apply bytes_at_app in BA as [_ BA]. rewrite length_le4 in BA.
  apply bytes_at_app in BA as [_ BA]. rewrite length_le8 in BA.
  rewrite <- (firstn_skipn i ks) in BA at 1. rewrite u32s_app in BA. apply bytes_at_app in BA as [_ BA].
  rewrite u32s_length, firstn_length_le in BA by lia.
  rewrite <- (firstn_skipn n (skipn i ks)) in BA. rewrite u32s_app in BA. apply bytes_at_app in BA as [BA _].
  split.
  - replace (E + 16 + 4 * Z.of_nat i) with (E + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + Z.of_nat (4 * i)) by lia. exact BA.
  - (first [ dand3 WR as W0 W1 W2 | destruct WR as (W0 & W1 & W2) ]). cbn [cells_size csize Nat.add] in W1, W2.
    rewrite firstn_length_le by (rewrite skipn_length; lia).
    split; [lia|]. split; [lia|]. intros j Hj. replace (E + 16 + 4 * Z.of_nat i + j) with (E + (16 + 4 * Z.of_nat i + j)) by lia.
    apply W2. lia.
Qed.

End CEIL.

(* [comment removed for export] *)
Definition cpush_drain_W (sp : word) (depth C c ri sb nf n : Z) : list (Z * Z) :=
  let E := C + 80 * c in let R := ri + 128 * c in let fa := free_array_of sb c in
  [(bv_unsigned sp - depth, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88);
   (fa + 4 * nf, fa + 4 * nf + 4 * n)].

Section CachePush.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo C c sb ri k maxc nf mfa : Z) (ks junk : list word) (statv nfs v88 : word).

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (C + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (free_array_of sb c).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (Z.shiftr maxc 1).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo usp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  (* [comment removed for export] *)
  Hypothesis CLO : aobj C 3888.   (* [comment removed for export] *)
  Hypothesis CHI : C + 3888 <= alloc_ceiling.
  Hypothesis CAL : C mod 16 = 0.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis KR : 0 <= k < 2^28.
  (* [comment removed for export] *)
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_cs : apart C 3888 sb (2^37).
  Hypothesis SEP_cr : apart C 3888 ri 4096.
  (* [comment removed for export] *)
  Hypothesis MXR : 2 <= maxc <= 16.
  Hypothesis MXE : maxc mod 2 = 0.
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis LJ : length junk = Z.to_nat h.
  Hypothesis NF0 : 0 <= nf.
  Hypothesis NFH : nf + h < 2^27.
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1d78 [C8 (wz sb)].
  Hypothesis CRI : ro_cells rsegs m 0xb1d88 [C8 (wz ri)].
  Hypothesis CITV : ro_cells rsegs m 0xb1d80 [C4 (wz 4294967295)].
  Hypothesis CGPS : ro_cells rsegs m 0xa9170 [C8 (wz 0x144e60)].
  Hypothesis CPS : ro_cells rsegs m 0x144e60 [C8 (wz 4096)].
  (* [comment removed for export] *)
  Hypothesis PC : rw_cells rsegs m E [C4 (wz maxc); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)].
  Hypothesis STA : rw_cells rsegs m (C + 2576) [C8 statv].
  Hypothesis MX : rw_cells rsegs m R [C8 (wz 0)].
  Hypothesis NFC : rw_cells rsegs m (R + 16) [C8 (wz nf)].
  Hypothesis MFA : rw_cells rsegs m (R + 24) [C8 (wz mfa)].
  Hypothesis NFS : rw_cells rsegs m (R + 80) [C8 nfs; C8 v88].
  Hypothesis DST : u32arr rsegs m (fa + 4 * nf) junk.


  Definition cpush_drain_fast_post : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (cpush_drain_W sp 320 C c ri sb nf h) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
    /\ rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz k)))]
    /\ rw_cells rsegs m' (C + 2576) [C8 statv']
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))]
    /\ rw_cells rsegs m' (R + 24) [C8 (wz mfa)]
    /\ rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88]
    /\ u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)).

  (* [comment removed for export] *)
  #[using="DST NFS MFA NFC MX STA PC CPS CGPS CITV CRI CSB NFH NF0 LJ LKS MXE MXR SEP_cr SEP_cs SEP_rs RIAL RIHI RILO SBAL SBHI SBLO KR CR CAL CHI CLO RA2 SPA SPH CEIL ST MI statv junk Clg"] Lemma cpush_drain_fast :
    lo <= usp - 320 -> 4 * (nf + h) <= mfa -> mfa < 2^64 ->
    evt rsegs cpush_drain_fast_post
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz C) (wz 0xb1d58) (wz c) (wz (sb + c * 4294967296 + 16 * k)) a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz lcdealloc_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros LOLE FIT MFH.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (maxc_half maxc MXR MXE) as [MH HR8]. pose proof (class_size_range c CR) as CSR. unfold kMaxSize in CSR.
    unfold kHighMemBeg, free_array_of in *.
    pose proof (munch_refl (cpush_drain_W sp 320 C c ri sb nf h) m) as MU. unfold cpush_drain_W, free_array_of in MU. cbv zeta in MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    eapply (lcdealloc_full_ok _ _ gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              lo C c (sb + c * 4294967296 + 16 * k) maxc ks); [> try (fside CV) .. | idtac].
    intros a4b a5b m1 LF PC1 MU1 WM1 MI1 ST1. unfold lcd_frame in LF. rewrite ?unsigned_lit in LF, MU1, ST1 by lia.
    clear PC. kpost MU1 WM1.
    unfold lcdealloc_after, lcdrain_entry.
    (* [comment removed for export] *)
    eapply (lcdrain_pre_ok _ _ gp tp t0 t1 t2 _ _ _ _ a6 a7 _ _ _ s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
              lo C E c maxc maxc (class_size c) ks); [> try (fside CV) .. | idtac].
    intros a6c scr m2 DF PC2 MU2 WM2 MI2 ST2. unfold lcdrain_frame in DF. rewrite ?unsigned_lit in DF, MU2, ST2 by lia.
    clear PC1. kpost MU2 WM2.
    unfold lcdrain_ret, rta_entry. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    eapply (rta_lock_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ _ a6c a7 _ _ _ s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2
              lo ri sb c (usp + -48 + -56) (C + 2560) (E + 16 + 4 * (maxc - h)) h nf); [> try (fside CV) .. | idtac].
    intros t0d t1d t2d a4d a5d a6d t3d t4d t5d t6d scr2 m3 MX3 NFC3 RF MU3 WM3 MI3 ST3. unfold rta_frame in RF.
    rewrite ?unsigned_lit in RF, MU3, ST3 by lia.
    clear MX NFC. kpost MU3 WM3.
    unfold rta_efasret, efas_entry. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (efas_fast_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 lo R (nf + h) mfa)|];
      [> try (fside CV) .. | idtac].
    all: try (fside CV).
    intros ms' PO. destruct_exs PO. (first [ dand5 PO as E4 MUc WMc MI4 ST4 | destruct PO as (E4 & MUc & WMc & MI4 & ST4) ]). subst ms'. rewrite ?unsigned_lit in MUc, ST4 by lia.
    kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x39f74)) with (Z_to_bv 64 0x39f74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells rsegs m4 E _ |- _ =>
      pose proof (line_chunks m4 E _ _ _ ks (Z.to_nat (maxc - h)) (Z.to_nat h) H LKS ltac:(lia)) as SRC end.
    rewrite !Z2Nat.id in SRC by lia.
    remember (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) as ws eqn:HWS.
    assert (LWS : length ws = Z.to_nat h) by (subst ws; rewrite firstn_length_le by (rewrite skipn_length; lia); reflexivity).
    assert (LWZ : Z.of_nat (length ws) = h) by (rewrite LWS, Z2Nat.id by lia; reflexivity).
    assert (LJZ : Z.of_nat (length junk) = h) by (rewrite LJ, Z2Nat.id by lia; reflexivity).
    eapply evt_cut; [eapply (rta_post_ok mrtos_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m4 (usp + -48 + -64) lo ri sb c
                               (usp + -48 + -56) (E + 16 + 4 * (maxc - h)) h nf 1 nfs v88 ws junk scr2)|];
      [> try (fside CV) .. | idtac].
    all: try (fside CV).
    all: try zmod.
    intros ms' PO. destruct_exs PO. (first [ dand10 PO as E5 MUc WMc MI5 ST5 MX5 NFC5 NFS5 SRC5 DST5 | destruct PO as (E5 & MUc & WMc & MI5 & ST5 & MX5 & NFC5 & NFS5 & SRC5 & DST5) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST5 by lia. unfold free_array_of in MUc, DST5.
    clear SRC DST NFS. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x39cd0)) with (Z_to_bv 64 0x39cd0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
    (* [comment removed for export] *)
    eapply (lcdrain_post_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 (usp + -48) lo scr);
      [> try (fside CV) .. | idtac].
    all: try zmod.
    intros t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f m6 MU6 WM6 MI6 ST6.
    rewrite ?unsigned_lit in MU6, ST6 by lia. kpost MU6 WM6.
    replace (ret_pc (Z_to_bv 64 0x39a88)) with (Z_to_bv 64 0x39a88) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (lcdealloc_after_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m6
                               usp lo C c sb k (maxc - h) maxc ks)|];
      [> try (fside CV) .. | idtac].
    all: try (fside CV). all: try zmod.
    intros ms' PO. destruct_exs PO. (first [ dand7 PO as E7 MUc WMc MI7 ST7 PC7 STA7 | destruct PO as (E7 & MUc & WMc & MI7 & ST7 & PC7 & STA7) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST7 by lia.
    kpost MUc WMc. rewrite Z_to_bv_bv_unsigned. subst ws.
    apply evt_done. unfold cpush_drain_fast_post, cpush_drain_W, free_array_of. cbv zeta.
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcell | eassumption].
  Qed.

  (* [comment removed for export] *)
  Hypothesis CPMH : ro_cells rsegs m 0xb1d90 [C1 (Z_to_bv 8 0)].
  Hypothesis CGCF : ro_cells rsegs m 0xa9180 [C8 (wz CF)].
  Hypothesis CDMP : ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)].
  Hypothesis MFA0 : 0 <= mfa.
  Hypothesis MFAM : mfa mod kFaMap = 0.
  #[warnings="-notation-for-abbreviation"] Local Notation nm := (round_up (4 * (nf + h)) kFaMap).
  #[warnings="-notation-for-abbreviation"] Local Notation fe := (sb + c * 4294967296 + kFreeArrayOffset + mfa).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End CachePush.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
