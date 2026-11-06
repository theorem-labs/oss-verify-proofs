(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Arr Frame Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit BF_refill2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
Ltac cstep := stepA; try first [if_true | if_false].

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
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma le4_sx32 : forall w : word, le4 (sx32 w) = le4 w.
Proof. aceil.
  intros w. unfold le4, sx32. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z_to_le_bytes_mod by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 (bv_unsigned w)) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned w) 32) by (cbn; lia). f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648. change (2^32) with 4294967296.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma nth_error_Some_lt : forall {X} (l : list X) i, (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof. aceil.
  intros X l i Hi. destruct (nth_error l i) as [x|] eqn:E; [exists x; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Section GFA2.
Variable P : acc -> Prop.
(* [comment removed for export] *)
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo INST STAT c CH n SB RI RP FA : Z).
Hypothesis HRP : RP = RI + kRegSize * c.
Hypothesis HFA : FA = SB + c * 2^32 + 0xE0000000.
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 128.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis HC : 1 <= c <= 30.
Hypothesis HN : 1 <= n <= 16.
Hypothesis HINST : 0xa5000 <= INST /\ INST + 64 <= 0x603000.
Hypothesis HSB : 0x10007fff8000 <= SB /\ SB + 2^37 + 4096 <= alloc_ceiling /\ SB mod 4096 = 0.
Hypothesis HRI : RI = SB + 2^37.
Hypothesis HCH : (0x1000 <= CH /\ (CH + 64 <= 0x10000 \/ 0x603000 <= CH)) /\ CH + 64 <= alloc_ceiling /\ CH mod 4 = 0.   (* [comment removed for export] *)
Hypothesis HCS : CH + 64 <= SB \/ SB + 2^37 + 4096 <= CH.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).      (* [comment removed for export] *)
Hypothesis PRI : forall a k, RI <= a -> a + Z.of_nat k <= RI + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, CH <= a -> a + Z.of_nat k <= CH + 64 -> P (Z_to_bv 64 a, k).

Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -128)).
Notation GW := (gfa_W sp CH n RP).
Notation FRAME m fj cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 :=
  (rw_cells bsegs m (bv_unsigned sp + -128) [CB 24 fj; C8 cs11; C8 cs10; C8 cs9; C8 cs8; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 ra]).

(* [comment removed for export] *)
Local Ltac geom :=
  pose proof LOC as LOCu; aceil;
  pose proof HSB as (SB1 & SB2 & SB3); aceil;
  pose proof HCH as (CH1 & CH2 & CH4); aceil;
  pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR;
  assert (HRP' : RP = SB + 2^37 + 128 * c) by (rewrite HRP, HRI; unfold kRegSize; lia);
  assert (PRP : forall a k, RP <= a -> a + Z.of_nat k <= RP + 128 -> P (Z_to_bv 64 a, k)) by (intros a' k' H1 H2; apply PRI; rewrite HRP' in H1, H2; lia);
  assert (FA1 : SB <= FA) by (rewrite HFA; lia);
  assert (FA2 : FA + 2^29 <= SB + 2^37) by (rewrite HFA; lia);
  assert (FA4 : FA mod 4 = 0) by (rewrite HFA; clear -SB3; aceil; Z.div_mod_to_equations; lia).

(* [comment removed for export] *)
Definition gfa_done (rv : Z) (ncop : nat) (cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 xt4 xt5 xt6 : word) (m0 : mem)
    (nf' mfa au mu na' nfr : Z) (ws ds0 : list word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 : word) m' ds,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3 xt4 xt5 xt6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch GW m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' RP (rrow 0 nf' mfa au mu na' nfr)
    /\ u32arr bsegs m' FA ws /\ u32arr bsegs m' CH ds /\ length ds = 16%nat
    /\ (forall j, (j < ncop)%nat -> nth_error ds j = nth_error ws (Z.to_nat nf' + j)%nat)
    /\ (forall j, (ncop <= j)%nat -> nth_error ds j = nth_error ds0 j).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gfa_unlock_ret :
  forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
         (cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (fj : list byte) (rv : Z)
         (mu0 m0 : mem) (nf mfa au mu na nfr : Z) (ws ds : list word) (Q : machine_state -> Prop),
  mem_inv bsegs mu0 -> stk bsegs mu0 lo (bv_unsigned sp + -128) -> munch GW m0 mu0 -> wmono bsegs m0 mu0 ->
  FRAME mu0 fj cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  rw_cells bsegs mu0 RP (rrow kMtxWriter nf mfa au mu na nfr) ->
  u32arr bsegs mu0 FA ws -> 4 * Z.of_nat (length ws) <= 2^29 -> u32arr bsegs mu0 CH ds -> length ds = 16%nat ->
  (forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 : word) (m' : mem),
     mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) -> munch GW m0 m' -> wmono bsegs m0 m' ->
     rw_cells bsegs m' RP (rrow 0 nf mfa au mu na nfr) -> u32arr bsegs m' FA ws -> u32arr bsegs m' CH ds ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3 xt4 xt5 xt6)
                        F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 RP) (Z_to_bv 64 rv) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                          xs2 (Z_to_bv 64 0x2000000000000000) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x37a94) fc None mu0 (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI SK MU WM FR RROW AF LWS AC LDS K. unfold rrow, kMtxWriter in RROW. unfold gfa_W in MU. geom.
  do 15 zstepA.   (* [comment removed for export] *)
  do 5 cstep.     (* [comment removed for export] *)
  do 8 cstep.     (* [comment removed for export] *)
  do 5 cstep.     (* [comment removed for export] *)
  cstep.          (* [comment removed for export] *)
  do 16 zstepA.   (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  eapply K; try eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section COPY.
(* [comment removed for export] *)
Variables (xra xt0 xt1 xt2 xs1 xa0 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word).
Variables (ml : mem) (ws ds0 : list word) (nf' : Z).
Hypothesis SRC : u32arr bsegs ml FA ws.
Hypothesis NF0 : 0 <= nf'.
Hypothesis NFN : nf' + n <= Z.of_nat (length ws).
Hypothesis LWS : 4 * Z.of_nat (length ws) <= 2^29.
Hypothesis PFA : forall a k, FA <= a -> a + Z.of_nat k <= FA + 4 * Z.of_nat (length ws) -> P (Z_to_bv 64 a, k).

Definition CF (mm : mem) (ds : list word) (i : Z) : Prop :=
  mem_inv bsegs mm /\ stk bsegs mm lo (bv_unsigned sp + -128) /\ munch [(CH, CH + 4 * n)] ml mm /\ wmono bsegs ml mm
  /\ u32arr bsegs mm CH ds /\ length ds = 16%nat
  /\ (forall j, (j < Z.to_nat i)%nat -> nth_error ds j = nth_error ws (Z.to_nat nf' + j)%nat)
  /\ (forall j, (Z.to_nat i <= j)%nat -> nth_error ds j = nth_error ds0 j).

Definition CST (pc i : Z) (a2 : word) (mm : mem) : machine_state :=
  MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 RP) xs1 xa0 (Z_to_bv 64 (CH + 4 * n)) a2 (Z_to_bv 64 (CH + 4 * i)) (Z_to_bv 64 n) (Z_to_bv 64 (4 * nf')) xa6 xa7
          xs2 (Z_to_bv 64 0x2000000000000000) (Z_to_bv 64 (FA + 4 * nf' + 4 * i)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
     F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs).

Lemma gfa_copy_iter : forall (i : Z) (mm : mem) (ds : list word) (a2 : word) (Q : machine_state -> Prop),
  0 <= i < n -> CF mm ds i ->
  (i + 1 = n -> forall mm' ds' a2', CF mm' ds' (i + 1) -> evtA bsegs P Q (CST 0x37a84 (i + 1) a2' mm')) ->
  (i + 1 < n -> forall mm' ds' a2', CF mm' ds' (i + 1) -> evtA bsegs P Q (CST 0x37a70 (i + 1) a2' mm')) ->
  evtA bsegs P Q (CST 0x37a70 i a2 mm).
Proof. aceil.
  intros i mm ds a2 Q Hi (MI & SK & MU & WM & ARR & LDS & D1 & D2) KX KL. unfold CST. geom.
  assert (SRCm : u32arr bsegs mm FA ws).
  { eapply u32arr_transport; [exact SRC| exact MU| exact WM|]. cbn [disjoint_from]. clear -CEILB HCS FA1 FA2 LWS HN. lia. }
  destruct (nth_error_Some_lt ws (Z.to_nat (nf' + i)) ltac:(lia)) as (w & Hw).
  pose proof (u32arr_read bsegs mm FA ws (nf' + i) w _ SRCm Hw ltac:(lia) eq_refl) as HR.
  zstepA.   (* [comment removed for export] *)
  clear SRCm.
  pose proof (u32arr_store_ok bsegs mm CH ds i (Z_to_bv 64 (CH + 4 * i)) ARR ltac:(rewrite LDS; lia) eq_refl) as SOK.
  stepA.    (* [comment removed for export] *)
  all: lazymatch goal with |- P _ => apply PCH; lia | _ => idtac end.
  rewrite (le4_sx32 w).
  pose proof (u32arr_write bsegs mm CH ds i w ARR ltac:(rewrite LDS; lia)) as ARR'.
  clear ARR. store_done. rename ARR' into ARR.
  assert (CF' : CF m (upd ds (Z.to_nat i) w) (i + 1)).
  { split; [exact MI|]. split; [exact SK|]. split; [exact MU|]. split; [exact WM|]. split; [exact ARR|].
    split; [rewrite upd_length; exact LDS|]. split.
    - intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE].
      + rewrite nth_error_upd_same by (rewrite LDS; lia). rewrite <- Hw. f_equal. lia.
      + rewrite nth_error_upd_other by lia. apply D1. lia.
    - intros j Hj. rewrite nth_error_upd_other by lia. apply D2. lia. }
  zstepA. zstepA.  (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    replace (CH + 4 * i + 4) with (CH + 4 * (i + 1)) by lia.
    replace (FA + 4 * nf' + 4 * i + 4) with (FA + 4 * nf' + 4 * (i + 1)) by lia.
    eapply (KL ltac:(lia)). exact CF'.
  - replace (CH + 4 * i + 4) with (CH + 4 * (i + 1)) by lia.
    replace (FA + 4 * nf' + 4 * i + 4) with (FA + 4 * nf' + 4 * (i + 1)) by lia.
    eapply (KX ltac:(lia)). exact CF'.
Qed.

Lemma gfa_copy : forall (k : nat) (i : Z) (mm : mem) (ds : list word) (a2 : word) (Q : machine_state -> Prop),
  i + Z.of_nat k + 1 = n -> 0 <= i -> CF mm ds i ->
  (forall mm' ds' a2', CF mm' ds' n -> evtA bsegs P Q (CST 0x37a84 n a2' mm')) ->
  evtA bsegs P Q (CST 0x37a70 i a2 mm).
Proof. aceil.
  induction k as [|k IH]; intros i mm ds a2 Q Hk Hi HCF KX.
  - eapply gfa_copy_iter; [lia| exact HCF| |intros; exfalso; lia].
    intros E mm' ds' a2' CF'. rewrite E in CF' |- *. exact (KX _ _ _ CF').
  - eapply gfa_copy_iter; [lia| exact HCF| intros; exfalso; lia|].
    intros _ mm' ds' a2' CF'. eapply IH; [lia| lia| exact CF'| exact KX].
Qed.
End COPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gfa_tail :
  forall (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
         (cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (fj : list byte)
         (mt m0 : mem) (nf' mfa au mu na nfr : Z) (ws ds0 : list word),
  mem_inv bsegs mt -> stk bsegs mt lo (bv_unsigned sp + -128) -> munch GW m0 mt -> wmono bsegs m0 mt ->
  FRAME mt fj cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  rw_cells bsegs mt RP (rrow kMtxWriter nf' mfa au mu na nfr) ->
  u32arr bsegs mt FA ws -> 0 <= nf' -> nf' + n <= Z.of_nat (length ws) -> 4 * Z.of_nat (length ws) <= 2^29 ->
  (forall a k, FA <= a -> a + Z.of_nat k <= FA + 4 * Z.of_nat (length ws) -> P (Z_to_bv 64 a, k)) ->
  u32arr bsegs mt CH ds0 -> length ds0 = 16%nat -> 0 <= na < 2^64 ->
  evtA bsegs P (gfa_done 1 (Z.to_nat n) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 xt4 xt5 xt6 m0 nf' mfa au mu (na + n) nfr ws ds0)
    (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 RP) xs1 xa0 xa1 xa2 (Z_to_bv 64 CH) (Z_to_bv 64 n) (Z_to_bv 64 nf') xa6 xa7
             xs2 (Z_to_bv 64 0x2000000000000000) (Z_to_bv 64 FA) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x37a60) fc None mt (seg_rom bsegs)).
Proof. aceil.
  intros until ds0. intros MI SK MU0 WM0 FR RROW AF NF0 NFN LWS PFA AC LDS NA0. geom.
  do 4 zstepA.     (* [comment removed for export] *)
  replace (nf' ≪ 2) with (4 * nf') by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (n ≪ 2) with (4 * n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (Z_to_bv 64 CH) with (Z_to_bv 64 (CH + 4 * 0)) by (f_equal; lia).
  replace (FA + 4 * nf') with (FA + 4 * nf' + 4 * 0) by lia.
  eapply (gfa_copy xra xt0 xt1 xt2 xs1 xa0 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mt ws ds0 nf' AF NF0 NFN LWS PFA
            (Z.to_nat (n - 1)) 0 mt ds0); [lia| lia| |].
  { split; [exact MI|]. split; [exact SK|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact AC|].
    split; [exact LDS|]. split; [intros j Hj; exfalso; lia| intros j Hj; reflexivity]. }
  intros mm ds a2' (MI' & SK' & MUL & WML & ARR & LDS' & D1 & D2). unfold CST.
  assert (FR' : FRAME mm fj cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11).
  { eapply rw_cells_transport; [exact FR| exact MUL| exact WML|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. clear -CEILB LOCu LO CH2 HN. lia. }
  assert (RROW' : rw_cells bsegs mm RP (rrow kMtxWriter nf' mfa au mu na nfr)).
  { eapply rw_cells_transport; [exact RROW| exact MUL| exact WML|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul rrow]. clear -CEILB HCS HRP' HC HN. lia. }
  assert (AF' : u32arr bsegs mm FA ws).
  { eapply u32arr_transport; [exact AF| exact MUL| exact WML|]. cbn [disjoint_from]. clear -CEILB HCS FA1 FA2 LWS HN. lia. }
  assert (MU : munch GW m0 mm).
  { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MUL]. unfold sub_fp, gfa_W. cbn [outside]. clear. intros x Hx. tauto. }
  clear FR RROW AF MUL MI SK MU0.
  assert (WM : wmono bsegs m0 mm) by (eapply wmono_trans; [exact WM0| exact WML]). clear WM0 WML.
  unfold rrow, kMtxWriter in RROW'. unfold gfa_W in MU.
  zstepA.          (* [comment removed for export] *)
  zstepA.          (* [comment removed for export] *)
  zstepA.          (* [comment removed for export] *)
  zstepA.          (* [comment removed for export] *)
  eapply gfa_unlock_ret; try eassumption.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 m' MI2 SK2 MU2 WM2 RROW2 AF2 AC2.
  apply evtA_done. unfold gfa_done. do 13 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try eassumption.
Qed.

(* [comment removed for export] *)
Notation LOCKED a5v xs2 xs10 xs11 xt3 xt4 xt5 xt6 :=
  (mkR ra SP' gp tp (Z_to_bv 64 0) (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 0) (Z_to_bv 64 RP) (Z_to_bv 64 INST) (Z_to_bv 64 (RP + 8))
       (Z_to_bv 64 STAT) (Z_to_bv 64 c) (Z_to_bv 64 CH) (Z_to_bv 64 n) a5v (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
       xs2 (Z_to_bv 64 0x2000000000000000) (Z_to_bv 64 FA) (Z_to_bv 64 0x10000000000) (Z_to_bv 64 0x10000000000fffff)
       (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 1500) (Z_to_bv 64 0xdfffffffffffffff) xs10 xs11 xt3 xt4 xt5 xt6).

(* [comment removed for export] *)
Lemma gfa_direct :
  forall (xs2 xs10 xs11 xt3 xt4 xt5 xt6 : word) (cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (fj : list byte)
         (m1 : mem) (nf mfa au mu na nfr : Z) (ws ds0 : list word),
  mem_inv bsegs m1 -> stk bsegs m1 lo (bv_unsigned sp + -128) ->
  FRAME m1 fj cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  rw_cells bsegs m1 RP (rrow kMtxWriter nf mfa au mu na nfr) ->
  u32arr bsegs m1 FA ws -> n <= nf -> nf <= Z.of_nat (length ws) -> 4 * Z.of_nat (length ws) <= 2^29 ->
  (forall a k, FA <= a -> a + Z.of_nat k <= FA + 4 * Z.of_nat (length ws) -> P (Z_to_bv 64 a, k)) ->
  u32arr bsegs m1 CH ds0 -> length ds0 = 16%nat -> 0 <= na < 2^64 ->
  evtA bsegs P (gfa_done 1 (Z.to_nat n) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 xt4 xt5 xt6 m1 (nf - n) mfa au mu (na + n) nfr ws ds0)
    (MS (LOCKED (Z_to_bv 64 0) xs2 xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x37a4c) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until ds0. intros MI SK FR RROW AF NFN NFL LWS PFA AC LDS NA0. geom. unfold rrow, kMtxWriter in RROW.
  assert (MU : munch GW m1 m1) by apply munch_refl. unfold gfa_W in MU. assert (WM : wmono bsegs m1 m1) by apply wmono_refl.
  zstepA.          (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. clear -CEILB K0 NFN NFL LWS HN. lia. }   (* [comment removed for export] *)
  zstepA.          (* [comment removed for export] *)
  zstepA.          (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { exfalso. clear -CEILB K1 HN. lia. }              (* [comment removed for export] *)
  eapply gfa_tail; try eassumption; lia.
Qed.

(* [comment removed for export] *)
Definition gfa_at_pop (xs10 xs11 xt3 xt4 xt5 xt6 : word) (m : mem) (nf : Z) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR (Z_to_bv 64 0x37bb8) SP' gp tp (Z_to_bv 64 0) (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 0) (Z_to_bv 64 RP) (Z_to_bv 64 INST)
                            (Z_to_bv 64 INST) (Z_to_bv 64 STAT) (Z_to_bv 64 c) (Z_to_bv 64 RP) (Z_to_bv 64 (n - nf)) (Z_to_bv 64 nf) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                            (Z_to_bv 64 (RP + 8)) (Z_to_bv 64 0x2000000000000000) (Z_to_bv 64 FA) (Z_to_bv 64 CH) (Z_to_bv 64 n)
                            (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 1500) (Z_to_bv 64 0xdfffffffffffffff) xs10 xs11 xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x37c04) fc None m (seg_rom bsegs).

Lemma gfa_to_pop :
  forall (xs2 xs10 xs11 xt3 xt4 xt5 xt6 : word) (m1 : mem) (nf mfa au mu na nfr : Z),
  mem_inv bsegs m1 -> rw_cells bsegs m1 RP (rrow kMtxWriter nf mfa au mu na nfr) -> 0 <= nf < n ->
  evtA bsegs P (gfa_at_pop xs10 xs11 xt3 xt4 xt5 xt6 m1 nf)
    (MS (LOCKED (Z_to_bv 64 0) xs2 xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x37a4c) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until nfr. intros MI RROW NF. geom. unfold rrow, kMtxWriter in RROW.
  zstepA.          (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. 2:{ exfalso. clear -CEILB K0 NF HN. lia. }       (* [comment removed for export] *)
  do 7 zstepA.     (* [comment removed for export] *)
  apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gfa_pop_ok :
  forall (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 : word)
         (cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) (fj : list byte)
         (m3 m0 : mem) (nf1 mfa au mu na nfr : Z) (ws ds0 : list word),
  mem_inv bsegs m3 -> stk bsegs m3 lo (bv_unsigned sp + -128) -> munch GW m0 m3 -> wmono bsegs m0 m3 ->
  FRAME m3 fj cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  rw_cells bsegs m3 RP (rrow kMtxWriter nf1 mfa au mu na nfr) ->
  u32arr bsegs m3 FA ws -> n <= nf1 -> nf1 <= Z.of_nat (length ws) -> 4 * Z.of_nat (length ws) <= 2^29 ->
  (forall a k, FA <= a -> a + Z.of_nat k <= FA + 4 * Z.of_nat (length ws) -> P (Z_to_bv 64 a, k)) ->
  u32arr bsegs m3 CH ds0 -> length ds0 = 16%nat -> 0 <= na < 2^64 ->
  evtA bsegs P (gfa_done 1 (Z.to_nat n) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 xt4 xt5 xt6 m0 (nf1 - n) mfa au mu (na + n) nfr ws ds0)
    (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 RP) (Z_to_bv 64 INST) (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 (RP + 8)) (Z_to_bv 64 0x2000000000000000) (Z_to_bv 64 FA) (Z_to_bv 64 CH) (Z_to_bv 64 n)
             (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 1500) (Z_to_bv 64 0xdfffffffffffffff) xs10 xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x37bb8) fc None m3 (seg_rom bsegs)).
Proof. aceil.
  intros until ds0. intros MI SK MU0 WM0 FR RROW AF NFN NFL LWS PFA AC LDS NA0. geom. unfold rrow, kMtxWriter in RROW.
  unfold gfa_W in MU0.
  cstep.           (* [comment removed for export] *)
  zstepA.          (* [comment removed for export] *)
  zstepA.          (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. clear -CEILB K0 NFN NFL LWS HN. lia. }   (* [comment removed for export] *)
  do 5 zstepA.     (* [comment removed for export] *)
  eapply gfa_tail; try eassumption; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End GFA2.

End RC__1.
