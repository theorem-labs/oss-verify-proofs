(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan sha256 c0661b96). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strcpyw.v, with its module paths, addresses and numbers changed; 344 of its 490 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strtolfix.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 20 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/Bz/A/I_strtolfix.v of this library by derive_y.py b7b132fb12a7: module paths lib.A -> lib.AU, the image module Asan -> AsanUbsan and Img0 -> Img0U, addresses moved from fuzz_headamp's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/Bz/A/I_strtolfix.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Lemma sfix_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x51b10) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51b00) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Lemma sfix_loopE : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a5' a6' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2 a3 a4 a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x51c4c) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51c3c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Definition is_blank (c : Z) : bool := ((9 <=? c) && (c <=? 13)) || (c =? 32).
Fixpoint nblank (l : list byte) : nat :=
  match l with b :: l' => if is_blank (bv_unsigned b) then Datatypes.S (nblank l') else O | [] => O end.
Definition fix_off (l : list byte) : Z :=
  match nth_error l (nblank l) with
  | Some b => if (bv_unsigned b =? 43) || (bv_unsigned b =? 45) then Z.of_nat (nblank l) + 1 else Z.of_nat (nblank l)
  | None => Z.of_nat (nblank l)
  end.
Lemma nblank_nul : forall str, (nblank (str ++ [Z_to_bv 8 0]) <= length str)%nat.
Proof. induction str as [|b str IH]; [vm_compute; lia|]. cbn [app nblank length]. destruct (is_blank (bv_unsigned b)); lia. Qed.
Lemma fix_off_range : forall str, 0 <= fix_off (str ++ [Z_to_bv 8 0]) <= Z.of_nat (length str).
Proof.
  intros str. unfold fix_off. pose proof (nblank_nul str) as H.
  destruct (nth_error (str ++ [Z_to_bv 8 0]) (nblank (str ++ [Z_to_bv 8 0]))) as [b|] eqn:E; [|lia].
  destruct ((bv_unsigned b =? 43) || (bv_unsigned b =? 45))%bool eqn:SG; [|lia].
  destruct (Nat.eq_dec (nblank (str ++ [Z_to_bv 8 0])) (length str)) as [EQ|NE]; [|lia].
  exfalso. rewrite EQ, nth_error_app2, Nat.sub_diag in E by lia. cbn in E. injection E as <-. vm_compute in SG. discriminate.
Qed.
Lemma blank_code : forall c, 0 <= c < 256 -> is_blank c = (((c + -9) mod 18446744073709551616 <? 5) || (c =? 32))%bool.
Proof.
  intros c Hc. unfold is_blank. f_equal.
  destruct (Z.leb_spec 9 c) as [H9|H9]; cbn [andb].
  - rewrite Z.mod_small by lia. destruct (Z.leb_spec c 13), (Z.ltb_spec (c + -9) 5); try reflexivity; lia.
  - replace ((c + -9) mod 18446744073709551616) with (c + -9 + 18446744073709551616) by (apply (Z.mod_unique _ _ (-1)); lia).
    destruct (Z.ltb_spec (c + -9 + 18446744073709551616) 5); [lia| reflexivity].
Qed.

Lemma sfix_ws : forall (n i : nat) (A : Z) (str : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> 0 <= A -> A + Z.of_nat (length str) + 1 < 2^64 ->
  (i <= length str)%nat -> nblank (skipn i (str ++ [Z_to_bv 8 0])) = n -> (nblank (str ++ [Z_to_bv 8 0]) = i + n)%nat ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (a1' a4' a5' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' (Z_to_bv 64 32) (Z_to_bv 64 (A + fix_off (str ++ [Z_to_bv 8 0]))) a4' a5' a6 a7
                    (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x519c4) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 5) (Z_to_bv 64 32) (Z_to_bv 64 (A + Z.of_nat i)) a4 a5 a6 a7
             (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x519a0) fc None m (seg_rom asegs)).
Proof.
  induction n as [|n IH]; intros i A str ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    STR A0 AN Hi Hn Hnb MI;
    set (LL := str ++ [Z_to_bv 8 0]) in *;
    (destruct (nth_error LL i) as [b|] eqn:Eb; [| exfalso; apply nth_error_None in Eb; unfold LL in Eb; rewrite length_app in Eb; cbn in Eb; lia]);
    pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Rb; cbn in Rb;
    pose proof (bytes_at_nth1 asegs m A LL i b STR Eb) as Bb;
    pose proof (ro_C1_of_bytes _ _ _ Bb) as CB;
    assert (SK : skipn i LL = b :: skipn (Datatypes.S i) LL)
      by (clear - Eb; revert i Eb; induction LL as [|x l IHl]; intros [|i] E; cbn in *; try discriminate; [injection E as ->; reflexivity | apply IHl; exact E]);
    rewrite SK in Hn; cbn [nblank] in Hn; pose proof (blank_code _ Rb) as BC;
    assert (EUi : bv_unsigned (Z_to_bv 64 (A + Z.of_nat i)) = A + Z.of_nat i) by (apply unsigned_lit; lia);
    assert (EUi1 : bv_unsigned (Z_to_bv 64 (A + Z.of_nat i + 1)) = A + Z.of_nat i + 1) by (apply unsigned_lit; lia);
    pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
    remember (A + Z.of_nat i)%Z as ci eqn:Eci.
  - destruct (is_blank (bv_unsigned b)) eqn:EB; [discriminate Hn|]. symmetry in BC. apply orb_false_iff in BC. destruct BC as [BC1 BC2].
    apply Z.ltb_ge in BC1. apply Z.eqb_neq in BC2.
    assert (FO : fix_off LL = if ((bv_unsigned b =? 43) || (bv_unsigned b =? 45))%bool then Z.of_nat i + 1 else Z.of_nat i).
    { unfold fix_off. replace (nblank LL) with i by lia. rewrite Eb. reflexivity. }
    lstep. lstep. lstep. if_cases Kbl; [ zify_cond Kbl; exfalso; lia | ]. lstep. if_cases Kbe; [ zify_cond Kbe; exfalso; lia | ].
    lstep. lstep. if_cases K3.
    + lstep. zify_cond K3. apply evt_done. do 3 eexists.
      rewrite FO, (proj2 (Z.eqb_eq _ _) K3). cbn [orb]. rewrite Eci. replace (A + (Z.of_nat i + 1)) with (A + Z.of_nat i + 1) by lia. reflexivity.
    + lstep. lstep. if_cases K4.
      * zify_cond K3. zify_cond K4. apply evt_done. do 3 eexists.
        rewrite FO, (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_neq _ _) K4). cbn [orb]. rewrite Eci. reflexivity.
      * lstep. zify_cond K3. zify_cond K4. apply evt_done. do 3 eexists.
        rewrite FO, (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_eq _ _) K4), orb_true_r. rewrite Eci. replace (A + (Z.of_nat i + 1)) with (A + Z.of_nat i + 1) by lia. reflexivity.
  - destruct (is_blank (bv_unsigned b)) eqn:EB; [| discriminate Hn]. injection Hn as Hn.
    symmetry in BC. apply orb_true_iff in BC.
    assert (ILT : (i < length str)%nat).
    { destruct (Nat.eq_dec i (length str)) as [EQ|]; [|lia]. exfalso. unfold LL in Eb. rewrite EQ, nth_error_app2, Nat.sub_diag in Eb by lia. cbn in Eb. injection Eb as <-. vm_compute in EB. discriminate. }
    lstep. lstep. lstep. if_cases K1.
    + lstep. replace (ci + 1) with (A + Z.of_nat (Datatypes.S i)) by (rewrite Eci; lia).
      eapply (IH (Datatypes.S i)); [exact STR| lia| lia| lia| exact Hn| unfold LL in *; lia| exact MI].
    + lstep. if_cases K2.
      * lstep. replace (ci + 1) with (A + Z.of_nat (Datatypes.S i)) by (rewrite Eci; lia).
        eapply (IH (Datatypes.S i)); [exact STR| lia| lia| lia| exact Hn| unfold LL in *; lia| exact MI].
      * exfalso. zify_cond K1. zify_cond K2. destruct BC as [BC|BC]; [apply Z.ltb_lt in BC| apply Z.eqb_eq in BC]; lia.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition sfix_chkpost (q : Z) (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (q + -2144)) gp tp t0' t1' t2' (Z_to_bv 64 q) s1' a0' a1' a2' a3' a4' a5' a6' a7'
                    s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x51a44) fc None m' (seg_rom asegs)
      /\ munch [(q - 2224, q - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (q + -2144).

Lemma sfix_rip : forall (q p L : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (q + -2144) -> lo <= q - 2224 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  acc asegs m p (L + 1) -> rng_ok p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (sfix_chkpost q gp tp s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 (L + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51b18) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(q - 2224, q - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (q + -2144)) = q + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold sfix_chkpost. do 24 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma sfix_chk : forall (q p L : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (q + -2144) -> lo <= q - 2224 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  chk_ok m p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (sfix_chkpost q gp tp s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 (L + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x519f4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(q - 2224, q - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (M2S : m2s_cells m) by (split; [exact G2| split; [exact SHC| exact HM]]). unfold SHB in SHC.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (L + 1)) = L + 1) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. if_false. lstep. lstep.
  destruct (Z_lt_le_dec L 64) as [SMALL|BIG].
  - lstep.
    assert (Cb : negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (L + -64))) = false).
    { unfold bv_ltu. apply negb_false_iff, Z.ltb_lt. rewrite (unsigned_lit_wrap (-65)), (unsigned_lit_wrap (L + -64)).
      change ((-65) mod 2^64) with 18446744073709551551.
      assert (HMd : (L + -64) mod 2^64 = L + -64 + 2^64)
        by (rewrite Zmod_eq_full by lia; replace ((L + -64) / 2^64) with (-1) by (Z.div_mod_to_equations; lia); lia).
      rewrite HMd. lia. }
    rewrite Cb; cbv iota.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + (L + 1) + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + (L + 1) - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + (L + 1) + -1) / 8) with ((p + (L + 1) - 1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p (L + 1) AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + (L + 1) - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. unfold sfix_chkpost. do 24 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (sfix_rip q p L); try assumption; unfold kHighShadowEnd; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (sfix_loop (Z.to_nat ((p + (L + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold sfix_chkpost. do 24 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (sfix_rip q p L); try assumption; unfold kHighShadowEnd; lia.
    + apply evt_done. unfold sfix_chkpost. do 24 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - lstep.
    assert (Cb : negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (L + -64))) = true).
    { unfold bv_ltu. apply negb_true_iff, Z.ltb_ge. rewrite (unsigned_lit_wrap (-65)), (unsigned_lit (L + -64)) by lia.
      change ((-65) mod 2^64) with 18446744073709551551. lia. }
    rewrite Cb; cbv iota. lstep. if_true.
    apply (sfix_rip q p L); try assumption; unfold kHighShadowEnd; lia.
Qed.

Definition sfix_tpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (str : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q + -2224, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' A (str ++ [Z_to_bv 8 0]).

Lemma sfix_back : forall (q p L : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 : word) F fc (m : mem) (lo : Z) (str fjunk : list byte),
  stk asegs m lo (q + -2144) -> lo <= q - 2224 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  chk_ok m p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  bytes_at asegs m p (str ++ [Z_to_bv 8 0]) -> (p + Z.of_nat (length str) + 1 <= q + -2224 \/ q <= p) ->
  rw_cells asegs m (q + -72) [C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells asegs m (q + -2144) [CB 2072 fjunk] ->
  evt asegs (sfix_tpost vra q gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 s8 s9 s10 s11 F fc p str lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 (L + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x519f4) fc None m (seg_rom asegs)).
Proof.
  intros until fjunk. intros ST LO LOLO SPH D0 N0 DN CHK M2S MI STR SEPS FRs FR. unfold kHighShadowEnd in *.
  pose proof (munch_refl [(q + -2224, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  call (sfix_chk q p L); try eassumption; try (unfold kHighShadowEnd; lia).
  lazymatch goal with H : stk asegs _ lo (q + -2144) |- _ => rename H into ST1 end.
  do 10 lstep. release_frame FR ST1 (q + -72). release_frame FRs ST1 q. lstep. lstep.
  unfold sfix_tpost. sys_finish. all: rewrite ?EU; assumption.
Qed.

Definition sfixE_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (str : list byte) (E k : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q + -2224, q); (E, E + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' A (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' E [C8 (Z_to_bv 64 (A + k))].

Definition icells_sx (m : mem) : Prop :=
  ro_cells asegs m 0x9c7e0 [C8 (Z_to_bv 64 0x136d68)] /\ ro_cells asegs m 0x136e5d [C1 (Z_to_bv 8 0)].

Lemma sfix_from_57268 : forall (q A E lo fo k : Z) (ra gp tp t0 t1 t2 s1 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 : word) F fc (m : mem) (str fjunk : list byte),
  stk asegs m lo (q + -2144) -> lo <= q - 2224 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= A -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> (A + Z.of_nat (length str) + 1 <= q + -2224 \/ q <= A) ->
  (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) -> 0 <= fo <= Z.of_nat (length str) -> 0 <= k ->
  m2s_cells m -> icells_sx m -> mem_inv asegs m ->
  0 < E -> (E + 8 <= q + -2224 \/ q <= E) -> (E + 8 <= A \/ A + Z.of_nat (length str) + 1 <= E) ->
  rw_cells asegs m E [C8 (Z_to_bv 64 (A + k))] ->
  rw_cells asegs m (q + -72) [C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells asegs m (q + -2144) [CB 2072 fjunk] ->
  evt asegs (sfixE_post vra q gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 s8 s9 s10 s11 F fc A str E k lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 1) a1 a2 (Z_to_bv 64 (A + fo)) a4 a5 a6 a7
             (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x519c4) fc None m (seg_rom asegs)).
Proof.
  intros until fjunk. intros ST LO LOLO SPH A0 A47 N40 STR SEPS CHK FO K0 M2S (IC1 & IC2) MI E0 ESEP ESEP2 ECELL FRs FR.
  unfold kHighShadowEnd in *.
  do 2 lstep. lstep. lstep. if_true. do 4 lstep.
  replace (Z.land 18446744073709551615 (A + fo - A + 1)) with (fo + 1)
    by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; lia).
  eapply evt_mono.
  { eapply (sfix_back q A fo); try eassumption; try (apply (CHK (fo + 1)); lia); try (unfold kHighShadowEnd; lia); try lia. }
  intros ms' Hpost. unfold sfix_tpost in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Heq & Hmunch & Hwm & Hmi & Hstk & Hba).
  unfold sfixE_post. do 16 eexists. split; [exact Heq|].
  split; [apply (munch_weaken [(q + -2224, q)]); [unfold sub_fp; intros x Hx; cbn in Hx |- *; tauto| exact Hmunch]|].
  split; [exact Hwm|]. split; [exact Hmi|]. split; [exact Hstk|]. split; [exact Hba|].
  apply (rw_cells_agree asegs m m' E _ ECELL); [| exact Hwm].
  apply (agree_of_munch _ _ _ _ Hmunch). intros y Hy; cbn in Hy |- *; destruct ESEP as [He|He]; lia.
Qed.

Lemma sfix_from_57204 : forall (q A E k lo : Z) (ra gp tp t0 t1 t2 s1 a1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 : word) F fc (m : mem) (str fjunk : list byte),
  stk asegs m lo (q + -2144) -> lo <= q - 2224 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= A -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> (A + Z.of_nat (length str) + 1 <= q + -2224 \/ q <= A) ->
  (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) -> 0 <= k <= Z.of_nat (length str) ->
  m2s_cells m -> icells_sx m -> mem_inv asegs m ->
  0 < E -> (E + 8 <= q + -2224 \/ q <= E) -> (E + 8 <= A \/ A + Z.of_nat (length str) + 1 <= E) ->
  rw_cells asegs m E [C8 (Z_to_bv 64 (A + k))] ->
  rw_cells asegs m (q + -72) [C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells asegs m (q + -2144) [CB 2072 fjunk] ->
  evt asegs (sfixE_post vra q gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 s8 s9 s10 s11 F fc A str E k lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 1) a1 (Z_to_bv 64 E) (Z_to_bv 64 (A + k)) a4 a5 a6 a7
             (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51960) fc None m (seg_rom asegs)).
Proof.
  intros until fjunk. intros ST LO LOLO SPH A0 A47 N40 STR SEPS CHK HK M2S ICX MI E0 ESEP ESEP2 ECELL FRs FR.
  lstep. if_cases Kbe.
  - assert (KZ : k = 0). { zify_cond Kbe. rewrite ?(unsigned_lit A), ?(unsigned_lit (A + k)) in Kbe by lia. lia. }
    subst k. do 3 lstep. lstep.
    replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + Z.of_nat 0)) at 1 by (f_equal; lia).
    eapply evt_cut.
    { eapply (sfix_ws (nblank (str ++ [Z_to_bv 8 0])) 0%nat A str);
        [exact STR| lia| lia| lia| rewrite skipn_O; reflexivity| lia| exact MI]. }
    intros ms' (a1' & a4' & a5' & ->).
    eapply (sfix_from_57268 q A E lo (fix_off (str ++ [Z_to_bv 8 0])) 0);
      try eassumption; try (pose proof (fix_off_range str); lia); try (unfold kHighShadowEnd; lia).
  - lstep. if_cases Kg; zify_cond Kg;
    [ eapply (sfix_from_57268 q A E lo k k); try eassumption; try lia; try (unfold kHighShadowEnd; lia)
    | exfalso; rewrite ?(unsigned_lit A), ?(unsigned_lit (A + k)) in Kg by lia; lia ].
Qed.

Lemma sfix_tail : forall (q A E k base lo : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 : word) F fc (m : mem) (str fjunk : list byte),
  stk asegs m lo (q + -2144) -> lo <= q - 2224 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= A -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> (A + Z.of_nat (length str) + 1 <= q + -2224 \/ q <= A) ->
  (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) -> 0 <= k <= Z.of_nat (length str) ->
  (base = 10 \/ base = 16) -> m2s_cells m -> icells_sx m -> mem_inv asegs m ->
  0 < E -> (E + 8 <= q + -2224 \/ q <= E) -> (E + 8 <= A \/ A + Z.of_nat (length str) + 1 <= E) ->
  rw_cells asegs m E [C8 (Z_to_bv 64 (A + k))] ->
  rw_cells asegs m (q + -72) [C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells asegs m (q + -2144) [CB 2072 fjunk] ->
  evt asegs (sfixE_post vra q gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 s8 s9 s10 s11 F fc A str E k lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 (Z_to_bv 64 E) (Z_to_bv 64 (A + k)) (Z_to_bv 64 base) a5 a6 a7
             (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5194c) fc None m (seg_rom asegs)).
Proof.
  intros until fjunk. intros ST LO LOLO SPH A0 A47 N40 STR SEPS CHK HK HB M2S ICX MI E0 ESEP ESEP2 ECELL FRs FR.
  destruct HB as [HB|HB]; subst base; do 4 lstep; lstep; if_false;
    eapply (sfix_from_57204 q A E k lo); try eassumption; try lia; try (unfold kHighShadowEnd; lia).
Qed.

Lemma sfixE_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (A E k base lo : Z) (str ejunk : list byte),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2144 - 80 -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  0 <= A -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> (A + Z.of_nat (length str) + 1 <= bv_unsigned sp + -2224 \/ bv_unsigned sp <= A) ->
  (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) -> 0 <= k <= Z.of_nat (length str) ->
  0 < E -> E + 8 <= 2^47 -> E mod 8 = 0 -> rw_cells asegs m E [CB 8 ejunk] -> chk_ok m E 8 ->
  (E + 8 <= bv_unsigned sp + -2224 \/ bv_unsigned sp <= E) -> (E + 8 <= A \/ A + Z.of_nat (length str) + 1 <= E) ->
  (E + 8 <= 0x9c7e0 \/ 0x136e5e <= E) ->
  (base = 10 \/ base = 16) -> m2s_cells m -> icells_sx m -> mem_inv asegs m ->
  a3' = Z_to_bv 64 (A + k) -> a4' = Z_to_bv 64 base ->
  evt asegs (sfixE_post ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A str E k lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 A) (Z_to_bv 64 E) a3' a4' a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x518c4) fc None m (seg_rom asegs)).
Proof.
  intros until ejunk.
  intros ST LO LOLO SPH A0 A47 N40 STR SEPS CHK HK E0 E47 EAL ECELL CHKE ESEP ESEP2 ESEPRT HB M2S ICX MI HA3 HA4.
  subst a3' a4'.
  pose proof (bv_unsigned_in_range 64 sp) as HSPR. unfold bv_modulus in HSPR. cbn [Z.of_N] in HSPR.
  unfold kHighShadowEnd in LOLO.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2144 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp + -2224, usp); (E, E + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 72%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  zidle_beginz usp 2144%Z MUz1 WMz1.
  xsteps_to 0x51904%Z.
  zidle_end MUz1 WMz1.
  lstep. if_cases Kz; zify_cond Kz; [exfalso; lia|]. lstep. lstep. lstep. if_cases Kg; zify_cond Kg; [exfalso; lia|].
  pose proof ((proj2 (proj2 CHKE)) ltac:(lia)) as RIMEp. destruct RIMEp as (RIME & _).
  unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd in RIME.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with HMU : munch _ m mm |- _ =>
      assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm)
        by (apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ (conj _ I)); lia);
      pose proof (chk_ok_agree m mm E _ CHKE ltac:(lia) ltac:(lia) AGS) as CHKE1;
      assert (CHK1 : forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok mm A nn)
        by (intros nn Hnn; apply (chk_ok_agree m mm A nn (CHK nn Hnn) ltac:(lia) ltac:(lia) AGS));
      assert (M2S1 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
        [ apply (rw_cells_agree asegs m mm _ _ M1); [| assumption]; apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ (conj _ I)); lia
        | apply (rw_cells_agree asegs m mm _ _ M2); [| assumption]; apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ (conj _ I)); lia
        | apply (rw_cells_agree asegs m mm _ _ M3); [| assumption]; apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ (conj _ I)); lia ]);
      assert (ICX1 : icells_sx mm) by (destruct ICX as (I1 & I2); split;
        [ apply (ro_cells_agree asegs m mm _ _ I1); apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ (conj _ I)); lia
        | apply (ro_cells_agree asegs m mm _ _ I2); apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ (conj _ I)); lia ])
    end
  end.
  destruct M2S1 as (G2 & SHC & HM). unfold SHB in SHC.
  destruct CHKE1 as (ACE1 & QWE1 & ROE1).
  destruct (QWE1 ltac:(lia)) as (w1 & w2 & W1 & W2).
  do 10 lstep.
  unfold al8, shad, SHB in W1, W2.
  assert (E1 : Z.land ((2147450880 + E ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((E / 8 + 2147450880) / 8)).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
  assert (E2 : Z.land ((2147450880 + (E + 7) ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * (((E + 8 - 1) / 8 + 2147450880) / 8)).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (E + 8 - 1) with (E + 7) by lia. lia. }
  rewrite E1, E2. clear E1 E2.
  lstep. lstep. lstep. lstep. if_cases Kq.
  + destruct (ACE1 7 ltac:(lia)) as (b7 & B7 & OK7).
    assert (HB7 : bv_unsigned b7 = 0).
    { unfold sh_ok in OK7. destruct OK7 as [H|[H1 H2]]; [exact H|].
      exfalso. assert (HM7 : (E + 7) mod 8 = 7) by (rewrite Zplus_mod, EAL; reflexivity). lia. }
    assert (Eb7 : b7 = Z_to_bv 8 0) by (apply bv_eq; rewrite HB7; vm_compute; reflexivity). rewrite Eb7 in B7.
    unfold shad, SHB in B7. pose proof (ro_C1_of_bytes _ _ _ B7) as CB7.
    rewrite ?Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
    assert (HD7 : (E + 7) / 8 = E / 8) by (Z.div_mod_to_equations; lia).
    rewrite HD7 in CB7 |- *.
    replace (E / 8 + 2147450880) with (2147450880 + E / 8) in CB7 by lia.
    remember (2147450880 + E / 8)%Z as ea eqn:Eea.
    assert (EUea : bv_unsigned (Z_to_bv 64 ea) = ea) by (apply unsigned_lit; rewrite Eea; Z.div_mod_to_equations; lia).
    clear W1 W2. lstep. do 5 lstep. lstep. if_true. lstep. lstep. if_true.
    assert (M2S1 : m2s_cells m1) by (split; [exact G2| split; [exact SHC| exact HM]]).
    eapply evt_mono.
    { eapply (sfix_tail usp A E k base lo); try eassumption; try (unfold kHighShadowEnd; lia); try lia. }
    intros ms' Hpost. unfold sfixE_post in Hpost |- *.
    destruct Hpost as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Heq & Hmunch1 & Hwm1 & Hmi & Hstk & Hba & Hecell).
    do 16 eexists. split; [exact Heq|].
    split; [eapply munch_trans; [exact MU| exact Hmunch1]|].
    split; [eapply wmono_trans; [exact WM| exact Hwm1]|].
    split; [exact Hmi|]. split; [exact Hstk|]. split; [exact Hba|]. exact Hecell.
  + assert (M2S1 : m2s_cells m1) by (split; [exact G2| split; [exact SHC| exact HM]]).
    eapply evt_mono.
    { eapply (sfix_tail usp A E k base lo); try eassumption; try (unfold kHighShadowEnd; lia); try lia. }
    intros ms' Hpost. unfold sfixE_post in Hpost |- *.
    destruct Hpost as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Heq & Hmunch1 & Hwm1 & Hmi & Hstk & Hba & Hecell).
    do 16 eexists. split; [exact Heq|].
    split; [eapply munch_trans; [exact MU| exact Hmunch1]|].
    split; [eapply wmono_trans; [exact WM| exact Hwm1]|].
    split; [exact Hmi|]. split; [exact Hstk|]. split; [exact Hba|]. exact Hecell.
Qed.

End WithRIP.
